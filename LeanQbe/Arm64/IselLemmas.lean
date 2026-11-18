module

public import LeanQbe.Arm64.TargLemmas
import Kraken.AArch64.Parser

/-!
# AArch64 instruction selection lemmas

`op_runs`: the snippet `op o (.reg d)` of `Isel.lean` computes `o`'s value into `x d`, clobbering
at most `x16`/`x17` and leaving memory unchanged.

* Flag fact for `subs` (`notCondOf_subs`): after `cmp a, b`, the negated condition of `cset` holds
  iff the IL comparison is false, at widths 32 and 64.
* Remainders: `umod_eq_sub`, `srem_eq_sub` (`msub` after `udiv`/`sdiv`).
* One lemma per family: `binIns_runs`, `cmpIns_runs`, `extIns_runs`; operands `args_runs`.

No native bit-blasting tactics: proofs go through `toNat`/`toInt` (`grind`, `omega`), or bitwise
`ext`.
-/

@[expose] public section

namespace LeanQbe.Arm64

theorem umod_eq_sub {n : Nat} (a b : BitVec n) : a % b = a - (a / b) * b := by
  apply BitVec.eq_of_toNat_eq
  have h := BitVec.isLt a
  rw [BitVec.toNat_umod, BitVec.toNat_sub, BitVec.toNat_mul, BitVec.toNat_udiv]
  have hq : a.toNat / b.toNat * b.toNat ≤ a.toNat := Nat.div_mul_le_self _ _
  have := Nat.mod_add_div a.toNat b.toNat
  rw [Nat.mul_comm] at this
  rw [Nat.mod_eq_of_lt (a := a.toNat / b.toNat * b.toNat) (by omega)]
  rw [show 2 ^ n - a.toNat / b.toNat * b.toNat + a.toNat =
    2 ^ n + (a.toNat - a.toNat / b.toNat * b.toNat) by omega]
  rw [Nat.add_mod_left, Nat.mod_eq_of_lt (a := a.toNat - a.toNat / b.toNat * b.toNat) (by omega)]
  omega

theorem srem_eq_sub {n : Nat} (a b : BitVec n) : a.srem b = a - (a.sdiv b) * b := by
  rw [BitVec.srem_eq, BitVec.sdiv_eq]
  rcases a.msb <;> rcases b.msb <;> simp only [umod_eq_sub, BitVec.udiv_eq] <;>
    simp only [BitVec.neg_mul, BitVec.mul_neg, BitVec.neg_neg, BitVec.sub_eq_add_neg,
      BitVec.neg_add]

@[step_simp]
theorem getRegOrZr_xzr (regs : Reg64s) (w : RegWidth) : regs.getRegOrZr (xzr w) = 0#w.bits := by
  simp [Reg64s.getRegOrZr, Reg64s.getRegOrZr64, RegOrZr.base, BitVec.take]

private theorem wr2_spec {w : RegWidth} {o₁ o₂ : Operation w} {s : MachineData} {t d : XReg}
    {vt vd : Val}
    (h₁ : ∀ [Labels] p next jmp, o₁.interp p s next jmp = next (wr s t vt))
    (h₂ : ∀ [Labels] p next jmp, o₂.interp p (wr s t vt) next jmp = next (wr (wr s t vt) d vd)) :
    ∃ s', Runs [ins o₁, ins o₂] s s' ∧ get s' (.reg d) = vd ∧
      (∀ x, x ≠ .reg d → x ≠ .reg t → get s' x = get s x) ∧ s'.dmem = s.dmem :=
  ⟨_, Runs.cons h₁ (Runs.single h₂), get_wr_same .., fun z hz hz' => by simp [hz, hz'], rfl⟩

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
    obtain ⟨hta, htb⟩ := ht (.inl rfl)
    simp only [BinOp.eval] at hv; split at hv <;> simp only [Option.some.injEq, reduceCtorEq] at hv
    subst hv; have hy0' : ¬ y.toNat = 0 := by grind [sdivDefined]
    refine wr2_spec (vt := (x.sdiv y).setWidth 64) (fun _ _ _ => ?_) (fun _ _ _ => ?_) <;>
      (subst hx hy; cases w <;> simp at hy0' <;>
        simp [step_simp, wr, Reg64s.getXReg_setXReg, hta, htb, BitVec.toNat_eq, hy0', srem_eq_sub])
  case urem =>
    obtain ⟨hta, htb⟩ := ht (.inr rfl)
    simp only [BinOp.eval] at hv; split at hv <;> simp only [Option.some.injEq, reduceCtorEq] at hv
    subst hv; have hy0' : ¬ y.toNat = 0 := by grind
    refine wr2_spec (vt := (x / y).setWidth 64) (fun _ _ _ => ?_) (fun _ _ _ => ?_) <;>
      (subst hx hy; cases w <;> simp at hy0' <;>
        simp [step_simp, wr, Reg64s.getXReg_setXReg, hta, htb, BitVec.toNat_eq, hy0', umod_eq_sub])
  all_goals cases w
  all_goals
    refine ⟨wr s d (r.setWidth 64), Runs.single fun p next jmp => ?_, get_wr_same ..,
      fun x hx _ => get_wr_of_ne _ _ _ _ hx, rfl⟩
    simp only [BinOp.eval] at hv
    simp only [step_simp, wr, Int64.toInt_zero, Int.toNat_zero, BitVec.shiftLeft_zero,
      BitVec.add_zero, BitVec.ushiftRight_eq, hx, hy]
  case div.W32 | div.W64 | udiv.W32 | udiv.W64 => grind [sdivDefined]
  all_goals simp only [Option.some.injEq] at hv; rw [hv]

@[step_simp]
theorem setRegOrZr_xzr (regs : Reg64s) (w : RegWidth) (v : BitVec w.bits) :
    regs.setRegOrZr (xzr w) v = regs := by
  cases w <;> rfl

theorem notCondOf_subs {n : Nat} (hn : n = 32 ∨ n = 64) (co : CmpOp) (x y : BitVec n) :
    (notCondOf co).interp (StatusFlags.subs (x - y) x y) = !(co.eval x y) := by
  rcases hn with rfl | rfl <;> cases co <;>
    grind [notCondOf, StatusFlags.subs, StatusFlags.from_result, CondCode.interp, CmpOp.eval,
      BitVec.unsigned, BitVec.signed]

private theorem subs_s_runs (w : RegWidth) (a b : XReg) (s : MachineData) :
    let x := (get s (.reg a)).setWidth w.bits
    let y := (get s (.reg b)).setWidth w.bits
    Runs [ins (.SUBS_s (xzr w) (zr a w) (sh b))] s
      { s with status := StatusFlags.subs (x - y) x y } := by
  intro x y
  refine Runs.single fun p next jmp => ?_
  simp only [step_simp, Int64.toInt_zero, Int.toNat_zero, BitVec.shiftLeft_zero, get_reg, x, y]

private theorem csinc_subs_runs (w : RegWidth) (co : CmpOp) (d : XReg) (x y : BitVec w.bits)
    (s : MachineData) :
    Runs [ins (w := .W32) (.CSINC (zr d .W32) (xzr .W32) (xzr .W32) (notCondOf co))]
      { s with status := StatusFlags.subs (x - y) x y }
      (wr { s with status := StatusFlags.subs (x - y) x y } d (boolVal (co.eval x y))) := by
  refine Runs.single fun p next jmp => ?_
  simp only [step_simp, notCondOf_subs (by cases w <;> simp) co x y, wr]
  congr 3
  cases co.eval x y <;> decide

private theorem wr_spec {c : List Directive} {s : MachineData} {sf : StatusFlags}
    {d : XReg} {v : Val} (h : Runs c s (wr { s with status := sf } d v)) :
    ∃ s', Runs c s s' ∧ get s' (.reg d) = v ∧ (∀ r, r ≠ .reg d → get s' r = get s r) ∧
      s'.dmem = s.dmem :=
  ⟨_, h, get_wr_same .., fun _ => get_wr_of_ne _ _ _ _, rfl⟩

theorem cmpIns_runs (w : RegWidth) (co : CmpOp) (d a b : XReg) (s : MachineData) :
    ∃ s', Runs (cmpIns w co d a b) s s' ∧
      get s' (.reg d) =
        boolVal (co.eval ((get s (.reg a)).setWidth w.bits) ((get s (.reg b)).setWidth w.bits)) ∧
      (∀ x, x ≠ .reg d → get s' x = get s x) ∧ s'.dmem = s.dmem :=
  wr_spec (Runs.append (subs_s_runs w a b s) (csinc_subs_runs w co d _ _ s))

set_option linter.unusedSimpArgs false in
theorem extIns_runs (k : Cls) (sz : Sz) (sg : Bool) (d a : XReg) (s : MachineData) :
    ∃ s', Runs (extIns k sz sg d a) s s' ∧
      get s' (.reg d) = k.trunc (sz.extend sg (get s (.reg a))) ∧
      (∀ x, x ≠ .reg d → get s' x = get s x) ∧ s'.dmem = s.dmem := by
  refine wr_spec (sf := s.status) ?_
  rw [get_reg]
  cases sz <;> cases sg <;> cases k <;> dsimp only [extIns, widthOf, topBit] <;>
    refine Runs.single fun p next jmp => ?_ <;>
    simp only [step_simp, Int64.toInt_zero, Int.toNat_zero, BitVec.shiftLeft_zero, evalSBFM,
      evalUBFM, Cls.trunc, Sz.extend, wr, BitVec.take, ite_true, ite_false, Bool.false_eq_true] <;>
    congr 3 <;> simp [lo32, zext32] <;> ext i hi <;>
    grind

theorem argIn_reg {a : Arg Reg} {tmp : XReg} {ca : List Directive} {ra : XReg}
    (h : argIn a tmp = some (ca, ra)) : a = .var (.reg ra) ∨ (ra = tmp ∧ ∃ c, a = .imm c) := by
  revert h; fun_cases argIn a tmp <;> grind

theorem args_runs {a b : Arg Reg} {ca cb : List Directive} {ra rb : XReg} {s : MachineData}
    (ha : argIn a .X16 = some (ca, ra)) (hb : argIn b .X17 = some (cb, rb))
    (hvars : ∀ r, r ∈ a.vars ++ b.vars → r ∉ scratch) :
    ∃ s₂, Runs (ca ++ cb) s s₂ ∧ get s₂ (.reg ra) = (a.map (get s)).val ∧
      get s₂ (.reg rb) = (b.map (get s)).val ∧ (∀ r, r ∉ scratch → get s₂ r = get s r) ∧
      s₂.dmem = s.dmem := by
  obtain ⟨s₁, h₁, hra, hf₁, hd₁, -⟩ := argIn_runs ha s
  obtain ⟨s₂, h₂, hrb, hf₂, hd₂, -⟩ := argIn_runs hb s₁
  have hnot : ∀ r, r ∈ a.vars ++ b.vars → r ≠ .reg .X16 ∧ r ≠ .reg .X17 := fun r hr => by
    simpa [scratch] using hvars r hr
  refine ⟨s₂, h₁.append h₂, ?_, ?_, by grind [scratch], hd₂.trans hd₁⟩
  · rcases argIn_reg ha with rfl | ⟨rfl, -⟩ <;> grind [Arg.vars]
  · exact hrb.trans (Arg.val_map_congr fun r hr => hf₁ r (hnot r (List.mem_append_right _ hr)).1)

theorem remTmp_spec {a b : Arg Reg} {ca cb : List Directive} {ra rb t : XReg}
    (ha : argIn a .X16 = some (ca, ra)) (hb : argIn b .X17 = some (cb, rb))
    (hvars : ∀ r, r ∈ a.vars ++ b.vars → r ∉ scratch) (ht : remTmp a b = some t) :
    (t = .X16 ∨ t = .X17) ∧ t ≠ ra ∧ t ≠ rb := by
  have hva : ∀ r, a = .var (.reg r) → r ≠ .X16 ∧ r ≠ .X17 := fun r h => by
    simpa [h, Arg.vars, scratch] using hvars (.reg r)
  have hvb : ∀ r, b = .var (.reg r) → r ≠ .X16 ∧ r ≠ .X17 := fun r h => by
    simpa [h, Arg.vars, scratch] using hvars (.reg r)
  rcases argIn_reg ha with rfl | ⟨rfl, c, rfl⟩ <;> rcases argIn_reg hb with rfl | ⟨rfl, c', rfl⟩ <;>
    simp only [remTmp, Option.some.injEq, reduceCtorEq] at ht <;> grind

theorem swapCmp_eval {n : Nat} (co : CmpOp) (a b : BitVec n) :
    (swapCmp co).eval a b = co.eval b a := by
  cases co <;> grind [swapCmp, CmpOp.eval]

@[step_simp]
theorem getRegOrSp_sp (regs : Reg64s) (r : XReg) (w : RegWidth) :
    regs.getRegOrSp (sp r w) = (regs.getXReg r).toBitVec.setWidth w.bits := by
  cases w
  · rfl
  · simp [sp, Reg64s.getRegOrSp, Reg64s.getRegOrSp64, RegWidth.bits, MemWidth.bits,
      BitVec.take, BitVec.setWidth_eq]; rfl

@[step_simp]
theorem setRegOrSp_sp (regs : Reg64s) (d : XReg) (w : RegWidth) (v : BitVec w.bits) :
    regs.setRegOrSp (sp d w) v = regs.setXReg d (UInt64.ofBitVec (v.setWidth 64)) := by
  cases w <;> rfl

theorem ofInt_toInt_setWidth_of_lt (m : Nat) {v : Val} (h : v.toNat < 4096) :
    BitVec.ofInt m v.toInt = v.setWidth m := by
  grind

theorem imm12?_some {k : Cls} {c : Val} {ei : ExtOrImmReg} (h : imm12? k c = some ei) :
    ei = .imm { imm := .int64 (Int64.ofBitVec (k.trunc c)), shift := .S0 } ∧
      BitVec.ofInt (widthOf k).bits (Int64.ofBitVec (k.trunc c)).toInt =
        c.setWidth (widthOf k).bits := by
  simp only [imm12?] at h
  split at h
  · rename_i hlt
    refine ⟨(Option.some.inj h).symm, ?_⟩
    rw [Int64.toInt, Int64.toBitVec_ofBitVec, ofInt_toInt_setWidth_of_lt _ hlt]
    cases k <;> simp [Cls.trunc, widthOf, RegWidth.bits, MemWidth.bits]
  · contradiction

theorem eval_cmp_widthOf (k : Cls) (o : CmpOp) (a b : Arg Val) :
    (Op.cmp k o a b).eval = some (boolVal
      (o.eval (a.val.setWidth (widthOf k).bits) (b.val.setWidth (widthOf k).bits))) := by
  cases k <;> simp [Op.eval, widthOf, RegWidth.bits, MemWidth.bits]

theorem eval_bin_widthOf (k : Cls) (o : BinOp) (a b : Arg Val) :
    (Op.bin k o a b).eval =
      (o.eval (a.val.setWidth (widthOf k).bits) (b.val.setWidth (widthOf k).bits)).map
        (BitVec.setWidth 64) := by
  cases k
  · rfl
  · simp only [Op.eval, widthOf, RegWidth.bits, MemWidth.bits, BitVec.setWidth_eq]
    rcases o.eval a.val b.val <;> rfl

theorem lo32_toNat_mod32 (cb : Val) : (lo32 cb).toNat % 32 = cb.toNat % 32 := by
  simp only [lo32, BitVec.toNat_setWidth]
  omega

theorem evalUBFM_lsl {w : RegWidth} (x : w.type) {n : Nat} (hn : n < w.bits) :
    evalUBFM (w := w) x ((w.bits - n) % w.bits) (w.bits - 1 - n) = x <<< n := by
  cases w <;>
    simp only [evalUBFM, RegWidth.bits, MemWidth.bits, BitVec.take, BitVec.zeroExtend] at hn ⊢ <;>
    ext i hi <;> grind

theorem evalUBFM_lsr {w : RegWidth} (x : w.type) {n : Nat} (hn : n < w.bits) :
    evalUBFM (w := w) x n (w.bits - 1) = x >>> n := by
  cases w <;>
    simp only [evalUBFM, RegWidth.bits, MemWidth.bits, BitVec.take, BitVec.zeroExtend] at hn ⊢ <;>
    ext i hi <;> grind

theorem evalSBFM_asr {w : RegWidth} (x : w.type) {n : Nat} (hn : n < w.bits) :
    evalSBFM (w := w) x n (w.bits - 1) = x.sshiftRight n := by
  cases w <;>
    simp only [evalSBFM, RegWidth.bits, MemWidth.bits, BitVec.take, BitVec.zeroExtend] at hn ⊢ <;>
    ext i hi <;> grind

set_option linter.unusedSimpArgs false in
theorem shiftImmIns_runs {k : Cls} {bo : BinOp} {d ra : XReg} {cb : Val}
    {ds : List Directive} {v : Val} {s : MachineData}
    (hs : shiftImmIns (widthOf k) bo d ra cb = some ds)
    (hv : ((Op.bin k bo (.var (.reg ra)) (.imm cb)).map (get s)).eval = some v) :
    ∃ s', Runs ds s s' ∧ get s' (.reg d) = v ∧ (∀ r, r ≠ .reg d → get s' r = get s r) ∧
      s'.dmem = s.dmem := by
  have hn32 : cb.toNat % (RegWidth.W32).bits < (RegWidth.W32).bits := Nat.mod_lt _ (by decide)
  have hn64 : cb.toNat % (RegWidth.W64).bits < (RegWidth.W64).bits := Nat.mod_lt _ (by decide)
  cases bo <;> simp only [shiftImmIns, Option.some.injEq, reduceCtorEq] at hs <;> subst hs <;>
    cases k <;> simp only [Op.map, Op.eval, Arg.map, Arg.val, BinOp.eval, Option.map_some,
      Option.some.injEq, lo32_toNat_mod32] at hv <;> subst hv <;>
    refine ⟨wr s d _, Runs.single fun p next jmp => ?_, get_wr_same ..,
      fun z hz => get_wr_of_ne _ _ _ _ hz, rfl⟩ <;>
    simp only [step_simp, evalUBFM_lsl _ hn32, evalUBFM_lsl _ hn64, evalUBFM_lsr _ hn32,
      evalUBFM_lsr _ hn64, evalSBFM_asr _ hn32, evalSBFM_asr _ hn64, get_reg, wr, widthOf,
      RegWidth.bits, MemWidth.bits, lo32, zext32, BitVec.setWidth_eq]

private theorem binImmIns_runs {k : Cls} {bo : BinOp} {d a : XReg} {c v : Val} {ei : ExtOrImmReg}
    {ds : List Directive} {s : MachineData} (hei : imm12? k c = some ei)
    (hbi : binImmIns (widthOf k) bo d a ei = some ds)
    (hv : (bo.eval ((get s (.reg a)).setWidth (widthOf k).bits)
      (c.setWidth (widthOf k).bits)).map (BitVec.setWidth 64) = some v) :
    ∃ s', Runs ds s s' ∧ get s' (.reg d) = v ∧ (∀ r, r ≠ .reg d → get s' r = get s r) ∧
      s'.dmem = s.dmem := by
  obtain ⟨rfl, hof⟩ := imm12?_some hei
  refine wr_spec (sf := s.status) ?_
  cases bo <;> simp only [binImmIns, Option.some.injEq, reduceCtorEq] at hbi <;> subst hbi <;>
    simp only [BinOp.eval, Option.map_some, Option.some.injEq] at hv <;> subst hv <;>
    refine Runs.single fun p next jmp => ?_ <;>
    simp only [step_simp, hof, get_reg, wr]

theorem fastBin_runs {k : Cls} {bo : BinOp} {d : XReg} {a b : Arg Reg}
    {ds : List Directive} {v : Val} {s : MachineData}
    (hf : fastBin? k bo d a b = some ds)
    (hv : ((Op.bin k bo a b).map (get s)).eval = some v) :
    ∃ s', Runs ds s s' ∧ get s' (.reg d) = v ∧ (∀ r, r ≠ .reg d → get s' r = get s r) ∧
      s'.dmem = s.dmem := by
  revert hf
  fun_cases fastBin? k bo d a b <;> intro hf
  · obtain rfl := Option.some.inj hf
    exact shiftImmIns_runs ‹_› hv
  · simp only [Op.map, eval_bin_widthOf] at hv
    obtain ⟨ei, hei, hbi⟩ := Option.bind_eq_some_iff.mp hf
    exact binImmIns_runs hei hbi hv
  · simp only [Op.map, eval_bin_widthOf] at hv
    rename_i hbo
    simp only [beq_iff_eq] at hbo
    subst hbo
    obtain ⟨ei, hei, hbi⟩ := Option.bind_eq_some_iff.mp hf
    refine binImmIns_runs hei hbi ?_
    simpa [BinOp.eval, Arg.map, Arg.val, BitVec.add_comm] using hv
  · contradiction
  · contradiction

private theorem subs_e_runs {k : Cls} {c : Val} {ei : ExtOrImmReg} (hei : imm12? k c = some ei)
    (a : XReg) (s : MachineData) :
    let x := (get s (.reg a)).setWidth (widthOf k).bits
    let y := c.setWidth (widthOf k).bits
    Runs [ins (.SUBS_e (xzr (widthOf k)) (sp a (widthOf k)) ei)] s
      { s with status := StatusFlags.subs (x - y) x y } := by
  intro x y
  obtain ⟨rfl, hof⟩ := imm12?_some hei
  refine Runs.single fun p next jmp => ?_
  simp only [step_simp, hof, get_reg, x, y]

private theorem cmpImmIns_runs {k : Cls} {co : CmpOp} {d a : XReg} {c : Val} {ei : ExtOrImmReg}
    (hei : imm12? k c = some ei) (s : MachineData) :
    let x := (get s (.reg a)).setWidth (widthOf k).bits
    let y := c.setWidth (widthOf k).bits
    ∃ s', Runs (cmpImmIns (widthOf k) co d a ei) s s' ∧ get s' (.reg d) = boolVal (co.eval x y) ∧
      (∀ r, r ≠ .reg d → get s' r = get s r) ∧ s'.dmem = s.dmem :=
  wr_spec (Runs.append (subs_e_runs hei a s) (csinc_subs_runs (widthOf k) co d _ _ s))

theorem fastCmp_runs {k : Cls} {co : CmpOp} {d : XReg} {a b : Arg Reg}
    {ds : List Directive} {v : Val} {s : MachineData}
    (hf : fastCmp? k co d a b = some ds)
    (hv : ((Op.cmp k co a b).map (get s)).eval = some v) :
    ∃ s', Runs ds s s' ∧ get s' (.reg d) = v ∧ (∀ r, r ≠ .reg d → get s' r = get s r) ∧
      s'.dmem = s.dmem := by
  simp only [Op.map, eval_cmp_widthOf, Option.some.injEq] at hv
  subst hv
  revert hf
  fun_cases fastCmp? k co d a b <;> intro hf
  · obtain ⟨ei, hei, hds⟩ := Option.bind_eq_some_iff.mp hf
    obtain rfl := Option.some.inj hds
    exact cmpImmIns_runs hei s
  · obtain ⟨ei, hei, hds⟩ := Option.bind_eq_some_iff.mp hf
    obtain rfl := Option.some.inj hds
    simpa [Arg.map, Arg.val, swapCmp_eval] using cmpImmIns_runs (co := swapCmp co) hei s
  · contradiction

private theorem weaken_scratch {c : List Directive} {s : MachineData} {d : XReg} {v : Val}
    (h : ∃ s', Runs c s s' ∧ get s' (.reg d) = v ∧ (∀ r, r ≠ .reg d → get s' r = get s r) ∧
      s'.dmem = s.dmem) :
    ∃ s', Runs c s s' ∧ get s' (.reg d) = v ∧
      (∀ r, r ∉ .reg d :: scratch → get s' r = get s r) ∧ s'.dmem = s.dmem := by
  obtain ⟨s', h1, h2, h3, h4⟩ := h
  exact ⟨s', h1, h2, fun z hz => h3 z (not_mem_rd_scratch hz).1, h4⟩

theorem op_runs {o : Op Reg} {d : XReg} {c : List Directive} {v : Val} {s : MachineData}
    (hc : op o (.reg d) = some c) (hvars : ∀ r, r ∈ o.vars → r ∉ scratch)
    (hv : (o.map (get s)).eval = some v) :
    ∃ s', Runs c s s' ∧ get s' (.reg d) = v ∧ (∀ r, r ∉ .reg d :: scratch → get s' r = get s r) ∧
      s'.dmem = s.dmem := by
  cases o with
  | bin k bo a b =>
    cases hfb : fastBin? k bo d a b with
    | some ds =>
      simp only [op, hfb, Option.some.injEq] at hc; subst hc
      exact weaken_scratch (fastBin_runs hfb hv)
    | none =>
      simp only [op, hfb, bind, Option.bind_eq_some_iff] at hc
      obtain ⟨⟨ca, ra⟩, ha, ⟨cb, rb⟩, hb, hc⟩ := hc
      dsimp only at hc
      obtain ⟨t, ht16, ht, rfl⟩ : ∃ t, (t = .X16 ∨ t = .X17) ∧
          (bo = .rem ∨ bo = .urem → t ≠ ra ∧ t ≠ rb) ∧
          c = ca ++ cb ++ binIns (widthOf k) bo d ra rb t := by
        split at hc <;> simp only [Option.bind_eq_some_iff, Option.some.injEq] at hc <;>
          grind [remTmp_spec ha hb hvars]
      obtain ⟨s₂, h₂, hra, hrb, hf₂, hd₂⟩ := args_runs (s := s) ha hb hvars
      simp only [Op.map, eval_bin_widthOf] at hv
      obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp hv
      obtain ⟨s', h', hd', hf', hm'⟩ := binIns_runs (widthOf k) bo d ra rb t s₂ r ht
        (by rw [hra, hrb]; exact hr)
      refine ⟨s', h₂.append h', hd', fun z hz => ?_, hm'.trans hd₂⟩
      obtain ⟨hzd, hz16, hz17⟩ := not_mem_rd_scratch hz
      grind
  | cmp k co a b =>
    cases hfc : fastCmp? k co d a b with
    | some ds =>
      simp only [op, hfc, Option.some.injEq] at hc; subst hc
      exact weaken_scratch (fastCmp_runs hfc hv)
    | none =>
      simp only [op, hfc, bind, Option.bind_eq_some_iff, Option.some.injEq] at hc
      obtain ⟨⟨ca, ra⟩, ha, ⟨cb, rb⟩, hb, rfl⟩ := hc
      obtain ⟨s₂, h₂, hra, hrb, hf₂, hd₂⟩ := args_runs (s := s) ha hb hvars
      obtain ⟨s', h', hd', hf', hm'⟩ := cmpIns_runs (widthOf k) co d ra rb s₂
      simp only [Op.map, eval_cmp_widthOf, Option.some.injEq] at hv; subst hv
      exact ⟨s', h₂.append h', by rw [hd', hra, hrb], by grind, hm'.trans hd₂⟩
  | ext k sz sg a =>
    rcases a with ((r | _) | c₀) <;> simp only [op, Option.some.injEq, reduceCtorEq] at hc <;>
      subst hc <;> simp only [Op.map, Op.eval, Arg.map, Arg.val, Option.some.injEq] at hv <;>
      subst hv
    · exact weaken_scratch (extIns_runs k sz sg d r s)
    · exact weaken_scratch (wr_spec (sf := s.status) (runs_movImm d _ s))
  | copy k a =>
    rcases a with ((r | _) | c₀) <;> simp only [op, Option.some.injEq, reduceCtorEq] at hc <;>
      subst hc <;> simp only [Op.map, Op.eval, Arg.map, Arg.val, Option.some.injEq] at hv <;>
      subst hv
    · exact weaken_scratch (extIns_runs k .l false d r s)
    · exact weaken_scratch (wr_spec (sf := s.status) (runs_movImm d _ s))

private theorem truthy_boolVal_true : Truthy (boolVal true) := by decide
private theorem not_truthy_boolVal_false : ¬ Truthy (boolVal false) := by decide

theorem condOf_subs {n : Nat} (hn : n = 32 ∨ n = 64) (co : CmpOp) (x y : BitVec n) :
    (condOf co).interp (StatusFlags.subs (x - y) x y) = co.eval x y := by
  have h : ∀ sf : StatusFlags, (condOf co).interp sf = !(notCondOf co).interp sf := by
    rintro ⟨sn, sz, sc, sv⟩
    cases co <;> cases sn <;> cases sz <;> cases sc <;> cases sv <;> rfl
  rw [h, notCondOf_subs hn, Bool.not_not]

theorem eventually_bcond [Host] {i j : Nat} {cc : CondCode} {l : Label} {s : MachineData}
    {post : @_root_.Post MachineState}
    (hi : Host.prog[i]? = some (ins (w := .W64) (.B_cond cc (.label l))))
    (hj : Labels.label l = Host.addrOf j)
    (h : (cc.interp s.status = true → Eventually (step1 Host.exe) post ⟨s, Host.addrOf j⟩) ∧
      (cc.interp s.status = false → Eventually (step1 Host.exe) post ⟨s, Host.addrOf (i + 1)⟩)) :
    Eventually (step1 Host.exe) post ⟨s, Host.addrOf i⟩ := by
  refine Host.eventually_of_interp_cps hi ?_
  simp only [step_simp, hj]
  cases hc : cc.interp s.status
  · simp only [Bool.false_eq_true, ↓reduceIte, Effects.All]; exact h.2 hc
  · simp only [↓reduceIte, Effects.All]; exact h.1 hc

private theorem eventually_runs_bcond [Host] {k j : Nat} {cls : Cls} {co : CmpOp} {l : Label}
    {pfx : List Directive} {v : Val} {s s' : MachineData}
    {x y : BitVec (widthOf cls).bits} {post : @_root_.Post MachineState}
    (hr : Runs pfx s s')
    (hc : (pfx ++ [ins (w := .W64) (.B_cond (condOf co) (.label l))]).IsInfixAt Host.prog k)
    (hj : Labels.label l = Host.addrOf j)
    (hs : s'.status = StatusFlags.subs (x - y) x y) (hv : v = boolVal (co.eval x y))
    (hkeep : ∀ r, r ∉ scratch → get s' r = get s r) (hmem : s'.dmem = s.dmem)
    (hk : ∀ s' : MachineData, (∀ r, r ∉ scratch → get s' r = get s r) → s'.dmem = s.dmem →
      (Truthy v → Eventually (step1 Host.exe) post ⟨s', Host.addrOf j⟩) ∧
      (¬ Truthy v → Eventually (step1 Host.exe) post
        ⟨s', Host.addrOf (k + (pfx ++ [ins (w := .W64)
          (.B_cond (condOf co) (.label l))]).length)⟩)) :
    Eventually (step1 Host.exe) post ⟨s, Host.addrOf k⟩ := by
  obtain ⟨hpfx, hbcond⟩ := List.IsInfixAt.append hc
  refine hr.eventually hpfx (eventually_bcond (List.isInfixAt_singleton.mp hbcond) hj ⟨?_, ?_⟩)
  all_goals
    rw [hs, condOf_subs (by cases cls <;> simp [widthOf, RegWidth.bits, MemWidth.bits])]
    intro h
  · exact (hk s' hkeep hmem).1 (by rw [hv, h]; exact truthy_boolVal_true)
  · rw [show k + pfx.length + 1 = k + (pfx ++ [_]).length by simp [Nat.add_assoc]]
    exact (hk s' hkeep hmem).2 (by rw [hv, h]; exact not_truthy_boolVal_false)

private theorem eventually_jnzCmp_fallback [Host] {k j : Nat} {cls : Cls} {co : CmpOp}
    {a b : Arg Reg} {l : Label} {c : List Directive} {v : Val} {s : MachineData}
    {post : @_root_.Post MachineState}
    (hfb : (do
      let (ca, ra) ← argIn a .X16
      let (cb, rb) ← argIn b .X17
      some (ca ++ cb ++ [ins (.SUBS_s (xzr (widthOf cls)) (zr ra (widthOf cls)) (sh rb)),
        ins (w := .W64) (.B_cond (condOf co) (.label l))])) = some c)
    (hc : c.IsInfixAt Host.prog k) (hj : Labels.label l = Host.addrOf j)
    (hvars : ∀ r, r ∈ a.vars ++ b.vars → r ∉ scratch)
    (hv : (Op.cmp cls co (a.map (get s)) (b.map (get s))).eval = some v)
    (hk : ∀ s' : MachineData, (∀ r, r ∉ scratch → get s' r = get s r) → s'.dmem = s.dmem →
      (Truthy v → Eventually (step1 Host.exe) post ⟨s', Host.addrOf j⟩) ∧
      (¬ Truthy v → Eventually (step1 Host.exe) post ⟨s', Host.addrOf (k + c.length)⟩)) :
    Eventually (step1 Host.exe) post ⟨s, Host.addrOf k⟩ := by
  simp only [bind, Option.bind_eq_some_iff, Option.some.injEq] at hfb
  obtain ⟨⟨ca, ra⟩, ha, ⟨cb, rb⟩, hb, rfl⟩ := hfb
  obtain ⟨s₂, h₂, hra, hrb, hf₂, hd₂⟩ := args_runs (s := s) ha hb hvars
  rw [eval_cmp_widthOf, Option.some.injEq, ← hra, ← hrb] at hv
  have hassoc : ca ++ cb ++ [ins (.SUBS_s (xzr (widthOf cls)) (zr ra (widthOf cls)) (sh rb)),
      ins (w := .W64) (.B_cond (condOf co) (.label l))] =
    (ca ++ cb ++ [ins (.SUBS_s (xzr (widthOf cls)) (zr ra (widthOf cls)) (sh rb))]) ++
      [ins (w := .W64) (.B_cond (condOf co) (.label l))] := by simp
  rw [hassoc] at hc hk
  exact eventually_runs_bcond (h₂.append (subs_s_runs (widthOf cls) ra rb s₂)) hc hj rfl hv.symm
    hf₂ hd₂ hk

theorem eventually_jnzCmp [Host] {k j : Nat} {cls : Cls} {co : CmpOp} {a b : Arg Reg}
    {l : Label} {c : List Directive} {v : Val} {s : MachineData}
    {post : @_root_.Post MachineState}
    (hop : jnzCmp cls co a b l = some c) (hc : c.IsInfixAt Host.prog k)
    (hj : Labels.label l = Host.addrOf j) (hvars : ∀ r, r ∈ a.vars ++ b.vars → r ∉ scratch)
    (hv : (Op.cmp cls co (a.map (get s)) (b.map (get s))).eval = some v)
    (hk : ∀ s' : MachineData, (∀ r, r ∉ scratch → get s' r = get s r) → s'.dmem = s.dmem →
      (Truthy v → Eventually (step1 Host.exe) post ⟨s', Host.addrOf j⟩) ∧
      (¬ Truthy v → Eventually (step1 Host.exe) post ⟨s', Host.addrOf (k + c.length)⟩)) :
    Eventually (step1 Host.exe) post ⟨s, Host.addrOf k⟩ := by
  revert hop
  fun_cases jnzCmp cls co a b l <;> intro hop <;>
    first
    | exact eventually_jnzCmp_fallback hop hc hj hvars hv hk
    | obtain rfl := Option.some.inj hop
      rw [eval_cmp_widthOf, Option.some.injEq] at hv
  · exact eventually_runs_bcond (subs_e_runs ‹_› _ s) hc hj rfl hv.symm (fun _ _ => rfl) rfl hk
  · refine eventually_runs_bcond (subs_e_runs ‹_› _ s) hc hj rfl ?_ (fun _ _ => rfl) rfl hk
    simpa [Arg.map, Arg.val, swapCmp_eval] using hv.symm

section ParserChecks
open Kraken.AArch64.Parser

-- Basic snippets
example : mov (.reg .X0) (.reg .X1) = ⸨prog| add x0, x1, #0 ⸩ := rfl
example : movi (.reg .X0) 42 = ⸨prog| ldr x0, =42 ⸩ := rfl
example : jmp "L" = ⸨prog| b L ⸩ := rfl
example : jnz (.reg .X0) "L" = ⸨prog| cbnz w0, L ⸩ := rfl
example : ret = ⸨prog| ret ⸩ := rfl

-- Loads (all Sz × Bool × Cls combinations, register and immediate addresses)
example : load .l .l false (.reg .X0) (.var (.reg .X1)) = some ⸨prog| ldr x0, [x1] ⸩ := rfl
example : load .w .l false (.reg .X0) (.var (.reg .X1)) =
  some ⸨prog|
    ldr x0, [x1]
    mov w0, w0 ⸩ := rfl
example : load .l .w true  (.reg .X0) (.var (.reg .X1)) =
  some ⸨prog| ldrsw x0, [x1] ⸩ := rfl
example : load .l .w false (.reg .X0) (.var (.reg .X1)) = some ⸨prog| ldr w0, [x1] ⸩ := rfl
example : load .w .w true  (.reg .X0) (.var (.reg .X1)) = some ⸨prog| ldr w0, [x1] ⸩ := rfl
example : load .l .h false (.reg .X0) (.var (.reg .X1)) =
  some ⸨prog| ldrh w0, [x1] ⸩ := rfl
example : load .l .h true  (.reg .X0) (.var (.reg .X1)) =
  some ⸨prog| ldrsh x0, [x1] ⸩ := rfl
example : load .w .h true  (.reg .X0) (.var (.reg .X1)) =
  some ⸨prog| ldrsh w0, [x1] ⸩ := rfl
example : load .l .b false (.reg .X0) (.var (.reg .X1)) =
  some ⸨prog| ldrb w0, [x1] ⸩ := rfl
example : load .l .b true  (.reg .X0) (.var (.reg .X1)) =
  some ⸨prog| ldrsb x0, [x1] ⸩ := rfl
example : load .w .b true  (.reg .X0) (.var (.reg .X1)) =
  some ⸨prog| ldrsb w0, [x1] ⸩ := rfl
example : load .l .l false (.reg .X0) (.imm 0x1000) =
  some ⸨prog|
    ldr x16, =4096
    ldr x0, [x16] ⸩ := rfl

-- Stores (all Sz, register and immediate operands)
example : store .l (.var (.reg .X0)) (.var (.reg .X1)) = some ⸨prog| str x0, [x1] ⸩ := rfl
example : store .w (.var (.reg .X0)) (.var (.reg .X1)) = some ⸨prog| str w0, [x1] ⸩ := rfl
example : store .h (.var (.reg .X0)) (.var (.reg .X1)) = some ⸨prog| strh w0, [x1] ⸩ := rfl
example : store .b (.var (.reg .X0)) (.var (.reg .X1)) = some ⸨prog| strb w0, [x1] ⸩ := rfl
example : store .b (.imm 0) (.var (.reg .X1)) =
  some ⸨prog|
    ldr x17, =0
    strb w17, [x1] ⸩ := rfl

-- Representative operations (bin, cmp, ext, copy)
example : op (.bin .l .add (.var (.reg .X1)) (.var (.reg .X2))) (.reg .X0) =
  some ⸨prog| add x0, x1, x2 ⸩ := rfl
example : op (.bin .w .sub (.var (.reg .X1)) (.var (.reg .X2))) (.reg .X0) =
  some ⸨prog| sub w0, w1, w2 ⸩ := rfl
example : op (.bin .l .mul (.var (.reg .X1)) (.var (.reg .X2))) (.reg .X0) =
  some ⸨prog| mul x0, x1, x2 ⸩ := rfl
example : op (.bin .l .div (.var (.reg .X1)) (.var (.reg .X2))) (.reg .X0) =
  some ⸨prog| sdiv x0, x1, x2 ⸩ := rfl
example : op (.bin .l .rem (.var (.reg .X1)) (.var (.reg .X2))) (.reg .X0) =
  some ⸨prog|
    sdiv x17, x1, x2
    msub x0, x17, x2, x1 ⸩ := rfl
example : op (.cmp .l .slt (.var (.reg .X1)) (.var (.reg .X2))) (.reg .X0) =
  some ⸨prog|
    cmp x1, x2
    cset w0, lt ⸩ := rfl
example : op (.ext .l .b true (.var (.reg .X1))) (.reg .X0) =
  some ⸨prog| sxtb x0, w1 ⸩ := rfl
example : op (.ext .w .h false (.var (.reg .X1))) (.reg .X0) =
  some ⸨prog| uxth w0, w1 ⸩ := rfl
example : op (.copy .w (.var (.reg .X1))) (.reg .X0) =
  some ⸨prog| mov w0, w1 ⸩ := rfl

end ParserChecks

end LeanQbe.Arm64
