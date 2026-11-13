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
        simp [step_simp, wr, Reg64s.getXReg_setXReg_of_ne _ _ _ _ hta,
          Reg64s.getXReg_setXReg_of_ne _ _ _ _ htb, Reg64s.getXReg_setXReg_same, BitVec.toNat_eq,
          hy0', srem_eq_sub]
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
        simp [step_simp, wr, Reg64s.getXReg_setXReg_of_ne _ _ _ _ hta,
          Reg64s.getXReg_setXReg_of_ne _ _ _ _ htb, Reg64s.getXReg_setXReg_same, BitVec.toNat_eq,
          hy0', umod_eq_sub]
  all_goals cases w
  all_goals
    refine ⟨wr s d (r.setWidth 64), Runs.single fun p next jmp => ?_, get_wr_same ..,
      fun x hx _ => get_wr_of_ne _ _ _ _ hx, rfl⟩
    simp only [BinOp.eval] at hv
    simp only [step_simp, wr, Int64.toInt_zero, Int.toNat_zero, BitVec.shiftLeft_zero,
      BitVec.add_zero, BitVec.ushiftRight_eq, hx, hy]
  case div.W32 | div.W64 =>
    by_cases h : sdivDefined x y = true
    · simp only [h, ite_true, Option.some.injEq] at hv
      subst hv
      have hy0 : y ≠ 0 := by
        simp only [sdivDefined, Bool.and_eq_true, bne_iff_ne] at h; exact h.1
      grind
    · simp only [h, Bool.false_eq_true, ite_false, reduceCtorEq] at hv
  case udiv.W32 | udiv.W64 => grind
  all_goals (simp only [Option.some.injEq] at hv; rw [hv])

@[step_simp]
theorem setRegOrZr_xzr (regs : Reg64s) (w : RegWidth) (v : BitVec w.bits) :
    regs.setRegOrZr (xzr w) v = regs := by
  cases w <;> rfl

theorem notCondOf_subs {n : Nat} (hn : n = 32 ∨ n = 64) (co : CmpOp) (x y : BitVec n) :
    (notCondOf co).interp (StatusFlags.subs (x - y) x y) = !(co.eval x y) := by
  rcases hn with rfl | rfl <;> cases co <;>
    grind [notCondOf, StatusFlags.subs, StatusFlags.from_result, CondCode.interp, CmpOp.eval,
      BitVec.unsigned, BitVec.signed]

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
  · simp only [step_simp, Int64.toInt_zero, Int.toNat_zero, BitVec.shiftLeft_zero, hx, hy]
  · simp only [step_simp, hc, wr]
    congr 3
    cases co.eval x y <;> decide

set_option linter.unusedSimpArgs false in
theorem extIns_runs (k : Cls) (sz : Sz) (sg : Bool) (d a : XReg) (s : MachineData) :
    ∃ s', Runs (extIns k sz sg d a) s s' ∧
      get s' (.reg d) = k.trunc (sz.extend sg (get s (.reg a))) ∧
      (∀ x, x ≠ .reg d → get s' x = get s x) ∧ s'.dmem = s.dmem := by
  refine ⟨wr s d (k.trunc (sz.extend sg (get s (.reg a)))), ?_, get_wr_same ..,
    fun z hz => get_wr_of_ne _ _ _ _ hz, rfl⟩
  rw [get_reg]
  cases sz <;> cases sg <;> cases k <;> dsimp only [extIns, widthOf, topBit] <;>
    refine Runs.single fun p next jmp => ?_ <;>
    simp only [step_simp, Int64.toInt_zero, Int.toNat_zero, BitVec.shiftLeft_zero, evalSBFM,
      evalUBFM, Cls.trunc, Sz.extend, wr, BitVec.take, ite_true, ite_false, Bool.false_eq_true] <;>
    congr 3 <;> simp [lo32, zext32] <;> ext i hi <;>
    grind

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
    grind
  · subst ha' hb' hbc
    simp only [remTmp, Option.some.injEq] at ht
    grind
  · subst ha' hb' hac
    simp only [remTmp, Option.some.injEq] at ht
    grind
  · subst hac hbc
    simp [remTmp] at ht

theorem swapCmp_eval {n : Nat} (co : CmpOp) (a b : BitVec n) :
    (swapCmp co).eval a b = co.eval b a := by
  cases co <;> try rfl
  · simp only [swapCmp, CmpOp.eval]; rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, eq_comm]
  · simp only [swapCmp, CmpOp.eval]; rw [Bool.eq_iff_iff, bne_iff_ne, bne_iff_ne, ne_comm]

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

theorem setWidth32_clsW (c : Val) : (Cls.w.trunc c).setWidth 32 = c.setWidth 32 := by
  simp only [Cls.trunc, zext32, lo32]
  grind

theorem ofInt_toInt_clsW {cb : Val} (hlt : (Cls.w.trunc cb).toNat < 4096) :
    BitVec.ofInt 32 (Cls.w.trunc cb).toInt = cb.setWidth 32 := by
  rw [ofInt_toInt_setWidth_of_lt 32 hlt, setWidth32_clsW]

theorem ofInt_toInt_clsL {cb : Val} (hlt : (Cls.l.trunc cb).toNat < 4096) :
    BitVec.ofInt 64 (Cls.l.trunc cb).toInt = cb := by
  rw [ofInt_toInt_setWidth_of_lt 64 hlt]
  simp [Cls.trunc, BitVec.setWidth_eq]

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

set_option linter.unusedSimpArgs false in
theorem fastBin_runs {k : Cls} {bo : BinOp} {d : XReg} {a b : Arg Reg}
    {ds : List Directive} {v : Val} {s : MachineData}
    (hf : fastBin? k bo d a b = some ds)
    (hv : ((Op.bin k bo a b).map (get s)).eval = some v) :
    ∃ s', Runs ds s s' ∧ get s' (.reg d) = v ∧ (∀ r, r ≠ .reg d → get s' r = get s r) ∧
      s'.dmem = s.dmem := by
  cases a with
  | var va =>
    cases va with
    | SP => simp [fastBin?] at hf
    | reg ra =>
      cases b with
      | var _ => simp [fastBin?] at hf
      | imm cb =>
        cases hsh : shiftImmIns (widthOf k) bo d ra cb with
        | some ds' =>
          simp only [fastBin?, hsh, Option.some.injEq] at hf
          subst hf
          exact shiftImmIns_runs hsh hv
        | none =>
          simp only [fastBin?, hsh, imm12?, bind, Option.bind_eq_some_iff] at hf
          split at hf
          · rename_i hlt
            simp only [Option.some.injEq] at hf
            obtain ⟨ei, rfl, hbin⟩ := hf
            cases bo <;> simp only [binImmIns, Option.some.injEq, reduceCtorEq] at hbin <;>
              subst hbin <;> cases k <;>
              simp only [Op.map, Op.eval, Arg.map, Arg.val, BinOp.eval, Option.map_some,
                Option.some.injEq] at hv <;> subst hv <;>
              refine ⟨wr s d _, Runs.single fun p next jmp => ?_, get_wr_same ..,
                fun z hz => get_wr_of_ne _ _ _ _ hz, rfl⟩
            · simp [step_simp, Int64.toBitVec_ofBitVec, ofInt_toInt_clsW hlt, get_reg, wr, widthOf,
                RegWidth.bits, MemWidth.bits, lo32, zext32, BitVec.setWidth_eq, BitVec.zeroExtend]
              rfl
            · simp [step_simp, Int64.toBitVec_ofBitVec, ofInt_toInt_clsL hlt, setWidth32_clsW,
                get_reg, wr, widthOf, RegWidth.bits, MemWidth.bits, Cls.trunc, BitVec.setWidth_eq]
              rfl
            · simp [step_simp, Int64.toBitVec_ofBitVec, ofInt_toInt_clsW hlt, get_reg, wr, widthOf,
                RegWidth.bits, MemWidth.bits, lo32, zext32, BitVec.setWidth_eq, BitVec.zeroExtend]
              rfl
            · simp [step_simp, Int64.toBitVec_ofBitVec, ofInt_toInt_clsL hlt, get_reg, wr, widthOf,
                RegWidth.bits, MemWidth.bits, Cls.trunc, BitVec.setWidth_eq]
              rfl
          · obtain ⟨_, ⟨⟩, _⟩ := hf
  | imm ca =>
    cases b with
    | imm _ => simp [fastBin?] at hf
    | var vb =>
      cases vb with
      | SP => simp [fastBin?] at hf
      | reg rb =>
        by_cases hbo : bo = .add
        · subst hbo
          simp only [fastBin?, beq_self_eq_true, ite_true, imm12?, bind,
            Option.bind_eq_some_iff] at hf
          split at hf
          · rename_i hlt
            simp only [Option.some.injEq] at hf
            obtain ⟨ei, rfl, hbin⟩ := hf
            simp only [binImmIns, Option.some.injEq] at hbin; subst hbin
            cases k <;> simp only [Op.map, Op.eval, Arg.map, Arg.val, BinOp.eval, Option.map_some,
              Option.some.injEq] at hv <;> subst hv <;>
              refine ⟨wr s d _, Runs.single fun p next jmp => ?_, get_wr_same ..,
                fun z hz => get_wr_of_ne _ _ _ _ hz, rfl⟩
            · simp [step_simp, Int64.toBitVec_ofBitVec, ofInt_toInt_clsW hlt, get_reg, wr, widthOf,
              RegWidth.bits, MemWidth.bits, lo32, zext32, BitVec.setWidth_eq, BitVec.zeroExtend]
              rw [BitVec.add_comm]; rfl
            · simp [step_simp, Int64.toBitVec_ofBitVec, ofInt_toInt_clsL hlt, get_reg, wr, widthOf,
              RegWidth.bits, MemWidth.bits, Cls.trunc, BitVec.setWidth_eq]
              rw [BitVec.add_comm]; rfl
          · obtain ⟨_, ⟨⟩, _⟩ := hf
        · simp [fastBin?, hbo] at hf

set_option linter.unusedSimpArgs false in
theorem fastCmp_runs {k : Cls} {co : CmpOp} {d : XReg} {a b : Arg Reg}
    {ds : List Directive} {v : Val} {s : MachineData}
    (hf : fastCmp? k co d a b = some ds)
    (hv : ((Op.cmp k co a b).map (get s)).eval = some v) :
    ∃ s', Runs ds s s' ∧ get s' (.reg d) = v ∧ (∀ r, r ≠ .reg d → get s' r = get s r) ∧
      s'.dmem = s.dmem := by
  cases a with
  | var va =>
    cases va with
    | SP => simp [fastCmp?] at hf
    | reg ra =>
      cases b with
      | var _ => simp [fastCmp?] at hf
      | imm cb =>
        simp only [fastCmp?, imm12?, bind, Option.bind_eq_some_iff] at hf
        split at hf
        · rename_i hlt
          simp only [Option.some.injEq] at hf
          obtain ⟨ei, rfl, rfl⟩ := hf
          cases k
          · generalize hx : (get s (.reg ra)).setWidth 32 = x
            generalize hy : cb.setWidth 32 = y
            rw [get_reg] at hx
            have hc := notCondOf_subs (Or.inl rfl) co x y
            refine ⟨wr { s with status := StatusFlags.subs (x - y) x y } d (boolVal (co.eval x y)),
              Runs.cons (s₂ := { s with status := StatusFlags.subs (x - y) x y })
                (fun p next jmp => ?_) (Runs.single fun p next jmp => ?_),
              ?_, fun z hz => get_wr_of_ne _ _ _ _ hz, rfl⟩
            · simp [step_simp, Int64.toBitVec_ofBitVec, ofInt_toInt_clsW hlt, widthOf,
              RegWidth.bits, MemWidth.bits, hx, hy]; rfl
            · simp only [step_simp, hc, wr]
              congr 3; cases co.eval x y <;> decide
            · rw [get_wr_same, ← hx, ← hy, ← get_reg]
              simp only [Op.map, Op.eval, Arg.map, Arg.val, Option.some.injEq] at hv; subst hv; rfl
          · generalize hx : get s (.reg ra) = x
            rw [get_reg] at hx
            have hc := notCondOf_subs (Or.inr rfl) co x cb
            refine ⟨wr { s with status := StatusFlags.subs (x - cb) x cb } d
              (boolVal (co.eval x cb)),
              Runs.cons (s₂ := { s with status := StatusFlags.subs (x - cb) x cb })
                (fun p next jmp => ?_) (Runs.single fun p next jmp => ?_),
              ?_, fun z hz => get_wr_of_ne _ _ _ _ hz, rfl⟩
            · simp [step_simp, Int64.toBitVec_ofBitVec, ofInt_toInt_clsL hlt, widthOf,
              RegWidth.bits, MemWidth.bits, BitVec.setWidth_eq, hx]; rfl
            · simp only [step_simp, hc, wr]
              congr 3; cases co.eval x cb <;> decide
            · rw [get_wr_same, ← hx, ← get_reg]
              simp only [Op.map, Op.eval, Arg.map, Arg.val, Option.some.injEq] at hv; subst hv; rfl
        · obtain ⟨_, ⟨⟩, _⟩ := hf
  | imm ca =>
    cases b with
    | imm _ => simp [fastCmp?] at hf
    | var vb =>
      cases vb with
      | SP => simp [fastCmp?] at hf
      | reg rb =>
        simp only [fastCmp?, imm12?, bind, Option.bind_eq_some_iff] at hf
        split at hf
        · rename_i hlt
          simp only [Option.some.injEq] at hf
          obtain ⟨ei, rfl, rfl⟩ := hf
          cases k
          · generalize hx : (get s (.reg rb)).setWidth 32 = x
            generalize hy : ca.setWidth 32 = y
            rw [get_reg] at hx
            have hc := notCondOf_subs (Or.inl rfl) (swapCmp co) x y
            refine ⟨wr { s with status := StatusFlags.subs (x - y) x y } d
              (boolVal ((swapCmp co).eval x y)),
              Runs.cons (s₂ := { s with status := StatusFlags.subs (x - y) x y })
                (fun p next jmp => ?_) (Runs.single fun p next jmp => ?_),
              ?_, fun z hz => get_wr_of_ne _ _ _ _ hz, rfl⟩
            · simp [step_simp, Int64.toBitVec_ofBitVec, ofInt_toInt_clsW hlt, widthOf,
              RegWidth.bits, MemWidth.bits, hx, hy]; rfl
            · simp only [step_simp, hc, wr]
              congr 3; cases (swapCmp co).eval x y <;> decide
            · rw [get_wr_same, swapCmp_eval, ← hx, ← hy, ← get_reg]
              simp only [Op.map, Op.eval, Arg.map, Arg.val, Option.some.injEq] at hv; subst hv; rfl
          · generalize hx : get s (.reg rb) = x
            rw [get_reg] at hx
            have hc := notCondOf_subs (Or.inr rfl) (swapCmp co) x ca
            refine ⟨wr { s with status := StatusFlags.subs (x - ca) x ca } d
              (boolVal ((swapCmp co).eval x ca)),
              Runs.cons (s₂ := { s with status := StatusFlags.subs (x - ca) x ca })
                (fun p next jmp => ?_) (Runs.single fun p next jmp => ?_),
              ?_, fun z hz => get_wr_of_ne _ _ _ _ hz, rfl⟩
            · simp [step_simp, Int64.toBitVec_ofBitVec, ofInt_toInt_clsL hlt, widthOf,
              RegWidth.bits, MemWidth.bits, BitVec.setWidth_eq, hx]; rfl
            · simp only [step_simp, hc, wr]
              congr 3; cases (swapCmp co).eval x ca <;> decide
            · rw [get_wr_same, swapCmp_eval, ← hx, ← get_reg]
              simp only [Op.map, Op.eval, Arg.map, Arg.val, Option.some.injEq] at hv; subst hv; rfl
        · obtain ⟨_, ⟨⟩, _⟩ := hf

theorem op_runs {o : Op Reg} {d : XReg} {c : List Directive} {v : Val} {s : MachineData}
    (hc : op o (.reg d) = some c) (hvars : ∀ r, r ∈ o.vars → r ∉ scratch)
    (hv : (o.map (get s)).eval = some v) :
    ∃ s', Runs c s s' ∧ get s' (.reg d) = v ∧ (∀ r, r ∉ .reg d :: scratch → get s' r = get s r) ∧
      s'.dmem = s.dmem := by
  cases o with
  | bin k bo a b =>
    cases hfb : fastBin? k bo d a b with
    | some ds =>
      simp only [op, hfb, Option.some.injEq] at hc
      subst hc
      obtain ⟨s', h', hd', hf', hm'⟩ := fastBin_runs hfb hv
      exact ⟨s', h', hd', fun z hz => hf' z (not_mem_rd_scratch hz).1, hm'⟩
    | none =>
      simp only [op, hfb, bind, Option.bind_eq_some_iff] at hc
      obtain ⟨⟨ca, ra⟩, ha, ⟨cb, rb⟩, hb, hc⟩ := hc
      dsimp only at hc
      have hv' : ∀ r, r ∈ a.vars ++ b.vars → r ∉ scratch := hvars
      obtain ⟨t, ht16, ht, rfl⟩ : ∃ t, (t = .X16 ∨ t = .X17) ∧
          (bo = .rem ∨ bo = .urem → t ≠ ra ∧ t ≠ rb) ∧
          c = ca ++ cb ++ binIns (widthOf k) bo d ra rb t := by
        cases bo
        case rem | urem =>
          obtain ⟨t, ht, hc⟩ := Option.bind_eq_some_iff.mp hc
          simp only [Option.some.injEq] at hc
          obtain ⟨h1, h2, h3⟩ := remTmp_spec ha hb hv' ht
          exact ⟨t, h1, fun _ => ⟨h2, h3⟩, hc.symm⟩
        all_goals
          grind
      obtain ⟨s₂, h₂, hra, hrb, hf₂, hd₂⟩ := args_runs (s := s) ha hb hv'
      simp only [Op.map, Op.eval] at hv
      cases k
      · obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp hv
        obtain ⟨s', h', hd', hf', hm'⟩ := binIns_runs .W32 bo d ra rb t s₂ r ht
          (by rw [hra, hrb]; exact hr)
        refine ⟨s', h₂.append h', hd', fun z hz => ?_, hm'.trans hd₂⟩
        obtain ⟨hzd, hz16, hz17⟩ := not_mem_rd_scratch hz
        grind
      · obtain ⟨s', h', hd', hf', hm'⟩ := binIns_runs .W64 bo d ra rb t s₂ v ht
          (by rw [hra, hrb]; simpa using hv)
        refine ⟨s', h₂.append h', hd'.trans (BitVec.setWidth_eq v), fun z hz => ?_, hm'.trans hd₂⟩
        obtain ⟨hzd, hz16, hz17⟩ := not_mem_rd_scratch hz
        grind
  | cmp k co a b =>
    cases hfc : fastCmp? k co d a b with
    | some ds =>
      simp only [op, hfc, Option.some.injEq] at hc
      subst hc
      obtain ⟨s', h', hd', hf', hm'⟩ := fastCmp_runs hfc hv
      exact ⟨s', h', hd', fun z hz => hf' z (not_mem_rd_scratch hz).1, hm'⟩
    | none =>
      simp only [op, hfc, bind, Option.bind_eq_some_iff, Option.some.injEq] at hc
      obtain ⟨⟨ca, ra⟩, ha, ⟨cb, rb⟩, hb, rfl⟩ := hc
      dsimp only
      have hv' : ∀ r, r ∈ a.vars ++ b.vars → r ∉ scratch := hvars
      obtain ⟨s₂, h₂, hra, hrb, hf₂, hd₂⟩ := args_runs (s := s) ha hb hv'
      obtain ⟨s', h', hd', hf', hm'⟩ := cmpIns_runs (widthOf k) co d ra rb s₂
      refine ⟨s', h₂.append h', ?_, fun z hz => ?_, hm'.trans hd₂⟩
      · rw [hd', hra, hrb]
        cases k <;> simp only [Op.map, Op.eval, Option.some.injEq] at hv <;> subst hv
        · rfl
        · simp [widthOf]
      · grind
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

private theorem subs_s_runs (w : RegWidth) (a b : XReg) (s : MachineData) :
    let x := (get s (.reg a)).setWidth w.bits
    let y := (get s (.reg b)).setWidth w.bits
    Runs [ins (.SUBS_s (xzr w) (zr a w) (sh b))] s
      { s with status := StatusFlags.subs (x - y) x y } := by
  intro x y
  refine Runs.single fun p next jmp => ?_
  simp only [step_simp, Int64.toInt_zero, Int.toNat_zero, BitVec.shiftLeft_zero, get_reg, x, y]

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
  dsimp only at hc hk ⊢
  obtain ⟨s₂, h₂, hra, hrb, hf₂, hd₂⟩ := args_runs (s := s) ha hb hvars
  obtain ⟨hca, htail⟩ := List.IsInfixAt.append hc
  obtain ⟨hsubs, hbcond⟩ := htail.cons
  have hbcond1 := List.isInfixAt_singleton.mp hbcond
  refine Runs.eventually h₂ hca ?_
  refine Runs.eventually (subs_s_runs (widthOf cls) ra rb s₂)
    (List.isInfixAt_singleton.mpr hsubs) ?_
  refine eventually_bcond hbcond1 hj ?_
  let x := (get s₂ (.reg ra)).setWidth (widthOf cls).bits
  let y := (get s₂ (.reg rb)).setWidth (widthOf cls).bits
  let s₃ : MachineData := { s₂ with status := StatusFlags.subs (x - y) x y }
  have hkeep : ∀ r, r ∉ scratch → get s₃ r = get s r := fun r hr => hf₂ r hr
  have hv' : v = boolVal ((condOf co).interp s₃.status) := by
    rw [condOf_subs (by cases cls <;> simp [widthOf, RegWidth.bits, MemWidth.bits])]
    simp only [x, y, hra, hrb]
    cases cls <;> simp only [Op.eval, widthOf, RegWidth.bits, MemWidth.bits,
      Option.some.injEq] at hv ⊢
    · exact hv.symm
    · exact hv.symm
  have hlen : k + (ca ++ cb).length +
      [ins (.SUBS_s (xzr (widthOf cls)) (zr ra (widthOf cls)) (sh rb))].length + 1 =
      k + ((ca ++ cb) ++ [ins (.SUBS_s (xzr (widthOf cls)) (zr ra (widthOf cls)) (sh rb)),
        ins (w := .W64) (.B_cond (condOf co) (.label l))]).length := by
    simp [List.length_append]; omega
  constructor
  · intro ht
    refine (hk s₃ hkeep hd₂).1 ?_
    rw [hv', ht]; exact truthy_boolVal_true
  · intro hf
    rw [hlen]
    refine (hk s₃ hkeep hd₂).2 ?_
    rw [hv', hf]; exact not_truthy_boolVal_false

set_option linter.unusedSimpArgs false in
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
  cases a with
  | var va =>
    cases va with
    | SP => exact eventually_jnzCmp_fallback hop hc hj hvars hv hk
    | reg ra =>
      cases b with
      | var vb => exact eventually_jnzCmp_fallback hop hc hj hvars hv hk
      | imm cb =>
        cases him : imm12? cls cb with
        | none =>
          simp only [jnzCmp, him] at hop
          exact eventually_jnzCmp_fallback hop hc hj hvars hv hk
        | some ei =>
          simp only [jnzCmp, him, Option.some.injEq] at hop
          subst hop
          simp only [imm12?] at him
          split at him
          · rename_i hlt
            simp only [Option.some.injEq] at him
            subst him
            obtain ⟨h0, hc1⟩ := hc.cons; obtain ⟨h1, -⟩ := hc1.cons
            cases cls
            · generalize hx : (get s (.reg ra)).setWidth 32 = x
              generalize hy : cb.setWidth 32 = y
              rw [get_reg] at hx
              have hcond := condOf_subs (Or.inl rfl) co x y
              have hs1 : Runs [ins (.SUBS_e (xzr .W32) (sp ra .W32)
                  (.imm { imm := .int64 (Int64.ofBitVec (Cls.w.trunc cb)), shift := .S0 }))] s
                  { s with status := StatusFlags.subs (x - y) x y } := by
                refine Runs.single fun p next jmp => ?_
                simp [step_simp, Int64.toBitVec_ofBitVec, ofInt_toInt_clsW hlt, widthOf,
                  RegWidth.bits, MemWidth.bits, hx, hy]
              refine Runs.eventually hs1 (List.isInfixAt_singleton.mpr h0) ?_
              refine eventually_bcond h1 hj ?_
              have hv' : v = boolVal (co.eval x y) := by
                rw [← hx, ← hy, ← get_reg]
                simp only [Op.map, Op.eval, Arg.map, Arg.val, Option.some.injEq] at hv
                exact hv.symm
              simp only [List.length_cons, List.length_nil, Nat.zero_add] at hk ⊢
              rw [← Nat.add_assoc] at hk
              exact ⟨fun ht => (hk { s with status := StatusFlags.subs (x - y) x y }
                  (fun _ _ => rfl) rfl).1 (by rw [hv', ← hcond, ht]; exact truthy_boolVal_true),
                fun hf => (hk { s with status := StatusFlags.subs (x - y) x y }
                  (fun _ _ => rfl) rfl).2
                  (by rw [hv', ← hcond, hf]; exact not_truthy_boolVal_false)⟩
            · generalize hx : get s (.reg ra) = x
              rw [get_reg] at hx
              have hcond := condOf_subs (Or.inr rfl) co x cb
              have hs1 : Runs [ins (.SUBS_e (xzr .W64) (sp ra .W64)
                  (.imm { imm := .int64 (Int64.ofBitVec (Cls.l.trunc cb)), shift := .S0 }))] s
                  { s with status := StatusFlags.subs (x - cb) x cb } := by
                refine Runs.single fun p next jmp => ?_
                simp [step_simp, Int64.toBitVec_ofBitVec, ofInt_toInt_clsL hlt, widthOf,
                  RegWidth.bits, MemWidth.bits, BitVec.setWidth_eq, hx]
              refine Runs.eventually hs1 (List.isInfixAt_singleton.mpr h0) ?_
              refine eventually_bcond h1 hj ?_
              have hv' : v = boolVal (co.eval x cb) := by
                rw [← hx, ← get_reg]
                simp only [Op.map, Op.eval, Arg.map, Arg.val, Option.some.injEq] at hv
                exact hv.symm
              simp only [List.length_cons, List.length_nil, Nat.zero_add] at hk ⊢
              rw [← Nat.add_assoc] at hk
              exact ⟨fun ht => (hk { s with status := StatusFlags.subs (x - cb) x cb }
                  (fun _ _ => rfl) rfl).1 (by rw [hv', ← hcond, ht]; exact truthy_boolVal_true),
                fun hf => (hk { s with status := StatusFlags.subs (x - cb) x cb }
                  (fun _ _ => rfl) rfl).2
                  (by rw [hv', ← hcond, hf]; exact not_truthy_boolVal_false)⟩
          · simp at him
  | imm ca =>
    cases b with
    | imm _ => exact eventually_jnzCmp_fallback hop hc hj hvars hv hk
    | var vb =>
      cases vb with
      | SP => exact eventually_jnzCmp_fallback hop hc hj hvars hv hk
      | reg rb =>
        cases him : imm12? cls ca with
        | none =>
          simp only [jnzCmp, him] at hop
          exact eventually_jnzCmp_fallback hop hc hj hvars hv hk
        | some ei =>
          simp only [jnzCmp, him, Option.some.injEq] at hop
          subst hop
          simp only [imm12?] at him
          split at him
          · rename_i hlt
            simp only [Option.some.injEq] at him
            subst him
            obtain ⟨h0, hc1⟩ := hc.cons; obtain ⟨h1, -⟩ := hc1.cons
            cases cls
            · generalize hx : (get s (.reg rb)).setWidth 32 = x
              generalize hy : ca.setWidth 32 = y
              rw [get_reg] at hx
              have hcond := condOf_subs (Or.inl rfl) (swapCmp co) x y
              have hs1 : Runs [ins (.SUBS_e (xzr .W32) (sp rb .W32)
                  (.imm { imm := .int64 (Int64.ofBitVec (Cls.w.trunc ca)), shift := .S0 }))] s
                  { s with status := StatusFlags.subs (x - y) x y } := by
                refine Runs.single fun p next jmp => ?_
                simp [step_simp, Int64.toBitVec_ofBitVec, ofInt_toInt_clsW hlt, widthOf,
                  RegWidth.bits, MemWidth.bits, hx, hy]
              refine Runs.eventually hs1 (List.isInfixAt_singleton.mpr h0) ?_
              refine eventually_bcond h1 hj ?_
              have hv' : v = boolVal ((swapCmp co).eval x y) := by
                rw [swapCmp_eval, ← hx, ← hy, ← get_reg]
                simp only [Op.map, Op.eval, Arg.map, Arg.val, Option.some.injEq] at hv
                exact hv.symm
              simp only [List.length_cons, List.length_nil, Nat.zero_add] at hk ⊢
              rw [← Nat.add_assoc] at hk
              exact ⟨fun ht => (hk { s with status := StatusFlags.subs (x - y) x y }
                  (fun _ _ => rfl) rfl).1 (by rw [hv', ← hcond, ht]; exact truthy_boolVal_true),
                fun hf => (hk { s with status := StatusFlags.subs (x - y) x y }
                  (fun _ _ => rfl) rfl).2
                  (by rw [hv', ← hcond, hf]; exact not_truthy_boolVal_false)⟩
            · generalize hx : get s (.reg rb) = x
              rw [get_reg] at hx
              have hcond := condOf_subs (Or.inr rfl) (swapCmp co) x ca
              have hs1 : Runs [ins (.SUBS_e (xzr .W64) (sp rb .W64)
                  (.imm { imm := .int64 (Int64.ofBitVec (Cls.l.trunc ca)), shift := .S0 }))] s
                  { s with status := StatusFlags.subs (x - ca) x ca } := by
                refine Runs.single fun p next jmp => ?_
                simp [step_simp, Int64.toBitVec_ofBitVec, ofInt_toInt_clsL hlt, widthOf,
                  RegWidth.bits, MemWidth.bits, BitVec.setWidth_eq, hx]
              refine Runs.eventually hs1 (List.isInfixAt_singleton.mpr h0) ?_
              refine eventually_bcond h1 hj ?_
              have hv' : v = boolVal ((swapCmp co).eval x ca) := by
                rw [swapCmp_eval, ← hx, ← get_reg]
                simp only [Op.map, Op.eval, Arg.map, Arg.val, Option.some.injEq] at hv
                exact hv.symm
              simp only [List.length_cons, List.length_nil, Nat.zero_add] at hk ⊢
              rw [← Nat.add_assoc] at hk
              exact ⟨fun ht => (hk { s with status := StatusFlags.subs (x - ca) x ca }
                  (fun _ _ => rfl) rfl).1 (by rw [hv', ← hcond, ht]; exact truthy_boolVal_true),
                fun hf => (hk { s with status := StatusFlags.subs (x - ca) x ca }
                  (fun _ _ => rfl) rfl).2
                  (by rw [hv', ← hcond, hf]; exact not_truthy_boolVal_false)⟩
          · simp at him

section ParserChecks
open Kraken.AArch64.Parser

-- Basic snippets
example : mov (.reg .X0) (.reg .X1) = parseAArch64("add x0, x1, #0") := rfl
example : movi (.reg .X0) 42 = parseAArch64("ldr x0, =42") := rfl
example : jmp "L" = parseAArch64("b L") := rfl
example : jnz (.reg .X0) "L" = parseAArch64("cbnz w0, L") := rfl
example : ret = parseAArch64("ret") := rfl

-- Loads (all Sz × Bool × Cls combinations, register and immediate addresses)
example : load .l .l false (.reg .X0) (.var (.reg .X1)) = some (parseAArch64("ldr x0, [x1]")) := rfl
example : load .w .l false (.reg .X0) (.var (.reg .X1)) =
  some (parseAArch64("ldr x0, [x1]
mov w0, w0")) := rfl
example : load .l .w true  (.reg .X0) (.var (.reg .X1)) =
  some (parseAArch64("ldrsw x0, [x1]")) := rfl
example : load .l .w false (.reg .X0) (.var (.reg .X1)) = some (parseAArch64("ldr w0, [x1]")) := rfl
example : load .w .w true  (.reg .X0) (.var (.reg .X1)) = some (parseAArch64("ldr w0, [x1]")) := rfl
example : load .l .h false (.reg .X0) (.var (.reg .X1)) =
  some (parseAArch64("ldrh w0, [x1]")) := rfl
example : load .l .h true  (.reg .X0) (.var (.reg .X1)) =
  some (parseAArch64("ldrsh x0, [x1]")) := rfl
example : load .w .h true  (.reg .X0) (.var (.reg .X1)) =
  some (parseAArch64("ldrsh w0, [x1]")) := rfl
example : load .l .b false (.reg .X0) (.var (.reg .X1)) =
  some (parseAArch64("ldrb w0, [x1]")) := rfl
example : load .l .b true  (.reg .X0) (.var (.reg .X1)) =
  some (parseAArch64("ldrsb x0, [x1]")) := rfl
example : load .w .b true  (.reg .X0) (.var (.reg .X1)) =
  some (parseAArch64("ldrsb w0, [x1]")) := rfl
example : load .l .l false (.reg .X0) (.imm 0x1000) =
  some (parseAArch64("ldr x16, =4096
ldr x0, [x16]")) := rfl

-- Stores (all Sz, register and immediate operands)
example : store .l (.var (.reg .X0)) (.var (.reg .X1)) = some (parseAArch64("str x0, [x1]")) := rfl
example : store .w (.var (.reg .X0)) (.var (.reg .X1)) = some (parseAArch64("str w0, [x1]")) := rfl
example : store .h (.var (.reg .X0)) (.var (.reg .X1)) = some (parseAArch64("strh w0, [x1]")) := rfl
example : store .b (.var (.reg .X0)) (.var (.reg .X1)) = some (parseAArch64("strb w0, [x1]")) := rfl
example : store .b (.imm 0) (.var (.reg .X1)) =
  some (parseAArch64("ldr x17, =0
strb w17, [x1]")) := rfl

-- Representative operations (bin, cmp, ext, copy)
example : op (.bin .l .add (.var (.reg .X1)) (.var (.reg .X2))) (.reg .X0) =
  some (parseAArch64("add x0, x1, x2")) := rfl
example : op (.bin .w .sub (.var (.reg .X1)) (.var (.reg .X2))) (.reg .X0) =
  some (parseAArch64("sub w0, w1, w2")) := rfl
example : op (.bin .l .mul (.var (.reg .X1)) (.var (.reg .X2))) (.reg .X0) =
  some (parseAArch64("mul x0, x1, x2")) := rfl
example : op (.bin .l .div (.var (.reg .X1)) (.var (.reg .X2))) (.reg .X0) =
  some (parseAArch64("sdiv x0, x1, x2")) := rfl
example : op (.bin .l .rem (.var (.reg .X1)) (.var (.reg .X2))) (.reg .X0) =
  some (parseAArch64("sdiv x17, x1, x2
msub x0, x17, x2, x1")) := rfl
example : op (.cmp .l .slt (.var (.reg .X1)) (.var (.reg .X2))) (.reg .X0) =
  some (parseAArch64("cmp x1, x2
cset w0, lt")) := rfl
example : op (.ext .l .b true (.var (.reg .X1))) (.reg .X0) =
  some (parseAArch64("sxtb x0, w1")) := rfl
example : op (.ext .w .h false (.var (.reg .X1))) (.reg .X0) =
  some (parseAArch64("uxth w0, w1")) := rfl
example : op (.copy .w (.var (.reg .X1))) (.reg .X0) =
  some (parseAArch64("mov w0, w1")) := rfl
example : op (.bin .l .shl (.var (.reg .X1)) (.imm 3)) (.reg .X0) =
  some (parseAArch64("lsl x0, x1, #3")) := rfl
example : op (.bin .w .shr (.var (.reg .X1)) (.imm 3)) (.reg .X0) =
  some (parseAArch64("lsr w0, w1, #3")) := rfl
example : op (.bin .l .sar (.var (.reg .X1)) (.imm 63)) (.reg .X0) =
  some (parseAArch64("asr x0, x1, #63")) := rfl

end ParserChecks

end LeanQbe.Arm64
