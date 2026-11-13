module

public import LeanQbe.Arm64.Isel
public import Kraken.AArch64.WP
public import Kraken.AArch64.Regs
public import Kraken.AArch64.Sep
public import LeanQbe.StepSimp

/-!
# AArch64 snippet lemmas: infrastructure, moves, constants, jumps, return

* `get s r`: the value of register `r` (`x0` to `x30`, `sp`) in machine data `s`.
* `Runs c s s'`: the straight-line code `c` runs from `s` and falls through with `s'`, at every
  position of every host. Sequential composition is `Runs.append`; single instructions are
  `Runs.single`, given their effect on the machine data.
* Step lemmas, in continuation form, for `mov`, `movi`, `jmp`, `jnz`, `ret`, and the operands of
  `Isel.lean` (`argIn`).
-/

@[expose] public section

namespace LeanQbe.Arm64

/-! ## Registers -/

/-- The value of register `r`. -/
abbrev get (s : MachineData) (r : Reg) : Val := s.regs.getRegOrSp64 r

/-- `s` with `x d := v`. -/
abbrev wr (s : MachineData) (d : XReg) (v : Val) : MachineData := { s with regs := s.regs.setXReg d v }

theorem get_reg (s : MachineData) (r : XReg) : get s (.reg r) = (s.regs.getXReg r).toBitVec := rfl

theorem get_sp (s : MachineData) : get s .SP = s.regs.SP.toBitVec := rfl

@[simp] theorem get_wr_same (s : MachineData) (d : XReg) (v : Val) : get (wr s d v) (.reg d) = v := by
  simp [get_reg]

@[simp] theorem get_wr_of_ne (s : MachineData) (d : XReg) (v : Val) (r : Reg) (h : r ≠ .reg d) :
    get (wr s d v) r = get s r := by
  cases r with
  | SP => simp [get_sp]
  | reg r =>
    have h' : d ≠ r := fun e => h (e ▸ rfl)
    simp [get_reg, Reg64s.getXReg_setXReg_of_ne _ _ _ _ h']

theorem get_wr (s : MachineData) (d : XReg) (v : Val) (r : Reg) :
    get (wr s d v) r = if r = .reg d then v else get s r := by
  split
  · subst r; exact get_wr_same ..
  · exact get_wr_of_ne _ _ _ _ ‹_›

@[simp] theorem wr_wr_same (s : MachineData) (d : XReg) (v v' : Val) :
    wr (wr s d v) d v' = wr s d v' := by
  simp [wr]

@[simp] theorem dmem_wr (s : MachineData) (d : XReg) (v : Val) : (wr s d v).dmem = s.dmem := rfl

/-! `step_simp` (`LeanQbe/StepSimp.lean`) on AArch64: Kraken's interpreter down to the reads and
writes of the machine state, and (tagged where they are stated) the accesses to the operand forms
`zr`, `xzr` and `sp` in terms of `Reg64s.getXReg` and `Reg64s.setXReg`. -/

attribute [step_simp] Directive.interp Instr.interp Operation.interp ConstExpr.interp
  ConstExpr.evalBranchTarget ExtOrImmReg.interp ShiftRegExpr.interp AddrOrLit.interpLoad
  AddrExpr.interpLoad AddrExpr.interpStore AddrExpr.checkSPAlignment AddrExpr.eval Effects.All
  MachineData.setRegOrZr MachineData.setRegOrSp

/-- Writing a `w`-register zero-extends. -/
@[step_simp]
theorem setRegOrZr_zr (regs : Reg64s) (d : XReg) (w : RegWidth) (v : BitVec w.bits) :
    regs.setRegOrZr (zr d w) v = regs.setXReg d (v.setWidth 64) := by
  cases w
  · rfl
  · show regs.setXReg d v = _
    simp

/-- Reading a `w`-register truncates. -/
@[step_simp]
theorem getRegOrZr_zr (regs : Reg64s) (r : XReg) (w : RegWidth) :
    regs.getRegOrZr (zr r w) = (regs.getXReg r).toBitVec.setWidth w.bits := by
  simp only [Reg64s.getRegOrZr, Reg64s.getRegOrZr64, RegOrZr.base, BitVec.take]
  ext i
  simp

/-! ## Straight-line code -/

/-- The straight-line code `c` runs from `s` and falls through with `s'`, in every host. -/
def Runs (c : List Directive) (s s' : MachineData) : Prop :=
  ∀ [Host] (k : Nat) (post : @_root_.Post MachineState), c.IsInfixAt Host.prog k →
    Eventually (step1 Host.exe) post ⟨s', Host.addrOf (k + c.length)⟩ →
    Eventually (step1 Host.exe) post ⟨s, Host.addrOf k⟩

theorem Runs.nil (s : MachineData) : Runs [] s s := fun _ _ _ h => h

theorem Runs.append {c₁ c₂ : List Directive} {s₁ s₂ s₃ : MachineData} (h₁ : Runs c₁ s₁ s₂)
    (h₂ : Runs c₂ s₂ s₃) : Runs (c₁ ++ c₂) s₁ s₃ := by
  intro _ k post hk h
  obtain ⟨hk₁, hk₂⟩ := List.IsInfixAt.append hk
  refine h₁ k post hk₁ (h₂ (k + c₁.length) post hk₂ ?_)
  rwa [Nat.add_assoc, ← List.length_append]

/-- One instruction whose outcomes, for every label assignment, are exactly falling through with
`s'` (up to effects that `Effects.All` ignores, such as access checks). -/
theorem Runs.single' {w : RegWidth} {o : Operation w} {s s' : MachineData}
    (ho : ∀ [Labels] (p : Std.Rco Int64) (next : MachineData → Effects)
      (jmp : Int64 → MachineData → Effects) (post : MachineState → Prop),
      (o.interp p s next jmp).All post ↔ (next s').All post) :
    Runs [ins o] s s' := by
  intro _ k post hk h
  refine Host.eventually_of_interp_cps (List.isInfixAt_singleton.mp hk) ?_
  simp only [Directive.interp, Instr.interp, Effects.All]
  exact (ho _ _ _ _).mpr h

/-- One instruction whose effect, for every label assignment, is to fall through with `s'`. -/
theorem Runs.single {w : RegWidth} {o : Operation w} {s s' : MachineData}
    (ho : ∀ [Labels] (p : Std.Rco Int64) (next : MachineData → Effects)
      (jmp : Int64 → MachineData → Effects), o.interp p s next jmp = next s') :
    Runs [ins o] s s' :=
  Runs.single' fun p next jmp _ => by rw [ho]

theorem Runs.cons {w : RegWidth} {o : Operation w} {c : List Directive} {s₁ s₂ s₃ : MachineData}
    (ho : ∀ [Labels] (p : Std.Rco Int64) (next : MachineData → Effects)
      (jmp : Int64 → MachineData → Effects), o.interp p s₁ next jmp = next s₂)
    (h : Runs c s₂ s₃) : Runs (ins o :: c) s₁ s₃ :=
  Runs.append (c₁ := [ins o]) (Runs.single ho) h

/-- Use `Runs` in a step lemma. -/
theorem Runs.eventually [Host] {c : List Directive} {s s' : MachineData} {k : Nat}
    {post : @_root_.Post MachineState} (hr : Runs c s s') (hk : c.IsInfixAt Host.prog k)
    (h : Eventually (step1 Host.exe) post ⟨s', Host.addrOf (k + c.length)⟩) :
    Eventually (step1 Host.exe) post ⟨s, Host.addrOf k⟩ :=
  hr k post hk h

/-! ## Moves and constants -/

theorem runs_mov_reg (d : XReg) (rs : Reg) (s : MachineData) :
    Runs (mov (.reg d) rs) s (wr s d (get s rs)) := by
  refine Runs.single fun p next jmp => ?_
  simp only [step_simp, Reg64s.setRegOrSp, Reg64s.setRegOrSp64]
  congr
  simp [Reg64s.getRegOrSp, RegOrSp.base, BitVec.take]

theorem runs_mov_sp (rs : Reg) (s : MachineData) :
    Runs (mov .SP rs) s { s with regs := { s.regs with SP := UInt64.ofBitVec (get s rs) } } := by
  refine Runs.single fun p next jmp => ?_
  simp only [step_simp, Reg64s.setRegOrSp, Reg64s.setRegOrSp64]
  congr
  simp [Reg64s.getRegOrSp, RegOrSp.base, BitVec.take]

private theorem ofInt_toInt_ofBitVec (x : BitVec 64) : BitVec.ofInt 64 (Int64.ofBitVec x).toInt = x := by
  rw [Int64.toInt, Int64.toBitVec_ofBitVec, BitVec.ofInt_toInt]

theorem runs_movImm (r : XReg) (c : Val) (s : MachineData) : Runs (movImm r c) s (wr s r c) := by
  refine Runs.single fun p next jmp => ?_
  simp only [step_simp, Literal.interpLoad, ofInt_toInt_ofBitVec, BitVec.setWidth_eq]

/-! ## Operands -/

/-- An operand in a register: the code `ca` puts the operand's value in `ra`, clobbering at most
`tmp`; a variable operand is its own register. -/
theorem argIn_runs {a : Arg Reg} {tmp : XReg} {ca : List Directive} {ra : XReg}
    (h : argIn a tmp = some (ca, ra)) (s : MachineData) :
    ∃ s', Runs ca s s' ∧ get s' (.reg ra) = (a.map (get s)).val ∧
      (∀ r, r ≠ .reg tmp → get s' r = get s r) ∧ s'.dmem = s.dmem ∧
      (∀ x, a = .var x → x = .reg ra ∧ ca = []) := by
  match a, h with
  | .var (.reg r), h =>
    simp only [argIn, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨s, Runs.nil s, rfl, fun _ _ => rfl, rfl, fun x hx => by cases hx; exact ⟨rfl, rfl⟩⟩
  | .imm c, h =>
    simp only [argIn, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨_, runs_movImm _ c s, get_wr_same .., fun r hr => get_wr_of_ne _ _ _ _ hr, rfl,
      fun _ hx => by cases hx⟩

/-- Operand values only depend on the registers the operand mentions. -/
theorem Arg.val_map_congr {a : Arg Reg} {s s' : MachineData} (h : ∀ r, r ∈ a.vars → get s' r = get s r) :
    (a.map (get s')).val = (a.map (get s)).val := by
  cases a with
  | var r => exact h r (by simp [Arg.vars])
  | imm c => rfl

/-- `rd` is not `x16` or `x17`, and not `r`. -/
theorem not_mem_rd_scratch {r : Reg} {d : XReg} (h : r ∉ .reg d :: scratch) :
    r ≠ .reg d ∧ r ≠ .reg .X16 ∧ r ≠ .reg .X17 := by
  simpa [scratch] using h

/-! ## Loads and stores -/

/-- Bitwise equality of truncations and extensions of 64-bit values. -/
local macro "ext_bits" : tactic => `(tactic| (
  ext j hj
  simp [BitVec.getLsbD_signExtend, BitVec.getLsbD_setWidth, BitVec.msb_setWidth]
  all_goals (by_cases h1 : j < 8 <;> by_cases h2 : j < 16 <;> by_cases h3 : j < 32 <;>
    simp [h1, h2, h3] <;> omega)))

theorem atReg_addr (s : MachineData) (a : XReg) :
    BitVec.ofInt 64 ((s.regs.getRegOrSp (.low (.reg a) .W64)).signed + Int64.toInt 0) =
      get s (.reg a) := by
  simp [BitVec.signed, get_reg]

private theorem ofInt_eq_setWidth {n : Nat} (hn : n = 8 ∨ n = 16 ∨ n = 32) (i : Int) :
    BitVec.ofInt n i = (BitVec.ofInt 64 i).setWidth n := by
  apply BitVec.eq_of_toNat_eq
  rcases hn with rfl | rfl | rfl <;> simp only [BitVec.toNat_ofInt, BitVec.toNat_setWidth] <;> omega

private theorem next_wr_congr {next : MachineData → Effects} {post : MachineState → Prop}
    {s : MachineData} {d : XReg} {A B : Val} (h : A = B) :
    (next { s with regs := s.regs.setXReg d A }).All post ↔
      (next { s with regs := s.regs.setXReg d B }).All post := by
  rw [h]

set_option linter.unusedSimpArgs false in
theorem loadIns_runs (k : Cls) (sz : Sz) (sg : Bool) (d a : XReg) (s : MachineData) (v : Val)
    (hv : loadVal s.dmem k sz sg (get s (.reg a)) = some v) :
    Runs (loadIns k sz sg d a) s (wr s d v) := by
  simp only [loadVal, Option.map_eq_some_iff] at hv
  obtain ⟨i, hi, rfl⟩ := hv
  cases sz <;> cases sg <;> cases k <;> simp only [Sz.bytes] at hi
  case l.false.w | l.true.w =>
    refine Runs.append (s₂ := wr s d (BitVec.ofInt 64 i)) (Runs.single' fun p next jmp post => ?_)
      (Runs.single fun p next jmp => ?_)
    · simp only [step_simp, MachineData.load, atReg_addr, MemWidth.bytes, hi]
      simp [wr]
    · simp only [step_simp, wr, Reg64s.setXReg_setXReg_same, Reg64s.getXReg_setXReg_same,
      UInt64.toBitVec_ofBitVec, Reg64s.getRegOrZr_xzr, Cls.trunc, Sz.extend, Int64.toInt_zero,
      Int.toNat_zero, BitVec.shiftLeft_zero]
      generalize BitVec.ofInt 64 i = X
      congr 3
      ext_bits
  all_goals
    apply Runs.single'
    intro _ p next jmp post
    simp only [step_simp, MachineData.load, atReg_addr, MemWidth.bytes, hi]
    simp only [MemWidth.bits, widthOf, RegWidth.bits, Cls.trunc, Sz.extend, wr]
    try rw [ofInt_eq_setWidth (by decide) i]
    try (generalize BitVec.ofInt 64 i = X; apply next_wr_congr; ext_bits)

set_option linter.unusedSimpArgs false in
theorem storeIns_runs (sz : Sz) (x a : XReg) (s : MachineData)
    (hok : storeOk s.dmem sz (get s (.reg a))) :
    Runs (storeIns sz x a) s
      { s with dmem := storeMem s.dmem sz (get s (.reg a)) (get s (.reg x)) } := by
  obtain ⟨i, hi⟩ := hok
  have e8 : ∀ y : BitVec 64, (BitVec.setWidth 32 y).take 8 = y.setWidth 8 := fun y => by
    simp only [BitVec.take]; ext_bits
  have e16 : ∀ y : BitVec 64, (BitVec.setWidth 32 y).take 16 = y.setWidth 16 := fun y => by
    simp only [BitVec.take]; ext_bits
  cases sz <;> simp only [Sz.bytes] at hi
  all_goals
    apply Runs.single'
    intro _ p next jmp post
    simp only [step_simp, MachineData.store, atReg_addr, MemWidth.bytes, hi, storeMem]
    simp only [RegWidth.bits, MemWidth.bits, e8, e16, BitVec.setWidth_eq, get_reg]

/-- The `load` snippet. -/
theorem load_runs {k : Cls} {sz : Sz} {sg : Bool} {d : XReg} {a : Arg Reg} {c : List Directive}
    {v : Val} {s : MachineData} (hc : load k sz sg (.reg d) a = some c)
    (hv : loadVal s.dmem k sz sg (a.map (get s)).val = some v) :
    ∃ s', Runs c s s' ∧ get s' (.reg d) = v ∧ (∀ r, r ∉ .reg d :: scratch → get s' r = get s r) ∧
      s'.dmem = s.dmem := by
  simp only [load] at hc
  match ha : argIn a .X16, hc with
  | some (ca, ra), hc =>
    simp only [bind, Option.bind, Option.some.injEq] at hc
    subst hc
    obtain ⟨s₁, hr₁, hget₁, hkeep₁, hmem₁, -⟩ := argIn_runs ha s
    refine ⟨wr s₁ d v, Runs.append hr₁ (loadIns_runs k sz sg d ra s₁ v (by rw [hmem₁, hget₁]; exact hv)),
      get_wr_same .., fun r hr => ?_, hmem₁⟩
    obtain ⟨h1, h2, -⟩ := not_mem_rd_scratch hr
    rw [get_wr_of_ne _ _ _ _ h1, hkeep₁ r h2]

/-- The `store` snippet. -/
theorem store_runs {sz : Sz} {x a : Arg Reg} {c : List Directive} {s : MachineData}
    (hc : store sz x a = some c) (hvars : ∀ r, r ∈ x.vars ++ a.vars → r ∉ scratch)
    (hok : storeOk s.dmem sz (a.map (get s)).val) :
    ∃ s', Runs c s s' ∧ (∀ r, r ∉ scratch → get s' r = get s r) ∧
      s'.dmem = storeMem s.dmem sz (a.map (get s)).val (x.map (get s)).val := by
  simp only [store] at hc
  match hx : argIn x .X17, ha : argIn a .X16, hc with
  | some (cx, rx), some (ca, ra), hc =>
    simp only [bind, Option.bind, Option.some.injEq] at hc
    subst hc
    obtain ⟨s₁, hr₁, hget₁, hkeep₁, hmem₁, hvar₁⟩ := argIn_runs hx s
    obtain ⟨s₂, hr₂, hget₂, hkeep₂, hmem₂, hvar₂⟩ := argIn_runs ha s₁
    have hnot : ∀ r, r ∈ x.vars ++ a.vars → r ≠ .reg .X16 ∧ r ≠ .reg .X17 := fun r hr => by
      simpa [scratch] using hvars r hr
    have ha₁ : (a.map (get s₁)).val = (a.map (get s)).val :=
      Arg.val_map_congr fun r hr => hkeep₁ r (hnot r (List.mem_append_right _ hr)).2
    have hx₂ : get s₂ (.reg rx) = (x.map (get s)).val := by
      cases x with
      | imm cv =>
        have : rx = .X17 := by simp only [argIn, Option.some.injEq, Prod.mk.injEq] at hx; exact hx.2.symm
        subst this
        rw [hkeep₂ _ (by decide), hget₁]
      | var r =>
        obtain ⟨rfl, -⟩ := hvar₁ r rfl
        rw [hkeep₂ _ (hnot _ (by simp [Arg.vars])).1, hget₁]
    refine ⟨_, Runs.append (Runs.append hr₁ hr₂) (storeIns_runs sz rx ra s₂ ?_), fun r hr => ?_, ?_⟩
    · rw [hmem₂, hmem₁, hget₂, ha₁]; exact hok
    · have : r ≠ .reg .X16 ∧ r ≠ .reg .X17 := by simpa [scratch] using hr
      show get s₂ r = get s r
      rw [hkeep₂ r this.1, hkeep₁ r this.2]
    · show storeMem s₂.dmem sz (get s₂ (.reg ra)) (get s₂ (.reg rx)) = _
      rw [hmem₂, hmem₁, hget₂, ha₁, hx₂]

/-! ## Basic snippets -/

theorem get_setSP (s : MachineData) (v : Val) (r : Reg) :
    get { s with regs := { s.regs with SP := UInt64.ofBitVec v } } r = if r = .SP then v else get s r := by
  cases r with
  | SP => simp [get_sp]
  | reg x => simp only [reduceCtorEq, ↓reduceIte, get_reg]; cases x <;> rfl

theorem mov_runs (rd rs : Reg) (s : MachineData) :
    ∃ s', Runs (mov rd rs) s s' ∧ get s' rd = get s rs ∧ (∀ r, r ∉ [rd] → get s' r = get s r) ∧
      s'.dmem = s.dmem := by
  cases rd with
  | reg d =>
    exact ⟨_, runs_mov_reg d rs s, get_wr_same .., fun r hr => get_wr_of_ne _ _ _ _ (by simpa using hr),
      rfl⟩
  | SP =>
    refine ⟨_, runs_mov_sp rs s, by simp [get_setSP], fun r hr => ?_, rfl⟩
    have h : r ≠ .SP := by simpa using hr
    simp [get_setSP, h]

theorem movi_runs (rd : Reg) (c : Val) (s : MachineData) :
    ∃ s', Runs (movi rd c) s s' ∧ get s' rd = c ∧ (∀ r, r ∉ rd :: scratch → get s' r = get s r) ∧
      s'.dmem = s.dmem := by
  cases rd with
  | reg d =>
    exact ⟨_, runs_movImm d c s, get_wr_same .., fun r hr => get_wr_of_ne _ _ _ _
      (not_mem_rd_scratch hr).1, rfl⟩
  | SP =>
    refine ⟨_, Runs.append (runs_movImm .X16 c s) (runs_mov_sp _ _), ?_, fun r hr => ?_, rfl⟩
    · show get { (wr s .X16 c) with
        regs := { (wr s .X16 c).regs with SP := UInt64.ofBitVec (get (wr s .X16 c) (.reg .X16)) } }
        .SP = c
      rw [get_setSP]
      simp
    · have : r ≠ .SP ∧ r ≠ .reg .X16 ∧ r ≠ .reg .X17 := by simpa [scratch] using hr
      show get { (wr s .X16 c) with
        regs := { (wr s .X16 c).regs with SP := UInt64.ofBitVec (get (wr s .X16 c) (.reg .X16)) } }
        r = get s r
      rw [get_setSP]
      simp [this.1, get_wr_of_ne _ _ _ _ this.2.1]

section
variable [Host]

/-- Use a `Runs` fact in continuation form. -/
theorem Runs.spec {c : List Directive} {s : MachineData} {P : MachineData → Prop} {k : Nat}
    {post : @_root_.Post MachineState} (hr : ∃ s', Runs c s s' ∧ P s')
    (hk : c.IsInfixAt Host.prog k)
    (h : ∀ s', P s' → Eventually (step1 Host.exe) post ⟨s', Host.addrOf (k + c.length)⟩) :
    Eventually (step1 Host.exe) post ⟨s, Host.addrOf k⟩ := by
  obtain ⟨s', hr, hp⟩ := hr
  exact hr.eventually hk (h s' hp)

theorem eventually_jmp {k j : Nat} {l : Label} {s : MachineData} {post : @_root_.Post MachineState}
    (hc : (jmp l).IsInfixAt Host.prog k) (hj : Labels.label l = Host.addrOf j)
    (h : Eventually (step1 Host.exe) post ⟨s, Host.addrOf j⟩) :
    Eventually (step1 Host.exe) post ⟨s, Host.addrOf k⟩ := by
  refine Host.eventually_of_interp_cps (List.isInfixAt_singleton.mp hc) ?_
  simp only [step_simp]
  rw [hj]
  exact h

/-- `cbnz w_x, l` -/
theorem eventually_cbnz32 {i j : Nat} {x : XReg} {l : Label} {s : MachineData}
    {post : @_root_.Post MachineState}
    (hi : Host.prog[i]? = some (ins (w := .W32) (.CBNZ (zr x .W32) (.label l))))
    (hj : Labels.label l = Host.addrOf j)
    (h : (Truthy (get s (.reg x)) → Eventually (step1 Host.exe) post ⟨s, Host.addrOf j⟩) ∧
      (¬ Truthy (get s (.reg x)) → Eventually (step1 Host.exe) post ⟨s, Host.addrOf (i + 1)⟩)) :
    Eventually (step1 Host.exe) post ⟨s, Host.addrOf i⟩ := by
  refine Host.eventually_of_interp_cps hi ?_
  simp only [step_simp, hj]
  by_cases ht : Truthy (get s (.reg x))
  · have : ((s.regs.getXReg x).toBitVec.setWidth 32 != 0) = true := by
      simpa [Truthy, get_reg] using ht
    simp only [this, ↓reduceIte, Effects.All]
    exact h.1 ht
  · have : ((s.regs.getXReg x).toBitVec.setWidth 32 != 0) = false := by
      simpa [Truthy, get_reg] using ht
    simp only [this, Bool.false_eq_true, ↓reduceIte, Effects.All]
    exact h.2 ht

theorem eventually_jnz {k j : Nat} {r : Reg} {l : Label} {s : MachineData}
    {post : @_root_.Post MachineState}
    (hc : (jnz r l).IsInfixAt Host.prog k) (hj : Labels.label l = Host.addrOf j)
    (h : ∀ s' : MachineData, (∀ r, r ∉ scratch → get s' r = get s r) → s'.dmem = s.dmem →
      (Truthy (get s r) → Eventually (step1 Host.exe) post ⟨s', Host.addrOf j⟩) ∧
      (¬ Truthy (get s r) →
        Eventually (step1 Host.exe) post ⟨s', Host.addrOf (k + (jnz r l).length)⟩)) :
    Eventually (step1 Host.exe) post ⟨s, Host.addrOf k⟩ := by
  cases r with
  | reg x =>
    exact eventually_cbnz32 (List.isInfixAt_singleton.mp hc) hj (h s (fun _ _ => rfl) rfl)
  | SP =>
    obtain ⟨hmov, hcb⟩ := List.IsInfixAt.append hc
    refine Runs.eventually (runs_mov_reg .X16 .SP s) hmov ?_
    refine eventually_cbnz32 (List.isInfixAt_singleton.mp hcb) hj ?_
    have := h (wr s .X16 (get s .SP)) (fun r hr => get_wr_of_ne _ _ _ _ (by
      intro e; subst e; simp [scratch] at hr)) rfl
    simp only [get_wr_same]
    exact this

theorem eventually_ret {k : Nat} {s : MachineData} {ra : Int64} {post : @_root_.Post MachineState}
    (hc : ret.IsInfixAt Host.prog k) (hra : s.regs.X30 = ra.toUInt64)
    (h : Eventually (step1 Host.exe) post ⟨s, ra⟩) :
    Eventually (step1 Host.exe) post ⟨s, Host.addrOf k⟩ :=
  Host.eventually_ret (List.isInfixAt_singleton.mp hc) hra h

end

end LeanQbe.Arm64
