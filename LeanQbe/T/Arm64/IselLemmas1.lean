module

public import LeanQbe.T.Arm64.Isel
public import LeanQbe.T.OpsLemmas
public import LeanQbe.T.AbiLemmas
public import LeanQbe.T.Logic.MemLemmas

/-!
# AArch64 Scalar Instruction Selection Proofs — Part 1 (`T9`)

Core `Program.wp` / `FallsTo` bridge, scratch framing, move/branch/clearFlags/load/store
`GprTarget` proofs (including arbitrary-64-bit displacements, `.SP` unaligned routing via `.X16`,
bit-0 `TBNZ` ignoring upper `.bool` garbage bits, and `.bool .flag` stores), shared bitfield /
division / carry / borrow / byte-swap arithmetic lemmas, and non-`op` `NoLab` theorems.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64

open LeanQbe.T

/-! ## 1. Framing helpers -/

theorem armFrame_upd_regs {s s' : MachineData} {gClob : List Reg} {fClob : FlagMask}
    (hkeep : ∀ r, r ∉ gClob → get s' r = get s r)
    (hflg : fClob = maskAll ∨ fClob = maskNZCV ∧
      (∀ c, FlagMask.disjoint (armCondReads c) maskNZCV = true → c.interp s'.status = c.interp s.status) ∨
      s'.status = s.status) :
    armMach.Frame armCondReads s s' gClob [] fClob := by
  refine ⟨hkeep, fun v => v.elim, ?_⟩
  rcases hflg with rfl | ⟨rfl, hnzcv⟩ | hst
  · intro c hdisj
    cases c <;> simp [FlagMask.disjoint, armCondReads, maskAll, maskN, maskZ, maskC, maskV] at hdisj
  · exact hnzcv
  · intro c _; simp [hst]

theorem armFrame_nzcv {s s' : MachineData} {gClob : List Reg}
    (hkeep : ∀ r, r ∉ gClob → get s' r = get s r) :
    armMach.Frame armCondReads s s' gClob [] maskNZCV :=
  armFrame_upd_regs hkeep (Or.inr (Or.inl ⟨rfl, fun c hdisj => by
    cases c <;> simp [FlagMask.disjoint, armCondReads, maskNZCV, maskN, maskZ, maskC, maskV] at hdisj⟩))

theorem armFrame_status_eq {s s' : MachineData} {gClob : List Reg} {fClob : FlagMask}
    (hkeep : ∀ r, r ∉ gClob → get s' r = get s r) (hst : s'.status = s.status) :
    armMach.Frame armCondReads s s' gClob [] fClob :=
  armFrame_upd_regs hkeep (Or.inr (Or.inr hst))

theorem xreg_ne_scratch_of_not_mem {x : XReg} (hx : XRegOrSp.reg x ∉ armScratch) :
    x ≠ .X16 ∧ x ≠ .X17 := by
  have ⟨h1, h2⟩ := ne_of_not_mem_armScratch hx
  exact ⟨fun e => h1 (congrArg XRegOrSp.reg e), fun e => h2 (congrArg XRegOrSp.reg e)⟩

theorem frame_wr {s : MachineData} (x : XReg) (v : BitVec 64) {gClob : List Reg}
    (hx : XRegOrSp.reg x ∈ gClob) (fClob : FlagMask) :
    armMach.Frame armCondReads s (wr s x v) gClob [] fClob :=
  armFrame_status_eq (fun r hr => get_wr_of_ne s x v r fun e => hr (e ▸ hx)) rfl

theorem frame_setStatus {s : MachineData} (st : StatusFlags) (gClob : List Reg) :
    armMach.Frame armCondReads s { s with status := st } gClob [] maskNZCV :=
  armFrame_nzcv fun _ _ => rfl

/-! ## 2. Low-level directive `Program.wp` builders & operand materialization -/

@[t_step_simp]
theorem Reg64s_getXReg_setXReg_of_ne' (regs : Reg64s) (a b : XReg) (v : BitVec 64)
    (h : a ≠ b) : (regs.setXReg a v).getXReg b = regs.getXReg b :=
  Reg64s.getXReg_setXReg_of_ne regs a b v h

theorem armCset64_wp [Host] (d : XReg) (c : ArmCond) (s : MachineData) :
    _root_.Program.wp [armCset64 d c]
      (fun s' => s' = wr s d (BitVec.ofNat 64 (c.interp s.status).toNat))
      (fun _ _ => False) s := by
  refine armDirFallsTo_wp (by
    intro _ p next jmp P hk
    simp only [t_step_simp]
    rw [show (armNegCond c).toKraken.interp s.status = !(c.interp s.status) from
      armNegCond_interp c s.status]
    cases hc : c.interp s.status
    · simp only [Bool.not_false, ↓reduceIte, BitVec.setWidth_eq]
      exact hk _ (by simp [wr, hc])
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, BitVec.setWidth_eq]
      exact hk _ (by simp [wr, hc]))

theorem armImm12_some {n : Nat} {c : BitVec n} {ei : ExtOrImmReg}
    (_hn : n ≤ 64) (h : armImm12? c = some ei) :
    ei = .imm { imm := .int64 (Int64.ofNat c.toNat), shift := .S0 } ∧
      c.toNat < 4096 ∧
      ∀ w : RegWidth, ∀ [Labels] (p : Std.Rco Int64) (regs : Reg64s),
        ExtOrImmReg.interp (w := w) ei regs p = (c.setWidth n).setWidth w.bits := by
  dsimp only [armImm12?] at h
  split at h
  · rename_i hlt
    have hlt' : c.toNat < 4096 := Nat.blt_eq.mp hlt
    rcases Option.some.inj h with rfl
    refine ⟨rfl, hlt', fun w _ p regs => ?_⟩
    simp only [ExtOrImmReg.interp, ConstExpr.interp, BitVec.setWidth_eq]
    rw [Int64.toInt_ofNat_of_lt (by omega : c.toNat < 2 ^ 63), BitVec.ofInt_natCast]
    apply BitVec.eq_of_toNat_eq
    simp
  · cases h

theorem armArgIn_wp [Host] {n : Nat} (hn : n ≤ 64) {tmp : XReg} {pa : PArg Reg Empty ArmCond (.bits n)}
    {v : BitVec n} {s : MachineData} {ca : List Instr} {ra : XReg}
    (ha : armArgInIns tmp pa = some (ca, ra)) (hp : armMach.PArgHolds s (.bits n) pa v) :
    _root_.Program.wp (emitClean ca) (fun s' =>
      (s'.regs.getXReg ra).toBitVec.setWidth n = v ∧
      s'.dmem = s.dmem ∧ s'.status = s.status ∧
      armMach.Frame armCondReads s s' [.reg tmp] [] maskNone) (fun _ _ => False) s := by
  cases pa with
  | vec vr => exact vr.elim
  | gpr r =>
    cases r with
    | SP => simp [armArgInIns] at ha
    | reg x =>
      simp only [armArgInIns, Option.some.injEq, Prod.mk.injEq] at ha
      rcases ha with ⟨rfl, rfl⟩
      refine armWp_nil ⟨?_, rfl, rfl, Machine.Frame.refl (M := armMach) armCondReads s [.reg tmp] [] maskNone⟩
      simpa [Machine.PArgHolds, GprHolds, armMach, get_reg] using hp.2
  | imm c =>
    simp only [armArgInIns, Option.some.injEq, Prod.mk.injEq] at ha
    rcases ha with ⟨rfl, rfl⟩
    simp only [Machine.PArgHolds] at hp
    simp only [emitClean_cons, emitClean_nil]
    refine armWp_mono (armLdrPoolBv_wp tmp (c.setWidth 64) s) ?_
    rintro s' rfl
    refine ⟨?_, rfl, rfl, frame_wr tmp (c.setWidth 64) List.mem_cons_self maskNone⟩
    rw [← get_reg, get_wr_same, BitVec.setWidth_setWidth_of_le _ hn, BitVec.setWidth_eq, hp]

theorem armBoolArgIn_wp [Host] {tmp : XReg} {pa : PArg Reg Empty ArmCond .bool}
    {b : Bool} {s : MachineData} {ca : List Instr} {ra : XReg}
    (ha : armBoolArgInIns tmp pa = some (ca, ra)) (hp : armMach.PArgHolds s .bool pa b) :
    _root_.Program.wp (emitClean ca) (fun s' =>
      (s'.regs.getXReg ra).toBitVec.setWidth 8 = BitVec.ofNat 8 b.toNat ∧
      s'.dmem = s.dmem ∧ s'.status = s.status ∧
      armMach.Frame armCondReads s s' [.reg tmp] [] maskNone) (fun _ _ => False) s := by
  cases pa with
  | vec vr => exact vr.elim
  | gpr r =>
    cases r with
    | SP => simp [armBoolArgInIns] at ha
    | reg x =>
      simp only [armBoolArgInIns, Option.some.injEq, Prod.mk.injEq] at ha
      rcases ha with ⟨rfl, rfl⟩
      refine armWp_nil ⟨?_, rfl, rfl, Machine.Frame.refl (M := armMach) armCondReads s [.reg tmp] [] maskNone⟩
      simpa [Machine.PArgHolds, GprHolds, armMach, get_reg] using hp
  | imm cv =>
    simp only [armBoolArgInIns, Option.some.injEq, Prod.mk.injEq] at ha
    rcases ha with ⟨rfl, rfl⟩
    simp only [Machine.PArgHolds] at hp
    subst hp
    simp only [emitClean_cons, emitClean_nil]
    refine armWp_mono (armLdrPoolBv_wp tmp (BitVec.ofNat 64 cv.toNat) s) ?_
    rintro s' rfl
    refine ⟨?_, rfl, rfl, frame_wr tmp _ List.mem_cons_self maskNone⟩
    rw [← get_reg, get_wr_same]
    cases cv <;> rfl
  | flag cond =>
    simp only [armBoolArgInIns, Option.some.injEq, Prod.mk.injEq] at ha
    rcases ha with ⟨rfl, rfl⟩
    simp only [Machine.PArgHolds] at hp
    simp only [emitClean_cons, emitClean_nil]
    refine armWp_mono (armCset64_wp tmp cond s) ?_
    rintro s' rfl
    refine ⟨?_, rfl, rfl, frame_wr tmp _ List.mem_cons_self maskNone⟩
    rw [← get_reg, get_wr_same, hp]
    cases b <;> rfl

/-! ## 3. Non-`op` `GprTarget` specs (`clearFlags`, `mov`, `movi`, `setcc`, `jmp`, `jcc`, `jnzGpr`, `load`, `store`) -/

theorem armClearFlags_spec {h : Host} {k : Nat} {s : MachineData} {post : MachineState → Prop} :
    armMach.FallsTo armCondReads h k armClearFlags armScratch [] FlagMask.all s
      (fun s' => (∀ c ∈ armZeroFlags, armMach.evalCond s' c = false) ∧ s'.dmem = s.dmem) post := by
  letI := h
  refine armFallsTo_of_wp (armWp_mono (armDirFallsTo_wp (by
    intro _ p next jmp P hk
    simp only [t_step_simp, Reg64s.setRegOrZr_xzr]
    exact hk _ rfl)) ?_)
  rintro s' rfl
  refine ⟨⟨?_, rfl⟩, armFrame_upd_regs (fun _ _ => rfl) (Or.inl rfl)⟩
  intro c hc
  simp only [armZeroFlags, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> simp [ArmCond.interp, ArmCond.toKraken,
    StatusFlags.adds, StatusFlags.from_result, BitVec.unsigned, BitVec.signed]

theorem armMov_spec {h : Host} {k : Nat} {rd rs : Reg} {s : MachineData}
    {post : MachineState → Prop} :
    armMach.FallsTo armCondReads h k (armMov rd rs) [rd] [] FlagMask.none s
      (fun s' => armMach.getGpr s' rd = armMach.getGpr s rs ∧ s'.dmem = s.dmem) post := by
  letI := h
  refine armFallsTo_of_wp (armWp_mono (armDirFallsTo_wp (by
    intro _ p next jmp P hk
    simp only [t_step_simp, imm0, Int64.toInt_zero]
    rw [show BitVec.ofInt RegWidth.W64.bits 0 = 0#64 from rfl, BitVec.add_zero]
    exact hk _ rfl)) ?_)
  rintro s' rfl
  refine ⟨⟨?_, rfl⟩, armFrame_status_eq (fun r hr => ?_) rfl⟩
  · cases rd <;> cases rs <;>
      simp [get_reg, get_sp, Reg64s.setRegOrSp, Reg64s.setRegOrSp64,
        Reg64s.getRegOrSp_reg64, Reg64s.getRegOrSp_sp64]
  · have hne : r ≠ rd := fun e => hr (e ▸ List.mem_cons_self)
    cases rd with
    | SP =>
      cases r with
      | SP => exact absurd rfl hne
      | reg xr => rfl
    | reg xd =>
      cases r with
      | SP => simp [get_sp, Reg64s.setRegOrSp, Reg64s.setRegOrSp64]
      | reg xr =>
        have hx : xd ≠ xr := fun e => hne (congrArg XRegOrSp.reg e.symm)
        simp [get_reg, Reg64s.setRegOrSp, Reg64s.setRegOrSp64, hx]

theorem armMovi_spec {h : Host} {k : Nat} {rd : Reg} {c : BitVec 64} {s : MachineData}
    {post : MachineState → Prop} :
    armMach.FallsTo armCondReads h k (armMovi rd c) (rd :: armScratch) [] FlagMask.none s
      (fun s' => armMach.getGpr s' rd = c ∧ s'.dmem = s.dmem) post := by
  letI := h
  refine armFallsTo_of_wp ?_
  cases rd with
  | reg d =>
    refine armWp_mono (armLdrPoolBv_wp d c s) ?_
    rintro s' rfl
    exact ⟨⟨get_wr_same s d c, rfl⟩, frame_wr d c List.mem_cons_self FlagMask.none⟩
  | SP =>
    refine armWp_cons (armLdrPoolBv_wp .X16 c s) ?_
    rintro s₁ rfl
    refine armWp_mono (armMovToSp_wp .X16 (wr s .X16 c)) ?_
    rintro s' rfl
    refine ⟨⟨by simp [get_sp, get_wr_same], rfl⟩, armFrame_status_eq (fun r hr => ?_) rfl⟩
    simp only [List.mem_cons, armScratch, List.not_mem_nil, or_false, not_or] at hr
    cases r with
    | SP => exact absurd rfl hr.1
    | reg xr =>
      have hx : .X16 ≠ xr := fun e => hr.2.1 (congrArg XRegOrSp.reg e.symm)
      simp only [get_reg]
      exact congrArg UInt64.toBitVec (Reg64s.getXReg_setXReg_of_ne s.regs .X16 xr c hx)

theorem armSetcc_spec {h : Host} {k : Nat} {rd : Reg} {c : ArmCond} {s : MachineData}
    {post : MachineState → Prop} (_ : rd ∉ armScratch) :
    armMach.FallsTo armCondReads h k (armSetcc rd c) (rd :: armScratch) [] FlagMask.none s
      (fun s' => GprHolds (armMach.getGpr s' rd) .bool (armMach.evalCond s c) ∧ s'.dmem = s.dmem)
      post := by
  letI := h
  refine armFallsTo_of_wp ?_
  cases rd with
  | reg d =>
    refine armWp_mono (armCset64_wp d c s) ?_
    rintro s' rfl
    refine ⟨⟨?_, rfl⟩, frame_wr d _ List.mem_cons_self FlagMask.none⟩
    dsimp only [armMach]
    rw [get_wr_same]
    cases c.interp s.status <;> rfl
  | SP =>
    refine armWp_cons (armCset64_wp .X16 c s) ?_
    rintro s₁ rfl
    refine armWp_mono (armMovToSp_wp .X16 (wr s .X16 _)) ?_
    rintro s' rfl
    refine ⟨⟨?_, rfl⟩, armFrame_status_eq (fun r hr => ?_) rfl⟩
    · simp only [get_sp, get_wr_same, GprHolds]
      cases c.interp s.status <;> rfl
    · simp only [List.mem_cons, armScratch, List.not_mem_nil, or_false, not_or] at hr
      cases r with
      | SP => exact absurd rfl hr.1
      | reg xr =>
        have hx : .X16 ≠ xr := fun e => hr.2.1 (congrArg XRegOrSp.reg e.symm)
        simp only [get_reg]
        exact congrArg UInt64.toBitVec (Reg64s.getXReg_setXReg_of_ne s.regs .X16 xr _ hx)

theorem armJmp_spec {h : Host} {k j : Nat} {l : Sym} {s : MachineData}
    {post : MachineState → Prop}
    (hc : (armJmp l).IsInfixAt (armMach.prog h) k)
    (hl : armMach.labelAddr h l = armMach.addrOf h j)
    (hk : ∀ s', armMach.Frame armCondReads s s' armScratch [] FlagMask.none →
      s'.dmem = s.dmem → armMach.Run h j s' post) :
    armMach.Run h k s post := by
  letI := h
  refine Host.eventually_of_interp_cps (List.isInfixAt_singleton.mp hc) ?_
  simp only [t_step_simp]
  have hl' : Labels.label l = Host.addrOf j := hl
  rw [hl']
  exact hk s (Machine.Frame.refl (M := armMach) armCondReads s armScratch [] FlagMask.none) rfl

theorem armJcc_spec {h : Host} {k j : Nat} {c : ArmCond} {l : Sym} {s : MachineData}
    {post : MachineState → Prop}
    (hc : (armJcc c l).IsInfixAt (armMach.prog h) k)
    (hl : armMach.labelAddr h l = armMach.addrOf h j)
    (hk : ∀ s', armMach.Frame armCondReads s s' armScratch [] FlagMask.none →
      s'.dmem = s.dmem →
      (armMach.evalCond s c = true → armMach.Run h j s' post) ∧
      (armMach.evalCond s c = false → armMach.Run h (k + (armJcc c l).length) s' post)) :
    armMach.Run h k s post := by
  letI := h
  refine Host.eventually_of_interp_cps (List.isInfixAt_singleton.mp hc) ?_
  simp only [t_step_simp]
  have hrun := hk s (Machine.Frame.refl (M := armMach) armCondReads s armScratch [] FlagMask.none) rfl
  have hl' : Labels.label l = Host.addrOf j := hl
  cases hev : c.interp s.status
  · simp only [hev, Bool.false_eq_true, ↓reduceIte, Effects.All]
    exact hrun.2 hev
  · simp only [hev, ↓reduceIte, Effects.All]
    rw [hl']
    exact hrun.1 hev

private theorem bool_getLsbD_zero {v : BitVec 64} {b : Bool}
    (hb : GprHolds v .bool b) : (v.setWidth 32).getLsbD 0 = b := by
  simp only [GprHolds] at hb
  have h0 : (v.setWidth 32).getLsbD 0 = (v.setWidth 8).getLsbD 0 := by simp
  rw [h0, hb]
  cases b <;> decide

theorem armJnzGpr_spec {h : Host} {k j : Nat} {r : Reg} {l : Sym} {b : Bool} {s : MachineData}
    {post : MachineState → Prop}
    (hc : (armJnzGpr r l).1.IsInfixAt (armMach.prog h) k)
    (hl : armMach.labelAddr h l = armMach.addrOf h j)
    (_ : r ∉ armScratch) (hb : GprHolds (armMach.getGpr s r) .bool b)
    (hk : ∀ s', armMach.Frame armCondReads s s' armScratch [] (armJnzGpr r l).2 →
      s'.dmem = s.dmem →
      (b = true → armMach.Run h j s' post) ∧
      (b = false → armMach.Run h (k + (armJnzGpr r l).1.length) s' post)) :
    armMach.Run h k s post := by
  letI := h
  have hl' : Labels.label l = Host.addrOf j := hl
  cases r with
  | reg x =>
    refine Host.eventually_of_interp_cps (List.isInfixAt_singleton.mp hc) ?_
    simp only [t_step_simp]
    have hbit : ((s.regs.getXReg x).toBitVec.setWidth 32).getLsbD 0 = b :=
      bool_getLsbD_zero (by simpa [armMach, get_reg] using hb)
    have hrun := hk s (Machine.Frame.refl (M := armMach) armCondReads s armScratch [] maskNone) rfl
    cases b
    · simp only [hbit]; exact hrun.2 rfl
    · simp only [hbit]; rw [hl']; exact hrun.1 rfl
  | SP =>
    dsimp only [armJnzGpr, armJnzGprIns] at hc
    simp only [emitClean_cons, emitClean_nil] at hc
    rw [show [armMovToX .X16 .SP, ins (.TBNZ (zr .X16 .W32) 0 (.label l))] =
      [armMovToX .X16 .SP] ++ [ins (.TBNZ (zr .X16 .W32) 0 (.label l))] from rfl] at hc
    have hpair := hc.append
    have hrun1 : @Program.wp h [armMovToX .X16 .SP] (fun s' => s' = wr s .X16 (get s .SP))
        (fun _ _ => False) s := armMovToX_wp .X16 .SP s
    refine eventually_trans _ _ _ _ (hrun1 k hpair.1) ?_
    rintro ⟨s₁, a⟩ (⟨ha, rfl⟩ | hf)
    · dsimp only at ha; subst ha
      refine Host.eventually_of_interp_cps (List.isInfixAt_singleton.mp hpair.2) ?_
      simp only [t_step_simp]
      have hbit : (((wr s .X16 (get s .SP)).regs.getXReg .X16).toBitVec.setWidth 32).getLsbD 0 = b := by
        rw [← get_reg, get_wr_same]; exact bool_getLsbD_zero hb
      have hfr : armMach.Frame armCondReads s (wr s .X16 (get s .SP)) armScratch []
          (armJnzGpr .SP l).2 :=
        frame_wr .X16 (get s .SP) List.mem_cons_self maskNone
      have hrun := hk _ hfr rfl
      dsimp only [armMach, Machine.Run, armJnzGpr, List.length_cons, List.length_nil] at hrun
      cases b
      · simp only [hbit]
        exact hrun.2 rfl
      · simp only [hbit]; rw [hl']; exact hrun.1 rfl
    · exact False.elim hf

private theorem armAtDisp_eval [Labels] (s : MachineData) (rb : XReg) (disp : Int64) (p : Std.Rco Int64) :
    (armAtDisp rb disp).eval s p = ((s.regs.getXReg rb).toBitVec + disp.toBitVec, s) := by
  simp only [AddrExpr.eval, ConstExpr.interp, Reg64s.getRegOrSp_reg64, BitVec.signed,
    BitVec.ofInt_add]
  rw [← Int64.toInt_toBitVec]
  simp

private theorem armAtIdx_eval [Labels] (s : MachineData) (rb idx : XReg) (p : Std.Rco Int64) :
    (armAtIdx rb idx).eval s p = ((s.regs.getXReg rb).toBitVec + (s.regs.getXReg idx).toBitVec, s) := by
  simp only [AddrExpr.eval, MemExtRegExpr.interp, BitVec.apply_mem_extend,
    Reg64s.getRegOrSp_reg64, Reg64s.getRegOrZr64, RegOrZr.base, BitVec.signed]
  exact congrArg (·, s) (ofInt_toInt_add_toNat _ _)

private theorem armAtReg_eval [Labels] (s : MachineData) (rb : XReg) (p : Std.Rco Int64) :
    (atReg rb).eval s p = ((s.regs.getXReg rb).toBitVec, s) := by
  simp only [AddrExpr.eval, ConstExpr.interp, Int64.toInt_zero, Reg64s.getRegOrSp_reg64,
    BitVec.signed, Int.add_zero, BitVec.ofInt_toInt]

theorem armSetupAddr_wp [Host] (scale : Nat) (a : AddrArg Reg) (s : MachineData)
    (haregs : ∀ r ∈ a.regs, r ∉ armScratch)
    (hva : armAddrValid a = true) :
    let (setup, addr) := armSetupAddrIns scale a
    (∃ rx, addr.base = .low (.reg rx) .W64) ∧
    _root_.Program.wp (emitClean setup) (fun s' =>
      (∀ [Labels] p, addr.eval s' p = (a.eval (get s), s')) ∧
      (∀ x, x ≠ .X16 → s'.regs.getXReg x = s.regs.getXReg x) ∧
      s'.regs.SP = s.regs.SP ∧ s'.dmem = s.dmem ∧ s'.status = s.status ∧
      armMach.Frame armCondReads s s' [.reg .X16] [] maskNone) (fun _ _ => False) s := by
  cases a with
  | baseIdxDisp _ _ _ _ => simp [armAddrValid] at hva
  | imm addr =>
    simp only [armSetupAddrIns, emitClean_cons, emitClean_nil]
    refine ⟨⟨.X16, rfl⟩, armWp_mono (armLdrPoolBv_wp .X16 addr s) ?_⟩
    rintro s' rfl
    refine ⟨by intro _ p; rw [armAtReg_eval, ← get_reg, get_wr_same, AddrArg.eval],
      fun x hx => Reg64s.getXReg_setXReg_of_ne _ _ _ _ hx.symm, rfl, rfl, rfl,
      frame_wr .X16 addr List.mem_cons_self maskNone⟩
  | baseDisp base disp =>
    cases base with
    | reg rb =>
      have hrb16 : rb ≠ .X16 := fun h => haregs (.reg rb) (by simp [AddrArg.regs]) (by simp [h, armScratch])
      dsimp only [armSetupAddrIns]
      split
      · rename_i h0
        have hd : disp.toBitVec = 0#64 := by
          have := beq_iff_eq.mp h0; subst this; rfl
        refine ⟨⟨rb, rfl⟩, armWp_nil ⟨by intro _ p; rw [armAtReg_eval, AddrArg.eval, hd, BitVec.add_zero, get_reg],
          fun _ _ => rfl, rfl, rfl, rfl,
          Machine.Frame.refl (M := armMach) armCondReads s [.reg .X16] [] maskNone⟩⟩
      · split
        · refine ⟨⟨rb, rfl⟩, armWp_nil ⟨by intro _ p; rw [armAtDisp_eval, AddrArg.eval, get_reg],
            fun _ _ => rfl, rfl, rfl, rfl,
            Machine.Frame.refl (M := armMach) armCondReads s [.reg .X16] [] maskNone⟩⟩
        · simp only [emitClean_cons, emitClean_nil]
          refine ⟨⟨rb, rfl⟩, armWp_mono (armLdrPoolBv_wp .X16 disp.toBitVec s) ?_⟩
          rintro s' rfl
          refine ⟨by
              intro _ p
              rw [armAtIdx_eval, AddrArg.eval, get_reg, Reg64s.getXReg_setXReg_of_ne _ _ _ _ hrb16.symm,
                Reg64s.getXReg_setXReg_same],
            fun x hx => Reg64s.getXReg_setXReg_of_ne _ _ _ _ hx.symm,
            rfl, rfl, rfl, frame_wr .X16 _ List.mem_cons_self maskNone⟩
    | SP =>
      dsimp only [armSetupAddrIns]
      split
      · rename_i h0
        have hd : disp.toBitVec = 0#64 := by
          have := beq_iff_eq.mp h0; subst this; rfl
        simp only [emitClean_cons, emitClean_nil]
        refine ⟨⟨.X16, rfl⟩, armWp_mono (armMovToX_wp .X16 .SP s) ?_⟩
        rintro s' rfl
        refine ⟨by intro _ p; rw [armAtReg_eval, AddrArg.eval, hd, BitVec.add_zero, ← get_reg, get_wr_same],
          fun x hx => Reg64s.getXReg_setXReg_of_ne _ _ _ _ hx.symm,
          rfl, rfl, rfl, frame_wr .X16 (get s .SP) List.mem_cons_self maskNone⟩
      · split
        · simp only [emitClean_cons, emitClean_nil]
          refine ⟨⟨.X16, rfl⟩, armWp_mono (armDirFallsTo_wp (by
            intro _ p next jmp P hk
            simp only [t_step_simp, Reg64s.setRegOrSp, Reg64s.setRegOrSp64,
              Reg64s.getRegOrSp_sp64, ConstExpr.interp, RegWidth.bits]
            rw [← Int64.toInt_toBitVec, BitVec.ofInt_toInt]
            exact hk _ rfl)) ?_⟩
          rintro s' rfl
          refine ⟨by
              intro _ p
              simp only [armAtReg_eval, AddrArg.eval, get_sp, Reg64s.getXReg_setXReg_same],
            fun x hx => Reg64s.getXReg_setXReg_of_ne _ _ _ _ hx.symm,
            rfl, rfl, rfl, frame_wr .X16 _ List.mem_cons_self maskNone⟩
        · simp only [emitClean_cons, emitClean_nil]
          refine ⟨⟨.X16, rfl⟩, armWp_cons (armLdrPoolBv_wp .X16 disp.toBitVec s) ?_⟩
          rintro s₁ rfl
          refine armWp_mono (armDirFallsTo_wp (by
            intro _ p next jmp P hk
            simp only [t_step_simp, ExtRegExpr.interp, BitVec.apply_extend,
              Reg64s.setRegOrSp, Reg64s.setRegOrSp64, Reg64s.getRegOrSp_sp64, RegWidth.bits,
              Reg64s.getRegOrZr64, RegOrZr.base, BitVec.unsigned]
            rw [Reg64s.getXReg_setXReg_same, BitVec.ofInt_natCast, BitVec.ofNat_toNat]
            exact hk _ rfl)) ?_
          rintro s' rfl
          refine ⟨by
              intro _ p
              simp only [armAtReg_eval, AddrArg.eval, get_sp, Reg64s.getXReg_setXReg_same]
              rfl,
            fun x hx => by
              rw [Reg64s.getXReg_setXReg_of_ne _ _ _ _ hx.symm,
                Reg64s.getXReg_setXReg_of_ne _ _ _ _ hx.symm],
            rfl, rfl, rfl, frame_wr .X16 _ List.mem_cons_self maskNone⟩

private theorem zeroExtend_setWidth_low {k m : Nat} (hk : k ≤ m) (hk64 : k ≤ 64) (v : BitVec k) :
    ((v.zeroExtend m).setWidth 64).setWidth k = v := by
  rw [BitVec.zeroExtend, BitVec.setWidth_setWidth_of_le _ hk64,
    BitVec.setWidth_setWidth_of_le _ hk, BitVec.setWidth_eq]

private theorem Reg64s_getXReg_setSP' (regs : Reg64s) (v : UInt64) (x : XReg) :
    ({ regs with SP := v } : Reg64s).getXReg x = regs.getXReg x := by
  cases x <;> rfl

private theorem armLoadDir_wp [Host] {t : Ty} {d : XReg} {addr : AddrExpr} {a : BitVec 64}
    {v : Val t} {s : MachineData} {dir : Instr}
    (hdir : armLoadDirI t d addr = some dir) (hnoSp : ∃ rx, addr.base = .low (.reg rx) .W64)
    (heval : ∀ [Labels] p, addr.eval s p = (a, s)) (hload : loadVal s.dmem t a = some v) :
    _root_.Program.wp [.instr dir] (fun s' =>
      ∃ w64 : BitVec 64, s' = wr s d w64 ∧ GprHolds w64 t v) (fun _ _ => False) s := by
  obtain ⟨rx, hrx⟩ := hnoSp
  simp only [loadVal, Option.bind_eq_some_iff] at hload
  rcases hload with ⟨i, hi, hv⟩
  cases t with
  | bool =>
    simp only [armLoadDirI, Option.some.injEq] at hdir; subst hdir
    simp only [Ty.bytes, Ty.size] at hi
    cases hb : (i == 0 || i == 1) <;> simp only [hb, Bool.false_eq_true, ↓reduceIte,
      Option.some.injEq, reduceCtorEq] at hv
    subst hv
    refine armDirFallsTo_wp (by
      intro _ p next jmp P hk
      simp only [Directive.interp, Instr.interp, Operation.interp, AddrExpr.interpLoad,
        AddrExpr.checkSPAlignment, hrx, heval p, MachineData.load, MemWidth.bytes, hi,
        MachineData.setRegOrZr, setRegOrZr_zr, MemWidth.bits, RegWidth.bits, Effects.All]
      refine hk _ ⟨_, rfl, ?_⟩
      simp only [Bool.or_eq_true, beq_iff_eq] at hb
      simp only [GprHolds, zeroExtend_setWidth_low (by decide : 8 ≤ 32) (by decide)]
      rcases hb with rfl | rfl <;> decide)
  | bits n =>
    have hns : (n = 8 ∨ n = 16) ∨ (n = 32 ∨ n = 64) := by
      rcases (by omega : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64 ∨ (n ≠ 8 ∧ n ≠ 16 ∧ n ≠ 32 ∧ n ≠ 64))
        with h | h | h | h | ⟨h1, h2, h3, h4⟩
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr h)
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
      · exfalso; revert hdir; simp [armLoadDirI, h1, h2, h3, h4]
    rcases hns with (rfl | rfl) | (rfl | rfl) <;>
      (simp only [armLoadDirI, Option.some.injEq] at hdir; subst hdir;
       simp only [Ty.bytes, Ty.size, ofBits, Option.some.injEq] at hi hv; subst hv;
       refine armDirFallsTo_wp (by
         intro _ p next jmp P hk
         simp only [Directive.interp, Instr.interp, Operation.interp]
         try simp only [AddrOrLit.interpLoad]
         simp only [AddrExpr.interpLoad, AddrExpr.checkSPAlignment, hrx, heval p,
           MachineData.load, MemWidth.bytes, hi, MachineData.setRegOrZr, setRegOrZr_zr,
           MemWidth.bits, Effects.All]
         refine hk _ ⟨_, rfl, by decide, ?_⟩
         first
         | exact zeroExtend_setWidth_low (by decide : _ ≤ 32) (by decide) _
         | simp))
  | float _ | pair _ _ => simp [armLoadDirI] at hdir

theorem armLoad_spec {h : Host} {k : Nat} {t : Ty} {rd : Reg} {a : AddrArg Reg}
    {c : List Directive} {clob : FlagMask} {v : Val t} {s : MachineData} {post : MachineState → Prop}
    (hc_in : armLoad t rd a = some (c, clob)) (_ : rd ∉ armScratch)
    (haregs : ∀ r ∈ a.regs, r ∉ armScratch) (hv : loadVal (armMach.mem s) t (a.eval (get s)) = some v) :
    armMach.FallsTo armCondReads h k c (rd :: armScratch) [] clob s
      (fun s' => GprHolds (armMach.getGpr s' rd) t v ∧ armMach.mem s' = armMach.mem s) post := by
  letI := h
  obtain ⟨ci, hc, rfl⟩ := emitCleanPair_eq_some.mp hc_in
  have hva : armAddrValid a = true := by
    cases a with
    | imm _ | baseDisp _ _ => rfl
    | baseIdxDisp _ _ _ _ =>
      dsimp only [armLoadIns, armAddrValid] at hc
      contradiction
  dsimp only [armLoadIns] at hc
  rw [show (!armAddrValid a) = false by simp [hva]] at hc
  simp only [Bool.false_eq_true, ↓reduceIte, bind, Option.bind_eq_some_iff] at hc
  rcases hc with ⟨scale, _, hrest⟩
  have hsetup := armSetupAddr_wp scale a s haregs hva
  generalize armSetupAddrIns scale a = sa at hrest hsetup
  rcases sa with ⟨setup, addr⟩
  rcases hsetup with ⟨hnoSp, hwpSetup⟩
  cases rd with
  | reg d =>
    simp only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at hrest
    rcases hrest with ⟨dir, hdir, rfl, rfl⟩
    simp only [emitClean_append, emitClean_cons, emitClean_nil]
    refine armFallsTo_of_wp (armWp_append hwpSetup ?_)
    rintro s₁ ⟨heval, _, _, hdmem₁, hst₁, hfr₁⟩
    refine armWp_mono (armLoadDir_wp hdir hnoSp heval (by simpa [armMach, hdmem₁] using hv)) ?_
    rintro s₂ ⟨w64, rfl, hw64⟩
    refine ⟨⟨by simpa [armMach, get_wr_same] using hw64, hdmem₁⟩, armFrame_status_eq ?_ hst₁⟩
    intro r hr
    have hnd : r ≠ .reg d := fun e => hr (e ▸ List.mem_cons_self)
    rw [get_wr_of_ne s₁ d w64 r hnd]
    exact hfr₁.1 r fun h16 => hr (by simp at h16; subst h16; simp [armScratch])
  | SP =>
    simp only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at hrest
    rcases hrest with ⟨dir, hdir, rfl, rfl⟩
    simp only [emitClean_append, emitClean_cons, emitClean_nil]
    refine armFallsTo_of_wp (armWp_append hwpSetup ?_)
    rintro s₁ ⟨heval, hx₁, _, hdmem₁, hst₁, _⟩
    refine armWp_cons (armLoadDir_wp hdir hnoSp heval (by simpa [armMach, hdmem₁] using hv)) ?_
    rintro s₂ ⟨w64, rfl, hw64⟩
    refine armWp_mono (armMovToSp_wp .X16 (wr s₁ .X16 w64)) ?_
    rintro s₃ rfl
    refine ⟨⟨?_, hdmem₁⟩, armFrame_status_eq ?_ hst₁⟩
    · simpa [armMach, get_sp, get_wr_same] using hw64
    · intro r hr
      simp only [List.mem_cons, armScratch, List.not_mem_nil, or_false, not_or] at hr
      cases r with
      | SP => exact absurd rfl hr.1
      | reg xr =>
        have hx16 : xr ≠ .X16 := fun e => hr.2.1 (congrArg XRegOrSp.reg e)
        have h1 := hx₁ xr hx16
        simp only [get_reg, Reg64s_getXReg_setSP',
          Reg64s.getXReg_setXReg_of_ne _ _ _ _ hx16.symm]
        exact congrArg UInt64.toBitVec h1

private theorem armStoreValIn_wp [Host] {t : Ty} {pa : PArg Reg Empty ArmCond t}
    {v : Val t} {s : MachineData} {valSetup : List Instr} {rx : XReg}
    (hpa : armStoreValInIns t pa = some (valSetup, rx))
    (hp : armMach.PArgHolds s t pa v)
    (hregs : ∀ r ∈ pa.gprs, r ∉ armScratch)
    (ht : t = .bool ∨ t = .bits 8 ∨ t = .bits 16 ∨ t = .bits 32 ∨ t = .bits 64) :
    _root_.Program.wp (emitClean valSetup) (fun s' =>
      rx ≠ .X16 ∧
      (∃ w64 : BitVec 64, (s'.regs.getXReg rx).toBitVec = w64 ∧ GprHolds w64 t v) ∧
      s'.dmem = s.dmem ∧ s'.status = s.status ∧
      (∀ x, x ≠ .X17 → s'.regs.getXReg x = s.regs.getXReg x) ∧ s'.regs.SP = s.regs.SP)
      (fun _ _ => False) s := by
  cases t with
  | float _ | pair _ _ => rcases ht with h | h | h | h | h <;> cases h
  | bool =>
    cases pa with
    | vec vr => exact vr.elim
    | flag cond =>
      simp only [armStoreValInIns, Option.some.injEq, Prod.mk.injEq] at hpa
      rcases hpa with ⟨rfl, rfl⟩
      simp only [Machine.PArgHolds] at hp
      simp only [emitClean_cons, emitClean_nil]
      refine armWp_mono (armCset64_wp .X17 cond s) ?_
      rintro s' rfl
      refine ⟨by decide, ⟨_, rfl, ?_⟩, rfl, rfl,
        fun x hx => Reg64s.getXReg_setXReg_of_ne _ _ _ _ hx.symm, rfl⟩
      rw [Reg64s.getXReg_setXReg_same, hp]
      cases v <;> rfl
    | gpr r =>
      cases r with
      | reg x =>
        simp only [armStoreValInIns, Option.some.injEq, Prod.mk.injEq] at hpa
        rcases hpa with ⟨rfl, rfl⟩
        have hx16 : x ≠ .X16 := (xreg_ne_scratch_of_not_mem (hregs (.reg x) (by simp [PArg.gprs]))).1
        refine armWp_nil ⟨hx16, ⟨_, rfl, ?_⟩, rfl, rfl, fun _ _ => rfl, rfl⟩
        simpa [Machine.PArgHolds, armMach, get_reg] using hp
      | SP =>
        simp only [armStoreValInIns, Option.some.injEq, Prod.mk.injEq] at hpa
        rcases hpa with ⟨rfl, rfl⟩
        simp only [emitClean_cons, emitClean_nil]
        refine armWp_mono (armMovToX_wp .X17 .SP s) ?_
        rintro s' rfl
        refine ⟨by decide, ⟨_, rfl, ?_⟩, rfl, rfl,
          fun x hx => Reg64s.getXReg_setXReg_of_ne _ _ _ _ hx.symm, rfl⟩
        rw [Reg64s.getXReg_setXReg_same]
        simpa [Machine.PArgHolds, armMach, get_sp] using hp
    | imm c =>
      simp only [armStoreValInIns, Option.some.injEq, Prod.mk.injEq] at hpa
      rcases hpa with ⟨rfl, rfl⟩
      simp only [Machine.PArgHolds] at hp
      simp only [emitClean_cons, emitClean_nil]
      refine armWp_mono (armLdrPoolBv_wp .X17 _ s) ?_
      rintro s' rfl
      refine ⟨by decide, ⟨_, rfl, ?_⟩, rfl, rfl,
        fun x hx => Reg64s.getXReg_setXReg_of_ne _ _ _ _ hx.symm, rfl⟩
      rw [Reg64s.getXReg_setXReg_same]
      subst hp; cases c <;> rfl
  | bits n =>
    have hn64 : n ≤ 64 := by rcases ht with h | h | h | h | h <;> cases h <;> decide
    cases pa with
    | vec vr => exact vr.elim
    | gpr r =>
      cases r with
      | reg x =>
        simp only [armStoreValInIns, Option.some.injEq, Prod.mk.injEq] at hpa
        rcases hpa with ⟨rfl, rfl⟩
        have hx16 : x ≠ .X16 := (xreg_ne_scratch_of_not_mem (hregs (.reg x) (by simp [PArg.gprs]))).1
        refine armWp_nil ⟨hx16, ⟨_, rfl, ?_⟩, rfl, rfl, fun _ _ => rfl, rfl⟩
        simpa [Machine.PArgHolds, armMach, get_reg] using hp
      | SP =>
        simp only [armStoreValInIns, Option.some.injEq, Prod.mk.injEq] at hpa
        rcases hpa with ⟨rfl, rfl⟩
        simp only [emitClean_cons, emitClean_nil]
        refine armWp_mono (armMovToX_wp .X17 .SP s) ?_
        rintro s' rfl
        refine ⟨by decide, ⟨_, rfl, ?_⟩, rfl, rfl,
          fun x hx => Reg64s.getXReg_setXReg_of_ne _ _ _ _ hx.symm, rfl⟩
        rw [Reg64s.getXReg_setXReg_same]
        simpa [Machine.PArgHolds, armMach, get_sp] using hp
    | imm c =>
      simp only [armStoreValInIns, Option.some.injEq, Prod.mk.injEq] at hpa
      rcases hpa with ⟨rfl, rfl⟩
      simp only [Machine.PArgHolds] at hp
      simp only [emitClean_cons, emitClean_nil]
      refine armWp_mono (armLdrPoolBv_wp .X17 _ s) ?_
      rintro s' rfl
      refine ⟨by decide, ⟨_, rfl, ?_⟩, rfl, rfl,
        fun x hx => Reg64s.getXReg_setXReg_of_ne _ _ _ _ hx.symm, rfl⟩
      rw [Reg64s.getXReg_setXReg_same]
      dsimp only
      refine ⟨hn64, ?_⟩; subst hp
      rw [BitVec.setWidth_setWidth_of_le _ hn64, BitVec.setWidth_eq]

private theorem take_setWidth_32_low {k : Nat} (hk : k ≤ 32) (v : BitVec 64) :
    ((v.setWidth 32).take k) = v.setWidth k := by
  ext i hi; simp [BitVec.take, show (i : Nat) < 32 by omega]

private theorem armStoreDir_wp [Host] {t : Ty} {rx : XReg} {addr : AddrExpr} {a : BitVec 64}
    {v : Val t} {s : MachineData} {dir : Instr}
    (hdir : armStoreDirI t rx addr = some dir) (hnoSp : ∃ r, addr.base = .low (.reg r) .W64)
    (heval : ∀ [Labels] p, addr.eval s p = (a, s))
    (hval : GprHolds (s.regs.getXReg rx).toBitVec t v)
    (hok : storeOk s.dmem t a) :
    _root_.Program.wp [.instr dir] (fun s' =>
      s'.regs = s.regs ∧ s'.status = s.status ∧ s'.dmem = storeMem s.dmem t a v)
      (fun _ _ => False) s := by
  obtain ⟨r, hr⟩ := hnoSp
  rcases hok with ⟨i, hi⟩
  cases t with
  | bool =>
    simp only [armStoreDirI, Option.some.injEq] at hdir; subst hdir
    simp only [Ty.bytes, Ty.size] at hi
    refine armDirFallsTo_wp (by
      intro _ p next jmp P hk
      simp only [Directive.interp, Instr.interp, Operation.interp, AddrExpr.interpStore,
        AddrExpr.checkSPAlignment, hr, heval p, getRegOrZr_zr, RegWidth.bits, MachineData.store,
        MemWidth.bytes, Effects.All]
      rw [hi]
      refine hk _ ⟨rfl, rfl, ?_⟩
      simp only [storeMem, Ty.bytes, Ty.size, toBits, GprHolds] at hval ⊢
      rw [take_setWidth_32_low (by decide : 8 ≤ 32), hval]
      congr 2; cases v <;> rfl)
  | bits n =>
    have hns : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64 := by
      rcases (by omega : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64 ∨ (n ≠ 8 ∧ n ≠ 16 ∧ n ≠ 32 ∧ n ≠ 64))
        with h | h | h | h | ⟨h1, h2, h3, h4⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h))
      · exfalso; revert hdir; simp [armStoreDirI, h1, h2, h3, h4]
    rcases hns with rfl | rfl | rfl | rfl <;>
      (simp only [armStoreDirI, Option.some.injEq] at hdir; subst hdir;
       simp only [Ty.bytes, Ty.size] at hi;
       refine armDirFallsTo_wp (by
         intro _ p next jmp P hk
         simp only [Directive.interp, Instr.interp, Operation.interp, AddrExpr.interpStore,
           AddrExpr.checkSPAlignment, hr, heval p, getRegOrZr_zr, RegWidth.bits,
           MachineData.store, MemWidth.bytes, Effects.All]
         rw [hi]
         refine hk _ ⟨rfl, rfl, ?_⟩
         simp only [storeMem, Ty.bytes, Ty.size, toBits, GprHolds] at hval ⊢
         try rw [take_setWidth_32_low (by decide : _ ≤ 32)]
         rw [hval.2]; rfl))
  | float _ | pair _ _ => simp [armStoreDirI] at hdir

theorem armStore_spec {h : Host} {k : Nat} {t : Ty} {pa : PArg Reg Empty ArmCond t}
    {a : AddrArg Reg} {c : List Directive} {clob : FlagMask} {v : Val t} {s : MachineData}
    {post : MachineState → Prop}
    (hc_in : armStore t pa a = some (c, clob))
    (hregs : ∀ r ∈ pa.gprs ++ a.regs, r ∉ armScratch)
    (hp : armMach.PArgHolds s t pa v) (hok : storeOk (armMach.mem s) t (a.eval (get s))) :
    armMach.FallsTo armCondReads h k c armScratch [] clob s
      (fun s' => armMach.mem s' = storeMem (armMach.mem s) t (a.eval (get s)) v) post := by
  letI := h
  obtain ⟨ci, hc, rfl⟩ := emitCleanPair_eq_some.mp hc_in
  have hvaValid : armAddrValid a = true := by
    cases a with
    | imm _ | baseDisp _ _ => rfl
    | baseIdxDisp _ _ _ _ =>
      dsimp only [armStoreIns, armAddrValid] at hc
      contradiction
  dsimp only [armStoreIns] at hc
  rw [show (!armAddrValid a) = false by simp [hvaValid]] at hc
  simp only [Bool.false_eq_true, ↓reduceIte, bind, Option.bind_eq_some_iff] at hc
  rcases hc with ⟨scale, hsc, ⟨valSetup, rx⟩, hva, dir, hdir, rfl, rfl⟩
  have ht : t = .bool ∨ t = .bits 8 ∨ t = .bits 16 ∨ t = .bits 32 ∨ t = .bits 64 := by
    match t with
    | .bool => exact Or.inl rfl
    | .bits 8 => exact Or.inr (Or.inl rfl)
    | .bits 16 => exact Or.inr (Or.inr (Or.inl rfl))
    | .bits 32 => exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    | .bits 64 => exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
    | .bits n =>
      rcases (by omega : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64 ∨ (n ≠ 8 ∧ n ≠ 16 ∧ n ≠ 32 ∧ n ≠ 64))
        with hn | hn | hn | hn | ⟨h1, h2, h3, h4⟩
      · subst hn; exact Or.inr (Or.inl rfl)
      · subst hn; exact Or.inr (Or.inr (Or.inl rfl))
      · subst hn; exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      · subst hn; exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
      · exfalso; revert hsc; simp [armMemScale, h1, h2, h3, h4]
    | .float _ | .pair _ _ => simp [armMemScale] at hsc
  have hpaRegs : ∀ r ∈ pa.gprs, r ∉ armScratch := fun r hr => hregs r (List.mem_append_left _ hr)
  have haRegs : ∀ r ∈ a.regs, r ∉ armScratch := fun r hr => hregs r (List.mem_append_right _ hr)
  rw [List.append_assoc]
  simp only [emitClean_append, emitClean_cons, emitClean_nil]
  refine armFallsTo_of_wp (armWp_append (armStoreValIn_wp hva hp hpaRegs ht) ?_)
  rintro s₁ ⟨hrx16, ⟨w64, hrx₁, hw64⟩, hdmem₁, hst₁, hx₁, hsp₁⟩
  have hsetup := armSetupAddr_wp scale a s₁ haRegs hvaValid
  generalize armSetupAddrIns scale a = sa at hdir hsetup
  rcases sa with ⟨addrSetup, addr⟩
  rcases hsetup with ⟨hnoSp, hwpAddr⟩
  have heqAddr : a.eval (get s₁) = a.eval (get s) := by
    cases a with
    | baseIdxDisp _ _ _ _ => simp [armAddrValid] at hvaValid
    | imm _ => rfl
    | baseDisp b disp =>
      simp only [AddrArg.eval]
      have hrb : b ∉ armScratch := haRegs b (by simp [AddrArg.regs])
      cases b with
      | SP => simp [get_sp, hsp₁]
      | reg rb =>
        have h17 : rb ≠ .X17 := (xreg_ne_scratch_of_not_mem hrb).2
        simp [get_reg, hx₁ rb h17]
  refine armWp_append hwpAddr ?_
  rintro s₂ ⟨heval₂, hx₂, hsp₂, hdmem₂, hst₂, _⟩
  rw [heqAddr] at heval₂
  have hval₂ : GprHolds (s₂.regs.getXReg rx).toBitVec t v := by
    rw [hx₂ rx hrx16, hrx₁]; exact hw64
  have hok₂ : storeOk s₂.dmem t (a.eval (get s)) := by rw [hdmem₂, hdmem₁]; exact hok
  refine armWp_mono (armStoreDir_wp hdir hnoSp heval₂ hval₂ hok₂) ?_
  rintro s₃ ⟨hregs₃, hst₃, hdmem₃⟩
  refine ⟨by simpa [armMach, hdmem₂, hdmem₁] using hdmem₃, armFrame_status_eq ?_ (by rw [hst₃, hst₂, hst₁])⟩
  intro r hr
  cases r with
  | SP => simp [get_sp, hregs₃, hsp₂, hsp₁]
  | reg x =>
    have hx16' : x ≠ .X16 := fun e => hr (by simp [e, armScratch])
    have hx17' : x ≠ .X17 := fun e => hr (by simp [e, armScratch])
    simp [get_reg, hregs₃, hx₂ x hx16', hx₁ x hx17']

/-! ## 4. Shared bitfield, shift/rotate, comparison, division, and carry/borrow lemmas -/

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

theorem evalUBFM_low {w : RegWidth} (x : w.type) {n : Nat} (hn0 : 0 < n) (hn : n ≤ w.bits) :
    evalUBFM (w := w) x 0 (n - 1) = (x.setWidth n).setWidth w.bits := by
  cases w <;>
    simp only [evalUBFM, RegWidth.bits, MemWidth.bits, BitVec.take, BitVec.zeroExtend] at hn0 hn ⊢ <;>
    ext i hi <;> grind

theorem evalSBFM_low {w : RegWidth} (x : w.type) {n : Nat} (hn0 : 0 < n) (hn : n ≤ w.bits) :
    evalSBFM (w := w) x 0 (n - 1) = (x.setWidth n).signExtend w.bits := by
  cases w <;>
    simp only [evalSBFM, RegWidth.bits, MemWidth.bits, BitVec.take, BitVec.zeroExtend] at hn0 hn ⊢ <;>
    ext i hi <;> grind

theorem evalUBFM_32_63 (x : BitVec 64) :
    evalUBFM (w := .W64) x 32 63 = x >>> 32 :=
  evalUBFM_lsr x (by decide)

theorem evalEXTR_rotr {w : RegWidth} (x : w.type) (k : Nat) :
    (let lsb := k % w.bits
     if lsb == 0 then x else (x <<< (w.bits - lsb)) ||| (x >>> lsb)) = x.rotateRight k := by
  cases w <;> simp only [RegWidth.bits, MemWidth.bits] <;> ext i hi <;> grind

theorem evalEXTR_fshr {n : Nat} (hn : n = 32 ∨ n = 64) (a b : BitVec n) {k : Nat} (hk : k < n) :
    (if k == 0 then b else (a <<< (n - k)) ||| (b >>> k)) = ((a ++ b) >>> k).extractLsb' 0 n := by
  rcases hn with rfl | rfl <;> ext i hi <;> grind

theorem evalEXTR_fshl {n : Nat} (hn : n = 32 ∨ n = 64) (a b : BitVec n) {k : Nat}
    (hk : k < n) :
    (a <<< k) ||| (b >>> (n - k)) = ((a ++ b) <<< k).extractLsb' n n := by
  rcases hn with rfl | rfl <;> ext i hi <;> grind

theorem shl_subword_mask {n : Nat} (hn : n = 8 ∨ n = 16) (a : BitVec 32) (y : BitVec n) :
    (a <<< ((y.setWidth 32 &&& BitVec.ofNat 32 (n - 1)).toNat % 32)).setWidth n =
      a.setWidth n <<< (y.toNat % n) := by
  rcases hn with rfl | rfl <;> ext i hi <;> grind

theorem lshr_subword_mask {n : Nat} (hn : n = 8 ∨ n = 16) (x y : BitVec n) :
    ((x.setWidth 32).ushiftRight ((y.setWidth 32 &&& BitVec.ofNat 32 (n - 1)).toNat % 32)).setWidth n =
      x >>> (y.toNat % n) := by
  rcases hn with rfl | rfl <;> ext i hi <;> grind

theorem ashr_subword_mask {n : Nat} (hn : n = 8 ∨ n = 16) (x y : BitVec n) :
    ((x.signExtend 32).sshiftRight ((y.setWidth 32 &&& BitVec.ofNat 32 (n - 1)).toNat % 32)).setWidth n =
      x.sshiftRight (y.toNat % n) := by
  rcases hn with rfl | rfl <;> ext i hi <;> grind

theorem rotr_subword_mask {n : Nat} (hn : n = 8 ∨ n = 16) (x y : BitVec n) :
    let rep := x.setWidth 32 ||| (x.setWidth 32 <<< n)
    (rep.ushiftRight ((y.setWidth 32 &&& BitVec.ofNat 32 (n - 1)).toNat % 32)).setWidth n =
      x.rotateRight (y.toNat % n) := by
  rcases hn with rfl | rfl <;> ext i hi <;> grind

theorem rotl_subword_mask {n : Nat} (hn : n = 8 ∨ n = 16) (x y : BitVec n) :
    let rep := x.setWidth 32 ||| (x.setWidth 32 <<< n)
    let cnt := ((0#32 - y.setWidth 32) &&& BitVec.ofNat 32 (n - 1)).toNat % 32
    (rep.ushiftRight cnt).setWidth n = x.rotateLeft (y.toNat % n) := by
  rcases hn with rfl | rfl <;> ext i hi <;> grind

theorem armCmpCond_subs {n : Nat} (hn : n = 32 ∨ n = 64) (o : CmpOp) (x y : BitVec n) :
    (armCmpCond o).interp (StatusFlags.subs (x - y) x y) = o.evalBits x y := by
  simp only [armCmpCond, ArmCond.interp, ArmCond.toKraken, CondCode.interp,
    StatusFlags.subs, StatusFlags.from_result, CmpOp.evalBits, BitVec.ult, BitVec.ule,
    BitVec.slt, BitVec.sle]
  rcases hn with rfl | rfl <;> cases o <;>
    grind [BitVec.unsigned, BitVec.signed]

theorem cmp_subword_unsigned {n : Nat} (hn : n = 8 ∨ n = 16) (o : CmpOp)
    (ho : armIsSignedCmp o = false) (x y : BitVec n) :
    o.evalBits (x.setWidth 32) (y.setWidth 32) = o.evalBits x y := by
  have hx := x.isLt; have hy := y.isLt
  have hinj : x.setWidth 32 = y.setWidth 32 ↔ x = y := by
    constructor
    · intro h; have := congrArg (BitVec.setWidth n) h
      rcases hn with rfl | rfl <;> simpa using this
    · rintro rfl; rfl
  rcases hn with rfl | rfl <;> cases o <;> simp only [armIsSignedCmp] at ho
  all_goals first
    | exact absurd ho (by decide)
    | (dsimp only [CmpOp.evalBits]; simp only [hinj, ne_eq])
    | (dsimp only [CmpOp.evalBits, BitVec.ult, BitVec.ule];
       simp [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega : x.toNat < 2 ^ 32),
         Nat.mod_eq_of_lt (by omega : y.toNat < 2 ^ 32)])

theorem setWidth_signExtend_self {n w : Nat} (hle : n ≤ w) (x : BitVec n) :
    (x.signExtend w).setWidth n = x := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_signExtend, hi,
    show (i : Nat) < w by omega, decide_true, Bool.true_and, ↓reduceIte]

theorem cmp_subword_signed {n : Nat} (hn : n = 8 ∨ n = 16) (o : CmpOp)
    (ho : armIsSignedCmp o = true) (x y : BitVec n) :
    o.evalBits (x.signExtend 32) (y.signExtend 32) = o.evalBits x y := by
  have hle8 : 8 ≤ 32 := by decide
  have hle16 : 16 ≤ 32 := by decide
  rcases hn with rfl | rfl <;> cases o <;> simp only [armIsSignedCmp] at ho
  all_goals first
    | exact absurd ho (by decide)
    | simp [CmpOp.evalBits, BitVec.slt, BitVec.sle, BitVec.toInt_signExtend_of_le, hle8, hle16]

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

theorem udiv_subword_32 {n : Nat} (hn : n = 8 ∨ n = 16) (a b : BitVec n) :
    (a.setWidth 32 / b.setWidth 32).setWidth n = a / b := by
  have ha := a.isLt; have hb := b.isLt
  rcases hn with rfl | rfl <;> apply BitVec.eq_of_toNat_eq <;>
    simp [BitVec.toNat_udiv, Nat.mod_eq_of_lt (by omega : a.toNat < 4294967296),
      Nat.mod_eq_of_lt (by omega : b.toNat < 4294967296)] <;>
    exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) ha

theorem urem_subword_32 {n : Nat} (hn : n = 8 ∨ n = 16) (a b : BitVec n) :
    (a.setWidth 32 % b.setWidth 32).setWidth n = a % b := by
  have ha := a.isLt; have hb := b.isLt
  rcases hn with rfl | rfl <;> apply BitVec.eq_of_toNat_eq <;>
    simp [BitVec.toNat_umod, Nat.mod_eq_of_lt (by omega : a.toNat < 4294967296),
      Nat.mod_eq_of_lt (by omega : b.toNat < 4294967296)] <;>
    (by_cases hb0 : b.toNat = 0
     · simp [hb0, ha]
     · exact Nat.lt_trans (Nat.mod_lt _ (Nat.pos_of_ne_zero hb0)) hb)

theorem setWidth_sub_of_le {n w : Nat} (hle : n ≤ w) (x y : BitVec w) :
    (x - y).setWidth n = x.setWidth n - y.setWidth n := by
  apply BitVec.eq_of_toNat_eq
  rcases Nat.eq_or_lt_of_le hle with rfl | _
  · simp
  · obtain ⟨k, hk⟩ := Nat.pow_dvd_pow 2 hle
    have hx := x.isLt; have hy := y.isLt
    have hpow : 0 < 2 ^ n := Nat.two_pow_pos n
    have hyk : y.toNat < 2 ^ n * k := hk ▸ hy
    have hqlt : y.toNat / 2 ^ n < k :=
      (Nat.mul_lt_mul_left hpow).mp (by have := Nat.mul_div_le y.toNat (2 ^ n); omega)
    have hdiv : y.toNat = 2 ^ n * (y.toNat / 2 ^ n) + y.toNat % 2 ^ n := by
      have := Nat.div_add_mod y.toNat (2 ^ n); omega
    have hsum_w : y.toNat + (2 ^ n * (k - y.toNat / 2 ^ n - 1) + (2 ^ n - y.toNat % 2 ^ n)) =
        2 ^ w := by
      have hmod := Nat.mod_lt y.toNat hpow
      have hk_rhs : 2 ^ n * k = 2 ^ n * (k - y.toNat / 2 ^ n - 1) + 2 ^ n + 2 ^ n * (y.toNat / 2 ^ n) := by
        calc 2 ^ n * k = 2 ^ n * ((k - y.toNat / 2 ^ n - 1) + 1 + y.toNat / 2 ^ n) := by
                congr 1; omega
          _ = _ := by rw [Nat.mul_add, Nat.mul_add, Nat.mul_one]
      omega
    have hsub_w : 2 ^ w - y.toNat =
        2 ^ n * (k - y.toNat / 2 ^ n - 1) + (2 ^ n - y.toNat % 2 ^ n) :=
      Nat.sub_eq_of_eq_add (by omega)
    simp only [BitVec.toNat_setWidth, BitVec.toNat_sub]
    rw [Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 hle), hsub_w, Nat.add_assoc, Nat.mul_add_mod,
      Nat.add_mod (2 ^ n - y.toNat % 2 ^ n) x.toNat, Nat.add_mod (2 ^ n - y.toNat % 2 ^ n) (x.toNat % 2 ^ n),
      Nat.mod_mod]

theorem setWidth_neg_of_le {n w : Nat} (hle : n ≤ w) (x : BitVec w) :
    (-x).setWidth n = -(x.setWidth n) := by
  simpa [BitVec.zero_sub] using setWidth_sub_of_le hle 0#w x

theorem setWidth_mul_of_le {n w : Nat} (hle : n ≤ w) (x y : BitVec w) :
    (x * y).setWidth n = x.setWidth n * y.setWidth n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_mul]
  rw [Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 hle), Nat.mul_mod]

theorem sdiv_subword_32 {n : Nat} (hn : n = 8 ∨ n = 16) (a b : BitVec n) :
    ((a.signExtend 32).sdiv (b.signExtend 32)).setWidth n = a.sdiv b := by
  have hle : n ≤ 32 := by rcases hn with rfl | rfl <;> decide
  have hmsb : ∀ x : BitVec n, (x.signExtend 32).msb = x.msb := fun x => by
    rw [BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_signExtend]
    have h2 : x.msb = x.getLsbD (n - 1) := by
      rcases hn with rfl | rfl <;> exact BitVec.msb_eq_getLsbD_last x
    rw [h2]; rcases hn with rfl | rfl <;> simp
  have hpos : ∀ {x : BitVec n}, x.msb = false → x.signExtend 32 = x.setWidth 32 := fun {x} hx => by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_signExtend, BitVec.getLsbD_setWidth, hi, decide_true, Bool.true_and]
    by_cases hin : i < n
    · simp [hin]
    · have hge : x.getLsbD i = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by decide) (by omega)))
      simp [hin, hx, hge]
  have hneg : ∀ {x : BitVec n}, x.msb = true → -(x.signExtend 32) = (-x).setWidth 32 := fun {x} hx => by
    have hse : (x.signExtend 32).toInt = x.toInt := BitVec.toInt_signExtend_of_le hle
    have hxle := BitVec.le_toInt x
    have htoInt : (-(x.signExtend 32)).toInt = -x.toInt := by
      rw [BitVec.toInt_neg_of_ne_intMin (fun he => by
        have := congrArg BitVec.toInt he; rw [hse, BitVec.toInt_intMin] at this
        rcases hn with rfl | rfl <;> omega), hse]
    have hxn := x.isLt
    have hmdec := BitVec.msb_eq_decide x
    rw [hx] at hmdec
    have hhalf : 2 ^ (n - 1) ≤ x.toNat := by simpa using hmdec
    have hcondx := BitVec.toInt_eq_toNat_cond x
    have hxlt : x.toInt < 0 := by rcases hn with rfl | rfl <;> (split at hcondx <;> omega)
    have hx_sub : (-x.toInt).toNat = 2 ^ n - x.toNat := by
      rcases hn with rfl | rfl <;> (split at hcondx <;> omega)
    have hxne0 : x ≠ 0 := fun h0 => by subst h0; simp at hx
    have hxtoNat : x.toNat ≠ 0 := fun h0 => hxne0 (BitVec.eq_of_toNat_eq (by simpa using h0))
    have hneg_nat : (-(x.signExtend 32)).toNat = (-x.toInt).toNat := by
      have hcond := BitVec.toInt_eq_toNat_cond (-(x.signExtend 32))
      have hlt32 := (-(x.signExtend 32)).isLt
      rcases hn with rfl | rfl <;> (split at hcond <;> omega)
    apply BitVec.eq_of_toNat_eq
    simp [hneg_nat, hx_sub, BitVec.toNat_setWidth, BitVec.toNat_neg, hxtoNat,
      Nat.mod_eq_of_lt (by rcases hn with rfl | rfl <;> omega : 2 ^ n - x.toNat < 2 ^ 32)]
  rw [BitVec.sdiv_eq, BitVec.sdiv_eq, hmsb a, hmsb b]
  cases ha : a.msb <;> cases hb : b.msb <;>
    simp [hpos, hneg, setWidth_neg_of_le hle, udiv_subword_32 hn, ha, hb]

theorem srem_subword_32 {n : Nat} (hn : n = 8 ∨ n = 16) (a b : BitVec n) :
    ((a.signExtend 32).srem (b.signExtend 32)).setWidth n = a.srem b := by
  have hle : n ≤ 32 := by rcases hn with rfl | rfl <;> decide
  rw [srem_eq_sub, srem_eq_sub, setWidth_sub_of_le hle, setWidth_mul_of_le hle,
    sdiv_subword_32 hn, setWidth_signExtend_self hle, setWidth_signExtend_self hle]

/-! ## 5. Non-`op` `NoLab` theorems -/

theorem armClearFlags_noLab (l : Sym) : Kraken.Directive.label l ∉ armGpr.clearFlags :=
  emitClean_noLab _ l

theorem armMov_noLab (rd rs : Reg) (l : Sym) : Kraken.Directive.label l ∉ armGpr.mov rd rs :=
  emitClean_noLab _ l

theorem armMovi_noLab (rd : Reg) (c : BitVec 64) (l : Sym) :
    Kraken.Directive.label l ∉ armGpr.movi rd c :=
  emitClean_noLab _ l

theorem armSetcc_noLab (rd : Reg) (c : ArmCond) (l : Sym) :
    Kraken.Directive.label l ∉ armGpr.setcc rd c :=
  emitClean_noLab _ l

theorem armJmp_noLab (tgt l : Sym) : Kraken.Directive.label l ∉ armGpr.jmp tgt :=
  emitClean_noLab _ l

theorem armJcc_noLab (c : ArmCond) (tgt l : Sym) : Kraken.Directive.label l ∉ armGpr.jcc c tgt :=
  emitClean_noLab _ l

theorem armJnzGpr_noLab (r : Reg) (tgt l : Sym) :
    Kraken.Directive.label l ∉ (armGpr.jnzGpr r tgt).1 :=
  emitClean_noLab _ l

theorem armLoad_noLab {t : Ty} {rd : Reg} {a : AddrArg Reg} {c : List Directive} {clob : FlagMask}
    (hc : armGpr.load t rd a = some (c, clob)) (l : Sym) : Kraken.Directive.label l ∉ c :=
  emitCleanPair_noLab hc l

theorem armStore_noLab {t : Ty} {pa : PArg Reg Empty ArmCond t} {a : AddrArg Reg}
    {c : List Directive} {clob : FlagMask} (hc : armGpr.store t pa a = some (c, clob)) (l : Sym) :
    Kraken.Directive.label l ∉ c :=
  emitCleanPair_noLab hc l

end LeanQbe.T.Arm64


