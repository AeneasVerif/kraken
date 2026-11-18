module

public import Kraken.AArch64.OmniSemantics
public import Kraken.AArch64.Regs
public import Kraken.AArch64.WP
public import LeanQbe.Arm64.Targ
public import LeanQbe.Arm64.TargLemmas
public import LeanQbe.StepSimp

/-!
# Spike S2 (AArch64): NZCV Flag-Frame Preservation & Borrow Inversion (Locks L3–L6)

Standalone verification against `Kraken.AArch64.OmniSemantics` (`0 sorry`, `-DwarningAsError=true`)
proving the `G7` / `L3`–`L6` read-only flag cache, clobber-mask frame laws, and `SBCS` borrow
inversion on AArch64:

1. **`ArmCond` & `CondCode.NV` audit finding:**
   * In AArch64 hardware and `Kraken/AArch64/Semantics.lean:403-404`, both `CondCode.AL` and
     `CondCode.NV` (`0b1111`) evaluate to `true`, so `(CondCode.AL.invert).interp st = true ≠ !true`.
   * `ArmCond` therefore restricts `Isa.Cond` to the 14 genuine invertible NZCV conditions
     (`EQ, NE, CS, CC, MI, PL, VS, VC, HI, LS, GE, LT, GT, LE`), giving exact involutive negation
     `armNegCond_interp : (armNegCond c).interp st = !(c.interp st)`.

2. **Move-class, carry, borrow, and branch snippets in `Kraken.AArch64`:**
   * `mov rd, rs` (`ADD_e rd rs #0`): `clob = 0#8` (preserves all NZCV conditions, valid for `SP`).
   * `MOVZ rd, #0`: `clob = 0#8` (preserves all NZCV conditions).
   * `addImm12 rd, rb, #disp` (`ADD_e`, AArch64 `lea` counterpart): `clob = 0#8`.
   * `csetMove rd, c` (`CSINC rd, xzr, xzr, (armNegCond c).toKraken`): `clob = 0#8` (the single
     flag → GPR move `L3`, writing `0/1` to `rd` while preserving all NZCV conditions).
   * `ADC rd, ra, rb` (non-flag-setting carry add): `clob = 0#8` (reads `.CS`, preserves NZCV).
   * `SBCS rd, ra, rb` (encapsulated borrow inversion for `T9`): reads `borrow_in` from `.CC`
     (`!s.status.c`), writes `a - b - borrow_in` to `rd`, and sets `.CC` to
     `decide (a.toNat < b.toNat + borrow_in.toNat)` matching `OpCode.subb` (`Ops.lean:519`)!
-/

set_option autoImplicit false

@[expose] public section

namespace SpikeS2.Arm64

open LeanQbe Arm64

/-! ## 1. `ArmCond` and Clobber Masks (`N=0, Z=1, C=2, V=3`) -/

/-- Audit witness: `CondCode.AL.invert = .NV`, which still evaluates to `true` in AArch64! -/
theorem kraken_nv_always_true (st : StatusFlags) :
    (CondCode.AL.invert).interp st = true := rfl

/-- The 14 invertible NZCV conditions on AArch64 (excluding `AL`/`NV`). -/
inductive ArmCond
  | eq | ne | cs | cc | mi | pl | vs | vc | hi | ls | ge | lt | gt | le
  deriving Repr, BEq, DecidableEq, Hashable

def ArmCond.toKraken : ArmCond → CondCode
  | .eq => .EQ | .ne => .NE
  | .cs => .CS | .cc => .CC
  | .mi => .MI | .pl => .PL
  | .vs => .VS | .vc => .VC
  | .hi => .HI | .ls => .LS
  | .ge => .GE | .lt => .LT
  | .gt => .GT | .le => .LE

@[reducible] def ArmCond.interp (c : ArmCond) (st : StatusFlags) : Bool :=
  c.toKraken.interp st

def armNegCond : ArmCond → ArmCond
  | .eq => .ne | .ne => .eq
  | .cs => .cc | .cc => .cs
  | .mi => .pl | .pl => .mi
  | .vs => .vc | .vc => .vs
  | .hi => .ls | .ls => .hi
  | .ge => .lt | .lt => .ge
  | .gt => .le | .le => .gt

abbrev FlagMask := BitVec 8

def maskNone : FlagMask := 0x00#8
def maskN    : FlagMask := 0x01#8 -- bit 0
def maskZ    : FlagMask := 0x02#8 -- bit 1
def maskC    : FlagMask := 0x04#8 -- bit 2
def maskV    : FlagMask := 0x08#8 -- bit 3
def maskNZCV : FlagMask := 0x0F#8

@[reducible] def FlagMask.disjoint (reads clob : FlagMask) : Bool :=
  (reads &&& clob) == 0#8

def armCondReads : ArmCond → FlagMask
  | .eq | .ne => maskZ
  | .cs | .cc => maskC
  | .mi | .pl => maskN
  | .vs | .vc => maskV
  | .hi | .ls => maskC ||| maskZ
  | .ge | .lt => maskN ||| maskV
  | .gt | .le => maskN ||| maskZ ||| maskV

theorem armNegCond_interp (c : ArmCond) (st : StatusFlags) :
    (armNegCond c).interp st = !(c.interp st) := by
  rcases st with ⟨n, z, cf, v⟩
  cases c <;> cases n <;> cases z <;> cases cf <;> cases v <;> rfl

theorem armNegCond_reads (c : ArmCond) :
    armCondReads (armNegCond c) = armCondReads c := by
  cases c <;> rfl

def KeepsFlags (s s' : MachineData) (clob : FlagMask) : Prop :=
  ∀ c : ArmCond, FlagMask.disjoint (armCondReads c) clob = true →
    c.interp s'.status = c.interp s.status

theorem keepsFlags_refl (s : MachineData) (clob : FlagMask) : KeepsFlags s s clob :=
  fun _ _ => rfl

theorem keepsFlags_of_status_eq {s s' : MachineData} (h : s'.status = s.status) (clob : FlagMask) :
    KeepsFlags s s' clob := by
  intro c _; rw [h]

private theorem getLsbD_false_of_and_zero {m clob : BitVec 8} {i : Nat}
    (h : m &&& clob = 0#8) (hm : m.getLsbD i = true) : clob.getLsbD i = false := by
  have hi : (m &&& clob).getLsbD i = false := by rw [h]; simp
  rw [BitVec.getLsbD_and, hm, Bool.true_and] at hi
  exact hi

theorem keepsFlags_of_bits {s s' : MachineData} {clob : FlagMask}
    (hn : clob.getLsbD 0 = false → s'.status.n = s.status.n)
    (hz : clob.getLsbD 1 = false → s'.status.z = s.status.z)
    (hc : clob.getLsbD 2 = false → s'.status.c = s.status.c)
    (hv : clob.getLsbD 3 = false → s'.status.v = s.status.v) :
    KeepsFlags s s' clob := by
  intro c hdisj
  simp only [FlagMask.disjoint, beq_iff_eq] at hdisj
  cases c <;> simp only [armCondReads, ArmCond.interp, ArmCond.toKraken, CondCode.interp] at hdisj ⊢
  · rw [hz (getLsbD_false_of_and_zero hdisj rfl)]
  · rw [hz (getLsbD_false_of_and_zero hdisj rfl)]
  · rw [hc (getLsbD_false_of_and_zero hdisj rfl)]
  · rw [hc (getLsbD_false_of_and_zero hdisj rfl)]
  · rw [hn (getLsbD_false_of_and_zero hdisj rfl)]
  · rw [hn (getLsbD_false_of_and_zero hdisj rfl)]
  · rw [hv (getLsbD_false_of_and_zero hdisj rfl)]
  · rw [hv (getLsbD_false_of_and_zero hdisj rfl)]
  · rw [hc (getLsbD_false_of_and_zero hdisj rfl), hz (getLsbD_false_of_and_zero hdisj rfl)]
  · rw [hc (getLsbD_false_of_and_zero hdisj rfl), hz (getLsbD_false_of_and_zero hdisj rfl)]
  · rw [hn (getLsbD_false_of_and_zero hdisj rfl), hv (getLsbD_false_of_and_zero hdisj rfl)]
  · rw [hn (getLsbD_false_of_and_zero hdisj rfl), hv (getLsbD_false_of_and_zero hdisj rfl)]
  · rw [hz (getLsbD_false_of_and_zero hdisj rfl), hn (getLsbD_false_of_and_zero hdisj rfl),
        hv (getLsbD_false_of_and_zero hdisj rfl)]
  · rw [hz (getLsbD_false_of_and_zero hdisj rfl), hn (getLsbD_false_of_and_zero hdisj rfl),
        hv (getLsbD_false_of_and_zero hdisj rfl)]

/-! ## 2. Move-Class, Carry/Borrow, and `CSET` Snippets in Kraken AArch64 -/

/-- 2a. `mov (.reg rd) rs` (`ADD_e`, `clob = maskNone`): preserves all NZCV flags. -/
theorem mov_reg_keepsFlags [Host] {k : Nat} {rd : XReg} {rs : Reg} {s : MachineData}
    {post : MachineState → Prop}
    (hc : (mov (.reg rd) rs).IsInfixAt Host.prog k)
    (hk : ∀ s' : MachineData,
      get s' (.reg rd) = get s rs →
      (∀ r, r ≠ .reg rd → get s' r = get s r) →
      s'.dmem = s.dmem →
      KeepsFlags s s' maskNone →
      Eventually (step1 Host.exe) post ⟨s', Host.addrOf (k + 1)⟩) :
    Eventually (step1 Host.exe) post ⟨s, Host.addrOf k⟩ := by
  refine Runs.eventually (runs_mov_reg rd rs s) hc ?_
  exact hk _ (get_wr_same s rd (get s rs)) (fun r hne => get_wr_of_ne s rd _ r hne)
    rfl (keepsFlags_refl _ _)

/-- 2b. `MOVZ rd, #0` (`clob = maskNone`): preserves all NZCV flags. -/
def movzZero64 (rd : XReg) : List Directive :=
  [ins (w := .W64) (.MOVZ (zr rd .W64) (.int64 0) .LSL0)]

theorem runs_movzZero64 (rd : XReg) (s : MachineData) :
    Runs (movzZero64 rd) s (wr s rd 0#64) := by
  refine Runs.single fun p next jmp => ?_
  simp only [step_simp, MovShift.toNat]
  rfl

theorem movzZero64_keepsFlags [Host] {k : Nat} {rd : XReg} {s : MachineData}
    {post : MachineState → Prop}
    (hc : (movzZero64 rd).IsInfixAt Host.prog k)
    (hk : ∀ s' : MachineData,
      get s' (.reg rd) = 0#64 →
      (∀ r, r ≠ .reg rd → get s' r = get s r) →
      s'.dmem = s.dmem →
      KeepsFlags s s' maskNone →
      Eventually (step1 Host.exe) post ⟨s', Host.addrOf (k + 1)⟩) :
    Eventually (step1 Host.exe) post ⟨s, Host.addrOf k⟩ := by
  refine Runs.eventually (runs_movzZero64 rd s) hc ?_
  exact hk _ (get_wr_same s rd 0#64) (fun r hne => get_wr_of_ne s rd _ r hne)
    rfl (keepsFlags_refl _ _)

/-- 2c. `addImm12 rd rb imm12` (`ADD_e`, AArch64 counterpart of `lea [rb + disp]`, `clob = maskNone`). -/
def addImm12 (rd : XReg) (rb : Reg) (disp : UInt16) : List Directive :=
  [ins (w := .W64) (.ADD_e (.low (.reg rd) .W64) (.low rb .W64)
    (.imm { imm := .int64 (Int64.ofNat disp.toNat), shift := .S0 }))]

theorem addImm12_keepsFlags [Host] {k : Nat} {rd : XReg} {rb : Reg} {disp : UInt16}
    {s : MachineData} {post : MachineState → Prop}
    (hc : (addImm12 rd rb disp).IsInfixAt Host.prog k)
    (hk : ∀ s' : MachineData,
      get s' (.reg rd) = get s rb + BitVec.ofNat 64 disp.toNat →
      (∀ r, r ≠ .reg rd → get s' r = get s r) →
      s'.dmem = s.dmem →
      KeepsFlags s s' maskNone →
      Eventually (step1 Host.exe) post ⟨s', Host.addrOf (k + 1)⟩) :
    Eventually (step1 Host.exe) post ⟨s, Host.addrOf k⟩ := by
  have hr : Runs (addImm12 rd rb disp) s (wr s rd (get s rb + BitVec.ofNat 64 disp.toNat)) := by
    refine Runs.single fun p next jmp => ?_
    simp only [step_simp, Reg64s.setRegOrSp, Reg64s.setRegOrSp64, Reg64s.getRegOrSp,
      RegOrSp.base, BitVec.take]
    congr 2
    have hlt : disp.toNat < 65536 := disp.toNat_lt
    have hex : BitVec.ofInt 64 (Int64.ofNat disp.toNat).toInt = BitVec.ofNat 64 disp.toNat := by
      apply BitVec.eq_of_toInt_eq
      simp [Int64.toInt_ofNat_of_lt (by omega : disp.toNat < 2 ^ 63)]
    rw [BitVec.extractLsb'_eq_self, ← hex]
  refine Runs.eventually hr hc ?_
  exact hk _ (get_wr_same _ _ _) (fun r hne => get_wr_of_ne _ _ _ r hne)
    rfl (keepsFlags_refl _ _)

/-- 2d. `csetMove rd c` (`CSINC rd, xzr, xzr, (armNegCond c).toKraken`, `clob = maskNone`):
the single flag → GPR move (`L3`) materializes `0/1` into `rd` and preserves ALL NZCV flags! -/
def csetMove (rd : XReg) (c : ArmCond) : List Directive :=
  [ins (w := .W64) (.CSINC (zr rd .W64) (xzr .W64) (xzr .W64) (armNegCond c).toKraken)]

theorem csetMove_keepsFlags [Host] {k : Nat} {rd : XReg} {c : ArmCond} {s : MachineData}
    {post : MachineState → Prop}
    (hc : (csetMove rd c).IsInfixAt Host.prog k)
    (hk : ∀ s' : MachineData,
      get s' (.reg rd) = BitVec.ofNat 64 (c.interp s.status).toNat →
      (∀ r, r ≠ .reg rd → get s' r = get s r) →
      s'.dmem = s.dmem →
      KeepsFlags s s' maskNone →
      Eventually (step1 Host.exe) post ⟨s', Host.addrOf (k + 1)⟩) :
    Eventually (step1 Host.exe) post ⟨s, Host.addrOf k⟩ := by
  have hr : Runs (csetMove rd c) s (wr s rd (BitVec.ofNat 64 (c.interp s.status).toNat)) := by
    refine Runs.single fun p next jmp => ?_
    simp only [step_simp, Reg64s.getRegOrZr_xzr]
    have hneg : (armNegCond c).toKraken.interp s.status = !(c.interp s.status) :=
      armNegCond_interp c s.status
    rw [hneg]
    cases c.interp s.status <;> rfl
  refine Runs.eventually hr hc ?_
  exact hk _ (get_wr_same _ _ _) (fun r hne => get_wr_of_ne _ _ _ r hne)
    rfl (keepsFlags_refl _ _)

/-- 2e. `ADC rd, ra, rb` (`clob = maskNone`): consumes `.cs` (`status.c`) without clobbering ANY flag! -/
def adc64 (rd ra rb : XReg) : List Directive :=
  [ins (w := .W64) (.ADC (zr rd .W64) (zr ra .W64) (zr rb .W64))]

theorem adc64_keepsFlags [Host] {k : Nat} {rd ra rb : XReg} {s : MachineData}
    {post : MachineState → Prop}
    (hc : (adc64 rd ra rb).IsInfixAt Host.prog k)
    (hk : ∀ s' : MachineData,
      let cin := ArmCond.cs.interp s.status
      get s' (.reg rd) = get s (.reg ra) + get s (.reg rb) + BitVec.ofNat 64 cin.toNat →
      (∀ r, r ≠ .reg rd → get s' r = get s r) →
      s'.dmem = s.dmem →
      KeepsFlags s s' maskNone →
      Eventually (step1 Host.exe) post ⟨s', Host.addrOf (k + 1)⟩) :
    Eventually (step1 Host.exe) post ⟨s, Host.addrOf k⟩ := by
  have hr : Runs (adc64 rd ra rb) s
      (wr s rd (get s (.reg ra) + get s (.reg rb) + BitVec.ofNat 64 (ArmCond.cs.interp s.status).toNat)) := by
    refine Runs.single fun p next jmp => ?_
    simp only [step_simp, ArmCond.interp, ArmCond.toKraken, CondCode.interp, BitVec.setWidth_eq]
    rfl
  refine Runs.eventually hr hc ?_
  exact hk _ (get_wr_same _ _ _) (fun r hne => get_wr_of_ne _ _ _ r hne)
    rfl (keepsFlags_refl _ _)

/-- 2f. `SBCS rd, ra, rb` (`clob = maskNZCV`): borrow-inversion proof for `T9`!
With `borrow` cached in `.flag .cc` (`ArmCond.cc.interp status = !status.c`), `SBCS` consumes
`borrow_in` from `.cc`, writes `a - b - borrow_in` to `rd`, and writes `borrow_out` back to `.cc`,
matching `OpCode.subb` (`decide (a.toNat < b.toNat + borrow_in.toNat)`) with zero extra instructions! -/
def sbcs64 (rd ra rb : XReg) : List Directive :=
  [ins (w := .W64) (.SBCS (zr rd .W64) (zr ra .W64) (zr rb .W64))]

private theorem sbcs_borrow_inv (a b : BitVec 64) (cflag : Bool) :
    (!decide ((a.unsigned : Int) ≥ b.unsigned + (if cflag = true then 0 else 1))) =
      decide (a.toNat < b.toNat + (!cflag).toNat) := by
  dsimp only [BitVec.unsigned]
  cases cflag
  · by_cases h : a.toNat < b.toNat + 1
    · have hge : ¬ ((a.toNat : Int) ≥ b.toNat + 1) := by omega
      simp [h, hge]
    · have hge : (a.toNat : Int) ≥ b.toNat + 1 := by omega
      simp [h, hge]
  · by_cases h : a.toNat < b.toNat
    · simp [h]
    · simp [h]; omega

theorem sbcs64_borrow_spec [Host] {k : Nat} {rd ra rb : XReg} {s : MachineData}
    {post : MachineState → Prop}
    (hc : (sbcs64 rd ra rb).IsInfixAt Host.prog k)
    (hk : ∀ s' : MachineData,
      let a := get s (.reg ra)
      let b := get s (.reg rb)
      let bin := ArmCond.cc.interp s.status
      get s' (.reg rd) = a - b - BitVec.ofNat 64 bin.toNat →
      ArmCond.cc.interp s'.status = decide (a.toNat < b.toNat + bin.toNat) →
      (∀ r, r ≠ .reg rd → get s' r = get s r) →
      s'.dmem = s.dmem →
      KeepsFlags s s' maskNZCV →
      Eventually (step1 Host.exe) post ⟨s', Host.addrOf (k + 1)⟩) :
    Eventually (step1 Host.exe) post ⟨s, Host.addrOf k⟩ := by
  refine Host.eventually_of_interp_cps (List.isInfixAt_singleton.mp hc) ?_
  simp only [step_simp, BitVec.setWidth_eq]
  refine hk _ ?_ ?_ ?_ rfl ?_
  · simp [get_reg, ArmCond.interp, ArmCond.toKraken]
  · simp only [ArmCond.interp, ArmCond.toKraken, CondCode.interp, StatusFlags.from_result, get_reg]
    exact sbcs_borrow_inv (s.regs.getXReg ra).toBitVec (s.regs.getXReg rb).toBitVec s.status.c
  · intro r hne
    exact get_wr_of_ne { s with status := _ } rd _ r hne
  · refine keepsFlags_of_bits ?_ ?_ ?_ ?_
    all_goals (intro hbit; simp [maskNZCV] at hbit)

end SpikeS2.Arm64

#print axioms SpikeS2.Arm64.kraken_nv_always_true
#print axioms SpikeS2.Arm64.mov_reg_keepsFlags
#print axioms SpikeS2.Arm64.movzZero64_keepsFlags
#print axioms SpikeS2.Arm64.addImm12_keepsFlags
#print axioms SpikeS2.Arm64.csetMove_keepsFlags
#print axioms SpikeS2.Arm64.adc64_keepsFlags
#print axioms SpikeS2.Arm64.sbcs64_borrow_spec
