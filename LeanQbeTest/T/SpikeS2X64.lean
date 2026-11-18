module

public import Kraken.X64.OmniSemantics
public import Kraken.X64.Regs
public import Kraken.X64.WP
public import LeanQbe.Amd64.Targ
public import LeanQbe.Amd64.IselLemmas
public import LeanQbe.StepSimp

/-!
# Spike S2 (X64): Flag-Frame Preservation under Clobber Masks (Locks L3–L6)

Standalone verification against `Kraken.X64.OmniSemantics` (`0 sorry`, `-DwarningAsError=true`)
proving the `G7` / `L3`–`L6` read-only flag cache and clobber-mask frame laws on x86-64:

1. **Clobber-mask & condition-read model (`FlagMask := BitVec 8`):**
   * Bit layout: `CF=0, PF=1, AF=2, ZF=3, SF=4, OF=5`.
   * `x64CondReads : CondCode → FlagMask` maps all 16 x64 condition codes (`o, no, c, nc, z, nz,
     be, a, s, ns, p, np, l, ge, le, g`) to their exact status-bit dependencies (note: no `CondCode`
     reads `AF`).
   * `x64NegCond : CondCode → CondCode` negates `CondCode.interp` while preserving `x64CondReads`.
   * Generic kill law (`flagCacheHolds_killFlags`): after any snippet satisfying `KeepsFlags s s' clob`,
     dropping flag entries whose `reads` overlaps `clob` preserves all remaining flag entries.

2. **Move-class & partial-clobber snippets in `Kraken.X64` (`Host.eventually_of_interp_cps`):**
   * `mov %rs, %rd` (`movD`): `clob = 0#8` (preserves all 16 `CondCode`s).
   * `mov $0, %rd` and general `mov $c, %rd` (`moviD`): `clob = 0#8` (preserves all 16 `CondCode`s),
     plus explicit counterexample showing `xor %edx, %edx` clobbers `CF` (killing carry chains).
   * `lea disp(%ra, %rb, scale), %rd` (`lea`): `clob = 0#8` (preserves all 16 `CondCode`s).
   * `setcc cc %dl; movzbl %dl, %edx` (`Move.setcc` flag → GPR): `clob = 0#8` (materializes `0/1`
     into `rd` while preserving all 16 `CondCode`s).
   * `adcx %rs, %rd`: `clob = maskCF` — writes `(sum, cout)` into `(rd, .c)` and preserves all
     unread conditions (including `.o`/`.no` for interleaved `adox` chains, and `.z`/`.nz`).
   * `adox %rs, %rd`: `clob = maskOF` — writes `(sum, cout)` into `(rd, .o)` and preserves all
     unread conditions (including `.c`/`.nc` for interleaved `adcx` chains).
   * `dec %rd`: `clob = maskDecInc` — sets `.z`/`.nz` for loop exit while preserving `.c`/`.nc` (`CF`)
     across loop back-edges (`G12d`).
   * **Demonic undefined flags (`Effects.undefined` → `∀ v` in `Effects.All`):**
     * `rol $c, %rd`: `OF` is demonically chosen when `c % 64 > 1`, yet `clob = maskCF ||| maskOF`
       frames `.z`/`.nz`/`.s`/`.ns`/`.p`/`.np` across every demonic branch.
-/

set_option autoImplicit false

@[expose] public section

namespace SpikeS2.X64

open LeanQbe Amd64

/-! ## 1. Clobber Masks and `CondCode` Read Masks -/

abbrev FlagMask := BitVec 8

def maskNone : FlagMask := 0x00#8
def maskCF   : FlagMask := 0x01#8 -- bit 0
def maskPF   : FlagMask := 0x02#8 -- bit 1
def maskAF   : FlagMask := 0x04#8 -- bit 2
def maskZF   : FlagMask := 0x08#8 -- bit 3
def maskSF   : FlagMask := 0x10#8 -- bit 4
def maskOF   : FlagMask := 0x20#8 -- bit 5
def maskAll  : FlagMask := 0xFF#8

/-- `dec` / `inc` clobber `PF, AF, ZF, SF, OF` while leaving `CF` untouched. -/
def maskDecInc : FlagMask := maskPF ||| maskAF ||| maskZF ||| maskSF ||| maskOF

@[reducible] def FlagMask.disjoint (reads clob : FlagMask) : Bool :=
  (reads &&& clob) == 0#8

/-- Architectural status bits read by each x64 `CondCode`. -/
def x64CondReads : CondCode → FlagMask
  | .o  | .no => maskOF
  | .c  | .nc => maskCF
  | .z  | .nz => maskZF
  | .be | .a  => maskCF ||| maskZF
  | .s  | .ns => maskSF
  | .p  | .np => maskPF
  | .l  | .ge => maskSF ||| maskOF
  | .le | .g  => maskZF ||| maskSF ||| maskOF

/-- Exact negation of each x64 `CondCode`. -/
def x64NegCond : CondCode → CondCode
  | .o  => .no | .no => .o
  | .c  => .nc | .nc => .c
  | .z  => .nz | .nz => .z
  | .be => .a  | .a  => .be
  | .s  => .ns | .ns => .s
  | .p  => .np | .np => .p
  | .l  => .ge | .ge => .l
  | .le => .g  | .g  => .le

theorem x64NegCond_interp (cc : CondCode) (st : StatusFlags) :
    (x64NegCond cc).interp st = !(cc.interp st) := by
  rcases st with ⟨cf, pf, _, zf, sf, of_⟩
  cases cc <;> cases cf <;> cases pf <;> cases zf <;> cases sf <;> cases of_ <;> rfl

theorem x64NegCond_reads (cc : CondCode) :
    x64CondReads (x64NegCond cc) = x64CondReads cc := by
  cases cc <;> rfl

/-- L4 Flag-Frame Clause: every condition reading no bit in `clob` evaluates identically in `s'` and `s`. -/
def KeepsFlags (s s' : MachineData) (clob : FlagMask) : Prop :=
  ∀ cc : CondCode, FlagMask.disjoint (x64CondReads cc) clob = true →
    cc.interp s'.status = cc.interp s.status

theorem keepsFlags_refl (s : MachineData) (clob : FlagMask) : KeepsFlags s s clob :=
  fun _ _ => rfl

theorem keepsFlags_of_status_eq {s s' : MachineData} (h : s'.status = s.status) (clob : FlagMask) :
    KeepsFlags s s' clob := by
  intro cc _; rw [h]

private theorem getLsbD_false_of_and_zero {m clob : BitVec 8} {i : Nat}
    (h : m &&& clob = 0#8) (hm : m.getLsbD i = true) : clob.getLsbD i = false := by
  have hi : (m &&& clob).getLsbD i = false := by rw [h]; simp
  rw [BitVec.getLsbD_and, hm, Bool.true_and] at hi
  exact hi

theorem keepsFlags_mono {s s' : MachineData} {m₁ m₂ : FlagMask}
    (h : KeepsFlags s s' m₁) (hsub : m₁ &&& ~~~m₂ = 0#8) : KeepsFlags s s' m₂ := by
  intro cc hdisj
  apply h cc
  simp only [FlagMask.disjoint, beq_iff_eq] at hdisj ⊢
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  have h1 : (m₁ &&& ~~~m₂).getLsbD ↑i = false := by rw [hsub]; simp
  have h2 : (x64CondReads cc &&& m₂).getLsbD ↑i = false := by rw [hdisj]; simp
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_zero] at h1 h2 ⊢
  cases hri : (x64CondReads cc).getLsbD ↑i <;> cases hm1 : m₁.getLsbD ↑i <;>
    cases hm2 : m₂.getLsbD ↑i <;> simp_all

/-- Bit-level sufficient condition for `KeepsFlags`: if every individual status bit clear in `clob`
is preserved between `s.status` and `s'.status`, then `KeepsFlags s s' clob` holds for all 16 `CondCode`s. -/
theorem keepsFlags_of_bits {s s' : MachineData} {clob : FlagMask}
    (hcf : clob.getLsbD 0 = false → s'.status.cf = s.status.cf)
    (hpf : clob.getLsbD 1 = false → s'.status.pf = s.status.pf)
    (hzf : clob.getLsbD 3 = false → s'.status.zf = s.status.zf)
    (hsf : clob.getLsbD 4 = false → s'.status.sf = s.status.sf)
    (hof : clob.getLsbD 5 = false → s'.status.of = s.status.of) :
    KeepsFlags s s' clob := by
  intro cc hdisj
  simp only [FlagMask.disjoint, beq_iff_eq] at hdisj
  cases cc <;> simp only [x64CondReads, CondCode.interp] at hdisj ⊢
  · rw [hof (getLsbD_false_of_and_zero hdisj rfl)]
  · rw [hof (getLsbD_false_of_and_zero hdisj rfl)]
  · rw [hcf (getLsbD_false_of_and_zero hdisj rfl)]
  · rw [hcf (getLsbD_false_of_and_zero hdisj rfl)]
  · rw [hzf (getLsbD_false_of_and_zero hdisj rfl)]
  · rw [hzf (getLsbD_false_of_and_zero hdisj rfl)]
  · rw [hcf (getLsbD_false_of_and_zero hdisj rfl), hzf (getLsbD_false_of_and_zero hdisj rfl)]
  · rw [hcf (getLsbD_false_of_and_zero hdisj rfl), hzf (getLsbD_false_of_and_zero hdisj rfl)]
  · rw [hsf (getLsbD_false_of_and_zero hdisj rfl)]
  · rw [hsf (getLsbD_false_of_and_zero hdisj rfl)]
  · rw [hpf (getLsbD_false_of_and_zero hdisj rfl)]
  · rw [hpf (getLsbD_false_of_and_zero hdisj rfl)]
  · rw [hsf (getLsbD_false_of_and_zero hdisj rfl), hof (getLsbD_false_of_and_zero hdisj rfl)]
  · rw [hsf (getLsbD_false_of_and_zero hdisj rfl), hof (getLsbD_false_of_and_zero hdisj rfl)]
  · rw [hsf (getLsbD_false_of_and_zero hdisj rfl), hof (getLsbD_false_of_and_zero hdisj rfl),
        hzf (getLsbD_false_of_and_zero hdisj rfl)]
  · rw [hzf (getLsbD_false_of_and_zero hdisj rfl), hsf (getLsbD_false_of_and_zero hdisj rfl),
        hof (getLsbD_false_of_and_zero hdisj rfl)]

/-! ## 2. Generic Flag-Cache Kill Rule (Lock L5) -/

/-- Symbolic flag-cache entry `(varOrImmId, cond)`. -/
abbrev FlagCache := List (Nat × CondCode)

def FlagCacheHolds (env : Nat → Bool) (s : MachineData) (F : FlagCache) : Prop :=
  ∀ x cc, (x, cc) ∈ F → cc.interp s.status = env x

/-- L5 generic kill rule: drop every cached condition whose read mask overlaps `clob`. -/
def killFlags (clob : FlagMask) (F : FlagCache) : FlagCache :=
  F.filter fun (_, cc) => FlagMask.disjoint (x64CondReads cc) clob

theorem killFlags_none (F : FlagCache) : killFlags maskNone F = F := by
  induction F with
  | nil => rfl
  | cons p rest ih =>
    rcases p with ⟨x, cc⟩
    have hd : FlagMask.disjoint (x64CondReads cc) maskNone = true := by
      cases cc <;> rfl
    simp only [killFlags, List.filter_cons, hd, ↓reduceIte]
    exact congrArg ((x, cc) :: ·) ih

theorem flagCacheHolds_killFlags {env : Nat → Bool} {s s' : MachineData} {clob : FlagMask}
    {F : FlagCache} (hF : FlagCacheHolds env s F) (hK : KeepsFlags s s' clob) :
    FlagCacheHolds env s' (killFlags clob F) := by
  intro x cc hmem
  simp only [killFlags, List.mem_filter] at hmem
  rw [hK cc hmem.2]
  exact hF x cc hmem.1

/-- `adcx` explicitly preserves `.o` and `.no` (`OF` carry chain for `adox`)! -/
theorem adcx_preserves_OF {s s' : MachineData} (hK : KeepsFlags s s' maskCF) :
    CondCode.o.interp s'.status = CondCode.o.interp s.status ∧
    CondCode.no.interp s'.status = CondCode.no.interp s.status :=
  ⟨hK .o rfl, hK .no rfl⟩

/-- Contrast (Lock L4 hazard): `xor %edx, %edx` does NOT satisfy `KeepsFlags s s' maskNone` when `s.status.cf = true`,
because `xor` clears `CF` to `false` (and demonically chooses `AF`). -/
theorem xor_self_kills_cf [Labels] (rd : Reg64) (p : Std.Rco Int64) (s : MachineData) (hcf : s.status.cf = true) :
    ∃ post : MachineState → Prop,
      (∀ s', s'.regs.get64 rd = 0#64 → KeepsFlags s s' maskNone → post ⟨s', p.upper⟩) ∧
      ¬ ((Operation.xor (.reg (d rd)) (.reg (d rd))).interp
          (address_size := ⟨.W64⟩) p s (fun s' => .done ⟨s', p.upper⟩) (fun pc s' => .done ⟨s', pc⟩)).All post := by
  refine ⟨fun st => st.data.status.cf = true, ?_, ?_⟩
  · intro s' _ hK
    have hc := hK .c rfl
    simpa [CondCode.interp, hcf] using hc
  · simp only [Operation.interp, Operand.interp, RegOrMem.interp, MachineData.set,
      MachineData.setReg, Effects.All, StatusFlags.from_result]
    intro hall
    have hfalse := hall false
    simp at hfalse

private theorem adcx_sum_carry (a b : BitVec 64) (cin : Bool) :
    ((a + b + BitVec.ofNat 64 cin.toNat).unsigned != a.unsigned + b.unsigned + (cin.toNat : Int)) =
      decide (2 ^ 64 ≤ a.toNat + b.toNat + cin.toNat) := by
  dsimp only [BitVec.unsigned]
  have ha := a.isLt
  have hb := b.isLt
  have hc : cin.toNat ≤ 1 := by cases cin <;> decide
  have hv : (a + b + BitVec.ofNat 64 cin.toNat).toNat = (a.toNat + b.toNat + cin.toNat) % 2 ^ 64 := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  rw [hv]
  by_cases hle : 2 ^ 64 ≤ a.toNat + b.toNat + cin.toNat
  · have hmod : (a.toNat + b.toNat + cin.toNat) % 2 ^ 64 = a.toNat + b.toNat + cin.toNat - 2 ^ 64 := by
      omega
    rw [hmod, decide_eq_true hle]
    simp only [bne_iff_ne, ne_eq]
    omega
  · have hmod : (a.toNat + b.toNat + cin.toNat) % 2 ^ 64 = a.toNat + b.toNat + cin.toNat :=
      Nat.mod_eq_of_lt (by omega)
    rw [hmod, decide_eq_false hle]
    simp

/-! ## 3. Snippet Flag-Frame Theorems in Kraken X64 -/

section Snippets
variable [Host]

/-- 3a. `mov %rs, %rd` (`clob = maskNone`): preserves all 16 condition codes (`KeepsFlags s s' 0#8`). -/
theorem mov_keepsFlags {k : Nat} {rd rs : Reg64} {s : MachineData} {post : MachineState → Prop}
    (hc : [movD rd rs].IsInfixAt Host.prog k)
    (hk : ∀ s' : MachineData,
      s'.regs.get64 rd = s.regs.get64 rs →
      (∀ r, r ≠ rd → s'.regs.get64 r = s.regs.get64 r) →
      s'.dmem = s.dmem →
      KeepsFlags s s' maskNone →
      Run (k + 1) s' post) :
    Run k s post := by
  refine Host.eventually_of_interp_cps (List.isInfixAt_singleton.mp hc) ?_
  simp only [step_simp, movD]
  exact hk _ (Reg64s.get64_set64_same s.regs rd _)
    (fun r hne => Reg64s.get64_set64_of_ne s.regs rd r _ hne.symm)
    rfl (keepsFlags_refl _ _)

/-- 3b. `mov $0, %rd` (and general `mov $c, %rd`, `clob = maskNone`): preserves all 16 condition codes! -/
theorem movi_keepsFlags {k : Nat} {rd : Reg64} {c : BitVec 64} {s : MachineData}
    {post : MachineState → Prop}
    (hc : [moviD rd c].IsInfixAt Host.prog k)
    (hk : ∀ s' : MachineData,
      s'.regs.get64 rd = c →
      (∀ r, r ≠ rd → s'.regs.get64 r = s.regs.get64 r) →
      s'.dmem = s.dmem →
      KeepsFlags s s' maskNone →
      Run (k + 1) s' post) :
    Run k s post := by
  refine Host.eventually_of_interp_cps (List.isInfixAt_singleton.mp hc) ?_
  simp only [step_simp, moviD]
  refine hk _ ?_ (fun r hne => Reg64s.get64_set64_of_ne s.regs rd r _ hne.symm) rfl (keepsFlags_refl _ _)
  rw [Reg64s.get64_set64_same]
  simp [BitVec.truncate]

/-- Specialization: `mov $0, %rd` keeps `CF` and `OF` carry chains intact (`clob = 0#8`). -/
theorem movi_zero_keepsFlags {k : Nat} {rd : Reg64} {s : MachineData} {post : MachineState → Prop}
    (hc : [moviD rd 0#64].IsInfixAt Host.prog k)
    (hk : ∀ s' : MachineData,
      s'.regs.get64 rd = 0#64 →
      (∀ r, r ≠ rd → s'.regs.get64 r = s.regs.get64 r) →
      s'.dmem = s.dmem →
      KeepsFlags s s' maskNone →
      Run (k + 1) s' post) :
    Run k s post :=
  movi_keepsFlags hc hk

/-- 3c. `lea addr, %rd` (`clob = maskNone`): 64-bit address calculation preserves ALL 16 condition codes! -/
def leaD (rd : Reg64) (addr : AddrExpr) : Directive :=
  ins (.lea (q rd) addr)

theorem lea_keepsFlags {k : Nat} {rd : Reg64} {addr : AddrExpr} {s : MachineData}
    {post : MachineState → Prop}
    (hc : [leaD rd addr].IsInfixAt Host.prog k)
    (hk : ∀ s' : MachineData,
      (∀ r, r ≠ rd → s'.regs.get64 r = s.regs.get64 r) →
      s'.dmem = s.dmem →
      KeepsFlags s s' maskNone →
      Run (k + 1) s' post) :
    Run k s post := by
  refine Host.eventually_of_interp_cps (List.isInfixAt_singleton.mp hc) ?_
  simp only [step_simp, leaD]
  exact hk _ (fun r hne => Reg64s.get64_set64_of_ne s.regs rd r _ hne.symm) rfl (keepsFlags_refl _ _)

/-- Concrete `[base + disp]` `lea` value + flag preservation (`clob = maskNone`). -/
theorem lea_base_disp_keepsFlags {k : Nat} {rd rb : Reg64} {disp : Int64} {s : MachineData}
    {post : MachineState → Prop}
    (hc : [leaD rd { base := some (.reg rb), idx := none, disp := .int64 disp }].IsInfixAt Host.prog k)
    (hk : ∀ s' : MachineData,
      s'.regs.get64 rd = s.regs.get64 rb + disp.toBitVec →
      (∀ r, r ≠ rd → s'.regs.get64 r = s.regs.get64 r) →
      s'.dmem = s.dmem →
      KeepsFlags s s' maskNone →
      Run (k + 1) s' post) :
    Run k s post := by
  refine Host.eventually_of_interp_cps (List.isInfixAt_singleton.mp hc) ?_
  simp only [step_simp, leaD, AddrExpr.interp_base_disp]
  refine hk _ ?_ (fun r hne => Reg64s.get64_set64_of_ne s.regs rd r _ hne.symm) rfl (keepsFlags_refl _ _)
  rw [Reg64s.get64_set64_same]
  simp

/-- 3d. `Move.setcc` (`setcc %rd_b; movzbl %rd_b, %rd_d`, `clob = maskNone`):
the single flag → GPR move (Lock L3) materializes `0/1` into `rd` while preserving ALL flags! -/
def setccMove (rd : Reg64) (cc : CondCode) : List Directive :=
  [ins8 (.setcc cc (.reg (b8 rd))), ins32 (.movzx (.reg (d rd)) (.reg (b8 rd)))]

theorem setccMove_keepsFlags {k : Nat} {rd : Reg64} {cc : CondCode} {s : MachineData}
    {post : MachineState → Prop}
    (hc : (setccMove rd cc).IsInfixAt Host.prog k)
    (hk : ∀ s' : MachineData,
      s'.regs.get64 rd = BitVec.ofNat 64 (cc.interp s.status).toNat →
      (∀ r, r ≠ rd → s'.regs.get64 r = s.regs.get64 r) →
      s'.dmem = s.dmem →
      KeepsFlags s s' maskNone →
      Run (k + 2) s' post) :
    Run k s post := by
  obtain ⟨h0, hc1⟩ := hc.cons
  obtain ⟨h1, -⟩ := hc1.cons
  refine Host.eventually_of_interp_cps h0 ?_
  simp only [step_simp]
  refine Host.eventually_of_interp_cps h1 ?_
  simp only [step_simp]
  refine hk _ ?_ ?_ rfl (keepsFlags_refl _ _)
  · simp only [Reg64s.set, Reg64s.get64_set64_same]
    change BitVec.zeroExtend 64 (BitVec.zeroExtend 32
      (((s.regs.get64 rd).replaceLow (BitVec.ofNat 8 (cc.interp s.status).toNat)).setWidth 8)) = _
    rw [replaceLow_setWidth]
    cases cc.interp s.status <;> rfl
  · intro r hne
    simp only [Reg64s.set]
    rw [Reg64s.get64_set64_of_ne _ rd r _ hne.symm, Reg64s.get64_set64_of_ne _ rd r _ hne.symm]

/-- 3e. `adcx %rs, %rd` (`clob = maskCF`): reads `CF`, writes `(sum, cout)` to `(rd, CF)`,
and preserves all conditions disjoint from `maskCF` (in particular `.o`/`.no` for interleaved `adox`!). -/
def adcx64D (rd rs : Reg64) : Directive :=
  ins (.adcx (q rd) (.reg (q rs)))

theorem adcx64_keepsFlags {k : Nat} {rd rs : Reg64} {s : MachineData} {post : MachineState → Prop}
    (hc : [adcx64D rd rs].IsInfixAt Host.prog k)
    (hk : ∀ s' : MachineData,
      let a := s.regs.get64 rd
      let b := s.regs.get64 rs
      let cin := CondCode.c.interp s.status
      s'.regs.get64 rd = a + b + BitVec.ofNat 64 cin.toNat →
      CondCode.c.interp s'.status = decide (2 ^ 64 ≤ a.toNat + b.toNat + cin.toNat) →
      (∀ r, r ≠ rd → s'.regs.get64 r = s.regs.get64 r) →
      s'.dmem = s.dmem →
      KeepsFlags s s' maskCF →
      Run (k + 1) s' post) :
    Run k s post := by
  refine Host.eventually_of_interp_cps (List.isInfixAt_singleton.mp hc) ?_
  simp only [step_simp, Reg.interp, adcx64D, get_q]
  have hsum : s.regs.get64 rs + s.regs.get64 rd + BitVec.ofNat 64 s.status.cf.toNat =
      s.regs.get64 rd + s.regs.get64 rs + BitVec.ofNat 64 s.status.cf.toNat := by
    rw [BitVec.add_comm (s.regs.get64 rs) (s.regs.get64 rd)]
  have hcout : ((s.regs.get64 rs + s.regs.get64 rd + BitVec.ofNat 64 s.status.cf.toNat).unsigned !=
      (s.regs.get64 rs).unsigned + (s.regs.get64 rd).unsigned + (s.status.cf.toNat : Int)) =
      decide (2 ^ 64 ≤ (s.regs.get64 rd).toNat + (s.regs.get64 rs).toNat + s.status.cf.toNat) := by
    rw [hsum]
    have hcomm : (s.regs.get64 rs).unsigned + (s.regs.get64 rd).unsigned =
        (s.regs.get64 rd).unsigned + (s.regs.get64 rs).unsigned := Int.add_comm _ _
    rw [hcomm]
    exact adcx_sum_carry (s.regs.get64 rd) (s.regs.get64 rs) s.status.cf
  refine hk _ ?_ ?_ ?_ rfl ?_
  · simp only [Reg64s.get64_set64_same, CondCode.interp]
    exact hsum
  · simp only [CondCode.interp]
    exact hcout
  · intro r hne
    exact Reg64s.get64_set64_of_ne s.regs rd r _ hne.symm
  · refine keepsFlags_of_bits ?_ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    intro hbit; simp [maskCF] at hbit

/-- 3f. `adox %rs, %rd` (`clob = maskOF`): dual chain writes `(rd, OF)` and preserves `CF`! -/
def adox64D (rd rs : Reg64) : Directive :=
  ins (.adox (q rd) (.reg (q rs)))

theorem adox64_keepsFlags {k : Nat} {rd rs : Reg64} {s : MachineData} {post : MachineState → Prop}
    (hc : [adox64D rd rs].IsInfixAt Host.prog k)
    (hk : ∀ s' : MachineData,
      let a := s.regs.get64 rd
      let b := s.regs.get64 rs
      let cin := CondCode.o.interp s.status
      s'.regs.get64 rd = a + b + BitVec.ofNat 64 cin.toNat →
      CondCode.o.interp s'.status = decide (2 ^ 64 ≤ a.toNat + b.toNat + cin.toNat) →
      (∀ r, r ≠ rd → s'.regs.get64 r = s.regs.get64 r) →
      s'.dmem = s.dmem →
      KeepsFlags s s' maskOF →
      Run (k + 1) s' post) :
    Run k s post := by
  refine Host.eventually_of_interp_cps (List.isInfixAt_singleton.mp hc) ?_
  simp only [step_simp, Reg.interp, adox64D, get_q]
  have hsum : s.regs.get64 rs + s.regs.get64 rd + BitVec.ofNat 64 s.status.of.toNat =
      s.regs.get64 rd + s.regs.get64 rs + BitVec.ofNat 64 s.status.of.toNat := by
    rw [BitVec.add_comm (s.regs.get64 rs) (s.regs.get64 rd)]
  have hcout : ((s.regs.get64 rs + s.regs.get64 rd + BitVec.ofNat 64 s.status.of.toNat).unsigned !=
      (s.regs.get64 rs).unsigned + (s.regs.get64 rd).unsigned + (s.status.of.toNat : Int)) =
      decide (2 ^ 64 ≤ (s.regs.get64 rd).toNat + (s.regs.get64 rs).toNat + s.status.of.toNat) := by
    rw [hsum]
    have hcomm : (s.regs.get64 rs).unsigned + (s.regs.get64 rd).unsigned =
        (s.regs.get64 rd).unsigned + (s.regs.get64 rs).unsigned := Int.add_comm _ _
    rw [hcomm]
    exact adcx_sum_carry (s.regs.get64 rd) (s.regs.get64 rs) s.status.of
  refine hk _ ?_ ?_ ?_ rfl ?_
  · simp only [Reg64s.get64_set64_same, CondCode.interp]
    exact hsum
  · simp only [CondCode.interp]
    exact hcout
  · intro r hne
    exact Reg64s.get64_set64_of_ne s.regs rd r _ hne.symm
  · refine keepsFlags_of_bits (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) ?_
    intro hbit; simp [maskOF] at hbit

/-- 3g. `dec %rd` (`clob = maskDecInc`): decrements `rd`, sets `.nz` (`rd - 1 ≠ 0`), and
preserves `CF` (`.c`/`.nc`) for G12d loop-carried carry chains! -/
def dec64D (rd : Reg64) : Directive :=
  ins (.dec (.reg (q rd)))

theorem dec64_keepsCF {k : Nat} {rd : Reg64} {s : MachineData} {post : MachineState → Prop}
    (hc : [dec64D rd].IsInfixAt Host.prog k)
    (hk : ∀ s' : MachineData,
      s'.regs.get64 rd = s.regs.get64 rd - 1#64 →
      CondCode.nz.interp s'.status = decide (s.regs.get64 rd - 1#64 ≠ 0#64) →
      (∀ r, r ≠ rd → s'.regs.get64 r = s.regs.get64 r) →
      s'.dmem = s.dmem →
      KeepsFlags s s' maskDecInc →
      Run (k + 1) s' post) :
    Run k s post := by
  refine Host.eventually_of_interp_cps (List.isInfixAt_singleton.mp hc) ?_
  simp only [step_simp, dec64D, StatusFlags.from_result]
  refine hk _ (Reg64s.get64_set64_same s.regs rd _) ?_ ?_ rfl ?_
  · by_cases h0 : s.regs.get64 rd - 1#64 = 0#64 <;> simp [CondCode.interp, BitVec.zero, h0]
  · intro r hne; exact Reg64s.get64_set64_of_ne s.regs rd r _ hne.symm
  · refine keepsFlags_of_bits (fun _ => rfl) ?_ ?_ ?_ ?_
    all_goals (intro hbit; simp [maskDecInc, maskPF, maskAF, maskZF, maskSF, maskOF] at hbit)

/-- 3h. Demonic undefined flags (`Effects.undefined` → `∀ v` in `Effects.All`):
`rol $c, %rd` demonically chooses `OF` when `c % 64 > 1`, yet `KeepsFlags s s' (maskCF ||| maskOF)`
holds across EVERY demonic choice (`ZF`, `SF`, `PF` preserved). -/
def rolImm64D (rd : Reg64) (cnt : UInt8) : Directive :=
  ins (.rol (.reg (q rd)) (.imm8 (.int64 (Int64.ofNat cnt.toNat))))

theorem rolImm64_demonic_keepsFlags {k : Nat} {rd : Reg64} {cnt : UInt8} {s : MachineData}
    {post : MachineState → Prop}
    (hc : [rolImm64D rd cnt].IsInfixAt Host.prog k)
    (hk : ∀ s' : MachineData,
      s'.regs.get64 rd = (s.regs.get64 rd).rotateLeft (cnt.toNat % 64) →
      (∀ r, r ≠ rd → s'.regs.get64 r = s.regs.get64 r) →
      s'.dmem = s.dmem →
      KeepsFlags s s' (maskCF ||| maskOF) →
      Run (k + 1) s' post) :
    Run k s post := by
  refine Host.eventually_of_interp_cps (List.isInfixAt_singleton.mp hc) ?_
  simp only [step_simp, rolImm64D, ShiftCountExpr.interpMasked, ShiftCountExpr.interp]
  have hmask : (((Int64.ofNat cnt.toNat).toBitVec.take 8).toNat &&& 63) = cnt.toNat % 64 := by
    have hlt : cnt.toNat < 256 := cnt.toNat_lt
    have hex : ((Int64.ofNat cnt.toNat).toBitVec.take 8).toNat = cnt.toNat := by
      have hbv : (Int64.ofNat cnt.toNat).toBitVec.take 8 = BitVec.ofNat 8 cnt.toNat := by
        apply BitVec.eq_of_getLsbD_eq
        intro j hj
        have hj8 : (j : Nat) < 8 := hj
        have hj64 : (j : Nat) < 64 := by omega
        have h1 : ((Int64.ofNat cnt.toNat).toBitVec.take 8).getLsbD ↑j =
            (BitVec.ofNat 64 cnt.toNat).getLsbD ↑j := by
          simp [BitVec.take, hj8]
        rw [h1, BitVec.getLsbD_ofNat, BitVec.getLsbD_ofNat]
        simp [hj8, hj64]
      rw [hbv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
    rw [hex, Nat.and_two_pow_sub_one_eq_mod _ 6]
  rw [hmask]
  by_cases hc0 : (cnt.toNat % 64 == 0) = true
  · simp only [hc0, ↓reduceIte, Effects.All]
    have h0 : cnt.toNat % 64 = 0 := beq_iff_eq.mp hc0
    refine hk _ ?_ (fun r hne => Reg64s.get64_set64_of_ne _ rd r _ hne.symm) rfl (keepsFlags_refl _ _)
    rw [h0, Reg64s.get64_set64_same]
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    simp [BitVec.rotateLeft, BitVec.rotateLeftAux, show (j : Nat) < 64 from hj]
  · simp only [Bool.not_eq_true] at hc0
    simp only [hc0, Bool.false_eq_true, ↓reduceIte]
    by_cases hc1 : (cnt.toNat % 64 == 1) = true
    · simp only [hc1, ↓reduceIte, Effects.All]
      refine hk _ (Reg64s.get64_set64_same _ _ _)
        (fun r hne => Reg64s.get64_set64_of_ne _ rd r _ hne.symm) rfl ?_
      refine keepsFlags_of_bits ?_ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) ?_
      all_goals (intro hbit; simp [maskCF, maskOF] at hbit)
    · simp only [Bool.not_eq_true] at hc1
      simp only [hc1, Bool.false_eq_true, ↓reduceIte, Effects.All]
      intro demonic_of
      refine hk _ (Reg64s.get64_set64_same _ _ _)
        (fun r hne => Reg64s.get64_set64_of_ne _ rd r _ hne.symm) rfl ?_
      refine keepsFlags_of_bits ?_ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) ?_
      all_goals (intro hbit; simp [maskCF, maskOF] at hbit)

end Snippets

end SpikeS2.X64

#print axioms SpikeS2.X64.mov_keepsFlags
#print axioms SpikeS2.X64.movi_zero_keepsFlags
#print axioms SpikeS2.X64.xor_self_kills_cf
#print axioms SpikeS2.X64.lea_base_disp_keepsFlags
#print axioms SpikeS2.X64.setccMove_keepsFlags
#print axioms SpikeS2.X64.adcx64_keepsFlags
#print axioms SpikeS2.X64.adox64_keepsFlags
#print axioms SpikeS2.X64.dec64_keepsCF
#print axioms SpikeS2.X64.rolImm64_demonic_keepsFlags
