module

public import LeanQbe.T.Arm64.Targ
public import LeanQbe.T.MainLemmas
import LeanQbe.T.RegaLemmas
import LeanQbe.T.Logic.MemLemmas
import LeanQbe.T.Arm64.IselLemmas4
import LeanQbe.T.Arm64.IselNarrowLemmas
import LeanQbe.T.Arm64.IselFlagHooksLemmas
import LeanQbe.T.Arm64.IselScrLemmas5
import LeanQbe.T.Arm64.FrameLemmas

/-!
# AAPCS64 Arm64 `LabelClean`, `TargetLayout`, `TargetInit`, & Concrete Lifting

* `armLabelClean : Rega.LabelClean armTarget.toIsa`: discharges compiler-side label uniqueness
  structurally via all verified `NoLab` theorems from `Arm64/{Isel,Frame}Lemmas*` and empty vector
  elimination.
* `armLayout : TargetLayout armTarget`: concrete `Host.ofLayout` using 4-byte uniform layout
  starting at `0x1000`.
* `armInit : TargetInit armTarget 2048 8192`: concrete AAPCS64 initial machine state across
  arbitrary legal scalar argument signatures (`bool`, `bits`), with `sp0 = 0x1000#64`,
  `x30 = ra0 = 0x1234`, and payload bytes at `0x1000#64`.
* `arm64_of_call`, `arm64_of_call_emp`, `arm64_of_returns`, `arm64_of_returns_emp`: project
  `armTarget.FnSpec` to concrete `Kraken.AArch64` `step1 Host.exe` postconditions.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Arm64

open Std Std.ExtHashMap
open LeanQbe.T

/-! ## 1. Structural `Rega.LabelClean armTarget.toIsa` -/

/-- No AArch64 instruction-selection or frame snippet ever emits a `.label` directive, and
`Kraken.Directive.label` is injective. -/
theorem armLabelClean : Rega.LabelClean armTarget.toIsa where
  label_inj _ _ h := Kraken.Directive.label.inj h
  mov := armMov_noLab
  movi := armMovi_noLab
  setcc := armSetcc_noLab
  jmp := armJmp_noLab
  jcc := armJcc_noLab
  jnzGpr := armJnzGpr_noLab
  jnzGprInv _ r inv tgt h l := by cases h; exact armJnzGprInv_noLab r inv tgt l
  op _ _ _ _ _ _ h l := armOp_noLab h l
  testOp _ _ _ _ _ _ _ h l := armTestOp_noLab h l
  cmpZeroJcc _ _ _ _ _ _ h l := armCmpZeroJcc_noLab h l
  testJcc _ _ _ _ _ _ _ h l := armTestJcc_noLab h l
  load _ _ _ _ _ h l := armLoad_noLab h l
  loadSext _ _ _ _ _ _ h l := armLoadSext_noLab h l
  store _ _ _ _ _ h l := armStore_noLab h l
  leaArith _ _ _ _ _ _ _ _ h l := armLeaArith_noLab h l
  loadZextIdx _ _ _ _ _ _ _ _ h l := armLoadZextIdx_noLab h l
  loadSextZextIdx _ _ _ _ _ _ _ _ _ h l := armLoadSextZextIdx_noLab h l
  storeZextIdx _ _ _ _ _ _ _ _ h l := armStoreZextIdx_noLab h l
  leaArithZext _ _ _ _ _ _ _ h l := armLeaArithZext_noLab h l
  cmpMem _ _ _ _ _ _ _ h l := armCmpMem_noLab h l
  shiftAlu _ _ _ _ _ _ _ _ _ h l := armShiftedAlu_noLab h l
  shiftCmp _ _ _ _ _ _ _ _ _ _ h l := armShiftedCmp_noLab h l
  mulHi _ _ _ _ _ _ _ _ h1 h2 l := by cases h1; exact armMulHi_noLab h2 l
  storeScr _ _ _ _ _ _ _ _ h1 h2 l := by cases h1; exact armStoreScr_noLab h2 l
  storeZextIdxScr _ _ _ _ _ _ _ _ _ _ _ h1 h2 l := by cases h1; exact armStoreZextIdxScr_noLab h2 l
  loadScr _ _ _ _ _ _ _ _ h1 h2 l := by cases h1; exact armLoadScr_noLab h2 l
  loadZextIdxScr _ _ _ _ _ _ _ _ _ _ _ h1 h2 l := by cases h1; exact armLoadZextIdxScr_noLab h2 l
  opScr _ _ _ _ _ _ _ _ _ _ _ h1 h2 l := by cases h1; exact armOpScr_noLab h2 l
  clearFlags := armClearFlags_noLab
  vmov _ d := d.elim
  vmovi _ d := d.elim
  vslotSt _ _ s := s.elim
  vslotLd _ d := d.elim
  vop _ _ _ _ _ _ h := nomatch h
  vload _ d := d.elim
  vstore _ s := s.elim
  prologue := armPrologue_noLab
  epilogue := armEpilogue_noLab
  slotSt := armSlotSt_noLab
  slotLd := armSlotLd_noLab
  saveRegs := fun _ base rs h l => by cases h; exact armSaveRegs_noLab base rs l
  restoreRegs := fun _ base rs h l => by cases h; exact armRestoreRegs_noLab base rs l
  canonAbi := armCanonAbi_noLab
  call := armCall_noLab
  exitJmp := armExitJmp_noLab
  ret := armRet_noLab

/-! ## 2. Concrete Kraken AArch64 `TargetLayout` -/

/-- Uniform AArch64 layout: 4 bytes per instruction, 0 bytes per label, base address `0x1000`. -/
@[expose, instance_reducible] def armUniformLayout : Layout where
  start := 0x1000
  instrSize _ := 4
  instrSize_pos _ := by decide

/-- Size per AArch64 directive under `armUniformLayout`. -/
@[expose, reducible] def armDirSize : Directive → Nat
  | .instr _ => 4
  | .label _ => 0
  | .byteArray arr => arr.size
  | .word bytes _ => bytes

/-- Kernel-reducible check that laying out `p` under `armUniformLayout` fits in `2 ^ 64` bytes. -/
@[expose] def armProgSmall (p : List Directive) : Bool :=
  decide ((p.map armDirSize).sum < 2 ^ 64)

private theorem size_map_armUniformLayout :
    ∀ (xs : List Directive) (k : Nat),
      ((xs.mapIdx fun i d =>
          ({ directive := d, size := armUniformLayout.size d (k + i) } :
            Kraken.Sized Directive)).map (·.size)) =
        xs.map armDirSize
  | [], _ => rfl
  | d :: xs, k => by
    rw [List.mapIdx_cons, List.map_cons, List.map_cons]
    have hd : armUniformLayout.size d (k + 0) = armDirSize d := by cases d <;> rfl
    have hrest :
        (xs.mapIdx fun i d' =>
          ({ directive := d', size := armUniformLayout.size d' (k + (i + 1)) } :
            Kraken.Sized Directive)) =
        xs.mapIdx fun i d' =>
          ({ directive := d', size := armUniformLayout.size d' ((k + 1) + i) } :
            Kraken.Sized Directive) := by
      congr 1; funext i d'; rw [show k + (i + 1) = (k + 1) + i from by omega]
    rw [hd, hrest, size_map_armUniformLayout xs (k + 1)]

theorem armUniformLayout_small (p : List Directive) (h : armProgSmall p = true) :
    (armUniformLayout.apply p).sizeBefore p.length < 2 ^ 64 := by
  have hs : (armUniformLayout.apply p).sizeBefore p.length = (p.map armDirSize).sum := by
    simp only [Kraken.Executable.sizeBefore, Kraken.Layout.apply]
    rw [List.take_of_length_le (by simp)]
    simpa using congrArg List.sum (size_map_armUniformLayout p 0)
  rw [hs]
  exact of_decide_eq_true h

@[expose] def armLabelOf? : Directive → Option String
  | .label l => some l
  | _ => none

/-- Concrete AArch64 host layout (`Host.ofLayout` with `armUniformLayout` and `labelsNodupBy`). -/
@[expose] def armLayout : TargetLayout armTarget where
  labelsNodup := labelsNodupBy armLabelOf?
  progSmall := armProgSmall
  layoutOf prog h := .ofLayout prog armUniformLayout (armUniformLayout_small prog h)
  prog_layoutOf _ _ := rfl
  labelsUnique_layoutOf {prog} h hnd :=
    letI : Host := .ofLayout prog armUniformLayout (armUniformLayout_small prog h)
    Host.labelsUnique_of_nodup (labelsNodupBy_nodup armLabelOf? hnd)

/-! ## 3. Concrete Initial Machine State (`armInit : TargetInit armTarget 2048 8192`) -/

/-- `n`-byte zero stack below `sp = 0x1000` and payload `bs` at `0x1000`. -/
@[expose] def armInitMem (n : Nat) (bs : List UInt8) : Mem 64 :=
  (stackZeros n ++ bs).At (0x1000#64 - BitVec.ofNat 64 n)

theorem armInitMem_entry (n : Nat) (bs : List UInt8) (hn : n ≤ 2048) (hbs : bs.length ≤ 8192) :
    armInitMem n bs =⋆
      Eq (bs.At 0x1000#64) ⋆ armTarget.Entry 0x1000#64 0x1234 n ⋆ Std.ExtHashMap.emp := by
  have hzs : (stackZeros n).length = n := stackZeros_length n
  have h1 := Mem.At_append_sep (stackZeros n) bs (0x1000#64 - BitVec.ofNat 64 n)
    (by rw [hzs]; exact Nat.le_trans (Nat.add_le_add hn hbs) (by decide))
  have e1 : 0x1000#64 - BitVec.ofNat 64 n + BitVec.ofNat 64 (stackZeros n).length = 0x1000#64 := by
    rw [hzs, BitVec.sub_add_cancel]
  rw [e1] at h1
  have h0 : (Eq (bs.At 0x1000#64) ⋆
      Eq ((stackZeros n).At (0x1000#64 - BitVec.ofNat 64 n)) ⋆
      Std.ExtHashMap.emp) (armInitMem n bs) := by
    rw [Std.ExtHashMap.sep_emp]
    refine sep_cast (show Eq (armInitMem n bs) (armInitMem n bs) from rfl) ?_
    change Eq ((stackZeros n ++ bs).At (0x1000#64 - BitVec.ofNat 64 n)) = _
    rw [h1, Std.ExtHashMap.sep_comm]
  have hsub : ∀ m, Eq ((stackZeros n).At (0x1000#64 - BitVec.ofNat 64 n)) m →
      armTarget.Entry 0x1000#64 0x1234 n m := by
    intro m hm
    dsimp only [Target.Entry, armTarget, armFrameTarget, armFramePreds]
    simp only [region_zero, Std.ExtHashMap.sep_emp]
    exact ⟨stackZeros n, hzs, hm.symm⟩
  exact sep_mono_mid hsub h0

/-- Encode typed ABI scalar argument value into a 64-bit register word. -/
@[expose] def valToGpr : (t : Ty) → Val t → BitVec 64
  | .bool, b => BitVec.ofNat 64 b.toNat
  | .bits _, v => v.setWidth 64
  | _, _ => 0

/-- Populate AAPCS64 argument registers `x0..x7` with `SP = 0x1000` and `X30 = 0x1234`. -/
@[expose] def setArmAbiRegs :
    {ts : List Ty} → Tup (AbiReg Reg Empty) ts → Tup Val ts → Reg64s
  | [], _, _ => { SP := 0x1000, X30 := (0x1234 : Int64).toUInt64 }
  | t :: _, (loc, locs), (v, vs) =>
    let p := setArmAbiRegs locs vs
    match loc with
    | .gpr (.reg x) => p.setXReg x (valToGpr t v)
    | .gpr .SP => p
    | .vec vr => vr.elim

private theorem armAssignSig_cons {t : Ty} {ts : List Ty} {loc : AbiReg Reg Empty t}
    {locs : Tup (AbiReg Reg Empty) ts} {gs : List Reg} {vs : List Empty}
    (h : armTarget.toIsa.assignSig (t :: ts) gs vs = some (loc, locs)) :
    match loc with
    | .gpr r => ∃ gs', gs = r :: gs' ∧ armTarget.toIsa.assignSig ts gs' vs = some locs ∧
        (t = .bool ∨ ∃ n, t = .bits n ∧ n ≤ 64)
    | .vec vr => vr.elim := by
  cases t with
  | bool =>
    cases gs with
    | nil => simp [Isa.assignSig] at h
    | cons r0 gs' =>
      simp only [Isa.assignSig, Option.map_eq_some_iff] at h
      obtain ⟨locs', h', hloc⟩ := h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hloc
      exact ⟨gs', rfl, h', Or.inl rfl⟩
  | bits n =>
    cases gs with
    | nil => simp [Isa.assignSig] at h
    | cons r0 gs' =>
      simp only [Isa.assignSig] at h
      cases hbw : [8, 16, 32, 64].contains n
      · simp only [hbw, Bool.false_eq_true, ↓reduceIte] at h; cases h
      · simp only [hbw, ↓reduceIte, Option.map_eq_some_iff] at h
        obtain ⟨locs', h', hloc⟩ := h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj hloc
        have hle : n ≤ 64 := by
          simp only [List.contains_eq_mem, List.mem_cons,
            List.not_mem_nil, or_false, decide_eq_true_eq] at hbw
          rcases hbw with rfl | rfl | rfl | rfl <;> decide
        exact ⟨gs', rfl, h', Or.inr ⟨n, rfl, hle⟩⟩
  | float _ => simp [Isa.assignSig] at h
  | pair _ _ => cases vs with | nil => simp [Isa.assignSig] at h | cons v _ => exact v.elim

private theorem setArmAbiRegs_get_sp :
    ∀ {ts : List Ty} {locs : Tup (AbiReg Reg Empty) ts} {args : Tup Val ts}
      {gs : List Reg} {vs : List Empty},
      armTarget.toIsa.assignSig ts gs vs = some locs →
      (setArmAbiRegs locs args).SP = 0x1000
  | [], (), (), _, _, _ => rfl
  | t :: ts, (loc, locs), (_, vs), gs, vs', h => by
    have hc := armAssignSig_cons h
    cases loc with
    | vec vr => exact vr.elim
    | gpr r =>
      obtain ⟨gs', rfl, h', _⟩ := hc
      cases r with
      | reg x =>
        dsimp only [setArmAbiRegs]
        rw [Reg64s.SP_setXReg]
        exact setArmAbiRegs_get_sp (args := vs) h'
      | SP => dsimp only [setArmAbiRegs]; exact setArmAbiRegs_get_sp (args := vs) h'

private theorem setArmAbiRegs_get_x30 :
    ∀ {ts : List Ty} {locs : Tup (AbiReg Reg Empty) ts} {args : Tup Val ts}
      {gs : List Reg} {vs : List Empty},
      .reg .X30 ∉ gs → armTarget.toIsa.assignSig ts gs vs = some locs →
      (setArmAbiRegs locs args).X30 = (0x1234 : Int64).toUInt64
  | [], (), (), _, _, _, _ => rfl
  | t :: ts, (loc, locs), (v, vs), gs, vs', h30, h => by
    have hc := armAssignSig_cons h
    cases loc with
    | vec vr => exact vr.elim
    | gpr r =>
      obtain ⟨gs', rfl, h', _⟩ := hc
      cases r with
      | reg x =>
        have hne : x ≠ .X30 := fun e => h30 (e ▸ List.mem_cons_self)
        have ih := setArmAbiRegs_get_x30 (args := vs)
          (fun hm => h30 (List.mem_cons_of_mem _ hm)) h'
        have hx : (setArmAbiRegs (ts := t :: ts)
            (AbiReg.gpr (.reg x), locs) (v, vs)).getXReg .X30 =
            (setArmAbiRegs locs vs).getXReg .X30 := by
          dsimp only [setArmAbiRegs]
          exact Reg64s.getXReg_setXReg_of_ne _ _ _ _ hne
        simpa [Reg64s.getXReg] using hx.trans ih
      | SP =>
        dsimp only [setArmAbiRegs]
        exact setArmAbiRegs_get_x30 (args := vs) (fun hm => h30 (List.mem_cons_of_mem _ hm)) h'

private theorem armAbi_frame {g g' : Reg64s} :
    ∀ {ts : List Ty} {locs : Tup (AbiReg Reg Empty) ts} {args : Tup Val ts}
      {gs : List Reg} {vs : List Empty},
      (∀ r ∈ gs, g'.getRegOrSp64 r = g.getRegOrSp64 r) →
      armTarget.toIsa.assignSig ts gs vs = some locs →
      TRel (fun t loc val => match loc with
        | .gpr r => AbiGprHolds (g.getRegOrSp64 r) t val
        | .vec vr => vr.elim) locs args →
      TRel (fun t loc val => match loc with
        | .gpr r => AbiGprHolds (g'.getRegOrSp64 r) t val
        | .vec vr => vr.elim) locs args
  | [], (), (), _, _, _, _, _ => .nil
  | _ :: _, (loc, _), (_, _), _, _, hg, h, hrel => by
    cases hrel with
    | cons h1 h2 =>
      have hc := armAssignSig_cons h
      cases loc with
      | vec vr => exact vr.elim
      | gpr r =>
        obtain ⟨_, rfl, h', _⟩ := hc
        exact .cons (by simpa [hg r List.mem_cons_self] using h1)
          (armAbi_frame (fun x hm => hg x (List.mem_cons_of_mem _ hm)) h' h2)

private theorem setArmAbiRegs_holds :
    ∀ {ts : List Ty} {locs : Tup (AbiReg Reg Empty) ts} {args : Tup Val ts}
      {gs : List Reg} {vs : List Empty},
      gs.Nodup → .SP ∉ gs → armTarget.toIsa.assignSig ts gs vs = some locs →
      TRel (fun t loc val => match loc with
        | .gpr r => AbiGprHolds ((setArmAbiRegs locs args).getRegOrSp64 r) t val
        | .vec vr => vr.elim) locs args
  | [], (), (), _, _, _, _, _ => .nil
  | t :: ts, (loc, locs), (v, vs), gs, vs', hgs, hsp, h => by
    have hc := armAssignSig_cons h
    cases loc with
    | vec vr => exact vr.elim
    | gpr r =>
      obtain ⟨gs', rfl, h', hty⟩ := hc
      obtain ⟨hnmem, hgs'⟩ := List.nodup_cons.mp hgs
      cases r with
      | SP => exact absurd List.mem_cons_self hsp
      | reg x =>
        have hhead :
            AbiGprHolds ((setArmAbiRegs (ts := t :: ts)
              (AbiReg.gpr (.reg x), locs) (v, vs)).getRegOrSp64 (.reg x)) t v := by
          rcases hty with rfl | ⟨n, rfl, hn⟩
          · change AbiGprHolds (((setArmAbiRegs locs vs).setXReg x
              (valToGpr .bool v)).getXReg x).toBitVec .bool v
            dsimp only [valToGpr, AbiGprHolds]; simp
          · change AbiGprHolds (((setArmAbiRegs locs vs).setXReg x
              (valToGpr (.bits n) v)).getXReg x).toBitVec (.bits n) v
            dsimp only [valToGpr, AbiGprHolds]; simp [hn]
        refine .cons hhead (armAbi_frame ?_ h' (setArmAbiRegs_holds hgs'
          (fun hm => hsp (List.mem_cons_of_mem _ hm)) h'))
        intro y hy
        cases y with
        | SP => exact absurd (List.mem_cons_of_mem _ hy) hsp
        | reg y =>
          have hne : x ≠ y := fun e => hnmem (e ▸ hy)
          dsimp only [setArmAbiRegs]
          exact congrArg UInt64.toBitVec (Reg64s.getXReg_setXReg_of_ne _ _ _ _ hne)

/-- Concrete initial `MachineData` with `n`-byte stack, `sp0 = 0x1000#64`, return address `0x1234`
in `x30`, payload `bs` at `0x1000#64`, and AAPCS64 argument registers populated from `args`. -/
@[expose] def armInitState (n : Nat) (bs : List UInt8) {as : List Ty} (args : Tup Val as) :
    MachineData :=
  let regs :=
    match armTarget.toIsa.assignArgs as with
    | some locs => setArmAbiRegs locs args
    | none => { SP := 0x1000, X30 := (0x1234 : Int64).toUInt64 }
  { regs := regs, dmem := armInitMem n bs }

private theorem trel_arm_imp {P Q : ∀ t, AbiReg Reg Empty t → Val t → Prop}
    (h : ∀ t a v, P t a v → Q t a v) :
    ∀ {ts : List Ty} {xs : Tup (AbiReg Reg Empty) ts} {ys : Tup Val ts},
      TRel P xs ys → TRel Q xs ys
  | [], _, _, .nil => .nil
  | _ :: _, _, _, .cons hx hxs => .cons (h _ _ _ hx) (trel_arm_imp h hxs)

/-- Closed concrete execution harness for `armTarget` (`sp0 = 0x1000#64`, `ra0 = 0x1234`). -/
@[expose] def armInit : TargetInit armTarget 2048 8192 where
  sp0 := 0x1000#64
  ra0 := 0x1234
  ret0 := .reg .X0
  arg0 := .reg .X0
  initState := armInitState
  get_sp := fun n bs {as} args => by
    dsimp only [armTarget, armMach, get, armInitState]
    cases h : armTarget.toIsa.assignArgs as with
    | none => rfl
    | some locs =>
      change (setArmAbiRegs locs args).SP.toBitVec = 0x1000#64
      exact congrArg UInt64.toBitVec (setArmAbiRegs_get_sp h)
  argsIn := fun n bs {as} args his => by
    obtain ⟨locs, hlocs⟩ := Option.isSome_iff_exists.mp his
    refine ⟨locs, hlocs, ?_⟩
    dsimp only [armInitState]; rw [hlocs]; dsimp only
    exact trel_arm_imp (fun t loc v h => by
        cases loc with
        | gpr _ => exact h
        | vec vr => exact vr.elim)
      (setArmAbiRegs_holds (by simp) (by simp) hlocs)
  raReg := fun n bs {as} args => by
    dsimp only [armTarget, armFrameTarget, armFramePreds, get, get_reg, armInitState]
    cases h : armTarget.toIsa.assignArgs as with
    | none => rfl
    | some locs =>
      have hx : (setArmAbiRegs locs args).X30 = (0x1234 : Int64).toUInt64 :=
        setArmAbiRegs_get_x30 (by simp) h
      change ((setArmAbiRegs locs args).X30).toBitVec = (0x1234 : Int64).toBitVec
      rw [hx]; rfl
  spEntry := by dsimp only [armTarget, armFrameTarget, armFramePreds]; decide
  mem_entry n bs {_} _ hn hbs := armInitMem_entry n bs hn hbs
  retsIn_singleton v s h := by
    obtain ⟨locs, hlocs, hrel⟩ := h
    change some (AbiReg.gpr (.reg .X0), ()) = some locs at hlocs
    injection hlocs with hlocs; subst hlocs
    cases hrel with
    | cons h1 _ => exact h1.2.trans (by simp)
  argsIn_singleton v s h := by
    obtain ⟨locs, hlocs, hrel⟩ := h
    change some (AbiReg.gpr (.reg .X0), ()) = some locs at hlocs
    injection hlocs with hlocs; subst hlocs
    cases hrel with
    | cons h1 _ => exact h1.2.trans (by simp)

/-! ## 4. Concrete Kraken-AArch64 Lifting Lemmas (`arm64_of_*`) -/

private theorem arm64_entry_mem {s : MachineData} {ra : Int64} {b : Nat} {P R : Mem 64 → Prop}
    (hmem : s.dmem =⋆ P ⋆ region (s.regs.SP.toBitVec - BitVec.ofNat 64 b) b ⋆ R) :
    armTarget.mach.mem s =⋆
      P ⋆ armTarget.Entry (armTarget.mach.getGpr s armTarget.frame.sp) ra b ⋆ R := by
  refine sep_mono (fun _ => sep_mono_r fun _ h => ?_) hmem
  dsimp only [Target.Entry, armTarget, armFrameTarget, armFramePreds, get]
  simp only [region_zero, Std.ExtHashMap.sep_emp]
  exact h

/-- Translates `armTarget.FnSpec` into the concrete Kraken-AArch64 `step1 Host.exe` statement. -/
theorem arm64_of_call [hh : Host] {sym : Sym} {b nX : Nat} {as bs : List Ty}
    {spec : Spec as bs} (hfn : armTarget.FnSpec hh sym spec b nX)
    {args : Tup Val as} {m : Mem 64} {Q : Post bs} {X : XPost} (hspec : spec args m Q X)
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hargs : armTarget.ArgsIn args s)
    (hra : s.regs.X30 = ra.toUInt64)
    (hsp : s.regs.SP.toNat % 16 = 0)
    (hmem : s.dmem =⋆ Eq m ⋆ region (s.regs.SP.toBitVec - BitVec.ofNat 64 b) b ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st =>
        (st.pc = ra ∧
          (∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29],
            st.data.regs.getXReg r = s.regs.getXReg r) ∧
          st.data.regs.SP = s.regs.SP ∧
          ∃ rets m', Q rets m' ∧ armTarget.RetsIn rets st.data ∧
            (st.data.dmem =⋆ Eq m' ⋆
              region (s.regs.SP.toBitVec - BitVec.ofNat 64 b) b ⋆ R)) ∨
        (∃ (sym' : Sym) (cs : List Ty) (xs : Tup Val cs) (m' : Mem 64),
          X sym' cs xs m' ∧ armTarget.Defined hh sym' ∧ st.pc = Labels.label sym' ∧
          armTarget.ArgsIn xs st.data ∧ st.data.regs.SP.toNat % 16 = 0 ∧
          ∃ (ra' : Int64) (n' : Nat) (F : Mem 64 → Prop), nX ≤ n' ∧
            (st.data.dmem =⋆ Eq m' ⋆
              armTarget.Entry (get st.data .SP) ra' n' ⋆ F ⋆ R)))
      ⟨s, Labels.label sym⟩ := by
  have hra' : armTarget.frameSpec.raReg s ra := by
    change s.regs.X30.toBitVec = ra.toBitVec
    rw [hra]; rfl
  refine eventually_weaken _ _ _ _ ?_
    (hfn args m Q X hspec s ra R hargs hra' hsp (arm64_entry_mem hmem))
  rintro st (⟨hpc, rets, m', hQ, hrets, ⟨hcs, hsp'⟩, hm'⟩ |
    ⟨sym', cs, xs, m', hX, hdef, hpc, has, hspE, ra', n', F, hnX, _, _, hm'⟩)
  · refine Or.inl ⟨hpc, fun r hr => ?_, ?_, rets, m', hQ, hrets, ?_⟩
    · have := hcs (.reg r) (by simp at hr ⊢; omega)
      exact UInt64.toBitVec_inj.mp this
    · have : get st.data .SP = get s .SP := by simpa [armFrame] using hsp'
      exact UInt64.toBitVec_inj.mp this
    · simp only [Target.Exit, get, Nat.add_zero] at hm'; exact hm'
  · exact Or.inr ⟨sym', cs, xs, m', hX, hdef, hpc, has, hspE, ra', n', F, hnX, hm'⟩

/-- Simplified `arm64_of_call` erasing exit stack/frame details down to `∃ m', X sym' cs xs m'`. -/
theorem arm64_of_call_emp [hh : Host] {sym : Sym} {b nX : Nat} {as bs : List Ty}
    {spec : Spec as bs} (hfn : armTarget.FnSpec hh sym spec b nX)
    {args : Tup Val as} {m : Mem 64} {Q : Post bs} {X : XPost} (hspec : spec args m Q X)
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hargs : armTarget.ArgsIn args s)
    (hra : s.regs.X30 = ra.toUInt64)
    (hsp : s.regs.SP.toNat % 16 = 0)
    (hmem : s.dmem =⋆ Eq m ⋆ region (s.regs.SP.toBitVec - BitVec.ofNat 64 b) b ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st =>
        (st.pc = ra ∧
          (∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29],
            st.data.regs.getXReg r = s.regs.getXReg r) ∧
          st.data.regs.SP = s.regs.SP ∧
          ∃ rets m', Q rets m' ∧ armTarget.RetsIn rets st.data ∧
            (st.data.dmem =⋆ Eq m' ⋆
              region (s.regs.SP.toBitVec - BitVec.ofNat 64 b) b ⋆ R)) ∨
        (∃ (sym' : Sym) (cs : List Ty) (xs : Tup Val cs) (m' : Mem 64),
          X sym' cs xs m' ∧ armTarget.Defined hh sym' ∧ st.pc = Labels.label sym' ∧
          armTarget.ArgsIn xs st.data ∧ st.data.regs.SP.toNat % 16 = 0))
      ⟨s, Labels.label sym⟩ := by
  refine eventually_weaken _ _ _ _ ?_ (arm64_of_call hfn hspec s ra R hargs hra hsp hmem)
  rintro st (hret | ⟨sym', cs, xs, m', hX, hdef, hpc, has, hspE, _⟩)
  · exact Or.inl hret
  · exact Or.inr ⟨sym', cs, xs, m', hX, hdef, hpc, has, hspE⟩

/-- Non-exiting specialization of `arm64_of_call` (`X = fun _ _ _ _ => False`). -/
theorem arm64_of_returns [hh : Host] {sym : Sym} {b nX : Nat} {as bs : List Ty}
    {spec : Spec as bs} (hfn : armTarget.FnSpec hh sym spec b nX)
    {args : Tup Val as} {m : Mem 64} {Q : Post bs}
    (hspec : spec args m Q (fun _ _ _ _ => False))
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hargs : armTarget.ArgsIn args s)
    (hra : s.regs.X30 = ra.toUInt64)
    (hsp : s.regs.SP.toNat % 16 = 0)
    (hmem : s.dmem =⋆ Eq m ⋆ region (s.regs.SP.toBitVec - BitVec.ofNat 64 b) b ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = ra ∧
        (∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29],
          st.data.regs.getXReg r = s.regs.getXReg r) ∧
        st.data.regs.SP = s.regs.SP ∧
        ∃ rets m', Q rets m' ∧ armTarget.RetsIn rets st.data ∧
          (st.data.dmem =⋆ Eq m' ⋆
            region (s.regs.SP.toBitVec - BitVec.ofNat 64 b) b ⋆ R))
      ⟨s, Labels.label sym⟩ := by
  refine eventually_weaken _ _ _ _ ?_ (arm64_of_call hfn hspec s ra R hargs hra hsp hmem)
  rintro st (hret | ⟨_, _, _, _, hX, _⟩)
  · exact hret
  · exact hX.elim

/-- Empty-heap specialization of `arm64_of_returns`. -/
theorem arm64_of_returns_emp [hh : Host] {sym : Sym} {b nX : Nat} {as bs : List Ty}
    {spec : Spec as bs} (hfn : armTarget.FnSpec hh sym spec b nX)
    {args : Tup Val as} {Q' : Tup Val bs → Prop}
    (hspec : spec args ∅ (fun rets m' => Q' rets ∧ Std.ExtHashMap.emp m')
      (fun _ _ _ _ => False))
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hargs : armTarget.ArgsIn args s)
    (hra : s.regs.X30 = ra.toUInt64)
    (hsp : s.regs.SP.toNat % 16 = 0)
    (hmem : s.dmem =⋆ region (s.regs.SP.toBitVec - BitVec.ofNat 64 b) b ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = ra ∧
        (∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29],
          st.data.regs.getXReg r = s.regs.getXReg r) ∧
        st.data.regs.SP = s.regs.SP ∧
        ∃ rets, armTarget.RetsIn rets st.data ∧ Q' rets ∧
          (st.data.dmem =⋆ region (s.regs.SP.toBitVec - BitVec.ofNat 64 b) b ⋆ R))
      ⟨s, Labels.label sym⟩ := by
  have hmem' : s.dmem =⋆ Eq (∅ : Mem 64) ⋆
      region (s.regs.SP.toBitVec - BitVec.ofNat 64 b) b ⋆ R := by
    rw [eq_empty_eq_emp, Std.ExtHashMap.emp_sep]; exact hmem
  refine eventually_weaken _ _ _ _ ?_ (arm64_of_returns hfn hspec s ra R hargs hra hsp hmem')
  rintro st ⟨hpc, hcs, hsp', rets, m', ⟨hQ, hm0⟩, hrets, hm'⟩
  rw [← eq_empty_eq_emp] at hm0
  subst hm0
  rw [eq_empty_eq_emp, Std.ExtHashMap.emp_sep] at hm'
  exact ⟨hpc, hcs, hsp', rets, hrets, hQ, hm'⟩

end LeanQbe.T.Arm64
