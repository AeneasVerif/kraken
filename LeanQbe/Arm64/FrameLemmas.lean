module

public import LeanQbe.Arm64.TargLemmas
public import LeanQbe.AbiLemmas
import Kraken.AArch64.Parser

/-!
# AArch64 frame lemmas (Target v1): prologue, epilogue, slots, call, tail jump

Stack accesses with base `sp` need a 16-byte aligned `sp` (Kraken faults otherwise); every lemma that
touches memory through `sp` takes `(get s .SP).toNat % 16 = 0`.
-/

@[expose] public section

namespace LeanQbe.Arm64

open Std

/-! ## Stack pointer arithmetic -/

/-- `s` with `sp := v`. -/
abbrev setSP (s : MachineData) (v : Val) : MachineData :=
  { s with regs := { s.regs with SP := UInt64.ofBitVec v } }

theorem get_setSP_sp (s : MachineData) (v : Val) : get (setSP s v) .SP = v := by
  simp [get_setSP]

theorem get_setSP_of_ne (s : MachineData) (v : Val) (r : Reg) (h : r ≠ .SP) :
    get (setSP s v) r = get s r := by
  simp [get_setSP, h]

theorem ofInt_toInt_ofNat (o : Nat) : BitVec.ofInt 64 (Int64.ofNat o).toInt = BitVec.ofNat 64 o := by
  grind

/-- The address `[sp, #o]`. -/
theorem sp_addr (s : MachineData) (o : Nat) :
    BitVec.ofInt 64 ((s.regs.getRegOrSp (.low .SP .W64)).signed + (Int64.ofNat o).toInt) =
      get s .SP + BitVec.ofNat 64 o := by
  rw [BitVec.ofInt_add, ofInt_toInt_ofNat]
  simp [BitVec.signed, get_sp]

/-- A 16-byte aligned `sp` passes Kraken's alignment check. -/
theorem sp_aligned (s : MachineData) (h : (get s .SP).toNat % 16 = 0) :
    (s.regs.getRegOrSp RegOrSp.SP % 16#64 != 0#64) = false := by
  have h' : s.regs.SP.toBitVec % 16#64 = 0#64 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_umod, BitVec.toNat_ofNat]
    simpa [get_sp] using h
  simp [Reg64s.getRegOrSp, Reg64s.getRegOrSp64, RegOrSp.base, BitVec.take, h']

theorem runs_subSp (n : Nat) (s : MachineData) :
    Runs (subSp n) s (setSP s (get s .SP - BitVec.ofNat 64 n)) := by
  refine Runs.single fun p next jmp => ?_
  simp only [step_simp, Reg64s.setRegOrSp, Reg64s.setRegOrSp64, Reg64s.getRegOrSp_sp64,
    RegWidth.bits, ofInt_toInt_ofNat, get_sp]

theorem runs_addSp (n : Nat) (s : MachineData) :
    Runs (addSp n) s (setSP s (get s .SP + BitVec.ofNat 64 n)) := by
  refine Runs.single fun p next jmp => ?_
  simp only [step_simp, Reg64s.setRegOrSp, Reg64s.setRegOrSp64, Reg64s.getRegOrSp_sp64,
    RegWidth.bits, ofInt_toInt_ofNat, get_sp]

/-! ## Stack slots -/

theorem runs_stSp (v : XReg) (o : Nat) (s : MachineData) {G : Mem 64 → Prop}
    (hal : (get s .SP).toNat % 16 = 0)
    (hmem : s.dmem =⋆ region (get s .SP + BitVec.ofNat 64 o) 8 ⋆ G) :
    ∃ s', Runs (stSp v o) s s' ∧ s'.regs = s.regs ∧
      (s'.dmem =⋆ word (get s .SP + BitVec.ofNat 64 o) (get s (.reg v)) ⋆ G) := by
  obtain ⟨bs, hl, hbs⟩ := region_sep_elim hmem
  refine ⟨{ s with dmem :=
      (Mem.storeInt s.dmem (get s .SP + BitVec.ofNat 64 o) 8 (get s (.reg v)).toInt) },
    Runs.single' fun p next jmp post => ?_, rfl,
    Mem.storeInt_sep _ 8 bs G s.dmem ⟨hbs, hl⟩ (get s (.reg v)).toInt⟩
  simp only [step_simp, sp_aligned s hal, sp_addr, Bool.false_eq_true, ↓reduceIte]
  rw [store_All_of_sep _ _ .W64 _ _ _ bs G hbs hl]
  simp [get_reg]

theorem runs_ldSp (d : XReg) (o : Nat) (s : MachineData) {v : Val} {G : Mem 64 → Prop}
    (hal : (get s .SP).toNat % 16 = 0)
    (hmem : s.dmem =⋆ word (get s .SP + BitVec.ofNat 64 o) v ⋆ G) :
    Runs (ldSp d o) s (wr s d v) := by
  refine Runs.single' fun p next jmp post => ?_
  simp only [step_simp, sp_aligned s hal, sp_addr, Bool.false_eq_true, ↓reduceIte]
  rw [load_All_of_sep _ _ .W64 _ _ (Int.toBytes 8 v.toInt) G hmem (Int.toBytes_length _ _)]
  have hv : BitVec.ofInt 64 (Int.ofBytes (Int.toBytes 8 v.toInt)) = v :=
    BitVec.ofInt_ofBytes_toBytes 64 8 rfl v
  simp only [MemWidth.bits, hv, BitVec.setWidth_eq]

/-! ## Frame layout -/

theorem frameSize_ge (ns : Nat) : 8 * ns + 8 ≤ frameSize ns := by
  unfold frameSize; omega

theorem frameSize_mod (ns : Nat) : frameSize ns % 16 = 0 := by
  unfold frameSize; omega

/-- A multiple of 16 below an aligned address is aligned. -/
theorem aligned_sub (sp : Val) (n : Nat) (hsp : sp.toNat % 16 = 0) (hn : n % 16 = 0) :
    (sp - BitVec.ofNat 64 n).toNat % 16 = 0 := by
  grind

/-- What the frame keeps besides the slots: the saved `x30` above the slots, then padding. -/
def Saved (sp0 : Val) (ra : Int64) (ns : Nat) : Mem 64 → Prop :=
  word (sp0 - BitVec.ofNat 64 (frameSize ns) + BitVec.ofNat 64 (8 * ns)) ra.toBitVec ⋆
    region (sp0 - BitVec.ofNat 64 (frameSize ns) + BitVec.ofNat 64 (8 * ns) + BitVec.ofNat 64 8)
      (frameSize ns - 8 * ns - 8)

/-- The frame region splits into slots, the `x30` cell and padding. -/
theorem region_frame (a : Val) (ns : Nat) (hF : frameSize ns ≤ 2 ^ 64) :
    region a (frameSize ns) = region a (8 * ns) ⋆ (region (a + BitVec.ofNat 64 (8 * ns)) 8 ⋆
      region (a + BitVec.ofNat 64 (8 * ns) + BitVec.ofNat 64 8) (frameSize ns - 8 * ns - 8)) := by
  have hge := frameSize_ge ns
  have e : frameSize ns = 8 * ns + (8 + (frameSize ns - 8 * ns - 8)) := by omega
  conv => lhs; rw [e]
  rw [region_split (by omega), region_split (by omega)]

theorem x30_toBitVec (s : MachineData) (ra : Int64) (h : s.regs.X30 = ra.toUInt64) :
    get s (.reg .X30) = ra.toBitVec := by
  simp [get_reg, Reg64s.getXReg, h]

section
variable [Host]

theorem eventually_prologue {k ns : Nat} {s : MachineData} {ra : Int64} {G : Mem 64 → Prop}
    {post : @_root_.Post MachineState}
    (hc : (prologue ns).IsInfixAt Host.prog k) (hra : s.regs.X30 = ra.toUInt64)
    (hsp : (get s .SP).toNat % 16 = 0) (hF : frameSize ns ≤ 2 ^ 64)
    (hmem : s.dmem =⋆ region (get s .SP) 0 ⋆
      region (get s .SP - BitVec.ofNat 64 (frameSize ns)) (frameSize ns) ⋆ G)
    (hk : ∀ s' : MachineData, get s' .SP = get s .SP - BitVec.ofNat 64 (frameSize ns) →
      (∀ r, r ∉ .SP :: [.reg .X30] ++ scratch → get s' r = get s r) →
      (s'.dmem =⋆ Saved (get s .SP) ra ns ⋆
        region (get s .SP - BitVec.ofNat 64 (frameSize ns)) (8 * ns) ⋆ G) →
      Eventually (step1 Host.exe) post ⟨s', Host.addrOf (k + (prologue ns).length)⟩) :
    Eventually (step1 Host.exe) post ⟨s, Host.addrOf k⟩ := by
  obtain ⟨hsub, hst⟩ := List.IsInfixAt.append hc
  generalize ha : get s .SP - BitVec.ofNat 64 (frameSize ns) = a at hmem hk
  let s₁ := setSP s a
  have hsp₁ : (get s₁ .SP).toNat % 16 = 0 := by
    rw [get_setSP_sp, ← ha]; exact aligned_sub _ _ hsp (frameSize_mod ns)
  rw [region_zero, ExtHashMap.emp_sep, region_frame a ns hF] at hmem
  have hmem₁ : s₁.dmem =⋆ region (get s₁ .SP + BitVec.ofNat 64 (8 * ns)) 8 ⋆
      (region a (8 * ns) ⋆
        region (a + BitVec.ofNat 64 (8 * ns) + BitVec.ofNat 64 8) (frameSize ns - 8 * ns - 8) ⋆ G) := by
    rw [get_setSP_sp]
    have e : region a (8 * ns) ⋆ (region (a + BitVec.ofNat 64 (8 * ns)) 8 ⋆
        region (a + BitVec.ofNat 64 (8 * ns) + BitVec.ofNat 64 8) (frameSize ns - 8 * ns - 8)) ⋆ G =
        region (a + BitVec.ofNat 64 (8 * ns)) 8 ⋆ (region a (8 * ns) ⋆
        region (a + BitVec.ofNat 64 (8 * ns) + BitVec.ofNat 64 8) (frameSize ns - 8 * ns - 8) ⋆ G) := by
      ac_rfl
    rw [← e]; exact hmem
  obtain ⟨s₂, hr₂, hregs₂, hmem₂⟩ := runs_stSp .X30 (8 * ns) s₁ hsp₁ hmem₁
  refine Runs.eventually (runs_subSp _ s) hsub ?_
  rw [ha]
  refine Runs.eventually hr₂ hst ?_
  have hlen : k + (subSp (frameSize ns)).length + (stSp .X30 (8 * ns)).length =
      k + (prologue ns).length := by simp [prologue, subSp, stSp]
  rw [hlen]
  have hget₂ : ∀ r, get s₂ r = get s₁ r := fun r => by simp [get, hregs₂]
  refine hk s₂ (by rw [hget₂, get_setSP_sp]) (fun r hr => ?_) ?_
  · have : r ≠ .SP := by intro e; subst e; simp at hr
    rw [hget₂, get_setSP_of_ne _ _ _ this]
  · rw [get_setSP_sp] at hmem₂
    have hx : get s₁ (.reg .X30) = ra.toBitVec := by
      rw [get_setSP_of_ne _ _ _ (by simp)]; exact x30_toBitVec s ra hra
    rw [hx] at hmem₂
    have e : word (a + BitVec.ofNat 64 (8 * ns)) ra.toBitVec ⋆ (region a (8 * ns) ⋆
        region (a + BitVec.ofNat 64 (8 * ns) + BitVec.ofNat 64 8) (frameSize ns - 8 * ns - 8) ⋆ G) =
        Saved (get s .SP) ra ns ⋆ region a (8 * ns) ⋆ G := by
      simp only [Saved, ha]; ac_rfl
    rw [← e]; exact hmem₂

theorem eventually_epilogue {k ns : Nat} {s : MachineData} {ra : Int64} {G : Mem 64 → Prop}
    {post : @_root_.Post MachineState}
    (hc : (epilogue ns).IsInfixAt Host.prog k)
    (hsp : (get s .SP).toNat % 16 = 0) (hF : frameSize ns ≤ 2 ^ 64)
    (hmem : s.dmem =⋆ Saved (get s .SP + BitVec.ofNat 64 (frameSize ns)) ra ns ⋆ G)
    (hk : ∀ s' : MachineData, get s' .SP = get s .SP + BitVec.ofNat 64 (frameSize ns) →
      s'.regs.X30 = ra.toUInt64 →
      (∀ r, r ∉ .SP :: [.reg .X30] ++ scratch → get s' r = get s r) →
      (s'.dmem =⋆ region (get s .SP + BitVec.ofNat 64 (frameSize ns)) 0 ⋆
        region (get s .SP + BitVec.ofNat 64 (8 * ns)) (frameSize ns - 8 * ns) ⋆ G) →
      Eventually (step1 Host.exe) post ⟨s', Host.addrOf (k + (epilogue ns).length)⟩) :
    Eventually (step1 Host.exe) post ⟨s, Host.addrOf k⟩ := by
  obtain ⟨hld, hadd⟩ := List.IsInfixAt.append hc
  have hcancel : get s .SP + BitVec.ofNat 64 (frameSize ns) - BitVec.ofNat 64 (frameSize ns) =
      get s .SP := BitVec.add_sub_cancel ..
  simp only [Saved, hcancel] at hmem
  rw [ExtHashMap.sep_assoc] at hmem
  have hr₁ : Runs (ldSp .X30 (8 * ns)) s (wr s .X30 ra.toBitVec) :=
    runs_ldSp .X30 (8 * ns) s hsp hmem
  refine Runs.eventually hr₁ hld ?_
  refine Runs.eventually (runs_addSp _ _) hadd ?_
  have hlen : k + (ldSp .X30 (8 * ns)).length + (addSp (frameSize ns)).length =
      k + (epilogue ns).length := by simp [epilogue, addSp, ldSp]
  rw [hlen]
  have hsp₁ : get (wr s .X30 ra.toBitVec) .SP = get s .SP := get_wr_of_ne _ _ _ _ (by simp)
  refine hk _ (by rw [get_setSP_sp, hsp₁]) ?_ (fun r hr => ?_) ?_
  · show (UInt64.ofBitVec ra.toBitVec) = ra.toUInt64
    rfl
  · have h1 : r ≠ .SP := by intro e; subst e; simp at hr
    have h2 : r ≠ .reg .X30 := by intro e; subst e; simp at hr
    rw [get_setSP_of_ne _ _ _ h1, get_wr_of_ne _ _ _ _ h2]
  · have hge := frameSize_ge ns
    have e : frameSize ns - 8 * ns = 8 + (frameSize ns - 8 * ns - 8) := by omega
    rw [region_zero, ExtHashMap.emp_sep, e, region_split (by omega), ExtHashMap.sep_assoc]
    exact sep_mono (fun _ h => word_region h) hmem

/-- Slot `i` := `r`. -/
theorem eventually_slotSt {k i : Nat} {r : Reg} {s : MachineData} {G : Mem 64 → Prop}
    {post : @_root_.Post MachineState}
    (hc : (slotSt i r).IsInfixAt Host.prog k) (hr : r ∉ scratch)
    (hsp : (get s .SP).toNat % 16 = 0)
    (hmem : s.dmem =⋆ region (get s .SP + BitVec.ofNat 64 (8 * i)) 8 ⋆ G)
    (hk : ∀ s' : MachineData, (∀ r, r ∉ scratch → get s' r = get s r) →
      (s'.dmem =⋆ word (get s .SP + BitVec.ofNat 64 (8 * i)) (get s r) ⋆ G) →
      Eventually (step1 Host.exe) post ⟨s', Host.addrOf (k + (slotSt i r).length)⟩) :
    Eventually (step1 Host.exe) post ⟨s, Host.addrOf k⟩ := by
  cases r with
  | reg x =>
    obtain ⟨s', hr', hregs, hmem'⟩ := runs_stSp x (8 * i) s hsp hmem
    exact Runs.eventually hr' hc (hk s' (fun r _ => by simp [get, hregs]) hmem')
  | SP =>
    obtain ⟨hmov, hst⟩ := List.IsInfixAt.append hc
    let s₁ := wr s .X17 (get s .SP)
    have hsp₁ : get s₁ .SP = get s .SP := get_wr_of_ne _ _ _ _ (by simp)
    have hmem₁ : s₁.dmem =⋆ region (get s₁ .SP + BitVec.ofNat 64 (8 * i)) 8 ⋆ G := by
      rw [hsp₁]; exact hmem
    obtain ⟨s', hr', hregs, hmem'⟩ := runs_stSp .X17 (8 * i) s₁ (by rw [hsp₁]; exact hsp) hmem₁
    refine Runs.eventually (runs_mov_reg .X17 .SP s) hmov ?_
    refine Runs.eventually hr' hst ?_
    have hlen : k + (mov (.reg .X17) .SP).length + (stSp .X17 (8 * i)).length =
        k + (slotSt i .SP).length := by simp [slotSt, mov, stSp]
    rw [hlen]
    refine hk s' (fun r hr => ?_) ?_
    · have : r ≠ .reg .X17 := by intro e; subst e; simp [scratch] at hr
      grind
    · grind

/-- `rd` := slot `i`. -/
theorem eventually_slotLd {k i : Nat} {rd : Reg} {v : Val} {s : MachineData} {G : Mem 64 → Prop}
    {post : @_root_.Post MachineState}
    (hc : (slotLd rd i).IsInfixAt Host.prog k)
    (hsp : (get s .SP).toNat % 16 = 0)
    (hmem : s.dmem =⋆ word (get s .SP + BitVec.ofNat 64 (8 * i)) v ⋆ G)
    (hk : ∀ s' : MachineData, get s' rd = v → (∀ r, r ∉ rd :: scratch → get s' r = get s r) →
      s'.dmem = s.dmem →
      Eventually (step1 Host.exe) post ⟨s', Host.addrOf (k + (slotLd rd i).length)⟩) :
    Eventually (step1 Host.exe) post ⟨s, Host.addrOf k⟩ := by
  cases rd with
  | reg x =>
    exact Runs.eventually (runs_ldSp x (8 * i) s hsp hmem) hc
      (hk _ (get_wr_same ..) (fun r hr => get_wr_of_ne _ _ _ _ (not_mem_rd_scratch hr).1) rfl)
  | SP =>
    obtain ⟨hld, hmov⟩ := List.IsInfixAt.append hc
    refine Runs.eventually (runs_ldSp .X17 (8 * i) s hsp hmem) hld ?_
    refine Runs.eventually (runs_mov_sp _ _) hmov ?_
    have hlen : k + (ldSp .X17 (8 * i)).length + (mov .SP (.reg .X17)).length =
        k + (slotLd .SP i).length := by simp [slotLd, mov, ldSp]
    rw [hlen]
    refine hk _ (by rw [get_setSP]; simp) (fun r hr => ?_) rfl
    have : r ≠ .SP ∧ r ≠ .reg .X16 ∧ r ≠ .reg .X17 := by simpa [scratch] using hr
    show get (setSP (wr s .X17 v) (get (wr s .X17 v) (.reg .X17))) r = get s r
    rw [get_setSP_of_ne _ _ _ this.1, get_wr_of_ne _ _ _ _ this.2.2]

/-- `bl sym`: `x30` holds the return address, control is at `sym`. -/
theorem eventually_call {k : Nat} {sym : Label} {s : MachineData} {post : @_root_.Post MachineState}
    (hc : (call sym).IsInfixAt Host.prog k)
    (hk : Eventually (step1 Host.exe) post
      ⟨wr s .X30 (Host.addrOf (k + 1)).toBitVec, Labels.label sym⟩) :
    Eventually (step1 Host.exe) post ⟨s, Host.addrOf k⟩ := by
  refine Host.eventually_of_interp_cps (List.isInfixAt_singleton.mp hc) ?_
  simp only [step_simp, Reg64s.setRegOrZr, Reg64s.setRegOrZr64]
  grind

/-- `b sym` -/
theorem eventually_tailJmp {k : Nat} {sym : Label} {s : MachineData}
    {post : @_root_.Post MachineState}
    (hc : (tailJmp sym).IsInfixAt Host.prog k)
    (hk : Eventually (step1 Host.exe) post ⟨s, Labels.label sym⟩) :
    Eventually (step1 Host.exe) post ⟨s, Host.addrOf k⟩ := by
  refine Host.eventually_of_interp_cps (List.isInfixAt_singleton.mp hc) ?_
  simp only [step_simp]
  exact hk

end

section ParserChecks
open Kraken.AArch64.Parser

example : prologue 1 = ⸨prog|
  sub sp, sp, #16
  str x30, [sp, #8] ⸩ := rfl
example : epilogue 1 = ⸨prog|
  ldr x30, [sp, #8]
  add sp, sp, #16 ⸩ := rfl
example : slotSt 0 (.reg .X3) = ⸨prog| str x3, [sp] ⸩ := rfl
example : slotLd (.reg .X3) 0 = ⸨prog| ldr x3, [sp] ⸩ := rfl
example : call "f" = ⸨prog| bl f ⸩ := rfl
example : tailJmp "f" = ⸨prog| b f ⸩ := rfl

end ParserChecks

end LeanQbe.Arm64
