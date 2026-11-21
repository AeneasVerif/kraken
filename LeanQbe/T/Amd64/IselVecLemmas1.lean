module

public import LeanQbe.T.Amd64.IselVec
public import LeanQbe.T.Amd64.FrameLemmas
import all Kraken.Mem
import all Kraken.Separation

/-!
# SysV x64 Vector Target Verification — Part 1 (`T10`)

Bank invariants, Kraken `RegZmms`/`AvxOperation` step helpers, `BitVec.ofLanes` bit extraction,
64-byte slot/region bridges, `x64VecSpec` non-op obligations (`vmov`, `vmovi`, `vslotSt`, `vslotLd`,
`vload`, `vstore`), and corresponding `NoLab` theorems.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Amd64

open Std Std.ExtHashMap

/-! ## 1. Bank invariants & slot-width classification -/

theorem x64Vec_disj : ∀ r ∈ x64VecScratch,
    r ∉ x64VecAllocatable ∧ r ∉ x64VecArgRegs ∧ r ∉ x64VecRetRegs := by
  intro r hr
  simp only [x64VecScratch, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;>
    simp [x64VecAllocatable, x64VecArgRegs, x64VecRetRegs]

theorem x64VecArgRegs_nodup : x64VecArgRegs.Nodup := by decide
theorem x64VecRetRegs_nodup : x64VecRetRegs.Nodup := by decide

theorem x64AbiVec_slot : ∀ t, x64IsAbiVec t = true → (x64VecSlotWidth t).isSome = true := by
  intro t ht
  simp only [x64IsAbiVec, Bool.and_eq_true, beq_iff_eq] at ht
  simp [x64VecSlotWidth, ht.1, ht.2]

theorem ne_of_not_mem_x64VecScratch {r : RegMm} (hr : r ∉ x64VecScratch) :
    r ≠ .mm14 ∧ r ≠ .mm15 := by
  simp only [x64VecScratch, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  exact hr

theorem x64VecSlotWidth_pair {t : Ty} {w : SlotWidth} (hw : x64VecSlotWidth t = some w) :
    ∃ a b, t = .pair a b := by
  cases t with
  | pair a b => exact ⟨a, b, rfl⟩
  | bool => simp [x64VecSlotWidth, x64IsVecBits, x64IsI32Vec, x64IsF32Vec] at hw
  | bits n =>
    by_cases hn : n = 32 <;>
      simp [x64VecSlotWidth, x64IsVecBits, x64IsI32Vec, x64IsF32Vec, hn, Ty.size] at hw
  | float f =>
    cases f <;> simp [x64VecSlotWidth, x64IsVecBits, x64IsI32Vec, x64IsF32Vec, Ty.size] at hw

theorem x64VecSlotWidth_bits_eq {t : Ty} {w : SlotWidth} (hw : x64VecSlotWidth t = some w) :
    w.bits = t.size := by
  dsimp only [x64VecSlotWidth] at hw
  cases hb : x64IsVecBits t
  · simp [hb] at hw
  · simp only [hb, ↓reduceIte] at hw
    split at hw <;> first | (cases hw; simp_all [SlotWidth.bits]) | cases hw

theorem x64VecSlotWidth_le_awBits {t : Ty} {w : SlotWidth} (hw : x64VecSlotWidth t = some w) :
    t.size ≤ (x64AwOf w).bits := by
  rw [← x64VecSlotWidth_bits_eq hw]
  cases w <;> decide

theorem x64VecSlotWidth_le_512 {t : Ty} {w : SlotWidth} (hw : x64VecSlotWidth t = some w) :
    t.size ≤ 512 := by
  rw [← x64VecSlotWidth_bits_eq hw]
  exact w.bits_le_512

theorem x64IsI32Vec_size_bytes {t : Ty} (h : x64IsI32Vec t = true) : 8 * t.bytes = t.size := by
  induction t with
  | bool | float _ => simp [x64IsI32Vec] at h
  | bits n =>
    by_cases hn : n = 32
    · subst hn; rfl
    · simp [x64IsI32Vec, hn] at h
  | pair a b iha _ =>
    simp only [x64IsI32Vec, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, ha⟩ := h
    have := iha ha
    simp only [Ty.size, Ty.bytes] at this ⊢
    omega

theorem x64IsF32Vec_size_bytes {t : Ty} (h : x64IsF32Vec t = true) : 8 * t.bytes = t.size := by
  induction t with
  | bool | bits _ => simp [x64IsF32Vec] at h
  | float f =>
    cases f <;> simp [x64IsF32Vec] at h
    rfl
  | pair a b iha _ =>
    simp only [x64IsF32Vec, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, ha⟩ := h
    have := iha ha
    simp only [Ty.size, Ty.bytes] at this ⊢
    omega

theorem x64IsVecBits_of_slot {t : Ty} {w : SlotWidth} (hw : x64VecSlotWidth t = some w) :
    x64IsVecBits t = true := by
  by_cases h : x64IsVecBits t = true
  · exact h
  · simp [x64VecSlotWidth, h] at hw

theorem x64VecSlotWidth_bytes {t : Ty} {w : SlotWidth} (hw : x64VecSlotWidth t = some w) :
    t.bytes = 8 * w.slots := by
  have hbs : 8 * t.bytes = t.size := by
    rcases Bool.or_eq_true_iff.mp (x64IsVecBits_of_slot hw) with h | h
    · exact x64IsI32Vec_size_bytes h
    · exact x64IsF32Vec_size_bytes h
  have hbits := x64VecSlotWidth_bits_eq hw
  rw [SlotWidth.bits_eq_64_mul_slots] at hbits
  omega

theorem x64AwOf_bytes_of_ne_w64 {w : SlotWidth} (hne : w ≠ .w64) :
    (x64AwOf w).bytes = 8 * w.slots := by
  cases w <;> first | exact absurd rfl hne | rfl

theorem x64AwOf_bits_of_ne_w64 {w : SlotWidth} (hne : w ≠ .w64) :
    (x64AwOf w).bits = w.bits := by
  cases w <;> first | exact absurd rfl hne | rfl

theorem x64AwOf_bits_le (w : SlotWidth) : (x64AwOf w).bits ≤ 512 := by
  cases w <;> decide

theorem x64W_bits_le_awBits (w : SlotWidth) : w.bits ≤ (x64AwOf w).bits := by
  cases w <;> decide

/-! ## 2. BitVec, `ofLanes`, `RegZmms`, and `Effects.All` helpers -/

theorem take_eq_setWidth {m n : Nat} (v : BitVec m) : BitVec.take v n = v.setWidth n := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [BitVec.take, hi]

theorem zeroExtend_eq_setWidth {m n : Nat} (v : BitVec m) :
    v.zeroExtend n = v.setWidth n := rfl

theorem setWidth_replaceLow {w n : Nat} (hn : n ≤ w) (old : BitVec w) (new : BitVec n) :
    (old.replaceLow new).setWidth n = new := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.replaceLow, BitVec.getLsbD_setWidth, hi, decide_true, Bool.true_and]
  have hlt : (i : Nat) < w := Nat.lt_of_lt_of_le hi hn
  simp only [hlt, decide_true, Bool.true_and]
  rw [show (old.drop n).append new = (old.drop n) ++ new from rfl, BitVec.getLsbD_append]
  simp [hi]

theorem getLsbD_ofLanes_fold {w c : Nat} (f : Nat → BitVec c) (hpos : 0 < c) :
    ∀ (n i : Nat), i < w →
      ((List.range n).foldl (fun acc j => acc ||| ((f j).setWidth w <<< (c * j))) 0#w).getLsbD i =
        if i / c < n then (f (i / c)).getLsbD (i % c) else false
  | 0, i, _ => by simp
  | n + 1, i, hi => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have ih := getLsbD_ofLanes_fold f hpos n i hi
    simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
      ih, hi, decide_true, Bool.true_and]
    have hcn : c * n = n * c := Nat.mul_comm c n
    have hcn1 : c * (n + 1) = (n + 1) * c := Nat.mul_comm c (n + 1)
    by_cases hlt : i < c * n
    · have hd1 : i / c < n := (Nat.div_lt_iff_lt_mul hpos).mpr (hcn ▸ hlt)
      have hd2 : i / c < n + 1 := Nat.lt_succ_of_lt hd1
      simp [hlt, hd1, hd2]
    · by_cases hlt2 : i < c * (n + 1)
      · have hge1 : ¬(i / c < n) := fun h => hlt (hcn ▸ (Nat.div_lt_iff_lt_mul hpos).mp h)
        have hd2 : i / c < n + 1 := (Nat.div_lt_iff_lt_mul hpos).mpr (hcn1 ▸ hlt2)
        have hdiv : i / c = n := by omega
        have hdm := Nat.div_add_mod i c
        rw [hdiv] at hdm
        have hmod : i - c * n = i % c := by omega
        have hltw : i % c < w := Nat.lt_of_le_of_lt (Nat.mod_le i c) hi
        simp [hlt, hdiv, hmod, Bool.false_or, hltw]
      · have hge1 : ¬(i / c < n) := fun h => hlt (hcn ▸ (Nat.div_lt_iff_lt_mul hpos).mp h)
        have hge2 : ¬(i / c < n + 1) := fun h => hlt2 (hcn1 ▸ (Nat.div_lt_iff_lt_mul hpos).mp h)
        have hgec : c ≤ i - c * n := by
          have : c * (n + 1) = c * n + c := Nat.mul_succ c n
          omega
        have hfalse : (f n).getLsbD (i - c * n) = false := BitVec.getLsbD_of_ge (f n) _ hgec
        simp [hlt, hge1, hge2, hfalse]

theorem getLsbD_ofLanes {w c : Nat} (f : Nat → BitVec c) (hpos : 0 < c) (hdvd : c ∣ w)
    (i : Nat) (hi : i < w) :
    (BitVec.ofLanes w c f).getLsbD i = (f (i / c)).getLsbD (i % c) := by
  rw [BitVec.ofLanes, getLsbD_ofLanes_fold f hpos (w / c) i hi]
  have hlt : i / c < w / c := by
    obtain ⟨k, hk⟩ := hdvd
    rw [hk, Nat.mul_comm c k, Nat.mul_div_cancel k hpos, Nat.div_lt_iff_lt_mul hpos]
    rw [hk, Nat.mul_comm c k] at hi
    exact hi
  simp [hlt]

theorem RegZmms.get512_set512_same (s : RegZmms) (r : RegMm) (v : BitVec 512) :
    (s.set512 r v).get512 r = v := by
  cases r <;> rfl

theorem RegZmms.get512_set512_of_ne (s : RegZmms) {r r' : RegMm} (h : r ≠ r')
    (v : BitVec 512) : (s.set512 r v).get512 r' = s.get512 r' := by
  cases r <;> cases r' <;> first | rfl | exact absurd rfl h

theorem RegZmms.get512_set512 (s : RegZmms) (r r' : RegMm) (v : BitVec 512) :
    (s.set512 r v).get512 r' = if r = r' then v else s.get512 r' := by
  split
  · subst r'; exact RegZmms.get512_set512_same s r v
  · exact RegZmms.get512_set512_of_ne s ‹_› v

theorem RegZmms.get_eq_setWidth (s : RegZmms) {aw : AvxWidth} (r : AvxReg aw) :
    s.get r = (s.get512 r.base).setWidth aw.bits := by
  simp only [RegZmms.get, take_eq_setWidth]

theorem RegZmms.set_eq (s : RegZmms) {aw : AvxWidth} (r : AvxReg aw) (v : aw.type) :
    s.set r v = s.set512 r.base (v.setWidth 512) := by
  cases r <;> simp [RegZmms.set, AvxReg.base, BitVec.setWidth_eq]

@[simp] theorem RegZmms.get512_set_same (s : RegZmms) {aw : AvxWidth} (r : AvxReg aw) (v : aw.type) :
    (s.set r v).get512 r.base = v.setWidth 512 := by
  rw [RegZmms.set_eq, RegZmms.get512_set512_same]

@[simp] theorem RegZmms.get512_set_xmm_same (s : RegZmms) (r : RegMm) (v : BitVec 128) :
    (s.set (.xmm r) v).get512 r = v.setWidth 512 :=
  RegZmms.get512_set_same s (.xmm r) v

@[simp] theorem RegZmms.get512_set_avx_same (s : RegZmms) (w : SlotWidth) (r : RegMm)
    (v : (x64AwOf w).type) :
    (s.set (x64AvxRegOf w r) v).get512 r = v.setWidth 512 := by
  have h := RegZmms.get512_set_same s (x64AvxRegOf w r) v
  cases w <;> exact h

theorem RegZmms.get512_set_of_ne (s : RegZmms) {aw : AvxWidth} {r : AvxReg aw} {r' : RegMm}
    (h : r.base ≠ r') (v : aw.type) : (s.set r v).get512 r' = s.get512 r' := by
  rw [RegZmms.set_eq, RegZmms.get512_set512_of_ne _ h]

theorem RegZmms.get512_set_xmm_of_ne (s : RegZmms) {r r' : RegMm} (h : r ≠ r')
    (v : BitVec 128) : (s.set (.xmm r) v).get512 r' = s.get512 r' :=
  RegZmms.get512_set_of_ne s (r := .xmm r) h v

theorem RegZmms.get512_set_avx_of_ne (s : RegZmms) (w : SlotWidth) {r r' : RegMm} (h : r ≠ r')
    (v : (x64AwOf w).type) : (s.set (x64AvxRegOf w r) v).get512 r' = s.get512 r' := by
  apply RegZmms.get512_set_of_ne
  cases w <;> exact h

@[simp] theorem RegZmms.get512_setLegacy_xmm (s : RegZmms) (r : RegMm) (v : BitVec 128) :
    (s.setLegacy (.xmm r) v).get512 r = (s.get512 r).replaceLow v := by
  simp [RegZmms.setLegacy, RegZmms.get512_set512_same]

theorem RegZmms.get512_setLegacy_of_ne (s : RegZmms) {aw : AvxWidth} {r : AvxReg aw} {r' : RegMm}
    (h : r.base ≠ r') (v : aw.type) : (s.setLegacy r v).get512 r' = s.get512 r' := by
  cases r <;> simp only [RegZmms.setLegacy, AvxReg.base] at h ⊢ <;>
    exact RegZmms.get512_set512_of_ne _ h _

theorem RegZmms.get512_setLegacy_xmm_of_ne (s : RegZmms) {r r' : RegMm} (h : r ≠ r')
    (v : BitVec 128) : (s.setLegacy (.xmm r) v).get512 r' = s.get512 r' :=
  RegZmms.get512_setLegacy_of_ne s (r := .xmm r) h v

@[simp] theorem x64AvxRegOf_base (w : SlotWidth) (r : RegMm) :
    (x64AvxRegOf w r).base = r := by
  cases w <;> rfl

theorem vecFallsTo_of_wp {h : Host} {k : Nat} {c : List Directive}
    {gClob : List Reg64} {vClob : List RegMm} {fClob : FlagMask} {s : MachineData}
    {Q : MachineData → Prop} {post : MachineState → Prop}
    (hwp : @Program.wp h c
      (fun s' => Q s' ∧ x64Mach.Frame x64CondReads s s' gClob vClob fClob)
      (fun _ _ => False) s) :
    x64Mach.FallsTo x64CondReads h k c gClob vClob fClob s Q post := by
  letI := h
  intro hc hk
  exact Program.wp.eventually hwp hc
    (fun s' ⟨hq, hfr⟩ => hk s' hq hfr) (fun _ _ hf => False.elim hf)

theorem vecFrame_upd {s s' : MachineData} {gClob : List Reg64} {vClob : List RegMm}
    {fClob : FlagMask}
    (hg : ∀ r, r ∉ gClob → s'.regs.get64 r = s.regs.get64 r)
    (hv : ∀ vr, vr ∉ vClob → s'.zmms.get512 vr = s.zmms.get512 vr)
    (hf : fClob = maskAll ∨ s'.status = s.status) :
    x64Mach.Frame x64CondReads s s' gClob vClob fClob := by
  refine ⟨hg, hv, ?_⟩
  rcases hf with rfl | hst
  · intro cc hdisj
    cases cc <;> simp [FlagMask.disjoint, x64CondReads, maskAll, maskOF, maskCF, maskZF, maskSF,
      maskPF] at hdisj
  · intro cc _; simp [hst]

@[t_step_simp]
theorem x64AtBaseR10_interp [Labels] (regs : Reg64s) (rb : Reg64) (p : Std.Rco Int64) :
    (@AddrExpr.interp _ ⟨.W64⟩ (x64AtBaseR10 rb) regs p).zeroExtend 64 =
      regs.get64 rb + regs.get64 .r10 := by
  simp only [AddrExpr.interp, BitVec.toAddressSize, BitVec.take, Width.bytes,
    ConstExpr.interp, Int64.toInt_zero, Int.add_zero, BitVec.signed, BitVec.extractLsb'_eq_self,
    BitVec.zeroExtend, BitVec.setWidth_eq]
  rw [show (↑(1 : Nat) : Int) = 1 from rfl, Int.mul_one]
  exact ofInt_toInt_add (regs.get64 rb) (regs.get64 .r10)

theorem load_All_of_loadInt (s : MachineData) (addr : BitVec 64) (w : Width)
    (ret : w.type → MachineData → Effects) (post : MachineState → Prop) (i : Int)
    (hload : Mem.loadInt s.dmem addr w.bytes = some i) :
    (MachineData.load s addr w ret).All post ↔ (ret (.ofInt w.bits i) s).All post := by
  simp [MachineData.load, hload, Effects.All_require_read_access]

theorem store_All_of_loadInt (s : MachineData) (addr : BitVec 64) (w : Width) (v : w.type)
    (ret : MachineData → Effects) (post : MachineState → Prop) (i : Int)
    (hload : Mem.loadInt s.dmem addr w.bytes = some i) :
    (MachineData.store s addr v ret).All post ↔
      (ret { s with dmem := Mem.storeInt s.dmem addr w.bytes v.toInt }).All post := by
  simp [MachineData.store, hload, Effects.All_require_write_access]

theorem loadAvx_All_of_loadInt (s : MachineData) (addr : BitVec 64) (w : AvxWidth)
    (ret : w.type → MachineData → Effects) (post : MachineState → Prop) (i : Int)
    (hload : Mem.loadInt s.dmem addr w.bytes = some i) :
    (MachineData.loadAvx s addr w ret false).All post ↔ (ret (.ofInt w.bits i) s).All post := by
  simp [MachineData.loadAvx, hload, Effects.All_require_read_access]

theorem storeAvx_All_of_loadInt (s : MachineData) (addr : BitVec 64) (w : AvxWidth) (v : w.type)
    (ret : MachineData → Effects) (post : MachineState → Prop) (i : Int)
    (hload : Mem.loadInt s.dmem addr w.bytes = some i) :
    (MachineData.storeAvx s addr v ret false).All post ↔
      (ret { s with dmem := Mem.storeInt s.dmem addr w.bytes v.toInt }).All post := by
  simp [MachineData.storeAvx, hload, Effects.All_require_write_access]

/-! ## 3. Single-instruction and addressing `Directive.FallsTo` lemmas -/

theorem x64MoviD_fallsTo (rd : Reg64) (c : BitVec 64) (s : MachineData) :
    Directive.FallsTo (x64MoviD rd c) s
      (fun s' => s' = { s with regs := s.regs.set64 rd c }) := by
  intro _ p next jmp P hk
  simp only [t_step_simp, x64MoviD, Int64.toBitVec_ofBitVec, BitVec.truncate]
  rw [BitVec.setWidth_eq]
  exact hk _ rfl

theorem x64LeaBaseR10_fallsTo (rb : Reg64) (s : MachineData) :
    Directive.FallsTo (ins (.lea (q .r10) (x64AtBaseR10 rb))) s
      (fun s' => s' = { s with regs := s.regs.set64 .r10 (s.regs.get64 rb + s.regs.get64 .r10) }) := by
  intro _ p next jmp P hk
  simp only [t_step_simp, x64AtBaseR10_interp]
  exact hk _ rfl

theorem x64AddrPrep_fallsTo [Host] {a : AddrArg Reg64} {s : MachineData}
    (ha : ∀ r ∈ a.regs, r ∉ x64Scratch) :
    @Program.wp _ (x64AddrPrep a).1
      (fun s' => s'.dmem = s.dmem ∧ s'.status = s.status ∧ s'.zmms = s.zmms ∧
        (∀ r, r ≠ .r10 → s'.regs.get64 r = s.regs.get64 r) ∧
        ∀ [Labels] (p : Std.Rco Int64),
          (@AddrExpr.interp _ ⟨.W64⟩ (x64AddrPrep a).2 s'.regs p).zeroExtend 64 =
            a.eval (x64Mach.getGpr s))
      (fun _ _ => False) s := by
  cases a with
  | baseDisp rb disp =>
    have hrb : rb ≠ .r10 := (ne_of_not_mem_x64Scratch (ha rb List.mem_cons_self)).1
    dsimp only [x64AddrPrep, x64AddrPrepIns]
    split
    · exact Program.wp_nil ⟨rfl, rfl, rfl, fun _ _ => rfl, fun {_} p => by
        rw [AddrExpr.interp_base_disp, zeroExtend_eq_setWidth, BitVec.setWidth_eq]; rfl⟩
    · refine Program.wp.cons (Directive.FallsTo.wp (x64MoviD_fallsTo .r10 disp.toBitVec s)) ?_
      rintro s₁ rfl
      refine Program.wp.mono
        (Directive.FallsTo.wp (x64LeaBaseR10_fallsTo rb { s with regs := s.regs.set64 .r10 disp.toBitVec })) ?_
      rintro s' rfl
      refine ⟨rfl, rfl, rfl, fun r hr => ?_, fun {_} p => ?_⟩
      · simp [Reg64s.get64_set64, hr.symm]
      · simp only [atReg_interp, Reg64s.get64_set64_same,
          Reg64s.get64_set64_of_ne _ _ _ _ hrb.symm]; rfl
  | imm c =>
    dsimp only [x64AddrPrep, x64AddrPrepIns]
    refine Program.wp.mono (Directive.FallsTo.wp (x64MoviD_fallsTo .r10 c s)) ?_
    rintro s' rfl
    refine ⟨rfl, rfl, rfl, fun r hr => Reg64s.get64_set64_of_ne _ _ _ _ hr.symm, fun {_} p => ?_⟩
    simp [Reg64s.get64_set64_same, AddrArg.eval]

theorem x64SlotAddr_fallsTo [Host] (i : Nat) (s : MachineData) :
    @Program.wp _ (x64SlotAddr i).1
      (fun s' => s'.dmem = s.dmem ∧ s'.status = s.status ∧ s'.zmms = s.zmms ∧
        (∀ r, r ≠ .r10 → s'.regs.get64 r = s.regs.get64 r) ∧
        ∀ [Labels] (p : Std.Rco Int64),
          (@AddrExpr.interp _ ⟨.W64⟩ (x64SlotAddr i).2 s'.regs p).zeroExtend 64 =
            s.regs.get64 .rsp + BitVec.ofNat 64 (8 * i))
      (fun _ _ => False) s := by
  dsimp only [x64SlotAddr, x64SlotAddrIns]
  split
  · exact Program.wp_nil ⟨rfl, rfl, rfl, fun _ _ => rfl, fun {_} p => by
      rw [x64AtSp_interp, Int64_toBitVec_ofNat]⟩
  · refine Program.wp.mono (Directive.FallsTo.wp (x64MoviD_fallsTo .r10 (BitVec.ofNat 64 (8 * i)) s)) ?_
    rintro s' rfl
    refine ⟨rfl, rfl, rfl, fun r hr => Reg64s.get64_set64_of_ne _ _ _ _ hr.symm, fun {_} p => ?_⟩
    rw [x64AtSpR10_interp, Reg64s.get64_set64_same,
      Reg64s.get64_set64_of_ne _ _ _ _ (by decide)]

theorem x64VmovDqu32_fallsTo (w : SlotWidth) (vd vs : RegMm) (s : MachineData) :
    Directive.FallsTo
      (x64Avx w (.vmovdqu32 (.avx (x64AvxRegOf w vd)) (.avx (x64AvxRegOf w vs)))) s
      (fun s' => s' = { s with zmms := (s.zmms.set (x64AvxRegOf w vd)
        ((s.zmms.get512 vs).setWidth (x64AwOf w).bits)) }) := by
  intro _ p next jmp P hk
  simp only [t_step_simp, AvxOperation.interp, AvxRegOrMem.interp, MachineData.setAvx,
    MachineData.setAvxReg, RegZmms.get_eq_setWidth, x64AvxRegOf_base]
  exact hk _ rfl

theorem x64VmovIn64_reg_fallsTo (vd : RegMm) (rs : Reg64) (s : MachineData) :
    Directive.FallsTo (x64Avx128 (.vmovIn .W64 (.xmm vd) (.reg (q rs)))) s
      (fun s' => s' = { s with zmms := (s.zmms.set (.xmm vd)
        ((s.regs.get64 rs).setWidth 128)) }) := by
  intro _ p next jmp P hk
  simp only [t_step_simp, AvxOperation.interp, MachineData.setAvxReg, zeroExtend_eq_setWidth]
  exact hk _ rfl

theorem x64Vmovq_fallsTo (vd vs : RegMm) (s : MachineData) :
    Directive.FallsTo (x64Avx128 (.vmovq (.xmm vd) (.xmm vs))) s
      (fun s' => s' = { s with zmms := (s.zmms.set (.xmm vd)
        (((s.zmms.get512 vs).setWidth 64).setWidth 128)) }) := by
  intro _ p next jmp P hk
  simp only [t_step_simp, AvxOperation.interp, MachineData.setAvxReg, RegZmms.get_eq_setWidth,
    AvxReg.base, take_eq_setWidth, zeroExtend_eq_setWidth]
  rw [BitVec.setWidth_setWidth_of_le (s.zmms.get512 vs) (by decide)]
  exact hk _ rfl

theorem x64Pshufd_fallsTo (vd vs : RegMm) (imm : BitVec 8) (s : MachineData) :
    Directive.FallsTo
      (x64Avx128 (.pshufd (.avx (.xmm vd)) (.avx (.xmm vs)) (.int64 (Int64.ofNat imm.toNat)))) s
      (fun s' => s' = { s with zmms := (s.zmms.setLegacy (.xmm vd)
        (((s.zmms.get512 vs).setWidth 128).shuffleDwords imm)) }) := by
  intro _ p next jmp P hk
  have himm : (BitVec.ofNat 64 imm.toNat).take 8 = imm := by
    rw [take_eq_setWidth]
    apply BitVec.eq_of_toNat_eq
    simp
  simp only [t_step_simp, AvxOperation.interp, AvxRegOrMem.interp, MachineData.setAvxLegacy,
    MachineData.setAvxLegacyReg, RegZmms.get_eq_setWidth, AvxReg.base, ConstExpr.interp,
    Int64_toBitVec_ofNat, himm]
  exact hk _ rfl

theorem x64Vpternlogd_fallsTo (w : SlotWidth) (vd s2 s3 : RegMm) (imm : BitVec 8)
    (s : MachineData) :
    Directive.FallsTo (x64TernlogD w vd s2 s3 imm) s
      (fun s' => s' = { s with zmms := (s.zmms.set (x64AvxRegOf w vd)
        (BitVec.ternaryLogic
          ((s.zmms.get512 vd).setWidth (x64AwOf w).bits)
          ((s.zmms.get512 s2).setWidth (x64AwOf w).bits)
          ((s.zmms.get512 s3).setWidth (x64AwOf w).bits) imm)) }) := by
  intro _ p next jmp P hk
  have himm : (BitVec.ofNat 64 imm.toNat).take 8 = imm := by
    rw [take_eq_setWidth]
    apply BitVec.eq_of_toNat_eq
    simp
  simp only [t_step_simp, x64TernlogD, AvxOperation.interp, AvxRegOrMem.interp,
    MachineData.setAvx, MachineData.setAvxReg, RegZmms.get_eq_setWidth, x64AvxRegOf_base,
    ConstExpr.interp, Int64_toBitVec_ofNat, himm]
  exact hk _ rfl

/-! ## 4. `x64VmoviWith` proofs (`ternaryLogic`, `0x00`, `0xFF`, `movi64`, `movi128`) -/

private theorem ternaryLogic_key :
    ∀ (k : Fin 8) (x y z : Bool),
      ((if k.1 / 4 % 2 == 1 then x else !x) &&
       (if k.1 / 2 % 2 == 1 then y else !y) &&
       (if k.1 % 2 == 1 then z else !z)) =
      (k.1 == 4 * x.toNat + 2 * y.toNat + z.toNat) := by decide

private theorem ternaryLogic_fold_getLsbD {w : Nat} (a b c : BitVec w) (imm : BitVec 8)
    (i : Nat) (hi : i < w) :
    ∀ (l : List Nat) (acc : BitVec w), (∀ k ∈ l, k < 8) →
      (l.foldl (fun acc k =>
        if imm.getLsbD k then
          acc ||| ((if k / 4 % 2 == 1 then a else ~~~a) &&&
            (if k / 2 % 2 == 1 then b else ~~~b) &&&
            (if k % 2 == 1 then c else ~~~c))
        else acc) acc).getLsbD i =
      (acc.getLsbD i ||
        (decide ((4 * (a.getLsbD i).toNat + 2 * (b.getLsbD i).toNat + (c.getLsbD i).toNat) ∈ l) &&
         imm.getLsbD (4 * (a.getLsbD i).toNat + 2 * (b.getLsbD i).toNat + (c.getLsbD i).toNat)))
  | [], acc, _ => by simp
  | k :: l, acc, hl => by
    have hk : k < 8 := hl k List.mem_cons_self
    have ih := ternaryLogic_fold_getLsbD a b c imm i hi l
    simp only [List.foldl_cons, List.mem_cons]
    let idx := 4 * (a.getLsbD i).toNat + 2 * (b.getLsbD i).toNat + (c.getLsbD i).toNat
    have hkey : ((if k / 4 % 2 == 1 then a.getLsbD i else !a.getLsbD i) &&
        (if k / 2 % 2 == 1 then b.getLsbD i else !b.getLsbD i) &&
        (if k % 2 == 1 then c.getLsbD i else !c.getLsbD i)) = (k == idx) :=
      ternaryLogic_key ⟨k, hk⟩ (a.getLsbD i) (b.getLsbD i) (c.getLsbD i)
    have hterm : ((if k / 4 % 2 == 1 then a else ~~~a) &&&
        (if k / 2 % 2 == 1 then b else ~~~b) &&&
        (if k % 2 == 1 then c else ~~~c)).getLsbD i = (k == idx) := by
      rw [BitVec.getLsbD_and, BitVec.getLsbD_and]
      have h1 : (if k / 4 % 2 == 1 then a else ~~~a).getLsbD i =
          (if k / 4 % 2 == 1 then a.getLsbD i else !a.getLsbD i) := by
        split <;> simp [hi]
      have h2 : (if k / 2 % 2 == 1 then b else ~~~b).getLsbD i =
          (if k / 2 % 2 == 1 then b.getLsbD i else !b.getLsbD i) := by
        split <;> simp [hi]
      have h3 : (if k % 2 == 1 then c else ~~~c).getLsbD i =
          (if k % 2 == 1 then c.getLsbD i else !c.getLsbD i) := by
        split <;> simp [hi]
      rw [h1, h2, h3, hkey]
    by_cases himmk : imm.getLsbD k = true
    · simp only [himmk, ↓reduceIte]
      rw [ih _ (fun m hm => hl m (List.mem_cons_of_mem _ hm)), BitVec.getLsbD_or, hterm]
      dsimp only [idx] at hkey ⊢
      by_cases heq : k = 4 * (a.getLsbD i).toNat + 2 * (b.getLsbD i).toNat + (c.getLsbD i).toNat
      · subst heq; simp [himmk]
      · have hbeq : (k == 4 * (a.getLsbD i).toNat + 2 * (b.getLsbD i).toNat + (c.getLsbD i).toNat) =
            false := beq_false_of_ne heq
        have hne : 4 * (a.getLsbD i).toNat + 2 * (b.getLsbD i).toNat + (c.getLsbD i).toNat ≠ k :=
          fun h => heq h.symm
        simp [hbeq, hne]
    · have himmk' : imm.getLsbD k = false := Bool.eq_false_iff.mpr himmk
      simp only [himmk', Bool.false_eq_true, ↓reduceIte]
      rw [ih _ (fun m hm => hl m (List.mem_cons_of_mem _ hm))]
      by_cases heq : k = 4 * (a.getLsbD i).toNat + 2 * (b.getLsbD i).toNat + (c.getLsbD i).toNat
      · subst heq; simp [himmk']
      · have hne : 4 * (a.getLsbD i).toNat + 2 * (b.getLsbD i).toNat + (c.getLsbD i).toNat ≠ k :=
          fun h => heq h.symm
        simp [hne]

theorem getLsbD_ternaryLogic {w : Nat} (a b c : BitVec w) (imm : BitVec 8) (i : Nat)
    (hi : i < w) :
    (BitVec.ternaryLogic a b c imm).getLsbD i =
      imm.getLsbD (4 * (a.getLsbD i).toNat + 2 * (b.getLsbD i).toNat + (c.getLsbD i).toNat) := by
  dsimp only [BitVec.ternaryLogic]
  rw [ternaryLogic_fold_getLsbD a b c imm i hi (List.range 8) (0#w)
    (fun k hk => List.mem_range.mp hk)]
  have hlt : 4 * (a.getLsbD i).toNat + 2 * (b.getLsbD i).toNat + (c.getLsbD i).toNat < 8 := by
    cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.getLsbD i <;> decide
  have hmem : 4 * (a.getLsbD i).toNat + 2 * (b.getLsbD i).toNat + (c.getLsbD i).toNat ∈
      List.range 8 := List.mem_range.mpr hlt
  simp [hmem]

private theorem ternaryLogic_all0 {w : Nat} (a : BitVec w) :
    BitVec.ternaryLogic a a a 0x00#8 = 0#w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_ternaryLogic a a a 0x00#8 i hi]
  simp

private theorem ternaryLogic_all1 {w : Nat} (a : BitVec w) :
    BitVec.ternaryLogic a a a 0xFF#8 = BitVec.allOnes w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_ternaryLogic a a a 0xFF#8 i hi]
  cases a.getLsbD i <;> simp [hi]

theorem ternaryLogic_or (a b : BitVec 128) :
    BitVec.ternaryLogic a b b 0xFE#8 = a ||| b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_ternaryLogic a b b 0xFE#8 i hi, BitVec.getLsbD_or]
  cases a.getLsbD i <;> cases b.getLsbD i <;> rfl

theorem shufd_0x4e_combine128 (hi64 lo64 : BitVec 64) :
    ((hi64.setWidth 128).shuffleDwords 0x4e#8) ||| (lo64.setWidth 128) =
      (hi64 ++ lo64).cast (by decide) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_or, BitVec.shuffleDwords, getLsbD_ofLanes _ (by decide) (by decide) i hi,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_cast, BitVec.getLsbD_append]
  have hi' : (i : Nat) < 128 := hi
  simp only [BitVec.lane, BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth,
    show i % 32 < 32 from Nat.mod_lt _ (by decide), decide_true, Bool.true_and]
  rcases Nat.lt_or_ge i 64 with h64 | h64
  · have hq : i / 32 = 0 ∨ i / 32 = 1 := by omega
    have hidx : 4 * ((i / 32) / 4) + ((0x4e#8 : BitVec 8).toNat >>> (2 * ((i / 32) % 4))) % 4 =
        i / 32 + 2 := by
      rcases hq with h | h <;> simp [h]
    rw [hidx]
    have hhi0 : hi64.getLsbD (32 * (i / 32 + 2) + i % 32) = false :=
      BitVec.getLsbD_of_ge hi64 _ (by omega)
    have hlt128 : 32 * (i / 32 + 2) + i % 32 < 128 := by omega
    simp [hhi0, h64, hi', hlt128]
  · have hq : i / 32 = 2 ∨ i / 32 = 3 := by omega
    have hidx : 4 * ((i / 32) / 4) + ((0x4e#8 : BitVec 8).toNat >>> (2 * ((i / 32) % 4))) % 4 =
        i / 32 - 2 := by
      rcases hq with h | h <;> simp [h]
    rw [hidx]
    have hsum : 32 * (i / 32 - 2) + i % 32 = i - 64 := by omega
    have hlo0 : lo64.getLsbD i = false := BitVec.getLsbD_of_ge lo64 i (by omega)
    have hfalse : ¬(i < 64) := by omega
    have hi64_lt : i - 64 < 128 := by omega
    simp [hsum, hlo0, hfalse, hi', hi64_lt]

theorem movi128_join512 (c : BitVec 512) :
    ((c.extractLsb' 64 64 ++ c.extractLsb' 0 64).cast (by decide) : BitVec 128) = c.setWidth 128 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_cast, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb',
    BitVec.getLsbD_setWidth, show (i : Nat) < 128 from hi, decide_true, Bool.true_and]
  split <;> rename_i hlt
  · simp [hlt]
  · simp [show (i : Nat) - 64 < 64 by omega, show 64 + (i - 64) = i by omega]

theorem x64Movi64_wp [Host] (vd : RegMm) (lo : BitVec 64) (s : MachineData) :
    @Program.wp _ (x64Movi64 vd lo)
      (fun s' => s'.dmem = s.dmem ∧ s'.status = s.status ∧
        (∀ r, r ≠ .r10 → s'.regs.get64 r = s.regs.get64 r) ∧
        (∀ vr, vr ≠ vd → s'.zmms.get512 vr = s.zmms.get512 vr) ∧
        s'.zmms.get512 vd = (lo.setWidth 128).setWidth 512)
      (fun _ _ => False) s := by
  refine Program.wp.cons (Directive.FallsTo.wp (x64MoviD_fallsTo .r10 lo s)) ?_
  rintro s₁ rfl
  refine Program.wp.mono (Directive.FallsTo.wp (x64VmovIn64_reg_fallsTo vd .r10 _)) ?_
  rintro s' rfl
  refine ⟨rfl, rfl, fun r hr => Reg64s.get64_set64_of_ne _ _ _ _ hr.symm,
    fun vr hvr => RegZmms.get512_set_xmm_of_ne _ hvr.symm _, ?_⟩
  dsimp only
  rw [RegZmms.get512_set_xmm_same, Reg64s.get64_set64_same]

theorem x64Movi128_wp [Host] (vd tmp : RegMm) (hne : tmp ≠ vd) (c : BitVec 512) (s : MachineData) :
    @Program.wp _ (x64Movi128 vd tmp c)
      (fun s' => s'.dmem = s.dmem ∧ s'.status = s.status ∧
        (∀ r, r ≠ .r10 → s'.regs.get64 r = s.regs.get64 r) ∧
        (∀ vr, vr ≠ vd → vr ≠ tmp → s'.zmms.get512 vr = s.zmms.get512 vr) ∧
        s'.zmms.get512 vd = (c.setWidth 128).setWidth 512)
      (fun _ _ => False) s := by
  refine Program.wp.cons (Directive.FallsTo.wp (x64MoviD_fallsTo .r10 (c.extractLsb' 64 64) s)) ?_
  rintro s1 rfl
  refine Program.wp.cons (Directive.FallsTo.wp (x64VmovIn64_reg_fallsTo vd .r10 _)) ?_
  rintro s2 rfl
  refine Program.wp.cons (Directive.FallsTo.wp (x64Pshufd_fallsTo vd vd 0x4e#8 _)) ?_
  rintro s3 rfl
  refine Program.wp.cons (Directive.FallsTo.wp (x64MoviD_fallsTo .r10 (c.extractLsb' 0 64) _)) ?_
  rintro s4 rfl
  refine Program.wp.cons (Directive.FallsTo.wp (x64VmovIn64_reg_fallsTo tmp .r10 _)) ?_
  rintro s5 rfl
  refine Program.wp.mono (Directive.FallsTo.wp (x64Vpternlogd_fallsTo .w128 vd tmp tmp 0xFE#8 _)) ?_
  rintro s' rfl
  let z1 := s.zmms.set (.xmm vd) ((c.extractLsb' 64 64).setWidth 128)
  let z2 := z1.setLegacy (.xmm vd) (((z1.get512 vd).setWidth 128).shuffleDwords 0x4e#8)
  let z3 := z2.set (.xmm tmp) ((c.extractLsb' 0 64).setWidth 128)
  have hd_set : BitVec.ternaryLogic ((z3.get512 vd).setWidth 128)
      ((z3.get512 tmp).setWidth 128) ((z3.get512 tmp).setWidth 128) 0xFE#8 =
      c.setWidth 128 := by
    dsimp only [z3, z2, z1]
    rw [RegZmms.get512_set_xmm_of_ne _ hne,
      RegZmms.get512_setLegacy_xmm,
      setWidth_replaceLow (by decide),
      RegZmms.get512_set_xmm_same,
      BitVec.setWidth_setWidth_of_le _ (by decide),
      BitVec.setWidth_eq,
      RegZmms.get512_set_xmm_same,
      BitVec.setWidth_setWidth_of_le _ (by decide),
      BitVec.setWidth_eq,
      ternaryLogic_or,
      shufd_0x4e_combine128,
      movi128_join512]
  refine ⟨rfl, rfl, fun r hr => ?_, fun vr hvd htmp => ?_, ?_⟩
  · simp [Reg64s.get64_set64_of_ne _ _ _ _ hr.symm]
  · dsimp only
    rw [RegZmms.get512_set_avx_of_ne _ .w128 hvd.symm,
      RegZmms.get512_set_xmm_of_ne _ htmp.symm,
      RegZmms.get512_setLegacy_xmm_of_ne _ hvd.symm,
      RegZmms.get512_set_xmm_of_ne _ hvd.symm]
  · dsimp only
    rw [RegZmms.get512_set_avx_same, Reg64s.get64_set64_same]
    exact congrArg (BitVec.setWidth 512) hd_set

theorem x64VmoviWith_wp [Host] {tmp : RegMm} {w : SlotWidth} {vd : RegMm} {c : BitVec 512}
    {code : List Directive} (hcode : x64VmoviWith tmp w vd c = some code) (hne : tmp ≠ vd)
    (s : MachineData) :
    @Program.wp _ code
      (fun s' => s'.dmem = s.dmem ∧ s'.status = s.status ∧
        (∀ r, r ≠ .r10 → s'.regs.get64 r = s.regs.get64 r) ∧
        (∀ vr, vr ≠ vd → vr ≠ tmp → s'.zmms.get512 vr = s.zmms.get512 vr) ∧
        (s'.zmms.get512 vd).setWidth w.bits = c.setWidth w.bits)
      (fun _ _ => False) s := by
  dsimp only [x64VmoviWith] at hcode
  obtain ⟨ci, hci, rfl⟩ := emitCleanOpt_eq_some.mp hcode
  cases w with
  | w64 =>
    simp only [x64VmoviWithIns, Option.some.injEq] at hci
    subst hci
    refine Program.wp.mono (x64Movi64_wp vd (c.extractLsb' 0 64) s) ?_
    rintro s' ⟨hd, hs, hg, hv, hvd⟩
    refine ⟨hd, hs, hg, fun vr h1 _ => hv vr h1, ?_⟩
    rw [hvd, BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_setWidth_of_le _ (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp [show (i : Nat) < 64 from hi]
  | w128 =>
    simp only [x64VmoviWithIns, Option.some.injEq] at hci
    subst hci
    refine Program.wp.mono (x64Movi128_wp vd tmp hne c s) ?_
    rintro s' ⟨hd, hs, hg, hv, hvd⟩
    refine ⟨hd, hs, hg, hv, ?_⟩
    rw [hvd, BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]
  | w256 | w512 =>
    dsimp only [x64VmoviWithIns] at hci
    split at hci
    · rename_i hz
      simp only [Option.some.injEq] at hci
      subst hci
      refine Program.wp.mono (Directive.FallsTo.wp (x64Vpternlogd_fallsTo _ vd vd vd 0x00#8 s)) ?_
      rintro s' rfl
      refine ⟨rfl, rfl, fun _ _ => rfl,
        fun vr h1 _ => RegZmms.get512_set_avx_of_ne _ _ h1.symm _, ?_⟩
      dsimp only
      rw [RegZmms.get512_set_avx_same, ternaryLogic_all0, BitVec.setWidth_setWidth_of_le _ (by decide),
        BitVec.setWidth_eq]
      exact (beq_iff_eq.mp hz).symm
    · split at hci
      · rename_i hones
        simp only [Option.some.injEq] at hci
        subst hci
        refine Program.wp.mono (Directive.FallsTo.wp (x64Vpternlogd_fallsTo _ vd vd vd 0xFF#8 s)) ?_
        rintro s' rfl
        refine ⟨rfl, rfl, fun _ _ => rfl,
          fun vr h1 _ => RegZmms.get512_set_avx_of_ne _ _ h1.symm _, ?_⟩
        dsimp only
        rw [RegZmms.get512_set_avx_same, ternaryLogic_all1, BitVec.setWidth_setWidth_of_le _ (by decide),
          BitVec.setWidth_eq]
        exact (beq_iff_eq.mp hones).symm
      · simp at hci

/-! ## 5. Slot `bytes64` / `Int.toBytes` bridge lemmas -/

theorem array64_eq_bytes64 (a : BitVec 64) (xs : List (BitVec 64)) (h : 8 * xs.length ≤ 2 ^ 64) :
    array64 a xs = Eq ((bytes64 xs).At a) := by
  induction xs generalizing a with
  | nil => rw [array64_nil, bytes64, List.flatMap_nil]; exact eq_nil_At a
  | cons x xs ih =>
    have hl : (Int.toBytes 8 x.toInt).length + (bytes64 xs).length ≤ 2 ^ 64 := by
      simp only [Int.toBytes_length, bytes64_length] at *; simp at h; omega
    have h' : 8 * xs.length ≤ 2 ^ 64 := by simp at h; omega
    rw [array64_cons, ih (a + 8) h',
      show bytes64 (x :: xs) = Int.toBytes 8 x.toInt ++ bytes64 xs from rfl]
    show (Eq ((Int.toBytes 8 x.toInt).At a) ⋆ Eq ((bytes64 xs).At (a + BitVec.ofNat 64 8))) = _
    rw [Mem.At_append_sep _ _ a hl, Int.toBytes_length]

private theorem toBytes_append_nat (a b n : Nat) :
    Int.toBytes (a + b) (n : Int) = Int.toBytes a (n : Int) ++ Int.toBytes b ((n / 256 ^ a : Nat) : Int) := by
  induction a generalizing n with
  | zero => simp [Int.toBytes]
  | succ a ih =>
    rw [Nat.succ_add, Int.toBytes, Int.toBytes, List.cons_append]
    congr 1
    have hdiv : (n : Int) / 256 = ((n / 256 : Nat) : Int) := by omega
    rw [hdiv, ih (n / 256), Nat.pow_succ, Nat.mul_comm (256 ^ a) 256, ← Nat.div_div_eq_div_mul]

private theorem toBytes_bitvec_eq_toNat {m n : Nat} (h : m = 8 * n) (x : BitVec m) :
    Int.toBytes n x.toInt = Int.toBytes n (x.toNat : Int) := by
  rw [← Int.toBytes_emod, ← Int.toBytes_emod (x := (x.toNat : Int)), Int.take, Int.take, ← h]
  congr 1
  rw [BitVec.toInt_eq_msb_cond]
  have hlt : (x.toNat : Int) < 2 ^ m := by exact_mod_cast x.isLt
  have hnn : (0 : Int) ≤ x.toNat := Int.natCast_nonneg _
  cases x.msb
  · simp [Int.emod_eq_of_lt hnn hlt]
  · simp only [↓reduceIte, Int.natCast_pow, Int.cast_ofNat_Int]
    rw [Int.sub_emod_right, Int.emod_eq_of_lt hnn hlt]

private theorem toBytes_extract_step {m : Nat} (k : Nat) (hk : 64 + 8 * k = m) (v : BitVec m) :
    Int.toBytes (8 + k) (v.toNat : Int) =
      Int.toBytes 8 (v.extractLsb' 0 64).toInt ++
        Int.toBytes k ((v.extractLsb' 64 (8 * k)).toNat : Int) := by
  rw [toBytes_append_nat 8 k v.toNat, toBytes_bitvec_eq_toNat (n := 8) rfl]
  have h256 : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
  have hlo : Int.toBytes 8 ((v.extractLsb' 0 64).toNat : Int) = Int.toBytes 8 (v.toNat : Int) := by
    rw [← Int.toBytes_emod, ← Int.toBytes_emod (x := (v.toNat : Int)), Int.take, Int.take]
    congr 1
    simp only [BitVec.extractLsb', BitVec.toNat_ofNat, Nat.shiftRight_zero,
      show (8 * 8 : Nat) = 64 from rfl]
    exact_mod_cast Nat.mod_eq_of_lt (Nat.mod_lt v.toNat (by decide : 0 < 2 ^ 64))
  have hhi : v.toNat / 256 ^ 8 = (v.extractLsb' 64 (8 * k)).toNat := by
    rw [h256, BitVec.extractLsb', BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    symm
    apply Nat.mod_eq_of_lt
    have hv : v.toNat < 2 ^ m := v.isLt
    rw [Nat.div_lt_iff_lt_mul (Nat.pow_pos (by decide))]
    rw [← Nat.pow_add, Nat.add_comm (8 * k) 64, hk]
    exact hv
  rw [hlo, hhi]

private theorem toBytes_bitvec64_split {m k : Nat} (h : 64 + 8 * k = m) (v : BitVec m) :
    Int.toBytes (8 + k) v.toInt =
      Int.toBytes 8 (v.extractLsb' 0 64).toInt ++ Int.toBytes k (v.extractLsb' 64 (8 * k)).toInt := by
  rw [toBytes_bitvec_eq_toNat (m := m) (n := 8 + k) (by omega) v,
    toBytes_extract_step k h v, toBytes_bitvec_eq_toNat (m := 8 * k) (n := k) rfl]

private theorem bytes64_cons (x : BitVec 64) (xs : List (BitVec 64)) :
    bytes64 (x :: xs) = Int.toBytes 8 x.toInt ++ bytes64 xs := rfl

private theorem bytes64_nil : bytes64 [] = [] := rfl

private def extract64List (bv : BitVec 512) (off : Nat) : Nat → List (BitVec 64)
  | 0 => []
  | k + 1 => bv.extractLsb' off 64 :: extract64List bv (off + 64) k

private theorem extract64_zero {w : Nat} (bv : BitVec w) (off len : Nat) (hlen : 64 ≤ len) :
    (bv.extractLsb' off len).extractLsb' 0 64 = bv.extractLsb' off 64 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp [show (i : Nat) < 64 from hi, show (i : Nat) < len by omega]

private theorem extract64_step {w : Nat} (bv : BitVec w) (off lo m : Nat) :
    (bv.extractLsb' off (lo + m)).extractLsb' lo m = bv.extractLsb' (off + lo) m := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp [show (i : Nat) < m from hi, Nat.add_assoc]

private theorem extract64_step_toInt {w : Nat} (bv : BitVec w) (off lo m1 m2 m3 : Nat)
    (hm1 : m1 = m2) (hm3 : m3 = lo + m2) :
    ((bv.extractLsb' off m3).extractLsb' lo m1).toInt =
      (bv.extractLsb' (off + lo) m2).toInt := by
  subst hm1; subst hm3; rw [extract64_step]

private theorem bytes64_extract64List (bv : BitVec 512) :
    ∀ (k off : Nat), off + 64 * k ≤ 512 →
      bytes64 (extract64List bv off k) = Int.toBytes (8 * k) (bv.extractLsb' off (64 * k)).toInt
  | 0, _, _ => rfl
  | k + 1, off, _ => by
    rw [extract64List, bytes64_cons, bytes64_extract64List bv k (off + 64) (by omega)]
    have hsplit := toBytes_bitvec64_split (m := 64 * (k + 1)) (k := 8 * k) (by omega)
      (bv.extractLsb' off (64 * (k + 1)))
    rw [show 8 * (k + 1) = 8 + 8 * k from by omega, hsplit]
    have h1 : (bv.extractLsb' off (64 * (k + 1))).extractLsb' 0 64 = bv.extractLsb' off 64 :=
      extract64_zero bv off (64 * (k + 1)) (by omega)
    rw [h1]
    have hrest := extract64_step_toInt bv off 64 (8 * (8 * k)) (64 * k) (64 * (k + 1)) (by omega) (by omega)
    rw [hrest]

theorem bytes64_unpackSlotWords (w : SlotWidth) (bv : BitVec 512) :
    bytes64 (unpackSlotWords w bv) =
      Int.toBytes (8 * w.slots) (bv.setWidth (64 * w.slots)).toInt := by
  have hlist : unpackSlotWords w bv = extract64List bv 0 w.slots := by
    cases w <;> rfl
  have hex : bv.extractLsb' 0 (64 * w.slots) = bv.setWidth (64 * w.slots) := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp [show (i : Nat) < 64 * w.slots from hi]
  rw [hlist, bytes64_extract64List bv w.slots 0 (by have := w.slots_le_eight; omega), hex]

/-! ## 6. `VecTarget` non-op specifications & `NoLab` theorems -/

theorem x64Vmov_spec {h : Host} {k : Nat} {w : SlotWidth} {vd vs : RegMm} {s : MachineData}
    {post : MachineState → Prop} :
    x64Mach.FallsTo x64CondReads h k (x64Vmov w vd vs) [] [vd] FlagMask.none s
      (fun s' => (x64Mach.getVec s' vd).setWidth w.bits = (x64Mach.getVec s vs).setWidth w.bits ∧
        x64Mach.mem s' = x64Mach.mem s) post := by
  apply vecFallsTo_of_wp
  refine Program.wp.mono (Directive.FallsTo.wp (x64VmovDqu32_fallsTo w vd vs s)) ?_
  rintro s' rfl
  refine ⟨⟨?_, rfl⟩, vecFrame_upd (fun _ _ => rfl) (fun vr hvr => ?_) (Or.inr rfl)⟩
  · dsimp only [x64Mach]
    rw [RegZmms.get512_set_avx_same,
      BitVec.setWidth_setWidth_of_le _ w.bits_le_512,
      BitVec.setWidth_setWidth_of_le _ (x64W_bits_le_awBits w)]
  · exact RegZmms.get512_set_avx_of_ne _ w (fun e => hvr (by simp [e])) _

theorem x64Vmovi_spec {h : Host} {k : Nat} {w : SlotWidth} {vd : RegMm} {c : BitVec 512}
    {code : List Directive} {s : MachineData} {post : MachineState → Prop}
    (hcode : x64Vmovi w vd c = some code) (hvd : vd ∉ x64VecScratch) :
    x64Mach.FallsTo x64CondReads h k code x64Scratch (vd :: x64VecScratch) FlagMask.none s
      (fun s' => (x64Mach.getVec s' vd).setWidth w.bits = c.setWidth w.bits ∧
        x64Mach.mem s' = x64Mach.mem s) post := by
  have hne : .mm14 ≠ vd := (ne_of_not_mem_x64VecScratch hvd).1.symm
  apply vecFallsTo_of_wp
  refine Program.wp.mono (x64VmoviWith_wp hcode hne s) ?_
  rintro s' ⟨hdmem, hst, hgpr, hv, hvd_val⟩
  refine ⟨⟨hvd_val, hdmem⟩, vecFrame_upd (fun r hr => ?_) (fun vr hvr => ?_) (Or.inr hst)⟩
  · exact hgpr r (ne_of_not_mem_x64Scratch hr).1
  · rw [List.mem_cons, not_or] at hvr
    exact hv vr hvr.1 (ne_of_not_mem_x64VecScratch hvr.2).1

private theorem vmovOut64_mem_fallsTo (addr : AddrExpr) (a : BitVec 64) (vs : RegMm)
    (s : MachineData)
    (haddr : ∀ [Labels] (p : Std.Rco Int64), (@AddrExpr.interp _ ⟨.W64⟩ addr s.regs p).zeroExtend 64 = a)
    (hload : ∃ i, Mem.loadInt s.dmem a 8 = some i) :
    Directive.FallsTo (x64Avx128 (.vmovOut .W64 (.mem addr) (.xmm vs))) s
      (fun s' => s'.regs = s.regs ∧ s'.zmms = s.zmms ∧ s'.status = s.status ∧
        s'.dmem = Mem.storeInt s.dmem a 8 ((s.zmms.get512 vs).setWidth 64).toInt) := by
  obtain ⟨i, hi⟩ := hload
  intro _ p next jmp P hk
  simp only [t_step_simp, AvxOperation.interp, MachineData.set, haddr p]
  rw [store_All_of_loadInt _ _ .W64 _ _ _ i hi, RegZmms.get_eq_setWidth, AvxReg.base,
    take_eq_setWidth, BitVec.setWidth_setWidth_of_le _ (by decide)]
  exact hk _ ⟨rfl, rfl, rfl, rfl⟩

private theorem vmovdqu32_store_fallsTo (w : SlotWidth) (hne : w ≠ .w64) (addr : AddrExpr)
    (a : BitVec 64) (vs : RegMm) (s : MachineData)
    (haddr : ∀ [Labels] (p : Std.Rco Int64), (@AddrExpr.interp _ ⟨.W64⟩ addr s.regs p).zeroExtend 64 = a)
    (hload : ∃ i, Mem.loadInt s.dmem a (8 * w.slots) = some i) :
    Directive.FallsTo (x64Avx w (.vmovdqu32 (.mem addr) (.avx (x64AvxRegOf w vs)))) s
      (fun s' => s'.regs = s.regs ∧ s'.zmms = s.zmms ∧ s'.status = s.status ∧
        s'.dmem = Mem.storeInt s.dmem a (8 * w.slots)
          ((s.zmms.get512 vs).setWidth (64 * w.slots)).toInt) := by
  obtain ⟨i, hi⟩ := hload
  have hbytes : (x64AwOf w).bytes = 8 * w.slots := x64AwOf_bytes_of_ne_w64 hne
  have hbits : (x64AwOf w).bits = 64 * w.slots := by
    rw [x64AwOf_bits_of_ne_w64 hne, SlotWidth.bits_eq_64_mul_slots]
  intro _ p next jmp P hk
  simp only [t_step_simp, AvxOperation.interp, AvxRegOrMem.interp, MachineData.setAvx, haddr p]
  rw [storeAvx_All_of_loadInt _ _ (x64AwOf w) _ _ _ i (hbytes ▸ hi), hbytes,
    RegZmms.get_eq_setWidth, x64AvxRegOf_base, hbits]
  exact hk _ ⟨rfl, rfl, rfl, rfl⟩

private theorem vmovIn64_mem_fallsTo (addr : AddrExpr) (a : BitVec 64) (vd : RegMm) (i : Int)
    (s : MachineData)
    (haddr : ∀ [Labels] (p : Std.Rco Int64), (@AddrExpr.interp _ ⟨.W64⟩ addr s.regs p).zeroExtend 64 = a)
    (hload : Mem.loadInt s.dmem a 8 = some i) :
    Directive.FallsTo (x64Avx128 (.vmovIn .W64 (.xmm vd) (.mem addr))) s
      (fun s' => s' = { s with zmms := s.zmms.set (.xmm vd) ((BitVec.ofInt 64 i).setWidth 128) }) := by
  intro _ p next jmp P hk
  simp only [t_step_simp, AvxOperation.interp, RegOrMem.interp, MachineData.setAvxReg, haddr p]
  rw [load_All_of_loadInt _ _ .W64 _ _ i hload, zeroExtend_eq_setWidth]
  exact hk _ rfl

private theorem vmovdqu32_load_fallsTo (w : SlotWidth) (hne : w ≠ .w64) (addr : AddrExpr)
    (a : BitVec 64) (vd : RegMm) (i : Int) (s : MachineData)
    (haddr : ∀ [Labels] (p : Std.Rco Int64), (@AddrExpr.interp _ ⟨.W64⟩ addr s.regs p).zeroExtend 64 = a)
    (hload : Mem.loadInt s.dmem a (8 * w.slots) = some i) :
    Directive.FallsTo (x64Avx w (.vmovdqu32 (.avx (x64AvxRegOf w vd)) (.mem addr))) s
      (fun s' => s' = { s with zmms := (s.zmms.set (x64AvxRegOf w vd)
        (BitVec.ofInt (x64AwOf w).bits i)) }) := by
  have hbytes : (x64AwOf w).bytes = 8 * w.slots := x64AwOf_bytes_of_ne_w64 hne
  intro _ p next jmp P hk
  simp only [t_step_simp, AvxOperation.interp, AvxRegOrMem.interp, MachineData.setAvx,
    MachineData.setAvxReg, haddr p]
  rw [loadAvx_All_of_loadInt _ _ (x64AwOf w) _ _ i (hbytes ▸ hload)]
  exact hk _ rfl

theorem x64VslotSt_spec {h : Host} {k : Nat} {w : SlotWidth} {i : Nat} {vr : RegMm}
    {s : MachineData} {G : Mem 64 → Prop} {post : MachineState → Prop}
    (_hvr : vr ∉ x64VecScratch) (_hsp : True)
    (hmem : s.dmem =⋆ region (s.regs.get64 .rsp + BitVec.ofNat 64 (8 * i)) (8 * w.slots) ⋆ G) :
    x64Mach.FallsTo x64CondReads h k (x64VslotSt w i vr) x64Scratch x64VecScratch FlagMask.none s
      (fun s' => s'.dmem =⋆
        array64 (s.regs.get64 .rsp + BitVec.ofNat 64 (8 * i))
          (unpackSlotWords w (x64Mach.getVec s vr)) ⋆ G) post := by
  let a := s.regs.get64 .rsp + BitVec.ofNat 64 (8 * i)
  obtain ⟨bs, hbs_len, hbs_mem⟩ := region_sep_elim hmem
  have hslots_le : 8 * w.slots ≤ 2 ^ 64 := by have := w.slots_le_eight; omega
  have hload : Mem.loadInt s.dmem a (8 * w.slots) = some (Int.ofBytes bs) :=
    Mem.loadInt_sep bs a (8 * w.slots) G s.dmem hbs_mem hbs_len hslots_le
  have harr : array64 a (unpackSlotWords w (x64Mach.getVec s vr)) =
      Eq ((Int.toBytes (8 * w.slots) ((x64Mach.getVec s vr).setWidth (64 * w.slots)).toInt).At a) := by
    rw [array64_eq_bytes64 a _ (by rw [unpackSlotWords_length]; exact hslots_le),
      bytes64_unpackSlotWords]
  apply vecFallsTo_of_wp
  dsimp only [x64VslotSt, x64VslotStIns]
  simp only [emitClean_append, emitClean_cons, emitClean_nil]
  refine Program.wp.append (x64SlotAddr_fallsTo i s) ?_
  rintro s1 ⟨hdmem1, hst1, hzmms1, hgpr1, haddr1⟩
  have hload1 : Mem.loadInt s1.dmem a (8 * w.slots) = some (Int.ofBytes bs) := hdmem1 ▸ hload
  have hst_mem : (Eq ((Int.toBytes (8 * w.slots)
      ((x64Mach.getVec s vr).setWidth (64 * w.slots)).toInt).At a) ⋆ G)
      (Mem.storeInt s1.dmem a (8 * w.slots) ((x64Mach.getVec s vr).setWidth (64 * w.slots)).toInt) :=
    Mem.storeInt_sep a (8 * w.slots) bs G s1.dmem ⟨hdmem1 ▸ hbs_mem, hbs_len⟩ _
  by_cases hw64 : w = .w64
  · subst hw64; refine Program.wp.mono (Directive.FallsTo.wp (vmovOut64_mem_fallsTo (x64SlotAddr i).2 a vr
        s1 (fun {_} p => haddr1 p) ⟨_, hload1⟩)) ?_
    rintro s' ⟨hg', hv', hst', hdmem'⟩
    refine ⟨?_, vecFrame_upd (fun r hr => ?_) (fun v _ => by rw [hv', hzmms1]) (Or.inr (hst'.trans hst1))⟩
    · dsimp only [x64Mach] at harr hst_mem ⊢
      rw [harr, hdmem', hzmms1]
      exact hst_mem
    · rw [hg']; exact hgpr1 r (ne_of_not_mem_x64Scratch hr).1
  · dsimp only [x64VmemI]; split
    · exact absurd rfl hw64
    · refine Program.wp.mono (Directive.FallsTo.wp (vmovdqu32_store_fallsTo w hw64 (x64SlotAddr i).2 a vr
          s1 (fun {_} p => haddr1 p) ⟨_, hload1⟩)) ?_
      rintro s' ⟨hg', hv', hst', hdmem'⟩
      refine ⟨?_, vecFrame_upd (fun r hr => ?_) (fun v _ => by rw [hv', hzmms1]) (Or.inr (hst'.trans hst1))⟩
      · dsimp only [x64Mach] at harr hst_mem ⊢
        rw [harr, hdmem', hzmms1]
        exact hst_mem
      · rw [hg']; exact hgpr1 r (ne_of_not_mem_x64Scratch hr).1

private theorem ofInt_ofBytes_toBytes_cast {m k n : Nat} (hm : m = k) (hn : k = 8 * n)
    (x : BitVec k) :
    BitVec.ofInt m (Int.ofBytes (Int.toBytes n x.toInt)) = x.cast hm.symm := by
  subst hm; subst hn; exact BitVec.ofInt_ofBytes_toBytes _ n rfl x

theorem x64VslotLd_spec {h : Host} {k : Nat} {w : SlotWidth} {i : Nat} {vd : RegMm}
    {bv : BitVec 512} {s : MachineData} {G : Mem 64 → Prop} {post : MachineState → Prop}
    (_hvd : vd ∉ x64VecScratch) (_hsp : True)
    (hmem : s.dmem =⋆
      array64 (s.regs.get64 .rsp + BitVec.ofNat 64 (8 * i)) (unpackSlotWords w bv) ⋆ G) :
    x64Mach.FallsTo x64CondReads h k (x64VslotLd w vd i) x64Scratch (vd :: x64VecScratch) FlagMask.none s
      (fun s' => (x64Mach.getVec s' vd).setWidth w.bits = bv.setWidth w.bits ∧
        x64Mach.mem s' = x64Mach.mem s) post := by
  let a := s.regs.get64 .rsp + BitVec.ofNat 64 (8 * i)
  have hslots_le : 8 * w.slots ≤ 2 ^ 64 := by have := w.slots_le_eight; omega
  have harr : array64 a (unpackSlotWords w bv) =
      Eq ((Int.toBytes (8 * w.slots) (bv.setWidth (64 * w.slots)).toInt).At a) := by
    rw [array64_eq_bytes64 a _ (by rw [unpackSlotWords_length]; exact hslots_le),
      bytes64_unpackSlotWords]
  have hmem_bs : (Eq ((Int.toBytes (8 * w.slots) (bv.setWidth (64 * w.slots)).toInt).At a) ⋆ G)
      s.dmem := by rwa [← harr]
  have hload : Mem.loadInt s.dmem a (8 * w.slots) =
      some (Int.ofBytes (Int.toBytes (8 * w.slots) (bv.setWidth (64 * w.slots)).toInt)) :=
    Mem.loadInt_sep _ a (8 * w.slots) G s.dmem hmem_bs (Int.toBytes_length _ _) hslots_le
  apply vecFallsTo_of_wp
  dsimp only [x64VslotLd, x64VslotLdIns]
  simp only [emitClean_append, emitClean_cons, emitClean_nil]
  refine Program.wp.append (x64SlotAddr_fallsTo i s) ?_
  rintro s1 ⟨hdmem1, hst1, hzmms1, hgpr1, haddr1⟩
  have hload1 : Mem.loadInt s1.dmem a (8 * w.slots) = _ := hdmem1 ▸ hload
  by_cases hw64 : w = .w64
  · subst hw64; refine Program.wp.mono (Directive.FallsTo.wp (vmovIn64_mem_fallsTo (x64SlotAddr i).2 a vd _ s1
        (fun {_} p => haddr1 p) hload1)) ?_
    rintro s' rfl
    have hbv : BitVec.ofInt 64 (Int.ofBytes (Int.toBytes 8 (bv.setWidth 64).toInt)) = bv.setWidth 64 :=
      BitVec.ofInt_ofBytes_toBytes 64 8 rfl _
    refine ⟨⟨?_, hdmem1⟩, vecFrame_upd (fun r hr => hgpr1 r (ne_of_not_mem_x64Scratch hr).1)
      (fun v hv => ?_) (Or.inr hst1)⟩
    · dsimp only [x64Mach]
      rw [RegZmms.get512_set_xmm_same, show SlotWidth.w64.bits = 64 from rfl,
        BitVec.setWidth_setWidth_of_le _ (by decide : 64 ≤ 512),
        BitVec.setWidth_setWidth_of_le _ (by decide : 64 ≤ 128),
        show SlotWidth.w64.slots = 1 from rfl, Nat.mul_one, hbv, BitVec.setWidth_eq]
    · rw [RegZmms.get512_set_xmm_of_ne _ (fun e => hv (by simp [e])), hzmms1]
  · dsimp only [x64VmemI]; split
    · exact absurd rfl hw64
    · refine Program.wp.mono (Directive.FallsTo.wp (vmovdqu32_load_fallsTo w hw64 (x64SlotAddr i).2 a vd _ s1
          (fun {_} p => haddr1 p) hload1)) ?_
      rintro s' rfl
      refine ⟨⟨?_, hdmem1⟩, vecFrame_upd (fun r hr => hgpr1 r (ne_of_not_mem_x64Scratch hr).1)
        (fun v hv => ?_) (Or.inr hst1)⟩
      · dsimp only [x64Mach]
        rw [RegZmms.get512_set_avx_same]
        have hbits_eq : (x64AwOf w).bits = 64 * w.slots := by
          rw [x64AwOf_bits_of_ne_w64 hw64, SlotWidth.bits_eq_64_mul_slots]
        have hset : BitVec.ofInt (x64AwOf w).bits
            (Int.ofBytes (Int.toBytes (8 * w.slots) (bv.setWidth (64 * w.slots)).toInt)) =
            (bv.setWidth (64 * w.slots)).cast hbits_eq.symm :=
          ofInt_ofBytes_toBytes_cast hbits_eq (by omega) (bv.setWidth (64 * w.slots))
        rw [hset, BitVec.setWidth_setWidth_of_le _ w.bits_le_512]
        apply BitVec.eq_of_getLsbD_eq; intro j hj
        have hj1 : j < (x64AwOf w).bits := by
          rw [hbits_eq, ← SlotWidth.bits_eq_64_mul_slots]; exact hj
        have hj2 : j < 64 * w.slots := by
          rw [← SlotWidth.bits_eq_64_mul_slots]; exact hj
        simp [hj1, hj2]
      · rw [RegZmms.get512_set_avx_of_ne _ w (fun e => hv (by simp [e])), hzmms1]

private theorem setWidth_ofInt_of_eq {m n : Nat} (h : n = m) (i : Int) :
    (BitVec.ofInt m i).setWidth n = BitVec.ofInt n i := by
  subst h; exact BitVec.setWidth_eq _

theorem x64Vload_spec {h : Host} {k : Nat} {t : Ty} {vd : RegMm} {a : AddrArg Reg64}
    {c : List Directive} {clob : FlagMask} {val : Val t} {s : MachineData}
    {post : MachineState → Prop}
    (hv : x64Vload t vd a = some (c, clob)) (_hvd : vd ∉ x64VecScratch)
    (ha : ∀ r ∈ a.regs, r ∉ x64Scratch)
    (hload : loadVal (x64Mach.mem s) t (a.eval (x64Mach.getGpr s)) = some val) :
    x64Mach.FallsTo x64CondReads h k c x64Scratch (vd :: x64VecScratch) clob s
      (fun s' => VecHolds (x64Mach.getVec s' vd) t val ∧ x64Mach.mem s' = x64Mach.mem s) post := by
  dsimp only [x64Vload] at hv
  obtain ⟨ci, hci, rfl⟩ := emitCleanPair_eq_some.mp hv
  dsimp only [x64VloadIns] at hci
  cases hw : x64VecSlotWidth t with
  | none => simp [hw] at hci
  | some w =>
    rw [hw] at hci
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hci
    rcases hci with ⟨rfl, rfl⟩
    simp only [emitClean_append, emitClean_cons, emitClean_nil]
    obtain ⟨x, y, rfl⟩ := x64VecSlotWidth_pair hw
    have hbytes : (Ty.pair x y).bytes = 8 * w.slots := x64VecSlotWidth_bytes hw
    have hbits : w.bits = (Ty.pair x y).size := x64VecSlotWidth_bits_eq hw
    have hle512 : (Ty.pair x y).size ≤ 512 := x64VecSlotWidth_le_512 hw
    simp only [loadVal, Option.bind_eq_some_iff, Option.some.injEq] at hload
    obtain ⟨i_mem, hi_mem, rfl⟩ := hload
    have hsz : x.size + y.size = (Ty.pair x y).size := rfl
    apply vecFallsTo_of_wp
    refine Program.wp.append (x64AddrPrep_fallsTo ha) ?_
    rintro s1 ⟨hdmem1, hst1, hzmms1, hgpr1, haddr1⟩
    have hi1 : Mem.loadInt s1.dmem (a.eval s.regs.get64) (8 * w.slots) = some i_mem := by
      rw [hdmem1, ← hbytes]; exact hi_mem
    by_cases hw64 : w = .w64
    · subst hw64
      have hsz64 : x.size + y.size = 64 := hsz.trans (hbits.symm.trans rfl)
      refine Program.wp.mono (Directive.FallsTo.wp (vmovIn64_mem_fallsTo (x64AddrPrep a).2
          (a.eval s.regs.get64) vd i_mem s1 (fun {_} p => haddr1 p) hi1)) ?_
      rintro s' rfl
      refine ⟨⟨⟨hle512, ?_⟩, hdmem1⟩, vecFrame_upd (fun r hr => hgpr1 r (ne_of_not_mem_x64Scratch hr).1)
        (fun v hv => ?_) (Or.inr hst1)⟩
      · dsimp only [x64Mach]
        rw [RegZmms.get512_set_xmm_same, toBits_ofBits,
          BitVec.setWidth_setWidth_of_le _ (by omega : (Ty.pair x y).size ≤ 512),
          BitVec.setWidth_setWidth_of_le _ (by omega : (Ty.pair x y).size ≤ 128),
          setWidth_ofInt_of_eq (by omega) i_mem]
      · rw [RegZmms.get512_set_xmm_of_ne _ (fun e => hv (by simp [e])), hzmms1]
    · have htsize : (Ty.pair x y).size = (x64AwOf w).bits := by
        rw [← hbits, x64AwOf_bits_of_ne_w64 hw64]
      dsimp only [x64VmemI]; split
      · exact absurd rfl hw64
      · refine Program.wp.mono (Directive.FallsTo.wp (vmovdqu32_load_fallsTo w hw64 (x64AddrPrep a).2
            (a.eval s.regs.get64) vd i_mem s1 (fun {_} p => haddr1 p) hi1)) ?_
        rintro s' rfl
        refine ⟨⟨⟨hle512, ?_⟩, hdmem1⟩, vecFrame_upd (fun r hr => hgpr1 r (ne_of_not_mem_x64Scratch hr).1)
          (fun v hv => ?_) (Or.inr hst1)⟩
        · dsimp only [x64Mach]
          rw [RegZmms.get512_set_avx_same, toBits_ofBits,
            BitVec.setWidth_setWidth_of_le _ hle512,
            setWidth_ofInt_of_eq htsize i_mem]
        · rw [RegZmms.get512_set_avx_of_ne _ w (fun e => hv (by simp [e])), hzmms1]

private theorem toInt_eq_of_cast {m n : Nat} (h : m = n) (u : BitVec m) (v : BitVec n)
    (heq : u.cast h = v) : u.toInt = v.toInt := by
  subst h; cases heq; rfl

theorem x64Vstore_spec {h : Host} {k : Nat} {t : Ty} {vs : RegMm} {a : AddrArg Reg64}
    {c : List Directive} {clob : FlagMask} {val : Val t} {s : MachineData}
    {post : MachineState → Prop}
    (hv : x64Vstore t vs a = some (c, clob)) (ha : ∀ r ∈ a.regs, r ∉ x64Scratch)
    (_hvs : vs ∉ x64VecScratch) (hhold : VecHolds (x64Mach.getVec s vs) t val)
    (hsok : storeOk (x64Mach.mem s) t (a.eval (x64Mach.getGpr s))) :
    x64Mach.FallsTo x64CondReads h k c x64Scratch x64VecScratch clob s
      (fun s' => x64Mach.mem s' = storeMem (x64Mach.mem s) t (a.eval (x64Mach.getGpr s)) val) post := by
  dsimp only [x64Vstore] at hv
  obtain ⟨ci, hci, rfl⟩ := emitCleanPair_eq_some.mp hv
  dsimp only [x64VstoreIns] at hci
  cases hw : x64VecSlotWidth t with
  | none => simp [hw] at hci
  | some w =>
    rw [hw] at hci
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hci
    rcases hci with ⟨rfl, rfl⟩
    simp only [emitClean_append, emitClean_cons, emitClean_nil]
    have hbytes : t.bytes = 8 * w.slots := x64VecSlotWidth_bytes hw
    have hbits : w.bits = t.size := x64VecSlotWidth_bits_eq hw
    have hb8 : 8 * t.bytes = t.size := by
      rcases Bool.or_eq_true_iff.mp (x64IsVecBits_of_slot hw) with h' | h'
      · exact x64IsI32Vec_size_bytes h'
      · exact x64IsF32Vec_size_bytes h'
    obtain ⟨i_mem, hi_mem⟩ := hsok
    apply vecFallsTo_of_wp
    refine Program.wp.append (x64AddrPrep_fallsTo ha) ?_
    rintro s1 ⟨hdmem1, hst1, hzmms1, hgpr1, haddr1⟩
    have hi1 : Mem.loadInt s1.dmem (a.eval s.regs.get64) (8 * w.slots) = some i_mem := by
      rw [hdmem1, ← hbytes]; exact hi_mem
    by_cases hw64 : w = .w64
    · subst hw64
      have hts64 : t.size = 64 := hbits.symm
      refine Program.wp.mono (Directive.FallsTo.wp (vmovOut64_mem_fallsTo (x64AddrPrep a).2
          (a.eval s.regs.get64) vs s1 (fun {_} p => haddr1 p) ⟨_, hi1⟩)) ?_
      rintro s' ⟨hg', hv', hst', hdmem'⟩
      refine ⟨?_, vecFrame_upd (fun r hr => hg' ▸ hgpr1 r (ne_of_not_mem_x64Scratch hr).1)
        (fun v _ => by rw [hv', hzmms1]) (Or.inr (hst'.trans hst1))⟩
      change s'.dmem = storeMem s.dmem t (a.eval (x64Mach.getGpr s)) val
      rw [hdmem', hdmem1, hzmms1]
      simp only [storeMem]
      congr 1
      · exact hbytes.symm
      · refine toInt_eq_of_cast (by omega) ((s.zmms.get512 vs).setWidth 64)
          ((toBits t val).setWidth (8 * t.bytes)) ?_
        apply BitVec.eq_of_getLsbD_eq; intro j hj
        have h2 := congrArg (fun bv => bv.getLsbD j) hhold.2
        have hj64 : j < 64 := by omega
        simp [hj64, hb8, hts64] at h2 ⊢
        exact h2
    · have htsize : t.size = 64 * w.slots := by
        rw [← hbits, SlotWidth.bits_eq_64_mul_slots]
      dsimp only [x64VmemI]; split
      · exact absurd rfl hw64
      · refine Program.wp.mono (Directive.FallsTo.wp (vmovdqu32_store_fallsTo w hw64 (x64AddrPrep a).2
            (a.eval s.regs.get64) vs s1 (fun {_} p => haddr1 p) ⟨_, hi1⟩)) ?_
        rintro s' ⟨hg', hv', hst', hdmem'⟩
        refine ⟨?_, vecFrame_upd (fun r hr => hg' ▸ hgpr1 r (ne_of_not_mem_x64Scratch hr).1)
          (fun v _ => by rw [hv', hzmms1]) (Or.inr (hst'.trans hst1))⟩
        rw [hdmem', hdmem1, hzmms1]
        simp only [storeMem]
        congr 1
        · exact hbytes.symm
        · refine toInt_eq_of_cast (by omega) ((s.zmms.get512 vs).setWidth (64 * w.slots))
            ((toBits t val).setWidth (8 * t.bytes)) ?_
          apply BitVec.eq_of_getLsbD_eq; intro j hj
          have h2 := congrArg (fun bv => bv.getLsbD j) hhold.2
          have hj64s : j < 64 * w.slots := by omega
          simp [hj64s, hb8, htsize] at h2 ⊢
          exact h2

/-! ## 7. `NoLab` theorems (part 1) -/

section NoLab

theorem x64Vmov_noLab (w : SlotWidth) (vd vs : RegMm) (l : Sym) :
    Kraken.Directive.label l ∉ x64Vmov w vd vs :=
  emitClean_noLab _ l

theorem x64Vmovi_noLab {w : SlotWidth} {vd : RegMm} {c : BitVec 512} {code : List Directive}
    (h : x64Vmovi w vd c = some code) (l : Sym) : Kraken.Directive.label l ∉ code :=
  emitCleanOpt_noLab h l

theorem x64VslotSt_noLab (w : SlotWidth) (i : Nat) (vs : RegMm) (l : Sym) :
    Kraken.Directive.label l ∉ x64VslotSt w i vs :=
  emitClean_noLab _ l

theorem x64VslotLd_noLab (w : SlotWidth) (vd : RegMm) (i : Nat) (l : Sym) :
    Kraken.Directive.label l ∉ x64VslotLd w vd i :=
  emitClean_noLab _ l

theorem x64Vload_noLab {t : Ty} {vd : RegMm} {a : AddrArg Reg64} {c : List Directive}
    {clob : FlagMask} (h : x64Vload t vd a = some (c, clob)) (l : Sym) :
    Kraken.Directive.label l ∉ c :=
  emitCleanPair_noLab h l

theorem x64Vstore_noLab {t : Ty} {vs : RegMm} {a : AddrArg Reg64} {c : List Directive}
    {clob : FlagMask} (h : x64Vstore t vs a = some (c, clob)) (l : Sym) :
    Kraken.Directive.label l ∉ c :=
  emitCleanPair_noLab h l

end NoLab

end LeanQbe.T.Amd64
