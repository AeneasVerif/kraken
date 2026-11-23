module

public import LeanQbe.T.Amd64.Frame
public import LeanQbe.T.AbiLemmas
import Kraken.X64.Parser

/-!
# SysV x64 Frame Verification

Proves `x64FrameSpec : FrameTarget x64Mach x64Frame x64CondReads`, `NoLab` invariants for all
frame/call/ABI snippets, and `ParserChecks` against `Kraken.X64.Parser`.
All frame and slot proofs hold unconditionally up to `frameSize ns + 8 ≤ 2 ^ 64` (using `movabs`
+ register/indexed addressing when offsets reach `2 ^ 31`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Amd64

open Std Std.ExtHashMap

/-! ## 1. Frame size arithmetic and address helpers -/

theorem x64FrameSize_ge (ns : Nat) : 8 * ns ≤ x64FrameSize ns := by
  dsimp only [x64FrameSize]; split <;> omega

theorem x64FrameSize_mod (ns : Nat) : x64FrameSize ns % 16 = 8 := by
  dsimp only [x64FrameSize]
  rcases Nat.mod_two_eq_zero_or_one ns with h | h <;> simp [h] <;> omega

@[t_step_simp]
theorem x64AtSpR10_interp [Labels] (regs : Reg64s) (p : Std.Rco Int64) :
    (@AddrExpr.interp _ ⟨.W64⟩ x64AtSpR10 regs p).zeroExtend 64 =
      regs.get64 .rsp + regs.get64 .r10 := by
  simp only [AddrExpr.interp, BitVec.toAddressSize, BitVec.take, Width.bytes, ConstExpr.interp,
    Int64.toInt_zero, Int.add_zero, BitVec.signed, BitVec.extractLsb'_eq_self,
    BitVec.zeroExtend, BitVec.setWidth_eq]
  rw [show (↑(1 : Nat) : Int) = 1 from rfl, Int.mul_one]
  exact ofInt_toInt_add (regs.get64 .rsp) (regs.get64 .r10)

@[t_step_simp]
theorem x64AtSp_interp [Labels] (regs : Reg64s) (off : Int64) (p : Std.Rco Int64) :
    (@AddrExpr.interp _ ⟨.W64⟩ (x64AtSp off) regs p).zeroExtend 64 =
      regs.get64 .rsp + off.toBitVec := by
  rw [AddrExpr.interp_base_disp]
  simp [BitVec.zeroExtend, BitVec.setWidth_eq]

/-! ## 2. `Program.wp` to `x64Mach.FallsTo` bridge & single-directive step lemmas -/

private theorem fallsTo_of_wp {h : Host} {k : Nat} {c : List Directive}
    {gClob : List Reg64} {fClob : FlagMask} {s : MachineData}
    {Q : MachineData → Prop} {post : MachineState → Prop}
    (hwp : @Program.wp h c (fun s' => Q s' ∧ x64Mach.Frame x64CondReads s s' gClob [] fClob)
      (fun _ _ => False) s) :
    x64Mach.FallsTo x64CondReads h k c gClob [] fClob s Q post := by
  letI := h
  intro hc hk
  exact Program.wp.eventually hwp hc
    (fun s' ⟨hq, hfr⟩ => hk s' hq hfr) (fun _ _ hf => False.elim hf)

private theorem frame_upd_regs {s s' : MachineData} {gClob : List Reg64} {fClob : FlagMask}
    (hkeep : ∀ r, r ∉ gClob → s'.regs.get64 r = s.regs.get64 r)
    (hvec : s'.zmms = s.zmms)
    (hflg : fClob = maskAll ∨ s'.status = s.status) :
    x64Mach.Frame x64CondReads s s' gClob [] fClob := by
  refine ⟨hkeep, fun vr _ => by simp [hvec], ?_⟩
  rcases hflg with rfl | hst
  · intro cc hdisj
    cases cc <;> (
      dsimp only [FlagMask.disjoint, x64CondReads, maskAll, maskOF, maskCF, maskZF, maskSF,
        maskPF] at hdisj
      exact absurd hdisj (by decide))
  · intro cc _; simp [hst]

private theorem x64SubSpD_fallsTo (c : Int64) (s : MachineData) :
    Directive.FallsTo (x64SubSpD c) s
      (fun s' => s'.regs = s.regs.set64 .rsp (s.regs.get64 .rsp - c.toBitVec) ∧
        s'.zmms = s.zmms ∧ s'.dmem = s.dmem) := by
  intro _ p next jmp P hk
  dsimp only [x64SubSpD]; simp only [t_step_simp]
  exact hk _ ⟨rfl, rfl, rfl⟩

private theorem x64AddSpD_fallsTo (c : Int64) (s : MachineData) :
    Directive.FallsTo (x64AddSpD c) s
      (fun s' => s'.regs = s.regs.set64 .rsp (s.regs.get64 .rsp + c.toBitVec) ∧
        s'.zmms = s.zmms ∧ s'.dmem = s.dmem) := by
  intro _ p next jmp P hk
  dsimp only [x64AddSpD]; simp only [t_step_simp, BitVec.add_comm]
  exact hk _ ⟨rfl, rfl, rfl⟩

private theorem x64MoviD_fallsTo (rd : Reg64) (c : BitVec 64) (s : MachineData) :
    Directive.FallsTo (x64MoviD rd c) s
      (fun s' => s' = { s with regs := s.regs.set64 rd c }) := by
  intro _ p next jmp P hk
  dsimp only [x64MoviD]; simp only [t_step_simp, Int64.toBitVec_ofBitVec, BitVec.truncate]
  rw [BitVec.setWidth_eq]
  exact hk _ rfl

private theorem x64SubSpR10_fallsTo (s : MachineData) :
    Directive.FallsTo (ins (.sub (.reg (q .rsp)) (.reg (q .r10)))) s
      (fun s' => s'.regs = s.regs.set64 .rsp (s.regs.get64 .rsp - s.regs.get64 .r10) ∧
        s'.zmms = s.zmms ∧ s'.dmem = s.dmem) := by
  intro _ p next jmp P hk
  simp only [t_step_simp]
  exact hk _ ⟨rfl, rfl, rfl⟩

private theorem x64AddSpR10_fallsTo (s : MachineData) :
    Directive.FallsTo (ins (.add (.reg (q .rsp)) (.reg (q .r10)))) s
      (fun s' => s'.regs = s.regs.set64 .rsp (s.regs.get64 .rsp + s.regs.get64 .r10) ∧
        s'.zmms = s.zmms ∧ s'.dmem = s.dmem) := by
  intro _ p next jmp P hk
  simp only [t_step_simp]
  exact hk _ ⟨by rw [BitVec.add_comm], rfl, rfl⟩

private theorem x64StAddr_fallsTo (r : Reg64) (addr : AddrExpr) (a : BitVec 64)
    {R : Mem 64 → Prop} (s : MachineData)
    (haddr : ∀ [Labels] (p : Std.Rco Int64),
      (@AddrExpr.interp _ ⟨.W64⟩ addr s.regs p).zeroExtend 64 = a)
    (hmem : (region a 8 ⋆ R) s.dmem) :
    Directive.FallsTo (ins (.mov (.mem addr) (.reg (q r)))) s
      (fun s' => s'.regs = s.regs ∧ s'.zmms = s.zmms ∧ s'.status = s.status ∧
        (cell64 a (s.regs.get64 r) ⋆ R) s'.dmem) := by
  obtain ⟨bs, hl, hbs⟩ := region_sep_elim hmem
  intro _ p next jmp P hk
  simp only [t_step_simp, haddr p]
  rw [store_All_of_sep _ _ .W64 _ _ _ bs R hbs hl]
  exact hk _ ⟨rfl, rfl, rfl, Mem.storeInt_sep _ 8 bs R s.dmem ⟨hbs, hl⟩ (s.regs.get64 r).toInt⟩

private theorem x64LdAddr_fallsTo (rd : Reg64) (addr : AddrExpr) (a v : BitVec 64)
    {R : Mem 64 → Prop} (s : MachineData)
    (haddr : ∀ [Labels] (p : Std.Rco Int64),
      (@AddrExpr.interp _ ⟨.W64⟩ addr s.regs p).zeroExtend 64 = a)
    (hmem : (cell64 a v ⋆ R) s.dmem) :
    Directive.FallsTo (ins (.mov (.reg (q rd)) (.mem addr))) s
      (fun s' => s' = { s with regs := s.regs.set64 rd v }) := by
  intro _ p next jmp P hk
  simp only [t_step_simp, haddr p]
  rw [load_All_of_sep _ _ .W64 _ _ (Int.toBytes 8 v.toInt) R hmem (Int.toBytes_length _ _)]
  have hv : BitVec.ofInt 64 (Int.ofBytes (Int.toBytes 8 v.toInt)) = v :=
    BitVec.ofInt_ofBytes_toBytes 64 8 rfl v
  simp only [hv]
  exact hk _ rfl

/-! ## 3. `FrameTarget` snippet specifications -/

private theorem x64Prologue_spec {h : Host} {k ns : Nat} {s : MachineData} {ra : Int64}
    {G : Mem 64 → Prop} {post : MachineState → Prop}
    (hF : x64FrameSize ns + 8 ≤ 2 ^ 64)
    (hmem : s.dmem =⋆ cell64 (s.regs.get64 .rsp) ra.toBitVec ⋆
      region (s.regs.get64 .rsp - BitVec.ofNat 64 (x64FrameSize ns)) (x64FrameSize ns) ⋆ G) :
    x64Mach.FallsTo x64CondReads h k (x64Prologue ns).1 [.rsp, .r10, .r11] []
      (x64Prologue ns).2 s
      (fun s' => s'.regs.get64 .rsp = s.regs.get64 .rsp - BitVec.ofNat 64 (x64FrameSize ns) ∧
        (s'.dmem =⋆
          (region (s.regs.get64 .rsp - BitVec.ofNat 64 (x64FrameSize ns) +
              BitVec.ofNat 64 (8 * ns)) (x64FrameSize ns - 8 * ns) ⋆
            cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆
          region (s.regs.get64 .rsp - BitVec.ofNat 64 (x64FrameSize ns)) (8 * ns) ⋆ G)) post := by
  letI := h
  have hle : 8 * ns ≤ x64FrameSize ns := x64FrameSize_ge ns
  have hsplit : region (s.regs.get64 .rsp - BitVec.ofNat 64 (x64FrameSize ns)) (x64FrameSize ns) =
      (region (s.regs.get64 .rsp - BitVec.ofNat 64 (x64FrameSize ns)) (8 * ns) ⋆
        region (s.regs.get64 .rsp - BitVec.ofNat 64 (x64FrameSize ns) +
          BitVec.ofNat 64 (8 * ns)) (x64FrameSize ns - 8 * ns)) :=
    region_frame_split hle (by omega)
  have hmem' : (s.dmem =⋆
      (region (s.regs.get64 .rsp - BitVec.ofNat 64 (x64FrameSize ns) +
          BitVec.ofNat 64 (8 * ns)) (x64FrameSize ns - 8 * ns) ⋆
        cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆
      region (s.regs.get64 .rsp - BitVec.ofNat 64 (x64FrameSize ns)) (8 * ns) ⋆ G) := by
    rw [hsplit] at hmem
    exact sep_cast hmem (by ac_rfl)
  apply fallsTo_of_wp
  dsimp only [x64Prologue, x64PrologueIns]
  simp only [emitClean_ite]
  split
  · refine Program.wp.mono (Directive.FallsTo.wp (x64SubSpD_fallsTo (Int64.ofNat (x64FrameSize ns)) s)) ?_
    rintro s' ⟨hregs, hzmms, hdmem⟩
    have hrsp : s'.regs.get64 .rsp = s.regs.get64 .rsp - BitVec.ofNat 64 (x64FrameSize ns) := by
      rw [hregs, Reg64s.get64_set64_same]; rfl
    refine ⟨⟨hrsp, hdmem ▸ hmem'⟩, frame_upd_regs (fun r hr => ?_) hzmms (Or.inl rfl)⟩
    have hne : .rsp ≠ r := fun e => hr (e ▸ List.mem_cons_self)
    rw [hregs, Reg64s.get64_set64_of_ne _ _ _ _ hne]
  · refine Program.wp.cons
      (Directive.FallsTo.wp (x64MoviD_fallsTo .r10 (BitVec.ofNat 64 (x64FrameSize ns)) s)) ?_
    rintro s₁ rfl
    refine Program.wp.mono
      (Directive.FallsTo.wp (x64SubSpR10_fallsTo { s with regs := s.regs.set64 .r10 _ })) ?_
    rintro s' ⟨hregs, hzmms, hdmem⟩
    have hrsp1 : (s.regs.set64 .r10 (BitVec.ofNat 64 (x64FrameSize ns))).get64 .rsp =
        s.regs.get64 .rsp := Reg64s.get64_set64_of_ne _ _ _ _ (by decide)
    have hr10 : (s.regs.set64 .r10 (BitVec.ofNat 64 (x64FrameSize ns))).get64 .r10 =
        BitVec.ofNat 64 (x64FrameSize ns) := Reg64s.get64_set64_same _ _ _
    have hrsp : s'.regs.get64 .rsp = s.regs.get64 .rsp - BitVec.ofNat 64 (x64FrameSize ns) := by
      rw [hregs, Reg64s.get64_set64_same, hrsp1, hr10]
    refine ⟨⟨hrsp, hdmem ▸ hmem'⟩, frame_upd_regs (fun r hr => ?_) hzmms (Or.inl rfl)⟩
    have hne1 : .rsp ≠ r := fun e => hr (by simp [e])
    have hne2 : .r10 ≠ r := fun e => hr (by simp [e])
    rw [hregs, Reg64s.get64_set64_of_ne _ _ _ _ hne1, Reg64s.get64_set64_of_ne _ _ _ _ hne2]

private theorem x64Epilogue_spec {h : Host} {k ns : Nat} {s : MachineData} {ra : Int64}
    {G : Mem 64 → Prop} {post : MachineState → Prop}
    (hmem : s.dmem =⋆
      (region (s.regs.get64 .rsp + BitVec.ofNat 64 (x64FrameSize ns) -
          BitVec.ofNat 64 (x64FrameSize ns) + BitVec.ofNat 64 (8 * ns)) (x64FrameSize ns - 8 * ns) ⋆
        cell64 (s.regs.get64 .rsp + BitVec.ofNat 64 (x64FrameSize ns)) ra.toBitVec) ⋆ G) :
    x64Mach.FallsTo x64CondReads h k (x64Epilogue ns).1 [.rsp, .r10, .r11] []
      (x64Epilogue ns).2 s
      (fun s' => s'.regs.get64 .rsp = s.regs.get64 .rsp + BitVec.ofNat 64 (x64FrameSize ns) ∧
        True ∧
        (s'.dmem =⋆ cell64 (s.regs.get64 .rsp + BitVec.ofNat 64 (x64FrameSize ns)) ra.toBitVec ⋆
          region (s.regs.get64 .rsp + BitVec.ofNat 64 (8 * ns)) (x64FrameSize ns - 8 * ns) ⋆ G))
      post := by
  letI := h
  rw [BitVec.add_sub_cancel] at hmem
  have hmem' : (s.dmem =⋆ cell64 (s.regs.get64 .rsp + BitVec.ofNat 64 (x64FrameSize ns)) ra.toBitVec ⋆
      region (s.regs.get64 .rsp + BitVec.ofNat 64 (8 * ns)) (x64FrameSize ns - 8 * ns) ⋆ G) :=
    sep_cast hmem (by ac_rfl)
  apply fallsTo_of_wp
  dsimp only [x64Epilogue, x64EpilogueIns]
  simp only [emitClean_ite]
  split
  · refine Program.wp.mono (Directive.FallsTo.wp (x64AddSpD_fallsTo (Int64.ofNat (x64FrameSize ns)) s)) ?_
    rintro s' ⟨hregs, hzmms, hdmem⟩
    have hrsp : s'.regs.get64 .rsp = s.regs.get64 .rsp + BitVec.ofNat 64 (x64FrameSize ns) := by
      rw [hregs, Reg64s.get64_set64_same]; rfl
    refine ⟨⟨hrsp, trivial, hdmem ▸ hmem'⟩, frame_upd_regs (fun r hr => ?_) hzmms (Or.inl rfl)⟩
    have hne : .rsp ≠ r := fun e => hr (e ▸ List.mem_cons_self)
    rw [hregs, Reg64s.get64_set64_of_ne _ _ _ _ hne]
  · refine Program.wp.cons
      (Directive.FallsTo.wp (x64MoviD_fallsTo .r10 (BitVec.ofNat 64 (x64FrameSize ns)) s)) ?_
    rintro s₁ rfl
    refine Program.wp.mono
      (Directive.FallsTo.wp (x64AddSpR10_fallsTo { s with regs := s.regs.set64 .r10 _ })) ?_
    rintro s' ⟨hregs, hzmms, hdmem⟩
    have hrsp1 : (s.regs.set64 .r10 (BitVec.ofNat 64 (x64FrameSize ns))).get64 .rsp =
        s.regs.get64 .rsp := Reg64s.get64_set64_of_ne _ _ _ _ (by decide)
    have hr10 : (s.regs.set64 .r10 (BitVec.ofNat 64 (x64FrameSize ns))).get64 .r10 =
        BitVec.ofNat 64 (x64FrameSize ns) := Reg64s.get64_set64_same _ _ _
    have hrsp : s'.regs.get64 .rsp = s.regs.get64 .rsp + BitVec.ofNat 64 (x64FrameSize ns) := by
      rw [hregs, Reg64s.get64_set64_same, hrsp1, hr10]
    refine ⟨⟨hrsp, trivial, hdmem ▸ hmem'⟩, frame_upd_regs (fun r hr => ?_) hzmms (Or.inl rfl)⟩
    have hne1 : .rsp ≠ r := fun e => hr (by simp [e])
    have hne2 : .r10 ≠ r := fun e => hr (by simp [e])
    rw [hregs, Reg64s.get64_set64_of_ne _ _ _ _ hne1, Reg64s.get64_set64_of_ne _ _ _ _ hne2]

private theorem x64SlotSt_spec {h : Host} {k i : Nat} {r : Reg64} {s : MachineData}
    {G : Mem 64 → Prop} {post : MachineState → Prop}
    (hr : r ∉ x64Scratch)
    (hmem : s.dmem =⋆ region (s.regs.get64 .rsp + BitVec.ofNat 64 (8 * i)) 8 ⋆ G) :
    x64Mach.FallsTo x64CondReads h k (x64SlotSt i r) x64Scratch [] maskNone s
      (fun s' => s'.dmem =⋆
        cell64 (s.regs.get64 .rsp + BitVec.ofNat 64 (8 * i)) (s.regs.get64 r) ⋆ G) post := by
  letI := h
  have ⟨hr10, _⟩ := ne_of_not_mem_x64Scratch hr
  apply fallsTo_of_wp
  dsimp only [x64SlotSt, x64SlotStIns]
  simp only [emitClean_ite]
  split
  · refine Program.wp.mono
      (Directive.FallsTo.wp (x64StAddr_fallsTo r (x64AtSp (Int64.ofNat (8 * i)))
        (s.regs.get64 .rsp + BitVec.ofNat 64 (8 * i)) s
        (fun p => by rw [x64AtSp_interp, Int64_toBitVec_ofNat]) hmem)) ?_
    rintro s' ⟨hregs, hzmms, hst, hdmem⟩
    exact ⟨hdmem, frame_upd_regs (fun x _ => by rw [hregs]) hzmms (Or.inr hst)⟩
  · refine Program.wp.cons
      (Directive.FallsTo.wp (x64MoviD_fallsTo .r10 (BitVec.ofNat 64 (8 * i)) s)) ?_
    rintro s₁ rfl
    have hrsp1 : (s.regs.set64 .r10 (BitVec.ofNat 64 (8 * i))).get64 .rsp = s.regs.get64 .rsp :=
      Reg64s.get64_set64_of_ne _ _ _ _ (by decide)
    have hr10_val : (s.regs.set64 .r10 (BitVec.ofNat 64 (8 * i))).get64 .r10 = BitVec.ofNat 64 (8 * i) :=
      Reg64s.get64_set64_same _ _ _
    have hr_val : (s.regs.set64 .r10 (BitVec.ofNat 64 (8 * i))).get64 r = s.regs.get64 r :=
      Reg64s.get64_set64_of_ne _ _ _ _ hr10.symm
    refine Program.wp.mono
      (Directive.FallsTo.wp (x64StAddr_fallsTo r x64AtSpR10
        (s.regs.get64 .rsp + BitVec.ofNat 64 (8 * i))
        { s with regs := s.regs.set64 .r10 (BitVec.ofNat 64 (8 * i)) }
        (fun p => by rw [x64AtSpR10_interp, hrsp1, hr10_val]) hmem)) ?_
    rintro s' ⟨hregs, hzmms, hst, hdmem⟩
    rw [hr_val] at hdmem
    refine ⟨hdmem, frame_upd_regs (fun x hx => ?_) hzmms (Or.inr hst)⟩
    have hne : .r10 ≠ x := fun e => hx (by simp [e, x64Scratch])
    rw [hregs, Reg64s.get64_set64_of_ne _ _ _ _ hne]

private theorem x64SlotLd_spec {h : Host} {k i : Nat} {rd : Reg64} {v : BitVec 64} {s : MachineData}
    {G : Mem 64 → Prop} {post : MachineState → Prop}
    (hrd : rd ∉ x64Scratch)
    (hmem : s.dmem =⋆ cell64 (s.regs.get64 .rsp + BitVec.ofNat 64 (8 * i)) v ⋆ G) :
    x64Mach.FallsTo x64CondReads h k (x64SlotLd rd i) (rd :: x64Scratch) [] maskNone s
      (fun s' => s'.regs.get64 rd = v ∧ s'.dmem = s.dmem) post := by
  letI := h
  have ⟨hrd10, _⟩ := ne_of_not_mem_x64Scratch hrd
  apply fallsTo_of_wp
  dsimp only [x64SlotLd, x64SlotLdIns]
  simp only [emitClean_ite]
  split
  · refine Program.wp.mono
      (Directive.FallsTo.wp (x64LdAddr_fallsTo rd (x64AtSp (Int64.ofNat (8 * i)))
        (s.regs.get64 .rsp + BitVec.ofNat 64 (8 * i)) v s
        (fun p => by rw [x64AtSp_interp, Int64_toBitVec_ofNat]) hmem)) ?_
    rintro s' rfl
    refine ⟨⟨Reg64s.get64_set64_same _ _ _, rfl⟩, frame_upd_regs (fun x hx => ?_) rfl (Or.inr rfl)⟩
    have hne : rd ≠ x := fun e => hx (e ▸ List.mem_cons_self)
    exact Reg64s.get64_set64_of_ne _ _ _ _ hne
  · refine Program.wp.cons
      (Directive.FallsTo.wp (x64MoviD_fallsTo .r10 (BitVec.ofNat 64 (8 * i)) s)) ?_
    rintro s₁ rfl
    have hrsp1 : (s.regs.set64 .r10 (BitVec.ofNat 64 (8 * i))).get64 .rsp = s.regs.get64 .rsp :=
      Reg64s.get64_set64_of_ne _ _ _ _ (by decide)
    have hr10_val : (s.regs.set64 .r10 (BitVec.ofNat 64 (8 * i))).get64 .r10 = BitVec.ofNat 64 (8 * i) :=
      Reg64s.get64_set64_same _ _ _
    refine Program.wp.mono
      (Directive.FallsTo.wp (x64LdAddr_fallsTo rd x64AtSpR10
        (s.regs.get64 .rsp + BitVec.ofNat 64 (8 * i)) v
        { s with regs := s.regs.set64 .r10 (BitVec.ofNat 64 (8 * i)) }
        (fun p => by rw [x64AtSpR10_interp, hrsp1, hr10_val]) hmem)) ?_
    rintro s' rfl
    refine ⟨⟨Reg64s.get64_set64_same _ _ _, rfl⟩, frame_upd_regs (fun x hx => ?_) rfl (Or.inr rfl)⟩
    have hne1 : rd ≠ x := fun e => hx (by simp [e])
    have hne2 : .r10 ≠ x := fun e => hx (by simp [e, x64Scratch])
    rw [Reg64s.get64_set64_of_ne _ _ _ _ hne1, Reg64s.get64_set64_of_ne _ _ _ _ hne2]

private theorem x64Canon8_fallsTo (r : Reg64) (s : MachineData) :
    Directive.FallsTo (ins32 (.movzx (.reg (d r)) (.reg (b8 r)))) s
      (fun s' => s' = { s with regs := s.regs.set64 r (((s.regs.get64 r).setWidth 8).setWidth 64) }) := by
  intro _ p next jmp P hk
  simp only [t_step_simp, BitVec.zeroExtend]
  have e : (((s.regs.get64 r).setWidth 8).setWidth 32).setWidth 64 =
      ((s.regs.get64 r).setWidth 8).setWidth 64 := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp [show (i : Nat) < 64 from hi]
  rw [e]
  exact hk _ rfl

private theorem x64Canon16_fallsTo (r : Reg64) (s : MachineData) :
    Directive.FallsTo (ins32 (.movzx (.reg (d r)) (.reg (h16 r)))) s
      (fun s' => s' = { s with regs := s.regs.set64 r (((s.regs.get64 r).setWidth 16).setWidth 64) }) := by
  intro _ p next jmp P hk
  simp only [t_step_simp, BitVec.zeroExtend]
  have e : (((s.regs.get64 r).setWidth 16).setWidth 32).setWidth 64 =
      ((s.regs.get64 r).setWidth 16).setWidth 64 := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp [show (i : Nat) < 64 from hi]
  rw [e]
  exact hk _ rfl

private theorem x64Canon32_fallsTo (r : Reg64) (s : MachineData) :
    Directive.FallsTo (ins32 (.mov (.reg (d r)) (.reg (d r)))) s
      (fun s' => s' = { s with regs := s.regs.set64 r (((s.regs.get64 r).setWidth 32).setWidth 64) }) := by
  intro _ p next jmp P hk
  simp only [t_step_simp, BitVec.zeroExtend]
  exact hk _ rfl

private theorem x64CanonAbi_spec {h : Host} {k : Nat} {t : Ty} {r : Reg64} {v : Val t}
    {s : MachineData} {post : MachineState → Prop}
    (ht : t = .bool ∨ ∃ n ∈ [8, 16, 32, 64], t = .bits n)
    (hh : GprHolds (s.regs.get64 r) t v) :
    x64Mach.FallsTo x64CondReads h k (x64CanonAbi t r).1 (r :: x64Scratch) []
      (x64CanonAbi t r).2 s
      (fun s' => AbiGprHolds (s'.regs.get64 r) t v ∧ s'.dmem = s.dmem) post := by
  letI := h
  have hsingle : ∀ (dir : Directive) (n : Nat)
      (hd : Directive.FallsTo dir s
        (fun s' => s' = { s with regs := s.regs.set64 r (((s.regs.get64 r).setWidth n).setWidth 64) }))
      (hAbi : AbiGprHolds (((s.regs.get64 r).setWidth n).setWidth 64) t v),
      x64Mach.FallsTo x64CondReads h k [dir] (r :: x64Scratch) [] maskNone s
        (fun s' => AbiGprHolds (s'.regs.get64 r) t v ∧ s'.dmem = s.dmem) post := by
    intro dir n hd hAbi
    refine fallsTo_of_wp (Program.wp.mono (Directive.FallsTo.wp hd) ?_)
    rintro s' rfl
    refine ⟨⟨by simpa [Reg64s.get64_set64_same] using hAbi, rfl⟩,
      frame_upd_regs (fun x hx => ?_) rfl (Or.inr rfl)⟩
    have hne : r ≠ x := fun e => hx (e ▸ List.mem_cons_self)
    exact Reg64s.get64_set64_of_ne _ _ _ _ hne
  rcases ht with rfl | ⟨n, hn, rfl⟩
  · exact hsingle _ 8 (x64Canon8_fallsTo r s) (abiGprHolds_bool_of_gprHolds hh)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl | rfl | rfl
    · exact hsingle _ 8 (x64Canon8_fallsTo r s) (abiGprHolds_bits_of_gprHolds hh)
    · exact hsingle _ 16 (x64Canon16_fallsTo r s) (abiGprHolds_bits_of_gprHolds hh)
    · exact hsingle _ 32 (x64Canon32_fallsTo r s) (abiGprHolds_bits_of_gprHolds hh)
    · exact Machine.FallsTo.nil ⟨abiGprHolds_bits64_of_gprHolds hh, rfl⟩

private theorem x64Call_spec {h : Host} {k : Nat} {sym : Sym} {s : MachineData}
    {G : Mem 64 → Prop} {post : MachineState → Prop}
    (hc : [x64CallD sym].IsInfixAt Host.prog k)
    (hmem : s.dmem =⋆ region (s.regs.get64 .rsp - 8#64) 8 ⋆ G)
    (hk : ∀ s' : MachineData,
      s'.regs.get64 .rsp = s.regs.get64 .rsp - 8#64 →
      x64Mach.Frame x64CondReads s s' (.rsp :: [] ++ x64Scratch) [] maskAll →
      True →
      (s'.dmem =⋆ cell64 (s'.regs.get64 .rsp) (Host.addrOf (k + 1)).toBitVec ⋆ G) →
      Eventually (step1 Host.exe) post ⟨s', hostLabel h sym⟩) :
    x64Mach.Run h k s post := by
  letI := h
  obtain ⟨bs, hl, hbs⟩ := region_sep_elim hmem
  refine Host.eventually_of_interp_cps (List.isInfixAt_singleton.mp hc) ?_
  dsimp only [x64CallD]; simp only [t_step_simp, Width.bytesv, Width.bytes, Width.bits]
  rw [store_All_of_sep { s with regs := s.regs.set64 .rsp (s.regs.get64 .rsp - 8#64) } _
    .W64 _ _ _ bs G hbs hl]
  have hrsp : ({ s with regs := s.regs.set64 .rsp (s.regs.get64 .rsp - 8#64) }).regs.get64 .rsp =
      s.regs.get64 .rsp - 8#64 := Reg64s.get64_set64_same s.regs .rsp _
  have hfr : x64Mach.Frame x64CondReads s
      { s with regs := s.regs.set64 .rsp (s.regs.get64 .rsp - 8#64),
               dmem := Mem.storeInt s.dmem (s.regs.get64 .rsp - 8#64) 8
                 (Host.addrOf (k + 1)).toBitVec.toInt }
      (.rsp :: [] ++ x64Scratch) [] maskAll := by
    refine frame_upd_regs (fun r hr => ?_) rfl (Or.inl rfl)
    have hne : .rsp ≠ r := fun e => hr (e ▸ List.mem_cons_self)
    exact Reg64s.get64_set64_of_ne _ _ _ _ hne
  have hm' : ((Mem.storeInt s.dmem (s.regs.get64 .rsp - 8#64) 8
      (Host.addrOf (k + 1)).toBitVec.toInt) =⋆
      cell64 (s.regs.get64 .rsp - 8#64) (Host.addrOf (k + 1)).toBitVec ⋆ G) :=
    Mem.storeInt_sep _ 8 bs G s.dmem ⟨hbs, hl⟩ _
  dsimp only [Effects.All, Width.bytes]
  rw [Int64.ofBitVec_toBitVec, Int64.add_comm, Int64.sub_add_cancel]
  refine hk _ hrsp hfr trivial ?_
  rw [hrsp]
  exact hm'

private theorem x64ExitJmp_spec {h : Host} {k : Nat} {sym : Sym} {s : MachineData}
    {post : MachineState → Prop}
    (hc : [x64JmpD sym].IsInfixAt Host.prog k)
    (hk : ∀ s' : MachineData,
      x64Mach.Frame x64CondReads s s' x64Scratch [] maskNone → s'.dmem = s.dmem →
      Eventually (step1 Host.exe) post ⟨s', hostLabel h sym⟩) :
    x64Mach.Run h k s post := by
  letI := h
  refine Host.eventually_of_interp_cps (List.isInfixAt_singleton.mp hc) ?_
  dsimp only [x64JmpD]; simp only [t_step_simp, RelRegOrMem.interp]
  rw [Int64.ofBitVec_toBitVec, Int64.add_comm, Int64.sub_add_cancel]
  exact hk s (Machine.Frame.refl (M := x64Mach) x64CondReads s x64Scratch [] maskNone) rfl

private theorem x64Ret_spec {h : Host} {k : Nat} {s : MachineData} {ra : Int64}
    {R : Mem 64 → Prop} {post : MachineState → Prop}
    (hc : [x64RetD].IsInfixAt Host.prog k)
    (hmem : s.dmem =⋆ cell64 (s.regs.get64 .rsp) ra.toBitVec ⋆ R)
    (hk : ∀ s' : MachineData,
      x64Mach.KeepsGpr s s' (.rsp :: x64Scratch) →
      x64Mach.KeepsVec s s' [] →
      s'.regs.get64 .rsp = s.regs.get64 .rsp + 8#64 →
      s'.dmem = s.dmem →
      Eventually (step1 Host.exe) post ⟨s', ra⟩) :
    x64Mach.Run h k s post := by
  letI := h
  refine Host.eventually_of_interp_cps (List.isInfixAt_singleton.mp hc) ?_
  dsimp only [x64RetD]; simp only [t_step_simp]
  rw [load_All_of_sep _ _ .W64 _ _ (Int.toBytes 8 ra.toBitVec.toInt) R hmem
    (Int.toBytes_length _ _)]
  have hra : BitVec.ofInt 64 (Int.ofBytes (Int.toBytes 8 ra.toBitVec.toInt)) = ra.toBitVec :=
    BitVec.ofInt_ofBytes_toBytes 64 8 rfl ra.toBitVec
  simp only [hra, Int64.ofBitVec_toBitVec]
  refine hk _ (fun r hr => ?_) (fun _ _ => rfl) (by simp) rfl
  have hne : .rsp ≠ r := fun e => hr (e ▸ List.mem_cons_self)
  exact Reg64s.get64_set64_of_ne _ _ _ _ hne

/-! ## 4. `x64FrameSpec : FrameTarget x64Mach x64Frame x64CondReads` -/

theorem x64FrameSpec_spec :
    FrameSpec x64Mach x64Frame x64CondReads x64FramePreds where
  sp_disj := by simp
  scratch_disj := by simp
  cs_disj := by simp
  ra_disj := by simp
  argRegs_nodup := by decide
  retRegs_nodup := by decide
  retAddr_region _ _ _ h := cell64_region h
  raReg_of_raRegs _ _ _ _ _ := trivial
  slots_le_frameSize := x64FrameSize_ge
  spOk_frame _ _ _ := trivial
  spEntry_call sp ns h := aligned16_add8_sub_call h (x64FrameSize_mod ns)
  labelAddr_eq {h} {_} {_} hk hfirst := letI := h; Host.label_eq_addrOf hk hfirst
  label_spec {h} {_} {_} {_} {_} hi hrun := letI := h; Host.eventually_label hi hrun
  prologue_spec {h} {_} {_} {_} {_} {_} {_} _ _ hF hmem :=
    letI := h; x64Prologue_spec hF hmem
  epilogue_spec {h} {_} {_} {_} {_} {_} {_} _ _ hmem :=
    letI := h; x64Epilogue_spec hmem
  slotSt_spec {h} {_} {_} {_} {_} {_} {_} hr _ hmem :=
    letI := h; x64SlotSt_spec hr hmem
  slotLd_spec {h} {_} {_} {_} {_} {_} {_} {_} hrd _ hmem :=
    letI := h; x64SlotLd_spec hrd hmem
  canonAbi_spec {h} {_} {_} {_} {_} {_} {_} ht _ hh :=
    letI := h; x64CanonAbi_spec ht hh
  call_spec {h} {_} {_} {_} {_} {_} hc hmem hk :=
    letI := h; x64Call_spec hc hmem hk
  exitJmp_spec {h} {_} {_} {_} {_} hc hk :=
    letI := h; x64ExitJmp_spec hc hk
  ret_spec {h} {_} {_} {_} {_} {_} hc _ hmem hk :=
    letI := h; x64Ret_spec hc hmem hk
  leafZeroFrame_ok _ := rfl

@[expose] def x64FrameSpec : FrameTarget x64Mach x64Frame x64CondReads where
  toFramePreds := x64FramePreds
  spec := x64FrameSpec_spec

/-! ## 5. `NoLab` lemmas -/

section NoLab

theorem x64Prologue_noLab (ns : Nat) (l : Sym) :
    Kraken.Directive.label l ∉ (x64Frame.prologue ns).1 :=
  emitClean_noLab _ l

theorem x64Epilogue_noLab (ns : Nat) (l : Sym) :
    Kraken.Directive.label l ∉ (x64Frame.epilogue ns).1 :=
  emitClean_noLab _ l

theorem x64SlotSt_noLab (i : Nat) (r : Reg64) (l : Sym) :
    Kraken.Directive.label l ∉ x64Frame.slotSt i r :=
  emitClean_noLab _ l

theorem x64SlotLd_noLab (rd : Reg64) (i : Nat) (l : Sym) :
    Kraken.Directive.label l ∉ x64Frame.slotLd rd i :=
  emitClean_noLab _ l

theorem x64CanonAbi_noLab (t : Ty) (r : Reg64) (l : Sym) :
    Kraken.Directive.label l ∉ (x64Frame.canonAbi t r).1 :=
  emitClean_noLab _ l

theorem x64Call_noLab (sym : Sym) (l : Sym) :
    Kraken.Directive.label l ∉ x64Frame.call sym :=
  emitClean_noLab _ l

theorem x64ExitJmp_noLab (sym : Sym) (l : Sym) :
    Kraken.Directive.label l ∉ x64Frame.exitJmp sym :=
  emitClean_noLab _ l

theorem x64Ret_noLab (l : Sym) :
    Kraken.Directive.label l ∉ x64Frame.ret :=
  emitClean_noLab _ l

end NoLab

/-! ## 6. `ParserChecks` (`Kraken.X64.Parser`) -/

section ParserChecks
open Kraken.X64.Parser

example : ⸨prog| subq $8, %rsp ⸩ = (x64Frame.prologue 0).1 := rfl
example : ⸨prog| addq $8, %rsp ⸩ = (x64Frame.epilogue 0).1 := rfl
example : ⸨prog| movabs $4294967304, %r10; subq %r10, %rsp ⸩ =
    (x64Frame.prologue (2 ^ 29)).1 := rfl
example : ⸨prog| movabs $4294967304, %r10; addq %r10, %rsp ⸩ =
    (x64Frame.epilogue (2 ^ 29)).1 := rfl
example : ⸨prog| movq %rax, 8(%rsp) ⸩ = x64Frame.slotSt 1 .rax := rfl
example : ⸨prog| movq 8(%rsp), %rax ⸩ = x64Frame.slotLd .rax 1 := rfl
example : ⸨prog| movabs $4294967296, %r10; movq %rax, (%rsp, %r10, 1) ⸩ =
    x64Frame.slotSt (2 ^ 29) .rax := rfl
example : ⸨prog| movabs $4294967296, %r10; movq (%rsp, %r10, 1), %rax ⸩ =
    x64Frame.slotLd .rax (2 ^ 29) := rfl
example : ⸨prog| movzbl %dil, %edi ⸩ = (x64Frame.canonAbi .bool .rdi).1 := rfl
example : ⸨prog| movzbl %dil, %edi ⸩ = (x64Frame.canonAbi i8 .rdi).1 := rfl
example : ⸨prog| movzwl %di, %edi ⸩ = (x64Frame.canonAbi i16 .rdi).1 := rfl
example : ⸨prog| movl %edi, %edi ⸩ = (x64Frame.canonAbi i32 .rdi).1 := rfl
example : ⸨prog| call f ⸩ = x64Frame.call "f" := rfl
example : ⸨prog| jmp f ⸩ = x64Frame.exitJmp "f" := rfl
example : ⸨prog| ret ⸩ = x64Frame.ret := rfl

end ParserChecks

end LeanQbe.T.Amd64
