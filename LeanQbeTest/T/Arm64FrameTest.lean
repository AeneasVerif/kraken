module

public import LeanQbe.T.Arm64.FrameLemmas
import Kraken.AArch64.Parser

/-!
# AAPCS64 Arm64 Frame & ABI Verification Tests

Standalone downstream module verifying:
1. Kernel `rfl` reduction of `armFrame` (`bitWidths`, `raBytes`, registers, `frameSize` at
   small/`4096`/`32768` boundaries, and directive generation vs `Kraken.AArch64.Parser`).
2. Generic `armFrameSpec : FrameTarget armMach armFrame armCondReads` round-trip over arbitrary
   `ns ≥ 1` (`armFrameSize ns ≤ 2 ^ 64`): prologue → slot store → slot load → `canonAbi` →
   epilogue → return, preserving `calleeSaved`, restoring `sp` and `x30`, establishing
   `AbiGprHolds`, and transitioning `Entry` → `Exit`.
3. Dedicated `.SP` slot and ABI canonicalization checks (`slotSt i .SP`, `slotLd .SP i`,
   `canonAbi i8 .SP`).
4. Concrete `Host.ofLayout` caller → `bl "callee"` → callee → `ret` → caller `ret` composition.
5. `NoLab` invariance and standard-axiom audit `[propext, Classical.choice, Quot.sound]`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbeTest.T.Arm64FrameTest

open LeanQbe.T
open LeanQbe.T.Arm64
open Kraken.AArch64.Parser
open Std Std.ExtHashMap

/-! ## 1. Kernel `rfl` metadata and parser checks -/

theorem armFrame_metadata_rfl :
    armFrame.sp = .SP ∧
    armFrame.raBytes = 0 ∧
    armFrame.bitWidths = [8, 16, 32, 64] ∧
    armFrame.raRegs = [.reg .X30] ∧
    armFrame.argRegs = [.reg .X0, .reg .X1, .reg .X2, .reg .X3, .reg .X4, .reg .X5, .reg .X6, .reg .X7] ∧
    armFrame.retRegs = [.reg .X0, .reg .X1, .reg .X2, .reg .X3, .reg .X4, .reg .X5, .reg .X6, .reg .X7] := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem armFrameSize_rfl :
    armFrame.frameSize 0 = 16 ∧
    armFrame.frameSize 1 = 16 ∧
    armFrame.frameSize 2 = 32 ∧
    armFrame.frameSize 510 = 4096 ∧
    armFrame.frameSize 4096 = 32784 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem armFrame_parser_rfl :
    ⸨prog|
      sub sp, sp, #16
      str x30, [sp, #8]
      str x0, [sp, #0]
      ldr x0, [sp, #0]
      uxth x0, w0
      ldr x30, [sp, #8]
      add sp, sp, #16
      ret
    ⸩ =
      (armFrame.prologue 1).1 ++ armFrame.slotSt 0 (.reg .X0) ++ armFrame.slotLd (.reg .X0) 0 ++
        (armFrame.canonAbi i16 (.reg .X0)).1 ++ (armFrame.epilogue 1).1 ++ armFrame.ret := rfl

theorem armFrame_large_and_sp_parser_rfl :
    ⸨prog|
      ldr x16, =32784
      sub sp, sp, x16
      ldr x16, =32768
      str x30, [sp, x16]
    ⸩ = (armFrame.prologue 4096).1 ∧
    ⸨prog|
      mov x17, sp
      ldr x16, =32768
      str x17, [sp, x16]
    ⸩ = armFrame.slotSt 4096 .SP ∧
    ⸨prog|
      ldr x16, =32768
      ldr x17, [sp, x16]
      mov sp, x17
    ⸩ = armFrame.slotLd .SP 4096 ∧
    ⸨prog|
      mov x16, sp
      uxtb x16, w16
      mov sp, x16
    ⸩ = (armFrame.canonAbi i8 .SP).1 := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-! ## 2. Generic `armFrameSpec` round-trip over arbitrary `ns ≥ 1` (`armFrameSize ns ≤ 2 ^ 64`) -/

def armEchoProg (ns : Nat) : List Directive :=
  (armFrame.prologue ns).1 ++ armFrame.slotSt 0 (.reg .X0) ++ armFrame.slotLd (.reg .X0) 0 ++
    (armFrame.canonAbi i16 (.reg .X0)).1 ++ (armFrame.epilogue ns).1 ++ armFrame.ret

theorem armEchoProg_noLab (ns : Nat) (l : Sym) :
    Kraken.Directive.label l ∉ armEchoProg ns := by
  simp only [armEchoProg, List.mem_append, not_or]
  exact ⟨⟨⟨⟨⟨armPrologue_noLab ns l, armSlotSt_noLab 0 (.reg .X0) l⟩,
    armSlotLd_noLab (.reg .X0) 0 l⟩, armCanonAbi_noLab i16 (.reg .X0) l⟩,
    armEpilogue_noLab ns l⟩, armRet_noLab l⟩

theorem armEchoProg_spec {h : Host} {k ns : Nat} {v : Val i16} {s : MachineData}
    {ra : Int64} {R : Mem 64 → Prop} {post : MachineState → Prop}
    (hns : 1 ≤ ns)
    (hF : armFrame.frameSize ns + armFrame.raBytes ≤ 2 ^ 64)
    (hc : (armEchoProg ns).IsInfixAt (armMach.prog h) k)
    (hra : armFrameSpec.raReg s ra)
    (hsp : armFrameSpec.spEntry (armMach.getGpr s armFrame.sp))
    (hh : GprHolds (armMach.getGpr s (.reg .X0)) i16 v)
    (hmem : s.dmem =⋆
      armFrameSpec.RetAddr (armMach.getGpr s armFrame.sp) ra ⋆
      region (armMach.getGpr s armFrame.sp - BitVec.ofNat 64 (armFrame.frameSize ns))
        (armFrame.frameSize ns) ⋆ R)
    (hret : ∀ s' : MachineData,
      AbiGprHolds (armMach.getGpr s' (.reg .X0)) i16 v →
      (∀ r ∈ armFrame.calleeSaved, armMach.getGpr s' r = armMach.getGpr s r) →
      armMach.getGpr s' armFrame.sp = armMach.getGpr s armFrame.sp →
      (s'.dmem =⋆
        region (armMach.getGpr s armFrame.sp - BitVec.ofNat 64 (armFrame.frameSize ns))
          (armFrame.frameSize ns + armFrame.raBytes) ⋆ R) →
      Eventually (armMach.step h) post (armMach.mkState s' ra)) :
    armMach.Run h k s post := by
  letI := h
  obtain ⟨hleft, hretAt⟩ := hc.append
  obtain ⟨hleft, hepi⟩ := hleft.append
  obtain ⟨hleft, hcab⟩ := hleft.append
  obtain ⟨hleft, hld⟩ := hleft.append
  obtain ⟨hpro, hst⟩ := hleft.append
  simp only [List.length_append, ← Nat.add_assoc] at hld hcab hepi hretAt
  have hle : 8 ≤ 8 * ns := by omega
  have hF0 : armFrame.frameSize ns ≤ 2 ^ 64 := by
    change armFrameSize ns ≤ 2 ^ 64
    change armFrameSize ns + 0 ≤ 2 ^ 64 at hF
    omega
  refine armFrameSpec.prologue_spec (ra := ra) hra hsp hF hmem hpro ?_
  rintro s1 ⟨hsp1, hmem1⟩ hfr1
  have hsp1_ok : armFrameSpec.spOk (armMach.getGpr s1 armFrame.sp) := by
    rw [hsp1]; exact armFrameSpec.spOk_frame _ ns hsp
  have hsplit1 : region (armMach.getGpr s1 armFrame.sp) (8 * ns) =
      (region (armMach.getGpr s1 armFrame.sp) 8 ⋆
        region (armMach.getGpr s1 armFrame.sp + 8#64) (8 * ns - 8)) := by
    have he : 8 * ns = 8 + (8 * ns - 8) := by omega
    conv => lhs; rw [he]
    exact region_split (by
      have hge := armFrameSize_slots ns
      change armFrameSize ns ≤ 2 ^ 64 at hF0
      omega)
  have hmem1' : (s1.dmem =⋆ region (armMach.getGpr s1 armFrame.sp + BitVec.ofNat 64 (8 * 0)) 8 ⋆
      (region (armMach.getGpr s1 armFrame.sp + 8#64) (8 * ns - 8) ⋆
        armFrameSpec.Saved (armMach.getGpr s armFrame.sp) ra ns ⋆ R)) := by
    rw [← hsp1, hsplit1] at hmem1
    rw [show BitVec.ofNat 64 (8 * 0) = 0#64 from rfl, BitVec.add_zero]
    exact sep_cast hmem1 (by ac_rfl)
  refine armFrameSpec.slotSt_spec (r := .reg .X0) (by simp) hsp1_ok hmem1' hst ?_
  intro s2 hmem2 hfr2
  have hval : armMach.getGpr s1 (.reg .X0) = armMach.getGpr s (.reg .X0) :=
    hfr1.1 (.reg .X0) (by simp)
  have hsp2 : armMach.getGpr s2 armFrame.sp = armMach.getGpr s1 armFrame.sp :=
    hfr2.1 armFrame.sp (by simp)
  have hsp2_ok : armFrameSpec.spOk (armMach.getGpr s2 armFrame.sp) := hsp2 ▸ hsp1_ok
  have hmem2' : (s2.dmem =⋆
      cell64 (armMach.getGpr s2 armFrame.sp + BitVec.ofNat 64 (8 * 0)) (armMach.getGpr s (.reg .X0)) ⋆
      (region (armMach.getGpr s1 armFrame.sp + 8#64) (8 * ns - 8) ⋆
        armFrameSpec.Saved (armMach.getGpr s armFrame.sp) ra ns ⋆ R)) := by
    rw [hsp2, ← hval]; exact hmem2
  refine armFrameSpec.slotLd_spec (rd := .reg .X0) (by simp) hsp2_ok hmem2' hld ?_
  rintro s3 ⟨hx0_3, hdmem3⟩ hfr3
  have hh3 : GprHolds (armMach.getGpr s3 (.reg .X0)) i16 v := hx0_3 ▸ hh
  refine armFrameSpec.canonAbi_spec (Or.inr ⟨16, by decide, rfl⟩) (by simp) hh3 hcab ?_
  rintro s4 ⟨hAbi4, hdmem4⟩ hfr4
  have hsp4 : armMach.getGpr s4 armFrame.sp =
      armMach.getGpr s armFrame.sp - BitVec.ofNat 64 (armFrame.frameSize ns) := by
    rw [hfr4.1 _ (by simp), hfr3.1 _ (by simp), hsp2, hsp1]
  have hsp4_ok : armFrameSpec.spOk (armMach.getGpr s4 armFrame.sp) := by
    rw [hsp4]; exact armFrameSpec.spOk_frame _ ns hsp
  have hmem4 : s4.dmem =⋆
      armFrameSpec.Saved (armMach.getGpr s4 armFrame.sp + BitVec.ofNat 64 (armFrame.frameSize ns)) ra ns ⋆
      (region (armMach.getGpr s armFrame.sp - BitVec.ofNat 64 (armFrame.frameSize ns)) (8 * ns) ⋆ R) := by
    rw [hsp4, BitVec.sub_add_cancel]
    have h42 : s4.dmem = s2.dmem := hdmem4.trans hdmem3
    rw [h42]
    have hreg : (cell64 (armMach.getGpr s2 armFrame.sp + BitVec.ofNat 64 (8 * 0))
        (armMach.getGpr s (.reg .X0)) ⋆
        (region (armMach.getGpr s1 armFrame.sp + 8#64) (8 * ns - 8) ⋆
          armFrameSpec.Saved (armMach.getGpr s armFrame.sp) ra ns ⋆ R)) s2.dmem := hmem2'
    have hreg2 := sep_mono (fun _ => cell64_region) hreg
    rw [hsp2, Nat.mul_zero, BitVec.add_zero] at hreg2
    have hback := sep_cast hreg2 (show
        (region (armMach.getGpr s1 armFrame.sp) 8 ⋆
          (region (armMach.getGpr s1 armFrame.sp + 8#64) (8 * ns - 8) ⋆
            armFrameSpec.Saved (armMach.getGpr s armFrame.sp) ra ns ⋆ R)) =
        (armFrameSpec.Saved (armMach.getGpr s armFrame.sp) ra ns ⋆
          ((region (armMach.getGpr s1 armFrame.sp) 8 ⋆
            region (armMach.getGpr s1 armFrame.sp + 8#64) (8 * ns - 8)) ⋆ R)) from by ac_rfl)
    rw [← hsplit1, hsp1] at hback
    exact hback
  refine armFrameSpec.epilogue_spec hsp4_ok hF hmem4 hepi ?_
  rintro s5 ⟨hsp5, hra5, hmem5⟩ hfr5
  have hsp5' : armMach.getGpr s5 armFrame.sp = armMach.getGpr s armFrame.sp := by
    rw [hsp5, hsp4, BitVec.sub_add_cancel]
  have hmem5' : s5.dmem =⋆
      armFrameSpec.RetAddr (armMach.getGpr s5 armFrame.sp) ra ⋆
      (region (armMach.getGpr s armFrame.sp - BitVec.ofNat 64 (armFrame.frameSize ns))
        (armFrame.frameSize ns) ⋆ R) := by
    rw [hsp4, BitVec.sub_add_cancel] at hmem5
    rw [hsp5']
    have hsplit_frame := region_frame_split
      (a := armMach.getGpr s armFrame.sp - BitVec.ofNat 64 (armFrame.frameSize ns))
      (slots := 8 * ns) (frame := armFrame.frameSize ns) (armFrameSize_slots ns) hF0
    have hcast := sep_cast hmem5 (show
        (armFrameSpec.RetAddr (armMach.getGpr s armFrame.sp) ra ⋆
          region (armMach.getGpr s armFrame.sp - BitVec.ofNat 64 (armFrame.frameSize ns) + BitVec.ofNat 64 (8 * ns))
            (armFrame.frameSize ns - 8 * ns) ⋆
          (region (armMach.getGpr s armFrame.sp - BitVec.ofNat 64 (armFrame.frameSize ns)) (8 * ns) ⋆ R)) =
        (armFrameSpec.RetAddr (armMach.getGpr s armFrame.sp) ra ⋆
          ((region (armMach.getGpr s armFrame.sp - BitVec.ofNat 64 (armFrame.frameSize ns)) (8 * ns) ⋆
            region (armMach.getGpr s armFrame.sp - BitVec.ofNat 64 (armFrame.frameSize ns) + BitVec.ofNat 64 (8 * ns))
              (armFrame.frameSize ns - 8 * ns)) ⋆ R)) from by ac_rfl)
    rw [← hsplit_frame] at hcast
    exact hcast
  refine armFrameSpec.ret_spec hretAt hra5 hmem5' ?_
  rintro s6 hk6 _ hsp6 hdmem6
  have hx0_6 : AbiGprHolds (armMach.getGpr s6 (.reg .X0)) i16 v := by
    have h65 : armMach.getGpr s6 (.reg .X0) = armMach.getGpr s5 (.reg .X0) := hk6 (.reg .X0) (by simp)
    have h54 : armMach.getGpr s5 (.reg .X0) = armMach.getGpr s4 (.reg .X0) := hfr5.1 (.reg .X0) (by simp)
    rw [h65, h54]
    exact hAbi4
  have hcs6 : ∀ r ∈ armFrame.calleeSaved, armMach.getGpr s6 r = armMach.getGpr s r := by
    intro r hr
    have hnot_sp : r ≠ armFrame.sp := fun e => armFrameSpec.sp_disj.2.2.1 (e ▸ hr)
    have hnot_sc : r ∉ armScratch := fun hsc => (armFrameSpec.scratch_disj r hsc).2.1 hr
    have hnot_ra : r ≠ .reg .X30 := by
      have hra' := fun h => (armFrameSpec.ra_disj r h).2.2.1 hr
      simpa using hra'
    have hnot_x0 : r ≠ .reg .X0 := fun e => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> cases e
    rw [hk6 r (by simp [hnot_sp, hnot_sc]),
      hfr5.1 r (by simp [hnot_sp, hnot_sc, hnot_ra]),
      hfr4.1 r (by simp [hnot_x0, hnot_sc]),
      hfr3.1 r (by simp [hnot_x0, hnot_sc]),
      hfr2.1 r (by simp [hnot_sc]),
      hfr1.1 r (by simp [hnot_sp, hnot_sc, hnot_ra])]
  have hsp_out : armMach.getGpr s6 armFrame.sp = armMach.getGpr s armFrame.sp := by
    rw [show armFrame.raBytes = 0 from rfl, BitVec.add_zero] at hsp6
    exact hsp6.trans hsp5'
  have hmem_out : s6.dmem =⋆
      region (armMach.getGpr s armFrame.sp - BitVec.ofNat 64 (armFrame.frameSize ns))
        (armFrame.frameSize ns + armFrame.raBytes) ⋆ R := by
    dsimp only [armMach] at hdmem6
    rw [hdmem6]
    have hm1 := sep_mono (fun _ => armFrameSpec.retAddr_region _ _ _) hmem5'
    have hzero : armFrame.raBytes = 0 := rfl
    rw [hzero] at hm1 ⊢
    rw [region_zero, emp_sep] at hm1
    simpa [Nat.add_zero] using hm1
  exact hret s6 hx0_6 hcs6 hsp_out hmem_out

/-! ## 3. Dedicated `.SP` slot and ABI canonicalization corner-case tests -/

theorem armSpCorner_spec {h : Host} {k i : Nat} {s : MachineData} {v : Val i8}
    {R : Mem 64 → Prop} {post : MachineState → Prop}
    (hc : (armFrame.slotSt i .SP ++ armFrame.slotLd .SP i ++ (armFrame.canonAbi i8 .SP).1).IsInfixAt
      (armMach.prog h) k)
    (hsp : armFrameSpec.spOk (armMach.getGpr s armFrame.sp))
    (hh : GprHolds (armMach.getGpr s .SP) i8 v)
    (hmem : s.dmem =⋆ region (armMach.getGpr s armFrame.sp + BitVec.ofNat 64 (8 * i)) 8 ⋆ R)
    (hk : ∀ s' : MachineData,
      AbiGprHolds (armMach.getGpr s' .SP) i8 v →
      (s'.dmem =⋆ cell64 (armMach.getGpr s armFrame.sp + BitVec.ofNat 64 (8 * i)) (armMach.getGpr s .SP) ⋆ R) →
      Eventually (armMach.step h) post (armMach.mkState s' (armMach.addrOf h
        (k + (armFrame.slotSt i .SP ++ armFrame.slotLd .SP i ++ (armFrame.canonAbi i8 .SP).1).length)))) :
    armMach.Run h k s post := by
  letI := h
  obtain ⟨hleft, hcab⟩ := hc.append
  obtain ⟨hst, hld⟩ := hleft.append
  simp only [List.length_append, ← Nat.add_assoc] at hcab
  refine armFrameSpec.slotSt_spec (r := .SP) (by simp) hsp hmem hst ?_
  intro s1 hmem1 hfr1
  have hsp1 : armMach.getGpr s1 armFrame.sp = armMach.getGpr s armFrame.sp :=
    hfr1.1 .SP (by simp)
  have hsp1_ok : armFrameSpec.spOk (armMach.getGpr s1 armFrame.sp) := hsp1 ▸ hsp
  have hmem1' : s1.dmem =⋆
      cell64 (armMach.getGpr s1 armFrame.sp + BitVec.ofNat 64 (8 * i)) (armMach.getGpr s .SP) ⋆ R := by
    rw [hsp1]; exact hmem1
  refine armFrameSpec.slotLd_spec (rd := .SP) (by simp) hsp1_ok hmem1' hld ?_
  rintro s2 ⟨hsp2, hdmem2⟩ hfr2
  have hh2 : GprHolds (armMach.getGpr s2 .SP) i8 v := hsp2 ▸ hh
  refine armFrameSpec.canonAbi_spec (t := i8) (r := .SP) (Or.inr ⟨8, by decide, rfl⟩)
    (by simp) hh2 hcab ?_
  rintro s3 ⟨hAbi3, hdmem3⟩ _
  dsimp only [armMach] at hdmem2 hdmem3
  simp only [List.length_append, ← Nat.add_assoc] at hk
  exact hk s3 hAbi3 (by rwa [hdmem3, hdmem2])

/-! ## 4. Concrete `Host.ofLayout` caller → `bl "callee"` → callee → `ret` test -/

@[instance_reducible] def testLayout : Layout where
  start := 0x20000
  instrSize _ := 4
  instrSize_pos _ := by decide

def callerCalleeProg : List Directive :=
  [armFrame.label "caller"] ++ (armFrame.prologue 1).1 ++ armFrame.call "callee" ++
    (armFrame.epilogue 1).1 ++ armFrame.ret ++
  [armFrame.label "callee"] ++ armEchoProg 1

theorem callerCallee_small :
    (Kraken.Layout.apply testLayout callerCalleeProg).sizeBefore callerCalleeProg.length < 2 ^ 64 := by
  have : (Kraken.Layout.apply testLayout callerCalleeProg).sizeBefore callerCalleeProg.length = 56 := by
    simp [Kraken.Layout.apply, Kraken.Executable.sizeBefore, Kraken.Layout.size, callerCalleeProg, armEchoProg]
    decide
  omega

@[instance_reducible] def concreteHost : Host :=
  Host.ofLayout callerCalleeProg testLayout callerCallee_small

theorem concreteHost_unique : concreteHost.LabelsUnique :=
  letI := concreteHost
  Host.labelsUnique_of_nodup (by decide)

theorem callerCallee_e2e {v : Val i16} {s : MachineData} {ra : Int64} {R : Mem 64 → Prop}
    (hra : armFrameSpec.raReg s ra)
    (hsp : armFrameSpec.spEntry (armMach.getGpr s armFrame.sp))
    (hh : GprHolds (armMach.getGpr s (.reg .X0)) i16 v)
    (hmem : s.dmem =⋆
      armFrameSpec.RetAddr (armMach.getGpr s armFrame.sp) ra ⋆
      region (armMach.getGpr s armFrame.sp - 32#64) 32 ⋆ R) :
    armMach.Run concreteHost 0 s fun st =>
      st.pc = ra ∧ AbiGprHolds (armMach.getGpr st.data (.reg .X0)) i16 v ∧
      (∀ r ∈ armFrame.calleeSaved, armMach.getGpr st.data r = armMach.getGpr s r) ∧
      armMach.getGpr st.data armFrame.sp = armMach.getGpr s armFrame.sp := by
  letI := concreteHost
  refine armFrameSpec.label_spec (k := 0) (l := "caller") rfl ?_
  have hsp_frame : region (armMach.getGpr s armFrame.sp - 32#64) 32 =
      (region (armMach.getGpr s armFrame.sp - 32#64) 16 ⋆
        region (armMach.getGpr s armFrame.sp - 16#64) 16) := by
    have := region_split (a := armMach.getGpr s armFrame.sp - 32#64) (n1 := 16) (n2 := 16) (by decide)
    grind
  have hmem_pro : (s.dmem =⋆
      armFrameSpec.RetAddr (armMach.getGpr s armFrame.sp) ra ⋆
      region (armMach.getGpr s armFrame.sp - BitVec.ofNat 64 (armFrame.frameSize 1))
        (armFrame.frameSize 1) ⋆ (region (armMach.getGpr s armFrame.sp - 32#64) 16 ⋆ R)) := by
    rw [hsp_frame] at hmem
    simpa [armFrame, armFrameSize] using sep_cast hmem (by ac_rfl)
  refine armFrameSpec.prologue_spec (h := concreteHost) (k := 1) (ns := 1) (ra := ra)
    hra hsp (by decide) hmem_pro ⟨List.drop 3 callerCalleeProg, rfl⟩ ?_
  rintro s1 ⟨hsp1, hmem1⟩ hfr1
  have hsp1_val : armMach.getGpr s1 armFrame.sp = armMach.getGpr s armFrame.sp - 16#64 := by
    simpa [armFrame, armFrameSize] using hsp1
  have hmem_call : (s1.dmem =⋆
      region (armMach.getGpr s1 armFrame.sp - BitVec.ofNat 64 armFrame.raBytes) armFrame.raBytes ⋆
      (region (armMach.getGpr s armFrame.sp - 32#64) 16 ⋆
        armFrameSpec.Saved (armMach.getGpr s armFrame.sp) ra 1 ⋆
        region (armMach.getGpr s armFrame.sp - 16#64) 8 ⋆ R)) := by
    have hzero : armFrame.raBytes = 0 := rfl
    have hfs1 : armFrame.frameSize 1 = 16 := rfl
    rw [hfs1] at hmem1
    rw [hzero, BitVec.sub_zero, region_zero, emp_sep]
    exact sep_cast hmem1 (by ac_rfl)
  refine armFrameSpec.call_spec (h := concreteHost) (k := 3) (sym := "callee")
    (List.isInfixAt_singleton.mpr rfl) hmem_call ?_
  rintro s2 hsp2 hfr2 hra2 hmem2
  have hlbl : armMach.labelAddr concreteHost "callee" = armMach.addrOf concreteHost 7 :=
    armFrameSpec.labelAddr_eq rfl (concreteHost_unique.first rfl)
  rw [hlbl]
  refine armFrameSpec.label_spec (h := concreteHost) (k := 7) (l := "callee") rfl ?_
  have hsp2_entry : armFrameSpec.spEntry (armMach.getGpr s2 armFrame.sp) := by
    rw [hsp2, hsp1_val]; exact armFrameSpec.spEntry_call _ 1 hsp
  have hh2 : GprHolds (armMach.getGpr s2 (.reg .X0)) i16 v := by
    rw [hfr2.1 (.reg .X0) (by simp), hfr1.1 (.reg .X0) (by simp)]; exact hh
  have hmem_callee : s2.dmem =⋆
      armFrameSpec.RetAddr (armMach.getGpr s2 armFrame.sp) (Host.addrOf 4) ⋆
      region (armMach.getGpr s2 armFrame.sp - BitVec.ofNat 64 (armFrame.frameSize 1))
        (armFrame.frameSize 1) ⋆
      (armFrameSpec.Saved (armMach.getGpr s armFrame.sp) ra 1 ⋆
        region (armMach.getGpr s armFrame.sp - 16#64) 8 ⋆ R) := by
    have hsp2' : armMach.getGpr s2 armFrame.sp = armMach.getGpr s armFrame.sp - 16#64 := by
      rw [hsp2, hsp1_val]; change _ - 0#64 = _; grind
    have hsub32 : armMach.getGpr s armFrame.sp - 32#64 =
        armMach.getGpr s2 armFrame.sp - BitVec.ofNat 64 (armFrame.frameSize 1) := by
      rw [hsp2']; change _ = _ - 16#64; grind
    have haddr4 : armMach.addrOf concreteHost (3 + (armFrame.call "callee").length) = Host.addrOf 4 := rfl
    have hfs1 : armFrame.frameSize 1 = 16 := rfl
    rw [haddr4, hsub32] at hmem2
    rw [hfs1]
    exact sep_cast hmem2 (by ac_rfl)
  refine armEchoProg_spec (ns := 1) (v := v) (h := concreteHost) (k := 8) (by decide) (by decide)
    ⟨[], rfl⟩ hra2 hsp2_entry hh2 hmem_callee ?_
  rintro s3 hx0_3 hcs3 hsp3 hmem3
  have hsp3_eq : armMach.getGpr s3 armFrame.sp = armMach.getGpr s armFrame.sp - 16#64 := by
    rw [hsp3, hsp2, hsp1_val]; change _ - 0#64 = _; grind
  have hsp3_ok : armFrameSpec.spOk (armMach.getGpr s3 armFrame.sp) := by
    rw [hsp3_eq]; simpa [armFrame, armFrameSize] using armFrameSpec.spOk_frame _ 1 hsp
  have hmem_epi : s3.dmem =⋆
      armFrameSpec.Saved (armMach.getGpr s3 armFrame.sp + BitVec.ofNat 64 (armFrame.frameSize 1)) ra 1 ⋆
      (region (armMach.getGpr s armFrame.sp - 16#64) 8 ⋆
        (region (armMach.getGpr s armFrame.sp - 32#64) 16 ⋆ R)) := by
    have hsp_saved : armMach.getGpr s3 armFrame.sp + BitVec.ofNat 64 (armFrame.frameSize 1) =
        armMach.getGpr s armFrame.sp := by
      rw [hsp3_eq]; change _ - 16#64 + 16#64 = _; grind
    have hsub32' : armMach.getGpr s2 armFrame.sp - BitVec.ofNat 64 (armFrame.frameSize 1) =
        armMach.getGpr s armFrame.sp - 32#64 := by
      rw [hsp2, hsp1_val]; change _ - 0#64 - 16#64 = _; grind
    have hlen16 : armFrame.frameSize 1 + armFrame.raBytes = 16 := rfl
    rw [hsub32', hlen16] at hmem3
    rw [hsp_saved]
    exact sep_cast hmem3 (by ac_rfl)
  refine armFrameSpec.epilogue_spec (h := concreteHost) (k := 4) (ns := 1) (ra := ra)
    hsp3_ok (by decide) hmem_epi ⟨List.drop 6 callerCalleeProg, rfl⟩ ?_
  rintro s4 ⟨hsp4, hra4, hmem4⟩ hfr4
  have hsp4_eq : armMach.getGpr s4 armFrame.sp = armMach.getGpr s armFrame.sp := by
    rw [hsp4, hsp3_eq]; change _ - 16#64 + 16#64 = _; grind
  have hmem_ret : s4.dmem =⋆ armFrameSpec.RetAddr (armMach.getGpr s4 armFrame.sp) ra ⋆
      (region (armMach.getGpr s3 armFrame.sp + BitVec.ofNat 64 (8 * 1)) (armFrame.frameSize 1 - 8 * 1) ⋆
        (region (armMach.getGpr s armFrame.sp - 16#64) 8 ⋆
          (region (armMach.getGpr s armFrame.sp - 32#64) 16 ⋆ R))) := by
    rw [← hsp4] at hmem4
    exact sep_cast hmem4 (by ac_rfl)
  refine armFrameSpec.ret_spec (h := concreteHost) (k := 6) (ra := ra)
    (List.isInfixAt_singleton.mpr rfl) hra4 hmem_ret ?_
  rintro s5 hk5 _ hsp5 _
  refine Eventually.done _ ⟨rfl, ?_, ?_, ?_⟩
  · rw [hk5 (.reg .X0) (by simp), hfr4.1 (.reg .X0) (by simp)]
    exact hx0_3
  · intro r hr
    have hnot_sp : r ≠ armFrame.sp := fun e => armFrameSpec.sp_disj.2.2.1 (e ▸ hr)
    have hnot_sc : r ∉ armScratch := fun hsc => (armFrameSpec.scratch_disj r hsc).2.1 hr
    have hnot_ra : r ≠ .reg .X30 := by
      have hra' := fun h => (armFrameSpec.ra_disj r h).2.2.1 hr
      simpa using hra'
    rw [hk5 r (by simp [hnot_sp, hnot_sc]),
      hfr4.1 r (by simp [hnot_sp, hnot_sc, hnot_ra]),
      hcs3 r hr,
      hfr2.1 r (by simp [hnot_sp, hnot_sc, hnot_ra]),
      hfr1.1 r (by simp [hnot_sp, hnot_sc, hnot_ra])]
  · rw [show armFrame.raBytes = 0 from rfl, BitVec.add_zero] at hsp5
    exact hsp5.trans hsp4_eq

/-! ## 5. Standard-axiom audit -/

#print axioms LeanQbe.T.Arm64.armFrameSpec
#print axioms LeanQbe.T.Arm64.armPrologue_noLab
#print axioms LeanQbe.T.Arm64.armEpilogue_noLab
#print axioms LeanQbe.T.Arm64.armSlotSt_noLab
#print axioms LeanQbe.T.Arm64.armSlotLd_noLab
#print axioms LeanQbe.T.Arm64.armCanonAbi_noLab
#print axioms LeanQbe.T.Arm64.armCall_noLab
#print axioms LeanQbe.T.Arm64.armExitJmp_noLab
#print axioms LeanQbe.T.Arm64.armRet_noLab
#print axioms armEchoProg_spec
#print axioms armSpCorner_spec
#print axioms callerCallee_e2e

end LeanQbeTest.T.Arm64FrameTest
