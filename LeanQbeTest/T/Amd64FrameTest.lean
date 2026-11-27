module

public import LeanQbe.T.Amd64.FrameLemmas
import Kraken.X64.Parser

/-!
# SysV x64 Frame & ABI Verification Tests

Standalone downstream module verifying:
1. Kernel `rfl` / `t_kernel_rfl` reduction of `x64Frame` (`bitWidths`, `raBytes`, registers,
   `frameSize` at small and `2^31`-crossing boundaries, and directive generation vs
   `Kraken.X64.Parser`).
2. Generic `x64FrameSpec : FrameTarget x64Mach x64Frame x64CondReads` round-trip for arbitrary
   `ns ≥ 1` (`x64FrameSize ns + 8 ≤ 2 ^ 64`): prologue → slot store → slot load → `canonAbi` →
   epilogue → return, preserving `calleeSaved`, restoring `rsp`, and establishing `AbiGprHolds`.
3. Concrete `Host.ofLayout` caller → `call "callee"` → callee → `ret` → caller `ret` composition.
4. `NoLab` invariance and standard-axiom audit `[propext, Classical.choice, Quot.sound]`.
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.Amd64FrameTest

open LeanQbe.T
open LeanQbe.T.Amd64
open Kraken.X64.Parser
open Std Std.ExtHashMap

/-! ## 1. Kernel `rfl` / `t_kernel_rfl` property and parser checks -/

theorem x64Frame_metadata_rfl :
    x64Frame.sp = .rsp ∧
    x64Frame.raBytes = 8 ∧
    x64Frame.bitWidths = [8, 16, 32, 64] ∧
    x64Frame.raRegs = [] ∧
    x64Frame.argRegs = [.rdi, .rsi, .rdx, .rcx, .r8, .r9] ∧
    x64Frame.retRegs = [.rax, .rdx, .rcx, .rsi, .rdi, .r8, .r9] := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem x64FrameSize_rfl :
    x64Frame.frameSize 0 = 8 ∧
    x64Frame.frameSize 1 = 8 ∧
    x64Frame.frameSize 2 = 24 ∧
    x64Frame.frameSize (2 ^ 29) = 4294967304 ∧
    x64Frame.frameSize (2 ^ 29 + 1) = 4294967304 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem x64Frame_parser_rfl :
    ⸨prog| subq $8, %rsp; movq %rdi, (%rsp);
      movq (%rsp), %rax; movl %eax, %eax; addq $8, %rsp; ret ⸩ =
      (x64Frame.prologue 1).1 ++ x64Frame.slotSt 0 .rdi ++ x64Frame.slotLd .rax 0 ++
        (x64Frame.canonAbi i32 .rax).1 ++ (x64Frame.epilogue 1).1 ++ x64Frame.ret := rfl

theorem x64Frame_large_parser_rfl :
    ⸨prog| movabs $4294967304, %r10; subq %r10, %rsp ⸩ = (x64Frame.prologue (2 ^ 29)).1 ∧
    ⸨prog| movabs $4294967296, %r10; movq %rdi, (%rsp, %r10, 1) ⸩ =
      x64Frame.slotSt (2 ^ 29) .rdi ∧
    ⸨prog| movabs $4294967296, %r10; movq (%rsp, %r10, 1), %rax ⸩ =
      x64Frame.slotLd .rax (2 ^ 29) ∧
    ⸨prog| movabs $4294967304, %r10; addq %r10, %rsp ⸩ = (x64Frame.epilogue (2 ^ 29)).1 := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-! ## 2. Generic `x64FrameSpec` round-trip over arbitrary `ns ≥ 1` (`frameSize ns + 8 ≤ 2 ^ 64`) -/

def x64EchoProg (ns : Nat) : List Directive :=
  (x64Frame.prologue ns).1 ++ x64Frame.slotSt 0 .rdi ++ x64Frame.slotLd .rax 0 ++
    (x64Frame.canonAbi i32 .rax).1 ++ (x64Frame.epilogue ns).1 ++ x64Frame.ret

theorem x64EchoProg_noLab (ns : Nat) (l : Sym) :
    Kraken.Directive.label l ∉ x64EchoProg ns := by
  simp only [x64EchoProg, List.mem_append, not_or]
  exact ⟨⟨⟨⟨⟨x64Prologue_noLab ns l, x64SlotSt_noLab 0 .rdi l⟩,
    x64SlotLd_noLab .rax 0 l⟩, x64CanonAbi_noLab i32 .rax l⟩, x64Epilogue_noLab ns l⟩,
      x64Ret_noLab l⟩

theorem x64EchoProg_spec {h : Host} {k ns : Nat} {v : Val i32} {s : MachineData}
    {ra : Int64} {R : Mem 64 → Prop} {post : MachineState → Prop}
    (hns : 1 ≤ ns)
    (hF : x64Frame.frameSize ns + x64Frame.raBytes ≤ 2 ^ 64)
    (hc : (x64EchoProg ns).IsInfixAt (x64Mach.prog h) k)
    (hsp : x64FrameSpec.spEntry (x64Mach.getGpr s x64Frame.sp))
    (hh : GprHolds (x64Mach.getGpr s .rdi) i32 v)
    (hmem : s.dmem =⋆
      x64FrameSpec.RetAddr (x64Mach.getGpr s x64Frame.sp) ra ⋆
      region (x64Mach.getGpr s x64Frame.sp - BitVec.ofNat 64 (x64Frame.frameSize ns))
        (x64Frame.frameSize ns) ⋆ R)
    (hret : ∀ s' : MachineData,
      AbiGprHolds (x64Mach.getGpr s' .rax) i32 v →
      (∀ r ∈ x64Frame.calleeSaved, x64Mach.getGpr s' r = x64Mach.getGpr s r) →
      x64Mach.getGpr s' x64Frame.sp = x64Mach.getGpr s x64Frame.sp + 8#64 →
      (s'.dmem =⋆
        region (x64Mach.getGpr s x64Frame.sp - BitVec.ofNat 64 (x64Frame.frameSize ns))
          (x64Frame.frameSize ns + x64Frame.raBytes) ⋆ R) →
      Eventually (x64Mach.step h) post (x64Mach.mkState s' ra)) :
    x64Mach.Run h k s post := by
  letI := h
  obtain ⟨hleft, hretAt⟩ := hc.append
  obtain ⟨hleft, hepi⟩ := hleft.append
  obtain ⟨hleft, hcab⟩ := hleft.append
  obtain ⟨hleft, hld⟩ := hleft.append
  obtain ⟨hpro, hst⟩ := hleft.append
  simp only [List.length_append, ← Nat.add_assoc] at hld hcab hepi hretAt
  have hle : 8 ≤ 8 * ns := by omega
  have hF0 : x64Frame.frameSize ns ≤ 2 ^ 64 := by
    change x64FrameSize ns ≤ 2 ^ 64
    change x64FrameSize ns + 8 ≤ 2 ^ 64 at hF
    omega
  refine x64FrameSpec.prologue_spec (ra := ra) trivial hsp hF hmem hpro ?_
  rintro s1 ⟨hsp1, hmem1⟩ hfr1
  have hsplit1 : region (x64Mach.getGpr s1 x64Frame.sp) (8 * ns) =
      (region (x64Mach.getGpr s1 x64Frame.sp) 8 ⋆
        region (x64Mach.getGpr s1 x64Frame.sp + 8#64) (8 * ns - 8)) := by
    have he : 8 * ns = 8 + (8 * ns - 8) := by omega
    conv => lhs; rw [he]
    exact region_split (by
      have hge := x64FrameSize_ge ns
      change x64FrameSize ns ≤ 2 ^ 64 at hF0
      omega)
  have hmem1' : (s1.dmem =⋆ region (x64Mach.getGpr s1 x64Frame.sp + BitVec.ofNat 64 (8 * 0)) 8 ⋆
      (region (x64Mach.getGpr s1 x64Frame.sp + 8#64) (8 * ns - 8) ⋆
        x64FrameSpec.Saved (x64Mach.getGpr s x64Frame.sp) ra ns ⋆ R)) := by
    rw [← hsp1, hsplit1] at hmem1
    rw [show BitVec.ofNat 64 (8 * 0) = 0#64 from rfl, BitVec.add_zero]
    exact sep_cast hmem1 (by ac_rfl)
  refine x64FrameSpec.slotSt_spec (r := .rdi) (by simp) trivial hmem1' hst ?_
  intro s2 hmem2 hfr2
  have hval : x64Mach.getGpr s1 .rdi = x64Mach.getGpr s .rdi :=
    hfr1.1 .rdi (by simp)
  have hsp2 : x64Mach.getGpr s2 x64Frame.sp = x64Mach.getGpr s1 x64Frame.sp :=
    hfr2.1 x64Frame.sp (by simp)
  have hmem2' : (s2.dmem =⋆
      cell64 (x64Mach.getGpr s2 x64Frame.sp + BitVec.ofNat 64 (8 * 0)) (x64Mach.getGpr s .rdi) ⋆
      (region (x64Mach.getGpr s1 x64Frame.sp + 8#64) (8 * ns - 8) ⋆
        x64FrameSpec.Saved (x64Mach.getGpr s x64Frame.sp) ra ns ⋆ R)) := by
    rw [hsp2, ← hval]; exact hmem2
  refine x64FrameSpec.slotLd_spec (rd := .rax) (by simp) trivial hmem2' hld ?_
  rintro s3 ⟨hrax3, hdmem3⟩ hfr3
  have hh3 : GprHolds (x64Mach.getGpr s3 .rax) i32 v := hrax3 ▸ hh
  refine x64FrameSpec.canonAbi_spec (Or.inr ⟨32, by decide, rfl⟩) (by simp) hh3 hcab ?_
  rintro s4 ⟨hAbi4, hdmem4⟩ hfr4
  have hsp4 : x64Mach.getGpr s4 x64Frame.sp =
      x64Mach.getGpr s x64Frame.sp - BitVec.ofNat 64 (x64Frame.frameSize ns) := by
    rw [hfr4.1 _ (by simp), hfr3.1 _ (by simp), hsp2, hsp1]
  have hmem4 : s4.dmem =⋆
      x64FrameSpec.Saved (x64Mach.getGpr s4 x64Frame.sp + BitVec.ofNat 64 (x64Frame.frameSize ns))
        ra ns ⋆
      (region (x64Mach.getGpr s x64Frame.sp - BitVec.ofNat 64 (x64Frame.frameSize ns))
        (8 * ns) ⋆ R) := by
    rw [hsp4, BitVec.sub_add_cancel]
    have h42 : s4.dmem = s2.dmem := hdmem4.trans hdmem3
    rw [h42]
    have hreg : (cell64 (x64Mach.getGpr s2 x64Frame.sp + BitVec.ofNat 64 (8 * 0))
      (x64Mach.getGpr s .rdi) ⋆
        (region (x64Mach.getGpr s1 x64Frame.sp + 8#64) (8 * ns - 8) ⋆
          x64FrameSpec.Saved (x64Mach.getGpr s x64Frame.sp) ra ns ⋆ R)) s2.dmem := hmem2'
    have hreg2 := sep_mono (fun _ => cell64_region) hreg
    rw [hsp2, Nat.mul_zero, BitVec.add_zero] at hreg2
    have hback := sep_cast hreg2 (show
        (region (x64Mach.getGpr s1 x64Frame.sp) 8 ⋆
          (region (x64Mach.getGpr s1 x64Frame.sp + 8#64) (8 * ns - 8) ⋆
            x64FrameSpec.Saved (x64Mach.getGpr s x64Frame.sp) ra ns ⋆ R)) =
        (x64FrameSpec.Saved (x64Mach.getGpr s x64Frame.sp) ra ns ⋆
          ((region (x64Mach.getGpr s1 x64Frame.sp) 8 ⋆
            region (x64Mach.getGpr s1 x64Frame.sp + 8#64) (8 * ns - 8)) ⋆ R)) from by ac_rfl)
    rw [← hsplit1, hsp1] at hback
    exact hback
  refine x64FrameSpec.epilogue_spec trivial hF hmem4 hepi ?_
  rintro s5 ⟨hsp5, _, hmem5⟩ hfr5
  have hsp5' : x64Mach.getGpr s5 x64Frame.sp = x64Mach.getGpr s x64Frame.sp := by
    rw [hsp5, hsp4, BitVec.sub_add_cancel]
  have hmem5' : s5.dmem =⋆
      x64FrameSpec.RetAddr (x64Mach.getGpr s5 x64Frame.sp) ra ⋆
      (region (x64Mach.getGpr s x64Frame.sp - BitVec.ofNat 64 (x64Frame.frameSize ns))
        (x64Frame.frameSize ns) ⋆ R) := by
    rw [hsp4, BitVec.sub_add_cancel] at hmem5
    rw [hsp5']
    have hsplit_frame := region_frame_split (a :=
      x64Mach.getGpr s x64Frame.sp - BitVec.ofNat 64 (x64Frame.frameSize ns))
      (slots := 8 * ns) (frame := x64Frame.frameSize ns) (x64FrameSize_ge ns) hF0
    have hcast := sep_cast hmem5 (show
        (x64FrameSpec.RetAddr (x64Mach.getGpr s x64Frame.sp) ra ⋆
          region (x64Mach.getGpr s x64Frame.sp - BitVec.ofNat 64 (x64Frame.frameSize ns) +
            BitVec.ofNat 64 (8 * ns))
            (x64Frame.frameSize ns - 8 * ns) ⋆
          (region (x64Mach.getGpr s x64Frame.sp - BitVec.ofNat 64 (x64Frame.frameSize ns))
            (8 * ns) ⋆ R)) =
        (x64FrameSpec.RetAddr (x64Mach.getGpr s x64Frame.sp) ra ⋆
          ((region (x64Mach.getGpr s x64Frame.sp - BitVec.ofNat 64 (x64Frame.frameSize ns))
            (8 * ns) ⋆
            region (x64Mach.getGpr s x64Frame.sp - BitVec.ofNat 64 (x64Frame.frameSize ns) +
              BitVec.ofNat 64 (8 * ns))
              (x64Frame.frameSize ns - 8 * ns)) ⋆ R)) from by ac_rfl)
    rw [← hsplit_frame] at hcast
    exact hcast
  refine x64FrameSpec.ret_spec hretAt trivial hmem5' ?_
  rintro s6 hk6 _ hsp6 hdmem6
  have hrax6 : AbiGprHolds (x64Mach.getGpr s6 .rax) i32 v := by
    have h65 : x64Mach.getGpr s6 .rax = x64Mach.getGpr s5 .rax := hk6 .rax (by simp)
    have h54 : x64Mach.getGpr s5 .rax = x64Mach.getGpr s4 .rax := hfr5.1 .rax (by simp)
    rw [h65, h54]
    exact hAbi4
  have hcs6 : ∀ r ∈ x64Frame.calleeSaved, x64Mach.getGpr s6 r = x64Mach.getGpr s r := by
    intro r hr
    have hnot_sp : r ≠ x64Frame.sp := fun e => x64FrameSpec.sp_disj.2.2.1 (e ▸ hr)
    have hnot_sc : r ∉ x64Scratch := fun hsc => (x64FrameSpec.scratch_disj r hsc).2.1 hr
    have hnot_rax : r ≠ .rax := fun e => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with h | h | h | h | h | h <;> subst h <;> cases e
    rw [hk6 r (by simp [hnot_sp, hnot_sc]),
      hfr5.1 r (by simp [hnot_sp, hnot_sc]),
      hfr4.1 r (by simp [hnot_rax, hnot_sc]),
      hfr3.1 r (by simp [hnot_rax, hnot_sc]),
      hfr2.1 r (by simp [hnot_sc]),
      hfr1.1 r (by simp [hnot_sp, hnot_sc])]
  have hsp_out : x64Mach.getGpr s6 x64Frame.sp = x64Mach.getGpr s x64Frame.sp + 8#64 := by
    rw [hsp6, hsp5']
  have hmem_out : s6.dmem =⋆
      region (x64Mach.getGpr s x64Frame.sp - BitVec.ofNat 64 (x64Frame.frameSize ns))
        (x64Frame.frameSize ns + x64Frame.raBytes) ⋆ R := by
    dsimp only [x64Mach] at hdmem6
    rw [hdmem6]
    have hm1 := sep_mono (fun _ => x64FrameSpec.retAddr_region _ _ _) hmem5'
    have hm2 := sep_cast hm1 (show
        (region (x64Mach.getGpr s5 x64Frame.sp) x64Frame.raBytes ⋆
          (region (x64Mach.getGpr s x64Frame.sp - BitVec.ofNat 64 (x64Frame.frameSize ns))
            (x64Frame.frameSize ns) ⋆ R)) =
        ((region (x64Mach.getGpr s x64Frame.sp - BitVec.ofNat 64 (x64Frame.frameSize ns))
            (x64Frame.frameSize ns) ⋆
          region (x64Mach.getGpr s5 x64Frame.sp) x64Frame.raBytes) ⋆ R) from by ac_rfl)
    rw [hsp5'] at hm2
    have hm3 : (region (x64Mach.getGpr s x64Frame.sp - BitVec.ofNat 64 (x64Frame.frameSize ns))
          (x64Frame.frameSize ns) ⋆
        region (x64Mach.getGpr s x64Frame.sp - BitVec.ofNat 64 (x64Frame.frameSize ns) +
          BitVec.ofNat 64 (x64Frame.frameSize ns)) x64Frame.raBytes) =
        region (x64Mach.getGpr s x64Frame.sp - BitVec.ofNat 64 (x64Frame.frameSize ns))
          (x64Frame.frameSize ns + x64Frame.raBytes) := by
      exact (region_split hF).symm
    rw [BitVec.sub_add_cancel] at hm3
    rwa [hm3] at hm2
  exact hret s6 hrax6 hcs6 hsp_out hmem_out

/-! ## 3. Concrete `Host.ofLayout` caller → `call "callee"` → callee → `ret` test -/

@[instance_reducible] def testLayout : Layout where
  start := 0x10000
  instrSize _ := 4
  instrSize_pos _ := by decide

def callerCalleeProg : List Directive :=
  [x64Frame.label "caller"] ++ (x64Frame.prologue 1).1 ++ x64Frame.call "callee" ++
    (x64Frame.epilogue 1).1 ++ x64Frame.ret ++
  [x64Frame.label "callee"] ++ x64EchoProg 1

theorem callerCallee_small :
    (Kraken.Layout.apply testLayout callerCalleeProg).sizeBefore callerCalleeProg.length < 2 ^ 64 :=
      by
  have : (Kraken.Layout.apply testLayout callerCalleeProg).sizeBefore callerCalleeProg.length =
    40 := by
    simp [Kraken.Layout.apply, Kraken.Executable.sizeBefore, Kraken.Layout.size, callerCalleeProg]
    decide
  omega

@[instance_reducible] def concreteHost : Host :=
  Host.ofLayout callerCalleeProg testLayout callerCallee_small

theorem concreteHost_unique : concreteHost.LabelsUnique :=
  letI := concreteHost
  Host.labelsUnique_of_nodup (by decide)

theorem callerCallee_e2e {v : Val i32} {s : MachineData} {ra : Int64} {R : Mem 64 → Prop}
    (hsp : x64FrameSpec.spEntry (x64Mach.getGpr s x64Frame.sp))
    (hh : GprHolds (x64Mach.getGpr s .rdi) i32 v)
    (hmem : s.dmem =⋆
      x64FrameSpec.RetAddr (x64Mach.getGpr s x64Frame.sp) ra ⋆
      region (x64Mach.getGpr s x64Frame.sp - 32#64) 32 ⋆ R) :
    x64Mach.Run concreteHost 0 s fun st =>
      st.pc = ra ∧ AbiGprHolds (x64Mach.getGpr st.data .rax) i32 v ∧
      (∀ r ∈ x64Frame.calleeSaved, x64Mach.getGpr st.data r = x64Mach.getGpr s r) ∧
      x64Mach.getGpr st.data x64Frame.sp = x64Mach.getGpr s x64Frame.sp + 8#64 := by
  letI := concreteHost
  refine x64FrameSpec.label_spec (k := 0) (l := "caller") rfl ?_
  have hsp_frame : region (x64Mach.getGpr s x64Frame.sp - 32#64) 32 =
      (region (x64Mach.getGpr s x64Frame.sp - 32#64) 24 ⋆
        region (x64Mach.getGpr s x64Frame.sp - 8#64) 8) := by
    have := region_split (a := x64Mach.getGpr s x64Frame.sp - 32#64) (n1 := 24) (n2 :=
      8) (by decide)
    grind
  have hmem_pro : (s.dmem =⋆
      x64FrameSpec.RetAddr (x64Mach.getGpr s x64Frame.sp) ra ⋆
      region (x64Mach.getGpr s x64Frame.sp - BitVec.ofNat 64 (x64Frame.frameSize 1))
        (x64Frame.frameSize 1) ⋆ (region (x64Mach.getGpr s x64Frame.sp - 32#64) 24 ⋆ R)) := by
    rw [hsp_frame] at hmem
    simpa [x64Frame, x64FrameSize] using sep_cast hmem (by ac_rfl)
  refine x64FrameSpec.prologue_spec (h := concreteHost) (k := 1) (ns := 1) (ra := ra)
    trivial hsp (by decide) hmem_pro (List.isInfixAt_singleton.mpr rfl) ?_
  rintro s1 ⟨hsp1, hmem1⟩ hfr1
  have hsp1_val : x64Mach.getGpr s1 x64Frame.sp = x64Mach.getGpr s x64Frame.sp - 8#64 := by
    simpa [x64Frame, x64FrameSize] using hsp1
  have hsplit_24 : region (x64Mach.getGpr s x64Frame.sp - 32#64) 24 =
      (region (x64Mach.getGpr s x64Frame.sp - 32#64) 16 ⋆
        region (x64Mach.getGpr s x64Frame.sp - 16#64) 8) := by
    have := region_split (a := x64Mach.getGpr s x64Frame.sp - 32#64) (n1 := 16) (n2 :=
      8) (by decide)
    grind
  have hmem_call : (s1.dmem =⋆
      region (x64Mach.getGpr s1 x64Frame.sp - BitVec.ofNat 64 x64Frame.raBytes) x64Frame.raBytes ⋆
      (region (x64Mach.getGpr s x64Frame.sp - 32#64) 16 ⋆
        x64FrameSpec.Saved (x64Mach.getGpr s x64Frame.sp) ra 1 ⋆
        region (x64Mach.getGpr s x64Frame.sp - 8#64) 8 ⋆ R)) := by
    rw [hsplit_24] at hmem1
    rw [hsp1_val]
    have hsp16 : x64Mach.getGpr s x64Frame.sp - 8#64 - BitVec.ofNat 64 x64Frame.raBytes =
        x64Mach.getGpr s x64Frame.sp - 16#64 := by
      change _ - 8#64 - 8#64 = _; grind
    rw [hsp16]
    have hfs1 : x64Frame.frameSize 1 = 8 := rfl
    have hra1 : x64Frame.raBytes = 8 := rfl
    rw [hfs1] at hmem1
    rw [hra1]
    exact sep_cast hmem1 (by ac_rfl)
  refine x64FrameSpec.call_spec (h := concreteHost) (k := 2) (sym := "callee")
    (List.isInfixAt_singleton.mpr rfl) hmem_call ?_
  rintro s2 hsp2 hfr2 _ hmem2
  have hlbl : x64Mach.labelAddr concreteHost "callee" = x64Mach.addrOf concreteHost 5 :=
    x64FrameSpec.labelAddr_eq rfl (concreteHost_unique.first rfl)
  rw [hlbl]
  refine x64FrameSpec.label_spec (h := concreteHost) (k := 5) (l := "callee") rfl ?_
  have hsp2_entry : x64FrameSpec.spEntry (x64Mach.getGpr s2 x64Frame.sp) := by
    rw [hsp2, hsp1_val]; exact x64FrameSpec.spEntry_call _ 1 hsp
  have hh2 : GprHolds (x64Mach.getGpr s2 .rdi) i32 v := by
    rw [hfr2.1 .rdi (by simp), hfr1.1 .rdi (by simp)]; exact hh
  have hmem_callee : s2.dmem =⋆
      x64FrameSpec.RetAddr (x64Mach.getGpr s2 x64Frame.sp) (Host.addrOf 3) ⋆
      region (x64Mach.getGpr s2 x64Frame.sp - BitVec.ofNat 64 (x64Frame.frameSize 1))
        (x64Frame.frameSize 1) ⋆
      (region (x64Mach.getGpr s x64Frame.sp - 32#64) 8 ⋆
        x64FrameSpec.Saved (x64Mach.getGpr s x64Frame.sp) ra 1 ⋆
        region (x64Mach.getGpr s x64Frame.sp - 8#64) 8 ⋆ R) := by
    have hsplit_16 : region (x64Mach.getGpr s x64Frame.sp - 32#64) 16 =
        (region (x64Mach.getGpr s x64Frame.sp - 32#64) 8 ⋆
          region (x64Mach.getGpr s x64Frame.sp - 24#64) 8) := by
      have := region_split (a := x64Mach.getGpr s x64Frame.sp - 32#64) (n1 := 8) (n2 :=
        8) (by decide)
      grind
    rw [hsplit_16] at hmem2
    have hsp2' : x64Mach.getGpr s2 x64Frame.sp = x64Mach.getGpr s x64Frame.sp - 16#64 := by
      rw [hsp2, hsp1_val]; grind
    have haddr3 : x64Mach.addrOf concreteHost (2 + (x64Frame.call "callee").length) =
      Host.addrOf 3 := rfl
    have hsub24 : x64Mach.getGpr s x64Frame.sp - 24#64 =
        x64Mach.getGpr s2 x64Frame.sp - BitVec.ofNat 64 (x64Frame.frameSize 1) := by
      rw [hsp2']; change _ = _ - 8#64; grind
    rw [haddr3, hsub24] at hmem2
    exact sep_cast hmem2 (by ac_rfl)
  refine x64EchoProg_spec (ns := 1) (v := v) (h := concreteHost) (k := 6) (by decide) (by decide)
    ⟨[], rfl⟩ hsp2_entry hh2 hmem_callee ?_
  rintro s3 hrax3 hcs3 hsp3 hmem3
  have hsp3_eq : x64Mach.getGpr s3 x64Frame.sp = x64Mach.getGpr s x64Frame.sp - 8#64 := by
    rw [hsp3, hsp2, hsp1_val]; grind
  have hmem_epi : s3.dmem =⋆
      x64FrameSpec.Saved (x64Mach.getGpr s3 x64Frame.sp + BitVec.ofNat 64 (x64Frame.frameSize 1)) ra
        1 ⋆
      (region (x64Mach.getGpr s x64Frame.sp - 8#64) 8 ⋆
        (region (x64Mach.getGpr s x64Frame.sp - 32#64) 24 ⋆ R)) := by
    have h24 : x64Mach.getGpr s2 x64Frame.sp - BitVec.ofNat 64 (x64Frame.frameSize 1) =
        x64Mach.getGpr s x64Frame.sp - 24#64 := by
      rw [hsp2, hsp1_val]; change _ - 8#64 - 8#64 = _; grind
    have hlen16 : x64Frame.frameSize 1 + x64Frame.raBytes = 16 := rfl
    rw [h24, hlen16] at hmem3
    rw [hsp3_eq]
    have hsp_saved : x64Mach.getGpr s x64Frame.sp - 8#64 + BitVec.ofNat 64 (x64Frame.frameSize 1) =
        x64Mach.getGpr s x64Frame.sp := by
      change _ - 8#64 + 8#64 = _; grind
    rw [hsp_saved]
    have hsplit_24' : region (x64Mach.getGpr s x64Frame.sp - 32#64) 24 =
        (region (x64Mach.getGpr s x64Frame.sp - 32#64) 8 ⋆
          region (x64Mach.getGpr s x64Frame.sp - 24#64) 16) := by
      have := region_split (a := x64Mach.getGpr s x64Frame.sp - 32#64) (n1 := 8) (n2 :=
        16) (by decide)
      grind
    rw [hsplit_24']
    exact sep_cast hmem3 (by ac_rfl)
  refine x64FrameSpec.epilogue_spec (h := concreteHost) (k := 3) (ns := 1) (ra := ra)
    trivial (by decide) hmem_epi (List.isInfixAt_singleton.mpr rfl) ?_
  rintro s4 ⟨hsp4, _, hmem4⟩ hfr4
  have hsp4_eq : x64Mach.getGpr s4 x64Frame.sp = x64Mach.getGpr s x64Frame.sp := by
    rw [hsp4, hsp3_eq]; grind
  have hmem_ret : s4.dmem =⋆ x64FrameSpec.RetAddr (x64Mach.getGpr s4 x64Frame.sp) ra ⋆
      (region (x64Mach.getGpr s3 x64Frame.sp + BitVec.ofNat 64 (8 * 1))
        (x64Frame.frameSize 1 - 8 * 1) ⋆
        (region (x64Mach.getGpr s x64Frame.sp - 8#64) 8 ⋆
          (region (x64Mach.getGpr s x64Frame.sp - 32#64) 24 ⋆ R))) := by
    rw [← hsp4] at hmem4
    exact sep_cast hmem4 (by ac_rfl)
  refine x64FrameSpec.ret_spec (h := concreteHost) (k := 4) (ra := ra)
    (List.isInfixAt_singleton.mpr rfl) trivial hmem_ret ?_
  rintro s5 hk5 _ hsp5 _
  refine Eventually.done _ ⟨rfl, ?_, ?_, ?_⟩
  · rw [hk5 .rax (by simp), hfr4.1 .rax (by simp)]
    exact hrax3
  · intro r hr
    have hnot_sp : r ≠ x64Frame.sp := fun e => x64FrameSpec.sp_disj.2.2.1 (e ▸ hr)
    have hnot_sc : r ∉ x64Scratch := fun hsc => (x64FrameSpec.scratch_disj r hsc).2.1 hr
    rw [hk5 r (by simp [hnot_sp, hnot_sc]),
      hfr4.1 r (by simp [hnot_sp, hnot_sc]),
      hcs3 r hr,
      hfr2.1 r (by simp [hnot_sp, hnot_sc]),
      hfr1.1 r (by simp [hnot_sp, hnot_sc])]
  · rw [hsp5, hsp4_eq]

/-! ## 4. Standard-axiom audit -/

#print axioms LeanQbe.T.Amd64.x64FrameSpec
#print axioms LeanQbe.T.Amd64.x64Prologue_noLab
#print axioms LeanQbe.T.Amd64.x64Epilogue_noLab
#print axioms LeanQbe.T.Amd64.x64SlotSt_noLab
#print axioms LeanQbe.T.Amd64.x64SlotLd_noLab
#print axioms LeanQbe.T.Amd64.x64CanonAbi_noLab
#print axioms LeanQbe.T.Amd64.x64Call_noLab
#print axioms LeanQbe.T.Amd64.x64ExitJmp_noLab
#print axioms LeanQbe.T.Amd64.x64Ret_noLab
#print axioms x64EchoProg_spec
#print axioms callerCallee_e2e

end LeanQbeTest.T.Amd64FrameTest
