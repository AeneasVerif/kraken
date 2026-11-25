module

public import LeanQbe.T.Vll.Sem
import LeanQbe.T.TargetLemmas
import LeanQbe.T.AbiLemmas

/-!
# Tests for `BedrockMach` L1 VLLIR Core (`VllCoreTest`)

Exercises:
1. Two concrete toy architectures: `toyArch` (link-register convention `.linkReg .lr` with
   `writeSubZeroExtend` and `.native (.incR r)`) and `toyStackArch` (stack return convention
   `.stack` with `writeSubX64`), proving `Arch.Wf` and generic `vllFrameTarget` for both.
2. An L1 `VllCodeMap toyArch` combining landing pads (`pad`, `padsOk`), `symAddr`, hardware
   `call`/`ret`, a structured `cmp`/`jcc`/`alu` loop (`sum_loop`), `.native` escape-hatch
   execution, open indirect `ijmp`, and `halt`.
3. `VllCodeMap.wp_of_ranked` (`Xcap.wp_of_ranked` / `Lfp.lfp_of_ranked`) + `Xcap.adequacy`
   proving total correctness and termination on every initial state.
4. Open-module `Xcap.ModOk.link` + `Xcap.ModOk.close` with `vllCallPre` (hardware `call`/`ret`).
5. Multi-step small-step `vllMach` execution (`movi`, `alu`, `native`, `call`, `ret`, `ijmp`).
6. `#print axioms` checks confirming `⊆ [propext, Classical.choice, Quot.sound]`.
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.VllCoreTest

open LeanQbe.T
open LeanQbe.T.Vll

/-! ## 1. Toy Link-Register Architecture (`toyArch`) & Stack Architecture (`toyStackArch`) -/

inductive ToyReg where
  | r0 | r1 | r2 | r3 | lr | sp | t0
  deriving DecidableEq, Repr, Inhabited

inductive ToyCond where
  | eq | ne
  deriving DecidableEq, Repr, Inhabited

structure ToyFlags where
  z : Bool
  deriving DecidableEq, Repr, Inhabited

inductive ToyNative where
  | incR (r : ToyReg)
  deriving DecidableEq, Repr

@[expose] def toyFrameSize (ns : Nat) : Nat :=
  (8 * ns + 8 + 15) / 16 * 16

@[expose] def toyStackFrameSize (ns : Nat) : Nat :=
  8 * ns + (if ns % 2 == 0 then 8 else 0)

@[expose] def toyNativeStep :
    ToyNative → (Sym → BitVec 64) → MachData ToyReg Empty ToyFlags →
    NativeOutcome ToyReg Empty ToyFlags → Prop
  | .incR r, _, s, out =>
    out = .fall { s with gpr := fun q => if q = r then s.gpr r + 1#64 else s.gpr q }

@[expose, reducible] def toyArch : Arch where
  Reg := ToyReg
  VReg := Empty
  Cond := ToyCond
  Flags := ToyFlags
  Native := ToyNative
  abi := {
    sp := .sp
    raKind := .linkReg .lr
    scratch := [.t0]
    allocatable := [.r0, .r1, .r2]
    callerSaved := [.r0, .r1, .r2, .t0]
    calleeSaved := [.r3]
    argRegs := [.r0, .r1]
    retRegs := [.r0]
    stackAlign := 16
    pcAlign := 4
    pcName := "pc"
    frameSize := toyFrameSize
    spEntry := fun sp => sp.toNat % 16 = 0
    spOk := fun sp => sp.toNat % 16 = 0
    prologueClob := FlagMask.none
    epilogueClob := FlagMask.none
  }
  writeSub := writeSubZeroExtend
  condReads := fun _ => 0x01#8
  negCond := fun | .eq => .ne | .ne => .eq
  evalCond := fun f c => match c with | .eq => f.z | .ne => !f.z
  zeroFlags := [.eq]
  clearFlagsVal := ⟨false⟩
  cmpClob := 0x01#8
  cmpFlags := fun _ a b _ => ⟨a == b⟩
  testClob := 0x01#8
  testFlags := fun w a b _ => ⟨(a &&& b) == 0#w.bits⟩
  nativeStep := toyNativeStep
  nativeEffect := fun
    | .incR r => {
        gUses := [r], gClob := [r], fClob := FlagMask.none,
        readsMem := false, writesMem := false, isControl := false
      }

theorem toyArch_wf : toyArch.Wf where
  sp_disj := by dsimp only [toyArch, Abi.raRegs, RaKind.raRegs]; decide
  scratch_disj := by
    intro r hr; simp only [toyArch, List.mem_singleton] at hr; subst hr; decide
  cs_disj := by
    intro r hr; simp only [toyArch, List.mem_singleton] at hr; subst hr; decide
  ra_disj := by
    intro r hr
    simp only [toyArch, Abi.raRegs, RaKind.raRegs, List.mem_singleton] at hr
    subst hr; decide
  argRegs_nodup := by decide
  retRegs_nodup := by decide
  callerSaved_sub := by
    intro r hr
    simp only [toyArch, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> decide
  align_pos := by simp
  slots_le_frameSize := fun ns => by dsimp only [toyArch, toyFrameSize]; omega
  linkReg_frameSize := fun _ _ ns => by dsimp only [toyArch, toyFrameSize]; omega
  spOk_frame := fun sp ns hsp => by
    dsimp only [toyArch] at hsp ⊢
    exact aligned16_sub hsp (by dsimp only [toyFrameSize]; omega)
  spEntry_call := fun sp ns hsp => by
    dsimp only [toyArch, Abi.raBytes, RaKind.raBytes] at hsp ⊢
    rw [BitVec.sub_zero]
    exact aligned16_sub hsp (by dsimp only [toyFrameSize]; omega)
  writeSub_setWidth := writeSubZeroExtend_setWidth
  writeSub_w64 := writeSubZeroExtend_w64
  negCond_reads := fun c => by cases c <;> rfl
  negCond_eval := fun f c => by cases f; cases c <;> simp
  clearFlags_zero := by
    intro c hc; simp only [toyArch, List.mem_singleton] at hc; subst hc; rfl
  aluFlags_frame := fun _ _ _ _ _ _ _ _ => rfl
  cmpFlags_frame := fun _ _ _ _ c hc => by
    cases c <;> simp [FlagMask.disjoint] at hc
  testFlags_frame := fun _ _ _ _ c hc => by
    cases c <;> simp [FlagMask.disjoint] at hc
  jnzGprFlags_frame := fun _ _ _ _ => rfl
  prologueFlags_frame := fun _ _ _ _ => rfl
  epilogueFlags_frame := fun _ _ _ _ => rfl
  canonAbiFlags_frame := fun _ _ _ _ => rfl

/-- Generic `FrameTarget` instantiated automatically for `toyArch`. -/
def toyFrameTarget :
    FrameTarget (vllMach toyArch) (vllFrameIsa toyArch) toyArch.condReads :=
  vllFrameTarget toyArch toyArch_wf

@[expose, reducible] def toyStackArch : Arch :=
  { toyArch with
    abi := { toyArch.abi with
      raKind := .stack
      frameSize := toyStackFrameSize
      spEntry := fun sp => (sp + 8#64).toNat % 16 = 0
      spOk := fun _ => True
      prologueClob := FlagMask.all
      epilogueClob := FlagMask.all
    }
    writeSub := writeSubX64
  }

theorem toyStackArch_wf : toyStackArch.Wf where
  sp_disj := by dsimp only [toyStackArch, toyArch, Abi.raRegs, RaKind.raRegs]; decide
  scratch_disj := toyArch_wf.scratch_disj
  cs_disj := toyArch_wf.cs_disj
  ra_disj := by
    intro r hr; simp only [toyStackArch, Abi.raRegs, RaKind.raRegs, List.not_mem_nil] at hr
  argRegs_nodup := toyArch_wf.argRegs_nodup
  retRegs_nodup := toyArch_wf.retRegs_nodup
  callerSaved_sub := toyArch_wf.callerSaved_sub
  align_pos := toyArch_wf.align_pos
  slots_le_frameSize := fun ns => by dsimp only [toyStackArch, toyStackFrameSize]; split <;> omega
  linkReg_frameSize := fun _ h => by simp [toyStackArch] at h
  spOk_frame := fun _ _ _ => trivial
  spEntry_call := fun sp ns hsp => by
    dsimp only [toyStackArch, Abi.raBytes, RaKind.raBytes] at hsp ⊢
    have hmod : toyStackFrameSize ns % 16 = 8 := by
      dsimp only [toyStackFrameSize]
      rcases Nat.mod_two_eq_zero_or_one ns with h | h <;> simp [h] <;> omega
    exact aligned16_add8_sub_call hsp hmod
  writeSub_setWidth := writeSubX64_setWidth
  writeSub_w64 := writeSubX64_w64
  negCond_reads := toyArch_wf.negCond_reads
  negCond_eval := toyArch_wf.negCond_eval
  clearFlags_zero := toyArch_wf.clearFlags_zero
  aluFlags_frame := toyArch_wf.aluFlags_frame
  cmpFlags_frame := toyArch_wf.cmpFlags_frame
  testFlags_frame := toyArch_wf.testFlags_frame
  jnzGprFlags_frame := toyArch_wf.jnzGprFlags_frame
  prologueFlags_frame := fun _ _ _ _ => rfl
  epilogueFlags_frame := fun _ _ _ _ => rfl
  canonAbiFlags_frame := toyArch_wf.canonAbiFlags_frame

/-- Generic `FrameTarget` instantiated automatically for `.stack` convention `toyStackArch`. -/
def toyStackFrameTarget :
    FrameTarget (vllMach toyStackArch) (vllFrameIsa toyStackArch) toyStackArch.condReads :=
  vllFrameTarget toyStackArch toyStackArch_wf

/-! ## 2. L1 Program: Structured Loop + Hardware `call`/`ret` + `.native` + Indirect `ijmp` -/

@[expose] def demoSymAddr : Sym → BitVec 64
  | "main"       => 0x1000#64
  | "sum_loop"   => 0x1010#64
  | "loop_body"  => 0x1020#64
  | "loop_done"  => 0x1030#64
  | "after_call" => 0x1040#64
  | "dispatch"   => 0x1050#64
  | _            => 0#64

@[expose] def blkMain : Block toyArch where
  label := "main"
  pad? := some .btiJC
  body := [
    .movi .r1 0#64,
    .symAddr "dispatch" .r2
  ]
  term := .call "sum_loop" "after_call"

@[expose] def blkSumLoop : Block toyArch where
  label := "sum_loop"
  body := [.cmp .w64 .r0 (.imm 0#64)]
  term := .jcc .eq "loop_done" "loop_body"

@[expose] def blkLoopBody : Block toyArch where
  label := "loop_body"
  body := [
    .alu .add .w64 .r1 .r1 (.reg .r0),
    .alu .sub .w64 .r0 .r0 (.imm 1#64)
  ]
  term := .jmp "sum_loop"

@[expose] def blkLoopDone : Block toyArch where
  label := "loop_done"
  body := []
  term := .ret

@[expose] def blkAfterCall : Block toyArch where
  label := "after_call"
  body := [.native (.incR .r1)]
  term := .ijmp .r2

@[expose] def blkDispatch : Block toyArch where
  label := "dispatch"
  pad? := some .btiJ
  body := []
  term := .halt .r1

@[expose] def demoCodeMap : VllCodeMap toyArch where
  blocks := [blkMain, blkSumLoop, blkLoopBody, blkLoopDone, blkAfterCall, blkDispatch]
  symAddr := demoSymAddr
  addrTaken := ["main", "dispatch"]

theorem demoCodeMap_padsOk : demoCodeMap.padsOk = true := rfl
theorem demoCodeMap_labelsUnique : demoCodeMap.labelsUnique = true := rfl
theorem demoCodeMap_addrsUnique : demoCodeMap.addrsUnique = true := rfl

/-- Triangular sum `1 + 2 + … + n` modulo `2^64`. -/
@[expose] def triSum : Nat → BitVec 64
  | 0 => 0#64
  | n + 1 => BitVec.ofNat 64 (n + 1) + triSum n

private theorem bv64_toNat_sub_one {x : BitVec 64} (hne : x ≠ 0#64) :
    (x - 1#64).toNat = x.toNat - 1 ∧ 0 < x.toNat := by
  have hpos : 0 < x.toNat := by
    cases hx : x.toNat with
    | zero => exact absurd (BitVec.eq_of_toNat_eq hx) hne
    | succ k => exact Nat.succ_pos k
  have hle : (1#64 : BitVec 64) ≤ x :=
    BitVec.le_def.mpr (by simpa using Nat.succ_le_of_lt hpos)
  have hsub : (x - 1#64).toNat = x.toNat - 1 := by
    rw [BitVec.toNat_sub_of_le hle]; rfl
  exact ⟨hsub, hpos⟩

/-- Ranked `Xcap.wp` proof of `demoCodeMap`: exercises `VllCodeMap.wp_of_ranked`, hardware
`call`/`ret`, loop termination, `.native`, and indirect `ijmp`. -/
theorem demo_wp (target : BitVec 64) (s : MachSt toyArch)
    (ht : target = triSum (s.gpr .r0).toNat + 1#64) :
    demoCodeMap.wp (fun c _ => c = target) 0x1000#64 s := by
  let I : Nat → Xcap.CodeSpec (MachSt toyArch) := fun rank pc st =>
    (pc = 0x1000#64 ∧ rank = 2 * (st.gpr .r0).toNat + 5 ∧
      target = triSum (st.gpr .r0).toNat + 1#64) ∨
    (pc = 0x1010#64 ∧ rank = 2 * (st.gpr .r0).toNat + 4 ∧
      st.gpr .lr = 0x1040#64 ∧ st.gpr .r2 = 0x1050#64 ∧
      target = st.gpr .r1 + triSum (st.gpr .r0).toNat + 1#64) ∨
    (pc = 0x1020#64 ∧ rank = 2 * (st.gpr .r0).toNat + 3 ∧
      st.gpr .r0 ≠ 0#64 ∧ st.gpr .lr = 0x1040#64 ∧ st.gpr .r2 = 0x1050#64 ∧
      target = st.gpr .r1 + triSum (st.gpr .r0).toNat + 1#64) ∨
    (pc = 0x1030#64 ∧ rank = 3 ∧
      st.gpr .lr = 0x1040#64 ∧ st.gpr .r2 = 0x1050#64 ∧
      target = st.gpr .r1 + 1#64) ∨
    (pc = 0x1040#64 ∧ rank = 2 ∧
      st.gpr .r2 = 0x1050#64 ∧ target = st.gpr .r1 + 1#64) ∨
    (pc = 0x1050#64 ∧ rank = 1 ∧ target = st.gpr .r1)
  refine demoCodeMap.wp_of_ranked I ?_ (2 * (s.gpr .r0).toNat + 5) 0x1000#64 s
    (Or.inl ⟨rfl, rfl, ht⟩)
  rintro rank pc st (hMain | hLoop | hBody | hDone | hAfter | hDisp)
  · rcases hMain with ⟨rfl, rfl, htar⟩
    refine ⟨blkMain, rfl, bwp_of_bodyWp ?_⟩
    apply instrWp_movi
    apply instrWp_symAddr
    refine termWp_call_linkReg (lr := ToyReg.lr) rfl ?_
    refine ⟨2 * (st.gpr .r0).toNat + 4, by omega, Or.inr (Or.inl ?_)⟩
    refine ⟨rfl, ?_, rfl, rfl, ?_⟩
    · simp [MachSt.setGpr]
    · simp [MachSt.setGpr, htar]
  · rcases hLoop with ⟨rfl, rfl, hlr, hr2, htar⟩
    refine ⟨blkSumLoop, rfl, bwp_of_bodyWp ?_⟩
    apply instrWp_cmp
    refine termWp_jcc ?_ ?_
    · intro heq
      have h0 : st.gpr .r0 = 0#64 := by
        simpa [toyArch, Src.evalW, Src.eval, MachSt.flags_setFlags, BitVec.setWidth_eq] using heq
      refine ⟨3, by omega, Or.inr (Or.inr (Or.inr (Or.inl ?_)))⟩
      refine ⟨rfl, rfl, hlr, hr2, ?_⟩
      simpa [h0, triSum] using htar
    · intro hne
      have hnz : st.gpr .r0 ≠ 0#64 := by
        intro hz
        simp [toyArch, Src.evalW, Src.eval, hz] at hne
      refine ⟨2 * (st.gpr .r0).toNat + 3, by omega, Or.inr (Or.inr (Or.inl ?_))⟩
      exact ⟨rfl, rfl, hnz, hlr, hr2, htar⟩
  · rcases hBody with ⟨rfl, rfl, hnz, hlr, hr2, htar⟩
    refine ⟨blkLoopBody, rfl, bwp_of_bodyWp ?_⟩
    apply instrWp_alu
    apply instrWp_alu
    refine termWp_jmp ?_
    obtain ⟨hdec, hpos⟩ := bv64_toNat_sub_one hnz
    have hsucc : (st.gpr .r0).toNat = ((st.gpr .r0).toNat - 1) + 1 := by omega
    have hbv : BitVec.ofNat 64 (((st.gpr .r0).toNat - 1) + 1) = st.gpr .r0 := by
      rw [← hsucc, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    have htri : triSum (st.gpr .r0).toNat = st.gpr .r0 + triSum ((st.gpr .r0).toNat - 1) := by
      conv => lhs; rw [hsucc]
      simp only [triSum, hbv]
    refine ⟨2 * (st.gpr .r0 - 1#64).toNat + 4, by omega, Or.inr (Or.inl ?_)⟩
    refine ⟨rfl, ?_, ?_, ?_, ?_⟩
    · simp [toyArch, CoreAlu.eval, Src.evalW, Src.eval, MachSt.setGprW, MachSt.setGpr,
        writeSubZeroExtend]
    · simp [MachSt.setGprW, MachSt.setGpr, hlr]
    · simp [MachSt.setGprW, MachSt.setGpr, hr2]
    · simp only [toyArch, CoreAlu.eval, Src.evalW, Src.eval, MachSt.setGprW, MachSt.setGpr,
        writeSubZeroExtend, MachSt.gpr_setFlags, BitVec.setWidth_eq, reduceCtorEq, ↓reduceIte]
      rw [hdec, htar, htri]
      simp only [BitVec.add_assoc]
  · rcases hDone with ⟨rfl, rfl, hlr, hr2, htar⟩
    refine ⟨blkLoopDone, rfl, bwp_of_bodyWp ?_⟩
    refine termWp_ret_linkReg (lr := ToyReg.lr) rfl ?_
    refine ⟨2, by omega, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))⟩
    exact ⟨hlr, rfl, hr2, htar⟩
  · rcases hAfter with ⟨rfl, rfl, hr2, htar⟩
    refine ⟨blkAfterCall, rfl, bwp_of_bodyWp ?_⟩
    refine instrWp_native ⟨_, rfl⟩ ?_ (fun _ _ h => by cases h) (fun _ _ h => by cases h)
    intro s₁ hs₁
    cases hs₁
    refine termWp_ijmp ?_
    refine ⟨1, by omega, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_))))⟩
    exact ⟨by simpa using hr2, rfl, by simpa using htar⟩
  · rcases hDisp with ⟨rfl, rfl, htar⟩
    refine ⟨blkDispatch, rfl, bwp_of_bodyWp ?_⟩
    exact termWp_halt htar.symm

/-- End-to-end `Xcap.adequacy` on `demoCodeMap`: every initial state halts with
`triSum (s.gpr .r0).toNat + 1#64`. -/
theorem demo_adequate (s : MachSt toyArch) :
    ∃ c s', demoCodeMap.Halts 0x1000#64 s c s' ∧
      c = triSum (s.gpr .r0).toNat + 1#64 :=
  demoCodeMap.adequacy (demo_wp _ s rfl)

/-! ## 3. Open-Module `Xcap.ModOk.link` + `Xcap.ModOk.close` with `vllCallPre` -/

@[expose] def modSym : Sym → BitVec 64
  | "entry"  => 0x2000#64
  | "callee" => 0x2010#64
  | "exit"   => 0x2020#64
  | _        => 0#64

@[expose] def modCalleeBlk : Block toyArch :=
  { label := "callee", body := [.native (.incR .r0)], term := .ret }

@[expose] def modExitBlk : Block toyArch :=
  { label := "exit", body := [], term := .halt .r0 }

@[expose] def modEntryBlk : Block toyArch :=
  { label := "entry", body := [], term := .call "callee" "exit" }

@[expose] def codeCallee : Xcap.Code (Block toyArch) := fun pc =>
  if pc = 0x2010#64 then some modCalleeBlk else none

@[expose] def codeExit : Xcap.Code (Block toyArch) := fun pc =>
  if pc = 0x2020#64 then some modExitBlk else none

@[expose] def codeEntry : Xcap.Code (Block toyArch) := fun pc =>
  if pc = 0x2000#64 then some modEntryBlk else none

@[expose] def calleeSpec (v : BitVec 64) : Xcap.CodeSpec (MachSt toyArch) → MachSt toyArch → Prop :=
  vllCallPre toyArch (fun s => s.gpr .r0 = v) (fun s => s.gpr .r0 = v + 1#64)

theorem modCallee_ok (v : BitVec 64) :
    Xcap.ModOk (vllXcapMach toyArch modSym) codeCallee (fun c _ => c = v + 1#64)
      [] [(0x2010#64, calleeSpec v)] := by
  intro big Ψ hsub hcl _ e he
  simp only [List.mem_singleton] at he
  subst he
  intro s ⟨hr0, hret⟩
  refine hcl 0x2010#64 modCalleeBlk (hsub 0x2010#64 _ rfl) s (bwp_of_bodyWp ?_)
  refine instrWp_native ⟨_, rfl⟩ ?_ (fun _ _ h => by cases h) (fun _ _ h => by cases h)
  intro s₁ hs₁
  cases hs₁
  refine termWp_ret_linkReg (lr := ToyReg.lr) rfl ?_
  exact hret _ (by simp [hr0])

theorem modExit_ok (v : BitVec 64) :
    Xcap.ModOk (vllXcapMach toyArch modSym) codeExit (fun c _ => c = v + 1#64)
      [] [(0x2020#64, fun _ s => s.gpr .r0 = v + 1#64)] := by
  intro big Ψ hsub hcl _ e he
  simp only [List.mem_singleton] at he
  subst he
  intro s hr0
  refine hcl 0x2020#64 modExitBlk (hsub 0x2020#64 _ rfl) s (bwp_of_bodyWp ?_)
  exact termWp_halt hr0

theorem modEntry_ok (v : BitVec 64) :
    Xcap.ModOk (vllXcapMach toyArch modSym) codeEntry (fun c _ => c = v + 1#64)
      [(0x2010#64, calleeSpec v), (0x2020#64, fun _ s => s.gpr .r0 = v + 1#64)]
      [(0x2000#64, fun _ s => s.gpr .r0 = v)] := by
  intro big Ψ hsub hcl himp e he
  simp only [List.mem_singleton] at he
  subst he
  intro s hr0
  have hcal := himp (0x2010#64, calleeSpec v) List.mem_cons_self
  have hexit := himp (0x2020#64, fun _ s => s.gpr .r0 = v + 1#64)
    (List.mem_cons_of_mem _ List.mem_cons_self)
  refine hcl 0x2000#64 modEntryBlk (hsub 0x2000#64 _ rfl) s (bwp_of_bodyWp ?_)
  exact termWp_call_cptr_linkReg (lr := ToyReg.lr) rfl hcal (by simp [MachSt.setGpr]; exact hr0)
    hexit

theorem linked_vll_adequate (v : BitVec 64) (s : MachSt toyArch) (hr0 : s.gpr .r0 = v) :
    ∃ c s', Xcap.Halts (vllXcapMach toyArch modSym)
      (Xcap.union (Xcap.union codeCallee codeExit) codeEntry) 0x2000#64 s c s' ∧
      c = v + 1#64 := by
  have h12 := Xcap.ModOk.link (modCallee_ok v) (modExit_ok v)
    (fun pc => by by_cases h : pc = 0x2010#64 <;> simp [codeCallee, codeExit, h])
    (fun _ h => nomatch h)
  have h123 := Xcap.ModOk.link h12 (modEntry_ok v)
    (fun pc => by
      by_cases h1 : pc = 0x2010#64 <;> by_cases h2 : pc = 0x2020#64 <;>
        simp [Xcap.union, codeCallee, codeExit, codeEntry, h1, h2])
    (fun e he => Or.inl he)
  exact Xcap.adequacy (Xcap.ModOk.close h123 (e := (0x2000#64, fun _ s => s.gpr .r0 = v))
    (by simp) (fun _ => hr0))

/-! ## 4. Small-Step `vllMach` Multi-Step Execution Test -/

@[expose] def smallProg : List (Instr toyArch) := [
  .label "f",
  .movi .r0 41#64,
  .native (.incR .r0),
  .call "id",
  .ijmp .r2,
  .label "id",
  .ret
]

@[expose] def smallHost : VllHost toyArch where
  prog := smallProg
  addrOf k := BitVec.ofNat 64 (4 * k)
  labelAddr l := if l == "f" then 0#64 else if l == "id" then 20#64 else 0#64
  addrOf_inj := by
    intro i j hi hj heq
    have hi' : i < 7 := hi
    have hj' : j < 7 := hj
    have hnat := congrArg BitVec.toNat heq
    simp only [BitVec.toNat_ofNat] at hnat
    omega
  labelAddr_wf := by
    intro k l hk hfirst
    have hklt : k < 7 := Nat.lt_of_not_le fun hge => by
      have hnone : smallProg[k]? = none := List.getElem?_eq_none (by simpa [smallProg] using hge)
      rw [hnone] at hk; cases hk
    rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 by omega) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · cases hk; rfl
    · cases hk
    · cases hk
    · cases hk
    · cases hk
    · cases hk; rfl
    · cases hk

theorem smallHost_run (s : MachSt toyArch) :
    (vllMach toyArch).Run smallHost 0 s
      (fun st => st.pc = s.gpr .r2 ∧ st.data.gpr .r0 = 42#64) := by
  apply vllMach_label_spec (l := "f") rfl
  apply vllMach_movi_spec (rd := ToyReg.r0) (imm := 41#64) (List.isInfixAt_singleton.mpr rfl)
  intro s1 ⟨hr0_1, _⟩ hfr1
  apply vllMach_native_fallsTo (A := toyArch) (d := ToyNative.incR .r0)
    (gClob := [ToyReg.r0]) (vClob := []) (fClob := FlagMask.none)
    (Q := fun s' => s'.gpr .r0 = 42#64)
    ⟨_, rfl⟩
    (fun s' hs' => by
      cases hs'
      have hr0_1' : s1.gpr .r0 = 41#64 := hr0_1
      exact ⟨by simp [hr0_1'],
        ⟨fun q hq => by
          have hne : q ≠ .r0 := fun e => hq (e ▸ List.mem_cons_self)
          dsimp only [vllMach]
          simp [hne], fun _ _ => rfl, fun _ _ => rfl⟩⟩)
    (fun _ _ h => by cases h) (fun _ _ h => by cases h)
    (List.isInfixAt_singleton.mpr rfl)
  intro s2 hr0_2 hfr2
  have hm2 : (s2.mem =⋆ region (s2.gpr .sp - 0#64) 0 ⋆ Eq s2.mem) := by
    rw [BitVec.sub_zero, region_zero, Std.ExtHashMap.emp_sep]
  refine vllMach_call_spec toyArch_wf (sym := "id") (List.isInfixAt_singleton.mpr rfl) hm2 ?_
  intro s3 _ hfr3 hra3 _
  have hm3 : (s3.mem =⋆ (vllFramePreds toyArch).RetAddr (s3.gpr .sp) (smallHost.addrOf 4) ⋆
      Eq s3.mem) := by
    simp only [vllFramePreds, toyArch, region_zero, Std.ExtHashMap.emp_sep]
  have hid : smallHost.labelAddr "id" = smallHost.addrOf 5 := rfl
  rw [hid]
  apply vllMach_label_spec (l := "id") rfl
  refine vllMach_ret_spec (List.isInfixAt_singleton.mpr rfl) hra3 hm3 ?_
  intro s4 hk4 _ _ _
  apply vllMach_ijmp_spec (r := ToyReg.r2) (List.isInfixAt_singleton.mpr rfl)
  apply Eventually.done
  have hr2_4 : s4.gpr .r2 = s.gpr .r2 := by
    have h4 : s4.gpr .r2 = s3.gpr .r2 := hk4 .r2 (by decide)
    have h3 : s3.gpr .r2 = s2.gpr .r2 := hfr3.1 .r2 (by decide)
    have h2 : s2.gpr .r2 = s1.gpr .r2 := hfr2.1 .r2 (by decide)
    have h1 : s1.gpr .r2 = s.gpr .r2 := hfr1.1 .r2 (by decide)
    rw [h4, h3, h2, h1]
  have hr0_4 : s4.gpr .r0 = 42#64 := by
    have h4 : s4.gpr .r0 = s3.gpr .r0 := hk4 .r0 (by decide)
    have h3 : s3.gpr .r0 = s2.gpr .r0 := hfr3.1 .r0 (by decide)
    rw [h4, h3]; exact hr0_2
  exact ⟨hr2_4, hr0_4⟩

end LeanQbeTest.T.VllCoreTest

#print axioms LeanQbe.T.Vll.writeSubX64_setWidth
#print axioms LeanQbe.T.Vll.LoadExt.apply_gprHolds
#print axioms LeanQbe.T.Vll.VllCodeMap.lookupPc_of_wf
#print axioms LeanQbe.T.Vll.vllFrameTarget
#print axioms LeanQbe.T.Vll.bwp_of_bodyWp
#print axioms LeanQbe.T.Vll.VllCodeMap.adequacy
#print axioms LeanQbe.T.Vll.vllMach_run_of_bodyWp
#print axioms LeanQbeTest.T.VllCoreTest.toyFrameTarget
#print axioms LeanQbeTest.T.VllCoreTest.toyStackFrameTarget
#print axioms LeanQbeTest.T.VllCoreTest.demo_adequate
#print axioms LeanQbeTest.T.VllCoreTest.linked_vll_adequate
#print axioms LeanQbeTest.T.VllCoreTest.smallHost_run
