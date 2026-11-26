module

public import LeanQbe.T.Amd64.VllAsmX64Lemmas
import LeanQbe.T.Amd64.IselLemmas1
import LeanQbe.T.Logic.MemLemmas
meta import Lean
meta import LeanQbe.T.Amd64.VllX64
meta import LeanQbe.T.Amd64.VllAsmX64
meta import LeanQbe.T.Amd64.VllAsmX64Lemmas0
meta import LeanQbe.T.Amd64.VllAsmX64Lemmas1
meta import LeanQbe.T.Amd64.VllAsmX64Lemmas

/-! # Smoke Tests & Audit for `Amd64.VllX64` / `Amd64.VllAsmX64` (`VllAsmX64Test`) -/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.VllAsmX64Test

open LeanQbe.T LeanQbe.T.Amd64 LeanQbe.T.Vll Std

/-! ## 1. Concrete `VllCodeMap` & 1:1 Assembler Structural Checks -/

example : (asmX64 (.pad .endbr)).length = 1 := rfl
example : asmX64 (.load .w32 .zx .rax (.baseDisp .rsi 0)) =
    [ins32 (.mov (.reg (d .rax)) (.mem (atReg .rsi)))] := rfl
example : asmX64 (.store .w16 .rdi (.baseDisp .rsi 8)) =
    [ins16 (.mov (.mem (atDisp .rsi 8)) (.reg (h16 .rdi)))] := rfl
example : asmX64 (.slotSt 1 .rax) = x64SlotSt 1 .rax := rfl
example : asmX64 (.slotLd .rdi 2) = x64SlotLd .rdi 2 := rfl
example : asmX64 (.native (.label "n")) = [Kraken.Directive.label "n"] := rfl
example : (asmX64 (.call "callee")).length = 1 := rfl
example : (asmX64 (.icall .rax)).length = 1 := rfl
example : (asmX64 (.jcc .z "L")).length = 1 := rfl
example : (asmX64 (.tailJmpR .rcx)).length = 1 := rfl
example : (asmX64 (.ijmp .rdx)).length = 1 := rfl

/-! ## 2. Test 1: ALU, Flags, `pad`, `.native`, `jnzGpr`, `ijmp`, `exitJmp` -/

theorem noScratch_of_all {xs : List Reg64}
    (h : xs.all (fun r => r != .r10 && r != .r11) = true) : ∀ r ∈ xs, r ∉ x64Scratch := by
  intro r hr hc; have hb := List.all_eq_true.mp h r hr
  simp only [x64Scratch, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> simp at hb

theorem execBody_nil_eq {A : Arch} {sym : Sym → BitVec 64} {s s' : MachSt A}
    (h : ExecBody A sym [] s (.fall s')) : s' = s := by cases h; rfl

theorem execBody_cons {A : Arch} {sym : Sym → BitVec 64} {i : Vll.Instr A} {is s out}
    (h : ExecBody A sym (i :: is) s (.fall out)) :
    ∃ s₁, instrRel A sym 0#64 i s (.fall s₁) ∧ ExecBody A sym is s₁ (.fall out) := by
  cases h with | cons_fall h1 h2 => exact ⟨_, h1, h2⟩

theorem term1_infix {h : Host} {k : Nat} {i : Vll.Instr x64Arch}
    (ht : (asmX64List [i]).IsInfixAt Host.prog k) : (asmX64 i).IsInfixAt Host.prog k := by
  simpa [asmX64List] using ht

theorem term2_infix_fst {h : Host} {k : Nat} {i₁ i₂ : Vll.Instr x64Arch}
    (ht : (asmX64List [i₁, i₂]).IsInfixAt Host.prog k) : (asmX64 i₁).IsInfixAt Host.prog k := by
  rcases ht with ⟨rest, hr⟩; refine ⟨asmX64 i₂ ++ rest, ?_⟩
  simpa [asmX64List, List.append_assoc] using hr

theorem symAddr_eq {h : Host} {s : String} {k : Nat} (hl : hostLabel h s = Host.addrOf k) :
    Int64.ofBitVec (hostSymAddr h s) = Host.addrOf k := by
  rw [hostSymAddr, Int64.ofBitVec_toBitVec, hl]

namespace AluIndirectTest

abbrev entryBlk : Block x64Arch where
  label := "entry"; pad? := some .endbr
  body :=
    [ .native (ins (.nop 1)), .clearFlags, .movi .rax 7#64
    , .alu .add .w64 .rax .rax (.imm 5#64) true, .alu .mul .w8 .rax .rax (.imm 3#64) false
    , .alu .shl .w32 .rcx .rax (.imm 2#64) false
    , .cmp .w64 .rax (.imm 36#64), .setcc .rdx .z, .symAddr "done" .rdi ]
  term := .jnzGpr .rdx "target" "dead"

abbrev deadBlk : Block x64Arch := { label := "dead", term := .exitJmp "err" }
abbrev targetBlk : Block x64Arch := { label := "target", pad? := some .endbr, term := .ijmp .rdi }
abbrev doneBlk : Block x64Arch := { label := "done", pad? := some .endbr, term := .exitJmp "halt" }
abbrev cm : VllCodeMap x64Arch :=
  { blocks := [entryBlk, deadBlk, targetBlk, doneBlk], symAddr _ := 0#64
  , addrTaken := ["target", "done"] }
#guard cm.padsOk ∧ cm.labelsUnique ∧ cm.bodiesStraightLine

abbrev prog : Program :=
  asmX64Prog cm ++ [Kraken.Directive.label "err", Kraken.Directive.label "halt"]
abbrev layout : Layout :=
  { start := 0x1000, instrSize := fun _ => 4, instrSize_pos := fun _ => by decide }
abbrev host : Host := .ofLayout prog layout (by decide)
attribute [local instance] host

theorem labelsUnique : host.LabelsUnique := Host.labelsUnique_of_nodup (by decide)
abbrev kTarget : Nat :=
  (asmX64Block (some "dead") entryBlk).length + (asmX64Block (some "target") deadBlk).length
abbrev kDone : Nat := kTarget + (asmX64Block (some "done") targetBlk).length
abbrev kHalt : Nat := (asmX64Prog cm).length + 1
theorem hlTarget : hostLabel host "target" = Host.addrOf kTarget :=
  Host.label_eq_addrOf_of_unique labelsUnique rfl
theorem hlDone : hostLabel host "done" = Host.addrOf kDone :=
  Host.label_eq_addrOf_of_unique labelsUnique rfl
theorem hlHalt : hostLabel host "halt" = Host.addrOf kHalt :=
  Host.label_eq_addrOf_of_unique labelsUnique rfl
theorem hcEntry : (asmX64Block (some "dead") entryBlk).IsInfixAt Host.prog 0 := ⟨_, rfl⟩
theorem hcTarget : (asmX64Block (some "done") targetBlk).IsInfixAt Host.prog kTarget := ⟨_, rfl⟩
theorem hcDone : (asmX64Block none doneBlk).IsInfixAt Host.prog kDone := ⟨_, rfl⟩

theorem nop_exec {sym : Sym → BitVec 64} {s : MachSt x64Arch} {o : InstrOut x64Arch}
    (h : instrRel x64Arch sym 0#64 (.native (ins (.nop 1))) s o) :
    ∃ s', o = .fall s' ∧ (∀ r, s'.gpr r = s.gpr r) ∧ s'.mem = s.mem := by
  rcases h with ⟨no, hns, hio⟩; obtain ⟨sk0, p, hr0, hv0, hf0, hm0, hbody⟩ := hns
  cases no with
  | fall s1 =>
    cases hio; obtain ⟨hg, _, _, hm⟩ := x64Arch_nativeEffectSound (ins (.nop 1)) sym s (.fall s1)
      ⟨sk0, p, hr0, hv0, hf0, hm0, hbody⟩
    exact ⟨s1, rfl,
      fun r => hg r (by simp [x64Arch, x64NativeEffect, x64OpNativeEffect]), hm rfl⟩
  | jump _ _ =>
    obtain ⟨_, hre, _⟩ := hbody
    simp only [Directive.interp, Instr.interp, Operation.interp] at hre
    cases hre with | require_exec h' => cases h'
  | halt _ _ => exact hbody.elim

theorem alu_indirect_e2e (sk : MachineData) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = hostLabel host "halt" ∧
        st.data.regs.get64 .rax = 36#64 ∧ st.data.regs.get64 .rcx = 144#64)
      ⟨sk, Host.addrOf 0⟩ := by
  let sv0 := krakenToMachData sk
  have hbody : VllListPre host (0 + (asmX64List [.label "entry", .pad .endbr]).length)
      maskAll sv0 sk entryBlk.body := by
    dsimp only [entryBlk]
    refine ⟨⟨⟨fun _ => rfl, fun _ => rfl, rfl, fun _ => rfl⟩,
        by simp [t_step_simp, Effects.All]⟩, fun _ _ _ _ _ => ?_⟩
    repeat refine ⟨⟨rfl, noScratch_of_all (by decide), trivial⟩, fun _ _ _ _ _ => ?_⟩
    refine ⟨⟨rfl, noScratch_of_all (by decide),
        by simp [x64CondReads, FlagMask.disjoint, nextFlagMask, maskNone, maskZF]⟩,
      fun _ _ _ _ _ => ?_⟩
    exact ⟨⟨rfl, noScratch_of_all (by decide), trivial⟩, fun _ _ _ _ _ => trivial⟩
  refine asmX64Block_run (some "dead") entryBlk hcEntry
    (SimState_maskAll (fun _ _ => rfl) (fun _ => rfl) rfl) hbody ?_
  intro _ _ sv9 sk9 hex9 hsim9 _ hterm9
  obtain ⟨_, h1, hex1⟩ := execBody_cons hex9; rcases nop_exec h1 with ⟨sv1, hno, _⟩; cases hno
  obtain ⟨_, h2, hex2⟩ := execBody_cons hex1; cases h2
  obtain ⟨_, h3, hex3⟩ := execBody_cons hex2; cases h3
  obtain ⟨_, h4, hex4⟩ := execBody_cons hex3; cases h4
  obtain ⟨_, h5, hex5⟩ := execBody_cons hex4; cases h5
  obtain ⟨_, h6, hex6⟩ := execBody_cons hex5; cases h6
  obtain ⟨_, h7, hex7⟩ := execBody_cons hex6; cases h7
  obtain ⟨_, h8, hex8⟩ := execBody_cons hex7; cases h8
  obtain ⟨_, h9, hex9'⟩ := execBody_cons hex8; cases h9
  have hsv9 := execBody_nil_eq hex9'
  have hsw : BitVec.setWidth 8 12#64 = 12#8 ∧ BitVec.setWidth 8 3#64 = 3#8 ∧
      BitVec.setWidth 32 36#64 = 36#32 ∧ BitVec.setWidth 32 2#64 = 2#32 := ⟨rfl, rfl, rfl, rfl⟩
  have hev : CoreAlu.add.eval .w64 7#64 5#64 = 12#64 ∧ CoreAlu.mul.eval .w8 12#8 3#8 = 36#8 ∧
      CoreAlu.shl.eval .w32 36#32 2#32 = 144#32 := by decide
  have hws : writeSubX64 .w64 7#64 12#64 = 12#64 ∧ writeSubX64 .w8 12#64 36#8 = 36#64 :=
    ⟨rfl, by decide⟩
  have hshl : ∀ old, writeSubX64 .w32 old 144#32 = 144#64 := fun _ => by simp [writeSubX64]
  have hcmpz : ∀ f, CondCode.z.interp (x64CmpFlags .w64 36#64 36#64 f) = true := fun _ => by
    simp [x64CmpFlags, StatusFlags.from_result, CondCode.interp, BitVec.zero]
  have hrax : sv9.gpr .rax = 36#64 := by
    simp [hsv9, MachSt.setGpr, MachSt.setGprW, MachSt.setFlags, x64Arch, Src.evalW, Src.eval,
      BitVec.setWidth_eq, hsw.1, hsw.2.1, hev.1, hws.1, hev.2.1, hws.2]
  have hrcx : sv9.gpr .rcx = 144#64 := by
    simp [hsv9, MachSt.setGpr, MachSt.setGprW, MachSt.setFlags, x64Arch, Src.evalW, Src.eval,
      BitVec.setWidth_eq, hsw.1, hsw.2.1, hsw.2.2.1, hsw.2.2.2, hev.1, hws.1, hev.2.1, hws.2,
      hev.2.2, hshl]
  have hrdx : (sv9.gpr .rdx).setWidth 8 = 1#8 := by
    simp [hsv9, MachSt.setGpr, MachSt.setGprW, MachSt.setFlags, x64Arch, Src.evalW, Src.eval,
      BitVec.setWidth_eq, hsw.1, hsw.2.1, hev.1, hws.1, hev.2.1, hws.2, hcmpz]
    exact writeSubX64_setWidth .w8 _ _
  have hrdi : sv9.gpr .rdi = hostSymAddr host "done" := by simp [hsv9, MachSt.setGpr]
  refine asmX64_jnzGpr_run (term1_infix hterm9) hsim9 (by simp [x64Scratch]) (fun _ h0 _ _ => ?_)
    (fun sk10 h0 hsim10 _ => ?_)
  · exact absurd h0 (by rw [hrdx]; decide)
  · rw [symAddr_eq hlTarget]
    refine asmX64Block_run (some "done") targetBlk hcTarget hsim10 trivial ?_
    intro _ _ sv11 sk11 hex11 hsim11 _ hterm11; cases hex11
    refine asmX64_ijmp_run (term1_infix hterm11) hsim11 (by simp [x64Scratch]) ?_
    simp only [MachSt.gpr_setFlags, hrdi]; rw [symAddr_eq hlDone]
    refine asmX64Block_run none doneBlk hcDone hsim11 trivial ?_
    intro _ _ sv12 sk12 hex12 hsim12 _ hterm12; cases hex12
    refine asmX64_exitJmp_run (term1_infix hterm12) ?_
    rw [symAddr_eq hlHalt]
    exact .done _ ⟨hlHalt.symm, (hsim12.1 .rax (by simp [x64Scratch])).trans hrax,
      (hsim12.1 .rcx (by simp [x64Scratch])).trans hrcx⟩

end AluIndirectTest

/-! ## 3. Test 2: `prologue`, `slotSt`, `slotLd`, `canonAbi`, `epilogue`, `icall`, `ret`, `tail` -/

namespace CallSlotTailTest

abbrev callerBlk : Block x64Arch where
  label := "caller"; pad? := some .endbr
  body := [.mov .w32 .rdi .rsi, .symAddr "callee" .rcx]
  term := .icall .rcx "after"

abbrev calleeBlk : Block x64Arch where
  label := "callee"; pad? := some .endbr
  body := [.prologue 1, .slotSt 0 .rdi, .slotLd .rax 0, .canonAbi i16 .rax, .epilogue 1]
  term := .ret

abbrev afterBlk : Block x64Arch :=
  { label := "after", body := [.symAddr "exit" .r9], term := .tailJmpR .r9 }
abbrev cm : VllCodeMap x64Arch :=
  { blocks := [callerBlk, calleeBlk, afterBlk], symAddr _ := 0#64, addrTaken := ["callee"] }
#guard cm.padsOk ∧ cm.labelsUnique ∧ cm.bodiesStraightLine

abbrev prog : Program := asmX64Prog cm ++ [Kraken.Directive.label "exit"]
abbrev layout : Layout :=
  { start := 0x2000, instrSize := fun _ => 4, instrSize_pos := fun _ => by decide }
abbrev host : Host := .ofLayout prog layout (by decide)
attribute [local instance] host

theorem labelsUnique : host.LabelsUnique := Host.labelsUnique_of_nodup (by decide)
abbrev kRetStub : Nat :=
  0 + (asmX64List ((.label "caller" :: [.pad .endbr]) ++ callerBlk.body)).length + 1
abbrev kCallee : Nat := (asmX64Block (some "callee") callerBlk).length
abbrev kAfter : Nat := kCallee + (asmX64Block (some "after") calleeBlk).length
abbrev kExit : Nat := (asmX64Prog cm).length
theorem hlCallee : hostLabel host "callee" = Host.addrOf kCallee :=
  Host.label_eq_addrOf_of_unique labelsUnique rfl
theorem hlAfter : hostLabel host "after" = Host.addrOf kAfter :=
  Host.label_eq_addrOf_of_unique labelsUnique rfl
theorem hlExit : hostLabel host "exit" = Host.addrOf kExit :=
  Host.label_eq_addrOf_of_unique labelsUnique rfl
theorem hcCaller : (asmX64Block (some "callee") callerBlk).IsInfixAt Host.prog 0 := ⟨_, rfl⟩
theorem hcCallee : (asmX64Block (some "after") calleeBlk).IsInfixAt Host.prog kCallee := ⟨_, rfl⟩
theorem hcAfter : (asmX64Block none afterBlk).IsInfixAt Host.prog kAfter := ⟨_, rfl⟩

theorem call_slot_tail_e2e (sk : MachineData) (v0 v1 : BitVec 64) {R : Mem 64 → Prop}
    (hm : (cell64 (sk.regs.get64 .rsp - 8#64) v0 ⋆
        (cell64 (sk.regs.get64 .rsp - 16#64) v1 ⋆ R)) sk.dmem) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = hostLabel host "exit" ∧
        st.data.regs.get64 .rax = ((sk.regs.get64 .rsi).setWidth 16).setWidth 64 ∧
        st.data.regs.get64 .rsp = sk.regs.get64 .rsp)
      ⟨sk, Host.addrOf 0⟩ := by
  let rsp0 := sk.regs.get64 .rsp
  let sv0 := krakenToMachData sk
  have hbody1 : VllListPre host (0 + (asmX64List [.label "caller", .pad .endbr]).length)
      maskAll sv0 sk callerBlk.body := by
    dsimp only [callerBlk]
    exact ⟨⟨rfl, noScratch_of_all (by decide), trivial⟩,
      fun _ _ _ _ _ => ⟨⟨rfl, noScratch_of_all (by decide), trivial⟩, fun _ _ _ _ _ => trivial⟩⟩
  refine asmX64Block_run (some "callee") callerBlk hcCaller
    (SimState_maskAll (fun _ _ => rfl) (fun _ => rfl) rfl) hbody1 ?_
  intro _ _ sv2 sk2 hex2 hsim2 _ hterm2
  obtain ⟨_, ha, hex2'⟩ := execBody_cons hex2; cases ha
  obtain ⟨_, hb, hex2''⟩ := execBody_cons hex2'; cases hb
  have hsv2 := execBody_nil_eq hex2''
  have hrsp2 : sv2.gpr .rsp = rsp0 := by simp [hsv2, sv0, krakenToMachData, rsp0]
  have hmem2 : sv2.mem = sk.dmem := by simp [hsv2, sv0, krakenToMachData]
  obtain ⟨hst_ic, hm_ic⟩ := store_cell64 (Host.addrOf kRetStub).toBitVec hm
  refine asmX64_icall_run (term2_infix_fst hterm2) hsim2 (by simp [x64Scratch])
    (by simpa [hsv2, sv0, krakenToMachData] using hst_ic) fun sk3 hsim3 _ => ?_
  let sv3 := (sv2.setGpr .rsp (sv2.gpr .rsp - 8#64)).setMem (storeMem sv2.mem i64
    (sv2.gpr .rsp - 8#64) (Host.addrOf kRetStub).toBitVec)
  have hrsp3 : sv3.gpr .rsp = rsp0 - 8#64 := by simp [sv3, hrsp2]
  have hm_ic' : (cell64 (rsp0 - 8#64) (Host.addrOf kRetStub).toBitVec ⋆
      (cell64 (rsp0 - 16#64) v1 ⋆ R)) sv3.mem := by
    simpa [sv3, hrsp2, hmem2, rsp0] using hm_ic
  have hslot_addr : sv3.gpr .rsp - BitVec.ofNat 64 (x64FrameSize 1) +
      BitVec.ofNat 64 (8 * 0) = rsp0 - 16#64 := by
    rw [hrsp3]; dsimp only [x64FrameSize]
    rw [show (8 * 1 + if 1 % 2 == 0 then 8 else 0) = 8 from rfl, BitVec.sub_sub]; simp
  have hm_slot : (cell64 (rsp0 - 16#64) v1 ⋆
      (cell64 (rsp0 - 8#64) (Host.addrOf kRetStub).toBitVec ⋆ R)) sv3.mem :=
    sep_cast hm_ic' (by ac_rfl)
  obtain ⟨hst_sl, hm_sl⟩ := store_cell64 (sv3.gpr .rdi) hm_slot
  have hbody2 : VllListPre host
      (kCallee + (asmX64List [.label "callee", .pad .endbr]).length)
      maskAll sv3 sk3 calleeBlk.body := by
    dsimp only [calleeBlk]
    refine ⟨⟨rfl, noScratch_of_all (by decide), trivial⟩, fun sv4 _ ha4 _ _ => ?_⟩; cases ha4
    refine ⟨⟨rfl, noScratch_of_all (by decide), by simpa [hslot_addr, x64Arch] using hst_sl⟩,
      fun sv5 _ hb5 _ _ => ?_⟩
    obtain ⟨_, hb5⟩ := hb5; cases hb5
    refine ⟨⟨rfl, noScratch_of_all (by decide),
        ⟨sv3.gpr .rdi, (by simpa [hslot_addr, x64Arch] using loadVal_cell64 hm_sl)⟩⟩,
      fun _ _ _ _ _ => ?_⟩
    exact ⟨⟨rfl, noScratch_of_all (by decide), by simp⟩,
      fun _ _ _ _ _ => ⟨⟨rfl, noScratch_of_all (by decide), trivial⟩, fun _ _ _ _ _ => trivial⟩⟩
  have hrcx2 : sv2.gpr .rcx = hostSymAddr host "callee" := by simp [hsv2]
  rw [hrcx2, symAddr_eq hlCallee]
  refine asmX64Block_run (some "after") calleeBlk hcCallee
    (show SimState maskAll sv3 sk3 from hsim3) hbody2 ?_
  intro _ _ sv8 sk8 hex8 hsim8 _ hterm8
  obtain ⟨_, ha, hex8'⟩ := execBody_cons hex8; cases ha
  obtain ⟨_, hb, hex8''⟩ := execBody_cons hex8'; obtain ⟨_, hb⟩ := hb; cases hb
  obtain ⟨_, hc, hex8'''⟩ := execBody_cons hex8''; obtain ⟨vld, hvld, hc⟩ := hc; cases hc
  obtain ⟨_, hd, hex8''''⟩ := execBody_cons hex8'''; cases hd
  obtain ⟨_, he, hex8'''''⟩ := execBody_cons hex8''''; cases he
  have hsv8 := execBody_nil_eq hex8'''''
  have hslot_eq : sv8.gpr .rsp = rsp0 - 8#64 := by
    simp [hsv8, x64Arch, x64FrameSize, hrsp3, BitVec.sub_add_cancel]
  have hm_ret : (cell64 (rsp0 - 8#64) (Host.addrOf kRetStub).toBitVec ⋆
      (cell64 (rsp0 - 16#64) (sv3.gpr .rdi) ⋆ R))
      (storeMem sv3.mem i64 (rsp0 - 16#64) (sv3.gpr .rdi)) := sep_cast hm_sl (by ac_rfl)
  have hld_ret : loadVal sv8.mem i64 (sv8.gpr .rsp) = some (Host.addrOf kRetStub).toBitVec := by
    rw [hslot_eq]
    simpa [hsv8, x64Arch, hslot_addr,
      show (sv3.setGpr .rsp (sv3.gpr .rsp - BitVec.ofNat 64 (x64FrameSize 1))).gpr .rdi =
        sv3.gpr .rdi from rfl] using loadVal_cell64 hm_ret
  have hvld_eq : vld = sv3.gpr .rdi := by
    have h0 := loadVal_cell64 hm_sl
    simp only [MachSt.mem_setMem, MachSt.mem_setFlags, MachSt.mem_setGpr, MachSt.gpr_setMem,
      MachSt.gpr_setFlags, MachSt.gpr_setGpr_same, x64Arch] at hvld
    rw [show (sv3.setGpr .rsp (sv3.gpr .rsp - BitVec.ofNat 64 (x64FrameSize 1))).gpr .rdi =
        sv3.gpr .rdi from rfl, hslot_addr] at hvld
    exact Option.some.inj (hvld.symm.trans h0)
  have hrax8 : sv8.gpr .rax = ((sk.regs.get64 .rsi).setWidth 16).setWidth 64 := by
    have hrdi3 : sv3.gpr .rdi = ((sk.regs.get64 .rsi).setWidth 32).setWidth 64 := by
      simp [sv3, hsv2, sv0, krakenToMachData, x64Arch, writeSubX64]
    simp [hsv8, hvld_eq, hrdi3, canonAbiVal, x64Arch]
  refine asmX64_ret_run (term1_infix hterm8) hsim8 hld_ret fun sk9 hsim9 _ => ?_
  rw [Int64.ofBitVec_toBitVec]
  let sv9 := sv8.setGpr .rsp (sv8.gpr .rsp + 8#64)
  have hj_stub : (asmX64 (.jmp "after")).IsInfixAt Host.prog kRetStub :=
    List.isInfixAt_singleton.mpr rfl
  refine asmX64_jmp_run (fMask := maskNone) (sv := sv9) hj_stub ?_
  rw [symAddr_eq hlAfter]
  have hbody3 : VllListPre host (kAfter + (asmX64List [.label "after"]).length)
      maskAll sv9 sk9 afterBlk.body := by
    dsimp only [afterBlk]
    exact ⟨⟨rfl, noScratch_of_all (by decide), trivial⟩, fun _ _ _ _ _ => trivial⟩
  refine asmX64Block_run none afterBlk hcAfter hsim9 hbody3 ?_
  intro _ _ sv10 sk10 hex10 hsim10 _ hterm10
  obtain ⟨_, hf, hex10'⟩ := execBody_cons hex10; cases hf
  have hsv10 := execBody_nil_eq hex10'
  refine asmX64_tailJmpR_run (term1_infix hterm10) hsim10 (by simp [x64Scratch]) ?_
  have hr9 : sv10.gpr .r9 = hostSymAddr host "exit" := by simp [hsv10, MachSt.setGpr]
  rw [hr9, symAddr_eq hlExit]
  exact .done _ ⟨hlExit.symm,
    (hsim10.1 .rax (by simp [x64Scratch])).trans (by simpa [hsv10, sv9] using hrax8),
    (hsim10.1 .rsp (by simp [x64Scratch])).trans
      (by simp [hsv10, hslot_eq, rsp0, BitVec.sub_add_cancel])⟩

end CallSlotTailTest

/-! ## 4. `#print axioms` & MetaM Closure / Kernel Audit -/

#print axioms LeanQbe.T.Amd64.x64Arch_wf
#print axioms LeanQbe.T.Amd64.x64Arch_nativeEffectSound
#print axioms LeanQbe.T.Amd64.asmX64_fallsTo
#print axioms LeanQbe.T.Amd64.asmX64List_fallsTo
#print axioms LeanQbe.T.Amd64.asmX64_jump
#print axioms LeanQbe.T.Amd64.asmX64Block_run
#print axioms AluIndirectTest.alu_indirect_e2e
#print axioms CallSlotTailTest.call_slot_tail_e2e

meta section
open Lean

private def allowedStdAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]
private def isForbiddenArchMod (m : Name) : Bool :=
  let s := m.toString; (s.splitOn "Arm64").length > 1 || s.startsWith "Kraken.AArch64"

#eval show MetaM Unit from do
  let mods : List Name := [`LeanQbe.T.Amd64.VllX64, `LeanQbe.T.Amd64.VllAsmX64,
    `LeanQbe.T.Amd64.VllAsmX64Lemmas0, `LeanQbe.T.Amd64.VllAsmX64Lemmas1,
    `LeanQbe.T.Amd64.VllAsmX64Lemmas]
  for mod in mods do
    let env ← importModules #[{ module := mod }] {}
    let bad := env.header.moduleNames.filter isForbiddenArchMod
    if !bad.isEmpty then throwError "Module {mod} imports Arm64/AArch64: {bad.toList}"
  let testBad := (← getEnv).header.moduleNames.filter isForbiddenArchMod
  if !testBad.isEmpty then throwError "VllAsmX64Test imports Arm64/AArch64: {testBad.toList}"
  let targets : List Name := [``LeanQbe.T.Amd64.x64Arch, ``LeanQbe.T.Amd64.x64Arch_wf,
    ``LeanQbe.T.Amd64.x64Arch_nativeEffectSound, ``LeanQbe.T.Amd64.asmX64,
    ``LeanQbe.T.Amd64.asmX64List,
    ``LeanQbe.T.Amd64.asmX64Block, ``LeanQbe.T.Amd64.asmX64Prog, ``LeanQbe.T.Amd64.asmX64_fallsTo,
    ``LeanQbe.T.Amd64.asmX64List_fallsTo, ``LeanQbe.T.Amd64.asmX64_jump,
    ``LeanQbe.T.Amd64.asmX64Block_run, ``AluIndirectTest.alu_indirect_e2e,
    ``CallSlotTailTest.call_slot_tail_e2e]
  let env ← getEnv
  for nm in targets do
    let some ci := env.find? nm | throwError "Missing {nm}"
    if ci.isUnsafe then throwError "Unsafe: {nm}"
    let badAx := (← Lean.collectAxioms nm).filter fun a => !allowedStdAxioms.contains a
    if !badAx.isEmpty then throwError "{nm} disallowed axioms: {badAx.toList}"

end
end LeanQbeTest.T.VllAsmX64Test
end
