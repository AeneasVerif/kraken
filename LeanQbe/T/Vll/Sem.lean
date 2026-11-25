module

public import LeanQbe.T.Vll.Syntax
public import LeanQbe.T.Xcap.Link
import LeanQbe.T.TargetLemmas
import LeanQbe.T.Logic.MemLemmas
import LeanQbe.T.AbiLemmas

/-!
# Target-Neutral `BedrockMach` L1 Semantics (`Vll.Sem`)

Operational semantics, `LeanQbe.T.Machine` instance, `FrameTarget` proof, and generic `Xcap.Mach`
instance for `BedrockMach` L1 VLLIR, parameterized by `A : Arch`:

* `MachSt A` (`MachData A.Reg A.VReg A.Flags`) with state updaters and simplification rules.
* Unified single-instruction relation `instrRel` covering every `Instr A` constructor, including
  hardware `.stack` / `.linkReg` `call`/`icall`/`ret`/`prologue`/`epilogue`, open `ijmp`,
  `symAddr`, `pad`, and the `.native d` escape hatch.
* `VllHost A`, `vllStep`, `vllMach (A : Arch) : Machine A.Reg A.VReg A.Cond (Instr A)`,
  `FallsTo` / `Run` step lemmas for every instruction, and generic `vllFrameTarget`.
* `ExecBody`, `termExec`, `BlockExec`, `vllXcapMach (A : Arch) (symAddr) : Xcap.Mach (MachSt A)
  (Block A)`, compositional `instrWp`/`bodyWp`/`termWp` rules (`bwp_of_bodyWp`), hardware-call
  XCAP `cptr` helpers (`vllCallPre`), `VllCodeMap` XCAP wrappers (`wp`, `adequacy`,
  `wp_of_ranked`), and straight-line `ExecBody` → `vllMach.Run` correspondence.

Zero `Kraken.X64`, `Kraken.AArch64`, `Amd64`, `Arm64`, or public `*Lemmas*` imports.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Vll

open LeanQbe.T
open Std Std.ExtHashMap

/-! ## 1. Machine State `MachSt A`, Configuration `Config A`, and State Updaters -/

/-- Architectural data state of `BedrockMach` L1 (`gpr`, `vreg`, `flags`, `mem`). -/
abbrev MachSt (A : Arch) : Type := MachData A.Reg A.VReg A.Flags

/-- Full small-step machine configuration (`data` + 64-bit `pc`). -/
structure Config (A : Arch) : Type where
  data : MachSt A
  pc : BitVec 64

/-- Update GPR `r` to full 64-bit word `v`. -/
@[expose] def MachSt.setGpr {A : Arch} (s : MachSt A) (r : A.Reg) (v : BitVec 64) : MachSt A :=
  { s with gpr := fun q => if q = r then v else s.gpr q }

/-- Update GPR `r` at sub-word width `w` via `A.writeSub`. -/
@[expose] def MachSt.setGprW {A : Arch} (s : MachSt A) (w : Width) (r : A.Reg)
    (v : BitVec w.bits) : MachSt A :=
  s.setGpr r (A.writeSub w (s.gpr r) v)

/-- Update vector register `vr` to 512-bit value `v`. -/
@[expose] def MachSt.setVec {A : Arch} (s : MachSt A) (vr : A.VReg) (v : BitVec 512) :
    MachSt A :=
  { s with vreg := fun q => if q = vr then v else s.vreg q }

/-- Update status flags to `f`. -/
@[expose] def MachSt.setFlags {A : Arch} (s : MachSt A) (f : A.Flags) : MachSt A :=
  { s with flags := f }

/-- Update partial memory to `m`. -/
@[expose] def MachSt.setMem {A : Arch} (s : MachSt A) (m : Mem 64) : MachSt A :=
  { s with mem := m }

@[simp] theorem MachSt.gpr_setGpr_same {A : Arch} (s : MachSt A) (r : A.Reg) (v : BitVec 64) :
    (s.setGpr r v).gpr r = v := by
  simp [MachSt.setGpr]

@[simp] theorem MachSt.gpr_setGpr_ne {A : Arch} (s : MachSt A) {r q : A.Reg} (v : BitVec 64)
    (h : q ≠ r) : (s.setGpr r v).gpr q = s.gpr q := by
  simp [MachSt.setGpr, h]

@[simp] theorem MachSt.vreg_setGpr {A : Arch} (s : MachSt A) (r : A.Reg) (v : BitVec 64) :
    (s.setGpr r v).vreg = s.vreg := rfl

@[simp] theorem MachSt.flags_setGpr {A : Arch} (s : MachSt A) (r : A.Reg) (v : BitVec 64) :
    (s.setGpr r v).flags = s.flags := rfl

@[simp] theorem MachSt.mem_setGpr {A : Arch} (s : MachSt A) (r : A.Reg) (v : BitVec 64) :
    (s.setGpr r v).mem = s.mem := rfl

@[simp] theorem MachSt.gpr_setGprW_same {A : Arch} (s : MachSt A) (w : Width) (r : A.Reg)
    (v : BitVec w.bits) : (s.setGprW w r v).gpr r = A.writeSub w (s.gpr r) v := by
  simp [MachSt.setGprW]

@[simp] theorem MachSt.gpr_setGprW_ne {A : Arch} (s : MachSt A) (w : Width) {r q : A.Reg}
    (v : BitVec w.bits) (h : q ≠ r) : (s.setGprW w r v).gpr q = s.gpr q := by
  simp [MachSt.setGprW, h]

@[simp] theorem MachSt.vreg_setGprW {A : Arch} (s : MachSt A) (w : Width) (r : A.Reg)
    (v : BitVec w.bits) : (s.setGprW w r v).vreg = s.vreg := rfl

@[simp] theorem MachSt.flags_setGprW {A : Arch} (s : MachSt A) (w : Width) (r : A.Reg)
    (v : BitVec w.bits) : (s.setGprW w r v).flags = s.flags := rfl

@[simp] theorem MachSt.mem_setGprW {A : Arch} (s : MachSt A) (w : Width) (r : A.Reg)
    (v : BitVec w.bits) : (s.setGprW w r v).mem = s.mem := rfl

@[simp] theorem MachSt.gpr_setFlags {A : Arch} (s : MachSt A) (f : A.Flags) :
    (s.setFlags f).gpr = s.gpr := rfl

@[simp] theorem MachSt.vreg_setFlags {A : Arch} (s : MachSt A) (f : A.Flags) :
    (s.setFlags f).vreg = s.vreg := rfl

@[simp] theorem MachSt.flags_setFlags {A : Arch} (s : MachSt A) (f : A.Flags) :
    (s.setFlags f).flags = f := rfl

@[simp] theorem MachSt.mem_setFlags {A : Arch} (s : MachSt A) (f : A.Flags) :
    (s.setFlags f).mem = s.mem := rfl

@[simp] theorem MachSt.gpr_setMem {A : Arch} (s : MachSt A) (m : Mem 64) :
    (s.setMem m).gpr = s.gpr := rfl

@[simp] theorem MachSt.vreg_setMem {A : Arch} (s : MachSt A) (m : Mem 64) :
    (s.setMem m).vreg = s.vreg := rfl

@[simp] theorem MachSt.flags_setMem {A : Arch} (s : MachSt A) (m : Mem 64) :
    (s.setMem m).flags = s.flags := rfl

@[simp] theorem MachSt.mem_setMem {A : Arch} (s : MachSt A) (m : Mem 64) :
    (s.setMem m).mem = m := rfl

/-! ## 2. Unified Single-Instruction Transition Relation (`instrRel`) -/

/-- Outcome of executing one `Instr A`. -/
inductive InstrOut (A : Arch) : Type where
  | fall (s' : MachSt A)
  | jump (pc' : BitVec 64) (s' : MachSt A)
  | halt (code : BitVec 64) (s' : MachSt A)

/-- Embed `NativeOutcome` into `InstrOut`. -/
@[expose] def NativeOutcome.toInstrOut {A : Arch} :
    NativeOutcome A.Reg A.VReg A.Flags → InstrOut A
  | .fall s' => .fall s'
  | .jump pc' s' => .jump pc' s'
  | .halt c s' => .halt c s'

/-- Canonical ABI zero-extension of a 64-bit register value for type `t`. -/
@[expose] def canonAbiVal (t : Ty) (v : BitVec 64) : BitVec 64 :=
  match t with
  | .bool => (v.setWidth 8).setWidth 64
  | .bits n => (v.setWidth n).setWidth 64
  | _ => v

/-- Relational single-instruction operational semantics shared by `vllMach` (small-step
`Machine`) and `vllXcapMach` (block-step `Xcap.Mach`).
`symAddr` resolves symbolic labels to 64-bit addresses; `nextPc` is the fall-through return
address pushed/written by hardware `call`/`icall`. -/
@[expose] def instrRel (A : Arch) (symAddr : Sym → BitVec 64) (nextPc : BitVec 64) :
    Instr A → MachSt A → InstrOut A → Prop
  | .label _, s, out => out = .fall s
  | .pad _, s, out => out = .fall s
  | .mov w rd rs, s, out =>
    out = .fall (s.setGprW w rd ((s.gpr rs).setWidth w.bits))
  | .movi rd imm, s, out =>
    out = .fall (s.setGpr rd imm)
  | .alu op w rd lhs rhs sf, s, out =>
    let a := (s.gpr lhs).setWidth w.bits
    let b := rhs.evalW w s.gpr
    let res := op.eval w a b
    let f' := A.aluFlags op w sf a b s.flags
    out = .fall ((s.setGprW w rd res).setFlags f')
  | .cmp w lhs rhs, s, out =>
    let a := (s.gpr lhs).setWidth w.bits
    let b := rhs.evalW w s.gpr
    out = .fall (s.setFlags (A.cmpFlags w a b s.flags))
  | .test w lhs rhs, s, out =>
    let a := (s.gpr lhs).setWidth w.bits
    let b := rhs.evalW w s.gpr
    out = .fall (s.setFlags (A.testFlags w a b s.flags))
  | .clearFlags, s, out =>
    out = .fall (s.setFlags A.clearFlagsVal)
  | .setcc rd c, s, out =>
    let b := A.evalCond s.flags c
    out = .fall (s.setGprW .w8 rd (BitVec.ofNat 8 b.toNat))
  | .load w ext rd addr, s, out =>
    ∃ v : BitVec w.bits, loadVal s.mem w.toTy (addr.eval s.gpr) = some v ∧
      out = .fall (s.setGpr rd (ext.apply A w (s.gpr rd) v))
  | .store w rs addr, s, out =>
    let a := addr.eval s.gpr
    storeOk s.mem w.toTy a ∧
      out = .fall (s.setMem (storeMem s.mem w.toTy a ((s.gpr rs).setWidth w.bits)))
  | .slotSt i rs, s, out =>
    let a := s.gpr A.abi.sp + BitVec.ofNat 64 (8 * i)
    storeOk s.mem i64 a ∧ out = .fall (s.setMem (storeMem s.mem i64 a (s.gpr rs)))
  | .slotLd rd i, s, out =>
    let a := s.gpr A.abi.sp + BitVec.ofNat 64 (8 * i)
    ∃ v : BitVec 64, loadVal s.mem i64 a = some v ∧ out = .fall (s.setGpr rd v)
  | .prologue ns, s, out =>
    let fsz := A.abi.frameSize ns
    let sp' := s.gpr A.abi.sp - BitVec.ofNat 64 fsz
    let f' := A.prologueFlags ns s.flags
    match A.abi.raKind with
    | .stack => out = .fall ((s.setGpr A.abi.sp sp').setFlags f')
    | .linkReg lr =>
      let raAddr := sp' + BitVec.ofNat 64 (8 * ns)
      storeOk s.mem i64 raAddr ∧
        out = .fall (((s.setGpr A.abi.sp sp').setMem
          (storeMem s.mem i64 raAddr (s.gpr lr))).setFlags f')
  | .epilogue ns, s, out =>
    let fsz := A.abi.frameSize ns
    let sp' := s.gpr A.abi.sp + BitVec.ofNat 64 fsz
    let f' := A.epilogueFlags ns s.flags
    match A.abi.raKind with
    | .stack => out = .fall ((s.setGpr A.abi.sp sp').setFlags f')
    | .linkReg lr =>
      let raAddr := s.gpr A.abi.sp + BitVec.ofNat 64 (8 * ns)
      ∃ ra : BitVec 64, loadVal s.mem i64 raAddr = some ra ∧
        out = .fall (((s.setGpr lr ra).setGpr A.abi.sp sp').setFlags f')
  | .canonAbi t r, s, out =>
    out = .fall ((s.setGpr r (canonAbiVal t (s.gpr r))).setFlags (A.canonAbiFlags t s.flags))
  | .jmp l, s, out => out = .jump (symAddr l) s
  | .jcc c l, s, out =>
    if A.evalCond s.flags c then out = .jump (symAddr l) s else out = .fall s
  | .jnzGpr r l, s, out =>
    let s' := s.setFlags (A.jnzGprFlags (s.gpr r) s.flags)
    if (s.gpr r).setWidth 8 != 0#8 then out = .jump (symAddr l) s' else out = .fall s'
  | .call sym, s, out =>
    match A.abi.raKind with
    | .stack =>
      let sp' := s.gpr A.abi.sp - 8#64
      storeOk s.mem i64 sp' ∧
        out = .jump (symAddr sym)
          ((s.setGpr A.abi.sp sp').setMem (storeMem s.mem i64 sp' nextPc))
    | .linkReg lr =>
      out = .jump (symAddr sym) (s.setGpr lr nextPc)
  | .icall r, s, out =>
    let tgt := s.gpr r
    match A.abi.raKind with
    | .stack =>
      let sp' := s.gpr A.abi.sp - 8#64
      storeOk s.mem i64 sp' ∧
        out = .jump tgt
          ((s.setGpr A.abi.sp sp').setMem (storeMem s.mem i64 sp' nextPc))
    | .linkReg lr =>
      out = .jump tgt (s.setGpr lr nextPc)
  | .ret, s, out =>
    match A.abi.raKind with
    | .stack =>
      ∃ ra : BitVec 64, loadVal s.mem i64 (s.gpr A.abi.sp) = some ra ∧
        out = .jump ra (s.setGpr A.abi.sp (s.gpr A.abi.sp + 8#64))
    | .linkReg lr =>
      out = .jump (s.gpr lr) s
  | .exitJmp sym, s, out => out = .jump (symAddr sym) s
  | .tailJmpR r, s, out => out = .jump (s.gpr r) s
  | .symAddr sym rd, s, out => out = .fall (s.setGpr rd (symAddr sym))
  | .ijmp r, s, out => out = .jump (s.gpr r) s
  | .native d, s, out =>
    ∃ no, A.nativeStep d symAddr s no ∧ out = no.toInstrOut

/-! ## 3. Small-Step Host & `vllMach : Machine A.Reg A.VReg A.Cond (Instr A)` -/

/-- Laid-out host program for `vllMach A`: flat directive list `prog`, injective instruction
address map `addrOf`, and symbol resolution `labelAddr` agreeing with first `.label` entries. -/
structure VllHost (A : Arch) : Type where
  prog : List (Instr A)
  addrOf : Nat → BitVec 64
  labelAddr : Sym → BitVec 64
  addrOf_inj : ∀ {i j}, i < prog.length → j < prog.length → addrOf i = addrOf j → i = j
  labelAddr_wf : ∀ {k l}, prog[k]? = some (.label l) →
    (∀ j < k, prog[j]? ≠ some (.label l)) → labelAddr l = addrOf k

/-- Small-step omni-semantics transition relation for `vllMach A`. -/
@[expose] def vllStep {A : Arch} (h : VllHost A) (st : Config A) (post : Config A → Prop) :
    Prop :=
  ∃ k instr, h.prog[k]? = some instr ∧ h.addrOf k = st.pc ∧
    (∃ o, instrRel A h.labelAddr (h.addrOf (k + 1)) instr st.data o) ∧
    (∀ s', instrRel A h.labelAddr (h.addrOf (k + 1)) instr st.data (.fall s') →
      post ⟨s', h.addrOf (k + 1)⟩) ∧
    (∀ pc' s', instrRel A h.labelAddr (h.addrOf (k + 1)) instr st.data (.jump pc' s') →
      post ⟨s', pc'⟩) ∧
    (∀ c s', instrRel A h.labelAddr (h.addrOf (k + 1)) instr st.data (.halt c s') → False)

/-- `BedrockMach` L1 packaged as a `LeanQbe.T.Machine A.Reg A.VReg A.Cond (Instr A)`. -/
@[expose] def vllMach (A : Arch) : Machine A.Reg A.VReg A.Cond (Instr A) where
  MData := MachSt A
  Addr := BitVec 64
  State := Config A
  Host := VllHost A
  getGpr s r := s.gpr r
  getVec s vr := s.vreg vr
  evalCond s c := A.evalCond s.flags c
  mem s := s.mem
  mkState s a := ⟨s, a⟩
  pc st := st.pc
  data st := st.data
  pc_mk _ _ := rfl
  data_mk _ _ := rfl
  mk_eta _ := rfl
  prog h := h.prog
  addrOf h k := h.addrOf k
  labelAddr h l := h.labelAddr l
  step h := vllStep h

/-! ## 4. Small-Step Framing Helpers & `FallsTo` / `Run` Step Lemmas for `vllMach` -/

private theorem vllMach_step_at {A : Arch} {h : VllHost A} {k : Nat} {instr : Instr A}
    {s : MachSt A} {post : Config A → Prop}
    (hk : h.prog[k]? = some instr)
    (hex : ∃ o, instrRel A h.labelAddr (h.addrOf (k + 1)) instr s o)
    (hfall : ∀ s', instrRel A h.labelAddr (h.addrOf (k + 1)) instr s (.fall s') →
      (vllMach A).Run h (k + 1) s' post)
    (hjump : ∀ pc' s', instrRel A h.labelAddr (h.addrOf (k + 1)) instr s (.jump pc' s') →
      Eventually (vllStep h) post ⟨s', pc'⟩)
    (hhalt : ∀ c s', instrRel A h.labelAddr (h.addrOf (k + 1)) instr s (.halt c s') → False) :
    (vllMach A).Run h k s post := by
  exact step_cps (vllStep h) post ⟨s, h.addrOf k⟩
    ⟨k, instr, hk, rfl, hex, hfall, hjump, hhalt⟩

private theorem vllMach_fallsTo_det {A : Arch} {h : VllHost A} {k : Nat} {instr : Instr A}
    {gClob : List A.Reg} {vClob : List A.VReg} {fClob : FlagMask}
    {s s' : MachSt A} {Q : MachSt A → Prop} {post : Config A → Prop}
    (hrel : ∀ o, instrRel A h.labelAddr (h.addrOf (k + 1)) instr s o ↔ o = .fall s')
    (hq : Q s')
    (hfr : (vllMach A).Frame A.condReads s s' gClob vClob fClob) :
    (vllMach A).FallsTo A.condReads h k [instr] gClob vClob fClob s Q post := by
  intro hc cont
  have hk : h.prog[k]? = some instr := List.isInfixAt_singleton.mp hc
  refine vllMach_step_at hk ⟨.fall s', (hrel _).mpr rfl⟩ ?_ ?_ ?_
  · intro s₁ hr
    have heq : s₁ = s' := by
      have h1 := (hrel _).mp hr
      injection h1
    subst heq
    simpa only [List.length_singleton] using cont s₁ hq hfr
  · intro _ _ hr
    have h1 := (hrel _).mp hr
    cases h1
  · intro _ _ hr
    have h1 := (hrel _).mp hr
    cases h1

private theorem frame_setGpr {A : Arch} (s : MachSt A) (r : A.Reg) (v : BitVec 64)
    {gClob : List A.Reg} {vClob : List A.VReg} {fClob : FlagMask} (hr : r ∈ gClob) :
    (vllMach A).Frame A.condReads s (s.setGpr r v) gClob vClob fClob := by
  refine ⟨fun q hq => ?_, fun _ _ => rfl, fun _ _ => rfl⟩
  have hne : q ≠ r := fun e => hq (e ▸ hr)
  exact MachSt.gpr_setGpr_ne s v hne

private theorem frame_setGpr_flags {A : Arch} (s : MachSt A) (r : A.Reg) (v : BitVec 64)
    (f' : A.Flags) {gClob : List A.Reg} {vClob : List A.VReg} {fClob : FlagMask}
    (hr : r ∈ gClob) (hf : A.FlagsAgree s.flags f' fClob) :
    (vllMach A).Frame A.condReads s ((s.setGpr r v).setFlags f') gClob vClob fClob := by
  refine ⟨fun q hq => ?_, fun _ _ => rfl, fun c hc => hf c hc⟩
  have hne : q ≠ r := fun e => hq (e ▸ hr)
  exact MachSt.gpr_setGpr_ne s v hne

private theorem frame_setFlags {A : Arch} (s : MachSt A) (f' : A.Flags)
    {gClob : List A.Reg} {vClob : List A.VReg} {fClob : FlagMask}
    (hf : A.FlagsAgree s.flags f' fClob) :
    (vllMach A).Frame A.condReads s (s.setFlags f') gClob vClob fClob :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun c hc => hf c hc⟩

private theorem frame_setMem {A : Arch} (s : MachSt A) (m : Mem 64)
    {gClob : List A.Reg} {vClob : List A.VReg} {fClob : FlagMask} :
    (vllMach A).Frame A.condReads s (s.setMem m) gClob vClob fClob :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩

theorem vllMach_label_spec {A : Arch} {h : VllHost A} {k : Nat} {l : Sym}
    {s : MachSt A} {post : Config A → Prop}
    (hk : h.prog[k]? = some (.label l))
    (hnext : (vllMach A).Run h (k + 1) s post) :
    (vllMach A).Run h k s post := by
  refine vllMach_step_at hk ⟨.fall s, rfl⟩ ?_ ?_ ?_
  · intro s' hr; cases hr; exact hnext
  · intro _ _ hr; cases hr
  · intro _ _ hr; cases hr

theorem vllMach_pad_spec {A : Arch} {h : VllHost A} {k : Nat} {pk : PadKind}
    {s : MachSt A} {post : Config A → Prop} :
    (vllMach A).FallsTo A.condReads h k [.pad pk] [] [] FlagMask.none s
      (fun s' => s' = s) post :=
  vllMach_fallsTo_det (fun _ => Iff.rfl) rfl (Machine.Frame.refl _ _ _ _ _)

theorem vllMach_movW_spec {A : Arch} (hwf : A.Wf) {h : VllHost A} {k : Nat}
    {w : Width} {rd rs : A.Reg} {s : MachSt A} {post : Config A → Prop} :
    (vllMach A).FallsTo A.condReads h k [.mov w rd rs] [rd] [] FlagMask.none s
      (fun s' => s'.gpr rd = A.writeSub w (s.gpr rd) ((s.gpr rs).setWidth w.bits) ∧
        GprHolds (s'.gpr rd) w.toTy ((s.gpr rs).setWidth w.bits) ∧
        s'.mem = s.mem) post := by
  refine vllMach_fallsTo_det (fun _ => Iff.rfl) ?_ (frame_setGpr s rd _ List.mem_cons_self)
  exact ⟨MachSt.gpr_setGprW_same s w rd _,
    by rw [MachSt.gpr_setGprW_same]; exact hwf.writeSub_gprHolds w _ _, rfl⟩

theorem vllMach_mov_spec {A : Arch} (hwf : A.Wf) {h : VllHost A} {k : Nat}
    {rd rs : A.Reg} {s : MachSt A} {post : Config A → Prop} :
    (vllMach A).FallsTo A.condReads h k [.mov .w64 rd rs] [rd] [] FlagMask.none s
      (fun s' => (vllMach A).getGpr s' rd = (vllMach A).getGpr s rs ∧
        (vllMach A).mem s' = (vllMach A).mem s) post := by
  refine vllMach_fallsTo_det (fun _ => Iff.rfl) ?_ (frame_setGpr s rd _ List.mem_cons_self)
  refine ⟨?_, rfl⟩
  show (s.setGprW .w64 rd ((s.gpr rs).setWidth 64)).gpr rd = s.gpr rs
  rw [MachSt.gpr_setGprW_same, hwf.writeSub_w64, BitVec.setWidth_eq]

theorem vllMach_movi_spec {A : Arch} {h : VllHost A} {k : Nat}
    {rd : A.Reg} {imm : BitVec 64} {s : MachSt A} {post : Config A → Prop} :
    (vllMach A).FallsTo A.condReads h k [.movi rd imm] [rd] [] FlagMask.none s
      (fun s' => (vllMach A).getGpr s' rd = imm ∧ (vllMach A).mem s' = (vllMach A).mem s) post :=
  vllMach_fallsTo_det (fun _ => Iff.rfl) ⟨MachSt.gpr_setGpr_same s rd imm, rfl⟩
    (frame_setGpr s rd imm List.mem_cons_self)

theorem vllMach_alu_spec {A : Arch} (hwf : A.Wf) {h : VllHost A} {k : Nat}
    {op : CoreAlu} {w : Width} {rd lhs : A.Reg} {rhs : Src A} {sf : Bool}
    {s : MachSt A} {post : Config A → Prop} :
    let a := (s.gpr lhs).setWidth w.bits
    let b := rhs.evalW w s.gpr
    (vllMach A).FallsTo A.condReads h k [.alu op w rd lhs rhs sf] [rd] [] (A.aluClob op sf) s
      (fun s' => s'.gpr rd = A.writeSub w (s.gpr rd) (op.eval w a b) ∧
        GprHolds (s'.gpr rd) w.toTy (op.eval w a b) ∧
        s'.flags = A.aluFlags op w sf a b s.flags ∧
        s'.mem = s.mem) post := by
  intro a b
  refine vllMach_fallsTo_det (fun _ => Iff.rfl) ?_
    (frame_setGpr_flags s rd _ _ List.mem_cons_self (hwf.aluFlags_frame op w sf a b s.flags))
  refine ⟨MachSt.gpr_setGprW_same s w rd _, ?_, rfl, rfl⟩
  rw [MachSt.gpr_setFlags, MachSt.gpr_setGprW_same]
  exact hwf.writeSub_gprHolds w _ _

theorem vllMach_cmp_spec {A : Arch} (hwf : A.Wf) {h : VllHost A} {k : Nat}
    {w : Width} {lhs : A.Reg} {rhs : Src A} {s : MachSt A} {post : Config A → Prop} :
    let a := (s.gpr lhs).setWidth w.bits
    let b := rhs.evalW w s.gpr
    (vllMach A).FallsTo A.condReads h k [.cmp w lhs rhs] [] [] A.cmpClob s
      (fun s' => s'.flags = A.cmpFlags w a b s.flags ∧ s'.mem = s.mem) post := by
  intro a b
  exact vllMach_fallsTo_det (fun _ => Iff.rfl) ⟨rfl, rfl⟩
    (frame_setFlags s _ (hwf.cmpFlags_frame w a b s.flags))

theorem vllMach_test_spec {A : Arch} (hwf : A.Wf) {h : VllHost A} {k : Nat}
    {w : Width} {lhs : A.Reg} {rhs : Src A} {s : MachSt A} {post : Config A → Prop} :
    let a := (s.gpr lhs).setWidth w.bits
    let b := rhs.evalW w s.gpr
    (vllMach A).FallsTo A.condReads h k [.test w lhs rhs] [] [] A.testClob s
      (fun s' => s'.flags = A.testFlags w a b s.flags ∧ s'.mem = s.mem) post := by
  intro a b
  exact vllMach_fallsTo_det (fun _ => Iff.rfl) ⟨rfl, rfl⟩
    (frame_setFlags s _ (hwf.testFlags_frame w a b s.flags))

theorem vllMach_clearFlags_spec {A : Arch} (hwf : A.Wf) {h : VllHost A} {k : Nat}
    {s : MachSt A} {post : Config A → Prop}
    (hreads : ∀ c, FlagMask.disjoint (A.condReads c) FlagMask.all = true →
      A.evalCond A.clearFlagsVal c = A.evalCond s.flags c) :
    (vllMach A).FallsTo A.condReads h k [.clearFlags] [] [] FlagMask.all s
      (fun s' => (∀ c ∈ A.zeroFlags, (vllMach A).evalCond s' c = false) ∧
        (vllMach A).mem s' = (vllMach A).mem s) post :=
  vllMach_fallsTo_det (fun _ => Iff.rfl)
    ⟨fun c hc => hwf.clearFlags_zero c hc, rfl⟩
    (frame_setFlags s A.clearFlagsVal hreads)

theorem vllMach_setcc_spec {A : Arch} (hwf : A.Wf) {h : VllHost A} {k : Nat}
    {rd : A.Reg} {c : A.Cond} {s : MachSt A} {post : Config A → Prop} :
    (vllMach A).FallsTo A.condReads h k [.setcc rd c] [rd] [] FlagMask.none s
      (fun s' => GprHolds ((vllMach A).getGpr s' rd) .bool ((vllMach A).evalCond s c) ∧
        (vllMach A).mem s' = (vllMach A).mem s) post := by
  refine vllMach_fallsTo_det (fun _ => Iff.rfl) ?_ (frame_setGpr s rd _ List.mem_cons_self)
  refine ⟨?_, rfl⟩
  show ((s.setGprW .w8 rd (BitVec.ofNat 8 (A.evalCond s.flags c).toNat)).gpr rd).setWidth 8 = _
  rw [MachSt.gpr_setGprW_same, hwf.writeSub_setWidth .w8]
  rfl

theorem vllMach_load_spec {A : Arch} (hwf : A.Wf) {h : VllHost A} {k : Nat}
    {w : Width} {ext : LoadExt} {rd : A.Reg} {addr : AddrArg A.Reg}
    {v : BitVec w.bits} {s : MachSt A} {post : Config A → Prop}
    (hld : loadVal s.mem w.toTy (addr.eval s.gpr) = some v) :
    (vllMach A).FallsTo A.condReads h k [.load w ext rd addr] [rd] [] FlagMask.none s
      (fun s' => s'.gpr rd = ext.apply A w (s.gpr rd) v ∧
        GprHolds (s'.gpr rd) w.toTy v ∧ s'.mem = s.mem) post := by
  let v' := ext.apply A w (s.gpr rd) v
  refine vllMach_fallsTo_det (s' := s.setGpr rd v') ?_ ?_
    (frame_setGpr s rd v' List.mem_cons_self)
  · intro o
    simp only [instrRel, hld, Option.some.injEq, exists_eq_left', v']
  · exact ⟨MachSt.gpr_setGpr_same s rd v',
      by rw [MachSt.gpr_setGpr_same]; exact ext.apply_gprHolds hwf w _ v, rfl⟩

theorem vllMach_store_spec {A : Arch} {h : VllHost A} {k : Nat}
    {w : Width} {rs : A.Reg} {addr : AddrArg A.Reg} {s : MachSt A} {post : Config A → Prop}
    (hst : storeOk s.mem w.toTy (addr.eval s.gpr)) :
    (vllMach A).FallsTo A.condReads h k [.store w rs addr] [] [] FlagMask.none s
      (fun s' => s'.mem = storeMem s.mem w.toTy (addr.eval s.gpr) ((s.gpr rs).setWidth w.bits))
      post := by
  let m' := storeMem s.mem w.toTy (addr.eval s.gpr) ((s.gpr rs).setWidth w.bits)
  refine vllMach_fallsTo_det (s' := s.setMem m') ?_ rfl (frame_setMem s m')
  intro o
  simp only [instrRel, hst, true_and, m']

theorem vllMach_slotSt_spec {A : Arch} {h : VllHost A} {k i : Nat} {rs : A.Reg}
    {s : MachSt A} {G : Mem 64 → Prop} {post : Config A → Prop}
    (hm : (s.mem =⋆ region (s.gpr A.abi.sp + BitVec.ofNat 64 (8 * i)) 8 ⋆ G)) :
    (vllMach A).FallsTo A.condReads h k [.slotSt i rs] A.abi.scratch [] FlagMask.none s
      (fun s' => s'.mem =⋆
        cell64 (s.gpr A.abi.sp + BitVec.ofNat 64 (8 * i)) (s.gpr rs) ⋆ G) post := by
  obtain ⟨v0, hv0⟩ := region_sep_cell64 hm
  obtain ⟨hst, hmem'⟩ := store_cell64 (s.gpr rs) hv0
  let m' := storeMem s.mem i64 (s.gpr A.abi.sp + BitVec.ofNat 64 (8 * i)) (s.gpr rs)
  refine vllMach_fallsTo_det (s' := s.setMem m') ?_ hmem' (frame_setMem s m')
  intro o
  simp only [instrRel, hst, true_and, m']

theorem vllMach_slotLd_spec {A : Arch} {h : VllHost A} {k i : Nat} {rd : A.Reg}
    {v : BitVec 64} {s : MachSt A} {G : Mem 64 → Prop} {post : Config A → Prop}
    (hm : (s.mem =⋆ cell64 (s.gpr A.abi.sp + BitVec.ofNat 64 (8 * i)) v ⋆ G)) :
    (vllMach A).FallsTo A.condReads h k [.slotLd rd i] (rd :: A.abi.scratch) [] FlagMask.none s
      (fun s' => s'.gpr rd = v ∧ s'.mem = s.mem) post := by
  have hld : loadVal s.mem i64 (s.gpr A.abi.sp + BitVec.ofNat 64 (8 * i)) = some v :=
    loadVal_cell64 hm
  refine vllMach_fallsTo_det ?_ ⟨MachSt.gpr_setGpr_same s rd v, rfl⟩
    (frame_setGpr s rd v List.mem_cons_self)
  intro o
  simp only [instrRel, hld, Option.some.injEq, exists_eq_left']

theorem vllMach_canonAbi_spec {A : Arch} (hwf : A.Wf) {h : VllHost A} {k : Nat}
    {t : Ty} {r : A.Reg} {v : Val t} {s : MachSt A} {post : Config A → Prop}
    (ht : t = .bool ∨ ∃ n ∈ A.abi.bitWidths, t = .bits n)
    (hholds : GprHolds (s.gpr r) t v) :
    (vllMach A).FallsTo A.condReads h k [.canonAbi t r]
      (r :: A.abi.scratch) [] (A.abi.canonAbiClob t) s
      (fun s' => AbiGprHolds (s'.gpr r) t v ∧ s'.mem = s.mem) post := by
  refine vllMach_fallsTo_det (fun _ => Iff.rfl) ?_
    (frame_setGpr_flags s r _ _ List.mem_cons_self (hwf.canonAbiFlags_frame t s.flags))
  refine ⟨?_, rfl⟩
  rw [MachSt.gpr_setFlags, MachSt.gpr_setGpr_same]
  rcases ht with rfl | ⟨n, _, rfl⟩
  · exact abiGprHolds_bool_of_gprHolds hholds
  · exact abiGprHolds_bits_of_gprHolds hholds

theorem vllMach_symAddr_spec {A : Arch} {h : VllHost A} {k : Nat}
    {sym : Sym} {rd : A.Reg} {s : MachSt A} {post : Config A → Prop} :
    (vllMach A).FallsTo A.condReads h k [.symAddr sym rd] [rd] [] FlagMask.none s
      (fun s' => s'.gpr rd = h.labelAddr sym ∧ s'.mem = s.mem) post :=
  vllMach_fallsTo_det (fun _ => Iff.rfl) ⟨MachSt.gpr_setGpr_same s rd _, rfl⟩
    (frame_setGpr s rd _ List.mem_cons_self)

theorem vllMach_jmp_spec {A : Arch} {h : VllHost A} {k j : Nat} {l : Sym}
    {s : MachSt A} {post : Config A → Prop}
    (hc : [Instr.jmp l].IsInfixAt h.prog k)
    (hl : h.labelAddr l = h.addrOf j)
    (hcont : (vllMach A).Run h j s post) :
    (vllMach A).Run h k s post := by
  have hk : h.prog[k]? = some (.jmp l) := List.isInfixAt_singleton.mp hc
  refine vllMach_step_at hk ⟨.jump (h.labelAddr l) s, rfl⟩ ?_ ?_ ?_
  · intro _ hr; cases hr
  · intro pc' s' hr
    cases hr
    rw [hl]
    exact hcont
  · intro _ _ hr; cases hr

theorem vllMach_jcc_spec {A : Arch} {h : VllHost A} {k j : Nat} {c : A.Cond} {l : Sym}
    {s : MachSt A} {post : Config A → Prop}
    (hc : [Instr.jcc c l].IsInfixAt h.prog k)
    (hl : h.labelAddr l = h.addrOf j)
    (ht : A.evalCond s.flags c = true → (vllMach A).Run h j s post)
    (hf : A.evalCond s.flags c = false → (vllMach A).Run h (k + 1) s post) :
    (vllMach A).Run h k s post := by
  have hk : h.prog[k]? = some (.jcc c l) := List.isInfixAt_singleton.mp hc
  cases he : A.evalCond s.flags c with
  | true =>
    refine vllMach_step_at hk ⟨.jump (h.labelAddr l) s, by simp [instrRel, he]⟩ ?_ ?_ ?_
    · intro _ hr; simp [instrRel, he] at hr
    · intro pc' s' hr
      simp only [instrRel, he, ↓reduceIte, InstrOut.jump.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      rw [hl]
      exact ht he
    · intro _ _ hr; simp [instrRel, he] at hr
  | false =>
    refine vllMach_step_at hk ⟨.fall s, by simp [instrRel, he]⟩ ?_ ?_ ?_
    · intro s' hr
      simp only [instrRel, he, Bool.false_eq_true, ↓reduceIte, InstrOut.fall.injEq] at hr
      subst hr
      exact hf he
    · intro _ _ hr; simp [instrRel, he] at hr
    · intro _ _ hr; simp [instrRel, he] at hr

theorem vllMach_jnzGpr_spec {A : Arch} (hwf : A.Wf) {h : VllHost A} {k j : Nat}
    {r : A.Reg} {l : Sym} {b : Bool} {s : MachSt A} {post : Config A → Prop}
    (hc : [Instr.jnzGpr r l].IsInfixAt h.prog k)
    (hl : h.labelAddr l = h.addrOf j)
    (hb : GprHolds (s.gpr r) .bool b)
    (hcont : ∀ s', (vllMach A).Frame A.condReads s s' A.abi.scratch [] A.jnzGprClob →
      s'.mem = s.mem →
      (b = true → (vllMach A).Run h j s' post) ∧
      (b = false → (vllMach A).Run h (k + 1) s' post)) :
    (vllMach A).Run h k s post := by
  have hk : h.prog[k]? = some (.jnzGpr r l) := List.isInfixAt_singleton.mp hc
  let s' := s.setFlags (A.jnzGprFlags (s.gpr r) s.flags)
  have hfr : (vllMach A).Frame A.condReads s s' A.abi.scratch [] A.jnzGprClob :=
    frame_setFlags s _ (hwf.jnzGprFlags_frame (s.gpr r) s.flags)
  have h8 : (s.gpr r).setWidth 8 = BitVec.ofNat 8 b.toNat := hb
  cases b with
  | true =>
    have hnz : ((s.gpr r).setWidth 8 != 0#8) = true := by rw [h8]; decide
    refine vllMach_step_at hk ⟨.jump (h.labelAddr l) s', by simp [instrRel, hnz, s']⟩ ?_ ?_ ?_
    · intro _ hr; simp [instrRel, hnz] at hr
    · intro pc' s₁ hr
      simp only [instrRel, hnz, ↓reduceIte, InstrOut.jump.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      rw [hl]
      exact (hcont s' hfr rfl).1 rfl
    · intro _ _ hr; simp [instrRel, hnz] at hr
  | false =>
    have hz : ((s.gpr r).setWidth 8 != 0#8) = false := by rw [h8]; decide
    refine vllMach_step_at hk ⟨.fall s', by simp [instrRel, hz, s']⟩ ?_ ?_ ?_
    · intro s₁ hr
      simp only [instrRel, hz, Bool.false_eq_true, ↓reduceIte, InstrOut.fall.injEq] at hr
      subst hr
      exact (hcont s' hfr rfl).2 rfl
    · intro _ _ hr; simp [instrRel, hz] at hr
    · intro _ _ hr; simp [instrRel, hz] at hr

theorem vllMach_exitJmp_spec {A : Arch} {h : VllHost A} {k : Nat} {sym : Sym}
    {s : MachSt A} {post : Config A → Prop}
    (hc : [Instr.exitJmp sym].IsInfixAt h.prog k)
    (hcont : Eventually (vllStep h) post ⟨s, h.labelAddr sym⟩) :
    (vllMach A).Run h k s post := by
  have hk : h.prog[k]? = some (.exitJmp sym) := List.isInfixAt_singleton.mp hc
  refine vllMach_step_at hk ⟨.jump (h.labelAddr sym) s, rfl⟩ ?_ ?_ ?_
  · intro _ hr; cases hr
  · intro pc' s' hr; cases hr; exact hcont
  · intro _ _ hr; cases hr

theorem vllMach_tailJmpR_spec {A : Arch} {h : VllHost A} {k : Nat} {r : A.Reg}
    {s : MachSt A} {post : Config A → Prop}
    (hc : [Instr.tailJmpR r].IsInfixAt h.prog k)
    (hcont : Eventually (vllStep h) post ⟨s, s.gpr r⟩) :
    (vllMach A).Run h k s post := by
  have hk : h.prog[k]? = some (.tailJmpR r) := List.isInfixAt_singleton.mp hc
  refine vllMach_step_at hk ⟨.jump (s.gpr r) s, rfl⟩ ?_ ?_ ?_
  · intro _ hr; cases hr
  · intro pc' s' hr; cases hr; exact hcont
  · intro _ _ hr; cases hr

theorem vllMach_ijmp_spec {A : Arch} {h : VllHost A} {k : Nat} {r : A.Reg}
    {s : MachSt A} {post : Config A → Prop}
    (hc : [Instr.ijmp r].IsInfixAt h.prog k)
    (hcont : Eventually (vllStep h) post ⟨s, s.gpr r⟩) :
    (vllMach A).Run h k s post := by
  have hk : h.prog[k]? = some (.ijmp r) := List.isInfixAt_singleton.mp hc
  refine vllMach_step_at hk ⟨.jump (s.gpr r) s, rfl⟩ ?_ ?_ ?_
  · intro _ hr; cases hr
  · intro pc' s' hr; cases hr; exact hcont
  · intro _ _ hr; cases hr

theorem vllMach_native_fallsTo {A : Arch} {h : VllHost A} {k : Nat} {d : A.Native}
    {gClob : List A.Reg} {vClob : List A.VReg} {fClob : FlagMask}
    {s : MachSt A} {Q : MachSt A → Prop} {post : Config A → Prop}
    (hex : ∃ s', A.nativeStep d h.labelAddr s (.fall s'))
    (hfall : ∀ s', A.nativeStep d h.labelAddr s (.fall s') →
      Q s' ∧ (vllMach A).Frame A.condReads s s' gClob vClob fClob)
    (hnoJump : ∀ pc' s', ¬A.nativeStep d h.labelAddr s (.jump pc' s'))
    (hnoHalt : ∀ c s', ¬A.nativeStep d h.labelAddr s (.halt c s')) :
    (vllMach A).FallsTo A.condReads h k [.native d] gClob vClob fClob s Q post := by
  intro hc cont
  have hk : h.prog[k]? = some (.native d) := List.isInfixAt_singleton.mp hc
  obtain ⟨s₀, hs₀⟩ := hex
  refine vllMach_step_at hk ⟨.fall s₀, .fall s₀, hs₀, rfl⟩ ?_ ?_ ?_
  · intro s' ⟨no, hstep, heq⟩
    cases no with
    | fall s₁ =>
      cases heq
      obtain ⟨hq, hfr⟩ := hfall s' hstep
      simpa only [List.length_singleton] using cont s' hq hfr
    | jump _ _ => cases heq
    | halt _ _ => cases heq
  · intro pc' s' ⟨no, hstep, heq⟩
    cases no with
    | fall _ => cases heq
    | jump p₁ s₁ => cases heq; exact False.elim (hnoJump pc' s' hstep)
    | halt _ _ => cases heq
  · intro c s' ⟨no, hstep, heq⟩
    cases no with
    | fall _ => cases heq
    | jump _ _ => cases heq
    | halt c₁ s₁ => cases heq; exact False.elim (hnoHalt c s' hstep)

theorem vllMach_native_jump {A : Arch} {h : VllHost A} {k : Nat} {d : A.Native}
    {s : MachSt A} {post : Config A → Prop}
    (hc : [Instr.native d].IsInfixAt h.prog k)
    (hex : ∃ o, A.nativeStep d h.labelAddr s o)
    (hfall : ∀ s', A.nativeStep d h.labelAddr s (.fall s') →
      (vllMach A).Run h (k + 1) s' post)
    (hjump : ∀ pc' s', A.nativeStep d h.labelAddr s (.jump pc' s') →
      Eventually (vllStep h) post ⟨s', pc'⟩)
    (hhalt : ∀ c s', ¬A.nativeStep d h.labelAddr s (.halt c s')) :
    (vllMach A).Run h k s post := by
  have hk : h.prog[k]? = some (.native d) := List.isInfixAt_singleton.mp hc
  obtain ⟨o₀, ho₀⟩ := hex
  refine vllMach_step_at hk ⟨o₀.toInstrOut, o₀, ho₀, rfl⟩ ?_ ?_ ?_
  · intro s' ⟨no, hstep, heq⟩
    cases no with
    | fall s₁ => cases heq; exact hfall s' hstep
    | jump _ _ => cases heq
    | halt _ _ => cases heq
  · intro pc' s' ⟨no, hstep, heq⟩
    cases no with
    | fall _ => cases heq
    | jump p₁ s₁ => cases heq; exact hjump pc' s' hstep
    | halt _ _ => cases heq
  · intro c s' ⟨no, hstep, heq⟩
    cases no with
    | fall _ => cases heq
    | jump _ _ => cases heq
    | halt c₁ s₁ => cases heq; exact hhalt c s' hstep

/-! ## 5. Generic `FramePreds`, `FrameIsa`, and `vllFrameTarget` (`.stack` & `.linkReg`) -/

/-- Generic `FramePreds` for `vllMach A`, handling both x86-64-style `.stack` return addresses
and AArch64-style `.linkReg lr` link-register return addresses. -/
@[expose] def vllFramePreds (A : Arch) : FramePreds (vllMach A) where
  RetAddr sp ra :=
    match A.abi.raKind with
    | .stack => cell64 sp ra
    | .linkReg _ => region sp 0
  raReg s ra :=
    match A.abi.raKind with
    | .stack => True
    | .linkReg lr => s.gpr lr = ra
  spEntry := A.abi.spEntry
  spOk := A.abi.spOk
  Saved sp ra ns :=
    let fsz := A.abi.frameSize ns
    match A.abi.raKind with
    | .stack =>
      region (sp - BitVec.ofNat 64 fsz + BitVec.ofNat 64 (8 * ns)) (fsz - 8 * ns) ⋆
        cell64 sp ra
    | .linkReg _ =>
      cell64 (sp - BitVec.ofNat 64 fsz + BitVec.ofNat 64 (8 * ns)) ra ⋆
        region (sp - BitVec.ofNat 64 fsz + BitVec.ofNat 64 (8 * ns) + 8#64)
          (fsz - 8 * ns - 8)

/-- Generic `FrameIsa` over `Instr A` derived directly from `A.abi`. -/
@[expose] def vllFrameIsa (A : Arch) : FrameIsa A.Reg (Instr A) where
  label := .label
  sp := A.abi.sp
  scratch := A.abi.scratch
  allocatable := A.abi.allocatable
  calleeSaved := A.abi.calleeSaved
  raRegs := A.abi.raRegs
  argRegs := A.abi.argRegs
  retRegs := A.abi.retRegs
  bitWidths := A.abi.bitWidths
  raBytes := A.abi.raBytes
  frameSize := A.abi.frameSize
  prologue ns := ([.prologue ns], A.abi.prologueClob)
  epilogue ns := ([.epilogue ns], A.abi.epilogueClob)
  slotSt i r := [.slotSt i r]
  slotLd rd i := [.slotLd rd i]
  canonAbi t r := ([.canonAbi t r], A.abi.canonAbiClob t)
  call sym := [.call sym]
  exitJmp sym := [.exitJmp sym]
  ret := [.ret]
  leafZeroFrame := A.abi.leafZeroFrame

theorem vllMach_prologue_spec {A : Arch} (hwf : A.Wf) {h : VllHost A} {k ns : Nat}
    {s : MachSt A} {ra : BitVec 64} {G : Mem 64 → Prop} {post : Config A → Prop}
    (hra : (vllFramePreds A).raReg s ra)
    (hbound : A.abi.frameSize ns + A.abi.raBytes ≤ 2 ^ 64)
    (hm : s.mem =⋆ (vllFramePreds A).RetAddr (s.gpr A.abi.sp) ra ⋆
      region (s.gpr A.abi.sp - BitVec.ofNat 64 (A.abi.frameSize ns)) (A.abi.frameSize ns) ⋆ G) :
    (vllMach A).FallsTo A.condReads h k [.prologue ns]
      (A.abi.sp :: A.abi.raRegs ++ A.abi.scratch) [] A.abi.prologueClob s
      (fun s' => s'.gpr A.abi.sp = s.gpr A.abi.sp - BitVec.ofNat 64 (A.abi.frameSize ns) ∧
        (s'.mem =⋆ (vllFramePreds A).Saved (s.gpr A.abi.sp) ra ns ⋆
          region (s.gpr A.abi.sp - BitVec.ofNat 64 (A.abi.frameSize ns)) (8 * ns) ⋆ G)) post := by
  cases hkind : A.abi.raKind with
  | stack =>
    have hfsz : A.abi.frameSize ns ≤ 2 ^ 64 := by
      simp only [Abi.raBytes, hkind, RaKind.raBytes] at hbound; omega
    have hsplit := region_frame_split (a := s.gpr A.abi.sp - BitVec.ofNat 64 (A.abi.frameSize ns))
      (hwf.slots_le_frameSize ns) hfsz
    have hm' :
        (s.mem =⋆ (vllFramePreds A).Saved (s.gpr A.abi.sp) ra ns ⋆
          region (s.gpr A.abi.sp - BitVec.ofNat 64 (A.abi.frameSize ns)) (8 * ns) ⋆ G) := by
      simp only [vllFramePreds, hkind] at hm ⊢
      rw [hsplit] at hm
      exact sep_cast hm (by ac_rfl)
    let sp' := s.gpr A.abi.sp - BitVec.ofNat 64 (A.abi.frameSize ns)
    let f' := A.prologueFlags ns s.flags
    refine vllMach_fallsTo_det (s' := (s.setGpr A.abi.sp sp').setFlags f') ?_
      ⟨MachSt.gpr_setGpr_same s A.abi.sp sp', hm'⟩
      (frame_setGpr_flags s A.abi.sp sp' f' List.mem_cons_self (hwf.prologueFlags_frame ns s.flags))
    intro o
    simp only [instrRel, hkind, sp', f']
  | linkReg lr =>
    have hlr_le : 8 * ns + 8 ≤ A.abi.frameSize ns := hwf.linkReg_frameSize lr hkind ns
    have hfsz : A.abi.frameSize ns ≤ 2 ^ 64 := by
      simp only [Abi.raBytes, hkind, RaKind.raBytes] at hbound; omega
    have hlr_eq : s.gpr lr = ra := by
      simpa only [vllFramePreds, hkind] using hra
    have hsplit := region_frame_split_ra
      (a := s.gpr A.abi.sp - BitVec.ofNat 64 (A.abi.frameSize ns)) hlr_le hfsz
    simp only [vllFramePreds, hkind] at hm
    rw [region_zero, emp_sep, hsplit] at hm
    have hm_focus :
        (region (s.gpr A.abi.sp - BitVec.ofNat 64 (A.abi.frameSize ns) +
            BitVec.ofNat 64 (8 * ns)) 8 ⋆
          (region (s.gpr A.abi.sp - BitVec.ofNat 64 (A.abi.frameSize ns) +
              BitVec.ofNat 64 (8 * ns) + 8#64) (A.abi.frameSize ns - 8 * ns - 8) ⋆
            region (s.gpr A.abi.sp - BitVec.ofNat 64 (A.abi.frameSize ns)) (8 * ns) ⋆ G)) s.mem :=
      sep_cast hm (by ac_rfl)
    obtain ⟨v0, hv0⟩ := region_sep_cell64 hm_focus
    obtain ⟨hst, hmem_st⟩ := store_cell64 (s.gpr lr) hv0
    have hmem_post :
        (storeMem s.mem i64
          (s.gpr A.abi.sp - BitVec.ofNat 64 (A.abi.frameSize ns) + BitVec.ofNat 64 (8 * ns))
          (s.gpr lr) =⋆
          (vllFramePreds A).Saved (s.gpr A.abi.sp) ra ns ⋆
            region (s.gpr A.abi.sp - BitVec.ofNat 64 (A.abi.frameSize ns)) (8 * ns) ⋆ G) := by
      simp only [vllFramePreds, hkind]
      rw [hlr_eq] at hmem_st ⊢
      exact sep_cast hmem_st (by ac_rfl)
    let sp' := s.gpr A.abi.sp - BitVec.ofNat 64 (A.abi.frameSize ns)
    let m' := storeMem s.mem i64 (sp' + BitVec.ofNat 64 (8 * ns)) (s.gpr lr)
    let f' := A.prologueFlags ns s.flags
    refine vllMach_fallsTo_det (s' := ((s.setGpr A.abi.sp sp').setMem m').setFlags f') ?_
      ⟨MachSt.gpr_setGpr_same s A.abi.sp sp', hmem_post⟩ ?_
    · intro o
      simp only [instrRel, hkind, sp', m', f']
      exact ⟨fun h => h.2, fun h => ⟨hst, h⟩⟩
    · refine ⟨fun q hq => ?_, fun _ _ => rfl,
        fun c hc => hwf.prologueFlags_frame ns s.flags c hc⟩
      have hne : q ≠ A.abi.sp := fun e => hq (e ▸ List.mem_cons_self)
      exact MachSt.gpr_setGpr_ne s sp' hne

theorem vllMach_epilogue_spec {A : Arch} (hwf : A.Wf) {h : VllHost A} {k ns : Nat}
    {s : MachSt A} {ra : BitVec 64} {G : Mem 64 → Prop} {post : Config A → Prop}
    (hbound : A.abi.frameSize ns + A.abi.raBytes ≤ 2 ^ 64)
    (hm : s.mem =⋆
      (vllFramePreds A).Saved (s.gpr A.abi.sp + BitVec.ofNat 64 (A.abi.frameSize ns)) ra ns ⋆ G) :
    (vllMach A).FallsTo A.condReads h k [.epilogue ns]
      (A.abi.sp :: A.abi.raRegs ++ A.abi.scratch) [] A.abi.epilogueClob s
      (fun s' => s'.gpr A.abi.sp = s.gpr A.abi.sp + BitVec.ofNat 64 (A.abi.frameSize ns) ∧
        (vllFramePreds A).raReg s' ra ∧
        (s'.mem =⋆
          (vllFramePreds A).RetAddr (s.gpr A.abi.sp + BitVec.ofNat 64 (A.abi.frameSize ns)) ra ⋆
            region (s.gpr A.abi.sp + BitVec.ofNat 64 (8 * ns))
              (A.abi.frameSize ns - 8 * ns) ⋆ G)) post := by
  have hcancel :
      s.gpr A.abi.sp + BitVec.ofNat 64 (A.abi.frameSize ns) -
        BitVec.ofNat 64 (A.abi.frameSize ns) = s.gpr A.abi.sp :=
    BitVec.add_sub_cancel (s.gpr A.abi.sp) (BitVec.ofNat 64 (A.abi.frameSize ns))
  cases hkind : A.abi.raKind with
  | stack =>
    have hm' :
        (s.mem =⋆ (vllFramePreds A).RetAddr
          (s.gpr A.abi.sp + BitVec.ofNat 64 (A.abi.frameSize ns)) ra ⋆
          region (s.gpr A.abi.sp + BitVec.ofNat 64 (8 * ns))
            (A.abi.frameSize ns - 8 * ns) ⋆ G) := by
      simp only [vllFramePreds, hkind] at hm ⊢
      rw [hcancel] at hm
      exact sep_cast hm (by ac_rfl)
    let sp' := s.gpr A.abi.sp + BitVec.ofNat 64 (A.abi.frameSize ns)
    let f' := A.epilogueFlags ns s.flags
    refine vllMach_fallsTo_det (s' := (s.setGpr A.abi.sp sp').setFlags f') ?_
      ⟨MachSt.gpr_setGpr_same s A.abi.sp sp', by simp [vllFramePreds, hkind], hm'⟩
      (frame_setGpr_flags s A.abi.sp sp' f' List.mem_cons_self (hwf.epilogueFlags_frame ns s.flags))
    intro o
    simp only [instrRel, hkind, sp', f']
  | linkReg lr =>
    have hlr_le : 8 * ns + 8 ≤ A.abi.frameSize ns := hwf.linkReg_frameSize lr hkind ns
    have hfsz : A.abi.frameSize ns ≤ 2 ^ 64 := by
      simp only [Abi.raBytes, hkind, RaKind.raBytes] at hbound; omega
    have hsp_ne_lr : A.abi.sp ≠ lr := by
      have hdisj := hwf.sp_disj.2.2.2.2.2
      simp only [Abi.raRegs, hkind, RaKind.raRegs, List.mem_singleton] at hdisj
      exact hdisj
    simp only [vllFramePreds, hkind] at hm
    rw [hcancel] at hm
    have hld : loadVal s.mem i64 (s.gpr A.abi.sp + BitVec.ofNat 64 (8 * ns)) = some ra := by
      have hm_c : (cell64 (s.gpr A.abi.sp + BitVec.ofNat 64 (8 * ns)) ra ⋆
          (region (s.gpr A.abi.sp + BitVec.ofNat 64 (8 * ns) + 8#64)
            (A.abi.frameSize ns - 8 * ns - 8) ⋆ G)) s.mem := sep_cast hm (by ac_rfl)
      exact loadVal_cell64 hm_c
    have hmerge :
        region (s.gpr A.abi.sp + BitVec.ofNat 64 (8 * ns)) (A.abi.frameSize ns - 8 * ns) =
          (region (s.gpr A.abi.sp + BitVec.ofNat 64 (8 * ns)) 8 ⋆
            region (s.gpr A.abi.sp + BitVec.ofNat 64 (8 * ns) + 8#64)
              (A.abi.frameSize ns - 8 * ns - 8)) := by
      have heq : A.abi.frameSize ns - 8 * ns = 8 + (A.abi.frameSize ns - 8 * ns - 8) := by omega
      conv => lhs; rw [heq]
      exact region_split (by omega)
    have hm_reg :
        (region (s.gpr A.abi.sp + BitVec.ofNat 64 (8 * ns)) 8 ⋆
          region (s.gpr A.abi.sp + BitVec.ofNat 64 (8 * ns) + 8#64)
            (A.abi.frameSize ns - 8 * ns - 8) ⋆ G) s.mem := by
      have h1 :
          ((region (s.gpr A.abi.sp + BitVec.ofNat 64 (8 * ns)) 8 ⋆
            region (s.gpr A.abi.sp + BitVec.ofNat 64 (8 * ns) + 8#64)
              (A.abi.frameSize ns - 8 * ns - 8)) ⋆ G) s.mem :=
        sep_mono (fun _ => sep_mono (fun _ => cell64_region)) hm
      exact sep_cast h1 (by ac_rfl)
    have hm_post :
        (s.mem =⋆ (vllFramePreds A).RetAddr
          (s.gpr A.abi.sp + BitVec.ofNat 64 (A.abi.frameSize ns)) ra ⋆
          region (s.gpr A.abi.sp + BitVec.ofNat 64 (8 * ns))
            (A.abi.frameSize ns - 8 * ns) ⋆ G) := by
      simp only [vllFramePreds, hkind]
      rw [region_zero, emp_sep, hmerge]
      exact sep_cast hm_reg (by ac_rfl)
    let sp' := s.gpr A.abi.sp + BitVec.ofNat 64 (A.abi.frameSize ns)
    let f' := A.epilogueFlags ns s.flags
    refine vllMach_fallsTo_det (s' := ((s.setGpr lr ra).setGpr A.abi.sp sp').setFlags f') ?_ ?_ ?_
    · intro o
      simp only [instrRel, hkind, hld, Option.some.injEq, exists_eq_left', sp', f']
    · refine ⟨by simp [sp'], ?_, hm_post⟩
      simp only [vllFramePreds, hkind, MachSt.gpr_setFlags]
      rw [MachSt.gpr_setGpr_ne _ sp' hsp_ne_lr.symm, MachSt.gpr_setGpr_same]
    · refine ⟨fun q hq => ?_, fun _ _ => rfl,
        fun c hc => hwf.epilogueFlags_frame ns s.flags c hc⟩
      have hq_sp : q ≠ A.abi.sp := fun e => hq (e ▸ List.mem_cons_self)
      have hq_lr : q ≠ lr := fun e => hq (by
        rw [e]; apply List.mem_cons_of_mem
        apply List.mem_append_left
        simp [Abi.raRegs, hkind, RaKind.raRegs])
      dsimp only [vllMach]
      simp only [MachSt.gpr_setFlags]
      rw [MachSt.gpr_setGpr_ne _ sp' hq_sp, MachSt.gpr_setGpr_ne _ ra hq_lr]

theorem vllMach_call_spec {A : Arch} (hwf : A.Wf) {h : VllHost A} {k : Nat} {sym : Sym}
    {s : MachSt A} {G : Mem 64 → Prop} {post : Config A → Prop}
    (hc : [Instr.call sym].IsInfixAt h.prog k)
    (hm : s.mem =⋆ region (s.gpr A.abi.sp - BitVec.ofNat 64 A.abi.raBytes) A.abi.raBytes ⋆ G)
    (hcont : ∀ s',
      s'.gpr A.abi.sp = s.gpr A.abi.sp - BitVec.ofNat 64 A.abi.raBytes →
      (vllMach A).Frame A.condReads s s'
        (A.abi.sp :: A.abi.raRegs ++ A.abi.scratch) [] FlagMask.all →
      (vllFramePreds A).raReg s' (h.addrOf (k + 1)) →
      (s'.mem =⋆ (vllFramePreds A).RetAddr (s'.gpr A.abi.sp) (h.addrOf (k + 1)) ⋆ G) →
      Eventually (vllStep h) post ⟨s', h.labelAddr sym⟩) :
    (vllMach A).Run h k s post := by
  have hk : h.prog[k]? = some (.call sym) := List.isInfixAt_singleton.mp hc
  cases hkind : A.abi.raKind with
  | stack =>
    simp only [Abi.raBytes, hkind, RaKind.raBytes] at hm
    obtain ⟨v0, hv0⟩ := region_sep_cell64 hm
    obtain ⟨hst, hmem'⟩ := store_cell64 (h.addrOf (k + 1)) hv0
    let sp' := s.gpr A.abi.sp - 8#64
    let s' := (s.setGpr A.abi.sp sp').setMem (storeMem s.mem i64 sp' (h.addrOf (k + 1)))
    refine vllMach_step_at hk ⟨.jump (h.labelAddr sym) s', by
      simp only [instrRel, hkind, hst, true_and, s', sp']⟩ ?_ ?_ ?_
    · intro _ hr; simp only [instrRel, hkind] at hr; cases hr.2
    · intro pc' s₁ hr
      simp only [instrRel, hkind] at hr
      cases hr.2
      refine hcont s' ?_ ?_ (by simp [vllFramePreds, hkind]) ?_
      · simp [s', sp', Abi.raBytes, hkind, RaKind.raBytes]
      · refine ⟨fun q hq => ?_, fun _ _ => rfl, fun _ _ => rfl⟩
        have hne : q ≠ A.abi.sp := fun e => hq (e ▸ List.mem_cons_self)
        exact MachSt.gpr_setGpr_ne s sp' hne
      · simpa only [vllFramePreds, hkind, s', sp', MachSt.mem_setMem,
          MachSt.gpr_setMem, MachSt.gpr_setGpr_same] using hmem'
    · intro _ _ hr; simp only [instrRel, hkind] at hr; cases hr.2
  | linkReg lr =>
    have hsp_ne_lr : A.abi.sp ≠ lr := by
      have hdisj := hwf.sp_disj.2.2.2.2.2
      simp only [Abi.raRegs, hkind, RaKind.raRegs, List.mem_singleton] at hdisj
      exact hdisj
    let s' := s.setGpr lr (h.addrOf (k + 1))
    refine vllMach_step_at hk ⟨.jump (h.labelAddr sym) s', by
      simp only [instrRel, hkind, s']⟩ ?_ ?_ ?_
    · intro _ hr; simp only [instrRel, hkind] at hr; cases hr
    · intro pc' s₁ hr
      simp only [instrRel, hkind] at hr
      cases hr
      refine hcont s' ?_ ?_ ?_ ?_
      · simp [s', Abi.raBytes, hkind, RaKind.raBytes, hsp_ne_lr]
      · refine ⟨fun q hq => ?_, fun _ _ => rfl, fun _ _ => rfl⟩
        have hne : q ≠ lr := fun e => hq (by
          rw [e]; apply List.mem_cons_of_mem; apply List.mem_append_left
          simp [Abi.raRegs, hkind, RaKind.raRegs])
        exact MachSt.gpr_setGpr_ne s _ hne
      · simp [vllFramePreds, hkind, s']
      · simp only [vllFramePreds, hkind, Abi.raBytes, RaKind.raBytes, BitVec.sub_zero] at hm ⊢
        simpa only [s', MachSt.mem_setGpr, MachSt.gpr_setGpr_ne _ _ hsp_ne_lr] using hm
    · intro _ _ hr; simp only [instrRel, hkind] at hr; cases hr

theorem vllMach_icall_spec {A : Arch} (hwf : A.Wf) {h : VllHost A} {k : Nat} {r : A.Reg}
    {s : MachSt A} {G : Mem 64 → Prop} {post : Config A → Prop}
    (hc : [Instr.icall r].IsInfixAt h.prog k)
    (hm : s.mem =⋆ region (s.gpr A.abi.sp - BitVec.ofNat 64 A.abi.raBytes) A.abi.raBytes ⋆ G)
    (hcont : ∀ s',
      s'.gpr A.abi.sp = s.gpr A.abi.sp - BitVec.ofNat 64 A.abi.raBytes →
      (vllMach A).Frame A.condReads s s'
        (A.abi.sp :: A.abi.raRegs ++ A.abi.scratch) [] FlagMask.all →
      (vllFramePreds A).raReg s' (h.addrOf (k + 1)) →
      (s'.mem =⋆ (vllFramePreds A).RetAddr (s'.gpr A.abi.sp) (h.addrOf (k + 1)) ⋆ G) →
      Eventually (vllStep h) post ⟨s', s.gpr r⟩) :
    (vllMach A).Run h k s post := by
  have hk : h.prog[k]? = some (.icall r) := List.isInfixAt_singleton.mp hc
  cases hkind : A.abi.raKind with
  | stack =>
    simp only [Abi.raBytes, hkind, RaKind.raBytes] at hm
    obtain ⟨v0, hv0⟩ := region_sep_cell64 hm
    obtain ⟨hst, hmem'⟩ := store_cell64 (h.addrOf (k + 1)) hv0
    let sp' := s.gpr A.abi.sp - 8#64
    let s' := (s.setGpr A.abi.sp sp').setMem (storeMem s.mem i64 sp' (h.addrOf (k + 1)))
    refine vllMach_step_at hk ⟨.jump (s.gpr r) s', by
      simp only [instrRel, hkind, hst, true_and, s', sp']⟩ ?_ ?_ ?_
    · intro _ hr; simp only [instrRel, hkind] at hr; cases hr.2
    · intro pc' s₁ hr
      simp only [instrRel, hkind] at hr
      cases hr.2
      refine hcont s' ?_ ?_ (by simp [vllFramePreds, hkind]) ?_
      · simp [s', sp', Abi.raBytes, hkind, RaKind.raBytes]
      · refine ⟨fun q hq => ?_, fun _ _ => rfl, fun _ _ => rfl⟩
        have hne : q ≠ A.abi.sp := fun e => hq (e ▸ List.mem_cons_self)
        exact MachSt.gpr_setGpr_ne s sp' hne
      · simpa only [vllFramePreds, hkind, s', sp', MachSt.mem_setMem,
          MachSt.gpr_setMem, MachSt.gpr_setGpr_same] using hmem'
    · intro _ _ hr; simp only [instrRel, hkind] at hr; cases hr.2
  | linkReg lr =>
    have hsp_ne_lr : A.abi.sp ≠ lr := by
      have hdisj := hwf.sp_disj.2.2.2.2.2
      simp only [Abi.raRegs, hkind, RaKind.raRegs, List.mem_singleton] at hdisj
      exact hdisj
    let s' := s.setGpr lr (h.addrOf (k + 1))
    refine vllMach_step_at hk ⟨.jump (s.gpr r) s', by
      simp only [instrRel, hkind, s']⟩ ?_ ?_ ?_
    · intro _ hr; simp only [instrRel, hkind] at hr; cases hr
    · intro pc' s₁ hr
      simp only [instrRel, hkind] at hr
      cases hr
      refine hcont s' ?_ ?_ ?_ ?_
      · simp [s', Abi.raBytes, hkind, RaKind.raBytes, hsp_ne_lr]
      · refine ⟨fun q hq => ?_, fun _ _ => rfl, fun _ _ => rfl⟩
        have hne : q ≠ lr := fun e => hq (by
          rw [e]; apply List.mem_cons_of_mem; apply List.mem_append_left
          simp [Abi.raRegs, hkind, RaKind.raRegs])
        exact MachSt.gpr_setGpr_ne s _ hne
      · simp [vllFramePreds, hkind, s']
      · simp only [vllFramePreds, hkind, Abi.raBytes, RaKind.raBytes, BitVec.sub_zero] at hm ⊢
        simpa only [s', MachSt.mem_setGpr, MachSt.gpr_setGpr_ne _ _ hsp_ne_lr] using hm
    · intro _ _ hr; simp only [instrRel, hkind] at hr; cases hr

theorem vllMach_ret_spec {A : Arch} {h : VllHost A} {k : Nat}
    {s : MachSt A} {ra : BitVec 64} {R : Mem 64 → Prop} {post : Config A → Prop}
    (hc : [Instr.ret].IsInfixAt h.prog k)
    (hra : (vllFramePreds A).raReg s ra)
    (hm : s.mem =⋆ (vllFramePreds A).RetAddr (s.gpr A.abi.sp) ra ⋆ R)
    (hcont : ∀ s',
      (vllMach A).KeepsGpr s s' (A.abi.sp :: A.abi.scratch) →
      (vllMach A).KeepsVec s s' [] →
      s'.gpr A.abi.sp = s.gpr A.abi.sp + BitVec.ofNat 64 A.abi.raBytes →
      s'.mem = s.mem →
      Eventually (vllStep h) post ⟨s', ra⟩) :
    (vllMach A).Run h k s post := by
  have hk : h.prog[k]? = some .ret := List.isInfixAt_singleton.mp hc
  cases hkind : A.abi.raKind with
  | stack =>
    simp only [vllFramePreds, hkind] at hm
    have hld : loadVal s.mem i64 (s.gpr A.abi.sp) = some ra := loadVal_cell64 hm
    let s' := s.setGpr A.abi.sp (s.gpr A.abi.sp + 8#64)
    refine vllMach_step_at hk ⟨.jump ra s', by
      simp only [instrRel, hkind, hld, Option.some.injEq, exists_eq_left', s']⟩ ?_ ?_ ?_
    · intro _ hr; simp only [instrRel, hkind, hld, Option.some.injEq, exists_eq_left'] at hr
      cases hr
    · intro pc' s₁ hr
      simp only [instrRel, hkind, hld, Option.some.injEq, exists_eq_left'] at hr
      cases hr
      refine hcont s' (fun q hq => ?_) (fun _ _ => rfl) ?_ rfl
      · have hne : q ≠ A.abi.sp := fun e => hq (e ▸ List.mem_cons_self)
        exact MachSt.gpr_setGpr_ne s _ hne
      · simp [s', Abi.raBytes, hkind, RaKind.raBytes]
    · intro _ _ hr; simp only [instrRel, hkind, hld, Option.some.injEq, exists_eq_left'] at hr
      cases hr
  | linkReg lr =>
    have hlr : s.gpr lr = ra := by simpa only [vllFramePreds, hkind] using hra
    refine vllMach_step_at hk ⟨.jump ra s, by simp [instrRel, hkind, hlr]⟩ ?_ ?_ ?_
    · intro _ hr; simp only [instrRel, hkind] at hr; cases hr
    · intro pc' s₁ hr
      simp only [instrRel, hkind, hlr] at hr
      cases hr
      refine hcont s (fun _ _ => rfl) (fun _ _ => rfl) ?_ rfl
      simp [Abi.raBytes, hkind, RaKind.raBytes]
    · intro _ _ hr; simp only [instrRel, hkind] at hr; cases hr

/-- Generic `FrameTarget` instance for `vllMach A` and `vllFrameIsa A`, discharging every
`Target.FrameSpec` obligation once for all architectures satisfying `A.Wf`. -/
def vllFrameTarget (A : Arch) (hwf : A.Wf) :
    FrameTarget (vllMach A) (vllFrameIsa A) A.condReads where
  toFramePreds := vllFramePreds A
  spec := {
    sp_disj := hwf.sp_disj
    scratch_disj := hwf.scratch_disj
    cs_disj := hwf.cs_disj
    ra_disj := hwf.ra_disj
    argRegs_nodup := hwf.argRegs_nodup
    retRegs_nodup := hwf.retRegs_nodup
    retAddr_region := by
      intro a ra m h
      cases hkind : A.abi.raKind with
      | stack =>
        simp only [vllFramePreds, hkind] at h
        simpa only [vllFrameIsa, Abi.raBytes, hkind, RaKind.raBytes] using cell64_region h
      | linkReg lr =>
        simp only [vllFramePreds, hkind] at h
        simpa only [vllFrameIsa, Abi.raBytes, hkind, RaKind.raBytes] using h
    raReg_of_raRegs := by
      intro s s' ra hkeep hra
      cases hkind : A.abi.raKind with
      | stack => simp [vllFramePreds, hkind]
      | linkReg lr =>
        simp only [vllFramePreds, hkind] at hra ⊢
        have hlr := hkeep lr (by simp [vllFrameIsa, Abi.raRegs, hkind, RaKind.raRegs])
        exact hlr.trans hra
    slots_le_frameSize := hwf.slots_le_frameSize
    spOk_frame := hwf.spOk_frame
    spEntry_call := hwf.spEntry_call
    labelAddr_eq := fun hk hfirst => VllHost.labelAddr_wf _ hk hfirst
    label_spec := fun hk hnext => vllMach_label_spec hk hnext
    prologue_spec := fun hra _ hbound hm => vllMach_prologue_spec hwf hra hbound hm
    epilogue_spec := fun _ hbound hm => vllMach_epilogue_spec hwf hbound hm
    slotSt_spec := fun _ _ hm => vllMach_slotSt_spec hm
    slotLd_spec := fun _ _ hm => vllMach_slotLd_spec hm
    canonAbi_spec := fun ht _ hholds => vllMach_canonAbi_spec hwf ht hholds
    call_spec := fun hc hm hcont => vllMach_call_spec hwf hc hm hcont
    exitJmp_spec := fun hc hcont =>
      vllMach_exitJmp_spec hc (hcont _ (Machine.Frame.refl _ _ _ _ _) rfl)
    ret_spec := fun hc hra hm hcont => vllMach_ret_spec hc hra hm hcont
  }

/-! ## 6. `Xcap.Mach (MachSt A) (Block A)` & Compositional Block WP Rules -/

/-- Execute a straight-line instruction list `body` under `symAddr`. An early jump or halt
(e.g. from a `.native` control instruction) terminates the body immediately. -/
inductive ExecBody (A : Arch) (symAddr : Sym → BitVec 64) :
    List (Instr A) → MachSt A → InstrOut A → Prop where
  | nil {s} : ExecBody A symAddr [] s (.fall s)
  | cons_fall {i is s s₁ out} :
      instrRel A symAddr 0#64 i s (.fall s₁) →
      ExecBody A symAddr is s₁ out →
      ExecBody A symAddr (i :: is) s out
  | cons_jump {i is s pc' s'} :
      instrRel A symAddr 0#64 i s (.jump pc' s') →
      ExecBody A symAddr (i :: is) s (.jump pc' s')
  | cons_halt {i is s c s'} :
      instrRel A symAddr 0#64 i s (.halt c s') →
      ExecBody A symAddr (i :: is) s (.halt c s')

/-- Operational semantics of a block terminator `Term A`, producing an `Xcap.Out (MachSt A)`. -/
@[expose] def termExec (A : Arch) (symAddr : Sym → BitVec 64) :
    Term A → MachSt A → Xcap.Out (MachSt A) → Prop
  | .fall next, s, o => o = .jump (symAddr next) s
  | .jmp l, s, o => o = .jump (symAddr l) s
  | .jcc c l fall, s, o =>
    o = .jump (if A.evalCond s.flags c then symAddr l else symAddr fall) s
  | .jnzGpr r l fall, s, o =>
    let s' := s.setFlags (A.jnzGprFlags (s.gpr r) s.flags)
    o = .jump (if (s.gpr r).setWidth 8 != 0#8 then symAddr l else symAddr fall) s'
  | .call sym retL, s, o =>
    match A.abi.raKind with
    | .stack =>
      let sp' := s.gpr A.abi.sp - 8#64
      storeOk s.mem i64 sp' ∧
        o = .jump (symAddr sym)
          ((s.setGpr A.abi.sp sp').setMem (storeMem s.mem i64 sp' (symAddr retL)))
    | .linkReg lr =>
      o = .jump (symAddr sym) (s.setGpr lr (symAddr retL))
  | .icall r retL, s, o =>
    let tgt := s.gpr r
    match A.abi.raKind with
    | .stack =>
      let sp' := s.gpr A.abi.sp - 8#64
      storeOk s.mem i64 sp' ∧
        o = .jump tgt
          ((s.setGpr A.abi.sp sp').setMem (storeMem s.mem i64 sp' (symAddr retL)))
    | .linkReg lr =>
      o = .jump tgt (s.setGpr lr (symAddr retL))
  | .ret, s, o =>
    match A.abi.raKind with
    | .stack =>
      ∃ ra : BitVec 64, loadVal s.mem i64 (s.gpr A.abi.sp) = some ra ∧
        o = .jump ra (s.setGpr A.abi.sp (s.gpr A.abi.sp + 8#64))
    | .linkReg lr =>
      o = .jump (s.gpr lr) s
  | .exitJmp sym, s, o => o = .jump (symAddr sym) s
  | .tailJmpR r, s, o => o = .jump (s.gpr r) s
  | .ijmp r, s, o => o = .jump (s.gpr r) s
  | .halt r, s, o => o = .halt (s.gpr r) s
  | .nativeTerm d, s, o =>
    ∃ no, A.nativeStep d symAddr s no ∧
      match no with
      | .fall _ => False
      | .jump pc' s' => o = .jump pc' s'
      | .halt c s' => o = .halt c s'

/-- Full basic-block execution relation combining `ExecBody` and `termExec`. -/
inductive BlockExec (A : Arch) (symAddr : Sym → BitVec 64) (b : Block A) (s : MachSt A) :
    Xcap.Out (MachSt A) → Prop where
  | fall {s₁ o} :
      ExecBody A symAddr b.body s (.fall s₁) →
      termExec A symAddr b.term s₁ o →
      BlockExec A symAddr b s o
  | earlyJump {pc' s'} :
      ExecBody A symAddr b.body s (.jump pc' s') →
      BlockExec A symAddr b s (.jump pc' s')
  | earlyHalt {c s'} :
      ExecBody A symAddr b.body s (.halt c s') →
      BlockExec A symAddr b s (.halt c s')

/-- `BedrockMach` L1 instantiated as a generic `Xcap.Mach (MachSt A) (Block A)`, connecting
open `ijmp`, hardware `call`/`icall`/`ret`, and `.native` directly to `Xcap` (`Lfp`/`Core`/
`Link`). -/
@[expose] def vllXcapMach (A : Arch) (symAddr : Sym → BitVec 64) :
    Xcap.Mach (MachSt A) (Block A) where
  exec := BlockExec A symAddr

/-- View a `VllCodeMap A` as an `Xcap.Code (Block A)`. -/
@[expose] def VllCodeMap.toXcapCode {A : Arch} (cm : VllCodeMap A) : Xcap.Code (Block A) :=
  cm.lookupPc

/-- Weakest precondition of a `VllCodeMap A` via `Xcap.wp`. -/
@[expose] def VllCodeMap.wp {A : Arch} (cm : VllCodeMap A) (H : Xcap.Halt (MachSt A)) :
    Xcap.CodeSpec (MachSt A) :=
  Xcap.wp (vllXcapMach A cm.symAddr) cm.toXcapCode H

/-- Big-step halting relation of a `VllCodeMap A` via `Xcap.Halts`. -/
@[expose] def VllCodeMap.Halts {A : Arch} (cm : VllCodeMap A) :
    BitVec 64 → MachSt A → BitVec 64 → MachSt A → Prop :=
  Xcap.Halts (vllXcapMach A cm.symAddr) cm.toXcapCode

/-- Adequacy for `VllCodeMap.wp`: every `wp`-verified entry terminates in a state satisfying `H`. -/
theorem VllCodeMap.adequacy {A : Arch} {cm : VllCodeMap A} {H : Xcap.Halt (MachSt A)}
    {pc : BitVec 64} {s : MachSt A} (h : cm.wp H pc s) :
    ∃ c s', cm.Halts pc s c s' ∧ H c s' :=
  Xcap.adequacy h

/-- `Nat`-ranked invariant introduction for loops and cyclic SCCs in a `VllCodeMap A`. -/
theorem VllCodeMap.wp_of_ranked {A : Arch} {cm : VllCodeMap A} {H : Xcap.Halt (MachSt A)}
    (I : Nat → Xcap.CodeSpec (MachSt A))
    (hI : ∀ n pc s, I n pc s → ∃ b, cm.lookupPc pc = some b ∧
      Xcap.bwp (vllXcapMach A cm.symAddr) b
        (fun pc' s' => ∃ k, k < n ∧ I k pc' s') H s) :
    ∀ n pc s, I n pc s → cm.wp H pc s :=
  Xcap.wp_of_ranked I hI

/-- Single-instruction WP predicate for compositional `Block` verification. -/
@[expose] def instrWp (A : Arch) (symAddr : Sym → BitVec 64) (i : Instr A)
    (K : MachSt A → Prop) (Ψ : Xcap.CodeSpec (MachSt A)) (H : Xcap.Halt (MachSt A))
    (s : MachSt A) : Prop :=
  (∃ o, instrRel A symAddr 0#64 i s o) ∧
  (∀ s', instrRel A symAddr 0#64 i s (.fall s') → K s') ∧
  (∀ pc' s', instrRel A symAddr 0#64 i s (.jump pc' s') → Ψ pc' s') ∧
  (∀ c s', instrRel A symAddr 0#64 i s (.halt c s') → H c s')

/-- Straight-line body WP predicate threading `K` across `List (Instr A)`. -/
@[expose] def bodyWp (A : Arch) (symAddr : Sym → BitVec 64) :
    List (Instr A) → (MachSt A → Prop) → Xcap.CodeSpec (MachSt A) →
    Xcap.Halt (MachSt A) → MachSt A → Prop
  | [], K, _, _, s => K s
  | i :: is, K, Ψ, H, s => instrWp A symAddr i (bodyWp A symAddr is K Ψ H) Ψ H s

/-- Terminator WP predicate matching `Xcap.bwp`. -/
@[expose] def termWp (A : Arch) (symAddr : Sym → BitVec 64) (t : Term A)
    (Ψ : Xcap.CodeSpec (MachSt A)) (H : Xcap.Halt (MachSt A)) (s : MachSt A) : Prop :=
  (∃ o, termExec A symAddr t s o) ∧
  (∀ pc' s', termExec A symAddr t s (.jump pc' s') → Ψ pc' s') ∧
  (∀ c s', termExec A symAddr t s (.halt c s') → H c s')

private theorem execBody_exists_of_bodyWp {A : Arch} {symAddr : Sym → BitVec 64}
    {Ψ : Xcap.CodeSpec (MachSt A)} {H : Xcap.Halt (MachSt A)} {K : MachSt A → Prop} :
    ∀ {is : List (Instr A)} {s : MachSt A},
      bodyWp A symAddr is K Ψ H s →
      (∀ s₁, K s₁ → ∃ o, ExecBody A symAddr [] s₁ o ∧
        (∀ s₂, o = .fall s₂ → K s₂)) →
      ∃ o, ExecBody A symAddr is s o ∧
        (∀ s', o = .fall s' → K s')
  | [], s, hK, _ => ⟨.fall s, .nil, fun _ heq => by cases heq; exact hK⟩
  | i :: is, s, ⟨⟨o₁, ho₁⟩, hf, _, _⟩, hnil => by
    cases o₁ with
    | fall s₁ =>
      obtain ⟨o₂, hex₂, hK₂⟩ := execBody_exists_of_bodyWp (hf s₁ ho₁) hnil
      exact ⟨o₂, .cons_fall ho₁ hex₂, hK₂⟩
    | jump pc' s' =>
      exact ⟨.jump pc' s', .cons_jump ho₁, fun _ h => nomatch h⟩
    | halt c s' =>
      exact ⟨.halt c s', .cons_halt ho₁, fun _ h => nomatch h⟩

private theorem execBody_sound_of_bodyWp {A : Arch} {symAddr : Sym → BitVec 64}
    {Ψ : Xcap.CodeSpec (MachSt A)} {H : Xcap.Halt (MachSt A)} {K : MachSt A → Prop} :
    ∀ {is : List (Instr A)} {s : MachSt A} {o : InstrOut A},
      ExecBody A symAddr is s o →
      bodyWp A symAddr is K Ψ H s →
      (match o with
      | .fall s' => K s'
      | .jump pc' s' => Ψ pc' s'
      | .halt c s' => H c s')
  | _, _, _, .nil, hK => hK
  | _, _, _, .cons_fall hr hex, ⟨_, hf, _, _⟩ =>
    execBody_sound_of_bodyWp hex (hf _ hr)
  | _, _, _, .cons_jump hr, ⟨_, _, hj, _⟩ => hj _ _ hr
  | _, _, _, .cons_halt hr, ⟨_, _, _, hh⟩ => hh _ _ hr

/-- Compositional `Xcap.bwp` introduction for any `Block A` from `bodyWp` + `termWp`. -/
theorem bwp_of_bodyWp {A : Arch} {symAddr : Sym → BitVec 64} {b : Block A}
    {Ψ : Xcap.CodeSpec (MachSt A)} {H : Xcap.Halt (MachSt A)} {s : MachSt A}
    (h : bodyWp A symAddr b.body (termWp A symAddr b.term Ψ H) Ψ H s) :
    Xcap.bwp (vllXcapMach A symAddr) b Ψ H s := by
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨o, hex, hK⟩ := execBody_exists_of_bodyWp h
      (fun s₁ h1 => ⟨.fall s₁, .nil, fun _ heq => by cases heq; exact h1⟩)
    cases o with
    | fall s₁ =>
      obtain ⟨⟨ot, hot⟩, _, _⟩ := hK s₁ rfl
      exact ⟨ot, .fall hex hot⟩
    | jump pc' s' => exact ⟨.jump pc' s', .earlyJump hex⟩
    | halt c s' => exact ⟨.halt c s', .earlyHalt hex⟩
  · intro pc' s' hbe
    cases hbe with
    | fall hex hterm =>
      have ht := execBody_sound_of_bodyWp hex h
      exact ht.2.1 pc' s' hterm
    | earlyJump hex =>
      exact execBody_sound_of_bodyWp hex h
  · intro c s' hbe
    cases hbe with
    | fall hex hterm =>
      have ht := execBody_sound_of_bodyWp hex h
      exact ht.2.2 c s' hterm
    | earlyHalt hex =>
      exact execBody_sound_of_bodyWp hex h

/-! ### Compositional `instrWp` and `termWp` Rules -/

theorem instrWp_det {A : Arch} {symAddr : Sym → BitVec 64} {i : Instr A}
    {K : MachSt A → Prop} {Ψ : Xcap.CodeSpec (MachSt A)} {H : Xcap.Halt (MachSt A)}
    {s s' : MachSt A}
    (hrel : ∀ o, instrRel A symAddr 0#64 i s o ↔ o = .fall s')
    (hk : K s') :
    instrWp A symAddr i K Ψ H s := by
  refine ⟨⟨.fall s', (hrel _).mpr rfl⟩, ?_, ?_, ?_⟩
  · intro s₁ hr; have h1 := (hrel _).mp hr; cases h1; exact hk
  · intro _ _ hr; have h1 := (hrel _).mp hr; cases h1
  · intro _ _ hr; have h1 := (hrel _).mp hr; cases h1

theorem instrWp_label {A : Arch} {symAddr : Sym → BitVec 64} {l : Sym}
    {K : MachSt A → Prop} {Ψ : Xcap.CodeSpec (MachSt A)} {H : Xcap.Halt (MachSt A)}
    {s : MachSt A} (hk : K s) :
    instrWp A symAddr (.label l) K Ψ H s :=
  instrWp_det (fun _ => Iff.rfl) hk

theorem instrWp_pad {A : Arch} {symAddr : Sym → BitVec 64} {pk : PadKind}
    {K : MachSt A → Prop} {Ψ : Xcap.CodeSpec (MachSt A)} {H : Xcap.Halt (MachSt A)}
    {s : MachSt A} (hk : K s) :
    instrWp A symAddr (.pad pk) K Ψ H s :=
  instrWp_det (fun _ => Iff.rfl) hk

theorem instrWp_mov {A : Arch} {symAddr : Sym → BitVec 64} {w : Width} {rd rs : A.Reg}
    {K : MachSt A → Prop} {Ψ : Xcap.CodeSpec (MachSt A)} {H : Xcap.Halt (MachSt A)}
    {s : MachSt A} (hk : K (s.setGprW w rd ((s.gpr rs).setWidth w.bits))) :
    instrWp A symAddr (.mov w rd rs) K Ψ H s :=
  instrWp_det (fun _ => Iff.rfl) hk

theorem instrWp_movi {A : Arch} {symAddr : Sym → BitVec 64} {rd : A.Reg} {imm : BitVec 64}
    {K : MachSt A → Prop} {Ψ : Xcap.CodeSpec (MachSt A)} {H : Xcap.Halt (MachSt A)}
    {s : MachSt A} (hk : K (s.setGpr rd imm)) :
    instrWp A symAddr (.movi rd imm) K Ψ H s :=
  instrWp_det (fun _ => Iff.rfl) hk

theorem instrWp_alu {A : Arch} {symAddr : Sym → BitVec 64} {op : CoreAlu} {w : Width}
    {rd lhs : A.Reg} {rhs : Src A} {sf : Bool}
    {K : MachSt A → Prop} {Ψ : Xcap.CodeSpec (MachSt A)} {H : Xcap.Halt (MachSt A)}
    {s : MachSt A}
    (hk : K ((s.setGprW w rd (op.eval w ((s.gpr lhs).setWidth w.bits) (rhs.evalW w s.gpr))).setFlags
      (A.aluFlags op w sf ((s.gpr lhs).setWidth w.bits) (rhs.evalW w s.gpr) s.flags))) :
    instrWp A symAddr (.alu op w rd lhs rhs sf) K Ψ H s :=
  instrWp_det (fun _ => Iff.rfl) hk

theorem instrWp_cmp {A : Arch} {symAddr : Sym → BitVec 64} {w : Width} {lhs : A.Reg}
    {rhs : Src A} {K : MachSt A → Prop} {Ψ : Xcap.CodeSpec (MachSt A)} {H : Xcap.Halt (MachSt A)}
    {s : MachSt A}
    (hk : K (s.setFlags (A.cmpFlags w ((s.gpr lhs).setWidth w.bits) (rhs.evalW w s.gpr) s.flags))) :
    instrWp A symAddr (.cmp w lhs rhs) K Ψ H s :=
  instrWp_det (fun _ => Iff.rfl) hk

theorem instrWp_test {A : Arch} {symAddr : Sym → BitVec 64} {w : Width} {lhs : A.Reg}
    {rhs : Src A} {K : MachSt A → Prop} {Ψ : Xcap.CodeSpec (MachSt A)} {H : Xcap.Halt (MachSt A)}
    {s : MachSt A}
    (hk : K (s.setFlags
      (A.testFlags w ((s.gpr lhs).setWidth w.bits) (rhs.evalW w s.gpr) s.flags))) :
    instrWp A symAddr (.test w lhs rhs) K Ψ H s :=
  instrWp_det (fun _ => Iff.rfl) hk

theorem instrWp_setcc {A : Arch} {symAddr : Sym → BitVec 64} {rd : A.Reg} {c : A.Cond}
    {K : MachSt A → Prop} {Ψ : Xcap.CodeSpec (MachSt A)} {H : Xcap.Halt (MachSt A)}
    {s : MachSt A} (hk : K (s.setGprW .w8 rd (BitVec.ofNat 8 (A.evalCond s.flags c).toNat))) :
    instrWp A symAddr (.setcc rd c) K Ψ H s :=
  instrWp_det (fun _ => Iff.rfl) hk

theorem instrWp_load {A : Arch} {symAddr : Sym → BitVec 64} {w : Width} {ext : LoadExt}
    {rd : A.Reg} {addr : AddrArg A.Reg} {v : BitVec w.bits}
    {K : MachSt A → Prop} {Ψ : Xcap.CodeSpec (MachSt A)} {H : Xcap.Halt (MachSt A)}
    {s : MachSt A}
    (hld : loadVal s.mem w.toTy (addr.eval s.gpr) = some v)
    (hk : K (s.setGpr rd (ext.apply A w (s.gpr rd) v))) :
    instrWp A symAddr (.load w ext rd addr) K Ψ H s := by
  refine instrWp_det ?_ hk
  intro o
  simp only [instrRel, hld, Option.some.injEq, exists_eq_left']

theorem instrWp_store {A : Arch} {symAddr : Sym → BitVec 64} {w : Width} {rs : A.Reg}
    {addr : AddrArg A.Reg} {K : MachSt A → Prop} {Ψ : Xcap.CodeSpec (MachSt A)}
    {H : Xcap.Halt (MachSt A)} {s : MachSt A}
    (hst : storeOk s.mem w.toTy (addr.eval s.gpr))
    (hk : K (s.setMem (storeMem s.mem w.toTy (addr.eval s.gpr) ((s.gpr rs).setWidth w.bits)))) :
    instrWp A symAddr (.store w rs addr) K Ψ H s := by
  refine instrWp_det ?_ hk
  intro o
  simp only [instrRel, hst, true_and]

theorem instrWp_symAddr {A : Arch} {symAddr : Sym → BitVec 64} {sym : Sym} {rd : A.Reg}
    {K : MachSt A → Prop} {Ψ : Xcap.CodeSpec (MachSt A)} {H : Xcap.Halt (MachSt A)}
    {s : MachSt A} (hk : K (s.setGpr rd (symAddr sym))) :
    instrWp A symAddr (.symAddr sym rd) K Ψ H s :=
  instrWp_det (fun _ => Iff.rfl) hk

theorem instrWp_native {A : Arch} {symAddr : Sym → BitVec 64} {d : A.Native}
    {K : MachSt A → Prop} {Ψ : Xcap.CodeSpec (MachSt A)} {H : Xcap.Halt (MachSt A)}
    {s : MachSt A}
    (hex : ∃ no, A.nativeStep d symAddr s no)
    (hfall : ∀ s', A.nativeStep d symAddr s (.fall s') → K s')
    (hjump : ∀ pc' s', A.nativeStep d symAddr s (.jump pc' s') → Ψ pc' s')
    (hhalt : ∀ c s', A.nativeStep d symAddr s (.halt c s') → H c s') :
    instrWp A symAddr (.native d) K Ψ H s := by
  obtain ⟨no₀, hno₀⟩ := hex
  refine ⟨⟨no₀.toInstrOut, no₀, hno₀, rfl⟩, ?_, ?_, ?_⟩
  · intro s' ⟨no, hst, heq⟩
    cases no with
    | fall s₁ => cases heq; exact hfall s' hst
    | jump _ _ => cases heq
    | halt _ _ => cases heq
  · intro pc' s' ⟨no, hst, heq⟩
    cases no with
    | fall _ => cases heq
    | jump p₁ s₁ => cases heq; exact hjump pc' s' hst
    | halt _ _ => cases heq
  · intro c s' ⟨no, hst, heq⟩
    cases no with
    | fall _ => cases heq
    | jump _ _ => cases heq
    | halt c₁ s₁ => cases heq; exact hhalt c s' hst

theorem termWp_fall {A : Arch} {symAddr : Sym → BitVec 64} {next : Sym}
    {Ψ : Xcap.CodeSpec (MachSt A)} {H : Xcap.Halt (MachSt A)} {s : MachSt A}
    (h : Ψ (symAddr next) s) :
    termWp A symAddr (.fall next) Ψ H s :=
  ⟨⟨_, rfl⟩, fun _ _ ho => by cases ho; exact h, fun _ _ ho => by cases ho⟩

theorem termWp_jmp {A : Arch} {symAddr : Sym → BitVec 64} {l : Sym}
    {Ψ : Xcap.CodeSpec (MachSt A)} {H : Xcap.Halt (MachSt A)} {s : MachSt A}
    (h : Ψ (symAddr l) s) :
    termWp A symAddr (.jmp l) Ψ H s :=
  ⟨⟨_, rfl⟩, fun _ _ ho => by cases ho; exact h, fun _ _ ho => by cases ho⟩

theorem termWp_jcc {A : Arch} {symAddr : Sym → BitVec 64} {c : A.Cond} {l fall : Sym}
    {Ψ : Xcap.CodeSpec (MachSt A)} {H : Xcap.Halt (MachSt A)} {s : MachSt A}
    (ht : A.evalCond s.flags c = true → Ψ (symAddr l) s)
    (hf : A.evalCond s.flags c = false → Ψ (symAddr fall) s) :
    termWp A symAddr (.jcc c l fall) Ψ H s := by
  refine ⟨⟨_, rfl⟩, fun pc' s' ho => ?_, fun _ _ ho => by cases ho⟩
  cases ho
  cases hc : A.evalCond s.flags c
  · simpa [hc] using hf hc
  · simpa [hc] using ht hc

theorem termWp_jnzGpr {A : Arch} {symAddr : Sym → BitVec 64} {r : A.Reg} {l fall : Sym}
    {Ψ : Xcap.CodeSpec (MachSt A)} {H : Xcap.Halt (MachSt A)} {s : MachSt A}
    (ht : ((s.gpr r).setWidth 8 != 0#8) = true →
      Ψ (symAddr l) (s.setFlags (A.jnzGprFlags (s.gpr r) s.flags)))
    (hf : ((s.gpr r).setWidth 8 != 0#8) = false →
      Ψ (symAddr fall) (s.setFlags (A.jnzGprFlags (s.gpr r) s.flags))) :
    termWp A symAddr (.jnzGpr r l fall) Ψ H s := by
  refine ⟨⟨_, rfl⟩, fun pc' s' ho => ?_, fun _ _ ho => by cases ho⟩
  cases ho
  cases hz : ((s.gpr r).setWidth 8 != 0#8)
  · simpa [hz] using hf hz
  · simpa [hz] using ht hz

theorem termWp_call_linkReg {A : Arch} {symAddr : Sym → BitVec 64} {lr : A.Reg}
    {sym retL : Sym} {Ψ : Xcap.CodeSpec (MachSt A)} {H : Xcap.Halt (MachSt A)} {s : MachSt A}
    (hkind : A.abi.raKind = .linkReg lr)
    (h : Ψ (symAddr sym) (s.setGpr lr (symAddr retL))) :
    termWp A symAddr (.call sym retL) Ψ H s := by
  refine ⟨⟨.jump (symAddr sym) (s.setGpr lr (symAddr retL)),
    by simp [termExec, hkind]⟩, ?_, ?_⟩
  · intro pc' s' ho; simp only [termExec, hkind] at ho; cases ho; exact h
  · intro _ _ ho; simp only [termExec, hkind] at ho; cases ho

theorem termWp_call_stack {A : Arch} {symAddr : Sym → BitVec 64}
    {sym retL : Sym} {Ψ : Xcap.CodeSpec (MachSt A)} {H : Xcap.Halt (MachSt A)} {s : MachSt A}
    (hkind : A.abi.raKind = .stack)
    (hst : storeOk s.mem i64 (s.gpr A.abi.sp - 8#64))
    (h : Ψ (symAddr sym)
      ((s.setGpr A.abi.sp (s.gpr A.abi.sp - 8#64)).setMem
        (storeMem s.mem i64 (s.gpr A.abi.sp - 8#64) (symAddr retL)))) :
    termWp A symAddr (.call sym retL) Ψ H s := by
  refine ⟨⟨.jump (symAddr sym)
    ((s.setGpr A.abi.sp (s.gpr A.abi.sp - 8#64)).setMem
      (storeMem s.mem i64 (s.gpr A.abi.sp - 8#64) (symAddr retL))),
    by simp [termExec, hkind, hst]⟩, ?_, ?_⟩
  · intro pc' s' ho; simp only [termExec, hkind] at ho; cases ho.2; exact h
  · intro _ _ ho; simp only [termExec, hkind] at ho; cases ho.2

theorem termWp_icall_linkReg {A : Arch} {symAddr : Sym → BitVec 64} {lr r : A.Reg}
    {retL : Sym} {Ψ : Xcap.CodeSpec (MachSt A)} {H : Xcap.Halt (MachSt A)} {s : MachSt A}
    (hkind : A.abi.raKind = .linkReg lr)
    (h : Ψ (s.gpr r) (s.setGpr lr (symAddr retL))) :
    termWp A symAddr (.icall r retL) Ψ H s := by
  refine ⟨⟨.jump (s.gpr r) (s.setGpr lr (symAddr retL)),
    by simp [termExec, hkind]⟩, ?_, ?_⟩
  · intro pc' s' ho; simp only [termExec, hkind] at ho; cases ho; exact h
  · intro _ _ ho; simp only [termExec, hkind] at ho; cases ho

theorem termWp_ret_linkReg {A : Arch} {symAddr : Sym → BitVec 64} {lr : A.Reg}
    {Ψ : Xcap.CodeSpec (MachSt A)} {H : Xcap.Halt (MachSt A)} {s : MachSt A}
    (hkind : A.abi.raKind = .linkReg lr)
    (h : Ψ (s.gpr lr) s) :
    termWp A symAddr .ret Ψ H s := by
  refine ⟨⟨.jump (s.gpr lr) s, by simp [termExec, hkind]⟩, ?_, ?_⟩
  · intro pc' s' ho; simp only [termExec, hkind] at ho; cases ho; exact h
  · intro _ _ ho; simp only [termExec, hkind] at ho; cases ho

theorem termWp_ret_stack {A : Arch} {symAddr : Sym → BitVec 64} {ra : BitVec 64}
    {Ψ : Xcap.CodeSpec (MachSt A)} {H : Xcap.Halt (MachSt A)} {s : MachSt A}
    (hkind : A.abi.raKind = .stack)
    (hld : loadVal s.mem i64 (s.gpr A.abi.sp) = some ra)
    (h : Ψ ra (s.setGpr A.abi.sp (s.gpr A.abi.sp + 8#64))) :
    termWp A symAddr .ret Ψ H s := by
  refine ⟨⟨.jump ra (s.setGpr A.abi.sp (s.gpr A.abi.sp + 8#64)),
    by simp [termExec, hkind, hld]⟩, ?_, ?_⟩
  · intro pc' s' ho
    simp only [termExec, hkind, hld, Option.some.injEq, exists_eq_left'] at ho
    cases ho; exact h
  · intro _ _ ho
    simp only [termExec, hkind, hld, Option.some.injEq, exists_eq_left'] at ho
    cases ho

theorem termWp_ijmp {A : Arch} {symAddr : Sym → BitVec 64} {r : A.Reg}
    {Ψ : Xcap.CodeSpec (MachSt A)} {H : Xcap.Halt (MachSt A)} {s : MachSt A}
    (h : Ψ (s.gpr r) s) :
    termWp A symAddr (.ijmp r) Ψ H s :=
  ⟨⟨_, rfl⟩, (fun _ _ ho => by cases ho; exact h), (fun _ _ ho => by cases ho)⟩

theorem termWp_tailJmpR {A : Arch} {symAddr : Sym → BitVec 64} {r : A.Reg}
    {Ψ : Xcap.CodeSpec (MachSt A)} {H : Xcap.Halt (MachSt A)} {s : MachSt A}
    (h : Ψ (s.gpr r) s) :
    termWp A symAddr (.tailJmpR r) Ψ H s :=
  ⟨⟨_, rfl⟩, (fun _ _ ho => by cases ho; exact h), (fun _ _ ho => by cases ho)⟩

theorem termWp_exitJmp {A : Arch} {symAddr : Sym → BitVec 64} {sym : Sym}
    {Ψ : Xcap.CodeSpec (MachSt A)} {H : Xcap.Halt (MachSt A)} {s : MachSt A}
    (h : Ψ (symAddr sym) s) :
    termWp A symAddr (.exitJmp sym) Ψ H s :=
  ⟨⟨_, rfl⟩, (fun _ _ ho => by cases ho; exact h), (fun _ _ ho => by cases ho)⟩

theorem termWp_halt {A : Arch} {symAddr : Sym → BitVec 64} {r : A.Reg}
    {Ψ : Xcap.CodeSpec (MachSt A)} {H : Xcap.Halt (MachSt A)} {s : MachSt A}
    (h : H (s.gpr r) s) :
    termWp A symAddr (.halt r) Ψ H s :=
  ⟨⟨_, rfl⟩, (fun _ _ ho => by cases ho), (fun _ _ ho => by cases ho; exact h)⟩

/-! ### Hardware-Call XCAP `cptr` Preconditions (`vllCallPre`) -/

/-- Generic XCAP call precondition for `BedrockMach` L1: `Pre s` holds and the hardware return
target (either `gpr lr` under `.linkReg lr`, or `[sp]` under `.stack`) is a valid `Xcap.cptr`
for `Post` (matching `Xcap.callPre` on `.linkReg` and stack-popped `Post` on `.stack`). -/
@[expose] def vllCallPre (A : Arch) (Pre Post : MachSt A → Prop) :
    Xcap.CodeSpec (MachSt A) → MachSt A → Prop :=
  match A.abi.raKind with
  | .linkReg lr => Xcap.callPre (fun s => s.gpr lr) Pre Post
  | .stack => fun Ψ s =>
      Pre s ∧ ∃ ra, loadVal s.mem i64 (s.gpr A.abi.sp) = some ra ∧
        Xcap.cptr Ψ ra (fun s' => Post s')

/-- Using a `cptr` at `vllCallPre` for a `.linkReg` hardware `call sym retL`. -/
theorem termWp_call_cptr_linkReg {A : Arch} {symAddr : Sym → BitVec 64} {lr : A.Reg}
    {sym retL : Sym} {Pre Post : MachSt A → Prop}
    {Ψ : Xcap.CodeSpec (MachSt A)} {H : Xcap.Halt (MachSt A)} {s : MachSt A}
    (hkind : A.abi.raKind = .linkReg lr)
    (hcallee : Xcap.cptr Ψ (symAddr sym) (vllCallPre A Pre Post Ψ))
    (hpre : Pre (s.setGpr lr (symAddr retL)))
    (hret : Xcap.cptr Ψ (symAddr retL) Post) :
    termWp A symAddr (.call sym retL) Ψ H s := by
  refine termWp_call_linkReg hkind ?_
  apply hcallee
  simp only [vllCallPre, hkind, Xcap.callPre, MachSt.gpr_setGpr_same]
  exact ⟨hpre, hret⟩

/-- Using a `cptr` at `vllCallPre` for a `.stack` hardware `call sym retL`. -/
theorem termWp_call_cptr_stack {A : Arch} {symAddr : Sym → BitVec 64}
    {sym retL : Sym} {Pre Post : MachSt A → Prop}
    {Ψ : Xcap.CodeSpec (MachSt A)} {H : Xcap.Halt (MachSt A)}
    {s : MachSt A} {G : Mem 64 → Prop}
    (hkind : A.abi.raKind = .stack)
    (hm : s.mem =⋆ region (s.gpr A.abi.sp - 8#64) 8 ⋆ G)
    (hcallee : Xcap.cptr Ψ (symAddr sym) (vllCallPre A Pre Post Ψ))
    (hpre : Pre ((s.setGpr A.abi.sp (s.gpr A.abi.sp - 8#64)).setMem
      (storeMem s.mem i64 (s.gpr A.abi.sp - 8#64) (symAddr retL))))
    (hret : Xcap.cptr Ψ (symAddr retL) Post) :
    termWp A symAddr (.call sym retL) Ψ H s := by
  obtain ⟨v0, hv0⟩ := region_sep_cell64 hm
  obtain ⟨hst, hmem'⟩ := store_cell64 (symAddr retL) hv0
  refine termWp_call_stack hkind hst ?_
  apply hcallee
  simp only [vllCallPre, hkind]
  refine ⟨hpre, symAddr retL, ?_, hret⟩
  simpa only [MachSt.mem_setMem, MachSt.gpr_setMem, MachSt.gpr_setGpr_same]
    using loadVal_cell64 hmem'

/-! ## 7. Bridge Between `bodyWp` (XCAP) and `vllMach.Run` (Small-Step `Machine`) -/

/-- Any straight-line instruction sequence satisfying `bodyWp` with no early jumps/halts
advances `vllMach.Run` from index `k` to `k + is.length`. -/
theorem vllMach_run_of_bodyWp {A : Arch} {h : VllHost A} {K : MachSt A → Prop}
    {post : Config A → Prop} :
    ∀ {is : List (Instr A)} {k : Nat} {s : MachSt A},
      is.IsInfixAt h.prog k →
      (∀ i ∈ is, ∀ sym, i ≠ .call sym) →
      (∀ i ∈ is, ∀ r, i ≠ .icall r) →
      bodyWp A h.labelAddr is K (fun _ _ => False) (fun _ _ => False) s →
      (∀ s', K s' → (vllMach A).Run h (k + is.length) s' post) →
      (vllMach A).Run h k s post
  | [], k, s, _, _, _, hK, hcont => by
    simpa only [List.length_nil, Nat.add_zero] using hcont s hK
  | i :: is, k, s, hinf, hnc, hnic, hwp, hcont => by
    obtain ⟨hk, hinf'⟩ := List.IsInfixAt.cons hinf
    have hnc_i : ∀ sym, i ≠ .call sym := fun sym => hnc i List.mem_cons_self sym
    have hnic_i : ∀ r, i ≠ .icall r := fun r => hnic i List.mem_cons_self r
    have heq_rel : ∀ o, instrRel A h.labelAddr (h.addrOf (k + 1)) i s o ↔
        instrRel A h.labelAddr 0#64 i s o := by
      intro o
      cases i with
      | call sym => exact absurd rfl (hnc_i sym)
      | icall r => exact absurd rfl (hnic_i r)
      | label _ | pad _ | mov _ _ _ | movi _ _ | alu _ _ _ _ _ _ | cmp _ _ _
      | test _ _ _ | clearFlags | setcc _ _ | load _ _ _ _ | store _ _ _
      | slotSt _ _ | slotLd _ _ | prologue _ | epilogue _ | canonAbi _ _
      | jmp _ | jcc _ _ | jnzGpr _ _ | ret | exitJmp _ | tailJmpR _
      | symAddr _ _ | ijmp _ | native _ => exact Iff.rfl
    obtain ⟨⟨o₀, ho₀⟩, hfall, hjump, hhalt⟩ := hwp
    refine vllMach_step_at hk ⟨o₀, (heq_rel o₀).mpr ho₀⟩ ?_ ?_ ?_
    · intro s₁ hr
      have hr0 := (heq_rel _).mp hr
      have hwp' := hfall s₁ hr0
      refine vllMach_run_of_bodyWp hinf'
        (fun x hx => hnc x (List.mem_cons_of_mem _ hx))
        (fun x hx => hnic x (List.mem_cons_of_mem _ hx))
        hwp' ?_
      intro s' hKs'
      simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm 1 is.length] using hcont s' hKs'
    · intro pc' s' hr
      exact False.elim (hjump pc' s' ((heq_rel _).mp hr))
    · intro c s' hr
      exact hhalt c s' ((heq_rel _).mp hr)

end LeanQbe.T.Vll
