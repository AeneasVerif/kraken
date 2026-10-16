module

/-
A caller that moves a byte range onto an overlapping range through a call to `memmove`, after
Erbsen et al., "Foundational Integration Verification of a Cryptographic Server" (PLDI 2024,
§2.3). `memmove_spec` proves the callee on its own: the source holds the bytes `bs`, the
destination is an owned block, and on return the destination owns `bs` and the frame `R₂` is
unchanged. The source can overlap the destination. `memmove_correct` proves the caller from the
resulting `CallSpec` alone.
-/
public import Kraken.StateCfg
public import Kraken.SeparationMem
import Kraken.X64.Parser

open Kraken.X64.Parser
open Std.WP
open Lean.Order
open scoped Program.WP

set_option experimental.vcgen true

namespace State

/-- The callee: copy `rdx` bytes from `rsi` to `rdi`, forward when `rdi ≤ rsi` and backward
otherwise, so that an overlapping source is read before it is overwritten. -/
def memmove : Program := parse("
memmove:
  cmp %rsi, %rdi
  jbe fwd
  add %rdx, %rsi
  add %rdx, %rdi
bwd:
  test %rdx, %rdx
  je bdone
  dec %rsi
  dec %rdi
  movb (%rsi), %al
  movb %al, (%rdi)
  dec %rdx
  jmp bwd
bdone:
  ret
fwd:
  test %rdx, %rdx
  je fdone
  movb (%rsi), %al
  movb %al, (%rdi)
  add $1, %rsi
  add $1, %rdi
  dec %rdx
  jmp fwd
fdone:
  ret
")

/-- The caller, with the callee linked between its two blocks. -/
def memmoveProg : Program := parse("
start:
  call memmove
  jmp done
") ++ memmove ++ parse("
done:
  nop
")

/-- `memmove` clobbers `rax`, `rsi`, `rdi` and `rdx`. -/
abbrev mmMod : Modifies := ⟨[.rax, .rsi, .rdi, .rdx]⟩

/-! ## The callee -/

/-- The registers `memmove` does not touch. -/
private abbrev MMKeep (s t : MachineData) : Prop :=
  t.regs.get64 .rbx = s.regs.get64 .rbx ∧ t.regs.get64 .rcx = s.regs.get64 .rcx
    ∧ t.regs.get64 .rbp = s.regs.get64 .rbp ∧ t.regs.get64 .r8 = s.regs.get64 .r8
    ∧ t.regs.get64 .r9 = s.regs.get64 .r9 ∧ t.regs.get64 .r10 = s.regs.get64 .r10
    ∧ t.regs.get64 .r11 = s.regs.get64 .r11 ∧ t.regs.get64 .r12 = s.regs.get64 .r12
    ∧ t.regs.get64 .r13 = s.regs.get64 .r13 ∧ t.regs.get64 .r14 = s.regs.get64 .r14
    ∧ t.regs.get64 .r15 = s.regs.get64 .r15

/-- In `fwd`, `rdx` bytes remain. The bytes below them are copied, and the source above them
is unread. -/
private abbrev MMFwd (bs : List UInt8) (R₂ : DataMem → Prop) (s : MachineData) (ra : Int64)
    (t : MachineData) : Prop :=
  (s.regs.get64 .rdi).toNat ≤ (s.regs.get64 .rsi).toNat ∧ (t.regs.get64 .rdx).toNat ≤ bs.length
    ∧ t.regs.get64 .rsi = s.regs.get64 .rsi + .ofNat 64 (bs.length - (t.regs.get64 .rdx).toNat)
    ∧ t.regs.get64 .rdi = s.regs.get64 .rdi + .ofNat 64 (bs.length - (t.regs.get64 .rdx).toNat)
    ∧ t.regs.get64 .rsp = s.regs.get64 .rsp - 8#64 ∧ MMKeep s t
    ∧ (t.dmem =⋆ Mem.Bytes (s.regs.get64 .rsp - 8#64) (Int.toBytes 8 ra.toBitVec.toInt)
        ⋆ Mem.Blocks [(s.regs.get64 .rdi, bs.length)] ⋆ R₂)
    ∧ Mem.Contains t.dmem (s.regs.get64 .rdi) (bs.take (bs.length - (t.regs.get64 .rdx).toNat))
    ∧ Mem.Contains t.dmem (t.regs.get64 .rsi) (bs.drop (bs.length - (t.regs.get64 .rdx).toNat))

/-- In `bwd`, `rdx` bytes remain. The bytes above them are copied, and the source below them is
unread. -/
private abbrev MMBwd (bs : List UInt8) (R₂ : DataMem → Prop) (s : MachineData) (ra : Int64)
    (t : MachineData) : Prop :=
  (s.regs.get64 .rsi).toNat < (s.regs.get64 .rdi).toNat ∧ (t.regs.get64 .rdx).toNat ≤ bs.length
    ∧ t.regs.get64 .rsi = s.regs.get64 .rsi + t.regs.get64 .rdx
    ∧ t.regs.get64 .rdi = s.regs.get64 .rdi + t.regs.get64 .rdx
    ∧ t.regs.get64 .rsp = s.regs.get64 .rsp - 8#64 ∧ MMKeep s t
    ∧ (t.dmem =⋆ Mem.Bytes (s.regs.get64 .rsp - 8#64) (Int.toBytes 8 ra.toBitVec.toInt)
        ⋆ Mem.Blocks [(s.regs.get64 .rdi, bs.length)] ⋆ R₂)
    ∧ Mem.Contains t.dmem (t.regs.get64 .rdi) (bs.drop (t.regs.get64 .rdx).toNat)
    ∧ Mem.Contains t.dmem (s.regs.get64 .rsi) (bs.take (t.regs.get64 .rdx).toNat)

/-- The callee's table, for a call from `s` that returns to `ra`, with arguments `P`. -/
private abbrev mm_table (P : Prop) (bs : List UInt8) (R₂ : DataMem → Prop)
    (s : MachineData) (ra : Int64) : Label → MachineData → Prop
  | "memmove", t => t = s.pushRa ra ∧ P
  | "bwd", t => P ∧ MMBwd bs R₂ s ra t
  | "bdone", t => P ∧ MMBwd bs R₂ s ra t ∧ t.regs.get64 .rdx = 0
  | "fwd", t => P ∧ MMFwd bs R₂ s ra t
  | "fdone", t => P ∧ MMFwd bs R₂ s ra t ∧ t.regs.get64 .rdx = 0
  | _, _ => False

/-- The contract of `memmove`, in every linked program. -/
theorem memmove_spec [Host] [BlockEntries] [FunDecls] (bs : List UInt8) (R₁ R₂ : DataMem → Prop)
    (hent : ∀ l ∈ Program.labels memmove, l ∈ BlockEntries.labels) (s : MachineData) (ra : Int64) :
    ⦃ fun t => t = s.pushRa ra
      ∧ (bs.length = (s.regs.get64 .rdx).toNat
        ∧ (s.regs.get64 .rsi).toNat + bs.length < 2 ^ 64
        ∧ (s.regs.get64 .rdi).toNat + bs.length < 2 ^ 64
        ∧ (s.dmem =⋆ Mem.Bytes (s.regs.get64 .rsi) bs ⋆ Mem.Blocks [(s.regs.get64 .rsp - 8#64, 8)] ⋆ R₁)
        ∧ s.dmem =⋆ Mem.Blocks [(s.regs.get64 .rsp - 8#64, 8), (s.regs.get64 .rdi, bs.length)] ⋆ R₂) ⦄
      memmove
    ⦃ (fun _ _ => False); fun a t => a = ra
      ∧ (t.dmem =⋆ Mem.Blocks [(s.regs.get64 .rsp - 8#64, 8)] ⋆ Mem.Bytes (s.regs.get64 .rdi) bs ⋆ R₂)
      ∧ mmMod.Agree s t ⦄ := by
  refine Program.WP.cfg (p := memmove) (mm_table ?_ bs R₂ s ra) (fun _ t => (t.regs.get64 .rdx).toNat)
    (fun _ => False) _ hent ?_ ?_
  · intro s₀ l t h₀ ht
    apply MachineData.stackAtOrBelow_of_rsp_eq
    obtain ⟨rfl, -⟩ := h₀
    unfold mm_table at ht
    split at ht <;> grind
  cfg_cases [memmove]
  all_goals kvcgen64 with finish

/-! ## The caller -/

/-- The caller's table: `start` holds the arguments, `done` the moved bytes. The blocks of the
callee are entered only by the call. -/
private abbrev mp_table (d : MachineData) (bs : List UInt8) (R₂ : DataMem → Prop) :
    Label → MachineData → Prop
  | "start", s => s = d
  | "done", s => s.regs.get64 .rsp = d.regs.get64 .rsp ∧ s.dmem =⋆ Mem.Blocks [(d.regs.get64 .rsp - 8#64, 8)]
      ⋆ Mem.Bytes (d.regs.get64 .rdi) bs ⋆ R₂
  | _, _ => False

theorem memmove_correct [Host] (hp : memmoveProg.IsInfix Host.prog)
    (d : MachineData) (bs : List UInt8) (R₁ R₂ : DataMem → Prop)
    (hn : bs.length = (d.regs.get64 .rdx).toNat)
    (hsrc : (d.regs.get64 .rsi).toNat + bs.length < 2 ^ 64)
    (hdst : (d.regs.get64 .rdi).toNat + bs.length < 2 ^ 64)
    (h₁ : d.dmem =⋆ Mem.Bytes (d.regs.get64 .rsi) bs ⋆ Mem.Blocks [(d.regs.get64 .rsp - 8#64, 8)] ⋆ R₁)
    (h₂ : d.dmem =⋆ Mem.Blocks [(d.regs.get64 .rsp - 8#64, 8), (d.regs.get64 .rdi, bs.length)] ⋆ R₂) :
    Eventually (step1 Host.exe)
      (fun st => st.data.dmem =⋆ Mem.Blocks [(d.regs.get64 .rsp - 8#64, 8)]
        ⋆ Mem.Bytes (d.regs.get64 .rdi) bs ⋆ R₂)
      ⟨d, startAddr hp⟩ := by
  letI := BlockEntries.ofLabels (Program.labels memmoveProg)
  have hk := List.isInfixAt_infixIdx hp
  generalize memmoveProg.infixIdx Host.prog hp = k at hk
  have hmp : memmove.IsInfixAt memmoveProg 3 := ⟨_, rfl⟩
  have hmm : memmove.IsInfixAt Host.prog (k + 3) := List.IsInfixAt.trans hmp hk
  letI : Embeds memmove := ⟨⟨k + 3, hmm⟩⟩
  letI : FunDecls := ⟨[Fragment.mk memmove]⟩
  have hstart : (Fragment.mk memmove).startAddr = label "memmove" := (Host.label_eq (i := 0) hmm rfl).symm
  have hg : FunDecls.at (label "memmove") = some (Fragment.mk memmove) := by
    show List.find? _ [_] = _
    simp [hstart]
  have hcall := Program.WP.callSpec_of_triple hg
    (memmove_spec bs R₁ R₂ fun _ h => BlockEntries.mem_ofLabels
      (Program.mem_labels.mpr (hmp.isInfix.subset (Program.mem_labels.mp h))))
  apply Program.WP.step1_of_wp hp
  refine Program.WP.cfg_wp (l₀ := "start") (mp_table d bs R₂) (fun _ _ => 0) _ ⊥
    (fun _ => BlockEntries.mem_ofLabels) ?_ ?_ d rfl
  · intro s₀ l t h₀ ht
    apply MachineData.stackAtOrBelow_of_rsp_eq
    subst h₀
    unfold mp_table at ht
    split at ht <;> grind
  cfg_cases [memmoveProg, memmove]
  · kvcgen64 [hcall] with finish
  · kvcgen64 with finish

end State
