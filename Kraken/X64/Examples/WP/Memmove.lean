module

/-
A caller that moves a byte range onto an overlapping range through a call to `memmove`, after
Erbsen et al., "Foundational Integration Verification of a Cryptographic Server" (PLDI 2024,
§2.3). `memmove_spec` proves the callee on its own: the source holds the bytes `bs`, the
destination is mapped, and on return the destination holds `bs` and the memory outside the
destination and the return slot is unchanged. The source can overlap the destination. `memmove_correct` proves the caller from the
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

/-- `memmove` clobbers `rax`, `rsi`, `rdi`, `rdx`, the destination and its return slot. -/
abbrev mmMod (s : MachineData) : Modifies :=
  ⟨[.rax, .rsi, .rdi, .rdx],
    [(s.regs.get64 .rdi, (s.regs.get64 .rdx).toNat), (s.regs.get64 .rsp - 8#64, 8)]⟩

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
private abbrev MMFwd (bs : List UInt8) (s : MachineData) (ra : Int64)
    (t : MachineData) : Prop :=
  (s.regs.get64 .rdi).toNat ≤ (s.regs.get64 .rsi).toNat ∧ (t.regs.get64 .rdx).toNat ≤ bs.length
    ∧ t.regs.get64 .rsi = s.regs.get64 .rsi + .ofNat 64 (bs.length - (t.regs.get64 .rdx).toNat)
    ∧ t.regs.get64 .rdi = s.regs.get64 .rdi + .ofNat 64 (bs.length - (t.regs.get64 .rdx).toNat)
    ∧ t.regs.get64 .rsp = s.regs.get64 .rsp - 8#64 ∧ MMKeep s t
    ∧ Mem.Contains t.dmem (s.regs.get64 .rsp - 8#64) (Int.toBytes 8 ra.toBitVec.toInt)
    ∧ Mem.Mapped [(s.regs.get64 .rsp - 8#64, 8), (s.regs.get64 .rdi, bs.length)] t.dmem
    ∧ Mem.UnchangedOutside (mmMod s).mem s.dmem t.dmem
    ∧ Mem.Contains t.dmem (s.regs.get64 .rdi) (bs.take (bs.length - (t.regs.get64 .rdx).toNat))
    ∧ Mem.Contains t.dmem (t.regs.get64 .rsi) (bs.drop (bs.length - (t.regs.get64 .rdx).toNat))

/-- In `bwd`, `rdx` bytes remain. The bytes above them are copied, and the source below them is
unread. -/
private abbrev MMBwd (bs : List UInt8) (s : MachineData) (ra : Int64)
    (t : MachineData) : Prop :=
  (s.regs.get64 .rsi).toNat < (s.regs.get64 .rdi).toNat ∧ (t.regs.get64 .rdx).toNat ≤ bs.length
    ∧ t.regs.get64 .rsi = s.regs.get64 .rsi + t.regs.get64 .rdx
    ∧ t.regs.get64 .rdi = s.regs.get64 .rdi + t.regs.get64 .rdx
    ∧ t.regs.get64 .rsp = s.regs.get64 .rsp - 8#64 ∧ MMKeep s t
    ∧ Mem.Contains t.dmem (s.regs.get64 .rsp - 8#64) (Int.toBytes 8 ra.toBitVec.toInt)
    ∧ Mem.Mapped [(s.regs.get64 .rsp - 8#64, 8), (s.regs.get64 .rdi, bs.length)] t.dmem
    ∧ Mem.UnchangedOutside (mmMod s).mem s.dmem t.dmem
    ∧ Mem.Contains t.dmem (t.regs.get64 .rdi) (bs.drop (t.regs.get64 .rdx).toNat)
    ∧ Mem.Contains t.dmem (s.regs.get64 .rsi) (bs.take (t.regs.get64 .rdx).toNat)

/-- The contract of `memmove`, in every linked program. -/
theorem memmove_spec [Host] [FunDecls] (bs : List UInt8) (s : MachineData) (ra : Int64) :
    ⦃ fun t => t = s.pushRa ra
      ∧ (bs.length = (s.regs.get64 .rdx).toNat
        ∧ (s.regs.get64 .rsi).toNat + bs.length < 2 ^ 64
        ∧ (s.regs.get64 .rdi).toNat + bs.length < 2 ^ 64
        ∧ Mem.Contains s.dmem (s.regs.get64 .rsi) bs
        ∧ Mem.Mapped [(s.regs.get64 .rsp - 8#64, 8), (s.regs.get64 .rdi, bs.length)] s.dmem
        ∧ Mem.Blocks.Disjoint [(s.regs.get64 .rsi, bs.length), (s.regs.get64 .rdi, bs.length)]
            [(s.regs.get64 .rsp - 8#64, 8)]) ⦄
      memmove
    ⦃ (fun _ _ => False); fun a t => a = ra
      ∧ Mem.Contains t.dmem (s.regs.get64 .rdi) bs
      ∧ (mmMod s).Agree s t ⦄ := by
  refine ⟨fun s₀ ⟨h₀, _⟩ => ?_⟩
  subst h₀
  refine Program.WP.cfg (fun
      | .entry, t | .label "memmove", t => t = s.pushRa ra
      | .label "bwd", t => MMBwd bs s ra t
      | .label "bdone", t => MMBwd bs s ra t ∧ t.regs.get64 .rdx = 0
      | .label "fwd", t => MMFwd bs s ra t
      | .label "fdone", t => MMFwd bs s ra t ∧ t.regs.get64 .rdx = 0
      | _, _ => False)
    (fun _ t => (t.regs.get64 .rdx).toNat) ?_ rfl
  cfg_cases
  all_goals kvcgen64 with finish

/-! ## The caller -/

theorem memmove_correct [Host] (hp : memmoveProg.IsInfix Host.prog)
    (d : MachineData) (bs : List UInt8)
    (hn : bs.length = (d.regs.get64 .rdx).toNat)
    (hsrc : (d.regs.get64 .rsi).toNat + bs.length < 2 ^ 64)
    (hdst : (d.regs.get64 .rdi).toNat + bs.length < 2 ^ 64)
    (hbs : Mem.Contains d.dmem (d.regs.get64 .rsi) bs)
    (hmap : Mem.Mapped [(d.regs.get64 .rsp - 8#64, 8), (d.regs.get64 .rdi, bs.length)] d.dmem)
    (hdisj : Mem.Blocks.Disjoint [(d.regs.get64 .rsi, bs.length), (d.regs.get64 .rdi, bs.length)]
      [(d.regs.get64 .rsp - 8#64, 8)]) :
    Eventually (step1 Host.exe)
      (fun st => Mem.Contains st.data.dmem (d.regs.get64 .rdi) bs
        ∧ Mem.UnchangedOutside (mmMod d).mem d.dmem st.data.dmem)
      ⟨d, startAddr hp⟩ := by
  have hk := List.isInfixAt_infixIdx hp
  generalize memmoveProg.infixIdx Host.prog hp = k at hk
  have hmm : memmove.IsInfixAt Host.prog (k + 3) :=
    List.IsInfixAt.trans (⟨_, rfl⟩ : memmove.IsInfixAt memmoveProg 3) hk
  letI : Embeds memmove := ⟨⟨k + 3, hmm⟩⟩
  letI : FunDecls := ⟨[Fragment.mk memmove]⟩
  have hstart : (Fragment.mk memmove).startAddr = label "memmove" := (Host.label_eq (i := 0) hmm rfl).symm
  have hg : FunDecls.at (label "memmove") = some (Fragment.mk memmove) := by
    show List.find? _ [_] = _
    simp [hstart]
  have hcall := Program.WP.callSpec_of_triple hg (memmove_spec bs)
  apply Program.WP.step1_of_wp hp
  refine Program.WP.cfg (fun
      | .entry, s | .label "start", s => s = d
      | .label "done", s => s.regs.get64 .rsp = d.regs.get64 .rsp ∧ Mem.Contains s.dmem (d.regs.get64 .rdi) bs
          ∧ Mem.UnchangedOutside (mmMod d).mem d.dmem s.dmem
      | .exit, s => Mem.Contains s.dmem (d.regs.get64 .rdi) bs ∧ Mem.UnchangedOutside (mmMod d).mem d.dmem s.dmem
      | _, _ => False)
    (fun _ _ => 0) ?_ rfl
  cfg_cases
  all_goals kvcgen64 [hcall] with finish

end State
