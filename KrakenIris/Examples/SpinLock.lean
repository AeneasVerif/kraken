module

public import KrakenIris.Eventually
import Kraken.X64.Parser
meta import Kraken.X64.Semantics
import Std.Tactic.BVDecide

/-!
# Example: a spin lock

`%rdi` holds the address of the lock byte. The byte is 0 when the lock is free.

```
acquire:                      release:
  mov  $1, %eax                 movb $0, (%rdi)
  xchg %al, (%rdi)
  test %al, %al
  jnz  acquire

```
The lock byte lives in the shared memory, under an Iris invariant:

    `is_lock N L R`  :=  inv N (∃ b, L ↦ b ∗ if b = 0 then R else True)

`R` is whatever the lock protects.
`xchg` is one atomic step.

-/

public section

open Iris BI
open Kraken.X64.Parser

/-- The parser does not know `xchg` yet -/
def spinAcquire : Program :=
  ⸨prog| acquire: mov $1, %eax⸩ ++
  [.instr (.regular .W64 .W8 (.xchg (.mem ⟨some (.reg .rdi), none, .int64 0⟩) Reg.al))] ++
  ⸨prog|
    test %al, %al
    jnz acquire⸩

def spinRelease : Program := ⸨prog| release: movb $0, (%rdi)⸩

/-! Small facts about bytes and registers that the proofs need. -/

private theorem extractLsb'_replaceLow (x : BitVec 64) (v : BitVec 8) :
    BitVec.extractLsb' 0 8 (x.replaceLow v) = v := by
  simp only [BitVec.replaceLow, BitVec.drop]
  bv_decide

private theorem ofInt_ofBytes_singleton (b : UInt8) :
    BitVec.ofInt 8 (Int.ofBytes [b]) = b.toBitVec := by
  simp [Int.ofBytes]

private theorem toBytes_one : Int.toBytes 1 (BitVec.toInt 1#8) = [1] := by decide

private theorem toBytes_zero : Int.toBytes 1 (BitVec.toInt 0#8) = [0] := by decide

private theorem toBitVec_eq_zero (b : UInt8) : b.toBitVec = 0#8 ↔ b = 0 :=
  ⟨fun h => UInt8.toBitVec_inj.mp h, fun h => h ▸ rfl⟩

section
variable {GF : BundledGFunctors} [InvGS GF] [G : krakenGS GF]

/-- The byte at `L` is a lock protecting `R`. -/
def is_lock (N : Namespace) (L : BitVec 64) (R : IProp GF) : IProp GF :=
  inv N iprop(∃ b : UInt8, L ↦ b ∗ if b = 0 then R else True)

instance (N : Namespace) (L : BitVec 64) (R : IProp GF) : Persistent (is_lock N L R) := by
  unfold is_lock
  infer_instance

/-- `acquire` eventually runs off its end holding `R`, with `%rdi` still pointing at the lock. -/
theorem spinAcquire_spec [layout : Layout] (N : Namespace) (L : BitVec 64) (R : IProp GF)
    (s : MachineData) (hrdi : s.regs.rdi.toBitVec = L)
    (hshared : Mem.loadInt s.dmem L 1 = none) :
    is_lock N L R -∗
    EventuallyI (straightlineStepI (layout spinAcquire))
      (fun s' => iprop(R ∗ ⌜s'.pc = (layout spinAcquire).addrOf spinAcquire.length ∧
        s'.data.regs.rdi.toBitVec = L⌝))
      ⟨s, layout.start⟩ := by
  iintro #Hlock
  iloeb as IH generalizing %s %hrdi %hshared
  iapply EventuallyI.step_cps
  rw [straightlineStepI]
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩,
    zmms, status, df, dmem⟩ := s
  simp only at hrdi hshared
  unfold spinAcquire
  simp only [Executable.straightline]
  rw [Kraken.Executable.directivesFromStart]
  simp [List.mapIdx, List.mapIdx.go]
  simp only [Directives.interp, Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    RegOrMem.interp, MachineData.set, MachineData.setReg, MachineData.rmw,
    Effects.AllI_require_exec_access, Effects.AllI_require_read_access,
    Effects.AllI_require_write_access]
  simp [AddrExpr.interp, BitVec.toAddressSize, BitVec.take, BitVec.drop, BitVec.signed,
    ConstExpr.interp, Reg64s.get, Reg64s.get64, Reg64s.set, Reg64s.set64, Reg.base, Reg.offset,
    Labels.label, Kraken.Layout.apply, Kraken.Executable.withAddresses,
    CondCode.interp, StatusFlags.from_result, extractLsb'_replaceLow, hrdi, hshared]
  unfold is_lock
  iinv Hlock with ⟨%b, >HL, HR⟩ Hclose
  iapply Effects.AllI_nonmem_load (⊤ \ ↑N) _ _ .W8 _ [b] _ rfl $$ [HL]
  · simp only [pointstoBytes_cons, pointstoBytes_nil]
    iframe
  iintro !> HL
  iapply Effects.AllI_nonmem_store (⊤ \ ↑N) _ _ _ _ [b] _ rfl $$ HL
  iintro !> HL
  simp only [Width.bytes, toBytes_one, pointstoBytes_cons, pointstoBytes_nil]
  icases HL with ⟨HL, -⟩
  imod Hclose $$ [HL]
  · inext
    iexists 1
    iframe
    simp only [show (1 : UInt8) ≠ 0 by decide, ↓reduceIte]
    itrivial
  iapply Effects.AllI_yield
  simp only [Effects.AllI_require_exec_access]
  iapply Effects.AllI_undefined
  iintro %af
  simp only [Effects.AllI_require_exec_access, Width.bits, ofInt_ofBytes_singleton,
    toBitVec_eq_zero]
  by_cases hb : b = 0
  · simp only [hb, ↓reduceIte]
    iapply Effects.AllI_done
    imodintro
    iapply EventuallyI.done
    iframe HR
    ipureintro
    refine ⟨?_, hrdi⟩
    simp [Kraken.Executable.addrOf, Kraken.Executable.sizeBefore, Int64.ofNat_add,
      Int64.add_assoc]
  · simp only [hb, ↓reduceIte]
    iapply Effects.AllI_done
    imodintro
    iapply IH
    · ipureintro; exact hrdi
    · ipureintro; exact hshared

/-- `release` eventually runs off its end, having given `R` back to the invariant. -/
theorem spinRelease_spec [layout : Layout] (N : Namespace) (L : BitVec 64) (R : IProp GF)
    (s : MachineData) (hrdi : s.regs.rdi.toBitVec = L)
    (hshared : Mem.loadInt s.dmem L 1 = none) :
    is_lock N L R -∗ R -∗
    EventuallyI (straightlineStepI (layout spinRelease))
      (fun s' => iprop(⌜s'.pc = (layout spinRelease).addrOf spinRelease.length⌝))
      ⟨s, layout.start⟩ := by
  iintro #Hlock HR
  iapply EventuallyI.step_cps
  rw [straightlineStepI]
  unfold spinRelease
  simp only [Executable.straightline]
  rw [Kraken.Executable.directivesFromStart]
  simp [List.mapIdx, List.mapIdx.go]
  simp only [Directives.interp, Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    MachineData.set, MachineData.store,
    Effects.AllI_require_exec_access, Effects.AllI_require_write_access]
  simp [AddrExpr.interp, BitVec.toAddressSize, BitVec.take, BitVec.signed, ConstExpr.interp,
    Reg64s.get64, hrdi, hshared]
  unfold is_lock
  iinv Hlock with ⟨%b, >HL, -⟩ Hclose
  iapply Effects.AllI_nonmem_store (⊤ \ ↑N) _ _ _ _ [b] _ rfl $$ [HL]
  · simp only [pointstoBytes_cons, pointstoBytes_nil]
    iframe
  iintro !> HL
  simp only [Width.bytes, toBytes_zero, pointstoBytes_cons, pointstoBytes_nil]
  icases HL with ⟨HL, -⟩
  imod Hclose $$ [HL HR]
  · inext
    iexists 0
    iframe HL
    simp only [↓reduceIte]
    iexact HR
  iapply Effects.AllI_yield
  iapply Effects.AllI_done
  imodintro
  iapply EventuallyI.done
  ipureintro
  simp [Kraken.Executable.addrOf, Kraken.Executable.sizeBefore, Kraken.Layout.apply, List.mapIdx,
    List.mapIdx.go, Int64.ofNat_add, Int64.add_assoc]

end
