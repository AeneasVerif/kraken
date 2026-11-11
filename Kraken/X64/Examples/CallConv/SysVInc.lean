module

import Kraken.Tactics
import Kraken.X64.Parser
import Kraken.X64.Sep
public import Kraken.X64.WP.Call
import Kraken.X64.Examples.CallConv.RunStep
public import Kraken.X64.SysV

/-!
# A procedure call under the System V AMD64 convention

`sysv_inc` returns its first argument plus one. `sysv_caller` is a SysV procedure that calls it.
Both satisfy `IncSpec`: the convention's `CallPre`/`CallPost` plus the argument and the result,
and nothing the convention already guarantees (callee-saved registers, the direction flag, the
stack pointer). `inc_spec` is proved from the callee's code, for any placement in the ambient
program. `caller_spec` is proved from the caller's code and the callee's `IncSpec` alone, through
`ProcSpec.wp_call_owned`: it does not depend on the callee's code.

`inc_spec` steps through the callee with the project's `kstep` tactic: `Host.run_cons` turns each
instruction of the fragment into an `Effects.All` goal, and `kstep` runs it, including the load of
the return address (`load_sep`). `caller_spec` and the other examples use `run_step`
(`CallConv/RunStep.lean`), because `kstep` cannot yet reduce `disp(%r)` addresses, has no AVX memory
rules, and does not handle `call`.
-/

open Kraken.X64.Parser
open Kraken.X64.Stack
open Kraken.X64.SysV
open Std.ExtHashMap

public section

namespace CallConv.SysVInc

def inc_body : Program := ⸨prog|
sysv_inc:
  movq %rdi, %rax
  addq $1, %rax
  ret⸩

variable [Host]

/-- The specification of an increment procedure at `entry` that needs `d` bytes of stack. -/
abbrev IncSpec (d : Nat) (entry : Int64) : Prop :=
  Host.exe.ProcSpec entry
    (fun (x : BitVec 64 × (Mem 64 → Prop)) ra t => CallPre d x.2 ra t ∧ ArgU64 t x.1)
    (fun x ra t s => CallPost d x.2 ra t s ∧ RetU64 s (x.1 + 1))

theorem inc_spec {j : Nat} (hj : inc_body.IsInfixAt Host.prog j)
    (hfirst : ∀ i, i < j → Host.prog[i]? ≠ some (.label "sysv_inc")) :
    IncSpec 0 (label "sysv_inc") := by
  rw [Host.label_addrOf hj.cons.1 hfirst]
  rintro ⟨n, R⟩ ra t ⟨⟨-, hdf, -, hmem⟩, harg⟩
  have h1 := hj.cons.2
  have h2 := h1.cons.2
  have h3 := h2.cons.2
  -- `kstep` states registers as fields (`t.regs.rsp.toBitVec`), not through `get64`
  simp only [Reg64s.get64] at hmem
  refine Host.run_cons hj ?_
  sym => kstep; tactic =>
  -- movq %rdi, %rax
  refine Host.run_cons h1 ?_
  sym => kstep; tactic =>
  -- addq $1, %rax
  refine Host.run_cons h2 ?_
  sym => kstep; tactic =>
  -- ret
  refine Host.run_cons h3 ?_
  sym => kstep; tactic =>
  refine Eventually.done _ ⟨?_, ⟨?_, hdf, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩, ?_⟩
  · rw [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, Int64.ofBitVec_toBitVec]
  · simp (config := { zetaDelta := true })
  · exact Owned.intro hmem (Int.toBytes_length _ _)
  · simp only [Reg64s.get64] at harg
    simp (config := { zetaDelta := true }) [harg, BitVec.add_comm]

/-- A SysV procedure that calls `sysv_inc`. On entry `rsp + 8` is 16-byte aligned, so it moves
`rsp` down by 8 to make `rsp` aligned at the `call`. -/
def caller : Program := ⸨prog|
sysv_caller:
  subq $8, %rsp
  call sysv_inc
  addq $8, %rsp
  ret⸩

omit [Host] in
/-- The caller's 16-byte reservation: the callee's return-address slot and 8 bytes of padding. -/
private theorem reserve16_eq (r : BitVec 64) :
    Reserve 16 r = Owned 8 (r - 16) ⋆ Owned 8 (r - 8) := by
  rw [Reserve, show (16 : Nat) = 8 + 8 from rfl, Owned.split 8 8 _ (by omega)]
  congr 2
  bv_omega

/-- The caller needs 16 bytes of stack: 8 of padding and 8 for the callee's return address. -/
theorem caller_spec {c : Nat} (hc : caller.IsInfixAt Host.prog c)
    (hcfirst : ∀ i, i < c → Host.prog[i]? ≠ some (.label "sysv_caller"))
    (hinc : IncSpec 0 (label "sysv_inc")) :
    IncSpec 16 (label "sysv_caller") := by
  rw [Host.label_addrOf hc.cons.1 hcfirst]
  rintro ⟨n, R⟩ ra t ⟨⟨hal, hdf, -, hmem⟩, harg⟩
  have h1 := hc.cons.2
  have h2 := h1.cons.2
  have h3 := h2.cons.2
  have h4 := h3.cons.2
  rw [reserve16_eq, sep_assoc, sep_comm_l] at hmem
  have e8 : BitVec.truncate Width.W64.bits (Int64.toBitVec 8) = 8 := rfl
  -- the frame arithmetic, for any `r`: `bv_omega` does not go through on the `get64` terms
  have e16 : ∀ r : BitVec 64, r - 8 - 8 = r - 16 := fun _ => by bv_omega
  have eal : ∀ r : BitVec 64, r.toNat % 16 = 8 → (r - 16).toNat % 16 = 8 := fun _ _ => by bv_omega
  have eret : ∀ r : BitVec 64, 8 + (r - 16 + 8) = r := fun _ => by bv_omega
  run_step hc
  -- subq $8, %rsp
  run_step h1 [e8]
  -- call sysv_inc
  refine Host.run_wp h2 ?_
  refine hinc.wp_call_owned
    (n, RetCell ra (t.regs.get64 .rsp) ⋆ (Owned 8 (t.regs.get64 .rsp - 8) ⋆ R))
    (by simpa only [Reg64s.get64_set64_self, e16]) ?_ ?_
  · intro ra' hpushed
    refine ⟨⟨?_, by simpa using hdf, by simp, ?_⟩, ?_⟩
    · simp only [EntryAligned, MachineData.get64_pushRa, ite_true, Reg64s.get64_set64_self, e16]
      exact eal _ hal
    · simpa only [MachineData.get64_pushRa, ite_true, Reserve.zero, emp_sep,
        Reg64s.get64_set64_self, e16] using hpushed
    · simpa only [ArgU64, MachineData.get64_pushRa, reduceCtorEq, ite_false,
        Reg64s.get64_set64_ne _ (show Reg64.rsp ≠ .rdi by decide)] using harg
  · rintro ra' s' ⟨⟨hrsp, hdf', hsaved, hm⟩, hret⟩
    simp only [MachineData.get64_pushRa, ite_true, Reg64s.get64_set64_self, e16, Reserve.zero,
      emp_sep] at hrsp hm
    have er : 8 + s'.regs.get64 .rsp = t.regs.get64 .rsp := by
      rw [hrsp]; exact eret _
    rw [sep_comm_l] at hm
    have hretld := Mem.loadInt_sep _ _ 8 _ _ hm (Int.toBytes_length _ _) (by decide)
    -- addq $8, %rsp
    run_step h3 [e8]
    -- ret
    run_step h4 [er]
    refine Effects.All_load (w := .W64) hretld ?_
    simp only [Effects.All]
    refine Eventually.done _ ⟨?_, ⟨?_, hdf', ?_, ?_⟩, ?_⟩
    · show Int64.ofBitVec (BitVec.ofInt 64 _) = ra
      rw [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, Int64.ofBitVec_toBitVec]
    · simp
    · obtain ⟨hbx, hbp, h12, h13, h14, h15⟩ := hsaved
      simp_all [SavedRegs, Reg64s.get64_set64]
    · refine Owned.intro (bs := Int.toBytes 8 ra.toBitVec.toInt) ?_ (Int.toBytes_length _ _)
      rw [reserve16_eq, sep_assoc]
      exact hm
    · simpa [RetU64, Reg64s.get64_set64] using hret

end CallConv.SysVInc
