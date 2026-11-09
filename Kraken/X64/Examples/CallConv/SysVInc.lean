module

import Kraken.Tactics
import Kraken.X64.Parser
import Kraken.X64.Sep
public import Kraken.X64.WP.Call
import Kraken.X64.Examples.CallConv.RunStep
public import Kraken.SysV

/-!
# A procedure call under the System V AMD64 convention

`sysv_inc` returns its first argument plus one. `inc_spec` is its `ProcSpec` under `Kraken.SysV`,
proved from its own code alone, for any placement in the ambient program. `sysv_caller` is a SysV
procedure that calls it; `caller_spec` is its `ProcSpec`, of the same shape, proved using only
`inc_spec` through `ProcSpec.wp_call_owned`. Neither specification restates what the convention
already guarantees (callee-saved registers, the direction flag, the stack pointer): that is all in
`CallPre`/`CallPost`.

`inc_spec` steps through the callee with the project's `kstep` tactic: `Host.run_cons` turns each
instruction of the fragment into an `Effects.All` goal, and `kstep` runs it, including the load of
the return address (`load_sep`). `caller_spec` and the other examples use `run_step`
(`CallConv/RunStep.lean`), because `kstep` cannot yet reduce `disp(%r)` addresses, has no AVX memory
rules, and does not handle `call`.
-/

open Kraken.X64.Parser
open Kraken.Stack
open Kraken.SysV
open Std.ExtHashMap

public section

namespace CallConv.SysVInc

def inc_body : Program := parse("
sysv_inc:
  movq %rdi, %rax
  addq $1, %rax
  ret
")

variable [Host]

theorem inc_spec {j : Nat} (hj : inc_body.IsInfixAt Host.prog j) :
    Host.exe.ProcSpec (Host.addrOf j)
      (fun (x : BitVec 64 × (Mem 64 → Prop)) ra t => CallPre 0 x.2 ra t ∧ ArgU64 t x.1)
      (fun x ra t s => CallPost 0 x.2 ra t s ∧ RetU64 s (x.1 + 1)) := by
  rintro ⟨n, R⟩ ra t ⟨⟨-, hdf, hmem⟩, harg⟩
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
  refine Eventually.done _ ⟨?_, ⟨?_, hdf, rfl, ⟨rfl, rfl, rfl, rfl, rfl⟩, ?_⟩, ?_⟩
  · rw [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, Int64.ofBitVec_toBitVec]
  · simp (config := { zetaDelta := true })
  · exact Owned.intro hmem (Int.toBytes_length _ _)
  · simp only [Reg64s.get64] at harg
    simp (config := { zetaDelta := true }) [harg, BitVec.add_comm]

omit [Host] in
/-- The caller's 16-byte reservation: the callee's return-address slot and 8 bytes of padding. -/
private theorem reserve16_eq {r : BitVec 64} (h : 16 ≤ r.toNat) :
    Reserve 16 r = Owned 8 (r - 16) ⋆ Owned 8 (r - 8) := by
  have h1 := Owned.split 8 8 (r - .ofNat 64 16) (by omega)
  simp only [Nat.reduceAdd] at h1
  have e : r - BitVec.ofNat 64 16 + BitVec.ofNat 64 8 = r - 8 := by bv_omega
  rw [Reserve_eq 16 r h, h1, e]
  rfl

omit [Host] in
private theorem sub_8_sub_8 (r : BitVec 64) : r - 8 - 8 = r - 16 := by bv_omega

omit [Host] in
private theorem add_8_sub_16_add_8 (r : BitVec 64) : 8 + (r - 16 + 8) = r := by bv_omega

omit [Host] in
/-- A procedure entered with `rsp + 8` aligned that moves `rsp` down by 8 before a `call` enters
its callee with `rsp + 8` aligned. -/
private theorem aligned_sub_16 {r : BitVec 64} (h : r.toNat % 16 = 8) : (r - 16).toNat % 16 = 8 := by
  bv_omega

/-- A SysV procedure that calls `sysv_inc`. On entry `rsp + 8` is 16-byte aligned, so it moves
`rsp` down by 8 to make `rsp` aligned at the `call`. -/
def caller : Program := parse("
sysv_caller:
  subq $8, %rsp
  call sysv_inc
  addq $8, %rsp
  ret
")

/-- The caller's specification has the same shape as `inc_spec`: the convention, with a 16-byte
reservation for the padding and the callee's return-address slot, plus the argument and the result.
It is proved from `inc_spec` alone, through `ProcSpec.wp_call_owned`. -/
theorem caller_spec {j c : Nat} (hj : inc_body.IsInfixAt Host.prog j)
    (hfirst : ∀ i, i < j → Host.prog[i]? ≠ some (.label "sysv_inc"))
    (hc : caller.IsInfixAt Host.prog c) :
    Host.exe.ProcSpec (Host.addrOf c)
      (fun (x : BitVec 64 × (Mem 64 → Prop)) ra t => CallPre 16 x.2 ra t ∧ ArgU64 t x.1)
      (fun x ra t s => CallPost 16 x.2 ra t s ∧ RetU64 s (x.1 + 1)) := by
  rintro ⟨n, R⟩ ra t ⟨⟨hal, hdf, hmem⟩, harg⟩
  have h1 := hc.cons.2
  have h2 := h1.cons.2
  have h3 := h2.cons.2
  have h4 := h3.cons.2
  have hle := Reserve.le_second hmem
  rw [reserve16_eq hle, sep_assoc, sep_comm_l] at hmem
  have e8 : BitVec.truncate Width.W64.bits (Int64.toBitVec 8) = 8 := rfl
  have e16 : t.regs.get64 .rsp - 8 - 8 = t.regs.get64 .rsp - 16 := sub_8_sub_8 _
  run_step hc
  -- subq $8, %rsp
  run_step h1 [e8]
  -- call sysv_inc
  refine Host.run_wp h2 ?_
  refine (inc_spec hj).wp_call_owned (Host.label_addrOf hj.cons.1 hfirst)
    (n, RetCell ra (t.regs.get64 .rsp) ⋆ (Owned 8 (t.regs.get64 .rsp - 8) ⋆ R))
    (by simpa only [Reg64s.get64_set64_self, e16]) ?_ ?_
  · intro ra' hpushed
    refine ⟨⟨?_, by simpa using hdf, ?_⟩, ?_⟩
    · simp only [EntryAligned, MachineData.get64_pushRa, ite_true, Reg64s.get64_set64_self, e16]
      exact aligned_sub_16 hal
    · simpa only [MachineData.get64_pushRa, ite_true, Reserve.zero, emp_sep,
        Reg64s.get64_set64_self, e16] using hpushed
    · simpa only [ArgU64, MachineData.get64_pushRa, reduceCtorEq, ite_false,
        Reg64s.get64_set64_ne _ (show Reg64.rsp ≠ .rdi by decide)] using harg
  · rintro ra' s' ⟨⟨hrsp, hdf', hrbp, hsaved, hm⟩, hret⟩
    simp only [MachineData.get64_pushRa, ite_true, Reg64s.get64_set64_self, e16, Reserve.zero,
      emp_sep] at hrsp hm
    have er : 8 + s'.regs.get64 .rsp = t.regs.get64 .rsp := by rw [hrsp]; exact add_8_sub_16_add_8 _
    rw [sep_comm_l] at hm
    have hretld := Mem.loadInt_sep _ _ 8 _ _ hm (Int.toBytes_length _ _) (by decide)
    -- addq $8, %rsp
    run_step h3 [e8]
    -- ret
    run_step h4 [er]
    refine Effects.All_load (w := .W64) hretld ?_
    simp only [Effects.All]
    refine Eventually.done _ ⟨?_, ⟨?_, hdf', ?_, ?_, ?_⟩, ?_⟩
    · show Int64.ofBitVec (BitVec.ofInt 64 _) = ra
      rw [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, Int64.ofBitVec_toBitVec]
    · simp
    · simpa [Reg64s.get64_set64] using hrbp
    · obtain ⟨hbx, h12, h13, h14, h15⟩ := hsaved
      simp_all [SavedRegs, Reg64s.get64_set64]
    · refine Owned.intro (bs := Int.toBytes 8 ra.toBitVec.toInt) ?_ (Int.toBytes_length _ _)
      rw [reserve16_eq hle, sep_assoc]
      exact hm
    · simpa [RetU64, Reg64s.get64_set64] using hret

end CallConv.SysVInc
