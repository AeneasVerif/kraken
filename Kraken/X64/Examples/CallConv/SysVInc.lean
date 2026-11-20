module

import Kraken.Tactics
import Kraken.X64.Parser
import Kraken.X64.Sep
public import Kraken.X64.ProcSpec
public import Kraken.X64.SysV

/-!
# A procedure call under the System V AMD64 convention

`sysv_inc` returns its first argument plus one. `sysv_caller` is a SysV procedure that calls it.
Both satisfy `IncSpec`.
-/

open Kraken (WellFormedLayout)
open Kraken.X64.Parser
open Kraken.X64.Stack
open Kraken.X64.SysV
open Std.ExtHashMap

public section

namespace CallConv.SysVInc

def prog : Program := ⸨prog|
sysv_inc:
  movq %rdi, %rax
  addq $1, %rax
  ret
sysv_caller:
  -- We need to align the stack for the callee.
  subq $8, %rsp
  call sysv_inc
  addq $8, %rsp
  ret⸩

variable [WellFormedLayout prog]

/-- The address of label `l` in `prog`. -/
abbrev lbl (l : String) : Int64 := @Labels.label! (Executable.labels prog.toExecutable) l

private theorem lbl_inc : lbl "sysv_inc" = prog.toExecutable.addrOf 0 :=
  Labels.label!_of_label? (label?_eq_some_addrOf rfl)

private theorem lbl_caller : lbl "sysv_caller" = prog.toExecutable.addrOf 4 :=
  Labels.label!_of_label? (label?_eq_some_addrOf rfl)

/-- The specification of an increment procedure at `entry` that needs `d` bytes of stack. -/
abbrev IncSpec (d : Nat) (entry : Int64) : Prop :=
  prog.toExecutable.ProcSpec entry
    (fun (x : BitVec 64 × (Mem 64 → Prop)) ra t => CallPre d x.2 ra t ∧ ArgU64 t x.1)
    (fun x ra t s => CallPost d x.2 ra t s ∧ RetU64 s (x.1 + 1))

theorem inc_spec : IncSpec 0 (lbl "sysv_inc") := by
  rw [lbl_inc]
  rintro ⟨n, R⟩ ra t ⟨⟨-, hdf, hmem⟩, harg⟩
  simp only [Reg64s.get64] at hmem
  sym => kstep; tactic =>
  refine Eventually.done _ ⟨?_, ⟨?_, hdf, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩, ?_⟩
  · rw [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, Int64.ofBitVec_toBitVec]
  · simp (config := { zetaDelta := true })
  · exact Owned.intro hmem (Int.toBytes_length _ _)
  · simp only [Reg64s.get64] at harg
    simp (config := { zetaDelta := true }) [harg, BitVec.add_comm]

omit [WellFormedLayout prog] in
private theorem reserve16_eq (r : BitVec 64) :
    Reserve 16 r = Owned 8 (r - 8 - 8) ⋆ Owned 8 (r - 8) := by
  rw [Reserve, show (16 : Nat) = 8 + 8 from rfl, Owned.split 8 8 _ (by omega)]
  congr 2 <;> bv_omega

/-- The caller needs 16 bytes of stack: 8 of padding and 8 for the callee's return address. -/
theorem caller_spec (hinc : IncSpec 0 (lbl "sysv_inc")) :
    IncSpec 16 (lbl "sysv_caller") := by
  rw [lbl_inc] at hinc
  rw [lbl_caller]
  rintro ⟨n, R⟩ ra t ⟨⟨hal, hdf, hmem⟩, harg⟩
  rw [reserve16_eq, sep_assoc, sep_comm_l] at hmem
  obtain ⟨bs, hbs, hmem⟩ := Owned.elim hmem
  simp only [Reg64s.get64] at hmem hal harg
  sym =>
  kstep 2
  case h_mem => tactic => simp (config := { zetaDelta := true }); exact hmem
  case h_len => exact hbs
  kstep 0
  tactic =>
  rename_i v st r
  have hr : r = t.regs.rsp.toBitVec - 8 - 8 := by simp (config := { zetaDelta := true })
  clear_value v st r
  subst hr
  have hpush := Mem.storeInt_sep _ 8 bs _ _ ⟨hmem, hbs⟩ (prog.toExecutable.addrOf 7).toBitVec.toInt
  refine eventually_trans _ _ _ _
    (hinc (n, RetCell ra t.regs.rsp.toBitVec ⋆ (Owned 8 (t.regs.rsp.toBitVec - 8) ⋆ R))
      (prog.toExecutable.addrOf 7) _ ⟨⟨?_, hdf, ?_⟩, harg⟩) ?_
  · simp only [Reg64s.get64] at hal ⊢
    bv_omega
  · simp only [Reg64s.get64, Owned.zero, emp_sep]
    exact hpush
  rintro ⟨s', pc⟩ ⟨hpc, ⟨hrsp, hdf', hsaved, hm⟩, hret⟩
  dsimp only at hpc hdf' hrsp hsaved hm hret
  subst hpc
  simp only [Reg64s.get64, Owned.zero, emp_sep] at hrsp hsaved hm hret
  have er : t.regs.rsp.toBitVec = 8 + s'.regs.rsp.toBitVec := by rw [hrsp]; bv_omega
  rw [sep_comm_l, er] at hm
  sym =>
  kstep
  case h_mem => tactic => simp (config := { zetaDelta := true }); exact hm
  case h_len => exact Int.toBytes_length _ _
  kstep 0
  tactic =>
  obtain ⟨hbx, hbp, h12, h13, h14, h15⟩ := hsaved
  rw [← er] at hm
  refine Eventually.done _ ⟨?_, ⟨?_, hdf', ⟨hbx, hbp, h12, h13, h14, h15⟩, ?_⟩, hret⟩
  · rw [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, Int64.ofBitVec_toBitVec]
  · simp (config := { zetaDelta := true }) [er]
  · show (Owned 8 _ ⋆ (Reserve 16 _ ⋆ R)) s'.dmem
    rw [reserve16_eq, sep_assoc]
    exact Owned.intro hm (Int.toBytes_length _ _)

end CallConv.SysVInc
