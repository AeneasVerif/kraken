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

open Kraken (Layout)
open Kraken.X64
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

variable (layout : Layout) [prog.AssemblableWith layout]

/-- The address of label `l` in `prog`. -/
abbrev lbl (l : String) : Int64 := @Labels.label! (Executable.labels (layout.apply prog)) l

private theorem lbl_inc : lbl layout "sysv_inc" = (layout.apply prog).addrOf 0 :=
  Labels.label!_of_label? (label?_eq_some_addrOf rfl)

private theorem lbl_caller : lbl layout "sysv_caller" = (layout.apply prog).addrOf 4 :=
  Labels.label!_of_label? (label?_eq_some_addrOf rfl)

/-- The specification of an increment procedure at `entry` that needs `d` bytes of stack. -/
abbrev IncSpec (d : Nat) (entry : Int64) : Prop :=
  ∀ (n : BitVec 64) (R : Mem 64 → Prop) (ra : Int64),
    (layout.apply prog).ProcSpec entry ra
      (fun t => SysV.Call d R ra t ∧ ArgU64 t n)
      (fun t s => SysV.Ret d R ra t s ∧ RetU64 s (n + 1))

theorem inc_spec : IncSpec layout 0 (lbl layout "sysv_inc") := by
  rw [lbl_inc]
  rintro n R ra t ⟨⟨-, hdf, hmem⟩, harg⟩
  sym => kstep; tactic =>
  refine Eventually.done _ ⟨?_, ⟨?_, hdf, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩, ?_⟩
  · rw [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, Int64.ofBitVec_toBitVec]
  · simp (config := { zetaDelta := true })
  · exact Owned.intro hmem (Int.toBytes_length _ _)
  · simp (config := { zetaDelta := true }) [harg, BitVec.add_comm]

omit [prog.AssemblableWith layout] in
private theorem reserve16_eq (r : BitVec 64) :
    Reserve 16 r = Owned 8 (r - 8 - 8) ⋆ Owned 8 (r - 8) := by
  rw [Reserve, show (16 : Nat) = 8 + 8 from rfl, Owned.split 8 8 _ (by omega)]
  congr 2 <;> bv_omega

/-- The caller needs 16 bytes of stack: 8 of padding and 8 for the callee's return address. -/
theorem caller_spec (hinc : IncSpec layout 0 (lbl layout "sysv_inc")) :
    IncSpec layout 16 (lbl layout "sysv_caller") := by
  rw [lbl_inc] at hinc
  rw [lbl_caller]
  rintro n R ra t ⟨⟨hal, hdf, hmem⟩, harg⟩
  rw [reserve16_eq, sep_assoc, sep_comm_l] at hmem
  obtain ⟨bs, hbs, hmem⟩ := Owned.elim hmem
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
  have hpush := Mem.storeInt_sep _ 8 bs _ _ ⟨hmem, hbs⟩ ((layout.apply prog).addrOf 7).toBitVec.toInt
  refine eventually_trans _ _ _ _
    (hinc n (RetCell ra t.regs.rsp.toBitVec ⋆ (Owned 8 (t.regs.rsp.toBitVec - 8) ⋆ R))
      ((layout.apply prog).addrOf 7) _ ⟨⟨?_, hdf, ?_⟩, harg⟩) ?_
  · dsimp only at hal ⊢
    bv_omega
  · simp only [Owned.zero, emp_sep]
    exact hpush
  rintro ⟨s', pc⟩ ⟨hpc, ⟨hrsp, hdf', hsaved, hm⟩, hret⟩
  dsimp only at hpc hdf' hrsp hsaved hm hret
  subst hpc
  simp only [Owned.zero, emp_sep] at hrsp hsaved hm hret
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
