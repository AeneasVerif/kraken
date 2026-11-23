module

import Kraken.Tactics
import Kraken.X64.Parser
import Kraken.X64.Sep
public import Kraken.X64.ProcSpec
public import Kraken.X64.Win64

/-!
# A procedure call under the Windows x64 convention

The same procedures as `CallConv.SysVInc`, but under `Kraken.X64.Win64`: the argument arrives in
`rcx`, and the callee homes it into the shadow space the caller allocated above the return address
before reading it back.
-/

open Kraken (WellFormedLayout)
open Kraken.X64
open Kraken.X64.Parser
open Kraken.X64.Stack
open Kraken.X64.Win64
open Std.ExtHashMap

public section

namespace CallConv.Win64Inc

def prog : Program := ⸨prog|
win64_inc:
  movq %rcx, 8(%rsp)
  movq 8(%rsp), %rax
  addq $1, %rax
  ret
win64_caller:
  -- Allocate the shadow space (32 bytes) and align the stack (8 more bytes).
  subq $40, %rsp
  call win64_inc
  addq $40, %rsp
  ret⸩

variable [WellFormedLayout prog]

/-- The address of label `l` in `prog`. -/
abbrev lbl (l : String) : Int64 := @Labels.label! (Executable.labels prog.toExecutable) l

private theorem lbl_inc : lbl "win64_inc" = prog.toExecutable.addrOf 0 :=
  label_eq_addrOf rfl

private theorem lbl_caller : lbl "win64_caller" = prog.toExecutable.addrOf 5 :=
  label_eq_addrOf rfl

omit [WellFormedLayout prog] in
private theorem shadow_split (r : BitVec 64) : Shadow r = Owned 8 (r + 8) ⋆ Owned 24 (r + 16) := by
  rw [Shadow, show (32 : Nat) = 8 + 24 from rfl, Owned.split 8 24 _ (by omega)]
  congr 2
  bv_omega

abbrev IncSpec (d : Nat) (entry : Int64) : Prop :=
  ∀ (n : BitVec 64) (R : Mem 64 → Prop) (ra : Int64),
    prog.toExecutable.ProcSpec entry ra
      (fun t => Win64.Call d R ra t ∧ ArgU64 t n)
      (fun t s => Win64.Ret d R ra t s ∧ RetU64 s (n + 1))

theorem inc_spec : IncSpec 0 (lbl "win64_inc") := by
  rw [lbl_inc]
  rintro n R ra t ⟨⟨-, hdf, hmem⟩, harg⟩
  rw [shadow_split, sep_assoc, sep_comm_l] at hmem
  obtain ⟨bs, hbs, hmem⟩ := Owned.elim hmem
  have e8 : ∀ x : BitVec 64, x + 8 = BitVec.ofInt 64 (x.toInt + 8) := fun x => by
    simp [BitVec.ofInt_add]
  rw [e8] at hmem
  have hmem' := Mem.storeInt_sep _ 8 bs _ _ ⟨hmem, hbs⟩ t.regs.rcx.toBitVec.toInt
  have hmem'' := hmem'
  rw [sep_comm_l] at hmem''
  sym =>
  kstep 1
  case h_mem => tactic => simp; exact hmem
  case h_len => exact hbs
  kstep 1
  case h_mem => tactic => simp; exact hmem'
  case h_len => exact Int.toBytes_length _ _
  kstep
  case h_mem => tactic => simp (config := { zetaDelta := true }); exact hmem''
  case h_len => exact Int.toBytes_length _ _
  kstep 0
  tactic =>
  refine Eventually.done _ ⟨?_, ⟨?_, hdf, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩, ?_⟩
  · rw [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, Int64.ofBitVec_toBitVec]
  · simp (config := { zetaDelta := true })
  · simp only [← e8] at hmem''
    simp only [Nat.shiftRight_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq, Int.add_zero]
    rw [show Int64.toInt 8 = 8 from rfl, ← e8]
    show (Owned 8 _ ⋆ (Shadow _ ⋆ _)) _
    refine Owned.intro (sep_mono (fun _ h => h) (fun m hm => ?_) hmem'') (Int.toBytes_length _ _)
    rw [shadow_split, sep_assoc]
    exact Owned.intro hm (Int.toBytes_length _ _)
  · simp (config := { zetaDelta := true }) [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, harg,
      BitVec.add_comm]

omit [WellFormedLayout prog] in
/-- The caller's 48-byte reservation: the callee's return-address slot, its shadow space, and the padding. -/
private theorem frame_eq (r : BitVec 64) :
    Reserve 48 r = Owned 8 (r - 40 - 8) ⋆ (Shadow (r - 40 - 8) ⋆ Owned 8 (r - 8)) := by
  rw [Reserve, show (48 : Nat) = 8 + (32 + 8) from rfl, Owned.split 8 _ _ (by omega),
    Owned.split 32 8 _ (by omega), show r - 40 - 8 = r - BitVec.ofNat 64 48 by bv_omega]
  congr 3 <;> bv_omega

theorem caller_spec (hinc : IncSpec 0 (lbl "win64_inc")) : IncSpec 48 (lbl "win64_caller") := by
  rw [lbl_inc] at hinc
  rw [lbl_caller]
  rintro n R ra t ⟨⟨hal, hdf, hmem⟩, harg⟩
  rw [frame_eq] at hmem
  replace hmem : t.dmem =⋆ Owned 8 (t.regs.rsp.toBitVec - 40 - 8)
      ⋆ (Shadow (t.regs.rsp.toBitVec - 40 - 8) ⋆ (RetCell ra t.regs.rsp.toBitVec
        ⋆ (Shadow t.regs.rsp.toBitVec ⋆ (Owned 8 (t.regs.rsp.toBitVec - 8) ⋆ R)))) :=
    cast (congrFun (by ac_rfl) _) hmem
  obtain ⟨bs, hbs, hmem⟩ := Owned.elim hmem
  sym =>
  kstep 2
  case h_mem => tactic => simp (config := { zetaDelta := true }); exact hmem
  case h_len => exact hbs
  kstep 0
  tactic =>
  rename_i v st r
  have hr : r = t.regs.rsp.toBitVec - 40 - 8 := by simp (config := { zetaDelta := true })
  clear_value v st r
  subst hr
  simp only [lbl_inc]
  have hpush := Mem.storeInt_sep _ 8 bs _ _ ⟨hmem, hbs⟩ (prog.toExecutable.addrOf 8).toBitVec.toInt
  refine eventually_trans _ _ _ _
    (hinc n (RetCell ra t.regs.rsp.toBitVec ⋆ (Shadow t.regs.rsp.toBitVec
        ⋆ (Owned 8 (t.regs.rsp.toBitVec - 8) ⋆ R)))
      (prog.toExecutable.addrOf 8) _ ⟨⟨?_, hdf, ?_⟩, harg⟩) ?_
  · dsimp only at hal ⊢
    bv_omega
  · simp only [Owned.zero, emp_sep]
    exact hpush
  rintro ⟨s', pc⟩ ⟨hpc, ⟨hrsp, hdf', hsaved, hxmm, hm⟩, hret⟩
  dsimp only at hpc hdf' hrsp hsaved hm hret
  subst hpc
  simp only [Owned.zero, emp_sep] at hrsp hsaved hm hret
  have er : t.regs.rsp.toBitVec = 40 + s'.regs.rsp.toBitVec := by rw [hrsp]; bv_omega
  have hm' : s'.dmem =⋆ RetCell ra t.regs.rsp.toBitVec ⋆ (Owned 8 (t.regs.rsp.toBitVec - 40 - 8)
      ⋆ (Owned 32 (t.regs.rsp.toBitVec - 40 - 8 + 8) ⋆ (Shadow t.regs.rsp.toBitVec
        ⋆ (Owned 8 (t.regs.rsp.toBitVec - 8) ⋆ R)))) :=
    cast (congrFun (by ac_rfl) _) hm
  have hret' := hm'
  rw [er] at hret'
  sym =>
  kstep
  case h_mem => tactic => simp (config := { zetaDelta := true }); exact hret'
  case h_len => exact Int.toBytes_length _ _
  kstep 0
  tactic =>
  obtain ⟨hbx, hbp, hdi, hsi, h12, h13, h14, h15⟩ := hsaved
  refine Eventually.done _
    ⟨?_, ⟨?_, hdf', ⟨hbx, hbp, hdi, hsi, h12, h13, h14, h15⟩, hxmm, ?_⟩, hret⟩
  · rw [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, Int64.ofBitVec_toBitVec]
  · simp (config := { zetaDelta := true }) [er]
  · show (Owned 8 _ ⋆ (Shadow _ ⋆ (Reserve 48 _ ⋆ R))) s'.dmem
    rw [frame_eq]
    simp only [Shadow] at hm' ⊢
    exact Owned.intro (cast (congrFun (by ac_rfl) _) hm') (Int.toBytes_length _ _)

end CallConv.Win64Inc
