module

import Kraken.X64.Parser
public import Kraken.X64.WP.Call
import Kraken.X64.Examples.CallConv.RunStep
public import Kraken.X64.Win64

/-!
# A procedure call under the Windows x64 convention

The same procedures as `CallConv.SysVInc`, but under `Kraken.X64.Win64`: the argument arrives in
`rcx`, and the callee homes it into the shadow space the caller allocated above the return address
before reading it back. The caller `win64_caller` allocates the shadow space plus padding with
`subq $40, %rsp` so that `rsp` is 16-byte aligned at the `call`. As under SysV, both satisfy
`IncSpec`, and `caller_spec` uses only the callee's `IncSpec`, through `ProcSpec.wp_call_owned`;
only `Pre`/`Post` differ.
-/

open Kraken.X64.Parser
open Kraken.X64.Stack
open Kraken.X64.Win64
open Std.ExtHashMap

public section

namespace CallConv.Win64Inc

def inc_body : Program := parse("
win64_inc:
  movq %rcx, 8(%rsp)
  movq 8(%rsp), %rax
  addq $1, %rax
  ret
")

variable [Host]

/-- The specification of an increment procedure at `entry` that needs `d` bytes of stack. -/
abbrev IncSpec (d : Nat) (entry : Int64) : Prop :=
  Host.exe.ProcSpec entry
    (fun (x : BitVec 64 × (Mem 64 → Prop)) ra t => CallPre d x.2 ra t ∧ ArgU64 t x.1)
    (fun x ra t s => CallPost d x.2 ra t s ∧ RetU64 s (x.1 + 1))

theorem inc_spec {j : Nat} (hj : inc_body.IsInfixAt Host.prog j)
    (hfirst : ∀ i, i < j → Host.prog[i]? ≠ some (.label "win64_inc")) :
    IncSpec 0 (label "win64_inc") := by
  rw [Host.label_addrOf hj.cons.1 hfirst]
  rintro ⟨n, R⟩ ra t ⟨⟨-, hdf, -, -, hmem⟩, harg⟩
  have h1 := hj.cons.2
  have h2 := h1.cons.2
  have h3 := h2.cons.2
  have h4 := h3.cons.2
  run_step hj
  -- the home slot of `rcx`, `[rsp + 8]`, to the head of the tree
  rw [Shadow_split, sep_assoc, sep_comm_l] at hmem
  obtain ⟨bs, hbs, hmem⟩ := Owned.elim hmem
  have hslot := Mem.loadInt_sep bs _ 8 _ _ hmem hbs (by decide)
  have hmem' := Mem.storeInt_sep _ 8 bs _ _ ⟨hmem, hbs⟩ (t.regs.get64 .rcx).toInt
  have hhome := Mem.loadInt_sep _ _ 8 _ _ hmem' (Int.toBytes_length _ _) (by decide)
  rw [sep_comm_l] at hmem'
  have hret := Mem.loadInt_sep _ _ 8 _ _ hmem' (Int.toBytes_length _ _) (by decide)
  have e8 : Int64.toBitVec 8 = 8 := rfl
  -- movq %rcx, 8(%rsp)
  run_step h1 [AddrExpr.interp_reg_disp, e8]
  refine Effects.All_store (w := .W64) (by rw [hslot]; rfl) ?_
  simp only [Effects.All]
  -- movq 8(%rsp), %rax
  run_step h2 [AddrExpr.interp_reg_disp, e8]
  refine Effects.All_load (w := .W64) hhome ?_
  simp only [Effects.All]
  rw [show BitVec.ofInt Width.W64.bits (Int.ofBytes (Int.toBytes 8 (t.regs.get64 .rcx).toInt))
    = t.regs.get64 .rcx from BitVec.ofInt_ofBytes_toBytes 64 8 rfl _]
  -- addq $1, %rax
  run_step h3
  -- ret
  run_step h4 [Reg64s.get64_set64, reduceCtorEq, ite_false]
  refine Effects.All_load (w := .W64) hret ?_
  simp only [Effects.All]
  refine Eventually.done _ ⟨?_, ?_, ?_⟩
  · show Int64.ofBitVec (BitVec.ofInt 64 _) = ra
    rw [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, Int64.ofBitVec_toBitVec]
  · refine ⟨?_, hdf, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    any_goals simp [Reg64s.get64_set64]
    refine Owned.intro (sep_mono (fun _ h => h) (fun m hm => ?_) hmem') (Int.toBytes_length _ _)
    rw [Shadow_split, sep_assoc]
    exact Owned.intro hm (Int.toBytes_length _ _)
  · simp only [RetU64, Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true]
    rw [show t.regs.get64 .rcx = n from harg, BitVec.add_comm]
    rfl

/-- A Windows x64 procedure that calls `win64_inc`. On entry `rsp + 8` is 16-byte aligned, so it
allocates the callee's 32-byte shadow space plus 8 bytes of padding to make `rsp` 16-byte aligned
at the `call`. -/
def caller : Program := parse("
win64_caller:
  subq $40, %rsp
  call win64_inc
  addq $40, %rsp
  ret
")

omit [Host] in
/-- The caller's 48-byte reservation: the callee's return-address slot, its shadow space, and the
padding. -/
private theorem frame_eq (r : BitVec 64) :
    Reserve 48 r = Owned 8 (r - 48) ⋆ (Shadow (r - 48) ⋆ Owned 8 (r - 8)) := by
  rw [Reserve, show (48 : Nat) = 8 + (32 + 8) from rfl, Owned.split 8 _ _ (by omega),
    Owned.split 32 8 _ (by omega)]
  congr 3 <;> bv_omega

/-- The caller needs 48 bytes of stack: 8 of padding, and the callee's shadow space and return
address. -/
theorem caller_spec {c : Nat} (hc : caller.IsInfixAt Host.prog c)
    (hcfirst : ∀ i, i < c → Host.prog[i]? ≠ some (.label "win64_caller"))
    (hinc : IncSpec 0 (label "win64_inc")) :
    IncSpec 48 (label "win64_caller") := by
  rw [Host.label_addrOf hc.cons.1 hcfirst]
  rintro ⟨n, R⟩ ra t ⟨⟨hal, hdf, hle, -, hmem⟩, harg⟩
  have h1 := hc.cons.2
  have h2 := h1.cons.2
  have h3 := h2.cons.2
  have h4 := h3.cons.2
  -- the callee's slot and shadow space to the head of the tree
  rw [frame_eq] at hmem
  dsimp only at hmem
  have hmem : t.dmem =⋆ Owned 8 (t.regs.get64 .rsp - 48) ⋆ (Shadow (t.regs.get64 .rsp - 48)
      ⋆ (RetCell ra (t.regs.get64 .rsp) ⋆ (Shadow (t.regs.get64 .rsp)
        ⋆ (Owned 8 (t.regs.get64 .rsp - 8) ⋆ R)))) :=
    cast (congrFun (by ac_rfl) _) hmem
  have e40 : BitVec.truncate Width.W64.bits (Int64.toBitVec 40) = 40 := rfl
  -- the frame arithmetic, for any `r`: `bv_omega` does not go through on the `get64` terms
  have e48 : ∀ r : BitVec 64, r - 40 - 8 = r - 48 := fun _ => by bv_omega
  have eal : ∀ r : BitVec 64, r.toNat % 16 = 8 → (r - 48).toNat % 16 = 8 := fun _ _ => by bv_omega
  have ebd : ∀ r : BitVec 64, 48 ≤ r.toNat → (r - 48).toNat + 40 ≤ 2 ^ 64 := fun _ _ => by
    bv_omega
  have eret : ∀ r : BitVec 64, 40 + (r - 48 + 8) = r := fun _ => by bv_omega
  run_step hc
  -- subq $40, %rsp
  run_step h1 [e40]
  -- call win64_inc
  refine Host.run_wp h2 ?_
  refine hinc.wp_call_owned
    (n, RetCell ra (t.regs.get64 .rsp) ⋆ (Shadow (t.regs.get64 .rsp)
      ⋆ (Owned 8 (t.regs.get64 .rsp - 8) ⋆ R)))
    (by simpa only [Reg64s.get64_set64_self, e48]) ?_ ?_
  · intro ra' hpushed
    refine ⟨⟨?_, by simpa using hdf, by simp, ?_, ?_⟩, ?_⟩
    · simp only [EntryAligned, MachineData.get64_pushRa, ite_true, Reg64s.get64_set64_self, e48]
      exact eal _ hal
    · simp only [MachineData.get64_pushRa, ite_true, Reg64s.get64_set64_self, e48]
      exact ebd _ hle
    · simpa only [MachineData.get64_pushRa, ite_true, Reserve.zero, emp_sep,
        Reg64s.get64_set64_self, e48] using hpushed
    · simpa only [ArgU64, MachineData.get64_pushRa, reduceCtorEq, ite_false,
        Reg64s.get64_set64_ne _ (show Reg64.rsp ≠ .rcx by decide)] using harg
  · rintro ra' s' ⟨⟨hrsp, hdf', hsaved, hxmm, hm⟩, hret⟩
    simp only [MachineData.get64_pushRa, ite_true, Reg64s.get64_set64_self, e48, Reserve.zero,
      emp_sep] at hrsp hm
    have er : 40 + s'.regs.get64 .rsp = t.regs.get64 .rsp := by rw [hrsp]; exact eret _
    -- restate `hm` syntactically: `ac_rfl` fails on the form `simp` leaves behind
    replace hm : s'.dmem =⋆ Owned 8 (t.regs.get64 .rsp - 48) ⋆ (Shadow (t.regs.get64 .rsp - 48)
        ⋆ (RetCell ra (t.regs.get64 .rsp) ⋆ (Shadow (t.regs.get64 .rsp)
          ⋆ (Owned 8 (t.regs.get64 .rsp - 8) ⋆ R)))) := hm
    have hm' : s'.dmem =⋆ RetCell ra (t.regs.get64 .rsp) ⋆ (Shadow (t.regs.get64 .rsp)
        ⋆ (Owned 8 (t.regs.get64 .rsp - 48) ⋆ (Shadow (t.regs.get64 .rsp - 48)
          ⋆ (Owned 8 (t.regs.get64 .rsp - 8) ⋆ R)))) :=
      cast (congrFun (by ac_rfl) _) hm
    have hretld := Mem.loadInt_sep _ _ 8 _ _ hm' (Int.toBytes_length _ _) (by decide)
    -- addq $40, %rsp
    run_step h3 [e40]
    -- ret
    run_step h4 [er]
    refine Effects.All_load (w := .W64) hretld ?_
    simp only [Effects.All]
    refine Eventually.done _ ⟨?_, ⟨?_, hdf', ?_, ?_, ?_⟩, ?_⟩
    · show Int64.ofBitVec (BitVec.ofInt 64 _) = ra
      rw [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, Int64.ofBitVec_toBitVec]
    · simp
    · obtain ⟨hbx, hbp, hdi, hsi, h12, h13, h14, h15⟩ := hsaved
      simp_all [SavedRegs, Reg64s.get64_set64]
    · simpa [SavedXmm] using hxmm
    · refine Owned.intro (bs := Int.toBytes 8 ra.toBitVec.toInt) ?_ (Int.toBytes_length _ _)
      rw [frame_eq]
      simp only [RetCell] at hm'
      exact cast (congrFun (by ac_rfl) _) hm'
    · simpa [RetU64, Reg64s.get64_set64] using hret

end CallConv.Win64Inc
