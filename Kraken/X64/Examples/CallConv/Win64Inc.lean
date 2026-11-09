module

import Kraken.X64.Parser
public import Kraken.X64.WP.Call
import Kraken.X64.Examples.CallConv.RunStep
public import Kraken.Win64

/-!
# A procedure call under the Windows x64 convention

The same procedure as `CallConv.SysVInc`, but under `Kraken.Win64`: the argument arrives in `rcx`,
and the callee homes it into the shadow space the caller allocated above the return address before
reading it back. The caller `win64_caller`, itself a Windows x64 procedure, allocates the shadow
space plus padding with `subq $40, %rsp` so that `rsp` is 16-byte aligned at the `call`. The call
rule `ProcSpec.wp_call_owned` is the one used under SysV; only `Pre`/`Post` differ.
-/

open Kraken.X64.Parser
open Kraken.Stack
open Kraken.Win64
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

theorem inc_spec {j : Nat} (hj : inc_body.IsInfixAt Host.prog j) :
    Host.exe.ProcSpec (Host.addrOf j)
      (fun (x : BitVec 64 × (Mem 64 → Prop)) ra t => CallPre 0 x.2 ra t ∧ ArgU64 t x.1)
      (fun x ra t s => CallPost 0 x.2 ra t s ∧ RetU64 s (x.1 + 1)) := by
  rintro ⟨n, R⟩ ra t ⟨⟨hal, hdf, hmem⟩, harg⟩
  have h1 := hj.cons.2
  have h2 := h1.cons.2
  have h3 := h2.cons.2
  have h4 := h3.cons.2
  run_step hj
  -- the home slot of `rcx`, `[rsp + 8]`, to the head of the tree
  have hb := Shadow.le_second hmem
  rw [Shadow_split _ hb, sep_assoc, sep_comm_l] at hmem
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
  · refine ⟨?_, hdf, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    any_goals simp [Reg64s.get64_set64]
    refine Owned.intro (sep_mono (fun _ h => h) (fun m hm => ?_) hmem') (Int.toBytes_length _ _)
    rw [Shadow_split _ hb, sep_assoc]
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
/-- A procedure that enters with `rsp + 8` aligned and moves `rsp` down by 40 before a `call`
enters its callee with `rsp + 8` aligned. -/
private theorem aligned_sub_48 {r : BitVec 64} (h : r.toNat % 16 = 8) : (r - 48).toNat % 16 = 8 := by
  bv_omega

omit [Host] in
private theorem sub_40_sub_8 (r : BitVec 64) : r - 40 - 8 = r - 48 := by bv_omega

omit [Host] in
private theorem add_40_sub_48_add_8 (r : BitVec 64) : 40 + (r - 48 + 8) = r := by bv_omega

omit [Host] in
/-- The caller's 48-byte reservation: the callee's return-address slot, its shadow space, and the
padding. -/
theorem frame_eq {r : BitVec 64} (h : 48 ≤ r.toNat) :
    Reserve 48 r = Owned 8 (r - 48) ⋆ (Shadow (r - 48) ⋆ Owned 8 (r - 8)) := by
  have h1 := Owned.split 8 40 (r - .ofNat 64 48) (by omega)
  have h2 := Owned.split 32 8 (r - .ofNat 64 48 + .ofNat 64 8) (by omega)
  simp only [Nat.reduceAdd] at h1 h2
  have e : r - BitVec.ofNat 64 48 + BitVec.ofNat 64 8 + BitVec.ofNat 64 32 = r - 8 := by bv_omega
  rw [Reserve_eq 48 r h, h1, h2, e, Shadow_eq _ (by bv_omega)]
  rfl

/-- The caller's specification has the same shape as `inc_spec`: the convention, with a 48-byte
reservation, plus the argument and the result. It is proved from `inc_spec` alone, through
`ProcSpec.wp_call_owned`. The caller's own shadow space is passed to the callee untouched, as part
of the frame. -/
theorem caller_spec {j c : Nat} (hj : inc_body.IsInfixAt Host.prog j)
    (hfirst : ∀ i, i < j → Host.prog[i]? ≠ some (.label "win64_inc"))
    (hc : caller.IsInfixAt Host.prog c) :
    Host.exe.ProcSpec (Host.addrOf c)
      (fun (x : BitVec 64 × (Mem 64 → Prop)) ra t => CallPre 48 x.2 ra t ∧ ArgU64 t x.1)
      (fun x ra t s => CallPost 48 x.2 ra t s ∧ RetU64 s (x.1 + 1)) := by
  rintro ⟨n, R⟩ ra t ⟨⟨hal, hdf, hmem⟩, harg⟩
  have h1 := hc.cons.2
  have h2 := h1.cons.2
  have h3 := h2.cons.2
  have h4 := h3.cons.2
  have hle := Reserve.le_third hmem
  -- the callee's slot and shadow space to the head of the tree; the rest is the callee's frame `F`
  rw [frame_eq hle] at hmem
  dsimp only at hmem
  have hmem : t.dmem =⋆ Owned 8 (t.regs.get64 .rsp - 48) ⋆ (Shadow (t.regs.get64 .rsp - 48)
      ⋆ (RetCell ra (t.regs.get64 .rsp) ⋆ (Shadow (t.regs.get64 .rsp)
        ⋆ (Owned 8 (t.regs.get64 .rsp - 8) ⋆ R)))) :=
    cast (congrFun (by ac_rfl) _) hmem
  have e40 : BitVec.truncate Width.W64.bits (Int64.toBitVec 40) = 40 := rfl
  have e48 : t.regs.get64 .rsp - 40 - 8 = t.regs.get64 .rsp - 48 := sub_40_sub_8 _
  run_step hc
  -- subq $40, %rsp
  run_step h1 [e40]
  -- call win64_inc
  refine Host.run_wp h2 ?_
  refine (inc_spec hj).wp_call_owned (Host.label_addrOf hj.cons.1 hfirst)
    (n, RetCell ra (t.regs.get64 .rsp) ⋆ (Shadow (t.regs.get64 .rsp)
      ⋆ (Owned 8 (t.regs.get64 .rsp - 8) ⋆ R)))
    (by simpa only [Reg64s.get64_set64_self, e48]) ?_ ?_
  · intro ra' hpushed
    refine ⟨⟨?_, by simpa using hdf, ?_⟩, ?_⟩
    · simp only [EntryAligned, MachineData.get64_pushRa, ite_true, Reg64s.get64_set64_self, e48]
      exact aligned_sub_48 hal
    · simpa only [MachineData.get64_pushRa, ite_true, Reserve.zero, emp_sep,
        Reg64s.get64_set64_self, e48] using hpushed
    · simpa only [ArgU64, MachineData.get64_pushRa, reduceCtorEq, ite_false,
        Reg64s.get64_set64_ne _ (show Reg64.rsp ≠ .rcx by decide)] using harg
  · rintro ra' s' ⟨⟨hrsp, hdf', hrbp, hsaved, hxmm, hm⟩, hret⟩
    simp only [MachineData.get64_pushRa, ite_true, Reg64s.get64_set64_self, e48, Reserve.zero,
      emp_sep] at hrsp hm
    have er : 40 + s'.regs.get64 .rsp = t.regs.get64 .rsp := by
      rw [hrsp]; exact add_40_sub_48_add_8 _
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
    refine Eventually.done _ ⟨?_, ⟨?_, hdf', ?_, ?_, ?_, ?_⟩, ?_⟩
    · show Int64.ofBitVec (BitVec.ofInt 64 _) = ra
      rw [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, Int64.ofBitVec_toBitVec]
    · simp
    · simpa [Reg64s.get64_set64] using hrbp
    · obtain ⟨hbx, hdi, hsi, h12, h13, h14, h15⟩ := hsaved
      simp_all [SavedRegs, Reg64s.get64_set64]
    · simpa [SavedXmm] using hxmm
    · refine Owned.intro (bs := Int.toBytes 8 ra.toBitVec.toInt) ?_ (Int.toBytes_length _ _)
      rw [frame_eq hle]
      simp only [RetCell] at hm'
      exact cast (congrFun (by ac_rfl) _) hm'
    · simpa [RetU64, Reg64s.get64_set64] using hret

end CallConv.Win64Inc
