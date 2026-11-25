module

import Kraken.SeparationTactics
import Kraken.Tactics
import Kraken.X64.Parser
import Kraken.X64.Sep
public import Kraken.X64.ProcSpec
public import Kraken.X64.SysV

/-!
# x86-64 `memcpy` Verification

Functional correctness of System V AMD64 ABI `memcpy(dst, src, n)` using
`tailrec_loop`.
-/

open Kraken (WellFormedLayout)
open Kraken.X64
open Kraken.X64.Parser
open Kraken.X64.Stack
open Kraken.X64.SysV
open Std.ExtHashMap

public section

namespace Examples.Memcpy

/-- System V AMD64 ABI `memcpy(dst, src, n)`:
- Arguments: `%rdi = dst`, `%rsi = src`, `%rdx = n`, `(%rsp) = ra`
- Returns: `%rax = dst`, `%rsp = rsp₀ + 8`, `pc = ra`, callee-saved registers preserved,
  and `src` bytes copied into `dst`. -/
def memcpy : Program := ⸨prog|
memcpy:
  movq %rdi, %rax
  subq $0, %rdx
  jz done
loop:
  movb (%rsi), %cl
  movb %cl, (%rdi)
  addq $1, %rsi
  addq $1, %rdi
  subq $1, %rdx
  jnz loop
done:
  ret
⸩

abbrev lbl [WellFormedLayout memcpy] (l : String) : Int64 :=
  @Labels.label! (Executable.labels memcpy.toExecutable) l

private theorem lbl_memcpy [WellFormedLayout memcpy] :
    lbl "memcpy" = memcpy.toExecutable.addrOf 0 :=
  Labels.label!_of_label? (label?_eq_some_addrOf rfl)

private theorem byte_roundtrip (b : UInt8) :
    Int.toBytes 1 (BitVec.ofInt 8 (Int.ofBytes [b])).toInt = [b] := by
  have h := UInt8.toBytes_ofBytes [b] (Nat.le_refl 1)
  simpa [UInt8.toBytes, UInt8.ofBytes] using h

private theorem replaceLow_low (r : BitVec 64) (b : BitVec 8) :
    BitVec.ofNat 8 (r.replaceLow b).toNat = b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_ofNat, decide_eq_true hi, Bool.true_and]
  change (r.replaceLow b).getLsbD i = b.getLsbD i
  simp only [BitVec.replaceLow, BitVec.getLsbD_setWidth,
    show i < 64 by omega, decide_true, Bool.true_and]
  rw [show (r.drop 8).append b = r.drop 8 ++ b from rfl, BitVec.getLsbD_append]
  simp [hi]

private theorem sep_cons (b : UInt8) (bs : List UInt8) (p : BitVec 64)
    (h_len : bs.length + 1 ≤ 2 ^ 64) :
    Eq ((b :: bs).At p) = Eq ([b].At p) ⋆ Eq (bs.At (p + 1#64)) := by
  simpa [Nat.add_comm] using Mem.At_append_sep [b] bs p (by simp; omega)

/-- Symbolic execution of one iteration of `memcpy`'s loop body (`loop:` through `jnz loop`). -/
private theorem memcpy_step [layout : WellFormedLayout memcpy] (s : MachineData)
    (b0 d0 : UInt8) (R_src R_dst : Mem 64 → Prop)
    (h_src : s.dmem =⋆ Eq ([b0].At s.regs.rsi.toBitVec) ⋆ R_src)
    (h_dst : s.dmem =⋆ Eq ([d0].At s.regs.rdi.toBitVec) ⋆ R_dst) :
    Eventually (step1 memcpy.toExecutable)
      (fun st =>
        st.pc = (if s.regs.rdx.toBitVec - 1#64 == 0#64
          then memcpy.toExecutable.addrOf 11
          else memcpy.toExecutable.addrOf 4) ∧
        st.data.regs.rax = s.regs.rax ∧
        st.data.regs.rsp = s.regs.rsp ∧
        st.data.regs.rsi = s.regs.rsi + 1 ∧
        st.data.regs.rdi = s.regs.rdi + 1 ∧
        st.data.regs.rdx = s.regs.rdx - 1 ∧
        st.data.df = s.df ∧
        SysV.SavedRegs s st.data ∧
        st.data.dmem = Mem.storeInt s.dmem s.regs.rdi.toBitVec 1
          (BitVec.ofInt 8 (Int.ofBytes [b0])).toInt)
      ⟨s, memcpy.toExecutable.addrOf 4⟩ := by
  sym =>
  kstep 1
  case h_mem => tactic => simp (config := { zetaDelta := true }); exact h_src
  case h_len => exact rfl
  kstep 1
  case h_mem => tactic => simp (config := { zetaDelta := true }); exact h_dst
  case h_len => exact rfl
  kstep 4
  tactic =>
  rename_i v_rsi _ v_rdi _ v_rdx _
  have h_rsi_eq : v_rsi = s.regs.rsi.toBitVec + 1#64 := by grind
  have h_rdi_eq : v_rdi = s.regs.rdi.toBitVec + 1#64 := by grind
  have h_rdx_eq : v_rdx = s.regs.rdx.toBitVec - 1#64 := by grind
  by_cases hzero : s.regs.rdx.toBitVec - 1#64 = 0#64
  · have hcond : (!(v_rdx == BitVec.zero 64)) = false := by
      simp [h_rdx_eq, hzero, BitVec.zero]
    simp only [hcond, Bool.false_eq_true, ↓reduceIte]
    sym => kstep 0; tactic =>
    refine .done _ ⟨by simp [hzero], rfl, rfl,
      by simp [h_rsi_eq],
      by simp [h_rdi_eq],
      by simp [h_rdx_eq],
      rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
    dsimp only
    congr 1
    · simp (config := { zetaDelta := true })
    · simp only [Nat.shiftRight_zero, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (BitVec.isLt _), replaceLow_low]
  · have hcond : (!(v_rdx == BitVec.zero 64)) = true := by
      simp [h_rdx_eq, hzero, BitVec.zero]
    simp only [hcond, ↓reduceIte]
    sym => kstep 0; tactic =>
    refine .done _ ⟨by simp [hzero], rfl, rfl,
      by simp [h_rsi_eq],
      by simp [h_rdi_eq],
      by simp [h_rdx_eq],
      rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
    dsimp only
    congr 1
    · simp (config := { zetaDelta := true })
    · simp only [Nat.shiftRight_zero, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (BitVec.isLt _), replaceLow_low]

/-- Ghost state threaded through `memcpy`'s tail-recursive loop invariant. -/
private structure LoopGhost where
  dstPtr : BitVec 64
  srcPtr : BitVec 64
  dst : List UInt8
  src : List UInt8
  frame : Mem 64 → Prop

theorem memcpy_correct [layout : WellFormedLayout memcpy]
    (dst_ptr src_ptr : BitVec 64) (dst src : List UInt8) (n : Nat)
    (R : Mem 64 → Prop) (ra : Int64) :
    memcpy.toExecutable.ProcSpec (lbl "memcpy") ra
      (fun t =>
        SysV.Call 0 (Eq (dst.At dst_ptr) ⋆ Eq (src.At src_ptr) ⋆ R) ra t ∧
        t.regs.rdi.toBitVec = dst_ptr ∧
        t.regs.rsi.toBitVec = src_ptr ∧
        t.regs.rdx.toNat = n ∧
        dst.length = n ∧ src.length = n)
      (fun t s =>
        SysV.Ret 0 (Eq (src.At dst_ptr) ⋆ Eq (src.At src_ptr) ⋆ R) ra t s ∧
        SysV.RetU64 s dst_ptr) := by
  rw [lbl_memcpy]
  rintro t ⟨⟨_, hdf, hmem⟩, h_rdi, h_rsi, h_rdx, h_dst_len, h_src_len⟩
  simp only [Owned.zero, emp_sep] at hmem
  let frame₀ : Mem 64 → Prop := RetCell ra t.regs.rsp.toBitVec ⋆ R
  have hmem₀ : t.dmem =⋆ Eq (dst.At dst_ptr) ⋆ Eq (src.At src_ptr) ⋆ frame₀ := by
    dsimp [frame₀]; ecancel
  let Q (g : LoopGhost) (st : MachineState) : Prop :=
    st.pc = memcpy.toExecutable.addrOf 11 ∧
    st.data.regs.rax.toBitVec = dst_ptr ∧
    st.data.regs.rsp = t.regs.rsp ∧
    st.data.df = false ∧
    SysV.SavedRegs t st.data ∧
    (st.data.dmem =⋆ Eq (g.src.At g.dstPtr) ⋆ Eq (g.src.At g.srcPtr) ⋆ g.frame)
  refine eventually_trans _ (Q ⟨dst_ptr, src_ptr, dst, src, frame₀⟩) _ _ ?_ ?_
  · -- Prologue + loop reaching `done:`
    by_cases hn : n = 0
    · subst hn
      obtain rfl := List.eq_nil_of_length_eq_zero h_dst_len
      obtain rfl := List.eq_nil_of_length_eq_zero h_src_len
      sym => kstep 3; tactic =>
      rename_i v status
      have hv : v = 0 := by grind
      simp [hv]
      sym => kstep 0; tactic =>
      exact .done _ ⟨rfl, by grind, rfl, hdf, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, hmem₀⟩
    · sym => kstep 3; tactic =>
      rename_i v status
      have hzf : (v == BitVec.zero 64) = false := by grind
      simp only [hzf, Bool.false_eq_true, ↓reduceIte]
      sym => kstep 0; tactic =>
      refine tailrec_loop
        (step1 memcpy.toExecutable)
        (Q ⟨dst_ptr, src_ptr, dst, src, frame₀⟩)
        _
        (fun v (g : LoopGhost) st =>
          st.pc = memcpy.toExecutable.addrOf 4 ∧
          0 < v ∧
          st.data.regs.rdx.toNat = v ∧
          st.data.regs.rdi.toBitVec = g.dstPtr ∧
          st.data.regs.rsi.toBitVec = g.srcPtr ∧
          st.data.regs.rax.toBitVec = dst_ptr ∧
          st.data.regs.rsp = t.regs.rsp ∧
          st.data.df = false ∧
          SysV.SavedRegs t st.data ∧
          g.dst.length = v ∧
          g.src.length = v ∧
          (st.data.dmem =⋆ Eq (g.dst.At g.dstPtr) ⋆ Eq (g.src.At g.srcPtr) ⋆ g.frame))
        (fun _ => Q)
        (· < ·) Nat.lt_wfRel.wf
        n ⟨dst_ptr, src_ptr, dst, src, frame₀⟩
        ⟨rfl, Nat.pos_of_ne_zero hn,
          by grind, h_rdi, h_rsi, by grind, rfl, hdf, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩,
          h_dst_len, h_src_len, hmem₀⟩
        ?_ (fun _ h => h)
      -- Loop body: one byte copied per iteration
      rintro v ⟨dp, sp, dbs, sbs, frame⟩ ⟨s, pc⟩
        ⟨hpc, hv_pos, h_rdx_v, h_rdi_v, h_rsi_v, h_rax_v, h_rsp_v, h_df_v, h_saved, h_dl, h_sl, h_m⟩
      dsimp only at hpc h_rdx_v h_rdi_v h_rsi_v h_rax_v h_rsp_v h_df_v h_saved h_dl h_sl h_m
      subst hpc
      cases dbs with
      | nil => simp at h_dl; omega
      | cons d0 ds =>
        cases sbs with
        | nil => simp at h_sl; omega
        | cons b0 bs =>
          have h_lt64 : v < 2 ^ 64 := h_rdx_v ▸ s.regs.rdx.toNat_lt
          simp only [List.length_cons] at h_dl h_sl
          rw [sep_cons d0 ds dp (by omega), sep_cons b0 bs sp (by omega)] at h_m
          have h_m_src : s.dmem =⋆ Eq ([b0].At s.regs.rsi.toBitVec) ⋆
              (Eq ([d0].At dp) ⋆ Eq (ds.At (dp + 1#64)) ⋆ Eq (bs.At (sp + 1#64)) ⋆ frame) := by
            rw [h_rsi_v]; ecancel
          have h_m_dst : s.dmem =⋆ Eq ([d0].At s.regs.rdi.toBitVec) ⋆
              (Eq (ds.At (dp + 1#64)) ⋆ Eq ([b0].At sp) ⋆ Eq (bs.At (sp + 1#64)) ⋆ frame) := by
            rw [h_rdi_v]; ecancel
          refine eventually_weaken _ _ _ _ ?_ (memcpy_step s b0 d0 _ _ h_m_src h_m_dst)
          rintro st ⟨hpc', hrax', hrsp', hrsi', hrdi', hrdx', hdf', hsaved', hdmem'⟩
          have hdmem_sep : st.data.dmem =⋆
              Eq ([b0].At dp) ⋆ Eq (ds.At (dp + 1#64)) ⋆
              Eq ([b0].At sp) ⋆ Eq (bs.At (sp + 1#64)) ⋆ frame := by
            have hs := Mem.storeInt_sep s.regs.rdi.toBitVec 1 [d0]
              (Eq (ds.At (dp + 1#64)) ⋆ Eq ([b0].At sp) ⋆ Eq (bs.At (sp + 1#64)) ⋆ frame)
              s.dmem ⟨h_m_dst, rfl⟩ (BitVec.ofInt 8 (Int.ofBytes [b0])).toInt
            rw [← hdmem'] at hs
            rw [h_rdi_v, byte_roundtrip] at hs
            simpa only [sep_assoc] using hs
          have hsaved_t : SysV.SavedRegs t st.data :=
            ⟨hsaved'.1.trans h_saved.1, hsaved'.2.1.trans h_saved.2.1,
             hsaved'.2.2.1.trans h_saved.2.2.1, hsaved'.2.2.2.1.trans h_saved.2.2.2.1,
             hsaved'.2.2.2.2.1.trans h_saved.2.2.2.2.1, hsaved'.2.2.2.2.2.trans h_saved.2.2.2.2.2⟩
          by_cases hv1 : v = 1
          · subst hv1
            have hds_nil : ds = [] := List.eq_nil_of_length_eq_zero (by omega)
            have hbs_nil : bs = [] := List.eq_nil_of_length_eq_zero (by omega)
            subst hds_nil; subst hbs_nil
            have hzero : (s.regs.rdx.toBitVec - 1#64 == 0#64) = true := by
              simp only [beq_iff_eq]
              apply BitVec.eq_of_toNat_eq
              have : s.regs.rdx.toBitVec.toNat = 1 := h_rdx_v
              simp [BitVec.toNat_sub, this]
            simp only [hzero, ↓reduceIte] at hpc'
            refine .inl ⟨hpc', by rw [hrax', h_rax_v], by rw [hrsp', h_rsp_v],
              by rw [hdf', h_df_v], hsaved_t, ?_⟩
            dsimp only
            rw [sep_cons b0 [] dp (by decide), sep_cons b0 [] sp (by decide)]
            ecancel
          · have hnz : (s.regs.rdx.toBitVec - 1#64 == 0#64) = false := by
              simp only [beq_eq_false_iff_ne]
              intro heq
              have h1 : s.regs.rdx.toBitVec.toNat = v := h_rdx_v
              have h2 := congrArg BitVec.toNat heq
              simp [BitVec.toNat_sub, h1] at h2
              omega
            simp only [hnz, Bool.false_eq_true, ↓reduceIte] at hpc'
            refine .inr ⟨v - 1,
              ⟨dp + 1#64, sp + 1#64, ds, bs, Eq ([b0].At dp) ⋆ Eq ([b0].At sp) ⋆ frame⟩,
              ⟨hpc', by omega, ?_, ?_, ?_, by rw [hrax', h_rax_v], by rw [hrsp', h_rsp_v],
               by rw [hdf', h_df_v], hsaved_t, by dsimp; omega, by dsimp; omega, ?_⟩,
              by omega, ?_⟩
            · rw [hrdx']
              change (s.regs.rdx.toBitVec - 1#64).toNat = v - 1
              have h1 : s.regs.rdx.toBitVec.toNat = v := h_rdx_v
              simp [BitVec.toNat_sub, h1]; omega
            · change st.data.regs.rdi.toBitVec = dp + 1#64
              rw [hrdi', UInt64.toBitVec_add, h_rdi_v]; rfl
            · change st.data.regs.rsi.toBitVec = sp + 1#64
              rw [hrsi', UInt64.toBitVec_add, h_rsi_v]; rfl
            · dsimp only; ecancel
            · rintro t_s ⟨hQ_pc, hQ_rax, hQ_rsp, hQ_df, hQ_saved, hQ_mem⟩
              dsimp only [Q] at hQ_pc hQ_rax hQ_rsp hQ_df hQ_saved hQ_mem ⊢
              refine ⟨hQ_pc, hQ_rax, hQ_rsp, hQ_df, hQ_saved, ?_⟩
              rw [sep_cons b0 bs dp (by omega), sep_cons b0 bs sp (by omega)]
              ecancel
  · -- Epilogue: `done: ret`
    rintro ⟨s, pc⟩ ⟨hpc, h_rax, h_rsp, h_df, h_saved, h_m⟩
    dsimp only [Q] at hpc h_rax h_rsp h_df h_saved h_m
    subst hpc
    have h_ret : s.dmem =⋆ RetCell ra s.regs.rsp.toBitVec ⋆
        (Eq (src.At dst_ptr) ⋆ Eq (src.At src_ptr) ⋆ R) := by
      rw [h_rsp]; dsimp [frame₀] at h_m; ecancel
    sym => kstep; tactic =>
    refine .done _ ⟨?_, ⟨?_, h_df, h_saved, ?_⟩, h_rax⟩
    · rw [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, Int64.ofBitVec_toBitVec]
    · simp (config := { zetaDelta := true }) [h_rsp]
    · simp only [Owned.zero, emp_sep]
      rw [← h_rsp]
      exact Owned.intro h_ret (Int.toBytes_length _ _)

end Examples.Memcpy
