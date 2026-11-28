module

public import LeanQbe.T.Examples.Bitblast.Proof.OpsDivCpopHelpers
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import LeanQbe.T.Logic.ProofKit

set_option autoImplicit false

namespace LeanQbe.T.Examples.Bitblast.Proof.OpsDivCpop

open LeanQbe.T
open LeanQbe.T.Examples.Bitblast.Ref
open LeanQbe.T.Examples.Bitblast.Src.OpsDivCpop

section

attribute [local c0_load] c0_load_array32_u32 c0_load_array32_u32_add_mul
attribute [local c0_store] c0_store_array32_u32 c0_store_array32_u32_add_mul

/-! ## `bv_blast_ite_into` and `bv_blast_ite_slice` -/

private theorem bv_blast_ite_into_loop_wp (Γ : Env) (hΓ_ite : Γ.Has "bv_aig_ite" bvAigIteSpec)
    {h : Val i64} {cond t_off f_off out_off w : Val i32} {Q : Post [Ty.bool]} {X : XPost}
    {hdr : BVHdrState} {g : Aig} {aigWords : List (BitVec 64)}
    {htSlots litsPool : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64}
    (hinv : AigInv hdr g aigWords htSlots)
    (hlcap : hdr.lits_cap.toNat ≤ litsPool.length)
    (ho : hdr.oom = 0#32)
    (hlen_cap : hdr.lits_len.toNat ≤ hdr.lits_cap.toNat)
    (_hlptr : 0 < w.toNat → hdr.lits_ptr ≠ 0#64)
    (htw : t_off.toNat + w.toNat ≤ hdr.lits_len.toNat)
    (hfw : f_off.toNat + w.toNat ≤ hdr.lits_len.toNat)
    (how : out_off.toNat + w.toNat ≤ hdr.lits_len.toNat)
    (hcond_wf : 0 < w.toNat → (cond >>> 1).toNat < hdr.aig_len.toNat)
    (ht_wf : SliceLitsWf hdr litsPool t_off.toNat w.toNat)
    (hf_wf : SliceLitsWf hdr litsPool f_off.toNat w.toNat)
    (hdisj_t : DisjointSlice out_off.toNat w.toNat t_off.toNat w.toNat)
    (hdisj_f : DisjointSlice out_off.toNat w.toNat f_off.toNat w.toNat)
    (hm : (array (t := i32) hdr.lits_ptr litsPool ⋆
      (bvHdrMem h hdr ⋆ array64 hdr.aig_ptr aigWords ⋆
        array (t := i32) hdr.ht_ptr htSlots ⋆ R)) m)
    (hpost : ∀ ret hdr' g' aigWords' htSlots' litsPool' m',
      hdr.AigFrame hdr' → g ≤ g' → g'.nodes.size ≤ g.nodes.size + 3 * w.toNat →
      AigInv hdr' g' aigWords' htSlots' → litsPool'.length = litsPool.length →
      (∀ p, p < out_off.toNat ∨ out_off.toNat + w.toNat ≤ p →
        litsPool'.getD p 0#32 = litsPool.getD p 0#32) →
      (hdr.oom ≠ 0#32 → hdr'.oom ≠ 0#32) → (ret = true ↔ hdr'.oom = 0#32) →
      (hdr.oom = 0#32 → hdr.lits_len.toNat ≤ hdr.lits_cap.toNat →
        (0 < w.toNat → hdr.lits_ptr ≠ 0#64) →
        t_off.toNat + w.toNat ≤ hdr.lits_len.toNat →
        f_off.toNat + w.toNat ≤ hdr.lits_len.toNat →
        out_off.toNat + w.toNat ≤ hdr.lits_len.toNat →
        g.A + 1 + g.nodes.size + 3 * w.toNat ≤ hdr.aig_cap.toNat →
        g.nodes.size + 3 * w.toNat ≤ bvMaxGates → hdr'.oom = 0#32) →
      (ret = true → SliceLitsWf hdr' litsPool' out_off.toNat w.toNat ∧
        ∀ ρ, sliceVal g' ρ litsPool' out_off.toNat w.toNat =
          if g.evalLit ρ (UInt32.ofBitVec cond) then sliceVal g ρ litsPool t_off.toNat w.toNat
          else sliceVal g ρ litsPool f_off.toNat w.toNat) →
      (bvHdrMem h hdr' ⋆ array64 hdr'.aig_ptr aigWords' ⋆
        array (t := i32) hdr'.ht_ptr htSlots' ⋆
        array (t := i32) hdr'.lits_ptr litsPool' ⋆ R) m' →
      Q (ret, ⟨⟩) m') :
    wp Γ Q X
      (Expr.group
        (fun Js => Blocks.cons (fun p : Tup Val [i32] =>
          Expr.let_ (op2 (OpCode.cmp CmpOp.ult i32) (Arg.var p.fst) (Arg.var w)) fun p_1 =>
          Expr.jnz (Arg.var p_1.fst)
            (Expr.let_ (op2 (OpCode.add i32) (Arg.var t_off) (Arg.var p.fst)) fun p_2 =>
            Expr.let_ (op1 (OpCode.zext 32 64) (Arg.var p_2.fst)) fun p_3 =>
            Expr.let_ (op2 (OpCode.mul i64) (Arg.var p_3.fst) (Arg.imm 4#64)) fun p_4 =>
            Expr.let_ (op2 (OpCode.add i64) (Arg.var hdr.lits_ptr) (Arg.var p_4.fst)) fun p_5 =>
            Expr.load i32 (Arg.var p_5.fst) fun ld_1 =>
            Expr.let_ (op2 (OpCode.add i32) (Arg.var f_off) (Arg.var p.fst)) fun p_6 =>
            Expr.let_ (op1 (OpCode.zext 32 64) (Arg.var p_6.fst)) fun p_7 =>
            Expr.let_ (op2 (OpCode.mul i64) (Arg.var p_7.fst) (Arg.imm 4#64)) fun p_8 =>
            Expr.let_ (op2 (OpCode.add i64) (Arg.var hdr.lits_ptr) (Arg.var p_8.fst)) fun p_9 =>
            Expr.load i32 (Arg.var p_9.fst) fun ld_2 =>
            Expr.call (as := [i64, i32, i32, i32]) "bv_aig_ite"
              (Arg.var h, Arg.var cond, Arg.var ld_1, Arg.var ld_2, ())
              fun (p_10 : Tup Val [i32]) =>
            Expr.let_ (op2 (OpCode.add i64) (Arg.var h) (Arg.imm 120#64)) fun p_11 =>
            Expr.load i32 (Arg.var p_11.fst) fun ld_3 =>
            Expr.let_ (op2 (OpCode.cmp CmpOp.ne i32) (Arg.var ld_3) (Arg.imm 0#32)) fun p_12 =>
            Expr.jnz (Arg.var p_12.fst) (Expr.ret (Arg.imm false, ()))
              (Expr.let_ (op2 (OpCode.add i32) (Arg.var out_off) (Arg.var p.fst)) fun p_13 =>
              Expr.let_ (op1 (OpCode.zext 32 64) (Arg.var p_13.fst)) fun p_14 =>
              Expr.let_ (op2 (OpCode.mul i64) (Arg.var p_14.fst) (Arg.imm 4#64)) fun p_15 =>
              Expr.let_ (op2 (OpCode.add i64) (Arg.var hdr.lits_ptr) (Arg.var p_15.fst))
                fun p_16 =>
              Expr.store (Arg.var p_10.fst) (Arg.var p_16.fst)
                (Expr.let_ (op2 (OpCode.add i32) (Arg.var p.fst) (Arg.imm 1#32)) fun p_17 =>
                Expr.jump Js.fst (Arg.var p_17.fst, ()))))
            (Expr.ret (Arg.imm true, ())))
          Blocks.nil)
        (fun Js => Expr.jump Js.fst (Arg.imm 0#32, ()))) m := by
  refine ProofKit.c0_while_state
    (fun st : Nat × BVHdrState × Aig × List (BitVec 64) × List (BitVec 32) ×
        List (BitVec 32) => (BitVec.ofNat 32 st.1, ()))
    (fun st => w.toNat - st.1)
    (fun st m' =>
      hdr.AigFrame st.2.1 ∧ g ≤ st.2.2.1 ∧
      st.2.2.1.nodes.size ≤ g.nodes.size + 3 * st.1 ∧
      AigInv st.2.1 st.2.2.1 st.2.2.2.1 st.2.2.2.2.1 ∧
      st.2.2.2.2.2.length = litsPool.length ∧ st.1 ≤ w.toNat ∧ st.2.1.oom = 0#32 ∧
      (∀ p, p < out_off.toNat ∨ out_off.toNat + st.1 ≤ p →
        st.2.2.2.2.2.getD p 0#32 = litsPool.getD p 0#32) ∧
      (∀ k, k < st.1 →
        ((st.2.2.2.2.2.getD (out_off.toNat + k) 0#32) >>> 1).toNat < st.2.1.aig_len.toNat) ∧
      (∀ k, k < st.1 → ∀ ρ,
        st.2.2.1.evalLit ρ (UInt32.ofBitVec (st.2.2.2.2.2.getD (out_off.toNat + k) 0#32)) =
          if g.evalLit ρ (UInt32.ofBitVec cond) then
            g.evalLit ρ (UInt32.ofBitVec (litsPool.getD (t_off.toNat + k) 0#32))
          else g.evalLit ρ (UInt32.ofBitVec (litsPool.getD (f_off.toNat + k) 0#32))) ∧
      (array (t := i32) hdr.lits_ptr st.2.2.2.2.2 ⋆
        (bvHdrMem h st.2.1 ⋆ array64 st.2.1.aig_ptr st.2.2.2.1 ⋆
          array (t := i32) st.2.1.ht_ptr st.2.2.2.2.1 ⋆ R)) m') ?_ ?_
  · intro J2 hJ2
    exact hJ2 (0, hdr, g, aigWords, htSlots, litsPool) m
      ⟨Modifies.refl _ _, Aig.extends_rfl g, by dsimp; omega, hinv, rfl, by omega,
        ho, fun _ _ => rfl, fun _ hk => False.elim (Nat.not_lt_zero _ hk),
        fun _ hk => False.elim (Nat.not_lt_zero _ hk), hm⟩
  · intro J2 st m1 ⟨hf1, hg1, hsz1, hinv1, hlen1, hjle, hoom1, hagree1, hwf1, heval1, hm1⟩ hjind
    rcases st with ⟨j, hdr1, g1, aw1, ht1, lp1⟩
    dsimp only at hf1 hg1 hsz1 hinv1 hlen1 hjle hoom1 hagree1 hwf1 heval1 hm1 hjind ⊢
    have hmod_j : j % 2 ^ 32 = j := by
      rw [Nat.mod_eq_of_lt]; have := w.isLt; omega
    have hjn : (BitVec.ofNat 32 j).toNat = j := by rw [BitVec.toNat_ofNat]; exact hmod_j
    c0_hfast_nogrp
    c0_hsplit
    · have hjlt : j < w.toNat := by omega
      have ht_fit1 : t_off.toNat + (BitVec.ofNat 32 j).toNat < 2 ^ 32 := by
        have := hdr.lits_cap.isLt; omega
      have ht_fit2 : t_off.toNat + (BitVec.ofNat 32 j).toNat < lp1.length := by omega
      have hf_fit1 : f_off.toNat + (BitVec.ofNat 32 j).toNat < 2 ^ 32 := by
        have := hdr.lits_cap.isLt; omega
      have hf_fit2 : f_off.toNat + (BitVec.ofNat 32 j).toNat < lp1.length := by omega
      c0_hfast_nogrp
      c0_hcall hΓ_ite
      have haig_le : hdr.aig_len.toNat ≤ hdr1.aig_len.toNat := by
        have hA : g.A = g1.A := hg1.1
        have hsz := hg1.2.1
        rw [hinv.aig_len_eq, hinv1.aig_len_eq, hA]; omega
      have ht_lp1 : lp1.getD (t_off.toNat + j) 0#32 = litsPool.getD (t_off.toNat + j) 0#32 := by
        apply hagree1; unfold DisjointSlice at hdisj_t; omega
      have hf_lp1 : lp1.getD (f_off.toNat + j) 0#32 = litsPool.getD (f_off.toNat + j) 0#32 := by
        apply hagree1; unfold DisjointSlice at hdisj_f; omega
      have ht_idx : BitVec.toNat (BitVec.setWidth 64 (t_off + BitVec.ofNat 32 j)) =
          t_off.toNat + j := by
        have hsum : (t_off + BitVec.ofNat 32 j).toNat = t_off.toNat + j := by
          rw [BitVec.toNat_add, hjn, Nat.mod_eq_of_lt]; omega
        rw [BitVec.toNat_setWidth, hsum, Nat.mod_eq_of_lt]; omega
      have hf_idx : BitVec.toNat (BitVec.setWidth 64 (f_off + BitVec.ofNat 32 j)) =
          f_off.toNat + j := by
        have hsum : (f_off + BitVec.ofNat 32 j).toNat = f_off.toNat + j := by
          rw [BitVec.toNat_add, hjn, Nat.mod_eq_of_lt]; omega
        rw [BitVec.toNat_setWidth, hsum, Nat.mod_eq_of_lt]; omega
      have ht_get : lp1[BitVec.toNat (BitVec.setWidth 64 (t_off + BitVec.ofNat 32 j))]'(by
          omega) = litsPool.getD (t_off.toNat + j) 0#32 := by
        simp only [ht_idx]
        rw [list_getD_eq_getElem lp1 0#32 (by omega)]
        exact ht_lp1
      have hf_get : lp1[BitVec.toNat (BitVec.setWidth 64 (f_off + BitVec.ofNat 32 j))]'(by
          omega) = litsPool.getD (f_off.toNat + j) 0#32 := by
        simp only [hf_idx]
        rw [list_getD_eq_getElem lp1 0#32 (by omega)]
        exact hf_lp1
      have hm1_lits : (array (t := i32) hdr1.lits_ptr lp1 ⋆
          (bvHdrMem h hdr1 ⋆ array64 hdr1.aig_ptr aw1 ⋆
            array (t := i32) hdr1.ht_ptr ht1 ⋆ R)) m1 := by
        rw [hf1.lits_ptr]; exact hm1
      have hm1_aig := opMem_to_aig (opMem_of_lits hm1_lits)
      refine ⟨hdr1, g1, aw1, ht1, array (t := i32) hdr1.lits_ptr lp1 ⋆ R, hinv1, ?_, hm1_aig, ?_⟩
      · intro _
        refine ⟨Nat.lt_of_lt_of_le (hcond_wf (by omega)) haig_le, ?_, ?_⟩
        · rw [ht_get]; exact Nat.lt_of_lt_of_le (ht_wf.2 j hjlt) haig_le
        · rw [hf_get]; exact Nat.lt_of_lt_of_le (hf_wf.2 j hjlt) haig_le
      · intro ret hdr2 g2 aw2 ht2 m2 hf12 hg12 hsz12 hinv2 hne2 hoom2 hres2 hm2
        rw [← hf12.lits_ptr] at hm2
        have hm2_full := opMem_of_aig hm2
        have hm2_l := opMem_to_lits hm2_full
        have hm2' : (array (t := i32) hdr.lits_ptr lp1 ⋆
            (bvHdrMem h hdr2 ⋆ array64 hdr2.aig_ptr aw2 ⋆
              array (t := i32) hdr2.ht_ptr ht2 ⋆ R)) m2 := by
          rw [hf12.lits_ptr, hf1.lits_ptr] at hm2_l; exact hm2_l
        c0_hfast_nogrp
        c0_hsplit
        · have hne_oom : hdr2.oom ≠ 0#32 := by simpa [bv_c0_bne_false] using hc
          clear hc
          c0_hfast_nogrp
          exact hpost false hdr2 g2 aw2 ht2 lp1 m2 (hf1.trans hf12)
            (Aig.extends_trans hg1 hg12) (by omega) hinv2 hlen1
            (fun p hp => hagree1 p (by
              rcases hp with hp | hp
              · exact Or.inl hp
              · exact Or.inr (by omega)))
            (fun h => absurd ho h) (by simp [hne_oom])
            (fun _ _ _ _ _ _ ha hb => by
              exfalso
              have hle_cap2 : g1.A + 1 + g1.nodes.size + 3 ≤ hdr1.aig_cap.toNat := by
                rw [hf1.aig_cap, ← hinv1.num_atoms_eq, hf1.num_atoms, hinv.num_atoms_eq]
                omega
              have hle_gates2 : g1.nodes.size + 3 ≤ bvMaxGates := by omega
              exact hne_oom (hoom2 hoom1 hle_cap2 hle_gates2))
            (fun h => absurd h (by decide)) hm2_full
        · have ho2 : hdr2.oom = 0#32 := by simpa [bv_c0_bne_false] using hc
          clear hc
          rcases hres2 ho2 with ⟨hret_wf, hret_eval⟩
          have ho_fit1 : out_off.toNat + (BitVec.ofNat 32 j).toNat < 2 ^ 32 := by
            have := hdr.lits_cap.isLt; omega
          have ho_fit2 : out_off.toNat + (BitVec.ofNat 32 j).toNat < lp1.length := by omega
          c0_hfast_nogrp
          have hadd_j1 : BitVec.ofNat 32 j + 1#32 = BitVec.ofNat 32 (j + 1) := by
            apply BitVec.eq_of_toNat_eq
            have := w.isLt
            have hmod1 : (1#32 : BitVec 32).toNat = 1 := rfl
            rw [BitVec.toNat_add, hjn, hmod1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
            omega
          rw [hadd_j1]
          have ho_idx : (BitVec.setWidth 64 (out_off + BitVec.ofNat 32 j)).toNat =
              out_off.toNat + (BitVec.ofNat 32 j).toNat := by
            rw [BitVec.toNat_setWidth,
              Nat.mod_eq_of_lt (by have := (out_off + BitVec.ofNat 32 j).isLt; omega)]
            rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
          rw [ho_idx] at hm
          let lp2 := lp1.set (out_off.toNat + (BitVec.ofNat 32 j).toNat) ret
          have hm2'' : (array (t := i32) hdr.lits_ptr lp2 ⋆
              (bvHdrMem h hdr2 ⋆ array64 hdr2.aig_ptr aw2 ⋆
                array (t := i32) hdr2.ht_ptr ht2 ⋆ R)) m := by
            exact hm
          refine hjind (j + 1, hdr2, g2, aw2, ht2, lp2) m (by omega) ?_
          have hg2 : g ≤ g2 := Aig.extends_trans hg1 hg12
          have hf2 : hdr.AigFrame hdr2 := hf1.trans hf12
          have haig12 : hdr1.aig_len.toNat ≤ hdr2.aig_len.toNat := by
            have hA12 : g1.A = g2.A := hg12.1
            have hsz12' := hg12.2.1
            rw [hinv1.aig_len_eq, hinv2.aig_len_eq, hA12]; omega
          refine ⟨hf2, hg2, by dsimp only; omega, hinv2, by simp [lp2, hlen1],
            by omega, ho2, ?_, ?_, ?_, hm2''⟩
          · intro p hp
            have hne_idx : p ≠ out_off.toNat + (BitVec.ofNat 32 j).toNat := by omega
            dsimp only [lp2]
            rw [list_getD_set_ne lp1 0#32 ret hne_idx]
            exact hagree1 p (by
              rcases hp with hp | hp
              · exact Or.inl hp
              · exact Or.inr (by omega))
          · intro k hk
            by_cases hkj : k = j
            · subst hkj
              dsimp only [lp2]
              simp only [hjn]
              rw [list_getD_set_self lp1 0#32 ret (by omega)]
              exact hret_wf
            · have hklt : k < j := by omega
              have hne_idx : out_off.toNat + k ≠ out_off.toNat + (BitVec.ofNat 32 j).toNat := by
                omega
              dsimp only [lp2]
              rw [list_getD_set_ne lp1 0#32 ret hne_idx]
              exact Nat.lt_of_lt_of_le (hwf1 k hklt) haig12
          · intro k hk ρ
            by_cases hkj : k = j
            · subst hkj
              dsimp only [lp2]
              simp only [hjn]
              rw [list_getD_set_self lp1 0#32 ret (by omega)]
              rw [hret_eval ρ]
              have hcond_lt : (UInt32.ofBitVec cond).toNat < 2 * (g.A + 1 + g.nodes.size) := by
                have hlt := hcond_wf (by omega)
                rw [hinv.aig_len_eq, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] at hlt
                simp only [UInt32.toNat] at hlt ⊢
                omega
              have ht_lt2 : (UInt32.ofBitVec (litsPool.getD (t_off.toNat + k) 0#32)).toNat <
                  2 * (g.A + 1 + g.nodes.size) := by
                have hlt := ht_wf.2 k hjlt
                rw [hinv.aig_len_eq, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] at hlt
                simp only [UInt32.toNat] at hlt ⊢
                omega
              have hf_lt2 : (UInt32.ofBitVec (litsPool.getD (f_off.toNat + k) 0#32)).toNat <
                  2 * (g.A + 1 + g.nodes.size) := by
                have hlt := hf_wf.2 k hjlt
                rw [hinv.aig_len_eq, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] at hlt
                simp only [UInt32.toNat] at hlt ⊢
                omega
              rw [Aig.evalLit_extend hg1 hcond_lt]
              have hgt : g1.evalLit ρ (UInt32.ofBitVec
                  (lp1[BitVec.toNat (BitVec.setWidth 64 (t_off + BitVec.ofNat 32 k))]'(by
                    omega))) = g.evalLit ρ
                      (UInt32.ofBitVec (litsPool.getD (t_off.toNat + k) 0#32)) := by
                rw [ht_get]; exact Aig.evalLit_extend hg1 ht_lt2
              have hgf : g1.evalLit ρ (UInt32.ofBitVec
                  (lp1[BitVec.toNat (BitVec.setWidth 64 (f_off + BitVec.ofNat 32 k))]'(by
                    omega))) = g.evalLit ρ
                      (UInt32.ofBitVec (litsPool.getD (f_off.toNat + k) 0#32)) := by
                rw [hf_get]; exact Aig.evalLit_extend hg1 hf_lt2
              rw [hgt, hgf]
              cases g.evalLit ρ (UInt32.ofBitVec cond) <;> rfl
            · have hklt : k < j := by omega
              have hne_idx : out_off.toNat + k ≠ out_off.toNat + (BitVec.ofNat 32 j).toNat := by
                omega
              dsimp only [lp2]
              rw [list_getD_set_ne lp1 0#32 ret hne_idx]
              have hlt1 : (UInt32.ofBitVec (lp1.getD (out_off.toNat + k) 0#32)).toNat <
                  2 * (g1.A + 1 + g1.nodes.size) := by
                have hlt := hwf1 k hklt
                rw [hinv1.aig_len_eq, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] at hlt
                simp only [UInt32.toNat] at hlt ⊢
                omega
              rw [Aig.evalLit_extend hg12 hlt1]
              exact heval1 k hklt ρ
    · have hjge : j = w.toNat := by omega
      clear hc
      c0_hfast_nogrp
      subst hjge
      rw [← hf1.lits_ptr] at hm1
      exact hpost true hdr1 g1 aw1 ht1 lp1 m1 hf1 hg1 hsz1 hinv1 hlen1 hagree1
        (fun hne => absurd ho hne) (by simp [hoom1]) (fun _ _ _ _ _ _ _ _ => hoom1)
        (fun _ => ⟨⟨by rw [hf1.lits_len]; exact how, hwf1⟩, fun ρ => by
          apply BitVec.eq_of_getLsbD_eq
          intro i hi
          rw [sliceVal_getLsbD hi, heval1 i hi]
          cases hcond : g.evalLit ρ (UInt32.ofBitVec cond)
          · simp [sliceVal_getLsbD hi]
          · simp [sliceVal_getLsbD hi]⟩)
        (opMem_of_lits hm1)

public theorem bv_blast_ite_into_wp (Γ : Env) (hΓ_ok : Γ.Has "bv_slice_ok" bvSliceOkSpec)
    (hΓ_ite : Γ.Has "bv_aig_ite" bvAigIteSpec) :
    bvBlastIteIntoSpec.Le (Func.wp Γ bv_blast_ite_into_body) := by
  intro ⟨h, cond, t_off, f_off, out_off, w, ⟨⟩⟩ m Q X
  rintro ⟨hdr, g, aigWords, htSlots, litsPool, R, hinv, hlcap, hpre, hmem, hpost⟩
  dsimp [Func.wp, bv_blast_ite_into_body]
  refine wp_join_state (fun _ : Unit => ()) (fun _ m' =>
    m' = m ∧ (hdr.oom ≠ 0#32 ∨ ¬(hdr.lits_len.toNat ≤ hdr.lits_cap.toNat ∧
      (0 < w.toNat → hdr.lits_ptr ≠ 0#64) ∧
      t_off.toNat + w.toNat ≤ hdr.lits_len.toNat ∧
      f_off.toNat + w.toNat ≤ hdr.lits_len.toNat ∧
      out_off.toNat + w.toNat ≤ hdr.lits_len.toNat))) ?_ ?_
  · intro J _ m' ⟨hm_eq, hfail⟩
    subst hm_eq
    c0_hfast_nogrp
    have hm1 := opMem_of_hdr_emp (by assumption)
    exact hpost false { hdr with oom := 1#32 } g aigWords htSlots litsPool _
      hdr_with_oom_aigFrame (Aig.extends_rfl g) (by omega) (aigInv_set_oom 1#32 hinv)
      rfl (fun _ _ => rfl) (fun _ => by simp) (by simp)
      (fun h0 hlcap0 hlptr ht hf ho _ _ => by
        exfalso; rcases hfail with hne | hbad
        · exact hne h0
        · exact hbad ⟨hlcap0, hlptr, ht, hf, ho⟩)
      (fun h => absurd h (by decide)) hm1
  · intro J hJ
    c0_hfast_nogrp
    c0_hsplit
    · have hne : hdr.oom ≠ 0#32 := by simpa [bv_c0_bne_false] using hc
      c0_hfast_nogrp
      exact hJ () m ⟨rfl, Or.inl hne⟩
    · have ho : hdr.oom = 0#32 := by simpa [bv_c0_bne_false] using hc
      clear hc
      c0_hcall hΓ_ok
      refine ⟨hdr, _, opMem_to_hdr hmem, ?_⟩
      dsimp only
      c0_hsplit
      · have hok_t := hc; clear hc
        c0_hcall hΓ_ok
        refine ⟨hdr, _, opMem_to_hdr hmem, ?_⟩
        dsimp only
        c0_hsplit
        · have hok_f := hc; clear hc
          c0_hcall hΓ_ok
          refine ⟨hdr, _, opMem_to_hdr hmem, ?_⟩
          dsimp only
          c0_hsplit
          · have hok_o := hc; clear hc
            have htw : t_off.toNat + w.toNat ≤ hdr.lits_len.toNat := by omega
            have hfw : f_off.toNat + w.toNat ≤ hdr.lits_len.toNat := by omega
            have how : out_off.toNat + w.toNat ≤ hdr.lits_len.toNat := by omega
            rcases hpre ho hok_t.1 hok_t.2.1 htw hfw how with
              ⟨hcond_wf, ht_wf, hf_wf, hdisj_t, hdisj_f⟩
            c0_hfast_nogrp
            exact bv_blast_ite_into_loop_wp Γ hΓ_ite hinv hlcap ho hok_t.1 hok_t.2.1
              htw hfw how hcond_wf ht_wf hf_wf hdisj_t hdisj_f (opMem_to_lits hmem) hpost
          · have hbad := hc; clear hc; c0_hfast_nogrp
            exact hJ () m ⟨rfl, Or.inr fun ⟨h1, h2, h3, h4, h5⟩ =>
              hbad ⟨h1, h2, by omega, by omega⟩⟩
        · have hbad := hc; clear hc; c0_hfast_nogrp
          exact hJ () m ⟨rfl, Or.inr fun ⟨h1, h2, h3, h4, h5⟩ =>
            hbad ⟨h1, h2, by omega, by omega⟩⟩
      · have hbad := hc; clear hc; c0_hfast_nogrp
        exact hJ () m ⟨rfl, Or.inr fun ⟨h1, h2, h3, h4, h5⟩ =>
          hbad ⟨h1, h2, by omega, by omega⟩⟩

public theorem bv_blast_ite_slice_wp (Γ : Env) (hΓ_ok : Γ.Has "bv_slice_ok" bvSliceOkSpec)
    (hΓ_mark : Γ.Has "bv_lits_mark" bvLitsMarkSpec)
    (hΓ_rel : Γ.Has "bv_lits_release" bvLitsReleaseSpec)
    (hΓ_alloc : Γ.Has "bv_lits_alloc" bvLitsAllocSpec)
    (hΓ_into : Γ.Has "bv_blast_ite_into" bvBlastIteIntoSpec) :
    bvBlastIteSliceSpec.Le (Func.wp Γ bv_blast_ite_slice_body) := by
  intro ⟨h, cond, t_off, f_off, w, ⟨⟩⟩ m Q X
  rintro ⟨hdr, g, aigWords, htSlots, litsPool, R, hinv, hlcap, hpre, hmem, hpost⟩
  dsimp [Func.wp, bv_blast_ite_slice_body]
  refine wp_join_state (fun _ : Unit => ()) (fun _ m' =>
    m' = m ∧ (hdr.oom ≠ 0#32 ∨ ¬(hdr.lits_len.toNat ≤ hdr.lits_cap.toNat ∧
      (0 < w.toNat → hdr.lits_ptr ≠ 0#64) ∧
      t_off.toNat + w.toNat ≤ hdr.lits_len.toNat ∧
      f_off.toNat + w.toNat ≤ hdr.lits_len.toNat))) ?_ ?_
  · intro J _ m' ⟨hm_eq, hfail⟩
    subst hm_eq
    c0_hfast_nogrp
    have hm1 := opMem_of_hdr_emp (by assumption)
    exact hpost 0xFFFFFFFF#32 { hdr with oom := 1#32 } g aigWords htSlots litsPool _
      (Modifies.set_oom _ hdr 1#32) (Aig.extends_rfl g) (by omega)
      (aigInv_set_oom 1#32 hinv) rfl (fun _ _ => rfl) (fun _ => by simp)
      (fun h0 hlcap0 hlptr ht hf _ _ _ => by
        exfalso; rcases hfail with hne | hbad
        · exact hne h0
        · exact hbad ⟨hlcap0, hlptr, ht, hf⟩)
      (fun _ => ⟨rfl, rfl⟩) (fun h => absurd h (by simp)) hm1
  · intro J hJ
    c0_hfast_nogrp
    c0_hsplit
    · have hne : hdr.oom ≠ 0#32 := by simpa [bv_c0_bne_false] using hc
      c0_hfast_nogrp
      exact hJ () m ⟨rfl, Or.inl hne⟩
    · have ho : hdr.oom = 0#32 := by simpa [bv_c0_bne_false] using hc
      clear hc
      c0_hcall hΓ_ok
      refine ⟨hdr, _, opMem_to_hdr hmem, ?_⟩
      dsimp only
      c0_hsplit
      · have hok_t := hc; clear hc
        c0_hcall hΓ_ok
        refine ⟨hdr, _, opMem_to_hdr hmem, ?_⟩
        dsimp only
        c0_hsplit
        · have hok_f := hc; clear hc
          have htw : t_off.toNat + w.toNat ≤ hdr.lits_len.toNat := by omega
          have hfw : f_off.toNat + w.toNat ≤ hdr.lits_len.toNat := by omega
          rcases hpre ho hok_t.1 hok_t.2.1 htw hfw with ⟨hcond_wf, ht_wf, hf_wf⟩
          c0_hcall hΓ_mark
          refine ⟨hdr, _, opMem_to_hdr hmem, ?_⟩
          c0_hcall hΓ_alloc
          refine ⟨hdr, _, opMem_to_hdr hmem, ?_⟩
          dsimp only
          by_cases hroom : w.toNat ≤ hdr.lits_cap.toNat - hdr.lits_len.toNat
          · simp only [ho, hok_t.1, hroom, and_self, ↓reduceIte]
            intro m1 hm1
            let hdr1 := { hdr with lits_len := hdr.lits_len + w, oom := 0#32 }
            have hf1 : hdr.DcBlastFrame hdr1 :=
              Modifies.set_lits_len_oom _ hdr (hdr.lits_len + w) 0#32
            have hinv1 : AigInv hdr1 g aigWords htSlots :=
              aigInv_blastFrame hinv hf1 rfl
            have hlen1 : hdr1.lits_len.toNat = hdr.lits_len.toNat + w.toNat := by
              change (hdr.lits_len + w).toNat = hdr.lits_len.toNat + w.toNat
              rw [BitVec.toNat_add, Nat.mod_eq_of_lt]; have := hdr.lits_cap.isLt; omega
            have hlcap1 : hdr1.lits_len.toNat ≤ hdr1.lits_cap.toNat := by
              change hdr1.lits_len.toNat ≤ hdr.lits_cap.toNat; omega
            c0_hfast_nogrp
            c0_hsplit
            · exfalso; simp at hc
            · clear hc
              c0_hcall hΓ_into
              have hdisj_t : DisjointSlice hdr.lits_len.toNat w.toNat t_off.toNat w.toNat :=
                Or.inr htw
              have hdisj_f : DisjointSlice hdr.lits_len.toNat w.toNat f_off.toNat w.toNat :=
                Or.inr hfw
              have hm1' := opMem_of_hdr hm1
              refine ⟨hdr1, g, aigWords, htSlots, litsPool, R, hinv1, hlcap, ?_, hm1', ?_⟩
              · intro _ _ _ _ _ _
                exact ⟨hcond_wf, sliceLitsWf_mono ht_wf (Nat.le_refl _) (by omega)
                    (fun _ _ _ => rfl),
                  sliceLitsWf_mono hf_wf (Nat.le_refl _) (by omega) (fun _ _ _ => rfl),
                  hdisj_t, hdisj_f⟩
              · intro ret hdr2 g2 aw2 ht2 lp2 m2 hf12 hg12 hsz12 hinv2 hlp2 hagree2 hne2
                  hret2 hoom2 hres2 hm2
                have hf2 : hdr.DcBlastFrame hdr2 := hf1.trans hf12.mono
                have hagree_old : ∀ p, p < hdr.lits_len.toNat →
                    lp2.getD p 0#32 = litsPool.getD p 0#32 :=
                  fun p hp => hagree2 p (Or.inl hp)
                c0_hsplit
                · have ho2 : hdr2.oom = 0#32 := hret2.mp hc
                  c0_hfast_nogrp
                  rcases hres2 hc with ⟨hwf2, hval2⟩
                  exact hpost hdr.lits_len hdr2 g2 aw2 ht2 lp2 m2 hf2 hg12 hsz12 hinv2 hlp2
                    hagree_old (fun h => absurd ho h) (fun _ _ _ _ _ _ _ _ => ho2)
                    (fun h => absurd ho2 h)
                    (fun _ => ⟨rfl, hf12.lits_len,
                      by rw [hf12.lits_len, hf12.lits_cap]; exact hlcap1,
                      hwf2, hval2⟩) hm2
                · have hne_oom : hdr2.oom ≠ 0#32 := fun hz => by
                    have := hret2.mpr hz
                    simp [hc] at this
                  clear hc
                  c0_hcall hΓ_rel
                  refine ⟨hdr2, _, opMem_to_hdr hm2, ?_⟩
                  have hmark_le : hdr.lits_len.toNat ≤ hdr2.lits_len.toNat := by
                    rw [hf12.lits_len]; omega
                  simp only [hmark_le, ↓reduceIte]
                  intro m3 hm3
                  c0_hfast_nogrp
                  let hdr3 := { hdr2 with lits_len := hdr.lits_len }
                  have hf3 : hdr.DcBlastFrame hdr3 := hf2.with_lits_len hdr.lits_len
                  have hinv3 : AigInv hdr3 g2 aw2 ht2 := aigInv_set_litsLen _ hinv2
                  exact hpost 0xFFFFFFFF#32 hdr3 g2 aw2 ht2 lp2 m3 hf3 hg12 hsz12 hinv3 hlp2
                    hagree_old (fun h => absurd ho h)
                    (fun _ _ _ _ _ _ ha hb => by
                      exfalso
                      have ho_false : hdr2.oom = 0#32 := by
                        apply hoom2 (by simp [hdr1]) hlcap1
                          (by rw [hf1.lits_ptr]; exact hok_t.2.1)
                          (by omega) (by omega) (by omega)
                        · rw [hf1.aig_cap]; exact ha
                        · exact hb
                      exact hne_oom ho_false)
                    (fun _ => ⟨rfl, rfl⟩) (fun h => absurd h hne_oom) (opMem_of_hdr hm3)
          · simp only [ho, hok_t.1, hroom, ne_eq, not_true_eq_false, ↓reduceIte]
            intro m1 hm1
            c0_hfast_nogrp
            c0_hsplit
            · clear hc
              c0_hfast_nogrp
              let hdr1 := { hdr with oom := 1#32 }
              have hm1' := opMem_of_hdr hm1
              exact hpost 0xFFFFFFFF#32 hdr1 g aigWords htSlots litsPool m1
                (Modifies.set_oom _ hdr 1#32) (Aig.extends_rfl g) (by omega)
                (aigInv_set_oom 1#32 hinv) rfl (fun _ _ => rfl) (fun _ => by simp [hdr1])
                (fun _ _ _ _ _ hw_fit _ _ => False.elim (hroom hw_fit))
                (fun _ => ⟨rfl, rfl⟩) (fun h => absurd h (by simp [hdr1])) hm1'
            · exfalso; simp at hc
        · have hbad := hc; clear hc; c0_hfast_nogrp
          exact hJ () m ⟨rfl, Or.inr fun ⟨h1, h2, h3, h4⟩ =>
            hbad ⟨h1, h2, by omega, by omega⟩⟩
      · have hbad := hc; clear hc; c0_hfast_nogrp
        exact hJ () m ⟨rfl, Or.inr fun ⟨h1, h2, h3, h4⟩ =>
          hbad ⟨h1, h2, by omega, by omega⟩⟩

/-! ## Shared AIG helpers and `bv_blast_sub_with_borrow` -/

public theorem lit_toNat_lt_of_shift {v : BitVec 32} {n : Nat} (h : (v >>> 1).toNat < n) :
    (UInt32.ofBitVec v).toNat < 2 * n := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] at h
  simp only [UInt32.toNat] at h ⊢
  omega

public theorem aigLit_xor_one_shift (l : BitVec 32) : (l ^^^ 1#32) >>> 1 = l >>> 1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have h1 : (1#32 : BitVec 32).getLsbD (1 + i) = false := by
    have hpow : 1 < 2 ^ (1 + i) := Nat.lt_of_lt_of_le (by omega) (Nat.le_self_pow (by omega) 2)
    have htb : Nat.testBit 1 (1 + i) = false := by
      simp [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt hpow]
    rw [BitVec.getLsbD_ofNat]; simp [htb]
  rw [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_xor, h1]
  simp

public theorem evalLit_zero (g : Aig) (ρ : Nat → Bool) :
    g.evalLit ρ (UInt32.ofBitVec 0#32) = false := by
  simp [Aig.evalLit, Aig.evalNode_zero]

public theorem evalLit_one (g : Aig) (ρ : Nat → Bool) :
    g.evalLit ρ (UInt32.ofBitVec 1#32) = true := by
  simp only [Aig.evalLit]
  have hsh : (UInt32.ofBitVec 1#32 >>> 1).toNat = 0 := rfl
  have hand : ((UInt32.ofBitVec 1#32 &&& 1) != 0) = true := rfl
  rw [hsh, hand, Aig.evalNode_zero]
  rfl

public theorem evalLit_xor_one (g : Aig) (ρ : Nat → Bool) (l : BitVec 32) :
    g.evalLit ρ (UInt32.ofBitVec (l ^^^ 1#32)) = !(g.evalLit ρ (UInt32.ofBitVec l)) := by
  have hsh : (UInt32.ofBitVec (l ^^^ 1#32) >>> 1).toNat = (UInt32.ofBitVec l >>> 1).toNat := by
    change ((l ^^^ 1#32) >>> 1).toNat = (l >>> 1).toNat
    rw [aigLit_xor_one_shift]
  have hbit : ((UInt32.ofBitVec (l ^^^ 1#32) &&& 1) != 0) =
      !((UInt32.ofBitVec l &&& 1) != 0) := by
    cases h0 : l.getLsbD 0
    · have hl : l &&& 1#32 = 0#32 := by
        apply BitVec.eq_of_getLsbD_eq; intro i hi
        cases i with | zero => simpa using h0 | succ k => simp
      have hr : (l ^^^ 1#32) &&& 1#32 = 1#32 := by
        apply BitVec.eq_of_getLsbD_eq; intro i hi
        cases i with | zero => simpa using h0 | succ k => simp
      have hl' : UInt32.ofBitVec l &&& 1 = UInt32.ofBitVec 0#32 := congrArg UInt32.ofBitVec hl
      have hr' : UInt32.ofBitVec (l ^^^ 1#32) &&& 1 = UInt32.ofBitVec 1#32 :=
        congrArg UInt32.ofBitVec hr
      rw [hl', hr']; decide
    · have hl : l &&& 1#32 = 1#32 := by
        apply BitVec.eq_of_getLsbD_eq; intro i hi
        cases i with | zero => simpa using h0 | succ k => simp
      have hr : (l ^^^ 1#32) &&& 1#32 = 0#32 := by
        apply BitVec.eq_of_getLsbD_eq; intro i hi
        cases i with | zero => simpa using h0 | succ k => simp
      have hl' : UInt32.ofBitVec l &&& 1 = UInt32.ofBitVec 1#32 := congrArg UInt32.ofBitVec hl
      have hr' : UInt32.ofBitVec (l ^^^ 1#32) &&& 1 = UInt32.ofBitVec 0#32 :=
        congrArg UInt32.ofBitVec hr
      rw [hl', hr']; decide
  simp only [Aig.evalLit, hsh, hbit]
  cases g.evalNode ρ (UInt32.ofBitVec l >>> 1).toNat <;>
    cases ((UInt32.ofBitVec l &&& 1) != 0) <;> rfl

public theorem aigBinOom_wp {rs : List Ty} (Γ : Env) {fn : String}
    {op : Bool → Bool → Bool} {maxNew : Nat} (hΓ : Γ.Has fn (bvAigBinSpec op maxNew))
    {h : Val i64} {lhs rhs : Val i32}
    {cont : Tup Val [i32] → Expr Val Cont rs} {failExpr : Expr Val Cont rs}
    {Q : Post rs} {X : XPost}
    {hdr : BVHdrState} {g : Aig} {aigWords : List (BitVec 64)}
    {htSlots litsPool : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64}
    (hinv : AigInv hdr g aigWords htSlots)
    (ho : hdr.oom = 0#32)
    (hlhs : (lhs >>> 1).toNat < hdr.aig_len.toNat)
    (hrhs : (rhs >>> 1).toNat < hdr.aig_len.toNat)
    (hm : (bvHdrMem h hdr ⋆ array64 hdr.aig_ptr aigWords ⋆
      array (t := i32) hdr.ht_ptr htSlots ⋆ array (t := i32) hdr.lits_ptr litsPool ⋆ R) m)
    (hfail : ∀ hdr' g' aw' ht' m',
      hdr.AigFrame hdr' → g ≤ g' → g'.nodes.size ≤ g.nodes.size + maxNew →
      AigInv hdr' g' aw' ht' → hdr'.oom ≠ 0#32 →
      (g.A + 1 + g.nodes.size + maxNew ≤ hdr.aig_cap.toNat →
        g.nodes.size + maxNew ≤ bvMaxGates → False) →
      (bvHdrMem h hdr' ⋆ array64 hdr'.aig_ptr aw' ⋆
        array (t := i32) hdr'.ht_ptr ht' ⋆ array (t := i32) hdr'.lits_ptr litsPool ⋆ R) m' →
      wp Γ Q X failExpr m')
    (hsucc : ∀ (ret : BitVec 32) hdr' g' aw' ht' m',
      hdr.AigFrame hdr' → g ≤ g' → g'.nodes.size ≤ g.nodes.size + maxNew →
      AigInv hdr' g' aw' ht' → hdr'.oom = 0#32 →
      (ret >>> 1).toNat < hdr'.aig_len.toNat →
      (∀ ρ, g'.evalLit ρ (UInt32.ofBitVec ret) =
        op (g.evalLit ρ (UInt32.ofBitVec lhs)) (g.evalLit ρ (UInt32.ofBitVec rhs))) →
      (bvHdrMem h hdr' ⋆ array64 hdr'.aig_ptr aw' ⋆
        array (t := i32) hdr'.ht_ptr ht' ⋆ array (t := i32) hdr'.lits_ptr litsPool ⋆ R) m' →
      wp Γ Q X (cont (ret, ⟨⟩)) m') :
    wp Γ Q X
      (Expr.call (as := [i64, i32, i32]) fn (Arg.var h, Arg.var lhs, Arg.var rhs, ())
        fun (p : Tup Val [i32]) =>
        Expr.let_ (op2 (OpCode.add i64) (Arg.var h) (Arg.imm 120#64)) fun p1 =>
        Expr.load i32 (Arg.var p1.fst) fun ld =>
        Expr.let_ (op2 (OpCode.cmp CmpOp.ne i32 Ty.bool (by decide))
          (Arg.var ld) (Arg.imm 0#32)) fun p2 =>
        Expr.jnz (Arg.var p2.fst) failExpr (cont p)) m := by
  c0_hcall hΓ
  refine ⟨hdr, g, aigWords, htSlots, array (t := i32) hdr.lits_ptr litsPool ⋆ R,
    hinv, fun _ => ⟨hlhs, hrhs⟩, opMem_to_aig hm, ?_⟩
  intro ret hdr' g' aw' ht' m' hf' hg' hsz' hinv' _ hoom' hres' hm'
  rw [← hf'.lits_ptr] at hm'
  have hm'' := opMem_of_aig hm'
  c0_hfast_nogrp
  c0_hsplit
  · have hne : hdr'.oom ≠ 0#32 := by simpa [bv_c0_bne_false] using hc
    clear hc
    exact hfail hdr' g' aw' ht' m' hf' hg' hsz' hinv' hne
      (fun ha hb => hne (hoom' ho ha hb)) hm''
  · have ho' : hdr'.oom = 0#32 := by simpa [bv_c0_bne_false] using hc
    clear hc
    rcases hres' ho' with ⟨hwf, heval⟩
    exact hsucc ret hdr' g' aw' ht' m' hf' hg' hsz' hinv' ho' hwf heval hm''

private theorem bv_sub_oom_ret0_wp {Γ : Env} {h : Val i64} {a_off b_off out_off w : Val i32}
    {Q : Post [i32]} {X : XPost} {hdr hdr_prev hdr' : BVHdrState} {g g_prev g' : Aig}
    {aw' : List (BitVec 64)} {ht' lp1 litsPool : List (BitVec 32)}
    {R : Mem 64 → Prop} {m' : Mem 64} {j stepGates : Nat}
    (ho : hdr.oom = 0#32)
    (hf_prev : hdr.AigFrame hdr_prev)
    (hg_prev : g ≤ g_prev)
    (hsz_prev : g_prev.nodes.size + stepGates ≤ g.nodes.size + 9 * w.toNat)
    (hf' : hdr.AigFrame hdr')
    (hg' : g ≤ g')
    (hsz' : g'.nodes.size ≤ g.nodes.size + 9 * w.toNat)
    (hinv' : AigInv hdr' g' aw' ht')
    (hlen1 : lp1.length = litsPool.length)
    (hagree1 : ∀ p, p < out_off.toNat ∨ out_off.toNat + j ≤ p →
      lp1.getD p 0#32 = litsPool.getD p 0#32)
    (hjw : j ≤ w.toNat)
    (hoom' : hdr'.oom ≠ 0#32)
    (hnofit : g_prev.A + 1 + g_prev.nodes.size + stepGates ≤ hdr_prev.aig_cap.toNat →
      g_prev.nodes.size + stepGates ≤ bvMaxGates → False)
    (hm' : (bvHdrMem h hdr' ⋆ array64 hdr'.aig_ptr aw' ⋆
      array (t := i32) hdr'.ht_ptr ht' ⋆ array (t := i32) hdr'.lits_ptr lp1 ⋆ R) m')
    (hpost : ∀ ret hdr'' g'' aw'' ht'' lp'' m'',
      hdr.AigFrame hdr'' → g ≤ g'' → g''.nodes.size ≤ g.nodes.size + 9 * w.toNat →
      AigInv hdr'' g'' aw'' ht'' → lp''.length = litsPool.length →
      (∀ p, p < out_off.toNat ∨ out_off.toNat + w.toNat ≤ p →
        lp''.getD p 0#32 = litsPool.getD p 0#32) →
      (hdr.oom ≠ 0#32 → hdr''.oom ≠ 0#32) →
      (hdr.oom = 0#32 → hdr.lits_len.toNat ≤ hdr.lits_cap.toNat →
        (0 < w.toNat → hdr.lits_ptr ≠ 0#64) →
        a_off.toNat + w.toNat ≤ hdr.lits_len.toNat →
        b_off.toNat + w.toNat ≤ hdr.lits_len.toNat →
        out_off.toNat + w.toNat ≤ hdr.lits_len.toNat →
        g.A + 1 + g.nodes.size + 9 * w.toNat ≤ hdr.aig_cap.toNat →
        g.nodes.size + 9 * w.toNat ≤ bvMaxGates → hdr''.oom = 0#32) →
      (hdr''.oom ≠ 0#32 → ret = 0#32) →
      (hdr''.oom = 0#32 →
        SliceLitsWf hdr'' lp'' out_off.toNat w.toNat ∧
        (ret >>> 1).toNat < hdr''.aig_len.toNat ∧
        ∀ ρ, sliceVal g'' ρ lp'' out_off.toNat w.toNat =
          sliceVal g ρ litsPool a_off.toNat w.toNat -
            sliceVal g ρ litsPool b_off.toNat w.toNat ∧
          g''.evalLit ρ (UInt32.ofBitVec ret) =
            (sliceVal g ρ litsPool a_off.toNat w.toNat).ult
              (sliceVal g ρ litsPool b_off.toNat w.toNat)) →
      (bvHdrMem h hdr'' ⋆ array64 hdr''.aig_ptr aw'' ⋆
        array (t := i32) hdr''.ht_ptr ht'' ⋆ array (t := i32) hdr''.lits_ptr lp'' ⋆ R) m'' →
      Q (ret, ⟨⟩) m'') :
    wp Γ Q X (Expr.ret (Arg.imm 0#32, ())) m' := by
  c0_hfast_nogrp
  exact hpost 0#32 hdr' g' aw' ht' lp1 m' hf' hg' hsz' hinv' hlen1
    (fun p hp => hagree1 p (by
      rcases hp with hp | hp
      · exact Or.inl hp
      · exact Or.inr (by omega)))
    (fun hne => absurd ho hne)
    (fun _ _ _ _ _ _ ha hb => by
      exfalso
      apply hnofit
      · have hA : g.A = g_prev.A := hg_prev.1
        rw [hf_prev.aig_cap, ← hA]
        omega
      · omega)
    (fun _ => rfl) (fun hz => absurd hz hoom') hm'

public theorem bv_blast_sub_with_borrow_wp (Γ : Env)
    (hΓ_ok : Γ.Has "bv_slice_ok" bvSliceOkSpec)
    (hΓ_not : Γ.Has "bv_aig_not" bvAigNotSpec)
    (hΓ_and : Γ.Has "bv_mk_and" bvMkAndSpec)
    (hΓ_or : Γ.Has "bv_aig_or" bvAigOrSpec)
    (hΓ_xor : Γ.Has "bv_aig_xor" bvAigXorSpec) :
    bvBlastSubWithBorrowSpec.Le (Func.wp Γ bv_blast_sub_with_borrow_body) := by
  intro ⟨h, a_off, b_off, out_off, w, ⟨⟩⟩ m Q X
  rintro ⟨hdr, g, aigWords, htSlots, litsPool, R, hinv, hlcap, hpre, hmem, hpost⟩
  dsimp [Func.wp, bv_blast_sub_with_borrow_body]
  refine wp_join_state (fun _ : Unit => ()) (fun _ m' =>
    m' = m ∧ (hdr.oom ≠ 0#32 ∨ ¬(hdr.lits_len.toNat ≤ hdr.lits_cap.toNat ∧
      (0 < w.toNat → hdr.lits_ptr ≠ 0#64) ∧
      a_off.toNat + w.toNat ≤ hdr.lits_len.toNat ∧
      b_off.toNat + w.toNat ≤ hdr.lits_len.toNat ∧
      out_off.toNat + w.toNat ≤ hdr.lits_len.toNat))) ?_ ?_
  · intro J _ m' ⟨hm_eq, hfail⟩
    subst hm_eq
    c0_hfast_nogrp
    have hm1 := opMem_of_hdr_emp (by assumption)
    exact hpost 0#32 { hdr with oom := 1#32 } g aigWords htSlots litsPool _
      hdr_with_oom_aigFrame (Aig.extends_rfl g) (by omega) (aigInv_set_oom 1#32 hinv)
      rfl (fun _ _ => rfl) (fun _ => by simp)
      (fun h0 hlcap0 hlptr ha hb ho _ _ => by
        exfalso; rcases hfail with hne | hbad
        · exact hne h0
        · exact hbad ⟨hlcap0, hlptr, ha, hb, ho⟩)
      (fun _ => rfl) (fun h => absurd h (by simp)) hm1
  · intro J hJ
    c0_hfast_nogrp
    c0_hsplit
    · have hne : hdr.oom ≠ 0#32 := by simpa [bv_c0_bne_false] using hc
      c0_hfast_nogrp
      exact hJ () m ⟨rfl, Or.inl hne⟩
    · have ho : hdr.oom = 0#32 := by simpa [bv_c0_bne_false] using hc
      clear hc
      c0_hcall hΓ_ok
      refine ⟨hdr, _, opMem_to_hdr hmem, ?_⟩
      dsimp only
      c0_hsplit
      · have hok_a := hc; clear hc
        c0_hcall hΓ_ok
        refine ⟨hdr, _, opMem_to_hdr hmem, ?_⟩
        dsimp only
        c0_hsplit
        · have hok_b := hc; clear hc
          c0_hcall hΓ_ok
          refine ⟨hdr, _, opMem_to_hdr hmem, ?_⟩
          dsimp only
          c0_hsplit
          · have hok_o := hc; clear hc
            have haw : a_off.toNat + w.toNat ≤ hdr.lits_len.toNat := by omega
            have hbw : b_off.toNat + w.toNat ≤ hdr.lits_len.toNat := by omega
            have how : out_off.toNat + w.toNat ≤ hdr.lits_len.toNat := by omega
            rcases hpre ho hok_a.1 hok_a.2.1 haw hbw how with
              ⟨ha_wf, hb_wf, hdisj_a, hdisj_b⟩
            c0_hfast_nogrp
            refine ProofKit.c0_while_state
              (fun st : Nat × Val i32 × BVHdrState × Aig × List (BitVec 64) ×
                  List (BitVec 32) × List (BitVec 32) => (st.2.1, BitVec.ofNat 32 st.1, ()))
              (fun st => w.toNat - st.1)
              (fun st m1 =>
                let (j, carry, hdr1, g1, aw1, ht1, lp1) := st
                hdr.AigFrame hdr1 ∧ g ≤ g1 ∧ g1.nodes.size ≤ g.nodes.size + 9 * j ∧
                  AigInv hdr1 g1 aw1 ht1 ∧ lp1.length = litsPool.length ∧
                  j ≤ w.toNat ∧ hdr1.oom = 0#32 ∧ (carry >>> 1).toNat < hdr1.aig_len.toNat ∧
                  (∀ p, p < out_off.toNat ∨ out_off.toNat + j ≤ p →
                    lp1.getD p 0#32 = litsPool.getD p 0#32) ∧
                  (∀ k, k < j →
                    ((lp1.getD (out_off.toNat + k) 0#32) >>> 1).toNat < hdr1.aig_len.toNat) ∧
                  (∀ ρ, g1.evalLit ρ (UInt32.ofBitVec carry) =
                    BitVec.carry j (sliceVal g ρ litsPool a_off.toNat w.toNat)
                      (~~~(sliceVal g ρ litsPool b_off.toNat w.toNat)) true) ∧
                  (∀ k, k < j → ∀ ρ,
                    g1.evalLit ρ (UInt32.ofBitVec (lp1.getD (out_off.toNat + k) 0#32)) =
                      (sliceVal g ρ litsPool a_off.toNat w.toNat -
                        sliceVal g ρ litsPool b_off.toNat w.toNat).getLsbD k) ∧
                  (array (t := i32) hdr.lits_ptr lp1 ⋆
                    (bvHdrMem h hdr1 ⋆ array64 hdr1.aig_ptr aw1 ⋆
                      array (t := i32) hdr1.ht_ptr ht1 ⋆ R)) m1) ?_ ?_
            · intro J2 hJ2
              refine hJ2 (0, 1#32, hdr, g, aigWords, htSlots, litsPool) _
                ⟨Modifies.refl _ _, Aig.extends_rfl g, by dsimp; omega, hinv, rfl,
                  by omega, ho, by rw [hinv.aig_len_eq]; simp; omega, fun _ _ => rfl,
                  fun _ hk => False.elim (Nat.not_lt_zero _ hk),
                  fun ρ => by rw [evalLit_one, BitVec.carry_zero],
                  fun _ hk => False.elim (Nat.not_lt_zero _ hk), opMem_to_lits hmem⟩
            · intro J2 st m1
                ⟨hf1, hg1, hsz1, hinv1, hlen1, hjle, hoom1, hcarry_wf1, hagree1, hwf1,
                  hcarry_eval1, heval1, hm1⟩ hjind
              rcases st with ⟨j, carry, hdr1, g1, aw1, ht1, lp1⟩
              dsimp only at *
              have hjn : (BitVec.ofNat 32 j).toNat = j := by
                rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]; have := w.isLt; omega
              c0_hfast_nogrp
              c0_hsplit
              · have hjlt : j < w.toNat := by omega
                have ha_fit1 : a_off.toNat + (BitVec.ofNat 32 j).toNat < 2 ^ 32 := by
                  have := hdr.lits_cap.isLt; omega
                have ha_fit2 : a_off.toNat + (BitVec.ofNat 32 j).toNat < lp1.length := by omega
                have hb_fit1 : b_off.toNat + (BitVec.ofNat 32 j).toNat < 2 ^ 32 := by
                  have := hdr.lits_cap.isLt; omega
                have hb_fit2 : b_off.toNat + (BitVec.ofNat 32 j).toNat < lp1.length := by omega
                c0_hfast_nogrp
                have ha_lp1 : lp1.getD (a_off.toNat + j) 0#32 =
                    litsPool.getD (a_off.toNat + j) 0#32 := by
                  apply hagree1; unfold DisjointSlice at hdisj_a; omega
                have hb_lp1 : lp1.getD (b_off.toNat + j) 0#32 =
                    litsPool.getD (b_off.toNat + j) 0#32 := by
                  apply hagree1; unfold DisjointSlice at hdisj_b; omega
                have ha_idx : (BitVec.setWidth 64 (a_off + BitVec.ofNat 32 j)).toNat =
                    a_off.toNat + j := by
                  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by
                    have := (a_off + BitVec.ofNat 32 j).isLt; omega),
                    BitVec.toNat_add, hjn, Nat.mod_eq_of_lt (by omega)]
                have hb_idx : (BitVec.setWidth 64 (b_off + BitVec.ofNat 32 j)).toNat =
                    b_off.toNat + j := by
                  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by
                    have := (b_off + BitVec.ofNat 32 j).isLt; omega),
                    BitVec.toNat_add, hjn, Nat.mod_eq_of_lt (by omega)]
                have ha_get : lp1[(BitVec.setWidth 64 (a_off + BitVec.ofNat 32 j)).toNat]'(by
                    omega) = litsPool.getD (a_off.toNat + j) 0#32 := by
                  simp only [ha_idx]; rw [list_getD_eq_getElem lp1 0#32 (by omega)]; exact ha_lp1
                have hb_get : lp1[(BitVec.setWidth 64 (b_off + BitVec.ofNat 32 j)).toNat]'(by
                    omega) = litsPool.getD (b_off.toNat + j) 0#32 := by
                  simp only [hb_idx]; rw [list_getD_eq_getElem lp1 0#32 (by omega)]; exact hb_lp1
                c0_hcall hΓ_not
                dsimp only [bvAigNotSpec]
                have haig01 : hdr.aig_len.toNat ≤ hdr1.aig_len.toNat := by
                  have hA := hg1.1; have hsz := hg1.2.1
                  rw [hinv.aig_len_eq, hinv1.aig_len_eq, hA]; omega
                have ha_lt1 : (lp1[(BitVec.setWidth 64 (a_off + BitVec.ofNat 32 j)).toNat] >>>
                    1).toNat < hdr1.aig_len.toNat := by
                  rw [ha_get]; exact Nat.lt_of_lt_of_le (ha_wf.2 j hjlt) haig01
                have hnb_lt1 : ((lp1[(BitVec.setWidth 64 (b_off + BitVec.ofNat 32 j)).toNat] ^^^
                    1#32) >>> 1).toNat < hdr1.aig_len.toNat := by
                  rw [aigLit_xor_one_shift, hb_get]
                  exact Nat.lt_of_lt_of_le (hb_wf.2 j hjlt) haig01
                have ha_lt_g : (UInt32.ofBitVec (litsPool.getD (a_off.toNat + j) 0#32)).toNat <
                    2 * (g.A + 1 + g.nodes.size) := by
                  have hlt := ha_wf.2 j hjlt; rw [hinv.aig_len_eq] at hlt
                  exact lit_toNat_lt_of_shift hlt
                have hb_lt_g : (UInt32.ofBitVec (litsPool.getD (b_off.toNat + j) 0#32)).toNat <
                    2 * (g.A + 1 + g.nodes.size) := by
                  have hlt := hb_wf.2 j hjlt; rw [hinv.aig_len_eq] at hlt
                  exact lit_toNat_lt_of_shift hlt
                have hm1' : (array (t := i32) hdr1.lits_ptr lp1 ⋆
                    (bvHdrMem h hdr1 ⋆ array64 hdr1.aig_ptr aw1 ⋆
                      array (t := i32) hdr1.ht_ptr ht1 ⋆ R)) m1 := by
                  rw [hf1.lits_ptr]; exact hm1
                have hm1_op := opMem_of_lits hm1'
                refine aigBinOom_wp Γ hΓ_xor hinv1 hoom1 ha_lt1 hnb_lt1 hm1_op ?_ ?_
                · intro hdr2 g2 aw2 ht2 m2 hf12 hg12 hsz12 hinv2 hoom2 hnofit hm2
                  exact bv_sub_oom_ret0_wp ho hf1 hg1 (by omega) (hf1.trans hf12)
                    (Aig.extends_trans hg1 hg12) (by omega) hinv2 hlen1 hagree1 (by omega)
                    hoom2 hnofit hm2 hpost
                · intro s0 hdr2 g2 aw2 ht2 m2 hf12 hg12 hsz12 hinv2 ho2 hs0_wf hs0_eval hm2
                  have haig12 : hdr1.aig_len.toNat ≤ hdr2.aig_len.toNat := by
                    have hA := hg12.1; have hsz := hg12.2.1
                    rw [hinv1.aig_len_eq, hinv2.aig_len_eq, hA]; omega
                  have hc_wf2 : (carry >>> 1).toNat < hdr2.aig_len.toNat :=
                    Nat.lt_of_lt_of_le hcarry_wf1 haig12
                  have hf2 := hf1.trans hf12
                  have hg2 := Aig.extends_trans hg1 hg12
                  refine aigBinOom_wp Γ hΓ_xor hinv2 ho2 hs0_wf hc_wf2 hm2 ?_ ?_
                  · intro hdr3 g3 aw3 ht3 m3 hf23 hg23 hsz23 hinv3 hoom3 hnofit hm3
                    exact bv_sub_oom_ret0_wp ho hf2 hg2 (by omega) (hf2.trans hf23)
                      (Aig.extends_trans hg2 hg23) (by omega) hinv3 hlen1 hagree1 (by omega)
                      hoom3 hnofit hm3 hpost
                  · intro sum hdr3 g3 aw3 ht3 m3 hf23 hg23 hsz23 hinv3 ho3 hsum_wf hsum_eval hm3
                    have hf3 := hf2.trans hf23
                    have hg3 := Aig.extends_trans hg2 hg23
                    have ho_fit1 : out_off.toNat + (BitVec.ofNat 32 j).toNat < 2 ^ 32 := by
                      have := hdr.lits_cap.isLt; omega
                    have ho_fit2 : out_off.toNat + (BitVec.ofNat 32 j).toNat < lp1.length := by
                      omega
                    have hm3_l : (array (t := i32) hdr.lits_ptr lp1 ⋆
                        (bvHdrMem h hdr3 ⋆ array64 hdr3.aig_ptr aw3 ⋆
                          array (t := i32) hdr3.ht_ptr ht3 ⋆ R)) m3 := by
                      rw [← hf3.lits_ptr]; exact opMem_to_lits hm3
                    c0_hfast_nogrp
                    have ho_idx : (BitVec.setWidth 64 (out_off + BitVec.ofNat 32 j)).toNat =
                        out_off.toNat + j := by
                      rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by
                        have := (out_off + BitVec.ofNat 32 j).isLt; omega),
                        BitVec.toNat_add, hjn, Nat.mod_eq_of_lt (by omega)]
                    rw [ho_idx] at hm
                    let lp2 := lp1.set (out_off.toNat + j) sum
                    have hm3' : (array (t := i32) hdr3.lits_ptr lp2 ⋆
                        (bvHdrMem h hdr3 ⋆ array64 hdr3.aig_ptr aw3 ⋆
                          array (t := i32) hdr3.ht_ptr ht3 ⋆ R)) m := by
                      rw [hf3.lits_ptr]; exact hm
                    have hm3_op := opMem_of_lits hm3'
                    have haig23 : hdr2.aig_len.toNat ≤ hdr3.aig_len.toNat := by
                      have hA := hg23.1; have hsz := hg23.2.1
                      rw [hinv2.aig_len_eq, hinv3.aig_len_eq, hA]; omega
                    have hs0_wf3 : (s0 >>> 1).toNat < hdr3.aig_len.toNat :=
                      Nat.lt_of_lt_of_le hs0_wf haig23
                    have hc_wf3 : (carry >>> 1).toNat < hdr3.aig_len.toNat :=
                      Nat.lt_of_lt_of_le hc_wf2 haig23
                    have hlen2 : lp2.length = litsPool.length := by simp [lp2, hlen1]
                    have hagree2 : ∀ p, p < out_off.toNat ∨ out_off.toNat + (j + 1) ≤ p →
                        lp2.getD p 0#32 = litsPool.getD p 0#32 := by
                      intro p hp
                      have hne : p ≠ out_off.toNat + j := by omega
                      dsimp only [lp2]; rw [list_getD_set_ne lp1 0#32 sum hne]
                      exact hagree1 p (by
                        rcases hp with hp | hp
                        · exact Or.inl hp
                        · exact Or.inr (by omega))
                    refine aigBinOom_wp Γ hΓ_and hinv3 ho3 hs0_wf3 hc_wf3 hm3_op ?_ ?_
                    · intro hdr4 g4 aw4 ht4 m4 hf34 hg34 hsz34 hinv4 hoom4 hnofit hm4
                      exact bv_sub_oom_ret0_wp ho hf3 hg3 (by omega) (hf3.trans hf34)
                        (Aig.extends_trans hg3 hg34) (by omega) hinv4 hlen2 hagree2
                        (by omega) hoom4 hnofit hm4 hpost
                    · intro cs hdr4 g4 aw4 ht4 m4 hf34 hg34 hsz34 hinv4 ho4 hcs_wf hcs_eval hm4
                      have hf4 := hf3.trans hf34
                      have hg4 := Aig.extends_trans hg3 hg34
                      have haig14 : hdr1.aig_len.toNat ≤ hdr4.aig_len.toNat := by
                        have hA := hg12.1; have hA2 := hg23.1; have hA3 := hg34.1
                        have hs1 := hg12.2.1; have hs2 := hg23.2.1; have hs3 := hg34.2.1
                        rw [hinv1.aig_len_eq, hinv4.aig_len_eq, hA, hA2, hA3]; omega
                      have ha_wf4 : (lp1[(BitVec.setWidth 64
                          (a_off + BitVec.ofNat 32 j)).toNat] >>> 1).toNat <
                          hdr4.aig_len.toNat := Nat.lt_of_lt_of_le ha_lt1 haig14
                      have hnb_wf4 : ((lp1[(BitVec.setWidth 64
                          (b_off + BitVec.ofNat 32 j)).toNat] ^^^ 1#32) >>> 1).toNat <
                          hdr4.aig_len.toNat := Nat.lt_of_lt_of_le hnb_lt1 haig14
                      refine aigBinOom_wp Γ hΓ_and hinv4 ho4 ha_wf4 hnb_wf4 hm4 ?_ ?_
                      · intro hdr5 g5 aw5 ht5 m5 hf45 hg45 hsz45 hinv5 hoom5 hnofit hm5
                        exact bv_sub_oom_ret0_wp ho hf4 hg4 (by omega) (hf4.trans hf45)
                          (Aig.extends_trans hg4 hg45) (by omega) hinv5 hlen2 hagree2
                          (by omega) hoom5 hnofit hm5 hpost
                      · intro ab hdr5 g5 aw5 ht5 m5 hf45 hg45 hsz45 hinv5 ho5 hab_wf hab_eval hm5
                        have hf5 := hf4.trans hf45
                        have hg5 := Aig.extends_trans hg4 hg45
                        have haig45 : hdr4.aig_len.toNat ≤ hdr5.aig_len.toNat := by
                          have hA := hg45.1; have hs := hg45.2.1
                          rw [hinv4.aig_len_eq, hinv5.aig_len_eq, hA]; omega
                        have hcs_wf5 : (cs >>> 1).toNat < hdr5.aig_len.toNat :=
                          Nat.lt_of_lt_of_le hcs_wf haig45
                        refine aigBinOom_wp Γ hΓ_or hinv5 ho5 hcs_wf5 hab_wf hm5 ?_ ?_
                        · intro hdr6 g6 aw6 ht6 m6 hf56 hg56 hsz56 hinv6 hoom6 hnofit hm6
                          exact bv_sub_oom_ret0_wp ho hf5 hg5 (by omega) (hf5.trans hf56)
                            (Aig.extends_trans hg5 hg56) (by omega) hinv6 hlen2 hagree2
                            (by omega) hoom6 hnofit hm6 hpost
                        · intro carry' hdr6 g6 aw6 ht6 m6 hf56 hg56 hsz56 hinv6 ho6 hc'_wf
                            hc'_eval hm6
                          c0_hfast_nogrp
                          have hadd_j1 : BitVec.ofNat 32 j + 1#32 = BitVec.ofNat 32 (j + 1) := by
                            apply BitVec.eq_of_toNat_eq
                            have := w.isLt; have hmod1 : (1#32 : BitVec 32).toNat = 1 := rfl
                            rw [BitVec.toNat_add, hjn, hmod1, BitVec.toNat_ofNat,
                              Nat.mod_eq_of_lt (by omega)]
                          rw [hadd_j1]
                          have hf6 := hf5.trans hf56
                          have hm6_l : (array (t := i32) hdr.lits_ptr lp2 ⋆
                              (bvHdrMem h hdr6 ⋆ array64 hdr6.aig_ptr aw6 ⋆
                                array (t := i32) hdr6.ht_ptr ht6 ⋆ R)) m6 := by
                            rw [← hf6.lits_ptr]; exact opMem_to_lits hm6
                          have hg6 := Aig.extends_trans hg5 hg56
                          have haig36 : hdr3.aig_len.toNat ≤ hdr6.aig_len.toNat := by
                            have hA1 := hg34.1; have hA2 := hg45.1; have hA3 := hg56.1
                            have hs1 := hg34.2.1; have hs2 := hg45.2.1; have hs3 := hg56.2.1
                            rw [hinv3.aig_len_eq, hinv6.aig_len_eq, hA1, hA2, hA3]; omega
                          have hg36 : g3 ≤ g6 :=
                            Aig.extends_trans hg34 (Aig.extends_trans hg45 hg56)
                          have ha_lit1 : (UInt32.ofBitVec
                              (litsPool.getD (a_off.toNat + j) 0#32)).toNat <
                              2 * (g1.A + 1 + g1.nodes.size) := by
                            have hA := hg1.1; have hsz := hg1.2.1; omega
                          have hb_lit1 : (UInt32.ofBitVec
                              (litsPool.getD (b_off.toNat + j) 0#32)).toNat <
                              2 * (g1.A + 1 + g1.nodes.size) := by
                            have hA := hg1.1; have hsz := hg1.2.1; omega
                          have hc_lit2 : (UInt32.ofBitVec carry).toNat <
                              2 * (g2.A + 1 + g2.nodes.size) := by
                            have hlt := hc_wf2; rw [hinv2.aig_len_eq] at hlt
                            exact lit_toNat_lt_of_shift hlt
                          have hs0_lit2 : (UInt32.ofBitVec s0).toNat <
                              2 * (g2.A + 1 + g2.nodes.size) := by
                            have hlt := hs0_wf; rw [hinv2.aig_len_eq] at hlt
                            exact lit_toNat_lt_of_shift hlt
                          refine hjind (j + 1, carry', hdr6, g6, aw6, ht6, lp2) m6 (by omega)
                            ⟨hf6, hg6, by dsimp only; omega, hinv6, hlen2, by omega, ho6, hc'_wf,
                              hagree2, ?_, ?_, ?_, hm6_l⟩
                          · intro k hk
                            by_cases hkj : k = j
                            · subst hkj; dsimp only [lp2]
                              rw [list_getD_set_self lp1 0#32 sum (by omega)]
                              exact Nat.lt_of_lt_of_le hsum_wf haig36
                            · have hklt : k < j := by omega
                              have hne : out_off.toNat + k ≠ out_off.toNat + j := by omega
                              dsimp only [lp2]
                              rw [list_getD_set_ne lp1 0#32 sum hne]
                              have haig16 : hdr1.aig_len.toNat ≤ hdr6.aig_len.toNat :=
                                Nat.le_trans haig12 (Nat.le_trans haig23 haig36)
                              exact Nat.lt_of_lt_of_le (hwf1 k hklt) haig16
                          · intro ρ
                            dsimp only at hs0_eval hsum_eval hcs_eval hab_eval hc'_eval ⊢
                            rw [hc'_eval ρ, Aig.evalLit_extend hg45 (lit_toNat_lt_of_shift (by
                                rw [← hinv4.aig_len_eq]; exact hcs_wf)),
                              hcs_eval ρ, hab_eval ρ]
                            have hg14 : g1 ≤ g4 := Aig.extends_trans hg12
                              (Aig.extends_trans hg23 hg34)
                            have ha_e : g4.evalLit ρ (UInt32.ofBitVec
                                (lp1[(BitVec.setWidth 64 (a_off + BitVec.ofNat 32 j)).toNat])) =
                                (sliceVal g ρ litsPool a_off.toNat w.toNat).getLsbD j := by
                              rw [ha_get, Aig.evalLit_extend hg14 ha_lit1,
                                Aig.evalLit_extend hg1 ha_lt_g, sliceVal_getLsbD hjlt]
                            have hnb_e : g4.evalLit ρ (UInt32.ofBitVec
                                (lp1[(BitVec.setWidth 64 (b_off + BitVec.ofNat 32 j)).toNat] ^^^
                                  1#32)) =
                                (!(sliceVal g ρ litsPool b_off.toNat w.toNat).getLsbD j) := by
                              rw [evalLit_xor_one, hb_get, Aig.evalLit_extend hg14 hb_lit1,
                                Aig.evalLit_extend hg1 hb_lt_g, sliceVal_getLsbD hjlt]
                            have hs0_e : g3.evalLit ρ (UInt32.ofBitVec s0) =
                                ((sliceVal g ρ litsPool a_off.toNat w.toNat).getLsbD j ^^
                                  !(sliceVal g ρ litsPool b_off.toNat w.toNat).getLsbD j) := by
                              rw [Aig.evalLit_extend hg23 hs0_lit2, hs0_eval ρ, ha_get, hb_get,
                                evalLit_xor_one, Aig.evalLit_extend hg1 ha_lt_g,
                                Aig.evalLit_extend hg1 hb_lt_g,
                                sliceVal_getLsbD hjlt, sliceVal_getLsbD hjlt]
                            have hc_e : g3.evalLit ρ (UInt32.ofBitVec carry) =
                                BitVec.carry j (sliceVal g ρ litsPool a_off.toNat w.toNat)
                                  (~~~(sliceVal g ρ litsPool b_off.toNat w.toNat)) true := by
                              rw [Aig.evalLit_extend hg23 hc_lit2, Aig.evalLit_extend hg12 (by
                                have hlt := hcarry_wf1; rw [hinv1.aig_len_eq] at hlt
                                exact lit_toNat_lt_of_shift hlt), hcarry_eval1 ρ]
                            rw [hs0_e, hc_e, ha_e, hnb_e]
                            rw [BitVec.carry_succ, BitVec.getLsbD_not]
                            simp only [hjlt, decide_true, Bool.true_and]
                            cases (sliceVal g ρ litsPool a_off.toNat w.toNat).getLsbD j <;>
                              cases (sliceVal g ρ litsPool b_off.toNat w.toNat).getLsbD j <;>
                              cases BitVec.carry j (sliceVal g ρ litsPool a_off.toNat w.toNat)
                                (~~~(sliceVal g ρ litsPool b_off.toNat w.toNat)) true <;> rfl
                          · intro k hk ρ
                            by_cases hkj : k = j
                            · subst hkj; dsimp only [lp2] at *
                              rw [list_getD_set_self lp1 0#32 sum (by omega)]
                              have hsum_lt3 : (UInt32.ofBitVec sum).toNat <
                                  2 * (g3.A + 1 + g3.nodes.size) := by
                                have hlt := hsum_wf
                                rw [hinv3.aig_len_eq] at hlt
                                exact lit_toNat_lt_of_shift hlt
                              rw [Aig.evalLit_extend hg36 hsum_lt3, hsum_eval ρ,
                                hs0_eval ρ, ha_get, hb_get,
                                evalLit_xor_one, Aig.evalLit_extend hg1 ha_lt_g,
                                Aig.evalLit_extend hg1 hb_lt_g,
                                Aig.evalLit_extend hg12 (by
                                  have hlt := hcarry_wf1; rw [hinv1.aig_len_eq] at hlt
                                  exact lit_toNat_lt_of_shift hlt),
                                hcarry_eval1 ρ, bv_sub_diff_getLsbD _ _ hjlt,
                                sliceVal_getLsbD hjlt, sliceVal_getLsbD hjlt]
                            · have hklt : k < j := by omega
                              have hne : out_off.toNat + k ≠ out_off.toNat + j := by omega
                              dsimp only [lp2]
                              rw [list_getD_set_ne lp1 0#32 sum hne]
                              have hg16 : g1 ≤ g6 :=
                                Aig.extends_trans hg12 (Aig.extends_trans hg23 hg36)
                              have hlit1 : (UInt32.ofBitVec
                                  (lp1.getD (out_off.toNat + k) 0#32)).toNat <
                                  2 * (g1.A + 1 + g1.nodes.size) := by
                                have hlt := hwf1 k hklt; rw [hinv1.aig_len_eq] at hlt
                                exact lit_toNat_lt_of_shift hlt
                              rw [Aig.evalLit_extend hg16 hlit1]
                              exact heval1 k hklt ρ
              · have hjge : j = w.toNat := by omega
                clear hc
                c0_hcall hΓ_not
                dsimp only [bvAigNotSpec]
                c0_hfast_nogrp
                subst hjge
                rw [← hf1.lits_ptr] at hm1
                refine hpost (carry ^^^ 1#32) hdr1 g1 aw1 ht1 lp1 m1 hf1 hg1 hsz1 hinv1 hlen1
                  hagree1 (fun hne => absurd ho hne) (fun _ _ _ _ _ _ _ _ => hoom1)
                  (fun hne => absurd hoom1 hne) (fun _ => ?_) (opMem_of_lits hm1)
                refine ⟨⟨by rw [hf1.lits_len]; exact how, hwf1⟩, ?_, fun ρ => ?_⟩
                · rw [aigLit_xor_one_shift]; exact hcarry_wf1
                · constructor
                  · apply BitVec.eq_of_getLsbD_eq
                    intro i hi
                    rw [sliceVal_getLsbD hi, heval1 i hi ρ]
                  · rw [evalLit_xor_one, hcarry_eval1 ρ, BitVec.ult_eq_not_carry]
          · have hbad := hc; clear hc; c0_hfast_nogrp
            exact hJ () m ⟨rfl, Or.inr fun ⟨h1, h2, h3, h4, h5⟩ =>
              hbad ⟨h1, h2, by omega, by omega⟩⟩
        · have hbad := hc; clear hc; c0_hfast_nogrp
          exact hJ () m ⟨rfl, Or.inr fun ⟨h1, h2, h3, h4, h5⟩ =>
            hbad ⟨h1, h2, by omega, by omega⟩⟩
      · have hbad := hc; clear hc; c0_hfast_nogrp
        exact hJ () m ⟨rfl, Or.inr fun ⟨h1, h2, h3, h4, h5⟩ =>
          hbad ⟨h1, h2, by omega, by omega⟩⟩

end

end LeanQbe.T.Examples.Bitblast.Proof.OpsDivCpop
