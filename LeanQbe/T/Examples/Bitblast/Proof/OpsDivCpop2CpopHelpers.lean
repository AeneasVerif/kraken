module

public import LeanQbe.T.Examples.Bitblast.Proof.OpsDivCpop2Helpers
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import LeanQbe.T.Logic.ProofKit
import LeanQbe.T.Logic.Rules

set_option autoImplicit false

namespace LeanQbe.T.Examples.Bitblast.Proof.OpsDivCpop

open LeanQbe.T
open LeanQbe.T.Examples.Bitblast.Ref
open LeanQbe.T.Examples.Bitblast.Src.OpsDivCpop

/-!
## Modular Helpers for `bv_blast_cpop` Loops (`OpsDivCpop2CpopHelpers`)

Defines C0 AST sub-expressions and proves `wp` lemmas for the `bv_blast_cpop` initialization,
copy-out, and iterative halving loops.
-/

section

attribute [local c0_load] load_hdr_oom load_hdr_lits_ptr load_hdr_lits_len load_hdr_lits_cap
attribute [local c0_store] store_hdr_oom store_hdr_lits_len

/-! ## Sub-expressions matching `bv_blast_cpop_body` -/

public abbrev cpopInitInnerExpr (buf0 w row_off outer_i : Val i32) (ld : Val i64)
    (outerJ : Cont [i32]) : Expr Val Cont [i32] :=
  Expr.group
    (fun Js_1 => Blocks.cons
      (fun p_42 : Tup Val [i32] =>
        Expr.let_ (op2 (OpCode.cmp CmpOp.ult i32 Ty.bool (by decide))
          (Arg.var p_42.fst) (Arg.var w)) fun p =>
        Expr.jnz (Arg.var p.fst)
          (Expr.let_ (op2 (OpCode.add i32) (Arg.var buf0) (Arg.var row_off)) fun p =>
          Expr.let_ (op2 (OpCode.add i32) (Arg.var p.fst) (Arg.var p_42.fst)) fun p =>
          Expr.let_ (op1 (OpCode.zext 32 64) (Arg.var p.fst)) fun p =>
          Expr.let_ (op2 (OpCode.mul i64) (Arg.var p.fst) (Arg.imm 4#64)) fun p =>
          Expr.let_ (op2 (OpCode.add i64) (Arg.var ld) (Arg.var p.fst)) fun p =>
          Expr.store (Arg.imm (t := i32) 0#32) (Arg.var p.fst)
            (Expr.let_ (op2 (OpCode.add i32) (Arg.var p_42.fst) (Arg.imm 1#32)) fun p =>
            Expr.jump Js_1.fst (Arg.var p.fst, ())))
          (Expr.let_ (op2 (OpCode.add i32) (Arg.var outer_i) (Arg.imm 1#32)) fun p =>
          Expr.jump outerJ (Arg.var p.fst, ())))
      Blocks.nil)
    (fun Js => Expr.jump Js.fst (Arg.imm 1#32, ()))

public abbrev cpopInitLoopExpr (a_off w buf0 : Val i32) (ld : Val i64)
    (afterExpr : Expr Val Cont [i32]) : Expr Val Cont [i32] :=
  Expr.group
    (fun Js => Blocks.cons
      (fun p_31 : Tup Val [i32] =>
        Expr.let_ (op2 (OpCode.cmp CmpOp.ult i32 Ty.bool (by decide))
          (Arg.var p_31.fst) (Arg.var w)) fun p_32 =>
        Expr.jnz (Arg.var p_32.fst)
          (Expr.let_ (op2 (OpCode.mul i32) (Arg.var p_31.fst) (Arg.var w)) fun p_33 =>
          Expr.let_ (op2 (OpCode.add i32) (Arg.var buf0) (Arg.var p_33.fst)) fun p_34 =>
          Expr.let_ (op1 (OpCode.zext 32 64) (Arg.var p_34.fst)) fun p_35 =>
          Expr.let_ (op2 (OpCode.mul i64) (Arg.var p_35.fst) (Arg.imm 4#64)) fun p_36 =>
          Expr.let_ (op2 (OpCode.add i64) (Arg.var ld) (Arg.var p_36.fst)) fun p_37 =>
          Expr.let_ (op2 (OpCode.add i32) (Arg.var a_off) (Arg.var p_31.fst)) fun p_38 =>
          Expr.let_ (op1 (OpCode.zext 32 64) (Arg.var p_38.fst)) fun p_39 =>
          Expr.let_ (op2 (OpCode.mul i64) (Arg.var p_39.fst) (Arg.imm 4#64)) fun p_40 =>
          Expr.let_ (op2 (OpCode.add i64) (Arg.var ld) (Arg.var p_40.fst)) fun p_41 =>
          Expr.load i32 (Arg.var p_41.fst) fun ld_3 =>
          Expr.store (Arg.var ld_3) (Arg.var p_37.fst)
            (cpopInitInnerExpr buf0 w p_33.fst p_31.fst ld Js.fst))
          afterExpr)
      Blocks.nil)
    (fun Js => Expr.jump Js.fst (Arg.imm 0#32, ()))

public abbrev cpopCopyOutLoopExpr (h : Val i64) (out_off w cur_in mark1 : Val i32) (ld : Val i64) :
    Expr Val Cont [i32] :=
  Expr.group
    (fun Js => Blocks.cons
      (fun p_35 : Tup Val [i32] =>
        Expr.let_ (op2 (OpCode.cmp CmpOp.ult i32 Ty.bool (by decide))
          (Arg.var p_35.fst) (Arg.var w)) fun p_36 =>
        Expr.jnz (Arg.var p_36.fst)
          (Expr.let_ (op2 (OpCode.add i32) (Arg.var out_off) (Arg.var p_35.fst)) fun p =>
          Expr.let_ (op1 (OpCode.zext 32 64) (Arg.var p.fst)) fun p =>
          Expr.let_ (op2 (OpCode.mul i64) (Arg.var p.fst) (Arg.imm 4#64)) fun p =>
          Expr.let_ (op2 (OpCode.add i64) (Arg.var ld) (Arg.var p.fst)) fun p =>
          Expr.let_ (op2 (OpCode.add i32) (Arg.var cur_in) (Arg.var p_35.fst)) fun p_37 =>
          Expr.let_ (op1 (OpCode.zext 32 64) (Arg.var p_37.fst)) fun p_38 =>
          Expr.let_ (op2 (OpCode.mul i64) (Arg.var p_38.fst) (Arg.imm 4#64)) fun p_39 =>
          Expr.let_ (op2 (OpCode.add i64) (Arg.var ld) (Arg.var p_39.fst)) fun p_40 =>
          Expr.load i32 (Arg.var p_40.fst) fun ld =>
          Expr.store (Arg.var ld) (Arg.var p.fst)
            (Expr.let_ (op2 (OpCode.add i32) (Arg.var p_35.fst) (Arg.imm 1#32)) fun p =>
            Expr.jump Js.fst (Arg.var p.fst, ())))
          (Expr.call (as := [i64, i32]) (bs := []) "bv_lits_release"
            (Arg.var h, Arg.var mark1, ()) fun _ => Expr.ret (Arg.var out_off, ())))
      Blocks.nil)
    (fun Js => Expr.jump Js.fst (Arg.imm 0#32, ()))

public abbrev cpopHalveLoopExpr (h : Val i64) (out_off w buf0 buf1 mark0 mark1 : Val i32)
    (ld : Val i64) : Expr Val Cont [i32] :=
  Expr.group
    (fun Js => Blocks.cons
      (fun p_33 : Tup Val [i32, i32, i32] =>
        Expr.let_ (op2 (OpCode.cmp CmpOp.ugt i32 Ty.bool (by decide))
          (Arg.var p_33.snd.snd.fst) (Arg.imm 1#32)) fun p_34 =>
        Expr.jnz (Arg.var p_34.fst)
          (Expr.call (as := [i64, i32, i32, i32, i32]) (bs := [Ty.bool]) "bv_blast_cpop_layer"
            (Arg.var h, Arg.var p_33.fst, Arg.var p_33.snd.fst, Arg.var p_33.snd.snd.fst,
              Arg.var w, ()) fun p_35 =>
          Expr.jnz (Arg.var p_35.fst)
            (Expr.let_ (op1 (OpCode.zext 32 64) (Arg.var p_33.snd.snd.fst)) fun p =>
            Expr.let_ (op2 (OpCode.add i64) (Arg.var p.fst) (Arg.imm 1#64)) fun p =>
            Expr.let_ (op1 (OpCode.sext 32 64) (Arg.imm 1#32)) fun p_36 =>
            Expr.let_ (op2 (OpCode.lshr i64) (Arg.var p.fst) (Arg.var p_36.fst)) fun p =>
            Expr.let_ (op1 (OpCode.trunc 64 32) (Arg.var p.fst)) fun p =>
            Expr.jump Js.fst (Arg.var p_33.snd.fst, Arg.var p_33.fst, Arg.var p.fst, ()))
            (Expr.call (as := [i64, i32]) (bs := []) "bv_lits_release"
              (Arg.var h, Arg.var mark0, ()) fun _ => Expr.ret (Arg.imm 4294967295#32, ())))
          (cpopCopyOutLoopExpr h out_off w p_33.fst mark1 ld))
      Blocks.nil)
    (fun Js => Expr.jump Js.fst (Arg.var buf0, Arg.var buf1, Arg.var w, ()))

/-! ## `bv_blast_cpop` loop proofs -/

public theorem aigInv_with_lits_len_oom {hdr : BVHdrState} {g : Aig}
    {aw : List (BitVec 64)} {ht : List (BitVec 32)}
    (hinv : AigInv hdr g aw ht) (llen o : BitVec 32) :
    AigInv { hdr with lits_len := llen, oom := o } g aw ht :=
  ⟨hinv.wf, hinv.num_atoms_eq, hinv.aig_len_eq, hinv.aig_len_le_cap,
   hinv.aig_cap_eq, hinv.aig_cap_lt, hinv.gates_bound, hinv.words_match,
   hinv.ht_len, hinv.ht_mask_lt, hinv.ht_pos, hinv.ht_bound⟩

public theorem aigInv_of_dcBlastFrame {hdr hdr' : BVHdrState} {g : Aig}
    {aw : List (BitVec 64)} {ht : List (BitVec 32)}
    (hinv : AigInv hdr g aw ht) (hf : hdr.DcBlastFrame hdr') (hlen : hdr'.aig_len = hdr.aig_len) :
    AigInv hdr' g aw ht :=
  ⟨hinv.wf, by rw [hf.num_atoms]; exact hinv.num_atoms_eq, by rw [hlen]; exact hinv.aig_len_eq,
   hinv.aig_len_le_cap, by rw [hf.aig_cap]; exact hinv.aig_cap_eq, hinv.aig_cap_lt,
   hinv.gates_bound, hinv.words_match, by rw [hf.ht_mask]; exact hinv.ht_len,
   fun x => by rw [hf.ht_mask]; exact hinv.ht_mask_lt x, hinv.ht_pos, hinv.ht_bound⟩

private theorem bv_cpop_init_inner_wp {Γ : Env} {h : Val i64} {buf0 w : BitVec 32}
    {i : Nat} {row_off : BitVec 32} {ld : Val i64} {outerJ : Cont [i32]}
    {hdr : BVHdrState} {g : Aig} {aw : List (BitVec 64)} {ht lpInit lp0 : List (BitVec 32)}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [i32]} {X : XPost}
    (hinv : AigInv hdr g aw ht) (hld : ld = hdr.lits_ptr)
    (_hpos_aig : 0 < hdr.aig_len.toNat) (hw1 : 1 < w.toNat) (hiw : i < w.toNat)
    (_hrow : row_off = BitVec.ofNat 32 (i * w.toNat)) (hrow_nat : row_off.toNat = i * w.toNat)
    (hw2_32 : w.toNat * w.toNat < 2 ^ 32)
    (hbuf : buf0.toNat + w.toNat * w.toNat ≤ hdr.lits_len.toNat)
    (hlencap : hdr.lits_len.toNat ≤ hdr.lits_cap.toNat)
    (hcaplen : hdr.lits_cap.toNat ≤ lpInit.length)
    (hlen0 : lpInit.length = lp0.length)
    (hagree0 : ∀ p, p < buf0.toNat + i * w.toNat ∨ buf0.toNat + i * w.toNat + 1 ≤ p →
      lpInit.getD p 0#32 = lp0.getD p 0#32)
    (hmem : (bvHdrMem h hdr ⋆ array64 hdr.aig_ptr aw ⋆
      array (t := i32) hdr.ht_ptr ht ⋆ array (t := i32) hdr.lits_ptr lpInit ⋆ R) m)
    (hnext : ∀ lp' m', lp'.length = lp0.length →
      (∀ p, p < buf0.toNat + i * w.toNat ∨ buf0.toNat + (i + 1) * w.toNat ≤ p →
        lp'.getD p 0#32 = lp0.getD p 0#32) →
      (∀ j, 0 < j → j < w.toNat → lp'.getD (buf0.toNat + i * w.toNat + j) 0#32 = 0#32) →
      lp'.getD (buf0.toNat + i * w.toNat) 0#32 = lpInit.getD (buf0.toNat + i * w.toNat) 0#32 →
      (bvHdrMem h hdr ⋆ array64 hdr.aig_ptr aw ⋆
        array (t := i32) hdr.ht_ptr ht ⋆ array (t := i32) hdr.lits_ptr lp' ⋆ R) m' →
      outerJ (BitVec.ofNat 32 (i + 1), ()) m') :
    wp Γ Q X (cpopInitInnerExpr buf0 w row_off (BitVec.ofNat 32 i) ld outerJ) m := by
  subst hld
  have _ := hinv
  have hiw_lt : i * w.toNat + w.toNat ≤ w.toNat * w.toNat := by
    have hmul : (i + 1) * w.toNat ≤ w.toNat * w.toNat := Nat.mul_le_mul_right _ hiw
    rw [Nat.add_mul, Nat.one_mul] at hmul; exact hmul
  let Inv : (Nat × List (BitVec 32)) → Mem 64 → Prop := fun st ml =>
    1 ≤ st.1 ∧ st.1 ≤ w.toNat ∧ st.2.length = lp0.length ∧
    (∀ p, p < buf0.toNat + i * w.toNat ∨ buf0.toNat + i * w.toNat + st.1 ≤ p →
      st.2.getD p 0#32 = lp0.getD p 0#32) ∧
    (∀ j, 0 < j → j < st.1 → st.2.getD (buf0.toNat + i * w.toNat + j) 0#32 = 0#32) ∧
    st.2.getD (buf0.toNat + i * w.toNat) 0#32 = lpInit.getD (buf0.toNat + i * w.toNat) 0#32 ∧
    (bvHdrMem h hdr ⋆ array64 hdr.aig_ptr aw ⋆
      array (t := i32) hdr.ht_ptr ht ⋆ array (t := i32) hdr.lits_ptr st.2 ⋆ R) ml
  dsimp only [cpopInitInnerExpr]
  apply wp_while_state1 (fun st => BitVec.ofNat 32 st.1) (fun st => w.toNat - st.1) Inv
  · intro J hJ
    exact wp_jump_state (proj := fun st : Nat × List (BitVec 32) => (BitVec.ofNat 32 st.1, ()))
      (1, lpInit) (by simp) (hJ (1, lpInit) m ⟨Nat.le_refl _, by omega, hlen0,
        hagree0, fun _ h0 h1 => by omega, rfl, hmem⟩)
  · intro J st ml ⟨hle1, hle, hlen, hpres, hzero, hbit0, hml⟩ hIH
    rcases st with ⟨k, lp⟩
    dsimp only at hle1 hle hlen hpres hzero hbit0 hml
    have hk32 : (BitVec.ofNat 32 k).toNat = k := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    by_cases hlt : k < w.toNat
    · have hadd_nat : (buf0 + row_off + BitVec.ofNat 32 k).toNat =
          buf0.toNat + i * w.toNat + k := by
        rw [BitVec.toNat_add, BitVec.toNat_add, hrow_nat, hk32,
          Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      have hsw_dst : (BitVec.setWidth 64 (buf0 + row_off + BitVec.ofNat 32 k)).toNat =
          buf0.toNat + i * w.toNat + k := by
        rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by
          have := (buf0 + row_off + BitVec.ofNat 32 k).isLt; omega), hadd_nat]
      have hbv1 : BitVec.ofNat 32 k + 1#32 = BitVec.ofNat 32 (k + 1) := by
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_add, hk32, show (1#32 : BitVec 32).toNat = 1 from rfl,
          BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      c0_hfast_nogrp
      · rw [hbv1]
        let lp1 := lp.set (buf0.toNat + i * w.toNat + k) 0#32
        refine hIH (k + 1, lp1) _ (by omega)
          ⟨by omega, by omega, by simp [lp1, hlen], ?_, ?_, ?_, ?_⟩
        · intro p hp
          have hne : p ≠ buf0.toNat + i * w.toNat + k := by omega
          dsimp only [lp1]; rw [list_getD_set_ne lp 0#32 _ hne]
          exact hpres p (by
            rcases hp with hp | hp
            · exact Or.inl hp
            · exact Or.inr (by omega))
        · intro j hj0 hjlt
          by_cases hjk : j = k
          · subst hjk; dsimp only [lp1]; rw [list_getD_set_self lp 0#32 _ (by omega)]
          · have hne : buf0.toNat + i * w.toNat + j ≠ buf0.toNat + i * w.toNat + k := by omega
            dsimp only [lp1]; rw [list_getD_set_ne lp 0#32 _ hne]; exact hzero j hj0 (by omega)
        · have hne : buf0.toNat + i * w.toNat ≠ buf0.toNat + i * w.toNat + k := by omega
          dsimp only [lp1]; rw [list_getD_set_ne lp 0#32 _ hne]; exact hbit0
        · have hm_raw : (array (t := i32) hdr.lits_ptr
              (lp.set (BitVec.setWidth 64 (buf0 + row_off + BitVec.ofNat 32 k)).toNat 0#32) ⋆
              (bvHdrMem h hdr ⋆ (array64 hdr.aig_ptr aw ⋆
                (array (t := i32) hdr.ht_ptr ht ⋆ (R ⋆ Std.ExtHashMap.emp))))) _ := ‹_›
          refine opMem_of_lits ?_
          simpa only [Std.ExtHashMap.sep_emp, ← Std.ExtHashMap.sep_assoc, hsw_dst] using hm_raw
      · exfalso; omega
    · have hid : k = w.toNat := by omega
      subst hid
      have hi1_lt : i + 1 < 2 ^ 32 := by have := w.isLt; omega
      have hi1 : BitVec.ofNat 32 i + 1#32 = BitVec.ofNat 32 (i + 1) := by
        apply BitVec.eq_of_toNat_eq
        simp [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi1_lt]
      c0_hfast_nogrp
      · exfalso; omega
      · rw [hi1]
        refine hnext lp ml hlen ?_ hzero hbit0 hml
        intro p hp
        exact hpres p (by
          rcases hp with hp | hp
          · exact Or.inl hp
          · rw [Nat.add_mul, Nat.one_mul] at hp; exact Or.inr (by omega))

public theorem bv_cpop_init_loop_wp {Γ : Env} {h : Val i64} {a_off w buf0 : BitVec 32}
    {ld : Val i64} {afterExpr : Expr Val Cont [i32]}
    {hdr : BVHdrState} {g : Aig} {aw : List (BitVec 64)} {ht lp0 : List (BitVec 32)}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [i32]} {X : XPost}
    (hinv : AigInv hdr g aw ht) (hld : ld = hdr.lits_ptr)
    (hw1 : 1 < w.toNat) (hw2_32 : w.toNat * w.toNat < 2 ^ 32)
    (ha_le_buf0 : a_off.toNat + w.toNat ≤ buf0.toNat)
    (hbuf : buf0.toNat + w.toNat * w.toNat ≤ hdr.lits_len.toNat)
    (hlencap : hdr.lits_len.toNat ≤ hdr.lits_cap.toNat)
    (hcaplen : hdr.lits_cap.toNat ≤ lp0.length)
    (hwf_a : SliceLitsWf hdr lp0 a_off.toNat w.toNat)
    (hmem : (bvHdrMem h hdr ⋆ array64 hdr.aig_ptr aw ⋆
      array (t := i32) hdr.ht_ptr ht ⋆ array (t := i32) hdr.lits_ptr lp0 ⋆ R) m)
    (hafter : ∀ lp' m', lp'.length = lp0.length →
      (∀ p, p < buf0.toNat ∨ buf0.toNat + w.toNat * w.toNat ≤ p →
        lp'.getD p 0#32 = lp0.getD p 0#32) →
      SliceLitsWf hdr lp' buf0.toNat (w.toNat * w.toNat) →
      (∀ ρ, sliceSum g ρ lp' buf0.toNat w.toNat w.toNat =
        (sliceVal g ρ lp0 a_off.toNat w.toNat).cpop) →
      (bvHdrMem h hdr ⋆ array64 hdr.aig_ptr aw ⋆
        array (t := i32) hdr.ht_ptr ht ⋆ array (t := i32) hdr.lits_ptr lp' ⋆ R) m' →
      wp Γ Q X afterExpr m') :
    wp Γ Q X (cpopInitLoopExpr a_off w buf0 ld afterExpr) m := by
  subst hld
  have hpos_aig : 0 < hdr.aig_len.toNat := by rw [hinv.aig_len_eq]; omega
  let Inv : (Nat × List (BitVec 32)) → Mem 64 → Prop := fun st ml =>
    st.1 ≤ w.toNat ∧ st.2.length = lp0.length ∧
    (∀ p, p < buf0.toNat ∨ buf0.toNat + st.1 * w.toNat ≤ p → st.2.getD p 0#32 = lp0.getD p 0#32) ∧
    SliceLitsWf hdr st.2 buf0.toNat (st.1 * w.toNat) ∧
    (∀ j, j < st.1 → ∀ ρ, sliceVal g ρ st.2 (buf0.toNat + j * w.toNat) w.toNat =
      BitVec.ofNat w.toNat ((sliceVal g ρ lp0 a_off.toNat w.toNat).getLsbD j).toNat) ∧
    (bvHdrMem h hdr ⋆ array64 hdr.aig_ptr aw ⋆
      array (t := i32) hdr.ht_ptr ht ⋆ array (t := i32) hdr.lits_ptr st.2 ⋆ R) ml
  dsimp only [cpopInitLoopExpr]
  apply wp_while_state1 (fun st => BitVec.ofNat 32 st.1) (fun st => w.toNat - st.1) Inv
  · intro J hJ
    exact wp_jump_state (proj := fun st : Nat × List (BitVec 32) => (BitVec.ofNat 32 st.1, ()))
      (0, lp0) (by simp) (hJ (0, lp0) m ⟨Nat.zero_le _, rfl, fun _ _ => rfl,
        (by simpa using sliceLitsWf_zero buf0.toNat (by omega)),
        fun _ hk => False.elim (Nat.not_lt_zero _ hk), hmem⟩)
  · intro J st ml ⟨hle, hlen, hpres, hwf_cur, hval_cur, hml⟩ hIH
    rcases st with ⟨i, lp⟩
    dsimp only at hle hlen hpres hwf_cur hval_cur hml
    have hi32 : (BitVec.ofNat 32 i).toNat = i := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    by_cases hlt : i < w.toNat
    · have hiw_lt : i * w.toNat + w.toNat ≤ w.toNat * w.toNat := by
        have hmul : (i + 1) * w.toNat ≤ w.toNat * w.toNat := Nat.mul_le_mul_right _ hlt
        rw [Nat.add_mul, Nat.one_mul] at hmul; exact hmul
      have hrow_eq : BitVec.ofNat 32 i * w = BitVec.ofNat 32 (i * w.toNat) := by
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_mul, hi32, BitVec.toNat_ofNat]
      have hrow_nat : (BitVec.ofNat 32 i * w).toNat = i * w.toNat := by
        rw [hrow_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      have hdst_nat : (buf0 + BitVec.ofNat 32 i * w).toNat = buf0.toNat + i * w.toNat := by
        rw [BitVec.toNat_add, hrow_nat, Nat.mod_eq_of_lt (by omega)]
      have hsrc_nat : (a_off + BitVec.ofNat 32 i).toNat = a_off.toNat + i := by
        rw [BitVec.toNat_add, hi32, Nat.mod_eq_of_lt (by omega)]
      have hsw_dst : (BitVec.setWidth 64 (buf0 + BitVec.ofNat 32 i * w)).toNat =
          buf0.toNat + i * w.toNat := by
        rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by
          have := (buf0 + BitVec.ofNat 32 i * w).isLt; omega), hdst_nat]
      have hsw_src : (BitVec.setWidth 64 (a_off + BitVec.ofNat 32 i)).toNat = a_off.toNat + i := by
        rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by
          have := (a_off + BitVec.ofNat 32 i).isLt; omega), hsrc_nat]
      c0_hfast_nogrp
      · have hsrc_get : lp[(BitVec.setWidth 64 (a_off + BitVec.ofNat 32 i)).toNat] =
            lp0.getD (a_off.toNat + i) 0#32 := by
          have hget : lp[(BitVec.setWidth 64 (a_off + BitVec.ofNat 32 i)).toNat] =
              lp.getD (a_off.toNat + i) 0#32 := by
            simp only [hsw_src]
            simp [List.getD_eq_getElem?_getD, show a_off.toNat + i < lp.length by omega]
          rw [hget]; apply hpres; omega
        let lpInit := lp.set (buf0.toNat + i * w.toNat) (lp0.getD (a_off.toNat + i) 0#32)
        have hm_raw : (array (t := i32) hdr.lits_ptr
            (lp.set (BitVec.setWidth 64 (buf0 + BitVec.ofNat 32 i * w)).toNat
              lp[(BitVec.setWidth 64 (a_off + BitVec.ofNat 32 i)).toNat]) ⋆
            (bvHdrMem h hdr ⋆ (array64 hdr.aig_ptr aw ⋆
              (array (t := i32) hdr.ht_ptr ht ⋆ (R ⋆ Std.ExtHashMap.emp))))) _ := ‹_›
        have hmInit := opMem_of_lits
          (by simpa only [Std.ExtHashMap.sep_emp, ← Std.ExtHashMap.sep_assoc, hsw_dst, hsrc_get]
            using hm_raw)
        apply bv_cpop_init_inner_wp (lp0 := lp) hinv rfl hpos_aig hw1 hlt hrow_eq hrow_nat hw2_32
          hbuf hlencap (by simp only [List.length_set, hlen]; exact hcaplen)
          (by simp only [List.length_set]) ?_ hmInit ?_
        · intro p hp
          have hne : p ≠ buf0.toNat + i * w.toNat := by omega
          exact list_getD_set_ne lp 0#32 _ hne
        · intro lp' m' hlen' hpres' hzero hbit0 hm'
          have hbit0' : lp'.getD (buf0.toNat + i * w.toNat) 0#32 =
              lp0.getD (a_off.toNat + i) 0#32 := by
            rw [hbit0, list_getD_set_self lp 0#32 _ (by omega)]
          have hpres0' : ∀ p, p < buf0.toNat ∨ buf0.toNat + (i + 1) * w.toNat ≤ p →
              lp'.getD p 0#32 = lp0.getD p 0#32 := fun p hp => by
            rw [hpres' p (by
              rcases hp with hp | hp
              · exact Or.inl (by omega)
              · exact Or.inr hp)]
            exact hpres p (by
              rcases hp with hp | hp
              · exact Or.inl hp
              · rw [Nat.add_mul, Nat.one_mul] at hp; exact Or.inr (by omega))
          have hwf' : SliceLitsWf hdr lp' buf0.toNat ((i + 1) * w.toNat) := by
            rw [Nat.add_mul, Nat.one_mul]
            refine ⟨by omega, fun j hj => ?_⟩
            by_cases hji : j < i * w.toNat
            · rw [hpres' (buf0.toNat + j) (Or.inl (by omega))]
              exact hwf_cur.2 j hji
            · have hj_ge : i * w.toNat ≤ j := by omega
              rcases Nat.eq_or_lt_of_le hj_ge with heq | hgt
              · rw [← heq, hbit0']; exact hwf_a.2 i hlt
              · have hk0 : 0 < j - i * w.toNat := by omega
                have hkw : j - i * w.toNat < w.toNat := by omega
                rw [show buf0.toNat + j = buf0.toNat + i * w.toNat + (j - i * w.toNat) from
                    by omega, hzero _ hk0 hkw]
                simpa using hpos_aig
          refine hIH (i + 1, lp') m' (by omega) ⟨by omega, hlen'.trans hlen, hpres0', hwf', ?_, hm'⟩
          intro j hj ρ
          by_cases hji : j = i
          · subst j
            apply BitVec.eq_of_getLsbD_eq
            intro b hb
            rw [sliceVal_getLsbD hb, BitVec.getLsbD_ofNat]
            by_cases hb0 : b = 0
            · subst b
              dsimp only
              rw [Nat.add_zero, hbit0', ← sliceVal_getLsbD hlt]
              cases (sliceVal g ρ lp0 a_off.toNat w.toNat).getLsbD i <;>
                simp [show 0 < w.toNat by omega]
            · have hbpos : 0 < b := Nat.pos_of_ne_zero hb0
              dsimp only
              rw [hzero b hbpos hb, evalLit_zero]
              have hdiv : ((sliceVal g ρ lp0 a_off.toNat w.toNat).getLsbD i).toNat / 2 ^ b = 0 := by
                apply Nat.div_eq_of_lt
                have h1lt : 1 < 2 ^ b := Nat.one_lt_two_pow (by omega)
                cases (sliceVal g ρ lp0 a_off.toNat w.toNat).getLsbD i <;>
                  simp only [Bool.toNat_true, Bool.toNat_false] <;> omega
              simp [Nat.testBit, Nat.shiftRight_eq_div_pow, hdiv]
          · have hjlt : j < i := by omega
            have hval_old := hval_cur j hjlt ρ
            rw [sliceVal_eq_of_agree (fun p hp1 hp2 => by
              have hjm : j * w.toNat + w.toNat ≤ i * w.toNat := by
                have := Nat.mul_le_mul_right w.toNat (show j + 1 ≤ i by omega)
                rw [Nat.add_mul, Nat.one_mul] at this; exact this
              exact hpres' p (Or.inl (by omega)))]
            exact hval_old
      · exfalso; omega
    · have hid : i = w.toNat := by omega
      subst hid
      c0_hfast_nogrp
      · exfalso; omega
      · refine hafter lp ml hlen hpres hwf_cur (fun ρ => ?_) hml
        dsimp only [sliceSum]
        have hfold := sliceSum_cpop_init_aux (sliceVal g ρ lp0 a_off.toNat w.toNat) w.toNat
        have hrange : ∀ k, k ∈ List.range w.toNat →
            sliceVal g ρ lp (buf0.toNat + k * w.toNat) w.toNat =
              BitVec.ofNat w.toNat ((sliceVal g ρ lp0 a_off.toNat w.toNat).getLsbD k).toNat :=
          fun k hk => hval_cur k (List.mem_range.mp hk) ρ
        have hcongr : ∀ (l : List Nat),
            (∀ k ∈ l, sliceVal g ρ lp (buf0.toNat + k * w.toNat) w.toNat =
              BitVec.ofNat w.toNat ((sliceVal g ρ lp0 a_off.toNat w.toNat).getLsbD k).toNat) →
            ∀ acc,
              List.foldl (fun a k => a + sliceVal g ρ lp (buf0.toNat + k * w.toNat) w.toNat) acc l =
              List.foldl (fun a k => a +
                BitVec.ofNat w.toNat ((sliceVal g ρ lp0 a_off.toNat w.toNat).getLsbD k).toNat)
                acc l := by
          intro l hl acc
          induction l generalizing acc with
          | nil => rfl
          | cons k ks ih =>
            simp only [List.foldl_cons, hl k (by simp)]
            exact ih (fun x hx => hl x (by simp [hx])) _
        rw [hcongr _ hrange _, hfold]
        rfl

public theorem bv_cpop_copy_out_wp {Γ : Env}
    (hrel : Γ.Has "bv_lits_release" bvLitsReleaseSpec)
    {h : Val i64} {out_off w cur_in mark1 : BitVec 32} {ld : Val i64}
    {hdr0 hdr : BVHdrState} {g : Aig} {aw : List (BitVec 64)} {ht lp0 : List (BitVec 32)}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [i32]} {X : XPost}
    (hinv : AigInv hdr g aw ht) (hld : ld = hdr.lits_ptr) (ho : hdr.oom = 0#32)
    (hmark1 : mark1 = hdr0.lits_len + w) (hmark_le : mark1.toNat ≤ hdr.lits_len.toNat)
    (hout_eq : out_off = hdr0.lits_len)
    (hout_w : out_off.toNat + w.toNat ≤ hdr.lits_len.toNat)
    (hcur_w : cur_in.toNat + w.toNat ≤ hdr.lits_len.toNat)
    (hlencap : hdr.lits_len.toNat ≤ hdr.lits_cap.toNat)
    (hcaplen : hdr.lits_cap.toNat ≤ lp0.length)
    (hdisj : DisjointSlice out_off.toNat w.toNat cur_in.toNat w.toNat)
    (hwf_cur : SliceLitsWf hdr lp0 cur_in.toNat w.toNat)
    (hmem : (bvHdrMem h hdr ⋆ array64 hdr.aig_ptr aw ⋆
      array (t := i32) hdr.ht_ptr ht ⋆ array (t := i32) hdr.lits_ptr lp0 ⋆ R) m)
    (hpost : ∀ hdr' lp' m',
      hdr.DcBlastFrame hdr' → hdr'.oom = 0#32 → hdr'.aig_len = hdr.aig_len →
      hdr'.lits_len = hdr0.lits_len + w → hdr'.lits_len.toNat ≤ hdr'.lits_cap.toNat →
      lp'.length = lp0.length →
      (∀ p, p < out_off.toNat ∨ out_off.toNat + w.toNat ≤ p → lp'.getD p 0#32 = lp0.getD p 0#32) →
      SliceLitsWf hdr' lp' out_off.toNat w.toNat →
      (∀ ρ, sliceVal g ρ lp' out_off.toNat w.toNat = sliceVal g ρ lp0 cur_in.toNat w.toNat) →
      (bvHdrMem h hdr' ⋆ array64 hdr'.aig_ptr aw ⋆
        array (t := i32) hdr'.ht_ptr ht ⋆ array (t := i32) hdr'.lits_ptr lp' ⋆ R) m' →
      Q (out_off, ()) m') :
    wp Γ Q X (cpopCopyOutLoopExpr h out_off w cur_in mark1 ld) m := by
  subst hld
  have _ := hinv
  let Inv : (Nat × List (BitVec 32)) → Mem 64 → Prop := fun st ml =>
    st.1 ≤ w.toNat ∧ st.2.length = lp0.length ∧
    (∀ p, p < out_off.toNat ∨ out_off.toNat + st.1 ≤ p → st.2.getD p 0#32 = lp0.getD p 0#32) ∧
    (∀ j, j < st.1 → st.2.getD (out_off.toNat + j) 0#32 = lp0.getD (cur_in.toNat + j) 0#32) ∧
    (bvHdrMem h hdr ⋆ array64 hdr.aig_ptr aw ⋆
      array (t := i32) hdr.ht_ptr ht ⋆ array (t := i32) hdr.lits_ptr st.2 ⋆ R) ml
  dsimp only [cpopCopyOutLoopExpr]
  apply wp_while_state1 (fun st => BitVec.ofNat 32 st.1) (fun st => w.toNat - st.1) Inv
  · intro J hJ
    exact wp_jump_state (proj := fun st : Nat × List (BitVec 32) => (BitVec.ofNat 32 st.1, ()))
      (0, lp0) (by simp) (hJ (0, lp0) m ⟨Nat.zero_le _, rfl, fun _ _ => rfl,
        fun _ hk => False.elim (Nat.not_lt_zero _ hk), hmem⟩)
  · intro J st ml ⟨hle, hlen, hpres, hcp, hml⟩ hIH
    rcases st with ⟨idx, lp⟩
    dsimp only at hle hlen hpres hcp hml
    have hi32 : (BitVec.ofNat 32 idx).toNat = idx := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    by_cases hlt : idx < w.toNat
    · have hsi_nat : (cur_in + BitVec.ofNat 32 idx).toNat = cur_in.toNat + idx := by
        rw [BitVec.toNat_add, hi32, Nat.mod_eq_of_lt (by omega)]
      have hdi_nat : (out_off + BitVec.ofNat 32 idx).toNat = out_off.toNat + idx := by
        rw [BitVec.toNat_add, hi32, Nat.mod_eq_of_lt (by omega)]
      have hsw_src : (BitVec.setWidth 64 (cur_in + BitVec.ofNat 32 idx)).toNat =
          cur_in.toNat + idx := by
        rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by
          have := (cur_in + BitVec.ofNat 32 idx).isLt; omega), hsi_nat]
      have hsw_dst : (BitVec.setWidth 64 (out_off + BitVec.ofNat 32 idx)).toNat =
          out_off.toNat + idx := by
        rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by
          have := (out_off + BitVec.ofNat 32 idx).isLt; omega), hdi_nat]
      have hbv1 : BitVec.ofNat 32 idx + 1#32 = BitVec.ofNat 32 (idx + 1) := by
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_add, hi32, show (1#32 : BitVec 32).toNat = 1 from rfl,
          BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      c0_hfast_nogrp
      · rw [hbv1]
        have hsrc_get : lp[(BitVec.setWidth 64 (cur_in + BitVec.ofNat 32 idx)).toNat] =
            lp0.getD (cur_in.toNat + idx) 0#32 := by
          have hget : lp[(BitVec.setWidth 64 (cur_in + BitVec.ofNat 32 idx)).toNat] =
              lp.getD (cur_in.toNat + idx) 0#32 := by
            simp only [hsw_src]
            simp [List.getD_eq_getElem?_getD, show cur_in.toNat + idx < lp.length by omega]
          rw [hget]; apply hpres; unfold DisjointSlice at hdisj; omega
        let lp1 := lp.set (out_off.toNat + idx) (lp0.getD (cur_in.toNat + idx) 0#32)
        refine hIH (idx + 1, lp1) _ (by omega) ⟨by omega, by simp [lp1, hlen], ?_, ?_, ?_⟩
        · intro p hp
          have hne : p ≠ out_off.toNat + idx := by omega
          dsimp only [lp1]; rw [list_getD_set_ne lp 0#32 _ hne]
          exact hpres p (by
            rcases hp with hp | hp
            · exact Or.inl hp
            · exact Or.inr (by omega))
        · intro j hj
          by_cases hji : j = idx
          · subst hji; dsimp only [lp1]; rw [list_getD_set_self lp 0#32 _ (by omega)]
          · have hne : out_off.toNat + j ≠ out_off.toNat + idx := by omega
            dsimp only [lp1]; rw [list_getD_set_ne lp 0#32 _ hne]; exact hcp j (by omega)
        · have hm_raw : (array (t := i32) hdr.lits_ptr
              (lp.set (BitVec.setWidth 64 (out_off + BitVec.ofNat 32 idx)).toNat
                lp[(BitVec.setWidth 64 (cur_in + BitVec.ofNat 32 idx)).toNat]) ⋆
              (bvHdrMem h hdr ⋆ (array64 hdr.aig_ptr aw ⋆
                (array (t := i32) hdr.ht_ptr ht ⋆ (R ⋆ Std.ExtHashMap.emp))))) _ := ‹_›
          refine opMem_of_lits ?_
          simpa only [Std.ExtHashMap.sep_emp, ← Std.ExtHashMap.sep_assoc, hsw_dst, hsrc_get] using
            hm_raw
      · exfalso; omega
    · have hid : idx = w.toNat := by omega
      subst hid
      c0_hfast_nogrp
      · exfalso; omega
      · c0_hcall hrel
        refine ⟨hdr, array64 hdr.aig_ptr aw ⋆ array (t := i32) hdr.ht_ptr ht ⋆
          array (t := i32) hdr.lits_ptr lp ⋆ R,
          (by simpa only [Std.ExtHashMap.sep_assoc] using hml), fun m' hm' => ?_⟩
        dsimp only
        simp only [hmark_le, ↓reduceIte] at hm'
        let hdr' : BVHdrState := { hdr with lits_len := mark1 }
        have hmark1_nat : mark1.toNat = out_off.toNat + w.toNat := by
          rw [hmark1, ← hout_eq, BitVec.toNat_add,
            Nat.mod_eq_of_lt (by have := hdr.lits_len.isLt; omega)]
        c0_hfast_nogrp
        refine hpost hdr' lp m' ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
          rfl, rfl, rfl, rfl, rfl, rfl⟩ ho rfl hmark1 (by dsimp [hdr']; omega) hlen hpres
          ⟨by dsimp [hdr']; omega, fun j hj => by rw [hcp j hj]; exact hwf_cur.2 j hj⟩
          (fun ρ => by
            apply BitVec.eq_of_getLsbD_eq; intro k hk
            rw [sliceVal_getLsbD hk, sliceVal_getLsbD hk, hcp k hk])
          (by simpa only [← Std.ExtHashMap.sep_assoc] using hm')

public theorem bv_cpop_halve_loop_wp {Γ : Env}
    (hlayer : Γ.Has "bv_blast_cpop_layer" bvBlastCpopLayerSpec)
    (hrel : Γ.Has "bv_lits_release" bvLitsReleaseSpec)
    {h : Val i64} {out_off w buf0 buf1 mark0 mark1 : BitVec 32} {ld : Val i64}
    {hdr0 hdrInit : BVHdrState} {gInit : Aig} {awInit : List (BitVec 64)}
    {htInit lpInit lpOrig : List (BitVec 32)}
    {R : Mem 64 → Prop} {mInit : Mem 64} {Q : Post [i32]} {X : XPost}
    (hinvInit : AigInv hdrInit gInit awInit htInit) (hld : ld = hdrInit.lits_ptr)
    (ho : hdrInit.oom = 0#32) (hw1 : 1 < w.toNat) (hw2_32 : w.toNat * w.toNat < 2 ^ 32)
    (hwh_32 : (w.toNat + 1) / 2 * w.toNat < 2 ^ 32)
    (hmark0 : mark0 = hdr0.lits_len) (hmark1 : mark1 = hdr0.lits_len + w)
    (hout_eq : out_off = hdr0.lits_len)
    (hout_w : out_off.toNat + w.toNat ≤ buf0.toNat)
    (hbuf0_w : buf0.toNat + w.toNat * w.toNat ≤ buf1.toNat)
    (hbuf1_w : buf1.toNat + (w.toNat + 1) / 2 * w.toNat ≤ hdrInit.lits_len.toNat)
    (hlencap : hdrInit.lits_len.toNat ≤ hdrInit.lits_cap.toNat)
    (hcaplen : hdrInit.lits_cap.toNat ≤ lpOrig.length)
    (hlenInit : lpInit.length = lpOrig.length)
    (hagreeOrig : ∀ p, p < hdr0.lits_len.toNat → lpInit.getD p 0#32 = lpOrig.getD p 0#32)
    (hwfInit : SliceLitsWf hdrInit lpInit buf0.toNat (w.toNat * w.toNat))
    (hframe0 : hdr0.DcBlastFrame hdrInit)
    (hmemInit : (bvHdrMem h hdrInit ⋆ array64 hdrInit.aig_ptr awInit ⋆
      array (t := i32) hdrInit.ht_ptr htInit ⋆ array (t := i32) hdrInit.lits_ptr lpInit ⋆ R) mInit)
    (hpost : ∀ ret hdr' g' aw' ht' lp' m',
      hdrInit.DcBlastFrame hdr' → gInit ≤ g' →
      g'.nodes.size ≤ gInit.nodes.size + 9 * (w.toNat - 1) * w.toNat →
      AigInv hdr' g' aw' ht' → lp'.length = lpOrig.length →
      (∀ p, p < hdr0.lits_len.toNat → lp'.getD p 0#32 = lpOrig.getD p 0#32) →
      (hdr'.oom = 0#32 → ret = hdr0.lits_len ∧ hdr'.lits_len = hdr0.lits_len + w ∧
        hdr'.lits_len.toNat ≤ hdr'.lits_cap.toNat ∧
        SliceLitsWf hdr' lp' out_off.toNat w.toNat ∧
        ∀ ρ, sliceVal g' ρ lp' out_off.toNat w.toNat =
          sliceSum gInit ρ lpInit buf0.toNat w.toNat w.toNat) →
      (hdr'.oom ≠ 0#32 → ret = 4294967295#32 ∧ hdr'.lits_len = hdr0.lits_len) →
      ((0 < w.toNat → hdr0.lits_ptr ≠ 0#64) →
        gInit.A + 1 + gInit.nodes.size + 9 * (w.toNat - 1) * w.toNat ≤ hdr0.aig_cap.toNat →
        gInit.nodes.size + 9 * (w.toNat - 1) * w.toNat ≤ bvMaxGates → hdr'.oom = 0#32) →
      (bvHdrMem h hdr' ⋆ array64 hdr'.aig_ptr aw' ⋆
        array (t := i32) hdr'.ht_ptr ht' ⋆ array (t := i32) hdr'.lits_ptr lp' ⋆ R) m' →
      Q (ret, ()) m') :
    wp Γ Q X (cpopHalveLoopExpr h out_off w buf0 buf1 mark0 mark1 ld) mInit := by
  subst hld
  have hw_32 : w.toNat < 2 ^ 32 := w.isLt
  have h1w : 1 ≤ w.toNat := by omega
  have hmark1_eq : mark1.toNat = out_off.toNat + w.toNat := by
    rw [hmark1, ← hout_eq, BitVec.toNat_add, Nat.mod_eq_of_lt (by have := buf0.isLt; omega)]
  let Inv : (BitVec 32 × BitVec 32 × Nat × BVHdrState × Aig × List (BitVec 64) ×
      List (BitVec 32) × List (BitVec 32)) → Mem 64 → Prop := fun st ml =>
    let (curIn, curOut, curLen, hdr, g, aw, ht, lp) := st
    1 ≤ curLen ∧ curLen ≤ w.toNat ∧
    hdrInit.AigFrame hdr ∧ gInit ≤ g ∧
    g.nodes.size + 9 * (curLen - 1) * w.toNat ≤ gInit.nodes.size + 9 * (w.toNat - 1) * w.toNat ∧
    AigInv hdr g aw ht ∧ lp.length = lpOrig.length ∧ hdr.oom = 0#32 ∧
    (∀ p, p < hdr0.lits_len.toNat → lp.getD p 0#32 = lpOrig.getD p 0#32) ∧
    ((curIn = buf0 ∧ curOut = buf1) ∨
      (curIn = buf1 ∧ curOut = buf0 ∧ curLen ≤ (w.toNat + 1) / 2)) ∧
    SliceLitsWf hdr lp curIn.toNat (curLen * w.toNat) ∧
    (∀ ρ, sliceSum g ρ lp curIn.toNat curLen w.toNat =
      sliceSum gInit ρ lpInit buf0.toNat w.toNat w.toNat) ∧
    (bvHdrMem h hdr ⋆ array64 hdr.aig_ptr aw ⋆
      array (t := i32) hdr.ht_ptr ht ⋆ array (t := i32) hdr.lits_ptr lp ⋆ R) ml
  dsimp only [cpopHalveLoopExpr]
  refine ProofKit.c0_while_state
    (fun st : BitVec 32 × BitVec 32 × Nat × BVHdrState × Aig × List (BitVec 64) ×
        List (BitVec 32) × List (BitVec 32) =>
      (st.1, st.2.1, BitVec.ofNat 32 st.2.2.1, ()))
    (fun st => st.2.2.1) Inv ?_ ?_
  · intro J hJ
    refine wp_jump_state (proj := fun st : BitVec 32 × BitVec 32 × Nat × BVHdrState × Aig ×
        List (BitVec 64) × List (BitVec 32) × List (BitVec 32) =>
        (st.1, st.2.1, BitVec.ofNat 32 st.2.2.1, ()))
      (buf0, buf1, w.toNat, hdrInit, gInit, awInit, htInit, lpInit) (by simp)
      (hJ (buf0, buf1, w.toNat, hdrInit, gInit, awInit, htInit, lpInit) mInit
        ⟨h1w, Nat.le_refl _, BVHdrState.AigFrame.rfl _, Aig.extends_rfl gInit, Nat.le_refl _,
          hinvInit, hlenInit, ho, hagreeOrig, Or.inl ⟨rfl, rfl⟩, hwfInit, fun _ => rfl, hmemInit⟩)
  · intro J st ml ⟨hge1, hlew, hf, hg, hsz, hinv, hlen, ho_cur, hpres, hbufs, hwf, hsum, hml⟩ hIH
    rcases st with ⟨curIn, curOut, curLen, hdr, g, aw, ht, lp⟩
    dsimp only at hge1 hlew hf hg hsz hinv hlen ho_cur hpres hbufs hwf hsum hml
    have hcl32 : (BitVec.ofNat 32 curLen).toNat = curLen := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    by_cases hgt1 : 1 < curLen
    · have hin_bound : curIn.toNat + curLen * w.toNat ≤ curOut.toNat ∨
          (curIn = buf1 ∧ curOut = buf0 ∧ curLen ≤ (w.toNat + 1) / 2 ∧
            curIn.toNat + curLen * w.toNat ≤ hdr.lits_len.toNat) := by
        rcases hbufs with ⟨rfl, rfl⟩ | ⟨rfl, rfl, hhl⟩
        · left
          have hmul : curLen * w.toNat ≤ w.toNat * w.toNat := Nat.mul_le_mul_right _ hlew
          omega
        · right
          have hmul : curLen * w.toNat ≤ (w.toNat + 1) / 2 * w.toNat := Nat.mul_le_mul_right _ hhl
          rw [hf.lits_len]; exact ⟨rfl, rfl, hhl, by omega⟩
      have hout_bound : curOut.toNat + (curLen + 1) / 2 * w.toNat ≤ curIn.toNat ∨
          (curIn = buf0 ∧ curOut = buf1 ∧
            curOut.toNat + (curLen + 1) / 2 * w.toNat ≤ hdr.lits_len.toNat) := by
        rcases hbufs with ⟨rfl, rfl⟩ | ⟨rfl, rfl, hhl⟩
        · right
          have hmul : (curLen + 1) / 2 * w.toNat ≤ (w.toNat + 1) / 2 * w.toNat :=
            Nat.mul_le_mul_right _ (by omega)
          rw [hf.lits_len]; exact ⟨rfl, rfl, by omega⟩
        · left
          have hmul : (curLen + 1) / 2 * w.toNat ≤ w.toNat * w.toNat :=
            Nat.mul_le_mul_right _ (by omega)
          omega
      have hin32 : curLen * w.toNat < 2 ^ 32 := by
        have hmul : curLen * w.toNat ≤ w.toNat * w.toNat := Nat.mul_le_mul_right _ hlew
        omega
      have hout32 : (curLen + 1) / 2 * w.toNat < 2 ^ 32 := by
        have hmul : (curLen + 1) / 2 * w.toNat ≤ (w.toNat + 1) / 2 * w.toNat :=
          Nat.mul_le_mul_right _ (by omega)
        omega
      have hin_hdr : curIn.toNat + curLen * w.toNat ≤ hdr.lits_len.toNat := by
        rcases hin_bound with h1 | ⟨_, _, _, h2⟩
        · rcases hbufs with ⟨rfl, rfl⟩ | ⟨rfl, rfl, _⟩ <;> rw [hf.lits_len] <;> omega
        · exact h2
      have hout_hdr : curOut.toNat + (curLen + 1) / 2 * w.toNat ≤ hdr.lits_len.toNat := by
        rcases hout_bound with h1 | ⟨_, _, h2⟩
        · rcases hbufs with ⟨rfl, rfl⟩ | ⟨rfl, rfl, _⟩ <;> rw [hf.lits_len] <;> omega
        · exact h2
      have hdisj_co : DisjointSlice curOut.toNat ((curLen + 1) / 2 * w.toNat)
          curIn.toNat (curLen * w.toNat) := by
        unfold DisjointSlice
        rcases hbufs with ⟨rfl, rfl⟩ | ⟨rfl, rfl, hhl⟩
        · right
          have hmul : curLen * w.toNat ≤ w.toNat * w.toNat := Nat.mul_le_mul_right _ hlew
          omega
        · left
          have hmul : (curLen + 1) / 2 * w.toNat ≤ w.toNat * w.toNat :=
            Nat.mul_le_mul_right _ (by omega)
          omega
      c0_hfast_nogrp
      · c0_hcall hlayer
        refine ⟨hdr, g, aw, ht, lp, R, hinv, (by rw [hf.lits_cap, hlen]; exact hcaplen),
          fun _ _ _ _ _ _ _ _ => ⟨by rwa [hcl32], by rw [hcl32]; exact hdisj_co⟩, hml, ?_⟩
        intro ret hdr' g' aw' ht' lp' m' hf' hg' hsz' hinv' hlen' hpres' hoom'
          hret_iff hbound' hval' hm'
        rw [hcl32] at hsz' hpres' hbound' hval'
        have hf0' := hf.trans hf'
        have hg0' := Aig.extends_trans hg hg'
        have hlen0' : lp'.length = lpOrig.length := hlen'.trans hlen
        have hpres0' : ∀ p, p < hdr0.lits_len.toNat → lp'.getD p 0#32 = lpOrig.getD p 0#32 :=
          fun p hp => by
            have hout_ge : hdr0.lits_len.toNat ≤ curOut.toNat := by
              rw [← hout_eq]
              rcases hbufs with ⟨_, rfl⟩ | ⟨_, rfl, _⟩ <;> omega
            rw [hpres' p (Or.inl (by omega))]
            exact hpres p hp
        have hbud : (curLen / 2) * (9 * w.toNat) + 9 * ((curLen + 1) / 2 - 1) * w.toNat =
            9 * (curLen - 1) * w.toNat := by
          have hid := cpop_gates_halving curLen hge1
          rw [← Nat.mul_assoc (curLen / 2) 9 w.toNat, Nat.mul_comm (curLen / 2) 9,
            Nat.mul_assoc 9 (curLen / 2) w.toNat, Nat.mul_assoc 9 ((curLen + 1) / 2 - 1) w.toNat,
            Nat.mul_assoc 9 (curLen - 1) w.toNat, ← Nat.mul_add, ← Nat.add_mul, hid]
        by_cases hok : ret = true
        · subst hok
          have ho' : hdr'.oom = 0#32 := hret_iff.mp rfl
          obtain ⟨hwf_next, hval_next⟩ := hval' rfl
          have hsz_next : g'.nodes.size + 9 * ((curLen + 1) / 2 - 1) * w.toNat ≤
              gInit.nodes.size + 9 * (w.toNat - 1) * w.toNat := by omega
          have hbufs_next : (curOut = buf0 ∧ curIn = buf1) ∨
              (curOut = buf1 ∧ curIn = buf0 ∧ (curLen + 1) / 2 ≤ (w.toNat + 1) / 2) := by
            rcases hbufs with ⟨rfl, rfl⟩ | ⟨rfl, rfl, _⟩
            · right; exact ⟨rfl, rfl, by omega⟩
            · left; exact ⟨rfl, rfl⟩
          have htrunc_bv : BitVec.setWidth 32 ((BitVec.setWidth 64 (BitVec.ofNat 32 curLen) +
              1#64) >>> OfNat.ofNat 1) = BitVec.ofNat 32 ((curLen + 1) / 2) := by
            apply BitVec.eq_of_toNat_eq
            have hze : (BitVec.setWidth 64 (BitVec.ofNat 32 curLen)).toNat = curLen := by
              rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by
                have := (BitVec.ofNat 32 curLen).isLt; omega), hcl32]
            have hcur1 : curLen + 1 < 2 ^ 64 := by have := w.isLt; omega
            have hhalf : (curLen + 1) / 2 < 2 ^ 32 := by have := w.isLt; omega
            rw [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
              BitVec.toNat_add, hze, show (1#64 : BitVec 64).toNat = 1 from rfl,
              Nat.mod_eq_of_lt hcur1, Nat.shiftRight_eq_div_pow,
              show (2 : Nat) ^ (OfNat.ofNat 1 : Nat) = 2 from rfl,
              Nat.mod_eq_of_lt hhalf, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hhalf]
          c0_hfast_nogrp
          · rw [htrunc_bv]
            refine hIH (curOut, curIn, (curLen + 1) / 2, hdr', g', aw', ht', lp') m'
              (cpop_next_len_lt hgt1)
              ⟨by omega, by omega, hf0', hg0', hsz_next, hinv', hlen0', ho', hpres0',
                hbufs_next, hwf_next, fun ρ => by rw [hval_next ρ, hsum ρ], hm'⟩
          · simp at ‹_›
        · have hretf : ret = false := by cases ret <;> simp_all
          subst hretf
          have hoom' : hdr'.oom ≠ 0#32 := fun hz => by cases hret_iff.mpr hz
          c0_hfast_nogrp
          · simp at ‹_›
          · c0_hcall hrel
            have hmark0_le : mark0.toNat ≤ hdr'.lits_len.toNat := by
              rw [hmark0, hf'.lits_len, hf.lits_len, ← hout_eq]; omega
            refine ⟨hdr', array64 hdr'.aig_ptr aw' ⋆ array (t := i32) hdr'.ht_ptr ht' ⋆
              array (t := i32) hdr'.lits_ptr lp' ⋆ R,
              (by simpa only [Std.ExtHashMap.sep_assoc] using hm'), fun m'' hm'' => ?_⟩
            dsimp only
            simp only [hmark0_le, ↓reduceIte] at hm''
            let hdr'' : BVHdrState := { hdr' with lits_len := mark0 }
            c0_hfast_nogrp
            have hf0'' : hdrInit.DcBlastFrame hdr'' :=
              hf0'.toDcBlastFrame.trans ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
                rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
            have hinv'' : AigInv hdr'' g' aw' ht' :=
              aigInv_with_lits_len_oom hinv' mark0 hdr'.oom
            refine hpost 4294967295#32 hdr'' g' aw' ht' lp' m'' hf0'' hg0' (by omega) hinv''
              hlen0' hpres0' (fun h0 => absurd h0 hoom') (fun _ => ⟨rfl, hmark0⟩)
              (fun hptr haig hgmax => ?_)
              (by simpa only [← Std.ExtHashMap.sep_assoc] using hm'')
            have hA : gInit.A = g.A := hg.1
            have hptr' : (0 < curLen * w.toNat → hdr.lits_ptr ≠ 0#64) ∧
                (0 < (curLen + 1) / 2 * w.toNat → hdr.lits_ptr ≠ 0#64) :=
              ⟨fun _ => by rw [hf.lits_ptr, hframe0.lits_ptr]; exact hptr (by omega),
               fun _ => by rw [hf.lits_ptr, hframe0.lits_ptr]; exact hptr (by omega)⟩
            have ho_ok := hbound' ho_cur (by rw [hf.lits_cap, hf.lits_len]; exact hlencap)
              hin32 hout32 hptr'.1 hptr'.2 hin_hdr hout_hdr
              (by rw [hf.aig_cap, hframe0.aig_cap, ← hA]; omega) (by omega)
            exact absurd ho_ok hoom'
      · exfalso; omega
    · have hid : curLen = 1 := by omega
      subst hid
      c0_hfast_nogrp
      · exfalso; omega
      · have hcur_w : curIn.toNat + w.toNat ≤ hdr.lits_len.toNat := by
          rcases hbufs with ⟨rfl, rfl⟩ | ⟨rfl, rfl, hhl⟩
          · have hmul : 1 * w.toNat ≤ w.toNat * w.toNat := Nat.mul_le_mul_right _ h1w
            rw [hf.lits_len]; omega
          · have hmul : 1 * w.toNat ≤ (w.toNat + 1) / 2 * w.toNat :=
              Nat.mul_le_mul_right _ (by omega)
            rw [hf.lits_len]; omega
        have hdisj_out : DisjointSlice out_off.toNat w.toNat curIn.toNat w.toNat := by
          unfold DisjointSlice
          rcases hbufs with ⟨rfl, rfl⟩ | ⟨rfl, rfl, _⟩ <;> left <;> omega
        have hout_w_hdr : out_off.toNat + w.toNat ≤ hdr.lits_len.toNat := by
          rw [hf.lits_len]; omega
        have hmark1_le : mark1.toNat ≤ hdr.lits_len.toNat := by omega
        apply bv_cpop_copy_out_wp hrel hinv (by rw [hf.lits_ptr]) ho_cur hmark1 hmark1_le
          hout_eq hout_w_hdr hcur_w (by rw [hf.lits_len, hf.lits_cap]; exact hlencap)
          (by rw [hf.lits_cap, hlen]; exact hcaplen) hdisj_out (by simpa using hwf) hml
        intro hdr' lp' m' hf' ho' haig' hlen_eq hcap' hlp_len hpres' hwf' hval' hm'
        have hpres0' : ∀ p, p < hdr0.lits_len.toNat → lp'.getD p 0#32 = lpOrig.getD p 0#32 :=
          fun p hp => by
            rw [hpres' p (Or.inl (by rw [hout_eq]; exact hp))]
            exact hpres p hp
        have hframe_tot : hdrInit.DcBlastFrame hdr' :=
          hf.toDcBlastFrame.trans hf'
        have hinv' : AigInv hdr' g aw ht := aigInv_of_dcBlastFrame hinv hf' haig'
        refine hpost out_off hdr' g aw ht lp' m' hframe_tot hg (by simpa using hsz) hinv'
          (hlp_len.trans hlen) hpres0' (fun _ => ⟨hout_eq, hlen_eq, hcap', hwf', fun ρ => by
            rw [hval' ρ, ← sliceSum_one, ← hsum ρ]⟩)
          (fun hne => absurd ho' hne) (fun _ _ _ => ho') hm'

end

end LeanQbe.T.Examples.Bitblast.Proof.OpsDivCpop
