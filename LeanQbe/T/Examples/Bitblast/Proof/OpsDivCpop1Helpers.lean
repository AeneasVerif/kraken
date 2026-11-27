module

public import LeanQbe.T.Examples.Bitblast.Proof.OpsDivCpopHelpers
import LeanQbe.T.Examples.Bitblast.Proof.OpsDivCpop0
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import LeanQbe.T.Logic.ProofKit
import LeanQbe.T.Logic.Rules

set_option autoImplicit false

namespace LeanQbe.T.Examples.Bitblast.Proof.OpsDivCpop

open LeanQbe.T
open LeanQbe.T.Examples.Bitblast.Src.OpsDivCpop
open LeanQbe.T.Examples.Bitblast.Ref

/-!
## Modular Helpers for Division / Modulo (`OpsDivCpop1Helpers`)

Shared bitvector, memory, and loop `wp` lemmas for `bv_blast_udiv_umod`.
-/

public theorem evalLit_extend_of_inv {hdr : BVHdrState} {g g' : Aig}
    {aw : List (BitVec 64)} {ht : List (BitVec 32)} {v : BitVec 32} {ρ : Nat → Bool}
    (hinv : AigInv hdr g aw ht) (hle : g ≤ g') (hlt : (v >>> 1).toNat < hdr.aig_len.toNat) :
    g'.evalLit ρ (UInt32.ofBitVec v) = g.evalLit ρ (UInt32.ofBitVec v) := by
  have h1 : (v >>> 1).toNat < g.A + 1 + g.nodes.size := by
    rw [← hinv.aig_len_eq]; exact hlt
  exact Aig.evalLit_extend hle (lit_toNat_lt_of_shift h1)

public theorem aig_len_pos_of_inv {hdr : BVHdrState} {g : Aig}
    {aw : List (BitVec 64)} {ht : List (BitVec 32)}
    (hinv : AigInv hdr g aw ht) : 0 < hdr.aig_len.toNat := by
  rw [hinv.aig_len_eq]; omega

public theorem aigLen_le_of_inv_le {hdr hdr' : BVHdrState} {g g' : Aig}
    {aw aw' : List (BitVec 64)} {ht ht' : List (BitVec 32)}
    (hinv : AigInv hdr g aw ht) (hinv' : AigInv hdr' g' aw' ht') (hle : g ≤ g') :
    hdr.aig_len.toNat ≤ hdr'.aig_len.toNat := by
  rw [hinv.aig_len_eq, hinv'.aig_len_eq]
  have hA : g.A = g'.A := hle.1
  have hnd : g.nodes.size ≤ g'.nodes.size := hle.2.1
  omega

public theorem sliceVal_extend {hdr : BVHdrState} {g g' : Aig}
    {aw : List (BitVec 64)} {ht lp : List (BitVec 32)} {off w : Nat} {ρ : Nat → Bool}
    (hinv : AigInv hdr g aw ht) (hle : g ≤ g') (hwf : SliceLitsWf hdr lp off w) :
    sliceVal g' ρ lp off w = sliceVal g ρ lp off w := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [sliceVal_getLsbD hj, sliceVal_getLsbD hj]
  exact evalLit_extend_of_inv hinv hle (hwf.2 j hj)

public theorem sliceVal_zero_of_all {g : Aig} {ρ : Nat → Bool}
    {lp : List (BitVec 32)} {off w : Nat}
    (hz : ∀ j, j < w → lp.getD (off + j) 0#32 = 0#32) :
    sliceVal g ρ lp off w = 0#w := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [sliceVal_getLsbD hj, hz j hj, evalLit_zero, BitVec.getLsbD_zero]

public theorem sliceLitsWf_zero_of_all {hdr : BVHdrState} {lp : List (BitVec 32)} {off w : Nat}
    (hpos : 0 < hdr.aig_len.toNat) (hb : off + w ≤ hdr.lits_len.toNat)
    (hz : ∀ j, j < w → lp.getD (off + j) 0#32 = 0#32) :
    SliceLitsWf hdr lp off w := by
  refine ⟨hb, fun j hj => ?_⟩
  rw [hz j hj]
  simpa using hpos

public theorem sliceLitsWf_of_agree {hdr : BVHdrState} {lp lp' : List (BitVec 32)}
    {off w : Nat}
    (hagree : ∀ p, off ≤ p → p < off + w → lp'.getD p 0#32 = lp.getD p 0#32)
    (hwf : SliceLitsWf hdr lp off w) :
    SliceLitsWf hdr lp' off w := by
  refine ⟨hwf.1, fun j hj => ?_⟩
  rw [hagree (off + j) (by omega) (by omega)]
  exact hwf.2 j hj

public theorem sliceLitsWf_of_inv_le {hdr hdr' : BVHdrState} {g g' : Aig}
    {aw aw' : List (BitVec 64)} {ht ht' lp lp' : List (BitVec 32)} {off w : Nat}
    (hinv : AigInv hdr g aw ht) (hinv' : AigInv hdr' g' aw' ht')
    (hle : g ≤ g') (hlen : hdr.lits_len.toNat ≤ hdr'.lits_len.toNat)
    (hwf : SliceLitsWf hdr lp off w)
    (hagree : ∀ p, off ≤ p → p < off + w → lp'.getD p 0#32 = lp.getD p 0#32) :
    SliceLitsWf hdr' lp' off w :=
  sliceLitsWf_mono hwf (aigLen_le_of_inv_le hinv hinv' hle) hlen hagree

public theorem getD_set_eq {α : Type _} (xs : List α) (i j : Nat) (v d : α)
    (hi : i < xs.length) :
    (xs.set i v).getD j d = if j = i then v else xs.getD j d := by
  by_cases hji : j = i
  · subst hji
    simp only [↓reduceIte, List.getD_eq_getElem?_getD, List.getElem?_set_self (by omega),
      Option.getD_some]
  · simp only [hji, ↓reduceIte, List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm hji)]

public theorem getD_set_ne {α : Type _} (xs : List α) (i j : Nat) (v d : α)
    (hji : j ≠ i) :
    (xs.set i v).getD j d = xs.getD j d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm hji)]

public theorem blastFrame_with_lits_len (hdr : BVHdrState) (len : BitVec 32) :
    hdr.DcBlastFrame { hdr with lits_len := len } :=
  { work_base := rfl, work_end := rfl, prog_ptr := rfl, aig_ptr := rfl,
    ht_ptr := rfl, atom_base_ptr := rfl, slice_off_ptr := rfl, lits_ptr := rfl,
    marks_ptr := rfl, dimacs_start := rfl, n_vars := rfl, n_nodes := rfl,
    n_cwords := rfl, root_node := rfl, num_atoms := rfl, aig_cap := rfl,
    ht_mask := rfl, lits_cap := rfl, dimacs_len := rfl }

private theorem step_mul_12_add {base step w k : Nat}
    (h : k ≤ base + step * (12 * w) + 9 * w + 3 * w) :
    k ≤ base + (step + 1) * (12 * w) := by
  have hs : (step + 1) * (12 * w) = step * (12 * w) + 12 * w := Nat.succ_mul step (12 * w)
  omega

private theorem step_mul_12_le {step w : Nat} (hlt : step < w) :
    step * (12 * w) + 12 * w ≤ 12 * w * w := by
  have hs : step * (12 * w) + 12 * w = (step + 1) * (12 * w) :=
    (Nat.succ_mul step (12 * w)).symm
  have h1 : (step + 1) * (12 * w) ≤ w * (12 * w) := Nat.mul_le_mul_right _ hlt
  have h2 : w * (12 * w) = 12 * w * w := by
    rw [Nat.mul_comm w (12 * w), Nat.mul_assoc]
  omega

private theorem mem_hdr_to_u32 {h : Val i64} {hdr : BVHdrState} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (bvHdrMem h hdr ⋆ R) m) :
    (array (t := i32) (h + 80#64) hdr.u32s ⋆ (array64 h hdr.u64s ⋆ R)) m := by
  dsimp only [bvHdrMem] at hm
  rw [Std.ExtHashMap.sep_comm (array64 h hdr.u64s)] at hm
  rwa [Std.ExtHashMap.sep_assoc] at hm

private theorem mem_hdr_of_u32 {h : Val i64} {hdr : BVHdrState} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (array (t := i32) (h + 80#64) hdr.u32s ⋆ (array64 h hdr.u64s ⋆ R)) m) :
    (bvHdrMem h hdr ⋆ R) m := by
  dsimp only [bvHdrMem]
  rw [← Std.ExtHashMap.sep_assoc] at hm
  rw [Std.ExtHashMap.sep_comm (array (t := i32) (h + 80#64) hdr.u32s) (array64 h hdr.u64s)] at hm
  exact hm

private theorem mem_hdr_to_u64 {h : Val i64} {hdr : BVHdrState} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (bvHdrMem h hdr ⋆ R) m) :
    (array64 h hdr.u64s ⋆ (array (t := i32) (h + 80#64) hdr.u32s ⋆ R)) m := by
  dsimp only [bvHdrMem] at hm
  rwa [Std.ExtHashMap.sep_assoc] at hm

private theorem u32s_set_oom (hdr : BVHdrState) (v : BitVec 32) :
    hdr.u32s.set 10 v = ({ hdr with oom := v }).u32s := rfl

public theorem wp_load_hdr_oom {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {h : Val i64} {hdr : BVHdrState}
    {aw : List (BitVec 64)} {ht lp : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64}
    {k : Val i32 → Expr Val Cont rs}
    (hm : (bvHdrMem h hdr ⋆ array64 hdr.aig_ptr aw ⋆
      array (t := i32) hdr.ht_ptr ht ⋆ array (t := i32) hdr.lits_ptr lp ⋆ R) m)
    (hk : wp Γ Q X (k hdr.oom) m) :
    wp Γ Q X
      (Expr.let_ (op2 (OpCode.add i64) (Arg.var h) (Arg.imm (t := i64) 120#64)) fun p_addr =>
        Expr.load i32 (Arg.var p_addr.fst) k) m := by
  c0_hfast_nogrp
  exact hk

public theorem wp_store_hdr_oom {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {h : Val i64} {hdr : BVHdrState}
    {aw : List (BitVec 64)} {ht lp : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64}
    {k : Expr Val Cont rs}
    (hm : (bvHdrMem h hdr ⋆ array64 hdr.aig_ptr aw ⋆
      array (t := i32) hdr.ht_ptr ht ⋆ array (t := i32) hdr.lits_ptr lp ⋆ R) m)
    (hk : ∀ m', (bvHdrMem h { hdr with oom := 1#32 } ⋆ array64 hdr.aig_ptr aw ⋆
      array (t := i32) hdr.ht_ptr ht ⋆ array (t := i32) hdr.lits_ptr lp ⋆ R) m' →
      wp Γ Q X k m') :
    wp Γ Q X
      (Expr.let_ (op2 (OpCode.add i64) (Arg.var h) (Arg.imm (t := i64) 120#64)) fun p_addr =>
        Expr.store (t := i32) (Arg.imm 1#32) (Arg.var p_addr.fst) k) m := by
  c0_hfast_nogrp
  exact hk m (by simpa only [Std.ExtHashMap.sep_emp, ← Std.ExtHashMap.sep_assoc] using hm)

public theorem wp_load_hdr_lits_ptr {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {h : Val i64} {hdr : BVHdrState}
    {aw : List (BitVec 64)} {ht lp : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64}
    {k : Val i64 → Expr Val Cont rs}
    (hm : (bvHdrMem h hdr ⋆ array64 hdr.aig_ptr aw ⋆
      array (t := i32) hdr.ht_ptr ht ⋆ array (t := i32) hdr.lits_ptr lp ⋆ R) m)
    (hk : wp Γ Q X (k hdr.lits_ptr) m) :
    wp Γ Q X
      (Expr.let_ (op2 (OpCode.add i64) (Arg.var h) (Arg.imm (t := i64) 56#64)) fun p_addr =>
        Expr.load i64 (Arg.var p_addr.fst) k) m := by
  c0_hfast_nogrp
  exact hk

private theorem wp_load_lits {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {h : Val i64} {hdr : BVHdrState}
    {aw : List (BitVec 64)} {ht lp : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64}
    {idx : BitVec 32} {a : Arg Val i64} {k : Val i32 → Expr Val Cont rs}
    (hm : (bvHdrMem h hdr ⋆ array64 hdr.aig_ptr aw ⋆
      array (t := i32) hdr.ht_ptr ht ⋆ array (t := i32) hdr.lits_ptr lp ⋆ R) m)
    (ha : a.val = hdr.lits_ptr + BitVec.zeroExtend 64 idx * 4#64)
    (hlt : idx.toNat < lp.length)
    (hk : wp Γ Q X (k (lp.getD idx.toNat 0#32)) m) :
    wp Γ Q X (Expr.load i32 a k) m := by
  have hby : (i32 : Ty).bytes = 4 := rfl
  have ha' : a.val = hdr.lits_ptr + BitVec.ofNat 64 (Ty.bytes i32 * idx.toNat) := by
    rw [ha, hby]; congr 1; bv_omega
  apply wp_load_array (i := idx.toNat) (by decide) ha' hlt (opMem_to_lits hm)
  have hget : lp[idx.toNat] = lp.getD idx.toNat 0#32 := by
    simp [List.getD_eq_getElem?_getD, hlt]
  rwa [hget]

private theorem wp_store_lits {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {h : Val i64} {hdr : BVHdrState}
    {aw : List (BitVec 64)} {ht lp : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64}
    {idx : BitVec 32} {v : Arg Val i32} {a : Arg Val i64} {k : Expr Val Cont rs}
    (hm : (bvHdrMem h hdr ⋆ array64 hdr.aig_ptr aw ⋆
      array (t := i32) hdr.ht_ptr ht ⋆ array (t := i32) hdr.lits_ptr lp ⋆ R) m)
    (ha : a.val = hdr.lits_ptr + BitVec.zeroExtend 64 idx * 4#64)
    (hlt : idx.toNat < lp.length)
    (hk : ∀ m', (bvHdrMem h hdr ⋆ array64 hdr.aig_ptr aw ⋆ array (t := i32) hdr.ht_ptr ht ⋆
        array (t := i32) hdr.lits_ptr (lp.set idx.toNat v.val) ⋆ R) m' →
      wp Γ Q X k m') :
    wp Γ Q X (Expr.store (t := i32) v a k) m := by
  have hby : (i32 : Ty).bytes = 4 := rfl
  have ha' : a.val = hdr.lits_ptr + BitVec.ofNat 64 (Ty.bytes i32 * idx.toNat) := by
    rw [ha, hby]; congr 1; bv_omega
  apply wp_store_array (i := idx.toNat) (by decide) ha' hlt (opMem_to_lits hm)
  intro m' hm'
  exact hk m' (opMem_of_lits hm')

public abbrev udivRelRetExpr (h : Val i64) (mark0 : Val i32) : Expr Val Cont [i32] :=
  Expr.call (as := [i64, i32]) (bs := []) "bv_lits_release"
    (Arg.var h, Arg.var mark0, ()) fun _ =>
    Expr.ret (Arg.imm (t := i32) 0xFFFFFFFF#32, ())

public abbrev udivZeroLoopExpr (w q_off r_off : Val i32) (ld : Val i64)
    (exitExpr : Tup Val [i32] → Expr Val Cont [i32]) : Expr Val Cont [i32] :=
  Expr.group
    (fun Js => Blocks.cons
      (fun p_24 : Tup Val [i32] =>
        Expr.let_ (op2 (OpCode.cmp CmpOp.ult i32 Ty.bool (by decide))
          (Arg.var p_24.fst) (Arg.var w)) fun p_25 =>
        Expr.jnz (Arg.var p_25.fst)
          (Expr.let_ (op2 (OpCode.add i32) (Arg.var q_off) (Arg.var p_24.fst)) fun p =>
            Expr.let_ (op1 (OpCode.zext 32 64) (Arg.var p.fst)) fun p =>
            Expr.let_ (op2 (OpCode.mul i64) (Arg.var p.fst) (Arg.imm 4#64)) fun p =>
            Expr.let_ (op2 (OpCode.add i64) (Arg.var ld) (Arg.var p.fst)) fun p =>
            Expr.store (Arg.imm (t := i32) 0#32) (Arg.var p.fst)
              (Expr.let_ (op2 (OpCode.add i32) (Arg.var r_off) (Arg.var p_24.fst)) fun p =>
                Expr.let_ (op1 (OpCode.zext 32 64) (Arg.var p.fst)) fun p =>
                Expr.let_ (op2 (OpCode.mul i64) (Arg.var p.fst) (Arg.imm 4#64)) fun p =>
                Expr.let_ (op2 (OpCode.add i64) (Arg.var ld) (Arg.var p.fst)) fun p =>
                Expr.store (Arg.imm (t := i32) 0#32) (Arg.var p.fst)
                  (Expr.let_ (op2 (OpCode.add i32) (Arg.var p_24.fst) (Arg.imm 1#32)) fun p =>
                    Expr.jump Js.fst (Arg.var p.fst, ()))))
          (exitExpr p_24))
      Blocks.nil)
    (fun Js => Expr.jump Js.fst (Arg.imm 0#32, ()))

public abbrev udivShiftRprimeExpr (w r_off rp_off : Val i32) (ld : Val i64)
    (exitExpr : Tup Val [i32] → Expr Val Cont [i32]) : Expr Val Cont [i32] :=
  Expr.group
    (fun Js_1 => Blocks.cons
      (fun p_40 : Tup Val [i32] =>
        Expr.let_ (op2 (OpCode.cmp CmpOp.ult i32 Ty.bool (by decide))
          (Arg.var p_40.fst) (Arg.var w)) fun p_41 =>
        Expr.jnz (Arg.var p_41.fst)
          (Expr.let_ (op2 (OpCode.add i32) (Arg.var rp_off) (Arg.var p_40.fst)) fun p =>
            Expr.let_ (op1 (OpCode.zext 32 64) (Arg.var p.fst)) fun p =>
            Expr.let_ (op2 (OpCode.mul i64) (Arg.var p.fst) (Arg.imm 4#64)) fun p =>
            Expr.let_ (op2 (OpCode.add i64) (Arg.var ld) (Arg.var p.fst)) fun p =>
            Expr.let_ (op2 (OpCode.add i32) (Arg.var r_off) (Arg.var p_40.fst)) fun p_42 =>
            Expr.let_ (op2 (OpCode.sub i32) (Arg.var p_42.fst) (Arg.imm 1#32)) fun p_43 =>
            Expr.let_ (op1 (OpCode.zext 32 64) (Arg.var p_43.fst)) fun p_44 =>
            Expr.let_ (op2 (OpCode.mul i64) (Arg.var p_44.fst) (Arg.imm 4#64)) fun p_45 =>
            Expr.let_ (op2 (OpCode.add i64) (Arg.var ld) (Arg.var p_45.fst)) fun p_46 =>
            Expr.load i32 (Arg.var p_46.fst) fun ld_v =>
            Expr.store (Arg.var ld_v) (Arg.var p.fst)
              (Expr.let_ (op2 (OpCode.add i32) (Arg.var p_40.fst) (Arg.imm 1#32)) fun p =>
                Expr.jump Js_1.fst (Arg.var p.fst, ())))
          (exitExpr p_40))
      Blocks.nil)
    (fun Js_1 => Expr.jump Js_1.fst (Arg.imm 1#32, ()))

public abbrev udivShiftQExpr (q_off w1 : Val i32) (ld : Val i64)
    (exitExpr : Expr Val Cont [i32]) : Expr Val Cont [i32] :=
  Expr.group
    (fun Js_2 => Blocks.cons
      (fun p : Tup Val [i32] =>
        Expr.let_ (op2 (OpCode.cmp CmpOp.ugt i32 Ty.bool (by decide))
          (Arg.var p.fst) (Arg.imm 0#32)) fun p_46 =>
        Expr.jnz (Arg.var p_46.fst)
          (Expr.let_ (op2 (OpCode.add i32) (Arg.var q_off) (Arg.var p.fst)) fun p_47 =>
            Expr.let_ (op1 (OpCode.zext 32 64) (Arg.var p_47.fst)) fun p_48 =>
            Expr.let_ (op2 (OpCode.mul i64) (Arg.var p_48.fst) (Arg.imm 4#64)) fun p_49 =>
            Expr.let_ (op2 (OpCode.add i64) (Arg.var ld) (Arg.var p_49.fst)) fun p_50 =>
            Expr.let_ (op2 (OpCode.add i32) (Arg.var q_off) (Arg.var p.fst)) fun p_51 =>
            Expr.let_ (op2 (OpCode.sub i32) (Arg.var p_51.fst) (Arg.imm 1#32)) fun p_52 =>
            Expr.let_ (op1 (OpCode.zext 32 64) (Arg.var p_52.fst)) fun p_53 =>
            Expr.let_ (op2 (OpCode.mul i64) (Arg.var p_53.fst) (Arg.imm 4#64)) fun p_54 =>
            Expr.let_ (op2 (OpCode.add i64) (Arg.var ld) (Arg.var p_54.fst)) fun p_55 =>
            Expr.load i32 (Arg.var p_55.fst) fun ld_v =>
            Expr.store (Arg.var ld_v) (Arg.var p_50.fst)
              (Expr.let_ (op2 (OpCode.sub i32) (Arg.var p.fst) (Arg.imm 1#32)) fun p =>
                Expr.jump Js_2.fst (Arg.var p.fst, ())))
          exitExpr)
      Blocks.nil)
    (fun Js_2 => Expr.jump Js_2.fst (Arg.var w1, ()))

public abbrev udivZeroRprimeExpr (w rp_off : Val i32) (ld : Val i64)
    (exitExpr : Tup Val [i32] → Expr Val Cont [i32]) : Expr Val Cont [i32] :=
  Expr.group
    (fun Js_1 => Blocks.cons
      (fun p_32 : Tup Val [i32] =>
        Expr.let_ (op2 (OpCode.cmp CmpOp.ult i32 Ty.bool (by decide))
          (Arg.var p_32.fst) (Arg.var w)) fun p_33 =>
        Expr.jnz (Arg.var p_33.fst)
          (Expr.let_ (op2 (OpCode.add i32) (Arg.var rp_off) (Arg.var p_32.fst)) fun p =>
            Expr.let_ (op1 (OpCode.zext 32 64) (Arg.var p.fst)) fun p =>
            Expr.let_ (op2 (OpCode.mul i64) (Arg.var p.fst) (Arg.imm 4#64)) fun p =>
            Expr.let_ (op2 (OpCode.add i64) (Arg.var ld) (Arg.var p.fst)) fun p =>
            Expr.store (Arg.imm (t := i32) 0#32) (Arg.var p.fst)
              (Expr.let_ (op2 (OpCode.add i32) (Arg.var p_32.fst) (Arg.imm 1#32)) fun p =>
                Expr.jump Js_1.fst (Arg.var p.fst, ())))
          (exitExpr p_32))
      Blocks.nil)
    (fun Js_1 => Expr.jump Js_1.fst (Arg.imm 0#32, ()))

public abbrev udivStepIterExpr (h : Val i64)
    (n_off d_off w mark0 q_off r_off rp_off diff_off step_bv : Val i32)
    (ld : Val i64) (J : Cont [i32, i32]) : Expr Val Cont [i32] :=
  Expr.let_ (op2 (OpCode.sub i32) (Arg.var w) (Arg.imm 1#32)) fun p_31 =>
  Expr.let_ (op2 (OpCode.sub i32) (Arg.var p_31.fst) (Arg.var step_bv)) fun p_32 =>
  Expr.let_ (op1 (OpCode.zext 32 64) (Arg.var rp_off)) fun p_33 =>
  Expr.let_ (op2 (OpCode.mul i64) (Arg.var p_33.fst) (Arg.imm 4#64)) fun p_34 =>
  Expr.let_ (op2 (OpCode.add i64) (Arg.var ld) (Arg.var p_34.fst)) fun p_35 =>
  Expr.let_ (op2 (OpCode.add i32) (Arg.var n_off) (Arg.var p_32.fst)) fun p_36 =>
  Expr.let_ (op1 (OpCode.zext 32 64) (Arg.var p_36.fst)) fun p_37 =>
  Expr.let_ (op2 (OpCode.mul i64) (Arg.var p_37.fst) (Arg.imm 4#64)) fun p_38 =>
  Expr.let_ (op2 (OpCode.add i64) (Arg.var ld) (Arg.var p_38.fst)) fun p_39 =>
  Expr.load i32 (Arg.var p_39.fst) fun ld_2 =>
  Expr.store (Arg.var ld_2) (Arg.var p_35.fst)
    (udivShiftRprimeExpr w r_off rp_off ld fun p_40 =>
      Expr.call (as := [i64, i32, i32, i32, i32]) (bs := [i32]) "bv_blast_sub_with_borrow"
        (Arg.var h, Arg.var rp_off, Arg.var d_off, Arg.var diff_off, Arg.var w, ()) fun p_42 =>
      Expr.let_ (op2 (OpCode.add i64) (Arg.var h) (Arg.imm (t := i64) 120#64)) fun p_43 =>
      Expr.load i32 (Arg.var p_43.fst) fun ld_3 =>
      Expr.let_ (op2 (OpCode.cmp CmpOp.ne i32 Ty.bool (by decide))
        (Arg.var ld_3) (Arg.imm 0#32)) fun p_44 =>
      Expr.jnz (Arg.var p_44.fst) (udivRelRetExpr h mark0)
        (Expr.call (as := [i64, i32, i32, i32, i32, i32]) (bs := [Ty.bool]) "bv_blast_ite_into"
          (Arg.var h, Arg.var p_42.fst, Arg.var rp_off, Arg.var diff_off,
            Arg.var r_off, Arg.var w, ()) fun p_45 =>
        Expr.jnz (Arg.var p_45.fst)
          (Expr.let_ (op2 (OpCode.sub i32) (Arg.var w) (Arg.imm 1#32)) fun p =>
            udivShiftQExpr q_off p.fst ld
              (Expr.let_ (op1 (OpCode.zext 32 64) (Arg.var q_off)) fun p =>
                Expr.let_ (op2 (OpCode.mul i64) (Arg.var p.fst) (Arg.imm 4#64)) fun p =>
                Expr.let_ (op2 (OpCode.add i64) (Arg.var ld) (Arg.var p.fst)) fun p =>
                Expr.call (as := [i32]) (bs := [i32]) "bv_aig_not" (Arg.var p_42.fst, ())
                  fun p_47 =>
                Expr.store (Arg.var p_47.fst) (Arg.var p.fst)
                  (Expr.let_ (op2 (OpCode.add i32) (Arg.var step_bv) (Arg.imm 1#32)) fun p =>
                    Expr.jump J (Arg.var p_40.fst, Arg.var p.fst, ()))))
          (udivRelRetExpr h mark0)))

public abbrev udivStepLoopExpr (h : Val i64)
    (n_off d_off w mark0 q_off r_off rp_off diff_off dummy0 : Val i32) (ld : Val i64)
    (exitExpr : Tup Val [i32, i32] → Expr Val Cont [i32]) : Expr Val Cont [i32] :=
  Expr.group
    (fun Js => Blocks.cons
      (fun p_29 : Tup Val [i32, i32] =>
        Expr.let_ (op2 (OpCode.cmp CmpOp.ult i32 Ty.bool (by decide))
          (Arg.var p_29.snd.fst) (Arg.var w)) fun p_30 =>
        Expr.jnz (Arg.var p_30.fst)
          (udivStepIterExpr h n_off d_off w mark0 q_off r_off rp_off diff_off p_29.snd.fst ld
            Js.fst)
          (exitExpr p_29))
      Blocks.nil)
    (fun Js => Expr.jump Js.fst (Arg.var dummy0, Arg.imm 0#32, ()))

public theorem bv_udiv_rel_ret_wp (Γ : Env)
    (hrel : Γ.Has "bv_lits_release" bvLitsReleaseSpec)
    {h : Val i64} {mark0 : BitVec 32} {hdr : BVHdrState}
    {aigWords : List (BitVec 64)} {htSlots litsPool : List (BitVec 32)}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [i32]} {X : XPost}
    (hlen : mark0.toNat ≤ hdr.lits_len.toNat)
    (hmem : (bvHdrMem h hdr ⋆ array64 hdr.aig_ptr aigWords ⋆
      array (t := i32) hdr.ht_ptr htSlots ⋆
      array (t := i32) hdr.lits_ptr litsPool ⋆ R) m)
    (hQ : ∀ m',
      (bvHdrMem h { hdr with lits_len := mark0 } ⋆ array64 hdr.aig_ptr aigWords ⋆
        array (t := i32) hdr.ht_ptr htSlots ⋆
        array (t := i32) hdr.lits_ptr litsPool ⋆ R) m' →
      Q (0xFFFFFFFF#32, ()) m') :
    wp Γ Q X (udivRelRetExpr h mark0) m := by
  dsimp only [udivRelRetExpr]
  c0_hcall hrel
  refine ⟨hdr, _, opMem_to_hdr hmem, ?_⟩
  simp only [hlen, ↓reduceIte]
  intro m' hm'
  exact hQ m' (opMem_of_hdr hm')

public theorem bv_udiv_alloc_rel_wp (Γ : Env)
    (halloc : Γ.Has "bv_lits_alloc" bvLitsAllocSpec)
    (hrel : Γ.Has "bv_lits_release" bvLitsReleaseSpec)
    {h : Val i64} {w mark0 : BitVec 32}
    {cont : Tup Val [i32] → Expr Val Cont [i32]}
    {hdr : BVHdrState} {aigWords : List (BitVec 64)} {htSlots litsPool : List (BitVec 32)}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [i32]} {X : XPost}
    (hoom : hdr.oom = 0#32)
    (hlencap : hdr.lits_len.toNat ≤ hdr.lits_cap.toNat)
    (hmark : mark0.toNat ≤ hdr.lits_len.toNat)
    (hmem : (bvHdrMem h hdr ⋆ array64 hdr.aig_ptr aigWords ⋆
      array (t := i32) hdr.ht_ptr htSlots ⋆
      array (t := i32) hdr.lits_ptr litsPool ⋆ R) m)
    (hfail : ¬ (w.toNat ≤ hdr.lits_cap.toNat - hdr.lits_len.toNat) → ∀ m',
      (bvHdrMem h { hdr with oom := 1#32, lits_len := mark0 } ⋆
        array64 hdr.aig_ptr aigWords ⋆ array (t := i32) hdr.ht_ptr htSlots ⋆
        array (t := i32) hdr.lits_ptr litsPool ⋆ R) m' →
      Q (0xFFFFFFFF#32, ()) m')
    (hsuc : w.toNat ≤ hdr.lits_cap.toNat - hdr.lits_len.toNat → ∀ m',
      (bvHdrMem h { hdr with lits_len := hdr.lits_len + w } ⋆
        array64 hdr.aig_ptr aigWords ⋆ array (t := i32) hdr.ht_ptr htSlots ⋆
        array (t := i32) hdr.lits_ptr litsPool ⋆ R) m' →
      wp Γ Q X (cont (hdr.lits_len, ())) m') :
    wp Γ Q X
      (Expr.call (as := [i64, i32]) (bs := [i32]) "bv_lits_alloc"
        (Arg.var h, Arg.var w, ()) fun p_off =>
        Expr.let_ (op2 (OpCode.add i64) (Arg.var h) (Arg.imm (t := i64) 120#64)) fun p_addr =>
        Expr.load i32 (Arg.var p_addr.fst) fun ld =>
        Expr.let_ (op2 (OpCode.cmp CmpOp.ne i32 Ty.bool (by decide))
          (Arg.var ld) (Arg.imm 0#32)) fun p_cmp =>
        Expr.jnz (Arg.var p_cmp.fst) (udivRelRetExpr h mark0) (cont p_off)) m := by
  c0_hcall halloc
  refine ⟨hdr, _, opMem_to_hdr hmem, ?_⟩
  by_cases hfit : w.toNat ≤ hdr.lits_cap.toNat - hdr.lits_len.toNat
  · simp only [hoom, hlencap, hfit, and_self, ↓reduceIte]
    intro m' hm'
    have hm'' : (bvHdrMem h { hdr with lits_len := hdr.lits_len + w } ⋆
        array64 hdr.aig_ptr aigWords ⋆ array (t := i32) hdr.ht_ptr htSlots ⋆
        array (t := i32) hdr.lits_ptr litsPool ⋆ R) m' := by
      simpa [hoom] using opMem_of_hdr hm'
    apply wp_load_hdr_oom hm''
    c0_hfast_nogrp
    · simp [hoom] at ‹_›
    · exact hsuc hfit m' hm''
  · simp only [hoom, hlencap, hfit, and_false, ↓reduceIte, ne_eq, not_true_eq_false]
    intro m' hm'
    have hm'' : (bvHdrMem h { hdr with oom := 1#32 } ⋆
        array64 hdr.aig_ptr aigWords ⋆ array (t := i32) hdr.ht_ptr htSlots ⋆
        array (t := i32) hdr.lits_ptr litsPool ⋆ R) m' := by
      simpa [hoom] using opMem_of_hdr hm'
    apply wp_load_hdr_oom hm''
    c0_hfast_nogrp
    · apply bv_udiv_rel_ret_wp Γ hrel (hdr := { hdr with oom := 1#32 }) hmark hm''
      exact hfail hfit
    · simp at ‹_›

public theorem bv_udiv_zero_loop_wp (Γ : Env)
    {h : Val i64} {w q_off r_off : BitVec 32} {ld : Val i64}
    {exitExpr : Tup Val [i32] → Expr Val Cont [i32]}
    {hdr : BVHdrState} {g : Aig} {aw : List (BitVec 64)} {ht lp0 : List (BitVec 32)}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [i32]} {X : XPost}
    (hinv : AigInv hdr g aw ht) (hld : ld = hdr.lits_ptr)
    (hq : q_off.toNat + w.toNat ≤ hdr.lits_len.toNat)
    (hr : r_off.toNat + w.toNat ≤ hdr.lits_len.toNat)
    (hlencap : hdr.lits_len.toNat ≤ hdr.lits_cap.toNat)
    (hcaplen : hdr.lits_cap.toNat ≤ lp0.length)
    (hdisj : DisjointSlice q_off.toNat w.toNat r_off.toNat w.toNat)
    (hmem : (bvHdrMem h hdr ⋆ array64 hdr.aig_ptr aw ⋆
      array (t := i32) hdr.ht_ptr ht ⋆ array (t := i32) hdr.lits_ptr lp0 ⋆ R) m)
    (hexit : ∀ (i_val : BitVec 32) (lp' : List (BitVec 32)) (m' : Mem 64),
      i_val = w → lp'.length = lp0.length →
      (∀ p, ¬ (q_off.toNat ≤ p ∧ p < q_off.toNat + w.toNat) →
        ¬ (r_off.toNat ≤ p ∧ p < r_off.toNat + w.toNat) → lp'.getD p 0#32 = lp0.getD p 0#32) →
      SliceLitsWf hdr lp' q_off.toNat w.toNat → SliceLitsWf hdr lp' r_off.toNat w.toNat →
      (∀ ρ, sliceVal g ρ lp' q_off.toNat w.toNat = 0#w.toNat) →
      (∀ ρ, sliceVal g ρ lp' r_off.toNat w.toNat = 0#w.toNat) →
      (bvHdrMem h hdr ⋆ array64 hdr.aig_ptr aw ⋆
        array (t := i32) hdr.ht_ptr ht ⋆ array (t := i32) hdr.lits_ptr lp' ⋆ R) m' →
      wp Γ Q X (exitExpr (i_val, ())) m') :
    wp Γ Q X (udivZeroLoopExpr w q_off r_off ld exitExpr) m := by
  subst hld
  let Inv : (Nat × List (BitVec 32)) → Mem 64 → Prop := fun st ml =>
    st.1 ≤ w.toNat ∧ st.2.length = lp0.length ∧
    (∀ p, ¬ (q_off.toNat ≤ p ∧ p < q_off.toNat + st.1) →
      ¬ (r_off.toNat ≤ p ∧ p < r_off.toNat + st.1) → st.2.getD p 0#32 = lp0.getD p 0#32) ∧
    (∀ j, j < st.1 → st.2.getD (q_off.toNat + j) 0#32 = 0#32) ∧
    (∀ j, j < st.1 → st.2.getD (r_off.toNat + j) 0#32 = 0#32) ∧
    (bvHdrMem h hdr ⋆ array64 hdr.aig_ptr aw ⋆
      array (t := i32) hdr.ht_ptr ht ⋆ array (t := i32) hdr.lits_ptr st.2 ⋆ R) ml
  apply wp_while_state1 (fun st => BitVec.ofNat 32 st.1) (fun st => w.toNat - st.1) Inv
  · intro J hJ
    exact wp_jump_state (proj := fun st : Nat × List (BitVec 32) => (BitVec.ofNat 32 st.1, ()))
      (0, lp0) (by simp) (hJ (0, lp0) m ⟨Nat.zero_le _, rfl, fun _ _ _ => rfl,
        (fun j hj => by omega), (fun j hj => by omega), hmem⟩)
  · intro J st ml ⟨hle, hlen, hpres, hqz, hrz, hml⟩ hIH
    rcases st with ⟨idx, lp⟩
    dsimp only at hle hlen hpres hqz hrz hml
    dsimp only [Blocks.get]
    by_cases hlt : idx < w.toNat
    · have hcap32 : hdr.lits_cap.toNat < 2 ^ 32 := hdr.lits_cap.isLt
      have hi32 : (BitVec.ofNat 32 idx).toNat = idx := by
        rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
      have hqi_nat : (q_off + BitVec.ofNat 32 idx).toNat = q_off.toNat + idx := by
        rw [BitVec.toNat_add, hi32]; exact Nat.mod_eq_of_lt (by omega)
      have hri_nat : (r_off + BitVec.ofNat 32 idx).toNat = r_off.toNat + idx := by
        rw [BitVec.toNat_add, hi32]; exact Nat.mod_eq_of_lt (by omega)
      have hqi_lt : q_off.toNat + idx < lp.length := by omega
      have hri_lt : r_off.toNat + idx < (lp.set (q_off.toNat + idx) 0#32).length := by
        simp; omega
      have hbv1 : BitVec.ofNat 32 idx + 1#32 = BitVec.ofNat 32 (idx + 1) := by
        apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_add, hi32, BitVec.toNat_ofNat]
        simp
      have hdisj_qi_rj : ∀ j, j < idx → r_off.toNat + j ≠ q_off.toNat + idx := by
        intro j hj; unfold DisjointSlice at hdisj; omega
      have hdisj_ri_qj : ∀ j, j ≤ idx → q_off.toNat + j ≠ r_off.toNat + idx := by
        intro j hj; unfold DisjointSlice at hdisj; omega
      have hbox := fun (_ : True) => hml
      clear hml
      c0_hfast_nogrp
      · have hml := hbox trivial
        clear hbox
        apply wp_store_lits hml (idx := q_off + BitVec.ofNat 32 idx)
        · rfl
        · rw [hqi_nat]; exact hqi_lt
        intro ml1 hml1
        have hbox1 := fun (_ : True) => hml1
        clear hml1
        c0_hfast_nogrp
        have hml1 := hbox1 trivial
        clear hbox1
        apply wp_store_lits hml1 (idx := r_off + BitVec.ofNat 32 idx)
        · rfl
        · rw [hri_nat]; simpa [hqi_nat] using hri_lt
        intro ml2 hml2
        rw [hqi_nat, hri_nat] at hml2
        have hbox2 := fun (_ : True) => hml2
        clear hml2
        c0_hfast_nogrp
        have hml2 := hbox2 trivial
        clear hbox2
        rw [hbv1]
        refine hIH (idx + 1, (lp.set (q_off.toNat + idx) 0#32).set (r_off.toNat + idx) 0#32) _
          (by omega) ⟨by omega, by simp [hlen], ?_, ?_, ?_, hml2⟩
        · intro p hpq hpr
          rw [getD_set_ne _ _ _ _ _ (by omega), getD_set_ne _ _ _ _ _ (by omega)]
          exact hpres p (by omega) (by omega)
        · intro j hj
          by_cases hji : j = idx
          · subst hji
            rw [getD_set_ne _ _ _ _ _ (hdisj_ri_qj j (Nat.le_refl j)),
              getD_set_eq _ _ _ _ _ hqi_lt]
            simp
          · have hji_lt : j < idx := by omega
            rw [getD_set_ne _ _ _ _ _ (hdisj_ri_qj j (by omega)),
              getD_set_ne _ _ _ _ _ (by omega)]
            exact hqz j hji_lt
        · intro j hj
          by_cases hji : j = idx
          · subst hji
            rw [getD_set_eq _ _ _ _ _ hri_lt]
            simp
          · have hji_lt : j < idx := by omega
            rw [getD_set_ne _ _ _ _ _ (by omega),
              getD_set_ne _ _ _ _ _ (hdisj_qi_rj j hji_lt)]
            exact hrz j hji_lt
      · bv_omega
    · have hi_eq : idx = w.toNat := by omega
      subst hi_eq
      have hbox := fun (_ : True) => hml
      clear hml
      c0_hfast_nogrp
      · bv_omega
      · have hml := hbox trivial
        clear hbox
        exact hexit (BitVec.ofNat 32 w.toNat) lp ml (by simp) hlen hpres
          (sliceLitsWf_zero_of_all (aig_len_pos_of_inv hinv) hq hqz)
          (sliceLitsWf_zero_of_all (aig_len_pos_of_inv hinv) hr hrz)
          (fun _ => sliceVal_zero_of_all hqz)
          (fun _ => sliceVal_zero_of_all hrz) hml

public theorem bv_udiv_shift_rprime_wp (Γ : Env)
    {h : Val i64} {w r_off rp_off : BitVec 32} {ld : Val i64}
    {exitExpr : Tup Val [i32] → Expr Val Cont [i32]}
    {hdr : BVHdrState} {aw : List (BitVec 64)} {ht lp0 : List (BitVec 32)}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [i32]} {X : XPost}
    (hld : ld = hdr.lits_ptr) (hw : 0 < w.toNat)
    (hr : r_off.toNat + w.toNat ≤ hdr.lits_len.toNat)
    (hrp : rp_off.toNat + w.toNat ≤ hdr.lits_len.toNat)
    (hlencap : hdr.lits_len.toNat ≤ hdr.lits_cap.toNat)
    (hcaplen : hdr.lits_cap.toNat ≤ lp0.length)
    (hdisj : DisjointSlice rp_off.toNat w.toNat r_off.toNat w.toNat)
    (hmem : (bvHdrMem h hdr ⋆ array64 hdr.aig_ptr aw ⋆
      array (t := i32) hdr.ht_ptr ht ⋆ array (t := i32) hdr.lits_ptr lp0 ⋆ R) m)
    (hexit : ∀ (k_val : BitVec 32) (lp' : List (BitVec 32)) (m' : Mem 64),
      k_val = w → lp'.length = lp0.length →
      (∀ p, ¬ (rp_off.toNat + 1 ≤ p ∧ p < rp_off.toNat + w.toNat) →
        lp'.getD p 0#32 = lp0.getD p 0#32) →
      (∀ j, 1 ≤ j → j < w.toNat →
        lp'.getD (rp_off.toNat + j) 0#32 = lp0.getD (r_off.toNat + (j - 1)) 0#32) →
      (bvHdrMem h hdr ⋆ array64 hdr.aig_ptr aw ⋆
        array (t := i32) hdr.ht_ptr ht ⋆ array (t := i32) hdr.lits_ptr lp' ⋆ R) m' →
      wp Γ Q X (exitExpr (k_val, ())) m') :
    wp Γ Q X (udivShiftRprimeExpr w r_off rp_off ld exitExpr) m := by
  subst hld
  let Inv : (Nat × List (BitVec 32)) → Mem 64 → Prop := fun st ml =>
    1 ≤ st.1 ∧ st.1 ≤ w.toNat ∧ st.2.length = lp0.length ∧
    (∀ p, ¬ (rp_off.toNat + 1 ≤ p ∧ p < rp_off.toNat + st.1) →
      st.2.getD p 0#32 = lp0.getD p 0#32) ∧
    (∀ j, 1 ≤ j → j < st.1 →
      st.2.getD (rp_off.toNat + j) 0#32 = lp0.getD (r_off.toNat + (j - 1)) 0#32) ∧
    (bvHdrMem h hdr ⋆ array64 hdr.aig_ptr aw ⋆
      array (t := i32) hdr.ht_ptr ht ⋆ array (t := i32) hdr.lits_ptr st.2 ⋆ R) ml
  apply wp_while_state1 (fun st => BitVec.ofNat 32 st.1) (fun st => w.toNat - st.1) Inv
  · intro J hJ
    exact wp_jump_state (proj := fun st : Nat × List (BitVec 32) => (BitVec.ofNat 32 st.1, ()))
      (1, lp0) (by simp) (hJ (1, lp0) m ⟨Nat.le_refl _, hw, rfl, fun _ _ => rfl,
        (fun j hj1 hj2 => by omega), hmem⟩)
  · intro J st ml ⟨hk1, hle, hlen, hpres, hsh, hml⟩ hIH
    rcases st with ⟨k, lp⟩
    dsimp only at hk1 hle hlen hpres hsh hml
    dsimp only [Blocks.get]
    by_cases hlt : k < w.toNat
    · have hcap32 : hdr.lits_cap.toNat < 2 ^ 32 := hdr.lits_cap.isLt
      have hk32 : (BitVec.ofNat 32 k).toNat = k := by
        rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
      have hrpk : (rp_off + BitVec.ofNat 32 k).toNat = rp_off.toNat + k := by
        rw [BitVec.toNat_add, hk32]; exact Nat.mod_eq_of_lt (by omega)
      have hrk1 : (r_off + BitVec.ofNat 32 k - 1#32).toNat = r_off.toNat + (k - 1) := by
        have hadd : (r_off + BitVec.ofNat 32 k).toNat = r_off.toNat + k := by
          rw [BitVec.toNat_add, hk32]; exact Nat.mod_eq_of_lt (by omega)
        rw [BitVec.toNat_sub, hadd]; simp only [BitVec.toNat_ofNat]; omega
      have hrpk_lt : rp_off.toNat + k < lp.length := by omega
      have hrk1_lt : r_off.toNat + (k - 1) < lp.length := by omega
      have hbv1 : BitVec.ofNat 32 k + 1#32 = BitVec.ofNat 32 (k + 1) := by
        apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_add, hk32, BitVec.toNat_ofNat]
        simp
      have hdisj_src : ¬ (rp_off.toNat + 1 ≤ r_off.toNat + (k - 1) ∧
          r_off.toNat + (k - 1) < rp_off.toNat + k) := by
        unfold DisjointSlice at hdisj; omega
      have hload_val : lp.getD (r_off.toNat + (k - 1)) 0#32 =
          lp0.getD (r_off.toNat + (k - 1)) 0#32 :=
        hpres (r_off.toNat + (k - 1)) hdisj_src
      have hbox := fun (_ : True) => hml
      clear hml
      c0_hfast_nogrp
      · have hml := hbox trivial
        clear hbox
        apply wp_load_lits hml (idx := r_off + BitVec.ofNat 32 k - 1#32)
        · rfl
        · rw [hrk1]; exact hrk1_lt
        apply wp_store_lits hml (idx := rp_off + BitVec.ofNat 32 k)
        · rfl
        · rw [hrpk]; exact hrpk_lt
        intro ml1 hml1
        rw [hrk1, hrpk] at hml1
        have hbox1 := fun (_ : True) => hml1
        clear hml1
        c0_hfast_nogrp
        have hml1 := hbox1 trivial
        clear hbox1
        rw [hbv1]
        refine hIH (k + 1, lp.set (rp_off.toNat + k) (lp.getD (r_off.toNat + (k - 1)) 0#32)) _
          (by omega) ⟨by omega, by omega, by simp [hlen], ?_, ?_, hml1⟩
        · intro p hp
          rw [getD_set_ne _ _ _ _ _ (by omega)]
          exact hpres p (by omega)
        · intro j hj1 hj2
          by_cases hjk : j = k
          · subst hjk
            rw [getD_set_eq _ _ _ _ _ hrpk_lt]
            simp only [↓reduceIte]
            exact hload_val
          · rw [getD_set_ne _ _ _ _ _ (by omega)]
            exact hsh j hj1 (by omega)
      · bv_omega
    · have hk_eq : k = w.toNat := by omega
      subst hk_eq
      have hbox := fun (_ : True) => hml
      clear hml
      c0_hfast_nogrp
      · bv_omega
      · have hml := hbox trivial
        clear hbox
        exact hexit (BitVec.ofNat 32 w.toNat) lp ml (by simp) hlen hpres hsh hml

public theorem bv_udiv_shift_q_wp (Γ : Env)
    {h : Val i64} {w q_off w1 : BitVec 32} {ld : Val i64}
    {exitExpr : Expr Val Cont [i32]}
    {hdr : BVHdrState} {aw : List (BitVec 64)} {ht lp0 : List (BitVec 32)}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [i32]} {X : XPost}
    (hld : ld = hdr.lits_ptr) (hw : 0 < w.toNat) (hw1 : w1 = w - 1#32)
    (hq : q_off.toNat + w.toNat ≤ hdr.lits_len.toNat)
    (hlencap : hdr.lits_len.toNat ≤ hdr.lits_cap.toNat)
    (hcaplen : hdr.lits_cap.toNat ≤ lp0.length)
    (hmem : (bvHdrMem h hdr ⋆ array64 hdr.aig_ptr aw ⋆
      array (t := i32) hdr.ht_ptr ht ⋆ array (t := i32) hdr.lits_ptr lp0 ⋆ R) m)
    (hexit : ∀ (lp' : List (BitVec 32)) (m' : Mem 64),
      lp'.length = lp0.length →
      (∀ p, ¬ (q_off.toNat + 1 ≤ p ∧ p < q_off.toNat + w.toNat) →
        lp'.getD p 0#32 = lp0.getD p 0#32) →
      (∀ j, 1 ≤ j → j < w.toNat →
        lp'.getD (q_off.toNat + j) 0#32 = lp0.getD (q_off.toNat + (j - 1)) 0#32) →
      (bvHdrMem h hdr ⋆ array64 hdr.aig_ptr aw ⋆
        array (t := i32) hdr.ht_ptr ht ⋆ array (t := i32) hdr.lits_ptr lp' ⋆ R) m' →
      wp Γ Q X exitExpr m') :
    wp Γ Q X (udivShiftQExpr q_off w1 ld exitExpr) m := by
  subst hld hw1
  let Inv : (Nat × List (BitVec 32)) → Mem 64 → Prop := fun st ml =>
    st.1 ≤ w.toNat - 1 ∧ st.2.length = lp0.length ∧
    (∀ p, ¬ (q_off.toNat + st.1 + 1 ≤ p ∧ p < q_off.toNat + w.toNat) →
      st.2.getD p 0#32 = lp0.getD p 0#32) ∧
    (∀ j, st.1 < j → j < w.toNat →
      st.2.getD (q_off.toNat + j) 0#32 = lp0.getD (q_off.toNat + (j - 1)) 0#32) ∧
    (bvHdrMem h hdr ⋆ array64 hdr.aig_ptr aw ⋆
      array (t := i32) hdr.ht_ptr ht ⋆ array (t := i32) hdr.lits_ptr st.2 ⋆ R) ml
  apply wp_while_state1 (fun st => BitVec.ofNat 32 st.1) (fun st => st.1) Inv
  · intro J hJ
    refine wp_jump_state (proj := fun st : Nat × List (BitVec 32) => (BitVec.ofNat 32 st.1, ()))
      (w.toNat - 1, lp0) ?_ (hJ (w.toNat - 1, lp0) m ⟨Nat.le_refl _, rfl, fun _ _ => rfl,
        (fun j hj1 hj2 => by omega), hmem⟩)
    dsimp [Arg.val, vals]; congr 1; apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat]; simp only [BitVec.toNat_ofNat]; omega
  · intro J st ml ⟨hle, hlen, hpres, hsh, hml⟩ hIH
    rcases st with ⟨k, lp⟩
    dsimp only at hle hlen hpres hsh hml
    dsimp only [Blocks.get]
    by_cases hgt : 0 < k
    · have hcap32 : hdr.lits_cap.toNat < 2 ^ 32 := hdr.lits_cap.isLt
      have hk32 : (BitVec.ofNat 32 k).toNat = k := by
        rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
      have hqk : (q_off + BitVec.ofNat 32 k).toNat = q_off.toNat + k := by
        rw [BitVec.toNat_add, hk32]; exact Nat.mod_eq_of_lt (by omega)
      have hqk1 : (q_off + BitVec.ofNat 32 k - 1#32).toNat = q_off.toNat + (k - 1) := by
        rw [BitVec.toNat_sub, hqk]; simp only [BitVec.toNat_ofNat]; omega
      have hqk_lt : q_off.toNat + k < lp.length := by omega
      have hqk1_lt : q_off.toNat + (k - 1) < lp.length := by omega
      have hbv1 : BitVec.ofNat 32 k - 1#32 = BitVec.ofNat 32 (k - 1) := by
        apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_sub, hk32, BitVec.toNat_ofNat]
        simp only [BitVec.toNat_ofNat]; omega
      have hload_val : lp.getD (q_off.toNat + (k - 1)) 0#32 =
          lp0.getD (q_off.toNat + (k - 1)) 0#32 :=
        hpres (q_off.toNat + (k - 1)) (by omega)
      have hbox := fun (_ : True) => hml
      clear hml
      c0_hfast_nogrp
      · have hml := hbox trivial
        clear hbox
        apply wp_load_lits hml (idx := q_off + BitVec.ofNat 32 k - 1#32)
        · rfl
        · rw [hqk1]; exact hqk1_lt
        apply wp_store_lits hml (idx := q_off + BitVec.ofNat 32 k)
        · rfl
        · rw [hqk]; exact hqk_lt
        intro ml1 hml1
        rw [hqk1, hqk] at hml1
        have hbox1 := fun (_ : True) => hml1
        clear hml1
        c0_hfast_nogrp
        have hml1 := hbox1 trivial
        clear hbox1
        rw [hbv1]
        refine hIH (k - 1, lp.set (q_off.toNat + k) (lp.getD (q_off.toNat + (k - 1)) 0#32)) _
          (by omega) ⟨by omega, by simp [hlen], ?_, ?_, hml1⟩
        · intro p hp
          rw [getD_set_ne _ _ _ _ _ (by omega)]
          exact hpres p (by omega)
        · intro j hj1 hj2
          by_cases hjk : j = k
          · subst hjk
            rw [getD_set_eq _ _ _ _ _ hqk_lt]
            simp only [↓reduceIte]
            exact hload_val
          · rw [getD_set_ne _ _ _ _ _ (by omega)]
            exact hsh j (by omega) hj2
      · bv_omega
    · have hk0 : k = 0 := by omega
      subst hk0
      have hbox := fun (_ : True) => hml
      clear hml
      c0_hfast_nogrp
      · bv_omega
      · have hml := hbox trivial
        clear hbox
        exact hexit lp ml hlen (fun p hp => hpres p (by omega)) (fun j hj1 hj2 => hsh j hj1 hj2)
          hml

public theorem bv_udiv_zero_rprime_wp (Γ : Env)
    {h : Val i64} {w rp_off : BitVec 32} {ld : Val i64}
    {exitExpr : Tup Val [i32] → Expr Val Cont [i32]}
    {hdr : BVHdrState} {g : Aig} {aw : List (BitVec 64)} {ht lp0 : List (BitVec 32)}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [i32]} {X : XPost}
    (hinv : AigInv hdr g aw ht) (hld : ld = hdr.lits_ptr)
    (hrp : rp_off.toNat + w.toNat ≤ hdr.lits_len.toNat)
    (hlencap : hdr.lits_len.toNat ≤ hdr.lits_cap.toNat)
    (hcaplen : hdr.lits_cap.toNat ≤ lp0.length)
    (hmem : (bvHdrMem h hdr ⋆ array64 hdr.aig_ptr aw ⋆
      array (t := i32) hdr.ht_ptr ht ⋆ array (t := i32) hdr.lits_ptr lp0 ⋆ R) m)
    (hexit : ∀ (k_val : BitVec 32) (lp' : List (BitVec 32)) (m' : Mem 64),
      k_val = w → lp'.length = lp0.length →
      (∀ p, ¬ (rp_off.toNat ≤ p ∧ p < rp_off.toNat + w.toNat) →
        lp'.getD p 0#32 = lp0.getD p 0#32) →
      SliceLitsWf hdr lp' rp_off.toNat w.toNat →
      (∀ ρ, sliceVal g ρ lp' rp_off.toNat w.toNat = 0#w.toNat) →
      (bvHdrMem h hdr ⋆ array64 hdr.aig_ptr aw ⋆
        array (t := i32) hdr.ht_ptr ht ⋆ array (t := i32) hdr.lits_ptr lp' ⋆ R) m' →
      wp Γ Q X (exitExpr (k_val, ())) m') :
    wp Γ Q X (udivZeroRprimeExpr w rp_off ld exitExpr) m := by
  subst hld
  let Inv : (Nat × List (BitVec 32)) → Mem 64 → Prop := fun st ml =>
    st.1 ≤ w.toNat ∧ st.2.length = lp0.length ∧
    (∀ p, ¬ (rp_off.toNat ≤ p ∧ p < rp_off.toNat + st.1) →
      st.2.getD p 0#32 = lp0.getD p 0#32) ∧
    (∀ j, j < st.1 → st.2.getD (rp_off.toNat + j) 0#32 = 0#32) ∧
    (bvHdrMem h hdr ⋆ array64 hdr.aig_ptr aw ⋆
      array (t := i32) hdr.ht_ptr ht ⋆ array (t := i32) hdr.lits_ptr st.2 ⋆ R) ml
  apply wp_while_state1 (fun st => BitVec.ofNat 32 st.1) (fun st => w.toNat - st.1) Inv
  · intro J hJ
    exact wp_jump_state (proj := fun st : Nat × List (BitVec 32) => (BitVec.ofNat 32 st.1, ()))
      (0, lp0) (by simp) (hJ (0, lp0) m ⟨Nat.zero_le _, rfl, fun _ _ => rfl,
        (fun j hj => by omega), hmem⟩)
  · intro J st ml ⟨hle, hlen, hpres, hrz, hml⟩ hIH
    rcases st with ⟨k, lp⟩
    dsimp only at hle hlen hpres hrz hml
    dsimp only [Blocks.get]
    by_cases hlt : k < w.toNat
    · have hcap32 : hdr.lits_cap.toNat < 2 ^ 32 := hdr.lits_cap.isLt
      have hk32 : (BitVec.ofNat 32 k).toNat = k := by
        rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
      have hrpk : (rp_off + BitVec.ofNat 32 k).toNat = rp_off.toNat + k := by
        rw [BitVec.toNat_add, hk32]; exact Nat.mod_eq_of_lt (by omega)
      have hrpk_lt : rp_off.toNat + k < lp.length := by omega
      have hbv1 : BitVec.ofNat 32 k + 1#32 = BitVec.ofNat 32 (k + 1) := by
        apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_add, hk32, BitVec.toNat_ofNat]
        simp
      have hbox := fun (_ : True) => hml
      clear hml
      c0_hfast_nogrp
      · have hml := hbox trivial
        clear hbox
        apply wp_store_lits hml (idx := rp_off + BitVec.ofNat 32 k)
        · rfl
        · rw [hrpk]; exact hrpk_lt
        intro ml1 hml1
        rw [hrpk] at hml1
        have hbox1 := fun (_ : True) => hml1
        clear hml1
        c0_hfast_nogrp
        have hml1 := hbox1 trivial
        clear hbox1
        rw [hbv1]
        refine hIH (k + 1, lp.set (rp_off.toNat + k) 0#32) _ (by omega)
          ⟨by omega, by simp [hlen], ?_, ?_, hml1⟩
        · intro p hp
          rw [getD_set_ne _ _ _ _ _ (by omega)]
          exact hpres p (by omega)
        · intro j hj
          by_cases hjk : j = k
          · subst hjk
            rw [getD_set_eq _ _ _ _ _ hrpk_lt]
            simp
          · rw [getD_set_ne _ _ _ _ _ (by omega)]
            exact hrz j (by omega)
      · bv_omega
    · have hk_eq : k = w.toNat := by omega
      subst hk_eq
      have hbox := fun (_ : True) => hml
      clear hml
      c0_hfast_nogrp
      · bv_omega
      · have hml := hbox trivial
        clear hbox
        exact hexit (BitVec.ofNat 32 w.toNat) lp ml (by simp) hlen hpres
          (sliceLitsWf_zero_of_all (aig_len_pos_of_inv hinv) hrp hrz)
          (fun _ => sliceVal_zero_of_all hrz) hml

private structure UdivStepState where
  dum : BitVec 32
  step : Nat
  hdr : BVHdrState
  g : Aig
  aw : List (BitVec 64)
  ht : List (BitVec 32)
  lp : List (BitVec 32)

private theorem bv_udiv_step_iter_wp (Γ : Env)
    (hnot : Γ.Has "bv_aig_not" bvAigNotSpec)
    (hsub : Γ.Has "bv_blast_sub_with_borrow" bvBlastSubWithBorrowSpec)
    (hite : Γ.Has "bv_blast_ite_into" bvBlastIteIntoSpec)
    (hrel : Γ.Has "bv_lits_release" bvLitsReleaseSpec)
    {h : Val i64} {n_off d_off w mark0 q_off r_off rp_off diff_off step_bv : BitVec 32}
    {ld : Val i64} {J : Cont [i32, i32]}
    {hdr0 hdrInit hdr : BVHdrState} {g0 gInit g : Aig}
    {awInit aw : List (BitVec 64)} {htInit lpInit ht lp : List (BitVec 32)}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [i32]} {X : XPost} {step : Nat}
    (hw : 0 < w.toNat) (hstep_lt : step < w.toNat) (hstep_bv : step_bv = BitVec.ofNat 32 step)
    (hframe0 : hdr0.DcBlastFrame hdrInit) (hframe : hdrInit.DcBlastFrame hdr)
    (hle0 : g0 ≤ gInit) (hle : gInit ≤ g)
    (hnodes0 : gInit.nodes.size ≤ g0.nodes.size + 4 * w.toNat)
    (hnodes : g.nodes.size ≤ gInit.nodes.size + step * (12 * w.toNat))
    (hinv0 : AigInv hdrInit gInit awInit htInit) (hinv : AigInv hdr g aw ht)
    (hld : ld = hdrInit.lits_ptr) (hoom : hdr.oom = 0#32)
    (hlencap0 : hdrInit.lits_len.toNat ≤ hdrInit.lits_cap.toNat)
    (hcaplen0 : hdrInit.lits_cap.toNat ≤ lpInit.length) (hptr0 : hdrInit.lits_ptr ≠ 0#64)
    (hmark0 : mark0 = hdr0.lits_len) (hlen_eq : hdr.lits_len = hdrInit.lits_len)
    (hq_eq : q_off.toNat = hdr0.lits_len.toNat + w.toNat)
    (hr_eq : r_off.toNat = q_off.toNat + w.toNat)
    (hrp_eq : rp_off.toNat = r_off.toNat + w.toNat)
    (hdiff_eq : diff_off.toNat = rp_off.toNat + w.toNat)
    (hlen5 : diff_off.toNat + w.toNat = hdrInit.lits_len.toNat)
    (hn : n_off.toNat + w.toNat ≤ hdr0.lits_len.toNat)
    (hd : d_off.toNat + w.toNat ≤ hdr0.lits_len.toNat)
    (hwfn : SliceLitsWf hdrInit lpInit n_off.toNat w.toNat)
    (hwfd : SliceLitsWf hdrInit lpInit d_off.toNat w.toNat)
    (hlen_lp : lp.length = lpInit.length)
    (hpres0 : ∀ p, p < q_off.toNat → lp.getD p 0#32 = lpInit.getD p 0#32)
    (hwfq : SliceLitsWf hdr lp q_off.toNat w.toNat)
    (hwfr : SliceLitsWf hdr lp r_off.toNat w.toNat)
    (hdiv_inv : ∀ ρ,
      let divSt := BitVec.divRec step
        { n := sliceVal gInit ρ lpInit n_off.toNat w.toNat,
          d := sliceVal gInit ρ lpInit d_off.toNat w.toNat }
        (BitVec.DivModState.init w.toNat)
      sliceVal g ρ lp q_off.toNat w.toNat = divSt.q ∧
      sliceVal g ρ lp r_off.toNat w.toNat = divSt.r)
    (hmem : (bvHdrMem h hdr ⋆ array64 hdr.aig_ptr aw ⋆
      array (t := i32) hdr.ht_ptr ht ⋆ array (t := i32) hdr.lits_ptr lp ⋆ R) m)
    (hfail : ∀ (hdrF : BVHdrState) (gF : Aig) (awF : List (BitVec 64))
      (htF lpF : List (BitVec 32)) (mF : Mem 64),
      hdr0.DcBlastFrame hdrF → g0 ≤ gF →
      gF.nodes.size ≤ g0.nodes.size + (7 * w.toNat + 12 * w.toNat * w.toNat) →
      AigInv hdrF gF awF htF → lpF.length = lpInit.length →
      (∀ p, p < hdr0.lits_len.toNat → lpF.getD p 0#32 = lpInit.getD p 0#32) →
      hdrF.oom ≠ 0#32 → hdrF.lits_len = hdr0.lits_len →
      (g0.A + 1 + g0.nodes.size + (7 * w.toNat + 12 * w.toNat * w.toNat) ≤ hdr0.aig_cap.toNat →
        g0.nodes.size + (7 * w.toNat + 12 * w.toNat * w.toNat) ≤ bvMaxGates → False) →
      (bvHdrMem h hdrF ⋆ array64 hdrF.aig_ptr awF ⋆
        array (t := i32) hdrF.ht_ptr htF ⋆ array (t := i32) hdrF.lits_ptr lpF ⋆ R) mF →
      Q (0xFFFFFFFF#32, ()) mF)
    (hnext : ∀ (dum' : BitVec 32) (hdr' : BVHdrState) (g' : Aig)
      (aw' : List (BitVec 64)) (ht' lp' : List (BitVec 32)) (m' : Mem 64),
      hdrInit.DcBlastFrame hdr' → gInit ≤ g' →
      g'.nodes.size ≤ gInit.nodes.size + (step + 1) * (12 * w.toNat) →
      AigInv hdr' g' aw' ht' → hdr'.oom = 0#32 → hdr'.lits_len = hdrInit.lits_len →
      lp'.length = lpInit.length →
      (∀ p, p < q_off.toNat → lp'.getD p 0#32 = lpInit.getD p 0#32) →
      SliceLitsWf hdr' lp' q_off.toNat w.toNat → SliceLitsWf hdr' lp' r_off.toNat w.toNat →
      (∀ ρ,
        let divSt := BitVec.divRec (step + 1)
          { n := sliceVal gInit ρ lpInit n_off.toNat w.toNat,
            d := sliceVal gInit ρ lpInit d_off.toNat w.toNat }
          (BitVec.DivModState.init w.toNat)
        sliceVal g' ρ lp' q_off.toNat w.toNat = divSt.q ∧
        sliceVal g' ρ lp' r_off.toNat w.toNat = divSt.r) →
      (bvHdrMem h hdr' ⋆ array64 hdr'.aig_ptr aw' ⋆
        array (t := i32) hdr'.ht_ptr ht' ⋆ array (t := i32) hdr'.lits_ptr lp' ⋆ R) m' →
      J (dum', BitVec.ofNat 32 (step + 1), ()) m') :
    wp Γ Q X
      (udivStepIterExpr h n_off d_off w mark0 q_off r_off rp_off diff_off step_bv ld J) m := by
  subst hld hstep_bv
  have hcap32 : hdrInit.lits_cap.toNat < 2 ^ 32 := hdrInit.lits_cap.isLt
  have hlencap : hdr.lits_len.toNat ≤ hdr.lits_cap.toNat := by
    rw [hlen_eq, hframe.lits_cap]; exact hlencap0
  have hcaplen : hdr.lits_cap.toNat ≤ lp.length := by
    rw [hlen_lp, hframe.lits_cap]; exact hcaplen0
  have hptr : hdr.lits_ptr = hdrInit.lits_ptr := hframe.lits_ptr
  have hstep32 : (BitVec.ofNat 32 step).toNat = step := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hidx_nat : (n_off + (w - 1#32 - BitVec.ofNat 32 step)).toNat =
      n_off.toNat + (w.toNat - 1 - step) := by
    have hw1 : (w - 1#32).toNat = w.toNat - 1 := by
      rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
    have hw1s : (w - 1#32 - BitVec.ofNat 32 step).toNat = w.toNat - 1 - step := by
      rw [BitVec.toNat_sub, hw1, hstep32]; omega
    rw [BitVec.toNat_add, hw1s]; exact Nat.mod_eq_of_lt (by omega)
  have hidx_lt : n_off.toNat + (w.toNat - 1 - step) < lp.length := by omega
  have hrp0_lt : rp_off.toNat < lp.length := by omega
  have hbv_step1 : BitVec.ofNat 32 step + 1#32 = BitVec.ofNat 32 (step + 1) := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_add, hstep32, BitVec.toNat_ofNat]
    simp
  dsimp only [udivStepIterExpr]
  c0_hfast_nogrp
  refine wp_load_lits hmem (idx := n_off + (w - 1#32 - BitVec.ofNat 32 step))
    (by rw [hptr]; rfl) (by rw [hidx_nat]; exact hidx_lt) ?_
  refine wp_store_lits hmem (idx := rp_off) (by rw [hptr]; rfl) hrp0_lt ?_
  intro m1 hmem1
  rw [hidx_nat] at hmem1
  let lp1 := lp.set rp_off.toNat (lp.getD (n_off.toNat + (w.toNat - 1 - step)) 0#32)
  have hdisj_rp_r : DisjointSlice rp_off.toNat w.toNat r_off.toNat w.toNat := by
    unfold DisjointSlice; omega
  apply bv_udiv_shift_rprime_wp Γ hptr.symm hw
    (by rw [hlen_eq]; omega) (by rw [hlen_eq]; omega) hlencap
    (by simp only [List.length_set]; exact hcaplen) hdisj_rp_r hmem1
  intro k_val lp2 m2 hkval hlen2 hpres2 hsh2 hmem2
  have hlen2_init : lp2.length = lpInit.length := by simpa [lp1, hlen_lp] using hlen2
  have hpres_lt_rp : ∀ p, p < rp_off.toNat → lp2.getD p 0#32 = lp.getD p 0#32 := by
    intro p hp
    rw [hpres2 p (by omega)]
    exact getD_set_ne _ _ _ _ _ (by omega)
  have hwf_n2 : SliceLitsWf hdr lp2 n_off.toNat w.toNat :=
    sliceLitsWf_of_inv_le hinv0 hinv hle (by rw [hlen_eq]; exact Nat.le_refl _) hwfn
      fun p _ _ => by rw [hpres_lt_rp p (by omega), hpres0 p (by omega)]
  have hwf_d2 : SliceLitsWf hdr lp2 d_off.toNat w.toNat :=
    sliceLitsWf_of_inv_le hinv0 hinv hle (by rw [hlen_eq]; exact Nat.le_refl _) hwfd
      fun p _ _ => by rw [hpres_lt_rp p (by omega), hpres0 p (by omega)]
  have hwf_rp2 : SliceLitsWf hdr lp2 rp_off.toNat w.toNat := by
    refine ⟨by rw [hlen_eq]; omega, fun j hj => ?_⟩
    by_cases hj0 : j = 0
    · subst hj0
      have h0eq : lp2.getD rp_off.toNat 0#32 =
          lpInit.getD (n_off.toNat + (w.toNat - 1 - step)) 0#32 := by
        rw [hpres2 rp_off.toNat (by omega)]
        simp only [getD_set_eq _ _ _ _ _ hrp0_lt, ↓reduceIte]
        exact hpres0 _ (by omega)
      rw [Nat.add_zero, h0eq]
      have haig := aigLen_le_of_inv_le hinv0 hinv hle
      have hwf0 := hwfn.2 (w.toNat - 1 - step) (by omega)
      omega
    · have hshj := hsh2 j (by omega) hj
      rw [hshj, getD_set_ne _ _ _ _ _ (by omega)]
      exact hwfr.2 (j - 1) (by omega)
  have hval_rp2 : ∀ ρ,
      sliceVal g ρ lp2 rp_off.toNat w.toNat =
        (sliceVal g ρ lp r_off.toNat w.toNat).shiftConcat
          ((sliceVal gInit ρ lpInit n_off.toNat w.toNat).getLsbD (w.toNat - 1 - step)) := by
    intro ρ
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    rw [sliceVal_getLsbD hj, divRec_rPrime_getLsbD _ _ j hj]
    by_cases hj0 : j = 0
    · subst hj0
      have h0eq : lp2.getD rp_off.toNat 0#32 =
          lpInit.getD (n_off.toNat + (w.toNat - 1 - step)) 0#32 := by
        rw [hpres2 rp_off.toNat (by omega)]
        simp only [getD_set_eq _ _ _ _ _ hrp0_lt, ↓reduceIte]
        exact hpres0 _ (by omega)
      simp only [Nat.add_zero, ↓reduceIte, h0eq]
      rw [sliceVal_getLsbD (w := w.toNat) (by omega)]
      exact evalLit_extend_of_inv hinv0 hle (hwfn.2 (w.toNat - 1 - step) (by omega))
    · simp only [hj0, ↓reduceIte]
      rw [hsh2 j (by omega) hj, getD_set_ne _ _ _ _ _ (by omega),
        sliceVal_getLsbD (w := w.toNat) (by omega)]
  c0_hcall hsub
  refine ⟨hdr, g, aw, ht, lp2, R, hinv, by rw [hlen2_init, hframe.lits_cap]; exact hcaplen0,
    ?_, hmem2, ?_⟩
  · intro _ _ _ _ _ _
    exact ⟨hwf_rp2, hwf_d2, by unfold DisjointSlice; omega, by unfold DisjointSlice; omega⟩
  · intro b_lit hdr1 g1 aw1 ht1 lp3 m3 hf1 hle1 hnodes1 hinv1 hlen3 hpres3 _ hbound1
      hoom1val hok1 hmem3
    have hlen3_init : lp3.length = lpInit.length := hlen3.trans hlen2_init
    have hf1_blast : hdr.DcBlastFrame hdr1 := hf1.toDcBlastFrame
    have hframe01 : hdr0.DcBlastFrame hdr1 := hframe0.trans (hframe.trans hf1_blast)
    have hle01 : g0 ≤ g1 := Aig.extends_trans hle0 (Aig.extends_trans hle hle1)
    have hpres_lt_diff : ∀ p, p < diff_off.toNat → lp3.getD p 0#32 = lp2.getD p 0#32 :=
      fun p hp => hpres3 p (Or.inl hp)
    have hpres_lt_q3 : ∀ p, p < q_off.toNat → lp3.getD p 0#32 = lpInit.getD p 0#32 := by
      intro p hp; rw [hpres_lt_diff p (by omega), hpres_lt_rp p (by omega), hpres0 p hp]
    apply wp_load_hdr_oom hmem3
    by_cases hoom1 : hdr1.oom = 0#32
    · c0_hfast_nogrp
      · exfalso; exact absurd hoom1 ‹_›
      · obtain ⟨hwf_diff3, hb_lt1, hb_val1⟩ := hok1 hoom1
        have hwf_rp3 : SliceLitsWf hdr1 lp3 rp_off.toNat w.toNat :=
          sliceLitsWf_of_inv_le hinv hinv1 hle1 (by rw [hf1.lits_len]; exact Nat.le_refl _) hwf_rp2
            (fun p _ hp2 => hpres_lt_diff p (by omega))
        have hlencap1 : hdr1.lits_len.toNat ≤ hdr1.lits_cap.toNat := by
          rw [hf1.lits_len, hf1.lits_cap]; exact hlencap
        c0_hcall hite
        refine ⟨hdr1, g1, aw1, ht1, lp3, R, hinv1,
          by rw [hlen3_init, hf1.lits_cap, hframe.lits_cap]; exact hcaplen0,
          ?_, hmem3, ?_⟩
        · intro _ _ _ _ _ _
          exact ⟨fun _ => hb_lt1, hwf_rp3, hwf_diff3, by unfold DisjointSlice; omega,
            by unfold DisjointSlice; omega⟩
        · intro ite_ok hdr2 g2 aw2 ht2 lp4 m4 hf2 hle2 hnodes2 hinv2 hlen4 hpres4 _
            hoom2_iff hbound2 hite_val hmem4
          have hlen4_init : lp4.length = lpInit.length := hlen4.trans hlen3_init
          have hf2_blast : hdr1.DcBlastFrame hdr2 := hf2.toDcBlastFrame
          have hle_init2 : gInit ≤ g2 := Aig.extends_trans hle (Aig.extends_trans hle1 hle2)
          have hle02 : g0 ≤ g2 := Aig.extends_trans hle0 hle_init2
          have hpres_lt_q4 : ∀ p, p < q_off.toNat → lp4.getD p 0#32 = lpInit.getD p 0#32 := by
            intro p hp; rw [hpres4 p (Or.inl (by omega)), hpres_lt_q3 p hp]
          by_cases hok2 : ite_ok = true
          · simp only [hok2]
            have hoom2 : hdr2.oom = 0#32 := hoom2_iff.mp hok2
            obtain ⟨hwf_r4, hr4_val⟩ := hite_val hok2
            have hld2 : hdr2.lits_ptr = hdrInit.lits_ptr := by
              rw [hf2.lits_ptr, hf1.lits_ptr, hptr]
            have hlencap2 : hdr2.lits_len.toNat ≤ hdr2.lits_cap.toNat := by
              rw [hf2.lits_len, hf1.lits_len, hf2.lits_cap, hf1.lits_cap]; exact hlencap
            have hcaplen2 : hdr2.lits_cap.toNat ≤ lp4.length := by
              rw [hlen4_init, hf2.lits_cap, hf1.lits_cap, hframe.lits_cap]
              exact hcaplen0
            c0_hfast_nogrp <;> first | contradiction | skip
            apply bv_udiv_shift_q_wp Γ hld2.symm hw rfl
              (by rw [hf2.lits_len, hf1.lits_len, hlen_eq]; omega) hlencap2 hcaplen2 hmem4
            intro lp5 m5 hlen5_lp hpres5 hsh5 hmem5
            have hlen5_init : lp5.length = lpInit.length := hlen5_lp.trans hlen4_init
            have hq0_lt : q_off.toNat < lp5.length := by omega
            c0_hfast_nogrp
            c0_hcall hnot
            dsimp only [bvAigNotSpec]
            apply wp_store_lits hmem5 (idx := q_off)
            · rw [hld2]; rfl
            · exact hq0_lt
            intro m6 hmem6
            c0_hfast_nogrp
            let lp6 := lp5.set q_off.toNat (b_lit ^^^ 1#32)
            rw [hbv_step1]
            apply hnext k_val hdr2 g2 aw2 ht2 lp6 m6
              (hframe.trans (hf1_blast.trans hf2_blast)) hle_init2
              (step_mul_12_add (by omega))
              hinv2 hoom2 (by rw [hf2.lits_len, hf1.lits_len, hlen_eq])
              (by simp [lp6, hlen5_init])
              (fun p hp => by
                rw [getD_set_ne _ _ _ _ _ (by omega), hpres5 p (by omega), hpres_lt_q4 p hp])
              ?wfq6 ?hwfr6 ?hdiv6 hmem6
            · refine ⟨by rw [hf2.lits_len, hf1.lits_len, hlen_eq]; omega, fun j hj => ?_⟩
              by_cases hj0 : j = 0
              · subst hj0
                dsimp only [Nat.add_zero, lp6]
                have hq_if : (if q_off.toNat = q_off.toNat then b_lit ^^^ 1#32 else
                    lp5.getD q_off.toNat 0#32) = b_lit ^^^ 1#32 := by simp
                rw [getD_set_eq _ _ _ _ _ hq0_lt, hq_if, aigLit_xor_one_shift]
                have haig12 := aigLen_le_of_inv_le hinv1 hinv2 hle2
                omega
              · dsimp only [lp6]
                rw [getD_set_ne _ _ _ _ _ (by omega), hsh5 j (by omega) hj,
                  hpres4 _ (Or.inl (by omega)), hpres_lt_diff _ (by omega),
                  hpres_lt_rp _ (by omega)]
                have haig := aigLen_le_of_inv_le hinv hinv2 (Aig.extends_trans hle1 hle2)
                have hwfq_j := hwfq.2 (j - 1) (by omega)
                omega
            · exact sliceLitsWf_of_agree
                (fun p _ hp2 => by
                  rw [getD_set_ne _ _ _ _ _ (by omega), hpres5 p (by omega)]) hwf_r4
            · intro ρ
              let args : BitVec.DivModArgs w.toNat :=
                { n := sliceVal gInit ρ lpInit n_off.toNat w.toNat,
                  d := sliceVal gInit ρ lpInit d_off.toNat w.toNat }
              have hst := divRec_step_state step hstep_lt
                (sliceVal gInit ρ lpInit n_off.toNat w.toNat)
                (sliceVal gInit ρ lpInit d_off.toNat w.toNat)
              have hdiv0 := hdiv_inv ρ
              have hstep_vals := hb_val1 ρ
              have hrp_extend : sliceVal g ρ lp2 rp_off.toNat w.toNat =
                  (BitVec.divRec step args
                    (BitVec.DivModState.init w.toNat)).r.shiftConcat
                    (args.n.getLsbD (w.toNat - 1 - step)) := by
                rw [hval_rp2 ρ, hdiv0.2]
              have hd2 : sliceVal g ρ lp2 d_off.toNat w.toNat = args.d :=
                (sliceVal_eq_of_agree fun p _ _ => by
                  rw [hpres_lt_rp p (by omega), hpres0 p (by omega)]).trans
                    (sliceVal_extend hinv0 hle hwfd)
              have hrp3 : sliceVal g1 ρ lp3 rp_off.toNat w.toNat =
                  sliceVal g ρ lp2 rp_off.toNat w.toNat :=
                (sliceVal_eq_of_agree fun p _ _ => hpres_lt_diff p (by omega)).trans
                  (sliceVal_extend hinv hle1 hwf_rp2)
              have hr4_eq : sliceVal g2 ρ lp4 r_off.toNat w.toNat =
                  if g1.evalLit ρ (UInt32.ofBitVec b_lit) then
                    sliceVal g1 ρ lp3 rp_off.toNat w.toNat
                  else sliceVal g1 ρ lp3 diff_off.toNat w.toNat := hr4_val ρ
              constructor
              · apply BitVec.eq_of_getLsbD_eq
                intro j hj
                rw [sliceVal_getLsbD hj, hst.2, divRec_rPrime_getLsbD _ _ j hj]
                by_cases hj0 : j = 0
                · subst hj0
                  simp only [Nat.add_zero, ↓reduceIte, lp6,
                    getD_set_eq _ _ _ _ _ hq0_lt, evalLit_xor_one]
                  rw [evalLit_extend_of_inv hinv1 hle2 hb_lt1, hstep_vals.2, hd2, hrp_extend]
                · simp only [hj0, ↓reduceIte]
                  dsimp only [lp6]
                  rw [getD_set_ne _ _ _ _ _ (by omega), hsh5 j (by omega) hj,
                    hpres4 _ (Or.inl (by omega)), hpres_lt_diff _ (by omega),
                    hpres_lt_rp _ (by omega)]
                  have hq_ext := evalLit_extend_of_inv (ρ := ρ) hinv (Aig.extends_trans hle1 hle2)
                    (hwfq.2 (j - 1) (by omega))
                  rw [hq_ext, ← sliceVal_getLsbD (w := w.toNat) (off := q_off.toNat) (by omega),
                    hdiv0.1]
              · have hr6_agree : sliceVal g2 ρ lp6 r_off.toNat w.toNat =
                    sliceVal g2 ρ lp4 r_off.toNat w.toNat := by
                  apply sliceVal_eq_of_agree
                  intro p hp1 hp2
                  rw [getD_set_ne _ _ _ _ _ (by omega), hpres5 p (by omega)]
                rw [hr6_agree, hr4_eq, hrp3, hstep_vals.1, hd2, hstep_vals.2, hd2,
                  hrp_extend, hst.1]
          · simp only [hok2]
            c0_hfast_nogrp
            · simp at ‹_›
            · have hoom2 : hdr2.oom ≠ 0#32 := fun h0 => hok2 (hoom2_iff.mpr h0)
              apply bv_udiv_rel_ret_wp Γ hrel
                (by rw [hf2.lits_len, hf1.lits_len, hlen_eq, hmark0]; omega) hmem4
              intro m5 hm5
              have hf2_m := blastFrame_with_lits_len hdr2 mark0
              have hm12 := step_mul_12_le hstep_lt
              refine hfail { hdr2 with lits_len := mark0 } g2 aw2 ht2 lp4 m5
                ((hframe01.trans hf2_blast).trans hf2_m) hle02 (by omega)
                (aigInv_blastFrame hinv2 hf2_m rfl)
                (by rw [hlen4_init])
                (fun p hp => hpres_lt_q4 p (by omega)) hoom2 hmark0 ?_ hm5
              intro hcap hmax
              have hcap1 : g1.A + 1 + g1.nodes.size + 3 * w.toNat ≤ hdr1.aig_cap.toNat := by
                have hA1 : g0.A = g1.A := hle01.1
                have haigc1 : hdr1.aig_cap = hdr0.aig_cap := hframe01.aig_cap
                rw [← hA1, haigc1]
                omega
              have hmax1 : g1.nodes.size + 3 * w.toNat ≤ bvMaxGates := by omega
              exact hoom2 (hbound2 hoom1 hlencap1 (fun _ => by rw [hf1.lits_ptr, hptr]; exact hptr0)
                (by rw [hf1.lits_len, hlen_eq]; omega)
                (by rw [hf1.lits_len, hlen_eq]; omega) (by rw [hf1.lits_len, hlen_eq]; omega)
                hcap1 hmax1)
    · c0_hfast_nogrp
      · apply bv_udiv_rel_ret_wp Γ hrel
          (by rw [hf1.lits_len, hlen_eq, hmark0]; omega) hmem3
        intro m4 hm4
        have hf1_m := blastFrame_with_lits_len hdr1 mark0
        have hm12 := step_mul_12_le hstep_lt
        refine hfail { hdr1 with lits_len := mark0 } g1 aw1 ht1 lp3 m4
          (hframe01.trans hf1_m) hle01 (by omega)
          (aigInv_blastFrame hinv1 hf1_m rfl) (by rw [hlen3_init])
          (fun p hp => hpres_lt_q3 p (by omega)) hoom1 hmark0 ?_ hm4
        intro hcap hmax
        have hcap0 : g.A + 1 + g.nodes.size + 9 * w.toNat ≤ hdr.aig_cap.toNat := by
          have hA : g0.A = g.A := (Aig.extends_trans hle0 hle).1
          have haigc : hdr.aig_cap = hdr0.aig_cap := (hframe0.trans hframe).aig_cap
          rw [← hA, haigc]
          omega
        have hmax0 : g.nodes.size + 9 * w.toNat ≤ bvMaxGates := by omega
        exact hoom1 (hbound1 hoom hlencap (fun _ => by rw [hptr]; exact hptr0)
          (by rw [hlen_eq]; omega) (by rw [hlen_eq]; omega) (by rw [hlen_eq]; omega)
          hcap0 hmax0)
      · exfalso; apply hoom1; bv_omega

public theorem bv_udiv_step_loop_wp (Γ : Env)
    (hnot : Γ.Has "bv_aig_not" bvAigNotSpec)
    (hsub : Γ.Has "bv_blast_sub_with_borrow" bvBlastSubWithBorrowSpec)
    (hite : Γ.Has "bv_blast_ite_into" bvBlastIteIntoSpec)
    (hrel : Γ.Has "bv_lits_release" bvLitsReleaseSpec)
    {h : Val i64} {n_off d_off w mark0 q_off r_off rp_off diff_off dummy0 : BitVec 32}
    {ld : Val i64}
    {exitExpr : Tup Val [i32, i32] → Expr Val Cont [i32]}
    {hdr0 hdrInit : BVHdrState} {g0 gInit : Aig}
    {awInit : List (BitVec 64)} {htInit lpInit : List (BitVec 32)}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [i32]} {X : XPost}
    (hw : 0 < w.toNat) (hframe0 : hdr0.DcBlastFrame hdrInit) (hle0 : g0 ≤ gInit)
    (hnodes0 : gInit.nodes.size ≤ g0.nodes.size + 4 * w.toNat)
    (hinv0 : AigInv hdrInit gInit awInit htInit)
    (hld : ld = hdrInit.lits_ptr) (hoom0 : hdrInit.oom = 0#32)
    (hlencap0 : hdrInit.lits_len.toNat ≤ hdrInit.lits_cap.toNat)
    (hcaplen0 : hdrInit.lits_cap.toNat ≤ lpInit.length) (hptr0 : hdrInit.lits_ptr ≠ 0#64)
    (hmark0 : mark0 = hdr0.lits_len)
    (hq_eq : q_off.toNat = hdr0.lits_len.toNat + w.toNat)
    (hr_eq : r_off.toNat = q_off.toNat + w.toNat)
    (hrp_eq : rp_off.toNat = r_off.toNat + w.toNat)
    (hdiff_eq : diff_off.toNat = rp_off.toNat + w.toNat)
    (hlen5 : diff_off.toNat + w.toNat = hdrInit.lits_len.toNat)
    (hn : n_off.toNat + w.toNat ≤ hdr0.lits_len.toNat)
    (hd : d_off.toNat + w.toNat ≤ hdr0.lits_len.toNat)
    (hwfn : SliceLitsWf hdrInit lpInit n_off.toNat w.toNat)
    (hwfd : SliceLitsWf hdrInit lpInit d_off.toNat w.toNat)
    (hwfq : SliceLitsWf hdrInit lpInit q_off.toNat w.toNat)
    (hwfr : SliceLitsWf hdrInit lpInit r_off.toNat w.toNat)
    (hqz : ∀ ρ, sliceVal gInit ρ lpInit q_off.toNat w.toNat = 0#w.toNat)
    (hrz : ∀ ρ, sliceVal gInit ρ lpInit r_off.toNat w.toNat = 0#w.toNat)
    (hmem : (bvHdrMem h hdrInit ⋆ array64 hdrInit.aig_ptr awInit ⋆
      array (t := i32) hdrInit.ht_ptr htInit ⋆ array (t := i32) hdrInit.lits_ptr lpInit ⋆ R) m)
    (hfail : ∀ (hdrF : BVHdrState) (gF : Aig) (awF : List (BitVec 64))
      (htF lpF : List (BitVec 32)) (mF : Mem 64),
      hdr0.DcBlastFrame hdrF → g0 ≤ gF →
      gF.nodes.size ≤ g0.nodes.size + (7 * w.toNat + 12 * w.toNat * w.toNat) →
      AigInv hdrF gF awF htF → lpF.length = lpInit.length →
      (∀ p, p < hdr0.lits_len.toNat → lpF.getD p 0#32 = lpInit.getD p 0#32) →
      hdrF.oom ≠ 0#32 → hdrF.lits_len = hdr0.lits_len →
      (g0.A + 1 + g0.nodes.size + (7 * w.toNat + 12 * w.toNat * w.toNat) ≤ hdr0.aig_cap.toNat →
        g0.nodes.size + (7 * w.toNat + 12 * w.toNat * w.toNat) ≤ bvMaxGates → False) →
      (bvHdrMem h hdrF ⋆ array64 hdrF.aig_ptr awF ⋆
        array (t := i32) hdrF.ht_ptr htF ⋆ array (t := i32) hdrF.lits_ptr lpF ⋆ R) mF →
      Q (0xFFFFFFFF#32, ()) mF)
    (hexit : ∀ (dum : BitVec 32) (hdrW : BVHdrState) (gW : Aig)
      (awW : List (BitVec 64)) (htW lpW : List (BitVec 32)) (mW : Mem 64),
      hdrInit.DcBlastFrame hdrW → gInit ≤ gW →
      gW.nodes.size ≤ gInit.nodes.size + w.toNat * (12 * w.toNat) →
      AigInv hdrW gW awW htW → hdrW.oom = 0#32 → hdrW.lits_len = hdrInit.lits_len →
      lpW.length = lpInit.length →
      (∀ p, p < q_off.toNat → lpW.getD p 0#32 = lpInit.getD p 0#32) →
      SliceLitsWf hdrW lpW q_off.toNat w.toNat → SliceLitsWf hdrW lpW r_off.toNat w.toNat →
      (∀ ρ,
        let out := BitVec.divRec w.toNat
          { n := sliceVal gInit ρ lpInit n_off.toNat w.toNat,
            d := sliceVal gInit ρ lpInit d_off.toNat w.toNat }
          (BitVec.DivModState.init w.toNat)
        sliceVal gW ρ lpW q_off.toNat w.toNat = out.q ∧
        sliceVal gW ρ lpW r_off.toNat w.toNat = out.r) →
      (bvHdrMem h hdrW ⋆ array64 hdrW.aig_ptr awW ⋆
        array (t := i32) hdrW.ht_ptr htW ⋆ array (t := i32) hdrW.lits_ptr lpW ⋆ R) mW →
      wp Γ Q X (exitExpr (dum, w, ())) mW) :
    wp Γ Q X (udivStepLoopExpr h n_off d_off w mark0 q_off r_off rp_off diff_off
      dummy0 ld exitExpr) m := by
  let Inv : UdivStepState → Mem 64 → Prop := fun st ml =>
    st.step ≤ w.toNat ∧ hdrInit.DcBlastFrame st.hdr ∧ gInit ≤ st.g ∧
    st.g.nodes.size ≤ gInit.nodes.size + st.step * (12 * w.toNat) ∧
    AigInv st.hdr st.g st.aw st.ht ∧ st.hdr.oom = 0#32 ∧ st.hdr.lits_len = hdrInit.lits_len ∧
    st.lp.length = lpInit.length ∧
    (∀ p, p < q_off.toNat → st.lp.getD p 0#32 = lpInit.getD p 0#32) ∧
    SliceLitsWf st.hdr st.lp q_off.toNat w.toNat ∧
    SliceLitsWf st.hdr st.lp r_off.toNat w.toNat ∧
    (∀ ρ,
      let divSt := BitVec.divRec st.step
        { n := sliceVal gInit ρ lpInit n_off.toNat w.toNat,
          d := sliceVal gInit ρ lpInit d_off.toNat w.toNat }
        (BitVec.DivModState.init w.toNat)
      sliceVal st.g ρ st.lp q_off.toNat w.toNat = divSt.q ∧
      sliceVal st.g ρ st.lp r_off.toNat w.toNat = divSt.r) ∧
    (bvHdrMem h st.hdr ⋆ array64 st.hdr.aig_ptr st.aw ⋆
      array (t := i32) st.hdr.ht_ptr st.ht ⋆ array (t := i32) st.hdr.lits_ptr st.lp ⋆ R) ml
  apply wp_while_state (fun st : UdivStepState => (st.dum, BitVec.ofNat 32 st.step, ()))
    (fun st : UdivStepState => w.toNat - st.step) Inv
  · intro J hJ
    refine wp_jump_state
      (proj := fun st : UdivStepState => (st.dum, BitVec.ofNat 32 st.step, ()))
      (UdivStepState.mk dummy0 0 hdrInit gInit awInit htInit lpInit) (by simp) ?_
    refine hJ _ m ⟨Nat.zero_le _, BVHdrState.DcBlastFrame.refl hdrInit,
      Aig.extends_rfl (g := gInit), by simp, hinv0, hoom0, rfl, rfl, fun _ _ => rfl,
      hwfq, hwfr, ?_, hmem⟩
    intro ρ; simp only [BitVec.divRec_zero, BitVec.DivModState.init]; exact ⟨hqz ρ, hrz ρ⟩
  · intro J st ml ⟨hle, hframe, hleInit, hnodes, hinv, hoom, hlen_eq, hlen_lp, hpres0,
        hwfq_s, hwfr_s, hdiv_inv, hml⟩ hIH
    rcases st with ⟨dum, step, hdr, g, aw, ht, lp⟩
    dsimp only at hle hframe hleInit hnodes hinv hoom hlen_eq hlen_lp hpres0
    dsimp only at hwfq_s hwfr_s hdiv_inv hml
    dsimp only [Blocks.get]
    by_cases hlt : step < w.toNat
    · c0_hfast_nogrp
      · apply bv_udiv_step_iter_wp Γ hnot hsub hite hrel hw hlt rfl hframe0 hframe hle0 hleInit
          hnodes0 hnodes hinv0 hinv hld hoom hlencap0 hcaplen0 hptr0 hmark0 hlen_eq
          hq_eq hr_eq hrp_eq hdiff_eq hlen5 hn hd hwfn hwfd hlen_lp hpres0 hwfq_s hwfr_s
          hdiv_inv hml hfail
        intro dum' hdr' g' aw' ht' lp' m' hf' hle' hnodes' hinv' hoom' hlen' hlp' hpres'
          hwfq' hwfr' hdiv' hml'
        refine hIH (UdivStepState.mk dum' (step + 1) hdr' g' aw' ht' lp') m'
          (by dsimp only; omega) ?_
        dsimp only [Inv]
        exact ⟨by omega, hf', hle', hnodes', hinv', hoom', hlen', hlp', hpres', hwfq', hwfr',
          hdiv', hml'⟩
      · have hstep32 : (BitVec.ofNat 32 step).toNat = step := by
          rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
        simp [hstep32] at ‹_›; omega
    · have hstep_eq : step = w.toNat := by omega
      subst hstep_eq
      c0_hfast_nogrp
      · omega
      · rw [show BitVec.ofNat 32 w.toNat = w from by simp]
        exact hexit dum hdr g aw ht lp ml hframe hleInit hnodes hinv hoom hlen_eq hlen_lp
          hpres0 hwfq_s hwfr_s hdiv_inv hml

end LeanQbe.T.Examples.Bitblast.Proof.OpsDivCpop
