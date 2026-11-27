module

public import LeanQbe.T.Examples.Bitblast.Proof.OpsDivCpopHelpers
public import LeanQbe.T.Examples.Bitblast.Proof.OpsDivCpop0
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
## Modular Helpers for Addition & Popcount Layer (`OpsDivCpop2Helpers`)

Provides C0 AST sub-expressions, memory helpers, and loop `wp` lemmas for
`bv_blast_add_into` and `bv_blast_cpop_layer`.
-/

section

attribute [local c0_load] load_hdr_oom load_hdr_lits_ptr load_hdr_lits_len load_hdr_lits_cap
attribute [local c0_store] store_hdr_oom store_hdr_lits_len

public theorem wp_load_lits_dc {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
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

public theorem wp_store_lits_dc {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
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

public theorem bv_add_oom_ret_false_wp {Γ : Env} {h : Val i64} {a_off b_off out_off w : Val i32}
    {Q : Post [Ty.bool]} {X : XPost} {hdr hdr_prev hdr' : BVHdrState} {g g_prev g' : Aig}
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
      (hdr.oom ≠ 0#32 → hdr''.oom ≠ 0#32) → (ret = true ↔ hdr''.oom = 0#32) →
      (hdr.oom = 0#32 → hdr.lits_len.toNat ≤ hdr.lits_cap.toNat →
        (0 < w.toNat → hdr.lits_ptr ≠ 0#64) →
        a_off.toNat + w.toNat ≤ hdr.lits_len.toNat →
        b_off.toNat + w.toNat ≤ hdr.lits_len.toNat →
        out_off.toNat + w.toNat ≤ hdr.lits_len.toNat →
        g.A + 1 + g.nodes.size + 9 * w.toNat ≤ hdr.aig_cap.toNat →
        g.nodes.size + 9 * w.toNat ≤ bvMaxGates → hdr''.oom = 0#32) →
      (ret = true →
        SliceLitsWf hdr'' lp'' out_off.toNat w.toNat ∧
        ∀ ρ, sliceVal g'' ρ lp'' out_off.toNat w.toNat =
          sliceVal g ρ litsPool a_off.toNat w.toNat +
            sliceVal g ρ litsPool b_off.toNat w.toNat) →
      (bvHdrMem h hdr'' ⋆ array64 hdr''.aig_ptr aw'' ⋆
        array (t := i32) hdr''.ht_ptr ht'' ⋆ array (t := i32) hdr''.lits_ptr lp'' ⋆ R) m'' →
      Q (ret, ⟨⟩) m'') :
    wp Γ Q X (Expr.ret (Arg.imm (t := Ty.bool) false, ())) m' := by
  c0_hfast_nogrp
  exact hpost false hdr' g' aw' ht' lp1 m' hf' hg' hsz' hinv' hlen1
    (fun p hp => hagree1 p (by
      rcases hp with hp | hp
      · exact Or.inl hp
      · exact Or.inr (by omega)))
    (fun hne => absurd ho hne)
    ⟨fun htf => absurd htf (by decide), fun hz => absurd hz hoom'⟩
    (fun _ _ _ _ _ _ ha hb => by
      exfalso
      apply hnofit
      · have hA : g.A = g_prev.A := hg_prev.1
        rw [hf_prev.aig_cap, ← hA]; omega
      · omega)
    (fun htf => absurd htf (by decide)) hm'

public abbrev addCarryStepExpr (h : Val i64) (w a_lit b_lit s0_lit carry_lit j_bv : Val i32)
    (loopJ : Cont [i32, i32]) : Expr Val Cont [Ty.bool] :=
  Expr.group
    (fun Js_1 => Blocks.cons
      (fun p : Tup Val [i32] =>
        Expr.let_ (op2 (OpCode.add i32) (Arg.var j_bv) (Arg.imm 1#32)) fun p_27 =>
        Expr.jump loopJ (Arg.var p.fst, Arg.var p_27.fst, ()))
      Blocks.nil)
    (fun Js_1 =>
      Expr.let_ (op2 (OpCode.add i32) (Arg.var j_bv) (Arg.imm 1#32)) fun p_27 =>
      Expr.let_ (op2 (OpCode.cmp CmpOp.ult i32 Ty.bool (by decide))
        (Arg.var p_27.fst) (Arg.var w)) fun p_28 =>
      Expr.jnz (Arg.var p_28.fst)
        (Expr.call (as := [i64, i32, i32]) (bs := [i32]) "bv_mk_and"
          (Arg.var h, Arg.var s0_lit, Arg.var carry_lit, ()) fun p_29 =>
          Expr.let_ (op2 (OpCode.add i64) (Arg.var h) (Arg.imm 120#64)) fun p_30 =>
          Expr.load i32 (Arg.var p_30.fst) fun ld =>
          Expr.let_ (op2 (OpCode.cmp CmpOp.ne i32 Ty.bool (by decide))
            (Arg.var ld) (Arg.imm 0#32)) fun p_31 =>
          Expr.jnz (Arg.var p_31.fst) (Expr.ret (Arg.imm (t := Ty.bool) false, ()))
            (Expr.call (as := [i64, i32, i32]) (bs := [i32]) "bv_mk_and"
              (Arg.var h, Arg.var a_lit, Arg.var b_lit, ()) fun p_32 =>
              Expr.let_ (op2 (OpCode.add i64) (Arg.var h) (Arg.imm 120#64)) fun p_33 =>
              Expr.load i32 (Arg.var p_33.fst) fun ld =>
              Expr.let_ (op2 (OpCode.cmp CmpOp.ne i32 Ty.bool (by decide))
                (Arg.var ld) (Arg.imm 0#32)) fun p_34 =>
              Expr.jnz (Arg.var p_34.fst) (Expr.ret (Arg.imm (t := Ty.bool) false, ()))
                (Expr.call (as := [i64, i32, i32]) (bs := [i32]) "bv_aig_or"
                  (Arg.var h, Arg.var p_29.fst, Arg.var p_32.fst, ()) fun p_35 =>
                  Expr.let_ (op2 (OpCode.add i64) (Arg.var h) (Arg.imm 120#64)) fun p =>
                  Expr.load i32 (Arg.var p.fst) fun ld =>
                  Expr.let_ (op2 (OpCode.cmp CmpOp.ne i32 Ty.bool (by decide))
                    (Arg.var ld) (Arg.imm 0#32)) fun p =>
                  Expr.jnz (Arg.var p.fst) (Expr.ret (Arg.imm (t := Ty.bool) false, ()))
                    (Expr.jump Js_1.fst (Arg.var p_35.fst, ())))))
        (Expr.jump Js_1.fst (Arg.var carry_lit, ())))

public abbrev addLoopExpr (h : Val i64) (a_off b_off out_off w : Val i32) (ld : Val i64) :
    Expr Val Cont [Ty.bool] :=
  Expr.group
    (fun Js => Blocks.cons
      (fun p_7 : Tup Val [i32, i32] =>
        Expr.let_ (op2 (OpCode.cmp CmpOp.ult i32 Ty.bool (by decide))
          (Arg.var p_7.snd.fst) (Arg.var w)) fun p_8 =>
        Expr.jnz (Arg.var p_8.fst)
          (Expr.let_ (op2 (OpCode.add i32) (Arg.var a_off) (Arg.var p_7.snd.fst)) fun p_9 =>
          Expr.let_ (op1 (OpCode.zext 32 64) (Arg.var p_9.fst)) fun p_10 =>
          Expr.let_ (op2 (OpCode.mul i64) (Arg.var p_10.fst) (Arg.imm 4#64)) fun p_11 =>
          Expr.let_ (op2 (OpCode.add i64) (Arg.var ld) (Arg.var p_11.fst)) fun p_12 =>
          Expr.load i32 (Arg.var p_12.fst) fun ld_1 =>
          Expr.let_ (op2 (OpCode.add i32) (Arg.var b_off) (Arg.var p_7.snd.fst)) fun p_13 =>
          Expr.let_ (op1 (OpCode.zext 32 64) (Arg.var p_13.fst)) fun p_14 =>
          Expr.let_ (op2 (OpCode.mul i64) (Arg.var p_14.fst) (Arg.imm 4#64)) fun p_15 =>
          Expr.let_ (op2 (OpCode.add i64) (Arg.var ld) (Arg.var p_15.fst)) fun p_16 =>
          Expr.load i32 (Arg.var p_16.fst) fun ld_2 =>
          Expr.call (as := [i64, i32, i32]) (bs := [i32]) "bv_aig_xor"
            (Arg.var h, Arg.var ld_1, Arg.var ld_2, ()) fun p_17 =>
          Expr.let_ (op2 (OpCode.add i64) (Arg.var h) (Arg.imm 120#64)) fun p_18 =>
          Expr.load i32 (Arg.var p_18.fst) fun ld_3 =>
          Expr.let_ (op2 (OpCode.cmp CmpOp.ne i32 Ty.bool (by decide))
            (Arg.var ld_3) (Arg.imm 0#32)) fun p_19 =>
          Expr.jnz (Arg.var p_19.fst) (Expr.ret (Arg.imm (t := Ty.bool) false, ()))
            (Expr.call (as := [i64, i32, i32]) (bs := [i32]) "bv_aig_xor"
              (Arg.var h, Arg.var p_17.fst, Arg.var p_7.fst, ()) fun p_20 =>
            Expr.let_ (op2 (OpCode.add i64) (Arg.var h) (Arg.imm 120#64)) fun p_21 =>
            Expr.load i32 (Arg.var p_21.fst) fun ld_4 =>
            Expr.let_ (op2 (OpCode.cmp CmpOp.ne i32 Ty.bool (by decide))
              (Arg.var ld_4) (Arg.imm 0#32)) fun p_22 =>
            Expr.jnz (Arg.var p_22.fst) (Expr.ret (Arg.imm (t := Ty.bool) false, ()))
              (Expr.let_ (op2 (OpCode.add i32) (Arg.var out_off) (Arg.var p_7.snd.fst)) fun p_23 =>
              Expr.let_ (op1 (OpCode.zext 32 64) (Arg.var p_23.fst)) fun p_24 =>
              Expr.let_ (op2 (OpCode.mul i64) (Arg.var p_24.fst) (Arg.imm 4#64)) fun p_25 =>
              Expr.let_ (op2 (OpCode.add i64) (Arg.var ld) (Arg.var p_25.fst)) fun p_26 =>
              Expr.store (Arg.var p_20.fst) (Arg.var p_26.fst)
                (addCarryStepExpr h w ld_1 ld_2 p_17.fst p_7.fst p_7.snd.fst Js.fst))))
          (Expr.ret (Arg.imm (t := Ty.bool) true, ())))
      Blocks.nil)
    (fun Js => Expr.jump Js.fst (Arg.imm 0#32, Arg.imm 0#32, ()))

private theorem bv_add_carry_step_wp (Γ : Env)
    (hΓ_and : Γ.Has "bv_mk_and" bvMkAndSpec)
    (hΓ_or : Γ.Has "bv_aig_or" bvAigOrSpec)
    {h : Val i64} {a_off b_off out_off w a_lit b_lit s0 carry : BitVec 32} {j : Nat}
    {hdr hdr3 : BVHdrState} {g g3 : Aig}
    {aw3 : List (BitVec 64)} {ht3 lp2 litsPool : List (BitVec 32)}
    {R : Mem 64 → Prop} {m3 : Mem 64} {Q : Post [Ty.bool]} {X : XPost}
    {loopJ : Cont [i32, i32]}
    (ho : hdr.oom = 0#32)
    (hjlt : j < w.toNat) (_hw32 : w.toNat < 2 ^ 32)
    (hf3 : hdr.AigFrame hdr3) (hg3 : g ≤ g3) (hsz3 : g3.nodes.size ≤ g.nodes.size + 9 * j + 6)
    (hinv3 : AigInv hdr3 g3 aw3 ht3) (ho3 : hdr3.oom = 0#32)
    (hlen2 : lp2.length = litsPool.length)
    (hagree2 : ∀ p, p < out_off.toNat ∨ out_off.toNat + (j + 1) ≤ p →
      lp2.getD p 0#32 = litsPool.getD p 0#32)
    (ha_wf3 : (a_lit >>> 1).toNat < hdr3.aig_len.toNat)
    (hb_wf3 : (b_lit >>> 1).toNat < hdr3.aig_len.toNat)
    (hs0_wf3 : (s0 >>> 1).toNat < hdr3.aig_len.toNat)
    (hc_wf3 : (carry >>> 1).toNat < hdr3.aig_len.toNat)
    (ha_eval : ∀ ρ, g3.evalLit ρ (UInt32.ofBitVec a_lit) =
      (sliceVal g ρ litsPool a_off.toNat w.toNat).getLsbD j)
    (hb_eval : ∀ ρ, g3.evalLit ρ (UInt32.ofBitVec b_lit) =
      (sliceVal g ρ litsPool b_off.toNat w.toNat).getLsbD j)
    (hs0_eval : ∀ ρ, g3.evalLit ρ (UInt32.ofBitVec s0) =
      ((sliceVal g ρ litsPool a_off.toNat w.toNat).getLsbD j ^^
        (sliceVal g ρ litsPool b_off.toNat w.toNat).getLsbD j))
    (hc_eval : ∀ ρ, g3.evalLit ρ (UInt32.ofBitVec carry) =
      BitVec.carry j (sliceVal g ρ litsPool a_off.toNat w.toNat)
        (sliceVal g ρ litsPool b_off.toNat w.toNat) false)
    (hm3 : (bvHdrMem h hdr3 ⋆ array64 hdr3.aig_ptr aw3 ⋆
      array (t := i32) hdr3.ht_ptr ht3 ⋆ array (t := i32) hdr3.lits_ptr lp2 ⋆ R) m3)
    (hpost : ∀ ret hdr'' g'' aw'' ht'' lp'' m'',
      hdr.AigFrame hdr'' → g ≤ g'' → g''.nodes.size ≤ g.nodes.size + 9 * w.toNat →
      AigInv hdr'' g'' aw'' ht'' → lp''.length = litsPool.length →
      (∀ p, p < out_off.toNat ∨ out_off.toNat + w.toNat ≤ p →
        lp''.getD p 0#32 = litsPool.getD p 0#32) →
      (hdr.oom ≠ 0#32 → hdr''.oom ≠ 0#32) → (ret = true ↔ hdr''.oom = 0#32) →
      (hdr.oom = 0#32 → hdr.lits_len.toNat ≤ hdr.lits_cap.toNat →
        (0 < w.toNat → hdr.lits_ptr ≠ 0#64) →
        a_off.toNat + w.toNat ≤ hdr.lits_len.toNat →
        b_off.toNat + w.toNat ≤ hdr.lits_len.toNat →
        out_off.toNat + w.toNat ≤ hdr.lits_len.toNat →
        g.A + 1 + g.nodes.size + 9 * w.toNat ≤ hdr.aig_cap.toNat →
        g.nodes.size + 9 * w.toNat ≤ bvMaxGates → hdr''.oom = 0#32) →
      (ret = true →
        SliceLitsWf hdr'' lp'' out_off.toNat w.toNat ∧
        ∀ ρ, sliceVal g'' ρ lp'' out_off.toNat w.toNat =
          sliceVal g ρ litsPool a_off.toNat w.toNat +
            sliceVal g ρ litsPool b_off.toNat w.toNat) →
      (bvHdrMem h hdr'' ⋆ array64 hdr''.aig_ptr aw'' ⋆
        array (t := i32) hdr''.ht_ptr ht'' ⋆ array (t := i32) hdr''.lits_ptr lp'' ⋆ R) m'' →
      Q (ret, ⟨⟩) m'')
    (hnext : ∀ (nextCarry : Val i32) hdr' g' aw' ht' m',
      hdr.AigFrame hdr' → g3 ≤ g' → g'.nodes.size ≤ g.nodes.size + 9 * (j + 1) →
      AigInv hdr' g' aw' ht' → hdr'.oom = 0#32 →
      (j + 1 < w.toNat → (nextCarry >>> 1).toNat < hdr'.aig_len.toNat ∧
        ∀ ρ, g'.evalLit ρ (UInt32.ofBitVec nextCarry) =
          BitVec.carry (j + 1) (sliceVal g ρ litsPool a_off.toNat w.toNat)
            (sliceVal g ρ litsPool b_off.toNat w.toNat) false) →
      (bvHdrMem h hdr' ⋆ array64 hdr'.aig_ptr aw' ⋆
        array (t := i32) hdr'.ht_ptr ht' ⋆ array (t := i32) hdr'.lits_ptr lp2 ⋆ R) m' →
      loopJ (nextCarry, BitVec.ofNat 32 (j + 1), ()) m') :
    wp Γ Q X (addCarryStepExpr h w a_lit b_lit s0 carry (BitVec.ofNat 32 j) loopJ) m3 := by
  let InvN : BitVec 32 → Mem 64 → Prop := fun nc ml =>
    ∃ hdr' g' aw' ht', hdr.AigFrame hdr' ∧ g3 ≤ g' ∧ g'.nodes.size ≤ g.nodes.size + 9 * (j + 1) ∧
      AigInv hdr' g' aw' ht' ∧ hdr'.oom = 0#32 ∧
      (j + 1 < w.toNat → (nc >>> 1).toNat < hdr'.aig_len.toNat ∧
        ∀ ρ, g'.evalLit ρ (UInt32.ofBitVec nc) =
          BitVec.carry (j + 1) (sliceVal g ρ litsPool a_off.toNat w.toNat)
            (sliceVal g ρ litsPool b_off.toNat w.toNat) false) ∧
      (bvHdrMem h hdr' ⋆ array64 hdr'.aig_ptr aw' ⋆
        array (t := i32) hdr'.ht_ptr ht' ⋆ array (t := i32) hdr'.lits_ptr lp2 ⋆ R) ml
  dsimp only [addCarryStepExpr]
  have hjn : (BitVec.ofNat 32 j).toNat = j := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hj1 : BitVec.ofNat 32 j + 1#32 = BitVec.ofNat 32 (j + 1) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, hjn, show (1#32 : BitVec 32).toNat = 1 from rfl,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hj1n : (BitVec.ofNat 32 (j + 1)).toNat = j + 1 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  apply wp_join_state1 (fun st : BitVec 32 => st) InvN
  · intro _ st ml ⟨hdr', g', aw', ht', hf', hg', hsz', hinv', ho', hnc', hml⟩
    c0_hfast_nogrp
    rw [hj1]
    exact hnext st hdr' g' aw' ht' ml hf' hg' hsz' hinv' ho' hnc' hml
  · intro J1 hJ1
    by_cases hlt1 : j + 1 < w.toNat
    · c0_hfast_nogrp
      · refine aigBinOom_wp Γ hΓ_and hinv3 ho3 hs0_wf3 hc_wf3 hm3 ?_ ?_
        · intro hdr4 g4 aw4 ht4 m4 hf34 hg34 hsz34 hinv4 hoom4 hnofit hm4
          exact bv_add_oom_ret_false_wp ho hf3 hg3 (by omega) (hf3.trans hf34)
            (Aig.extends_trans hg3 hg34) (by omega) hinv4 hlen2 hagree2 (by omega)
            hoom4 hnofit hm4 hpost
        · intro cs hdr4 g4 aw4 ht4 m4 hf34 hg34 hsz34 hinv4 ho4 hcs_wf hcs_eval hm4
          have hf4 := hf3.trans hf34
          have hg4 := Aig.extends_trans hg3 hg34
          have haig34 : hdr3.aig_len.toNat ≤ hdr4.aig_len.toNat := by
            have hA := hg34.1; have hs := hg34.2.1; rw [hinv3.aig_len_eq, hinv4.aig_len_eq, hA]
            omega
          refine aigBinOom_wp Γ hΓ_and hinv4 ho4 (Nat.lt_of_lt_of_le ha_wf3 haig34)
            (Nat.lt_of_lt_of_le hb_wf3 haig34) hm4 ?_ ?_
          · intro hdr5 g5 aw5 ht5 m5 hf45 hg45 hsz45 hinv5 hoom5 hnofit hm5
            exact bv_add_oom_ret_false_wp ho hf4 hg4 (by omega) (hf4.trans hf45)
              (Aig.extends_trans hg4 hg45) (by omega) hinv5 hlen2 hagree2 (by omega)
              hoom5 hnofit hm5 hpost
          · intro ab hdr5 g5 aw5 ht5 m5 hf45 hg45 hsz45 hinv5 ho5 hab_wf hab_eval hm5
            have hf5 := hf4.trans hf45
            have hg5 := Aig.extends_trans hg4 hg45
            have haig45 : hdr4.aig_len.toNat ≤ hdr5.aig_len.toNat := by
              have hA := hg45.1; have hs := hg45.2.1; rw [hinv4.aig_len_eq, hinv5.aig_len_eq, hA]
              omega
            refine aigBinOom_wp Γ hΓ_or hinv5 ho5 (Nat.lt_of_lt_of_le hcs_wf haig45) hab_wf hm5
              ?_ ?_
            · intro hdr6 g6 aw6 ht6 m6 hf56 hg56 hsz56 hinv6 hoom6 hnofit hm6
              exact bv_add_oom_ret_false_wp ho hf5 hg5 (by omega) (hf5.trans hf56)
                (Aig.extends_trans hg5 hg56) (by omega) hinv6 hlen2 hagree2 (by omega)
                hoom6 hnofit hm6 hpost
            · intro carry' hdr6 g6 aw6 ht6 m6 hf56 hg56 hsz56 hinv6 ho6 hc'_wf hc'_eval hm6
              c0_hfast_nogrp
              apply hJ1 carry' m6 ⟨hdr6, g6, aw6, ht6, hf5.trans hf56,
                Aig.extends_trans hg34 (Aig.extends_trans hg45 hg56),
                by omega, hinv6, ho6, fun _ => ⟨hc'_wf, ?_⟩, hm6⟩
              intro ρ
              have hg345 : g3 ≤ g5 := Aig.extends_trans hg34 hg45
              have hg34_lt : ∀ {v : BitVec 32}, (v >>> 1).toNat < hdr3.aig_len.toNat →
                  (UInt32.ofBitVec v).toNat < 2 * (g3.A + 1 + g3.nodes.size) := fun hv => by
                rw [hinv3.aig_len_eq] at hv; exact lit_toNat_lt_of_shift hv
              have hcs_lt4 : (UInt32.ofBitVec cs).toNat < 2 * (g4.A + 1 + g4.nodes.size) := by
                rw [hinv4.aig_len_eq] at hcs_wf; exact lit_toNat_lt_of_shift hcs_wf
              rw [hc'_eval ρ, Aig.evalLit_extend hg45 hcs_lt4, hcs_eval ρ, hab_eval ρ,
                Aig.evalLit_extend hg34 (hg34_lt ha_wf3),
                Aig.evalLit_extend hg34 (hg34_lt hb_wf3),
                hs0_eval ρ, hc_eval ρ, ha_eval ρ, hb_eval ρ, BitVec.carry_succ]
              cases (sliceVal g ρ litsPool a_off.toNat w.toNat).getLsbD j <;>
                cases (sliceVal g ρ litsPool b_off.toNat w.toNat).getLsbD j <;>
                cases BitVec.carry j (sliceVal g ρ litsPool a_off.toNat w.toNat)
                  (sliceVal g ρ litsPool b_off.toNat w.toNat) false <;> rfl
      · exfalso; omega
    · c0_hfast_nogrp
      · exfalso; omega
      · apply hJ1 carry m3 ⟨hdr3, g3, aw3, ht3, hf3, Aig.extends_rfl g3, by omega, hinv3, ho3,
          fun hbad => False.elim (hlt1 hbad), hm3⟩

public theorem bv_add_loop_wp (Γ : Env)
    (hΓ_xor : Γ.Has "bv_aig_xor" bvAigXorSpec)
    (hΓ_and : Γ.Has "bv_mk_and" bvMkAndSpec)
    (hΓ_or : Γ.Has "bv_aig_or" bvAigOrSpec)
    {h : Val i64} {a_off b_off out_off w : Val i32} {ld : Val i64}
    {hdr : BVHdrState} {g : Aig} {aigWords : List (BitVec 64)}
    {htSlots litsPool : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64}
    {Q : Post [Ty.bool]} {X : XPost}
    (hinv : AigInv hdr g aigWords htSlots) (hld : ld = hdr.lits_ptr)
    (hlcap : hdr.lits_cap.toNat ≤ litsPool.length) (ho : hdr.oom = 0#32)
    (hlencap : hdr.lits_len.toNat ≤ hdr.lits_cap.toNat)
    (haw : a_off.toNat + w.toNat ≤ hdr.lits_len.toNat)
    (hbw : b_off.toNat + w.toNat ≤ hdr.lits_len.toNat)
    (how : out_off.toNat + w.toNat ≤ hdr.lits_len.toNat)
    (ha_wf : SliceLitsWf hdr litsPool a_off.toNat w.toNat)
    (hb_wf : SliceLitsWf hdr litsPool b_off.toNat w.toNat)
    (hdisj_a : DisjointSlice out_off.toNat w.toNat a_off.toNat w.toNat)
    (hdisj_b : DisjointSlice out_off.toNat w.toNat b_off.toNat w.toNat)
    (hm : (bvHdrMem h hdr ⋆ array64 hdr.aig_ptr aigWords ⋆
      array (t := i32) hdr.ht_ptr htSlots ⋆ array (t := i32) hdr.lits_ptr litsPool ⋆ R) m)
    (hpost : ∀ ret hdr' g' aigWords' htSlots' litsPool' m',
      hdr.AigFrame hdr' → g ≤ g' → g'.nodes.size ≤ g.nodes.size + 9 * w.toNat →
      AigInv hdr' g' aigWords' htSlots' → litsPool'.length = litsPool.length →
      (∀ p, p < out_off.toNat ∨ out_off.toNat + w.toNat ≤ p →
        litsPool'.getD p 0#32 = litsPool.getD p 0#32) →
      (hdr.oom ≠ 0#32 → hdr'.oom ≠ 0#32) → (ret = true ↔ hdr'.oom = 0#32) →
      (hdr.oom = 0#32 → hdr.lits_len.toNat ≤ hdr.lits_cap.toNat →
        (0 < w.toNat → hdr.lits_ptr ≠ 0#64) →
        a_off.toNat + w.toNat ≤ hdr.lits_len.toNat →
        b_off.toNat + w.toNat ≤ hdr.lits_len.toNat →
        out_off.toNat + w.toNat ≤ hdr.lits_len.toNat →
        g.A + 1 + g.nodes.size + 9 * w.toNat ≤ hdr.aig_cap.toNat →
        g.nodes.size + 9 * w.toNat ≤ bvMaxGates → hdr'.oom = 0#32) →
      (ret = true → SliceLitsWf hdr' litsPool' out_off.toNat w.toNat ∧
        ∀ ρ, sliceVal g' ρ litsPool' out_off.toNat w.toNat =
          sliceVal g ρ litsPool a_off.toNat w.toNat +
            sliceVal g ρ litsPool b_off.toNat w.toNat) →
      (bvHdrMem h hdr' ⋆ array64 hdr'.aig_ptr aigWords' ⋆
        array (t := i32) hdr'.ht_ptr htSlots' ⋆
        array (t := i32) hdr'.lits_ptr litsPool' ⋆ R) m' →
      Q (ret, ⟨⟩) m') :
    wp Γ Q X (addLoopExpr h a_off b_off out_off w ld) m := by
  subst hld
  have hw32 : w.toNat < 2 ^ 32 := w.isLt
  have hcap32 : hdr.lits_cap.toNat < 2 ^ 32 := hdr.lits_cap.isLt
  let Inv : (Nat × Val i32 × BVHdrState × Aig × List (BitVec 64) ×
      List (BitVec 32) × List (BitVec 32)) → Mem 64 → Prop := fun st m1 =>
    let (j, carry, hdr1, g1, aw1, ht1, lp1) := st
    hdr.AigFrame hdr1 ∧ g ≤ g1 ∧ g1.nodes.size ≤ g.nodes.size + 9 * j ∧
    AigInv hdr1 g1 aw1 ht1 ∧ lp1.length = litsPool.length ∧ j ≤ w.toNat ∧ hdr1.oom = 0#32 ∧
    (j < w.toNat → (carry >>> 1).toNat < hdr1.aig_len.toNat ∧
      ∀ ρ, g1.evalLit ρ (UInt32.ofBitVec carry) =
        BitVec.carry j (sliceVal g ρ litsPool a_off.toNat w.toNat)
          (sliceVal g ρ litsPool b_off.toNat w.toNat) false) ∧
    (∀ p, p < out_off.toNat ∨ out_off.toNat + j ≤ p → lp1.getD p 0#32 = litsPool.getD p 0#32) ∧
    (∀ k, k < j → ((lp1.getD (out_off.toNat + k) 0#32) >>> 1).toNat < hdr1.aig_len.toNat) ∧
    (∀ k, k < j → ∀ ρ,
      g1.evalLit ρ (UInt32.ofBitVec (lp1.getD (out_off.toNat + k) 0#32)) =
        (sliceVal g ρ litsPool a_off.toNat w.toNat +
          sliceVal g ρ litsPool b_off.toNat w.toNat).getLsbD k) ∧
    (bvHdrMem h hdr1 ⋆ array64 hdr1.aig_ptr aw1 ⋆
      array (t := i32) hdr1.ht_ptr ht1 ⋆ array (t := i32) hdr1.lits_ptr lp1 ⋆ R) m1
  dsimp only [addLoopExpr]
  refine ProofKit.c0_while_state
    (fun st : Nat × Val i32 × BVHdrState × Aig × List (BitVec 64) ×
        List (BitVec 32) × List (BitVec 32) => (st.2.1, BitVec.ofNat 32 st.1, ()))
    (fun st => w.toNat - st.1) Inv ?_ ?_
  · intro J hJ
    refine hJ (0, 0#32, hdr, g, aigWords, htSlots, litsPool) m
      ⟨BVHdrState.AigFrame.rfl _, Aig.extends_rfl g, by dsimp; omega, hinv, rfl,
        Nat.zero_le _, ho,
        fun _ => ⟨by rw [hinv.aig_len_eq]; simp; omega,
          fun ρ => by rw [evalLit_zero, BitVec.carry_zero]⟩,
        fun _ _ => rfl, fun _ hk => False.elim (Nat.not_lt_zero _ hk),
        fun _ hk => False.elim (Nat.not_lt_zero _ hk), hm⟩
  · intro J st m1
      ⟨hf1, hg1, hsz1, hinv1, hlen1, hjle, ho1, hc1, hagree1, hwf1, heval1, hm1⟩ hjind
    rcases st with ⟨j, carry, hdr1, g1, aw1, ht1, lp1⟩
    dsimp only at *
    have hjn : (BitVec.ofNat 32 j).toNat = j := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    c0_hsplit
    · have hjlt : j < w.toNat := by rw [← hjn]; exact hc
      obtain ⟨hcarry_wf1, hcarry_eval1⟩ := hc1 hjlt
      have ha_idx : (a_off + BitVec.ofNat 32 j).toNat = a_off.toNat + j := by
        rw [BitVec.toNat_add, hjn, Nat.mod_eq_of_lt (by omega)]
      have hb_idx : (b_off + BitVec.ofNat 32 j).toNat = b_off.toNat + j := by
        rw [BitVec.toNat_add, hjn, Nat.mod_eq_of_lt (by omega)]
      have ho_idx : (out_off + BitVec.ofNat 32 j).toNat = out_off.toNat + j := by
        rw [BitVec.toNat_add, hjn, Nat.mod_eq_of_lt (by omega)]
      have hm1' : (bvHdrMem h hdr1 ⋆ array64 hdr1.aig_ptr aw1 ⋆
          array (t := i32) hdr1.ht_ptr ht1 ⋆ array (t := i32) hdr1.lits_ptr lp1 ⋆ R) m1 :=
        hm1
      c0_hstraight
      apply wp_load_lits_dc hm1' (idx := a_off + BitVec.ofNat 32 j)
        (by dsimp [Arg.val]; rw [hf1.lits_ptr]) (by omega)
      c0_hstraight
      apply wp_load_lits_dc hm1' (idx := b_off + BitVec.ofNat 32 j)
        (by dsimp [Arg.val]; rw [hf1.lits_ptr]) (by omega)
      have ha_get : lp1.getD (a_off + BitVec.ofNat 32 j).toNat 0#32 =
          litsPool.getD (a_off.toNat + j) 0#32 := by
        rw [ha_idx]; apply hagree1; unfold DisjointSlice at hdisj_a; omega
      have hb_get : lp1.getD (b_off + BitVec.ofNat 32 j).toNat 0#32 =
          litsPool.getD (b_off.toNat + j) 0#32 := by
        rw [hb_idx]; apply hagree1; unfold DisjointSlice at hdisj_b; omega
      have haig01 : hdr.aig_len.toNat ≤ hdr1.aig_len.toNat := by
        have hA := hg1.1; have hs := hg1.2.1; rw [hinv.aig_len_eq, hinv1.aig_len_eq, hA]; omega
      have ha_lt1 : (lp1.getD (a_off + BitVec.ofNat 32 j).toNat 0#32 >>> 1).toNat <
          hdr1.aig_len.toNat := by
        rw [ha_get]; exact Nat.lt_of_lt_of_le (ha_wf.2 j hjlt) haig01
      have hb_lt1 : (lp1.getD (b_off + BitVec.ofNat 32 j).toNat 0#32 >>> 1).toNat <
          hdr1.aig_len.toNat := by
        rw [hb_get]; exact Nat.lt_of_lt_of_le (hb_wf.2 j hjlt) haig01
      refine aigBinOom_wp Γ hΓ_xor hinv1 ho1 ha_lt1 hb_lt1 hm1' ?_ ?_
      · intro hdr2 g2 aw2 ht2 m2 hf12 hg12 hsz12 hinv2 hoom2 hnofit hm2
        exact bv_add_oom_ret_false_wp ho hf1 hg1 (by omega) (hf1.trans hf12)
          (Aig.extends_trans hg1 hg12) (by omega) hinv2 hlen1 hagree1 (by omega)
          hoom2 hnofit hm2 hpost
      · intro s0 hdr2 g2 aw2 ht2 m2 hf12 hg12 hsz12 hinv2 ho2 hs0_wf hs0_eval hm2
        have haig12 : hdr1.aig_len.toNat ≤ hdr2.aig_len.toNat := by
          have hA := hg12.1; have hs := hg12.2.1; rw [hinv1.aig_len_eq, hinv2.aig_len_eq, hA]; omega
        have hc_wf2 : (carry >>> 1).toNat < hdr2.aig_len.toNat :=
          Nat.lt_of_lt_of_le hcarry_wf1 haig12
        have hf2 := hf1.trans hf12
        have hg2 := Aig.extends_trans hg1 hg12
        refine aigBinOom_wp Γ hΓ_xor hinv2 ho2 hs0_wf hc_wf2 hm2 ?_ ?_
        · intro hdr3 g3 aw3 ht3 m3 hf23 hg23 hsz23 hinv3 hoom3 hnofit hm3
          exact bv_add_oom_ret_false_wp ho hf2 hg2 (by omega) (hf2.trans hf23)
            (Aig.extends_trans hg2 hg23) (by omega) hinv3 hlen1 hagree1 (by omega)
            hoom3 hnofit hm3 hpost
        · intro sum hdr3 g3 aw3 ht3 m3 hf23 hg23 hsz23 hinv3 ho3 hsum_wf hsum_eval hm3
          have hf3 := hf2.trans hf23
          have hg3 := Aig.extends_trans hg2 hg23
          c0_hstraight
          apply wp_store_lits_dc hm3 (idx := out_off + BitVec.ofNat 32 j)
            (v := Arg.var sum) (by dsimp [Arg.val]; rw [hf3.lits_ptr]) (by omega)
          intro m3' hm3'
          rw [ho_idx] at hm3'
          let lp2 := lp1.set (out_off.toNat + j) sum
          have hlen2 : lp2.length = litsPool.length := by simp [lp2, hlen1]
          have hagree2 : ∀ p, p < out_off.toNat ∨ out_off.toNat + (j + 1) ≤ p →
              lp2.getD p 0#32 = litsPool.getD p 0#32 := fun p hp => by
            have hne : p ≠ out_off.toNat + j := by omega
            dsimp only [lp2]; rw [list_getD_set_ne lp1 0#32 sum hne]
            exact hagree1 p (by
              rcases hp with hp | hp
              · exact Or.inl hp
              · exact Or.inr (by omega))
          have haig23 : hdr2.aig_len.toNat ≤ hdr3.aig_len.toNat := by
            have hA := hg23.1; have hs := hg23.2.1
            rw [hinv2.aig_len_eq, hinv3.aig_len_eq, hA]; omega
          have haig13 : hdr1.aig_len.toNat ≤ hdr3.aig_len.toNat := Nat.le_trans haig12 haig23
          have hg13 : g1 ≤ g3 := Aig.extends_trans hg12 hg23
          have hg03 : g ≤ g3 := Aig.extends_trans hg1 hg13
          have ha_lt_g : (UInt32.ofBitVec (litsPool.getD (a_off.toNat + j) 0#32)).toNat <
              2 * (g.A + 1 + g.nodes.size) := by
            have hlt := ha_wf.2 j hjlt; rw [hinv.aig_len_eq] at hlt
            exact lit_toNat_lt_of_shift hlt
          have hb_lt_g : (UInt32.ofBitVec (litsPool.getD (b_off.toNat + j) 0#32)).toNat <
              2 * (g.A + 1 + g.nodes.size) := by
            have hlt := hb_wf.2 j hjlt; rw [hinv.aig_len_eq] at hlt
            exact lit_toNat_lt_of_shift hlt
          have ha_eval3 : ∀ ρ, g3.evalLit ρ
              (UInt32.ofBitVec (lp1.getD (a_off + BitVec.ofNat 32 j).toNat 0#32)) =
              (sliceVal g ρ litsPool a_off.toNat w.toNat).getLsbD j := fun ρ => by
            rw [ha_get, Aig.evalLit_extend hg03 ha_lt_g, sliceVal_getLsbD hjlt]
          have hb_eval3 : ∀ ρ, g3.evalLit ρ
              (UInt32.ofBitVec (lp1.getD (b_off + BitVec.ofNat 32 j).toNat 0#32)) =
              (sliceVal g ρ litsPool b_off.toNat w.toNat).getLsbD j := fun ρ => by
            rw [hb_get, Aig.evalLit_extend hg03 hb_lt_g, sliceVal_getLsbD hjlt]
          have hs0_eval3 : ∀ ρ, g3.evalLit ρ (UInt32.ofBitVec s0) =
              ((sliceVal g ρ litsPool a_off.toNat w.toNat).getLsbD j ^^
                (sliceVal g ρ litsPool b_off.toNat w.toNat).getLsbD j) := fun ρ => by
            have hs0_lt2 : (UInt32.ofBitVec s0).toNat < 2 * (g2.A + 1 + g2.nodes.size) := by
              have hlt := hs0_wf; rw [hinv2.aig_len_eq] at hlt
              exact lit_toNat_lt_of_shift hlt
            rw [Aig.evalLit_extend hg23 hs0_lt2, hs0_eval ρ,
              ha_get, hb_get, Aig.evalLit_extend hg1 ha_lt_g,
              Aig.evalLit_extend hg1 hb_lt_g, sliceVal_getLsbD hjlt, sliceVal_getLsbD hjlt]
          have hc_eval3 : ∀ ρ, g3.evalLit ρ (UInt32.ofBitVec carry) =
              BitVec.carry j (sliceVal g ρ litsPool a_off.toNat w.toNat)
                (sliceVal g ρ litsPool b_off.toNat w.toNat) false := fun ρ => by
            have hc_lt1 : (UInt32.ofBitVec carry).toNat < 2 * (g1.A + 1 + g1.nodes.size) := by
              have hlt := hcarry_wf1; rw [hinv1.aig_len_eq] at hlt
              exact lit_toNat_lt_of_shift hlt
            rw [Aig.evalLit_extend hg13 hc_lt1, hcarry_eval1 ρ]
          have hs0_wf3 : (s0 >>> 1).toNat < hdr3.aig_len.toNat :=
            Nat.lt_of_lt_of_le hs0_wf haig23
          have hc_wf3 : (carry >>> 1).toNat < hdr3.aig_len.toNat :=
            Nat.lt_of_lt_of_le hc_wf2 haig23
          refine bv_add_carry_step_wp Γ hΓ_and hΓ_or ho hjlt hw32 hf3 hg3 (by omega) hinv3 ho3
            hlen2 hagree2 (Nat.lt_of_lt_of_le ha_lt1 haig13) (Nat.lt_of_lt_of_le hb_lt1 haig13)
            hs0_wf3 hc_wf3 ha_eval3 hb_eval3 hs0_eval3 hc_eval3 hm3' hpost ?_
          intro nextCarry hdr' g' aw' ht' m' hf' hg3' hsz' hinv' ho' hc' hm'
          have haig3' : hdr3.aig_len.toNat ≤ hdr'.aig_len.toNat := by
            have hA := hg3'.1; have hs := hg3'.2.1; rw [hinv3.aig_len_eq, hinv'.aig_len_eq, hA]
            omega
          have haig1' : hdr1.aig_len.toNat ≤ hdr'.aig_len.toNat := Nat.le_trans haig13 haig3'
          have hg2' : g2 ≤ g' := Aig.extends_trans hg23 hg3'
          have hg1' : g1 ≤ g' := Aig.extends_trans hg12 hg2'
          refine hjind (j + 1, nextCarry, hdr', g', aw', ht', lp2) m' (by omega)
            ⟨hf', Aig.extends_trans hg1 hg1', by omega, hinv', hlen2, by omega,
              ho', hc', hagree2, ?_, ?_, hm'⟩
          · intro k hk
            by_cases hkj : k = j
            · subst hkj; dsimp only [lp2]
              rw [list_getD_set_self lp1 0#32 sum (by omega)]
              exact Nat.lt_of_lt_of_le hsum_wf haig3'
            · have hklt : k < j := by omega
              have hne : out_off.toNat + k ≠ out_off.toNat + j := by omega
              dsimp only [lp2]
              rw [list_getD_set_ne lp1 0#32 sum hne]
              exact Nat.lt_of_lt_of_le (hwf1 k hklt) haig1'
          · intro k hk ρ
            by_cases hkj : k = j
            · subst hkj; dsimp only [lp2]
              rw [list_getD_set_self lp1 0#32 sum (by omega)]
              have hsum_lt2 : (UInt32.ofBitVec sum).toNat < 2 * (g3.A + 1 + g3.nodes.size) := by
                have hlt := hsum_wf; rw [hinv3.aig_len_eq] at hlt; exact lit_toNat_lt_of_shift hlt
              have hc_lt1 :
                  (UInt32.ofBitVec carry).toNat < 2 * (g1.A + 1 + g1.nodes.size) := by
                have hlt := hcarry_wf1
                rw [hinv1.aig_len_eq] at hlt; exact lit_toNat_lt_of_shift hlt
              rw [Aig.evalLit_extend hg3' hsum_lt2, hsum_eval ρ]
              dsimp only
              rw [hs0_eval ρ, ha_get, hb_get, Aig.evalLit_extend hg1 ha_lt_g,
                Aig.evalLit_extend hg1 hb_lt_g, Aig.evalLit_extend hg12 hc_lt1,
                hcarry_eval1 ρ, bv_add_sum_getLsbD _ _ hjlt, sliceVal_getLsbD hjlt,
                sliceVal_getLsbD hjlt]
            · have hklt : k < j := by omega
              have hne : out_off.toNat + k ≠ out_off.toNat + j := by omega
              dsimp only [lp2]
              rw [list_getD_set_ne lp1 0#32 sum hne]
              have hlit1 : (UInt32.ofBitVec (lp1.getD (out_off.toNat + k) 0#32)).toNat <
                  2 * (g1.A + 1 + g1.nodes.size) := by
                have hlt := hwf1 k hklt; rw [hinv1.aig_len_eq] at hlt
                exact lit_toNat_lt_of_shift hlt
              rw [Aig.evalLit_extend hg1' hlit1]
              exact heval1 k hklt ρ
    · have hjge : j = w.toNat := by omega
      subst hjge
      c0_hfast_nogrp
      refine hpost true hdr1 g1 aw1 ht1 lp1 m1 hf1 hg1 hsz1 hinv1 hlen1
        hagree1 (fun hne => absurd ho hne) ⟨fun _ => ho1, fun _ => rfl⟩
        (fun _ _ _ _ _ _ _ _ => ho1) (fun _ => ?_) hm1
      refine ⟨⟨by rw [hf1.lits_len]; exact how, hwf1⟩, fun ρ => ?_⟩
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      rw [sliceVal_getLsbD hi, heval1 i hi ρ]

/-! ## `bv_blast_cpop_layer` helpers -/

public abbrev cpopLayerCopyExpr (w src_off dst_off : Val i32) (ld : Val i64)
    (exitJ : Cont []) : Expr Val Cont [Ty.bool] :=
  Expr.group
    (fun Js_1 => Blocks.cons
      (fun p_40 : Tup Val [i32] =>
        Expr.let_ (op2 (OpCode.cmp CmpOp.ult i32 Ty.bool (by decide))
          (Arg.var p_40.fst) (Arg.var w)) fun p =>
        Expr.jnz (Arg.var p.fst)
          (Expr.let_ (op2 (OpCode.add i32) (Arg.var dst_off) (Arg.var p_40.fst)) fun p =>
          Expr.let_ (op1 (OpCode.zext 32 64) (Arg.var p.fst)) fun p =>
          Expr.let_ (op2 (OpCode.mul i64) (Arg.var p.fst) (Arg.imm 4#64)) fun p =>
          Expr.let_ (op2 (OpCode.add i64) (Arg.var ld) (Arg.var p.fst)) fun p =>
          Expr.let_ (op2 (OpCode.add i32) (Arg.var src_off) (Arg.var p_40.fst)) fun p_41 =>
          Expr.let_ (op1 (OpCode.zext 32 64) (Arg.var p_41.fst)) fun p_42 =>
          Expr.let_ (op2 (OpCode.mul i64) (Arg.var p_42.fst) (Arg.imm 4#64)) fun p_43 =>
          Expr.let_ (op2 (OpCode.add i64) (Arg.var ld) (Arg.var p_43.fst)) fun p_44 =>
          Expr.load i32 (Arg.var p_44.fst) fun ld_3 =>
          Expr.store (Arg.var ld_3) (Arg.var p.fst)
            (Expr.let_ (op2 (OpCode.add i32) (Arg.var p_40.fst) (Arg.imm 1#32)) fun p =>
            Expr.jump Js_1.fst (Arg.var p.fst, ())))
          (Expr.jump exitJ ()))
      Blocks.nil)
    (fun Js_1 => Expr.jump Js_1.fst (Arg.imm 0#32, ()))

public abbrev cpopLayerLoopExpr (h : Val i64) (in_off out_off in_len w : Val i32)
    (out_len64 ld : Val i64) : Expr Val Cont [Ty.bool] :=
  Expr.group
    (fun Js => Blocks.cons
      (fun p_19 : Tup Val [i32] =>
        Expr.let_ (op1 (OpCode.zext 32 64) (Arg.var p_19.fst)) fun p_20 =>
        Expr.let_ (op2 (OpCode.cmp CmpOp.ult i64 Ty.bool (by decide))
          (Arg.var p_20.fst) (Arg.var out_len64)) fun p_21 =>
        Expr.jnz (Arg.var p_21.fst)
          (Expr.let_ (op1 (OpCode.zext 32 64) (Arg.var in_off)) fun p_22 =>
          Expr.let_ (op1 (OpCode.zext 32 64) (Arg.var p_19.fst)) fun p_23 =>
          Expr.let_ (op2 (OpCode.mul i64) (Arg.imm 2#64) (Arg.var p_23.fst)) fun p_24 =>
          Expr.let_ (op1 (OpCode.zext 32 64) (Arg.var w)) fun p_25 =>
          Expr.let_ (op2 (OpCode.mul i64) (Arg.var p_24.fst) (Arg.var p_25.fst)) fun p_26 =>
          Expr.let_ (op2 (OpCode.add i64) (Arg.var p_22.fst) (Arg.var p_26.fst)) fun p_27 =>
          Expr.let_ (op1 (OpCode.trunc 64 32) (Arg.var p_27.fst)) fun p_28 =>
          Expr.let_ (op1 (OpCode.zext 32 64) (Arg.var out_off)) fun p_29 =>
          Expr.let_ (op1 (OpCode.zext 32 64) (Arg.var p_19.fst)) fun p_30 =>
          Expr.let_ (op1 (OpCode.zext 32 64) (Arg.var w)) fun p_31 =>
          Expr.let_ (op2 (OpCode.mul i64) (Arg.var p_30.fst) (Arg.var p_31.fst)) fun p_32 =>
          Expr.let_ (op2 (OpCode.add i64) (Arg.var p_29.fst) (Arg.var p_32.fst)) fun p_33 =>
          Expr.let_ (op1 (OpCode.trunc 64 32) (Arg.var p_33.fst)) fun p_34 =>
          Expr.group
            (fun Js_1 => Blocks.cons
              (fun _ : Tup Val [] =>
                Expr.let_ (op2 (OpCode.add i32) (Arg.var p_19.fst) (Arg.imm 1#32)) fun p =>
                Expr.jump Js.fst (Arg.var p.fst, ()))
              Blocks.nil)
            (fun Js_1 =>
              Expr.let_ (op1 (OpCode.zext 32 64) (Arg.var p_19.fst)) fun p_35 =>
              Expr.let_ (op2 (OpCode.mul i64) (Arg.imm 2#64) (Arg.var p_35.fst)) fun p_36 =>
              Expr.let_ (op2 (OpCode.add i64) (Arg.var p_36.fst) (Arg.imm 1#64)) fun p_37 =>
              Expr.let_ (op1 (OpCode.zext 32 64) (Arg.var in_len)) fun p_38 =>
              Expr.let_ (op2 (OpCode.cmp CmpOp.ult i64 Ty.bool (by decide))
                (Arg.var p_37.fst) (Arg.var p_38.fst)) fun p_39 =>
              Expr.jnz (Arg.var p_39.fst)
                (Expr.let_ (op1 (OpCode.zext 32 64) (Arg.var in_off)) fun p_40 =>
                Expr.let_ (op1 (OpCode.zext 32 64) (Arg.var p_19.fst)) fun p_41 =>
                Expr.let_ (op2 (OpCode.mul i64) (Arg.imm 2#64) (Arg.var p_41.fst)) fun p_42 =>
                Expr.let_ (op2 (OpCode.add i64) (Arg.var p_42.fst) (Arg.imm 1#64)) fun p_43 =>
                Expr.let_ (op1 (OpCode.zext 32 64) (Arg.var w)) fun p_44 =>
                Expr.let_ (op2 (OpCode.mul i64) (Arg.var p_43.fst) (Arg.var p_44.fst)) fun p_45 =>
                Expr.let_ (op2 (OpCode.add i64) (Arg.var p_40.fst) (Arg.var p_45.fst)) fun p_46 =>
                Expr.let_ (op1 (OpCode.trunc 64 32) (Arg.var p_46.fst)) fun p_47 =>
                Expr.call (as := [i64, i32, i32, i32, i32]) (bs := [Ty.bool])
                  "bv_blast_add_into"
                  (Arg.var h, Arg.var p_28.fst, Arg.var p_47.fst, Arg.var p_34.fst,
                    Arg.var w, ()) fun p =>
                Expr.jnz (Arg.var p.fst)
                  (Expr.jump Js_1.fst ())
                  (Expr.ret (Arg.imm (t := Ty.bool) false, ())))
                (cpopLayerCopyExpr w p_28.fst p_34.fst ld Js_1.fst)))
          (Expr.ret (Arg.imm (t := Ty.bool) true, ())))
      Blocks.nil)
    (fun Js => Expr.jump Js.fst (Arg.imm 0#32, ()))

public theorem bv_cpop_layer_copy_wp (Γ : Env)
    {h : Val i64} {w src_off dst_off : BitVec 32} {ld : Val i64} {exitJ : Cont []}
    {hdr : BVHdrState} {g : Aig} {aw : List (BitVec 64)} {ht lp0 : List (BitVec 32)}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [Ty.bool]} {X : XPost}
    (hld : ld = hdr.lits_ptr)
    (hsrc : src_off.toNat + w.toNat ≤ hdr.lits_len.toNat)
    (hdst : dst_off.toNat + w.toNat ≤ hdr.lits_len.toNat)
    (hlencap : hdr.lits_len.toNat ≤ hdr.lits_cap.toNat)
    (hcaplen : hdr.lits_cap.toNat ≤ lp0.length)
    (hdisj : DisjointSlice dst_off.toNat w.toNat src_off.toNat w.toNat)
    (hwf_src : SliceLitsWf hdr lp0 src_off.toNat w.toNat)
    (hmem : (bvHdrMem h hdr ⋆ array64 hdr.aig_ptr aw ⋆
      array (t := i32) hdr.ht_ptr ht ⋆ array (t := i32) hdr.lits_ptr lp0 ⋆ R) m)
    (hexit : ∀ (lp' : List (BitVec 32)) (m' : Mem 64),
      lp'.length = lp0.length →
      (∀ p, p < dst_off.toNat ∨ dst_off.toNat + w.toNat ≤ p → lp'.getD p 0#32 = lp0.getD p 0#32) →
      SliceLitsWf hdr lp' dst_off.toNat w.toNat →
      (∀ ρ, sliceVal g ρ lp' dst_off.toNat w.toNat = sliceVal g ρ lp0 src_off.toNat w.toNat) →
      (bvHdrMem h hdr ⋆ array64 hdr.aig_ptr aw ⋆
        array (t := i32) hdr.ht_ptr ht ⋆ array (t := i32) hdr.lits_ptr lp' ⋆ R) m' →
      exitJ () m') :
    wp Γ Q X (cpopLayerCopyExpr w src_off dst_off ld exitJ) m := by
  subst hld
  have hcap32 : hdr.lits_cap.toNat < 2 ^ 32 := hdr.lits_cap.isLt
  let Inv : (Nat × List (BitVec 32)) → Mem 64 → Prop := fun st ml =>
    st.1 ≤ w.toNat ∧ st.2.length = lp0.length ∧
    (∀ p, p < dst_off.toNat ∨ dst_off.toNat + st.1 ≤ p → st.2.getD p 0#32 = lp0.getD p 0#32) ∧
    (∀ j, j < st.1 → st.2.getD (dst_off.toNat + j) 0#32 = lp0.getD (src_off.toNat + j) 0#32) ∧
    (bvHdrMem h hdr ⋆ array64 hdr.aig_ptr aw ⋆
      array (t := i32) hdr.ht_ptr ht ⋆ array (t := i32) hdr.lits_ptr st.2 ⋆ R) ml
  dsimp only [cpopLayerCopyExpr]
  apply wp_while_state1 (fun st => BitVec.ofNat 32 st.1) (fun st => w.toNat - st.1) Inv
  · intro J hJ
    exact wp_jump_state (proj := fun st : Nat × List (BitVec 32) => (BitVec.ofNat 32 st.1, ()))
      (0, lp0) (by simp) (hJ (0, lp0) m ⟨Nat.zero_le _, rfl, fun _ _ => rfl,
        fun _ hk => False.elim (Nat.not_lt_zero _ hk), hmem⟩)
  · intro J st ml ⟨hle, hlen, hpres, hcp, hml⟩ hIH
    rcases st with ⟨idx, lp⟩
    dsimp only at hle hlen hpres hcp hml
    by_cases hlt : idx < w.toNat
    · have hi32 : (BitVec.ofNat 32 idx).toNat = idx := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      have hsi_nat : (src_off + BitVec.ofNat 32 idx).toNat = src_off.toNat + idx := by
        rw [BitVec.toNat_add, hi32, Nat.mod_eq_of_lt (by omega)]
      have hdi_nat : (dst_off + BitVec.ofNat 32 idx).toNat = dst_off.toNat + idx := by
        rw [BitVec.toNat_add, hi32, Nat.mod_eq_of_lt (by omega)]
      have hbv1 : BitVec.ofNat 32 idx + 1#32 = BitVec.ofNat 32 (idx + 1) := by
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_add, hi32, show (1#32 : BitVec 32).toNat = 1 from rfl,
          BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      c0_hfast_nogrp
      · rw [hbv1]
        have hsw_src : (BitVec.setWidth 64 (src_off + BitVec.ofNat 32 idx)).toNat =
            src_off.toNat + idx := by
          rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by
            have := (src_off + BitVec.ofNat 32 idx).isLt; omega), hsi_nat]
        have hsw_dst : (BitVec.setWidth 64 (dst_off + BitVec.ofNat 32 idx)).toNat =
            dst_off.toNat + idx := by
          rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by
            have := (dst_off + BitVec.ofNat 32 idx).isLt; omega), hdi_nat]
        have hsrc_lt_lp : (BitVec.setWidth 64 (src_off + BitVec.ofNat 32 idx)).toNat <
            lp.length := by omega
        have hsrc_get : lp[(BitVec.setWidth 64 (src_off + BitVec.ofNat 32 idx)).toNat] =
            lp0.getD (src_off.toNat + idx) 0#32 := by
          have hget : lp[(BitVec.setWidth 64 (src_off + BitVec.ofNat 32 idx)).toNat] =
              lp.getD (src_off.toNat + idx) 0#32 := by
            simp only [hsw_src]
            simp [List.getD_eq_getElem?_getD, show src_off.toNat + idx < lp.length by omega]
          rw [hget]
          apply hpres; unfold DisjointSlice at hdisj; omega
        let lp1 := lp.set (dst_off.toNat + idx) (lp0.getD (src_off.toNat + idx) 0#32)
        refine hIH (idx + 1, lp1) _ (by omega) ⟨by omega, by simp [lp1, hlen], ?_, ?_, ?_⟩
        · intro p hp
          have hne : p ≠ dst_off.toNat + idx := by omega
          dsimp only [lp1]; rw [list_getD_set_ne lp 0#32 _ hne]
          exact hpres p (by
            rcases hp with hp | hp
            · exact Or.inl hp
            · exact Or.inr (by omega))
        · intro j hj
          by_cases hji : j = idx
          · subst hji; dsimp only [lp1]; rw [list_getD_set_self lp 0#32 _ (by omega)]
          · have hjlt : j < idx := by omega
            have hne : dst_off.toNat + j ≠ dst_off.toNat + idx := by omega
            dsimp only [lp1]; rw [list_getD_set_ne lp 0#32 _ hne]; exact hcp j hjlt
        · have hm_raw : (array (t := i32) hdr.lits_ptr
              (lp.set (BitVec.setWidth 64 (dst_off + BitVec.ofNat 32 idx)).toNat
                lp[(BitVec.setWidth 64 (src_off + BitVec.ofNat 32 idx)).toNat]) ⋆
              (bvHdrMem h hdr ⋆ (array64 hdr.aig_ptr aw ⋆
                (array (t := i32) hdr.ht_ptr ht ⋆ (R ⋆ Std.ExtHashMap.emp))))) _ := ‹_›
          refine opMem_of_lits ?_
          simpa only [Std.ExtHashMap.sep_emp, ← Std.ExtHashMap.sep_assoc, hsw_dst, hsrc_get] using
            hm_raw
      · exfalso; omega
    · have hid : idx = w.toNat := by omega
      subst hid
      have hi32 : (BitVec.ofNat 32 w.toNat).toNat = w.toNat := by simp
      c0_hfast_nogrp
      · exfalso; omega
      · refine hexit lp ml hlen hpres ⟨hdst, fun j hj => ?_⟩ (fun ρ => ?_) hml
        · rw [hcp j hj]; exact hwf_src.2 j hj
        · apply BitVec.eq_of_getLsbD_eq; intro k hk
          rw [sliceVal_getLsbD hk, sliceVal_getLsbD hk, hcp k hk]

public theorem bv_cpop_layer_loop_wp (Γ : Env)
    (hadd : Γ.Has "bv_blast_add_into" bvBlastAddIntoSpec)
    {h : Val i64} {in_off out_off in_len w : BitVec 32} {out_len64 ld : Val i64}
    {hdr0 : BVHdrState} {g0 : Aig} {aw0 : List (BitVec 64)} {ht0 lp0 : List (BitVec 32)}
    {R : Mem 64 → Prop} {m0 : Mem 64} {Q : Post [Ty.bool]} {X : XPost}
    (hinv0 : AigInv hdr0 g0 aw0 ht0) (ho0 : hdr0.oom = 0#32)
    (hld : ld = hdr0.lits_ptr)
    (hlencap : hdr0.lits_len.toNat ≤ hdr0.lits_cap.toNat)
    (hcaplen : hdr0.lits_cap.toNat ≤ lp0.length)
    (hptr : (0 < in_len.toNat * w.toNat ∨ 0 < (in_len.toNat + 1) / 2 * w.toNat) →
      hdr0.lits_ptr ≠ 0#64)
    (hout64 : out_len64 = BitVec.ofNat 64 ((in_len.toNat + 1) / 2))
    (hin32 : in_len.toNat * w.toNat < 2 ^ 32)
    (hout32 : (in_len.toNat + 1) / 2 * w.toNat < 2 ^ 32)
    (hin : in_off.toNat + in_len.toNat * w.toNat ≤ hdr0.lits_len.toNat)
    (hout : out_off.toNat + (in_len.toNat + 1) / 2 * w.toNat ≤ hdr0.lits_len.toNat)
    (hwf_in : SliceLitsWf hdr0 lp0 in_off.toNat (in_len.toNat * w.toNat))
    (hdisj : DisjointSlice out_off.toNat ((in_len.toNat + 1) / 2 * w.toNat)
      in_off.toNat (in_len.toNat * w.toNat))
    (hmem : (bvHdrMem h hdr0 ⋆ array64 hdr0.aig_ptr aw0 ⋆
      array (t := i32) hdr0.ht_ptr ht0 ⋆ array (t := i32) hdr0.lits_ptr lp0 ⋆ R) m0)
    (hpost : ∀ ret hdr' g' aw' ht' lp' m',
      hdr0.AigFrame hdr' → g0 ≤ g' →
      g'.nodes.size ≤ g0.nodes.size + (in_len.toNat / 2) * (9 * w.toNat) →
      AigInv hdr' g' aw' ht' → lp'.length = lp0.length →
      (∀ p, p < out_off.toNat ∨ out_off.toNat + (in_len.toNat + 1) / 2 * w.toNat ≤ p →
        lp'.getD p 0#32 = lp0.getD p 0#32) →
      (hdr0.oom ≠ 0#32 → hdr'.oom ≠ 0#32) → (ret = true ↔ hdr'.oom = 0#32) →
      (hdr0.oom = 0#32 → hdr0.lits_len.toNat ≤ hdr0.lits_cap.toNat →
        in_len.toNat * w.toNat < 2 ^ 32 → (in_len.toNat + 1) / 2 * w.toNat < 2 ^ 32 →
        (0 < in_len.toNat * w.toNat → hdr0.lits_ptr ≠ 0#64) →
        (0 < (in_len.toNat + 1) / 2 * w.toNat → hdr0.lits_ptr ≠ 0#64) →
        in_off.toNat + in_len.toNat * w.toNat ≤ hdr0.lits_len.toNat →
        out_off.toNat + (in_len.toNat + 1) / 2 * w.toNat ≤ hdr0.lits_len.toNat →
        g0.A + 1 + g0.nodes.size + (in_len.toNat / 2) * (9 * w.toNat) ≤ hdr0.aig_cap.toNat →
        g0.nodes.size + (in_len.toNat / 2) * (9 * w.toNat) ≤ bvMaxGates → hdr'.oom = 0#32) →
      (ret = true →
        SliceLitsWf hdr' lp' out_off.toNat ((in_len.toNat + 1) / 2 * w.toNat) ∧
        ∀ ρ, sliceSum g' ρ lp' out_off.toNat ((in_len.toNat + 1) / 2) w.toNat =
          sliceSum g0 ρ lp0 in_off.toNat in_len.toNat w.toNat) →
      (bvHdrMem h hdr' ⋆ array64 hdr'.aig_ptr aw' ⋆
        array (t := i32) hdr'.ht_ptr ht' ⋆ array (t := i32) hdr'.lits_ptr lp' ⋆ R) m' →
      Q (ret, ⟨⟩) m') :
    wp Γ Q X (cpopLayerLoopExpr h in_off out_off in_len w out_len64 ld) m0 := by
  subst out_len64
  subst hld
  have hcap32 : hdr0.lits_cap.toNat < 2 ^ 32 := hdr0.lits_cap.isLt
  let outLen : Nat := (in_len.toNat + 1) / 2
  have hout_32 : outLen < 2 ^ 32 := by have := in_len.isLt; dsimp [outLen]; omega
  have hout64_nat : (BitVec.ofNat 64 outLen).toNat = outLen := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  let Inv : (Nat × BVHdrState × Aig × List (BitVec 64) × List (BitVec 32) ×
      List (BitVec 32)) → Mem 64 → Prop := fun st ml =>
    let (i, hdr, g, aw, ht, lp) := st
    i ≤ outLen ∧ hdr0.AigFrame hdr ∧ g0 ≤ g ∧
    g.nodes.size ≤ g0.nodes.size + min i (in_len.toNat / 2) * (9 * w.toNat) ∧
    AigInv hdr g aw ht ∧ lp.length = lp0.length ∧ hdr.oom = 0#32 ∧
    (∀ p, p < out_off.toNat ∨ out_off.toNat + i * w.toNat ≤ p → lp.getD p 0#32 = lp0.getD p 0#32) ∧
    SliceLitsWf hdr lp out_off.toNat (i * w.toNat) ∧
    (∀ k, k < i → ∀ ρ,
      if 2 * k + 1 < in_len.toNat then
        sliceVal g ρ lp (out_off.toNat + k * w.toNat) w.toNat =
          sliceVal g0 ρ lp0 (in_off.toNat + (2 * k) * w.toNat) w.toNat +
            sliceVal g0 ρ lp0 (in_off.toNat + (2 * k + 1) * w.toNat) w.toNat
      else
        sliceVal g ρ lp (out_off.toNat + k * w.toNat) w.toNat =
          sliceVal g0 ρ lp0 (in_off.toNat + (2 * k) * w.toNat) w.toNat) ∧
    (bvHdrMem h hdr ⋆ array64 hdr.aig_ptr aw ⋆
      array (t := i32) hdr.ht_ptr ht ⋆ array (t := i32) hdr.lits_ptr lp ⋆ R) ml
  dsimp only [cpopLayerLoopExpr]
  apply wp_while_state1 (fun st => BitVec.ofNat 32 st.1) (fun st => outLen - st.1) Inv
  · intro J hJ
    exact wp_jump_state
      (proj := fun st : Nat × BVHdrState × Aig × List (BitVec 64) × List (BitVec 32) ×
          List (BitVec 32) => (BitVec.ofNat 32 st.1, ()))
      (0, hdr0, g0, aw0, ht0, lp0) (by simp)
      (hJ (0, hdr0, g0, aw0, ht0, lp0) m0 ⟨Nat.zero_le _, BVHdrState.AigFrame.rfl _,
        Aig.extends_rfl g0, by simp, hinv0, rfl, ho0, fun _ _ => rfl,
        (by simpa using sliceLitsWf_zero out_off.toNat (by omega)),
        fun _ hk => False.elim (Nat.not_lt_zero _ hk), hmem⟩)
  · intro J st ml ⟨hle, hf, hg, hsz, hinv, hlen, ho, hpres, hwf_out, hstep, hml⟩ hIH
    rcases st with ⟨i, hdr, g, aw, ht, lp⟩
    dsimp only at hle hf hg hsz hinv hlen ho hpres hwf_out hstep hml
    have hi32 : (BitVec.ofNat 32 i).toNat = i := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hi64 : (BitVec.zeroExtend 64 (BitVec.ofNat 32 i)).toNat = i := by
      rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := (BitVec.ofNat 32 i).isLt; omega),
        hi32]
    by_cases hlt : i < outLen
    · have hcond : decide (BitVec.zeroExtend 64 (BitVec.ofNat 32 i) <
          BitVec.ofNat 64 outLen) = true := by simp [BitVec.lt_def, hi64, hout64_nat, hlt]
      c0_hfast_nogrp
      · let InvStep : Unit → Mem 64 → Prop := fun _ ms =>
          ∃ hdr' g' aw' ht' lp',
            hdr0.AigFrame hdr' ∧ g0 ≤ g' ∧
            g'.nodes.size ≤ g0.nodes.size + min (i + 1) (in_len.toNat / 2) * (9 * w.toNat) ∧
            AigInv hdr' g' aw' ht' ∧ lp'.length = lp0.length ∧ hdr'.oom = 0#32 ∧
            (∀ p, p < out_off.toNat ∨ out_off.toNat + (i + 1) * w.toNat ≤ p →
              lp'.getD p 0#32 = lp0.getD p 0#32) ∧
            SliceLitsWf hdr' lp' out_off.toNat ((i + 1) * w.toNat) ∧
            (∀ k, k < i + 1 → ∀ ρ,
              if 2 * k + 1 < in_len.toNat then
                sliceVal g' ρ lp' (out_off.toNat + k * w.toNat) w.toNat =
                  sliceVal g0 ρ lp0 (in_off.toNat + (2 * k) * w.toNat) w.toNat +
                    sliceVal g0 ρ lp0 (in_off.toNat + (2 * k + 1) * w.toNat) w.toNat
              else
                sliceVal g' ρ lp' (out_off.toNat + k * w.toNat) w.toNat =
                  sliceVal g0 ρ lp0 (in_off.toNat + (2 * k) * w.toNat) w.toNat) ∧
            (bvHdrMem h hdr' ⋆ array64 hdr'.aig_ptr aw' ⋆
              array (t := i32) hdr'.ht_ptr ht' ⋆ array (t := i32) hdr'.lits_ptr lp' ⋆ R) ms
        apply wp_join_state0 InvStep
        · intro _ _ ms ⟨hdr', g', aw', ht', lp', hf', hg', hsz', hinv', hlen', ho',
              hpres', hwf', hstep', hms⟩
          have hi1 : BitVec.ofNat 32 i + 1#32 = BitVec.ofNat 32 (i + 1) := by
            apply BitVec.eq_of_toNat_eq
            rw [BitVec.toNat_add, hi32, show (1#32 : BitVec 32).toNat = 1 from rfl,
              BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
          c0_hfast_nogrp
          rw [hi1]
          exact hIH (i + 1, hdr', g', aw', ht', lp') ms (by omega)
            ⟨by omega, hf', hg', hsz', hinv', hlen', ho', hpres', hwf', hstep', hms⟩
        · intro J1 hJ1
          have hi2_le : 2 * i < in_len.toNat := by dsimp [outLen] at hlt; omega
          have hi2w_lt : (2 * i) * w.toNat + w.toNat ≤ in_len.toNat * w.toNat := by
            have hmul : (2 * i + 1) * w.toNat ≤ in_len.toNat * w.toNat :=
              Nat.mul_le_mul_right _ (by omega)
            rw [Nat.add_mul, Nat.one_mul] at hmul; exact hmul
          have hiw_lt : i * w.toNat + w.toNat ≤ ((in_len.toNat + 1) / 2) * w.toNat := by
            have hmul : (i + 1) * w.toNat ≤ ((in_len.toNat + 1) / 2) * w.toNat :=
              Nat.mul_le_mul_right _ (by dsimp [outLen] at hlt; exact hlt)
            rw [Nat.add_mul, Nat.one_mul] at hmul; exact hmul
          have h28_nat : (BitVec.truncate 32 (BitVec.zeroExtend 64 in_off +
              2#64 * BitVec.zeroExtend 64 (BitVec.ofNat 32 i) * BitVec.zeroExtend 64 w)).toNat =
              in_off.toNat + (2 * i) * w.toNat := by
            have h1 : (BitVec.zeroExtend 64 in_off).toNat = in_off.toNat := by
              rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt]; have := in_off.isLt; omega
            have h2 : (BitVec.zeroExtend 64 w).toNat = w.toNat := by
              rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt]; have := w.isLt; omega
            rw [BitVec.truncate, BitVec.toNat_setWidth, BitVec.toNat_add, h1, BitVec.toNat_mul,
              BitVec.toNat_mul, hi64, h2]
            have hlt1 : 2 * i < 2 ^ 64 := by omega
            have hlt2 : 2 * i * w.toNat < 2 ^ 64 := by omega
            rw [show (2#64 : BitVec 64).toNat = 2 from rfl, Nat.mod_eq_of_lt hlt1,
              Nat.mod_eq_of_lt hlt2, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
          have h34_nat : (BitVec.truncate 32 (BitVec.zeroExtend 64 out_off +
              BitVec.zeroExtend 64 (BitVec.ofNat 32 i) * BitVec.zeroExtend 64 w)).toNat =
              out_off.toNat + i * w.toNat := by
            have h1 : (BitVec.zeroExtend 64 out_off).toNat = out_off.toNat := by
              rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt]; have := out_off.isLt; omega
            have h2 : (BitVec.zeroExtend 64 w).toNat = w.toNat := by
              rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt]; have := w.isLt; omega
            rw [BitVec.truncate, BitVec.toNat_setWidth, BitVec.toNat_add, h1, BitVec.toNat_mul,
              hi64, h2]
            have hlt2 : i * w.toNat < 2 ^ 64 := by omega
            rw [Nat.mod_eq_of_lt hlt2, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
          have haig0 : hdr0.aig_len.toNat ≤ hdr.aig_len.toNat := by
            have hA := hg.1; have hs := hg.2.1; rw [hinv0.aig_len_eq, hinv.aig_len_eq, hA]; omega
          have hwf_a : SliceLitsWf hdr lp (in_off.toNat + (2 * i) * w.toNat) w.toNat := by
            refine ⟨by rw [hf.lits_len]; omega, fun j hj => ?_⟩
            have hlt_w := hwf_in.2 ((2 * i) * w.toNat + j) (by omega)
            rw [show in_off.toNat + ((2 * i) * w.toNat + j) =
              in_off.toNat + (2 * i) * w.toNat + j from by omega] at hlt_w
            rw [hpres (in_off.toNat + (2 * i) * w.toNat + j)
              (by unfold DisjointSlice at hdisj; omega)]
            exact Nat.lt_of_lt_of_le hlt_w haig0
          by_cases hpair : 2 * i + 1 < in_len.toNat
          · have hi21w_lt : (2 * i + 1) * w.toNat + w.toNat ≤ in_len.toNat * w.toNat := by
              have hmul : (2 * i + 1 + 1) * w.toNat ≤ in_len.toNat * w.toNat :=
                Nat.mul_le_mul_right _ (by omega)
              rw [Nat.add_mul, Nat.one_mul] at hmul; exact hmul
            have h47_nat : (BitVec.truncate 32 (BitVec.zeroExtend 64 in_off +
                (2#64 * BitVec.zeroExtend 64 (BitVec.ofNat 32 i) + 1#64) *
                  BitVec.zeroExtend 64 w)).toNat = in_off.toNat + (2 * i + 1) * w.toNat := by
              have h1 : (BitVec.zeroExtend 64 in_off).toNat = in_off.toNat := by
                rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt]; have := in_off.isLt; omega
              have h2 : (BitVec.zeroExtend 64 w).toNat = w.toNat := by
                rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt]; have := w.isLt; omega
              rw [BitVec.truncate, BitVec.toNat_setWidth, BitVec.toNat_add, h1, BitVec.toNat_mul,
                BitVec.toNat_add, BitVec.toNat_mul, hi64, h2]
              have hlt1 : 2 * i < 2 ^ 64 := by omega
              have hlt1b : 2 * i + 1 < 2 ^ 64 := by omega
              have hlt2 : (2 * i + 1) * w.toNat < 2 ^ 64 := by omega
              rw [show (2#64 : BitVec 64).toNat = 2 from rfl,
                show (1#64 : BitVec 64).toNat = 1 from rfl, Nat.mod_eq_of_lt hlt1,
                Nat.mod_eq_of_lt hlt1b, Nat.mod_eq_of_lt hlt2,
                Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
            have hwf_b : SliceLitsWf hdr lp (in_off.toNat + (2 * i + 1) * w.toNat) w.toNat := by
              refine ⟨by rw [hf.lits_len]; omega, fun j hj => ?_⟩
              have hlt_w := hwf_in.2 ((2 * i + 1) * w.toNat + j) (by omega)
              rw [show in_off.toNat + ((2 * i + 1) * w.toNat + j) =
                in_off.toNat + (2 * i + 1) * w.toNat + j from by omega] at hlt_w
              rw [hpres (in_off.toNat + (2 * i + 1) * w.toNat + j)
                (by unfold DisjointSlice at hdisj; omega)]
              exact Nat.lt_of_lt_of_le hlt_w haig0
            c0_hfast_nogrp
            · c0_hcall hadd
              refine ⟨hdr, g, aw, ht, lp, R, hinv, by rw [hf.lits_cap, hlen]; exact hcaplen,
                fun _ _ _ _ _ _ => ⟨by rwa [h28_nat], by rwa [h47_nat],
                  by rw [h28_nat, h34_nat]; unfold DisjointSlice at hdisj ⊢; omega,
                  by rw [h47_nat, h34_nat]; unfold DisjointSlice at hdisj ⊢; omega⟩,
                hml, ?_⟩
              intro ret hdr' g' aw' ht' lp' m' hf' hg' hsz' hinv' hlen' hpres' hoom'
                hret_iff hbound' hval' hm'
              have hf0' := hf.trans hf'
              have hg0' := Aig.extends_trans hg hg'
              have hlen0' : lp'.length = lp0.length := hlen'.trans hlen
              have hpres0' : ∀ p, p < out_off.toNat ∨ out_off.toNat + (i + 1) * w.toNat ≤ p →
                  lp'.getD p 0#32 = lp0.getD p 0#32 := fun p hp => by
                rw [hpres' p (by
                  rw [h34_nat]
                  rcases hp with hp | hp
                  · exact Or.inl (by omega)
                  · rw [Nat.add_mul, Nat.one_mul] at hp; exact Or.inr (by omega))]
                exact hpres p (by
                  rcases hp with hp | hp
                  · exact Or.inl hp
                  · rw [Nat.add_mul, Nat.one_mul] at hp; exact Or.inr (by omega))
              have hpres0_all : ∀ p, p < out_off.toNat ∨ out_off.toNat + outLen * w.toNat ≤ p →
                  lp'.getD p 0#32 = lp0.getD p 0#32 := fun p hp =>
                hpres0' p (by
                  rcases hp with hp | hp
                  · exact Or.inl hp
                  · have hmul : (i + 1) * w.toNat ≤ outLen * w.toNat :=
                      Nat.mul_le_mul_right _ hlt
                    exact Or.inr (by omega))
              have hmin : min i (in_len.toNat / 2) = i := Nat.min_eq_left (by omega)
              have hmin1 : min (i + 1) (in_len.toNat / 2) = i + 1 := Nat.min_eq_left (by omega)
              rw [hmin] at hsz
              have hmul_tot : (i + 1) * (9 * w.toNat) ≤ (in_len.toNat / 2) * (9 * w.toNat) :=
                Nat.mul_le_mul_right _ (by omega)
              have hmul_step : i * (9 * w.toNat) + 9 * w.toNat = (i + 1) * (9 * w.toNat) := by
                rw [Nat.add_mul, Nat.one_mul]
              by_cases hok : ret = true
              · subst hok
                have ho' : hdr'.oom = 0#32 := hret_iff.mp rfl
                obtain ⟨hwf_c, hval_c⟩ := hval' rfl
                c0_hfast_nogrp
                · have haig1 : hdr.aig_len.toNat ≤ hdr'.aig_len.toNat := by
                    have hA := hg'.1; have hs := hg'.2.1
                    rw [hinv.aig_len_eq, hinv'.aig_len_eq, hA]; omega
                  have hwf' : SliceLitsWf hdr' lp' out_off.toNat ((i + 1) * w.toNat) := by
                    rw [Nat.add_mul, Nat.one_mul]
                    refine ⟨by rw [hf0'.lits_len]; omega, fun j hj => ?_⟩
                    by_cases hjlt : j < i * w.toNat
                    · rw [hpres' (out_off.toNat + j) (Or.inl (by rw [h34_nat]; omega))]
                      exact Nat.lt_of_lt_of_le (hwf_out.2 j hjlt) haig1
                    · rw [show out_off.toNat + j = (out_off.toNat + i * w.toNat) + (j - i * w.toNat)
                        from by omega]
                      rw [← h34_nat]
                      exact hwf_c.2 (j - i * w.toNat) (by omega)
                  apply hJ1 () m' ⟨hdr', g', aw', ht', lp', hf0', hg0', by rw [hmin1]; omega,
                    hinv', hlen0', ho', hpres0', hwf', ?_, hm'⟩
                  intro k hk ρ
                  by_cases hki : k = i
                  · subst k; simp only [hpair, ↓reduceIte]
                    rw [← h34_nat, hval_c ρ, h28_nat, h47_nat]
                    have ha_eq : sliceVal g ρ lp (in_off.toNat + (2 * i) * w.toNat) w.toNat =
                        sliceVal g0 ρ lp0 (in_off.toNat + (2 * i) * w.toNat) w.toNat := by
                      rw [sliceVal_eq_of_agree (fun p hp1 hp2 =>
                        hpres p (by unfold DisjointSlice at hdisj; omega))]
                      refine sliceVal_extend_aig hinv0 hg ?_
                      exact sliceLitsWf_sub hwf_in ⟨by omega, by omega⟩
                    have hb_eq : sliceVal g ρ lp (in_off.toNat + (2 * i + 1) * w.toNat) w.toNat =
                        sliceVal g0 ρ lp0 (in_off.toNat + (2 * i + 1) * w.toNat) w.toNat := by
                      rw [sliceVal_eq_of_agree (fun p hp1 hp2 =>
                        hpres p (by unfold DisjointSlice at hdisj; omega))]
                      refine sliceVal_extend_aig hinv0 hg ?_
                      exact sliceLitsWf_sub hwf_in ⟨by omega, by omega⟩
                    rw [ha_eq, hb_eq]
                  · have hklt : k < i := by omega
                    have hk_old := hstep k hklt ρ
                    have hk_agree : sliceVal g' ρ lp' (out_off.toNat + k * w.toNat) w.toNat =
                        sliceVal g ρ lp (out_off.toNat + k * w.toNat) w.toNat := by
                      rw [sliceVal_eq_of_agree (fun p hp1 hp2 =>
                        hpres' p (Or.inl (by
                          have hm : k * w.toNat + w.toNat ≤ i * w.toNat := by
                            rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega)
                          rw [h34_nat]; omega)))]
                      refine sliceVal_extend_aig hinv hg' ?_
                      have hm : k * w.toNat + w.toNat ≤ i * w.toNat := by
                        rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega)
                      exact sliceLitsWf_sub hwf_out ⟨by omega, by omega⟩
                    split <;> simp only [*] at hk_old <;> rwa [hk_agree]
                · simp at ‹_›
              · have hretf : ret = false := by cases ret <;> simp_all
                subst hretf
                have hoom' : hdr'.oom ≠ 0#32 := fun h0 => by cases hret_iff.mpr h0
                c0_hfast_nogrp
                · simp at ‹_›
                · refine hpost false hdr' g' aw' ht' lp' m' hf0' hg0' (by omega) hinv' hlen0'
                    hpres0_all (fun hne => absurd ho0 hne)
                    ⟨fun h => absurd h (by decide), fun hz => absurd hz hoom'⟩
                    (fun _ _ _ _ _ _ _ _ ha hb => by
                      have hA : g0.A = g.A := hg.1
                      have hptr_i : 0 < w.toNat → hdr.lits_ptr ≠ 0#64 := fun hw => by
                        rw [hf.lits_ptr]; apply hptr; left
                        exact Nat.mul_pos (by omega) hw
                      exact absurd (hbound' ho (by rw [hf.lits_cap, hf.lits_len]; exact hlencap)
                        hptr_i (by rw [hf.lits_len, h28_nat]; omega)
                        (by rw [hf.lits_len, h47_nat]; omega)
                        (by rw [hf.lits_len, h34_nat]; omega)
                        (by rw [hf.aig_cap, ← hA]; omega) (by omega)) hoom')
                    (fun h => absurd h (by decide)) hm'
            · exfalso
              have h2m : (2 : Nat) % 2 ^ 64 = 2 := by decide
              have him : i % 2 ^ 32 = i := Nat.mod_eq_of_lt (by omega)
              have h47m : (2 * i + 1) % 2 ^ 64 = 2 * i + 1 := Nat.mod_eq_of_lt (by omega)
              rw [h2m, him, h47m] at hc; omega
          · c0_hfast_nogrp
            · exfalso
              have h2m : (2 : Nat) % 2 ^ 64 = 2 := by decide
              have him : i % 2 ^ 32 = i := Nat.mod_eq_of_lt (by omega)
              have h47m : (2 * i + 1) % 2 ^ 64 = 2 * i + 1 := Nat.mod_eq_of_lt (by omega)
              rw [h2m, him, h47m] at hc; omega
            · apply bv_cpop_layer_copy_wp Γ (g := g) (by rw [hf.lits_ptr])
                (by rw [hf.lits_len, h28_nat]; omega) (by rw [hf.lits_len, h34_nat]; omega)
                (by rw [hf.lits_len, hf.lits_cap]; exact hlencap)
                (by rw [hf.lits_cap, hlen]; exact hcaplen)
                (by rw [h28_nat, h34_nat]; unfold DisjointSlice at hdisj ⊢; omega)
                (by rwa [h28_nat]) hml
              intro lp' m' hlen' hpres' hwf_c hval_c hm'
              have hlen0' : lp'.length = lp0.length := hlen'.trans hlen
              have hpres0' : ∀ p, p < out_off.toNat ∨ out_off.toNat + (i + 1) * w.toNat ≤ p →
                  lp'.getD p 0#32 = lp0.getD p 0#32 := fun p hp => by
                rw [hpres' p (by
                  rw [h34_nat]
                  rcases hp with hp | hp
                  · exact Or.inl (by omega)
                  · rw [Nat.add_mul, Nat.one_mul] at hp; exact Or.inr (by omega))]
                exact hpres p (by
                  rcases hp with hp | hp
                  · exact Or.inl hp
                  · rw [Nat.add_mul, Nat.one_mul] at hp; exact Or.inr (by omega))
              have hmin : min i (in_len.toNat / 2) = in_len.toNat / 2 := Nat.min_eq_right (by omega)
              have hmin1 : min (i + 1) (in_len.toNat / 2) = in_len.toNat / 2 :=
                Nat.min_eq_right (by omega)
              rw [hmin] at hsz
              have hwf' : SliceLitsWf hdr lp' out_off.toNat ((i + 1) * w.toNat) := by
                rw [Nat.add_mul, Nat.one_mul]
                refine ⟨by rw [hf.lits_len]; omega, fun j hj => ?_⟩
                by_cases hjlt : j < i * w.toNat
                · rw [hpres' (out_off.toNat + j) (Or.inl (by rw [h34_nat]; omega))]
                  exact hwf_out.2 j hjlt
                · rw [show out_off.toNat + j = (out_off.toNat + i * w.toNat) + (j - i * w.toNat)
                    from by omega]
                  rw [← h34_nat]
                  exact hwf_c.2 (j - i * w.toNat) (by omega)
              apply hJ1 () m' ⟨hdr, g, aw, ht, lp', hf, hg, by rw [hmin1]; exact hsz, hinv,
                hlen0', ho, hpres0', hwf', ?_, hm'⟩
              intro k hk ρ
              by_cases hki : k = i
              · subst k; simp only [hpair, ↓reduceIte]
                rw [← h34_nat, hval_c ρ, h28_nat]
                rw [sliceVal_eq_of_agree (fun p hp1 hp2 =>
                  hpres p (by unfold DisjointSlice at hdisj; omega))]
                refine sliceVal_extend_aig hinv0 hg ?_
                exact sliceLitsWf_sub hwf_in ⟨by omega, by omega⟩
              · have hklt : k < i := by omega
                have hk_old := hstep k hklt ρ
                have hk_agree : sliceVal g ρ lp' (out_off.toNat + k * w.toNat) w.toNat =
                    sliceVal g ρ lp (out_off.toNat + k * w.toNat) w.toNat :=
                  sliceVal_eq_of_agree (fun p hp1 hp2 =>
                    hpres' p (Or.inl (by
                      have hm : k * w.toNat + w.toNat ≤ i * w.toNat := by
                        rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega)
                      rw [h34_nat]; omega)))
                split <;> simp only [*] at hk_old <;> rwa [hk_agree]
      · exfalso; omega
    · have hid : i = outLen := by omega
      subst hid
      c0_hfast_nogrp
      · exfalso; omega
      · have hmin : min outLen (in_len.toNat / 2) = in_len.toNat / 2 := by
          dsimp [outLen]; exact Nat.min_eq_right (by omega)
        rw [hmin] at hsz
        refine hpost true hdr g aw ht lp ml hf hg hsz hinv hlen hpres
          (fun hne => absurd ho0 hne) ⟨fun _ => ho, fun _ => rfl⟩
          (fun _ _ _ _ _ _ _ _ _ _ => ho) (fun _ => ⟨hwf_out, fun ρ => ?_⟩) hml
        rw [← sliceSum_extend_aig hinv0 hg hwf_in]
        refine sliceSum_cpop_step_layer fun k hk => ?_
        have hk_s := hstep k hk ρ
        have h2kw : (2 * k) * w.toNat + w.toNat ≤ in_len.toNat * w.toNat := by
          have hmul : (2 * k + 1) * w.toNat ≤ in_len.toNat * w.toNat :=
            Nat.mul_le_mul_right _ (by omega)
          rw [Nat.add_mul, Nat.one_mul] at hmul; exact hmul
        split at hk_s
        · rename_i h2p
          have h21kw : (2 * k + 1) * w.toNat + w.toNat ≤ in_len.toNat * w.toNat := by
            have hmul : (2 * k + 1 + 1) * w.toNat ≤ in_len.toNat * w.toNat :=
              Nat.mul_le_mul_right _ (by omega)
            rw [Nat.add_mul, Nat.one_mul] at hmul; exact hmul
          simp only [h2p, ↓reduceIte, hk_s]
          rw [sliceVal_extend_aig hinv0 hg (sliceLitsWf_sub hwf_in ⟨by omega, by omega⟩),
            sliceVal_extend_aig hinv0 hg (sliceLitsWf_sub hwf_in ⟨by omega, by omega⟩)]
        · rename_i h2np
          simp only [h2np, ↓reduceIte, hk_s]
          rw [sliceVal_extend_aig hinv0 hg (sliceLitsWf_sub hwf_in ⟨by omega, by omega⟩)]

end

end LeanQbe.T.Examples.Bitblast.Proof.OpsDivCpop
