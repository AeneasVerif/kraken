/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Arisca.Proof.Poly2Spec
public import LeanQbe.T.Examples.Arisca.Proof.Poly2Sp0
public import LeanQbe.T.Examples.Arisca.Proof.Poly2R
public import LeanQbe.T.Examples.Arisca.Proof.Poly2ApplySubst
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ProofKit
import LeanQbe.T.Logic.MemLemmas
import Kraken.Separation

/-!
# ARiSCA `ar_apply` Loop 4 WP (`Arisca.Proof.Poly2ApplyLoop`)

`XPost`-polymorphic (`noExit = true`, `<= std3`) WP proof for `ar_apply_wp` (chaining
`apply_bx_loop_wp`, `apply_slR_loop_wp`, `apply_vq_loop_wp`, and Loop 4 `apply_outer_loop_wp`),
and public re-export of all `Poly2` proofs (`ar_add_q_wp`, `ar_load_rule_wp`, `ar_store_rule_wp`,
`ar_build_sp0_wp`, `ar_build_R_wp`, `ar_apply_wp`).
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Arisca.Proof

open Std
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.C0HeadStep
open LeanQbe.T.ProofKit
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Arisca
open LeanQbe.T.Examples.Arisca.Src
open LeanQbe.T.Examples.Arisca.Src.Poly


@[reducible] private def appStepPure : Expr Val Cont [.bool] → Expr Val Cont [.bool]
  | @Expr.let_ _ _ _ [.bits 64] op k =>
    match op with
    | .mk (.mul (.bits 64)) (a, b, ()) => k (a.val * b.val, ())
    | .mk (.add (.bits 64)) (a, b, ()) => k (a.val + b.val, ())
    | .mk (.copy (.bits 64)) (a, ()) => k (a.val, ())
    | .mk (.zext 32 64) (a, ()) => k (a.val.setWidth 64, ())
    | _ => k (0#64, ())
  | @Expr.let_ _ _ _ [.bits 32] op k =>
    match op with
    | .mk (.add (.bits 32)) (a, b, ()) => k (a.val + b.val, ())
    | .mk (.copy (.bits 32)) (a, ()) => k (a.val, ())
    | _ => k (0#32, ())
  | @Expr.let_ _ _ _ [.bits 8] _ k => k (0#8, ())
  | @Expr.let_ _ _ _ [.bool] _ k => k (false, ())
  | e => e

@[reducible] private def appSkipToGrp (n : Nat)
    (l8 : List (Val i8)) (l32 : List (Val i32)) (l64 : List (Val i64)) :
    Expr Val Cont [.bool] → Expr Val Cont [.bool]
  | e@(.group _ _) => e
  | e@(.jnz _ _ _) => e
  | e@(.call _ _ _) => e
  | e@(.let_ _ _) => match n with | 0 => e | m + 1 => appSkipToGrp m l8 l32 l64 (appStepPure e)
  | @Expr.load _ _ _ (.bits 8) _ k =>
    match n, l8 with
    | m + 1, v :: vs => appSkipToGrp m vs l32 l64 (k v)
    | _, _ => .ret (Arg.imm false, ())
  | @Expr.load _ _ _ (.bits 32) _ k =>
    match n, l32 with
    | m + 1, v :: vs => appSkipToGrp m l8 vs l64 (k v)
    | _, _ => .ret (Arg.imm false, ())
  | @Expr.load _ _ _ (.bits 64) _ k =>
    match n, l64 with
    | m + 1, v :: vs => appSkipToGrp m l8 l32 vs (k v)
    | _, _ => .ret (Arg.imm false, ())
  | e => e

private noncomputable def applyLoop4InnerExpr (cx : Val i64) (sym : Val i32)
    (curRm curRl curRh curRp : Val i64) (nR n : Val i32) (bx : Val i64)
    (nb : Val i32) (slB slR pool0 tm0 tl0 th0 ptop : Val i64)
    (JB : Cont [i32, i32, i64, i32]) (qnB bB ti mOff : Val i32)
    (ptB cl ch : Val i64) : Expr Val Cont [.bool] :=
  match applyLoop4Expr cx sym curRm curRl curRh curRp nR n bx nb slB slR pool0 tm0 tl0 th0 ptop with
  | @Expr.group _ _ _ [[.bits 32, .bits 32, .bits 64, .bits 32]] bs _ =>
    match bs (JB, ()) with
    | .cons b _ => match b (nR, qnB, ptB, bB, ()) with
      | @Expr.let_ _ _ _ [.bool] _ l0 => match l0 (false, ()) with
        | .jnz _ t _ => appSkipToGrp 30 [] [ti, mOff] [cl, ch] t
        | _ => .ret (Arg.imm false, ())
      | _ => .ret (Arg.imm false, ())
    | _ => .ret (Arg.imm false, ())
  | _ => .ret (Arg.imm false, ())

private noncomputable def applyLoop4JEExpr (cx : Val i64) (sym : Val i32)
    (curRm curRl curRh curRp : Val i64) (nR n : Val i32) (bx : Val i64)
    (nb : Val i32) (slB slR pool0 tm0 tl0 th0 ptop : Val i64)
    (JB : Cont [i32, i32, i64, i32]) (qnB bB ti mOff : Val i32) (ptB cl ch : Val i64)
    (rI qnI : Val i32) (ptI rl rh l h : Val i64)
    (Js : Cont [i32, i64]) : Expr Val Cont [.bool] :=
  match applyLoop4InnerExpr cx sym curRm curRl curRh curRp nR n bx nb slB slR pool0 tm0 tl0 th0 ptop
      JB qnB bB ti mOff ptB cl ch with
  | @Expr.group _ _ _ [[.bits 32, .bits 32, .bits 64]] bs _ =>
    match bs (fun _ _ => False, ()) with
    | .cons b _ => match b (rI, qnI, ptI, ()) with
      | @Expr.let_ _ _ _ [.bool] _ l0 => match l0 (false, ()) with
        | .jnz _ t _ =>
          match t with
          | @Expr.group _ _ _ [[.bits 32, .bits 64]] _ kJJ =>
            match appSkipToGrp 15 [0#8] [] [0#64] (kJJ (fun _ _ => False, ())) with
            | .jnz _ t2 _ =>
              match appSkipToGrp 25 [] [] [rl, rh] t2 with
              | @Expr.call _ _ _ _ _ [.bits 64, .bits 64] _ k =>
                match appSkipToGrp 15 [] [] [] (k (l, h, ())) with
                | @Expr.group _ _ _ [[.bits 32, .bits 64]] _ kJs => kJs (Js, ())
                | _ => .ret (Arg.imm false, ())
              | _ => .ret (Arg.imm false, ())
            | _ => .ret (Arg.imm false, ())
          | _ => .ret (Arg.imm false, ())
        | _ => .ret (Arg.imm false, ())
      | _ => .ret (Arg.imm false, ())
    | _ => .ret (Arg.imm false, ())
  | _ => .ret (Arg.imm false, ())

public section

private theorem apply_mul_ite_zero {n : Nat} (c1 c2 : Bool) {x y : BitVec n}
    (h : x * y = 0#n) :
    (if c1 = true then x else 0#n) * (if c2 = true then y else 0#n) = 0#n := by
  cases c1 <;> cases c2 <;> simp [h]

private theorem rSymLenSum_mono {rp rm : List (BitVec 32)} {a b : Nat} (hab : a ≤ b) :
    rSymLenSum rp rm a ≤ rSymLenSum rp rm b := by
  have hdiff : ∀ d, rSymLenSum rp rm a ≤ rSymLenSum rp rm (a + d) := by
    intro d
    induction d with
    | zero => simp
    | succ d ih =>
      rw [← Nat.add_assoc, rSymLenSum_succ]
      exact Nat.le_trans ih (Nat.le_add_right _ _)
  have hd := hdiff (b - a)
  rwa [show a + (b - a) = b by omega] at hd

private theorem apply_je_ptr4 (p : BitVec 64) (off : BitVec 32) :
    p + BitVec.setWidth 64 off * 4#64 = p + BitVec.ofNat 64 (4 * off.toNat) := by
  congr 1; apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mul_comm 4 off.toNat]

private theorem apply_je_step_bd {pool tm rp rm bx : List (BitVec 32)}
    {nb b r nR ptB ptI sPtop pcap la lb : Nat}
    (hb : b < nb) (hr : r < nR)
    (hcap : sPtop + (nR * bxSymLenSum pool tm bx nb + nb * rSymLenSum rp rm nR) ≤ pcap)
    (hptB : ptB ≤ sPtop + (b * rSymLenSum rp rm nR + nR * bxSymLenSum pool tm bx b))
    (hptI : ptI ≤ ptB + r * la + rSymLenSum rp rm r)
    (hla : la = (pool.getD (tm.getD (bx.getD b 0#32).toNat 0#32).toNat 0#32).toNat)
    (hlb : lb = (rp.getD (rm.getD r 0#32).toNat 0#32).toNat) :
    ptI + (la + lb) ≤ pcap := by
  have h1 := apply_outer_budget_le (pool := pool) (tm := tm) (rp := rp) (rm := rm)
    (bx := bx) (nb := nb) (nR := nR) (b := b + 1) hb
  have hrow := apply_row_budget_le (pool := pool) (tm := tm) (rp := rp) (rm := rm)
    (bx := bx) (nR := nR) (b := b)
  have h2 := apply_step_budget_le (pool := pool) (tm := tm) (rp := rp) (rm := rm)
    (bx := bx) (nR := nR) (b := b) (r := r)
  have hrm : (r + 1) * la ≤ nR * la := Nat.mul_le_mul_right la hr
  have hrs : rSymLenSum rp rm (r + 1) ≤ rSymLenSum rp rm nR := rSymLenSum_mono hr
  dsimp only at hrow h2
  rw [← hla] at hrow h2
  rw [← hlb] at h2
  omega

private theorem apply_je_wp (Γ : T.Env)
    (hMhas : ∀ xs m Q X, arMhasFromSpec xs m Q X →
      Γ "ar_mhas_from" [i64, i32, i32] [.bool] xs m Q X)
    (hMun : ∀ xs m Q X, arMunionSpec xs m Q X →
      Γ "ar_munion" [i64, i64, i32, i64] [i64] xs m Q X)
    {cx : BitVec 64} {sym : BitVec 32} {s0 s : ArCtxState}
    {tm0 tm1 pool0 pool1 : List (BitVec 32)} {ts0 tl0 th0 ts1 tl1 th1 : List (BitVec 64)}
    {tm0_1 tm1_1 pool0_1 pool1_1 qm : List (BitVec 32)} {qs ql qh : List (BitVec 64)}
    {ix ix2 bx vqOff' vq' : List (BitVec 32)} {vqSkip' : List (BitVec 8)}
    {partnerArr curRm : List (BitVec 32)} {curRl curRh : List (BitVec 64)}
    {curRp : List (BitVec 32)} {Valid : (Nat → Bool) → Prop} {R restTQ : Mem 64 → Prop}
    {nb : BitVec 32} {slB slR : BitVec 64} {qFin : Nat}
    {JB : Cont [i32, i32, i64, i32]} {qnB bB ti mOffBv : BitVec 32} {ptB cl ch : BitVec 64}
    {rI qnI : BitVec 32} {ptI rlBv rhBv l h : BitVec 64} {Js : Cont [i32, i64]}
    {poolB qmB : List (BitVec 32)} {qlB qhB : List (BitVec 64)}
    {n0 : BitVec 32} {Q : Post [.bool]} {X : XPost} {mI : Mem 64}
    (_hFoc0 : tMem s tm0_1 tm1_1 ts0 tl0 th0 ts1 tl1 th1 pool0_1 pool1_1 ⋆
        qMem s qm qs ql qh ix ix2 bx vqOff' vq' vqSkip' =
      (array (t := i32) (s.pool.getD s.pc.toNat 0#64)
        (if s.pc.toNat = 0 then pool0_1 else pool1_1) ⋆
       array (t := i32) (s.tm.getD s.tc.toNat 0#64) (if s.tc.toNat = 0 then tm0_1 else tm1_1) ⋆
       array64 (s.ts.getD s.tc.toNat 0#64) (if s.tc.toNat = 0 then ts0 else ts1) ⋆
       array64 (s.tl.getD s.tc.toNat 0#64) (if s.tc.toNat = 0 then tl0 else tl1) ⋆
       array64 (s.th.getD s.tc.toNat 0#64) (if s.tc.toNat = 0 then th0 else th1) ⋆
       array (t := i32) s.qm qm ⋆ array64 s.qs qs ⋆ array64 s.ql ql ⋆ array64 s.qh qh ⋆
       array (t := i32) s.bx bx ⋆ array (t := i32) s.vq_off vqOff' ⋆
       array (t := i32) s.vq vq' ⋆ array (t := i8) s.vq_skip vqSkip' ⋆ restTQ))
    (hCtx0 : ApplyLoopCtx cx sym s0 s tm0 tm1 pool0 pool1 ts0 tl0 th0 ts1 tl1 th1
      tm0_1 tm1_1 pool0_1 pool1_1 qm qs ql qh ix ix2 bx vqOff' vq' vqSkip'
      partnerArr curRm curRl curRh curRp Valid R
      (array (t := i32) (s.tm.getD s.tc.toNat 0#64) (if s.tc.toNat = 0 then tm0_1 else tm1_1) ⋆
       array64 (s.ts.getD s.tc.toNat 0#64) (if s.tc.toNat = 0 then ts0 else ts1) ⋆
       array64 (s.tl.getD s.tc.toNat 0#64) (if s.tc.toNat = 0 then tl0 else tl1) ⋆
       array64 (s.th.getD s.tc.toNat 0#64) (if s.tc.toNat = 0 then th0 else th1) ⋆
       array (t := i32) s.bx bx ⋆ array (t := i32) s.vq_off vqOff' ⋆
       array (t := i32) s.vq vq' ⋆ array (t := i8) s.vq_skip vqSkip' ⋆ restTQ)
      nb slB slR qFin)
    (hb_lt : bB.toNat < nb.toNat) (hr_lt : rI.toNat < s.cur_nr.toNat)
    (hqnB_le : qnB.toNat ≤ bB.toNat * s.cur_nr.toNat)
    (hspt_le : s.ptop.toNat ≤ ptB.toNat)
    (hptB_le : ptB.toNat ≤ s.ptop.toNat +
      (bB.toNat * rSymLenSum curRp curRm s.cur_nr.toNat +
        s.cur_nr.toNat * bxSymLenSum (if s.pc.toNat = 0 then pool0_1 else pool1_1)
          (if s.tc.toNat = 0 then tm0_1 else tm1_1) bx bB.toNat))
    (hmSl_eq : MonoSliceOk (if s.pc.toNat = 0 then pool0_1 else pool1_1) mOffBv.toNat s.ptop.toNat ∧
      ((if s.pc.toNat = 0 then pool0_1 else pool1_1).getD mOffBv.toNat 0#32).toNat + 1 < 2 ^ 32)
    (hmSo_eq : MonoSorted (if s.pc.toNat = 0 then pool0_1 else pool1_1) mOffBv.toNat)
    (hmOff_eq : mOffBv.toNat = ((if s.tc.toNat = 0 then tm0_1 else tm1_1).getD
      (bx.getD bB.toNat 0#32).toNat 0#32).toNat)
    (hbxM0 : sym.toNat ∈ symListAt (if s.pc.toNat = 0 then pool0_1 else pool1_1) mOffBv.toNat)
    (hsk0_d : vqSkip'.getD rI.toNat 0#8 = 0#8)
    (hrl_eq : rlBv = curRl.getD rI.toNat 0#64) (hrh_eq : rhBv = curRh.getD rI.toNat 0#64)
    (hcmul : coeff128 s.n_out.toNat l h =
      coeff128 s.n_out.toNat cl ch * coeff128 s.n_out.toNat rlBv rhBv)
    (hInvI' : ApplyInnerInv cx sym s pool0_1 pool1_1 qm qs ql qh curRm curRl curRh curRp Valid
      (array (t := i32) s.partner partnerArr ⋆ array (t := i32) s.cur_rm curRm ⋆
       array64 s.cur_rl curRl ⋆ array64 s.cur_rh curRh ⋆ array (t := i32) s.cur_rp curRp ⋆
       (array (t := i32) (s.tm.getD s.tc.toNat 0#64) (if s.tc.toNat = 0 then tm0_1 else tm1_1) ⋆
        array64 (s.ts.getD s.tc.toNat 0#64) (if s.tc.toNat = 0 then ts0 else ts1) ⋆
        array64 (s.tl.getD s.tc.toNat 0#64) (if s.tc.toNat = 0 then tl0 else tl1) ⋆
        array64 (s.th.getD s.tc.toNat 0#64) (if s.tc.toNat = 0 then th0 else th1) ⋆
        array (t := i32) s.bx bx ⋆ array (t := i32) s.vq_off vqOff' ⋆
        array (t := i32) s.vq vq' ⋆ array (t := i8) s.vq_skip vqSkip' ⋆ restTQ) ⋆ R)
      qnB.toNat ptB.toNat mOffBv.toNat cl ch poolB qmB qlB qhB qnI ptI rI mI)
    (hJs : ∀ xs m,
      (match xs with
       | (qnJ, ptJ, PUnit.unit) =>
         ApplyInnerInv cx sym s pool0_1 pool1_1 qm qs ql qh curRm curRl curRh curRp Valid
           (array (t := i32) s.partner partnerArr ⋆ array (t := i32) s.cur_rm curRm ⋆
            array64 s.cur_rl curRl ⋆ array64 s.cur_rh curRh ⋆ array (t := i32) s.cur_rp curRp ⋆
            (array (t := i32) (s.tm.getD s.tc.toNat 0#64)
              (if s.tc.toNat = 0 then tm0_1 else tm1_1) ⋆
             array64 (s.ts.getD s.tc.toNat 0#64) (if s.tc.toNat = 0 then ts0 else ts1) ⋆
             array64 (s.tl.getD s.tc.toNat 0#64) (if s.tc.toNat = 0 then tl0 else tl1) ⋆
             array64 (s.th.getD s.tc.toNat 0#64) (if s.tc.toNat = 0 then th0 else th1) ⋆
             array (t := i32) s.bx bx ⋆ array (t := i32) s.vq_off vqOff' ⋆
             array (t := i32) s.vq vq' ⋆ array (t := i8) s.vq_skip vqSkip' ⋆ restTQ) ⋆ R)
           qnB.toNat ptB.toNat mOffBv.toNat cl ch poolB qmB qlB qhB qnJ ptJ (rI + 1#32) m) →
      Js xs m) :
    wp Γ Q X (applyLoop4JEExpr cx sym s.cur_rm s.cur_rl s.cur_rh s.cur_rp s.cur_nr n0
      s.bx nb slB slR (s.pool.getD s.pc.toNat 0#64) (s.tm.getD s.tc.toNat 0#64)
      (s.tl.getD s.tc.toNat 0#64) (s.th.getD s.tc.toNat 0#64) s.ptop
      JB qnB bB ti mOffBv ptB cl ch rI qnI ptI rlBv rhBv l h Js) mI := by
  dsimp only [applyLoop4JEExpr, applyLoop4InnerExpr, applyLoop4Expr, applyAfterLoop3Expr,
    applyLoop3Expr, applyAfterLoop2Expr, applyLoop2Expr, applyLoop1ExitExpr, applyLoop1Expr]
  c0_hsteps_nogrp
  let dstPool := if s.pc.toNat = 0 then pool0_1 else pool1_1
  let dstTm := if s.tc.toNat = 0 then tm0_1 else tm1_1
  let srcTs := if s.tc.toNat = 0 then ts0 else ts1
  let srcTl := if s.tc.toNat = 0 then tl0 else tl1
  let srcTh := if s.tc.toNat = 0 then th0 else th1
  let rest4 := array (t := i32) (s.tm.getD s.tc.toNat 0#64) dstTm ⋆
    array64 (s.ts.getD s.tc.toNat 0#64) srcTs ⋆ array64 (s.tl.getD s.tc.toNat 0#64) srcTl ⋆
    array64 (s.th.getD s.tc.toNat 0#64) srcTh ⋆ array (t := i32) s.bx bx ⋆
    array (t := i32) s.vq_off vqOff' ⋆ array (t := i32) s.vq vq' ⋆
    array (t := i8) s.vq_skip vqSkip' ⋆ restTQ
  let Rloop4 := array (t := i32) s.partner partnerArr ⋆ array (t := i32) s.cur_rm curRm ⋆
    array64 s.cur_rl curRl ⋆ array64 s.cur_rh curRh ⋆ array (t := i32) s.cur_rp curRp ⋆
    rest4 ⋆ R
  have hnr_eq : s.cur_nr = s0.cur_nr := by conv => lhs; rw [hCtx0.hs1]
  have hdstPool_len : s0.pcap.toNat ≤ dstPool.length := by
    dsimp only [dstPool]; split; exact hCtx0.hp0_len; exact hCtx0.hp1_len
  have hr_nr0 : rI.toNat < s0.cur_nr.toNat := by rw [← hnr_eq]; exact hr_lt
  obtain ⟨_, hqnI_ge, hqnI_le, hptI_ge, hptI_le, poolI, qmI, qsI, qlI, qhI,
    hlI1, hlI2, hlI3, hlI4, hlI5, hpreI, hSlI, hSoI, hSiI, hWI, hSyI, hEvI, hmI⟩ := hInvI'
  have hInvI0 : ApplyInnerInv cx sym s pool0_1 pool1_1 qm qs ql qh curRm curRl curRh curRp
      Valid Rloop4 qnB.toNat ptB.toNat mOffBv.toNat cl ch poolB qmB qlB qhB qnI ptI rI mI :=
    ⟨by omega, hqnI_ge, hqnI_le, hptI_ge, hptI_le, poolI, qmI, qsI, qlI, qhI,
      hlI1, hlI2, hlI3, hlI4, hlI5, hpreI, hSlI, hSoI, hSiI, hWI, hSyI, hEvI, hmI⟩
  refine wp_join_group (fun (_ : Tup Val []) mE => mE = mI) ?_ ?_
  · rintro JE ⟨⟩ mE hmE
    subst mE
    have hnr_vq : s0.cur_nr.toNat < vqOff'.length :=
      Nat.lt_of_le_of_lt (le_trans (Nat.le_mul_of_pos_left _ hCtx0.hnb_pos) hCtx0.hnb_nr_q)
        hCtx0.hvqOff_len
    have hr_vqo0 : rI.toNat < vqOff'.length := by omega
    have hr_vqo1 : rI.toNat + 1 < vqOff'.length := by omega
    have hr_rp1 : (rI + 1#32).toNat = rI.toNat + 1 := apply_bv32_add1_lt hr_lt s.cur_nr.isLt
    have hr_vqo1' : (rI + 1#32).toNat < vqOff'.length := by rw [hr_rp1]; exact hr_vqo1
    c0_hsteps_nogrp
    let q1 := vqOff'[(rI + 1#32).toNat]'hr_vqo1'
    let q0 := vqOff'[rI.toNat]'hr_vqo0
    have hq1_eq : q1.toNat = (vqOff'.getD (rI.toNat + 1) 0#32).toNat := by
      dsimp only [q1]; simp only [hr_rp1]
      rw [getD_eq_getElem vqOff' 0#32 hr_vqo1]
    have hq0_eq : q0.toNat = (vqOff'.getD rI.toNat 0#32).toNat := by
      dsimp only [q0]; rw [getD_eq_getElem vqOff' 0#32 hr_vqo0]
    have hq0_q1 : q0.toNat ≤ q1.toNat := by
      rw [hq0_eq, hq1_eq]; exact ((hCtx0.hVqOk rI.toNat hr_nr0).2 hsk0_d).1
    have hq1_fin : q1.toNat ≤ qFin := by
      rw [hq1_eq]; exact ((hCtx0.hVqOk rI.toNat hr_nr0).2 hsk0_d).2.1
    have hm_pre_m : MonoSliceOk poolI mOffBv.toNat poolI.length := by
      have h1 := hmSl_eq.1
      have hpre_len : poolI.getD mOffBv.toNat 0#32 = dstPool.getD mOffBv.toNat 0#32 :=
        hpreI mOffBv.toNat h1.1
      have hpt_pi : s.ptop.toNat ≤ poolI.length := by
        have := hCtx0.hpt_cap; have hdp := hdstPool_len; dsimp only [dstPool] at hdp; omega
      exact ⟨Nat.lt_of_lt_of_le h1.1 hpt_pi, by rw [hpre_len]; exact Nat.le_trans h1.2 hpt_pi⟩
    have hm_32_I : (poolI.getD mOffBv.toNat 0#32).toNat + 1 < 2 ^ 32 := by
      rw [hpreI mOffBv.toNat hmSl_eq.1.1]; exact hmSl_eq.2
    refine wp_loop_group (fun remV ⟨qq, van, ⟨⟩⟩ mV =>
        mV = mI ∧ q0.toNat ≤ qq.toNat ∧ qq.toNat ≤ q1.toNat ∧
        remV = q1.toNat - qq.toNat ∧
        (van = true → ∀ σ, Valid σ →
          (monoValL σ ((symListAt dstPool mOffBv.toNat).filter
            (fun z => decide (z ≠ sym.toNat))) &&
           monoValL σ (symListAt curRp (curRm.getD rI.toNat 0#32).toNat)) = false))
      ?_ ?_
    · rintro JV remV ⟨qq, van, ⟨⟩⟩ mV hrecV ⟨hmV, hq0_qq, hqq_q1, hremV, hvan⟩
      subst mV
      refine wp_join_group (fun (_ : Tup Val []) m2 => m2 = mI) ?_ ?_
      · rintro Js2 ⟨⟩ m2 hm2
        subst m2
        refine wp_join_group (fun ⟨qnJ, ptJ, ⟨⟩⟩ mJ =>
            ApplyInnerInv cx sym s pool0_1 pool1_1 qm qs ql qh curRm curRl curRh curRp
              Valid Rloop4 qnB.toNat ptB.toNat mOffBv.toNat cl ch poolB qmB qlB qhB
              qnJ ptJ (rI + 1#32) mJ)
          ?_ ?_
        · rintro Js3 ⟨qnJ, ptJ, ⟨⟩⟩ mJ hInvJ
          c0_hsteps_nogrp
          exact hJs (qnJ, ptJ, ⟨⟩) mJ hInvJ
        · intro Js3 hJs3
          c0_hsteps_nogrp
          · have hv : van = true := by c0_bv_omega
            exact hJs3 (qnI, ptI, ⟨⟩) mI (apply_inner_skip_step hr_lt (fun σ hV => by
              dsimp only [termEval]; rw [← hrl_eq, ← hrh_eq]
              exact apply_van_zero_prod (hvan hv σ hV)) hInvI0)
          · have hr_rm : rI.toNat < curRm.length := Nat.lt_of_lt_of_le hr_nr0 hCtx0.hcurNr_rm
            let mrOffBv := curRm[rI.toNat]'hr_rm
            have hmr_eq : mrOffBv.toNat = (curRm.getD rI.toNat 0#32).toNat := by
              dsimp only [mrOffBv]; rw [getD_eq_getElem curRm 0#32 hr_rm]
            c0_hsteps_nogrp
            have hmrSl := hCtx0.hcurSl rI.toNat hr_nr0
            have hmr32 := hCtx0.hcurMr32 rI.toNat hr_nr0
            have hmrSo := hCtx0.hcurSo rI.toNat hr_nr0
            rw [← hmr_eq] at hmrSl hmr32 hmrSo
            let la := (poolI.getD mOffBv.toNat 0#32).toNat
            let lb := (curRp.getD mrOffBv.toNat 0#32).toNat
            have hla_eq : la = (dstPool.getD mOffBv.toNat 0#32).toNat := by
              dsimp only [la]; rw [hpreI _ hmSl_eq.1.1]
            have hstep_bd : ptI.toNat + (la + lb) ≤ s0.pcap.toNat := by
              have hptB' := hptB_le; have hptI' := hptI_le; have hcap := hCtx0.hpt_cap
              rw [hnr_eq] at hptB'; rw [← hla_eq] at hptI'; rw [hCtx0.hslB, hCtx0.hslR] at hcap
              exact apply_je_step_bd hb_lt (by rw [← hnr_eq]; exact hr_lt) hcap hptB' hptI'
                (by dsimp only [dstPool, dstTm] at hla_eq; rw [← hmOff_eq]; exact hla_eq)
                (by dsimp only [lb]; rw [← hmr_eq])
            have hpt_le_pool : ptI.toNat ≤ poolI.length := by
              have hdp := hdstPool_len; dsimp only [dstPool] at hdp; omega
            let poolPre := poolI.take ptI.toNat
            let poolTail := poolI.drop ptI.toNat
            have hpt4_eq : s.pool.getD s.pc.toNat 0#64 + BitVec.ofNat 64 (4 * ptI.toNat) =
                s.pool.getD s.pc.toNat 0#64 + ptI * 4#64 := by
              congr 1; apply BitVec.eq_of_toNat_eq
              simp [BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.mul_comm 4 ptI.toNat]
            let RnoRp := array (t := i32) s.partner partnerArr ⋆
              array (t := i32) s.cur_rm curRm ⋆ array64 s.cur_rl curRl ⋆
              array64 s.cur_rh curRh ⋆ rest4 ⋆ R
            have hm_split : (array (t := i32) (s.pool.getD s.pc.toNat 0#64 + ptI * 4#64) poolTail ⋆
                array (t := i32) (s.pool.getD s.pc.toNat 0#64) poolPre ⋆
                array (t := i32) s.cur_rp curRp ⋆
                (arCtxMem cx s ⋆ array (t := i32) s.qm qmI ⋆ array64 s.qs qsI ⋆
                  array64 s.ql qlI ⋆ array64 s.qh qhI ⋆ RnoRp)) mI := by
              have hsp := array32_split_at (s.pool.getD s.pc.toNat 0#64) poolI hpt_le_pool
              have hm' := hmI; rw [hsp, hpt4_eq] at hm'
              exact sep_cast hm' (by
                dsimp only [Rloop4, RnoRp, rest4, dstTm, srcTs, srcTl, srcTh, poolPre, poolTail]
                ac_rfl)
            have hspt_I : s.ptop.toNat ≤ ptI.toNat := le_trans hspt_le hptI_ge
            have hm_pre_sl : MonoSliceOk poolPre mOffBv.toNat poolPre.length := by
              refine monoSliceOk_take ⟨Nat.lt_of_lt_of_le hmSl_eq.1.1 hspt_I, ?_⟩ hpt_le_pool
              rw [hpreI _ hmSl_eq.1.1]; exact le_trans hmSl_eq.1.2 hspt_I
            have hpre_take : ∀ idx < s.ptop.toNat,
                poolPre.getD idx 0#32 = dstPool.getD idx 0#32 := fun idx hidx => by
              rw [list_getD_take poolI 0#32 (by omega), hpreI idx hidx]
            have hsym_pre : symListAt poolPre mOffBv.toNat = symListAt dstPool mOffBv.toNat :=
              symListAt_congr_take hmSl_eq.1 hpre_take
            have hm_has_sym : ∃ idx, 1 ≤ idx ∧ idx ≤ (poolPre.getD mOffBv.toNat 0#32).toNat ∧
                poolPre.getD (mOffBv.toNat + idx) 0#32 = sym := by
              have hmem' : sym.toNat ∈ symListAt poolPre mOffBv.toNat := by
                rw [hsym_pre]; exact hbxM0
              obtain ⟨idx, hidx_m, hidx_eq⟩ := List.mem_map.mp hmem'
              rw [List.mem_range] at hidx_m
              refine ⟨1 + idx, by omega, by omega, BitVec.eq_of_toNat_eq ?_⟩
              simpa only [Nat.add_assoc] using hidx_eq
            have hla_pre : (poolPre.getD mOffBv.toNat 0#32).toNat = la := by
              dsimp only [la, poolPre]
              rw [list_getD_take poolI 0#32 (lt_of_lt_of_le hmSl_eq.1.1 hspt_I)]
            have ha_ptr := apply_je_ptr4 (s.pool.getD s.pc.toNat 0#64) mOffBv
            have hb_ptr := apply_je_ptr4 s.cur_rp mrOffBv
            refine wp_call_of_spec _ _ (hMun ⟨s.pool.getD s.pc.toNat 0#64 + ptI * 4#64,
                s.pool.getD s.pc.toNat 0#64 + BitVec.setWidth 64 mOffBv * 4#64, sym,
                s.cur_rp + BitVec.setWidth 64 mrOffBv * 4#64, ⟨⟩⟩ mI _ X
              ⟨poolTail, s.pool.getD s.pc.toNat 0#64, poolPre, mOffBv.toNat,
                s.cur_rp, curRp, mrOffBv.toNat, _, ha_ptr, hb_ptr,
                hm_pre_sl, hmrSl, by rw [hla_pre, hla_eq]; exact hmSl_eq.2, hmr32,
                hm_has_sym,
                (by have hdp := hdstPool_len; dsimp only [dstPool] at hdp
                    dsimp only [poolTail]; rw [List.length_drop, hla_pre]; omega),
                by rw [hla_pre, hla_eq]; exact Nat.lt_of_le_of_lt (by omega) hCtx0.hpcap32,
                hm_split, fun sig out' mU hout_len hout_bd hout_sy hout_so hsig_u _ hmU => ?_⟩)
            let poolI' := poolPre ++ out'
            have hout_len' : out'.length = poolI.length - ptI.toNat := by
              rw [hout_len, List.length_drop]
            have hmU' : (arCtxMem cx s ⋆ array (t := i32) (s.pool.getD s.pc.toNat 0#64) poolI' ⋆
                array (t := i32) s.qm qmI ⋆ array64 s.qs qsI ⋆ array64 s.ql qlI ⋆
                array64 s.qh qhI ⋆ Rloop4) mU := by
              have hsp := poolTail_split (s.pool.getD s.pc.toNat 0#64) poolPre out'
              rw [List.length_take_of_le hpt_le_pool, hpt4_eq] at hsp
              have hmU0 : (array (t := i32) (s.pool.getD s.pc.toNat 0#64) poolPre ⋆
                  array (t := i32) (s.pool.getD s.pc.toNat 0#64 + ptI * 4#64) out' ⋆
                  (array (t := i32) s.cur_rp curRp ⋆
                    (arCtxMem cx s ⋆ array (t := i32) s.qm qmI ⋆ array64 s.qs qsI ⋆
                      array64 s.ql qlI ⋆ array64 s.qh qhI ⋆ RnoRp))) mU :=
                sep_cast hmU (by ac_rfl)
              rw [hsp] at hmU0
              exact sep_cast hmU0 (by dsimp only [Rloop4, RnoRp, poolI']; ac_rfl)
            have hqnI_lt_qcap : qnI.toNat < s0.qcap.toNat := by
              have h1 : (bB.toNat + 1) * s0.cur_nr.toNat ≤ nb.toNat * s0.cur_nr.toNat :=
                Nat.mul_le_mul_right _ hb_lt
              have h2 : (bB.toNat + 1) * s0.cur_nr.toNat =
                  bB.toNat * s0.cur_nr.toNat + s0.cur_nr.toNat := Nat.succ_mul _ _
              have hqnB_le' : qnB.toNat ≤ bB.toNat * s0.cur_nr.toNat := by
                rw [← hnr_eq]; exact hqnB_le
              have := hCtx0.hnb_nr_q; omega
            have hqn_qm : qnI.toNat < qmI.length := by have := hCtx0.hqm_len; omega
            have hqn_qs : qnI.toNat < qsI.length := by have := hCtx0.hqs_len; omega
            have hqn_ql : qnI.toNat < qlI.length := by have := hCtx0.hql_len; omega
            have hqn_qh : qnI.toNat < qhI.length := by have := hCtx0.hqh_len; omega
            have hstep := apply_emit_step_inv (qlL := qlI) (qhL := qhI) (l := l) (h := h) hspt_I
              (by have hdp := hdstPool_len; dsimp only [dstPool] at hdp
                  rw [hla_pre] at hout_bd; omega)
              (by rw [hla_pre] at hout_bd; exact Nat.lt_of_le_of_lt (by omega) hCtx0.hpcap32)
              hqn_qm hqn_qs hout_len'
              (hout_so (by unfold MonoSorted; rw [hsym_pre]; exact hmSo_eq) hmrSo)
              hsig_u hpreI hSlI hSoI hSiI hWI
            have hptI_32 : ptI.toNat < 2 ^ 32 :=
              Nat.lt_of_le_of_lt (Nat.le_trans (Nat.le_add_right _ _) hstep_bd) hCtx0.hpcap32
            have hpt_32_eq : ptI.setWidth 32 = BitVec.ofNat 32 ptI.toNat := by
              apply BitVec.eq_of_toNat_eq
              rw [apply_bv32_of_pt hptI_32, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hptI_32]
            have hqn_sw : (BitVec.setWidth 64 qnI : BitVec 64).toNat = qnI.toNat := by
              rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans qnI.isLt (by decide))]
            have hpoolI'_len : poolI'.length = poolI.length := by
              dsimp only [poolI', poolPre]
              rw [List.length_append, List.length_take_of_le hpt_le_pool, hout_len']
              omega
            have hla_pos : 1 ≤ la := by
              obtain ⟨idx, h1, h2, _⟩ := hm_has_sym
              rw [hla_pre] at h2; omega
            have hpt_lt' : ptI.toNat < poolI'.length := by
              have hdp := hdstPool_len
              dsimp only [dstPool] at hdp hlI1
              omega
            have hpt4_lt : s.pool.getD s.pc.toNat 0#64 + ptI * 4#64 =
                s.pool.getD s.pc.toNat 0#64 + BitVec.ofNat 64 (4 * ptI.toNat) := by
              congr 1; apply BitVec.eq_of_toNat_eq
              simp [BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.mul_comm 4 ptI.toNat]
            c0_hsteps_nogrp
            have hpt_step : (ptI + BitVec.setWidth 64 (poolI'[ptI.toNat]'hpt_lt') +
                1#64).toNat = ptI.toNat + (out'.getD 0 0#32).toNat + 1 := by
              have hlen0' : poolI'[ptI.toNat]'hpt_lt' = out'.getD 0 0#32 := by
                rw [← getD_eq_getElem poolI' 0#32 hpt_lt']
                simpa only [Nat.add_zero] using hstep.2.2.2.1 0 (Nat.zero_le _)
              rw [hlen0']
              exact apply_pt_plus_len
                (by have := hout_bd; rw [hla_pre] at this; omega)
                hCtx0.hpcap32
            have hpt_step' : (ptI + BitVec.setWidth 64
                (poolI'[ptI.toNat + (BitVec.ofNat 64 0).toNat]'(by
                  rw [show (BitVec.ofNat 64 0).toNat = 0 from rfl, Nat.add_zero]; exact hpt_lt')) +
                1).toNat = ptI.toNat + (out'.getD 0 0#32).toNat + 1 := by
              simpa only [show (BitVec.ofNat 64 0).toNat = 0 from rfl, Nat.add_zero,
                show (1 : BitVec 64) = 1#64 from rfl] using hpt_step
            have hqn_p1 : (qnI + 1#32).toNat = qnI.toNat + 1 :=
              apply_bv32_add1_lt (by omega) hCtx0.hqcap32
            have hrp1 : (rI + 1#32).toNat = rI.toNat + 1 := apply_bv32_add1_lt hr_lt s.cur_nr.isLt
            have hm_bd' : ptI.toNat + (out'.getD 0 0#32).toNat + 1 ≤
                ptB.toNat + (rI.toNat + 1) * (dstPool.getD mOffBv.toNat 0#32).toNat +
                  rSymLenSum curRp curRm (rI.toNat + 1) := by
              have hptI'' :
                  ptI.toNat ≤ ptB.toNat + rI.toNat * la + rSymLenSum curRp curRm rI.toNat := by
                dsimp only [dstPool] at hla_eq; rw [hla_eq]; exact hptI_le
              have hmul : (rI.toNat + 1) * la = rI.toNat * la + la := Nat.succ_mul _ _
              rw [rSymLenSum_succ, ← hmr_eq, ← hla_eq, hmul]
              have := hout_bd; rw [hla_pre] at this; omega
            have hqm_eq : qmI.set qnI.toNat (ptI.setWidth 32) =
                qmI.set qnI.toNat (BitVec.ofNat 32 ptI.toNat) := by rw [hpt_32_eq]
            refine hJs3 (qnI + 1#32, _, ⟨⟩) _
              ⟨by omega, by rw [hqn_p1]; omega, by rw [hqn_p1]; omega,
               by rw [hpt_step']; omega, by rw [hpt_step', hrp1]; exact hm_bd',
               poolI', qmI.set qnI.toNat (BitVec.ofNat 32 ptI.toNat),
               qsI.set qnI.toNat sig, qlI.set qnI.toNat l, qhI.set qnI.toNat h,
               by rw [hstep.1]; exact hlI1, by simp [hlI2], by simp [hlI3],
               by simp [hlI4], by simp [hlI5],
               hstep.2.1,
               (by rw [hpt_step', hqn_p1]; exact hstep.2.2.2.2.1),
               (by rw [hqn_p1]; exact hstep.2.2.2.2.2.1),
               (by rw [hqn_p1]; exact hstep.2.2.2.2.2.2.1),
               (by rw [hpt_step', hqn_p1]; exact hstep.2.2.2.2.2.2.2),
               (fun bd hSbM hSbR hBase i hi x hx => by
                 rw [hqn_p1] at hi
                 have hpt_toNat : (BitVec.ofNat 32 ptI.toNat).toNat = ptI.toNat := by
                   rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hptI_32]
                 rw [getD_set_eq qmI 0#32 _ hqn_qm] at hx
                 by_cases heq : i = qnI.toNat
                 · simp only [heq, ↓reduceIte, hpt_toNat] at hx
                   have hsym_out : symListAt poolI' ptI.toNat = symListAt out' 0 := by
                     have h0 : poolI'.getD ptI.toNat 0#32 = out'.getD 0 0#32 := by
                       simpa only [Nat.add_zero] using hstep.2.2.2.1 0 (Nat.zero_le _)
                     simp only [symListAt, h0, Nat.zero_add]
                     apply List.map_congr_left
                     intro q hq
                     rw [List.mem_range] at hq
                     rw [show ptI.toNat + 1 + q = ptI.toNat + (1 + q) by omega,
                       hstep.2.2.2.1 (1 + q) (by omega)]
                   rw [hsym_out, hout_sy] at hx
                   rcases hx with ⟨hx, _⟩ | hx
                   · rw [hsym_pre] at hx; exact hSbM x hx
                   · rw [hmr_eq] at hx; exact hSbR rI.toNat hr_lt x hx
                 · have hilt : i < qnI.toNat := by omega
                   simp only [heq, ↓reduceIte] at hx
                   rw [symListAt_congr_take (hSlI i hilt).1 hstep.2.2.1] at hx
                   exact hSyI bd hSbM hSbR hBase i hilt x hx),
               (fun σ hV => ?_), ?_⟩
            · have hout_sy' : ∀ z, z ∈ symListAt out' 0 ↔
                  (z ∈ symListAt poolI mOffBv.toNat ∧ z ≠ sym.toNat) ∨
                    z ∈ symListAt curRp mrOffBv.toNat := by
                intro z; rw [symListAt_congr_take hmSl_eq.1 hpreI, ← hsym_pre]
                exact hout_sy z
              rw [hqn_p1, apply_emit_step_eval hptI_32 hpt_le_pool hqn_qm hqn_ql hqn_qh hout_sy'
                  (fun i hi => (hSlI i hi).1) hstep.2.2.2.1 hcmul,
                hEvI σ hV, symListAt_congr_take hmSl_eq.1 hpreI]
              simp only [hrp1, List.range_succ, List.foldl_append, List.foldl_cons,
                List.foldl_nil, termEval, ← hmr_eq, ← hrl_eq, ← hrh_eq]
              ac_rfl
            · rw [← hqm_eq]; exact sep_cast ‹_› (by ac_rfl)
      · intro Js2 hJs2
        c0_hsteps_nogrp
        · exact hJs2 ⟨⟩ mI rfl
        · have hqq_lt : qq.toNat < q1.toNat := by c0_bv_omega
          have hvan_f : van = false := hc
          have hqq_vq : qq.toNat < vq'.length :=
            lt_of_lt_of_le hqq_lt (le_trans hq1_fin (le_trans hCtx0.hqFin_le hCtx0.hvq_len))
          let vqVal := vq'[qq.toNat]'hqq_vq
          c0_hsteps_nogrp
          let Rmhas := arCtxMem cx s ⋆
            array (t := i32) s.qm qmI ⋆ array64 s.qs qsI ⋆ array64 s.ql qlI ⋆
            array64 s.qh qhI ⋆ Rloop4
          have h_mhas : (array (t := i32) (s.pool.getD s.pc.toNat 0#64) poolI ⋆ Rmhas) mI :=
            sep_cast hmI (by dsimp only [Rmhas, Rloop4, rest4, dstTm, srcTs, srcTl, srcTh]; ac_rfl)
          refine wp_call_of_spec _ _ (hMhas ⟨_, 1#32, vqVal, ⟨⟩⟩ mI _ X
            ⟨s.pool.getD s.pc.toNat 0#64, poolI, mOffBv.toNat, Rmhas,
              (by simp only [List.getD_eq_getElem?_getD]; congr 1
                  apply BitVec.eq_of_toNat_eq
                  simp [BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
                    Nat.mul_comm 4 mOffBv.toNat]),
              hm_pre_m, hm_32_I, (by decide),
              (by rw [show (1#32 : BitVec 32).toNat = 1 from rfl]; omega),
              h_mhas, fun okV hokV _ => ?_⟩)
          c0_hsteps_nogrp
          have hqqp1 : (qq + 1#32).toNat = qq.toNat + 1 := apply_bv32_add1_lt hqq_lt q1.isLt
          refine hrecV (q1.toNat - (qq + 1#32).toNat) (qq + 1#32, okV, ⟨⟩) mI
            (by omega) ⟨rfl, by rw [hqqp1]; omega, by rw [hqqp1]; omega, rfl, ?_⟩
          intro hokT σ hV
          obtain ⟨idx, hidx1, hidx_le, hidx_eq⟩ := hokV hokT
          have hidx_eq' : dstPool.getD (mOffBv.toNat + idx) 0#32 = vq'.getD qq.toNat 0#32 := by
            have hlt_pt : mOffBv.toNat + idx < s.ptop.toNat := by
              have h1 := hmSl_eq.1.2
              have h2 := hpreI mOffBv.toNat hmSl_eq.1.1
              rw [h2] at hidx_le; omega
            rw [← hpreI _ hlt_pt, hidx_eq]
            dsimp only [vqVal]; exact (getD_eq_getElem vq' 0#32 hqq_vq).symm
          exact apply_van_step_true hCtx0.hPart (hCtx0.hVqOk rI.toNat hr_nr0) hsk0_d
            (by rw [← hq0_eq]; exact hq0_qq) (by rw [← hq1_eq]; exact hqq_lt)
            ⟨idx, hidx1, by rw [← hpreI _ hmSl_eq.1.1]; exact hidx_le, hidx_eq'⟩ σ hV
        · exact hJs2 ⟨⟩ mI rfl
    · intro JV hJV
      c0_hsteps_nogrp
      exact hJV (q1.toNat - q0.toNat) (q0, false, ⟨⟩) mI
        ⟨rfl, le_refl _, hq0_q1, rfl, fun h => by cases h⟩
  · intro JE hJE
    c0_hsplit_nobound
    · exact hJE ⟨⟩ mI rfl
    · c0_hsplit_nobound
      · exact hJE ⟨⟩ mI rfl
      · have hl0 : l = 0#64 := by c0_bv_omega
        have hh0 : h = 0#64 := by c0_bv_omega
        subst hl0 hh0
        c0_hsteps_nogrp
        exact hJs (qnI, ptI, ⟨⟩) mI (apply_inner_skip_step hr_lt (fun σ hV => by
          dsimp only [termEval]; rw [← hrl_eq, ← hrh_eq]
          have hcz : coeff128 s.n_out.toNat cl ch *
              coeff128 s.n_out.toNat rlBv rhBv = 0#(s.n_out.toNat) := by
            rw [← hcmul, apply_cmul_zero]
          exact apply_mul_ite_zero _ _ hcz) hInvI0)

private theorem apply_inner_loop_wp (Γ : T.Env)
    (hMhas : ∀ xs m Q X, arMhasFromSpec xs m Q X →
      Γ "ar_mhas_from" [i64, i32, i32] [.bool] xs m Q X)
    (hMun : ∀ xs m Q X, arMunionSpec xs m Q X →
      Γ "ar_munion" [i64, i64, i32, i64] [i64] xs m Q X)
    (hCmul : ∀ xs m Q X, arCmulSpec xs m Q X →
      Γ "ar_cmul" [i64, i64, i64, i64, i64] [i64, i64] xs m Q X)
    {cx : BitVec 64} {sym : BitVec 32} {s0 s : ArCtxState}
    {tm0 tm1 pool0 pool1 : List (BitVec 32)} {ts0 tl0 th0 ts1 tl1 th1 : List (BitVec 64)}
    {tm0_1 tm1_1 pool0_1 pool1_1 qm : List (BitVec 32)} {qs ql qh : List (BitVec 64)}
    {ix ix2 bx vqOff' vq' : List (BitVec 32)} {vqSkip' : List (BitVec 8)}
    {partnerArr curRm : List (BitVec 32)} {curRl curRh : List (BitVec 64)}
    {curRp : List (BitVec 32)} {Valid : (Nat → Bool) → Prop} {R restTQ : Mem 64 → Prop}
    {nb : BitVec 32} {slB slR : BitVec 64} {qFin : Nat}
    {JB : Cont [i32, i32, i64, i32]} {qnB bB ti mOffBv : BitVec 32} {ptB cl ch : BitVec 64}
    {n0 : BitVec 32} {Q : Post [.bool]} {X : XPost} {mB : Mem 64}
    (hFoc0 : tMem s tm0_1 tm1_1 ts0 tl0 th0 ts1 tl1 th1 pool0_1 pool1_1 ⋆
        qMem s qm qs ql qh ix ix2 bx vqOff' vq' vqSkip' =
      (array (t := i32) (s.pool.getD s.pc.toNat 0#64)
        (if s.pc.toNat = 0 then pool0_1 else pool1_1) ⋆
       array (t := i32) (s.tm.getD s.tc.toNat 0#64) (if s.tc.toNat = 0 then tm0_1 else tm1_1) ⋆
       array64 (s.ts.getD s.tc.toNat 0#64) (if s.tc.toNat = 0 then ts0 else ts1) ⋆
       array64 (s.tl.getD s.tc.toNat 0#64) (if s.tc.toNat = 0 then tl0 else tl1) ⋆
       array64 (s.th.getD s.tc.toNat 0#64) (if s.tc.toNat = 0 then th0 else th1) ⋆
       array (t := i32) s.qm qm ⋆ array64 s.qs qs ⋆ array64 s.ql ql ⋆ array64 s.qh qh ⋆
       array (t := i32) s.bx bx ⋆ array (t := i32) s.vq_off vqOff' ⋆
       array (t := i32) s.vq vq' ⋆ array (t := i8) s.vq_skip vqSkip' ⋆ restTQ))
    (hCtx0 : ApplyLoopCtx cx sym s0 s tm0 tm1 pool0 pool1 ts0 tl0 th0 ts1 tl1 th1
      tm0_1 tm1_1 pool0_1 pool1_1 qm qs ql qh ix ix2 bx vqOff' vq' vqSkip'
      partnerArr curRm curRl curRh curRp Valid R
      (array (t := i32) (s.tm.getD s.tc.toNat 0#64) (if s.tc.toNat = 0 then tm0_1 else tm1_1) ⋆
       array64 (s.ts.getD s.tc.toNat 0#64) (if s.tc.toNat = 0 then ts0 else ts1) ⋆
       array64 (s.tl.getD s.tc.toNat 0#64) (if s.tc.toNat = 0 then tl0 else tl1) ⋆
       array64 (s.th.getD s.tc.toNat 0#64) (if s.tc.toNat = 0 then th0 else th1) ⋆
       array (t := i32) s.bx bx ⋆ array (t := i32) s.vq_off vqOff' ⋆
       array (t := i32) s.vq vq' ⋆ array (t := i8) s.vq_skip vqSkip' ⋆ restTQ)
      nb slB slR qFin)
    (hb_lt : bB.toNat < nb.toNat)
    (hmSl_eq : MonoSliceOk (if s.pc.toNat = 0 then pool0_1 else pool1_1) mOffBv.toNat s.ptop.toNat ∧
      ((if s.pc.toNat = 0 then pool0_1 else pool1_1).getD mOffBv.toNat 0#32).toNat + 1 < 2 ^ 32)
    (hmSo_eq : MonoSorted (if s.pc.toNat = 0 then pool0_1 else pool1_1) mOffBv.toNat)
    (hmOff_eq : mOffBv.toNat = ((if s.tc.toNat = 0 then tm0_1 else tm1_1).getD
      (bx.getD bB.toNat 0#32).toNat 0#32).toNat)
    (hcl_eq : cl = (if s.tc.toNat = 0 then tl0 else tl1).getD (bx.getD bB.toNat 0#32).toNat 0#64)
    (hch_eq : ch = (if s.tc.toNat = 0 then th0 else th1).getD (bx.getD bB.toNat 0#32).toNat 0#64)
    (hbxM0 : sym.toNat ∈ symListAt (if s.pc.toNat = 0 then pool0_1 else pool1_1) mOffBv.toNat)
    (hOuterInv : ApplyOuterInv cx s tm0_1 tm1_1 pool0_1 pool1_1 tl0 th0 tl1 th1 qm qs ql qh
      bx curRm curRp nb Valid
      (array (t := i32) s.partner partnerArr ⋆ array (t := i32) s.cur_rm curRm ⋆
       array64 s.cur_rl curRl ⋆ array64 s.cur_rh curRh ⋆ array (t := i32) s.cur_rp curRp ⋆
       (array (t := i32) (s.tm.getD s.tc.toNat 0#64) (if s.tc.toNat = 0 then tm0_1 else tm1_1) ⋆
        array64 (s.ts.getD s.tc.toNat 0#64) (if s.tc.toNat = 0 then ts0 else ts1) ⋆
        array64 (s.tl.getD s.tc.toNat 0#64) (if s.tc.toNat = 0 then tl0 else tl1) ⋆
        array64 (s.th.getD s.tc.toNat 0#64) (if s.tc.toNat = 0 then th0 else th1) ⋆
        array (t := i32) s.bx bx ⋆ array (t := i32) s.vq_off vqOff' ⋆
        array (t := i32) s.vq vq' ⋆ array (t := i8) s.vq_skip vqSkip' ⋆ restTQ) ⋆ R)
      qnB ptB bB mB)
    (hJB : ∀ (qnJ : BitVec 32) (ptJ : BitVec 64) (mJ : Mem 64),
      ApplyOuterInv cx s tm0_1 tm1_1 pool0_1 pool1_1 tl0 th0 tl1 th1 qm qs ql qh
        bx curRm curRp nb Valid
        (array (t := i32) s.partner partnerArr ⋆ array (t := i32) s.cur_rm curRm ⋆
         array64 s.cur_rl curRl ⋆ array64 s.cur_rh curRh ⋆ array (t := i32) s.cur_rp curRp ⋆
         (array (t := i32) (s.tm.getD s.tc.toNat 0#64) (if s.tc.toNat = 0 then tm0_1 else tm1_1) ⋆
          array64 (s.ts.getD s.tc.toNat 0#64) (if s.tc.toNat = 0 then ts0 else ts1) ⋆
          array64 (s.tl.getD s.tc.toNat 0#64) (if s.tc.toNat = 0 then tl0 else tl1) ⋆
          array64 (s.th.getD s.tc.toNat 0#64) (if s.tc.toNat = 0 then th0 else th1) ⋆
          array (t := i32) s.bx bx ⋆ array (t := i32) s.vq_off vqOff' ⋆
          array (t := i32) s.vq vq' ⋆ array (t := i8) s.vq_skip vqSkip' ⋆ restTQ) ⋆ R)
        qnJ ptJ (bB + 1#32) mJ →
      JB (s.cur_nr, qnJ, ptJ, bB + 1#32, ⟨⟩) mJ) :
    wp Γ Q X (applyLoop4InnerExpr cx sym s.cur_rm s.cur_rl s.cur_rh s.cur_rp s.cur_nr n0
      s.bx nb slB slR (s.pool.getD s.pc.toNat 0#64) (s.tm.getD s.tc.toNat 0#64)
      (s.tl.getD s.tc.toNat 0#64) (s.th.getD s.tc.toNat 0#64) s.ptop
      JB qnB bB ti mOffBv ptB cl ch) mB := by
  dsimp only [applyLoop4InnerExpr, applyLoop4Expr, applyAfterLoop3Expr, applyLoop3Expr,
    applyAfterLoop2Expr, applyLoop2Expr, applyLoop1ExitExpr, applyLoop1Expr]
  c0_hsteps_nogrp
  let dstPool := if s.pc.toNat = 0 then pool0_1 else pool1_1
  let dstTm := if s.tc.toNat = 0 then tm0_1 else tm1_1
  let srcTs := if s.tc.toNat = 0 then ts0 else ts1
  let srcTl := if s.tc.toNat = 0 then tl0 else tl1
  let srcTh := if s.tc.toNat = 0 then th0 else th1
  let rest4 := array (t := i32) (s.tm.getD s.tc.toNat 0#64) dstTm ⋆
    array64 (s.ts.getD s.tc.toNat 0#64) srcTs ⋆ array64 (s.tl.getD s.tc.toNat 0#64) srcTl ⋆
    array64 (s.th.getD s.tc.toNat 0#64) srcTh ⋆ array (t := i32) s.bx bx ⋆
    array (t := i32) s.vq_off vqOff' ⋆ array (t := i32) s.vq vq' ⋆
    array (t := i8) s.vq_skip vqSkip' ⋆ restTQ
  let Rloop4 := array (t := i32) s.partner partnerArr ⋆ array (t := i32) s.cur_rm curRm ⋆
    array64 s.cur_rl curRl ⋆ array64 s.cur_rh curRh ⋆ array (t := i32) s.cur_rp curRp ⋆
    rest4 ⋆ R
  have hnr_eq : s.cur_nr = s0.cur_nr := by conv => lhs; rw [hCtx0.hs1]
  have hnout_eq : s.n_out = s0.n_out := by conv => lhs; rw [hCtx0.hs1]
  obtain ⟨_, hqnB_le, hspt_le, hptB_le, poolB, qmB, qsB, qlB, qhB,
    hlB1, hlB2, hlB3, hlB4, hlB5, hpreB, hSlB, hSoB, hSiB, hWB, hSyB, hEvB, hmB⟩ := hOuterInv
  refine wp_loop_group (fun remR ⟨rI, qnI, ptI, ⟨⟩⟩ mI =>
      remR = s.cur_nr.toNat - rI.toNat ∧
      ApplyInnerInv cx sym s pool0_1 pool1_1 qm qs ql qh curRm curRl curRh curRp
        Valid Rloop4 qnB.toNat ptB.toNat mOffBv.toNat cl ch poolB qmB qlB qhB qnI ptI rI mI)
    ?_ ?_
  · rintro JI remR ⟨rI, qnI, ptI, ⟨⟩⟩ mI hrecI ⟨hremR, hInvI⟩
    c0_hsteps_nogrp
    · have hr_lt : rI.toNat < s.cur_nr.toNat := hc; clear hc
      obtain ⟨_, hqnI_ge, hqnI_le, hptI_ge, hptI_le, poolI, qmI, qsI, qlI, qhI,
        hlI1, hlI2, hlI3, hlI4, hlI5, hpreI, hSlI, hSoI, hSiI, hWI, hSyI, hEvI, hmI⟩ := hInvI
      have hInvI' : ApplyInnerInv cx sym s pool0_1 pool1_1 qm qs ql qh curRm curRl curRh curRp
          Valid Rloop4 qnB.toNat ptB.toNat mOffBv.toNat cl ch poolB qmB qlB qhB qnI ptI rI mI :=
        ⟨by omega, hqnI_ge, hqnI_le, hptI_ge, hptI_le, poolI, qmI, qsI, qlI, qhI,
          hlI1, hlI2, hlI3, hlI4, hlI5, hpreI, hSlI, hSoI, hSiI, hWI, hSyI, hEvI, hmI⟩
      have hr_nr0 : rI.toNat < s0.cur_nr.toNat := by rw [← hnr_eq]; exact hr_lt
      have hr_skip : rI.toNat < vqSkip'.length :=
        Nat.lt_of_lt_of_le hr_nr0 (le_trans (le_trans (Nat.le_mul_of_pos_left _ hCtx0.hnb_pos)
          hCtx0.hnb_nr_q) (le_trans (by omega) hCtx0.hvqSkip_len))
      refine wp_join_group (fun ⟨qnJ, ptJ, ⟨⟩⟩ mJ =>
          ApplyInnerInv cx sym s pool0_1 pool1_1 qm qs ql qh curRm curRl curRh curRp
            Valid Rloop4 qnB.toNat ptB.toNat mOffBv.toNat cl ch poolB qmB qlB qhB
            qnJ ptJ (rI + 1#32) mJ)
        ?_ ?_
      · rintro JJ ⟨qnJ, ptJ, ⟨⟩⟩ mJ hInvJ
        c0_hsteps_nogrp
        have hrp1 : (rI + 1#32).toNat = rI.toNat + 1 := apply_bv32_add1_lt hr_lt s.cur_nr.isLt
        exact hrecI (s.cur_nr.toNat - (rI + 1#32).toNat) (rI + 1#32, qnJ, ptJ, ⟨⟩) mJ
          (by omega) ⟨rfl, hInvJ⟩
      · intro JJ hJJ
        c0_hsteps_nogrp
        apply wp_load_arr8_u32 (base := s.vq_skip) (xs := vqSkip') (i := rI)
          (R := arCtxMem cx s ⋆ array (t := i32) (s.pool.getD s.pc.toNat 0#64) poolI ⋆
            array (t := i32) s.qm qmI ⋆ array64 s.qs qsI ⋆ array64 s.ql qlI ⋆ array64 s.qh qhI ⋆
            array (t := i32) s.partner partnerArr ⋆ array (t := i32) s.cur_rm curRm ⋆
            array64 s.cur_rl curRl ⋆ array64 s.cur_rh curRh ⋆ array (t := i32) s.cur_rp curRp ⋆
            array (t := i32) (s.tm.getD s.tc.toNat 0#64) dstTm ⋆
            array64 (s.ts.getD s.tc.toNat 0#64) srcTs ⋆ array64 (s.tl.getD s.tc.toNat 0#64) srcTl ⋆
            array64 (s.th.getD s.tc.toNat 0#64) srcTh ⋆ array (t := i32) s.bx bx ⋆
            array (t := i32) s.vq_off vqOff' ⋆ array (t := i32) s.vq vq' ⋆ restTQ ⋆ R)
          (hi := hr_skip) (hm := sep_cast hmI (by dsimp only [Rloop4, rest4]; ac_rfl))
        · rfl
        c0_hsteps_nogrp
        · let skBv := vqSkip'[rI.toNat]'hr_skip
          have hsk0 : skBv = 0#8 := by dsimp only [skBv]; c0_bv_omega
          clear hc
          have hsk0_d : vqSkip'.getD rI.toNat 0#8 = 0#8 := by
            dsimp only [skBv] at hsk0; rwa [getD_eq_getElem vqSkip' 0#8 hr_skip]
          have hr_rl : rI.toNat < curRl.length := Nat.lt_of_lt_of_le hr_nr0 hCtx0.hcurNr_rl
          have hr_rh : rI.toNat < curRh.length := Nat.lt_of_lt_of_le hr_nr0 hCtx0.hcurNr_rh
          refine wp_load_arr64_idx (i := rI) (base := s.cur_rl) (xs := curRl)
            (R := arCtxMem cx s ⋆ array (t := i32) (s.pool.getD s.pc.toNat 0#64) poolI ⋆
              array (t := i32) s.qm qmI ⋆ array64 s.qs qsI ⋆ array64 s.ql qlI ⋆ array64 s.qh qhI ⋆
              array (t := i32) s.partner partnerArr ⋆ array (t := i32) s.cur_rm curRm ⋆
              array64 s.cur_rh curRh ⋆ array (t := i32) s.cur_rp curRp ⋆ rest4 ⋆ R)
            rfl hr_rl (sep_cast hmI (by dsimp only [Rloop4, rest4]; ac_rfl)) ?_
          c0_hsteps_nogrp
          refine wp_load_arr64_idx (i := rI) (base := s.cur_rh) (xs := curRh)
            (R := arCtxMem cx s ⋆ array (t := i32) (s.pool.getD s.pc.toNat 0#64) poolI ⋆
              array (t := i32) s.qm qmI ⋆ array64 s.qs qsI ⋆ array64 s.ql qlI ⋆ array64 s.qh qhI ⋆
              array (t := i32) s.partner partnerArr ⋆ array (t := i32) s.cur_rm curRm ⋆
              array64 s.cur_rl curRl ⋆ array (t := i32) s.cur_rp curRp ⋆ rest4 ⋆ R)
            rfl hr_rh (sep_cast hmI (by dsimp only [Rloop4, rest4]; ac_rfl)) ?_
          c0_hsteps_nogrp
          let rlBv := curRl[rI.toNat]'hr_rl
          let rhBv := curRh[rI.toNat]'hr_rh
          have hrl_eq : rlBv = curRl.getD rI.toNat 0#64 := (getD_eq_getElem curRl 0#64 hr_rl).symm
          have hrh_eq : rhBv = curRh.getD rI.toNat 0#64 := (getD_eq_getElem curRh 0#64 hr_rh).symm
          refine wp_call_of_spec _ _ (hCmul ⟨cx, cl, ch, rlBv, rhBv, ⟨⟩⟩ mI _ X
            ⟨s, array (t := i32) (s.pool.getD s.pc.toNat 0#64) poolI ⋆
                array (t := i32) s.qm qmI ⋆ array64 s.qs qsI ⋆ array64 s.ql qlI ⋆
                array64 s.qh qhI ⋆ Rloop4,
              (by have hmk := hCtx0.hMasks
                  rw [show s.n_out = s0.n_out by conv => lhs; rw [hCtx0.hs1],
                    show s.mlo = s0.mlo by conv => lhs; rw [hCtx0.hs1],
                    show s.mhi = s0.mhi by conv => lhs; rw [hCtx0.hs1]]
                  exact hmk),
              sep_cast hmI (by ac_rfl), fun l h hcmul => ?_⟩)
          c0_hsteps_nogrp
          refine wp_join_group (fun ⟨qnJ, ptJ, ⟨⟩⟩ mJ =>
              ApplyInnerInv cx sym s pool0_1 pool1_1 qm qs ql qh curRm curRl curRh curRp
                Valid Rloop4 qnB.toNat ptB.toNat mOffBv.toNat cl ch poolB qmB qlB qhB
                qnJ ptJ (rI + 1#32) mJ)
            ?_ ?_
          · rintro Js ⟨qnJ, ptJ, ⟨⟩⟩ mJ hInvJ
            c0_hsteps_nogrp
            exact hJJ (qnJ, ptJ, ⟨⟩) mJ hInvJ
          · intro Js hJs
            c0_hsteps_nogrp
            exact apply_je_wp (n0 := n0) (JB := JB) (ti := ti) (Q := Q) (X := X) Γ hMhas hMun
              hFoc0 hCtx0 hb_lt hr_lt hqnB_le hspt_le hptB_le hmSl_eq hmSo_eq hmOff_eq hbxM0
              hsk0_d hrl_eq hrh_eq hcmul hInvI' hJs
        · have hsk_ne : vqSkip'[rI.toNat]'hr_skip ≠ 0#8 := by c0_bv_omega
          have hsk_nz : vqSkip'.getD rI.toNat 0#8 ≠ 0#8 := by
            rw [getD_eq_getElem vqSkip' 0#8 hr_skip]; exact hsk_ne
          have hvan_r := (hCtx0.hVqOk rI.toNat hr_nr0).1 hsk_nz
          c0_hsteps_nogrp
          exact hJJ (qnI, ptI, ⟨⟩) mI (apply_inner_skip_step hr_lt (fun σ hV => by
            dsimp only [termEval]; rw [hvan_r σ hV]; simp) hInvI')
    · dsimp only [ApplyInnerInv] at hInvI
      have hr_done : rI.toNat = s.cur_nr.toNat := by
        have := hInvI.1; c0_bv_omega
      obtain rfl : rI = s.cur_nr := BitVec.eq_of_toNat_eq hr_done
      c0_hsteps_nogrp
      exact hJB qnI ptI mI (apply_inner_row_done hb_lt hspt_le hqnB_le hptB_le
        hEvB hmOff_eq hcl_eq hch_eq hbxM0
        (by rw [show s.tn = s0.tn by conv => lhs; rw [hCtx0.hs1]]
            exact hCtx0.hinc.1 bB.toNat hb_lt)
        hSyB (by rw [hnout_eq, hnr_eq]; exact hCtx0.hCurR) hInvI)
  · intro JI hJI
    c0_hsteps_nogrp
    refine hJI s.cur_nr.toNat (0#32, qnB, ptB, ⟨⟩) mB ⟨rfl, ?_⟩
    dsimp only [ApplyInnerInv]
    exact ⟨Nat.zero_le _, le_refl _, by simp, le_refl _, by simp,
      poolB, qmB, qsB, qlB, qhB, hlB1, hlB2, hlB3, hlB4, hlB5,
      hpreB, hSlB, hSoB, hSiB, hWB, (fun _ _ _ h => h), fun σ hV => by simp [hEvB σ hV], hmB⟩

theorem apply_outer_loop_wp (Γ : T.Env)
    (hMhas : ∀ xs m Q X, arMhasFromSpec xs m Q X →
      Γ "ar_mhas_from" [i64, i32, i32] [.bool] xs m Q X)
    (hMun : ∀ xs m Q X, arMunionSpec xs m Q X →
      Γ "ar_munion" [i64, i64, i32, i64] [i64] xs m Q X)
    (hCmul : ∀ xs m Q X, arCmulSpec xs m Q X →
      Γ "ar_cmul" [i64, i64, i64, i64, i64] [i64, i64] xs m Q X)
    (hMerge : ∀ xs m Q X, arMergeProductsSpec xs m Q X →
      Γ "ar_merge_products" [i64, i32] [] xs m Q X)
    {cx : BitVec 64} {sym : BitVec 32} {s0 s : ArCtxState}
    {tm0 tm1 pool0 pool1 : List (BitVec 32)} {ts0 tl0 th0 ts1 tl1 th1 : List (BitVec 64)}
    {tm0_1 tm1_1 pool0_1 pool1_1 qm : List (BitVec 32)} {qs ql qh : List (BitVec 64)}
    {ix ix2 bx vqOff' vq' : List (BitVec 32)} {vqSkip' : List (BitVec 8)}
    {partnerArr curRm : List (BitVec 32)} {curRl curRh : List (BitVec 64)}
    {curRp : List (BitVec 32)} {Valid : (Nat → Bool) → Prop} {R restTQ : Mem 64 → Prop}
    {nb : BitVec 32} {slB slR : BitVec 64} {qFin : Nat} {m0 : Mem 64}
    {Q : Post [.bool]} {X : XPost}
    (hFoc0 : tMem s tm0_1 tm1_1 ts0 tl0 th0 ts1 tl1 th1 pool0_1 pool1_1 ⋆
        qMem s qm qs ql qh ix ix2 bx vqOff' vq' vqSkip' =
      (array (t := i32) (s.pool.getD s.pc.toNat 0#64)
        (if s.pc.toNat = 0 then pool0_1 else pool1_1) ⋆
       array (t := i32) (s.tm.getD s.tc.toNat 0#64) (if s.tc.toNat = 0 then tm0_1 else tm1_1) ⋆
       array64 (s.ts.getD s.tc.toNat 0#64) (if s.tc.toNat = 0 then ts0 else ts1) ⋆
       array64 (s.tl.getD s.tc.toNat 0#64) (if s.tc.toNat = 0 then tl0 else tl1) ⋆
       array64 (s.th.getD s.tc.toNat 0#64) (if s.tc.toNat = 0 then th0 else th1) ⋆
       array (t := i32) s.qm qm ⋆ array64 s.qs qs ⋆ array64 s.ql ql ⋆ array64 s.qh qh ⋆
       array (t := i32) s.bx bx ⋆ array (t := i32) s.vq_off vqOff' ⋆
       array (t := i32) s.vq vq' ⋆ array (t := i8) s.vq_skip vqSkip' ⋆ restTQ))
    (hCtx0 : ApplyLoopCtx cx sym s0 s tm0 tm1 pool0 pool1 ts0 tl0 th0 ts1 tl1 th1
      tm0_1 tm1_1 pool0_1 pool1_1 qm qs ql qh ix ix2 bx vqOff' vq' vqSkip'
      partnerArr curRm curRl curRh curRp Valid R
      (array (t := i32) (s.tm.getD s.tc.toNat 0#64) (if s.tc.toNat = 0 then tm0_1 else tm1_1) ⋆
       array64 (s.ts.getD s.tc.toNat 0#64) (if s.tc.toNat = 0 then ts0 else ts1) ⋆
       array64 (s.tl.getD s.tc.toNat 0#64) (if s.tc.toNat = 0 then tl0 else tl1) ⋆
       array64 (s.th.getD s.tc.toNat 0#64) (if s.tc.toNat = 0 then th0 else th1) ⋆
       array (t := i32) s.bx bx ⋆ array (t := i32) s.vq_off vqOff' ⋆
       array (t := i32) s.vq vq' ⋆ array (t := i8) s.vq_skip vqSkip' ⋆ restTQ)
      nb slB slR qFin)
    (hm0 : (arCtxMem cx s ⋆ array (t := i32) s.partner partnerArr ⋆
      array (t := i32) s.cur_rm curRm ⋆ array64 s.cur_rl curRl ⋆ array64 s.cur_rh curRh ⋆
      array (t := i32) s.cur_rp curRp ⋆
      tMem s tm0_1 tm1_1 ts0 tl0 th0 ts1 tl1 th1 pool0_1 pool1_1 ⋆
      qMem s qm qs ql qh ix ix2 bx vqOff' vq' vqSkip' ⋆ R) m0)
    (hOk : ∀ (s' : ArCtxState) (tm0' tm1' : List (BitVec 32))
        (ts0' tl0' th0' ts1' tl1' th1' : List (BitVec 64))
        (pool0' pool1' qm' : List (BitVec 32)) (qs' ql' qh' : List (BitVec 64))
        (ix' ix2' bx' vqOff'' vq'' : List (BitVec 32)) (vqSkip'' : List (BitVec 8))
        (m' : Mem 64),
      let srcPool0 := if s0.pc.toNat = 0 then pool0 else pool1
      let srcTm0 := if s0.tc.toNat = 0 then tm0 else tm1
      let srcTl0 := if s0.tc.toNat = 0 then tl0 else tl1
      let srcTh0 := if s0.tc.toNat = 0 then th0 else th1
      let dstPool := if s'.pc.toNat = 0 then pool0' else pool1'
      let dstTm := if s'.tc.toNat = 0 then tm0' else tm1'
      let dstTs := if s'.tc.toNat = 0 then ts0' else ts1'
      let dstTl := if s'.tc.toNat = 0 then tl0' else tl1'
      let dstTh := if s'.tc.toNat = 0 then th0' else th1'
      s'.pc.toNat < 2 → s'.tc.toNat < 2 →
      s'.ptop.toNat ≤ s0.pcap.toNat → s'.tn.toNat ≤ s0.tcap.toNat →
      s' = { s0 with
        tc := s'.tc, tn := s'.tn, pc := s'.pc, ptop := s'.ptop,
        qn := s'.qn, ix := s'.ix, ix2 := s'.ix2 } →
      tm0'.length = tm0.length → tm1'.length = tm1.length →
      ts0'.length = ts0.length → tl0'.length = tl0.length → th0'.length = th0.length →
      ts1'.length = ts1.length → tl1'.length = tl1.length → th1'.length = th1.length →
      pool0'.length = pool0.length → pool1'.length = pool1.length →
      qm'.length = qm.length → qs'.length = qs.length →
      ql'.length = ql.length → qh'.length = qh.length →
      ((s'.ix = s0.ix ∧ s'.ix2 = s0.ix2 ∧
        ix'.length = ix.length ∧ ix2'.length = ix2.length) ∨
       (s'.ix = s0.ix2 ∧ s'.ix2 = s0.ix ∧
        ix'.length = ix2.length ∧ ix2'.length = ix.length)) →
      bx'.length = bx.length → vqOff''.length = vqOff'.length →
      vq''.length = vq'.length → vqSkip''.length = vqSkip'.length →
      (∀ i < s'.tn.toNat,
        MonoSliceOk dstPool (dstTm.getD i 0#32).toNat s'.ptop.toNat ∧
        (dstPool.getD (dstTm.getD i 0#32).toNat 0#32).toNat + 1 < 2 ^ 32) →
      (∀ i < s'.tn.toNat, MonoSorted dstPool (dstTm.getD i 0#32).toNat) →
      SigOk dstPool dstTm dstTs s'.tn.toNat →
      monoTotalWords dstPool dstTm s'.tn.toNat ≤ s'.ptop.toNat →
      (∀ bd : Nat, SymsBound srcPool0 srcTm0 s0.tn.toNat bd →
        SymsBound curRp curRm s0.cur_nr.toNat bd →
        SymsBound dstPool dstTm s'.tn.toNat bd) →
      (∀ σ, Valid σ →
        polyEval s0.n_out.toNat σ dstPool dstTm dstTl dstTh s'.tn.toNat =
          polyEval s0.n_out.toNat σ srcPool0 srcTm0 srcTl0 srcTh0 s0.tn.toNat) →
      (arCtxMem cx s' ⋆ array (t := i32) s'.partner partnerArr ⋆
        array (t := i32) s'.cur_rm curRm ⋆ array64 s'.cur_rl curRl ⋆
        array64 s'.cur_rh curRh ⋆ array (t := i32) s'.cur_rp curRp ⋆
        tMem s' tm0' tm1' ts0' tl0' th0' ts1' tl1' th1' pool0' pool1' ⋆
        qMem s' qm' qs' ql' qh' ix' ix2' bx' vqOff'' vq'' vqSkip'' ⋆ R) m' →
      Q (true, ⟨⟩) m') :
    wp Γ Q X (applyLoop4Expr cx sym s.cur_rm s.cur_rl s.cur_rh s.cur_rp s.cur_nr s.tn
      s.bx nb slB slR (s.pool.getD s.pc.toNat 0#64) (s.tm.getD s.tc.toNat 0#64)
      (s.tl.getD s.tc.toNat 0#64) (s.th.getD s.tc.toNat 0#64) s.ptop) m0 := by
  dsimp only [applyLoop4Expr, applyAfterLoop3Expr, applyLoop3Expr, applyAfterLoop2Expr,
    applyLoop2Expr, applyLoop1ExitExpr, applyLoop1Expr]
  let dstPool := if s.pc.toNat = 0 then pool0_1 else pool1_1
  let dstTm := if s.tc.toNat = 0 then tm0_1 else tm1_1
  let srcTs := if s.tc.toNat = 0 then ts0 else ts1
  let srcTl := if s.tc.toNat = 0 then tl0 else tl1
  let srcTh := if s.tc.toNat = 0 then th0 else th1
  have hdstPool_len : s0.pcap.toNat ≤ dstPool.length := by
    dsimp only [dstPool]; split; exact hCtx0.hp0_len; exact hCtx0.hp1_len
  have hdstTm_len : s0.tcap.toNat ≤ dstTm.length := by
    dsimp only [dstTm]; split; exact hCtx0.htm0_len; exact hCtx0.htm1_len
  have hsrcTl_len : s0.tcap.toNat ≤ srcTl.length := by
    dsimp only [srcTl]; split; exact hCtx0.htl0_len; exact hCtx0.htl1_len
  have hsrcTh_len : s0.tcap.toNat ≤ srcTh.length := by
    dsimp only [srcTh]; split; exact hCtx0.hth0_len; exact hCtx0.hth1_len
  let rest4 := array (t := i32) (s.tm.getD s.tc.toNat 0#64) dstTm ⋆
    array64 (s.ts.getD s.tc.toNat 0#64) srcTs ⋆ array64 (s.tl.getD s.tc.toNat 0#64) srcTl ⋆
    array64 (s.th.getD s.tc.toNat 0#64) srcTh ⋆ array (t := i32) s.bx bx ⋆
    array (t := i32) s.vq_off vqOff' ⋆ array (t := i32) s.vq vq' ⋆
    array (t := i8) s.vq_skip vqSkip' ⋆ restTQ
  let Rloop4 := array (t := i32) s.partner partnerArr ⋆ array (t := i32) s.cur_rm curRm ⋆
    array64 s.cur_rl curRl ⋆ array64 s.cur_rh curRh ⋆ array (t := i32) s.cur_rp curRp ⋆
    rest4 ⋆ R
  have hm0_foc : (arCtxMem cx s ⋆ array (t := i32) (s.pool.getD s.pc.toNat 0#64) dstPool ⋆
      array (t := i32) s.qm qm ⋆ array64 s.qs qs ⋆ array64 s.ql ql ⋆ array64 s.qh qh ⋆
      Rloop4) m0 := by
    have hm' : ((tMem s tm0_1 tm1_1 ts0 tl0 th0 ts1 tl1 th1 pool0_1 pool1_1 ⋆
        qMem s qm qs ql qh ix ix2 bx vqOff' vq' vqSkip') ⋆
        (arCtxMem cx s ⋆ array (t := i32) s.partner partnerArr ⋆
          array (t := i32) s.cur_rm curRm ⋆ array64 s.cur_rl curRl ⋆
          array64 s.cur_rh curRh ⋆ array (t := i32) s.cur_rp curRp ⋆ R)) m0 :=
      sep_cast hm0 (by ac_rfl)
    rw [hFoc0] at hm'
    dsimp only [Rloop4, rest4]; exact sep_cast hm' (by ac_rfl)
  c0_hsteps_nogrp
  refine wp_loop_group (fun remB ⟨_rB, qnB, ptB, bB, ⟨⟩⟩ mB =>
      remB = nb.toNat - bB.toNat ∧
      ApplyOuterInv cx s tm0_1 tm1_1 pool0_1 pool1_1 tl0 th0 tl1 th1 qm qs ql qh bx curRm curRp
        nb Valid Rloop4 qnB ptB bB mB) ?_ ?_
  · rintro JB remB ⟨_rB, qnB, ptB, bB, ⟨⟩⟩ mB hrecB ⟨hremB, hInvB⟩
    have hInvB' : ApplyOuterInv cx s tm0_1 tm1_1 pool0_1 pool1_1 tl0 th0 tl1 th1 qm qs ql qh
        bx curRm curRp nb Valid Rloop4 qnB ptB bB mB := hInvB
    dsimp only [ApplyOuterInv] at hInvB
    obtain ⟨hb_le, hqnB_le, hspt_le, hptB_le, poolB, qmB, qsB, qlB, qhB,
      hlB1, hlB2, hlB3, hlB4, hlB5, hpreB, hSlB, hSoB, hSiB, hWB, hSyB, hEvB, hmB⟩ := hInvB
    c0_hsteps_nogrp
    · have hb_lt : bB.toNat < nb.toNat := hc; clear hc
      have hbx_idx : bB.toNat < bx.length := Nat.lt_of_lt_of_le hb_lt hCtx0.hnb_bx
      refine wp_load_arr32_idx (off := 0) (i := bB) (base := s.bx) (xs := bx)
        (R := arCtxMem cx s ⋆ array (t := i32) (s.pool.getD s.pc.toNat 0#64) poolB ⋆
          array (t := i32) s.qm qmB ⋆ array64 s.qs qsB ⋆ array64 s.ql qlB ⋆ array64 s.qh qhB ⋆
          array (t := i32) s.partner partnerArr ⋆ array (t := i32) s.cur_rm curRm ⋆
          array64 s.cur_rl curRl ⋆ array64 s.cur_rh curRh ⋆ array (t := i32) s.cur_rp curRp ⋆
          array (t := i32) (s.tm.getD s.tc.toNat 0#64) dstTm ⋆
          array64 (s.ts.getD s.tc.toNat 0#64) srcTs ⋆ array64 (s.tl.getD s.tc.toNat 0#64) srcTl ⋆
          array64 (s.th.getD s.tc.toNat 0#64) srcTh ⋆ array (t := i32) s.vq_off vqOff' ⋆
          array (t := i32) s.vq vq' ⋆ array (t := i8) s.vq_skip vqSkip' ⋆ restTQ ⋆ R)
        (by simp) (by simpa using hbx_idx)
        (sep_cast hmB (by dsimp only [Rloop4, rest4]; ac_rfl)) ?_
      c0_hsteps_nogrp
      let ti := bx[0 + bB.toNat]'(by simpa using hbx_idx)
      have hti_eq : ti.toNat = (bx.getD bB.toNat 0#32).toNat := by
        dsimp only [ti]; simp only [Nat.zero_add]; rw [getD_eq_getElem bx 0#32 hbx_idx]
      have hti_tn : ti.toNat < s0.tn.toNat := by rw [hti_eq]; exact hCtx0.hinc.1 bB.toNat hb_lt
      have hti_tm : ti.toNat < dstTm.length :=
        Nat.lt_of_lt_of_le hti_tn (le_trans hCtx0.htn hdstTm_len)
      have hti_tl : ti.toNat < srcTl.length :=
        Nat.lt_of_lt_of_le hti_tn (le_trans hCtx0.htn hsrcTl_len)
      have hti_th : ti.toNat < srcTh.length :=
        Nat.lt_of_lt_of_le hti_tn (le_trans hCtx0.htn hsrcTh_len)
      refine wp_load_arr32_idx (off := 0) (i := ti) (base := s.tm.getD s.tc.toNat 0#64)
        (xs := dstTm)
        (R := arCtxMem cx s ⋆ array (t := i32) (s.pool.getD s.pc.toNat 0#64) poolB ⋆
          array (t := i32) s.qm qmB ⋆ array64 s.qs qsB ⋆ array64 s.ql qlB ⋆ array64 s.qh qhB ⋆
          array (t := i32) s.partner partnerArr ⋆ array (t := i32) s.cur_rm curRm ⋆
          array64 s.cur_rl curRl ⋆ array64 s.cur_rh curRh ⋆ array (t := i32) s.cur_rp curRp ⋆
          array64 (s.ts.getD s.tc.toNat 0#64) srcTs ⋆ array64 (s.tl.getD s.tc.toNat 0#64) srcTl ⋆
          array64 (s.th.getD s.tc.toNat 0#64) srcTh ⋆ array (t := i32) s.bx bx ⋆
          array (t := i32) s.vq_off vqOff' ⋆ array (t := i32) s.vq vq' ⋆
          array (t := i8) s.vq_skip vqSkip' ⋆ restTQ ⋆ R)
        (by simp [ti]) (by simpa using hti_tm)
        (sep_cast hmB (by dsimp only [Rloop4, rest4]; ac_rfl)) ?_
      c0_hsteps_nogrp
      let mOffBv := dstTm[0 + ti.toNat]'(by simpa using hti_tm)
      have hmOff_eq : mOffBv.toNat = (dstTm.getD (bx.getD bB.toNat 0#32).toNat 0#32).toNat := by
        dsimp only [mOffBv]; simp only [Nat.zero_add]
        rw [← hti_eq, getD_eq_getElem dstTm 0#32 hti_tm]
      have hmSl_eq : MonoSliceOk dstPool mOffBv.toNat s.ptop.toNat ∧
          (dstPool.getD mOffBv.toNat 0#32).toNat + 1 < 2 ^ 32 := by
        dsimp only [dstPool, dstTm, mOffBv]; simp only [Nat.zero_add]
        rw [← getD_eq_getElem (if s.tc.toNat = 0 then tm0_1 else tm1_1) 0#32 hti_tm]
        exact hCtx0.hSl1 ti.toNat hti_tn
      have hmSo_eq : MonoSorted dstPool mOffBv.toNat := by
        dsimp only [dstPool, dstTm, mOffBv]; simp only [Nat.zero_add]
        rw [← getD_eq_getElem (if s.tc.toNat = 0 then tm0_1 else tm1_1) 0#32 hti_tm]
        exact hCtx0.hSo1 ti.toNat hti_tn
      have hbxM0 : sym.toNat ∈ symListAt dstPool mOffBv.toNat := by
        rw [hmOff_eq]; exact hCtx0.hbxMem bB.toNat hb_lt
      refine wp_load_arr64_idx (i := ti) (base := s.tl.getD s.tc.toNat 0#64) (xs := srcTl)
        (R := arCtxMem cx s ⋆ array (t := i32) (s.pool.getD s.pc.toNat 0#64) poolB ⋆
          array (t := i32) s.qm qmB ⋆ array64 s.qs qsB ⋆ array64 s.ql qlB ⋆ array64 s.qh qhB ⋆
          array (t := i32) s.partner partnerArr ⋆ array (t := i32) s.cur_rm curRm ⋆
          array64 s.cur_rl curRl ⋆ array64 s.cur_rh curRh ⋆ array (t := i32) s.cur_rp curRp ⋆
          array (t := i32) (s.tm.getD s.tc.toNat 0#64) dstTm ⋆
          array64 (s.ts.getD s.tc.toNat 0#64) srcTs ⋆
          array64 (s.th.getD s.tc.toNat 0#64) srcTh ⋆ array (t := i32) s.bx bx ⋆
          array (t := i32) s.vq_off vqOff' ⋆ array (t := i32) s.vq vq' ⋆
          array (t := i8) s.vq_skip vqSkip' ⋆ restTQ ⋆ R)
        ?_ hti_tl (sep_cast hmB (by dsimp only [Rloop4, rest4]; ac_rfl)) ?_
      · simp only [Arg.val, ti, Nat.zero_add]
      c0_hsteps_nogrp
      refine wp_load_arr64_idx (i := ti) (base := s.th.getD s.tc.toNat 0#64) (xs := srcTh)
        (R := arCtxMem cx s ⋆ array (t := i32) (s.pool.getD s.pc.toNat 0#64) poolB ⋆
          array (t := i32) s.qm qmB ⋆ array64 s.qs qsB ⋆ array64 s.ql qlB ⋆ array64 s.qh qhB ⋆
          array (t := i32) s.partner partnerArr ⋆ array (t := i32) s.cur_rm curRm ⋆
          array64 s.cur_rl curRl ⋆ array64 s.cur_rh curRh ⋆ array (t := i32) s.cur_rp curRp ⋆
          array (t := i32) (s.tm.getD s.tc.toNat 0#64) dstTm ⋆
          array64 (s.ts.getD s.tc.toNat 0#64) srcTs ⋆
          array64 (s.tl.getD s.tc.toNat 0#64) srcTl ⋆ array (t := i32) s.bx bx ⋆
          array (t := i32) s.vq_off vqOff' ⋆ array (t := i32) s.vq vq' ⋆
          array (t := i8) s.vq_skip vqSkip' ⋆ restTQ ⋆ R)
        ?_ hti_th (sep_cast hmB (by dsimp only [Rloop4, rest4]; ac_rfl)) ?_
      · simp only [Arg.val, ti, Nat.zero_add]
      c0_hsteps_nogrp
      let cl := srcTl[ti.toNat]'hti_tl
      let ch := srcTh[ti.toNat]'hti_th
      have hcl_eq : cl = srcTl.getD (bx.getD bB.toNat 0#32).toNat 0#64 := by
        dsimp only [cl]; rw [← hti_eq, getD_eq_getElem srcTl 0#64 hti_tl]
      have hch_eq : ch = srcTh.getD (bx.getD bB.toNat 0#32).toNat 0#64 := by
        dsimp only [ch]; rw [← hti_eq, getD_eq_getElem srcTh 0#64 hti_th]
      have hbp1 : (bB + 1#32).toNat = bB.toNat + 1 := apply_bv32_add1_lt hb_lt nb.isLt
      exact apply_inner_loop_wp (n0 := s.tn) (ti := ti) (Q := Q) (X := X) Γ hMhas hMun hCmul
        hFoc0 hCtx0 hb_lt hmSl_eq hmSo_eq hmOff_eq hcl_eq hch_eq hbxM0 hInvB'
          (fun qnJ ptJ mJ hInvJ =>
          hrecB (nb.toNat - (bB + 1#32).toNat) (s.cur_nr, qnJ, ptJ, bB + 1#32, ⟨⟩) mJ
            (by omega) ⟨rfl, hInvJ⟩)
    · have hb_done : bB.toNat = nb.toNat := by c0_bv_omega
      obtain rfl : bB = nb := BitVec.eq_of_toNat_eq hb_done
      c0_hsteps_nogrp
      exact apply_outer_exit_wp Γ hMerge hCtx0 hqnB_le hspt_le hptB_le
        hlB1 hlB2 hlB3 hlB4 hlB5 hpreB hSlB hSoB hSiB hWB hSyB hEvB
        (sep_cast hm (by dsimp only [Rloop4, rest4]; ac_rfl)) hOk
  · intro JB hJB
    c0_hsteps_nogrp
    refine hJB nb.toNat (s.cur_nr, 0#32, s.ptop, 0#32, ⟨⟩) m0 ?_
    dsimp only [ApplyOuterInv]
    exact ⟨by simp, Nat.zero_le _, by simp, le_refl _, by simp,
      dstPool, qm, qs, ql, qh, rfl, rfl, rfl, rfl, rfl,
      fun _ _ => rfl, fun _ h0 => absurd h0 (Nat.not_lt_zero _),
      fun _ h0 => absurd h0 (Nat.not_lt_zero _), sigOk_empty _ _ _,
      by simp [monoTotalWords], fun _ _ _ _ hi => absurd hi (Nat.not_lt_zero _),
      fun _ _ => by simp [polyEval_zero, bxTermSum_zero], hm0_foc⟩

end

end LeanQbe.T.Examples.Arisca.Proof
