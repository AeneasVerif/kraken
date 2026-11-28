/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Arisca.Proof.Driver1Base
import LeanQbe.T.Logic.MemLemmas
import LeanQbe.T.Logic.ControlComb
import LeanQbe.T.Logic.ProofKit
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.C0StepAttr
meta import LeanQbe.T.Logic.C0StepAttr
import Kraken.Separation

/-!
# ARiSCA Gate Validator Helpers & Phases (`Arisca.Proof.Driver1GateBase`)

Shared AST extractors and WP phase lemmas (`ar_do_gate_row_wp`, `ar_do_gate_eval_wp`,
`ar_do_gate_dense_wp`) for `ar_do_gate_wp`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Arisca.Proof

open Std
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.C0HeadStep
open LeanQbe.T.ProofKit
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Arisca (Aig)
open LeanQbe.T.Examples.Arisca.Src
open LeanQbe.T.Examples.Arisca.Src.Driver

@[expose] public section

@[reducible] def fastIgn : Expr Val Cont [.bool] → Expr Val Cont [.bool]
  | @Expr.let_ _ _ _ [.bits 64] _ k => k (0#64, ())
  | @Expr.let_ _ _ _ [.bits 32] _ k => k (0#32, ())
  | @Expr.let_ _ _ _ [.bool] _ k => k (false, ())
  | @Expr.load _ _ _ (.bits 64) _ k => k 0#64
  | @Expr.load _ _ _ (.bits 32) _ k => k 0#32
  | .store _ _ k => k
  | @Expr.call _ _ _ _ _ [] _ k => k ()
  | e => e

@[reducible] def fastToGrp : Nat → Expr Val Cont [.bool] → Expr Val Cont [.bool]
  | 0, e => e
  | _ + 1, e@(.group _ _) => e
  | n + 1, e => fastToGrp n (fastIgn e)

@[reducible] def fastToJnz : Nat → Expr Val Cont [.bool] → Expr Val Cont [.bool]
  | 0, e => e
  | _ + 1, e@(.jnz _ _ _) => e
  | n + 1, e => fastToJnz n (fastIgn e)

def fastEval64 (pD : Val i64) : Nat → Expr Val Cont [.bool] → Expr Val Cont [.bool]
  | 0, e => e
  | _ + 1, e@(.group _ _) => e
  | n + 1, @Expr.load _ _ _ (.bits 64) _ k => fastEval64 pD n (k pD)
  | n + 1, @Expr.let_ _ _ _ [.bits 64] op k =>
    match op with
    | .mk (.add (.bits 64)) (a, b, ()) => fastEval64 pD n (k (a.val + b.val, ()))
    | .mk (.mul (.bits 64)) (a, b, ()) => fastEval64 pD n (k (a.val * b.val, ()))
    | .mk (.shl (.bits 64)) (a, b, ()) => fastEval64 pD n (k (a.val <<< b.val.toNat, ()))
    | .mk (.copy (.bits 64)) (a, ()) => fastEval64 pD n (k (a.val, ()))
    | .mk (.sext 32 64) (a, ()) => fastEval64 pD n (k (BitVec.signExtend 64 a.val, ()))
    | .mk (.zext 32 64) (a, ()) => fastEval64 pD n (k (BitVec.setWidth 64 a.val, ()))
    | _ => fastEval64 pD n (k (0#64, ()))
  | n + 1, e => fastEval64 pD n (fastIgn e)

inductive GateStep
  | jnzT | jnzF | grp0 | grp32 (v : Val i32) | grp64 (v : Val i64) | grpB32 (v : Val i32)

@[reducible] def runFast : List GateStep → Expr Val Cont [.bool] → Expr Val Cont [.bool]
  | [], e => e
  | .jnzT :: ss, e => match fastToJnz 12 e with | .jnz _ t _ => runFast ss t | _ => e
  | .jnzF :: ss, e => match fastToJnz 12 e with | .jnz _ _ f => runFast ss f | _ => e
  | .grp0 :: ss, e => match fastToGrp 12 e with
    | .group (sig := [[]]) b _ => runFast ss (Blocks.get (b ((fun _ _ => False), ())) .here ())
    | _ => e
  | .grp32 v :: ss, e => match fastToGrp 12 e with
    | .group (sig := [[.bits 32]]) b _ =>
      runFast ss (Blocks.get (b ((fun _ _ => False), ())) .here (v, ()))
    | _ => e
  | .grp64 v :: ss, e => match fastToGrp 12 e with
    | .group (sig := [[.bits 64]]) b _ =>
      runFast ss (Blocks.get (b ((fun _ _ => False), ())) .here (v, ()))
    | _ => e
  | .grpB32 v :: ss, e => match fastToGrp 12 e with
    | .group (sig := [[.bool, .bits 32]]) b _ =>
      runFast ss (Blocks.get (b ((fun _ _ => False), ())) .here (false, v, ()))
    | _ => e

@[reducible] def gateDenseExpr (cx : Val i64) (kraw nout nin nl : Val i32)
    (j0 : Val i32 := 0#32) : Expr Val Cont [.bool] :=
  match ar_do_gate_body Val Cont (cx, ()) with
  | @Expr.call _ _ _ _ _ [.bool, .bits 32] _ k1 =>
    match k1 (true, kraw, ()) with
    | .jnz _ (@Expr.let_ _ _ _ [.bits 32] (.mk (.and (.bits 32)) (ka, kb, ())) kkind) _ =>
      runFast [.jnzF, .jnzF, .jnzF, .grp32 nout, .grp32 nin,
        .grpB32 0#32, .jnzF, .grp0, .grpB32 0#32, .jnzF, .grpB32 nl, .grp64 0#64,
        .grpB32 0#32, .jnzF, .grpB32 0#32, .jnzF, .grp0, .grpB32 j0, .jnzF]
        (kkind (ka.val &&& kb.val, ()))
    | _ => .ret (Arg.imm false, ())
  | _ => .ret (Arg.imm false, ())

def gateEvalExpr (cx pD : Val i64) (kraw nout nin nl : Val i32)
    (j0 : Val i32 := 0#32) : Expr Val Cont [.bool] :=
  match fastEval64 pD 40 (gateDenseExpr cx kraw nout nin nl j0) with
  | .group (sig := [[]]) b1 _ =>
    match fastToGrp 15 (Blocks.get (b1 ((fun _ _ => False), ())) .here ()) with
    | .group (sig := [[]]) b2 _ => Blocks.get (b2 ((fun _ _ => False), ())) .here ()
    | _ => .ret (Arg.imm false, ())
  | _ => .ret (Arg.imm false, ())

def gateRowExpr (cx pD : Val i64) (kraw nout nin nl j0 o t n : Val i32)
    (Jt : Cont [i32, i32]) : Expr Val Cont [.bool] :=
  match fastToGrp 10 (gateEvalExpr cx pD kraw nout nin nl) with
  | .group (sig := [[.bits 32, .bits 32]]) bO _ =>
    match fastToJnz 10 (Blocks.get (bO ((fun _ _ => False), ())) .here (j0, o, ())) with
    | .jnz _ (.group (sig := [[.bits 64]]) bSel _) _ =>
      let p := if o = 0#32 then pD + 768#64 else pD + 896#64
      let eCan := match Blocks.get (bSel ((fun _ _ => False), ())) .here (p, ()) with
        | .call (bs := [.bits 32]) _ _ kCan => kCan (n, ())
        | e => e
      match fastToGrp 10 eCan with
      | .group (sig := [[.bits 32, .bits 32]]) bT _ =>
        match fastToJnz 10 (Blocks.get (bT (Jt, ())) .here (j0, t, ())) with
        | .jnz _ eI _ => eI
        | _ => .ret (Arg.imm false, ())
      | _ => .ret (Arg.imm false, ())
    | _ => .ret (Arg.imm false, ())
  | _ => .ret (Arg.imm false, ())

def GateSame (s s' : ArCtxState) : Prop :=
  s' = { s with
    pos := s'.pos, rs_n := s'.rs_n, rs_ptop := s'.rs_ptop,
    g_lmask := s'.g_lmask, g_tin := s'.g_tin, g_tto := s'.g_tto,
    g_outs := s'.g_outs, g_innet := s'.g_innet, g_inneg := s'.g_inneg,
    g_lnode := s'.g_lnode, g_vs := s'.g_vs }

def GateRowOk (g : Aig) (bindArr : List (BitVec 32)) (nin nout : BitVec 32)
    (s : ArCtxState) (ρ : Nat → Bool) (t : Nat) : Prop :=
  (∀ j < nin.toNat, (s.g_tin.getD j 0#64).toNat.testBit t =
    cSig g ρ bindArr (2 * (s.g_innet.getD j 0#32).toNat)) ∧
  (∀ q < nout.toNat, (s.g_tto.getD q 0#64).toNat.testBit t =
    cSig g ρ bindArr (2 * (s.g_outs.getD q 0#32).toNat))

end

public section

private theorem arCtxMem_ok {cx : BitVec 64} {s : ArCtxState} {R : Mem 64 → Prop} {m : Mem 64}
    (h : (arCtxMem cx s ⋆ R) m) : ArCtxLengthsOk s :=
  (sep_pure_l.mp h).1

private theorem dense_dlit {Γ : LeanQbe.T.Env}
    (hDlit : ∀ xs m Q X, arDlitSpec xs m Q X → Γ "ar_dlit" [i64, i32, i32] [] xs m Q X)
    {pa : Arg Val i64} {ja na : Arg Val i32} {d : List (BitVec 64)} (F : Mem 64 → Prop)
    {rs : List Ty} {Q : Post rs} {X : XPost} {k : Tup Val [] → Expr Val Cont rs} {m : Mem 64}
    (hj : ja.val.toNat < 4) (hd : d.length = 16) (hm : (array64 pa.val d ⋆ F) m)
    (hk : ∀ d' m', d'.length = 16 → (array64 pa.val d' ⋆ F) m' → wp Γ Q X (k ()) m') :
    wp Γ Q X (.call (as := [i64, i32, i32]) (bs := []) "ar_dlit" (pa, ja, na, ()) k) m :=
  gate_dlit_step hDlit rfl rfl rfl hj hd hm hk

private theorem dense_dzero {Γ : LeanQbe.T.Env}
    (hDzero : ∀ xs m Q X, arDzeroSpec xs m Q X → Γ "ar_dzero" [i64] [] xs m Q X)
    {pa : Arg Val i64} {d : List (BitVec 64)} (F : Mem 64 → Prop)
    {rs : List Ty} {Q : Post rs} {X : XPost} {k : Tup Val [] → Expr Val Cont rs} {m : Mem 64}
    (hd : d.length = 16) (hm : (array64 pa.val d ⋆ F) m)
    (hk : ∀ d' m', d'.length = 16 → (array64 pa.val d' ⋆ F) m' → wp Γ Q X (k ()) m') :
    wp Γ Q X (.call (as := [i64]) (bs := []) "ar_dzero" (pa, ()) k) m :=
  gate_dzero_step hDzero rfl hd hm hk

private theorem dense_dmul {Γ : LeanQbe.T.Env}
    (hDmul : ∀ xs m Q X, arDmulSpec xs m Q X → Γ "ar_dmul" [i64, i64, i64] [] xs m Q X)
    {aa ba ca : Arg Val i64} {a b c : List (BitVec 64)} (F : Mem 64 → Prop)
    {rs : List Ty} {Q : Post rs} {X : XPost} {k : Tup Val [] → Expr Val Cont rs} {m : Mem 64}
    (ha : a.length = 16) (hb : b.length = 16) (hc : c.length = 16)
    (hm : (array64 aa.val a ⋆ array64 ba.val b ⋆ array64 ca.val c ⋆ F) m)
    (hk : ∀ c' m', c'.length = 16 →
      (array64 aa.val a ⋆ array64 ba.val b ⋆ array64 ca.val c' ⋆ F) m' → wp Γ Q X (k ()) m') :
    wp Γ Q X (.call (as := [i64, i64, i64]) (bs := []) "ar_dmul" (aa, ba, ca, ()) k) m :=
  gate_dmul_step hDmul rfl rfl rfl ha hb hc hm hk

private theorem dense_daxpy {Γ : LeanQbe.T.Env}
    (hDaxpy : ∀ xs m Q X, arDaxpySpec xs m Q X → Γ "ar_daxpy" [i64, i64, i64] [] xs m Q X)
    {ya ka xa : Arg Val i64} {y x : List (BitVec 64)} (F : Mem 64 → Prop)
    {rs : List Ty} {Q : Post rs} {X : XPost} {k : Tup Val [] → Expr Val Cont rs} {m : Mem 64}
    (hy : y.length = 16) (hx : x.length = 16)
    (hm : (array64 ya.val y ⋆ array64 xa.val x ⋆ F) m)
    (hk : ∀ y' m', y'.length = 16 →
      (array64 ya.val y' ⋆ array64 xa.val x ⋆ F) m' → wp Γ Q X (k ()) m') :
    wp Γ Q X (.call (as := [i64, i64, i64]) (bs := []) "ar_daxpy" (ya, ka, xa, ()) k) m :=
  gate_daxpy_step hDaxpy rfl rfl rfl hy hx hm hk

private theorem doff16 :
    BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 16) * 8 = 128#64 := by decide
private theorem doff32 :
    BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 32) * 8 = 256#64 := by decide
private theorem doff48 :
    BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 48) * 8 = 384#64 := by decide
private theorem doff64 :
    BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 64) * 8 = 512#64 := by decide
private theorem doff80 :
    BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 80) * 8 = 640#64 := by decide
private theorem doff96 :
    BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 96) * 8 = 768#64 := by decide
private theorem doff112 :
    BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 112) * 8 = 896#64 := by decide

private theorem dense_inv_last {cx : BitVec 64} {s : ArCtxState} {Rest : Mem 64 → Prop}
    {a0 a1 a2 a3 a4 a5 a6 : List (BitVec 64)}
    (ha0 : a0.length = 16) (ha1 : a1.length = 16) (ha2 : a2.length = 16) (ha3 : a3.length = 16)
    (ha4 : a4.length = 16) (ha5 : a5.length = 16) (ha6 : a6.length = 16)
    {a7 : List (BitVec 64)} {m : Mem 64}
    (hm : (arCtxMem cx s ⋆ array64 s.dense a0 ⋆ array64 (s.dense + 128#64) a1 ⋆
      array64 (s.dense + 256#64) a2 ⋆ array64 (s.dense + 384#64) a3 ⋆
      array64 (s.dense + 512#64) a4 ⋆ array64 (s.dense + 640#64) a5 ⋆
      array64 (s.dense + 768#64) a6 ⋆ array64 (s.dense + 896#64) a7 ⋆ Rest) m)
    (ha7 : a7.length = 16) :
    ∃ x0 x1 x2 x3 x4 x5 x6 x7 : List (BitVec 64),
      x0.length = 16 ∧ x1.length = 16 ∧ x2.length = 16 ∧ x3.length = 16 ∧
      x4.length = 16 ∧ x5.length = 16 ∧ x6.length = 16 ∧ x7.length = 16 ∧
      (arCtxMem cx s ⋆ array64 s.dense x0 ⋆ array64 (s.dense + 128#64) x1 ⋆
        array64 (s.dense + 256#64) x2 ⋆ array64 (s.dense + 384#64) x3 ⋆
        array64 (s.dense + 512#64) x4 ⋆ array64 (s.dense + 640#64) x5 ⋆
        array64 (s.dense + 768#64) x6 ⋆ array64 (s.dense + 896#64) x7 ⋆ Rest) m :=
  ⟨a0, a1, a2, a3, a4, a5, a6, a7, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, hm⟩

private theorem row_shr_and1_ne0 (v : BitVec 64) (t : BitVec 32) (ht : t.toNat < 64) :
    (BitVec.setWidth 32 (v >>> ((BitVec.setWidth 64 t).toNat % 64) &&& 1) ≠ 0#32) ↔
      v.toNat.testBit t.toNat = true := by
  have hvv : v >>> ((BitVec.setWidth 64 t).toNat % 64) = v >>> BitVec.ofNat 64 t.toNat :=
    BitVec.eq_of_toNat_eq (by simp [Nat.mod_eq_of_lt ht])
  rw [hvv, show (1 : BitVec 64) = 1#64 from rfl, gate_bv64_shr_and1_eq v ht]
  cases v.toNat.testBit t.toNat <;> decide

theorem ar_do_gate_row_wp {Γ : LeanQbe.T.Env}
    (hCadd : ∀ xs m Q X, arCaddSpec xs m Q X →
      Γ "ar_cadd" [i64, i64, i64, i64, i64] [i64, i64] xs m Q X)
    {cx : BitVec 64} {kraw nout nin nl j0 o t n : BitVec 32} {s sO : ArCtxState} {g : Aig}
    {bindArr gY1 : List (BitVec 32)} {gL1 gH1 : List (BitVec 64)}
    {F : Mem 64 → Prop} {mC : Mem 64} {Q : Post [.bool]} {X : XPost} {Jt : Cont [i32, i32]}
    (hnout : nout = 1#32 ∨ nout = 2#32) (hnin : nin = 2#32 ∨ nin = 3#32)
    (ho_lt : o.toNat < nout.toNat) (ht64 : t.toNat < 64)
    (hn16 : n.toNat ≤ 16) (hmasks : MasksOk s.n_out.toNat s.mlo s.mhi) (hnout1 : 1 ≤ s.n_out.toNat)
    (hsO_eq : sO = { s with rs_n := sO.rs_n, rs_ptop := sO.rs_ptop })
    (hgY1 : 85 ≤ gY1.length) (hgL1 : 16 ≤ gL1.length) (hgH1 : 16 ≤ gH1.length)
    (hMono1 : ∀ i < n.toNat, MonoSliceOk gY1 (5 * i) 80 ∧ (gY1.getD (5 * i) 0#32).toNat ≤ 4)
    (houts : ∀ q < nout.toNat, (s.g_outs.getD q 0#32).toNat < s.n_nets.toNat)
    (hins : ∀ j < nin.toNat, (s.g_innet.getD j 0#32).toNat < s.n_nets.toNat)
    (hnn30 : s.n_nets.toNat ≤ 0x3FFFFFFF)
    (hmC : (arCtxMem cx sO ⋆ arrayPad i32 s.gsy gY1 ⋆ array64 s.gcl gL1 ⋆ array64 s.gch gH1 ⋆ F) mC)
    (hFail : Q (false, ⟨⟩) mC)
    (hNext : (∀ ρ, GateRowOk g bindArr nin nout s ρ t.toNat →
      polyEval s.n_out.toNat (cSig g ρ bindArr) gY1 gsyMOff gL1 gH1 n.toNat =
        bv s.n_out.toNat (cSig g ρ bindArr (2 * (s.g_outs.getD o.toNat 0#32).toNat))) →
      ∀ j', Jt (j', t + 1, ()) mC) :
    wp Γ Q X (gateRowExpr cx s.dense kraw nout nin nl j0 o t n Jt) mC := by
  have hn2 : nin.toNat ≤ 3 := by rcases hnin with rfl | rfl <;> decide
  have ho2 : nout.toNat ≤ 2 := by rcases hnout with rfl | rfl <;> decide
  have hsO_dense : sO.dense = s.dense := by rw [hsO_eq]
  have hsO_gsy : sO.gsy = s.gsy := by rw [hsO_eq]
  have hsO_gcl : sO.gcl = s.gcl := by rw [hsO_eq]
  have hsO_gch : sO.gch = s.gch := by rw [hsO_eq]
  have hsO_nout : sO.n_out = s.n_out := by rw [hsO_eq]
  have hsO_mlo : sO.mlo = s.mlo := by rw [hsO_eq]
  have hsO_mhi : sO.mhi = s.mhi := by rw [hsO_eq]
  have hsO_innet : sO.g_innet = s.g_innet := by rw [hsO_eq]
  have hsO_tin : sO.g_tin = s.g_tin := by rw [hsO_eq]
  have hsO_outs : sO.g_outs = s.g_outs := by rw [hsO_eq]
  have hsO_tto : sO.g_tto = s.g_tto := by rw [hsO_eq]
  have hsO_len : ArCtxLengthsOk sO := arCtxMem_ok (cx := cx)
    (R := arrayPad i32 s.gsy gY1 ⋆ array64 s.gcl gL1 ⋆ array64 s.gch gH1 ⋆ F) (m := mC)
    (sep_cast hmC (by ac_rfl))
  refine wp_loop_group (fun ki ⟨_jI, sl, sh, i, _⟩ mI =>
    i.toNat ≤ n.toNat ∧ ki = n.toNat - i.toNat ∧ mC = mI ∧
    ∀ ρ, GateRowOk g bindArr nin nout s ρ t.toNat →
      coeff128 s.n_out.toNat sl sh =
        polyEval s.n_out.toNat (cSig g ρ bindArr) gY1 gsyMOff gL1 gH1 i.toNat)
    ?_ (fun Ji hJi => by
      c0_hsteps
      refine hJi n.toNat (j0, 0#64, 0#64, 0#32, ()) mC
        ⟨Nat.zero_le _, Nat.sub_zero _, rfl, fun ρ _ => ?_⟩
      simp [coeff128, polyEval, polyEvalRange])
  · rintro Ji ki ⟨jI, sl, sh, i, _⟩ mI hrecI ⟨hi_le, rfl, rfl, hCur⟩
    dsimp only at hrecI hi_le hCur ⊢
    c0_hsteps_nogrp
    · have hi_lt : i.toNat < n.toNat := hc
      have hi5 : (5#32 * i).toNat = 5 * i.toNat := bv32_mul5_toNat (by omega)
      have hm_arr : (array (t := i32) sO.gsy gY1 ⋆
          (arCtxMem cx sO ⋆ u32PadTail s.gsy gY1.length ⋆ array64 s.gcl gL1 ⋆
            array64 s.gch gH1 ⋆ F)) mC := by
        rw [arrayPad_u32_unfold] at hmC
        rw [hsO_gsy]
        exact sep_cast hmC (by ac_rfl)
      have hm_rd := sep_cast hm_arr (by ac_rfl)
      have hmlen_lt : 5 * i.toNat < gY1.length := by omega
      have hmlen_lt' : (BitVec.setWidth 64 (5 * i)).toNat +
          (BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 0)).toNat < gY1.length := by
        rw [bv64_sw_toNat, show (5 : BitVec 32) = 5#32 from rfl, hi5,
          show (BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 0)).toNat = 0 from rfl]
        omega
      have hm1_bd := hMono1 i.toNat hi_lt
      c0_hsteps_nogrp
      let mlen := gY1[(BitVec.setWidth 64 (5 * i)).toNat +
        (BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 0)).toNat]'hmlen_lt'
      have hmlen_eq : mlen = gY1.getD (5 * i.toNat) 0#32 := by
        dsimp only [mlen]
        rw [d_getD_eq_getElem gY1 0#32 hmlen_lt]
        congr 1
      have hmlen4 : mlen.toNat ≤ 4 := by rw [hmlen_eq]; exact hm1_bd.2
      refine wp_loop_group (fun kk ⟨_jK, one, k2, _⟩ mK =>
        1 ≤ k2.toNat ∧ k2.toNat ≤ mlen.toNat + 1 ∧ kk = mlen.toNat + 1 - k2.toNat ∧
        mC = mK ∧
        (one = true → ∀ r < k2.toNat - 1, ∀ ρ, GateRowOk g bindArr nin nout s ρ t.toNat →
          cSig g ρ bindArr (gY1.getD (5 * i.toNat + 1 + r) 0#32).toNat = true) ∧
        (one = false → ∀ ρ, GateRowOk g bindArr nin nout s ρ t.toNat →
          ∃ r < mlen.toNat,
            cSig g ρ bindArr (gY1.getD (5 * i.toNat + 1 + r) 0#32).toNat = false))
        ?_ (fun Jk hJk => by
          c0_hsteps
          exact hJk mlen.toNat (jI, true, 1#32, ()) mC
            ⟨by decide, by rw [show (1#32 : BitVec 32).toNat = 1 from rfl]; omega,
             by rw [show (1#32 : BitVec 32).toNat = 1 from rfl]; omega, rfl,
             fun _ r hr => by rw [show (1#32 : BitVec 32).toNat = 1 from rfl] at hr; omega,
             fun h => by cases h⟩)
      · rintro Jk kk ⟨jK, one, k2, _⟩ mK hrecK
          ⟨hk2_1, hk2_le, rfl, rfl, hOneT, hOneF⟩
        dsimp only at hrecK hk2_1 hk2_le hOneT hOneF ⊢
        refine wp_join_group (fun _ mA => mC = mA ∧ (one = false ∨ mlen.toNat < k2.toNat))
          ?_ ?_
        · rintro _ _ mA ⟨rfl, hend⟩
          c0_hsteps_nogrp
          refine wp_join_group (fun ⟨sl', sh', _⟩ mCadd => mC = mCadd ∧
            ∀ ρ, GateRowOk g bindArr nin nout s ρ t.toNat → coeff128 s.n_out.toNat sl' sh' =
              polyEval s.n_out.toNat (cSig g ρ bindArr) gY1 gsyMOff gL1 gH1
                (i.toNat + 1)) ?_ ?_
          · rintro _ ⟨sl', sh', _⟩ mCadd ⟨rfl, hN⟩
            c0_hsteps_nogrp
            refine hrecI (n.toNat - (i + 1).toNat) (jK, sl', sh', i + 1, ()) mC
              (by rw [bv32_add1_toNat (by omega)]; omega)
              ⟨by rw [bv32_add1_toNat (by omega)]; omega, rfl, rfl, fun ρ hR => ?_⟩
            rw [bv32_add1_toNat (by omega)]; exact hN ρ hR
          · intro Jc hJc
            c0_hsteps_nogrp
            · subst ‹one = true›
              have hgcl_i : i.toNat < gL1.length := by omega
              have hgch_i : i.toNat < gH1.length := by omega
              have hc_mem : (arCtxMem cx sO ⋆ (arrayPad i32 s.gsy gY1 ⋆
                  array64 sO.gcl gL1 ⋆ array64 sO.gch gH1 ⋆ F)) mC := by
                rw [hsO_gcl, hsO_gch]; exact sep_cast hmC (by ac_rfl)
              c0_hsteps_nogrp
              apply wp_call_of_spec
              dsimp only [vals, Arg.val]
              refine hCadd _ _ _ _ ⟨sO, _,
                by rw [hsO_nout, hsO_mlo, hsO_mhi]; exact hmasks, hc_mem, fun sl' sh' hadd => ?_⟩
              refine hJc (sl', sh', ()) mC ⟨rfl, fun ρ hR => ?_⟩
              rw [hsO_nout] at hadd
              rw [hadd, show gL1[(BitVec.setWidth 64 i).toNat]' (by
                rw [bv64_sw_toNat]; exact hgcl_i) = gL1.getD i.toNat 0#64 from by
                  rw [d_getD_eq_getElem gL1 0#64 hgcl_i]; congr 1,
                show gH1[(BitVec.setWidth 64 i).toNat]' (by
                  rw [bv64_sw_toNat]; exact hgch_i) = gH1.getD i.toNat 0#64 from by
                    rw [d_getD_eq_getElem gH1 0#64 hgch_i]; congr 1]
              have hmvl := gate_monoValL_iff_one (σ := cSig g ρ bindArr) (gsy := gY1)
                (i := i.toNat) (mlen := mlen.toNat) (k2 := k2.toNat) (one := true)
                (congrArg BitVec.toNat hmlen_eq) (Or.inr (hend.resolve_left (by decide)))
                (fun _ r hr => hOneT rfl r hr ρ hR) (fun h => by cases h)
              rw [← gate_polyEval_step (by omega) (hCur ρ hR), hmvl]
              rfl
            · have honeF : one = false := hc
              subst honeF
              refine hJc (sl, sh, ()) mC ⟨rfl, fun ρ hR => ?_⟩
              have hmvl := gate_monoValL_iff_one (σ := cSig g ρ bindArr) (gsy := gY1)
                (i := i.toNat) (mlen := mlen.toNat) (k2 := k2.toNat) (one := false)
                (congrArg BitVec.toNat hmlen_eq) (Or.inl rfl)
                (fun h => by cases h) (fun _ => hOneF rfl ρ hR)
              simpa [hmvl] using gate_polyEval_step (by omega) (hCur ρ hR)
        · intro Ja hJa
          c0_hsteps_nogrp
          · have hhone : one = true := ‹one = true›
            have hk2_lt : k2.toNat ≤ mlen.toNat := ‹_›
            have hx_lt : (5#32 * i + k2).toNat < gY1.length := by
              rw [BitVec.toNat_add, hi5, Nat.mod_eq_of_lt (by omega)]; omega
            have hx_lt' : (BitVec.setWidth 64 (5 * i + k2)).toNat < gY1.length := by
              rw [bv64_sw_toNat, show (5 : BitVec 32) = 5#32 from rfl]; exact hx_lt
            c0_hsteps_nogrp
            let x := gY1[(BitVec.setWidth 64 (5 * i + k2)).toNat]'hx_lt'
            have hx_lt_nat : 5 * i.toNat + k2.toNat < gY1.length := by
              rw [BitVec.toNat_add, hi5, Nat.mod_eq_of_lt (by omega)] at hx_lt; exact hx_lt
            have hx_eq : x = gY1.getD (5 * i.toNat + k2.toNat) 0#32 := by
              dsimp only [x]
              rw [d_getD_eq_getElem gY1 0#32 hx_lt_nat]
              congr 1; rw [bv64_sw_toNat, show (5 : BitVec 32) = 5#32 from rfl,
                BitVec.toNat_add, hi5, Nat.mod_eq_of_lt (by omega)]
            have hj_in_len : sO.g_innet.length = 3 := hsO_len.g_innet
            have ho_out_len : sO.g_outs.length = 2 := hsO_len.g_outs
            have ho_tto_len : sO.g_tto.length = 2 := hsO_len.g_tto
            have hj_tin_len : sO.g_tin.length = 3 := hsO_len.g_tin
            refine wp_loop_group (fun kj ⟨j, fv, val, _⟩ mJ =>
              j.toNat ≤ nin.toNat ∧ kj = nin.toNat - j.toNat ∧ mC = mJ ∧
              (fv = true → ∀ ρ, GateRowOk g bindArr nin nout s ρ t.toNat →
                (val ≠ 0#32 ↔ cSig g ρ bindArr x.toNat = true)))
              ?_ (fun Jj hJj => by
                c0_hsteps
                exact hJj nin.toNat (0#32, false, 0#32, ()) mC
                  ⟨Nat.zero_le _, Nat.sub_zero _, rfl, fun h => by cases h⟩)
            · rintro Jj kj ⟨j, fv, val, _⟩ mJ hrecJ ⟨hj_le, rfl, rfl, hFv⟩
              dsimp only at hrecJ hj_le hFv ⊢
              c0_hsteps_nogrp
              · have hj_lt : j.toNat < nin.toNat := hc
                have hj_in : j.toNat < sO.g_innet.length := by rw [hj_in_len]; omega
                c0_hsteps_nogrp
                · refine wp_join_group (fun ⟨fv', val', _⟩ mJ2 => mC = mJ2 ∧
                    (fv' = true → ∀ ρ, GateRowOk g bindArr nin nout s ρ t.toNat →
                      (val' ≠ 0#32 ↔ cSig g ρ bindArr x.toNat = true)))
                    (fun _ ⟨fv', val', _⟩ mJ2 ⟨rfl, hFv'⟩ => by
                      c0_hsteps
                      exact hrecJ (nin.toNat - (j + 1).toNat) (j + 1, fv', val', ()) mC
                        (by rw [bv32_add1_toNat (by omega)]; omega)
                        ⟨by rw [bv32_add1_toNat (by omega)]; omega, rfl, rfl, hFv'⟩)
                    (fun Jm hJm => by
                      c0_hsteps_nogrp
                      · exact hJm (fv, val, ()) mC ⟨rfl, hFv⟩
                      · have hfvF : fv = false := ‹fv = false›
                        have hxi_eq : x.toNat = 2 * (s.g_innet.getD j.toNat 0#32).toNat := by
                          have hlhs :
                              gY1[BitVec.toNat (5 : BitVec 32) * i.toNat % 2 ^ 32 + k2.toNat]'
                                (by rw [show BitVec.toNat (5 : BitVec 32) = 5 from rfl,
                                      Nat.mod_eq_of_lt (by omega)]; exact hx_lt_nat) = x := by
                            rw [hx_eq, d_getD_eq_getElem gY1 0#32 hx_lt_nat]
                            congr 1
                            rw [show BitVec.toNat (5 : BitVec 32) = 5 from rfl,
                              Nat.mod_eq_of_lt (by omega)]
                          have h1 := hc
                          have hinj : sO.g_innet[j.toNat]'hj_in = s.g_innet.getD j.toNat 0#32 := by
                            rw [d_getD_eq_getElem s.g_innet 0#32 (by rw [← hsO_innet]; exact hj_in)]
                            simp only [hsO_innet]
                          have hlt32 : 2 * (s.g_innet.getD j.toNat 0#32).toNat < 2 ^ 32 := by
                            have := hins j.toNat hj_lt; omega
                          rw [hlhs, hinj] at h1
                          have h1n := congrArg BitVec.toNat h1
                          rwa [BitVec.toNat_mul, show BitVec.toNat (2 : BitVec 32) = 2 from rfl,
                            Nat.mod_eq_of_lt hlt32] at h1n
                        refine hJm (true, _, ()) mC ⟨rfl, fun _ ρ hR => ?_⟩
                        rw [hxi_eq, ← hR.1 j.toNat hj_lt,
                          show sO.g_tin[j.toNat]'(by omega) = s.g_tin.getD j.toNat 0#64 from by
                            rw [d_getD_eq_getElem s.g_tin 0#64 (by rw [← hsO_tin]; omega)]
                            simp only [hsO_tin]]
                        exact row_shr_and1_ne0 _ t ht64
                      · exact hJm (fv, val, ()) mC ⟨rfl, hFv⟩)
              · refine wp_join_group (fun ⟨fv', val', _⟩ mJ2 => mC = mJ2 ∧
                  (fv' = true → ∀ ρ, GateRowOk g bindArr nin nout s ρ t.toNat →
                    (val' ≠ 0#32 ↔ cSig g ρ bindArr x.toNat = true)))
                  (fun _ ⟨fv', val', _⟩ mJ2 ⟨rfl, hFv'⟩ => by
                    c0_hsteps_nogrp
                    · refine hrecK (mlen.toNat + 1 - (k2 + 1).toNat)
                        (j, decide (val' ≠ 0#32), k2 + 1, ()) mC
                        (by rw [bv32_add1_toNat (by omega)]; omega)
                        ⟨by rw [bv32_add1_toNat (by omega)]; omega,
                         by rw [bv32_add1_toNat (by omega)]; omega, rfl, rfl,
                         fun hd r hr ρ hR => ?_, fun hd ρ hR => ?_⟩
                      · rw [bv32_add1_toNat (by omega)] at hr
                        rcases Nat.eq_or_lt_of_le (show r ≤ k2.toNat - 1 by omega) with rfl | hrlt
                        · have hvne : val' ≠ 0#32 := by simpa using hd
                          rw [show 5 * i.toNat + 1 + (k2.toNat - 1) =
                              5 * i.toNat + k2.toNat by omega, ← hx_eq]
                          exact (hFv' ‹fv' = true› ρ hR).mp hvne
                        · exact hOneT hhone r hrlt ρ hR
                      · refine ⟨k2.toNat - 1, by omega, ?_⟩
                        rw [show 5 * i.toNat + 1 + (k2.toNat - 1) =
                            5 * i.toNat + k2.toNat by omega, ← hx_eq]
                        have hv0 : ¬ (val' ≠ 0#32) := by simpa using hd
                        exact Bool.eq_false_iff.mpr fun hct =>
                          hv0 ((hFv' ‹fv' = true› ρ hR).mpr hct)
                    · exact hFail)
                  (fun Jf hJf => by
                    c0_hsteps_nogrp
                    · exact hJf (fv, val, ()) mC ⟨rfl, hFv⟩
                    · have hfvF : fv = false := ‹fv = false›
                      have hnout2 : nout.toNat = 2 := by
                        have h1 : nout = 2#32 := ‹nout = 2#32›; rw [h1]; decide
                      have hxo_eq : x.toNat = 2 * (s.g_outs.getD 0 0#32).toNat := by
                        have hlhs :
                            gY1[BitVec.toNat (5 : BitVec 32) * i.toNat % 2 ^ 32 + k2.toNat]'
                              (by rw [show BitVec.toNat (5 : BitVec 32) = 5 from rfl,
                                    Nat.mod_eq_of_lt (by omega)]; exact hx_lt_nat) = x := by
                          rw [hx_eq, d_getD_eq_getElem gY1 0#32 hx_lt_nat]
                          congr 1
                          rw [show BitVec.toNat (5 : BitVec 32) = 5 from rfl,
                            Nat.mod_eq_of_lt (by omega)]
                        have hidx0 : (OfNat.ofNat 0 % 2 ^ 64 *
                            BitVec.toNat (4 : BitVec 64) % 2 ^ 64 / 4 : Nat) = 0 := by decide
                        have h1 := hc
                        have ho0s : sO.g_outs[0]'(by rw [ho_out_len]; decide) =
                            s.g_outs.getD 0 0#32 := by
                          rw [d_getD_eq_getElem s.g_outs 0#32 (by rw [← hsO_outs]; omega)]
                          simp only [hsO_outs]
                        have hlt32 : 2 * (s.g_outs.getD 0 0#32).toNat < 2 ^ 32 := by
                          have := houts 0 (by omega); omega
                        simp only [hidx0, hlhs, ho0s] at h1
                        have h1n := congrArg BitVec.toNat h1
                        rwa [BitVec.toNat_mul, show BitVec.toNat (2 : BitVec 32) = 2 from rfl,
                          Nat.mod_eq_of_lt hlt32] at h1n
                      refine hJf (true, _, ()) mC ⟨rfl, fun _ ρ hR => ?_⟩
                      have hgt0_eq :
                          sO.g_tto[(BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 0) * 8).toNat / 8]'
                            (by rw [ho_tto_len]; decide) = s.g_tto.getD 0 0#64 := by
                        rw [d_getD_eq_getElem s.g_tto 0#64 (by rw [← hsO_tto]; omega)]
                        simp only [hsO_tto]; rfl
                      rw [hxo_eq, ← hR.2 0 (by omega), hgt0_eq]
                      exact row_shr_and1_ne0 _ t ht64
                    · exact hJf (fv, val, ()) mC ⟨rfl, hFv⟩
                    · exact hJf (fv, val, ()) mC ⟨rfl, hFv⟩)
          · exact hJa () mC ⟨rfl, Or.inl hc⟩
          · have hk2_not : ¬ k2.toNat ≤ mlen.toNat := hc
            exact hJa () mC ⟨rfl, Or.inr (by omega)⟩
    · exact hFail
    · exact hFail
    · refine hNext (fun ρ hR => ?_) jI
      have hi_eq : i.toNat = n.toNat := by omega
      rw [← hi_eq, ← hCur ρ hR]
      have hsh0 : sh = 0#64 := ‹sh = 0#64›
      have hsl : sl = (s.g_tto.getD o.toNat 0#64 >>> BitVec.ofNat 64 t.toNat) &&& 1#64 := by
        have h1 := ‹sl = _›
        have hgt_eq : sO.g_tto[o.toNat]'(by rw [hsO_len.g_tto]; omega) =
            s.g_tto.getD o.toNat 0#64 := by
          rw [d_getD_eq_getElem s.g_tto 0#64 (by rw [← hsO_tto, hsO_len.g_tto]; omega)]
          simp only [hsO_tto]
        rw [hgt_eq] at h1
        rw [h1, Nat.mod_eq_of_lt ht64, show (1 : BitVec 64) = 1#64 from rfl]
        congr 1
        exact BitVec.eq_of_toNat_eq (by simp)
      rw [hsh0, hsl, gate_bv64_shr_and1_eq _ ht64,
        gate_coeff128_bit hnout1, hR.2 o.toNat ho_lt]

theorem ar_do_gate_eval_wp {Γ : LeanQbe.T.Env}
    (hDcanon : ∀ xs m Q X, arDcanonSpec xs m Q X → Γ "ar_dcanon" [i64, i64] [i32] xs m Q X)
    (hCadd : ∀ xs m Q X, arCaddSpec xs m Q X →
      Γ "ar_cadd" [i64, i64, i64, i64, i64] [i64, i64] xs m Q X)
    (hInstall : ∀ xs m Q X, arInstallRuleSpec xs m Q X →
      Γ "ar_install_rule" [i64, i32, i32] [.bool] xs m Q X)
    {cx : BitVec 64} {kraw nout nin nl : BitVec 32} {s : ArCtxState} {g : Aig}
    {bindArr ruleOff ruleN partnerArr : List (BitVec 32)}
    {d6 d7 : List (BitVec 64)} {gsy : List (BitVec 32)} {gcl gch : List (BitVec 64)}
    {rsM : List (BitVec 32)} {rsL rsH : List (BitVec 64)} {rsPool : List (BitVec 32)} {j0 : Val i32}
    {F : Mem 64 → Prop} {m : Mem 64} {Q : Post [.bool]} {X : XPost}
    (hkraw : (kraw &&& 255#32) = 6#32 → nout = 2#32)
    (hnout : nout = 1#32 ∨ nout = 2#32) (hnin : nin = 2#32 ∨ nin = 3#32)
    (hnl1 : 1 ≤ nl.toNat) (hnl6 : nl.toNat ≤ 6)
    (hnn30 : s.n_nets.toNat ≤ 0x3FFFFFFF) (hrcap30 : s.rs_cap.toNat < 2 ^ 30)
    (hrpcap32 : s.rs_pcap.toNat < 2 ^ 32) (hmasks : MasksOk s.n_out.toNat s.mlo s.mhi)
    (hnout1 : 1 ≤ s.n_out.toNat)
    (hd6 : d6.length = 16) (hd7 : d7.length = 16)
    (hgsy : 85 ≤ gsy.length) (hgcl : 16 ≤ gcl.length) (hgch : 16 ≤ gch.length)
    (houts : ∀ o < nout.toNat, (s.g_outs.getD o 0#32).toNat < s.n_nets.toNat)
    (houts_ne : nout.toNat = 2 → s.g_outs.getD 0 0#32 ≠ s.g_outs.getD 1 0#32)
    (hins : ∀ j < nin.toNat, (s.g_innet.getD j 0#32).toNat < s.n_nets.toNat)
    (hrow : ∀ ρ : Nat → Bool, ∃ t < 2 ^ nl.toNat, t < 64 ∧ GateRowOk g bindArr nin nout s ρ t)
    (hVs : ∀ j < 4, (s.g_vs.getD j 0#32).toNat / 2 < s.n_nets.toNat)
    (hrsn : s.rs_n.toNat ≤ s.rs_cap.toNat) (hrspt : s.rs_ptop.toNat ≤ s.rs_pcap.toNat)
    (hTot : monoTotalWords rsPool rsM s.rs_n.toNat ≤ s.rs_ptop.toNat)
    (hRsOk : ∀ r < s.rs_n.toNat,
      (rsPool.getD (rsM.getD r 0#32).toNat 0#32).toNat + 1 < 2 ^ 32)
    (hRsSorted : RulesSorted rsPool rsM s.rs_n.toNat)
    (hRep : ∀ ρ : Nat → Bool,
      PartnerRep (cSig g ρ bindArr) s.n_nets.toNat partnerArr ∧
      RulesRep s.n_out.toNat (cSig g ρ bindArr) s ruleOff ruleN rsM rsL rsH rsPool)
    (hm : (arCtxMem cx s ⋆ array64 (s.dense + 768#64) d6 ⋆ array64 (s.dense + 896#64) d7 ⋆
      arrayPad i32 s.gsy gsy ⋆ array64 s.gcl gcl ⋆ array64 s.gch gch ⋆
      array (t := i32) s.rule_off ruleOff ⋆ array (t := i32) s.rule_n ruleN ⋆
      array (t := i32) s.partner partnerArr ⋆ rsMem s rsM rsL rsH rsPool ⋆ F) m)
    (hQ : ∀ ok s' ruleOff' ruleN' partnerArr' gsy' gcl' gch' rsM' rsL' rsH' rsPool' m',
      s'.rs_n.toNat ≤ s.rs_cap.toNat → s'.rs_ptop.toNat ≤ s.rs_pcap.toNat →
      s' = { s with rs_n := s'.rs_n, rs_ptop := s'.rs_ptop } →
      ruleOff'.length = ruleOff.length → ruleN'.length = ruleN.length →
      partnerArr'.length = partnerArr.length → gsy'.length = gsy.length →
      gcl'.length = gcl.length → gch'.length = gch.length →
      rsM'.length = rsM.length → rsL'.length = rsL.length →
      rsH'.length = rsH.length → rsPool'.length = rsPool.length →
      (ok = true →
        monoTotalWords rsPool' rsM' s'.rs_n.toNat ≤ s'.rs_ptop.toNat ∧
        (SymsBound rsPool rsM s.rs_n.toNat s.n_nets.toNat →
          SymsBound rsPool' rsM' s'.rs_n.toNat s.n_nets.toNat) ∧
        (∀ r < s'.rs_n.toNat,
          (rsPool'.getD (rsM'.getD r 0#32).toNat 0#32).toNat + 1 < 2 ^ 32) ∧
        RulesSorted rsPool' rsM' s'.rs_n.toNat ∧
        (∀ ρ, PartnerRep (cSig g ρ bindArr) s.n_nets.toNat partnerArr' ∧
          RulesRep s'.n_out.toNat (cSig g ρ bindArr) s'
            ruleOff' ruleN' rsM' rsL' rsH' rsPool')) →
      (arCtxMem cx s' ⋆ array64 (s.dense + 768#64) d6 ⋆ array64 (s.dense + 896#64) d7 ⋆
        arrayPad i32 s.gsy gsy' ⋆ array64 s.gcl gcl' ⋆ array64 s.gch gch' ⋆
        array (t := i32) s.rule_off ruleOff' ⋆ array (t := i32) s.rule_n ruleN' ⋆
        array (t := i32) s.partner partnerArr' ⋆ rsMem s' rsM' rsL' rsH' rsPool' ⋆ F) m' →
      Q (ok, ⟨⟩) m') :
    wp Γ Q X (gateEvalExpr cx s.dense kraw nout nin nl j0) m := by
  obtain ⟨hntt_sh, _, hntt64⟩ := gate_ntt_bounds hnl1 hnl6
  have ho2 : nout.toNat ≤ 2 := by rcases hnout with rfl | rfl <;> decide
  let failQ : ∀ sO rO rN gY gL gH rM rL rH rP mO,
      sO.rs_n.toNat ≤ s.rs_cap.toNat → sO.rs_ptop.toNat ≤ s.rs_pcap.toNat →
      sO = { s with rs_n := sO.rs_n, rs_ptop := sO.rs_ptop } →
      rO.length = ruleOff.length → rN.length = ruleN.length →
      gY.length = gsy.length → gL.length = gcl.length → gH.length = gch.length →
      rM.length = rsM.length → rL.length = rsL.length → rH.length = rsH.length →
      rP.length = rsPool.length →
      (arCtxMem cx sO ⋆ array64 (s.dense + 768#64) d6 ⋆ array64 (s.dense + 896#64) d7 ⋆
        arrayPad i32 s.gsy gY ⋆ array64 s.gcl gL ⋆ array64 s.gch gH ⋆
        array (t := i32) s.rule_off rO ⋆ array (t := i32) s.rule_n rN ⋆
        array (t := i32) s.partner partnerArr ⋆ rsMem sO rM rL rH rP ⋆ F) mO →
      Q (false, ⟨⟩) mO :=
    fun sO rO rN gY gL gH rM rL rH rP mO a b c d e f h1 h2 h3 h4 h5 h6 hmO =>
      hQ false sO rO rN partnerArr gY gL gH rM rL rH rP mO
        a b c d e rfl f h1 h2 h3 h4 h5 h6 (fun h => by cases h) hmO
  c0_hsteps_nogrp
  refine wp_loop_group (fun k ⟨_jO, o, _⟩ mO =>
    o.toNat ≤ nout.toNat ∧ k = nout.toNat - o.toNat ∧
    ∃ sO rO rN gY gL gH rM rL rH rP,
      sO.rs_n.toNat ≤ s.rs_cap.toNat ∧ sO.rs_ptop.toNat ≤ s.rs_pcap.toNat ∧
      sO = { s with rs_n := sO.rs_n, rs_ptop := sO.rs_ptop } ∧
      rO.length = ruleOff.length ∧ rN.length = ruleN.length ∧
      gY.length = gsy.length ∧ gL.length = gcl.length ∧ gH.length = gch.length ∧
      rM.length = rsM.length ∧ rL.length = rsL.length ∧ rH.length = rsH.length ∧
      rP.length = rsPool.length ∧
      monoTotalWords rP rM sO.rs_n.toNat ≤ sO.rs_ptop.toNat ∧
      (SymsBound rsPool rsM s.rs_n.toNat s.n_nets.toNat →
        SymsBound rP rM sO.rs_n.toNat s.n_nets.toNat) ∧
      (∀ r < sO.rs_n.toNat, MonoSliceOk rP (rM.getD r 0#32).toNat sO.rs_ptop.toNat ∧
        (rP.getD (rM.getD r 0#32).toNat 0#32).toNat + 1 < 2 ^ 32) ∧
      RulesSorted rP rM sO.rs_n.toNat ∧
      (∀ ρ, RulesRep s.n_out.toNat (cSig g ρ bindArr) sO rO rN rM rL rH rP) ∧
      (arCtxMem cx sO ⋆ array64 (s.dense + 768#64) d6 ⋆ array64 (s.dense + 896#64) d7 ⋆
        arrayPad i32 s.gsy gY ⋆ array64 s.gcl gL ⋆ array64 s.gch gH ⋆
        array (t := i32) s.rule_off rO ⋆ array (t := i32) s.rule_n rN ⋆
        array (t := i32) s.partner partnerArr ⋆ rsMem sO rM rL rH rP ⋆ F) mO) ?_ ?_
  · rintro J k ⟨jO, o, _⟩ mO hrec ⟨ho_le, rfl, sO, rO, rN, gY, gL, gH, rM, rL, rH, rP, hsnO,
      hsptO, hsO_eq, hrO_l, hrN_l, hgY_l, hgL_l, hgH_l, hrM_l, hrL_l, hrH_l, hrP_l,
      hTotO, hSyO, hSlO, hRsSortedO, hRepO, hmO⟩
    dsimp only at *
    have hsO_len : ArCtxLengthsOk sO := arCtxMem_ok (cx := cx)
      (R := array64 (s.dense + 768#64) d6 ⋆ array64 (s.dense + 896#64) d7 ⋆
        arrayPad i32 s.gsy gY ⋆ array64 s.gcl gL ⋆ array64 s.gch gH ⋆
        array (t := i32) s.rule_off rO ⋆ array (t := i32) s.rule_n rN ⋆
        array (t := i32) s.partner partnerArr ⋆ rsMem sO rM rL rH rP ⋆ F) (m := mO)
      (sep_cast hmO (by ac_rfl))
    have hgl_o : sO.g_outs.length = 2 := hsO_len.g_outs
    have hgl_t : sO.g_tto.length = 2 := hsO_len.g_tto
    c0_hsteps_nogrp
    · have ho_lt : o.toNat < nout.toNat := hc
      let pD := if o = 0#32 then s.dense + 768#64 else s.dense + 896#64
      let dD := if o = 0#32 then d6 else d7
      let dOther := if o = 0#32 then d7 else d6
      let pOther := if o = 0#32 then s.dense + 896#64 else s.dense + 768#64
      refine wp_join_group (fun ⟨pSel, _⟩ mS => mS = mO ∧ pSel = pD) ?_ ?_
      · rintro _ ⟨pSel, _⟩ mS ⟨rfl, rfl⟩
        dsimp only
        have hmD : (arCtxMem cx sO ⋆ array64 pD dD ⋆ arrayPad i32 sO.gsy gY ⋆
            array64 sO.gcl gL ⋆ array64 sO.gch gH ⋆
            (array64 pOther dOther ⋆ array (t := i32) s.rule_off rO ⋆
              array (t := i32) s.rule_n rN ⋆ array (t := i32) s.partner partnerArr ⋆
              rsMem sO rM rL rH rP ⋆ F)) mS := by
          rw [show sO.gsy = s.gsy by rw [hsO_eq], show sO.gcl = s.gcl by rw [hsO_eq],
            show sO.gch = s.gch by rw [hsO_eq]]
          by_cases ho0 : o = 0#32
          · simp only [pD, dD, dOther, pOther, ite_eq_left ho0]; exact sep_cast hmO (by ac_rfl)
          · simp only [pD, dD, dOther, pOther, ite_eq_right ho0]; exact sep_cast hmO (by ac_rfl)
        apply wp_call_of_spec
        dsimp only [vals, Arg.val]
        refine hDcanon _ _ _ _ ⟨sO, dD, gL, gH, gY,
          (array64 pOther dOther ⋆ array (t := i32) s.rule_off rO ⋆
            array (t := i32) s.rule_n rN ⋆ array (t := i32) s.partner partnerArr ⋆
            rsMem sO rM rL rH rP ⋆ F),
          by rw [show sO.n_out = s.n_out by rw [hsO_eq], show sO.mlo = s.mlo by rw [hsO_eq],
            show sO.mhi = s.mhi by rw [hsO_eq]]; exact hmasks,
          by by_cases ho0 : o = 0#32 <;> simp [dD, ho0, hd6, hd7],
          by omega, by omega, by omega, hmD,
          fun n gY1 gL1 gH1 mC hn16 hgY1 hgL1 hgH1 hMono1 hMonoSorted1 _ hmC => ?_⟩
        have hmC' : (arCtxMem cx sO ⋆ array64 (s.dense + 768#64) d6 ⋆
            array64 (s.dense + 896#64) d7 ⋆ arrayPad i32 s.gsy gY1 ⋆
            array64 s.gcl gL1 ⋆ array64 s.gch gH1 ⋆
            array (t := i32) s.rule_off rO ⋆ array (t := i32) s.rule_n rN ⋆
            array (t := i32) s.partner partnerArr ⋆ rsMem sO rM rL rH rP ⋆ F) mC := by
          rw [show sO.gsy = s.gsy by rw [hsO_eq], show sO.gcl = s.gcl by rw [hsO_eq],
            show sO.gch = s.gch by rw [hsO_eq]] at hmC
          by_cases ho0 : o = 0#32
          · exact sep_cast hmC (by simp only [pD, dD, dOther, pOther, ite_eq_left ho0]; ac_rfl)
          · exact sep_cast hmC (by simp only [pD, dD, dOther, pOther, ite_eq_right ho0]; ac_rfl)
        c0_hsteps_nogrp
        refine wp_loop_group (fun kt ⟨_jT, t, _⟩ mT =>
          t.toNat ≤ 2 ^ nl.toNat ∧ kt = 2 ^ nl.toNat - t.toNat ∧ mC = mT ∧
          ∀ t0 < t.toNat, ∀ ρ : Nat → Bool, GateRowOk g bindArr nin nout s ρ t0 →
            polyEval s.n_out.toNat (cSig g ρ bindArr) gY1 gsyMOff gL1 gH1 n.toNat =
              bv s.n_out.toNat (cSig g ρ bindArr (2 * (s.g_outs.getD o.toNat 0#32).toNat)))
          ?_ (fun Jt hJt => by
            c0_hsteps
            exact hJt (2 ^ nl.toNat) (jO, 0#32, ()) mC
              ⟨Nat.zero_le _, Nat.sub_zero _, rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩)
        · rintro Jt kt ⟨jT, t, _⟩ mT hrecT ⟨ht_le, rfl, rfl, hPrev⟩
          dsimp only at hrecT ht_le hPrev ⊢
          c0_hsteps_nogrp
          · have ht_lt : t.toNat < 2 ^ nl.toNat := by
              have hc' : t.toNat < (1#32 <<< nl).toNat := by simpa [lift2] using hc
              rw [hntt_sh] at hc'; exact hc'
            have ht64 : t.toNat < 64 := lt_of_lt_of_le ht_lt hntt64
            have hmRow : (arCtxMem cx sO ⋆ arrayPad i32 s.gsy gY1 ⋆
                array64 s.gcl gL1 ⋆ array64 s.gch gH1 ⋆
                (array64 (s.dense + 768#64) d6 ⋆ array64 (s.dense + 896#64) d7 ⋆
                  array (t := i32) s.rule_off rO ⋆ array (t := i32) s.rule_n rN ⋆
                  array (t := i32) s.partner partnerArr ⋆ rsMem sO rM rL rH rP ⋆ F)) mC :=
              sep_cast hmC' (by ac_rfl)
            have hFailRow := failQ sO rO rN gY1 gL1 gH1 rM rL rH rP mC
              hsnO hsptO hsO_eq hrO_l hrN_l (hgY1.trans hgY_l) (hgL1.trans hgL_l)
              (hgH1.trans hgH_l) hrM_l hrL_l hrH_l hrP_l hmC'
            change wp Γ Q X (gateRowExpr cx s.dense kraw nout nin nl jT o t n Jt) mC
            refine ar_do_gate_row_wp hCadd (g := g) (bindArr := bindArr) hnout hnin ho_lt ht64 hn16
              hmasks hnout1 hsO_eq (by omega) (by omega) (by omega)
              (fun ii hii => ⟨(hMono1 ii hii).1, (hMono1 ii hii).2.1⟩)
              houts hins hnn30 hmRow hFailRow fun hCurT j' => ?_
            refine hrecT (2 ^ nl.toNat - (t + 1).toNat) (j', t + 1, ()) mC
              (by rw [bv32_add1_toNat (by omega)]; omega)
              ⟨by rw [bv32_add1_toNat (by omega)]; omega, rfl, rfl, fun t0 ht0 ρ hR0 => ?_⟩
            rw [bv32_add1_toNat (by omega)] at ht0
            rcases Nat.eq_or_lt_of_le (Nat.lt_succ_iff.mp ht0) with rfl | ht0lt
            · exact hCurT ρ hR0
            · exact hPrev t0 ht0lt ρ hR0
          · have ht_eq : t.toNat = 2 ^ nl.toNat := by
              have hnot : ¬t.toNat < (1#32 <<< nl).toNat := by simpa [lift2] using hc
              rw [hntt_sh] at hnot; omega
            have hpoly_ok : ∀ ρ : Nat → Bool,
                polyEval s.n_out.toNat (cSig g ρ bindArr) gY1 gsyMOff gL1 gH1 n.toNat =
                  bv s.n_out.toNat (cSig g ρ bindArr (2 * (s.g_outs.getD o.toNat 0#32).toNat)) :=
              fun ρ => by
                obtain ⟨t0, ht0, _, hrowT⟩ := hrow ρ
                exact hPrev t0 (by omega) ρ hrowT
            have ho_inst_lt : (sO.g_outs.getD o.toNat 0#32).toNat < sO.n_nets.toNat := by
              rw [show sO.g_outs = s.g_outs by rw [hsO_eq],
                show sO.n_nets = s.n_nets by rw [hsO_eq]]
              exact houts o.toNat ho_lt
            have hmI : (arCtxMem cx sO ⋆ array (t := i32) sO.rule_off rO ⋆
                array (t := i32) sO.rule_n rN ⋆ array (t := i32) sO.partner partnerArr ⋆
                array (t := i32) sO.gsy gY1 ⋆ array64 sO.gcl gL1 ⋆ array64 sO.gch gH1 ⋆
                rsMem sO rM rL rH rP ⋆
                (array64 (s.dense + 768#64) d6 ⋆ array64 (s.dense + 896#64) d7 ⋆
                  u32PadTail s.gsy gY1.length ⋆ F)) mC := by
              rw [show sO.rule_off = s.rule_off by rw [hsO_eq],
                show sO.rule_n = s.rule_n by rw [hsO_eq],
                show sO.partner = s.partner by rw [hsO_eq],
                show sO.gsy = s.gsy by rw [hsO_eq], show sO.gcl = s.gcl by rw [hsO_eq],
                show sO.gch = s.gch by rw [hsO_eq], arrayPad_u32_unfold] at *
              exact sep_cast hmC' (by ac_rfl)
            c0_hsteps_nogrp
            apply wp_call_of_spec
            dsimp only [vals, Arg.val]
            refine hInstall _ _ _ _ ⟨sO, rO, rN, partnerArr, rM, rL, rH, rP, gY1, gL1, gH1,
              (array64 (s.dense + 768#64) d6 ⋆ array64 (s.dense + 896#64) d7 ⋆
                u32PadTail s.gsy gY1.length ⋆ F),
              (by rw [← d_getD_eq_getElem sO.g_outs 0#32 (by rw [hsO_len.g_outs]; omega),
                    show sO.g_outs = s.g_outs by rw [hsO_eq],
                    show sO.n_nets = s.n_nets by rw [hsO_eq]]
                  exact houts o.toNat ho_lt),
              hn16,
              by rw [show sO.n_nets = s.n_nets by rw [hsO_eq]]; exact hnn30,
              by rw [show sO.rs_cap = s.rs_cap by rw [hsO_eq]]; exact hrcap30,
              by rw [show sO.rs_pcap = s.rs_pcap by rw [hsO_eq]]; exact hrpcap32,
              (hRepO (fun _ => false)).1, (hRepO (fun _ => false)).2.1,
              by rw [show sO.n_nets = s.n_nets by rw [hsO_eq]]; exact (hRep (fun _ => false)).1.1,
              by rw [show sO.rs_cap = s.rs_cap by rw [hsO_eq]]; exact hsnO,
              by rw [show sO.rs_pcap = s.rs_pcap by rw [hsO_eq]]; exact hsptO,
              (hRepO (fun _ => false)).2.2.2.2.1, (hRepO (fun _ => false)).2.2.2.2.2.1,
              (hRepO (fun _ => false)).2.2.2.2.2.2.1, (hRepO (fun _ => false)).2.2.2.2.2.2.2.1,
              by omega, by omega, by omega,
              by rw [show sO.n_out = s.n_out by rw [hsO_eq], show sO.mlo = s.mlo by rw [hsO_eq],
                show sO.mhi = s.mhi by rw [hsO_eq]]; exact hmasks,
              fun ii hii => ⟨(hMono1 ii hii).1, by have := (hMono1 ii hii).2.1; omega⟩,
              hMonoSorted1, hSlO, hRsSortedO, hTotO,
              ⟨cSig g (fun _ => false) bindArr,
                by rw [show sO.n_nets = s.n_nets by rw [hsO_eq]]
                   exact (hRep (fun _ => false)).1⟩,
              hmI,
              fun okI s1 rO1 rN1 rM1 rL1 rH1 rP1 m1 hsn1 hspt1 hs1_eq hrO1 hrN1
                hrM1 hrL1 hrH1 hrP1 hokI hm1 => ?_⟩
            have hs1_base : s1 = { s with rs_n := s1.rs_n, rs_ptop := s1.rs_ptop } := by
              rw [hs1_eq, hsO_eq]
            have hm1' : (arCtxMem cx s1 ⋆ array64 (s.dense + 768#64) d6 ⋆
                array64 (s.dense + 896#64) d7 ⋆ arrayPad i32 s.gsy gY1 ⋆
                array64 s.gcl gL1 ⋆ array64 s.gch gH1 ⋆
                array (t := i32) s.rule_off rO1 ⋆ array (t := i32) s.rule_n rN1 ⋆
                array (t := i32) s.partner partnerArr ⋆ rsMem s1 rM1 rL1 rH1 rP1 ⋆ F) m1 := by
              rw [show s1.rule_off = s.rule_off by rw [hs1_base],
                show s1.rule_n = s.rule_n by rw [hs1_base],
                show s1.partner = s.partner by rw [hs1_base],
                show s1.gsy = s.gsy by rw [hs1_base], show s1.gcl = s.gcl by rw [hs1_base],
                show s1.gch = s.gch by rw [hs1_base]] at hm1
              rw [arrayPad_u32_unfold]
              exact sep_cast hm1 (by ac_rfl)
            cases hokI_b : okI
            · dsimp only
              refine head_wp_jnz rfl (fun h => by cases h) (fun _ => ?_)
              c0_hstraight
              exact failQ s1 rO1 rN1 gY1 gL1 gH1 rM1 rL1 rH1 rP1 m1
                (by rw [hsO_eq] at hsn1; exact hsn1) (by rw [hsO_eq] at hspt1; exact hspt1)
                hs1_base (hrO1.trans hrO_l) (hrN1.trans hrN_l)
                (hgY1.trans hgY_l) (hgL1.trans hgL_l) (hgH1.trans hgH_l)
                (hrM1.trans hrM_l) (hrL1.trans hrL_l) (hrH1.trans hrH_l) (hrP1.trans hrP_l) hm1'
            · dsimp only
              refine head_wp_jnz rfl (fun _ => ?_) (fun h => by cases h)
              obtain ⟨hTot1, hSy1, hSl1, hRsSorted1, hRep1⟩ := hokI hokI_b
              have hGsyBound :
                  ∀ ii < n.toNat, ∀ x ∈ symListAt gY1 (5 * ii), x / 2 < s.n_nets.toNat := by
                intro ii hii x hx
                obtain ⟨j, hj4, rfl⟩ := (hMono1 ii hii).2.2 x hx
                rw [show sO.g_vs = s.g_vs by rw [hsO_eq]]
                exact hVs j hj4
              c0_hstraight
              refine hrec (nout.toNat - (o + 1).toNat) (jT, o + 1, ()) m1
                (by rw [bv32_add1_toNat (by omega)]; omega)
                ⟨by rw [bv32_add1_toNat (by omega)]; omega, rfl,
                 s1, rO1, rN1, gY1, gL1, gH1, rM1, rL1, rH1, rP1,
                 by rw [hsO_eq] at hsn1; exact hsn1, by rw [hsO_eq] at hspt1; exact hspt1,
                 hs1_base, hrO1.trans hrO_l, hrN1.trans hrN_l,
                 hgY1.trans hgY_l, hgL1.trans hgL_l, hgH1.trans hgH_l,
                 hrM1.trans hrM_l, hrL1.trans hrL_l, hrH1.trans hrH_l, hrP1.trans hrP_l,
                 hTot1, fun hSb => hSy1 s.n_nets.toNat (hSyO hSb) hGsyBound, hSl1, hRsSorted1,
                 fun ρ => by
                   rw [show s.n_out = s1.n_out by rw [hs1_base]]
                   refine hRep1 (cSig g ρ bindArr)
                     (by rw [show sO.n_nets = s.n_nets by rw [hsO_eq]]; exact (hRep ρ).1) ?_ ?_
                   · rw [show sO.n_out = s.n_out by rw [hsO_eq]]; exact hRepO ρ
                   · have ho_eq : sO.g_outs[o.toNat]' (by rw [hsO_len.g_outs]; omega) =
                         s.g_outs.getD o.toNat 0#32 := by
                       rw [d_getD_eq_getElem s.g_outs 0#32
                         (by rw [← show sO.g_outs = s.g_outs by rw [hsO_eq], hsO_len.g_outs]
                             omega)]
                       simp only [show sO.g_outs = s.g_outs by rw [hsO_eq]]
                     rw [show sO.n_out = s.n_out by rw [hsO_eq], ho_eq]
                     exact hpoly_ok ρ,
                 hm1'⟩
      · intro Js hJs
        c0_hsteps_nogrp
        · exact hJs (s.dense + 768#64, ()) mO
            ⟨rfl, by simp only [pD]; rw [ite_eq_left ‹o = 0#32›]⟩
        · exact hJs (s.dense + 896#64, ()) mO
            ⟨rfl, by simp only [pD]; rw [ite_eq_right ‹o ≠ 0#32›]⟩
    · have hpart_len : s.n_nets.toNat ≤ partnerArr.length := (hRep (fun _ => false)).1.1
      refine wp_join_group (fun _ mJ => Q (true, ⟨⟩) mJ)
        (fun _ _ mJ h => by c0_hstraight; exact h) fun Js hJs => ?_
      c0_hsteps_nogrp
      · exact failQ sO rO rN gY gL gH rM rL rH rP mO
          hsnO hsptO hsO_eq hrO_l hrN_l hgY_l hgL_l hgH_l
          hrM_l hrL_l hrH_l hrP_l hmO
      · have hkind6 : (kraw &&& 255#32) = 6#32 := by simpa [Arg.val] using ‹_›
        have hgt0 : sO.g_tto[0]'(by rw [hsO_len.g_tto]; decide) = s.g_tto.getD 0 0#64 := by
          rw [d_getD_eq_getElem s.g_tto 0#64
            (by rw [← show sO.g_tto = s.g_tto by rw [hsO_eq], hsO_len.g_tto]; decide)]
          simp only [show sO.g_tto = s.g_tto by rw [hsO_eq]]
        have hgt1 : sO.g_tto[1]'(by rw [hsO_len.g_tto]; decide) = s.g_tto.getD 1 0#64 := by
          rw [d_getD_eq_getElem s.g_tto 0#64
            (by rw [← show sO.g_tto = s.g_tto by rw [hsO_eq], hsO_len.g_tto]; decide)]
          simp only [show sO.g_tto = s.g_tto by rw [hsO_eq]]
        have hand0 : s.g_tto.getD 0 0#64 &&& s.g_tto.getD 1 0#64 = 0#64 := by
          rw [← hgt0, ← hgt1]; exact hc
        have hnout2 : nout.toNat = 2 := by rw [hkraw hkind6]; decide
        have ho0_lt : (s.g_outs.getD 0 0#32).toNat < partnerArr.length := by
          have := houts 0 (by omega); omega
        have ho1_lt : (s.g_outs.getD 1 0#32).toNat < partnerArr.length := by
          have := houts 1 (by omega); omega
        have h0_v : (BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 0) * 4).toNat / 4 <
            sO.g_outs.length := by rw [hsO_len.g_outs]; decide
        have h1_v : (4 : BitVec 64).toNat / 4 < sO.g_outs.length := by
          rw [hsO_len.g_outs]; decide
        have h1_v' : (BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 1) * 4).toNat / 4 = 1 := by decide
        have h0_idx : (BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 0) * 4).toNat / 4 = 0 := by
          decide
        have hgo0 : sO.g_outs[(BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 0) * 4).toNat / 4]'
            h0_v = s.g_outs.getD 0 0#32 := by
          rw [d_getD_eq_getElem s.g_outs 0#32
            (by rw [← show sO.g_outs = s.g_outs by rw [hsO_eq], hsO_len.g_outs]; decide)]
          simp only [show sO.g_outs = s.g_outs by rw [hsO_eq]]; rfl
        have hgo1 : sO.g_outs[(4 : BitVec 64).toNat / 4]'h1_v = s.g_outs.getD 1 0#32 := by
          rw [d_getD_eq_getElem s.g_outs 0#32
            (by rw [← show sO.g_outs = s.g_outs by rw [hsO_eq], hsO_len.g_outs]; decide)]
          simp only [show sO.g_outs = s.g_outs by rw [hsO_eq]]; rfl
        have hgo1' : sO.g_outs[1]'(by rw [hsO_len.g_outs]; decide) = s.g_outs.getD 1 0#32 := hgo1
        have hgo0' : sO.g_outs[0]'(by rw [hsO_len.g_outs]; decide) = s.g_outs.getD 0 0#32 := hgo0
        have hst0_sw : (BitVec.setWidth 64
            (sO.g_outs[(BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 0) * 4).toNat / 4]'h0_v)
            ).toNat < partnerArr.length := by
          rw [bv64_sw_toNat, hgo0]; exact ho0_lt
        have hst0_u :
            (sO.g_outs[(BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 0) * 4).toNat / 4]'h0_v).toNat <
            partnerArr.length := by
          rw [hgo0]; exact ho0_lt
        rw [← show sO.partner = s.partner by rw [hsO_eq]] at hmO
        c0_hstep
        have hst1_sw : (BitVec.setWidth 64 (sO.g_outs[(4 : BitVec 64).toNat / 4]'h1_v)).toNat <
            (partnerArr.set (BitVec.setWidth 64
              (sO.g_outs[(BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 0) * 4).toNat / 4]'h0_v)
              ).toNat (sO.g_outs[(4 : BitVec 64).toNat / 4]'h1_v)).length := by
          simp only [List.length_set]; rw [bv64_sw_toNat, hgo1]; exact ho1_lt
        have hst1_u : (sO.g_outs[(4 : BitVec 64).toNat / 4]'h1_v).toNat <
            (partnerArr.set (BitVec.setWidth 64
              (sO.g_outs[(BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 0) * 4).toNat / 4]'h0_v)
              ).toNat (sO.g_outs[(4 : BitVec 64).toNat / 4]'h1_v)).length := by
          simp only [List.length_set]; rw [hgo1]; exact ho1_lt
        c0_hsteps_nogrp
        let o0 := s.g_outs.getD 0 0#32
        let o1 := s.g_outs.getD 1 0#32
        let pa' := (partnerArr.set o0.toNat o1).set o1.toNat o0
        refine hJs () _ (hQ true sO rO rN pa' gY gL gH rM rL rH rP _
          hsnO hsptO hsO_eq hrO_l hrN_l (by simp [pa']) hgY_l hgL_l hgH_l
          hrM_l hrL_l hrH_l hrP_l
          (fun _ => ⟨hTotO, hSyO, fun r hr => (hSlO r hr).2, hRsSortedO, fun ρ => ?_⟩) (by
            simp only [bv64_sw_toNat, h1_v', h0_idx] at *
            rw [show (BitVec.toNat 4 / 4 : Nat) = 1 from by decide] at *
            rw [hgo0', hgo1', show sO.partner = s.partner by rw [hsO_eq]] at *
            exact sep_cast ‹_› (by ac_rfl)))
        · refine ⟨?_, by rw [show sO.n_out = s.n_out by rw [hsO_eq]]; exact hRepO ρ⟩
          obtain ⟨t, _, ht64, hrowT⟩ := hrow ρ
          have hno := gate_partner_no_both hand0 ht64
          rw [hrowT.2 0 (by omega), hrowT.2 1 (by omega)] at hno
          exact partnerRep_set_pair (hRep ρ).1 (houts 0 (by omega)) (houts 1 (by omega))
            (houts_ne hnout2) hno
      · exact hJs () _ (hQ true sO rO rN partnerArr gY gL gH rM rL rH rP mO
          hsnO hsptO hsO_eq hrO_l hrN_l rfl hgY_l hgL_l hgH_l
          hrM_l hrL_l hrH_l hrP_l
          (fun _ => ⟨hTotO, hSyO, fun r hr => (hSlO r hr).2, hRsSortedO, fun ρ =>
            ⟨(hRep ρ).1, by rw [show sO.n_out = s.n_out by rw [hsO_eq]]; exact hRepO ρ⟩⟩) hmO)
  · intro J hJ
    c0_hsteps
    refine hJ nout.toNat (j0, 0#32, ()) m
      ⟨Nat.zero_le _, Nat.sub_zero _, s, ruleOff, ruleN, gsy, gcl, gch, rsM, rsL, rsH, rsPool,
       hrsn, hrspt, by cases s; rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hTot, id,
       fun r hr => ⟨(hRep (fun _ => false)).2.2.2.2.2.2.2.2.2.1 r hr, hRsOk r hr⟩,
       hRsSorted, fun ρ => (hRep ρ).2, hm⟩

theorem ar_do_gate_dense_wp {Γ : LeanQbe.T.Env}
    (hDzero : ∀ xs m Q X, arDzeroSpec xs m Q X → Γ "ar_dzero" [i64] [] xs m Q X)
    (hDlit : ∀ xs m Q X, arDlitSpec xs m Q X → Γ "ar_dlit" [i64, i32, i32] [] xs m Q X)
    (hDmul : ∀ xs m Q X, arDmulSpec xs m Q X → Γ "ar_dmul" [i64, i64, i64] [] xs m Q X)
    (hDaxpy : ∀ xs m Q X, arDaxpySpec xs m Q X → Γ "ar_daxpy" [i64, i64, i64] [] xs m Q X)
    (hDcanon : ∀ xs m Q X, arDcanonSpec xs m Q X → Γ "ar_dcanon" [i64, i64] [i32] xs m Q X)
    (hCadd : ∀ xs m Q X, arCaddSpec xs m Q X →
      Γ "ar_cadd" [i64, i64, i64, i64, i64] [i64, i64] xs m Q X)
    (hInstall : ∀ xs m Q X, arInstallRuleSpec xs m Q X →
      Γ "ar_install_rule" [i64, i32, i32] [.bool] xs m Q X)
    {cx : BitVec 64} {kraw nout nin nl : BitVec 32} {s : ArCtxState} {g : Aig}
    {bindArr ruleOff ruleN partnerArr : List (BitVec 32)}
    {d0 d1 d2 d3 d4 d5 d6 d7 dRest : List (BitVec 64)}
    {gsy : List (BitVec 32)} {gcl gch : List (BitVec 64)}
    {rsM : List (BitVec 32)} {rsL rsH : List (BitVec 64)} {rsPool : List (BitVec 32)} {j0 : Val i32}
    {F : Mem 64 → Prop} {m : Mem 64} {Q : Post [.bool]} {X : XPost}
    (hkraw : (kraw &&& 255#32) = 6#32 → nout = 2#32)
    (hnout : nout = 1#32 ∨ nout = 2#32) (hnin : nin = 2#32 ∨ nin = 3#32)
    (hnl1 : 1 ≤ nl.toNat) (hnl6 : nl.toNat ≤ 6)
    (hnn30 : s.n_nets.toNat ≤ 0x3FFFFFFF) (hrcap30 : s.rs_cap.toNat < 2 ^ 30)
    (hrpcap32 : s.rs_pcap.toNat < 2 ^ 32) (hmasks : MasksOk s.n_out.toNat s.mlo s.mhi)
    (hnout1 : 1 ≤ s.n_out.toNat)
    (hd0 : d0.length = 16) (hd1 : d1.length = 16) (hd2 : d2.length = 16) (hd3 : d3.length = 16)
    (hd4 : d4.length = 16) (hd5 : d5.length = 16) (hd6 : d6.length = 16) (hd7 : d7.length = 16)
    (hgsy : 85 ≤ gsy.length) (hgcl : 16 ≤ gcl.length) (hgch : 16 ≤ gch.length)
    (houts : ∀ o < nout.toNat, (s.g_outs.getD o 0#32).toNat < s.n_nets.toNat)
    (houts_ne : nout.toNat = 2 → s.g_outs.getD 0 0#32 ≠ s.g_outs.getD 1 0#32)
    (hins : ∀ j < nin.toNat, (s.g_innet.getD j 0#32).toNat < s.n_nets.toNat)
    (hrow : ∀ ρ : Nat → Bool, ∃ t < 2 ^ nl.toNat, t < 64 ∧ GateRowOk g bindArr nin nout s ρ t)
    (hVs : ∀ j < 4, (s.g_vs.getD j 0#32).toNat / 2 < s.n_nets.toNat)
    (hrsn : s.rs_n.toNat ≤ s.rs_cap.toNat) (hrspt : s.rs_ptop.toNat ≤ s.rs_pcap.toNat)
    (hTot : monoTotalWords rsPool rsM s.rs_n.toNat ≤ s.rs_ptop.toNat)
    (hRsOk : ∀ r < s.rs_n.toNat,
      (rsPool.getD (rsM.getD r 0#32).toNat 0#32).toNat + 1 < 2 ^ 32)
    (hRsSorted : RulesSorted rsPool rsM s.rs_n.toNat)
    (hRep : ∀ ρ : Nat → Bool,
      PartnerRep (cSig g ρ bindArr) s.n_nets.toNat partnerArr ∧
      RulesRep s.n_out.toNat (cSig g ρ bindArr) s ruleOff ruleN rsM rsL rsH rsPool)
    (hm : (arCtxMem cx s ⋆ array64 s.dense d0 ⋆ array64 (s.dense + 128#64) d1 ⋆
      array64 (s.dense + 256#64) d2 ⋆ array64 (s.dense + 384#64) d3 ⋆
      array64 (s.dense + 512#64) d4 ⋆ array64 (s.dense + 640#64) d5 ⋆
      array64 (s.dense + 768#64) d6 ⋆ array64 (s.dense + 896#64) d7 ⋆
      array64 (s.dense + 1024#64) dRest ⋆
      arrayPad i32 s.gsy gsy ⋆ array64 s.gcl gcl ⋆ array64 s.gch gch ⋆
      array (t := i32) s.rule_off ruleOff ⋆ array (t := i32) s.rule_n ruleN ⋆
      array (t := i32) s.partner partnerArr ⋆ rsMem s rsM rsL rsH rsPool ⋆ F) m)
    (hQ : ∀ ok s' ruleOff' ruleN' partnerArr' dense' gsy' gcl' gch' rsM' rsL' rsH' rsPool' m',
      s'.rs_n.toNat ≤ s.rs_cap.toNat → s'.rs_ptop.toNat ≤ s.rs_pcap.toNat →
      s' = { s with rs_n := s'.rs_n, rs_ptop := s'.rs_ptop } →
      ruleOff'.length = ruleOff.length → ruleN'.length = ruleN.length →
      partnerArr'.length = partnerArr.length → dense'.length = 128 + dRest.length →
      gsy'.length = gsy.length → gcl'.length = gcl.length → gch'.length = gch.length →
      rsM'.length = rsM.length → rsL'.length = rsL.length →
      rsH'.length = rsH.length → rsPool'.length = rsPool.length →
      (ok = true →
        monoTotalWords rsPool' rsM' s'.rs_n.toNat ≤ s'.rs_ptop.toNat ∧
        (SymsBound rsPool rsM s.rs_n.toNat s.n_nets.toNat →
          SymsBound rsPool' rsM' s'.rs_n.toNat s.n_nets.toNat) ∧
        (∀ r < s'.rs_n.toNat,
          (rsPool'.getD (rsM'.getD r 0#32).toNat 0#32).toNat + 1 < 2 ^ 32) ∧
        RulesSorted rsPool' rsM' s'.rs_n.toNat ∧
        (∀ ρ, PartnerRep (cSig g ρ bindArr) s.n_nets.toNat partnerArr' ∧
          RulesRep s'.n_out.toNat (cSig g ρ bindArr) s' ruleOff' ruleN' rsM' rsL' rsH' rsPool')) →
      (arCtxMem cx s' ⋆ array64 s.dense dense' ⋆ arrayPad i32 s.gsy gsy' ⋆
        array64 s.gcl gcl' ⋆ array64 s.gch gch' ⋆ array (t := i32) s.rule_off ruleOff' ⋆
        array (t := i32) s.rule_n ruleN' ⋆ array (t := i32) s.partner partnerArr' ⋆
        rsMem s' rsM' rsL' rsH' rsPool' ⋆ F) m' →
      Q (ok, ⟨⟩) m') :
    wp Γ Q X (gateDenseExpr cx kraw nout nin nl j0) m := by
  let Rest : Mem 64 → Prop := array64 (s.dense + 1024#64) dRest ⋆
    arrayPad i32 s.gsy gsy ⋆ array64 s.gcl gcl ⋆ array64 s.gch gch ⋆
    array (t := i32) s.rule_off ruleOff ⋆ array (t := i32) s.rule_n ruleN ⋆
    array (t := i32) s.partner partnerArr ⋆ rsMem s rsM rsL rsH rsPool ⋆ F
  let DenseInv (m' : Mem 64) : Prop := ∃ a0 a1 a2 a3 a4 a5 a6 a7 : List (BitVec 64),
    a0.length = 16 ∧ a1.length = 16 ∧ a2.length = 16 ∧ a3.length = 16 ∧
    a4.length = 16 ∧ a5.length = 16 ∧ a6.length = 16 ∧ a7.length = 16 ∧
    (arCtxMem cx s ⋆ array64 s.dense a0 ⋆ array64 (s.dense + 128#64) a1 ⋆
      array64 (s.dense + 256#64) a2 ⋆ array64 (s.dense + 384#64) a3 ⋆
      array64 (s.dense + 512#64) a4 ⋆ array64 (s.dense + 640#64) a5 ⋆
      array64 (s.dense + 768#64) a6 ⋆ array64 (s.dense + 896#64) a7 ⋆ Rest) m'
  have hm_base : (arCtxMem cx s ⋆ array64 s.dense d0 ⋆ array64 (s.dense + 128#64) d1 ⋆
      array64 (s.dense + 256#64) d2 ⋆ array64 (s.dense + 384#64) d3 ⋆
      array64 (s.dense + 512#64) d4 ⋆ array64 (s.dense + 640#64) d5 ⋆
      array64 (s.dense + 768#64) d6 ⋆ array64 (s.dense + 896#64) d7 ⋆ Rest) m :=
    sep_cast hm (by dsimp only [Rest]; ac_rfl)
  apply head_wp_add (va := cx) (vb := (176 : BitVec 64))
  · rfl
  · rfl
  c0_hsteps_nogrp
  refine dense_dlit hDlit (arCtxMem cx s ⋆ array64 (s.dense + 128#64) d1 ⋆
      array64 (s.dense + 256#64) d2 ⋆ array64 (s.dense + 384#64) d3 ⋆
      array64 (s.dense + 512#64) d4 ⋆ array64 (s.dense + 640#64) d5 ⋆
      array64 (s.dense + 768#64) d6 ⋆ array64 (s.dense + 896#64) d7 ⋆ Rest)
    (by decide) hd0 ?_ fun a0 _ ha0 hm0 => ?_
  · dsimp only [Arg.val] at hm_base ⊢; exact sep_cast hm_base (by ac_rfl)
  c0_hsteps_nogrp
  refine dense_dlit hDlit (arCtxMem cx s ⋆ array64 s.dense a0 ⋆
      array64 (s.dense + 256#64) d2 ⋆ array64 (s.dense + 384#64) d3 ⋆
      array64 (s.dense + 512#64) d4 ⋆ array64 (s.dense + 640#64) d5 ⋆
      array64 (s.dense + 768#64) d6 ⋆ array64 (s.dense + 896#64) d7 ⋆ Rest)
    (by decide) hd1 ?_ fun a1 _ ha1 hm1 => ?_
  · simp only [Arg.val, doff16] at hm0 ⊢; exact sep_cast hm0 (by ac_rfl)
  refine wp_join_group (fun _ m2 =>
    ∃ a2 : List (BitVec 64), a2.length = 16 ∧
      (arCtxMem cx s ⋆ array64 s.dense a0 ⋆ array64 (s.dense + 128#64) a1 ⋆
        array64 (s.dense + 256#64) a2 ⋆ array64 (s.dense + 384#64) d3 ⋆
        array64 (s.dense + 512#64) d4 ⋆ array64 (s.dense + 640#64) d5 ⋆
        array64 (s.dense + 768#64) d6 ⋆ array64 (s.dense + 896#64) d7 ⋆ Rest) m2) ?_ ?_
  · rintro _ _ m2 ⟨a2, ha2, hm2⟩
    c0_hsteps_nogrp
    refine dense_dzero hDzero (arCtxMem cx s ⋆ array64 s.dense a0 ⋆
        array64 (s.dense + 128#64) a1 ⋆ array64 (s.dense + 256#64) a2 ⋆
        array64 (s.dense + 384#64) d3 ⋆ array64 (s.dense + 512#64) d4 ⋆
        array64 (s.dense + 640#64) d5 ⋆ array64 (s.dense + 768#64) d6 ⋆ Rest)
      hd7 ?_ fun a7 m7 ha7 hm7 => ?_
    · simp only [Arg.val, doff112] at hm2 ⊢; exact sep_cast hm2 (by ac_rfl)
    refine wp_join_group (fun _ mJ => DenseInv mJ) ?_ ?_
    · rintro _ _ mJ ⟨b0, b1, b2, b3, b4, b5, b6, b7, hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hmJ⟩
      let F_eval : Mem 64 → Prop :=
        array64 s.dense b0 ⋆ array64 (s.dense + 128#64) b1 ⋆
        array64 (s.dense + 256#64) b2 ⋆ array64 (s.dense + 384#64) b3 ⋆
        array64 (s.dense + 512#64) b4 ⋆ array64 (s.dense + 640#64) b5 ⋆
        array64 (s.dense + 1024#64) dRest ⋆ F
      change wp Γ Q X (gateEvalExpr cx s.dense kraw nout nin nl j0) mJ
      refine ar_do_gate_eval_wp hDcanon hCadd hInstall (F := F_eval) hkraw hnout hnin hnl1 hnl6
        hnn30 hrcap30 hrpcap32 hmasks hnout1 hb6 hb7 hgsy hgcl hgch houts houts_ne hins hrow hVs
        hrsn hrspt hTot hRsOk hRsSorted hRep (sep_cast hmJ (by dsimp only [Rest, F_eval]; ac_rfl))
        ?_
      intro ok s' ro' rn' pa' gsy' gcl' gch' rm' rl' rh' rp' m' h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
        h12 h13 hok hm'
      have hmg := dense_merge8 s.dense b0 b1 b2 b3 b4 b5 b6 b7 dRest hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7
      refine hQ ok s' ro' rn' pa' (b0 ++ b1 ++ b2 ++ b3 ++ b4 ++ b5 ++ b6 ++ b7 ++ dRest)
        gsy' gcl' gch' rm' rl' rh' rp' m' h1 h2 h3 h4 h5 h6 hmg.1 h7 h8 h9 h10 h11 h12 h13 hok ?_
      rw [← hmg.2]
      exact sep_cast hm' (by dsimp only [F_eval]; ac_rfl)
    · intro J hJ
      c0_hsteps_nogrp
      · refine dense_dmul hDmul (arCtxMem cx s ⋆ array64 (s.dense + 256#64) a2 ⋆
            array64 (s.dense + 384#64) d3 ⋆ array64 (s.dense + 512#64) d4 ⋆
            array64 (s.dense + 640#64) d5 ⋆ array64 (s.dense + 896#64) a7 ⋆ Rest)
          ha0 ha1 hd6 ?_ fun b6 _ hb6 hm_b => ?_
        · simp only [Arg.val, doff16, doff96] at hm7 ⊢; exact sep_cast hm7 (by ac_rfl)
        exact hJ () _ ⟨a0, a1, a2, d3, d4, d5, b6, a7, ha0, ha1, ha2, hd3, hd4, hd5, hb6, ha7,
          by simp only [Arg.val, doff16, doff96] at hm_b ⊢; exact sep_cast hm_b (by ac_rfl)⟩
      · refine wp_join_group (fun _ m3 => DenseInv m3) (fun _ _ m3 hm3 => hJ () m3 hm3)
          fun J2 hJ2 => by
          refine wp_join_group (fun _ m4 => m4 = m7) ?_ ?_
          · rintro _ _ _ rfl
            c0_hsteps_nogrp
            refine dense_dmul hDmul (arCtxMem cx s ⋆ array64 (s.dense + 256#64) a2 ⋆
                array64 (s.dense + 512#64) d4 ⋆ array64 (s.dense + 640#64) d5 ⋆
                array64 (s.dense + 768#64) d6 ⋆ array64 (s.dense + 896#64) a7 ⋆ Rest)
              ha0 ha1 hd3 ?_ fun b3 _ hb3 hma => ?_
            · simp only [Arg.val, doff16, doff48] at hm7 ⊢; exact sep_cast hm7 (by ac_rfl)
            refine dense_dzero hDzero (arCtxMem cx s ⋆ array64 s.dense a0 ⋆
                array64 (s.dense + 128#64) a1 ⋆ array64 (s.dense + 256#64) a2 ⋆
                array64 (s.dense + 384#64) b3 ⋆ array64 (s.dense + 512#64) d4 ⋆
                array64 (s.dense + 640#64) d5 ⋆ array64 (s.dense + 896#64) a7 ⋆ Rest)
              hd6 ?_ fun b6 _ hb6 hmb => ?_
            · simp only [Arg.val, doff16, doff48, doff96] at hma ⊢; exact sep_cast hma (by ac_rfl)
            refine dense_daxpy hDaxpy (arCtxMem cx s ⋆ array64 (s.dense + 128#64) a1 ⋆
                array64 (s.dense + 256#64) a2 ⋆ array64 (s.dense + 384#64) b3 ⋆
                array64 (s.dense + 512#64) d4 ⋆ array64 (s.dense + 640#64) d5 ⋆
                array64 (s.dense + 896#64) a7 ⋆ Rest)
              hb6 ha0 ?_ fun b6' _ hb6' hmc => ?_
            · simp only [Arg.val, doff96] at hmb ⊢; exact sep_cast hmb (by ac_rfl)
            refine dense_daxpy hDaxpy (arCtxMem cx s ⋆ array64 s.dense a0 ⋆
                array64 (s.dense + 256#64) a2 ⋆ array64 (s.dense + 384#64) b3 ⋆
                array64 (s.dense + 512#64) d4 ⋆ array64 (s.dense + 640#64) d5 ⋆
                array64 (s.dense + 896#64) a7 ⋆ Rest)
              hb6' ha1 ?_ fun b6'' _ hb6'' hmd => ?_
            · simp only [Arg.val, doff16, doff96] at hmc ⊢; exact sep_cast hmc (by ac_rfl)
            refine wp_join_group (fun ⟨_, _⟩ m5 => DenseInv m5 ∧
                ∃ d6c : List (BitVec 64), d6c.length = 16) ?_ ?_
            · rintro _ ⟨_, _⟩ m5 ⟨⟨c0, c1, c2, c3, c4, c5, c6, c7, hc0, hc1, hc2, hc3, hc4,
                hc5, hc6, hc7, hm5⟩, _⟩
              c0_hsteps_nogrp
              refine dense_daxpy hDaxpy (arCtxMem cx s ⋆ array64 s.dense c0 ⋆
                  array64 (s.dense + 128#64) c1 ⋆ array64 (s.dense + 256#64) c2 ⋆
                  array64 (s.dense + 512#64) c4 ⋆ array64 (s.dense + 640#64) c5 ⋆
                  array64 (s.dense + 896#64) c7 ⋆ Rest)
                hc6 hc3 ?_ fun c6' _ hc6' hmf => ?_
              · simp only [Arg.val, doff48, doff96] at hm5 ⊢; exact sep_cast hm5 (by ac_rfl)
              exact hJ2 () _ ⟨c0, c1, c2, c3, c4, c5, c6', c7, hc0, hc1, hc2, hc3, hc4, hc5,
                hc6', hc7,
                by simp only [Arg.val, doff48, doff96] at hmf ⊢; exact sep_cast hmf (by ac_rfl)⟩
            · intro J4 hJ4
              c0_hsteps_nogrp
              · exact hJ4 ((-1#64), ()) _ ⟨⟨a0, a1, a2, b3, d4, d5, b6'', a7, ha0, ha1, ha2, hb3,
                  hd4, hd5, hb6'', ha7, by
                    simp only [Arg.val, doff16, doff96] at hmd ⊢; exact sep_cast hmd (by ac_rfl)⟩,
                  b6'', hb6''⟩
              · exact hJ4 ((-2#64), ()) _ ⟨⟨a0, a1, a2, b3, d4, d5, b6'', a7, ha0, ha1, ha2, hb3,
                  hd4, hd5, hb6'', ha7, by
                    simp only [Arg.val, doff16, doff96] at hmd ⊢; exact sep_cast hmd (by ac_rfl)⟩,
                  b6'', hb6''⟩
          · intro J3 hJ3
            c0_hsteps_nogrp
            · exact hJ3 () m7 rfl
            · exact hJ3 () m7 rfl
            · refine wp_join_group (fun _ m4o => DenseInv m4o)
                (fun _ _ m4o hm4o => hJ2 () m4o hm4o) fun J4o hJ4o => by
                refine wp_join_group (fun _ m5 => m5 = m7) ?_ ?_
                · rintro _ _ _ rfl
                  c0_hsteps_nogrp
                  refine dense_dzero hDzero (arCtxMem cx s ⋆ array64 s.dense a0 ⋆
                      array64 (s.dense + 128#64) a1 ⋆ array64 (s.dense + 256#64) a2 ⋆
                      array64 (s.dense + 384#64) d3 ⋆ array64 (s.dense + 512#64) d4 ⋆
                      array64 (s.dense + 640#64) d5 ⋆ array64 (s.dense + 896#64) a7 ⋆ Rest)
                    hd6 ?_ fun c6 _ hc6 hmA => ?_
                  · simp only [Arg.val, doff96] at hm7 ⊢; exact sep_cast hm7 (by ac_rfl)
                  refine dense_dmul hDmul (arCtxMem cx s ⋆ array64 (s.dense + 256#64) a2 ⋆
                      array64 (s.dense + 512#64) d4 ⋆ array64 (s.dense + 640#64) d5 ⋆
                      array64 (s.dense + 768#64) c6 ⋆ array64 (s.dense + 896#64) a7 ⋆ Rest)
                    ha0 ha1 hd3 ?_ fun c3 _ hc3 hmB => ?_
                  · simp only [Arg.val, doff16, doff48, doff96] at hmA ⊢
                    exact sep_cast hmA (by ac_rfl)
                  refine dense_daxpy hDaxpy (arCtxMem cx s ⋆ array64 s.dense a0 ⋆
                      array64 (s.dense + 128#64) a1 ⋆ array64 (s.dense + 256#64) a2 ⋆
                      array64 (s.dense + 512#64) d4 ⋆ array64 (s.dense + 640#64) d5 ⋆
                      array64 (s.dense + 896#64) a7 ⋆ Rest) hc6 hc3 ?_ fun c6_1 _ hc6_1 hmC => ?_
                  · simp only [Arg.val, doff16, doff48, doff96] at hmB ⊢
                    exact sep_cast hmB (by ac_rfl)
                  refine dense_dmul hDmul (arCtxMem cx s ⋆ array64 s.dense a0 ⋆
                      array64 (s.dense + 128#64) a1 ⋆ array64 (s.dense + 512#64) d4 ⋆
                      array64 (s.dense + 768#64) c6_1 ⋆ array64 (s.dense + 896#64) a7 ⋆ Rest)
                    hc3 ha2 hd5 ?_ fun c5 _ hc5 hmD => ?_
                  · simp only [Arg.val, doff32, doff48, doff80, doff96] at hmC ⊢
                    exact sep_cast hmC (by ac_rfl)
                  refine dense_dmul hDmul (arCtxMem cx s ⋆ array64 (s.dense + 128#64) a1 ⋆
                      array64 (s.dense + 384#64) c3 ⋆ array64 (s.dense + 640#64) c5 ⋆
                      array64 (s.dense + 768#64) c6_1 ⋆ array64 (s.dense + 896#64) a7 ⋆ Rest)
                    ha0 ha2 hd4 ?_ fun c4 _ hc4 hmE => ?_
                  · simp only [Arg.val, doff32, doff48, doff64, doff80] at hmD ⊢
                    exact sep_cast hmD (by ac_rfl)
                  refine dense_daxpy hDaxpy (arCtxMem cx s ⋆ array64 s.dense a0 ⋆
                      array64 (s.dense + 128#64) a1 ⋆ array64 (s.dense + 256#64) a2 ⋆
                      array64 (s.dense + 384#64) c3 ⋆ array64 (s.dense + 640#64) c5 ⋆
                      array64 (s.dense + 896#64) a7 ⋆ Rest) hc6_1 hc4 ?_ fun c6_2 _ hc6_2 hmF => ?_
                  · simp only [Arg.val, doff32, doff64, doff96] at hmE ⊢
                    exact sep_cast hmE (by ac_rfl)
                  refine dense_dmul hDmul (arCtxMem cx s ⋆ array64 s.dense a0 ⋆
                      array64 (s.dense + 384#64) c3 ⋆ array64 (s.dense + 640#64) c5 ⋆
                      array64 (s.dense + 768#64) c6_2 ⋆ array64 (s.dense + 896#64) a7 ⋆ Rest)
                    ha1 ha2 hc4 ?_ fun c4' _ hc4' hmG => ?_
                  · simp only [Arg.val, doff16, doff32, doff64, doff96] at hmF ⊢
                    exact sep_cast hmF (by ac_rfl)
                  refine dense_daxpy hDaxpy (arCtxMem cx s ⋆ array64 s.dense a0 ⋆
                      array64 (s.dense + 128#64) a1 ⋆ array64 (s.dense + 256#64) a2 ⋆
                      array64 (s.dense + 384#64) c3 ⋆ array64 (s.dense + 640#64) c5 ⋆
                      array64 (s.dense + 896#64) a7 ⋆ Rest) hc6_2 hc4' ?_ fun c6_3 _ hc6_3 hmH => ?_
                  · simp only [Arg.val, doff16, doff32, doff64, doff96] at hmG ⊢
                    exact sep_cast hmG (by ac_rfl)
                  refine wp_join_group (fun _ mW => DenseInv mW)
                    (fun _ _ mW hmW => hJ4o () mW hmW) fun J5 hJ5 => by
                    c0_hsteps_nogrp
                    · refine dense_dzero hDzero (arCtxMem cx s ⋆ array64 s.dense a0 ⋆
                          array64 (s.dense + 128#64) a1 ⋆ array64 (s.dense + 256#64) a2 ⋆
                          array64 (s.dense + 512#64) c4' ⋆ array64 (s.dense + 640#64) c5 ⋆
                          array64 (s.dense + 768#64) c6_3 ⋆ array64 (s.dense + 896#64) a7 ⋆ Rest)
                        hc3 ?_ fun c3_1 _ hc3_1 hmI => ?_
                      · simp only [Arg.val, doff48, doff64, doff96] at hmH ⊢
                        exact sep_cast hmH (by ac_rfl)
                      refine dense_daxpy hDaxpy (arCtxMem cx s ⋆ array64 (s.dense + 128#64) a1 ⋆
                          array64 (s.dense + 256#64) a2 ⋆ array64 (s.dense + 512#64) c4' ⋆
                          array64 (s.dense + 640#64) c5 ⋆ array64 (s.dense + 768#64) c6_3 ⋆
                          array64 (s.dense + 896#64) a7 ⋆ Rest)
                        hc3_1 ha0 ?_ fun c3_2 _ hc3_2 hmJ2 => ?_
                      · simp only [Arg.val, doff48] at hmI ⊢; exact sep_cast hmI (by ac_rfl)
                      refine dense_daxpy hDaxpy (arCtxMem cx s ⋆ array64 s.dense a0 ⋆
                          array64 (s.dense + 256#64) a2 ⋆ array64 (s.dense + 512#64) c4' ⋆
                          array64 (s.dense + 640#64) c5 ⋆ array64 (s.dense + 768#64) c6_3 ⋆
                          array64 (s.dense + 896#64) a7 ⋆ Rest)
                        hc3_2 ha1 ?_ fun c3_3 _ hc3_3 hmK => ?_
                      · simp only [Arg.val, doff16, doff48] at hmJ2 ⊢
                        exact sep_cast hmJ2 (by ac_rfl)
                      refine dense_daxpy hDaxpy (arCtxMem cx s ⋆ array64 s.dense a0 ⋆
                          array64 (s.dense + 128#64) a1 ⋆ array64 (s.dense + 512#64) c4' ⋆
                          array64 (s.dense + 640#64) c5 ⋆ array64 (s.dense + 768#64) c6_3 ⋆
                          array64 (s.dense + 896#64) a7 ⋆ Rest)
                        hc3_3 ha2 ?_ fun c3_4 _ hc3_4 hmL => ?_
                      · simp only [Arg.val, doff16, doff32, doff48] at hmK ⊢
                        exact sep_cast hmK (by ac_rfl)
                      refine dense_daxpy hDaxpy (arCtxMem cx s ⋆ array64 s.dense a0 ⋆
                          array64 (s.dense + 128#64) a1 ⋆ array64 (s.dense + 256#64) a2 ⋆
                          array64 (s.dense + 512#64) c4' ⋆ array64 (s.dense + 640#64) c5 ⋆
                          array64 (s.dense + 896#64) a7 ⋆ Rest)
                        hc3_4 hc6_3 ?_ fun c3_5 _ hc3_5 hmM => ?_
                      · simp only [Arg.val, doff32, doff48, doff96] at hmL ⊢
                        exact sep_cast hmL (by ac_rfl)
                      refine dense_daxpy hDaxpy (arCtxMem cx s ⋆ array64 s.dense a0 ⋆
                          array64 (s.dense + 128#64) a1 ⋆ array64 (s.dense + 256#64) a2 ⋆
                          array64 (s.dense + 512#64) c4' ⋆ array64 (s.dense + 768#64) c6_3 ⋆
                          array64 (s.dense + 896#64) a7 ⋆ Rest)
                        hc3_5 hc5 ?_ fun c3_6 _ hc3_6 hmN => ?_
                      · simp only [Arg.val, doff48, doff80, doff96] at hmM ⊢
                        exact sep_cast hmM (by ac_rfl)
                      refine wp_loop_group (fun kq ⟨q, _⟩ mQ => q.toNat ≤ 16 ∧
                        kq = 16 - q.toNat ∧ ∃ r6 : List (BitVec 64), r6.length = 16 ∧
                        (arCtxMem cx s ⋆ array64 s.dense a0 ⋆ array64 (s.dense + 128#64) a1 ⋆
                          array64 (s.dense + 256#64) a2 ⋆ array64 (s.dense + 384#64) c3_6 ⋆
                          array64 (s.dense + 512#64) c4' ⋆ array64 (s.dense + 640#64) c5 ⋆
                          array64 (s.dense + 768#64) r6 ⋆ array64 (s.dense + 896#64) a7 ⋆
                          Rest) mQ)
                        (fun Jq kq ⟨q, _⟩ mQ hrecQ hinv => by
                          rcases hinv with ⟨hq_le, rfl, r6, hr6, hmQ⟩
                          dsimp only at hrecQ hq_le hmQ ⊢
                          c0_hsteps_nogrp
                          · have hq_lt : q.toNat < 16 := hc
                            have hq36 : (BitVec.setWidth 64 q).toNat < c3_6.length := by
                              rw [bv64_sw_toNat, hc3_6]; exact hq_lt
                            have hqr6 : (BitVec.setWidth 64 q).toNat < r6.length := by
                              rw [bv64_sw_toNat]; omega
                            refine head_wp_load
                              (addr := s.dense + 384#64 + BitVec.setWidth 64 q * 8)
                              (by simp only [Arg.val, doff48])
                              (c0_load_array64 (R := arCtxMem cx s ⋆ array64 s.dense a0 ⋆
                                array64 (s.dense + 128#64) a1 ⋆ array64 (s.dense + 256#64) a2 ⋆
                                array64 (s.dense + 512#64) c4' ⋆ array64 (s.dense + 640#64) c5 ⋆
                                array64 (s.dense + 768#64) r6 ⋆ array64 (s.dense + 896#64) a7 ⋆
                                Rest) (sep_cast hmQ (by ac_rfl)) hq36) ?_
                            refine head_wp_store
                              (addr := s.dense + 768#64 + BitVec.setWidth 64 q * 8)
                              rfl (by simp only [Arg.val, doff96])
                              (c0_store_array64 (R := arCtxMem cx s ⋆ array64 s.dense a0 ⋆
                                array64 (s.dense + 128#64) a1 ⋆ array64 (s.dense + 256#64) a2 ⋆
                                array64 (s.dense + 384#64) c3_6 ⋆ array64 (s.dense + 512#64) c4' ⋆
                                array64 (s.dense + 640#64) c5 ⋆ array64 (s.dense + 896#64) a7 ⋆
                                Rest) _ (sep_cast hmQ (by ac_rfl)) hqr6) fun mQ' hmQ' => ?_
                            c0_hsteps_nogrp
                            let r6' := r6.set (BitVec.setWidth 64 q).toNat
                              (c3_6[(BitVec.setWidth 64 q).toNat]'hq36)
                            refine hrecQ (16 - (q + 1).toNat) (q + 1, ()) mQ'
                              (by rw [bv32_add1_toNat (by omega)]; omega)
                              ⟨by rw [bv32_add1_toNat (by omega)]; omega, rfl, r6',
                                by simp [r6', hr6], sep_cast hmQ' (by ac_rfl)⟩
                          · exact hJ5 () mQ ⟨a0, a1, a2, c3_6, c4', c5, r6, a7, ha0, ha1, ha2,
                              hc3_6, hc4', hc5, hr6, ha7, hmQ⟩)
                        (fun Jq hJq => by
                          c0_hsteps
                          exact hJq 16 (0#32, ()) _ ⟨Nat.zero_le _, rfl, c6_3, hc6_3, by
                            simp only [Arg.val, doff48, doff80] at hmN ⊢
                            exact sep_cast hmN (by ac_rfl)⟩)
                    · refine dense_daxpy hDaxpy (arCtxMem cx s ⋆ array64 s.dense a0 ⋆
                          array64 (s.dense + 128#64) a1 ⋆ array64 (s.dense + 256#64) a2 ⋆
                          array64 (s.dense + 384#64) c3 ⋆ array64 (s.dense + 512#64) c4' ⋆
                          array64 (s.dense + 896#64) a7 ⋆ Rest)
                        hc6_3 hc5 ?_ fun c6_4 _ hc6_4 hmI => ?_
                      · simp only [Arg.val, doff64, doff80, doff96] at hmH ⊢
                        exact sep_cast hmH (by ac_rfl)
                      refine wp_join_group (fun _ mK => DenseInv mK)
                        (fun _ _ mK hmK => hJ5 () mK hmK) fun J6 hJ6 => by
                        c0_hsteps_nogrp
                        · refine dense_daxpy hDaxpy (arCtxMem cx s ⋆ array64 (s.dense + 128#64) a1 ⋆
                              array64 (s.dense + 256#64) a2 ⋆ array64 (s.dense + 384#64) c3 ⋆
                              array64 (s.dense + 512#64) c4' ⋆ array64 (s.dense + 640#64) c5 ⋆
                              array64 (s.dense + 768#64) c6_4 ⋆ Rest)
                            ha7 ha0 ?_ fun c7_1 _ hc7_1 hmJ2 => ?_
                          · simp only [Arg.val, doff80, doff96, doff112] at hmI ⊢
                            exact sep_cast hmI (by ac_rfl)
                          refine dense_daxpy hDaxpy (arCtxMem cx s ⋆ array64 s.dense a0 ⋆
                              array64 (s.dense + 256#64) a2 ⋆ array64 (s.dense + 384#64) c3 ⋆
                              array64 (s.dense + 512#64) c4' ⋆ array64 (s.dense + 640#64) c5 ⋆
                              array64 (s.dense + 768#64) c6_4 ⋆ Rest)
                            hc7_1 ha1 ?_ fun c7_2 _ hc7_2 hmK => ?_
                          · simp only [Arg.val, doff16, doff112] at hmJ2 ⊢
                            exact sep_cast hmJ2 (by ac_rfl)
                          refine dense_daxpy hDaxpy (arCtxMem cx s ⋆ array64 s.dense a0 ⋆
                              array64 (s.dense + 128#64) a1 ⋆ array64 (s.dense + 384#64) c3 ⋆
                              array64 (s.dense + 512#64) c4' ⋆ array64 (s.dense + 640#64) c5 ⋆
                              array64 (s.dense + 768#64) c6_4 ⋆ Rest)
                            hc7_2 ha2 ?_ fun c7_3 _ hc7_3 hmL => ?_
                          · simp only [Arg.val, doff16, doff32, doff112] at hmK ⊢
                            exact sep_cast hmK (by ac_rfl)
                          dsimp only [Arg.val] at hmL
                          let idx8 := (BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 8)).toNat
                          have hidx8 : idx8 < c7_3.length := by
                            rw [show idx8 = 8 from by decide]; omega
                          have h8_c7 : (BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 8) * 8).toNat /
                              8 < c7_3.length := by
                            rw [show (BitVec.ofNat (OfNat.ofNat 64)
                                (OfNat.ofNat 8) * 8).toNat / 8 = 8 from by decide]; omega
                          c0_hsteps_nogrp
                          let c7_4 := c7_3.set idx8 (c7_3[idx8]'hidx8 + (0 - 2))
                          exact hJ6 () _ (dense_inv_last ha0 ha1 ha2 hc3 hc4' hc5 hc6_4 (a7 := c7_4)
                            (by simp only [Arg.val, doff32, doff112] at *
                                dsimp only [c7_4, idx8]; exact sep_cast ‹_› (by ac_rfl))
                            (by dsimp only [c7_4]; rw [List.length_set]; exact hc7_3))
                        · exact hJ6 () _ ⟨a0, a1, a2, c3, c4', c5, c6_4, a7, ha0, ha1, ha2,
                            hc3, hc4', hc5, hc6_4, ha7, by
                              simp only [Arg.val, doff80, doff96] at hmI ⊢
                              exact sep_cast hmI (by ac_rfl)⟩
                · intro J4 hJ4
                  c0_hsteps_nogrp
                  · exact hJ4 () m7 rfl
                  · exact hJ4 () m7 rfl
                  · exact hJ4 () m7 rfl
                  · refine dense_dmul hDmul (arCtxMem cx s ⋆ array64 (s.dense + 256#64) a2 ⋆
                        array64 (s.dense + 384#64) d3 ⋆ array64 (s.dense + 512#64) d4 ⋆
                        array64 (s.dense + 640#64) d5 ⋆ array64 (s.dense + 896#64) a7 ⋆ Rest)
                      ha0 ha1 hd6 ?_ fun b6 _ hb6 hmA => ?_
                    · simp only [Arg.val, doff16, doff96] at hm7 ⊢; exact sep_cast hm7 (by ac_rfl)
                    refine dense_daxpy hDaxpy (arCtxMem cx s ⋆ array64 (s.dense + 128#64) a1 ⋆
                        array64 (s.dense + 256#64) a2 ⋆ array64 (s.dense + 384#64) d3 ⋆
                        array64 (s.dense + 512#64) d4 ⋆ array64 (s.dense + 640#64) d5 ⋆
                        array64 (s.dense + 768#64) b6 ⋆ Rest) ha7 ha0 ?_ fun b7_1 _ hb7_1 hmB => ?_
                    · simp only [Arg.val, doff16, doff96, doff112] at hmA ⊢
                      exact sep_cast hmA (by ac_rfl)
                    refine dense_daxpy hDaxpy (arCtxMem cx s ⋆ array64 s.dense a0 ⋆
                        array64 (s.dense + 256#64) a2 ⋆ array64 (s.dense + 384#64) d3 ⋆
                        array64 (s.dense + 512#64) d4 ⋆ array64 (s.dense + 640#64) d5 ⋆
                        array64 (s.dense + 768#64) b6 ⋆ Rest)
                      hb7_1 ha1 ?_ fun b7_2 _ hb7_2 hmC => ?_
                    · simp only [Arg.val, doff16, doff112] at hmB ⊢; exact sep_cast hmB (by ac_rfl)
                    dsimp only [Arg.val] at hmC
                    let idx8 := (BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 8)).toNat
                    have hidx8 : idx8 < b7_2.length := by rw [show idx8 = 8 from by decide]; omega
                    have h8_b7 : (BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 8) * 8).toNat / 8 <
                        b7_2.length := by
                      rw [show (BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 8) * 8).toNat / 8 =
                        8 from by decide]; omega
                    c0_hsteps_nogrp
                    let b7_3 := b7_2.set idx8 (b7_2[idx8]'hidx8 + (0 - 2))
                    exact hJ4o () _ (dense_inv_last ha0 ha1 ha2 hd3 hd4 hd5 hb6 (a7 := b7_3)
                      (by simp only [Arg.val, doff16, doff112] at *
                          dsimp only [b7_3, idx8]; exact sep_cast ‹_› (by ac_rfl))
                      (by dsimp only [b7_3]; rw [List.length_set]; exact hb7_2))
  · intro J2 hJ2
    c0_hsteps_nogrp
    · refine dense_dlit hDlit (arCtxMem cx s ⋆ array64 s.dense a0 ⋆
          array64 (s.dense + 128#64) a1 ⋆ array64 (s.dense + 384#64) d3 ⋆
          array64 (s.dense + 512#64) d4 ⋆ array64 (s.dense + 640#64) d5 ⋆
          array64 (s.dense + 768#64) d6 ⋆ array64 (s.dense + 896#64) d7 ⋆ Rest)
        (by decide) hd2 ?_ fun a2 m2 ha2 hm2 => ?_
      · simp only [Arg.val, doff16, doff32] at hm1 ⊢; exact sep_cast hm1 (by ac_rfl)
      exact hJ2 () m2 ⟨a2, ha2,
        by simp only [Arg.val, doff32] at hm2 ⊢; exact sep_cast hm2 (by ac_rfl)⟩
    · refine dense_dzero hDzero (arCtxMem cx s ⋆ array64 s.dense a0 ⋆
          array64 (s.dense + 128#64) a1 ⋆ array64 (s.dense + 384#64) d3 ⋆
          array64 (s.dense + 512#64) d4 ⋆ array64 (s.dense + 640#64) d5 ⋆
          array64 (s.dense + 768#64) d6 ⋆ array64 (s.dense + 896#64) d7 ⋆ Rest)
        hd2 ?_ fun a2 m2 ha2 hm2 => ?_
      · simp only [Arg.val, doff16, doff32] at hm1 ⊢; exact sep_cast hm1 (by ac_rfl)
      exact hJ2 () m2 ⟨a2, ha2,
        by simp only [Arg.val, doff32] at hm2 ⊢; exact sep_cast hm2 (by ac_rfl)⟩

theorem gate_nw_step {Γ : LeanQbe.T.Env}
    (hNW : ∀ xs m Q X, arNextWordSpec xs m Q X → Γ "ar_next_word" [i64] [.bool, i32] xs m Q X)
    {cxa : Arg Val i64} {cx : BitVec 64} {s : ArCtxState}
    {artBytes : List UInt8} {F : Mem 64 → Prop} {rs : List Ty} {Q : Post rs} {X : XPost}
    {k : Tup Val [.bool, i32] → Expr Val Cont rs} {m : Mem 64}
    (hcxa : cxa.val = cx) (hart64 : s.art.toNat + artBytes.length < 2 ^ 64)
    (hnw4 : 4 * s.nw.toNat ≤ artBytes.length)
    (hm : (arCtxMem cx s ⋆ bytes s.art artBytes ⋆ F) m)
    (hkF : ∀ v m', (arCtxMem cx s ⋆ bytes s.art artBytes ⋆ F) m' →
      wp Γ Q X (k (false, v, ())) m')
    (hkT : ∀ v s' m', s.pos.toNat < s.nw.toNat → s'.pos.toNat ≤ s.nw.toNat →
      v = BitVec.ofNat 32 (wordAt artBytes s.pos.toNat) → s' = { s with pos := s.pos + 1 } →
      (arCtxMem cx s' ⋆ bytes s.art artBytes ⋆ F) m' → wp Γ Q X (k (true, v, ())) m') :
    wp Γ Q X (.call (as := [i64]) (bs := [.bool, i32]) "ar_next_word" (cxa, ()) k) m := by
  apply wp_call_of_spec
  dsimp only [vals]
  rw [hcxa]
  refine hNW _ _ _ _ ⟨s, artBytes, F, hart64, hnw4, hm, fun ok v s' m' hif hm' => ?_⟩
  cases hok : ok <;> rw [hok] at hif
  · have hs_eq : s' = s := by
      by_cases hlt : s.pos.toNat < s.nw.toNat <;> simp only [hlt, ↓reduceIte] at hif
      · cases hif.1
      · exact hif.2.2
    rw [hs_eq] at hm'
    exact hkF v m' hm'
  · have hlt : s.pos.toNat < s.nw.toNat := by
      by_cases hlt : s.pos.toNat < s.nw.toNat <;> simp only [hlt, ↓reduceIte] at hif
      · exact hlt
      · cases hif.1
    simp only [hlt, ↓reduceIte] at hif
    rcases hif with ⟨_, hv, hs_eq⟩
    have hpos' : s'.pos.toNat ≤ s.nw.toNat := by
      have := s.nw.isLt
      rw [hs_eq, BitVec.toNat_add, show BitVec.toNat 1 = 1 from rfl,
        Nat.mod_eq_of_lt (by omega)]; omega
    exact hkT v s' m' hlt hpos' hv hs_eq hm'

theorem gate_same_mem_eq {s sC : ArCtxState} (hs : GateSame s sC)
    (artBytes : List UInt8) (rhs0 rhs1 olit bindArr ruleOff ruleN partnerArr : List (BitVec 32))
    (flippedArr : List (BitVec 8)) (inNetArr outRefArr stkN stkP memoN : List (BitVec 32))
    (memoV dense : List (BitVec 64)) (gsy : List (BitVec 32)) (gcl gch : List (BitVec 64))
    (rsM : List (BitVec 32)) (rsL rsH : List (BitVec 64)) (rsPool : List (BitVec 32)) :
    (bytes sC.art artBytes ⋆ aigArraysMem sC rhs0 rhs1 olit ⋆
      netTablesMem sC bindArr ruleOff ruleN partnerArr flippedArr inNetArr outRefArr ⋆
      gateScratchMem sC stkN stkP memoN memoV dense gsy gcl gch ⋆
      rsMem sC rsM rsL rsH rsPool) =
    (bytes s.art artBytes ⋆ aigArraysMem s rhs0 rhs1 olit ⋆
      netTablesMem s bindArr ruleOff ruleN partnerArr flippedArr inNetArr outRefArr ⋆
      gateScratchMem s stkN stkP memoN memoV dense gsy gcl gch ⋆
      rsMem s rsM rsL rsH rsPool) := by
  simp only [aigArraysMem, netTablesMem, gateScratchMem, rsMem,
    show sC.art = s.art by rw [hs], show sC.rhs0 = s.rhs0 by rw [hs],
    show sC.rhs1 = s.rhs1 by rw [hs], show sC.olit = s.olit by rw [hs],
    show sC.bind = s.bind by rw [hs], show sC.rule_off = s.rule_off by rw [hs],
    show sC.rule_n = s.rule_n by rw [hs], show sC.partner = s.partner by rw [hs],
    show sC.flipped = s.flipped by rw [hs], show sC.in_net = s.in_net by rw [hs],
    show sC.out_ref = s.out_ref by rw [hs], show sC.stk_n = s.stk_n by rw [hs],
    show sC.stk_p = s.stk_p by rw [hs], show sC.memo_n = s.memo_n by rw [hs],
    show sC.memo_v = s.memo_v by rw [hs], show sC.dense = s.dense by rw [hs],
    show sC.gsy = s.gsy by rw [hs], show sC.gcl = s.gcl by rw [hs],
    show sC.gch = s.gch by rw [hs], show sC.rs_m = s.rs_m by rw [hs],
    show sC.rs_l = s.rs_l by rw [hs], show sC.rs_h = s.rs_h by rw [hs],
    show sC.rs_pool = s.rs_pool by rw [hs]]

end

end LeanQbe.T.Examples.Arisca.Proof
