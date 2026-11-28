/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Arisca.Proof.Driver2Geom
import LeanQbe.T.Logic.MemLemmas
import LeanQbe.T.Logic.ProofKit
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
meta import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.C0StepAttr
meta import LeanQbe.T.Logic.C0StepAttr
import Kraken.Separation

/-!
# ARiSCA Dynamic Arena Setup WP (`Arisca.Proof.Driver2Base`)

`XPost`-polymorphic (`noExit = true`, `<= std3`) WP proof for `ar_setup_dynamic`
(`ar_setup_dynamic_wp`).
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Arisca.Proof

open Std Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.C0HeadStep
open LeanQbe.T.ProofKit
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Arisca.Src
open LeanQbe.T.Examples.Arisca.Src.Header
open LeanQbe.T.Examples.Arisca.Src.Driver

local elab "ar_unfold_body" : tactic => do
  let g ← Lean.Elab.Tactic.getMainGoal
  g.withContext do
    let ty := (← Lean.instantiateMVars (← g.getType)).consumeMData.headBeta
    let args := ty.getAppArgs
    let some e' ← Lean.Meta.unfoldDefinition? args[4]! | throwError "ar_unfold_body: stuck"
    let ty' := Lean.mkAppN ty.getAppFn (args.set! 4 e'.consumeMData.headBeta)
    Lean.Elab.Tactic.replaceMainGoal [← g.change ty' (checkDefEq := false)]

local elab "ar_whnf_body" : tactic => do
  let g ← Lean.Elab.Tactic.getMainGoal
  g.withContext do
    let ty := (← Lean.instantiateMVars (← g.getType)).consumeMData.headBeta
    let args := ty.getAppArgs
    let e' ← Lean.Meta.whnf args[4]!
    let ty' := Lean.mkAppN ty.getAppFn (args.set! 4 e'.consumeMData.headBeta)
    Lean.Elab.Tactic.replaceMainGoal [← g.change ty' (checkDefEq := false)]

@[reducible] private def dynIgn : Expr Val Cont [.bool] → Expr Val Cont [.bool]
  | @Expr.let_ _ _ _ [.bits 64] op k =>
    match op with
    | .mk (.mul (.bits 64)) (a, b, ()) => k (a.val * b.val, ())
    | .mk (.add (.bits 64)) (a, b, ()) => k (a.val + b.val, ())
    | .mk (.copy (.bits 64)) (a, ()) => k (a.val, ())
    | _ => k (0#64, ())
  | @Expr.let_ _ _ _ [.bits 32] _ k => k (0#32, ())
  | @Expr.let_ _ _ _ [.bool] _ k => k (false, ())
  | @Expr.load _ _ _ (.bits 64) _ k => k 0#64
  | @Expr.load _ _ _ (.bits 32) _ k => k 0#32
  | .store _ _ k => k
  | e => e

@[reducible] private def dynToJnz : Nat → Expr Val Cont [.bool] → Expr Val Cont [.bool]
  | 0, e => e
  | _ + 1, e@(.jnz _ _ _) => e
  | n + 1, e => dynToJnz n (dynIgn e)

@[reducible] private def dynToGrp : Nat → Expr Val Cont [.bool] → Expr Val Cont [.bool]
  | 0, e => e
  | _ + 1, e@(.group _ _) => e
  | n + 1, e => dynToGrp n (dynIgn e)

@[reducible] private def dynToCall : Nat → Expr Val Cont [.bool] → Expr Val Cont [.bool]
  | 0, e => e
  | _ + 1, e@(.call _ _ _) => e
  | n + 1, e => dynToCall n (dynIgn e)

@[reducible] private def dynSkipCalls : Nat → Expr Val Cont [.bool] → Expr Val Cont [.bool]
  | 0, e => dynToCall 20 e
  | n + 1, e => match dynToCall 20 e with
    | @Expr.call _ _ _ _ _ [.bits 64] _ k => dynSkipCalls n (k (0#64, ()))
    | e' => e'

@[reducible] private def dynTailAt (n : Nat) (cx cap : Val i64) : Expr Val Cont [.bool] :=
  match dynToJnz 20 (ar_setup_dynamic_body Val Cont (cx, ())) with
  | .jnz _ _ e1 =>
    match dynToJnz 20 e1 with
    | .jnz _ _ e2 =>
      match dynToGrp 20 e2 with
      | .group (sig := [[.bits 64]]) b _ =>
        match dynToJnz 20 (Blocks.get (b ((fun _ _ => False), ())) .here (cap, ())) with
        | .jnz _ _ e3 => dynSkipCalls n e3
        | _ => .ret (Arg.imm false, ())
      | _ => .ret (Arg.imm false, ())
    | _ => .ret (Arg.imm false, ())
  | _ => .ret (Arg.imm false, ())

@[reducible] private def dynTailExpr (cx cap : Val i64) : Expr Val Cont [.bool] :=
  dynTailAt 14 cx cap

public section

private theorem getD_set2_0 {l : List (BitVec 64)} {a b : BitVec 64} (h : l.length = 2) :
    ((l.set 0 a).set 1 b).getD 0 0#64 = a := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne (by decide),
    List.getElem?_set_self (by omega)]
  rfl

private theorem getD_set2_1 {l : List (BitVec 64)} {a b : BitVec 64} (h : l.length = 2) :
    ((l.set 0 a).set 1 b).getD 1 0#64 = b := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_set_self (by simp [h])]; rfl

private theorem dyn_alloc_qr_wp (Γ : T.Env)
    (hAlloc : ∀ xs m Q X, arAallocSpec xs m Q X → Γ "ar_aalloc" [i64, i64] [i64] xs m Q X)
    {cx : BitVec 64} {s0 : ArCtxState} {baseTop : Nat} {R : Mem 64 → Prop}
    {Q : Post [.bool]} {X : XPost}
    {cap tp14 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 : BitVec 64} {m : Mem 64}
    (hlens : ArCtxLengthsOk s0) (hwpos : 0 < s0.w.toNat)
    (hfit : s0.w.toNat + s0.wlen.toNat < 2 ^ 64)
    (hcap16 : 16 ≤ cap.toNat) (hcapMax : cap.toNat ≤ 300000000)
    (hpw_nat : (cap * 12).toNat = 12 * cap.toNat)
    (h4cap_nat : (4 * cap).toNat = 4 * cap.toNat)
    (h8cap_nat : (8 * cap).toNat = 8 * cap.toNat)
    (h4pw_nat : (4 * (cap * 12)).toNat = 4 * (12 * cap.toNat))
    (h4vo_nat : (4 * cap + 4).toNat = 4 * cap.toNat + 4)
    (hcap32_nat : (cap.setWidth 32).toNat = cap.toNat)
    (ht0_le : baseTop ≤ align8 s0.top.toNat)
    (_hfin_bd : dynEndTop s0.top.toNat cap.toNat ≤ s0.wlen.toNat)
    (hb14 : baseTop ≤ tp14.toNat) (ht14 : tp14.toNat ≤ s0.wlen.toNat)
    (ha8_al : align8 (8 * cap.toNat) = 8 * cap.toNat)
    (hap_al : align8 (4 * (12 * cap.toNat)) = 4 * (12 * cap.toNat))
    (hok14_prev : ((((((((((((((true && (p1 != 0#64)) && (p2 != 0#64)) && (p3 != 0#64)) &&
        (p4 != 0#64)) && (p5 != 0#64)) && (p6 != 0#64)) && (p7 != 0#64)) && (p8 != 0#64)) &&
        (p9 != 0#64)) && (p10 != 0#64)) && (p11 != 0#64)) && (p12 != 0#64)) && (p13 != 0#64)) &&
        (p14 != 0#64)) = true →
      let t0 := align8 s0.top.toNat; let a4 := align8 (4 * cap.toNat)
      let a8 := 8 * cap.toNat; let ap := 4 * (12 * cap.toNat)
      align8 tp14.toNat = t0 + 3 * a4 + 8 * a8 + 3 * ap ∧
      (p1 = s0.w + BitVec.ofNat 64 t0 ∧ p2 = s0.w + BitVec.ofNat 64 (t0 + a4) ∧
       p3 = s0.w + BitVec.ofNat 64 (t0 + a4 + a8) ∧
       p4 = s0.w + BitVec.ofNat 64 (t0 + a4 + 2 * a8)) ∧
      (p5 = s0.w + BitVec.ofNat 64 (t0 + a4 + 2 * a8 + ap) ∧
       p6 = s0.w + BitVec.ofNat 64 (t0 + 2 * a4 + 2 * a8 + ap) ∧
       p7 = s0.w + BitVec.ofNat 64 (t0 + 2 * a4 + 3 * a8 + ap) ∧
       p8 = s0.w + BitVec.ofNat 64 (t0 + 2 * a4 + 4 * a8 + ap) ∧
       p9 = s0.w + BitVec.ofNat 64 (t0 + 2 * a4 + 5 * a8 + ap) ∧
       p10 = s0.w + BitVec.ofNat 64 (t0 + 3 * a4 + 5 * a8 + ap) ∧
       p11 = s0.w + BitVec.ofNat 64 (t0 + 3 * a4 + 6 * a8 + ap) ∧
       p12 = s0.w + BitVec.ofNat 64 (t0 + 3 * a4 + 7 * a8 + ap) ∧
       p13 = s0.w + BitVec.ofNat 64 (t0 + 3 * a4 + 8 * a8 + ap) ∧
       p14 = s0.w + BitVec.ofNat 64 (t0 + 3 * a4 + 8 * a8 + 2 * ap)))
    (hm : (arCtxMem cx { s0 with
        top := tp14, rs_cap := cap.setWidth 32, rs_pcap := cap * 12,
        rs_m := p1, rs_l := p2, rs_h := p3, rs_pool := p4, tcap := cap.setWidth 32,
        tm := (s0.tm.set 0 p5).set 1 p9, ts := (s0.ts.set 0 p6).set 1 p10,
        tl := (s0.tl.set 0 p7).set 1 p11, th := (s0.th.set 0 p8).set 1 p12,
        pcap := cap * 12, pool := (s0.pool.set 0 p13).set 1 p14, qcap := cap.setWidth 32 } ⋆
      (region (s0.w + BitVec.ofNat 64 baseTop) (tp14.toNat - baseTop) ⋆
       (region (s0.w + tp14) (s0.wlen.toNat - tp14.toNat) ⋆ R))) m)
    (hQ : ∀ (ok : Bool) (m' : Mem 64),
      ((ok = false ∧ ∃ s' : ArCtxState,
          s'.w = s0.w ∧ s'.wlen = s0.wlen ∧
          (arCtxMem cx s' ⋆
            region (s0.w + BitVec.ofNat 64 baseTop) (s0.wlen.toNat - baseTop) ⋆ R) m') ∨
       (ok = true ∧ ∃ (s' : ArCtxState)
          (rsM : List (BitVec 32)) (rsL rsH : List (BitVec 64)) (rsPool : List (BitVec 32))
          (tm0 tm1 : List (BitVec 32)) (ts0 tl0 th0 ts1 tl1 th1 : List (BitVec 64))
          (pool0 pool1 qm : List (BitVec 32)) (qs ql qh : List (BitVec 64))
          (ix ix2 bx vqOff vq : List (BitVec 32)) (vqSkip : List (BitVec 8))
          (rm : List (BitVec 32)) (rl rh : List (BitVec 64))
          (rm2 : List (BitVec 32)) (rl2 rh2 : List (BitVec 64))
          (rpool : List (BitVec 32)),
          let cap := s'.qcap.toNat
          let pw := s'.pcap.toNat
          16 ≤ cap ∧ cap ≤ 300000000 ∧ pw = 12 * cap ∧
          s'.rs_cap = s'.qcap ∧ s'.tcap = s'.qcap ∧ s'.rcap = s'.qcap ∧
          s'.rs_pcap = s'.pcap ∧ s'.rpcap = s'.pcap ∧
          s'.top.toNat ≤ s'.wlen.toNat ∧
          DynGeom s' s0.top.toNat cap ∧
          s' = { s0 with
            top := s'.top, rs_cap := s'.rs_cap, rs_pcap := s'.rs_pcap,
            tcap := s'.tcap, pcap := s'.pcap, qcap := s'.qcap,
            rcap := s'.rcap, rpcap := s'.rpcap,
            rs_m := s'.rs_m, rs_l := s'.rs_l, rs_h := s'.rs_h, rs_pool := s'.rs_pool,
            tm := s'.tm, ts := s'.ts, tl := s'.tl, th := s'.th, pool := s'.pool,
            qm := s'.qm, qs := s'.qs, ql := s'.ql, qh := s'.qh,
            ix := s'.ix, ix2 := s'.ix2, bx := s'.bx,
            vq_off := s'.vq_off, vq := s'.vq, vq_skip := s'.vq_skip,
            rm := s'.rm, rl := s'.rl, rh := s'.rh,
            rm2 := s'.rm2, rl2 := s'.rl2, rh2 := s'.rh2, rpool := s'.rpool } ∧
          rsM.length = cap ∧ rsL.length = cap ∧ rsH.length = cap ∧ rsPool.length = pw ∧
          tm0.length = cap ∧ tm1.length = cap ∧
          ts0.length = cap ∧ tl0.length = cap ∧ th0.length = cap ∧
          ts1.length = cap ∧ tl1.length = cap ∧ th1.length = cap ∧
          pool0.length = pw ∧ pool1.length = pw ∧
          qm.length = cap ∧ qs.length = cap ∧ ql.length = cap ∧ qh.length = cap ∧
          ix.length = cap ∧ ix2.length = cap ∧ bx.length = cap ∧
          vqOff.length = cap + 1 ∧ vq.length = pw ∧ vqSkip.length = cap ∧
          rm.length = cap ∧ rl.length = cap ∧ rh.length = cap ∧
          rm2.length = cap ∧ rl2.length = cap ∧ rh2.length = cap ∧ rpool.length = pw ∧
          (arCtxMem cx s' ⋆
            region (s0.w + BitVec.ofNat 64 baseTop) (align8 s0.top.toNat - baseTop) ⋆
            rsMem s' rsM rsL rsH rsPool ⋆
            tMem s' tm0 tm1 ts0 tl0 th0 ts1 tl1 th1 pool0 pool1 ⋆
            qMem s' qm qs ql qh ix ix2 bx vqOff vq vqSkip ⋆
            rMem s' rm rl rh rm2 rl2 rh2 rpool ⋆
            region (s'.w + s'.top) (s'.wlen.toNat - s'.top.toNat) ⋆ R) m')) →
      Q (ok, ⟨⟩) m') :
    wp Γ Q X (dynTailExpr cx cap) m := by
  let t0 := align8 s0.top.toNat
  let a4 := align8 (4 * cap.toNat)
  let a8 := 8 * cap.toNat
  let ap := 4 * (12 * cap.toNat)
  let avo := align8 (4 * cap.toNat + 4)
  let avs := align8 cap.toNat
  let ok14 := ((((((((((((((true && (p1 != 0#64)) && (p2 != 0#64)) && (p3 != 0#64)) &&
    (p4 != 0#64)) && (p5 != 0#64)) && (p6 != 0#64)) && (p7 != 0#64)) && (p8 != 0#64)) &&
    (p9 != 0#64)) && (p10 != 0#64)) && (p11 != 0#64)) && (p12 != 0#64)) && (p13 != 0#64)) &&
    (p14 != 0#64))
  have ha14 : ok14 = true →
      (true = true ∧ p14 ≠ 0#64 ∧ p14 = s0.w + BitVec.ofNat 64 (t0 + 3 * a4 + 8 * a8 + 2 * ap) ∧
       tp14.toNat = tp14.toNat ∧ align8 tp14.toNat = t0 + 3 * a4 + 8 * a8 + 3 * ap) := by
    intro h
    have hp14_ne : p14 ≠ 0#64 := by
      simpa only [ok14, Bool.and_eq_true, bne_iff_ne] using
        ((Bool.and_eq_true _ _).mp h).2
    exact ⟨rfl, hp14_ne, (hok14_prev h).2.2.2.2.2.2.2.2.2.2.2, rfl, (hok14_prev h).1⟩
  have hok14 : (ok14 = true → p14 ≠ 0#64 ∧
      p14 = s0.w + BitVec.ofNat 64 (t0 + 3 * a4 + 8 * a8 + 2 * ap) ∧
      tp14.toNat = tp14.toNat ∧ align8 tp14.toNat = t0 + 3 * a4 + 8 * a8 + 3 * ap) ∧
      (ok14 = false → ok14 = false ∨ p14 = 0#64) :=
    ⟨fun h => (ha14 h).2, fun h => Or.inl h⟩
  let s15 : ArCtxState := { s0 with
    top := tp14, rs_cap := cap.setWidth 32, rs_pcap := cap * 12,
    rs_m := p1, rs_l := p2, rs_h := p3, rs_pool := p4, tcap := cap.setWidth 32,
    tm := (s0.tm.set 0 p5).set 1 p9, ts := (s0.ts.set 0 p6).set 1 p10,
    tl := (s0.tl.set 0 p7).set 1 p11, th := (s0.th.set 0 p8).set 1 p12,
    pcap := cap * 12, pool := (s0.pool.set 0 p13).set 1 p14, qcap := cap.setWidth 32 }
  ar_whnf_body
  c0_hsteps_nogrp
  c0_hcall (dyn_alloc_step Γ hAlloc hm hwpos hfit rfl rfl hb14 ht14)
  intro p15 tp15 m15 hb15 ht15 hd15 hm15
  have hok15 := dyn_step_chain hd15 hok14 h4cap_nat rfl
  c0_hsteps_nogrp
  let s16 : ArCtxState := { s15 with top := tp15, qm := p15 }
  have hm : _ := dyn_ctx_bind (s' := s16) rfl hm
  try clear m; clear hb14 ht14 hd15
  c0_hcall (dyn_alloc_step Γ hAlloc hm hwpos hfit rfl rfl hb15 ht15)
  intro p16 tp16 m16 hb16 ht16 hd16 hm16
  have hok16 := dyn_step_chain hd16 hok15 h8cap_nat (by rw [ha8_al])
  c0_hsteps_nogrp
  let s17 : ArCtxState := { s16 with top := tp16, qs := p16 }
  have hm : _ := dyn_ctx_bind (s' := s17) rfl hm
  try clear m15; clear hb15 ht15 hd16
  c0_hcall (dyn_alloc_step Γ hAlloc hm hwpos hfit rfl rfl hb16 ht16)
  intro p17 tp17 m17 hb17 ht17 hd17 hm17
  have hok17 := dyn_step_chain hd17 hok16 h8cap_nat (by rw [ha8_al])
  c0_hsteps_nogrp
  let s18 : ArCtxState := { s17 with top := tp17, ql := p17 }
  have hm : _ := dyn_ctx_bind (s' := s18) rfl hm
  try clear m16; clear hb16 ht16 hd17
  c0_hcall (dyn_alloc_step Γ hAlloc hm hwpos hfit rfl rfl hb17 ht17)
  intro p18 tp18 m18 hb18 ht18 hd18 hm18
  have hok18 := dyn_step_chain hd18 hok17 h8cap_nat (by rw [ha8_al])
  c0_hsteps_nogrp
  let s19 : ArCtxState := { s18 with top := tp18, qh := p18 }
  have hm : _ := dyn_ctx_bind (s' := s19) rfl hm
  try clear m17; clear hb17 ht17 hd18
  c0_hcall (dyn_alloc_step Γ hAlloc hm hwpos hfit rfl rfl hb18 ht18)
  intro p19 tp19 m19 hb19 ht19 hd19 hm19
  have hok19 := dyn_step_chain hd19 hok18 h4cap_nat rfl
  c0_hsteps_nogrp
  let s20 : ArCtxState := { s19 with top := tp19, ix := p19 }
  have hm : _ := dyn_ctx_bind (s' := s20) rfl hm
  try clear m18; clear hb18 ht18 hd19
  c0_hcall (dyn_alloc_step Γ hAlloc hm hwpos hfit rfl rfl hb19 ht19)
  intro p20 tp20 m20 hb20 ht20 hd20 hm20
  have hok20 := dyn_step_chain hd20 hok19 h4cap_nat rfl
  c0_hsteps_nogrp
  let s21 : ArCtxState := { s20 with top := tp20, ix2 := p20 }
  have hm : _ := dyn_ctx_bind (s' := s21) rfl hm
  try clear m19; clear hb19 ht19 hd20
  c0_hcall (dyn_alloc_step Γ hAlloc hm hwpos hfit rfl rfl hb20 ht20)
  intro p21 tp21 m21 hb21 ht21 hd21 hm21
  have hok21 := dyn_step_chain hd21 hok20 h4cap_nat rfl
  c0_hsteps_nogrp
  let s22 : ArCtxState := { s21 with top := tp21, bx := p21 }
  have hm : _ := dyn_ctx_bind (s' := s22) rfl hm
  try clear m20; clear hb20 ht20 hd21
  c0_hcall (dyn_alloc_step Γ hAlloc hm hwpos hfit rfl rfl hb21 ht21)
  intro p22 tp22 m22 hb22 ht22 hd22 hm22
  have hok22 := dyn_step_chain hd22 hok21 h4vo_nat rfl
  c0_hsteps_nogrp
  let s23 : ArCtxState := { s22 with top := tp22, vq_off := p22 }
  have hm : _ := dyn_ctx_bind (s' := s23) rfl hm
  try clear m21; clear hb21 ht21 hd22
  c0_hcall (dyn_alloc_step Γ hAlloc hm hwpos hfit rfl rfl hb22 ht22)
  intro p23 tp23 m23 hb23 ht23 hd23 hm23
  have hok23 := dyn_step_chain hd23 hok22 h4pw_nat (by rw [hap_al])
  c0_hsteps_nogrp
  let s24 : ArCtxState := { s23 with top := tp23, vq := p23 }
  have hm : _ := dyn_ctx_bind (s' := s24) rfl hm
  try clear m22; clear hb22 ht22 hd23
  c0_hcall (dyn_alloc_step Γ hAlloc hm hwpos hfit rfl rfl hb23 ht23)
  intro p24 tp24 m24 hb24 ht24 hd24 hm24
  have hok24 := dyn_step_chain hd24 hok23 rfl rfl
  c0_hsteps_nogrp
  let s25 : ArCtxState := { s0 with
    top := tp24, rs_cap := cap.setWidth 32, rs_pcap := cap * 12,
    rs_m := p1, rs_l := p2, rs_h := p3, rs_pool := p4, tcap := cap.setWidth 32,
    tm := (s0.tm.set 0 p5).set 1 p9, ts := (s0.ts.set 0 p6).set 1 p10,
    tl := (s0.tl.set 0 p7).set 1 p11, th := (s0.th.set 0 p8).set 1 p12,
    pcap := cap * 12, pool := (s0.pool.set 0 p13).set 1 p14, qcap := cap.setWidth 32,
    qm := p15, qs := p16, ql := p17, qh := p18, ix := p19, ix2 := p20, bx := p21,
    vq_off := p22, vq := p23, vq_skip := p24, rcap := cap.setWidth 32, rpcap := cap * 12 }
  have hm : _ := dyn_ctx_bind (s' := s25) rfl hm
  try clear m23; clear hb23 ht23 hd24
  c0_hcall (dyn_alloc_step Γ hAlloc hm hwpos hfit rfl rfl hb24 ht24)
  intro p25 tp25 m25 hb25 ht25 hd25 hm25
  have hok25 := dyn_step_chain hd25 hok24 h4cap_nat rfl
  c0_hsteps_nogrp
  let s26 : ArCtxState := { s25 with top := tp25, rm := p25 }
  have hm : _ := dyn_ctx_bind (s' := s26) rfl hm
  try clear m24; clear hb24 ht24 hd25
  c0_hcall (dyn_alloc_step Γ hAlloc hm hwpos hfit rfl rfl hb25 ht25)
  intro p26 tp26 m26 hb26 ht26 hd26 hm26
  have hok26 := dyn_step_chain hd26 hok25 h8cap_nat (by rw [ha8_al])
  c0_hsteps_nogrp
  let s27 : ArCtxState := { s26 with top := tp26, rl := p26 }
  have hm : _ := dyn_ctx_bind (s' := s27) rfl hm
  try clear m25; clear hb25 ht25 hd26
  c0_hcall (dyn_alloc_step Γ hAlloc hm hwpos hfit rfl rfl hb26 ht26)
  intro p27 tp27 m27 hb27 ht27 hd27 hm27
  have hok27 := dyn_step_chain hd27 hok26 h8cap_nat (by rw [ha8_al])
  c0_hsteps_nogrp
  let s28 : ArCtxState := { s27 with top := tp27, rh := p27 }
  have hm : _ := dyn_ctx_bind (s' := s28) rfl hm
  try clear m26; clear hb26 ht26 hd27
  c0_hcall (dyn_alloc_step Γ hAlloc hm hwpos hfit rfl rfl hb27 ht27)
  intro p28 tp28 m28 hb28 ht28 hd28 hm28
  have hok28 := dyn_step_chain hd28 hok27 h4cap_nat rfl
  c0_hsteps_nogrp
  let s29 : ArCtxState := { s28 with top := tp28, rm2 := p28 }
  have hm : _ := dyn_ctx_bind (s' := s29) rfl hm
  try clear m27; clear hb27 ht27 hd28
  c0_hcall (dyn_alloc_step Γ hAlloc hm hwpos hfit rfl rfl hb28 ht28)
  intro p29 tp29 m29 hb29 ht29 hd29 hm29
  have hok29 := dyn_step_chain hd29 hok28 h8cap_nat (by rw [ha8_al])
  c0_hsteps_nogrp
  let s30 : ArCtxState := { s29 with top := tp29, rl2 := p29 }
  have hm : _ := dyn_ctx_bind (s' := s30) rfl hm
  try clear m28; clear hb28 ht28 hd29
  c0_hcall (dyn_alloc_step Γ hAlloc hm hwpos hfit rfl rfl hb29 ht29)
  intro p30 tp30 m30 hb30 ht30 hd30 hm30
  have hok30 := dyn_step_chain hd30 hok29 h8cap_nat (by rw [ha8_al])
  c0_hsteps_nogrp
  let s31 : ArCtxState := { s30 with top := tp30, rh2 := p30 }
  have hm : _ := dyn_ctx_bind (s' := s31) rfl hm
  try clear m29; clear hb29 ht29 hd30
  c0_hcall (dyn_alloc_step Γ hAlloc hm hwpos hfit rfl rfl hb30 ht30)
  intro p31 tp31 m31 hb31 ht31 hd31 hm31
  have hok31 := dyn_step_chain hd31 hok30 h4pw_nat (by rw [hap_al])
  try clear m30; clear hb30 ht30 hd31
  let s31b : ArCtxState := { s0 with
    top := tp31, rs_cap := cap.setWidth 32, rs_pcap := cap * 12,
    rs_m := p1, rs_l := p2, rs_h := p3, rs_pool := p4, tcap := cap.setWidth 32,
    tm := (s0.tm.set 0 p5).set 1 p9, ts := (s0.ts.set 0 p6).set 1 p10,
    tl := (s0.tl.set 0 p7).set 1 p11, th := (s0.th.set 0 p8).set 1 p12,
    pcap := cap * 12, pool := (s0.pool.set 0 p13).set 1 p14, qcap := cap.setWidth 32,
    qm := p15, qs := p16, ql := p17, qh := p18, ix := p19, ix2 := p20, bx := p21,
    vq_off := p22, vq := p23, vq_skip := p24, rcap := cap.setWidth 32, rpcap := cap * 12,
    rm := p25, rl := p26, rh := p27, rm2 := p28, rl2 := p29, rh2 := p30 }
  have hm : _ := dyn_ctx_bind (s' := s31b) rfl hm31
  clear hm31
  refine head_wp_store rfl rfl (store_rpool p31 hm) fun m32 hm32 => ?_
  let s32 : ArCtxState := { s0 with
    top := tp31, rs_cap := cap.setWidth 32, rs_pcap := cap * 12,
    rs_m := p1, rs_l := p2, rs_h := p3, rs_pool := p4, tcap := cap.setWidth 32,
    tm := (s0.tm.set 0 p5).set 1 p9, ts := (s0.ts.set 0 p6).set 1 p10,
    tl := (s0.tl.set 0 p7).set 1 p11, th := (s0.th.set 0 p8).set 1 p12,
    pcap := cap * 12, pool := (s0.pool.set 0 p13).set 1 p14, qcap := cap.setWidth 32,
    qm := p15, qs := p16, ql := p17, qh := p18, ix := p19, ix2 := p20, bx := p21,
    vq_off := p22, vq := p23, vq_skip := p24, rcap := cap.setWidth 32, rpcap := cap * 12,
    rm := p25, rl := p26, rh := p27, rm2 := p28, rl2 := p29, rh2 := p30, rpool := p31 }
  have hm32' : _ := dyn_ctx_bind (cx := cx) (s' := s32) rfl hm32
  clear hm32; try clear hm
  have hFail32 : Q (false, ⟨⟩) m32 := hQ false m32
    (Or.inl ⟨rfl, s32, rfl, rfl, dyn_fail_wrap hfit hb31 ht31 (sep_cast hm32' (by ac_rfl))⟩)
  have hk0m : (BitVec.ofNat 64 0 * 8 : BitVec 64).toNat % 8 = 0 := by decide
  have hk0d : (BitVec.ofNat 64 0 * 8 : BitVec 64).toNat / 8 < 2 := by decide
  have hk1m : (BitVec.ofNat 64 1 * 8 : BitVec 64).toNat % 8 = 0 := by decide
  have hk1d : (BitVec.ofNat 64 1 * 8 : BitVec 64).toNat / 8 < 2 := by decide
  have hget0 : ∀ (xs : List (BitVec 64)) {k : Nat} (hk : k = 0) (hl : xs.length = 2),
      xs[k]'(by omega) = xs.getD 0 0#64 := fun xs k hk hl => by
    subst hk; simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : 0 < xs.length)]
  have hget1 : ∀ (xs : List (BitVec 64)) {k : Nat} (hk : k = 1) (hl : xs.length = 2),
      xs[k]'(by omega) = xs.getD 1 0#64 := fun xs k hk hl => by
    subst hk; simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : 1 < xs.length)]
  have hl32_tm : s32.tm.length = 2 := by simp [s32, hlens.tm]
  have hl32_ts : s32.ts.length = 2 := by simp [s32, hlens.ts]
  have hl32_tl : s32.tl.length = 2 := by simp [s32, hlens.tl]
  have hl32_th : s32.th.length = 2 := by simp [s32, hlens.th]
  have hl32_pool : s32.pool.length = 2 := by simp [s32, hlens.pool]
  c0_hsplit_nobound; · exact head_wp_ret rfl hFail32
  have hp1_ne : p1 ≠ 0#64 := by intro h; apply hc; simpa using h
  clear hc; c0_hsplit_nobound; · exact head_wp_ret rfl hFail32
  have hp2_ne : p2 ≠ 0#64 := by intro h; apply hc; simpa using h
  clear hc; c0_hsplit_nobound; · exact head_wp_ret rfl hFail32
  have hp3_ne : p3 ≠ 0#64 := by intro h; apply hc; simpa using h
  clear hc; c0_hsplit_nobound; · exact head_wp_ret rfl hFail32
  have hp4_ne : p4 ≠ 0#64 := by intro h; apply hc; simpa using h
  clear hc; c0_hsplit_nobound; · exact head_wp_ret rfl hFail32
  have hp5_ne : p5 ≠ 0#64 := by
    intro h; apply hc; rw [hget0 _ _ hl32_tm]
    · dsimp only [s32]; rw [getD_set2_0 hlens.tm]; simpa using h
    · decide
  clear hc; c0_hsplit_nobound; · exact head_wp_ret rfl hFail32
  have hp6_ne : p6 ≠ 0#64 := by
    intro h; apply hc; rw [hget0 _ _ hl32_ts]
    · dsimp only [s32]; rw [getD_set2_0 hlens.ts]; simpa using h
    · decide
  clear hc; c0_hsplit_nobound; · exact head_wp_ret rfl hFail32
  have hp7_ne : p7 ≠ 0#64 := by
    intro h; apply hc; rw [hget0 _ _ hl32_tl]
    · dsimp only [s32]; rw [getD_set2_0 hlens.tl]; simpa using h
    · decide
  clear hc; c0_hsplit_nobound; · exact head_wp_ret rfl hFail32
  have hp8_ne : p8 ≠ 0#64 := by
    intro h; apply hc; rw [hget0 _ _ hl32_th]
    · dsimp only [s32]; rw [getD_set2_0 hlens.th]; simpa using h
    · decide
  clear hc; c0_hsplit_nobound; · exact head_wp_ret rfl hFail32
  have hp9_ne : p9 ≠ 0#64 := by
    intro h; apply hc; rw [hget1 _ _ hl32_tm]
    · dsimp only [s32]; rw [getD_set2_1 hlens.tm]; simpa using h
    · decide
  clear hc; c0_hsplit_nobound; · exact head_wp_ret rfl hFail32
  have hp10_ne : p10 ≠ 0#64 := by
    intro h; apply hc; rw [hget1 _ _ hl32_ts]
    · dsimp only [s32]; rw [getD_set2_1 hlens.ts]; simpa using h
    · decide
  clear hc; c0_hsplit_nobound; · exact head_wp_ret rfl hFail32
  have hp11_ne : p11 ≠ 0#64 := by
    intro h; apply hc; rw [hget1 _ _ hl32_tl]
    · dsimp only [s32]; rw [getD_set2_1 hlens.tl]; simpa using h
    · decide
  clear hc; c0_hsplit_nobound; · exact head_wp_ret rfl hFail32
  have hp12_ne : p12 ≠ 0#64 := by
    intro h; apply hc; rw [hget1 _ _ hl32_th]
    · dsimp only [s32]; rw [getD_set2_1 hlens.th]; simpa using h
    · decide
  clear hc; c0_hsplit_nobound; · exact head_wp_ret rfl hFail32
  have hp13_ne : p13 ≠ 0#64 := by
    intro h; apply hc; rw [hget0 _ _ hl32_pool]
    · dsimp only [s32]; rw [getD_set2_0 hlens.pool]; simpa using h
    · decide
  clear hc; c0_hsplit_nobound; · exact head_wp_ret rfl hFail32
  have hp14_ne : p14 ≠ 0#64 := by
    intro h; apply hc; rw [hget1 _ _ hl32_pool]
    · dsimp only [s32]; rw [getD_set2_1 hlens.pool]; simpa using h
    · decide
  clear hc; clear hk0m hk0d hk1m hk1d hget0 hget1 hl32_tm hl32_ts hl32_tl hl32_th hl32_pool
  c0_hsplit_nobound; · exact head_wp_ret rfl hFail32
  have hp15_ne : p15 ≠ 0#64 := by intro h; apply hc; simpa using h
  clear hc; c0_hsplit_nobound; · exact head_wp_ret rfl hFail32
  have hp16_ne : p16 ≠ 0#64 := by intro h; apply hc; simpa using h
  clear hc; c0_hsplit_nobound; · exact head_wp_ret rfl hFail32
  have hp17_ne : p17 ≠ 0#64 := by intro h; apply hc; simpa using h
  clear hc; c0_hsplit_nobound; · exact head_wp_ret rfl hFail32
  have hp18_ne : p18 ≠ 0#64 := by intro h; apply hc; simpa using h
  clear hc; c0_hsplit_nobound; · exact head_wp_ret rfl hFail32
  have hp19_ne : p19 ≠ 0#64 := by intro h; apply hc; simpa using h
  clear hc; c0_hsplit_nobound; · exact head_wp_ret rfl hFail32
  have hp20_ne : p20 ≠ 0#64 := by intro h; apply hc; simpa using h
  clear hc; c0_hsplit_nobound; · exact head_wp_ret rfl hFail32
  have hp21_ne : p21 ≠ 0#64 := by intro h; apply hc; simpa using h
  clear hc; c0_hsplit_nobound; · exact head_wp_ret rfl hFail32
  have hp22_ne : p22 ≠ 0#64 := by intro h; apply hc; simpa using h
  clear hc; c0_hsplit_nobound; · exact head_wp_ret rfl hFail32
  have hp23_ne : p23 ≠ 0#64 := by intro h; apply hc; simpa using h
  clear hc; c0_hsplit_nobound; · exact head_wp_ret rfl hFail32
  have hp24_ne : p24 ≠ 0#64 := by intro h; apply hc; simpa using h
  clear hc; c0_hsplit_nobound; · exact head_wp_ret rfl hFail32
  have hp25_ne : p25 ≠ 0#64 := by intro h; apply hc; simpa using h
  clear hc; c0_hsplit_nobound; · exact head_wp_ret rfl hFail32
  have hp26_ne : p26 ≠ 0#64 := by intro h; apply hc; simpa using h
  clear hc; c0_hsplit_nobound; · exact head_wp_ret rfl hFail32
  have hp27_ne : p27 ≠ 0#64 := by intro h; apply hc; simpa using h
  clear hc; c0_hsplit_nobound; · exact head_wp_ret rfl hFail32
  have hp28_ne : p28 ≠ 0#64 := by intro h; apply hc; simpa using h
  clear hc; c0_hsplit_nobound; · exact head_wp_ret rfl hFail32
  have hp29_ne : p29 ≠ 0#64 := by intro h; apply hc; simpa using h
  clear hc; c0_hsplit_nobound; · exact head_wp_ret rfl hFail32
  have hp30_ne : p30 ≠ 0#64 := by intro h; apply hc; simpa using h
  clear hc; c0_hsplit_nobound; · exact head_wp_ret rfl hFail32
  have hp31_ne : p31 ≠ 0#64 := by intro h; apply hc; simpa using h
  clear hc
  c0_hsteps_nogrp
  have hall31 : (ok14 && (p15 != 0#64) && (p16 != 0#64) && (p17 != 0#64) && (p18 != 0#64) &&
      (p19 != 0#64) && (p20 != 0#64) && (p21 != 0#64) && (p22 != 0#64) && (p23 != 0#64) &&
      (p24 != 0#64) && (p25 != 0#64) && (p26 != 0#64) && (p27 != 0#64) && (p28 != 0#64) &&
      (p29 != 0#64) && (p30 != 0#64) && (p31 != 0#64)) = true := by
    simp only [ok14, Bool.and_eq_true, bne_iff_ne]
    exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨trivial, hp1_ne⟩, hp2_ne⟩, hp3_ne⟩, hp4_ne⟩, hp5_ne⟩,
      hp6_ne⟩, hp7_ne⟩, hp8_ne⟩, hp9_ne⟩, hp10_ne⟩, hp11_ne⟩, hp12_ne⟩, hp13_ne⟩, hp14_ne⟩,
      hp15_ne⟩, hp16_ne⟩, hp17_ne⟩, hp18_ne⟩, hp19_ne⟩, hp20_ne⟩, hp21_ne⟩, hp22_ne⟩, hp23_ne⟩,
      hp24_ne⟩, hp25_ne⟩, hp26_ne⟩, hp27_ne⟩, hp28_ne⟩, hp29_ne⟩, hp30_ne⟩, hp31_ne⟩
  have ha := fun {b1 b2 : Bool} (h : (b1 && b2) = true) => ((Bool.and_eq_true b1 b2).mp h).1
  have h30 := ha hall31; have h29 := ha h30; have h28 := ha h29; have h27 := ha h28
  have h26 := ha h27; have h25 := ha h26; have h24 := ha h25; have h23 := ha h24
  have h22 := ha h23; have h21 := ha h22; have h20 := ha h21; have h19 := ha h20
  have h18 := ha h19; have h17 := ha h18; have h16 := ha h17; have h15 := ha h16
  have h14 := ha h15
  obtain ⟨_, hp_rs, hp_t⟩ := hok14_prev h14
  have hpw64 : ∀ {x : BitVec 64} {a b : Nat},
      x = s0.w + BitVec.ofNat 64 a → a = b → x = s0.w + BitVec.ofNat 64 b :=
    fun h hab => hab ▸ h
  exact hQ true _ (Or.inr ⟨rfl, dyn_finish_alloc hlens hfit hcap16 hcapMax hpw_nat hcap32_nat
    hp_rs hp_t
    ⟨hpw64 (hok15.1 h15).2.1 (by omega), hpw64 (hok16.1 h16).2.1 (by omega),
     hpw64 (hok17.1 h17).2.1 (by omega), hpw64 (hok18.1 h18).2.1 (by omega),
     hpw64 (hok19.1 h19).2.1 (by omega), hpw64 (hok20.1 h20).2.1 (by omega),
     hpw64 (hok21.1 h21).2.1 (by omega), hpw64 (hok22.1 h22).2.1 (by omega),
     hpw64 (hok23.1 h23).2.1 (by omega), hpw64 (hok24.1 h24).2.1 (by omega)⟩
    ⟨hpw64 (hok25.1 h25).2.1 (by omega), hpw64 (hok26.1 h26).2.1 (by omega),
     hpw64 (hok27.1 h27).2.1 (by omega), hpw64 (hok28.1 h28).2.1 (by omega),
     hpw64 (hok29.1 h29).2.1 (by omega), hpw64 (hok30.1 h30).2.1 (by omega),
     hpw64 (hok31.1 hall31).2.1 (by omega)⟩
    (by rw [(hok31.1 hall31).2.2.1]; dsimp only [dynEndTop, t0, a4, a8, ap, avo, avs]; omega)
    ht0_le ht31 (sep_cast hm32' (by ac_rfl))⟩)

theorem ar_setup_dynamic_wp (Γ : T.Env)
    (hAlloc : ∀ xs m Q X, arAallocSpec xs m Q X → Γ "ar_aalloc" [i64, i64] [i64] xs m Q X) :
    ∀ xs m Q X, arSetupDynamicSpec xs m Q X → Func.wp Γ ar_setup_dynamic_body xs m Q X := by
  rintro ⟨cx, ⟨⟩⟩ m Q X
    ⟨s0, baseTop, R, hwpos, hfit, hbase0, htop0, hrn, hrpt, hpt0, htn0, hqn0, hpc0, htc0, hcnr0,
      hm, hQ⟩
  have hlens : ArCtxLengthsOk s0 := by
    have hm' : (arCtxMem cx s0 ⋆
        (region (s0.w + BitVec.ofNat 64 baseTop) (s0.top.toNat - baseTop) ⋆
         region (s0.w + s0.top) (s0.wlen.toNat - s0.top.toNat) ⋆ R)) m :=
      sep_cast hm (by ac_rfl)
    unfold arCtxMem at hm'
    exact (sep_pure_l (φ := ArCtxLengthsOk s0) (P := fun m => (arCtxTree cx s0).eval m)
      (R := region (s0.w + BitVec.ofNat 64 baseTop) (s0.top.toNat - baseTop) ⋆
        region (s0.w + s0.top) (s0.wlen.toNat - s0.top.toNat) ⋆ R)).mp hm' |>.1
  rw [Func.wp]
  ar_unfold_body
  c0_hsplit_nobound
  · c0_hsteps; exact hQ false m (Or.inl ⟨rfl, s0, rfl, rfl, dyn_fail_wrap hfit hbase0 htop0 hm⟩)
  · have htop_le : s0.top.toNat ≤ s0.wlen.toNat := by c0_bv_omega [hc]
    clear hc
    c0_hsplit_nobound
    · c0_hsteps
      exact hQ false m (Or.inl ⟨rfl, s0, rfl, rfl, dyn_fail_wrap hfit hbase0 htop_le hm⟩)
    · have hrem4096 : 4096 ≤ s0.wlen.toNat - s0.top.toNat := by c0_bv_omega [hc]
      clear hc
      c0_hstraight
      refine wp_join_group (fun (v : Tup Val [i64]) mC =>
          mC = m ∧ v.1.toNat ≤ 300000000 ∧
          401 * v.1.toNat + 4096 ≤ s0.wlen.toNat - s0.top.toNat) ?_ ?_
      · rintro Jcap ⟨cap, ⟨⟩⟩ mC ⟨hmC, hcapMax, hcapRem⟩; cases hmC
        dsimp only at hcapMax hcapRem
        c0_hsplit_nobound
        · c0_hsteps
          exact hQ false m (Or.inl ⟨rfl, s0, rfl, rfl, dyn_fail_wrap hfit hbase0 htop_le hm⟩)
        · have hcap16 : 16 ≤ cap.toNat := by c0_bv_omega [hc]
          clear hc
          have hpw_nat : (cap * 12).toNat = 12 * cap.toNat := by c0_bv_omega [hcapMax]
          have h4cap_nat : (4 * cap).toNat = 4 * cap.toNat := by c0_bv_omega [hcapMax]
          have h8cap_nat : (8 * cap).toNat = 8 * cap.toNat := by c0_bv_omega [hcapMax]
          have h4pw_nat : (4 * (cap * 12)).toNat = 4 * (12 * cap.toNat) := by
            c0_bv_omega [hcapMax, hpw_nat]
          have h4vo_nat : (4 * cap + 4).toNat = 4 * cap.toNat + 4 := by
            c0_bv_omega [hcapMax]
          have hcap32_nat : (cap.setWidth 32).toNat = cap.toNat := by
            rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
          have hfin_bd := dyn_slack_le s0.top.toNat cap.toNat (align8_sub_le _) hcapRem
          let t0 := align8 s0.top.toNat
          let a4 := align8 (4 * cap.toNat)
          let a8 := 8 * cap.toNat
          let ap := 4 * (12 * cap.toNat)
          let avo := align8 (4 * cap.toNat + 4)
          let avs := align8 cap.toNat
          have ht0_le : baseTop ≤ t0 := Nat.le_trans hbase0 (align8_ge _)
          have ht0_8 : t0 % 8 = 0 := align8_mod _
          have ha4_8 : a4 % 8 = 0 := align8_mod _
          have ha8_8 : a8 % 8 = 0 := by dsimp only [a8]; omega
          have hap_8 : ap % 8 = 0 := by dsimp only [ap]; omega
          have havo_8 : avo % 8 = 0 := align8_mod _
          have havs_8 : avs % 8 = 0 := align8_mod _
          have ha8_al : align8 a8 = a8 := by unfold align8; omega
          have hap_al : align8 ap = ap := by unfold align8; omega
          c0_hsteps_nogrp
          let s1 : ArCtxState := { s0 with rs_cap := cap.setWidth 32, rs_pcap := cap * 12 }
          have hm0' : (arCtxMem cx s1 ⋆ (region (s0.w + BitVec.ofNat 64 baseTop)
              (s1.top.toNat - baseTop) ⋆ (region (s0.w + s1.top)
              (s0.wlen.toNat - s1.top.toNat) ⋆ R))) m :=
            dyn_ctx_bind (s' := s1) rfl (sep_cast hm (by ac_rfl))
          clear hm
          c0_hcall (dyn_alloc_step Γ hAlloc hm0' hwpos hfit rfl rfl hbase0 htop_le)
          intro p1 tp1 m1 hb1 ht1 hd1 hm1
          have hok1 := dyn_step_init hd1 (by rfl : align8 s1.top.toNat = t0) h4cap_nat rfl
          c0_hsteps_nogrp
          let s2 : ArCtxState := { s1 with top := tp1, rs_m := p1 }
          have hm : _ := dyn_ctx_bind (s' := s2) rfl hm
          clear hd1 hm0'
          c0_hcall (dyn_alloc_step Γ hAlloc hm hwpos hfit rfl rfl hb1 ht1)
          intro p2 tp2 m2 hb2 ht2 hd2 hm2
          have hok2 := dyn_step_chain hd2 hok1 h8cap_nat (by rw [ha8_al])
          c0_hsteps_nogrp
          let s3 : ArCtxState := { s2 with top := tp2, rs_l := p2 }
          have hm : _ := dyn_ctx_bind (s' := s3) rfl hm
          try clear m1; clear hb1 ht1 hd2
          c0_hcall (dyn_alloc_step Γ hAlloc hm hwpos hfit rfl rfl hb2 ht2)
          intro p3 tp3 m3 hb3 ht3 hd3 hm3
          have hok3 := dyn_step_chain hd3 hok2 h8cap_nat (by rw [ha8_al])
          c0_hsteps_nogrp
          let s4 : ArCtxState := { s3 with top := tp3, rs_h := p3 }
          have hm : _ := dyn_ctx_bind (s' := s4) rfl hm
          try clear m2; clear hb2 ht2 hd3
          c0_hcall (dyn_alloc_step Γ hAlloc hm hwpos hfit rfl rfl hb3 ht3)
          intro p4 tp4 m4 hb4 ht4 hd4 hm4
          have hok4 := dyn_step_chain hd4 hok3 h4pw_nat (by rw [hap_al])
          c0_hsteps_nogrp
          let s5 : ArCtxState :=
            { s4 with top := tp4, rs_pool := p4, tcap := cap.setWidth 32 }
          have hm : _ := dyn_ctx_bind (s' := s5) rfl hm
          try clear m3; clear hb3 ht3 hd4
          c0_hcall (dyn_alloc_step Γ hAlloc hm hwpos hfit rfl rfl hb4 ht4)
          intro p5 tp5 m5 hb5 ht5 hd5 hm5
          have hok5 := dyn_step_chain hd5 hok4 h4cap_nat rfl
          have hst5 := dyn_store_tm0 p5 hm5
          refine head_wp_store rfl (by simp) hst5 fun _ hm5 => ?_
          let s6 : ArCtxState := { s5 with top := tp5, tm := s5.tm.set 0 p5 }
          have hm5 : _ := dyn_ctx_bind (s' := s6) rfl hm5
          try clear m4; clear hb4 ht4 hd5
          c0_hsteps_nogrp
          c0_hcall (dyn_alloc_step Γ hAlloc hm5 hwpos hfit rfl rfl hb5 ht5)
          intro p6 tp6 m6 hb6 ht6 hd6 hm6
          have hok6 := dyn_step_chain hd6 hok5 h8cap_nat (by rw [ha8_al])
          have hst6 := dyn_store_ts0 p6 hm6
          refine head_wp_store rfl (by simp) hst6 fun _ hm6 => ?_
          let s7 : ArCtxState := { s6 with top := tp6, ts := s6.ts.set 0 p6 }
          have hm6 : _ := dyn_ctx_bind (s' := s7) rfl hm6
          try clear m5; clear hm5 hb5 ht5 hd6
          c0_hsteps_nogrp
          c0_hcall (dyn_alloc_step Γ hAlloc hm6 hwpos hfit rfl rfl hb6 ht6)
          intro p7 tp7 m7 hb7 ht7 hd7 hm7
          have hok7 := dyn_step_chain hd7 hok6 h8cap_nat (by rw [ha8_al])
          have hst7 := dyn_store_tl0 p7 hm7
          refine head_wp_store rfl (by simp) hst7 fun _ hm7 => ?_
          let s8 : ArCtxState := { s7 with top := tp7, tl := s7.tl.set 0 p7 }
          have hm7 : _ := dyn_ctx_bind (s' := s8) rfl hm7
          try clear m6; clear hm6 hb6 ht6 hd7
          c0_hsteps_nogrp
          c0_hcall (dyn_alloc_step Γ hAlloc hm7 hwpos hfit rfl rfl hb7 ht7)
          intro p8 tp8 m8 hb8 ht8 hd8 hm8
          have hok8 := dyn_step_chain hd8 hok7 h8cap_nat (by rw [ha8_al])
          have hst8 := dyn_store_th0 p8 hm8
          refine head_wp_store rfl (by simp) hst8 fun _ hm8 => ?_
          let s9 : ArCtxState := { s8 with top := tp8, th := s8.th.set 0 p8 }
          have hm8 : _ := dyn_ctx_bind (s' := s9) rfl hm8
          try clear m7; clear hm7 hb7 ht7 hd8
          c0_hsteps_nogrp
          c0_hcall (dyn_alloc_step Γ hAlloc hm8 hwpos hfit rfl rfl hb8 ht8)
          intro p9 tp9 m9 hb9 ht9 hd9 hm9
          have hok9 := dyn_step_chain hd9 hok8 h4cap_nat rfl
          have hst9 := dyn_store_tm1 p9 hm9
          refine head_wp_store rfl (by rw [BitVec.add_assoc]; rfl) hst9 fun _ hm9 => ?_
          let s10 : ArCtxState := { s9 with top := tp9, tm := s9.tm.set 1 p9 }
          have hm9 : _ := dyn_ctx_bind (s' := s10) rfl hm9
          try clear m8; clear hm8 hb8 ht8 hd9
          c0_hsteps_nogrp
          c0_hcall (dyn_alloc_step Γ hAlloc hm9 hwpos hfit rfl rfl hb9 ht9)
          intro p10 tp10 m10 hb10 ht10 hd10 hm10
          have hok10 := dyn_step_chain hd10 hok9 h8cap_nat (by rw [ha8_al])
          have hst10 := dyn_store_ts1 p10 hm10
          refine head_wp_store rfl (by rw [BitVec.add_assoc]; rfl) hst10 fun _ hm10 => ?_
          let s11 : ArCtxState := { s10 with top := tp10, ts := s10.ts.set 1 p10 }
          have hm10 : _ := dyn_ctx_bind (s' := s11) rfl hm10
          try clear m9; clear hm9 hb9 ht9 hd10
          c0_hsteps_nogrp
          c0_hcall (dyn_alloc_step Γ hAlloc hm10 hwpos hfit rfl rfl hb10 ht10)
          intro p11 tp11 m11 hb11 ht11 hd11 hm11
          have hok11 := dyn_step_chain hd11 hok10 h8cap_nat (by rw [ha8_al])
          have hst11 := dyn_store_tl1 p11 hm11
          refine head_wp_store rfl (by rw [BitVec.add_assoc]; rfl) hst11 fun _ hm11 => ?_
          let s12 : ArCtxState := { s11 with top := tp11, tl := s11.tl.set 1 p11 }
          have hm11 : _ := dyn_ctx_bind (s' := s12) rfl hm11
          try clear m10; clear hm10 hb10 ht10 hd11
          c0_hsteps_nogrp
          c0_hcall (dyn_alloc_step Γ hAlloc hm11 hwpos hfit rfl rfl hb11 ht11)
          intro p12 tp12 m12 hb12 ht12 hd12 hm12
          have hok12 := dyn_step_chain hd12 hok11 h8cap_nat (by rw [ha8_al])
          have hst12 := dyn_store_th1 p12 hm12
          refine head_wp_store rfl (by rw [BitVec.add_assoc]; rfl) hst12 fun _ hm12 => ?_
          let s13a : ArCtxState := { s12 with top := tp12, th := s12.th.set 1 p12 }
          have hm12 : _ := dyn_ctx_bind (s' := s13a) rfl hm12
          try clear m11; clear hm11 hb11 ht11 hd12
          c0_hsteps_nogrp
          let s13 : ArCtxState := { s13a with pcap := cap * 12 }
          have hm : _ := dyn_ctx_bind (s' := s13) rfl hm
          clear hm12
          c0_hcall (dyn_alloc_step Γ hAlloc hm hwpos hfit rfl rfl hb12 ht12)
          intro p13 tp13 m13 hb13 ht13 hd13 hm13
          have hok13 := dyn_step_chain hd13 hok12 h4pw_nat (by rw [hap_al])
          have hst13 := dyn_store_pool0 p13 hm13
          refine head_wp_store rfl (by simp) hst13 fun _ hm13 => ?_
          let s14 : ArCtxState := { s13 with top := tp13, pool := s13.pool.set 0 p13 }
          have hm13 : _ := dyn_ctx_bind (s' := s14) rfl hm13
          try clear m12; clear hb12 ht12 hd13
          c0_hsteps_nogrp
          c0_hcall (dyn_alloc_step Γ hAlloc hm13 hwpos hfit rfl rfl hb13 ht13)
          intro p14 tp14 m14 hb14 ht14 hd14 hm14
          have hok14 := dyn_step_chain hd14 hok13 h4pw_nat (by rw [hap_al])
          have hst14 := dyn_store_pool1 p14 hm14
          refine head_wp_store rfl (by rw [BitVec.add_assoc]; rfl) hst14 fun _ hm14 => ?_
          let s15a : ArCtxState := { s14 with top := tp14, pool := s14.pool.set 1 p14 }
          have hm14 : _ := dyn_ctx_bind (s' := s15a) rfl hm14
          try clear m13; clear hm13 hb13 ht13 hd14
          c0_hsteps_nogrp
          let s15 : ArCtxState := { s0 with
            top := tp14, rs_cap := cap.setWidth 32, rs_pcap := cap * 12,
            rs_m := p1, rs_l := p2, rs_h := p3, rs_pool := p4, tcap := cap.setWidth 32,
            tm := (s0.tm.set 0 p5).set 1 p9, ts := (s0.ts.set 0 p6).set 1 p10,
            tl := (s0.tl.set 0 p7).set 1 p11, th := (s0.th.set 0 p8).set 1 p12,
            pcap := cap * 12, pool := (s0.pool.set 0 p13).set 1 p14, qcap := cap.setWidth 32 }
          have hm : _ := dyn_ctx_bind (s' := s15) rfl hm
          clear hm14
          change wp Γ Q X (dynTailExpr cx cap) _
          refine dyn_alloc_qr_wp Γ hAlloc hlens hwpos hfit hcap16 hcapMax hpw_nat h4cap_nat
            h8cap_nat h4pw_nat h4vo_nat hcap32_nat ht0_le hfin_bd hb14 ht14 ha8_al hap_al ?_ hm hQ
          intro h14
          have ha := fun {b1 b2 : Bool} (h : (b1 && b2) = true) => ((Bool.and_eq_true b1 b2).mp h).1
          have h13 := ha h14; have h12 := ha h13; have h11 := ha h12; have h10 := ha h11
          have h9 := ha h10; have h8 := ha h9; have h7 := ha h8; have h6 := ha h7
          have h5 := ha h6; have h4 := ha h5; have h3 := ha h4; have h2 := ha h3; have h1 := ha h2
          have hpw64 : ∀ {x : BitVec 64} {a b : Nat},
              x = s0.w + BitVec.ofNat 64 a → a = b → x = s0.w + BitVec.ofNat 64 b :=
            fun h hab => hab ▸ h
          exact ⟨by have := (hok14.1 h14).2.2.2; dsimp only [t0, a4, a8, ap] at *; omega,
            ⟨hpw64 (hok1.1 h1).2.1 (by omega), hpw64 (hok2.1 h2).2.1 (by omega),
             hpw64 (hok3.1 h3).2.1 (by omega), hpw64 (hok4.1 h4).2.1 (by omega)⟩,
            ⟨hpw64 (hok5.1 h5).2.1 (by omega), hpw64 (hok6.1 h6).2.1 (by omega),
             hpw64 (hok7.1 h7).2.1 (by omega), hpw64 (hok8.1 h8).2.1 (by omega),
             hpw64 (hok9.1 h9).2.1 (by omega), hpw64 (hok10.1 h10).2.1 (by omega),
             hpw64 (hok11.1 h11).2.1 (by omega), hpw64 (hok12.1 h12).2.1 (by omega),
             hpw64 (hok13.1 h13).2.1 (by omega), hpw64 (hok14.1 h14).2.1 (by omega)⟩⟩
      · intro Jcap hJcap
        have hunit : (20 + 4 * 12 + 56 + 8 * 12 + 36 + 4 + 40 + 4 * 12 + 5 + 4 * 12) %
            2 ^ 64 = 401 := by decide
        have hnum : (2 ^ 64 - 4096 + (2 ^ 64 - s0.top.toNat + s0.wlen.toNat)) % 2 ^ 64 =
            s0.wlen.toNat - s0.top.toNat - 4096 := by have := s0.wlen.isLt; omega
        c0_hsplit_nobound
        · c0_hsteps
          refine hJcap (300000000#64, ⟨⟩) m ⟨rfl, by decide, ?_⟩
          dsimp only; simp only [BitVec.reduceToNat] at hc; rw [hunit, hnum] at hc
          have h3e8 : (300000000#64 : BitVec 64).toNat = 300000000 := rfl
          have := Nat.div_mul_le_self (s0.wlen.toNat - s0.top.toNat - 4096) 401; omega
        · c0_hsteps
          simp only [BitVec.reduceToNat] at hc; rw [hunit, hnum] at hc
          have hle : (s0.wlen.toNat - s0.top.toNat - 4096) / 401 ≤ 300000000 := Nat.le_of_not_lt hc
          have hrew : ∀ x : BitVec 64, x.toNat = (s0.wlen.toNat - s0.top.toNat - 4096) / 401 →
              x.toNat ≤ 300000000 ∧ 401 * x.toNat + 4096 ≤ s0.wlen.toNat - s0.top.toNat :=
            fun x hx => by
              rw [hx]; have := Nat.div_mul_le_self (s0.wlen.toNat - s0.top.toNat - 4096) 401
              exact ⟨hle, by omega⟩
          refine hJcap (_, ⟨⟩) m ⟨rfl, hrew _ ?_⟩; dsimp only; rw [BitVec.toNat_udiv,
            show (20 + 4 * 12 + 56 + 8 * 12 + 36 + 4 + 40 + 4 * 12 + 5 + 4 * 12 : BitVec 64) =
              401#64 from rfl, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by decide),
            BitVec.toNat_sub_of_le (by
              rw [BitVec.le_def, BitVec.toNat_sub_of_le (BitVec.le_def.mpr htop_le)]
              simpa using hrem4096),
            BitVec.toNat_sub_of_le (BitVec.le_def.mpr htop_le)]; rfl

end
