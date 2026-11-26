/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep12BProofCong2a
import LeanQbe.T.Examples.Kissat.FullCongLemmas1
import LeanQbe.T.Examples.Kissat.FullCongLemmas2
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import LeanQbe.T.Logic.C0Agrees
import LeanQbe.T.Logic.MemLemmas

/-!
# Kissat Fidelity Step 12B — Congruence `eval_gate` Proof (`FullFidelityStep12BProofCong2b`)

Proves the parametric `(Γ : Env)` `Func.wp` contract `full_cong_eval_gate_s12b_wp` for
`FullFidelityStep12B.full_cong_eval_gate_body` against `step12BCongEvalGateSpec`:
wide AND arity up to `congruenceandarity = 1,000,000` (`tag = 0` for `≤ 64`, `tag = 3` for `≥ 65`),
XOR LHS self-cancellation, ITE-to-XOR & ITE-to-AND rewriting, 128-probe HT using `lit_mark`
wide-AND matching, and dynamic power-of-2 `occ_bkt ≤ 1,048,576`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep12B

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullCongHelpers
open LeanQbe.T.Examples.Kissat.FullM3CongBva
open LeanQbe.T.Examples.Kissat.FullM6CongSubst
open LeanQbe.T.Examples.Kissat.FullM8FidV12
open LeanQbe.T.Examples.Kissat.FullFidelityCong
open Kraken.Bedrock2.Test
open scoped FullArenaTactics Full.FullCongTactics
open scoped LeanQbe.T.Examples.Kissat.FullM6CongSubst.M6bHeadTactics

section EvalGateHelpers

/-! ## 1. Local Constant-Index `tmp` Rules & Fold/Self-Cancel Sub-Proofs -/

private theorem s12b_load_full_tmp0 {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (FullMem c s ⋆ R) m) (h0 : 0 < s.core.tmp.length) :
    loadVal m i32 (c.pTmp + 0#64) = some (s.core.tmp[0]'h0) := by
  simpa using FullArenaTactics.c0_load_full_tmp (i := 0#64) (by simpa using h0) hm

private theorem s12b_load_full_tmp1 {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (FullMem c s ⋆ R) m) (h1 : 1 < s.core.tmp.length) :
    loadVal m i32 (c.pTmp + 4#64) = some (s.core.tmp[1]'h1) := by
  simpa using FullArenaTactics.c0_load_full_tmp (i := 1#64) (by simpa using h1) hm

private theorem s12b_load_full_tmp2 {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (FullMem c s ⋆ R) m) (h2 : 2 < s.core.tmp.length) :
    loadVal m i32 (c.pTmp + 8#64) = some (s.core.tmp[2]'h2) := by
  simpa using FullArenaTactics.c0_load_full_tmp (i := 2#64) (by simpa using h2) hm

private theorem s12b_store_full_tmp0 {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (v : BitVec 32) (h0 : 0 < s.core.tmp.length) (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 (c.pTmp + 0#64) ∧
      (FullMem c { s with core := { s.core with tmp := s.core.tmp.set 0 v } } ⋆ R)
        (storeMem m i32 (c.pTmp + 0#64) v) := by
  simpa using FullArenaTactics.c0_store_full_tmp (i := 0#64) v (by simpa using h0) hm

private theorem s12b_store_full_tmp1 {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (v : BitVec 32) (h1 : 1 < s.core.tmp.length) (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 (c.pTmp + 4#64) ∧
      (FullMem c { s with core := { s.core with tmp := s.core.tmp.set 1 v } } ⋆ R)
        (storeMem m i32 (c.pTmp + 4#64) v) := by
  simpa using FullArenaTactics.c0_store_full_tmp (i := 1#64) v (by simpa using h1) hm

private theorem s12b_store_full_tmp2 {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (v : BitVec 32) (h2 : 2 < s.core.tmp.length) (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 (c.pTmp + 8#64) ∧
      (FullMem c { s with core := { s.core with tmp := s.core.tmp.set 2 v } } ⋆ R)
        (storeMem m i32 (c.pTmp + 8#64) v) := by
  simpa using FullArenaTactics.c0_store_full_tmp (i := 2#64) v (by simpa using h2) hm

attribute [local c0_load] s12b_load_full_tmp0 s12b_load_full_tmp1 s12b_load_full_tmp2
attribute [local c0_store] s12b_store_full_tmp0 s12b_store_full_tmp1 s12b_store_full_tmp2

private theorem s12bEv_afterFold_wp {Γ : Env} {ctx : Step12BEvCtx} {s0 su : FullState}
    {Q : Post [i64]} {X : XPost} {uf : Val i64} {mu : Mem 64}
    {chArg : Arg Val .bool} {kDone : Tup Val [.bool] → Expr Val Cont [i64]}
    (hex : Step12BEvOutCtx ctx s0 Q) (hoku : Step12BEvStOk ctx su)
    (hu2 : uf = 2#64 → ctx.F0.Unsat) (hmu : (FullMem ctx.cfg su ⋆ ctx.R) mu)
    (hk : ∀ ch' : Bool, wp Γ Q X (kDone (ch', ())) mu) :
    wp Γ Q X (.let_ ⟨.cmp .eq i64, (.var uf, (.imm 2#64, ()))⟩ fun p2 =>
      .jnz (.var p2.1) (.ret (.imm 2#64, ()))
        (.group (sig := [[.bool]]) (fun _ => .cons kDone .nil) fun Js =>
          .let_ ⟨.cmp .eq i64, (.var uf, (.imm 1#64, ()))⟩ fun p1 =>
          .jnz (.var p1.1) (.jump Js.1 (.imm true, ())) (.jump Js.1 (chArg, ())))) mu := by
  m6b_split
  · m6b_let; exact step12BEv_ret2 hex hoku (hu2 (beq_iff_eq.mp hc)) hmu
  · m6b_to_group
    refine wp_join_group (ts := [.bool]) (fun _ m_af => m_af = mu)
      (fun _ ⟨ch', ⟨⟩⟩ m_af hm_af => by rw [hm_af]; m6b_let; exact hk ch') ?_
    intro Jef hJef; m6b_split
    · m6b_let; exact hJef (true, ()) mu rfl
    · m6b_let; exact hJef (chArg.val, ()) mu rfl

private theorem s12bEv_afterEquiv_wp {Γ : Env} {ctx : Step12BEvCtx} {s0 st0 : FullState}
    {Q : Post [i64]} {X : XPost} {hPtr ctrl_off : Val i64} {ef : Val i64}
    {a1 a2 : Arg Val i32} {chArg : Arg Val .bool}
    {kDone : Tup Val [.bool] → Expr Val Cont [i64]}
    (hex : Step12BEvOutCtx ctx s0 Q)
    (hEnqVar : ∀ a m Q X, step12BCongEnqVarSpec a m Q X →
      Γ "full_cong_enq_var" [i64, i64, i32] [] a m Q X)
    (hcfg : hPtr = ctx.cfg.hdr) (hctrl : ctrl_off.toNat = ctx.ctrl_off)
    (hok : Step12BEvStOk ctx st0) (hef2 : ef = 2#64 → ctx.F0.Unsat) {mm : Mem 64}
    (hmu : (FullMem ctx.cfg st0 ⋆ ctx.R) mm)
    (hk : ∀ (st_f : FullState) (m_f : Mem 64) (ch_f : Bool),
      Step12BEvStOk ctx st_f → st_f.core.tmp = st0.core.tmp →
      (FullMem ctx.cfg st_f ⋆ ctx.R) m_f → wp Γ Q X (kDone (ch_f, ())) m_f) :
    wp Γ Q X (.let_ ⟨.cmp .eq i64, (.var ef, (.imm 2#64, ()))⟩ fun p2 =>
      .jnz (.var p2.1) (.ret (.imm 2#64, ()))
        (.group (sig := [[.bool]]) (fun _ => .cons kDone .nil) fun Js =>
          .let_ ⟨.cmp .eq i64, (.var ef, (.imm 1#64, ()))⟩ fun p1 =>
          .jnz (.var p1.1)
            (.let_ ⟨.lshr i32, (a1, (.imm 1#32, ()))⟩ fun s1 =>
             .call "full_cong_enq_var" (as := [i64, i64, i32]) (bs := [])
               (Arg.var hPtr, (Arg.var ctrl_off, (Arg.var s1.1, ()))) fun _ =>
             .let_ ⟨.lshr i32, (a2, (.imm 1#32, ()))⟩ fun s2 =>
             .call "full_cong_enq_var" (as := [i64, i64, i32]) (bs := [])
               (Arg.var hPtr, (Arg.var ctrl_off, (Arg.var s2.1, ()))) fun _ =>
             .jump Js.1 (.imm true, ()))
            (.jump Js.1 (chArg, ())))) mm := by
  subst hcfg
  m6b_split
  · m6b_let; exact step12BEv_ret2 hex hok (hef2 (beq_iff_eq.mp hc)) hmu
  · m6b_to_group; refine wp_join_group (ts := [.bool])
      (fun (_, ()) m_af => ∃ s_af : FullState,
        Step12BEvStOk ctx s_af ∧ s_af.core.tmp = st0.core.tmp ∧
        (FullMem ctx.cfg s_af ⋆ ctx.R) m_af)
      (fun _ ⟨ch_f, ⟨⟩⟩ m_f ⟨st_f, hok_f, htmp_f, hm_f⟩ => by
        m6b_let; exact hk st_f m_f ch_f hok_f htmp_f hm_f) ?_
    intro Jef hJef; m6b_split
    · m6b_steps; m6b_call hEnqVar
      refine step12BEv_enq hex hok hctrl hmu fun st_e1 m_e1 hok_e1 ht_e1 hm_e1 => ?_
      m6b_steps; m6b_call hEnqVar
      refine step12BEv_enq hex hok_e1 hctrl hm_e1 fun st_e2 m_e2 hok_e2 ht_e2 hm_e2 => ?_
      m6b_let; exact hJef (true, ()) m_e2 ⟨st_e2, hok_e2, ht_e2.trans ht_e1, hm_e2⟩
    · m6b_let; exact hJef (chArg.val, ()) mm ⟨st0, hok, rfl, hmu⟩

local macro "s12b_after_fold " hex:ident hres:ident _ch0:ident hc_ok:ident
    _mm:ident hmem:ident chVar:ident " => " k:tacticSeq : tactic =>
  `(tactic| (
    refine s12bEv_afterFold_wp $hex $hc_ok $hres $hmem
      fun $chVar => by m6b_let; ($k:tacticSeq)))

local macro "s12b_after_equiv_enq2 " _ctx:ident hex:ident henq:ident _st0:ident hres:ident
    _ch0:ident hc_ok:ident _mm:ident hmem:ident stVar:ident hokVar:ident mVar:ident hmVar:ident
    chVar:ident " => " k:tacticSeq : tactic =>
  `(tactic| (
    refine s12bEv_afterEquiv_wp $hex $henq rfl rfl $hc_ok $hres $hmem
      fun $stVar $mVar $chVar $hokVar _ $hmVar => by m6b_let; ($k:tacticSeq)))

private def s12bEv_tag1_selfcancel_expr {V : Ty → Type} {L : List Ty → Type}
    (hPtr pTmp ctrl_off : V i64) (next_ep lhs' jd ua : V i32)
    (Jsc : L [i32, .bool, .bool, i32]) : Expr V L [i64] :=
  .let_ ⟨.cmp .ugt i32, (.var ua, (.imm 0, ()))⟩ fun p0 =>
  .jnz (.var p0.1)
    (.let_ ⟨.not i32, (.imm 1, ())⟩ fun p_not =>
     .let_ ⟨.and i32, (.var lhs', (.var p_not.1, ()))⟩ fun p_tgt =>
     .group (sig := [[i32, i32]]) (fun Js_f => .cons (fun p =>
       .group (sig := [[.bool, .bool, i32]]) (fun Js_2 => .cons (fun p_1 =>
         .jump Jsc (.var p.1, (.var p_1.1, (.var p_1.2.1, (.var p_1.2.2.1, ()))))) .nil)
       fun Js_2 =>
       .let_ ⟨.cmp .ult i32, (.var p.2.1, (.var ua, ()))⟩ fun p_lt =>
       .jnz (.var p_lt.1)
         (.group (sig := [[i32]]) (fun Js_sh => .cons (fun p_jj =>
           .let_ ⟨.add i32, (.var p_jj.1, (.imm 1, ()))⟩ fun p_jj1 =>
           .let_ ⟨.cmp .ult i32, (.var p_jj1.1, (.var ua, ()))⟩ fun p_sh =>
           .jnz (.var p_sh.1)
             (.let_ ⟨.zext 32 64, (.var p_jj.1, ())⟩ fun p4 =>
              .let_ ⟨.mul i64, (.var p4.1, (.imm 4, ()))⟩ fun p5 =>
              .let_ ⟨.add i64, (.var pTmp, (.var p5.1, ()))⟩ fun p6 =>
              .let_ ⟨.add i32, (.var p_jj.1, (.imm 1, ()))⟩ fun p7 =>
              .let_ ⟨.zext 32 64, (.var p7.1, ())⟩ fun p8 =>
              .let_ ⟨.mul i64, (.var p8.1, (.imm 4, ()))⟩ fun p9 =>
              .let_ ⟨.add i64, (.var pTmp, (.var p9.1, ()))⟩ fun p10 =>
              .load i32 (.var p10.1) fun ld =>
              .store (t := i32) (.var ld) (.var p6.1)
                (.let_ ⟨.add i32, (.var p_jj.1, (.imm 1, ()))⟩ fun pn =>
                 .jump Js_sh.1 (.var pn.1, ())))
             (.let_ ⟨.sub i32, (.var ua, (.imm 1, ()))⟩ fun p_ua' =>
              .let_ ⟨.and i32, (.var lhs', (.imm 1, ()))⟩ fun p_ls =>
              .group (sig := [[.bool, .bool]]) (fun Js_u => .cons (fun p_5 =>
                .jump Js_2.1 (.var p_5.1, (.var p_5.2.1, (.var p_ua'.1, ())))) .nil)
              fun Js_u =>
              .let_ ⟨.cmp .eq i32, (.var p_ua'.1, (.imm 0, ()))⟩ fun pe0 =>
              .jnz (.var pe0.1)
                (.let_ ⟨.cmp .ne i32, (.var p_ls.1, (.imm 0, ()))⟩ fun pnz =>
                 .jnz (.var pnz.1)
                    (.let_ ⟨.add i64, (.var hPtr, (.imm 1024, ()))⟩ fun pinc =>
                     .store (t := i64) (.imm 1) (.var pinc.1) (Expr.ret (Arg.imm 2, ())))
                    (Expr.jump Js_u.1 (Arg.imm false, (Arg.imm false, ()))))
                 (Expr.group (sig := [[.bool, .bool]]) (fun Js_u1 => .cons (fun p_5 =>
                   Expr.jump Js_u.1 (.var p_5.1, (.var p_5.2.1, ()))) .nil)
                  fun Js_u1 =>
                  .let_ ⟨.cmp .eq i32, (.var p_ua'.1, (.imm 1, ()))⟩ fun pe1 =>
                  .jnz (.var pe1.1)
                    (.let_ ⟨.sext 32 64, (.imm 0, ())⟩ fun p0a =>
                     .let_ ⟨.mul i64, (.var p0a.1, (.imm 4, ()))⟩ fun p0b =>
                     .let_ ⟨.add i64, (.var pTmp, (.var p0b.1, ()))⟩ fun p0c =>
                     .load i32 (.var p0c.1) fun ld0 =>
                     .let_ ⟨.xor i32, (.imm 1, (.var p_ls.1, ()))⟩ fun px1 =>
                     .let_ ⟨.xor i32, (.var ld0, (.var px1.1, ()))⟩ fun pul =>
                     .call "full_cong_unit_fold" (as := [i64, i32, i32]) (bs := [i64])
                       (Arg.var hPtr, (Arg.var pul.1, (Arg.var next_ep, ()))) fun ru =>
                     .let_ ⟨.cmp .eq i64, (.var ru.1, (.imm 2, ()))⟩ fun pr2 =>
                     .jnz (.var pr2.1) (Expr.ret (Arg.imm 2, ()))
                       (Expr.group (sig := [[.bool]]) (fun Jch => .cons (fun pch =>
                         Expr.jump Js_u1.1 (Arg.imm false, (.var pch.1, ()))) .nil)
                        fun Jch =>
                        .let_ ⟨.cmp .eq i64, (.var ru.1, (.imm 1, ()))⟩ fun pr1 =>
                        .jnz (.var pr1.1) (Expr.jump Jch.1 (Arg.imm true, ()))
                          (Expr.jump Jch.1 (Arg.imm false, ()))))
                    (Expr.group (sig := [[.bool, .bool]]) (fun Js_u2 => .cons (fun p_5 =>
                      Expr.jump Js_u1.1 (.var p_5.1, (.var p_5.2.1, ()))) .nil)
                     fun Js_u2 =>
                     .let_ ⟨.cmp .eq i32, (.var p_ua'.1, (.imm 2, ()))⟩ fun pe2 =>
                     .jnz (.var pe2.1)
                       (.let_ ⟨.sext 32 64, (.imm 0, ())⟩ fun p0a =>
                        .let_ ⟨.mul i64, (.var p0a.1, (.imm 4, ()))⟩ fun p0b =>
                        .let_ ⟨.add i64, (.var pTmp, (.var p0b.1, ()))⟩ fun p0c =>
                        .load i32 (.var p0c.1) fun ld0 =>
                        .let_ ⟨.xor i32, (.var ld0, (.var p_ls.1, ()))⟩ fun pa0 =>
                        .let_ ⟨.sext 32 64, (.imm 1, ())⟩ fun p1a =>
                        .let_ ⟨.mul i64, (.var p1a.1, (.imm 4, ()))⟩ fun p1b =>
                        .let_ ⟨.add i64, (.var pTmp, (.var p1b.1, ()))⟩ fun p1c =>
                        .load i32 (.var p1c.1) fun ld1 =>
                        .call "full_cong_equiv_fold" (as := [i64, i32, i32, i32]) (bs := [i64])
                          (Arg.var hPtr, (Arg.var pa0.1, (Arg.var ld1, (Arg.var next_ep, ()))))
                          fun re =>
                        .let_ ⟨.cmp .eq i64, (.var re.1, (.imm 2, ()))⟩ fun pe_2 =>
                        .jnz (.var pe_2.1) (Expr.ret (Arg.imm 2, ()))
                          (Expr.group (sig := [[.bool]]) (fun Jch => .cons (fun pch =>
                            Expr.jump Js_u2.1 (Arg.imm false, (.var pch.1, ()))) .nil)
                           fun Jch =>
                           .let_ ⟨.cmp .eq i64, (.var re.1, (.imm 1, ()))⟩ fun pe_1 =>
                           .jnz (.var pe_1.1)
                             (.let_ ⟨.lshr i32, (.var pa0.1, (.imm 1, ()))⟩ fun ps0 =>
                              .call "full_cong_enq_var" (as := [i64, i64, i32]) (bs := [])
                                (Arg.var hPtr, (Arg.var ctrl_off, (Arg.var ps0.1, ()))) fun _ =>
                              .let_ ⟨.lshr i32, (.var ld1, (.imm 1, ()))⟩ fun ps1 =>
                              .call "full_cong_enq_var" (as := [i64, i64, i32]) (bs := [])
                                (Arg.var hPtr, (Arg.var ctrl_off, (Arg.var ps1.1, ()))) fun _ =>
                              Expr.jump Jch.1 (Arg.imm true, ()))
                             (Expr.jump Jch.1 (Arg.imm false, ()))))
                       (Expr.jump Js_u2.1 (Arg.imm false, (Arg.imm false, ()))))))
            ) .nil)
           fun Js_sh => Expr.jump Js_sh.1 (.var p.2.1, ()))
          (Expr.jump Js_2.1 (Arg.imm true, (Arg.imm false, (.var ua, ()))))
      ) .nil)
     fun Js_f =>
     Expr.group (sig := [[i32]]) (fun Js_i => .cons (fun pi =>
       .let_ ⟨.cmp .ult i32, (.var pi.1, (.var ua, ()))⟩ fun p_il =>
       .jnz (.var p_il.1)
         (.let_ ⟨.zext 32 64, (.var pi.1, ())⟩ fun p3 =>
          .let_ ⟨.mul i64, (.var p3.1, (.imm 4, ()))⟩ fun p4 =>
          .let_ ⟨.add i64, (.var pTmp, (.var p4.1, ()))⟩ fun p5 =>
          .load i32 (.var p5.1) fun ld =>
          .let_ ⟨.cmp .eq i32, (.var ld, (.var p_tgt.1, ()))⟩ fun peq =>
          .jnz (.var peq.1) (Expr.jump Js_f.1 (.var pi.1, (.var pi.1, ())))
            (.let_ ⟨.add i32, (.var pi.1, (.imm 1, ()))⟩ fun pii1 =>
             Expr.jump Js_i.1 (.var pii1.1, ())))
         (Expr.jump Js_f.1 (.var pi.1, (.var ua, ())))) .nil)
     fun Js_i => Expr.jump Js_i.1 (Arg.imm 0, ()))
    (Expr.jump Jsc (.var jd, (Arg.imm true, (Arg.imm false, (.var ua, ())))))

private theorem s12bEv_tag1_selfcancel_wp {Γ : Env} {ctx : Step12BEvCtx} {s0 : FullState}
    {Q : Post [i64]} {X : XPost} {repri tmpd : List (BitVec 32)}
    {hPtr pTmp ctrl_off : Val i64} {next_ep lhs' jd ua : Val i32}
    {Jsc : Cont [i32, .bool, .bool, i32]} {md : Mem 64}
    (hexit : Step12BEvOutCtx ctx s0 Q)
    (hUnitFold : ∀ a m Q X, m3CongUnitFoldSpec a m Q X →
      Γ "full_cong_unit_fold" [i64, i32, i32] [i64] a m Q X)
    (hEquivFold : ∀ a m Q X, m3CongEquivFoldSpec a m Q X →
      Γ "full_cong_equiv_fold" [i64, i32, i32, i32] [i64] a m Q X)
    (hEnqVar : ∀ a m Q X, step12BCongEnqVarSpec a m Q X →
      Γ "full_cong_enq_var" [i64, i64, i32] [] a m Q X)
    (h_hdr : hPtr = ctx.cfg.hdr) (h_tmp : pTmp = ctx.cfg.pTmp)
    (h_ctrl : ctrl_off.toNat = ctx.ctrl_off)
    (hrli : repri.length = 2 * ctx.cfg.max_vars)
    (htl_d : tmpd.length = ctx.cfg.max_vars)
    (hrepri : FullCongReprInv ctx.F_cur (2 * ctx.cv0) repri)
    (hokd : Step12BEvStOk ctx (wsState s0 repri tmpd))
    (hlhs'_lt : lhs'.toNat < 2 * ctx.cv0) (hua_cv : ua.toNat ≤ ctx.cv0)
    (hlt_d : ∀ q < ua.toNat,
      (tmpd[q]?.getD 0#32).toNat < 2 * ctx.cv0 ∧ (tmpd[q]?.getD 0#32).toNat % 2 = 0)
    (hxor_d : XorListGateDef (cnfOfClauses ctx.F_cur) lhs'.toNat
      ((tmpd.take ua.toNat).map BitVec.toNat))
    (hmd : (FullMem ctx.cfg (wsState s0 repri tmpd) ⋆ ctx.R) md)
    (hJsc : ∀ (isc : Val i32) (nh_sc ch_sc : Bool) (ua_sc : Val i32) (msc : Mem 64),
      (nh_sc = true → msc = md ∧ ua_sc = ua) →
      (nh_sc = false → ∃ st_sc : FullState,
        Step12BEvStOk ctx st_sc ∧ (FullMem ctx.cfg st_sc ⋆ ctx.R) msc) →
      Jsc (isc, nh_sc, ch_sc, ua_sc, ()) msc) :
    wp Γ Q X (s12bEv_tag1_selfcancel_expr hPtr pTmp ctrl_off next_ep lhs' jd ua Jsc) md := by
  subst h_hdr h_tmp
  let c := ctx.cfg; let F_cur := ctx.F_cur; let cv0 := ctx.cv0; let R := ctx.R
  have hsc := c.hscr; have hmx := c.hmaxv; unfold dimacsBound at hsc hmx
  have hw0 := hokd.1.2.1
  have hcv0_eq : s0.core.cur_vars = cv0 := hokd.2.1
  have hcv_le : cv0 ≤ c.max_vars := by rw [← hcv0_eq]; exact hokd.1.1.core_ok.cur_vars_le
  have hua_tmpd : ua.toNat ≤ tmpd.length := by rw [htl_d]; exact Nat.le_trans hua_cv hcv_le
  unfold s12bEv_tag1_selfcancel_expr
  m6b_split
  rotate_left
  · m6b_let; exact hJsc jd true false ua md (fun _ => ⟨rfl, rfl⟩) (fun h => by cases h)
  have hua_pos : 0 < ua.toNat := bv32_ult_lt hc; clear hc; m6b_to_group
  refine wp_loop_break_group (brkTs := [i32, i32]) (lpTs := [i32])
    (fun (ii, self_i, ()) ms => ms = md ∧ self_i.toNat ≤ ua.toNat ∧
      (self_i.toNat < ua.toNat → tmpd[self_i.toNat]?.getD 0#32 = lhs' &&& ~~~1#32))
    (fun rem (ii, ()) ms =>
      rem = ua.toNat - ii.toNat ∧ ms = md ∧ ii.toNat ≤ ua.toNat) ?_ ?_ ?_
  · rintro _ ⟨ii, self_i, ⟨⟩⟩ ms ⟨hms, hsi_le, hsi_eq⟩; subst ms
    m6b_to_group; refine wp_join_group (ts := [.bool, .bool, i32])
      (fun (nh', ch', ua', ()) m' =>
        (nh' = true → m' = md ∧ ua' = ua) ∧
        (nh' = false → ∃ st_sc : FullState, Step12BEvStOk ctx st_sc ∧ (FullMem c st_sc ⋆ R) m'))
      (fun _ ⟨nh', ch', ua', ⟨⟩⟩ m' h => by m6b_let; exact hJsc ii nh' ch' ua' m' h.1 h.2) ?_
    intro Jsc_s hJsc_s; m6b_split
    rotate_left
    · m6b_let; exact hJsc_s (true, false, ua, ()) md ⟨fun _ => ⟨rfl, rfl⟩, fun h => by cases h⟩
    have hsi_lt : self_i.toNat < ua.toNat := bv32_ult_lt hc; clear hc
    have hget_si := hsi_eq hsi_lt
    let xs_er := (tmpd.take ua.toNat).eraseIdx self_i.toNat
    m6b_to_group
    refine wp_loop_inv (ts := [i32])
      (fun (jj, ()) mj => ∃ tmpj : List (BitVec 32), tmpj.length = c.max_vars ∧
        self_i.toNat ≤ jj.toNat ∧ jj.toNat < ua.toNat ∧
        (∀ k < jj.toNat, tmpj[k]? = xs_er[k]?) ∧
        (∀ k, jj.toNat + 1 ≤ k → k < ua.toNat → tmpj[k]? = tmpd[k]?) ∧
        (FullMem c (wsState s0 repri tmpj) ⋆ R) mj)
      (fun (jj, ()) _ => ua.toNat - 1 - jj.toNat)
      (fun Jsh hJsh => by
        m6b_steps; exact hJsh (self_i, ()) md ⟨tmpd, htl_d, Nat.le_refl _, hsi_lt,
          (fun k hk => by rw [list_getElem?_eraseIdx_lt _ hk, List.getElem?_take_of_lt (by omega)]),
          fun _ _ _ => rfl, hmd⟩)
      (fun Jsh (jj, ()) mj ⟨tmpj, htl_j, hsi_jj, hjj_lt, hpref_j, htail_j, hmj⟩ ihsh => ?_)
    have hjj1_n : (jj + 1#32).toNat = jj.toNat + 1 := bv32_add1_lt_of (by omega)
    m6b_split
    · have hjj1_lt : jj.toNat + 1 < ua.toNat := by rw [← hjj1_n]; exact bv32_ult_lt hc
      have hua_tmpj : ua.toNat ≤ tmpj.length := by rw [htl_j]; exact Nat.le_trans hua_cv hcv_le
      have hjj_arr : (jj.setWidth 64).toNat < tmpj.length := by rw [bv_zext32_toNat]; omega
      have hjj1_arr : ((jj + 1#32).setWidth 64).toNat < tmpj.length := by
        rw [bv_zext32_toNat, hjj1_n]; omega
      have hjj1_d : jj.toNat + 1 < tmpd.length := by
        rw [htl_d]; exact Nat.lt_of_lt_of_le hjj1_lt (Nat.le_trans hua_cv hcv_le)
      have hld_eq : tmpj[((jj + 1#32).setWidth 64).toNat]'hjj1_arr =
          tmpd[jj.toNat + 1]'hjj1_d := by
        have hm1 : jj.toNat + 1 < tmpj.length := by omega
        have hg := htail_j (jj.toNat + 1) (Nat.le_refl _) hjj1_lt
        rw [list_getElem_congr (by rw [bv_zext32_toNat, hjj1_n]) hjj1_arr hm1]
        rw [List.getElem?_eq_getElem hm1, List.getElem?_eq_getElem hjj1_d] at hg
        exact Option.some.inj hg
      have hld_v :
          ∀ (hpf : (BitVec.setWidth 64 (jj + 1)).toNat < tmpj.length),
            tmpj[(BitVec.setWidth 64 (jj + 1)).toNat]'hpf = tmpd[jj.toNat + 1]'hjj1_d :=
        fun hpf => (list_getElem_congr rfl hpf hjj1_arr).trans hld_eq
      have hfs_tmp := focus_ws_tmp hmj; clear hmj
      generalize hR_tmp : FullTmpRest c (wsState s0 repri tmpj) ⋆ R = R_tmp at hfs_tmp
      m6b_steps; simp only [hld_v] at hm; subst hR_tmp
      exact ihsh (jj + 1#32, ()) m (by dsimp only; rw [hjj1_n]; omega)
        ⟨tmpj.set jj.toNat (tmpd[jj.toNat + 1]'hjj1_d), by rw [List.length_set]; exact htl_j,
         by omega, by omega,
         (fun k hk => by
           rw [hjj1_n] at hk
           by_cases hkj : k = jj.toNat
           · subst hkj; rw [List.getElem?_set_self (by omega)]
             have htk_l : (tmpd.take ua.toNat).length = ua.toNat := by
               simp [List.length_take]; omega
             rw [list_getElem?_eraseIdx_ge _ hsi_jj (by rw [htk_l]; omega),
               List.getElem?_take_of_lt hjj1_lt, List.getElem?_eq_getElem hjj1_d]
           · rw [List.getElem?_set_ne (Ne.symm hkj)]; exact hpref_j k (by omega)),
         (fun k hk1 hk2 => by
           rw [hjj1_n] at hk1; rw [List.getElem?_set_ne (by omega)]
           exact htail_j k (by omega) hk2),
         unfocus_ws_tmp hm⟩
    have hjj_eq : jj.toNat = ua.toNat - 1 := by
      have hnot : ¬ (jj + 1#32).toNat < ua.toNat := bv32_ult_not_lt hc
      rw [hjj1_n] at hnot; omega
    obtain ⟨hlt_j, hsem_j⟩ :=
      fid_xor_self_shift_done hsi_lt (by omega) (htl_j.trans htl_d.symm)
        (hjj_eq ▸ hpref_j) hget_si hlt_d hxor_d
    have hua_sub : (ua - 1#32).toNat = ua.toNat - 1 := bv32_sub1_toNat hua_pos
    have hokj := step12BEvStOk_wsState hokd hrli htl_j hrepri
    clear hc ihsh hpref_j htail_j; m6b_to_group
    let P_sc_in : Tup Val [.bool, .bool] → Mem 64 → Prop :=
      fun (nh', _, ()) m_in => nh' = false ∧
        ∃ st_in : FullState, Step12BEvStOk ctx st_in ∧ (FullMem c st_in ⋆ R) m_in
    refine wp_join_group P_sc_in
      (fun _ ⟨nh', ch', ⟨⟩⟩ m_in ⟨hnh', st_in, hok_in, hm_in⟩ => by
        m6b_let; exact hJsc_s (nh', ch', ua - 1#32, ()) m_in
          ⟨(fun h => by rw [hnh'] at h; cases h), fun _ => ⟨st_in, hok_in, hm_in⟩⟩) ?_
    intro Jsc0 hJsc0; m6b_split
    · have hua0 : ua.toNat - 1 = 0 := by
        have h := congrArg BitVec.toNat (beq_iff_eq.mp hc); simpa [hua_sub] using h
      clear hc; m6b_split
      · have hnz : (lhs' &&& 1#32) ≠ 0#32 := bne_iff_ne.mp hc
        have huns_cur : (cnfOfClauses F_cur).Unsat := fid_xor_cancel_unsat (fun α hα => by
          have h := hsem_j α hα; rw [hua0, List.take_zero, List.map_nil, xorEvalList_nil] at h
          exact h) hnz
        m6b_steps
        exact step12BEv_ret2 hexit (step12BEvStOk_with_inconsistent hokj huns_cur)
          (hw0.ext_sound.2 huns_cur) hm
      · m6b_let; exact hJsc0 (false, false, ()) mj ⟨rfl, wsState s0 repri tmpj, hokj, hmj⟩
    clear hc; m6b_to_group
    refine wp_join_group P_sc_in
      (fun _ ⟨nh', ch', ⟨⟩⟩ m_in h => by m6b_let; exact hJsc0 (nh', ch', ()) m_in h) ?_
    intro Jsc1 hJsc1; m6b_split
    · have hua1 : ua.toNat - 1 = 1 := by
        have h := congrArg BitVec.toNat (beq_iff_eq.mp hc); simpa [hua_sub] using h
      have h0_j : 0 < tmpj.length := by
        rw [htl_j]; have := Nat.le_trans hua_cv hcv_le; omega
      have h0_bv_j : (BitVec.ofNat 64 0).toNat < tmpj.length := by simpa using h0_j
      let t0 := tmpj[0]'h0_j
      have ht0_bv : tmpj[(BitVec.ofNat 64 0).toNat]'h0_bv_j = t0 :=
        list_getElem_congr (by decide) _ _
      have ht0_lt : t0.toNat < 2 * cv0 := by
        have h := (hlt_j 0 (by omega)).1; rwa [List.getElem?_eq_getElem h0_j,
          Option.getD_some] at h
      have hul_lt : (t0 ^^^ (1#32 ^^^ (lhs' &&& 1#32))).toNat < 2 * cv0 :=
        xor1_bit01_lt ht0_lt (bv32_xor1_and1_eq01 lhs')
      have hun := fid_xor_cancel_unit (lhs := lhs') (t0 := t0) fun α hα => by
        have h := hsem_j α hα
        have h1 : (tmpj.take (ua.toNat - 1)).map BitVec.toNat = [t0.toNat] := by
          rw [hua1, List.take_one, List.head?_eq_getElem?, List.getElem?_eq_getElem h0_j]; rfl
        rw [h1, xorEvalList_cons, xorEvalList_nil, Bool.bne_false] at h; exact h
      m6b_steps; try rw [ht0_bv]
      m6b_call hUnitFold
      refine step12BEv_unit hokj hul_lt hun hmj fun uf su mu hoku _ hu2 hmu => ?_
      refine s12bEv_afterFold_wp hexit hoku hu2 hmu fun ch' => by
        m6b_let; exact hJsc1 (false, ch', ()) mu ⟨rfl, su, hoku, hmu⟩
    clear hc; m6b_to_group
    refine wp_join_group P_sc_in
      (fun _ ⟨nh', ch', ⟨⟩⟩ m_in h => by m6b_let; exact hJsc1 (nh', ch', ()) m_in h) ?_
    intro Jsc2 hJsc2; m6b_split
    · have hua2 : ua.toNat - 1 = 2 := by
        have h := congrArg BitVec.toNat (beq_iff_eq.mp hc); simpa [hua_sub] using h
      have h0_j : 0 < tmpj.length := by
        rw [htl_j]; have := Nat.le_trans hua_cv hcv_le; omega
      have h1_j : 1 < tmpj.length := by
        rw [htl_j]; have := Nat.le_trans hua_cv hcv_le; omega
      have h0_bv_j : (BitVec.ofNat 64 0).toNat < tmpj.length := by simpa using h0_j
      have h1_bv_j : (BitVec.ofNat 64 1).toNat < tmpj.length := by simpa using h1_j
      let t0 := tmpj[0]'h0_j; let t1 := tmpj[1]'h1_j
      have ht0_bv : tmpj[(BitVec.ofNat 64 0).toNat]'h0_bv_j = t0 :=
        list_getElem_congr (by decide) _ _
      have ht1_bv : tmpj[(BitVec.ofNat 64 1).toNat]'h1_bv_j = t1 :=
        list_getElem_congr (by decide) _ _
      have ht0_lt : t0.toNat < 2 * cv0 := by
        have h := (hlt_j 0 (by omega)).1; rwa [List.getElem?_eq_getElem h0_j,
          Option.getD_some] at h
      have ht1_lt : t1.toNat < 2 * cv0 := by
        have h := (hlt_j 1 (by omega)).1; rwa [List.getElem?_eq_getElem h1_j,
          Option.getD_some] at h
      have ha0_lt : (t0 ^^^ (lhs' &&& 1#32)).toNat < 2 * cv0 :=
        xor1_bit01_lt ht0_lt (bv32_and1_eq01 lhs')
      have heqv := fid_xor_cancel_equiv (lhs := lhs') (t0 := t0) (t1 := t1) fun α hα => by
        have h := hsem_j α hα
        have h2 : (tmpj.take (ua.toNat - 1)).map BitVec.toNat = [t0.toNat, t1.toNat] := by
          rw [hua2]; apply List.ext_getElem
          · simp [List.length_take]; omega
          · intro k _ hk2; rcases k with _ | _ | k'
            · simp [t0]
            · simp [t1]
            · simp at hk2; omega
        rw [h2, xorEvalList_pair] at h; exact h
      m6b_steps; try rw [ht0_bv, ht1_bv]
      m6b_call hEquivFold
      refine step12BEv_equiv hokj ha0_lt ht1_lt heqv hmj fun ef se me hoke _ hef2 hme => ?_
      refine s12bEv_afterEquiv_wp hexit hEnqVar rfl h_ctrl hoke hef2 hme
        fun st_f m_f ch_f hok_f _ hm_f => by
        m6b_let; exact hJsc2 (false, ch_f, ()) m_f ⟨rfl, st_f, hok_f, hm_f⟩
    · m6b_let; exact hJsc2 (false, false, ()) mj ⟨rfl, wsState s0 repri tmpj, hokj, hmj⟩
  · rintro Bf Lf remf ⟨ii, ⟨⟩⟩ ms hBf hLf ⟨rfl, rfl, hii_le⟩
    m6b_split
    rotate_left; · m6b_steps; exact hBf (ii, ua, ()) ms ⟨rfl, Nat.le_refl _, fun h =>
      absurd h (by omega)⟩
    have hii_lt : ii.toNat < ua.toNat := bv32_ult_lt hc
    have hii_arr : (ii.setWidth 64).toNat < tmpd.length := by rw [bv_zext32_toNat]; omega
    have hii1 : (ii + 1#32).toNat = ii.toNat + 1 := bv32_add1_lt_of (by omega)
    clear hc; m6b_steps; m6b_split
    · have hfound : tmpd[ii.toNat]?.getD 0#32 = lhs' &&& ~~~1#32 := by
        have he := beq_iff_eq.mp hc; simp only [wsState_tmp] at he
        rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
        exact (list_getElem_congr (bv_zext32_toNat ii) hii_arr (by omega)).symm.trans he
      m6b_steps; exact hBf (ii, ii, ()) ms ⟨rfl, by omega, fun _ => hfound⟩
    · m6b_steps; exact hLf (ua.toNat - (ii + 1#32).toNat) (ii + 1#32, ()) ms (by omega)
        ⟨rfl, rfl, by omega⟩
  · intro _ Lf _ hLf; m6b_steps; exact hLf ua.toNat (0#32, ()) md ⟨rfl, rfl, Nat.zero_le _⟩

/-! ## 2. Main `Func.wp` Theorem (`full_cong_eval_gate_s12b_wp`) -/

theorem full_cong_eval_gate_s12b_wp (Γ : Env)
    (hFind : ∀ a m Q X, fullCongFindSpec a m Q X →
      Γ "full_cong_find" [i64, i32] [i32] a m Q X)
    (hSort : ∀ a m Q X, fullSortU32Spec a m Q X →
      Γ "full_sort_u32" [i64, i32] [] a m Q X)
    (hUnitFold : ∀ a m Q X, m3CongUnitFoldSpec a m Q X →
      Γ "full_cong_unit_fold" [i64, i32, i32] [i64] a m Q X)
    (hEquivFold : ∀ a m Q X, m3CongEquivFoldSpec a m Q X →
      Γ "full_cong_equiv_fold" [i64, i32, i32, i32] [i64] a m Q X)
    (hAndMatch : ∀ a m Q X, step12BCongAndMatchSpec a m Q X →
      Γ "full_cong_and_match" [i64, i32, i32] [.bool] a m Q X)
    (hXorMatch : ∀ a m Q X, m6CongXorMatchSpec a m Q X →
      Γ "full_cong_xor_match" [i64, i32, i32] [i32] a m Q X)
    (hEnqVar : ∀ a m Q X, step12BCongEnqVarSpec a m Q X →
      Γ "full_cong_enq_var" [i64, i64, i32] [] a m Q X) :
    ∀ a m Q X, step12BCongEvalGateSpec a m Q X →
      Func.wp Γ full_cong_eval_gate_body a m Q X := by
  rintro ⟨h, g, ht_off, ht_sz, next_ep, ctrl_off, ⟨⟩⟩ m0 Q X
    ⟨maxA, c, F0, F_cur, s0, scr0, g_len, R, hmaxA, rfl, hdw0, hrepr0, hht_pos, hht_bnd, hg_lt,
     hg_le_ht, hht_le, hpref0, hgat_g0, hht0, hq0, hm0, hQ⟩
  have hsc := c.hscr; have hmx := c.hmaxv; unfold dimacsBound at hsc hmx
  let cv0 := s0.core.cur_vars; let fuel0 := s0.core.fuel
  let ar0 := s0.core.arena; let alen0 := s0.core.arena_len
  let scr_init := s0.scratch.scratch_buf
  let ctx : Step12BEvCtx :=
    ⟨maxA, hmaxA, c, F0, F_cur, fuel0, ar0, alen0, cv0, g_len, ht_off.toNat, ht_sz.toNat,
     ctrl_off.toNat, scr0, scr_init, R⟩
  have hok0 : Step12BEvStOk ctx s0 :=
    ⟨hdw0, rfl, rfl, rfl, rfl, hrepr0, hht0, hq0,
     step12BScrFrame_refl hdw0.1.scratch_ok.scratch_buf_len⟩
  have hexit : Step12BEvOutCtx ctx s0 Q :=
    ⟨rfl, rfl, rfl, rfl, rfl, hg_le_ht, hht_le, hpref0, hq0, hQ⟩
  have hlen0 := hdw0.1; have hw0 := hdw0.2.1; have hcl0 := hdw0.2.2.2.2.2.1
  have hcv_le := hlen0.core_ok.cur_vars_le
  have hrl0 := hlen0.core_ok.repr_len; have htmpl0 := hlen0.core_ok.tmp_len_arr
  have hscrl0 := hlen0.scratch_ok.scratch_buf_len; have hvlen0 := hlen0.core_ok.vals_len
  clear hdw0 hrepr0 hht0 hlen0
  have hgat_g0' := hgat_g0
  obtain ⟨lhs0, mword, hscr0_g, hscr0_g1, hlhs0_lt, hbd_g, har_cv, har_max, hrhs0, hsem0⟩ :=
    hgat_g0'
  have hg_arr : g.toNat < s0.scratch.scratch_buf.length := by omega
  have hg1_n : (g + 1).toNat = g.toNat + 1 := by
    rw [BitVec.toNat_add, show (1 : BitVec 64).toNat = 1 from rfl, Nat.mod_eq_of_lt (by omega)]
  have hg1_arr : (g + 1).toNat < s0.scratch.scratch_buf.length := by omega
  have hst_g : s0.scratch.scratch_buf[g.toNat]'hg_arr = lhs0 :=
    list_getElem_eq_of_eqD hg_arr ((hpref0 g.toNat hg_lt).trans hscr0_g)
  have hst_g1 : s0.scratch.scratch_buf[(g + 1).toNat]'hg1_arr = mword :=
    list_getElem_eq_of_eqD hg1_arr
      (by rw [hg1_n]; exact (hpref0 (g.toNat + 1) (by omega)).trans hscr0_g1)
  m6b_to_group
  -- Decode `arity = (tag == 3u) ? (meta & CONG_ARITY_MASK) : (meta & 0xFFu)`
  refine wp_join_group (ts := [i32])
    (fun (arity, ()) ma => ma = m0 ∧ arity.toNat = step12BGateArity mword) ?_
    (fun Jar hJar => by
      m6b_steps; m6b_split
      · have ht3 : (mword >>> 28) = 3#32 := by rw [hst_g1] at hc; exact beq_iff_eq.mp hc
        m6b_steps
        exact hJar (_, ()) m0 ⟨rfl, by rw [hst_g1, step12BGateArity_of_eq3 ht3]; rfl⟩
      · have hne3 : (mword >>> 28) ≠ 3#32 := by
          rw [hst_g1] at hc; exact beq_eq_false_iff_ne.mp hc
        m6b_steps
        exact hJar (_, ()) m0 ⟨rfl, by rw [hst_g1, step12BGateArity_of_ne3 hne3]; rfl⟩)
  rintro _ ⟨arity, ⟨⟩⟩ ma ⟨hma, har_def⟩; subst ma
  -- Decode `gtype = (tag == 3u) ? 0u : tag`
  m6b_to_group
  refine wp_join_group (ts := [i32])
    (fun (gtype, ()) mg => mg = m0 ∧
      gtype = if (mword >>> 28) == 3#32 then 0#32 else mword >>> 28) ?_
    (fun Jgt hJgt => by
      m6b_split
      · have hb : ((mword >>> 28) == 3#32) = true := by rw [hst_g1] at hc; exact hc
        m6b_let; exact hJgt (0#32, ()) m0 ⟨rfl, by simp [hb]⟩
      · have hb : ((mword >>> 28) == 3#32) = false := by rw [hst_g1] at hc; exact hc
        m6b_let; rw [hst_g1]; exact hJgt (mword >>> 28, ()) m0 ⟨rfl, by simp [hb]⟩)
  rintro _ ⟨gtype, ⟨⟩⟩ mg ⟨hmg, hgtype_def⟩; subst mg
  m6b_steps
  m6b_split
  · m6b_let; exact step12BEv_exit hexit hok0 hm0 false false
  clear hc; m6b_split
  · m6b_let; exact step12BEv_exit hexit hok0 hm0 false false
  clear hc; m6b_split
  · m6b_let; exact step12BEv_exit hexit hok0 hm0 false false
  clear hc; m6b_steps; m6b_call hFind
  refine ⟨F_cur, 2 * cv0, s0.core.repr, FullReprRest c s0 ⋆ R, step12BEvStOk_repr hok0,
    by rw [hst_g]; exact hlhs0_lt, focus_full_repr hm0,
    fun lhs repr1 m1 hrl1 hrepr1 _ hlhs_lt hlhs_eqv hm1 => ?_⟩
  clear hm0
  have hm1' : (FullMem c (wsState s0 repr1 s0.core.tmp) ⋆ R) m1 := unfocus_full_repr hm1
  clear hm1
  have hlhs_eqv0 : LitEquiv (cnfOfClauses F_cur) lhs0.toNat lhs.toNat := by rwa [hst_g] at hlhs_eqv
  m6b_steps
  refine wp_loop_inv (ts := [i32]) (Step12BEvFindInv ctx s0 g.toNat arity.toNat)
    (fun (i, ()) _ => arity.toNat - i.toNat)
    (fun Ji hJi => by
      m6b_let; exact hJi (0#32, ()) m1 ⟨repr1, s0.core.tmp, hrl1.trans hrl0, htmpl0,
        Nat.zero_le _, hrepr1, fun _ h => absurd h (Nat.not_lt_zero _), hm1'⟩)
    (fun Ji (i, ()) mi ⟨repri, tmpi, hrli, htli, hi_le, hrepri, htmp_i, hmi⟩ ihi => ?_)
  have hoki := step12BEvStOk_wsState hok0 hrli htli hrepri
  dsimp only [ctx] at hrli htli hrepri htmp_i
  m6b_split
  · have hi_lt : i.toNat < arity.toNat := bv32_ult_lt hc
    obtain ⟨ri, hri_get, hri_lt⟩ := hrhs0 i.toNat (by omega)
    have hg2i_n : (g + 2 + i.setWidth 64).toNat = g.toNat + 2 + i.toNat :=
      bv64_add_zext32 (k := 2) (by omega)
    have hg2i_arr : (g + 2 + i.setWidth 64).toNat < s0.scratch.scratch_buf.length := by
      rw [hg2i_n]; omega
    have hst_g2i : s0.scratch.scratch_buf[(g + 2 + i.setWidth 64).toNat]'hg2i_arr = ri :=
      scr_g2i_get hpref0 hri_get (by omega) hg2i_n hg2i_arr
    have hi_tmp : (i.setWidth 64).toNat < tmpi.length := by rw [bv_zext32_toNat]; omega
    have hi1_n : (i + 1#32).toNat = i.toNat + 1 := bv32_add1_lt_of (by omega)
    m6b_steps; m6b_call hFind
    refine ⟨F_cur, 2 * cv0, repri, FullReprRest c (wsState s0 repri tmpi) ⋆ R, hrepri,
      by dsimp only [wsState]; rw [hst_g2i]; exact hri_lt, focus_full_repr hmi,
      fun rval repri' mi' hrl_i' hrepr_i' _ hrval_lt hrval_eqv hmi' => ?_⟩
    have hmi'' : (FullMem c (wsState s0 repri' tmpi) ⋆ R) mi' := ws_unfocus_repr hmi'
    clear hmi'
    have hfs_tmp := focus_full_tmp hmi''; clear hmi''
    generalize hR_tmp : FullTmpRest c (wsState s0 repri' tmpi) ⋆ R = R_tmp at hfs_tmp
    m6b_steps; subst hR_tmp; rw [bv_zext32_toNat] at hm
    exact ihi (i + 1#32, ()) m (by dsimp only; omega)
      ⟨repri', tmpi.set i.toNat rval, hrl_i'.trans hrli, by rw [List.length_set]; exact htli,
       by omega, hrepr_i',
       fun k' hk' => ws_find_tmp_step htmp_i htli (by omega) hri_get hrval_lt
         (by dsimp only [wsState] at hrval_eqv; rwa [hst_g2i] at hrval_eqv) k' (hi1_n ▸ hk'),
       ws_unfocus_tmp hm⟩
  have hi_eq : i.toNat = arity.toNat := by
    have hnot : ¬ i.toNat < arity.toNat := bv32_ult_not_lt hc
    omega
  have htmp_i_len : arity.toNat ≤ tmpi.length := by omega
  have htmp_i' : ∀ (k' : Nat) (hk' : k' < arity.toNat),
      (tmpi[k']'(by omega)).toNat < 2 * cv0 ∧
      LitEquiv (cnfOfClauses F_cur) (scr0[g.toNat + 2 + k']?.getD 0#32).toNat
        (tmpi[k']'(by omega)).toNat := fun k' hk' => by
    have h := htmp_i k' (by omega)
    rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at h
  clear hc; m6b_to_group
  refine wp_join_group (ts := [i32, i32, i32, i32, .bool, .bool])
    (fun (lhs', _iw, htag', harity, need_hash, _changed', ()) mj =>
      Step12BEvOut ctx lhs' htag' harity need_hash mj) ?_ ?_
  · -- Post-dispatch: HT probe + trail enqueue + return
    rintro _ ⟨lhs', _iw, htag', harity, need_hash, changed', ⟨⟩⟩ mj h
    obtain ⟨stj, hokj, hgatej, hlhsj_lt, hmj⟩ := h
    clear hSort; m6b_to_group
    refine wp_join_group (ts := [i32, .bool, .bool])
      (fun (_iwk, _chk, _keepk, ()) mk => ∃ stk : FullState,
        Step12BEvStOk ctx stk ∧ (FullMem c stk ⋆ R) mk) ?_ ?_
    · -- Trail enqueue + exit
      rintro _ ⟨_iwk, chk, keepk, ⟨⟩⟩ mk ⟨stk, hokk, hmk⟩
      clear hUnitFold hEquivFold hAndMatch hXorMatch; m6b_to_group
      refine wp_loop_inv (ts := [i64])
        (fun (_te, ()) m_t => ∃ stt : FullState,
          stt.core.trail_end = stk.core.trail_end ∧ Step12BEvStOk ctx stt ∧ (FullMem c stt ⋆ R) m_t)
        (fun (te, ()) _ => stk.core.trail_end - te.toNat)
        (fun Jt hJt => by m6b_steps; exact hJt (_, ()) mk ⟨stk, rfl, hokk, hmk⟩)
        (fun Jt (te, ()) m_t ⟨stt, hte_eq, hokt, hmt⟩ iht => ?_)
      m6b_split
      · have hcv_t : stt.core.cur_vars = cv0 := step12BEvStOk_cv hokt
        have hcv_le_t : stt.core.cur_vars ≤ c.max_vars :=
          (step12BEvStOk_dw hokt).1.core_ok.cur_vars_le
        have htrll_t : stt.core.trl.length = c.max_vars :=
          (step12BEvStOk_dw hokt).1.core_ok.trl_len
        have hte_end : stt.core.trail_end ≤ cv0 := by
          rw [← hcv_t]; exact ev_trail_end_le_cur_vars (step12BEvStOk_wit hokt)
        have hte_lt : te.toNat < stt.core.trail_end := by
          have hlt := bv64_ult_lt hc
          rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hlt
        have hte_trl : te.toNat < stt.core.trl.length := by rw [htrll_t]; omega
        have htl_lt : (stt.core.trl[te.toNat]'hte_trl).toNat < 2 * cv0 := by
          have h := (step12BEvStOk_wit hokt).trail_lits_lt te.toNat hte_lt
          rw [List.getElem?_eq_getElem hte_trl, Option.getD_some, hcv_t] at h; exact h
        have hte1 : (te + 1#64).toNat = te.toNat + 1 :=
          bv64_add1_toNat (n := stt.core.trail_end) hte_lt (by omega)
        m6b_steps; m6b_call hEnqVar
        refine step12BEv_enq_core hexit hokt rfl hmt fun st1 m1 hok1 hc1 hm1 => ?_
        m6b_steps; m6b_call hFind
        refine ⟨F_cur, 2 * cv0, st1.core.repr, FullReprRest c st1 ⋆ R, step12BEvStOk_repr hok1,
          htl_lt, focus_full_repr hm1, fun rtl repr_t m2 hrl_t hrepr_t _ _ _ hm2 => ?_⟩
        let st2 : FullState := { st1 with core := { st1.core with repr := repr_t } }
        have hm2' : (FullMem c st2 ⋆ R) m2 := unfocus_full_repr hm2
        have hok2 := step12BEvStOk_with_repr hok1
          (hrl_t.trans (step12BEvStOk_dw hok1).1.core_ok.repr_len) hrepr_t
        m6b_steps; m6b_call hEnqVar
        refine step12BEv_enq_core hexit hok2 rfl hm2' fun st3 m3 hok3 hc3 hm3 => ?_
        m6b_let; exact iht (te + 1#64, ()) m3 (by dsimp only; omega)
          ⟨st3, by
            rw [hc3, show st2.core.trail_end = st1.core.trail_end from rfl, hc1]
            exact hte_eq,
           hok3, hm3⟩
      clear hc; m6b_split
      · have hne0 : stt.core.inconsistent ≠ 0#64 := bne_iff_ne.mp hc
        m6b_steps
        exact step12BEv_ret2 hexit hokt (unsat_of_inconsistent_w (step12BEvStOk_wit hokt) hne0) hmt
      clear hc; m6b_to_group
      refine wp_join_group (ts := [i64])
        (fun (v1, ()) mv => v1 = (if chk then 1#64 else 0#64) ∧ mv = m_t)
        (fun _ ⟨v1, ⟨⟩⟩ mv ⟨hv1, hmv⟩ => by
          m6b_to_group
          refine wp_join_group (ts := [i64])
            (fun (v2, ()) mw => v2 = (if keepk then 4#64 else 0#64) ∧ mw = mv)
            (fun _ ⟨v2, ⟨⟩⟩ mw ⟨hv2, hmw⟩ => by
              m6b_steps; rw [hmw, hmv]
              have hg := step12BEv_exit hexit hokt hmt chk keepk
              dsimp only at hv1 hv2 hg; rw [hv1, hv2]; exact hg)
            (fun Jk hJk => by
              m6b_split
              · have hk' : keepk = true := hc
                m6b_let; exact hJk (4#64, ()) mv ⟨by simp only [hk', ite_true], rfl⟩
              · have hk' : keepk = false := hc
                m6b_let; exact hJk (0#64, ()) mv ⟨by simp only [hk', Bool.false_eq_true,
                  ite_false], rfl⟩))
        (fun Jc hJc => by
          m6b_split
          · have hc' : chk = true := hc
            m6b_let; exact hJc (1#64, ()) m_t ⟨by simp only [hc', ite_true], rfl⟩
          · have hc' : chk = false := hc
            m6b_let; exact hJc (0#64, ()) m_t ⟨by simp only [hc', Bool.false_eq_true, ite_false],
              rfl⟩)
    · -- HT probe block (`if (need_hash && h->inconsistent == 0ULL)`)
      intro Jex hJex; m6b_split
      rotate_left; · m6b_let; exact hJex (_iw, changed', false, ()) mj ⟨stj, hokj, hmj⟩
      have hnh : need_hash = true := hc; clear hc; m6b_split
      rotate_left; · m6b_let; exact hJex (_iw, changed', false, ()) mj ⟨stj, hokj, hmj⟩
      obtain ⟨hhar_cv, hgat0, hgat1, hgat2⟩ := hgatej hnh
      have hlhs'_lt := hlhsj_lt hnh
      have hhar_tmp : harity.toNat ≤ stj.core.tmp.length := by
        rw [(step12BEvStOk_dw hokj).1.core_ok.tmp_len_arr]; exact Nat.le_trans hhar_cv hcv_le
      clear hc hUnitFold; m6b_to_group
      refine wp_loop_inv (ts := [i32, i64])
        (fun (ih_v, _hv, ()) mhv => mhv = mj ∧ ih_v.toNat ≤ harity.toNat)
        (fun (ih_v, _, ()) _ => harity.toNat - ih_v.toNat)
        (fun Jhv hJhv => by m6b_steps; exact hJhv (0#32, _, ()) mj ⟨rfl, Nat.zero_le _⟩)
        (fun Jhv (ih_v, _hv, ()) mhv ⟨hmhv, hih_le⟩ ih_hv => ?_)
      subst mhv; m6b_split
      · have hih_lt : ih_v.toNat < harity.toNat := bv32_ult_lt hc
        have hih_arr : (ih_v.setWidth 64).toNat < stj.core.tmp.length := by
          rw [bv_zext32_toNat]; omega
        have hih1 : (ih_v + 1#32).toNat = ih_v.toNat + 1 := bv32_add1_lt_of (by omega)
        m6b_steps; exact ih_hv (ih_v + 1#32, _, ()) mj (by dsimp only; omega) ⟨rfl, by omega⟩
      clear hc; m6b_to_group
      refine wp_loop_break_group (brkTs := [.bool, .bool, i64, i64, .bool])
        (lpTs := [i64, i64, .bool])
        (fun (ch_p, keep_p, _, _, _, ()) mp => ∃ stp : FullState,
          Step12BEvStOk ctx stp ∧ (FullMem c stp ⋆ R) mp)
        (Step12BEvProbeInv ctx stj ht_sz.toNat) ?_ ?_ ?_
      · rintro _ ⟨ch_p, keep_p, _, _, _, ⟨⟩⟩ mp ⟨stp, hokp, hmp⟩
        m6b_let; exact hJex (ih_v, ch_p, keep_p, ()) mp ⟨stp, hokp, hmp⟩
      · rintro Bp Lp remp ⟨slot, probes, seen_self, ⟨⟩⟩ mp hBp hLp
          ⟨stp, hslot_lt, hpr_le, rfl, htmp_p, hokp, hmp⟩
        have hscrl_p := (step12BEvStOk_dw hokp).1.scratch_ok.scratch_buf_len
        have hrl_p := (step12BEvStOk_dw hokp).1.core_ok.repr_len
        have hlml_p := (step12BEvStOk_dw hokp).1.core_ok.lit_mark_len
        have hrepr_p := step12BEvStOk_repr hokp
        have hht_p := step12BEvStOk_ht hokp
        dsimp only [ctx] at hscrl_p hrl_p hlml_p hrepr_p hht_p
        have hpref_p := step12BScrFrame_pref hg_le_ht hht_le hpref0 hq0 (step12BEvStOk_fr hokp)
        m6b_split
        rotate_left
        · m6b_steps; exact hBp (changed', true, slot, probes, seen_self, ()) mp ⟨stp, hokp, hmp⟩
        have hpr_lt : probes.toNat < 128 := bv64_ult_lt hc
        have hhts_n : (ht_off + slot).toNat = ht_off.toNat + slot.toNat := by
          show (ht_off.toNat + slot.toNat) % 2 ^ 64 = ht_off.toNat + slot.toNat
          exact Nat.mod_eq_of_lt (by omega)
        have hhts_arr : (ht_off + slot).toNat < stp.scratch.scratch_buf.length := by omega
        let ent := stp.scratch.scratch_buf[(ht_off + slot).toNat]'hhts_arr
        have hent_slot : stp.scratch.scratch_buf[ht_off.toNat + slot.toNat]?.getD 0xFFFFFFFF#32 =
            ent := by rw [← hhts_n, List.getElem?_eq_getElem hhts_arr, Option.getD_some]
        clear hc; m6b_split
        · -- `ent == 0xFFFFFFFFu`: insert if `!seen_self && htag == gtype && res_sz < ht_lim`
          m6b_to_group; refine wp_join_group (ts := [])
            (fun () mins => ∃ stins : FullState,
              Step12BEvStOk ctx stins ∧ (FullMem c stins ⋆ R) mins)
            (fun _ ⟨⟩ mins ⟨stins, hokins, hmins⟩ => by
              m6b_let; exact hBp (changed', true, slot, probes, seen_self, ()) mins
                ⟨stins, hokins, hmins⟩) ?_
          intro Jins hJins; m6b_split
          · m6b_let; exact hJins () mp ⟨stp, hokp, hmp⟩
          m6b_split
          rotate_left; · m6b_let; exact hJins () mp ⟨stp, hokp, hmp⟩
          m6b_split
          rotate_left; · m6b_let; exact hJins () mp ⟨stp, hokp, hmp⟩
          have hi32 : i32.bytes = 4 := rfl; m6b_steps
          have hm_ins : (FullMem c { stp with scratch := { stp.scratch with
              scratch_buf := stp.scratch.scratch_buf.set (ht_off.toNat + slot.toNat) (g.setWidth 32)
              res_sz := stp.scratch.res_sz + 1#64 } } ⋆ R) m := by rw [hhts_n] at hm; exact hm
          exact hJins () m ⟨_, step12BEvStOk_ht_insert hokp rfl rfl hg_lt hg_le_ht hht_le hslot_lt
            hgat_g0, hm_ins⟩
        have hent_ne : ent ≠ 0xFFFFFFFF#32 := beq_eq_false_iff_ne.mp hc
        have hslot_next_lt : ((slot + 1#64) &&& (ht_sz - 1#64)).toNat < ht_sz.toNat :=
          bv64_and_sub1_lt hht_pos
        have hpr1 : (probes + 1#64).toNat = probes.toNat + 1 :=
          bv64_add1_toNat (n := 128) hpr_lt (by decide)
        clear hc; m6b_split
        · m6b_steps
          exact hLp (128 - (probes + 1#64).toNat)
            ((slot + 1#64) &&& (ht_sz - 1#64), probes + 1#64, true, ()) mp (by omega)
            ⟨stp, hslot_next_lt, by omega, rfl, htmp_p, hokp, hmp⟩
        have hent_gate : Step12BGateAt maxA F_cur cv0 scr0 g_len ent.toNat := by
          rcases hht_p slot.toNat hslot_lt with he | hg_e
          · rw [hent_slot] at he; exact absurd he hent_ne
          · rwa [hent_slot] at hg_e
        have ⟨elhs, emword, he0, he1, helhs_lt, hbd_e, _, _, herhs, hsem_e⟩ := hent_gate
        have he0_arr : ent.toNat < stp.scratch.scratch_buf.length := by omega
        have he1_n : (ent.setWidth 64 + 1).toNat = ent.toNat + 1 := by
          rw [BitVec.toNat_add, bv_zext32_toNat]
          show (ent.toNat + 1) % 2 ^ 64 = ent.toNat + 1; omega
        have he1_arr : (ent.setWidth 64 + 1).toNat < stp.scratch.scratch_buf.length := by omega
        have hst_e0 : stp.scratch.scratch_buf[(ent.setWidth 64).toNat]'
            (by rw [bv_zext32_toNat]; exact he0_arr) = elhs := by
          have h := (hpref_p ent.toNat (by omega)).trans he0
          rw [list_getElem_congr (bv_zext32_toNat ent) _ he0_arr]
          rw [List.getElem?_eq_getElem he0_arr] at h; exact Option.some.inj h
        have hst_e0' : stp.scratch.scratch_buf[(BitVec.setWidth 64
            stp.scratch.scratch_buf[(ht_off + slot).toNat]).toNat]'he0_arr = elhs := hst_e0
        have hst_e1 : stp.scratch.scratch_buf[(ent.setWidth 64 + 1).toNat]'he1_arr = emword := by
          have h := (hpref_p (ent.toNat + 1) (by omega)).trans he1
          rw [← he1_n, List.getElem?_eq_getElem he1_arr] at h; exact Option.some.inj h
        clear hc
        -- Decode `egtype = (etag == 3u) ? 0u : etag`
        m6b_to_group
        refine wp_join_group (ts := [i32])
          (fun (egtype, ()) meg => meg = mp ∧
            egtype = if (emword >>> 28) == 3#32 then 0#32 else emword >>> 28) ?_
          (fun Jeg hJeg => by
            m6b_split
            · have hb : ((emword >>> 28) == 3#32) = true := by rw [hst_e1] at hc; exact hc
              m6b_let; exact hJeg (0#32, ()) mp ⟨rfl, by simp [hb]⟩
            · have hb : ((emword >>> 28) == 3#32) = false := by rw [hst_e1] at hc; exact hc
              m6b_let; rw [hst_e1]; exact hJeg (emword >>> 28, ()) mp ⟨rfl, by simp [hb]⟩)
        rintro _ ⟨egtype, ⟨⟩⟩ meg ⟨hmeg, hegtype_def⟩; subst meg
        m6b_to_group
        refine wp_join_group (ts := [.bool, .bool])
          (fun _ mnxt => ∃ stn : FullState, stn.core.tmp = stj.core.tmp ∧
            Step12BEvStOk ctx stn ∧ (FullMem c stn ⋆ R) mnxt)
          (fun _ ⟨_, _, ⟨⟩⟩ mnxt ⟨stn, htmp_n, hokn, hmn⟩ => by
            m6b_let; exact hLp (128 - (probes + 1#64).toNat)
              ((slot + 1#64) &&& (ht_sz - 1#64), probes + 1#64, seen_self, ()) mnxt (by omega)
              ⟨stn, hslot_next_lt, by omega, rfl, htmp_n, hokn, hmn⟩) ?_
        intro Jnxt hJnxt
        m6b_split
        rotate_left; · m6b_let; exact hJnxt (_, _, ()) mp ⟨stp, htmp_p, hokp, hmp⟩
        have hegtype_eq : egtype = htag' := beq_iff_eq.mp hc
        clear hc; m6b_to_group
        refine wp_join_group (Step12BEvMatchInv ctx stp lhs') ?_ ?_
        · -- Post-match: `if (matched)`
          rintro _ ⟨matched, mlhs, ⟨⟩⟩ mmatch
            ⟨repr_m, mclr_m, lm_m, hrl_m, hml_m, hlml_m, hmk_m, hrepr_m, heqv_m, hmm⟩
          let stm : FullState :=
            { stp with core :=
              { stp.core with repr := repr_m, min_clr := mclr_m, lit_mark := lm_m } }
          have hokm := step12BEvStOk_with_repr_mclr_lm hokp hrl_m hml_m hlml_m hmk_m hrepr_m
          m6b_split
          rotate_left; · m6b_steps; exact hJnxt (_, _, ()) mmatch ⟨stm, htmp_p, hokm, hmm⟩
          obtain ⟨hml_lt, hlhs_ent⟩ := heqv_m hc
          m6b_steps; m6b_call hEquivFold
          refine step12BEv_equiv hokm hlhs'_lt hml_lt hlhs_ent hmm
            fun ef se me hoke _ hef2 hme => ?_
          m6b_split
          · m6b_let; exact step12BEv_ret2 hexit hoke (hef2 (beq_iff_eq.mp hc)) hme
          m6b_to_group; refine wp_join_group (ts := [.bool])
            (fun (ch_ef, ()) mef => ∃ stef : FullState,
              Step12BEvStOk ctx stef ∧ (FullMem c stef ⋆ R) mef)
            (fun _ ⟨ch_ef, ⟨⟩⟩ mef ⟨stef, hokef, hmef⟩ => by
              m6b_let; exact hBp (ch_ef, false, slot, probes, seen_self, ()) mef ⟨stef, hokef,
                hmef⟩) ?_
          intro Jef hJef; m6b_split
          rotate_left; · m6b_let; exact hJef (changed', ()) me ⟨se, hoke, hme⟩
          m6b_steps; m6b_call hEnqVar
          refine step12BEv_enq hexit hoke rfl hme fun s1 m1 hk1 _ hm1 => ?_
          m6b_steps; m6b_call hEnqVar
          refine step12BEv_enq hexit hk1 rfl hm1 fun s2 m2 hk2 _ hm2 => ?_
          m6b_steps; m6b_call hFind
          refine ⟨F_cur, 2 * cv0, s2.core.repr, FullReprRest c s2 ⋆ R, step12BEvStOk_repr hk2,
            hlhs'_lt, focus_full_repr hm2, fun fl r3 m3 hrl3 hrepr3 _ _ _ hm3 => ?_⟩
          let s3 : FullState := { s2 with core := { s2.core with repr := r3 } }
          have hm3' : (FullMem c s3 ⋆ R) m3 := unfocus_full_repr hm3
          have hk3 :=
            step12BEvStOk_with_repr hk2
              (hrl3.trans (step12BEvStOk_dw hk2).1.core_ok.repr_len) hrepr3
          m6b_steps; m6b_call hEnqVar
          refine step12BEv_enq hexit hk3 rfl hm3' fun s4 m4 hk4 _ hm4 => ?_
          m6b_steps; m6b_call hFind
          refine ⟨F_cur, 2 * cv0, s4.core.repr, FullReprRest c s4 ⋆ R, step12BEvStOk_repr hk4,
            hml_lt, focus_full_repr hm4, fun fm r5 m5 hrl5 hrepr5 _ _ _ hm5 => ?_⟩
          let s5 : FullState := { s4 with core := { s4.core with repr := r5 } }
          have hm5' : (FullMem c s5 ⋆ R) m5 := unfocus_full_repr hm5
          have hk5 :=
            step12BEvStOk_with_repr hk4
              (hrl5.trans (step12BEvStOk_dw hk4).1.core_ok.repr_len) hrepr5
          m6b_steps; m6b_call hEnqVar
          refine step12BEv_enq hexit hk5 rfl hm5' fun s6 m6 hk6 _ hm6 => ?_
          m6b_let; exact hJef (true, ()) m6 ⟨s6, hk6, hm6⟩
        · -- Match dispatch: `htag == 0`, `htag == 1`, `htag == 2`
          intro Jm hJm; m6b_split
          · have htag0_eq : htag' = 0#32 := beq_iff_eq.mp hc
            have hetag03 := step12B_gtype_eq0 hegtype_def (hegtype_eq.trans htag0_eq)
            obtain ⟨_, _, hand_eq⟩ := hgat0 htag0_eq
            m6b_steps; m6b_call hAndMatch
            refine ⟨maxA, c, F0, F_cur, stp, scr0, g_len, R, hmaxA, rfl,
              (step12BEvStOk_dw hokp).1, step12BEvStOk_wit hokp, step12BEvStOk_mk hokp,
              step12BEvStOk_cl hokp, step12BEvStOk_cv hokp ▸ hrepr_p, by omega, hpref_p,
              by rw [step12BEvStOk_cv hokp]; exact hent_gate,
              by rw [he1, Option.getD_some]; exact hetag03,
              by rw [step12BEvStOk_cv hokp]; exact hhar_cv, hmp, ?_⟩
            intro ok_m repr_m lm_m mm _ hrl_m hlml_m hmk_m hrepr_m hok_and hmm
            m6b_steps; rw [hst_e0']
            exact hJm (ok_m, elhs, ()) mm
              ⟨repr_m, stp.core.min_clr, lm_m, hrl_m,
               (step12BEvStOk_dw hokp).1.core_ok.min_clr_len_arr, hlml_m, hmk_m,
               by rw [← step12BEvStOk_cv hokp]; exact hrepr_m,
               fun hokt => ⟨helhs_lt, ws_match_and_equiv (htmp_p ▸ hand_eq) he0 (hok_and hokt).2.2⟩,
               hmm⟩
          clear hc; m6b_to_group
          refine wp_join_group (Step12BEvMatchInv ctx stp lhs')
            (fun _ ⟨m_ok, mlhs, ⟨⟩⟩ mf h => by m6b_let; exact hJm (m_ok, mlhs, ()) mf h) ?_
          intro Jmb hJmb; m6b_split
          · have htag1_eq : htag' = 1#32 := beq_iff_eq.mp hc
            have hetag1 := step12B_gtype_eq1 hegtype_def (hegtype_eq.trans htag1_eq)
            have hhar_24 : 2 ≤ harity.toNat ∧ harity.toNat ≤ 4 :=
              ⟨(hgat1 htag1_eq).1, (hgat1 htag1_eq).2.1⟩
            have hent_m6 : M6GateAt F_cur cv0 scr0 g_len ent.toNat :=
              step12BGateAt_to_m6_of_xor hent_gate (by rw [he1, Option.getD_some]; exact hetag1)
            m6b_steps; m6b_call hXorMatch
            refine ⟨c, F0, F_cur, stp, scr0, g_len, R, rfl, (step12BEvStOk_dw hokp).1,
              step12BEvStOk_wit hokp, step12BEvStOk_cl hokp, step12BEvStOk_cv hokp ▸ hrepr_p,
              by rw [step12BEvStOk_cv hokp]; omega, by omega, hpref_p,
              by rw [step12BEvStOk_cv hokp]; exact hent_m6,
              by rw [he1, Option.getD_some]; exact hetag1,
              by rw [step12BEvStOk_cv hokp]; exact hhar_cv,
              by intro k hk; rw [htmp_p, step12BEvStOk_cv hokp]; exact (hgat1 htag1_eq).2.2.1 k hk,
              hmp, ?_⟩
            intro ml repr_m mclr_m mm _ hrl_m hml_m hrepr_m hok_xor hmm
            have hmm' : (FullMem c { stp with core :=
                { stp.core with repr := repr_m, min_clr := mclr_m } } ⋆ R) mm := hmm
            clear hmm; m6b_to_group
            refine wp_unroll_group (fun Js_m hJs_m => ?_); dsimp only; m6b_split
            · have hml_ne : ml ≠ 0xFFFFFFFF#32 := bne_iff_ne.mp hc
              obtain ⟨_, _, hml_lt, hml_ev⟩ := hok_xor hml_ne
              m6b_steps; apply hJs_m; m6b_steps
              exact hJmb (true, ml, ()) mm
                ⟨repr_m, mclr_m, stp.core.lit_mark, hrl_m, hml_m, hlml_p,
                 step12BEvStOk_mk (st := stp) hokp, step12BEvStOk_cv hokp ▸ hrepr_m,
                 fun _ => ⟨step12BEvStOk_cv hokp ▸ hml_lt,
                   step12B_tag1_match_equiv (htag1_eq ▸ htmp_p ▸ hgatej hnh) hml_ev⟩, hmm'⟩
            · m6b_steps; apply hJs_m; m6b_steps; rw [hst_e0']
              exact hJmb (false, elhs, ()) mm
                ⟨repr_m, mclr_m, stp.core.lit_mark, hrl_m, hml_m, hlml_p,
                 step12BEvStOk_mk (st := stp) hokp, step12BEvStOk_cv hokp ▸ hrepr_m,
                 (fun h => by cases h), hmm'⟩
          clear hc; m6b_to_group
          refine wp_join_group (Step12BEvMatchInv ctx stp lhs')
            (fun _ ⟨m_ok, mlhs, ⟨⟩⟩ mf' h => by m6b_let; exact hJmb (m_ok, mlhs, ()) mf' h) ?_
          intro Jm2 hJm2; m6b_split
          rotate_left
          · m6b_let; rw [hst_e0']
            exact hJm2 (false, elhs, ()) mp ⟨stp.core.repr, stp.core.min_clr, stp.core.lit_mark,
              hrl_p, (step12BEvStOk_dw hokp).1.core_ok.min_clr_len_arr, hlml_p,
              step12BEvStOk_mk hokp, hrepr_p, (fun h => by cases h), hmp⟩
          have he_tag2 : htag' = 2#32 := beq_iff_eq.mp hc
          have hetag2 := step12B_gtype_eq2 hegtype_def (hegtype_eq.trans he_tag2)
          clear hc; m6b_split
          rotate_left
          · m6b_let; rw [hst_e0']
            exact hJm2 (false, elhs, ()) mp ⟨stp.core.repr, stp.core.min_clr, stp.core.lit_mark,
              hrl_p, (step12BEvStOk_dw hokp).1.core_ok.min_clr_len_arr, hlml_p,
              step12BEvStOk_mk hokp, hrepr_p, (fun h => by cases h), hmp⟩
          obtain ⟨har_ite, hite_s⟩ := hgat2 he_tag2
          have h3 : harity.toNat = 3 := by rw [har_ite]; decide
          have hite_e := step12B_gate_tag2_ite hetag2 hsem_e
          have ha_e : step12BGateArity emword = 3 := hite_e.1
          obtain ⟨er0, her0_get, her0_lt⟩ := herhs 0 (by omega)
          obtain ⟨er1, her1_get, her1_lt⟩ := herhs 1 (by omega)
          obtain ⟨er2, her2_get, her2_lt⟩ := herhs 2 (by omega)
          have he2_arr := scr_e_lt (scr := stp.scratch.scratch_buf) (g_len := g_len) (ent := ent)
            2 (by omega) (by omega) (by omega)
          have he3_arr := scr_e_lt (scr := stp.scratch.scratch_buf) (g_len := g_len) (ent := ent)
            3 (by omega) (by omega) (by omega)
          have he4_arr := scr_e_lt (scr := stp.scratch.scratch_buf) (g_len := g_len) (ent := ent)
            4 (by omega) (by omega) (by omega)
          have hst_e2 := scr_e_get (g_len := g_len) 2 (by omega) hpref_p her0_get he2_arr (by omega)
          have hst_e3 := scr_e_get (g_len := g_len) 3 (by omega) hpref_p her1_get he3_arr (by omega)
          have hst_e4 := scr_e_get (g_len := g_len) 4 (by omega) hpref_p her2_get he4_arr (by omega)
          m6b_steps; m6b_call hFind
          refine ⟨F_cur, 2 * cv0, stp.core.repr, FullReprRest c stp ⋆ R, hrepr_p, hst_e2 ▸ her0_lt,
            focus_full_repr hmp, fun ec repra ma hrla hrepra _ _ hec_eqv hma => ?_⟩
          have hma' := unfocus_full_repr hma; clear hma
          m6b_steps; m6b_call hFind
          refine ⟨F_cur, 2 * cv0, repra,
            FullReprRest c { stp with core := { stp.core with repr := repra } } ⋆ R,
            hrepra, hst_e3 ▸ her1_lt, focus_full_repr hma',
            fun et reprb mb hrlb hreprb _ _ het_eqv hmb => ?_⟩
          have hmb' := unfocus_full_repr hmb; clear hmb
          m6b_steps; m6b_call hFind
          refine ⟨F_cur, 2 * cv0, reprb,
            FullReprRest c { stp with core := { stp.core with repr := reprb } } ⋆ R,
            hreprb, hst_e4 ▸ her2_lt, focus_full_repr hmb',
            fun ee reprc mc hrlc hreprc _ _ hee_eqv hmc => ?_⟩
          let stpc : FullState := { stp with core := { stp.core with repr := reprc } }
          have hmc' : (FullMem c stpc ⋆ R) mc := by simpa only [stpc] using unfocus_full_repr hmc
          clear hmc
          have hite_e' : IteGateDef (cnfOfClauses F_cur) elhs.toNat ec.toNat et.toNat ee.toNat :=
            ite_eval_congr hite_e.2 (LitEquiv.refl _ _)
              (by rw [her0_get, Option.getD_some, ← hst_e2]; exact hec_eqv)
              (by rw [her1_get, Option.getD_some, ← hst_e3]; exact het_eqv)
              (by rw [her2_get, Option.getD_some, ← hst_e4]; exact hee_eqv)
          have hstj_tl : stj.core.tmp.length = c.max_vars :=
            (step12BEvStOk_dw hokj).1.core_ok.tmp_len_arr
          have hstp_tl : stp.core.tmp.length = c.max_vars :=
            (step12BEvStOk_dw hokp).1.core_ok.tmp_len_arr
          have htmp_ge3 : 3 ≤ stpc.core.tmp.length := by change 3 ≤ stp.core.tmp.length; omega
          have ht0_eq := tmp_st_get (k := 0) htmp_p (by omega)
          have ht1_eq := tmp_st_get (k := 1) htmp_p (by omega)
          have ht2_eq := tmp_st_get (k := 2) htmp_p (by omega)
          m6b_to_group
          refine wp_join_group (ts := [i32, i32, i32])
            (fun (ec1, et1, ee1, ()) mfin => mfin = mc ∧
              IteGateDef (cnfOfClauses F_cur) elhs.toNat ec1.toNat et1.toNat ee1.toNat) ?_ ?_
          · rintro _ ⟨ec1, et1, ee1, ⟨⟩⟩ mfin ⟨hmfin, hite_1⟩; subst mfin; m6b_to_group
            refine wp_join_group (ts := [i32, i32, i32])
              (fun (ml', et', ee', ()) mfin2 => mfin2 = mc ∧ ml'.toNat < 2 * cv0 ∧
                IteGateDef (cnfOfClauses F_cur) ml'.toNat ec1.toNat et'.toNat ee'.toNat) ?_ ?_
            · rintro _ ⟨ml', et', ee', ⟨⟩⟩ mfin2 ⟨hmfin2, hml'_lt, hite_f⟩
              subst mfin2; m6b_to_group
              refine wp_join_group (ts := [.bool])
                (fun (b, ()) mj => mj = mc ∧
                  (b = true → ml'.toNat < 2 * cv0 ∧ LitEquiv (cnfOfClauses F_cur) lhs'.toNat
                    ml'.toNat))
                (fun _ ⟨b, ⟨⟩⟩ mj ⟨hmj, hm⟩ => by
                  subst mj; m6b_let; exact hJm2 (b, ml', ()) mc
                    ⟨reprc, stp.core.min_clr, stp.core.lit_mark,
                     hrlc.trans (hrlb.trans (hrla.trans hrl_p)),
                     (step12BEvStOk_dw hokp).1.core_ok.min_clr_len_arr, hlml_p,
                     step12BEvStOk_mk (st := stp) hokp, hreprc, hm, hmc'⟩) ?_
              intro Jmi hJmi
              have ht0_a : 0 < stpc.core.tmp.length := by omega
              have ht1_a : 1 < stpc.core.tmp.length := by omega
              have ht2_a : 2 < stpc.core.tmp.length := by omega
              m6b_steps; m6b_split
              rotate_left; · m6b_let; exact hJmi (false, ()) mc ⟨rfl, fun h => by cases h⟩
              have hc0 : ec1 = stj.core.tmp[0]'(by omega) := by
                have h : ec1 = stpc.core.tmp[0] := beq_iff_eq.mp hc
                rw [h, ht0_eq, List.getElem?_eq_getElem (by omega), Option.getD_some]
              clear hc; m6b_steps; m6b_split
              rotate_left; · m6b_let; exact hJmi (false, ()) mc ⟨rfl, fun h => by cases h⟩
              have hc1 : et' = stj.core.tmp[1]'(by omega) := by
                have h : et' = stpc.core.tmp[1] := beq_iff_eq.mp hc
                rw [h, ht1_eq, List.getElem?_eq_getElem (by omega), Option.getD_some]
              clear hc; m6b_steps; m6b_split
              rotate_left; · m6b_let; exact hJmi (false, ()) mc ⟨rfl, fun h => by cases h⟩
              have hc2 : ee' = stj.core.tmp[2]'(by omega) := by
                have h : ee' = stpc.core.tmp[2] := beq_iff_eq.mp hc
                rw [h, ht2_eq, List.getElem?_eq_getElem (by omega), Option.getD_some]
              m6b_steps; exact hJmi (true, ()) mc ⟨rfl, fun _ =>
                ⟨hml'_lt, ws_hash_ite_equiv (by omega) hite_s hite_f hc0 hc1 hc2⟩⟩
            · intro Jf hJf; m6b_split
              · m6b_steps; rw [hst_e0']
                refine hJf (elhs ^^^ 1#32, et1 ^^^ 1#32, ee1 ^^^ 1#32, ()) mc
                  ⟨rfl, bv32_xor1_lt_cv helhs_lt, ?_⟩
                rw [FullCongHelpers.bv32_xor1_eq_litNeg, FullCongHelpers.bv32_xor1_eq_litNeg,
                  FullCongHelpers.bv32_xor1_eq_litNeg]
                exact iteGateDef_flip_out hite_1
              · m6b_let; rw [hst_e0']; exact hJf (elhs, et1, ee1, ()) mc ⟨rfl, helhs_lt, hite_1⟩
          · intro Jc1 hJc1; m6b_split
            · m6b_steps; refine hJc1 (ec ^^^ 1#32, ee, et, ()) mc ⟨rfl, ?_⟩
              rw [FullCongHelpers.bv32_xor1_eq_litNeg]; exact iteGateDef_flip_cond hite_e'
            · m6b_let; exact hJc1 (ec, et, ee, ()) mc ⟨rfl, hite_e'⟩
      · intro _ Lp _ hLp; m6b_steps
        exact hLp 128 (_ &&& (ht_sz - 1#64), 0#64, false, ()) mj
          ⟨stj, bv64_and_sub1_lt hht_pos, by decide, rfl, rfl, hokj, hmj⟩
  · -- Gate-type dispatch: `gtype == 0u`, `gtype == 1u`, `gtype == 2u`, `else`
    intro Js hJs; clear hAndMatch hXorMatch hFind
    m6b_split
    · -- `gtype == 0u` (wide AND, `arity ≤ 1,000,000`)
      have hgtype0 : gtype = 0#32 := beq_iff_eq.mp hc
      have htag03 := step12B_gtype_eq0 hgtype_def hgtype0
      have ⟨har2_0, hand0⟩ := step12B_gate_tag0_and htag03 hsem0
      rw [← har_def] at har2_0 hand0
      let rhs : List Nat := ((scr0.drop (g.toNat + 2)).take arity.toNat).map BitVec.toNat
      have hscr_ge : g.toNat + 2 + arity.toNat ≤ scr0.length := by
        obtain ⟨_, hr, _⟩ := hrhs0 (arity.toNat - 1) (by omega)
        have := (List.getElem?_eq_some_iff.mp hr).1; omega
      obtain ⟨hraw_of_rhs, hrhs_of_raw⟩ :=
        ws_tag0_raw_of_rhs (F_cur := F_cur) htmp_i_len hscr_ge fun k hk => by
          have h := (htmp_i k (hi_eq ▸ hk)).2
          simpa only [List.getElem?_take_of_lt hk] using h
      let raw := tmpi.take arity.toNat
      have hraw_len : raw.length = arity.toNat := by simp only [raw, List.length_take]; omega
      have hraw_lt : ∀ k < arity.toNat, (raw[k]?.getD 0#32).toNat < 2 * cv0 := fun k hk => by
        have hget : raw[k]?.getD 0#32 = tmpi[k]'(by omega) := by
          simp only [raw, List.getElem?_take, ite_eq_left hk]
          rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
        rw [hget]; exact (htmp_i' k hk).1
      clear hc ihi htmp_i hsem0 hgat_g0 hrhs0 hscr0_g hscr0_g1 hst_g hi_le hrl1 hrepr1 hm1'
      m6b_to_group
      refine wp_loop_break_group (brkTs := [i32, .bool, i32]) (lpTs := [i32, i32])
        (fun (il, has_false, na, ()) ml =>
          Step12BEvTag0P1Brk ctx s0 repri raw arity.toNat il has_false na ml)
        (fun rem (il, na, ()) ml =>
          rem = arity.toNat - il.toNat ∧
          Step12BEvTag0P1Inv ctx s0 repri raw arity.toNat il na ml) ?_ ?_ ?_
      · rintro _ ⟨il, has_false, na, ⟨⟩⟩ ml ⟨tmpl, htl_l, hna_le, hhf_l, hnohf_l, hml⟩
        have hokl := step12BEvStOk_wsState hok0 hrli htl_l hrepri
        dsimp only [ctx] at htl_l hna_le hhf_l hnohf_l
        let P_tag0 : Tup Val [i32, .bool, .bool] → Mem 64 → Prop :=
          fun (har', nh', _, ()) mj => Step12BEvOut ctx lhs gtype har' nh' mj
        m6b_to_group
        refine wp_join_group P_tag0
          (fun _ ⟨har', nh', ch', ⟨⟩⟩ mj h => by
            m6b_let; exact hJs (lhs, il, gtype, har', nh', ch', ()) mj h) ?_
        intro Jt0 hJt0; m6b_split
        · obtain ⟨k, hk, hff⟩ := hhf_l hc
          obtain ⟨x, hx_mem, hx_eqv⟩ := hrhs_of_raw k hk
          have hun_ent := andFold_has_false_entails (step12BEvStOk_wit hokl) hcl0 hand0
            hlhs_eqv0 ⟨x, hx_mem, (raw[k]?.getD 0#32).toNat, hraw_lt k hk, hx_eqv, hff⟩
          m6b_steps; m6b_call hUnitFold
          refine step12BEv_unit_xor1 hokl hlhs_lt hun_ent hml fun uf su mu hoku _ hu2 hmu => ?_
          s12b_after_fold hexit hu2 false hoku mu hmu ch' =>
            exact hJt0 (arity, false, ch', ()) mu (step12BEvOut_nohash su hoku hmu)
        have hhf_f : has_false = false := by cases has_false <;> first | rfl | cases hc
        obtain ⟨_, hsub_l, hnohf'⟩ := hnohf_l hhf_f; clear hc; m6b_to_group
        refine wp_join_group P_tag0
          (fun _ ⟨har', nh', ch', ⟨⟩⟩ mj h => by m6b_let; exact hJt0 (har', nh', ch', ()) mj h) ?_
        intro Jt0b hJt0b; m6b_split
        · have hna0 : na.toNat = 0 := by rw [beq_iff_eq.mp hc]; rfl
          have hun_ent := ws_tag0_all_true_entails (step12BEvStOk_wit hokl) hcl0 hand0
            hlhs_eqv0 hraw_lt hraw_of_rhs (hna0 ▸ hnohf')
          m6b_steps; m6b_call hUnitFold
          refine step12BEv_unit hokl hlhs_lt hun_ent hml fun uf su mu hoku _ hu2 hmu => ?_
          s12b_after_fold hexit hu2 false hoku mu hmu ch' =>
            exact hJt0b (arity, false, ch', ()) mu (step12BEvOut_nohash su hoku hmu)
        have hna_pos : 0 < na.toNat := by
          have hne : na ≠ 0#32 := beq_eq_false_iff_ne.mp hc
          rcases Nat.eq_zero_or_pos na.toNat with hz | hp
          · exact absurd (BitVec.eq_of_toNat_eq hz) hne
          · exact hp
        have hfwd_l := ws_tag0_hf_false_fwd F_cur hraw_lt hraw_of_rhs hnohf'
        clear hc; m6b_to_group
        refine wp_join_group (ts := [])
          (fun () ms => ∃ tmps : List (BitVec 32), tmps.length = c.max_vars ∧
            (∀ j < na.toNat, ∃ k < arity.toNat, tmps[j]? = raw[k]?) ∧
            (∀ x ∈ rhs, ∃ r < 2 * cv0, LitEquiv (cnfOfClauses F_cur) x r ∧
              (s0.core.vals[r]?.getD 0#8 = 1#8 ∨
                ∃ j < na.toNat, (tmps[j]?.getD 0#32).toNat = r)) ∧
            (FullMem c (wsState s0 repri tmps) ⋆ R) ms) ?_ ?_
        · rintro _ ⟨⟩ ms ⟨tmps, htl_s, hsub_s, hfwd_s, hms⟩
          m6b_to_group
          refine wp_loop_break_group (brkTs := [.bool, i32, i32]) (lpTs := [i32, i32])
            (fun (clash, ua, _si, ()) md =>
              Step12BEvTag0DedupBrk ctx s0 repri tmps lhs na.toNat clash ua md)
            (fun remd (ua, si, ()) md =>
              remd = na.toNat - si.toNat ∧
              Step12BEvTag0DedupInv ctx s0 repri tmps na.toNat ua si md)
            ?_ ?_ ?_
          · rintro _ ⟨clash, ua, _si, ⟨⟩⟩ md ⟨tmpd, htl_d, hua_le, hsub_tmps, hcl_d, huf_d, hmd⟩
            have hokd := step12BEvStOk_wsState hok0 hrli htl_d hrepri
            dsimp only [ctx] at htl_d hua_le hcl_d huf_d
            obtain ⟨hsub_d, hsub_raw_d⟩ := ws_tag0_sub_raw_d hsub_tmps hsub_s hrhs_of_raw
              (by omega) hraw_len
            m6b_to_group
            refine wp_join_group P_tag0
              (fun _ ⟨har', nh', ch', ⟨⟩⟩ mj h => by
                m6b_let; exact hJt0b (har', nh', ch', ()) mj h) ?_
            intro Jt0c hJt0c; m6b_split
            · have hun_ent : (cnfOfClauses F_cur).EntailsClause (cnfClause [litNeg lhs.toNat]) := by
                rcases hcl_d hc with hmem | hpair
                · exact ev_tag0_clash_lhs_entails hand0 hlhs_eqv0 hsub_s hrhs_of_raw
                    hraw_len (by omega) hmem
                · exact ws_tag0_clash_entails hand0 hlhs_eqv0 hsub_s hrhs_of_raw
                    hraw_len (by omega) hpair
              m6b_steps; m6b_call hUnitFold
              refine step12BEv_unit_xor1 hokd hlhs_lt hun_ent hmd
                fun uf su mu hoku _ hu2 hmu => ?_
              s12b_after_fold hexit hu2 false hoku mu hmu ch' =>
                exact hJt0c (arity, false, ch', ()) mu (step12BEvOut_nohash su hoku hmu)
            obtain ⟨hua_pos, hcov_d⟩ := huf_d hc; clear hc; m6b_to_group
            refine wp_join_group P_tag0
              (fun _ ⟨har', nh', ch', ⟨⟩⟩ mj h => by
                m6b_let; exact hJt0c (har', nh', ch', ()) mj h) ?_
            intro Jt0d hJt0d; m6b_split
            · have hua0 : ua.toNat = 0 := by rw [beq_iff_eq.mp hc]; rfl
              omega
            have hev_d := ws_tag0_dedup_eval (step12BEvStOk_wit hokd) hcl0 rfl
              (by omega) hand0 hlhs_eqv0 hfwd_s hcov_d hsub_raw_d
            clear hc; m6b_to_group
            refine wp_join_group P_tag0
              (fun _ ⟨har', nh', ch', ⟨⟩⟩ mj h => by
                m6b_let; exact hJt0d (har', nh', ch', ()) mj h) ?_
            intro Jt0e hJt0e; m6b_split
            · have hua1 : ua.toNat = 1 := by rw [beq_iff_eq.mp hc]; rfl
              obtain ⟨ht0_lt, ht0_eqv⟩ := ws_tag0_ua1_equiv (by omega) hraw_len
                (hsub_d 0 (by omega)) hraw_lt (hua1 ▸ hev_d)
              have h0_tmp : (0#64 : BitVec 64).toNat < tmpd.length := by
                change 0 < tmpd.length; omega
              m6b_steps; m6b_call hEquivFold
              refine step12BEv_equiv hokd hlhs_lt ht0_lt ht0_eqv hmd
                fun ef se me hoke _ hef2 hme => ?_
              s12b_after_equiv_enq2 ctx hexit hEnqVar se hef2 false hoke me hme st_f hok_f m_f hm_f
                ch_f =>
                exact hJt0e (arity, false, ch_f, ()) m_f (step12BEvOut_nohash st_f hok_f hm_f)
            have hua_ge2 : 2 ≤ ua.toNat := by
              have hne := beq_eq_false_iff_ne.mp hc
              have : ua.toNat ≠ 1 := fun h => hne (BitVec.eq_of_toNat_eq h); omega
            have hlhs_vals : (lhs.setWidth 64).toNat < s0.core.vals.length := by
              rw [bv_zext32_toNat, hvlen0]; omega
            have hua_cv : ua.toNat ≤ cv0 := by omega
            have hua_max : ua.toNat ≤ step12BCongAndArityMax := by omega
            clear hc; m6b_to_group
            refine wp_join_group P_tag0
              (fun _ ⟨har', nh', ch', ⟨⟩⟩ mj h => by
                m6b_let; exact hJt0e (har', nh', ch', ()) mj h) ?_
            intro Jt0f hJt0f; m6b_split
            · have hv1 : s0.core.vals[lhs.toNat]?.getD 0#8 = 1#8 :=
                vals_sgt0_eq1 (by rw [hvlen0]; omega) hlhs_vals
                  ((step12BEvStOk_wit hokd).vals_domain lhs.toNat hlhs_lt) hc
              have hents := ws_tag0_lhs_true_ents (step12BEvStOk_wit hokd) hcl0 hlhs_lt hv1 hev_d
              m6b_to_group; refine wp_loop_inv
                (fun (ch_k, k, ()) mk => ∃ stk : FullState, k.toNat ≤ ua.toNat ∧
                  Step12BEvStOk ctx stk ∧ stk.core.tmp = tmpd ∧ (FullMem c stk ⋆ R) mk)
                (fun (_, k, ()) _ => ua.toNat - k.toNat)
                (fun Jk hJk => by
                  m6b_steps; exact hJk (false, 0#32, ()) md
                    ⟨wsState s0 repri tmpd, Nat.zero_le _, hokd, rfl, hmd⟩)
                (fun Jk (ch_k, k, ()) mk ⟨stk, hk_le, hokk, htmp_k, hmk⟩ ihk => ?_)
              m6b_split
              · have hk_lt : k.toNat < ua.toNat := bv32_ult_lt hc
                have hk_tmp : (k.setWidth 64).toNat < stk.core.tmp.length := by
                  rw [bv_zext32_toNat, htmp_k]; omega
                have hk1 : (k + 1#32).toNat = k.toNat + 1 := bv32_add1_lt_of (by omega)
                obtain ⟨htk_lt, htk_ent⟩ := ws_tag0_unit_k_args htmp_k hk_lt hraw_len (by omega)
                  hsub_d hraw_lt hents hk_tmp
                m6b_steps; m6b_call hUnitFold
                refine step12BEv_unit hokk htk_lt htk_ent hmk
                  fun uf su mu hoku htmpu hu2 hmu => ?_
                s12b_after_fold hexit hu2 ch_k hoku mu hmu ch_u =>
                  exact ihk (ch_u, k + 1#32, ()) mu (by dsimp only; omega)
                    ⟨su, by omega, hoku, htmpu.trans htmp_k, hmu⟩
              · m6b_let
                exact hJt0f (arity, false, ch_k, ()) mk (step12BEvOut_nohash stk hokk hmk)
            · -- Direct wide-AND hashing (no `ua > 64u` cap!)
              m6b_let; exact hJt0f (ua, true, false, ()) md
                ⟨wsState s0 repri tmpd, hokd,
                 fun _ => ⟨hua_cv, fun _ => ⟨hua_ge2, hua_max, hev_d⟩,
                   fun h => absurd (hgtype0.symm.trans h) (by decide),
                   fun h => absurd (hgtype0.symm.trans h) (by decide)⟩,
                 fun _ => hlhs_lt, hmd⟩
          · rintro Bd Ld remd ⟨ua, si, ⟨⟩⟩ md hBd hLd
              ⟨rfl, tmpd, htl_d, hua_le, hsi_le, hua_pos_if, htail_d, hsub_tmps, hcov_d, hmd⟩
            dsimp only [ctx] at htl_d; m6b_split
            rotate_left
            · have hsi_eq : si.toNat = na.toNat := by have := bv32_ult_not_lt hc; omega
              rw [hsi_eq] at hua_pos_if hcov_d
              m6b_steps; exact hBd (false, ua, si, ()) md
                ⟨tmpd, htl_d, hsi_eq ▸ hua_le, hsub_tmps, (fun h => by cases h),
                 fun _ => ⟨hua_pos_if hna_pos, hcov_d⟩, hmd⟩
            have hsi_lt : si.toNat < na.toNat := bv32_ult_lt hc
            have hna_max : na.toNat ≤ c.max_vars :=
              Nat.le_trans hna_le (Nat.le_trans (har_def ▸ har_cv) hcv_le)
            have hsi_tmp : (si.setWidth 64).toNat < tmpd.length := by rw [bv_zext32_toNat]; omega
            have hsi_tl : si.toNat < tmpd.length := by omega
            have hsi_ts : si.toNat < tmps.length := by omega
            let cur := tmps[si.toNat]'hsi_ts
            have hcur_eq : tmpd[(si.setWidth 64).toNat]'hsi_tmp = cur :=
              (list_getElem_zext32_eq rfl hsi_tmp hsi_tl).trans
                (list_getElem_eq_of_eqD hsi_tl
                  ((htail_d si.toNat (Nat.le_refl _) hsi_lt).trans (List.getElem?_eq_getElem
                    hsi_ts)))
            have hsi1 : (si + 1#32).toNat = si.toNat + 1 := bv32_add1_lt_of (by omega)
            have hua1 : (ua + 1#32).toNat = ua.toNat + 1 := bv32_add1_lt_of (by omega)
            clear hc; m6b_steps; m6b_split
            · have hcl_lhs : (lhs ^^^ 1#32).toNat ∈ (tmps.take na.toNat).map BitVec.toNat := by
                have hc' : cur = lhs ^^^ 1#32 := by
                  have h := beq_iff_eq.mp hc; simp only [wsState_tmp] at h; rwa [hcur_eq] at h
                have h_tk : (tmps.take na.toNat)[si.toNat]'(by
                    simp only [List.length_take, htl_s]; omega) = cur := by
                  simp only [List.getElem_take, cur]
                rw [List.mem_map]; exact ⟨cur, h_tk ▸ List.getElem_mem _, by rw [hc']⟩
              m6b_steps; exact hBd (true, ua, si + 1#32, ()) md
                ⟨tmpd, htl_d, by omega, hsub_tmps, fun _ =>
                  Or.inl (by rwa [← FullCongHelpers.bv32_xor1_eq_litNeg]),
                 (fun h => by cases h), hmd⟩
            clear hc; m6b_to_group
            refine wp_join_group (ts := [.bool, i32])
              (fun (_, ua', ()) md' =>
                Step12BEvTag0DedupInv ctx s0 repri tmps na.toNat ua' (si + 1#32) md')
              (fun _ ⟨_, ua', ⟨⟩⟩ md' ⟨t', ht', hu', hs', hp', htl', hs_t', hc', hm'⟩ => by
                m6b_let; exact hLd (na.toNat - (si + 1#32).toNat)
                  (ua', si + 1#32, ()) md' (by omega)
                  ⟨rfl, t', ht', hu', hs', hp', htl', hs_t', hc', hm'⟩) ?_
            intro Jua hJua; m6b_split
            · have hua0 : ua.toNat = 0 := by rw [beq_iff_eq.mp hc]; rfl
              have hsi0 : si.toNat = 0 :=
                Nat.eq_zero_of_not_pos fun h => by have := hua_pos_if h; omega
              have h0_tmp : (0#64 : BitVec 64).toNat < tmpd.length := by
                change 0 < tmpd.length; omega
              have hfs_tmp := focus_ws_tmp hmd; clear hmd
              generalize hR_tmp : FullTmpRest c (wsState s0 repri tmpd) ⋆ R = R_tmp at hfs_tmp
              m6b_steps; subst hR_tmp; simp only [wsState_tmp] at hm; rw [hcur_eq] at hm
              obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := ws_tag0_dedup_first_inv hsi0
                htl_d hsi_lt (by omega) htail_d (by omega)
              exact hJua (false, 1#32, ()) m ⟨tmpd.set 0 cur, h1,
                by rw [hsi1]; have h1' : (1#32).toNat = 1 := rfl; omega,
                hsi1 ▸ h3, hsi1 ▸ h4, hsi1 ▸ h5, h6, hsi1 ▸ h7, unfocus_ws_tmp hm⟩
            have hua_pos : 0 < ua.toNat := by
              have hne : ua ≠ 0#32 := beq_eq_false_iff_ne.mp hc
              rcases Nat.eq_zero_or_pos ua.toNat with hz | hp
              · exact absurd (BitVec.eq_of_toNat_eq hz) hne
              · exact hp
            have hum1_n : ((ua - 1#32).setWidth 64).toNat = ua.toNat - 1 := by
              rw [bv_zext32_toNat, bv32_sub1_toNat hua_pos]
            have hum1_tmp : ((ua - 1#32).setWidth 64).toNat < tmpd.length := by rw [hum1_n]; omega
            let prev := tmpd[((ua - 1#32).setWidth 64).toNat]'hum1_tmp
            have hprev_eq : prev = tmpd[ua.toNat - 1]'(by omega) :=
              list_getElem_congr hum1_n hum1_tmp (by omega)
            m6b_split
            · have hcur_prev : cur = tmpd[ua.toNat - 1]'(by omega) :=
                (hcur_eq ▸ beq_iff_eq.mp hc).trans hprev_eq
              obtain ⟨h1, h2, h3, h4, h5⟩ := ws_tag0_dedup_dup_inv' (by omega) (by omega)
                hua_pos hua_le hsi_lt hcur_prev htail_d hcov_d
              m6b_steps; exact hLd (na.toNat - (si + 1#32).toNat) (ua, si + 1#32, ()) md (by omega)
                ⟨rfl, tmpd, htl_d, hsi1 ▸ h1, hsi1 ▸ h2, hsi1 ▸ h3, hsi1 ▸ h4, hsub_tmps, hsi1 ▸ h5,
                 hmd⟩
            m6b_split
            · have hcur_xor : cur = prev ^^^ 1#32 := hcur_eq ▸ beq_iff_eq.mp hc
              have hcl := ws_tag0_dedup_clash (by omega) (by omega) hua_pos hua_le hsi_lt
                hprev_eq hsub_tmps hcur_xor
              m6b_steps; exact hBd (true, ua, si + 1#32, ()) md
                ⟨tmpd, htl_d, by omega, hsub_tmps, fun _ => Or.inr hcl, (fun h => by cases h), hmd⟩
            have hua_tmp : (ua.setWidth 64).toNat < tmpd.length := by rw [bv_zext32_toNat]; omega
            have hfs_tmp := focus_ws_tmp hmd; clear hmd
            generalize hR_tmp : FullTmpRest c (wsState s0 repri tmpd) ⋆ R = R_tmp at hfs_tmp
            m6b_steps; subst hR_tmp; simp only [wsState_tmp] at hm
            rw [bv_zext32_toNat, hcur_eq] at hm
            obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ :=
              ws_tag0_dedup_push_inv htl_d (by omega) (by omega)
              hua_le hsi_lt htail_d hsub_tmps hcov_d
            exact hJua (false, ua + 1#32, ()) m ⟨tmpd.set ua.toNat cur, h1, hua1 ▸ hsi1 ▸ h2,
              hsi1 ▸ h3, hua1 ▸ hsi1 ▸ h4, hsi1 ▸ h5, hua1 ▸ h6, hua1 ▸ hsi1 ▸ h7,
                unfocus_ws_tmp hm⟩
          · intro _ Ld _ hLd; m6b_steps
            exact hLd na.toNat (0#32, 0#32, ()) ms
              ⟨rfl, tmps, htl_s, Nat.zero_le _, Nat.zero_le _,
               fun h => absurd h (Nat.not_lt_zero _), fun _ _ _ => rfl,
               fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _),
                 hms⟩
        · intro _ hJsort; m6b_split
          · m6b_steps; m6b_call hSort
            refine ⟨tmpl, FullTmpRest c (wsState s0 repri tmpl) ⋆ R, by omega, focus_full_tmp hml,
              fun tmps ms htl_s hperm_s _ hms => ?_⟩
            have hms' : (FullMem c (wsState s0 repri tmps) ⋆ R) ms := ws_unfocus_tmp hms
            clear hms; m6b_steps
            obtain ⟨hsub_s, hfwd_s⟩ := ws_tag0_post_sort (htl_s.trans htl_l) htl_l hna_le
              (Nat.le_trans (har_def ▸ har_cv) hcv_le) hperm_s hsub_l hfwd_l
            exact hJsort () ms ⟨tmps, htl_s.trans htl_l, hsub_s, hfwd_s, hms'⟩
          · m6b_steps; exact hJsort () ml ⟨tmpl, htl_l, hsub_l, hfwd_l, hml⟩
      · rintro Bl Ll rem ⟨il, na, ⟨⟩⟩ ml hBl hLl
          ⟨rfl, tmpl, htl_l, hna_le, hil_le, htail_l, hsub_l, hnohf_l, hml⟩
        dsimp only [ctx] at htl_l; m6b_split
        rotate_left
        · have hil_eq : il.toNat = arity.toNat := by
            have hnot : ¬ il.toNat < arity.toNat := bv32_ult_not_lt hc
            omega
          m6b_steps; exact hBl (il, false, na, ()) ml
            ⟨tmpl, htl_l, by omega, (fun h => by cases h), fun _ => ⟨hil_eq, hsub_l,
              hil_eq ▸ hnohf_l⟩,
             hml⟩
        have hil_lt : il.toNat < arity.toNat := bv32_ult_lt hc
        have hil_tmp : (il.setWidth 64).toNat < tmpl.length := by rw [bv_zext32_toNat]; omega
        have hil_tl : il.toNat < tmpl.length := by omega
        have hil_raw : il.toNat < raw.length := by rw [hraw_len]; exact hil_lt
        have hr_eq : tmpl[(il.setWidth 64).toNat]'hil_tmp = raw[il.toNat]'hil_raw :=
          (list_getElem_zext32_eq rfl hil_tmp hil_tl).trans
            (list_getElem_eq_of_eqD hil_tl
              ((htail_l il.toNat (Nat.le_refl _) hil_lt).trans (List.getElem?_eq_getElem hil_raw)))
        have hr_lt : (raw[il.toNat]'hil_raw).toNat < 2 * cv0 := by
          have h := hraw_lt il.toNat hil_lt
          rwa [List.getElem?_eq_getElem hil_raw, Option.getD_some] at h
        have hr_vals' : (raw[il.toNat]'hil_raw).toNat < s0.core.vals.length := by omega
        have hr_vals : ((tmpl[(il.setWidth 64).toNat]'hil_tmp).setWidth 64).toNat <
            s0.core.vals.length := by rw [hr_eq, bv_zext32_toNat]; exact hr_vals'
        have hil1 : (il + 1#32).toNat = il.toNat + 1 := bv32_add1_lt_of (by omega)
        have hna1 : (na + 1#32).toNat = na.toNat + 1 := bv32_add1_lt_of (by omega)
        have hna_tmp : (na.setWidth 64).toNat < tmpl.length := by rw [bv_zext32_toNat]; omega
        have hrv_dom := hw0.vals_domain (raw[il.toNat]'hil_raw).toNat hr_lt
        have hrv_get : s0.core.vals[((tmpl[(il.setWidth 64).toNat]'hil_tmp).setWidth 64).toNat]'
            hr_vals = s0.core.vals[(raw[il.toNat]'hil_raw).toNat]'hr_vals' :=
          list_getElem_congr (by rw [hr_eq, bv_zext32_toNat]) hr_vals hr_vals'
        clear hc; m6b_split
        · have hr_gd : raw[il.toNat]?.getD 0#32 = raw[il.toNat]'hil_raw := by
            rw [List.getElem?_eq_getElem hil_raw, Option.getD_some]
          have hff : s0.core.vals[(raw[il.toNat]?.getD 0#32).toNat]?.getD 0#8 = 0xFF#8 := by
            rw [hr_gd]; exact vals_slt0_eqff hr_vals' _ hrv_dom (hrv_get ▸ hc)
          m6b_steps; exact hBl (il, true, na, ()) ml
            ⟨tmpl, htl_l, by omega, fun _ => ⟨il.toNat, hil_lt, hff⟩, (fun h => by cases h), hml⟩
        have hnslt_se : ((s0.core.vals[((tmpl[(il.setWidth 64).toNat]'hil_tmp).setWidth 64).toNat]'
            hr_vals).signExtend 32).slt 0#32 = false := hc
        m6b_to_group; refine wp_join_group (ts := [i32])
          (fun (na', ()) ml' => Step12BEvTag0P1Inv ctx s0 repri raw arity.toNat (il + 1#32) na' ml')
          (fun _ ⟨na', ⟨⟩⟩ ml' ⟨t', ht', hn', hi', htl', hs', hno', hm'⟩ => by
            m6b_let; exact hLl (arity.toNat - (il + 1#32).toNat) (il + 1#32, na', ()) ml' (by omega)
              ⟨rfl, t', ht', hn', hi', htl', hs', hno', hm'⟩) ?_
        intro Jna hJna; clear hc; m6b_split
        · have hfs_tmp := focus_ws_tmp hml; clear hml
          generalize hR_tmp : FullTmpRest c (wsState s0 repri tmpl) ⋆ R = R_tmp at hfs_tmp
          m6b_steps; subst hR_tmp; simp only [wsState_tmp] at hm; rw [bv_zext32_toNat, hr_eq] at hm
          obtain ⟨h1, h2, h3, h4, h5, h6⟩ := ws_tag0_il_push_inv htl_l hna_le hil_lt
            (Nat.le_trans (har_def ▸ har_cv) hcv_le) hraw_len htail_l hsub_l (fun _ => hnohf_l)
          exact hJna (na + 1#32, ()) m
            ⟨tmpl.set na.toNat (raw[il.toNat]'(by rw [hraw_len]; exact hil_lt)),
             h1, hna1 ▸ hil1 ▸ h2, hil1 ▸ h3, hil1 ▸ h4, hna1 ▸ h5,
             hil1 ▸ hna1 ▸ h6 rfl, unfocus_ws_tmp hm⟩
        · have hr_gd : raw[il.toNat]?.getD 0#32 = raw[il.toNat]'hil_raw := by
            rw [List.getElem?_eq_getElem hil_raw, Option.getD_some]
          have h1_val : s0.core.vals[(raw[il.toNat]?.getD 0#32).toNat]?.getD 0#8 = 1#8 := by
            rw [hr_gd]
            exact vals_nslt0_ne0_eq1 hr_vals' _ hrv_dom (hrv_get ▸ hnslt_se) (hrv_get ▸ hc)
          m6b_steps; exact hJna (na, ()) ml
            ⟨tmpl, htl_l, by omega, by omega, fun j hj1 hj2 => htail_l j (by omega) hj2, hsub_l,
             hil1 ▸ ws_tag0_il_true_inv h1_val (fun _ => hnohf_l) rfl, hml⟩
      · intro _ _ _ hLp; m6b_steps
        exact hLp arity.toNat (0#32, 0#32, ()) mi
          ⟨rfl, tmpi, htli, Nat.zero_le _, Nat.zero_le _,
           fun j _ hj => by simp only [raw, List.getElem?_take_of_lt hj],
           fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _), hmi⟩
    -- `gtype != 0u`: `gtype == 1u` vs `gtype == 2u` vs `else`
    have hgtype_ne0 : gtype ≠ 0#32 := beq_eq_false_iff_ne.mp hc
    clear hc; m6b_to_group
    refine wp_join_group (ts := [i32, i32, i32, i32, .bool, .bool])
      (fun (lhs', _iw, htag', harity, need_hash, _changed', ()) mj =>
        Step12BEvOut ctx lhs' htag' harity need_hash mj)
      (fun _ ⟨lhs', _iw, htag', harity, need_hash, changed', ⟨⟩⟩ mj h => by
        m6b_let; exact hJs (lhs', _iw, htag', harity, need_hash, changed', ()) mj h) ?_
    intro Js hJs; m6b_to_group
    refine wp_join_group (ts := []) (fun () m_n1 => gtype ≠ 1#32 ∧ m_n1 = mi) ?_ ?_
    · -- `gtype == 2u && arity == 3u` (ITE + ITE-to-XOR + ITE-to-AND) vs `else`
      rintro _ ⟨⟩ m_n1 ⟨hgtype_ne1, hm_n1⟩; subst m_n1
      clear hSort ihi htmp_i hgat_g0 hrhs0 hscr0_g hscr0_g1 hst_g hrl1 hrepr1 hm1'
      m6b_to_group
      refine wp_join_group (ts := [i32, i32, i32, .bool, .bool])
        (fun (lhs', htag', har', nh', _, ()) mj => Step12BEvOut ctx lhs' htag' har' nh' mj)
        (fun _ ⟨lhs', htag', har', nh', ch', ⟨⟩⟩ mj h => by
          m6b_let; exact hJs (lhs', i, htag', har', nh', ch', ()) mj h) ?_
      intro Jt2b hJt2b; m6b_split
      rotate_left
      · m6b_let; exact hJt2b (lhs, gtype, arity, false, false, ()) mi
          (step12BEvOut_nohash (wsState s0 repri tmpi) hoki hmi)
      have hgtype2 : gtype = 2#32 := beq_iff_eq.mp hc
      have htag2 := step12B_gtype_eq2 hgtype_def hgtype2
      clear hc; m6b_split
      rotate_left
      · m6b_let; exact hJt2b (lhs, gtype, arity, false, false, ()) mi
          (step12BEvOut_nohash (wsState s0 repri tmpi) hoki hmi)
      have har3 : arity = 3#32 := beq_iff_eq.mp hc
      have har3_n : arity.toNat = 3 := by rw [har3]; decide
      have hite0 := (step12B_gate_tag2_ite htag2 hsem0).2; clear hsem0
      have ht_ge3 : 3 ≤ tmpi.length := by omega
      have ht0_a : (0#64 : BitVec 64).toNat < tmpi.length := by change 0 < tmpi.length; omega
      have ht1_a : (1#64 : BitVec 64).toNat < tmpi.length := by change 1 < tmpi.length; omega
      have ht2_a : (2#64 : BitVec 64).toNat < tmpi.length := by change 2 < tmpi.length; omega
      let cl := tmpi[0]'(by omega); let tl := tmpi[1]'(by omega); let el := tmpi[2]'(by omega)
      have hcl_lt : cl.toNat < 2 * cv0 := (htmp_i' 0 (by omega)).1
      have htl_lt : tl.toNat < 2 * cv0 := (htmp_i' 1 (by omega)).1
      have hel_lt : el.toNat < 2 * cv0 := (htmp_i' 2 (by omega)).1
      have hcv2_le : 2 * cv0 ≤ 2 * c.max_vars := Nat.mul_le_mul_left 2 hcv_le
      have hcl_vals : (cl.setWidth 64).toNat < s0.core.vals.length := by
        rw [bv_zext32_toNat, hvlen0]; exact Nat.lt_of_lt_of_le hcl_lt hcv2_le
      have htl_vals : (tl.setWidth 64).toNat < s0.core.vals.length := by
        rw [bv_zext32_toNat, hvlen0]; exact Nat.lt_of_lt_of_le htl_lt hcv2_le
      have hel_vals : (el.setWidth 64).toNat < s0.core.vals.length := by
        rw [bv_zext32_toNat, hvlen0]; exact Nat.lt_of_lt_of_le hel_lt hcv2_le
      have hvc_dom := hw0.vals_domain cl.toNat hcl_lt
      have hvt_dom := hw0.vals_domain tl.toNat htl_lt
      have hve_dom := hw0.vals_domain el.toNat hel_lt
      have hite_t : IteGateDef (cnfOfClauses F_cur) lhs.toNat cl.toNat tl.toNat el.toNat :=
        ite_eval_congr hite0 hlhs_eqv0 (htmp_i' 0 (by omega)).2
          (htmp_i' 1 (by omega)).2 (htmp_i' 2 (by omega)).2
      let P_t2 : Tup Val [i32, i32, i32, .bool, .bool, i32, i32, i32] → Mem 64 → Prop :=
        fun (lhs', htag', har', nh', _, _, _, _, ()) mj => Step12BEvOut ctx lhs' htag' har' nh' mj
      clear hc; m6b_to_group
      refine wp_join_group P_t2
        (fun _ ⟨lhs', htag', har', nh', ch', _, _, _, ⟨⟩⟩ mj h => by
          m6b_let; exact hJt2b (lhs', htag', har', nh', ch', ()) mj h) ?_
      intro Jt2_1 hJt2_1; m6b_split
      · -- `vc != 0`
        have hvc_ne := vals_ne0_1_or_ff (by rw [hvlen0]; omega) hcl_vals hvc_dom hc
        have heqc := ite_cond_const_equiv hw0 hcl0 hite_t hcl_lt hvc_ne
        m6b_to_group; refine wp_join_group (ts := [i32])
          (fun (br, ()) mbr => mbr = mi ∧ br.toNat < 2 * cv0 ∧
            LitEquiv (cnfOfClauses F_cur) lhs.toNat br.toNat)
          (fun _ ⟨br, ⟨⟩⟩ mbr ⟨hmbr, hbr_lt, heqv_br⟩ => by
            subst mbr; m6b_steps; m6b_call hEquivFold
            refine step12BEv_equiv hoki hlhs_lt hbr_lt heqv_br hmi
              fun ef se me hoke _ hef2 hme => ?_
            s12b_after_equiv_enq2 ctx hexit hEnqVar se hef2 false hoke me hme st_f hok_f m_f hm_f
              ch_f =>
              exact hJt2_1 (lhs, gtype, arity, false, ch_f, cl, tl, el, ()) m_f
                (step12BEvOut_nohash st_f hok_f hm_f)) ?_
        intro Jbr hJbr; m6b_split
        · have hvc1 := vals_sgt0_eq1 (by rw [hvlen0]; omega) hcl_vals hvc_dom hc
          m6b_let; exact hJbr (tl, ()) mi
            ⟨rfl, htl_lt, by simpa only [hvc1, bv_zext32_toNat, ite_true] using heqc⟩
        · have hvcff := vals_ne0_nsgt0_eqff (by rw [hvlen0]; omega) hcl_vals hvc_dom hvc_ne hc
          m6b_let; exact hJbr (el, ()) mi ⟨rfl, hel_lt, by
            simpa only [hvcff, bv_zext32_toNat, show ((0xFF#8 : BitVec 8) = 1#8) = False from by
              decide, ite_false] using heqc⟩
      clear hc; m6b_to_group
      refine wp_join_group P_t2
        (fun _ ⟨l', ht', ha', nh', ch', c', t', e', ⟨⟩⟩ mj h => by
          m6b_let; exact hJt2_1 (l', ht', ha', nh', ch', c', t', e', ()) mj h) ?_
      intro Jt2_2 hJt2_2; m6b_split
      · -- `t == e`
        have hte : tl = el := beq_iff_eq.mp hc
        have heqt : LitEquiv (cnfOfClauses F_cur) lhs.toNat tl.toNat :=
          ite_equal_branches_equiv hite_t (LitEquiv.refl _ _) (LitEquiv.refl _ _)
            (by rw [hte]; exact LitEquiv.refl _ _)
        m6b_steps; m6b_call hEquivFold
        refine step12BEv_equiv hoki hlhs_lt htl_lt heqt hmi fun ef se me hoke _ hef2 hme => ?_
        s12b_after_equiv_enq2 ctx hexit hEnqVar se hef2 false hoke me hme
          st_f hok_f m_f hm_f ch_f =>
          exact hJt2_2 (lhs, gtype, arity, false, ch_f, cl, tl, el, ()) m_f
            (step12BEvOut_nohash st_f hok_f hm_f)
      clear hc; m6b_to_group
      refine wp_join_group P_t2
        (fun _ ⟨l', ht', ha', nh', ch', c', t', e', ⟨⟩⟩ mj h => by
          m6b_let; exact hJt2_2 (l', ht', ha', nh', ch', c', t', e', ()) mj h) ?_
      intro Jt2_3 hJt2_3; m6b_to_group
      refine wp_join_group (ts := []) (fun _ mf => mf = mi) ?_ (fun J1 hJ1 => by
        m6b_split
        rotate_left; · m6b_let; exact hJ1 () mi rfl
        have ht1 := vals_sgt0_eq1 (by rw [hvlen0]; omega) htl_vals hvt_dom hc; clear hc; m6b_split
        rotate_left; · m6b_let; exact hJ1 () mi rfl
        have heqc := ite_branches_true_false_equiv hw0 hcl0 hite_t htl_lt hel_lt ht1
          (vals_slt0_eqff (by rw [hvlen0]; omega) hel_vals hve_dom hc)
        m6b_steps; m6b_call hEquivFold
        refine step12BEv_equiv hoki hlhs_lt hcl_lt heqc hmi fun ef se me hoke _ hef2 hme => ?_
        s12b_after_equiv_enq2 ctx hexit hEnqVar se hef2 false hoke me hme
          st_f hok_f m_f hm_f ch_f =>
          exact hJt2_3 (lhs, gtype, arity, false, ch_f, cl, tl, el, ()) m_f
            (step12BEvOut_nohash st_f hok_f hm_f))
      rintro _ ⟨⟩ mf hmf; subst mf; m6b_to_group
      refine wp_join_group P_t2
        (fun _ ⟨l', ht', ha', nh', ch', c', t', e', ⟨⟩⟩ mj h => by
          m6b_let; exact hJt2_3 (l', ht', ha', nh', ch', c', t', e', ()) mj h) ?_
      intro Jt2_4 hJt2_4; m6b_to_group
      refine wp_join_group (ts := []) (fun _ mf => mf = mi) ?_ (fun J2 hJ2 => by
        m6b_split
        rotate_left; · m6b_let; exact hJ2 () mi rfl
        have htff := vals_slt0_eqff (by rw [hvlen0]; omega) htl_vals hvt_dom hc; clear hc; m6b_split
        rotate_left; · m6b_let; exact hJ2 () mi rfl
        have heqc := ite_branches_false_true_equiv hw0 hcl0 hite_t htl_lt hel_lt htff
          (vals_sgt0_eq1 (by rw [hvlen0]; omega) hel_vals hve_dom hc)
        m6b_steps; m6b_call hEquivFold
        refine step12BEv_equiv hoki hlhs_lt (bv32_xor1_lt_cv hcl_lt)
          (by change LitEquiv (cnfOfClauses F_cur) lhs.toNat (cl ^^^ 1#32).toNat
              rw [FullCongHelpers.bv32_xor1_eq_litNeg]; exact heqc)
          hmi fun ef se me hoke _ hef2 hme => ?_
        s12b_after_equiv_enq2 ctx hexit hEnqVar se hef2 false hoke me hme
          st_f hok_f m_f hm_f ch_f =>
          exact hJt2_4 (lhs, gtype, arity, false, ch_f, cl, tl, el, ()) m_f
            (step12BEvOut_nohash st_f hok_f hm_f))
      rintro _ ⟨⟩ mf hmf; subst mf; m6b_to_group
      refine wp_join_group P_t2
        (fun _ ⟨l', ht', ha', nh', ch', c', t', e', ⟨⟩⟩ mj h => by
          m6b_let; exact hJt2_4 (l', ht', ha', nh', ch', c', t', e', ()) mj h) ?_
      intro Jt2_5 hJt2_5; m6b_to_group
      refine wp_join_group (ts := []) (fun _ mf => mf = mi) ?_ (fun J3 hJ3 => by
        m6b_split
        rotate_left; · m6b_let; exact hJ3 () mi rfl
        have ht1 := vals_sgt0_eq1 (by rw [hvlen0]; omega) htl_vals hvt_dom hc; clear hc; m6b_split
        rotate_left; · m6b_let; exact hJ3 () mi rfl
        have hun := ite_branches_both_true_entails hw0 hcl0 hite_t htl_lt hel_lt ht1
          (vals_sgt0_eq1 (by rw [hvlen0]; omega) hel_vals hve_dom hc)
        m6b_steps; m6b_call hUnitFold
        refine step12BEv_unit hoki hlhs_lt hun hmi fun uf su mu hoku _ hu2 hmu => ?_
        s12b_after_fold hexit hu2 false hoku mu hmu ch' =>
          exact hJt2_5 (lhs, gtype, arity, false, ch', cl, tl, el, ()) mu
            (step12BEvOut_nohash su hoku hmu))
      rintro _ ⟨⟩ mf hmf; subst mf; m6b_to_group
      refine wp_join_group P_t2
        (fun _ ⟨l', ht', ha', nh', ch', c', t', e', ⟨⟩⟩ mj h => by
          m6b_let; exact hJt2_5 (l', ht', ha', nh', ch', c', t', e', ()) mj h) ?_
      intro Jt2_6 hJt2_6; m6b_to_group
      refine wp_join_group (ts := []) (fun _ mf => mf = mi) ?_ (fun J4 hJ4 => by
        m6b_split
        rotate_left; · m6b_let; exact hJ4 () mi rfl
        have htff := vals_slt0_eqff (by rw [hvlen0]; omega) htl_vals hvt_dom hc; clear hc; m6b_split
        rotate_left; · m6b_let; exact hJ4 () mi rfl
        have hun := ite_branches_both_false_entails hw0 hcl0 hite_t htl_lt hel_lt htff
          (vals_slt0_eqff (by rw [hvlen0]; omega) hel_vals hve_dom hc)
        m6b_steps; m6b_call hUnitFold
        refine step12BEv_unit_xor1 hoki hlhs_lt hun hmi fun uf su mu hoku _ hu2 hmu => ?_
        s12b_after_fold hexit hu2 false hoku mu hmu ch' =>
          exact hJt2_6 (lhs, gtype, arity, false, ch', cl, tl, el, ()) mu
            (step12BEvOut_nohash su hoku hmu))
      rintro _ ⟨⟩ mf hmf; subst mf; m6b_to_group
      refine wp_join_group P_t2
        (fun _ ⟨l', ht', ha', nh', ch', c', t', e', ⟨⟩⟩ mj h => by
          m6b_let; exact hJt2_6 (l', ht', ha', nh', ch', c', t', e', ()) mj h) ?_
      intro Jt2_7 hJt2_7; m6b_to_group
      refine wp_join_group (ts := []) (fun _ mf => mf = mi) ?_ (fun J5 hJ5 => by
        -- ITE-to-XOR (`vt == 0 && ve == 0 && t == (e ^ 1u)`)
        m6b_split
        rotate_left; · m6b_let; exact hJ5 () mi rfl
        clear hc; m6b_split
        rotate_left; · m6b_let; exact hJ5 () mi rfl
        clear hc; m6b_split
        rotate_left; · m6b_let; exact hJ5 () mi rfl
        have hte1 : tl = el ^^^ 1#32 := beq_iff_eq.mp hc
        let lhs_x := lhs ^^^ ((1#32 ^^^ cl ^^^ tl) &&& 1#32)
        let r0 := cl &&& ~~~1#32; let r1 := tl &&& ~~~1#32
        have hpack := fid_ite_to_xor_pack hite_t hlhs_lt hcl_lt htl_lt hte1
        change lhs_x.toNat < 2 * cv0 ∧ r0.toNat < 2 * cv0 ∧ r1.toNat < 2 * cv0 ∧
          XorListGateDef (cnfOfClauses F_cur) lhs_x.toNat [r0.toNat, r1.toNat] at hpack
        obtain ⟨hlx_lt, hr0_lt, hr1_lt, hxor_x⟩ := hpack
        let P_t2x : Tup Val [i32, i32, .bool, .bool] → Mem 64 → Prop :=
          fun (ht', ha', nh', _, ()) mj => Step12BEvOut ctx lhs_x ht' ha' nh' mj
        clear hc; m6b_to_group
        refine wp_join_group P_t2x
          (fun _ ⟨ht', ha', nh', ch', ⟨⟩⟩ mj h => by
            m6b_let; exact hJt2_7 (lhs_x, ht', ha', nh', ch', cl, tl, el, ()) mj h) ?_
        intro Jt2x0 hJt2x0; m6b_steps; m6b_split
        · have hr01 : r0 = r1 := beq_iff_eq.mp hc
          have hun := fid_xor_pair_eq_entails (hr01 ▸ hxor_x)
          m6b_steps; m6b_call hUnitFold
          refine step12BEv_unit_xor1 hoki hlx_lt hun hmi fun uf su mu hoku _ hu2 hmu => ?_
          s12b_after_fold hexit hu2 false hoku mu hmu ch' =>
            exact hJt2x0 (gtype, arity, false, ch', ()) mu (step12BEvOut_nohash su hoku hmu)
        clear hc
        have hlx_vals : (lhs_x.setWidth 64).toNat < s0.core.vals.length := by
          rw [bv_zext32_toNat, hvlen0]; omega
        have hlx_vals' : lhs_x.toNat < s0.core.vals.length := by
          rw [← bv_zext32_toNat lhs_x]; exact hlx_vals
        m6b_to_group; refine wp_join_group P_t2x
          (fun _ ⟨ht', ha', nh', ch', ⟨⟩⟩ mj h => by
            m6b_let; exact hJt2x0 (ht', ha', nh', ch', ()) mj h) ?_
        intro Jt2x hJt2x; m6b_split
        · have hvl_dom := hw0.vals_domain lhs_x.toNat hlx_lt
          have hvl_ne := vals_ne0_1_or_ff hlx_vals' hlx_vals hvl_dom hc
          have heqc := ev_tag1_ua2_equiv hw0 hcl0 hlx_lt hxor_x hvl_ne
          clear hc; m6b_to_group
          refine wp_join_group (ts := [i32])
            (fun (a0, ()) ma => ma = mi ∧ a0.toNat < 2 * cv0 ∧
              LitEquiv (cnfOfClauses F_cur) a0.toNat r1.toNat)
            (fun _ ⟨a0, ⟨⟩⟩ ma ⟨hma, ha0_lt, heqv_a⟩ => by
              subst ma; m6b_steps; m6b_call hEquivFold
              refine step12BEv_equiv hoki ha0_lt hr1_lt heqv_a hmi
                fun ef se me hoke _ hef2 hme => ?_
              s12b_after_equiv_enq2 ctx hexit hEnqVar se hef2 false hoke me hme st_f hok_f m_f hm_f
                ch_f =>
                exact hJt2x (gtype, arity, false, ch_f, ()) m_f
                  (step12BEvOut_nohash st_f hok_f hm_f)) ?_
          intro Ja0 hJa0; m6b_split
          · simp only [wsState_vals] at hc
            have hv1 := vals_sgt0_eq1 hlx_vals' hlx_vals hvl_dom hc
            m6b_let; exact hJa0 (r0 ^^^ 1#32, ()) mi
              ⟨rfl, bv32_xor1_lt_cv hr0_lt, by simpa only [hv1, ite_true] using heqc⟩
          · simp only [wsState_vals] at hc
            have hvff := vals_ne0_nsgt0_eqff hlx_vals' hlx_vals hvl_dom hvl_ne hc
            m6b_let; exact hJa0 (r0, ()) mi ⟨rfl, hr0_lt, by
              simpa only [hvff, show (0xFF#8 : BitVec 8) ≠ 1#8 by decide, ite_false] using heqc⟩
        clear hc; m6b_to_group
        refine wp_join_group (ts := [i32])
          (fun (v0, ()) m0' => m0' = mi ∧ v0 = if r0.ult r1 then r0 else r1) ?_ (fun Jv0 hJv0 => by
            m6b_split
            · have hrlt : r0.ult r1 = true := hc
              m6b_let; exact hJv0 (r0, ()) mi ⟨rfl, by simp only [hrlt, ite_true]⟩
            · have hrlt : r0.ult r1 = false := hc
              m6b_let; exact hJv0 (r1, ()) mi ⟨rfl, by simp only [hrlt, Bool.false_eq_true,
                ite_false]⟩)
        rintro _ ⟨v0, ⟨⟩⟩ m0' ⟨hm0', hv0⟩; subst m0'
        m6b_to_group
        refine wp_join_group (ts := [i32])
          (fun (v1, ()) m1' => m1' = m ∧ v1 = if r0.ult r1 then r1 else r0) ?_ (fun Jv1 hJv1 => by
            m6b_split
            · have hrlt : r0.ult r1 = true := hc
              m6b_let; exact hJv1 (r1, ()) m ⟨rfl, by simp only [hrlt, ite_true]⟩
            · have hrlt : r0.ult r1 = false := hc
              m6b_let; exact hJv1 (r0, ()) m ⟨rfl, by simp only [hrlt, Bool.false_eq_true,
                ite_false]⟩)
        rintro _ ⟨v1, ⟨⟩⟩ m1' ⟨hm1', hv1⟩; subst m1'
        have ht1_len : 1 < (tmpi.set 0 v0).length := by simp; omega
        m6b_steps
        let tmps := (tmpi.set 0 v0).set 1 v1
        have hoks := step12BEvStOk_wsState (t := tmps) hok0 hrli
          (by dsimp only [tmps]; rw [List.length_set, List.length_set]; exact htli) hrepri
        exact hJt2x (1#32, 2#32, true, false, ()) _
          ⟨wsState s0 repri tmps, hoks,
           (fun _ => by
             subst hv0 hv1
             exact step12B_pair_xor_hash_ok (by omega) (by omega) hr0_lt hr1_lt hxor_x),
           fun _ => hlx_lt, by assumption⟩)
      -- ITE-to-AND + fallback ITE canonicalization
      rintro _ ⟨⟩ mf hmf; subst mf; m6b_to_group
      let P_ia : Tup Val [i32, .bool, i32, i32] → Mem 64 → Prop :=
        fun (lhs_a, ite_and, a0, a1, ()) ma => ma = mi ∧
          (ite_and = true → lhs_a.toNat < 2 * cv0 ∧ a0.toNat < 2 * cv0 ∧ a1.toNat < 2 * cv0 ∧
            And2Sem F_cur lhs_a a0 a1) ∧
          (ite_and = false → lhs_a = lhs)
      refine wp_join_group P_ia ?_ ?_
      · rintro _ ⟨lhs_a, ite_and, a0, a1, ⟨⟩⟩ ma ⟨hma, hia_t, hia_f⟩; subst ma
        m6b_to_group; refine wp_join_group P_t2
          (fun _ ⟨l', ht', ha', nh', ch', c', t', e', ⟨⟩⟩ mj h => by
            m6b_let; exact hJt2_7 (l', ht', ha', nh', ch', c', t', e', ()) mj h) ?_
        intro Jia0 hJia0; m6b_split
        · -- `if (ite_and)`
          obtain ⟨hla_lt, ha0_lt, ha1_lt, hand2⟩ := hia_t hc
          let P_ia4 : Tup Val [i32, i32, .bool, .bool] → Mem 64 → Prop :=
            fun (ht', ha', nh', _, ()) mj => Step12BEvOut ctx lhs_a ht' ha' nh' mj
          clear hc; m6b_to_group
          refine wp_join_group P_ia4
            (fun _ ⟨ht', ha', nh', ch', ⟨⟩⟩ mj h => by
              m6b_let; exact hJia0 (lhs_a, ht', ha', nh', ch', cl, tl, el, ()) mj h) ?_
          intro Jia1 hJia1; m6b_split
          · have ha01 : a0 = a1 := beq_iff_eq.mp hc
            have heqv := fid_and2_eq_equiv (ha01.symm ▸ hand2)
            m6b_steps; m6b_call hEquivFold
            refine step12BEv_equiv hoki hla_lt ha0_lt heqv hmi fun ef se me hoke _ hef2 hme => ?_
            s12b_after_equiv_enq2 ctx hexit hEnqVar se hef2 false hoke me hme st_f hok_f m_f hm_f
              ch_f =>
              exact hJia1 (gtype, arity, false, ch_f, ()) m_f (step12BEvOut_nohash st_f hok_f hm_f)
          clear hc; m6b_to_group
          refine wp_join_group P_ia4
            (fun _ ⟨ht', ha', nh', ch', ⟨⟩⟩ mj h => by
              m6b_let; exact hJia1 (ht', ha', nh', ch', ()) mj h) ?_
          intro Jia2 hJia2; m6b_to_group
          refine wp_join_group (ts := []) (fun _ mcl => mcl = mi ∧
              (a0 = a1 ^^^ 1#32 ∨ a0 = lhs_a ^^^ 1#32 ∨ a1 = lhs_a ^^^ 1#32))
            (fun _ ⟨⟩ mcl ⟨hmcl, hcl_disj⟩ => by
              subst mcl
              have hun := fid_and2_clash_entails hand2 hcl_disj
              m6b_steps; m6b_call hUnitFold
              refine step12BEv_unit_xor1 hoki hla_lt hun hmi fun uf su mu hoku _ hu2 hmu => ?_
              s12b_after_fold hexit hu2 false hoku mu hmu ch' =>
                exact hJia2 (gtype, arity, false, ch', ()) mu (step12BEvOut_nohash su hoku hmu)) ?_
          intro Jcl hJcl; m6b_split
          · m6b_let; exact hJcl () mi ⟨rfl, Or.inl (beq_iff_eq.mp hc)⟩
          clear hc; m6b_split
          · m6b_let; exact hJcl () mi ⟨rfl, Or.inr (Or.inl (beq_iff_eq.mp hc))⟩
          clear hc; m6b_split
          · m6b_let; exact hJcl () mi ⟨rfl, Or.inr (Or.inr (beq_iff_eq.mp hc))⟩
          clear hc
          have hla_vals : (lhs_a.setWidth 64).toNat < s0.core.vals.length := by
            rw [bv_zext32_toNat, hvlen0]; omega
          m6b_to_group; refine wp_join_group P_ia4
            (fun _ ⟨ht', ha', nh', ch', ⟨⟩⟩ mj h => by
              m6b_let; exact hJia2 (ht', ha', nh', ch', ()) mj h) ?_
          intro Jia3 hJia3; m6b_split
          · have hv1 := vals_sgt0_eq1 (by rw [hvlen0]; omega) hla_vals
              (hw0.vals_domain lhs_a.toNat hla_lt) hc
            obtain ⟨he0, he1⟩ := fid_and2_lhs_true_entails hw0 hcl0 hla_lt hv1 hand2
            m6b_steps; m6b_call hUnitFold
            refine step12BEv_unit hoki ha0_lt he0 hmi fun u0 s1 m1 hok1 _ hu0_2 hm1 => ?_
            s12b_after_fold hexit hu0_2 false hok1 m1 hm1 ch1 =>
              m6b_steps; m6b_call hUnitFold
              refine step12BEv_unit hok1 ha1_lt he1 hm1 fun u1 s2 m2 hok2 _ hu1_2 hm2 => ?_
              s12b_after_fold hexit hu1_2 ch1 hok2 m2 hm2 ch2 =>
                exact hJia3 (gtype, arity, false, ch2, ()) m2 (step12BEvOut_nohash s2 hok2 hm2)
          clear hc; m6b_to_group
          refine wp_join_group (ts := [i32])
            (fun (v0, ()) m0' => m0' = mi ∧ v0 = if a0.ult a1 then a0 else a1) ?_
            (fun Jv0 hJv0 => by
              m6b_split
              · have halt : a0.ult a1 = true := hc
                m6b_let; exact hJv0 (a0, ()) mi ⟨rfl, by simp only [halt, ite_true]⟩
              · have halt : a0.ult a1 = false := hc
                m6b_let; exact hJv0 (a1, ()) mi ⟨rfl, by simp only [halt, Bool.false_eq_true,
                  ite_false]⟩)
          rintro _ ⟨v0, ⟨⟩⟩ m0' ⟨hm0', hv0⟩; subst m0'
          m6b_to_group
          refine wp_join_group (ts := [i32])
            (fun (v1, ()) m1' => m1' = m ∧ v1 = if a0.ult a1 then a1 else a0) ?_
            (fun Jv1 hJv1 => by
              m6b_split
              · have halt : a0.ult a1 = true := hc
                m6b_let; exact hJv1 (a1, ()) m ⟨rfl, by simp only [halt, ite_true]⟩
              · have halt : a0.ult a1 = false := hc
                m6b_let; exact hJv1 (a0, ()) m ⟨rfl, by simp only [halt, Bool.false_eq_true,
                  ite_false]⟩)
          rintro _ ⟨v1, ⟨⟩⟩ m1' ⟨hm1', hv1⟩; subst m1'
          have ht1_len : 1 < (tmpi.set 0 v0).length := by simp; omega
          m6b_steps
          let tmps := (tmpi.set 0 v0).set 1 v1
          have hoks := step12BEvStOk_wsState (t := tmps) hok0 hrli
            (by dsimp only [tmps]; rw [List.length_set, List.length_set]; exact htli) hrepri
          exact hJia3 (0#32, 2#32, true, false, ()) _
            ⟨wsState s0 repri tmps, hoks,
             (fun _ => by
               subst hv0 hv1; exact step12B_pair_and_hash_ok (by omega) (by omega) hand2),
             fun _ => hla_lt, by assumption⟩
        · -- `else` (`ite_and == false`): canonical ITE
          have hla_eq : lhs_a = lhs := hia_f (by cases ite_and <;> first | rfl | cases hc)
          subst lhs_a; clear hc; m6b_to_group
          refine wp_join_group (ts := [i32, i32, i32])
            (fun (c1, t1, e1, ()) m1 => m1 = mi ∧
              IteGateDef (cnfOfClauses F_cur) lhs.toNat c1.toNat t1.toNat e1.toNat) ?_ ?_
          · rintro _ ⟨c1, t1, e1, ⟨⟩⟩ m1 ⟨hm1, hite_1⟩; subst m1; m6b_to_group
            refine wp_join_group (ts := [i32, i32, i32])
              (fun (lhs_t, t2, e2, ()) m2 => m2 = mi ∧ lhs_t.toNat < 2 * cv0 ∧
                IteGateDef (cnfOfClauses F_cur) lhs_t.toNat c1.toNat t2.toNat e2.toNat) ?_ ?_
            · rintro _ ⟨lhs_t, t2, e2, ⟨⟩⟩ m2 ⟨hm2, hlht_lt, hite_f⟩; subst m2
              have hfs_tmp := focus_ws_tmp hmi; clear hmi
              generalize hR_tmp : FullTmpRest c (wsState s0 repri tmpi) ⋆ R = R_tmp at hfs_tmp
              have ht1_len : 1 < tmpi.length := by omega
              have ht2_len : 2 < tmpi.length := by omega
              m6b_steps; subst hR_tmp
              let tmps := ((tmpi.set 0 c1).set 1 t2).set 2 e2
              have htmps_mem : (FullMem c (wsState s0 repri tmps) ⋆ R) m := by
                simpa only [tmps, show (0#64 : BitVec 64).toNat = 0 from rfl,
                  show (1#64 : BitVec 64).toNat = 1 from rfl,
                  show (2#64 : BitVec 64).toNat = 2 from rfl] using unfocus_ws_tmp hm
              have hoks := step12BEvStOk_wsState (t := tmps) hok0 hrli
                (by dsimp only [tmps]
                    rw [List.length_set, List.length_set, List.length_set]; exact htli)
                hrepri
              exact hJia0 (lhs_t, gtype, arity, true, false, c1, t2, e2, ()) m
                ⟨wsState s0 repri tmps, hoks,
                 fun _ => ⟨har_def ▸ har_cv, fun h => absurd (hgtype2.symm.trans h) (by decide),
                   fun h => absurd (hgtype2.symm.trans h) (by decide),
                   fun _ => ⟨har3, ev_tag2_tmp_ite ht_ge3 hite_f⟩⟩,
                 fun _ => hlht_lt, htmps_mem⟩
            · intro Jfl hJfl; m6b_split
              · m6b_steps; refine hJfl (lhs ^^^ 1#32, t1 ^^^ 1#32, e1 ^^^ 1#32, ()) mi
                  ⟨rfl, bv32_xor1_lt_cv hlhs_lt, ?_⟩
                rw [FullCongHelpers.bv32_xor1_eq_litNeg, FullCongHelpers.bv32_xor1_eq_litNeg,
                  FullCongHelpers.bv32_xor1_eq_litNeg]
                exact iteGateDef_flip_out hite_1
              · m6b_let; exact hJfl (lhs, t1, e1, ()) mi ⟨rfl, hlhs_lt, hite_1⟩
          · intro Jc hJc; m6b_split
            · m6b_steps; refine hJc (cl ^^^ 1#32, el, tl, ()) mi ⟨rfl, ?_⟩
              rw [FullCongHelpers.bv32_xor1_eq_litNeg]; exact iteGateDef_flip_cond hite_t
            · m6b_let; exact hJc (cl, tl, el, ()) mi ⟨rfl, hite_t⟩
      · -- 8-branch ITE-to-AND classifier
        intro Ja hJa; m6b_split
        · have hv := vals_sgt0_eq1 (by rw [hvlen0]; omega) htl_vals hvt_dom hc
          m6b_steps; exact hJa (lhs ^^^ 1#32, true, cl ^^^ 1#32, el ^^^ 1#32, ()) mi
            ⟨rfl, fun _ => ⟨bv32_xor1_lt_cv hlhs_lt, bv32_xor1_lt_cv hcl_lt, bv32_xor1_lt_cv hel_lt,
              fid_and2_of_vt_pos hw0 hcl0 hite_t htl_lt hv⟩, fun h => by cases h⟩
        clear hc; m6b_to_group; refine wp_join_group P_ia
          (fun _ ⟨l', b', x', y', ⟨⟩⟩ m' h => by m6b_let; exact hJa (l', b', x', y', ()) m' h) ?_
        intro Ja2 hJa2; m6b_split
        · have hv := vals_slt0_eqff (by rw [hvlen0]; omega) htl_vals hvt_dom hc
          m6b_steps; exact hJa2 (lhs, true, cl ^^^ 1#32, el, ()) mi
            ⟨rfl, fun _ => ⟨hlhs_lt, bv32_xor1_lt_cv hcl_lt, hel_lt,
              fid_and2_of_vt_neg hw0 hcl0 hite_t htl_lt hv⟩, fun h => by cases h⟩
        clear hc; m6b_to_group; refine wp_join_group P_ia
          (fun _ ⟨l', b', x', y', ⟨⟩⟩ m' h => by m6b_let; exact hJa2 (l', b', x', y', ()) m' h) ?_
        intro Ja3 hJa3; m6b_split
        · have hv := vals_sgt0_eq1 (by rw [hvlen0]; omega) hel_vals hve_dom hc
          m6b_steps; exact hJa3 (lhs ^^^ 1#32, true, cl, tl ^^^ 1#32, ()) mi
            ⟨rfl, fun _ => ⟨bv32_xor1_lt_cv hlhs_lt, hcl_lt, bv32_xor1_lt_cv htl_lt,
              fid_and2_of_ve_pos hw0 hcl0 hite_t hel_lt hv⟩, fun h => by cases h⟩
        clear hc; m6b_to_group; refine wp_join_group P_ia
          (fun _ ⟨l', b', x', y', ⟨⟩⟩ m' h => by m6b_let; exact hJa3 (l', b', x', y', ()) m' h) ?_
        intro Ja4 hJa4; m6b_split
        · have hv := vals_slt0_eqff (by rw [hvlen0]; omega) hel_vals hve_dom hc
          m6b_steps; exact hJa4 (lhs, true, cl, tl, ()) mi
            ⟨rfl, fun _ => ⟨hlhs_lt, hcl_lt, htl_lt,
              fid_and2_of_ve_neg hw0 hcl0 hite_t hel_lt hv⟩, fun h => by cases h⟩
        clear hc; m6b_to_group; refine wp_join_group P_ia
          (fun _ ⟨l', b', x', y', ⟨⟩⟩ m' h => by m6b_let; exact hJa4 (l', b', x', y', ()) m' h) ?_
        intro Ja5 hJa5; m6b_split
        · have hct : cl = tl := beq_iff_eq.mp hc
          m6b_steps; exact hJa5 (lhs ^^^ 1#32, true, cl ^^^ 1#32, el ^^^ 1#32, ()) mi
            ⟨rfl, fun _ => ⟨bv32_xor1_lt_cv hlhs_lt, bv32_xor1_lt_cv hcl_lt, bv32_xor1_lt_cv hel_lt,
              fun α hα => by
                rw [FullCongHelpers.bv32_xor1_eq_litNeg, FullCongHelpers.bv32_xor1_eq_litNeg,
                  FullCongHelpers.bv32_xor1_eq_litNeg]
                exact fid_ite_and_c_eq_t (hct ▸ hite_t) α hα⟩, fun h => by cases h⟩
        clear hc; m6b_to_group; refine wp_join_group P_ia
          (fun _ ⟨l', b', x', y', ⟨⟩⟩ m' h => by m6b_let; exact hJa5 (l', b', x', y', ()) m' h) ?_
        intro Ja6 hJa6; m6b_split
        · have hcnt : tl.toNat = litNeg cl.toNat := by
            have h1 : cl = tl ^^^ 1#32 := beq_iff_eq.mp hc
            have h2 : tl = cl ^^^ 1#32 := by rw [h1, BitVec.xor_assoc, BitVec.xor_self,
              BitVec.xor_zero]
            rw [h2, FullCongHelpers.bv32_xor1_eq_litNeg]
          m6b_steps; exact hJa6 (lhs, true, cl ^^^ 1#32, el, ()) mi
            ⟨rfl, fun _ => ⟨hlhs_lt, bv32_xor1_lt_cv hcl_lt, hel_lt, fun α hα => by
              rw [FullCongHelpers.bv32_xor1_eq_litNeg]
              exact fid_ite_and_c_eq_nt (hcnt ▸ hite_t) α hα⟩,
             fun h => by cases h⟩
        clear hc; m6b_to_group; refine wp_join_group P_ia
          (fun _ ⟨l', b', x', y', ⟨⟩⟩ m' h => by m6b_let; exact hJa6 (l', b', x', y', ()) m' h) ?_
        intro Ja7 hJa7; m6b_split
        · have hcne : el.toNat = litNeg cl.toNat := by
            have h1 : cl = el ^^^ 1#32 := beq_iff_eq.mp hc
            have h2 : el = cl ^^^ 1#32 := by rw [h1, BitVec.xor_assoc, BitVec.xor_self,
              BitVec.xor_zero]
            rw [h2, FullCongHelpers.bv32_xor1_eq_litNeg]
          m6b_steps; exact hJa7 (lhs ^^^ 1#32, true, cl, tl ^^^ 1#32, ()) mi
            ⟨rfl, fun _ => ⟨bv32_xor1_lt_cv hlhs_lt, hcl_lt, bv32_xor1_lt_cv htl_lt, fun α hα => by
              rw [FullCongHelpers.bv32_xor1_eq_litNeg, FullCongHelpers.bv32_xor1_eq_litNeg]
              exact fid_ite_and_c_eq_ne (hcne ▸ hite_t) α hα⟩, fun h => by cases h⟩
        clear hc; m6b_to_group; refine wp_join_group (ts := [.bool, i32, i32])
          (fun (b', x', y', ()) m' => P_ia (lhs, b', x', y', ()) m')
          (fun _ ⟨b', x', y', ⟨⟩⟩ m' h => by m6b_let; exact hJa7 (lhs, b', x', y', ()) m' h) ?_
        intro Ja8 hJa8; m6b_split
        · have hce : cl = el := beq_iff_eq.mp hc
          m6b_steps; exact hJa8 (true, cl, tl, ()) mi
            ⟨rfl, fun _ => ⟨hlhs_lt, hcl_lt, htl_lt,
              fun α hα => fid_ite_and_c_eq_e (hce ▸ hite_t) α hα⟩, fun h => by cases h⟩
        · m6b_let; exact hJa8 (false, 0#32, 0#32, ()) mi ⟨rfl, (fun h => by cases h), fun _ => rfl⟩
    · -- `gtype == 1u && 2 ≤ arity ≤ 4` (XOR + XOR LHS self-cancel)
      intro Jn1 hJn1; m6b_split
      rotate_left
      · have hgtype_ne1 : gtype ≠ 1#32 := beq_eq_false_iff_ne.mp hc
        m6b_steps; exact hJn1 () mi ⟨hgtype_ne1, rfl⟩
      have hgtype1 : gtype = 1#32 := beq_iff_eq.mp hc
      have htag1 := step12B_gtype_eq1 hgtype_def hgtype1
      have ⟨har2_1, har4_1, hxor0⟩ := step12B_gate_tag1_xor htag1 hsem0
      rw [← har_def] at har2_1 har4_1 hxor0
      have hscr_ge : g.toNat + 2 + arity.toNat ≤ scr0.length := by
        obtain ⟨_, hr, _⟩ := hrhs0 (arity.toNat - 1) (by omega)
        have := (List.getElem?_eq_some_iff.mp hr).1; omega
      have hxor_t : XorListGateDef (cnfOfClauses F_cur) lhs.toNat
          ((tmpi.take arity.toNat).map BitVec.toNat) :=
        ev_tag1_rx_congr hscr_ge htmp_i_len hlhs_eqv0
          (fun k hk => (htmp_i k (hi_eq ▸ hk)).2) hxor0
      let rx0 := (tmpi.take arity.toNat).map BitVec.toNat
      have hrx0_len : rx0.length = arity.toNat := by
        simp only [rx0, List.length_map, List.length_take, Nat.min_eq_left htmp_i_len]
      clear hc ihi htmp_i hsem0 hgat_g0 hscr0_g hscr0_g1 hst_g hi_le hrl1 hrepr1 hm1' hJn1 hrhs0
        hxor0
      m6b_split
      rotate_left
      · have hlt := bv32_ule_not_le hc; change arity.toNat < 2 at hlt; omega
      clear hc; m6b_split
      rotate_left
      · have hgt := bv32_ule_not_le hc; change 4 < arity.toNat at hgt; omega
      clear hc; m6b_to_group
      refine wp_loop_inv (ts := [i32, i32, i32])
        (fun (i1, flip1, na1, ()) ml =>
          Step12BEvTag1P1Inv ctx s0 repri tmpi rx0 arity.toNat i1 flip1 na1 ml)
        (fun (i1, _, _, ()) _ => arity.toNat - i1.toNat)
        (fun Jl1 hJl1 => by
          m6b_steps; exact hJl1 (0#32, 0#32, 0#32, ()) mi
            ⟨tmpi, htli, Nat.zero_le _, Nat.zero_le _, Or.inl rfl, (fun _ _ _ => rfl),
             (fun _ h => by cases h),
             (fun _ _ => by
               simp only [show (0#32 : BitVec 32).toNat = 0 from rfl, List.take_zero, List.map_nil,
                 xorEvalList_nil, show ((0#32 : BitVec 32) == 1#32) = false from rfl,
                   Bool.false_bne]),
             hmi⟩)
        (fun Jl1 (i1, flip1, na1, ()) ml ⟨tmpl, htl_l, hna_le, hi1_le, hfl1, htail_l, hlt_l,
          hxor_l, hml⟩ ihl1 => ?_)
      dsimp only [ctx] at htl_l hlt_l hxor_l; m6b_split
      · have hi1_lt : i1.toNat < arity.toNat := bv32_ult_lt hc
        have hi1_tmp : (i1.setWidth 64).toNat < tmpl.length := by rw [bv_zext32_toNat]; omega
        have hi1_tl : i1.toNat < tmpl.length := by omega
        let rl := tmpi[i1.toNat]'(by omega)
        have hrl_eq : tmpl[(i1.setWidth 64).toNat]'hi1_tmp = rl :=
          (list_getElem_zext32_eq rfl hi1_tmp hi1_tl).trans
            (list_getElem_eq_of_eqD hi1_tl
              ((htail_l i1.toNat (Nat.le_refl _) hi1_lt).trans (List.getElem?_eq_getElem (by
                omega))))
        have hrl_lt : rl.toNat < 2 * cv0 := (htmp_i' i1.toNat hi1_lt).1
        have hrl_vals : (rl.setWidth 64).toNat < s0.core.vals.length := by
          rw [bv_zext32_toNat, hvlen0]; omega
        have hrl_vals' : rl.toNat < s0.core.vals.length := by
          rw [bv_zext32_toNat] at hrl_vals; exact hrl_vals
        have hrv_dom := hw0.vals_domain rl.toNat hrl_lt
        have hrx_i : rx0[i1.toNat]'(by omega) = rl.toNat := by
          simp only [rx0, List.getElem_map, List.getElem_take, rl]
        have hi1_n : (i1 + 1#32).toNat = i1.toNat + 1 := bv32_add1_lt_of (by omega)
        have hna1_n : (na1 + 1#32).toNat = na1.toNat + 1 := bv32_add1_lt_of (by omega)
        have htr_vals : ((tmpl[(i1.setWidth 64).toNat]'hi1_tmp).setWidth 64).toNat <
            s0.core.vals.length := by rw [hrl_eq]; exact hrl_vals
        clear hc; m6b_to_group
        refine wp_join_group (ts := [i32, i32])
          (fun (fl', na', ()) ml' =>
            Step12BEvTag1P1Inv ctx s0 repri tmpi rx0 arity.toNat (i1 + 1#32) fl' na' ml')
          (fun _ ⟨fl', na', ⟨⟩⟩ ml' ⟨t', ht', hn', hi', hfl', htl', hlt', hx', hm'⟩ => by
            m6b_let; exact ihl1 (i1 + 1#32, fl', na', ()) ml' (by dsimp only; omega)
              ⟨t', ht', hn', hi', hfl', htl', hlt', hx', hm'⟩) ?_
        intro Jst hJst; m6b_steps; m6b_split
        · have hc_ne : ((s0.core.vals[(rl.setWidth 64).toNat]'hrl_vals).signExtend 32 != 0#32) =
              true := by
            simp only [wsState_vals, wsState_tmp] at hc
            rwa [list_getElem_congr (by rw [hrl_eq]) htr_vals hrl_vals] at hc
          have hrl_ne0 := vals_ne0_1_or_ff hrl_vals' hrl_vals hrv_dom hc_ne
          clear hc hc_ne; m6b_to_group
          refine wp_join_group (ts := [i32])
            (fun (fl', ()) mfl => mfl = ml ∧ (fl' = 0#32 ∨ fl' = 1#32) ∧
              ∀ α : Nat → Bool, (cnfOfClauses F_cur).Sat α →
                xorEvalList α (rx0.take (i1 + 1#32).toNat) = ((fl' == 1#32) !=
                  xorEvalList α ((tmpl.take na1.toNat).map BitVec.toNat)))
            (fun _ ⟨fl', ⟨⟩⟩ mfl ⟨hmfl, hfl', hx'⟩ => by
              subst mfl; m6b_let; exact hJst (fl', na1, ()) ml
                ⟨tmpl, htl_l, by omega, by omega, hfl', fun q hq1 hq2 => htail_l q (by omega) hq2,
                 hlt_l, hx', hml⟩) ?_
          intro Jf hJf; m6b_split
          · have hc_gt : (0#32 : BitVec 32).slt ((s0.core.vals[(rl.setWidth 64).toNat]'
                hrl_vals).signExtend 32) = true := by
              simp only [wsState_vals, wsState_tmp] at hc
              rwa [list_getElem_congr (by rw [hrl_eq]) htr_vals hrl_vals] at hc
            have h1_v := vals_sgt0_eq1 hrl_vals' hrl_vals hrv_dom hc_gt
            m6b_let; refine hJf (flip1 ^^^ 1#32, ()) ml ⟨rfl, by
              rcases hfl1 with rfl | rfl <;> simp,
              fun α hα => ?_⟩
            rw [hi1_n]; exact ev_xor_list_step_eval_ne0 hfl1 (hxor_l α hα) (by omega) hrx_i
              (Or.inl (entails_eval_true (vals1_entails hw0 hcl0 hrl_lt h1_v) hα))
              (by rw [entails_eval_true (vals1_entails hw0 hcl0 hrl_lt h1_v) hα]; rfl)
          · have hc_ngt : (0#32 : BitVec 32).slt ((s0.core.vals[(rl.setWidth 64).toNat]'
                hrl_vals).signExtend 32) = false := by
              simp only [wsState_vals, wsState_tmp] at hc
              rwa [list_getElem_congr (by rw [hrl_eq]) htr_vals hrl_vals] at hc
            have hff_v := vals_ne0_nsgt0_eqff hrl_vals' hrl_vals hrv_dom hrl_ne0 hc_ngt
            m6b_let; refine hJf (flip1, ()) ml ⟨rfl, hfl1, fun α hα => ?_⟩
            rw [hi1_n]; exact ev_xor_list_step_eval_ne0 hfl1 (hxor_l α hα) (by omega) hrx_i
              (Or.inr (entails_neg_eval_false (valsff_entails_neg hw0 hcl0 hrl_lt hff_v) hα))
              (by rw [entails_neg_eval_false (valsff_entails_neg hw0 hcl0 hrl_lt hff_v) hα]; rfl)
        · clear hc; let e0 := rl &&& ~~~1#32
          have hfs_tmp := focus_ws_tmp hml; clear hml
          generalize hR_tmp : FullTmpRest c (wsState s0 repri tmpl) ⋆ R = R_tmp at hfs_tmp
          have hna_arr : (na1.setWidth 64).toNat < tmpl.length := by rw [bv_zext32_toNat]; omega
          m6b_steps; subst hR_tmp; simp only [wsState_tmp] at hm ⊢
          rw [bv_zext32_toNat, hrl_eq] at hm; rw [hrl_eq]
          obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := ev_tag1_push_inv htl_l hna_le hi1_lt
            (Nat.le_trans (har_def ▸ har_cv) hcv_le) hfl1 htail_l hlt_l hrl_lt (by omega) hrx_i
            hxor_l
          exact hJst (flip1 ^^^ (rl &&& 1#32), na1 + 1#32, ()) m
            ⟨tmpl.set na1.toNat e0, h1, hna1_n ▸ hi1_n ▸ h2, hi1_n ▸ h3, h4, hi1_n ▸ h5,
             hna1_n ▸ h6, hna1_n ▸ hi1_n ▸ h7, unfocus_ws_tmp hm⟩
      -- Post P1: sort + dedup + XOR LHS self-cancel + fold/hash
      have hi1_eq : i1.toNat = arity.toNat := by
        have hnot : ¬ i1.toNat < arity.toNat := bv32_ult_not_lt hc
        omega
      rw [hi1_eq, List.take_of_length_le (by omega)] at hxor_l
      let lhs' := lhs ^^^ flip1
      have hlhs'_lt : lhs'.toNat < 2 * cv0 := xor1_bit01_lt hlhs_lt hfl1
      have hxor_l' : XorListGateDef (cnfOfClauses F_cur) lhs'.toNat
          ((tmpl.take na1.toNat).map BitVec.toNat) := fun α hα => by
        have h1 := hxor_l α hα; rw [← hxor_t α hα] at h1
        dsimp only [lhs']; rw [xor1_bit01_eval hfl1, h1]
        cases (flip1 == 1#32) <;> cases xorEvalList α ((tmpl.take na1.toNat).map BitVec.toNat) <;>
          rfl
      clear hc ihl1 htail_l hxor_l hrx0_len; m6b_to_group
      refine wp_join_group (ts := [])
        (fun () ms => ∃ tmps : List (BitVec 32), tmps.length = c.max_vars ∧
          (∀ q < na1.toNat, (tmps[q]?.getD 0#32).toNat < 2 * cv0 ∧
            (tmps[q]?.getD 0#32).toNat % 2 = 0) ∧
          XorListGateDef (cnfOfClauses F_cur) lhs'.toNat ((tmps.take na1.toNat).map BitVec.toNat) ∧
          (FullMem c (wsState s0 repri tmps) ⋆ R) ms) ?_ (fun _ hJsort1 => by
          m6b_split
          · m6b_steps; m6b_call hSort
            refine ⟨tmpl, FullTmpRest c (wsState s0 repri tmpl) ⋆ R, by omega, focus_full_tmp hml,
              fun tmps ms htl_s hperm_s _ hms => ?_⟩
            have hms' : (FullMem c (wsState s0 repri tmps) ⋆ R) ms := ws_unfocus_tmp hms
            clear hms; m6b_steps
            obtain ⟨hlt_s, hxor_s⟩ := ev_tag1_post_sort (by omega)
              (htl_s.trans htl_l ▸ htl_l.symm) hperm_s hlt_l hxor_l'
            exact hJsort1 () ms ⟨tmps, htl_s.trans htl_l, hlt_s, hxor_s, hms'⟩
          · m6b_steps; exact hJsort1 () ml ⟨tmpl, htl_l, hlt_l, hxor_l', hml⟩)
      rintro _ ⟨⟩ ms ⟨tmps, htl_s, hlt_s, hxor_s, hms⟩; m6b_to_group
      let P_d1 := Step12BEvTag1DedupInv ctx s0 repri tmps lhs' na1.toNat
      refine wp_loop_inv (ts := [i32, i32]) P_d1 (fun (jd, _, ()) _ => na1.toNat - jd.toNat)
        (fun Jd hJd => by
          m6b_steps; exact hJd (0#32, 0#32, ()) ms
            ⟨tmps, htl_s, Nat.zero_le _, Nat.zero_le _, (fun _ _ _ => rfl), (fun _ h => by cases h),
             (fun α hα => by
               rw [hxor_s α hα]; simp only [show (0#32 : BitVec 32).toNat = 0 from rfl,
                 List.take_zero, List.map_nil, xorEvalList_nil, Nat.sub_zero, List.drop_zero,
                 Bool.false_bne]), hms⟩)
        (fun Jd (jd, ua, ()) md ⟨tmpd, htl_d, hua_le, hjd_le, htail_d, hlt_d, hxord, hmd⟩ ihd => ?_)
      dsimp only [ctx] at htl_d hlt_d hxord; m6b_split
      · have hjd_lt : jd.toNat < na1.toNat := by dsimp only at hc; exact bv32_ult_lt hc
        clear hc; have hjd1_n : (jd + 1#32).toNat = jd.toNat + 1 := bv32_add1_lt_of (by omega)
        m6b_to_group
        refine wp_join_group (ts := [i32, i32])
          (fun x mp => (na1.toNat - x.1.toNat < na1.toNat - jd.toNat) ∧ P_d1 x mp)
          (fun _ ⟨jd', ua', ⟨⟩⟩ mp ⟨hdec, hP⟩ => by m6b_let; exact ihd (jd', ua', ()) mp hdec hP) ?_
        intro Js_d hJs_d; m6b_to_group
        refine wp_join_group (ts := []) (fun () mp => mp = md) ?_ (fun Jp hJp => by
          m6b_split
          rotate_left; · m6b_let; exact hJp () md rfl
          have hjd1_lt : jd.toNat + 1 < na1.toNat := by
            dsimp only at hc; rw [← hjd1_n]; exact bv32_ult_lt hc
          have hjd_arr : (jd.setWidth 64).toNat < tmpd.length := by rw [bv_zext32_toNat]; omega
          have hjd1_arr : ((jd + 1#32).setWidth 64).toNat < tmpd.length := by
            rw [bv_zext32_toNat]; omega
          m6b_steps; m6b_split
          rotate_left; · m6b_let; exact hJp () md rfl
          have heq_d : tmpd[(jd.setWidth 64).toNat]'hjd_arr =
              tmpd[((jd + 1#32).setWidth 64).toNat]'hjd1_arr := by
            dsimp only at hc; exact beq_iff_eq.mp hc
          have hsame : tmps[jd.toNat]?.getD 0#32 = tmps[jd.toNat + 1]?.getD 0#32 := by
            have hjd_m : jd.toNat < tmpd.length := by omega
            have hjd1_m : jd.toNat + 1 < tmpd.length := by omega
            have hl := list_getElem_congr (bv_zext32_toNat jd) hjd_arr hjd_m
            have hr := list_getElem_congr (by rw [bv_zext32_toNat, hjd1_n]) hjd1_arr hjd1_m
            rw [← htail_d jd.toNat (Nat.le_refl _) hjd_lt,
              ← htail_d (jd.toNat + 1) (by omega) hjd1_lt,
              List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega),
              Option.getD_some, Option.getD_some, hl.symm.trans (heq_d.trans hr)]
          have hjd2_n : (jd + 2#32).toNat = jd.toNat + 2 := bv32_add2_lt_of (by omega)
          m6b_let; refine hJs_d (jd + 2#32, ua, ()) md
            ⟨by dsimp only; rw [hjd2_n]; omega, ⟨tmpd, htl_d, by omega, by rw [hjd2_n]; omega,
              (fun q hq1 hq2 => by rw [hjd2_n] at hq1; exact htail_d q (by omega) hq2), hlt_d,
              (fun (α : Nat → Bool) (hα : (cnfOfClauses F_cur).Sat α) => by
                rw [hjd2_n]; exact ev_tag1_dedup_skip_eq (by omega) hjd1_lt hsame (hxord α hα)),
              hmd⟩⟩)
        rintro _ ⟨⟩ mp rfl
        have hjd_arr : (jd.setWidth 64).toNat < tmpd.length := by rw [bv_zext32_toNat]; omega
        have hua_arr : (ua.setWidth 64).toNat < tmpd.length := by rw [bv_zext32_toNat]; omega
        have hua1_n : (ua + 1#32).toNat = ua.toNat + 1 := bv32_add1_lt_of (by omega)
        let vjd := tmpd[(jd.setWidth 64).toNat]'hjd_arr
        have hvjd_eq : vjd = tmps[jd.toNat]?.getD 0#32 := by
          have hjd_m : jd.toNat < tmpd.length := by omega
          have hv0 : vjd = tmpd[jd.toNat]'hjd_m :=
            list_getElem_congr (bv_zext32_toNat jd) hjd_arr hjd_m
          have hg := htail_d jd.toNat (Nat.le_refl _) hjd_lt
          rw [List.getElem?_eq_getElem (by omega)] at hg; rw [hv0, ← hg, Option.getD_some]
        have hfs_tmp := focus_ws_tmp hmd; clear hmd
        generalize hR_tmp : FullTmpRest c (wsState s0 repri tmpd) ⋆ R = R_tmp at hfs_tmp
        m6b_steps; subst hR_tmp
        let tmpd' := tmpd.set ua.toNat vjd
        have hmd'' : (FullMem c (wsState s0 repri tmpd') ⋆ R) m := by
          try simp only [wsState_tmp] at hm
          simpa only [tmpd', vjd, bv_zext32_toNat] using unfocus_ws_tmp hm
        m6b_let; refine hJs_d (jd + 1#32, ua + 1#32, ()) m
          ⟨by dsimp only; rw [hjd1_n]; omega,
           ⟨tmpd', by simp only [tmpd', List.length_set]; exact htl_d,
            by rw [hua1_n, hjd1_n]; omega,
            by rw [hjd1_n]; omega,
            (fun q hq1 hq2 => by
              dsimp only [tmpd']; rw [hjd1_n] at hq1; rw [List.getElem?_set_ne (by omega)]
              exact htail_d q (by omega) hq2),
            (fun q hq => by
              dsimp only [tmpd']; rw [hua1_n] at hq
              by_cases hqe : q = ua.toNat
              · subst hqe; rw [List.getElem?_set_self (by omega), Option.getD_some, hvjd_eq]
                exact hlt_s jd.toNat hjd_lt
              · rw [List.getElem?_set_ne (Ne.symm hqe)]; exact hlt_d q (by omega)),
            (fun α hα => by
              rw [hua1_n, hjd1_n]; exact ev_tag1_dedup_push_eq (by omega) (by omega) hjd_lt
                (by omega) hvjd_eq (hxord α hα)), hmd''⟩⟩
      -- Post dedup: XOR LHS self-cancel then `if (need_hash)`
      have hjd_eq : jd.toNat = na1.toNat := by dsimp only at hc; have := bv32_ult_not_lt hc; omega
      rw [hjd_eq, Nat.sub_self, List.take_zero, List.map_nil] at hxord
      have hxor_d : XorListGateDef (cnfOfClauses F_cur) lhs'.toNat
          ((tmpd.take ua.toNat).map BitVec.toNat) := fun α hα => by
        have h := hxord α hα; change _ = (_ != xorEvalList α []) at h
        rwa [show xorEvalList α [] = false from rfl, Bool.bne_false] at h
      have hokd := step12BEvStOk_wsState hok0 hrli htl_d hrepri
      clear hc ihd htail_d hSort; m6b_to_group
      let P_sc : Tup Val [i32, .bool, .bool, i32] → Mem 64 → Prop :=
        fun (_isc, nh_sc, _ch_sc, ua_sc, ()) msc =>
          (nh_sc = true → msc = md ∧ ua_sc = ua) ∧
          (nh_sc = false → ∃ st_sc : FullState,
            Step12BEvStOk ctx st_sc ∧ (FullMem c st_sc ⋆ R) msc)
      refine wp_join_group P_sc ?_ ?_
      · -- `if (need_hash)`
        rintro _ ⟨isc, nh_sc, ch_sc, ua_sc, ⟨⟩⟩ msc ⟨hsc_t, hsc_f⟩
        let P_t1 : Tup Val [i32, .bool, .bool] → Mem 64 → Prop :=
          fun (har', nh', _, ()) mj => Step12BEvOut ctx lhs' gtype har' nh' mj
        m6b_to_group
        refine wp_join_group P_t1
          (fun _ ⟨har', nh', ch', ⟨⟩⟩ mj h => by
            m6b_let; exact hJs (lhs', isc, gtype, har', nh', ch', ()) mj h) ?_
        intro Jt1h hJt1h; m6b_split
        rotate_left
        · have hnhf : nh_sc = false := by cases nh_sc <;> first | rfl | cases hc
          obtain ⟨st_sc, hok_sc, hm_sc⟩ := hsc_f hnhf
          m6b_let; rw [hnhf]; exact hJt1h (arity, false, ch_sc, ()) msc
            (step12BEvOut_nohash st_sc hok_sc hm_sc)
        have hnh_t : nh_sc = true := hc
        obtain ⟨hmsc, hua_eq⟩ := hsc_t hnh_t; subst msc; subst ua_sc; subst nh_sc; clear hc
        m6b_to_group; refine wp_join_group P_t1
          (fun _ ⟨har', nh', ch', ⟨⟩⟩ mj h => by m6b_let; exact hJt1h (har', nh', ch', ()) mj h) ?_
        intro Jt1d hJt1d; m6b_split
        · have hua0 : ua.toNat = 0 := by rw [beq_iff_eq.mp hc]; rfl
          have hnil : ((tmpd.take ua.toNat).map BitVec.toNat) = [] := by
            rw [hua0, List.take_zero, List.map_nil]
          have hun_ent := ev_tag1_ua0_entails (hnil ▸ hxor_d)
          m6b_steps; m6b_call hUnitFold
          refine step12BEv_unit_xor1 hokd hlhs'_lt hun_ent hmd fun uf su mu hoku _ hu2 hmu => ?_
          s12b_after_fold hexit hu2 ch_sc hoku mu hmu ch' =>
            exact hJt1d (arity, false, ch', ()) mu (step12BEvOut_nohash su hoku hmu)
        have hua_ne0 : ua ≠ 0#32 := beq_eq_false_iff_ne.mp hc; clear hc; m6b_to_group
        refine wp_join_group P_t1
          (fun _ ⟨har', nh', ch', ⟨⟩⟩ mj h => by m6b_let; exact hJt1d (har', nh', ch', ()) mj h) ?_
        intro Jt1e hJt1e; m6b_split
        · have hua1 : ua.toNat = 1 := by rw [beq_iff_eq.mp hc]; rfl
          have h0_arr : 0 < tmpd.length := by omega
          have hone : (tmpd.take ua.toNat).map BitVec.toNat = [(tmpd[0]'h0_arr).toNat] := by
            rw [hua1, List.take_one, List.head?_eq_getElem?, List.getElem?_eq_getElem h0_arr]; rfl
          have hr0_lt : (tmpd[0]'h0_arr).toNat < 2 * cv0 := by
            have h := (hlt_d 0 (by omega)).1; rwa [List.getElem?_eq_getElem h0_arr,
              Option.getD_some] at h
          have heqv := ev_tag1_ua1_equiv (hone ▸ hxor_d)
          m6b_steps; m6b_call hEquivFold
          refine step12BEv_equiv hokd hlhs'_lt hr0_lt heqv hmd fun ef se me hoke _ hef2 hme => ?_
          s12b_after_equiv_enq2 ctx hexit hEnqVar se hef2 ch_sc hoke me hme st_f hok_f m_f hm_f ch_f
            =>
            exact hJt1e (arity, false, ch_f, ()) m_f (step12BEvOut_nohash st_f hok_f hm_f)
        have hua_ne1 : ua ≠ 1#32 := beq_eq_false_iff_ne.mp hc
        have hua_ge2 : 2 ≤ ua.toNat := by
          rcases Nat.lt_trichotomy ua.toNat 1 with h0 | h1 | h2
          · exact absurd (BitVec.eq_of_toNat_eq (by change ua.toNat = 0; omega)) hua_ne0
          · exact absurd (BitVec.eq_of_toNat_eq h1) hua_ne1
          · exact h2
        clear hc; m6b_to_group
        refine wp_join_group P_t1
          (fun _ ⟨har', nh', ch', ⟨⟩⟩ mj h => by m6b_let; exact hJt1e (har', nh', ch', ()) mj h) ?_
        intro Jt1f hJt1f
        have hJfb : Jt1f (ua, true, ch_sc, ()) md :=
          hJt1f (ua, true, ch_sc, ()) md ⟨wsState s0 repri tmpd, hokd,
            fun _ => ⟨by show ua.toNat ≤ cv0; omega,
              fun h => absurd (hgtype1.symm.trans h) (by decide),
              fun _ => ⟨hua_ge2, by show ua.toNat ≤ 4; omega, fun q hq => (hlt_d q hq).1, hxor_d⟩,
              fun h => absurd (hgtype1.symm.trans h) (by decide)⟩, fun _ => hlhs'_lt, hmd⟩
        m6b_split
        rotate_left; · m6b_let; exact hJfb
        have hua2 : ua.toNat = 2 := by rw [beq_iff_eq.mp hc]; rfl
        have h0_arr : 0 < tmpd.length := by omega
        have h1_arr : 1 < tmpd.length := by omega
        let t0 := tmpd[0]'h0_arr; let t1 := tmpd[1]'h1_arr
        have ht0_lt : t0.toNat < 2 * cv0 := by
          have h := (hlt_d 0 (by omega)).1; rwa [List.getElem?_eq_getElem h0_arr,
            Option.getD_some] at h
        have ht1_lt : t1.toNat < 2 * cv0 := by
          have h := (hlt_d 1 (by omega)).1; rwa [List.getElem?_eq_getElem h1_arr,
            Option.getD_some] at h
        have htwo : (tmpd.take ua.toNat).map BitVec.toNat = [t0.toNat, t1.toNat] := by
          rw [hua2]; apply List.ext_getElem
          · simp [List.length_take]; omega
          · intro k _ hk2; rcases k with _ | _ | k'
            · simp [t0]
            · simp [t1]
            · simp at hk2; omega
        have hl_vals : (lhs'.setWidth 64).toNat < s0.core.vals.length := by
          rw [bv_zext32_toNat, hvlen0]; omega
        clear hc; m6b_split
        rotate_left; · m6b_let; exact hJfb
        have hvl_dom := hw0.vals_domain lhs'.toNat hlhs'_lt
        have hl_vals' : lhs'.toNat < s0.core.vals.length := by
          rw [← bv_zext32_toNat lhs']; exact hl_vals
        have hvl_ne := vals_ne0_1_or_ff hl_vals' hl_vals hvl_dom hc
        have heqc := ev_tag1_ua2_equiv hw0 hcl0 hlhs'_lt (htwo ▸ hxor_d) hvl_ne
        clear hc; m6b_to_group
        refine wp_join_group (ts := [i32])
          (fun (a0, ()) ma => ma = md ∧ a0.toNat < 2 * cv0 ∧
            LitEquiv (cnfOfClauses F_cur) a0.toNat t1.toNat)
          (fun _ ⟨a0, ⟨⟩⟩ ma ⟨hma, ha0_lt, heqv_a⟩ => by
            subst ma; m6b_steps; m6b_call hEquivFold
            refine step12BEv_equiv hokd ha0_lt ht1_lt heqv_a hmd
              fun ef se me hoke _ hef2 hme => ?_
            s12b_after_equiv_enq2 ctx hexit hEnqVar se hef2 ch_sc hoke me hme st_f hok_f m_f hm_f
              ch_f =>
              exact hJt1f (arity, false, ch_f, ()) m_f (step12BEvOut_nohash st_f hok_f hm_f)) ?_
        intro Ja0 hJa0
        clear hUnitFold hEquivFold hEnqVar hQ hJt1f hJt1e hJt1d hJt1h hJs hok0 htmp_i' hpref0 hq0
        m6b_split
        · simp only [wsState_vals] at hc
          have hv1 := vals_sgt0_eq1 hl_vals' hl_vals hvl_dom hc
          m6b_let
          refine wp_load_of (s12b_load_full_tmp0 hmd (by rw [wsState_tmp]; exact h0_arr)) ?_
          m6b_let; exact hJa0 (t0 ^^^ 1#32, ()) md
            ⟨rfl, bv32_xor1_lt_cv ht0_lt, by simpa only [hv1, ite_true] using heqc⟩
        · simp only [wsState_vals] at hc
          have hvff := vals_ne0_nsgt0_eqff hl_vals' hl_vals hvl_dom hvl_ne hc
          m6b_let
          refine wp_load_of (s12b_load_full_tmp0 hmd (by rw [wsState_tmp]; exact h0_arr)) ?_
          m6b_let; exact hJa0 (t0, ()) md
            ⟨rfl, ht0_lt, by simpa only [hvff, show (0xFF#8 : BitVec 8) ≠ 1#8 by decide,
              ite_false] using heqc⟩
      · -- XOR LHS self-cancel body
        intro Jsc hJsc
        clear htmp_i' hxor_l' hxor_s hlt_s htl_s hxor_t har2_1 har4_1 hscr_ge hpref0 hq0
        dsimp only
        exact s12bEv_tag1_selfcancel_wp hexit hUnitFold hEquivFold hEnqVar rfl rfl rfl
          hrli htl_d hrepri hokd hlhs'_lt (by omega) hlt_d hxor_d hmd
          fun isc nh_sc ch_sc ua_sc msc h1 h2 =>
            hJsc (isc, nh_sc, ch_sc, ua_sc, ()) msc ⟨h1, h2⟩

end EvalGateHelpers

end LeanQbe.T.Examples.Kissat.FullFidelityStep12B

end
