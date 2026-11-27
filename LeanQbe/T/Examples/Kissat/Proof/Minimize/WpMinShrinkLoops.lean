/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Minimize.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Minimize.WpMinShrinkHelpers
public import LeanQbe.T.Examples.Kissat.Src.Minimize
public import LeanQbe.T.Logic.CanonicalEnv
import LeanQbe.T.Examples.Kissat.Proof.Minimize.MinTactics
import LeanQbe.T.Examples.Kissat.Proof.Minimize.WpMark
import LeanQbe.T.Examples.Kissat.Proof.Minimize.WpMinDfs
import LeanQbe.T.Examples.Kissat.Proof.Minimize.WpShrinkBlk
import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena1
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.ControlComb

/-!
# Early Loop Helpers for `full_min_shrink_m6` (`WpMinShrinkLoops`)

Factored AST definitions and WP proofs for the initial marking loop, `work_stk1` push block,
fallback `full_min_lit_dfs_m8` loop, and main level-block shrink loop used by `WpMinShrink`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Minimize

open Std Std.Sat
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics
open LeanQbe.T.Examples.Kissat.Src.Minimize
open FullMinTactics
open scoped FullArenaTactics FullMinTactics
open Kraken.Bedrock2.Test

public section

/-! ## 1. Exposed AST Builders & State Store Bridges -/

@[expose] def m6MarkLoopExpr {V : Ty → Type} {C : List Ty → Type} {rs : List Ty}
    (h pTmp tlen : V i64) (k : Expr V C rs) : Expr V C rs :=
  .group (sig := [[i64]]) (fun Ls => .cons (fun i =>
    .let_ (Op.mk (.cmp .ult i64 .bool rfl) (.var i.fst, .var tlen, ())) fun cmp =>
    .jnz (.var cmp.fst)
      (.let_ (Op.mk (.mul i64) (.var i.fst, .imm 4, ())) fun off =>
       .let_ (Op.mk (.add i64) (.var pTmp, .var off.fst, ())) fun addr =>
       .load i32 (.var addr.fst) fun ld =>
       .let_ (Op.mk (.lshr i32) (.var ld, .imm 1, ())) fun sh =>
       .let_ (Op.mk (.trunc 32 8) (.imm 2, ())) fun t2 =>
       .call "full_min_mark" (as := [i64, i32, i8]) (bs := [])
         (.var h, .var sh.fst, .var t2.fst, ()) fun _ =>
       .let_ (Op.mk (.add i64) (.var i.fst, .imm 1, ())) fun i1 =>
       .jump Ls.fst (.var i1.fst, ()))
      k) .nil) (fun Ls => .jump Ls.fst (.imm 0, ()))

@[expose] def m6AnaPushExpr {V : Ty → Type} {C : List Ty → Type} {rs : List Ty}
    (h pTmp cv beg : V i64) (Jout : C []) : Expr V C rs :=
  .let_ (Op.mk (.add i64) (.var h, .imm 848, ())) fun pWs1Addr =>
  .load i64 (.var pWs1Addr.fst) fun pWs1 =>
  .let_ (Op.mk (.mul i64) (.var beg, .imm 4, ())) fun boff =>
  .let_ (Op.mk (.add i64) (.var pTmp, .var boff.fst, ())) fun baddr =>
  .load i32 (.var baddr.fst) fun blit =>
  .let_ (Op.mk (.lshr i32) (.var blit, .imm 1, ())) fun uipv =>
  .group (sig := [[]]) (fun _Js => .cons (fun _ => .jump Jout ()) .nil) (fun Js =>
    .let_ (Op.mk (.zext 32 64) (.var uipv.fst, ())) fun uip64 =>
    .let_ (Op.mk (.cmp .ult i64 .bool rfl) (.var uip64.fst, .var cv, ())) fun hucv =>
    .jnz (.var hucv.fst)
      (.let_ (Op.mk (.add i64) (.var h, .imm 1144, ())) fun prs1 =>
       .load i64 (.var prs1.fst) fun rsz1 =>
       .let_ (Op.mk (.cmp .ult i64 .bool rfl) (.var rsz1, .var cv, ())) fun hrc =>
       .jnz (.var hrc.fst)
         (.let_ (Op.mk (.add i64) (.var h, .imm 1144, ())) fun prs2 =>
          .load i64 (.var prs2.fst) fun rsz2 =>
          .let_ (Op.mk (.mul i64) (.var rsz2, .imm 4, ())) fun roff =>
          .let_ (Op.mk (.add i64) (.var pWs1, .var roff.fst, ())) fun waddr =>
          .store (.var uipv.fst) (.var waddr.fst)
            (.let_ (Op.mk (.add i64) (.var h, .imm 1144, ())) fun prs3 =>
             .load i64 (.var prs3.fst) fun rsz3 =>
             .let_ (Op.mk (.add i64) (.var rsz3, .imm 1, ())) fun rsz1p =>
             .let_ (Op.mk (.add i64) (.var h, .imm 1144, ())) fun prs4 =>
             .store (.var rsz1p.fst) (.var prs4.fst) (.jump Js.fst ())))
         (.jump Js.fst ()))
      (.jump Js.fst ()))

@[expose] def m6Mk2LoopExpr {V : Ty → Type} {C : List Ty → Type} {rs : List Ty}
    (h pTmp beg end_b : V i64) (Jout : C []) : Expr V C rs :=
  .group (sig := [[i64]]) (fun Lm => .cons (fun mk2 =>
    .let_ (Op.mk (.cmp .ult i64 .bool rfl) (.var mk2.fst, .var end_b, ())) fun cmpm =>
    .jnz (.var cmpm.fst)
      (.group (sig := [[]]) (fun _J => .cons (fun _ =>
         .let_ (Op.mk (.add i64) (.var mk2.fst, .imm 1, ())) fun mk21 =>
         .jump Lm.fst (.var mk21.fst, ())) .nil) fun Jn =>
       .let_ (Op.mk (.mul i64) (.var mk2.fst, .imm 4, ())) fun moff =>
       .let_ (Op.mk (.add i64) (.var pTmp, .var moff.fst, ())) fun maddr =>
       .load i32 (.var maddr.fst) fun mlit =>
       .call "full_min_lit_dfs_m8" (as := [i64, i32, .bool, .bool]) (bs := [.bool])
         (.var h, .var mlit, .imm false, .imm false, ()) fun okd =>
       .jnz (.var okd.fst)
         (.let_ (Op.mk (.mul i64) (.var mk2.fst, .imm 4, ())) fun soff =>
          .let_ (Op.mk (.add i64) (.var pTmp, .var soff.fst, ())) fun saddr =>
          .store (@Arg.imm V i32 (4294967295 : BitVec 32)) (.var saddr.fst) (.jump Jn.fst ()))
         (.jump Jn.fst ()))
      (.jump Jout ())) .nil)
    (fun Lm => .jump Lm.fst (.var beg, ()))

@[expose] def m6ShrinkLoopExpr {V : Ty → Type} {C : List Ty → Type} {rs : List Ty}
    (h pTmp pLvl pTpos cv tlen : V i64) (k : Expr V C rs) : Expr V C rs :=
  let op64 (c : OpCode [i64, i64] [i64]) (a b : Arg V i64) := Op.mk c (a, b, ())
  .group (sig := [[i64]]) (fun Lbeg => .cons (fun beg =>
    .let_ (Op.mk (.cmp .ult i64 .bool rfl) (.var beg.fst, .var tlen, ())) fun cmpb =>
    .jnz (.var cmpb.fst)
      (.let_ (op64 (.mul i64) (.var beg.fst) (.imm 4)) fun bo1 =>
       .let_ (op64 (.add i64) (.var pTmp) (.var bo1.fst)) fun ba1 =>
       .load i32 (.var ba1.fst) fun blit1 =>
       .let_ (Op.mk (.lshr i32) (.var blit1, .imm 1, ())) fun bv1 =>
       .let_ (Op.mk (.zext 32 64) (.var bv1.fst, ())) fun bv1_64 =>
       .let_ (op64 (.mul i64) (.var bv1_64.fst) (.imm 4)) fun lo1 =>
       .let_ (op64 (.add i64) (.var pLvl) (.var lo1.fst)) fun la1 =>
       .load i32 (.var la1.fst) fun blvl =>
       .let_ (op64 (.mul i64) (.var beg.fst) (.imm 4)) fun bo2 =>
       .let_ (op64 (.add i64) (.var pTmp) (.var bo2.fst)) fun ba2 =>
       .load i32 (.var ba2.fst) fun blit2 =>
       .let_ (Op.mk (.lshr i32) (.var blit2, .imm 1, ())) fun bv2 =>
       .let_ (Op.mk (.zext 32 64) (.var bv2.fst, ())) fun bv2_64 =>
       .let_ (op64 (.mul i64) (.var bv2_64.fst) (.imm 4)) fun to1 =>
       .let_ (op64 (.add i64) (.var pTpos) (.var to1.fst)) fun ta1 =>
       .load i32 (.var ta1.fst) fun tpos0 =>
       .let_ (Op.mk (.zext 32 64) (.var tpos0, ())) fun max_tr0 =>
       .let_ (op64 (.add i64) (.var beg.fst) (.imm 1)) fun end_b0 =>
       .group (sig := [[i64, i64]]) (fun Lend => .cons (fun p30 =>
         .group (sig := [[]]) (fun _Jpost => .cons (fun _ =>
           .group (sig := [[]]) (fun _Jn => .cons (fun _ =>
             .jump Lbeg.fst (.var p30.snd.fst, ())) .nil) fun Jn =>
           .let_ (op64 (.sub i64) (.var p30.snd.fst) (.var beg.fst)) fun len_b =>
           .let_ (Op.mk (.cmp .uge i64 .bool rfl) (.var len_b.fst, .imm 2, ())) fun hge2 =>
           .jnz (.var hge2.fst)
             (.group (sig := [[]]) (fun _Jb => .cons (fun _ => .jump Jn.fst ()) .nil) fun Jb =>
              .call "full_shrink_blk_bool_m8" (as := [i64, i64, i64, i32, i64])
                (bs := [.bool])
                (.var h, .var beg.fst, .var p30.snd.fst, .var blvl, .var p30.fst, ()) fun okb =>
              .jnz (.var okb.fst)
                (m6AnaPushExpr h pTmp cv beg.fst Jb.fst)
                (m6Mk2LoopExpr h pTmp beg.fst p30.snd.fst Jb.fst))
             (.jump Jn.fst ())) .nil) fun Jp =>
         .let_ (Op.mk (.cmp .ult i64 .bool rfl) (.var p30.snd.fst, .var tlen, ())) fun cmpe =>
         .jnz (.var cmpe.fst)
           (.let_ (op64 (.mul i64) (.var p30.snd.fst) (.imm 4)) fun eo1 =>
            .let_ (op64 (.add i64) (.var pTmp) (.var eo1.fst)) fun ea1 =>
            .load i32 (.var ea1.fst) fun elit1 =>
            .let_ (Op.mk (.lshr i32) (.var elit1, .imm 1, ())) fun ev1 =>
            .let_ (Op.mk (.zext 32 64) (.var ev1.fst, ())) fun ev1_64 =>
            .let_ (op64 (.mul i64) (.var ev1_64.fst) (.imm 4)) fun elo1 =>
            .let_ (op64 (.add i64) (.var pLvl) (.var elo1.fst)) fun ela1 =>
            .load i32 (.var ela1.fst) fun elvl =>
            .let_ (Op.mk (.cmp .eq i32 .bool rfl) (.var elvl, .var blvl, ())) fun heql =>
            .jnz (.var heql.fst)
              (.let_ (op64 (.mul i64) (.var p30.snd.fst) (.imm 4)) fun eo2 =>
               .let_ (op64 (.add i64) (.var pTmp) (.var eo2.fst)) fun ea2 =>
               .load i32 (.var ea2.fst) fun elit2 =>
               .let_ (Op.mk (.lshr i32) (.var elit2, .imm 1, ())) fun ev2 =>
               .let_ (Op.mk (.zext 32 64) (.var ev2.fst, ())) fun ev2_64 =>
               .let_ (op64 (.mul i64) (.var ev2_64.fst) (.imm 4)) fun eto1 =>
               .let_ (op64 (.add i64) (.var pTpos) (.var eto1.fst)) fun eta1 =>
               .load i32 (.var eta1.fst) fun etpos =>
               .let_ (Op.mk (.zext 32 64) (.var etpos, ())) fun tp =>
               .group (sig := [[i64]]) (fun _Jmx => .cons (fun mtr =>
                 .let_ (op64 (.add i64) (.var p30.snd.fst) (.imm 1)) fun e1 =>
                 .jump Lend.fst (.var mtr.fst, .var e1.fst, ())) .nil) fun Jm =>
               .let_ (Op.mk (.cmp .ugt i64 .bool rfl) (.var tp.fst, .var p30.fst, ())) fun hgt =>
               .jnz (.var hgt.fst) (.jump Jm.fst (.var tp.fst, ()))
                 (.jump Jm.fst (.var p30.fst, ())))
              (.jump Jp.fst ()))
           (.jump Jp.fst ())) .nil)
         (fun Lend => .jump Lend.fst (.var max_tr0.fst, .var end_b0.fst, ())))
      k) .nil) (fun Lbeg => .jump Lbeg.fst (.imm 1, ()))

theorem m6B_store_work_stk1 {c : FullCfg} {s : FullState} {tmp1 : List (BitVec 32)}
    {mrk1 : List (BitVec 8)} {mclr1 sstk1 wsort1 ws1 : List (BitVec 32)} {mcl1 : Nat}
    {mcf1 ticks1 resSz1 : BitVec 64} {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 64}
    (v : BitVec 32)
    (hi : i.toNat < (Spec.s13BlkState s tmp1 mrk1 mclr1 sstk1 wsort1 ws1 mcl1 mcf1 ticks1
      resSz1).scratch.work_stk1.length)
    (hm : (FullMem c (Spec.s13BlkState s tmp1 mrk1 mclr1 sstk1 wsort1 ws1 mcl1 mcf1 ticks1
      resSz1) ⋆ R) m) :
    storeOk m i32 (c.pWorkStk1 + i * 4) ∧
      (FullMem c (Spec.s13BlkState s tmp1 mrk1 mclr1 sstk1 wsort1 (ws1.set i.toNat v) mcl1 mcf1
        ticks1 resSz1) ⋆ R) (storeMem m i32 (c.pWorkStk1 + i * 4) v) := by
  dsimp only [Spec.s13BlkState] at hi hm ⊢
  exact c0_store_full_work_stk1 v hi hm

theorem m6B_store_res_sz {c : FullCfg} {s : FullState} {tmp1 : List (BitVec 32)}
    {mrk1 : List (BitVec 8)} {mclr1 sstk1 wsort1 ws1 : List (BitVec 32)} {mcl1 : Nat}
    {mcf1 ticks1 resSz1 : BitVec 64} {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 64)
    (hm : (FullMem c (Spec.s13BlkState s tmp1 mrk1 mclr1 sstk1 wsort1 ws1 mcl1 mcf1 ticks1
      resSz1) ⋆ R) m) :
    storeOk m i64 (c.hdr + 1144) ∧
      (FullMem c (Spec.s13BlkState s tmp1 mrk1 mclr1 sstk1 wsort1 ws1 mcl1 mcf1 ticks1 v) ⋆ R)
        (storeMem m i64 (c.hdr + 1144) v) := by
  dsimp only [Spec.s13BlkState] at hm ⊢
  exact store_full_res_sz v hm

theorem m6B_store_tmp {c : FullCfg} {s : FullState} {tmp1 : List (BitVec 32)}
    {mrk1 : List (BitVec 8)} {mclr1 sstk1 wsort1 ws1 : List (BitVec 32)} {mcl1 : Nat}
    {mcf1 ticks1 resSz1 : BitVec 64} {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 64}
    (v : BitVec 32)
    (hi : i.toNat < (Spec.s13BlkState s tmp1 mrk1 mclr1 sstk1 wsort1 ws1 mcl1 mcf1 ticks1
      resSz1).core.tmp.length)
    (hm : (FullMem c (Spec.s13BlkState s tmp1 mrk1 mclr1 sstk1 wsort1 ws1 mcl1 mcf1 ticks1
      resSz1) ⋆ R) m) :
    storeOk m i32 (c.pTmp + i * 4) ∧
      (FullMem c (Spec.s13BlkState s (tmp1.set i.toNat v) mrk1 mclr1 sstk1 wsort1 ws1 mcl1 mcf1
        ticks1 resSz1) ⋆ R) (storeMem m i32 (c.pTmp + i * 4) v) := by
  dsimp only [Spec.s13BlkState] at hi hm ⊢
  exact c0_store_full_tmp v hi hm

theorem m6B_store_mrk {c : FullCfg} {s : FullState} {tmp1 : List (BitVec 32)}
    {mrk1 : List (BitVec 8)} {mclr1 sstk1 wsort1 ws1 : List (BitVec 32)} {mcl1 : Nat}
    {mcf1 ticks1 resSz1 : BitVec 64} {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 64}
    (v : BitVec 8)
    (hi : i.toNat < (Spec.s13BlkState s tmp1 mrk1 mclr1 sstk1 wsort1 ws1 mcl1 mcf1 ticks1
      resSz1).core.mrk.length)
    (hm : (FullMem c (Spec.s13BlkState s tmp1 mrk1 mclr1 sstk1 wsort1 ws1 mcl1 mcf1 ticks1
      resSz1) ⋆ R) m) :
    storeOk m i8 (c.pMark + i) ∧
      (FullMem c (Spec.s13BlkState s tmp1 (mrk1.set i.toNat v) mclr1 sstk1 wsort1 ws1 mcl1 mcf1
        ticks1 resSz1) ⋆ R) (storeMem m i8 (c.pMark + i) v) := by
  dsimp only [Spec.s13BlkState] at hi hm ⊢
  exact c0_store_full_mrk v hi hm

/-! ## 2. Initial Mark Loop, Push Helper & Fallback DFS Loop WPs -/

theorem m6_mark_loop_wp {Γ : Env} {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    {tmp_s : List (BitVec 32)} {orig_tlen : Nat} {ot_bv : BitVec 64}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post []} {X : XPost}
    {k : Expr Val Cont []}
    (hMm : Γ.Has "full_min_mark" Spec.fullMinMarkSpec)
    (hcore : FullOtfsCoreInv c F0 s) (htmp_len : tmp_s.length = c.max_vars)
    (hot_bv : ot_bv.toNat = orig_tlen) (hot_le : orig_tlen ≤ s.core.cur_vars)
    (hlits : ∀ k < orig_tlen,
      (tmp_s[k]?.getD 0#32).toNat < 2 * s.core.cur_vars ∧
      s.core.vals[(tmp_s[k]?.getD 0#32).toNat]?.getD 0#8 = 0xFF#8)
    (hm_arr : s.core.mrk.length = c.max_vars) (hclr_arr : s.core.min_clr.length = c.max_vars)
    (hsstk_arr : s.scratch.shrink_stk.length = c.max_vars)
    (hws_arr : s.scratch.wsort.length = 2 * c.max_vars)
    (hws1_arr : s.scratch.work_stk1.length = 2 * c.max_vars)
    (hno8 : ∀ w < s.core.cur_vars, (s.core.mrk[w]?.getD 0#8 &&& 8#8) = 0#8)
    (hmin0 : FullMinMarkInv
      (Spec.s13BlkState s tmp_s s.core.mrk s.core.min_clr s.scratch.shrink_stk s.scratch.wsort
        s.scratch.work_stk1 0 0#64 s.scratch.search_ticks s.scratch.res_sz).core [])
    (hm : (FullMem c (Spec.s13BlkState s tmp_s s.core.mrk s.core.min_clr s.scratch.shrink_stk
      s.scratch.wsort s.scratch.work_stk1 0 0#64 s.scratch.search_ticks s.scratch.res_sz) ⋆ R) m)
    (hk : ∀ (mrk1 : List (BitVec 8)) (mclr1 : List (BitVec 32)) (mcl1 : Nat) (mcf1 : BitVec 64)
        m1,
      mrk1.length = c.max_vars → mclr1.length = c.max_vars → mcl1 ≤ c.max_vars →
      FullMinMarkInv
        (Spec.s13BlkState s tmp_s mrk1 mclr1 s.scratch.shrink_stk s.scratch.wsort
          s.scratch.work_stk1 mcl1 mcf1 s.scratch.search_ticks s.scratch.res_sz).core
        ((tmp_s.take orig_tlen).map BitVec.toNat) →
      (∀ w < s.core.cur_vars, (mrk1[w]?.getD 0#8 &&& 8#8) = 0#8) →
      (∀ w, s.core.cur_vars ≤ w → mrk1[w]? = s.core.mrk[w]?) →
      (∀ j < orig_tlen, (mrk1[(tmp_s[j]?.getD 0#32).toNat / 2]?.getD 0#8 &&& 2#8) ≠ 0#8) →
      (FullMem c (Spec.s13BlkState s tmp_s mrk1 mclr1 s.scratch.shrink_stk s.scratch.wsort
        s.scratch.work_stk1 mcl1 mcf1 s.scratch.search_ticks s.scratch.res_sz) ⋆ R) m1 →
      wp Γ Q X k m1) :
    wp Γ Q X (m6MarkLoopExpr c.hdr c.pTmp ot_bv k) m := by
  have hcv := hcore.1.core_ok.cur_vars_le
  have hmx := c.hmaxv; unfold Ref.dimacsBound at hmx
  dsimp only [m6MarkLoopExpr]
  refine wp_loop_group (ts := [i64]) (fun n (i_bv, ()) m_i =>
      n = orig_tlen - i_bv.toNat ∧ i_bv.toNat ≤ orig_tlen ∧
      ∃ mrk_i mclr_i mcl_i mcf_i,
        mrk_i.length = c.max_vars ∧ mclr_i.length = c.max_vars ∧ mcl_i ≤ c.max_vars ∧
        FullMinMarkInv (Spec.s13BlkState s tmp_s mrk_i mclr_i s.scratch.shrink_stk s.scratch.wsort
          s.scratch.work_stk1 mcl_i mcf_i s.scratch.search_ticks s.scratch.res_sz).core
          ((tmp_s.take i_bv.toNat).map BitVec.toNat) ∧
        (∀ w < s.core.cur_vars, (mrk_i[w]?.getD 0#8 &&& 8#8) = 0#8) ∧
        (∀ w, s.core.cur_vars ≤ w → mrk_i[w]? = s.core.mrk[w]?) ∧
        (∀ j < i_bv.toNat, (mrk_i[(tmp_s[j]?.getD 0#32).toNat / 2]?.getD 0#8 &&& 2#8) ≠ 0#8) ∧
        (FullMem c (Spec.s13BlkState s tmp_s mrk_i mclr_i s.scratch.shrink_stk s.scratch.wsort
          s.scratch.work_stk1 mcl_i mcf_i s.scratch.search_ticks s.scratch.res_sz) ⋆ R) m_i)
    ?_ ?_
  · rintro L n_i ⟨i_bv, ⟨⟩⟩ m_i hL ⟨rfl, hi_le, mrk_i, mclr_i, mcl_i, mcf_i, hmrk_i, hmclr_i,
        hmcl_i, hmin_i, hno8_i, hab_i, hdone_i, hm_i⟩
    rw [Blocks.get_here]; ml_lets; ml_jnz; refine ⟨fun hlt => ?_, fun hge => ?_⟩
    · have hi_lt : i_bv.toNat < orig_tlen := by c0_cond hlt; rw [hot_bv] at hlt; exact hlt
      have hi_arr : i_bv.toNat < (Spec.s13BlkState s tmp_s mrk_i mclr_i s.scratch.shrink_stk
          s.scratch.wsort s.scratch.work_stk1 mcl_i mcf_i s.scratch.search_ticks
          s.scratch.res_sz).core.tmp.length := by
        dsimp only [Spec.s13BlkState]; rw [htmp_len]; omega
      ml_ld c0_load_full_tmp (s := Spec.s13BlkState s tmp_s mrk_i mclr_i s.scratch.shrink_stk
        s.scratch.wsort s.scratch.work_stk1 mcl_i mcf_i s.scratch.search_ticks s.scratch.res_sz)
        (i := i_bv) hi_arr hm_i
      have hi_arr' : i_bv.toNat < tmp_s.length := hi_arr
      have hl_lt := (hlits i_bv.toNat hi_lt).1
      have hv_lt : (tmp_s[i_bv.toNat]'hi_arr' >>> 1).toNat < s.core.cur_vars := by
        rw [bv32_lshr_1, List.getElem?_eq_getElem hi_arr', Option.getD_some] at *; omega
      let st := Spec.s13BlkState s tmp_s mrk_i mclr_i s.scratch.shrink_stk s.scratch.wsort
        s.scratch.work_stk1 mcl_i mcf_i s.scratch.search_ticks s.scratch.res_sz
      have hsc_st : st.LengthsOk c :=
        (m6CoreInv_blk hcore htmp_len hmrk_i hmclr_i hmcl_i hsstk_arr hws_arr hws1_arr).1
      ml_lets; apply wp_call_of_spec; apply hMm
      refine fullMinMarkSpec_step hsc_st hm_i (tmp_s[i_bv.toNat]'hi_arr' >>> 1) hv_lt 2#8
        fun m_1 hm_1 => ?_
      obtain ⟨hlen', hmin', hno8', hab', hdone'⟩ := m6_mark_step hcore htmp_len hot_le hi_lt hlits
        hmrk_i hmclr_i hmcl_i hsstk_arr hws_arr hws1_arr hmin_i hno8_i hab_i hdone_i
      have hst_eq := m6Blk_mark_step (s := s) (tmp1 := tmp_s) (mrk1 := mrk_i) (mclr1 := mclr_i)
        (sstk1 := s.scratch.shrink_stk) (wsort1 := s.scratch.wsort) (ws1 := s.scratch.work_stk1)
        (mcl1 := mcl_i) (mcf1 := mcf_i) (ticks1 := s.scratch.search_ticks)
        (resSz1 := s.scratch.res_sz) (tmp_s[i_bv.toNat]'hi_arr' >>> 1).toNat 2#8
      let st' := fullMinMarkStepState st (tmp_s[i_bv.toNat]'hi_arr' >>> 1).toNat 2#8
      have hst_rev : Spec.s13BlkState s tmp_s st'.core.mrk st'.core.min_clr s.scratch.shrink_stk
          s.scratch.wsort s.scratch.work_stk1 st'.core.min_clr_len st'.core.min_clr_full
          s.scratch.search_ticks s.scratch.res_sz = st' := hst_eq.symm
      have hi1 : (i_bv + 1).toNat = i_bv.toNat + 1 := m7_bv64_add1 (by omega)
      ml_lets; exact hL (orig_tlen - (i_bv.toNat + 1)) (i_bv + 1, ()) m_1 (by omega)
        ⟨by rw [hi1], by rw [hi1]; omega, st'.core.mrk, st'.core.min_clr, st'.core.min_clr_len,
          st'.core.min_clr_full, hlen'.core_ok.mrk_len, hlen'.core_ok.min_clr_len_arr,
          hlen'.core_ok.min_clr_len_le,
          by rw [hst_rev, hi1]; exact hmin', hno8', hab',
          by rw [hi1]; exact hdone', by rw [hst_rev]; exact hm_1⟩
    · have hi_eq : i_bv.toNat = orig_tlen := by c0_cond hge; rw [hot_bv] at hge; omega
      rw [hi_eq] at hmin_i hdone_i
      exact hk mrk_i mclr_i mcl_i mcf_i m_i hmrk_i hmclr_i hmcl_i hmin_i hno8_i hab_i hdone_i hm_i
  · intro L hL; ml_lets
    exact hL orig_tlen (0#64, ()) m ⟨rfl, Nat.zero_le _, s.core.mrk, s.core.min_clr, 0, 0#64,
      hm_arr, hclr_arr, Nat.zero_le _, by simpa using hmin0, hno8, fun _ _ => rfl,
      fun _ hj => by simp at hj, hm⟩

theorem m6_ana_push_wp {Γ : Env} {c : FullCfg} {s : FullState}
    {orig_tlen : Nat} {beg_bv cv_bv : BitVec 64} {tmp1 : List (BitVec 32)}
    {mrk1 : List (BitVec 8)} {mclr1 sstk1 wsort1 ws1 : List (BitVec 32)} {mcl1 : Nat}
    {mcf1 ticks1 resSz1 : BitVec 64} {R : Mem 64 → Prop} {m : Mem 64}
    {Q : Post []} {X : XPost} {Jout : Cont []}
    (hcv_bv : cv_bv.toNat = s.core.cur_vars) (hcv : s.core.cur_vars ≤ c.max_vars)
    (htmp_len : tmp1.length = c.max_vars) (hws1_len : ws1.length = 2 * c.max_vars)
    (hbeg_lt : beg_bv.toNat < orig_tlen) (hot_le : orig_tlen ≤ s.core.cur_vars)
    (hm : (FullMem c (Spec.s13BlkState s tmp1 mrk1 mclr1 sstk1 wsort1 ws1 mcl1 mcf1 ticks1
      resSz1) ⋆ R) m)
    (hJ : ∀ (ws' : List (BitVec 32)) (resSz' : BitVec 64) m',
      ws'.length = 2 * c.max_vars →
      (FullMem c (Spec.s13BlkState s tmp1 mrk1 mclr1 sstk1 wsort1 ws' mcl1 mcf1 ticks1 resSz') ⋆
        R) m' →
      wp Γ Q X (.jump Jout ()) m') :
    wp Γ Q X (m6AnaPushExpr c.hdr c.pTmp cv_bv beg_bv Jout) m := by
  have hmx := c.hmaxv; unfold Ref.dimacsBound at hmx
  let st := Spec.s13BlkState s tmp1 mrk1 mclr1 sstk1 wsort1 ws1 mcl1 mcf1 ticks1 resSz1
  have hbeg_arr : beg_bv.toNat < st.core.tmp.length := by
    dsimp only [st, Spec.s13BlkState]; rw [htmp_len]; omega
  dsimp only [m6AnaPushExpr]
  ml_ld load_full_work_stk1_ptr (s := st) hm
  ml_ld c0_load_full_tmp (s := st) (i := beg_bv) hbeg_arr hm
  ml_lets
  refine wp_join_group (ts := []) (fun () m_j => ∃ ws' resSz',
    ws'.length = 2 * c.max_vars ∧
    (FullMem c (Spec.s13BlkState s tmp1 mrk1 mclr1 sstk1 wsort1 ws' mcl1 mcf1 ticks1 resSz') ⋆
      R) m_j) ?_ ?_
  · rintro _ ⟨⟩ m_j ⟨ws', resSz', hwl, hm_j⟩; rw [Blocks.get_here]
    exact hJ ws' resSz' m_j hwl hm_j
  · intro Js hJs
    ml_lets; ml_jnz; refine ⟨fun _ => ?_, fun _ => ?_⟩
    · ml_ld load_full_res_sz (s := st) hm
      ml_lets; ml_jnz; refine ⟨fun hlt_rs => ?_, fun _ => ?_⟩
      · have hrs_cv : resSz1.toNat < s.core.cur_vars := by
          c0_cond hlt_rs; rw [hcv_bv] at hlt_rs; exact hlt_rs
        have hrs_arr : resSz1.toNat < st.scratch.work_stk1.length := by
          dsimp only [st, Spec.s13BlkState]; rw [hws1_len]; omega
        ml_ld load_full_res_sz (s := st) hm
        ml_lets
        ml_st m1, hm1 := m6B_store_work_stk1 (s := s) (tmp1 := tmp1) (mrk1 := mrk1)
          (mclr1 := mclr1) (sstk1 := sstk1) (wsort1 := wsort1) (ws1 := ws1) (mcl1 := mcl1)
          (mcf1 := mcf1) (ticks1 := ticks1) (resSz1 := resSz1)
          (tmp1[beg_bv.toNat]'hbeg_arr >>> 1) hrs_arr hm
        let ws' := ws1.set resSz1.toNat (tmp1[beg_bv.toNat]'hbeg_arr >>> 1)
        ml_ld load_full_res_sz (s := Spec.s13BlkState s tmp1 mrk1 mclr1 sstk1 wsort1 ws' mcl1 mcf1
          ticks1 resSz1) hm1
        ml_lets
        ml_st m2, hm2 := m6B_store_res_sz (s := s) (tmp1 := tmp1) (mrk1 := mrk1) (mclr1 := mclr1)
          (sstk1 := sstk1) (wsort1 := wsort1) (ws1 := ws') (mcl1 := mcl1) (mcf1 := mcf1)
          (ticks1 := ticks1) (resSz1 := resSz1) (resSz1 + 1) hm1
        exact hJs () m2 ⟨ws', resSz1 + 1, by simp [ws', hws1_len], hm2⟩
      · exact hJs () m ⟨ws1, resSz1, hws1_len, hm⟩
    · exact hJs () m ⟨ws1, resSz1, hws1_len, hm⟩

theorem m6_mk2_loop_wp {Γ : Env} {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {orig_tlen : Nat} {beg_bv end_bv : BitVec 64} {blvl : BitVec 32}
    {tmp_s tmp1 : List (BitVec 32)} {mrk0 mrk1 : List (BitVec 8)}
    {mclr1 sstk1 wsort1 ws1 : List (BitVec 32)} {mcl1 : Nat}
    {mcf1 ticks1 resSz1 : BitVec 64} {R : Mem 64 → Prop} {m : Mem 64}
    {Q : Post []} {X : XPost} {Jout : Cont []}
    (hDfs : Γ.Has "full_min_lit_dfs_m8" Spec.fullMinLitDfsSpec)
    (hcv : s.core.cur_vars ≤ c.max_vars) (hot_le : orig_tlen ≤ s.core.cur_vars)
    (hcore : FullOtfsCoreInv c F0 s) (hw : FullOtfsWitnessInv c F0 F_cur s.core)
    (hs_nosent : ∀ k < orig_tlen, tmp_s[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32)
    (hblk_lvl : ∀ j, beg_bv.toNat ≤ j → j < end_bv.toNat →
      (s.core.lvl[(tmp_s[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = blvl.toNat)
    (hinv : M6DfsLoopInv c F0 F_cur s orig_tlen blvl tmp_s mrk0 beg_bv.toNat end_bv.toNat
      beg_bv.toNat tmp1 mrk1 mclr1 sstk1 wsort1 ws1 mcl1 mcf1 ticks1 resSz1)
    (hm : (FullMem c (Spec.s13BlkState s tmp1 mrk1 mclr1 sstk1 wsort1 ws1 mcl1 mcf1 ticks1
      resSz1) ⋆ R) m)
    (hJ : ∀ (tmp' : List (BitVec 32)) (mrk' : List (BitVec 8)) (mclr' wsort' : List (BitVec 32))
        (mcl' : Nat) (mcf' ticks' : BitVec 64) m',
      M6DfsLoopInv c F0 F_cur s orig_tlen blvl tmp_s mrk0 beg_bv.toNat end_bv.toNat end_bv.toNat
        tmp' mrk' mclr' sstk1 wsort' ws1 mcl' mcf' ticks' resSz1 →
      (FullMem c (Spec.s13BlkState s tmp' mrk' mclr' sstk1 wsort' ws1 mcl' mcf' ticks' resSz1) ⋆
        R) m' →
      wp Γ Q X (.jump Jout ()) m') :
    wp Γ Q X (m6Mk2LoopExpr c.hdr c.pTmp beg_bv end_bv Jout) m := by
  have hmx := c.hmaxv; unfold Ref.dimacsBound at hmx
  dsimp only [m6Mk2LoopExpr]
  refine wp_loop_group (ts := [i64]) (fun n (mk2_bv, ()) m_i =>
      n = end_bv.toNat - mk2_bv.toNat ∧ beg_bv.toNat ≤ mk2_bv.toNat ∧
      mk2_bv.toNat ≤ end_bv.toNat ∧
      ∃ tmp_i mrk_i mclr_i wsort_i mcl_i mcf_i ticks_i,
        M6DfsLoopInv c F0 F_cur s orig_tlen blvl tmp_s mrk0 beg_bv.toNat end_bv.toNat
          mk2_bv.toNat tmp_i mrk_i mclr_i sstk1 wsort_i ws1 mcl_i mcf_i ticks_i resSz1 ∧
        (FullMem c (Spec.s13BlkState s tmp_i mrk_i mclr_i sstk1 wsort_i ws1 mcl_i mcf_i ticks_i
          resSz1) ⋆ R) m_i) ?_ ?_
  · rintro Lm n_i ⟨mk2_bv, ⟨⟩⟩ m_i hLm ⟨rfl, hbm, hme, tmp_i, mrk_i, mclr_i, wsort_i, mcl_i,
        mcf_i, ticks_i, hinv_i, hm_i⟩
    rw [Blocks.get_here]; ml_lets; ml_jnz; refine ⟨fun hlt => ?_, fun hge => ?_⟩
    · have hmk_lt : mk2_bv.toNat < end_bv.toNat := by c0_cond hlt; exact hlt
      have hel := hinv_i.end_le
      have hbg1 := hinv_i.beg_ge1
      refine wp_join_group (ts := []) (fun () m_n =>
          ∃ tmp' mrk' mclr' wsort' mcl' mcf' ticks',
            M6DfsLoopInv c F0 F_cur s orig_tlen blvl tmp_s mrk0 beg_bv.toNat end_bv.toNat
              (mk2_bv.toNat + 1) tmp' mrk' mclr' sstk1 wsort' ws1 mcl' mcf' ticks' resSz1 ∧
            (FullMem c (Spec.s13BlkState s tmp' mrk' mclr' sstk1 wsort' ws1 mcl' mcf' ticks'
              resSz1) ⋆ R) m_n) ?_ ?_
      · rintro _ ⟨⟩ m_n ⟨tmp', mrk', mclr', wsort', mcl', mcf', ticks', hinv', hm'⟩
        rw [Blocks.get_here]
        have hmk1 : (mk2_bv + 1).toNat = mk2_bv.toNat + 1 := m7_bv64_add1 (by omega)
        ml_lets; exact hLm (end_bv.toNat - (mk2_bv.toNat + 1)) (mk2_bv + 1, ()) m_n
          (by omega) ⟨by rw [hmk1], by rw [hmk1]; omega, by rw [hmk1]; omega, tmp', mrk', mclr',
            wsort', mcl', mcf', ticks', by rw [hmk1]; exact hinv', hm'⟩
      · intro Jn hJn
        let st_i := Spec.s13BlkState s tmp_i mrk_i mclr_i sstk1 wsort_i ws1 mcl_i mcf_i ticks_i
          resSz1
        have hmk_arr : mk2_bv.toNat < st_i.core.tmp.length := by
          dsimp only [st_i, Spec.s13BlkState]; rw [hinv_i.tmp_len]; omega
        ml_ld c0_load_full_tmp (s := st_i) (i := mk2_bv) hmk_arr hm_i
        have hcore_i : FullOtfsCoreInv c F0 st_i := m6CoreInv_blk hcore hinv_i.tmp_len
          hinv_i.mrk_len hinv_i.mclr_len hinv_i.mcl_le hinv_i.sstk_len hinv_i.wsort_len
          hinv_i.ws1_len
        have hmk_arr' : mk2_bv.toNat < tmp_i.length := hmk_arr
        have hmk_eq_s : tmp_i[mk2_bv.toNat]? = tmp_s[mk2_bv.toNat]? :=
          hinv_i.tail_eq mk2_bv.toNat (le_refl _) (by omega)
        have hmk_ne : tmp_i[mk2_bv.toNat]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 := by
          rw [hmk_eq_s]; exact hs_nosent mk2_bv.toNat (by omega)
        obtain ⟨hl2v, hval_eq, _⟩ := hinv_i.kept_lits mk2_bv.toNat (by omega) hmk_ne
        have hlvl_bd := hinv_i.kept_lvls mk2_bv.toNat (by omega) (by omega) hmk_ne
        have hget : tmp_i[mk2_bv.toNat]?.getD 0#32 = tmp_i[mk2_bv.toNat]'hmk_arr' := by
          rw [List.getElem?_eq_getElem hmk_arr', Option.getD_some]
        rw [hget] at hl2v hval_eq hlvl_bd
        ml_lets; apply wp_call_of_spec; apply hDfs
        refine Spec.fullMinLitDfsSpec_of hcore_i hinv_i.min_inv hl2v hval_eq hlvl_bd.2
          (fun v hv _ => hinv_i.no8 v hv) hm_i ?_
        intro ok_d mrk_d wsort_d mclr_d mcl_d mcf_d ticks_d m_d st_d hlen_d hab_d hmono_d
          hbit8_d hmin_d hok_d hm_d
        dsimp only [st_d, Spec.m8MinLitDfsState, st_i, Spec.s13BlkState] at hlen_d hab_d
        dsimp only [st_d, Spec.m8MinLitDfsState, st_i, Spec.s13BlkState] at hmono_d hbit8_d
        dsimp only [st_d, Spec.m8MinLitDfsState, st_i, Spec.s13BlkState] at hmin_d hok_d hm_d
        ml_jnz; refine ⟨fun hok_t => ?_, fun _ => ?_⟩
        · have hok_true : ok_d = true := by cases ok_d with | true => rfl | false => cases hok_t
          have hmk_arr_d : mk2_bv.toNat < (Spec.s13BlkState s tmp_i mrk_d mclr_d sstk1 wsort_d
              ws1 mcl_d mcf_d ticks_d resSz1).core.tmp.length := by
            dsimp only [Spec.s13BlkState]; exact hmk_arr
          ml_st m_s, hm_s := m6B_store_tmp (s := s) (tmp1 := tmp_i) (mrk1 := mrk_d)
            (mclr1 := mclr_d) (sstk1 := sstk1) (wsort1 := wsort_d) (ws1 := ws1) (mcl1 := mcl_d)
            (mcf1 := mcf_d) (ticks1 := ticks_d) (resSz1 := resSz1) 0xFFFFFFFF#32 hmk_arr_d hm_d
          have hroot_min : ∀ keep',
              (∀ l ∈ (((tmp_i.take orig_tlen).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat),
                l = (tmp_i[mk2_bv.toNat]?.getD 0#32).toNat ∨ l ∈ keep') →
              FullMinMarkInv
                (Spec.s13BlkState s tmp_i mrk_d mclr_d sstk1 wsort_d ws1 mcl_d mcf_d ticks_d
                  resSz1).core keep' := by
            intro keep' hsub
            refine (hok_d hok_true).1 keep' fun l hl => ?_
            rcases hsub l hl with rfl | hmem
            · left; rw [hget]; rfl
            · exact Or.inr hmem
          exact hJn () m_s ⟨tmp_i.set mk2_bv.toNat 0xFFFFFFFF#32, mrk_d, mclr_d, wsort_d, mcl_d,
            mcf_d, ticks_d, m6Dfs_step_true hcv hot_le hw hinv_i hmk_lt hlen_d.core_ok.mrk_len
            hlen_d.core_ok.min_clr_len_arr hlen_d.core_ok.min_clr_len_le
            hlen_d.scratch_ok.wsort_len hmono_d hbit8_d hab_d hroot_min, hm_s⟩
        · exact hJn () m_d ⟨tmp_i, mrk_d, mclr_d, wsort_d, mcl_d, mcf_d, ticks_d,
            m6Dfs_step_false hinv_i hmk_lt hblk_lvl hlen_d.core_ok.mrk_len
              hlen_d.core_ok.min_clr_len_arr hlen_d.core_ok.min_clr_len_le
              hlen_d.scratch_ok.wsort_len hmono_d hbit8_d hab_d hmin_d, hm_d⟩
    · have hmeq : mk2_bv.toNat = end_bv.toNat := by c0_cond hge; omega
      rw [hmeq] at hinv_i
      exact hJ tmp_i mrk_i mclr_i wsort_i mcl_i mcf_i ticks_i m_i hinv_i hm_i
  · intro Lm hLm; ml_lets
    exact hLm (end_bv.toNat - beg_bv.toNat) (beg_bv, ()) m ⟨rfl, le_refl _, hinv.mk_end,
      tmp1, mrk1, mclr1, wsort1, mcl1, mcf1, ticks1, hinv, hm⟩

/-! ## 3. Main Level-Block Grouping & Shrinking Loop WP -/

theorem m6_shrink_loop_wp {Γ : Env} {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {orig_tlen : Nat} {cv_bv ot_bv : BitVec 64}
    {tmp_s : List (BitVec 32)} {mrk1 : List (BitVec 8)} {mclr1 : List (BitVec 32)}
    {mcl1 : Nat} {mcf1 : BitVec 64} {R : Mem 64 → Prop} {m : Mem 64}
    {Q : Post []} {X : XPost} {k : Expr Val Cont []}
    (hSB : Γ.Has "full_shrink_blk_bool_m8" Spec.fullShrinkBlkBoolSpec)
    (hDfs : Γ.Has "full_min_lit_dfs_m8" Spec.fullMinLitDfsSpec)
    (hcore : FullOtfsCoreInv c F0 s) (hw : FullOtfsWitnessInv c F0 F_cur s.core)
    (hcv_bv : cv_bv.toNat = s.core.cur_vars) (hot_bv : ot_bv.toNat = orig_tlen)
    (hot_pos : 1 ≤ orig_tlen) (hot_le : orig_tlen ≤ s.core.cur_vars)
    (hs0_lvl : (s.core.lvl[(tmp_s[0]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = s.core.cur_level)
    (hs_lits : ∀ k < orig_tlen,
      (tmp_s[k]?.getD 0#32).toNat < 2 * s.core.cur_vars ∧
      s.core.vals[(tmp_s[k]?.getD 0#32).toNat]?.getD 0#8 = 0xFF#8 ∧
      tmp_s[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32)
    (hs_lvls : ∀ k, 1 ≤ k → k < orig_tlen →
      0 < (s.core.lvl[(tmp_s[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ∧
      (s.core.lvl[(tmp_s[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat < s.core.cur_level)
    (hs_sorted : ∀ i j, 1 ≤ i → i ≤ j → j < orig_tlen →
      (s.core.lvl[(tmp_s[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
      (s.core.lvl[(tmp_s[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat)
    (hinv1 : M6ShrinkLoopInv c F0 F_cur s orig_tlen tmp_s s.core.mrk 1 tmp_s mrk1 mclr1
      s.scratch.shrink_stk s.scratch.wsort s.scratch.work_stk1 mcl1 mcf1 s.scratch.search_ticks
      s.scratch.res_sz)
    (hm : (FullMem c (Spec.s13BlkState s tmp_s mrk1 mclr1 s.scratch.shrink_stk s.scratch.wsort
      s.scratch.work_stk1 mcl1 mcf1 s.scratch.search_ticks s.scratch.res_sz) ⋆ R) m)
    (hk : ∀ (tmp_f : List (BitVec 32)) (mrk_f : List (BitVec 8))
        (mclr_f sstk_f wsort_f ws_f : List (BitVec 32)) (mcl_f : Nat)
        (mcf_f ticks_f resSz_f : BitVec 64) m_f,
      M6ShrinkLoopInv c F0 F_cur s orig_tlen tmp_s s.core.mrk orig_tlen tmp_f mrk_f mclr_f sstk_f
        wsort_f ws_f mcl_f mcf_f ticks_f resSz_f →
      (FullMem c (Spec.s13BlkState s tmp_f mrk_f mclr_f sstk_f wsort_f ws_f mcl_f mcf_f ticks_f
        resSz_f) ⋆ R) m_f →
      wp Γ Q X k m_f) :
    wp Γ Q X (m6ShrinkLoopExpr c.hdr c.pTmp c.pLevel c.pTrailPos cv_bv ot_bv k) m := by
  have hlen0 := hcore.1.core_ok; have hcv := hlen0.cur_vars_le
  have hmx := c.hmaxv; unfold Ref.dimacsBound at hmx
  have hs_nosent : ∀ k < orig_tlen, tmp_s[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 := fun k hk =>
    (hs_lits k hk).2.2
  dsimp only [m6ShrinkLoopExpr]
  refine wp_loop_group (ts := [i64]) (fun n (beg_bv, ()) m_b =>
      n = orig_tlen - beg_bv.toNat ∧ 1 ≤ beg_bv.toNat ∧ beg_bv.toNat ≤ orig_tlen ∧
      ∃ tmp_b mrk_b mclr_b sstk_b wsort_b ws_b mcl_b mcf_b ticks_b resSz_b,
        M6ShrinkLoopInv c F0 F_cur s orig_tlen tmp_s s.core.mrk beg_bv.toNat tmp_b mrk_b mclr_b
          sstk_b wsort_b ws_b mcl_b mcf_b ticks_b resSz_b ∧
        (FullMem c (Spec.s13BlkState s tmp_b mrk_b mclr_b sstk_b wsort_b ws_b mcl_b mcf_b ticks_b
          resSz_b) ⋆ R) m_b) ?_ ?_
  · rintro Lbeg n_b ⟨beg_bv, ⟨⟩⟩ m_b hLbeg ⟨rfl, hb_ge1, hb_le, tmp_b, mrk_b, mclr_b, sstk_b,
        wsort_b, ws_b, mcl_b, mcf_b, ticks_b, resSz_b, hinv_b, hm_b⟩
    rw [Blocks.get_here]; ml_lets; ml_jnz; refine ⟨fun hlt_b => ?_, fun hge_b => ?_⟩
    · have hbeg_lt : beg_bv.toNat < orig_tlen := by c0_cond hlt_b; rw [hot_bv] at hlt_b; exact hlt_b
      let st_b := Spec.s13BlkState s tmp_b mrk_b mclr_b sstk_b wsort_b ws_b mcl_b mcf_b ticks_b
        resSz_b
      have hbeg_arr : beg_bv.toNat < st_b.core.tmp.length := by
        dsimp only [st_b, Spec.s13BlkState]; rw [hinv_b.tmp_len]; omega
      have hbeg_arr' : beg_bv.toNat < tmp_b.length := hbeg_arr
      have hbeg_eq : tmp_b[beg_bv.toNat]? = tmp_s[beg_bv.toNat]? :=
        hinv_b.tail_eq beg_bv.toNat (le_refl _) hbeg_lt
      have hbeg_v_lt : (tmp_b[beg_bv.toNat]'hbeg_arr' >>> 1).toNat < s.core.cur_vars := by
        have hl := (hs_lits beg_bv.toNat hbeg_lt).1
        rw [bv32_lshr_1, ← Option.getD_some (b := 0#32) (a := tmp_b[beg_bv.toNat]'hbeg_arr'),
          ← List.getElem?_eq_getElem hbeg_arr', hbeg_eq]
        omega
      have hbeg_lvl_len : ((tmp_b[beg_bv.toNat]'hbeg_arr' >>> 1).setWidth 64).toNat <
          st_b.core.lvl.length := by
        dsimp only [st_b, Spec.s13BlkState]; rw [bv_c0_zext32_64, hlen0.lvl_len]; omega
      have hbeg_tp_len : ((tmp_b[beg_bv.toNat]'hbeg_arr' >>> 1).setWidth 64).toNat <
          st_b.core.trail_pos.length := by
        dsimp only [st_b, Spec.s13BlkState]; rw [bv_c0_zext32_64, hlen0.trail_pos_len]; omega
      ml_ld c0_load_full_tmp (s := st_b) (i := beg_bv) hbeg_arr hm_b
      ml_ld c0_load_full_lvl (s := st_b)
        (i := (tmp_b[beg_bv.toNat]'hbeg_arr' >>> 1).setWidth 64) hbeg_lvl_len hm_b
      ml_ld c0_load_full_tmp (s := st_b) (i := beg_bv) hbeg_arr hm_b
      ml_ld c0_load_full_trail_pos (s := st_b)
        (i := (tmp_b[beg_bv.toNat]'hbeg_arr' >>> 1).setWidth 64) hbeg_tp_len hm_b
      let blvl :=
        s.core.lvl[((tmp_b[beg_bv.toNat]'hbeg_arr' >>> 1).setWidth 64).toNat]'hbeg_lvl_len
      let tpos0 :=
        s.core.trail_pos[((tmp_b[beg_bv.toNat]'hbeg_arr' >>> 1).setWidth 64).toNat]'hbeg_tp_len
      have hbeg_idx : (tmp_s[beg_bv.toNat]?.getD 0#32).toNat / 2 =
          ((tmp_b[beg_bv.toNat]'hbeg_arr' >>> 1).setWidth 64).toNat := by
        rw [bv_c0_zext32_64, bv32_lshr_1,
          ← Option.getD_some (b := 0#32) (a := tmp_b[beg_bv.toNat]'hbeg_arr'),
          ← List.getElem?_eq_getElem hbeg_arr', hbeg_eq]
      have hblvl_eq : (s.core.lvl[(tmp_s[beg_bv.toNat]?.getD 0#32).toNat / 2]?.getD 0#32).toNat =
          blvl.toNat := by
        dsimp only [blvl]
        rw [hbeg_idx, List.getElem?_eq_getElem hbeg_lvl_len, Option.getD_some]
      have htpos0_eq :
          (s.core.trail_pos[(tmp_s[beg_bv.toNat]?.getD 0#32).toNat / 2]?.getD 0#32).toNat =
          (tpos0.setWidth 64).toNat := by
        dsimp only [tpos0]
        rw [hbeg_idx, List.getElem?_eq_getElem hbeg_tp_len, Option.getD_some,
          bv_c0_zext32_64 tpos0]
      ml_lets
      refine wp_loop_group (ts := [i64, i64]) (fun n_e (max_tr, end_b, ()) m_e =>
          n_e = orig_tlen - end_b.toNat ∧ m_e = m_b ∧
          beg_bv.toNat < end_b.toNat ∧ end_b.toNat ≤ orig_tlen ∧
          (∀ j, beg_bv.toNat ≤ j → j < end_b.toNat →
            (s.core.lvl[(tmp_s[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = blvl.toNat) ∧
          (∀ j, beg_bv.toNat ≤ j → j < end_b.toNat →
            (s.core.trail_pos[(tmp_s[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ max_tr.toNat))
        ?_ ?_
      · rintro Lend n_e ⟨max_tr, end_b, ⟨⟩⟩ m_e hLend
          ⟨rfl, hm_eq, hbe_lt, he_le, hblk_lvl, hblk_tr⟩
        subst hm_eq
        rw [Blocks.get_here]
        refine wp_join_group (ts := []) (fun () m_p =>
            m_p = m_e ∧ (end_b.toNat < orig_tlen → blvl.toNat <
              (s.core.lvl[(tmp_s[end_b.toNat]?.getD 0#32).toNat / 2]?.getD 0#32).toNat))
          ?_ ?_
        · rintro _ ⟨⟩ m_p ⟨rfl, hend_strict⟩
          rw [Blocks.get_here]
          refine wp_join_group (ts := []) (fun () m_n =>
              ∃ tmp' mrk' mclr' sstk' wsort' ws' mcl' mcf' ticks' resSz',
                M6ShrinkLoopInv c F0 F_cur s orig_tlen tmp_s s.core.mrk end_b.toNat tmp' mrk'
                  mclr' sstk' wsort' ws' mcl' mcf' ticks' resSz' ∧
                (FullMem c (Spec.s13BlkState s tmp' mrk' mclr' sstk' wsort' ws' mcl' mcf' ticks'
                  resSz') ⋆ R) m_n) ?_ ?_
          · rintro _ ⟨⟩ m_n ⟨tmp', mrk', mclr', sstk', wsort', ws', mcl', mcf', ticks', resSz',
                hinv', hm'⟩
            rw [Blocks.get_here]; ml_lets
            exact hLbeg (orig_tlen - end_b.toNat) (end_b, ()) m_n (by omega)
              ⟨rfl, by omega, he_le, tmp', mrk', mclr', sstk', wsort', ws', mcl', mcf', ticks',
                resSz', hinv', hm'⟩
          · intro Jn hJn
            ml_lets; ml_jnz; refine ⟨fun hge2 => ?_, fun _ => ?_⟩
            · have hdiff2 : 2 ≤ end_b.toNat - beg_bv.toNat := by
                have h2 : (2 : BitVec 64).toNat ≤ (end_b - beg_bv).toNat := by
                  simpa only [BitVec.ule, decide_eq_true_eq] using hge2
                change 2 ≤ (end_b - beg_bv).toNat at h2
                rw [m7_bv64_sub (by omega)] at h2; exact h2
              refine wp_join_group (ts := []) (fun () m_j =>
                  ∃ tmp' mrk' mclr' sstk' wsort' ws' mcl' mcf' ticks' resSz',
                    M6ShrinkLoopInv c F0 F_cur s orig_tlen tmp_s s.core.mrk end_b.toNat tmp' mrk'
                      mclr' sstk' wsort' ws' mcl' mcf' ticks' resSz' ∧
                    (FullMem c (Spec.s13BlkState s tmp' mrk' mclr' sstk' wsort' ws' mcl' mcf' ticks'
                      resSz') ⋆ R) m_j) ?_ ?_
              · rintro _ ⟨⟩ m_j ⟨tmp', mrk', mclr', sstk', wsort', ws', mcl', mcf', ticks',
                    resSz', hinv', hm'⟩
                rw [Blocks.get_here]
                exact hJn () m_j ⟨tmp', mrk', mclr', sstk', wsort', ws', mcl', mcf', ticks',
                  resSz', hinv', hm'⟩
              · intro Jb hJb
                have hcore_b : FullOtfsCoreInv c F0 st_b := m6CoreInv_blk hcore hinv_b.tmp_len
                  hinv_b.mrk_len hinv_b.mclr_len hinv_b.mcl_le hinv_b.sstk_len hinv_b.wsort_len
                  hinv_b.ws1_len
                have hbeg_lvl_rng := hs_lvls beg_bv.toNat hb_ge1 hbeg_lt
                rw [hblvl_eq] at hbeg_lvl_rng
                ml_lets; apply wp_call_of_spec; apply hSB
                refine Spec.fullShrinkBlkBoolSpec_of hcore_b hinv_b.min_inv hinv_b.no8 hb_ge1 hbe_lt
                  he_le hot_le hbeg_lvl_rng.1 hbeg_lvl_rng.2 (fun j hj1 hj2 => by
                    dsimp only [Arg.val] at hj1 hj2
                    have heq := hinv_b.tail_eq j (by omega) (by omega)
                    have hls := hs_lits j (by omega)
                    refine ⟨by rw [heq]; exact hls.1, by rw [heq]; exact hls.2.1,
                      by rw [heq]; exact hblk_lvl j hj1 hj2,
                      by rw [heq]; exact hblk_tr j hj1 hj2⟩)
                  hinv_b.kept_lits hm_b ?_
                intro ok_s tmp' mrk' mclr' sstk' wsort' mcl' mcf' ticks' m_s st_s
                  hcore_s hmin_s hab_s hno8_s hm2_s hfalse_s hout_s hin_lvl_s hnodup_s hEnt_s
                  hkept_s hm_s
                dsimp only [st_s, Spec.m8ShrinkBlkBoolState, st_b, Spec.s13BlkState] at hcore_s
                dsimp only [st_s, Spec.m8ShrinkBlkBoolState, st_b, Spec.s13BlkState] at hmin_s
                dsimp only [st_s, Spec.m8ShrinkBlkBoolState, st_b, Spec.s13BlkState] at hab_s
                dsimp only [st_s, Spec.m8ShrinkBlkBoolState, st_b, Spec.s13BlkState] at hno8_s
                dsimp only [st_s, Spec.m8ShrinkBlkBoolState, st_b, Spec.s13BlkState] at hm2_s
                dsimp only [st_s, Spec.m8ShrinkBlkBoolState, st_b, Spec.s13BlkState] at hout_s
                dsimp only [st_s, Spec.m8ShrinkBlkBoolState, st_b, Spec.s13BlkState] at hin_lvl_s
                dsimp only [st_s, Spec.m8ShrinkBlkBoolState, st_b, Spec.s13BlkState] at hnodup_s
                dsimp only [st_s, Spec.m8ShrinkBlkBoolState, st_b, Spec.s13BlkState] at hEnt_s
                dsimp only [st_s, Spec.m8ShrinkBlkBoolState, st_b, Spec.s13BlkState] at hkept_s
                dsimp only [st_s, Spec.m8ShrinkBlkBoolState, st_b, Spec.s13BlkState] at hm_s
                ml_jnz; refine ⟨fun _ => ?_, fun hok_f => ?_⟩
                · refine m6_ana_push_wp hcv_bv hcv hcore_s.1.core_ok.tmp_len_arr
                    hinv_b.ws1_len hbeg_lt hot_le hm_s fun ws' resSz' m_j hwl' hm_j => ?_
                  rw [wp]
                  exact hJb () m_j ⟨tmp', mrk', mclr', sstk', wsort', ws', mcl', mcf', ticks',
                    resSz', m6Shrink_block_step hw hinv_b hbe_lt he_le hs0_lvl hs_nosent hs_lvls
                      hs_sorted hblk_lvl hend_strict hcore_s.1.core_ok.tmp_len_arr
                      hcore_s.1.core_ok.mrk_len hcore_s.1.core_ok.min_clr_len_arr
                      hcore_s.1.core_ok.min_clr_len_le hcore_s.1.scratch_ok.shrink_stk_len
                      hcore_s.1.scratch_ok.wsort_len hwl' hmin_s hab_s hno8_s hout_s hin_lvl_s
                      hnodup_s (fun hw' hent' => hEnt_s F_cur hw' hent') hkept_s, hm_j⟩
                · have hok_false : ok_s = false := by
                    cases ok_s with | false => rfl | true => cases hok_f
                  have htmp_eq : tmp' = tmp_b := hfalse_s hok_false
                  have hinv_b' : M6ShrinkLoopInv c F0 F_cur s orig_tlen tmp_s s.core.mrk
                      beg_bv.toNat tmp' mrk' mclr' sstk' wsort' ws_b mcl' mcf' ticks' resSz_b :=
                    { beg_ge1 := hinv_b.beg_ge1
                      beg_le := hinv_b.beg_le
                      tmp_len := hcore_s.1.core_ok.tmp_len_arr
                      mrk_len := hcore_s.1.core_ok.mrk_len
                      mclr_len := hcore_s.1.core_ok.min_clr_len_arr
                      mcl_le := hcore_s.1.core_ok.min_clr_len_le
                      sstk_len := hcore_s.1.scratch_ok.shrink_stk_len
                      wsort_len := hcore_s.1.scratch_ok.wsort_len
                      ws1_len := hinv_b.ws1_len
                      tmp0_eq := by rw [htmp_eq]; exact hinv_b.tmp0_eq
                      tail_eq := fun j hj1 hj2 => by rw [htmp_eq]; exact hinv_b.tail_eq j hj1 hj2
                      kept_lits := fun k hk hne => hkept_s k hk hne
                      kept_lvls := fun k hk1 hk2 hne => by
                        rw [htmp_eq] at hne ⊢; exact hinv_b.kept_lvls k hk1 hk2 hne
                      kept_sorted := fun i j hi hij hj hni hnj => by
                        rw [htmp_eq] at hni hnj ⊢
                        exact hinv_b.kept_sorted i j hi hij hj hni hnj
                      beg_bd := fun hlt k hk1 hk2 hne => by
                        rw [htmp_eq] at hne ⊢; exact hinv_b.beg_bd hlt k hk1 hk2 hne
                      nodup := by rw [htmp_eq]; exact hinv_b.nodup
                      min_inv := hmin_s
                      ent := by rw [htmp_eq]; exact hinv_b.ent
                      no8 := hno8_s
                      mrk_above := fun w hw => (hab_s w hw).trans (hinv_b.mrk_above w hw) }
                  have hdfs_init := m6Dfs_init hinv_b' hbe_lt he_le hblk_lvl
                  refine m6_mk2_loop_wp hDfs hcv hot_le hcore hw hs_nosent hblk_lvl hdfs_init hm_s
                    fun tmp'' mrk'' mclr'' wsort'' mcl'' mcf'' ticks'' m_d hdfs_d hm_d => ?_
                  rw [wp]
                  exact hJb () m_d ⟨tmp'', mrk'', mclr'', sstk', wsort'', ws_b, mcl'', mcf'',
                    ticks'', resSz_b, m6Dfs_to_loop hdfs_d hend_strict, hm_d⟩
            · exact hJn () m_p ⟨tmp_b, mrk_b, mclr_b, sstk_b, wsort_b, ws_b, mcl_b, mcf_b, ticks_b,
                resSz_b, m6Shrink_block_no_shrink hw hinv_b hbe_lt he_le hs0_lvl hs_nosent hs_lvls
                  hs_sorted hblk_lvl hend_strict, hm_b⟩
        · intro Jp hJp; ml_lets; ml_jnz; refine ⟨fun hlt_e => ?_, fun hge_e => ?_⟩
          · have he_lt : end_b.toNat < orig_tlen := by
              c0_cond hlt_e; rw [hot_bv] at hlt_e; exact hlt_e
            have he_arr : end_b.toNat < st_b.core.tmp.length := by
              dsimp only [st_b, Spec.s13BlkState]; rw [hinv_b.tmp_len]; omega
            have he_arr' : end_b.toNat < tmp_b.length := he_arr
            have he_eq : tmp_b[end_b.toNat]? = tmp_s[end_b.toNat]? :=
              hinv_b.tail_eq end_b.toNat (by omega) he_lt
            have he_v_lt : (tmp_b[end_b.toNat]'he_arr' >>> 1).toNat < s.core.cur_vars := by
              have hl := (hs_lits end_b.toNat he_lt).1
              rw [bv32_lshr_1, ← Option.getD_some (b := 0#32) (a := tmp_b[end_b.toNat]'he_arr'),
                ← List.getElem?_eq_getElem he_arr', he_eq]
              omega
            have he_lvl_len : ((tmp_b[end_b.toNat]'he_arr' >>> 1).setWidth 64).toNat <
                st_b.core.lvl.length := by
              dsimp only [st_b, Spec.s13BlkState]; rw [bv_c0_zext32_64, hlen0.lvl_len]; omega
            ml_ld c0_load_full_tmp (s := st_b) (i := end_b) he_arr hm_b
            ml_ld c0_load_full_lvl (s := st_b)
              (i := (tmp_b[end_b.toNat]'he_arr' >>> 1).setWidth 64) he_lvl_len hm_b
            ml_lets; ml_jnz; refine ⟨fun heq_l => ?_, fun hne_l => ?_⟩
            · have he_idx : (tmp_s[end_b.toNat]?.getD 0#32).toNat / 2 =
                  ((tmp_b[end_b.toNat]'he_arr' >>> 1).setWidth 64).toNat := by
                rw [bv_c0_zext32_64, bv32_lshr_1,
                  ← Option.getD_some (b := 0#32) (a := tmp_b[end_b.toNat]'he_arr'),
                  ← List.getElem?_eq_getElem he_arr', he_eq]
              have hl_eq :
                  (s.core.lvl[(tmp_s[end_b.toNat]?.getD 0#32).toNat / 2]?.getD 0#32).toNat =
                  blvl.toNat := by
                c0_cond heq_l
                rw [he_idx, List.getElem?_eq_getElem he_lvl_len, Option.getD_some]
                exact congrArg BitVec.toNat heq_l
              have he_tp_len : ((tmp_b[end_b.toNat]'he_arr' >>> 1).setWidth 64).toNat <
                  st_b.core.trail_pos.length := by
                dsimp only [st_b, Spec.s13BlkState]
                rw [bv_c0_zext32_64, hlen0.trail_pos_len]; omega
              ml_ld c0_load_full_tmp (s := st_b) (i := end_b) he_arr hm_b
              ml_ld c0_load_full_trail_pos (s := st_b)
                (i := (tmp_b[end_b.toNat]'he_arr' >>> 1).setWidth 64) he_tp_len hm_b
              let tp32 :=
                s.core.trail_pos[((tmp_b[end_b.toNat]'he_arr' >>> 1).setWidth 64).toNat]'he_tp_len
              have htp_eq :
                  (s.core.trail_pos[(tmp_s[end_b.toNat]?.getD 0#32).toNat / 2]?.getD 0#32).toNat =
                  (tp32.setWidth 64).toNat := by
                dsimp only [tp32]
                rw [he_idx, List.getElem?_eq_getElem he_tp_len, Option.getD_some,
                  bv_c0_zext32_64 tp32]
              ml_lets
              refine wp_join_group (ts := [i64]) (fun (mtr, ()) m_m =>
                  m_m = m_e ∧
                  (∀ j, beg_bv.toNat ≤ j → j < end_b.toNat + 1 →
                    (s.core.trail_pos[(tmp_s[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
                    mtr.toNat)) ?_ ?_
              · rintro _ ⟨mtr, ⟨⟩⟩ m_m ⟨rfl, htr'⟩
                rw [Blocks.get_here]
                have he1 : (end_b + 1).toNat = end_b.toNat + 1 := m7_bv64_add1 (by omega)
                ml_lets; exact hLend (orig_tlen - (end_b.toNat + 1)) (mtr, end_b + 1, ()) m_m
                  (by omega) ⟨by rw [he1], rfl, by rw [he1]; omega, by rw [he1]; omega,
                    fun j hj1 hj2 => by
                      by_cases hje : j = end_b.toNat
                      · subst j; exact hl_eq
                      · exact hblk_lvl j hj1 (by omega),
                    by rw [he1]; exact htr'⟩
              · intro Jm hJm; ml_lets; ml_jnz; refine ⟨fun hgt => ?_, fun hle => ?_⟩
                · have htp_gt : max_tr.toNat < (tp32.setWidth 64).toNat := by c0_cond hgt; exact hgt
                  exact hJm (tp32.setWidth 64, ()) m_e ⟨rfl, fun j hj1 hj2 => by
                    by_cases hje : j = end_b.toNat
                    · subst j; rw [htp_eq]; exact le_refl _
                    · have := hblk_tr j hj1 (by omega); omega⟩
                · have htp_le : (tp32.setWidth 64).toNat ≤ max_tr.toNat := by
                    c0_cond hle; exact Nat.not_lt.mp hle
                  exact hJm (max_tr, ()) m_e ⟨rfl, fun j hj1 hj2 => by
                    by_cases hje : j = end_b.toNat
                    · subst j; rw [htp_eq]; exact htp_le
                    · exact hblk_tr j hj1 (by omega)⟩
            · have he_idx : (tmp_s[end_b.toNat]?.getD 0#32).toNat / 2 =
                  ((tmp_b[end_b.toNat]'he_arr' >>> 1).setWidth 64).toNat := by
                rw [bv_c0_zext32_64, bv32_lshr_1,
                  ← Option.getD_some (b := 0#32) (a := tmp_b[end_b.toNat]'he_arr'),
                  ← List.getElem?_eq_getElem he_arr', he_eq]
              have hl_ne :
                  (s.core.lvl[(tmp_s[end_b.toNat]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≠
                  blvl.toNat := by
                c0_cond hne_l
                intro heq; apply hne_l; apply BitVec.eq_of_toNat_eq
                dsimp only [st_b, Spec.s13BlkState, blvl] at heq ⊢
                rw [he_idx, List.getElem?_eq_getElem he_lvl_len, Option.getD_some] at heq
                exact heq
              exact hJp () m_e ⟨rfl, fun _ => by
                have hle_s := hs_sorted beg_bv.toNat end_b.toNat hb_ge1 (by omega) he_lt
                rw [hblvl_eq] at hle_s; omega⟩
          · have he_ge : orig_tlen ≤ end_b.toNat := by
              c0_cond hge_e; rw [hot_bv] at hge_e; exact Nat.not_lt.mp hge_e
            exact hJp () m_e ⟨rfl, fun hlt => absurd hlt (Nat.not_lt.mpr he_ge)⟩
      · intro Lend hLend
        have hb1 : (beg_bv + 1).toNat = beg_bv.toNat + 1 := m7_bv64_add1 (by omega)
        ml_lets; exact hLend (orig_tlen - (beg_bv.toNat + 1)) (tpos0.setWidth 64, beg_bv + 1, ())
          m_b ⟨by rw [hb1], rfl, by rw [hb1]; omega, by rw [hb1]; omega,
            fun j hj1 hj2 => by
              have hjb : j = beg_bv.toNat := by omega
              subst j; exact hblvl_eq,
            fun j hj1 hj2 => by
              have hjb : j = beg_bv.toNat := by omega
              subst j; rw [htpos0_eq]; exact le_refl _⟩
    · have hbeq : beg_bv.toNat = orig_tlen := by c0_cond hge_b; rw [hot_bv] at hge_b; omega
      rw [hbeq] at hinv_b
      exact hk tmp_b mrk_b mclr_b sstk_b wsort_b ws_b mcl_b mcf_b ticks_b resSz_b m_b hinv_b hm_b
  · intro Lbeg hLbeg; ml_lets
    exact hLbeg (orig_tlen - 1) (1#64, ()) m ⟨rfl, le_refl _, hot_pos, tmp_s, mrk1, mclr1,
      s.scratch.shrink_stk, s.scratch.wsort, s.scratch.work_stk1, mcl1, mcf1,
      s.scratch.search_ticks, s.scratch.res_sz, hinv1, hm⟩

end

end LeanQbe.T.Examples.Kissat.Proof.Minimize
