/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Minimize.Spec
public import LeanQbe.T.Examples.Kissat.Src.Minimize
public import LeanQbe.T.Logic.CanonicalEnv
import LeanQbe.T.Examples.Kissat.Proof.Minimize.MinTactics
import LeanQbe.T.Examples.Kissat.Proof.Minimize.WpShrinkBlkHelpers
import LeanQbe.T.Examples.Kissat.Proof.Minimize.WpShrinkBlkLemmas
import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena1
import LeanQbe.T.Logic.C0Grind
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb

/-!
# `full_shrink_blk_bool_m8` WP Proof for `Kissat.Src.Minimize`

Proves `Func.wp Γ full_shrink_blk_bool_m8_body ...` against canonical
`Spec.fullShrinkBlkBoolSpec`, consuming `Γ.Has "full_min_mark" Spec.fullMinMarkSpec` and
`Γ.Has "full_shrink_lower_m8" Spec.fullShrinkLowerSpec`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Minimize

open Std Std.Sat
open LeanQbe.T LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics
open LeanQbe.T.Examples.Kissat.Src.Minimize
open FullMinTactics
open scoped FullArenaTactics FullMinTactics
open Kraken.Bedrock2.Test

private theorem m8SBlk_st_mrk_eq (s : FullState) (tmp1 : List (BitVec 32))
    (mrk1 : List (BitVec 8)) (mclr1 sstk1 wsort1 : List (BitVec 32))
    (mcl1 : Nat) (mcf1 ticks1 : BitVec 64) {i j : Nat} {v : BitVec 8} (h : i = j) :
    { m8SBlkSt s tmp1 mrk1 mclr1 sstk1 wsort1 mcl1 mcf1 ticks1 with
      core := { (m8SBlkSt s tmp1 mrk1 mclr1 sstk1 wsort1 mcl1 mcf1 ticks1).core with
        mrk := (m8SBlkSt s tmp1 mrk1 mclr1 sstk1 wsort1 mcl1 mcf1 ticks1).core.mrk.set i v } } =
      m8SBlkSt s tmp1 (mrk1.set j v) mclr1 sstk1 wsort1 mcl1 mcf1 ticks1 := by
  subst h; rfl

private theorem m8SBlk_st_tmp_eq (s : FullState) (tmp1 : List (BitVec 32))
    (mrk1 : List (BitVec 8)) (mclr1 sstk1 wsort1 : List (BitVec 32))
    (mcl1 : Nat) (mcf1 ticks1 : BitVec 64) {i j : Nat} {v : BitVec 32} (h : i = j) :
    { m8SBlkSt s tmp1 mrk1 mclr1 sstk1 wsort1 mcl1 mcf1 ticks1 with
      core := { (m8SBlkSt s tmp1 mrk1 mclr1 sstk1 wsort1 mcl1 mcf1 ticks1).core with
        tmp := (m8SBlkSt s tmp1 mrk1 mclr1 sstk1 wsort1 mcl1 mcf1 ticks1).core.tmp.set i v } } =
      m8SBlkSt s (tmp1.set j v) mrk1 mclr1 sstk1 wsort1 mcl1 mcf1 ticks1 := by
  subst h; rfl

private theorem m8SBlk_st_sstk_eq (s : FullState) (tmp1 : List (BitVec 32))
    (mrk1 : List (BitVec 8)) (mclr1 sstk1 wsort1 : List (BitVec 32))
    (mcl1 : Nat) (mcf1 ticks1 : BitVec 64) {i j : Nat} {v : BitVec 32} (h : i = j) :
    { m8SBlkSt s tmp1 mrk1 mclr1 sstk1 wsort1 mcl1 mcf1 ticks1 with
      scratch := { (m8SBlkSt s tmp1 mrk1 mclr1 sstk1 wsort1 mcl1 mcf1 ticks1).scratch with
        shrink_stk :=
          (m8SBlkSt s tmp1 mrk1 mclr1 sstk1 wsort1 mcl1 mcf1 ticks1).scratch.shrink_stk.set i
            v } } =
      m8SBlkSt s tmp1 mrk1 mclr1 (sstk1.set j v) wsort1 mcl1 mcf1 ticks1 := by
  subst h; rfl

private theorem bv8_and8_eq0_c0 {a : BitVec 8} (h : (a.setWidth 32 &&& 8#32) = 0#32) :
    (a &&& 8#8) = 0#8 := by revert a h; decide

private theorem bv8_and8_ne0_c0 {a : BitVec 8} (h : (a.setWidth 32 &&& 8#32) ≠ 0#32) :
    (a &&& 8#8) ≠ 0#8 := by revert a h; decide

private theorem bv8_and247_c0' (a : BitVec 8) :
    (a.setWidth 32 &&& 247#32).setWidth 8 = a &&& 0xF7#8 := by revert a; decide

private theorem bv8_or8_c0' (a : BitVec 8) :
    (a.setWidth 32 ||| 8#32).setWidth 8 = a ||| 8#8 := by revert a; decide

/-! ## 1. Factored Tail Expr & WP Proof (`if (failed || uip == 0xFFFFFFFFu) ...`) -/

private def m8ShrinkBit8UpdExpr {V : Ty → Type} {C : List Ty → Type} {rs : List Ty}
    (pMark : V i64) (sv : V i32) (isOr : Bool) (k : Expr V C rs) : Expr V C rs :=
  let imm32 : BitVec 32 := match isOr with | true => 8 | false => 247
  let op : OpCode [i32, i32] [i32] := match isOr with | true => .or i32 | false => .and i32
  .let_ (Op.mk (.zext 32 64) (.var sv, ())) fun pa_idx =>
  .let_ (Op.mk (.add i64) (.var pMark, .var pa_idx.fst, ())) fun pa_l =>
  .let_ (Op.mk (.zext 32 64) (.var sv, ())) fun pr_idx =>
  .let_ (Op.mk (.add i64) (.var pMark, .var pr_idx.fst, ())) fun pa_r =>
  .load i8 (.var pa_r.fst) fun ld =>
  .let_ (Op.mk (.trunc 32 8) (.imm imm32, ())) fun m8 =>
  .let_ (Op.mk (.zext 8 32) (.var ld, ())) fun l32 =>
  .let_ (Op.mk (.zext 8 32) (.var m8.fst, ())) fun m32 =>
  .let_ (Op.mk op (.var l32.fst, .var m32.fst, ())) fun a32 =>
  .let_ (Op.mk (.trunc 32 8) (.var a32.fst, ())) fun a8 =>
  .store (.var a8.fst) (.var pa_l.fst) k

private def m8ShrinkAfterExpr {V : Ty → Type} {C : List Ty → Type}
    (h pTmp pMark pShrinkStk beg end_b slen : V i64) (failed : V .bool) (uip : V i32) :
    Expr V C [.bool] :=
  let op64 (c : OpCode [i64, i64] [i64]) (a b : Arg V i64) := Op.mk c (a, b, ())
  let failBody : Expr V C [.bool] :=
    .group (sig := [[i64]]) (fun Ls => .cons (fun i =>
      .let_ (Op.mk (.cmp .ult i64 .bool rfl) (.var i.fst, .var slen, ())) fun cmp =>
      .jnz (.var cmp.fst)
        (.let_ (op64 (.mul i64) (.var i.fst) (.imm 4)) fun off =>
         .let_ (op64 (.add i64) (.var pShrinkStk) (.var off.fst)) fun addr =>
         .load i32 (.var addr.fst) fun sv =>
         m8ShrinkBit8UpdExpr pMark sv false
           (.let_ (op64 (.add i64) (.var i.fst) (.imm 1)) fun i1 =>
            .jump Ls.fst (.var i1.fst, ())))
        (.ret (.imm false, ()))) .nil)
      (fun Ls => .jump Ls.fst (.imm 0, ()))
  let succBody : Expr V C [.bool] :=
    .group (sig := [[i64]]) (fun Lk => .cons (fun k =>
      .let_ (Op.mk (.cmp .ult i64 .bool rfl) (.var k.fst, .var end_b, ())) fun cmp =>
      .jnz (.var cmp.fst)
        (.let_ (op64 (.mul i64) (.var k.fst) (.imm 4)) fun off =>
         .let_ (op64 (.add i64) (.var pTmp) (.var off.fst)) fun addr =>
         .store (@Arg.imm V i32 (4294967295 : BitVec 32)) (.var addr.fst)
           (.let_ (op64 (.add i64) (.var k.fst) (.imm 1)) fun k1 =>
            .jump Lk.fst (.var k1.fst, ())))
        (.let_ (op64 (.mul i64) (.var beg) (.imm 4)) fun boff =>
         .let_ (op64 (.add i64) (.var pTmp) (.var boff.fst)) fun baddr =>
         .let_ (Op.mk (.xor i32) (.var uip, .imm 1, ())) fun xlit =>
         .store (.var xlit.fst) (.var baddr.fst)
           (.group (sig := [[i64]]) (fun Li => .cons (fun i =>
             .let_ (Op.mk (.cmp .ult i64 .bool rfl) (.var i.fst, .var slen, ())) fun cmpi =>
             .jnz (.var cmpi.fst)
               (.let_ (op64 (.mul i64) (.var i.fst) (.imm 4)) fun offi =>
                .let_ (op64 (.add i64) (.var pShrinkStk) (.var offi.fst)) fun addri =>
                .load i32 (.var addri.fst) fun sv =>
                m8ShrinkBit8UpdExpr pMark sv false
                  (.let_ (Op.mk (.trunc 32 8) (.imm 2, ())) fun t2 =>
                   .call "full_min_mark" (as := [i64, i32, i8]) (bs := [])
                     (.var h, .var sv, .var t2.fst, ()) fun _ =>
                   .let_ (op64 (.add i64) (.var i.fst) (.imm 1)) fun i1 =>
                   .jump Li.fst (.var i1.fst, ())))
               (.ret (.imm true, ()))) .nil)
             (fun Li => .jump Li.fst (.imm 0, ()))))) .nil)
      (fun Lk => .jump Lk.fst (.var beg, ()))
  .group (sig := [[]]) (fun _Jt => .cons (fun _ => failBody) .nil) fun Jt =>
    .jnz (.var failed) (.jump Jt.fst ())
      (.let_ (Op.mk (.cmp .eq i32 .bool rfl)
          (.var uip, .imm (4294967295 : BitVec 32), ())) fun cmpu =>
       .jnz (.var cmpu.fst) (.jump Jt.fst ()) succBody)

private theorem m8_shrink_after_wp {Γ : Env} {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    {blvl uip : BitVec 32} {beg end_b : BitVec 64} {keepLen slen : Nat}
    {mrk1 : List (BitVec 8)} {mclr1 sstk1 wsort1 : List (BitVec 32)}
    {mcl1 : Nat} {mcf1 ticks1 slen_bv : BitVec 64} {failed : Bool}
    {t_uip : Nat} {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [.bool]} {X : XPost}
    (hMm : Γ.Has "full_min_mark" Spec.fullMinMarkSpec) (hcore : FullOtfsCoreInv c F0 s)
    (hbeg_end : beg.toNat < end_b.toNat)
    (hend_kl : end_b.toNat ≤ keepLen) (hkl_cv : keepLen ≤ s.core.cur_vars)
    (hblk_lvl : ∀ k, beg.toNat ≤ k → k < end_b.toNat →
      (s.core.lvl[(s.core.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = blvl.toNat)
    (hkeep : ∀ k < keepLen, s.core.tmp[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
      let l := (s.core.tmp[k]?.getD 0#32).toNat
      l < 2 * s.core.cur_vars ∧ s.core.vals[l]?.getD 0#8 = 0xFF#8 ∧
      (s.core.mrk[l / 2]?.getD 0#8 &&& 2#8) ≠ 0#8)
    (hsl_bv : slen_bv.toNat = slen)
    (hb : M8ShrinkBaseInv c s mrk1 mclr1 sstk1 wsort1 mcl1 mcf1 slen
      (((s.core.tmp.take keepLen).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat))
    (hok : failed = false → M8ShrinkStk8 mrk1 sstk1 slen ∧ uip ≠ 0xFFFFFFFF#32 ∧
      t_uip < s.core.trail_end ∧
      (s.core.trl[t_uip]?.getD 0#32).toNat = uip.toNat ∧
      (mrk1[uip.toNat / 2]?.getD 0#8 &&& 8#8) ≠ 0#8 ∧
      (s.core.lvl[uip.toNat / 2]?.getD 0#32).toNat = blvl.toNat ∧
      M8ShrinkBlk8 s mrk1 beg.toNat end_b.toNat ∧
      (∀ w < s.core.cur_vars, (mrk1[w]?.getD 0#8 &&& 8#8) ≠ 0#8 →
        w = uip.toNat / 2 ∨ ∃ idx < s.core.trail_end, t_uip < idx ∧
          (s.core.trl[idx]?.getD 0#32).toNat / 2 = w ∧ ShrinkResolved s.core mrk1 idx))
    (hm : (FullMem c (m8SBlkSt s s.core.tmp mrk1 mclr1 sstk1 wsort1 mcl1 mcf1 ticks1) ⋆ R) m)
    (hQ : ∀ (ok : Bool) tmp' mrk' mclr' sstk' wsort' mcl' mcf' ticks' m',
      let s' := Spec.m8ShrinkBlkBoolState s tmp' mrk' mclr' sstk' wsort' mcl' mcf' ticks'
      FullOtfsCoreInv c F0 s' →
      FullMinMarkInv s'.core (((tmp'.take keepLen).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat) →
      (∀ v, s.core.cur_vars ≤ v → mrk'[v]? = s.core.mrk[v]?) →
      (∀ v < s.core.cur_vars, (mrk'[v]?.getD 0#8 &&& 8#8) = 0#8) →
      (∀ v < s.core.cur_vars,
        (s.core.mrk[v]?.getD 0#8 &&& 2#8) ≠ 0#8 → (mrk'[v]?.getD 0#8 &&& 2#8) ≠ 0#8) →
      (ok = false → tmp' = s.core.tmp) →
      (∀ k < keepLen, (k < beg.toNat ∨ end_b.toNat ≤ k) → tmp'[k]? = s.core.tmp[k]?) →
      (∀ k, beg.toNat ≤ k → k < end_b.toNat → tmp'[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
        (s.core.lvl[(tmp'[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = blvl.toNat) →
      ((((s.core.tmp.take keepLen).filter (· ≠ 0xFFFFFFFF#32)).map
          fun x => x.toNat / 2).Nodup →
        (∀ k < keepLen, (k < beg.toNat ∨ end_b.toNat ≤ k) →
          s.core.tmp[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
          (s.core.lvl[(s.core.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≠ blvl.toNat) →
        (((tmp'.take keepLen).filter (· ≠ 0xFFFFFFFF#32)).map fun x => x.toNat / 2).Nodup) →
      (∀ F_cur, FullOtfsWitnessInv c F0 F_cur s.core →
        (cnfOfClauses F_cur).EntailsClause (cnfClause
          (((s.core.tmp.take keepLen).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat)) →
        FullOtfsWitnessInv c F0 F_cur s'.core ∧
        (cnfOfClauses F_cur).EntailsClause (cnfClause
          (((tmp'.take keepLen).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat))) →
      (∀ k < keepLen, tmp'[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
        let l := (tmp'[k]?.getD 0#32).toNat
        l < 2 * s.core.cur_vars ∧ s'.core.vals[l]?.getD 0#8 = 0xFF#8 ∧
        (mrk'[l / 2]?.getD 0#8 &&& 2#8) ≠ 0#8) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m') :
    wp Γ Q X (m8ShrinkAfterExpr c.hdr c.pTmp c.pMark c.pShrinkStk beg end_b slen_bv
      failed uip) m := by
  have hlen0 := hcore.1.core_ok; have hcv := hlen0.cur_vars_le
  have hmx := c.hmaxv; unfold Ref.dimacsBound at hmx
  dsimp only [m8ShrinkAfterExpr, m8ShrinkBit8UpdExpr]
  refine wp_join_group (ts := []) (fun _ m_fail => m_fail = m) ?_ ?_
  · rintro _ ⟨⟩ m_f hm_f; subst m_f; rw [Blocks.get_here]
    refine wp_loop_group (ts := [i64]) (fun n (i_bv, ()) m_i =>
        n = slen - i_bv.toNat ∧ i_bv.toNat ≤ slen ∧
        ∃ mrk_i, M8ShrinkBaseInv c s mrk_i mclr1 sstk1 wsort1 mcl1 mcf1 slen
          (((s.core.tmp.take keepLen).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat) ∧
          (∀ w < s.core.cur_vars, (mrk_i[w]?.getD 0#8 &&& 8#8) ≠ 0#8 →
            ∃ j, i_bv.toNat ≤ j ∧ j < slen ∧ (sstk1[j]?.getD 0#32).toNat = w) ∧
          (FullMem c (m8SBlkSt s s.core.tmp mrk_i mclr1 sstk1 wsort1 mcl1 mcf1 ticks1) ⋆ R)
            m_i) ?_ ?_
    · rintro L n_i ⟨i_bv, ⟨⟩⟩ m_i hL ⟨rfl, hi_le, mrk_i, hb_i, hrem_i, hm_i⟩
      rw [Blocks.get_here]; c0_hsplit
      · have hi_lt : i_bv.toNat < slen := by rw [← hsl_bv]; c0_grind
        have hsi_len : i_bv.toNat < (m8SBlkSt s s.core.tmp mrk_i mclr1 sstk1 wsort1
            mcl1 mcf1 ticks1).scratch.shrink_stk.length := by
          have := hb_i.slen_le; rw [hb_i.sstk_len]; omega
        obtain ⟨hsv_lt, hsv_arr, hb2, _, hrem2⟩ := m8Shrink_clear_step hcore hb_i hi_lt hrem_i
        let sv := sstk1[i_bv.toNat]'hsi_len
        have hmrk_bd : (sv.setWidth 64).toNat < (m8SBlkSt s s.core.tmp mrk_i mclr1 sstk1
            wsort1 mcl1 mcf1 ticks1).core.mrk.length := by rw [bv_c0_zext32_64]; exact hsv_arr
        c0_hsteps!
        rw [m8SBlk_st_mrk_eq s s.core.tmp mrk_i mclr1 sstk1 wsort1 mcl1 mcf1 ticks1
          (by rw [bv_c0_zext32_64])] at hm
        have hm_i1 : (FullMem c (m8SBlkSt s s.core.tmp
            (mrk_i.set sv.toNat (mrk_i[sv.toNat]?.getD 0#8 &&& 0xF7#8))
            mclr1 sstk1 wsort1 mcl1 mcf1 ticks1) ⋆ R) m := by
          have hget_m : mrk_i[sv.toNat] = mrk_i[sv.toNat]?.getD 0#8 := by
            rw [List.getElem?_eq_getElem hsv_arr, Option.getD_some]
          dsimp only [sv] at hget_m
          simpa only [bv_c0_zext32_64, bv8_and247_c0', hget_m] using hm
        have hi1 : (i_bv + 1).toNat = i_bv.toNat + 1 := by c0_bound
        exact hL (slen - (i_bv + 1).toNat) (i_bv + 1, ()) m
          (by rw [hi1]; omega) ⟨rfl, by rw [hi1]; omega, _, hb2, by rw [hi1]; exact hrem2, hm_i1⟩
      · have hi_eq : i_bv.toNat = slen := by rw [← hsl_bv]; c0_grind
        subst hi_eq
        have hno8_f : ∀ w < s.core.cur_vars, (mrk_i[w]?.getD 0#8 &&& 8#8) = 0#8 := fun w hw => by
          by_cases hnz : (mrk_i[w]?.getD 0#8 &&& 8#8) = 0#8
          · exact hnz
          · obtain ⟨j, hj1, hj2, _⟩ := hrem_i w hw hnz; omega
        c0_hsteps!
        refine hQ false s.core.tmp mrk_i mclr1 sstk1 wsort1 mcl1 mcf1 ticks1 m_i
          (m8CoreInv_blk hcore hlen0.tmp_len_arr hb_i.mrk_len hb_i.mclr_len hb_i.mcl_le
            hb_i.sstk_len hb_i.wsort_len) hb_i.min_inv hb_i.mrk_above hno8_f hb_i.mono2
          (fun _ => rfl) (fun _ _ _ => rfl) (fun k hk1 hk2 _ => hblk_lvl k hk1 hk2)
          (fun hnd _ => hnd) (fun _ hw hEnt => ⟨m8Witness_shrinkBlk hw, hEnt⟩)
          (fun k hk hne => ⟨(hkeep k hk hne).1, (hkeep k hk hne).2.1,
            hb_i.mono2 _ (by have := (hkeep k hk hne).1; omega) (hkeep k hk hne).2.2⟩) hm_i
    · intro L hL; c0_hsteps!; refine hL slen (0#64, ()) m ⟨by simp, Nat.zero_le _, mrk1, hb,
        fun w hw h8 => by
          obtain ⟨j, hj, hje⟩ := hb.bit8_sstk w hw h8; exact ⟨j, Nat.zero_le _, hj, hje⟩,
        hm⟩
  · rintro Jt hJt; c0_hsplit
    · c0_hsteps!; exact hJt () m rfl
    · have hf : failed = false := hc
      c0_hsplit
      · c0_hsteps!; exact hJt () m rfl
      · have huip_ne : uip ≠ 0xFFFFFFFF#32 := by c0_grind
        obtain ⟨hstk1, _, huip_te, huip_eq, huip_8, huip_lvl, hblk1, hres1⟩ := hok hf
        refine wp_loop_group (ts := [i64]) (fun n (k_bv, ()) m_k =>
            n = end_b.toNat - k_bv.toNat ∧ beg.toNat ≤ k_bv.toNat ∧ k_bv.toNat ≤ end_b.toNat ∧
            ∃ tmp_k, tmp_k.length = c.max_vars ∧
              (∀ j < keepLen, (j < beg.toNat ∨ k_bv.toNat ≤ j) → tmp_k[j]? = s.core.tmp[j]?) ∧
              (∀ j, beg.toNat ≤ j → j < k_bv.toNat → tmp_k[j]? = some 0xFFFFFFFF#32) ∧
              (FullMem c (m8SBlkSt s tmp_k mrk1 mclr1 sstk1 wsort1 mcl1 mcf1 ticks1) ⋆ R) m_k)
          ?_ ?_
        · rintro Lk n_k ⟨k_bv, ⟨⟩⟩ m_k hLk ⟨rfl, hk_beg, hk_end, tmp_k, htk_len, htk_out,
              htk_ff, hm_k⟩
          rw [Blocks.get_here]; c0_hsplit
          · have hkl : k_bv.toNat < end_b.toNat := by c0_grind
            obtain ⟨hk_arr, htk2_len, htk2_ff⟩ := m8Shrink_succ_tmp_step htk_len hkl hk_beg
              (by omega) htk_ff
            c0_hsteps!
            rw [m8SBlk_st_tmp_eq s tmp_k mrk1 mclr1 sstk1 wsort1 mcl1 mcf1 ticks1 rfl] at hm
            have hk1 : (k_bv + 1).toNat = k_bv.toNat + 1 := by c0_bound
            exact hLk (end_b.toNat - (k_bv + 1).toNat) (k_bv + 1, ()) m
              (by rw [hk1]; omega) ⟨rfl, by rw [hk1]; omega, by rw [hk1]; omega, _, htk2_len,
                fun j hj hjb => by
                  rw [List.getElem?_set_ne (by rw [hk1] at hjb; omega)]
                  exact htk_out j hj (hjb.elim Or.inl fun h => Or.inr (by rw [hk1] at h; omega)),
                by rw [hk1]; exact htk2_ff, hm⟩
          · have hk_eq : k_bv.toNat = end_b.toNat := by c0_grind
            have hbeg_arr : beg.toNat < (m8SBlkSt s tmp_k mrk1 mclr1 sstk1 wsort1 mcl1 mcf1
                ticks1).core.tmp.length := by rw [htk_len]; omega
            c0_hsteps_nogrp
            rw [m8SBlk_st_tmp_eq s tmp_k mrk1 mclr1 sstk1 wsort1 mcl1 mcf1 ticks1 rfl] at hm
            let tmp_f := tmp_k.set beg.toNat (uip ^^^ 1#32)
            have htf_len : tmp_f.length = c.max_vars := by simp [tmp_f, htk_len]
            have htf_out : ∀ k < keepLen, (k < beg.toNat ∨ end_b.toNat ≤ k) →
                tmp_f[k]? = s.core.tmp[k]? := fun k hk hkb => by
              dsimp only [tmp_f]; rw [List.getElem?_set_ne (by omega)]
              exact htk_out k hk (hkb.imp id fun h => by omega)
            have htf_beg : tmp_f[beg.toNat]? = some (uip ^^^ 1#32) :=
              List.getElem?_set_self hbeg_arr
            have htf_rest : ∀ k, beg.toNat < k → k < end_b.toNat →
                tmp_f[k]? = some 0xFFFFFFFF#32 := fun k hk1 hk2 => by
              dsimp only [tmp_f]; rw [List.getElem?_set_ne (by omega)]
              exact htk_ff k (by omega) (by omega)
            refine wp_loop_group (ts := [i64]) (fun n (i_bv, ()) m_i =>
                n = slen - i_bv.toNat ∧ i_bv.toNat ≤ slen ∧
                ∃ mrk_i mclr_i mcl_i mcf_i,
                  mrk_i.length = c.max_vars ∧ mclr_i.length = c.max_vars ∧ mcl_i ≤ c.max_vars ∧
                  (∀ w < s.core.cur_vars, (mrk_i[w]?.getD 0#8 &&& 0xF1#8) = 0#8) ∧
                  (mcf_i = 0#64 → ∀ w < s.core.cur_vars, (mrk_i[w]?.getD 0#8 &&& 6#8) ≠ 0#8 →
                    ∃ k < mcl_i, (mclr_i[k]?.getD 0#32).toNat = w) ∧
                  (∀ w, s.core.cur_vars ≤ w → mrk_i[w]? = mrk1[w]?) ∧
                  (∀ w < s.core.cur_vars,
                    (mrk1[w]?.getD 0#8 &&& 2#8) ≠ 0#8 → (mrk_i[w]?.getD 0#8 &&& 2#8) ≠ 0#8) ∧
                  (∀ k < i_bv.toNat,
                    (mrk_i[(sstk1[k]?.getD 0#32).toNat]?.getD 0#8 &&& 2#8) ≠ 0#8) ∧
                  (∀ w < s.core.cur_vars, (mrk_i[w]?.getD 0#8 &&& 8#8) ≠ 0#8 →
                    ∃ j, i_bv.toNat ≤ j ∧ j < slen ∧ (sstk1[j]?.getD 0#32).toNat = w) ∧
                  (∀ w < s.core.cur_vars, (mrk_i[w]?.getD 0#8 &&& 2#8) ≠ 0#8 →
                    (mrk1[w]?.getD 0#8 &&& 2#8) ≠ 0#8 ∨ (mrk1[w]?.getD 0#8 &&& 8#8) ≠ 0#8) ∧
                  (∀ w < s.core.cur_vars, (mrk_i[w]?.getD 0#8 &&& 8#8) ≠ 0#8 →
                    (mrk1[w]?.getD 0#8 &&& 8#8) ≠ 0#8) ∧
                  (FullMem c (m8SBlkSt s tmp_f mrk_i mclr_i sstk1 wsort1 mcl_i mcf_i ticks1) ⋆ R)
                    m_i) ?_ ?_
            · rintro Li n_i ⟨i_bv, ⟨⟩⟩ m_i hLi ⟨rfl, hi_le, mrk_i, mclr_i, mcl_i, mcf_i,
                  hmrki, hmclri, hmcli, hdom_i, hcov_i, hm_ab, hm2_i, hdone_2, hrem8, hnew2,
                  h8orig, hm_i⟩
              rw [Blocks.get_here]; c0_hsplit
              · have := hb.sstk_len; have := hb.slen_le; have := hlen0.tmp_len_arr
                have hi_lt : i_bv.toNat < slen := by rw [← hsl_bv]; c0_grind
                have hsi_len : i_bv.toNat < (m8SBlkSt s tmp_f mrk_i mclr_i sstk1 wsort1
                    mcl_i mcf_i ticks1).scratch.shrink_stk.length := by rw [hb.sstk_len]; omega
                let sv := sstk1[i_bv.toNat]'hsi_len
                have hsv_lt : sv.toNat < s.core.cur_vars := by
                  have := hb.sstk_lt i_bv.toNat hi_lt
                  rwa [List.getElem?_eq_getElem (by rw [hb.sstk_len]; omega), Option.getD_some]
                    at this
                have hmrk_bd : (sv.setWidth 64).toNat < (m8SBlkSt s tmp_f mrk_i mclr_i sstk1
                    wsort1 mcl_i mcf_i ticks1).core.mrk.length := by
                  rw [bv_c0_zext32_64, hmrki]; omega
                c0_hsteps!
                rw [m8SBlk_st_mrk_eq s tmp_f mrk_i mclr_i sstk1 wsort1 mcl_i mcf_i ticks1
                  (by rw [bv_c0_zext32_64])] at hm
                have hget_m : mrk_i[sv.toNat] = mrk_i[sv.toNat]?.getD 0#8 := by
                  rw [List.getElem?_eq_getElem (by rw [hmrki]; omega), Option.getD_some]
                have hm_mid : (FullMem c (m8SBlkSt s tmp_f
                    (mrk_i.set sv.toNat (mrk_i[sv.toNat]?.getD 0#8 &&& 0xF7#8))
                    mclr_i sstk1 wsort1 mcl_i mcf_i ticks1) ⋆ R) m := by
                  dsimp only [sv] at hget_m
                  simpa only [bv_c0_zext32_64, bv8_and247_c0', hget_m] using hm
                let mrk_mid := mrk_i.set sv.toNat (mrk_i[sv.toNat]?.getD 0#8 &&& 0xF7#8)
                let st_mid := m8BlkState s tmp_f mrk_mid mclr_i sstk1 wsort1 mcl_i mcf_i ticks1
                let st_fin := fullMinMarkStepState st_mid sv.toNat 2#8
                have hstep_all := m8Shrink_succ_mark_step (mrk_fin := st_fin.core.mrk)
                  (mclr_fin := st_fin.core.min_clr) (mcl_fin := st_fin.core.min_clr_len)
                  (mcf_fin := st_fin.core.min_clr_full) hcore hb.sstk_len hb.slen_le
                  hb.sstk_lt hstk1 hi_lt hmrki hmclri hmcli hdom_i hcov_i hm_ab hm2_i hdone_2 hrem8
                  hnew2 h8orig htf_len hb.wsort_len
                  (m8Blk_step (tmp1 := tmp_f) (mrk1 := mrk_mid) (mclr1 := mclr_i)
                    (sstk1 := sstk1) (wsort1 := wsort1) (mcl1 := mcl_i) (mcf1 := mcf_i)
                    (ticks1 := ticks1) sv.toNat 2#8)
                obtain ⟨_, _, hst_mid_ok, hm_mid8, hdom_mid, hcov_mid, hmf_len, hcf_len, hml_le,
                    hdomf, hcovf, hfab, hm2f, hdone2f, hrem8f, hnew2f, h8of⟩ := hstep_all
                apply wp_call_of_spec; apply hMm
                change Proof.Spec.fullMinMarkSpec (c.hdr, sv, 2#8, ()) m _ X
                refine ⟨c, st_mid, R, rfl, hst_mid_ok, hm_mid, ?_⟩
                have hi1 : (i_bv + 1).toNat = i_bv.toNat + 1 := by c0_bound
                by_cases h2z : (mrk_mid[sv.toNat]?.getD 0#8 &&& 2#8) = 0#8
                · have hcond : ¬ (st_mid.core.cur_vars ≤ sv.toNat ∨
                      (st_mid.core.mrk[sv.toNat]?.getD 0#8 &&& 2#8) ≠ 0#8) :=
                    fun h => h.elim
                      (by dsimp only [st_mid, m8BlkState, Spec.m8ShrinkBlkBoolState]; omega)
                      (fun hn => hn h2z)
                  rw [ite_eq_right hcond]
                  intro m_fin hm_fin
                  have hstep_f : st_fin = fullMinMarkState st_mid sv.toNat 2#8 := by
                    dsimp only [st_fin, fullMinMarkStepState, fullMinMarkStepCore, fullMinMarkState]
                    rw [ite_eq_right hcond]
                  have hm_fin' : (FullMem c (m8SBlkSt s tmp_f st_fin.core.mrk st_fin.core.min_clr
                      sstk1 wsort1 st_fin.core.min_clr_len st_fin.core.min_clr_full ticks1) ⋆ R)
                      m_fin := by
                    have h1 := m8Blk_step (s := s) (tmp1 := tmp_f) (mrk1 := mrk_mid)
                      (mclr1 := mclr_i) (sstk1 := sstk1) (wsort1 := wsort1) (mcl1 := mcl_i)
                      (mcf1 := mcf_i) (ticks1 := ticks1) sv.toNat 2#8
                    change (FullMem c (m8BlkState s tmp_f st_fin.core.mrk st_fin.core.min_clr
                      sstk1 wsort1 st_fin.core.min_clr_len st_fin.core.min_clr_full ticks1) ⋆ R)
                      m_fin
                    rw [← h1]; change (FullMem c st_fin ⋆ R) m_fin; rwa [hstep_f]
                  c0_hsteps!; exact hLi (slen - (i_bv + 1).toNat) (i_bv + 1, ()) m_fin
                    (by rw [hi1]; omega) ⟨rfl, by rw [hi1]; omega, st_fin.core.mrk,
                      st_fin.core.min_clr, st_fin.core.min_clr_len, st_fin.core.min_clr_full,
                      hmf_len, hcf_len, hml_le, hdomf, hcovf, hfab, hm2f,
                      by rw [hi1]; exact hdone2f, by rw [hi1]; exact hrem8f, hnew2f, h8of, hm_fin'⟩
                · have hcond : st_mid.core.cur_vars ≤ sv.toNat ∨
                      (st_mid.core.mrk[sv.toNat]?.getD 0#8 &&& 2#8) ≠ 0#8 := Or.inr h2z
                  rw [ite_eq_left hcond]
                  have hstep_id : st_fin = st_mid := by
                    dsimp only [st_fin, fullMinMarkStepState, fullMinMarkStepCore]
                    rw [ite_eq_left hcond]
                  have hm_fin' : (FullMem c (m8SBlkSt s tmp_f st_fin.core.mrk st_fin.core.min_clr
                      sstk1 wsort1 st_fin.core.min_clr_len st_fin.core.min_clr_full ticks1) ⋆ R)
                      m := by rwa [hstep_id]
                  c0_hsteps!; exact hLi (slen - (i_bv + 1).toNat) (i_bv + 1, ()) m
                    (by rw [hi1]; omega) ⟨rfl, by rw [hi1]; omega, st_fin.core.mrk,
                      st_fin.core.min_clr, st_fin.core.min_clr_len, st_fin.core.min_clr_full,
                      hmf_len, hcf_len, hml_le, hdomf, hcovf, hfab, hm2f,
                      by rw [hi1]; exact hdone2f, by rw [hi1]; exact hrem8f, hnew2f, h8of, hm_fin'⟩
              · have hi_eq : i_bv.toNat = slen := by rw [← hsl_bv]; c0_grind
                subst hi_eq
                have hno8_f : ∀ w < s.core.cur_vars, (mrk_i[w]?.getD 0#8 &&& 8#8) = 0#8 :=
                  fun w hw => by
                    by_cases hnz : (mrk_i[w]?.getD 0#8 &&& 8#8) = 0#8
                    · exact hnz
                    · obtain ⟨j, hj1, hj2, _⟩ := hrem8 w hw hnz; omega
                have h8_to_2 : ∀ w < s.core.cur_vars, (mrk1[w]?.getD 0#8 &&& 8#8) ≠ 0#8 →
                    (mrk_i[w]?.getD 0#8 &&& 2#8) ≠ 0#8 := fun w hw h8 => by
                  obtain ⟨j, hj, hjeq⟩ := hb.bit8_sstk w hw h8
                  rw [← hjeq]; exact hdone_2 j hj
                obtain ⟨hmin_f, hEnt_f, hlvl_f, hkeep_f⟩ := m8Shrink_blk_success_finish hcore
                  hbeg_end hend_kl hkl_cv hkeep hb hmrki hmclri htf_len hdom_i hcov_i hm2_i h8_to_2
                  hnew2 huip_te huip_eq huip_8 huip_lvl hres1 hblk1 htf_out htf_beg htf_rest
                c0_hsteps!
                exact hQ true tmp_f mrk_i mclr_i sstk1 wsort1 mcl_i mcf_i ticks1 m_i
                  (m8CoreInv_blk hcore htf_len hmrki hmclri hmcli hb.sstk_len hb.wsort_len) hmin_f
                  (fun w hw => (hm_ab w hw).trans (hb.mrk_above w hw)) hno8_f
                  (fun w hw h2 => hm2_i w hw (hb.mono2 w hw h2)) (fun hf' => by cases hf') htf_out
                  hlvl_f (fun hnd hout => m8Shrink_tmp_nodup (by rw [hlen0.tmp_len_arr]; omega)
                    (by rw [htf_len]; omega) huip_lvl htf_out htf_beg htf_rest hnd hout)
                  hEnt_f hkeep_f hm_i
            · intro Li hLi; c0_hsteps!; refine hLi slen (0#64, ()) m ⟨by simp, Nat.zero_le _, mrk1,
                mclr1, mcl1, mcf1, hb.mrk_len, hb.mclr_len, hb.mcl_le, hb.min_inv.mrk_dom,
                hb.min_inv.clr_cov, fun _ _ => rfl, fun _ _ h => h, fun k hk => by simp at hk,
                fun w hw h8 => by
                  obtain ⟨j, hj, hjeq⟩ := hb.bit8_sstk w hw h8; exact ⟨j, Nat.zero_le _, hj, hjeq⟩,
                fun _ _ h => Or.inl h, fun _ _ h => h, hm⟩
        · intro Lk hLk; c0_hsteps!; exact hLk (end_b.toNat - beg.toNat) (beg, ()) m
            ⟨rfl, le_refl _, le_of_lt hbeg_end, s.core.tmp, hlen0.tmp_len_arr, fun _ _ _ => rfl,
              fun _ h1 h2 => by omega, hm⟩

/-! ## 2. Factored Inner Reason-Literal Loop (`while (i < csz && !failed)`) -/

private def m8ShrinkClCheckExpr {V : Ty → Type} {C : List Ty → Type}
    (h pMark pLevel pShrinkStk cv : V i64)
    (uip32 blvl32 ot_v : V i32) (op_c sl_c : V i64) (f_c : V .bool)
    (J1 : C [i64, i64, .bool]) : Expr V C [.bool] :=
  let op64 (c : OpCode [i64, i64] [i64]) (a b : Arg V i64) := Op.mk c (a, b, ())
  let ov_op := Op.mk (.lshr i32) (.var ot_v, .imm 1, ())
  let mkSkip := .jump J1 (.var op_c, .var sl_c, .var f_c, ())
  .let_ ov_op fun ov =>
  .let_ (Op.mk (.cmp .ne i32 .bool rfl) (.var ot_v, .var uip32, ())) fun hneu =>
  .jnz (.var hneu.fst)
    (.let_ (Op.mk (.zext 32 64) (.var ov.fst, ())) fun ov64 =>
     .let_ (Op.mk (.cmp .ult i64 .bool rfl) (.var ov64.fst, .var cv, ())) fun hltcv =>
     .jnz (.var hltcv.fst)
       (.let_ (Op.mk (.zext 32 64) (.var ov.fst, ())) fun olv64 =>
        .let_ (op64 (.mul i64) (.var olv64.fst) (.imm 4)) fun olmul =>
        .let_ (op64 (.add i64) (.var pLevel) (.var olmul.fst)) fun oladdr =>
        .load i32 (.var oladdr.fst) fun lov =>
        .let_ (Op.mk (.cmp .ugt i32 .bool rfl) (.var lov, .imm 0, ())) fun hpos =>
        .jnz (.var hpos.fst)
          (.let_ (Op.mk (.zext 32 64) (.var ov.fst, ())) fun om64 =>
           .let_ (op64 (.add i64) (.var pMark) (.var om64.fst)) fun omaddr =>
           .load i8 (.var omaddr.fst) fun mov =>
           .let_ (Op.mk (.trunc 32 8) (.imm 8, ())) fun c8 =>
           .let_ (Op.mk (.zext 8 32) (.var mov, ())) fun mov32 =>
           .let_ (Op.mk (.zext 8 32) (.var c8.fst, ())) fun c832 =>
           .let_ (Op.mk (.and i32) (.var mov32.fst, .var c832.fst, ())) fun mand =>
           .let_ (Op.mk (.trunc 32 8) (.imm 0, ())) fun z8 =>
           .let_ (Op.mk (.zext 8 32) (.var z8.fst, ())) fun z832 =>
           .let_ (Op.mk (.cmp .eq i32 .bool rfl) (.var mand.fst, .var z832.fst, ())) fun hz =>
           .jnz (.var hz.fst)
             (.group (sig := [[i64, i64, .bool]]) (fun _J2 => .cons (fun out2 =>
                .jump J1 (.var out2.1, .var out2.2.1, .var out2.2.2.1, ())) .nil) fun J2 =>
                .let_ (Op.mk (.zext 32 64) (.var ov.fst, ())) fun ovl64 =>
                .let_ (op64 (.mul i64) (.var ovl64.fst) (.imm 4)) fun ovmul =>
                .let_ (op64 (.add i64) (.var pLevel) (.var ovmul.fst)) fun ovaddr =>
                .load i32 (.var ovaddr.fst) fun lov2 =>
                .let_ (Op.mk (.cmp .ult i32 .bool rfl) (.var lov2, .var blvl32, ())) fun hltb =>
                .jnz (.var hltb.fst)
                  (.group (sig := [[.bool]]) (fun _J2b => .cons (fun fb =>
                     .jump J2.fst (.var op_c, .var sl_c, .var fb.fst, ())) .nil) fun J2b =>
                   .call "full_shrink_lower_m8" (as := [i64, i32, i32]) (bs := [.bool])
                     (.var h, .var ot_v, .var ov.fst, ()) fun ok_l =>
                   .jnz (.var ok_l.fst)
                     (.jump J2b.fst (.var f_c, ()))
                     (.jump J2b.fst (.imm true, ())))
                  (.group (sig := [[i64, i64, .bool]]) (fun _J2e => .cons (fun out2e =>
                     .jump J2.fst (.var out2e.1, .var out2e.2.1, .var out2e.2.2.1, ())) .nil)
                     fun J2e =>
                   .let_ (Op.mk (.zext 32 64) (.var ov.fst, ())) fun ovl2 =>
                   .let_ (op64 (.mul i64) (.var ovl2.fst) (.imm 4)) fun ovm2 =>
                   .let_ (op64 (.add i64) (.var pLevel) (.var ovm2.fst)) fun ova2 =>
                   .load i32 (.var ova2.fst) fun lov3 =>
                   .let_ (Op.mk (.cmp .eq i32 .bool rfl) (.var lov3, .var blvl32, ())) fun heqb =>
                   .jnz (.var heqb.fst)
                     (.let_ (Op.mk (.cmp .ult i64 .bool rfl) (.var sl_c, .var cv, ())) fun hslc =>
                      .jnz (.var hslc.fst)
                        (m8ShrinkBit8UpdExpr pMark ov.fst true
                          (.let_ (op64 (.mul i64) (.var sl_c) (.imm 4)) fun soff =>
                           .let_ (op64 (.add i64) (.var pShrinkStk) (.var soff.fst)) fun saddr =>
                           .store (.var ov.fst) (.var saddr.fst)
                             (.let_ (op64 (.add i64) (.var sl_c) (.imm 1)) fun sl1 =>
                              .let_ (op64 (.add i64) (.var op_c) (.imm 1)) fun op1 =>
                              .jump J2e.fst (.var op1.fst, .var sl1.fst, .var f_c, ()))))
                        (.jump J2e.fst (.var op_c, .var sl_c, .imm true, ())))
                     (.jump J2e.fst (.var op_c, .var sl_c, .imm true, ()))))
             mkSkip)
          mkSkip)
       mkSkip)
    mkSkip

private def m8ShrinkClLoopExpr {V : Ty → Type} {C : List Ty → Type}
    (h pMark pLevel pShrinkStk pArena cv : V i64)
    (is_bin : V .bool) (uip32 rsn32 csz32 : V i32) (open_i slen : V i64) (failed : V .bool)
    (blvl32 : V i32)
    (kAfter : V i64 → V i64 → V .bool → Expr V C [.bool]) : Expr V C [.bool] :=
  let op64 (c : OpCode [i64, i64] [i64]) (a b : Arg V i64) := Op.mk c (a, b, ())
  .group (sig := [[i64, i64, .bool, i32]]) (fun Lc => .cons (fun args =>
    let op_c := args.1; let sl_c := args.2.1; let f_c := args.2.2.1; let j_c := args.2.2.2.1
    .group (sig := [[]]) (fun _Js1 => .cons (fun _ => kAfter op_c sl_c f_c) .nil)
      (fun Js1 =>
        .let_ (Op.mk (.cmp .ult i32 .bool rfl) (.var j_c, .var csz32, ())) fun hlt =>
        .jnz (.var hlt.fst)
          (.jnz (.var f_c) (.jump Js1.fst ())
             (.group (sig := [[i32]]) (fun _Jot => .cons (fun ot =>
                let ot_v := ot.1
                .group (sig := [[i64, i64, .bool]]) (fun _J1 => .cons (fun out1 =>
                  .let_ (Op.mk (.add i32) (.var j_c, .imm 1, ())) fun j1 =>
                  .jump Lc.fst (.var out1.1, .var out1.2.1, .var out1.2.2.1, .var j1.fst, ()))
                  .nil)
                  (fun J1 =>
                    m8ShrinkClCheckExpr h pMark pLevel pShrinkStk cv uip32 blvl32 ot_v
                      op_c sl_c f_c J1.fst)) .nil)
                (fun Jot =>
                  .jnz (.var is_bin)
                    (.let_ (Op.mk (.and i32) (.var rsn32, .imm (2147483647 : BitVec 32), ()))
                       fun bl =>
                     .jump Jot.fst (.var bl.fst, ()))
                    (.let_ (Op.mk (.zext 32 64) (.var rsn32, ())) fun r64 =>
                     .let_ (op64 (.add i64) (.var r64.fst) (.imm 3)) fun r3 =>
                     .let_ (Op.mk (.zext 32 64) (.var j_c, ())) fun j64 =>
                     .let_ (op64 (.add i64) (.var r3.fst) (.var j64.fst)) fun idx =>
                     .let_ (op64 (.mul i64) (.var idx.fst) (.imm 4)) fun off =>
                     .let_ (op64 (.add i64) (.var pArena) (.var off.fst)) fun addr =>
                     .load i32 (.var addr.fst) fun ld =>
                     .jump Jot.fst (.var ld, ())))))
          (.jump Js1.fst ()))) .nil)
    (fun Lc => .jump Lc.fst (.var open_i, .var slen, .var failed, .imm 0, ()))

private theorem m8_shrink_cl_check_wp {Γ : Env} {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    {blvl uip rsn ot : BitVec 32} {beg end_b : BitVec 64} {keepLen slen_n t_uip j_n : Nat}
    {op_c sl_c ticks_c : BitVec 64} {mrk_c : List (BitVec 8)}
    {mclr_c sstk_c wsort_c : List (BitVec 32)} {mcl_c : Nat} {mcf_c : BitVec 64}
    {is_bin : Bool} {R : Mem 64 → Prop} {m_c : Mem 64} {Q : Post [.bool]} {X : XPost}
    {J1 : Cont [i64, i64, .bool]}
    (hSL : Γ.Has "full_shrink_lower_m8" Spec.fullShrinkLowerSpec) (hcore : FullOtfsCoreInv c F0 s)
    (hblvl_lt : blvl.toNat < s.core.cur_level) (ht_te : t_uip < s.core.trail_end)
    (hend_mv : end_b.toNat ≤ c.max_vars)
    (hueq : (s.core.trl[t_uip]?.getD 0#32).toNat = uip.toNat)
    (hblk_lt : ∀ j, beg.toNat ≤ j → j < end_b.toNat →
      (s.core.tmp[j]?.getD 0#32).toNat / 2 < s.core.cur_vars)
    (hot_eq : ot.toNat = m8ShrinkRsnLit s rsn is_bin j_n)
    (hq_lt2v : m8ShrinkRsnLit s rsn is_bin j_n < 2 * s.core.cur_vars)
    (hq_src : m8ShrinkRsnLit s rsn is_bin j_n = uip.toNat ∨
      ∃ m < t_uip, (s.core.trl[m]?.getD 0#32).toNat = m8ShrinkRsnLit s rsn is_bin j_n ^^^ 1 ∧
        (s.core.lvl[m8ShrinkRsnLit s rsn is_bin j_n / 2]?.getD 0#32).toNat ≤ blvl.toNat)
    (hinv_c : M8ShrinkClInv c F0 s blvl beg.toNat end_b.toNat keepLen s.core.mrk slen_n t_uip
      uip rsn is_bin op_c.toNat sl_c.toNat j_n false mrk_c mclr_c sstk_c wsort_c mcl_c mcf_c
      ticks_c)
    (h8_c : M8ShrinkAll8 s blvl mrk_c (t_uip - 1) t_uip)
    (hm_c : (FullMem c (m8SBlkSt s s.core.tmp mrk_c mclr_c sstk_c wsort_c mcl_c mcf_c
      ticks_c) ⋆ R) m_c)
    (hJ1 : ∀ ys m_1,
      (match ys with
        | (op_1, sl_1, f_1, ()) =>
          ∃ mrk_1 mclr_1 sstk_1 wsort_1 mcl_1 mcf_1 ticks_1,
            M8ShrinkClInv c F0 s blvl beg.toNat end_b.toNat keepLen s.core.mrk slen_n
              t_uip uip rsn is_bin op_1.toNat sl_1.toNat (j_n + 1) f_1 mrk_1 mclr_1
              sstk_1 wsort_1 mcl_1 mcf_1 ticks_1 ∧
            (FullMem c (m8SBlkSt s s.core.tmp mrk_1 mclr_1 sstk_1 wsort_1 mcl_1 mcf_1
              ticks_1) ⋆ R) m_1) → J1 ys m_1) :
    wp Γ Q X (m8ShrinkClCheckExpr c.hdr c.pMark c.pLevel c.pShrinkStk
      (BitVec.ofNat 64 s.core.cur_vars) uip blvl ot op_c sl_c false J1) m_c := by
  have hlen0 := hcore.1.core_ok; have hcv := hlen0.cur_vars_le
  have hmx := c.hmaxv; unfold Ref.dimacsBound at hmx
  dsimp only [m8ShrinkClCheckExpr, m8ShrinkBit8UpdExpr]
  c0_hsplit
  · have hne_u : ot ≠ uip := hc
    have hov_lt : (ot >>> 1).toNat < s.core.cur_vars := by rw [bv32_lshr_1, hot_eq]; omega
    c0_hsplit
    · have hlv_bd : ((ot >>> 1).setWidth 64).toNat < (m8SBlkSt s s.core.tmp mrk_c mclr_c
          sstk_c wsort_c mcl_c mcf_c ticks_c).core.lvl.length := by
        dsimp only [m8SBlkSt, Spec.m8ShrinkBlkBoolState]; rw [hlen0.lvl_len, bv_c0_zext32_64]; omega
      c0_hsplit
      · have hmrk_bd : ((ot >>> 1).setWidth 64).toNat < (m8SBlkSt s s.core.tmp mrk_c mclr_c
            sstk_c wsort_c mcl_c mcf_c ticks_c).core.mrk.length := by
          dsimp only [m8SBlkSt, Spec.m8ShrinkBlkBoolState]
          rw [hinv_c.base.mrk_len, bv_c0_zext32_64]; omega
        c0_hsplit
        · have h8_ov : (mrk_c[(ot >>> 1).toNat]?.getD 0#8 &&& 8#8) = 0#8 := by
            rw [bv32_lshr_1, List.getElem?_eq_getElem
              (by rw [hinv_c.base.mrk_len]; rw [bv32_lshr_1] at hov_lt; omega), Option.getD_some]
            exact bv8_and8_eq0_c0 hc
          refine wp_join_group (ts := [i64, i64, .bool])
            (fun (op_2, sl_2, f_2, ()) m_2 =>
              ∃ mrk_2 mclr_2 sstk_2 wsort_2 mcl_2 mcf_2 ticks_2,
                M8ShrinkClInv c F0 s blvl beg.toNat end_b.toNat keepLen s.core.mrk slen_n t_uip
                  uip rsn is_bin op_2.toNat sl_2.toNat (j_n + 1) f_2 mrk_2 mclr_2 sstk_2 wsort_2
                  mcl_2 mcf_2 ticks_2 ∧
                (FullMem c (m8SBlkSt s s.core.tmp mrk_2 mclr_2 sstk_2 wsort_2 mcl_2 mcf_2
                  ticks_2) ⋆ R) m_2) ?_ ?_
          · rintro J2 ⟨op_2, sl_2, f_2, ⟨⟩⟩ m_2 h_in
            rw [Blocks.get_here]; c0_hsteps!; exact hJ1 (op_2, sl_2, f_2, ()) m_2 h_in
          · intro J2 hJ2; c0_hsplit
            · obtain ⟨m, hm, hmeq, _⟩ := hq_src.resolve_left (by
                rw [← hot_eq]; exact fun heq => hne_u (BitVec.eq_of_toNat_eq heq))
              have hlt_b : (s.core.lvl[ot.toNat / 2]?.getD 0#32).toNat < blvl.toNat := by
                rw [List.getElem?_eq_getElem (by rw [hlen0.lvl_len]; omega), Option.getD_some]
                exact hc
              have hov_lvl_lt : (s.core.lvl[(ot >>> 1).toNat]?.getD 0#32).toNat <
                  s.core.cur_level := by rw [bv32_lshr_1]; omega
              have hval_ot : (m8SBlkSt s s.core.tmp mrk_c mclr_c sstk_c wsort_c mcl_c mcf_c
                  ticks_c).core.vals[ot.toNat]?.getD 0#8 = 0xFF#8 := by
                obtain ⟨_, hw⟩ := hcore.2
                exact (hw.vals_false_iff ot.toNat (hot_eq ▸ hq_lt2v)).mpr
                  ⟨m, by omega, hot_eq ▸ hmeq⟩
              have hno8_ov := m8ShrinkOkInv_lvl_lt_no8 (ov := (ot >>> 1).toNat)
                (fun w hw h8 => (h8_c w hw h8).1) (by rw [bv32_lshr_1]; exact hlt_b)
              refine wp_join_group (ts := [.bool]) (fun (fb, ()) m_fb =>
                ∃ mrk2 mclr2 sstk2 wsort2 mcl2 mcf2 ticks2,
                  M8ShrinkClInv c F0 s blvl beg.toNat end_b.toNat keepLen s.core.mrk slen_n t_uip
                    uip rsn is_bin op_c.toNat sl_c.toNat (j_n + 1) fb mrk2 mclr2 sstk2 wsort2 mcl2
                    mcf2 ticks2 ∧
                  (FullMem c (m8SBlkSt s s.core.tmp mrk2 mclr2 sstk2 wsort2 mcl2 mcf2
                    ticks2) ⋆ R) m_fb) ?_ ?_
              · rintro J2b ⟨fb, ⟨⟩⟩ m_fb h_fb
                rw [Blocks.get_here]; c0_hsteps!; exact hJ2 (op_c, sl_c, fb, ()) m_fb h_fb
              · intro J2b hJ2b
                c0_hsteps!; apply wp_call_of_spec; apply hSL
                refine Spec.fullShrinkLowerSpec_of
                  (m8ShrinkBaseInv_core (ticks := ticks_c) hcore hinv_c.base)
                  hinv_c.base.min_inv (bv32_lshr_1 ot) (hot_eq ▸ hq_lt2v) hval_ot hov_lvl_lt
                  hno8_ov hm_c fun ok_l mrk2 wsort2 mclr2 mcl2 mcf2 ticks2 m2 hlok hab hm2 hm8
                    hmin2 hgot2 hm_2 => by
                  c0_hsplit
                  · have hot_t : ok_l = true := hc
                    c0_hsteps!; exact hJ2b (false, ()) m2 ⟨mrk2, mclr2, sstk_c, wsort2, mcl2, mcf2,
                      ticks2, m8Shrink_cl_step_lower_ok hcore ht_te hblk_lt hinv_c hot_eq
                        ⟨m, hm, hot_eq ▸ hmeq⟩ hlok hab hm2 hm8 hmin2 (hgot2 hot_t), hm_2⟩
                  · c0_hsteps!; exact hJ2b (true, ()) m2 ⟨mrk2, mclr2, sstk_c, wsort2, mcl2, mcf2,
                      ticks2, m8Shrink_cl_step_fail hinv_c hlok hab hm2 hm8 hmin2, hm_2⟩
            · refine wp_join_group (ts := [i64, i64, .bool])
                (fun (op_e, sl_e, f_e, ()) m_e =>
                  ∃ mrk_e mclr_e sstk_e wsort_e mcl_e mcf_e ticks_e,
                    M8ShrinkClInv c F0 s blvl beg.toNat end_b.toNat keepLen s.core.mrk slen_n
                      t_uip uip rsn is_bin op_e.toNat sl_e.toNat (j_n + 1) f_e mrk_e mclr_e
                      sstk_e wsort_e mcl_e mcf_e ticks_e ∧
                    (FullMem c (m8SBlkSt s s.core.tmp mrk_e mclr_e sstk_e wsort_e mcl_e mcf_e
                      ticks_e) ⋆ R) m_e) ?_ ?_
              · rintro J2e ⟨op_e, sl_e, f_e, ⟨⟩⟩ m_e h_e
                rw [Blocks.get_here]; c0_hsteps!; exact hJ2 (op_e, sl_e, f_e, ()) m_e h_e
              · intro J2e hJ2e; c0_hsplit
                · have heq_b : (s.core.lvl[ot.toNat / 2]?.getD 0#32).toNat = blvl.toNat := by
                    rw [List.getElem?_eq_getElem (by rw [hlen0.lvl_len]; omega), Option.getD_some]
                    exact congrArg BitVec.toNat hc
                  c0_hsplit
                  · have hcv_sl : sl_c.toNat < s.core.cur_vars := by c0_grind
                    have hmrk_w : ((ot >>> 1).setWidth 64).toNat < (m8SBlkSt s s.core.tmp mrk_c
                        mclr_c sstk_c wsort_c mcl_c mcf_c ticks_c).core.mrk.length := by
                      rw [bv_c0_zext32_64, hinv_c.base.mrk_len]; omega
                    let mrk_p := mrk_c.set (ot >>> 1).toNat
                      (mrk_c[(ot >>> 1).toNat]?.getD 0#8 ||| 8#8)
                    have hsl_c_bd : sl_c.toNat < (m8SBlkSt s s.core.tmp mrk_p mclr_c sstk_c
                        wsort_c mcl_c mcf_c ticks_c).scratch.shrink_stk.length := by
                      rw [hinv_c.base.sstk_len]; omega
                    c0_hsteps!
                    rw [m8SBlk_st_mrk_eq s s.core.tmp mrk_c mclr_c sstk_c wsort_c mcl_c mcf_c
                      ticks_c (by rw [bv_c0_zext32_64])] at hm
                    have hget_mp : mrk_c[(ot >>> 1).toNat] =
                        mrk_c[(ot >>> 1).toNat]?.getD 0#8 := by
                      rw [List.getElem?_eq_getElem (by rw [hinv_c.base.mrk_len]; omega),
                        Option.getD_some]
                    have hm_p : (FullMem c (m8SBlkSt s s.core.tmp mrk_p mclr_c
                        (sstk_c.set sl_c.toNat (ot >>> 1)) wsort_c mcl_c mcf_c
                        ticks_c) ⋆ R) m := by
                      rw [m8SBlk_st_sstk_eq s s.core.tmp _ mclr_c sstk_c wsort_c mcl_c mcf_c
                        ticks_c rfl] at hm
                      simpa only [bv_c0_zext32_64, bv8_or8_c0', hget_mp] using hm
                    obtain ⟨m0, hm0, hmeq, _⟩ := hq_src.resolve_left (by
                      rw [← hot_eq]; exact fun heq => hne_u (BitVec.eq_of_toNat_eq heq))
                    have hopl_c := (hinv_c.ok rfl).2.2.2.2.2.1; have := hinv_c.base.slen_le
                    have := hend_mv
                    have hop1' : (op_c + 1).toNat = op_c.toNat + 1 := by c0_bound
                    have hsl1' : (sl_c + 1).toNat = sl_c.toNat + 1 := by c0_bound
                    refine hJ2e (op_c + 1, sl_c + 1, false, ()) m
                      ⟨mrk_p, mclr_c, _, wsort_c, mcl_c, mcf_c, ticks_c, ?_, hm_p⟩
                    rw [hop1', hsl1']
                    exact m8Shrink_cl_step_push hcore ht_te hblk_lt hinv_c hot_eq
                      (hot_eq ▸ hq_lt2v) ⟨m0, hm0, hot_eq ▸ hmeq⟩ heq_b hcv_sl
                  · c0_hsteps!; exact hJ2e (op_c, sl_c, true, ()) m_c ⟨mrk_c, mclr_c, sstk_c,
                      wsort_c, mcl_c, mcf_c, ticks_c,
                      ⟨hinv_c.base, hinv_c.mono2_prev, fun h => by cases h⟩, hm_c⟩
                · c0_hsteps!; exact hJ2e (op_c, sl_c, true, ()) m_c ⟨mrk_c, mclr_c, sstk_c, wsort_c,
                    mcl_c, mcf_c, ticks_c,
                    ⟨hinv_c.base, hinv_c.mono2_prev, fun h => by cases h⟩, hm_c⟩
        · c0_hsteps!; refine hJ1 (op_c, sl_c, false, ()) m_c ⟨mrk_c, mclr_c, sstk_c, wsort_c,
              mcl_c, mcf_c, ticks_c, ?_, hm_c⟩
          have h8nz : (mrk_c[ot.toNat / 2]?.getD 0#8 &&& 8#8) ≠ 0#8 := by
            rw [List.getElem?_eq_getElem
              (by rw [hinv_c.base.mrk_len]; rw [bv32_lshr_1] at hov_lt; omega), Option.getD_some]
            exact bv8_and8_ne0_c0 hc
          obtain ⟨m, hm, hmeq, _⟩ := hq_src.resolve_left (by
            rw [← hot_eq]; exact fun heq => hne_u (BitVec.eq_of_toNat_eq heq))
          exact m8Shrink_cl_step_skip hcore ht_te hinv_c hot_eq
            (Or.inr ⟨m, hm, hot_eq ▸ hmeq, Or.inr h8nz⟩) hueq
      · c0_hsteps!; refine hJ1 (op_c, sl_c, false, ()) m_c ⟨mrk_c, mclr_c, sstk_c, wsort_c, mcl_c,
            mcf_c, ticks_c, ?_, hm_c⟩
        have hl0 : (s.core.lvl[ot.toNat / 2]?.getD 0#32).toNat = 0 := by
          have hgv : (s.core.lvl[ot.toNat / 2]?.getD 0#32).toNat =
              (s.core.lvl[ot.toNat / 2]'(by rw [hlen0.lvl_len]; omega)).toNat := by
            rw [List.getElem?_eq_getElem (by rw [hlen0.lvl_len]; omega), Option.getD_some]
          rw [hgv]; c0_grind
        obtain ⟨m, hm, hmeq, _⟩ := hq_src.resolve_left (by
          rw [← hot_eq]; exact fun heq => hne_u (BitVec.eq_of_toNat_eq heq))
        exact m8Shrink_cl_step_skip hcore ht_te hinv_c hot_eq
          (Or.inr ⟨m, hm, hot_eq ▸ hmeq, Or.inl hl0⟩) hueq
    · exfalso; c0_grind
  · c0_hsteps!; refine hJ1 (op_c, sl_c, false, ()) m_c ⟨mrk_c, mclr_c, sstk_c, wsort_c, mcl_c,
        mcf_c, ticks_c, ?_, hm_c⟩
    exact m8Shrink_cl_step_skip hcore ht_te hinv_c hot_eq (Or.inl (congrArg BitVec.toNat hc)) hueq

private theorem m8_shrink_cl_loop_wp {Γ : Env} {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    {blvl uip rsn csz_h : BitVec 32} {beg end_b : BitVec 64} {keepLen t_uip : Nat}
    {open_i slen_i ticks_h : BitVec 64} {mrk_i : List (BitVec 8)}
    {mclr_i sstk_i wsort_i : List (BitVec 32)} {mcl_i : Nat} {mcf_i : BitVec 64}
    {is_bin f_hdr : Bool} {cv_v : BitVec 64}
    {R : Mem 64 → Prop} {m_hdr : Mem 64} {Q : Post [.bool]} {X : XPost}
    {kAfter : Val i64 → Val i64 → Val .bool → Expr Val Cont [.bool]}
    (hSL : Γ.Has "full_shrink_lower_m8" Spec.fullShrinkLowerSpec) (hcore : FullOtfsCoreInv c F0 s)
    (hblvl_lt : blvl.toNat < s.core.cur_level) (hcv_eq : cv_v = BitVec.ofNat 64 s.core.cur_vars)
    (ht_te : t_uip < s.core.trail_end) (hend_mv : end_b.toNat ≤ c.max_vars)
    (hueq : (s.core.trl[t_uip]?.getD 0#32).toNat = uip.toNat)
    (hblk_lt : ∀ j, beg.toNat ≤ j → j < end_b.toNat →
      (s.core.tmp[j]?.getD 0#32).toNat / 2 < s.core.cur_vars)
    (hbig_f : is_bin = false → rsn.toNat ∈ fullArenaClauseRefsCore s.core ∧
      fullArenaClauseGarbCore s.core rsn.toNat = false ∧
      rsn.toNat + 3 ≤ s.core.arena_len ∧ 3 ≤ fullArenaClauseSizeCore s.core rsn.toNat ∧
      rsn.toNat + 3 + fullArenaClauseSizeCore s.core rsn.toNat ≤ s.core.arena_len)
    (hq_inv : ∀ k < (if is_bin then 1 else fullArenaClauseSizeCore s.core rsn.toNat),
      let q := m8ShrinkRsnLit s rsn is_bin k
      q < 2 * s.core.cur_vars ∧
      (q = uip.toNat ∨ ∃ m < t_uip, (s.core.trl[m]?.getD 0#32).toNat = q ^^^ 1 ∧
        (s.core.lvl[q / 2]?.getD 0#32).toNat ≤ blvl.toNat))
    (hcsz_h : f_hdr = false → (is_bin = true → csz_h = 1#32) ∧
      (is_bin = false → csz_h.toNat = fullArenaClauseSizeCore s.core rsn.toNat))
    (hf_hdr_eq : f_hdr = false) (hb_i : M8ShrinkBaseInv c s mrk_i mclr_i sstk_i wsort_i mcl_i
      mcf_i slen_i.toNat (((s.core.tmp.take keepLen).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat))
    (hblk_i : M8ShrinkBlk8 s mrk_i beg.toNat end_b.toNat)
    (hstk_i : M8ShrinkStk8 mrk_i sstk_i slen_i.toNat)
    (h8_a : M8ShrinkAll8 s blvl mrk_i (t_uip - 1) t_uip)
    (hcnt_a : trailCount8 s.core.trl mrk_i t_uip ≤ open_i.toNat - 1)
    (hop2 : 2 ≤ open_i.toNat) (hopl : open_i.toNat ≤ (end_b.toNat - beg.toNat) + slen_i.toNat)
    (hm_hdr : (FullMem c (m8SBlkSt s s.core.tmp mrk_i mclr_i sstk_i wsort_i mcl_i mcf_i
      ticks_h) ⋆ R) m_hdr)
    (hk : ∀ op_c sl_c f_c mrk_c mclr_c sstk_c wsort_c mcl_c mcf_c ticks_c m_c,
      (f_c = false → M8ShrinkCovAt s mrk_c t_uip rsn is_bin 0 →
        ∀ j < csz_h.toNat, M8ShrinkCovAt s mrk_c t_uip rsn is_bin j) →
      M8ShrinkClInv c F0 s blvl beg.toNat end_b.toNat keepLen s.core.mrk slen_i.toNat t_uip
        uip rsn is_bin op_c.toNat sl_c.toNat csz_h.toNat f_c mrk_c mclr_c sstk_c wsort_c
        mcl_c mcf_c ticks_c →
      (FullMem c (m8SBlkSt s s.core.tmp mrk_c mclr_c sstk_c wsort_c mcl_c mcf_c ticks_c) ⋆ R)
        m_c →
      wp Γ Q X (kAfter op_c sl_c f_c) m_c) :
    wp Γ Q X (m8ShrinkClLoopExpr c.hdr c.pMark c.pLevel c.pShrinkStk c.pArena cv_v
      is_bin uip rsn csz_h open_i slen_i f_hdr blvl kAfter)
      m_hdr := by
  subst hf_hdr_eq
  have hlen0 := hcore.1.core_ok; have hcv := hlen0.cur_vars_le
  have hmx := c.hmaxv; unfold Ref.dimacsBound at hmx
  subst hcv_eq; dsimp only [m8ShrinkClLoopExpr]
  refine wp_loop_group (ts := [i64, i64, .bool, i32])
    (fun nc (op_c, sl_c, f_c, j_c, ()) m_c =>
      ∃ mrk_c mclr_c sstk_c wsort_c mcl_c mcf_c ticks_c,
        nc = csz_h.toNat - j_c.toNat ∧ j_c.toNat ≤ csz_h.toNat ∧
        M8ShrinkClInv c F0 s blvl beg.toNat end_b.toNat keepLen s.core.mrk slen_i.toNat t_uip
          uip rsn is_bin op_c.toNat sl_c.toNat j_c.toNat f_c mrk_c mclr_c sstk_c wsort_c
          mcl_c mcf_c ticks_c ∧
        (FullMem c (m8SBlkSt s s.core.tmp mrk_c mclr_c sstk_c wsort_c mcl_c mcf_c ticks_c) ⋆ R)
          m_c) ?_ ?_
  · rintro Lc nc ⟨op_c, sl_c, f_c, j_c, ⟨⟩⟩ m_c hLc
      ⟨mrk_c, mclr_c, sstk_c, wsort_c, mcl_c, mcf_c, ticks_c, rfl, hj_le, hinv_c, hm_c⟩
    rw [Blocks.get_here]
    refine wp_join_group (ts := []) (fun _ m_k => m_k = m_c ∧
      ∃ mrk_k mclr_k sstk_k wsort_k mcl_k mcf_k ticks_k,
        (f_c = false → M8ShrinkCovAt s mrk_k t_uip rsn is_bin 0 →
          ∀ j < csz_h.toNat, M8ShrinkCovAt s mrk_k t_uip rsn is_bin j) ∧
        M8ShrinkClInv c F0 s blvl beg.toNat end_b.toNat keepLen s.core.mrk slen_i.toNat t_uip
          uip rsn is_bin op_c.toNat sl_c.toNat csz_h.toNat f_c mrk_k mclr_k sstk_k wsort_k
          mcl_k mcf_k ticks_k ∧
        (FullMem c (m8SBlkSt s s.core.tmp mrk_k mclr_k sstk_k wsort_k mcl_k mcf_k ticks_k) ⋆ R)
          m_k) ?_ ?_
    · rintro Js1 ⟨⟩ m_k ⟨rfl, mrk_k, mclr_k, sstk_k, wsort_k, mcl_k, mcf_k, ticks_k, hcov_k,
          hinv_k, hm_k⟩
      rw [Blocks.get_here]
      exact hk op_c sl_c f_c mrk_k mclr_k sstk_k wsort_k mcl_k mcf_k ticks_k m_k hcov_k hinv_k hm_k
    · intro Js1 hJs1; c0_hsplit
      · have hj_lt : j_c.toNat < csz_h.toNat := by c0_grind
        c0_hsplit
        · subst hc
          c0_hsteps!; exact hJs1 () m_c ⟨rfl, mrk_c, mclr_c, sstk_c, wsort_c, mcl_c, mcf_c,
            ticks_c, (fun hf => by cases hf),
            ⟨hinv_c.base, hinv_c.mono2_prev, fun h => by cases h⟩, hm_c⟩
        · have hf_false : f_c = false := hc
          subst hf_false
          obtain ⟨_, _, h8_c, _, _, _, _⟩ := hinv_c.ok rfl
          have hcsz_e : j_c.toNat <
              if is_bin then 1 else fullArenaClauseSizeCore s.core rsn.toNat := by
            cases hb_v : is_bin with
            | true => rw [(hcsz_h rfl).1 hb_v] at hj_lt; exact hj_lt
            | false => rw [(hcsz_h rfl).2 hb_v] at hj_lt; exact hj_lt
          obtain ⟨hq_lt2v, hq_src⟩ := hq_inv j_c.toNat hcsz_e
          refine wp_join_group (ts := [i32])
            (fun (ot, _) m_ot => m_ot = m_c ∧ ot.toNat = m8ShrinkRsnLit s rsn is_bin j_c.toNat)
            ?_ ?_
          · rintro Jot ⟨ot, ⟨⟩⟩ m_ot ⟨hm_ot, hot_eq⟩; subst m_ot; rw [Blocks.get_here]
            c0_hsteps_nogrp
            refine wp_join_group (ts := [i64, i64, .bool])
              (fun (op_1, sl_1, f_1, ()) m_1 =>
                ∃ mrk_1 mclr_1 sstk_1 wsort_1 mcl_1 mcf_1 ticks_1,
                  M8ShrinkClInv c F0 s blvl beg.toNat end_b.toNat keepLen s.core.mrk slen_i.toNat
                    t_uip uip rsn is_bin op_1.toNat sl_1.toNat (j_c.toNat + 1) f_1 mrk_1 mclr_1
                    sstk_1 wsort_1 mcl_1 mcf_1 ticks_1 ∧
                  (FullMem c (m8SBlkSt s s.core.tmp mrk_1 mclr_1 sstk_1 wsort_1 mcl_1 mcf_1
                    ticks_1) ⋆ R) m_1) ?_ ?_
            · rintro J1 ⟨op_1, sl_1, f_1, ⟨⟩⟩ m_1
                ⟨mrk_1, mclr_1, sstk_1, wsort_1, mcl_1, mcf_1, ticks_1, hinv_1, hm_1⟩
              rw [Blocks.get_here]; c0_hsteps!
              have hj1 : (j_c + 1#32).toNat = j_c.toNat + 1 := by
                cases hb_v : is_bin
                · have := (hbig_f hb_v).2.2.2.2
                  have : j_c.toNat < fullArenaClauseSizeCore s.core rsn.toNat := by
                    simpa [hb_v] using hcsz_e
                  have := hlen0.arena_len_le; exact min_bv32_add1_toNat (by omega)
                · have := hcsz_e; simp [hb_v] at this; exact min_bv32_add1_toNat (by omega)
              exact hLc (csz_h.toNat - (j_c + 1#32).toNat) (op_1, sl_1, f_1, j_c + 1#32, ()) m_1
                (by rw [hj1]; omega) ⟨mrk_1, mclr_1, sstk_1, wsort_1, mcl_1, mcf_1, ticks_1, rfl,
                  by rw [hj1]; omega, by rw [hj1]; exact hinv_1, hm_1⟩
            · intro J1 hJ1
              exact m8_shrink_cl_check_wp hSL hcore hblvl_lt ht_te hend_mv hueq hblk_lt hot_eq
                hq_lt2v hq_src hinv_c h8_c hm_c hJ1
          · intro Jot hJot; c0_hsplit
            · have hibt : is_bin = true := hc
              c0_hsteps!; exact hJot (rsn &&& 2147483647#32, ()) m_c
                ⟨rfl, by dsimp only [m8ShrinkRsnLit]; simp only [hibt, ↓reduceIte]⟩
            · have hibf : is_bin = false := hc
              have har_bd : (rsn.setWidth 64 + 3 + j_c.setWidth 64).toNat < (m8SBlkSt s s.core.tmp
                  mrk_c mclr_c sstk_c wsort_c mcl_c mcf_c ticks_c).core.arena.length := by
                rw [bv64_zext32_add3_add]; dsimp only [m8SBlkSt, Spec.m8ShrinkBlkBoolState]
                rw [hlen0.arena_len_arr]; have := (hbig_f hibf).2.2.2.2
                have := hlen0.arena_len_le; simp [hibf] at hcsz_e; omega
              c0_hsteps!
              refine hJot
                (s.core.arena[(rsn.setWidth 64 + 3 + j_c.setWidth 64).toNat]'har_bd, ()) m_c
                ⟨rfl, ?_⟩
              dsimp only [m8ShrinkRsnLit]; simp only [hibf, Bool.false_eq_true, ↓reduceIte]
              rw [List.getElem?_eq_getElem (by
                simpa only [m8SBlkSt, Spec.m8ShrinkBlkBoolState, bv64_zext32_add3_add]
                  using har_bd), Option.getD_some]
              simp only [bv64_zext32_add3_add]
      · have hj_eq : j_c.toNat = csz_h.toNat := by c0_grind
        rw [hj_eq] at hinv_c
        c0_hsteps!; exact hJs1 () m_c ⟨rfl, mrk_c, mclr_c, sstk_c, wsort_c, mcl_c, mcf_c, ticks_c,
          (fun hf _ j hj => (hinv_c.ok hf).2.2.2.2.2.2 j hj), hinv_c, hm_c⟩
  · intro Lc hLc; c0_hsteps!
    exact hLc csz_h.toNat (open_i, slen_i, false, 0#32, ()) m_hdr
      ⟨mrk_i, mclr_i, sstk_i, wsort_i, mcl_i, mcf_i, ticks_h, by simp, Nat.zero_le _,
        ⟨hb_i, hb_i.mono2, fun _ => ⟨hblk_i, hstk_i, h8_a, hcnt_a, hop2, hopl,
          fun _ hk => by simp at hk⟩⟩, hm_hdr⟩

private theorem m8_shrink_blk_cl_iter_wp {Γ : Env} {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    {blvl uip_a rsn csz_h : BitVec 32} {beg end_b open_i slen_i t_a ticks_h : BitVec 64}
    {keepLen : Nat} {mrk_i : List (BitVec 8)} {mclr_i sstk_i wsort_i : List (BitVec 32)}
    {mcl_i : Nat} {mcf_i : BitVec 64} {is_bin : Bool}
    {R : Mem 64 → Prop} {m_hdr : Mem 64} {Q : Post [.bool]} {X : XPost}
    {L : Cont [i64, i64, .bool, i32, i64]}
    (hSL : Γ.Has "full_shrink_lower_m8" Spec.fullShrinkLowerSpec) (hcore : FullOtfsCoreInv c F0 s)
    (hblvl_lt : blvl.toNat < s.core.cur_level) (hte : t_a.toNat < s.core.trail_end)
    (ht_pos' : 0 < t_a.toNat) (htm1 : (t_a - 1).toNat = t_a.toNat - 1)
    (hend_mv : end_b.toNat ≤ c.max_vars)
    (hueq : (s.core.trl[t_a.toNat]?.getD 0#32).toNat = uip_a.toNat)
    (hulvl : (s.core.lvl[uip_a.toNat / 2]?.getD 0#32).toNat = blvl.toNat)
    (hblk_lt : ∀ j, beg.toNat ≤ j → j < end_b.toNat →
      (s.core.tmp[j]?.getD 0#32).toNat / 2 < s.core.cur_vars)
    (hrsn_ne : rsn ≠ 0xFFFFFFFF#32)
    (hrsn_eq : rsn = s.core.rsns[(s.core.trl[t_a.toNat]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32)
    (his_bin : (is_bin = true) ↔ (rsn &&& 0x80000000#32) ≠ 0#32)
    (hbig_f : is_bin = false → rsn.toNat ∈ fullArenaClauseRefsCore s.core ∧
      fullArenaClauseGarbCore s.core rsn.toNat = false ∧
      rsn.toNat + 3 ≤ s.core.arena_len ∧ 3 ≤ fullArenaClauseSizeCore s.core rsn.toNat ∧
      rsn.toNat + 3 + fullArenaClauseSizeCore s.core rsn.toNat ≤ s.core.arena_len)
    (hq_inv : ∀ k < (if is_bin then 1 else fullArenaClauseSizeCore s.core rsn.toNat),
      let q := m8ShrinkRsnLit s rsn is_bin k
      q < 2 * s.core.cur_vars ∧
      (q = uip_a.toNat ∨ ∃ m < t_a.toNat, (s.core.trl[m]?.getD 0#32).toNat = q ^^^ 1 ∧
        (s.core.lvl[q / 2]?.getD 0#32).toNat ≤ blvl.toNat))
    (hcsz_h : false = false → (is_bin = true → csz_h = 1#32) ∧
      (is_bin = false → csz_h.toNat = fullArenaClauseSizeCore s.core rsn.toNat))
    (hb_i : M8ShrinkBaseInv c s mrk_i mclr_i sstk_i wsort_i mcl_i mcf_i slen_i.toNat
      (((s.core.tmp.take keepLen).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat))
    (hblk_i : M8ShrinkBlk8 s mrk_i beg.toNat end_b.toNat)
    (hstk_i : M8ShrinkStk8 mrk_i sstk_i slen_i.toNat)
    (h8_a : M8ShrinkAll8 s blvl mrk_i (t_a.toNat - 1) t_a.toNat)
    (hcnt_a : trailCount8 s.core.trl mrk_i t_a.toNat ≤ open_i.toNat - 1)
    (hop2 : 2 ≤ open_i.toNat) (hopl : open_i.toNat ≤ (end_b.toNat - beg.toNat) + slen_i.toNat)
    (hm_hdr : (FullMem c (m8SBlkSt s s.core.tmp mrk_i mclr_i sstk_i wsort_i mcl_i mcf_i
      ticks_h) ⋆ R) m_hdr)
    (hL : ∀ n' ys m', n' < t_a.toNat →
      (match ys with
        | (open_n, slen_n, failed_n, _uip_n, t_n, ()) =>
          n' = t_n.toNat ∧
          ∃ mrk_n mclr_n sstk_n wsort_n mcl_n mcf_n ticks_n,
            M8ShrinkBaseInv c s mrk_n mclr_n sstk_n wsort_n mcl_n mcf_n slen_n.toNat
              (((s.core.tmp.take keepLen).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat) ∧
            (failed_n = false → M8ShrinkStk8 mrk_n sstk_n slen_n.toNat ∧ 1 ≤ open_n.toNat ∧
              open_n.toNat ≤ (end_b.toNat - beg.toNat) + slen_n.toNat ∧
              M8ShrinkBlk8 s mrk_n beg.toNat end_b.toNat ∧
              M8ShrinkAll8 s blvl mrk_n t_n.toNat s.core.trail_end ∧
              trailCount8 s.core.trl mrk_n (min (t_n.toNat + 1) s.core.trail_end) ≤
                open_n.toNat) ∧
            (FullMem c (m8SBlkSt s s.core.tmp mrk_n mclr_n sstk_n wsort_n mcl_n mcf_n ticks_n) ⋆
              R) m') → L ys m') :
    wp Γ Q X (m8ShrinkClLoopExpr c.hdr c.pMark c.pLevel c.pShrinkStk c.pArena
      (BitVec.ofNat 64 s.core.cur_vars) is_bin uip_a rsn csz_h open_i slen_i false blvl
      (fun op_k sl_k f_k =>
        .group (sig := [[i64]]) (fun _Jo => .cons (fun op_d =>
          .jump L (.var op_d.fst, .var sl_k, .var f_k, .var uip_a, .var (t_a - 1), ())) .nil)
          fun Jo =>
          .jnz (.var f_k) (.jump Jo.fst (.var op_k, ()))
            (.let_ (Op.mk (.sub i64) (.var op_k, .imm 1, ())) fun op1 =>
             .jump Jo.fst (.var op1.fst, ())))) m_hdr := by
  refine m8_shrink_cl_loop_wp (Q := Q) (X := X) (uip := uip_a) (rsn := rsn) (csz_h := csz_h)
    (open_i := open_i) (slen_i := slen_i) (is_bin := is_bin) (f_hdr := false)
    (cv_v := BitVec.ofNat 64 s.core.cur_vars)
    hSL hcore hblvl_lt rfl hte hend_mv hueq hblk_lt hbig_f hq_inv hcsz_h rfl hb_i
    hblk_i hstk_i h8_a hcnt_a hop2 hopl hm_hdr ?_
  rintro op_c sl_c f_c mrk_c mclr_c sstk_c wsort_c mcl_c mcf_c ticks_c m_c _ hinv hm_c
  refine wp_join_group (ts := [i64])
    (fun (op_d, ()) m_d => m_d = m_c ∧
      (f_c = false → M8ShrinkStk8 mrk_c sstk_c sl_c.toNat ∧
        1 ≤ op_d.toNat ∧ op_d.toNat ≤ (end_b.toNat - beg.toNat) + sl_c.toNat ∧
        M8ShrinkBlk8 s mrk_c beg.toNat end_b.toNat ∧
        M8ShrinkAll8 s blvl mrk_c (t_a - 1).toNat s.core.trail_end ∧
        trailCount8 s.core.trl mrk_c (min ((t_a - 1).toNat + 1) s.core.trail_end) ≤
          op_d.toNat)) ?_ ?_
  · rintro Jo ⟨op_d, ⟨⟩⟩ m_d ⟨hm_d, hok_d⟩; subst m_d; rw [Blocks.get_here]; c0_hsteps!
    exact hL (t_a - 1).toNat (op_d, sl_c, f_c, uip_a, t_a - 1, ()) m_c (by omega)
      ⟨rfl, mrk_c, mclr_c, sstk_c, wsort_c, mcl_c, mcf_c, ticks_c, hinv.base, hok_d, hm_c⟩
  · intro Jo hJo; c0_hsplit
    · have hft : f_c = true := hc
      c0_hsteps!; exact hJo (op_c, ()) m_c ⟨rfl, fun hf => by cases (hft.symm.trans hf)⟩
    · have hfc : f_c = false := hc
      obtain ⟨hblk_c, hstk_c, h8_c, hcnt_c, hop2_c, hopl_c, hcov_c⟩ := hinv.ok hfc
      have hop1 : (op_c - 1).toNat = op_c.toNat - 1 := by c0_bound
      have hcsz_cov : ∀ j < (if is_bin then 1 else fullArenaClauseSizeCore s.core rsn.toNat),
          M8ShrinkCovAt s mrk_c t_a.toNat rsn is_bin j := fun j hj =>
        hcov_c j (by
          cases hb_v : is_bin
          · rw [hb_v] at hj; rw [(hcsz_h rfl).2 hb_v]; exact hj
          · rw [hb_v] at hj; rw [(hcsz_h rfl).1 hb_v]; exact hj)
      obtain ⟨h8_aft, hcnt_aft⟩ := m8Shrink_cl_after_step hcore hte ht_pos' hueq hulvl hblvl_lt
        hrsn_ne hrsn_eq his_bin hcsz_cov h8_c hcnt_c
      c0_hsteps!; exact hJo (op_c - 1, ()) m_c ⟨rfl, fun _ =>
        ⟨hstk_c, by rw [hop1]; omega, by rw [hop1]; omega, hblk_c,
          by rw [htm1]; exact h8_aft, by rw [htm1, hop1]; exact hcnt_aft⟩⟩

/-! ## 3. Main WP Theorem: `full_shrink_blk_bool_m8_wp` -/

public section

theorem full_shrink_blk_bool_m8_wp (Γ : Env)
    (hMm : Γ.Has "full_min_mark" Spec.fullMinMarkSpec)
    (hSL : Γ.Has "full_shrink_lower_m8" Spec.fullShrinkLowerSpec) :
    ∀ args m Q X, Spec.fullShrinkBlkBoolSpec args m Q X →
      Func.wp Γ full_shrink_blk_bool_m8_body args m Q X := by
  rintro ⟨h, beg, end_b, blvl, max_tr, ⟨⟩⟩ m Q X hsp
  obtain ⟨c, F0, s, keepLen, R, rfl, hcore, hmin, hno8, hbeg1, hbeg_end, hend_kl, hkl_cv,
      hblvl_pos, hblvl_lt, hblk, hkeep, hm, hQ⟩ := Spec.fullShrinkBlkBoolSpec_elim hsp
  unfold Func.wp full_shrink_blk_bool_m8_body; dsimp only [full_shrink_blk_bool_m8_body]
  have hlen0 := hcore.1.core_ok; have hcv := hlen0.cur_vars_le
  have hmx := c.hmaxv; have har := c.harena; unfold Ref.dimacsBound at hmx har
  have hblk_lt : ∀ j, beg.toNat ≤ j → j < end_b.toNat →
      (s.core.tmp[j]?.getD 0#32).toNat / 2 < s.core.cur_vars := fun j hj1 hj2 => by
    have := (hblk j hj1 hj2).1; omega
  let keep0 := ((s.core.tmp.take keepLen).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat
  c0_hsteps_nogrp
  have hb0 : M8ShrinkBaseInv c s s.core.mrk s.core.min_clr s.scratch.shrink_stk s.scratch.wsort
      s.core.min_clr_len s.core.min_clr_full 0 keep0 :=
    ⟨hlen0.mrk_len, hlen0.min_clr_len_arr, hlen0.min_clr_len_le, hcore.1.scratch_ok.shrink_stk_len,
      hcore.1.scratch_ok.wsort_len, Nat.zero_le _, fun _ _ => rfl, hmin, fun _ _ h => h,
      fun w hw h8w => absurd (hno8 w hw) h8w, fun _ hj => by cases hj⟩
  refine wp_loop_group (ts := [i64, i64]) (fun n (slen, k, ()) m_1 =>
      n = end_b.toNat - k.toNat ∧ beg.toNat ≤ k.toNat ∧ k.toNat ≤ end_b.toNat ∧
      slen.toNat = k.toNat - beg.toNat ∧
      ∃ mrk1 sstk1, M8ShrinkBaseInv c s mrk1 s.core.min_clr sstk1 s.scratch.wsort
        s.core.min_clr_len s.core.min_clr_full slen.toNat keep0 ∧
        M8ShrinkStk8 mrk1 sstk1 slen.toNat ∧
        (∀ j, beg.toNat ≤ j → j < k.toNat →
          (mrk1[(s.core.tmp[j]?.getD 0#32).toNat / 2]?.getD 0#8 &&& 8#8) ≠ 0#8) ∧
        trailCount8 s.core.trl mrk1 (min (max_tr.toNat + 1) s.core.trail_end) ≤ slen.toNat ∧
        (∀ w < s.core.cur_vars, (mrk1[w]?.getD 0#8 &&& 8#8) ≠ 0#8 →
          ∃ j, beg.toNat ≤ j ∧ j < k.toNat ∧ (s.core.tmp[j]?.getD 0#32).toNat / 2 = w) ∧
        (FullMem c (m8SBlkSt s s.core.tmp mrk1 s.core.min_clr sstk1 s.scratch.wsort
          s.core.min_clr_len s.core.min_clr_full s.scratch.search_ticks) ⋆ R) m_1) ?_ ?_
  · rintro L1 n1 ⟨slen, k, ⟨⟩⟩ m_1 hL1 ⟨rfl, hbk, hke, hsl_k, mrk1, sstk1, hb1, hstk8, hbp,
        hcnt1, hno8o, hm1⟩
    rw [Blocks.get_here]; c0_hsplit
    · have hk_lt : k.toNat < end_b.toNat := by c0_grind
      have hk_arr : k.toNat < (m8SBlkSt s s.core.tmp mrk1 s.core.min_clr sstk1 s.scratch.wsort
          s.core.min_clr_len s.core.min_clr_full s.scratch.search_ticks).core.tmp.length := by
        dsimp only [m8SBlkSt, Spec.m8ShrinkBlkBoolState]; rw [hlen0.tmp_len_arr]; omega
      obtain ⟨hv_lt, hsl_arr, hb2, hstk2, hbp2, hcnt2, hno8o2⟩ := m8Shrink_init_step hcore hbk
        hk_lt hend_kl hkl_cv hblk hb1 hstk8 hbp hcnt1 hno8o hsl_k hk_arr
      let v := s.core.tmp[k.toNat]'hk_arr >>> 1
      have hvm : (v.setWidth 64).toNat < (m8SBlkSt s s.core.tmp mrk1 s.core.min_clr sstk1
          s.scratch.wsort s.core.min_clr_len s.core.min_clr_full
          s.scratch.search_ticks).core.mrk.length := by
        dsimp only [m8SBlkSt, Spec.m8ShrinkBlkBoolState] at *; rw [bv_c0_zext32_64, hb1.mrk_len]
        exact Nat.lt_of_lt_of_le hv_lt hcv
      let mrk2 := mrk1.set v.toNat (mrk1[v.toNat]?.getD 0#8 ||| 8#8)
      have hsl_len : slen.toNat < (m8SBlkSt s s.core.tmp mrk2 s.core.min_clr sstk1
          s.scratch.wsort s.core.min_clr_len s.core.min_clr_full
          s.scratch.search_ticks).scratch.shrink_stk.length := hsl_arr
      c0_hsteps!
      rw [m8SBlk_st_mrk_eq s s.core.tmp mrk1 s.core.min_clr sstk1 s.scratch.wsort s.core.min_clr_len
        s.core.min_clr_full s.scratch.search_ticks (by rw [bv_c0_zext32_64])] at hm
      have hget_m2 : mrk1[v.toNat] = mrk1[v.toNat]?.getD 0#8 := by
        rw [List.getElem?_eq_getElem (by rw [hb1.mrk_len]; exact Nat.lt_of_lt_of_le hv_lt hcv),
          Option.getD_some]
      have hm3 : (FullMem c (m8SBlkSt s s.core.tmp mrk2 s.core.min_clr (sstk1.set slen.toNat v)
          s.scratch.wsort s.core.min_clr_len s.core.min_clr_full s.scratch.search_ticks) ⋆ R)
          m := by
        dsimp only [mrk2, v]
        rw [m8SBlk_st_sstk_eq s s.core.tmp _ s.core.min_clr sstk1 s.scratch.wsort s.core.min_clr_len
          s.core.min_clr_full s.scratch.search_ticks rfl] at hm
        have hget_m2' : mrk1[(s.core.tmp[k.toNat]'hk_arr >>> 1).toNat] =
            mrk1[(s.core.tmp[k.toNat]'hk_arr >>> 1).toNat]?.getD 0#8 := hget_m2
        simpa only [bv_c0_zext32_64, bv8_or8_c0', hget_m2'] using hm
      have hsl1 : (slen + 1).toNat = slen.toNat + 1 := by c0_bound
      have hk1 : (k + 1).toNat = k.toNat + 1 := by c0_bound
      exact hL1 (end_b.toNat - (k + 1).toNat) (slen + 1, k + 1, ()) m
        (by rw [hk1]; omega) ⟨rfl, by rw [hk1]; omega, by rw [hk1]; omega, by rw [hsl1, hk1]; omega,
          mrk2, _, by rw [hsl1]; exact hb2, by rw [hsl1]; exact hstk2,
          by rw [hk1]; exact hbp2, by rw [hsl1]; exact hcnt2, by rw [hk1]; exact hno8o2, hm3⟩
    · have hk_eq : k.toNat = end_b.toNat := by c0_grind
      rw [hk_eq] at hbp hno8o
      have h8_0 := m8Shrink_init_all8 hcore hblk hno8o
      have hsub0 : (end_b - beg).toNat = end_b.toNat - beg.toNat := by c0_bound
      c0_hsteps_nogrp
      refine wp_loop_break_group (brkTs := [i64, i64, .bool, i32, i64])
        (lpTs := [i64, i64, .bool, i32, i64])
        (fun (open_b, slen_b, failed_b, uip_b, _t_b, ()) m_b =>
          ∃ mrk_b mclr_b sstk_b wsort_b mcl_b mcf_b ticks_b t_uip,
            M8ShrinkBaseInv c s mrk_b mclr_b sstk_b wsort_b mcl_b mcf_b slen_b.toNat keep0 ∧
            (failed_b = false → M8ShrinkStk8 mrk_b sstk_b slen_b.toNat ∧ uip_b ≠ 0xFFFFFFFF#32 ∧
              t_uip < s.core.trail_end ∧ (s.core.trl[t_uip]?.getD 0#32).toNat = uip_b.toNat ∧
              (mrk_b[uip_b.toNat / 2]?.getD 0#8 &&& 8#8) ≠ 0#8 ∧
              (s.core.lvl[uip_b.toNat / 2]?.getD 0#32).toNat = blvl.toNat ∧
              M8ShrinkBlk8 s mrk_b beg.toNat end_b.toNat ∧
              (∀ w < s.core.cur_vars, (mrk_b[w]?.getD 0#8 &&& 8#8) ≠ 0#8 →
                w = uip_b.toNat / 2 ∨ ∃ idx < s.core.trail_end, t_uip < idx ∧
                  (s.core.trl[idx]?.getD 0#32).toNat / 2 = w ∧
                  ShrinkResolved s.core mrk_b idx)) ∧
            (FullMem c (m8SBlkSt s s.core.tmp mrk_b mclr_b sstk_b wsort_b mcl_b mcf_b ticks_b) ⋆
              R) m_b)
        (fun n (open_i, slen_i, failed_i, uip_i, t_i, ()) m_i =>
          n = t_i.toNat ∧
          ∃ mrk_i mclr_i sstk_i wsort_i mcl_i mcf_i ticks_i,
            M8ShrinkBaseInv c s mrk_i mclr_i sstk_i wsort_i mcl_i mcf_i slen_i.toNat keep0 ∧
            (failed_i = false → M8ShrinkStk8 mrk_i sstk_i slen_i.toNat ∧ 1 ≤ open_i.toNat ∧
              open_i.toNat ≤ (end_b.toNat - beg.toNat) + slen_i.toNat ∧
              M8ShrinkBlk8 s mrk_i beg.toNat end_b.toNat ∧
              M8ShrinkAll8 s blvl mrk_i t_i.toNat s.core.trail_end ∧
              trailCount8 s.core.trl mrk_i (min (t_i.toNat + 1) s.core.trail_end) ≤
                open_i.toNat) ∧
            (FullMem c (m8SBlkSt s s.core.tmp mrk_i mclr_i sstk_i wsort_i mcl_i mcf_i ticks_i) ⋆
              R) m_i) ?_ ?_ ?_
      · rintro B ⟨open_b, slen_b, failed_b, uip_b, t_b, ⟨⟩⟩ m_b
          ⟨mrk_b, mclr_b, sstk_b, wsort_b, mcl_b, mcf_b, ticks_b, t_uip, hb_b, hok_b, hm_b⟩
        rw [Blocks.get_here]
        exact m8_shrink_after_wp hMm hcore hbeg_end hend_kl hkl_cv
          (fun k hk1 hk2 => (hblk k hk1 hk2).2.2.1) hkeep rfl hb_b hok_b hm_b hQ
      · rintro B L n ⟨open_i, slen_i, failed_i, uip_i, t_i, ⟨⟩⟩ m_i hB hL
          ⟨rfl, mrk_i, mclr_i, sstk_i, wsort_i, mcl_i, mcf_i, ticks_i, hb_i, hok_i, hm_i⟩
        rw [Blocks.get_here]; c0_hsplit
        · subst hc; c0_hsteps!
          exact hB (open_i, slen_i, true, uip_i, t_i, ()) m_i
            ⟨mrk_i, mclr_i, sstk_i, wsort_i, mcl_i, mcf_i, ticks_i, 0, hb_i,
              (fun hf => by cases hf), hm_i⟩
        · have hfi : failed_i = false := hc
          subst hfi
          obtain ⟨hstk_i, hop1, hopl, hblk_i, h8_i, hcnt_i⟩ := hok_i rfl
          refine wp_loop_break_group (brkTs := [.bool, i32, i64]) (lpTs := [i64])
            (fun (f_a, uip_a, t_a, ()) m_a =>
              m_a = m_i ∧
              (f_a = false → t_a.toNat ≤ t_i.toNat ∧ t_a.toNat < s.core.trail_end ∧
                (s.core.trl[t_a.toNat]?.getD 0#32).toNat = uip_a.toNat ∧
                (mrk_i[uip_a.toNat / 2]?.getD 0#8 &&& 8#8) ≠ 0#8 ∧
                (s.core.lvl[uip_a.toNat / 2]?.getD 0#32).toNat = blvl.toNat ∧
                trailCount8 s.core.trl mrk_i t_a.toNat ≤ open_i.toNat - 1 ∧
                M8ShrinkAll8 s blvl mrk_i (t_a.toNat - 1) t_a.toNat))
            (fun n_t (t_c, ()) m_c =>
              n_t = t_c.toNat ∧ t_c.toNat ≤ t_i.toNat ∧ m_c = m_i ∧
              M8ShrinkAll8 s blvl mrk_i t_c.toNat s.core.trail_end ∧
              trailCount8 s.core.trl mrk_i (min (t_c.toNat + 1) s.core.trail_end) ≤ open_i.toNat)
            ?_ ?_ ?_
          · rintro Ba ⟨f_a, uip_a, t_a, ⟨⟩⟩ m_a ⟨hm_a, hok_a⟩; subst m_a; rw [Blocks.get_here]
            refine wp_join_group (ts := []) (fun _ m_j => m_j = m_i) ?_ ?_
            · rintro _ ⟨⟩ m_j hm_j; subst m_j; rw [Blocks.get_here]
              refine wp_join_group (ts := [.bool]) (fun (f_j, _) m_j =>
                  m_j = m_i ∧ (open_i.toNat ≠ 1 → f_j = true) ∧
                  (open_i.toNat = 1 → f_j = f_a)) ?_ ?_
              · rintro _ ⟨f_j, ⟨⟩⟩ m_j ⟨hm_j, hne1, heq1⟩; subst m_j; rw [Blocks.get_here]
                c0_hsteps!
                by_cases hf_a : f_a = true
                · subst hf_a
                  have hfj : f_j = true := by
                    by_cases h1 : open_i.toNat = 1
                    · exact (heq1 h1).trans rfl
                    · exact hne1 h1
                  exact hB (open_i, slen_i, f_j, uip_a, t_a, ()) m_i
                    ⟨mrk_i, mclr_i, sstk_i, wsort_i, mcl_i, mcf_i, ticks_i, 0,
                      hb_i, (fun h => by cases (hfj ▸ h)), hm_i⟩
                · have hfa : f_a = false := Bool.eq_false_iff.mpr hf_a
                  obtain ⟨_, hte, hueq, hu8, hulvl, hcnt_a, h8_a⟩ := hok_a hfa
                  by_cases ho1 : open_i.toNat = 1
                  · have hfj : f_j = false := (heq1 ho1).trans hfa
                    have hcnt0 : trailCount8 s.core.trl mrk_i t_a.toNat = 0 := by omega
                    exact hB (open_i, slen_i, f_j, uip_a, t_a, ()) m_i
                      ⟨mrk_i, mclr_i, sstk_i, wsort_i, mcl_i, mcf_i, ticks_i, t_a.toNat, hb_i,
                        (fun _ => ⟨hstk_i, by
                          intro heq; obtain ⟨_, hw⟩ := hcore.2
                          have hlt := hw.trail_lits_lt t_a.toNat hte
                          have h2 := congrArg BitVec.toNat heq
                          have hff : (0xFFFFFFFF#32 : BitVec 32).toNat = 4294967295 := rfl
                          rw [← hueq, hff] at h2; omega,
                          hte, hueq, hu8, hulvl, hblk_i,
                          m8Shrink_open1_done hcore hte hueq h8_a hcnt0⟩), hm_i⟩
                  · have hfj := hne1 ho1
                    exact hB (open_i, slen_i, f_j, uip_a, t_a, ()) m_i
                      ⟨mrk_i, mclr_i, sstk_i, wsort_i, mcl_i, mcf_i, ticks_i, 0, hb_i,
                        (fun h => by cases (hfj ▸ h)), hm_i⟩
              · intro J hJ; c0_hsplit
                · c0_hsteps!; exact hJ (true, ()) m_i ⟨rfl, fun _ => rfl,
                    fun h => absurd (BitVec.eq_of_toNat_eq h) hc⟩
                · c0_hsteps!; exact hJ (f_a, ()) m_i
                    ⟨rfl, fun h => absurd (congrArg BitVec.toNat hc) h, fun _ => rfl⟩
            · rintro Jt hJt; c0_hsplit
              · c0_hsteps!; exact hJt () m_i rfl
              · have hfa' : f_a = false := hc
                subst hfa'
                c0_hsplit
                · c0_hsteps!; exact hJt () m_i rfl
                · c0_hsplit
                  · c0_hsteps!; exact hJt () m_i rfl
                  · have hne1 : open_i ≠ 1 := by c0_grind
                    have ht_pos' : 0 < t_a.toNat := by c0_grind
                    have hop2 : 2 ≤ open_i.toNat := by
                      have : open_i.toNat ≠ 1 := fun h => hne1 (BitVec.eq_of_toNat_eq h)
                      omega
                    have htm1 : (t_a - 1).toNat = t_a.toNat - 1 := by c0_bound
                    obtain ⟨ht_le, hte, hueq, hu8, hulvl, hcnt_a, h8_a⟩ := hok_a rfl
                    have huip_lt2v : uip_a.toNat < 2 * s.core.cur_vars := by
                      obtain ⟨_, hw⟩ := hcore.2; rw [← hueq]; exact hw.trail_lits_lt t_a.toNat hte
                    have hur_len : ((uip_a >>> 1).setWidth 64).toNat < (m8SBlkSt s s.core.tmp mrk_i
                        mclr_i sstk_i wsort_i mcl_i mcf_i ticks_i).core.rsns.length := by
                      dsimp only [m8SBlkSt, Spec.m8ShrinkBlkBoolState]
                      rw [hlen0.rsns_len, bv_c0_zext32_64, bv32_lshr_1]; omega
                    let rsn := s.core.rsns[((uip_a >>> 1).setWidth 64).toNat]'hur_len
                    have hrsn_eq : rsn = s.core.rsns[(s.core.trl[t_a.toNat]?.getD 0#32).toNat /
                        2]?.getD 0xFFFFFFFF#32 := by
                      have hur_rsn : s.core.rsns[(s.core.trl[t_a.toNat]?.getD 0#32).toNat / 2]?.getD
                          0xFFFFFFFF#32 = s.core.rsns[
                            (s.core.trl[t_a.toNat]?.getD 0#32).toNat / 2]'(by
                              rw [hlen0.rsns_len]; omega) := by
                        rw [List.getElem?_eq_getElem (by rw [hlen0.rsns_len]; omega),
                          Option.getD_some]
                      rw [hur_rsn]; dsimp only [rsn]; congr 1
                      simp only [bv_c0_zext32_64, bv32_lshr_1, hueq]
                    c0_hsplit
                    · c0_hsteps!; exact hB (open_i, slen_i, true, uip_a, t_a - 1, ()) m_i
                        ⟨mrk_i, mclr_i, sstk_i, wsort_i, mcl_i, mcf_i, ticks_i, 0, hb_i,
                          (fun h => by cases h), hm_i⟩
                    · have hrsn_ne : rsn ≠ 0xFFFFFFFF#32 := by c0_grind
                      let is_bin := ((rsn &&& 0x80000000#32) != 0#32)
                      have his_bin : (is_bin = true) ↔ (rsn &&& 0x80000000#32) ≠ 0#32 := by
                        dsimp only [is_bin]; simp
                      obtain ⟨hbig_f, hq_inv⟩ := m8SBlk_reason_facts hcore hte hueq hulvl hblvl_lt
                        hrsn_eq hrsn_ne his_bin
                      refine wp_join_group (ts := [.bool, i32])
                        (fun (f_hdr, csz_h, ()) m_hdr =>
                          f_hdr = false ∧
                          (f_hdr = false → (is_bin = true → csz_h = 1#32) ∧
                            (is_bin = false →
                              csz_h.toNat = fullArenaClauseSizeCore s.core rsn.toNat)) ∧
                          ∃ ticks_h, (FullMem c (m8SBlkSt s s.core.tmp mrk_i mclr_i sstk_i wsort_i
                            mcl_i mcf_i ticks_h) ⋆ R) m_hdr) ?_ ?_
                      · rintro Jhdr ⟨f_hdr, csz_h, ⟨⟩⟩ m_hdr ⟨rfl, hcsz_h, ticks_h, hm_hdr⟩
                        rw [Blocks.get_here]; c0_hsteps_nogrp
                        simp only [liftCmp, lift2, evalBits_ne_bne]
                        have hend_mv : end_b.toNat ≤ c.max_vars := by omega
                        exact m8_shrink_blk_cl_iter_wp (rsn := rsn) (is_bin := is_bin)
                          (uip_a := uip_a) (csz_h := csz_h) (open_i := open_i) (slen_i := slen_i)
                          hSL hcore hblvl_lt hte ht_pos' htm1 hend_mv hueq hulvl hblk_lt hrsn_ne
                          hrsn_eq his_bin hbig_f hq_inv hcsz_h hb_i hblk_i hstk_i h8_a hcnt_a hop2
                          hopl hm_hdr (fun n' ys m' hn' hy => hL n' ys m' (by omega) hy)
                      · have hrsn_c0 : s.core.rsns[uip_a.toNat / 2] = rsn := by
                          dsimp only [rsn]; simp only [bv_c0_zext32_64, bv32_lshr_1]
                        intro Jhdr hJhdr; c0_hsplit
                        · have hibt : is_bin = true := by
                            dsimp only [is_bin]
                            simp only [liftCmp, lift2, evalBits_ne_bne] at hc
                            rwa [← hrsn_c0]
                          c0_hsteps!; exact hJhdr (false, 1#32, ()) m_i
                            ⟨rfl, fun _ => ⟨fun _ => rfl, (fun h => by rw [hibt] at h; cases h)⟩,
                              ticks_i, hm_i⟩
                        · have hibf : is_bin = false := by
                            dsimp only [is_bin]
                            simp only [liftCmp, lift2, evalBits_ne_bne] at hc
                            rwa [← hrsn_c0]
                          obtain ⟨_, _, ha3, hcsz3, hacsz⟩ := hbig_f hibf
                          c0_hsplit
                          · exfalso; have := hlen0.arena_len_le; c0_grind
                          · have har2 : (rsn.setWidth 64 + 2).toNat < (m8SBlkSt s s.core.tmp mrk_i
                                mclr_i sstk_i wsort_i mcl_i mcf_i ticks_i).core.arena.length := by
                              have := hlen0.arena_len_le; rw [bv64_zext32_add2]
                              dsimp only [m8SBlkSt, Spec.m8ShrinkBlkBoolState]
                              rw [hlen0.arena_len_arr]; omega
                            let csz := s.core.arena[(rsn.setWidth 64 + 2).toNat]'har2
                            have hcsz_eq :
                                csz.toNat = fullArenaClauseSizeCore s.core rsn.toNat := by
                              have hopt : (m8SBlkSt s s.core.tmp mrk_i mclr_i sstk_i wsort_i mcl_i
                                  mcf_i ticks_i).core.arena[(rsn.setWidth 64 + 2).toNat]? =
                                  s.core.arena[rsn.toNat + 2]? := by
                                dsimp only [m8SBlkSt, Spec.m8ShrinkBlkBoolState]
                                rw [bv64_zext32_add2]
                              rw [List.getElem?_eq_getElem har2] at hopt
                              exact congrArg (fun o => (o.getD 0#32).toNat) hopt
                            c0_hsplit
                            · exfalso; have := hlen0.arena_len_le
                              dsimp only [csz] at hcsz_eq
                              c0_grind [bv64_zext32_add2]
                            · c0_hsplit
                              · exfalso; have := hlen0.arena_len_le
                                dsimp only [csz] at hcsz_eq
                                c0_grind [bv64_zext32_add2]
                              · c0_hsteps!; exact hJhdr (false, csz, ()) m ⟨rfl, (fun _ =>
                                  ⟨(fun h => by rw [hibf] at h; cases h), fun _ => hcsz_eq⟩),
                                  ticks_i + 1#64, hm⟩
          · rintro Ba La na ⟨t_c, ⟨⟩⟩ m_c hBa hLa ⟨rfl, htc_le, hm_c, h8_c, hcnt_c⟩
            subst m_c; rw [Blocks.get_here, wp_jnz, Arg.val_imm]
            refine ⟨fun _ => ?_, fun h => by cases h⟩
            c0_hsplit
            · c0_hsteps!; exact hBa (true, uip_i, t_c, ()) m_i ⟨rfl, fun h => by cases h⟩
            · have htc_te : t_c.toNat < s.core.trail_end := by
                have := hlen0.trail_end_le; c0_grind
              have htc_arr : t_c.toNat < (m8SBlkSt s s.core.tmp mrk_i mclr_i sstk_i wsort_i
                  mcl_i mcf_i ticks_i).core.trl.length := by
                dsimp only [m8SBlkSt, Spec.m8ShrinkBlkBoolState]; rw [hlen0.trl_len]
                have := hlen0.trail_end_le; omega
              let lit := s.core.trl[t_c.toNat]'htc_arr
              have hlit_eq : lit = s.core.trl[t_c.toNat]?.getD 0#32 := by
                rw [List.getElem?_eq_getElem htc_arr, Option.getD_some]
              have hlt2v : lit.toNat < 2 * s.core.cur_vars := by
                obtain ⟨_, hw⟩ := hcore.2; rw [hlit_eq]; exact hw.trail_lits_lt t_c.toNat htc_te
              have hmrk_bd : ((lit >>> 1).setWidth 64).toNat < (m8SBlkSt s s.core.tmp mrk_i
                  mclr_i sstk_i wsort_i mcl_i mcf_i ticks_i).core.mrk.length := by
                rw [bv_c0_zext32_64, bv32_lshr_1, hb_i.mrk_len]; omega
              c0_hsplit
              · have h8_lit : (mrk_i[(lit >>> 1).toNat]?.getD 0#8 &&& 8#8) ≠ 0#8 := by
                  rw [bv32_lshr_1, List.getElem?_eq_getElem
                    (by rw [hb_i.mrk_len]; change lit.toNat / 2 < c.max_vars; omega),
                    Option.getD_some]
                  exact bv8_and8_ne0_c0 hc
                obtain ⟨hcnt', h8', _, hbl⟩ := m8Shrink_trail_found hcore h8_c hcnt_c (le_refl _)
                  htc_te hlit_eq (fun _ _ _ => by omega) h8_lit
                c0_hsteps!; exact hBa (false, lit, t_c, ()) m_i ⟨rfl, fun _ =>
                  ⟨htc_le, htc_te, (congrArg BitVec.toNat hlit_eq).symm, by rwa [← bv32_lshr_1],
                    hbl, hcnt', h8'⟩⟩
              · have hz_lit : (mrk_i[(s.core.trl[t_c.toNat]?.getD 0#32).toNat / 2]?.getD 0#8 &&&
                    8#8) = 0#8 := by
                  rw [List.getElem?_eq_getElem htc_arr, Option.getD_some,
                    List.getElem?_eq_getElem
                      (by rw [hb_i.mrk_len]; change lit.toNat / 2 < c.max_vars; omega),
                    Option.getD_some]
                  exact bv8_and8_eq0_c0 hc
                c0_hsplit
                · c0_hsteps!; exact hBa (true, uip_i, t_c, ()) m_i ⟨rfl, fun h => by cases h⟩
                · have htc_pos : 0 < t_c.toNat := by c0_grind
                  have htm1 : (t_c - 1).toNat = t_c.toNat - 1 := by c0_bound
                  have hcnt_step : trailCount8 s.core.trl mrk_i
                      (min ((t_c - 1).toNat + 1) s.core.trail_end) ≤ open_i.toNat := by
                    rw [htm1, show t_c.toNat - 1 + 1 = t_c.toNat by omega,
                      Nat.min_eq_left (by omega)]
                    have hste := trailCount8_step_zero hz_lit
                    have hcnt_c' := hcnt_c
                    rw [Nat.min_eq_left (by omega), hste] at hcnt_c'
                    exact hcnt_c'
                  have h8_step : M8ShrinkAll8 s blvl mrk_i (t_c - 1).toNat s.core.trail_end := by
                    intro w hw hw8; obtain ⟨hl, idx, hi, hv, hdisj⟩ := h8_c w hw hw8
                    refine ⟨hl, idx, hi, hv, ?_⟩
                    rcases hdisj with hle | hres | heq
                    · by_cases hit : idx = t_c.toNat
                      · subst hit; exfalso; rw [hv] at hz_lit; exact hw8 hz_lit
                      · exact Or.inl (by omega)
                    · exact Or.inr (Or.inl hres)
                    · exact Or.inr (Or.inr heq)
                  c0_hsteps!; exact hLa (t_c - 1).toNat (t_c - 1, ()) m_i (by omega)
                    ⟨rfl, by rw [htm1]; omega, rfl, h8_step, hcnt_step⟩
          · intro Ba La hBa hLa; c0_hsteps!; exact hLa t_i.toNat (t_i, ()) m_i
              ⟨rfl, le_refl _, rfl, h8_i, hcnt_i⟩
      · intro B L hB hL
        c0_hsteps!
        exact hL max_tr.toNat (end_b - beg, slen, false, 0xFFFFFFFF#32, max_tr, ()) m_1
          ⟨rfl, mrk1, s.core.min_clr, sstk1, s.scratch.wsort, s.core.min_clr_len,
            s.core.min_clr_full, s.scratch.search_ticks, hb1,
            fun _ => ⟨hstk8, by rw [hsub0]; omega, by rw [hsub0]; omega, hbp, h8_0,
              by rw [hsub0]; exact Nat.le_trans hcnt1 (by omega)⟩, hm1⟩
  · intro L1 hL1
    c0_hsteps!
    exact hL1 (end_b.toNat - beg.toNat) (0#64, beg, ()) m
      ⟨rfl, le_refl _, le_of_lt hbeg_end, by simp, s.core.mrk, s.scratch.shrink_stk, hb0,
        fun _ hj => by simp at hj, fun _ h1 h2 => by omega,
        by simp; rw [trailCount8_zero_of_all_zero (fun i hi => by
            obtain ⟨_, hw⟩ := hcore.2
            have := hw.trail_lits_lt i (Nat.lt_of_lt_of_le hi (Nat.min_le_right _ _)); omega)
          hno8 _ (le_refl _)],
        fun w hw h8 => absurd (hno8 w hw) h8, hm⟩

end

end LeanQbe.T.Examples.Kissat.Proof.Minimize
