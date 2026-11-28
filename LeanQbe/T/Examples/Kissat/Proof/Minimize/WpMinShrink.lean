/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Minimize.Spec
public import LeanQbe.T.Examples.Kissat.Src.Minimize
public import LeanQbe.T.Logic.CanonicalEnv
import LeanQbe.T.Examples.Kissat.Proof.Minimize.MinTactics
import LeanQbe.T.Examples.Kissat.Proof.Minimize.WpMark
import LeanQbe.T.Examples.Kissat.Proof.Minimize.WpSort
import LeanQbe.T.Examples.Kissat.Proof.Minimize.WpMinDfs
import LeanQbe.T.Examples.Kissat.Proof.Minimize.WpShrinkBlk
import LeanQbe.T.Examples.Kissat.Proof.Minimize.WpMinShrinkHelpers
import LeanQbe.T.Examples.Kissat.Proof.Minimize.WpMinShrinkLoops
import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena1
import LeanQbe.T.Logic.C0Grind
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.ControlComb

/-!
# `full_min_shrink_m6` WP Proof for `Kissat.Src.Minimize`

Proves `Func.wp Γ full_min_shrink_m6_body ...` against canonical `Spec.fullMinShrinkSpec`,
consuming `Γ.Has` for `full_sort_tmp`, `full_min_mark`, `full_shrink_blk_bool_m8`, and
`full_min_lit_dfs_m8`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Minimize

open Std Std.Sat
open LeanQbe.T LeanQbe.T.C0Grind LeanQbe.T.C0HeadStep LeanQbe.T.C0Step LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics
open LeanQbe.T.Examples.Kissat.Src.Minimize
open FullMinTactics
open scoped FullArenaTactics FullMinTactics
open Kraken.Bedrock2.Test

private abbrev m6KSt (s : FullState) (b : ShrinkScratch) (keep : Nat) (conf' : BitVec 64) :
    FullState :=
  Spec.fullMinShrinkState s b.tmp keep b.mrk b.mclr b.sstk b.wsort b.ws1 0 0#64
    conf' s.scratch.learned_lits s.scratch.min_removed b.ticks b.resSz

/-! ## 1. Compaction & Mark-Clearing Loops -/

private def m6CompactLoopExpr {V : Ty → Type} {C : List Ty → Type} {rs : List Ty}
    (pTmp tlen : V i64) (k : V i64 → Expr V C rs) : Expr V C rs :=
  .group (sig := [[i64, i64]]) (fun Lc => .cons (fun pk =>
    .let_ (Op.mk (.cmp .ult i64 .bool rfl) (.var pk.snd.fst, .var tlen, ())) fun cmpk =>
    .jnz (.var cmpk.fst)
      (.group (sig := [[i64]]) (fun _Jn => .cons (fun keep' =>
         .let_ (Op.mk (.add i64) (.var pk.snd.fst, .imm 1, ())) fun k1 =>
         .jump Lc.fst (.var keep'.fst, .var k1.fst, ())) .nil) fun Jn =>
       .let_ (Op.mk (.mul i64) (.var pk.snd.fst, .imm 4, ())) fun koff =>
       .let_ (Op.mk (.add i64) (.var pTmp, .var koff.fst, ())) fun kaddr =>
       .load i32 (.var kaddr.fst) fun lit =>
       .let_ (Op.mk (.cmp .ne i32 .bool rfl)
           (.var lit, .imm (4294967295 : BitVec 32), ())) fun hne =>
       .jnz (.var hne.fst)
         (.let_ (Op.mk (.mul i64) (.var pk.fst, .imm 4, ())) fun kpoff =>
          .let_ (Op.mk (.add i64) (.var pTmp, .var kpoff.fst, ())) fun kpaddr =>
          .let_ (Op.mk (.mul i64) (.var pk.snd.fst, .imm 4, ())) fun koff2 =>
          .let_ (Op.mk (.add i64) (.var pTmp, .var koff2.fst, ())) fun kaddr2 =>
          .load i32 (.var kaddr2.fst) fun lit2 =>
          .store (.var lit2) (.var kpaddr.fst)
            (.let_ (Op.mk (.add i64) (.var pk.fst, .imm 1, ())) fun keep1 =>
             .jump Jn.fst (.var keep1.fst, ())))
         (.jump Jn.fst (.var pk.fst, ())))
      (k pk.fst)) .nil)
    (fun Lc => .jump Lc.fst (.imm 1, .imm 1, ()))

private theorem m6_compact_loop_wp {Γ : Env} {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {orig_tlen : Nat} {ot_bv : BitVec 64}
    {tmp_s : List (BitVec 32)} {bf : ShrinkScratch} {R : Mem 64 → Prop} {m : Mem 64}
    {Q : Post []} {X : XPost} {after : Val i64 → Expr Val Cont []}
    (hot_bv : ot_bv.toNat = orig_tlen) (hot_pos : 1 ≤ orig_tlen)
    (hot_le : orig_tlen ≤ s.core.cur_vars) (hcv : s.core.cur_vars ≤ c.max_vars)
    (hs_0eq : tmp_s[0]? = s.core.tmp[0]?)
    (hs_nosent0 : tmp_s[0]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32)
    (hshrink : M6ShrinkLoopInv c F0 F_cur s orig_tlen tmp_s s.core.mrk orig_tlen bf)
    (hm : (FullMem c (bf.st s) ⋆ R) m)
    (hafter : ∀ (keep_bv : BitVec 64) (tmp_c : List (BitVec 32)) m_c,
      keep_bv.toNat ≤ orig_tlen →
      M6TmpOutInv c F0 F_cur s orig_tlen keep_bv.toNat tmp_c →
      (FullMem c ({ bf with tmp := tmp_c }.st s) ⋆ R) m_c →
      wp Γ Q X (after keep_bv) m_c) :
    wp Γ Q X (m6CompactLoopExpr c.pTmp ot_bv after) m := by
  have hmx := c.hmaxv; unfold Ref.dimacsBound at hmx
  dsimp only [m6CompactLoopExpr]
  refine wp_loop_group (ts := [i64, i64]) (fun n (keep_bv, k_bv, ()) m_c =>
      n = orig_tlen - k_bv.toNat ∧
      ∃ tmp_c, M6CompactInv c s orig_tlen tmp_s bf.tmp tmp_c keep_bv.toNat k_bv.toNat ∧
        (FullMem c ({ bf with tmp := tmp_c }.st s) ⋆ R) m_c) ?_ ?_
  · rintro Lc n_c ⟨keep_bv, k_bv, ⟨⟩⟩ m_c hLc ⟨rfl, tmp_c, hcinv, hm_c⟩
    c0_hsplit
    · have hk_lt : k_bv.toNat < orig_tlen := by c0_grind
      have hge1 := hcinv.keep_ge1
      have hkle := hcinv.keep_le
      refine wp_join_group (ts := [i64]) (fun (keep', ()) m_n =>
          ∃ tmp', M6CompactInv c s orig_tlen tmp_s bf.tmp tmp' keep'.toNat (k_bv.toNat + 1) ∧
            (FullMem c ({ bf with tmp := tmp' }.st s) ⋆ R) m_n) ?_ ?_
      · rintro _ ⟨keep', ⟨⟩⟩ m_n ⟨tmp', hcinv', hm'⟩
        have hk1 : (k_bv + 1).toNat = k_bv.toNat + 1 := by c0_bound
        c0_hsteps!
        exact hLc (orig_tlen - (k_bv.toNat + 1)) (keep', k_bv + 1, ()) m_n (by omega)
          ⟨by rw [hk1], tmp', by rw [hk1]; exact hcinv', hm'⟩
      · intro Jn hJn
        have hk_arr : k_bv.toNat < ({ bf with tmp := tmp_c }.st s).core.tmp.length := by
          rw [hcinv.tmp_len]; omega
        have hkeep_arr : keep_bv.toNat < ({ bf with tmp := tmp_c }.st s).core.tmp.length := by
          rw [hcinv.tmp_len]; omega
        c0_hsteps_nogrp; c0_hsplit
        · have hne_val : tmp_c[k_bv.toNat]?.getD 0#32 ≠ 0xFFFFFFFF#32 := by
            rw [List.getElem?_eq_getElem hk_arr, Option.getD_some]; exact hc
          c0_hsteps!
          have hk1 : (keep_bv + 1).toNat = keep_bv.toNat + 1 := by c0_bound
          refine hJn (keep_bv + 1, ()) _ ⟨_, ?_, hm⟩
          rw [hk1, ← Option.getD_some (b := 0#32) (a := tmp_c[k_bv.toNat]'hk_arr),
            ← List.getElem?_eq_getElem hk_arr]
          exact m6Compact_step_keep hcv hot_le hshrink hcinv hk_lt hne_val
        · have heq_val : tmp_c[k_bv.toNat]?.getD 0#32 = 0xFFFFFFFF#32 := by
            rw [List.getElem?_eq_getElem hk_arr, Option.getD_some]; exact hc
          exact hJn (keep_bv, ()) m_c ⟨tmp_c, m6Compact_step_skip hcv hot_le hcinv hk_lt
            hshrink.len.tmp_len heq_val, hm_c⟩
    · have hkle := hcinv.k_le
      have hk_eq : k_bv.toNat = orig_tlen := by c0_grind
      rw [hk_eq] at hcinv
      exact hafter keep_bv tmp_c m_c (Nat.le_trans hcinv.keep_le hcinv.k_le)
        (m6_compact_to_out hs_0eq hshrink hcinv) hm_c
  · intro Lc hLc; c0_hsteps!
    exact hLc (orig_tlen - 1) (1#64, 1#64, ()) m ⟨rfl, bf.tmp,
      m6Compact_init hot_pos hot_le hcv hs_nosent0 hshrink, hm⟩

private def m6ClearMrkExpr {V : Ty → Type} {C : List Ty → Type} {rs : List Ty}
    (h pMrk cv : V i64) (Jpost : C []) : Expr V C rs :=
  .let_ (Op.mk (.add i64) (.var h, .imm 280, ())) fun pmcf =>
  .load i64 (.var pmcf.fst) fun mcf =>
  .let_ (Op.mk (.cmp .ne i64 .bool rfl) (.var mcf, .imm 0, ())) fun hfull =>
  .jnz (.var hfull.fst)
    (.group (sig := [[i64]]) (fun Lv => .cons (fun v =>
       .let_ (Op.mk (.cmp .ult i64 .bool rfl) (.var v.fst, .var cv, ())) fun hv =>
       .jnz (.var hv.fst)
         (.let_ (Op.mk (.add i64) (.var pMrk, .var v.fst, ())) fun maddr =>
          .let_ (Op.mk (.trunc 32 8) (.imm 0, ())) fun z8 =>
          .store (.var z8.fst) (.var maddr.fst)
            (.let_ (Op.mk (.add i64) (.var v.fst, .imm 1, ())) fun v1 =>
             .jump Lv.fst (.var v1.fst, ())))
         (.jump Jpost ())) .nil) (fun Lv => .jump Lv.fst (.imm 0, ())))
    (.let_ (Op.mk (.add i64) (.var h, .imm 240, ())) fun pmclr =>
     .load i64 (.var pmclr.fst) fun pMclr =>
     .group (sig := [[i64]]) (fun Lz => .cons (fun z =>
       .let_ (Op.mk (.add i64) (.var h, .imm 272, ())) fun pmcl =>
       .load i64 (.var pmcl.fst) fun mcl =>
       .let_ (Op.mk (.cmp .ult i64 .bool rfl) (.var z.fst, .var mcl, ())) fun hz =>
       .jnz (.var hz.fst)
         (.let_ (Op.mk (.mul i64) (.var z.fst, .imm 4, ())) fun zoff =>
          .let_ (Op.mk (.add i64) (.var pMclr, .var zoff.fst, ())) fun zaddr =>
          .load i32 (.var zaddr.fst) fun zv =>
          .group (sig := [[]]) (fun _Jn => .cons (fun _ =>
             .let_ (Op.mk (.add i64) (.var z.fst, .imm 1, ())) fun z1 =>
             .jump Lz.fst (.var z1.fst, ())) .nil) fun Jn =>
           .let_ (Op.mk (.zext 32 64) (.var zv, ())) fun zv64 =>
           .let_ (Op.mk (.cmp .ult i64 .bool rfl) (.var zv64.fst, .var cv, ())) fun hzv =>
           .jnz (.var hzv.fst)
             (.let_ (Op.mk (.zext 32 64) (.var zv, ())) fun zv64b =>
              .let_ (Op.mk (.add i64) (.var pMrk, .var zv64b.fst, ())) fun maddr =>
              .let_ (Op.mk (.trunc 32 8) (.imm 0, ())) fun z8 =>
              .store (.var z8.fst) (.var maddr.fst) (.jump Jn.fst ()))
             (.jump Jn.fst ()))
         (.jump Jpost ())) .nil) (fun Lz => .jump Lz.fst (.imm 0, ())))

private theorem m6_clear_mrk_wp {Γ : Env} {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {orig_tlen : Nat} {cv_bv : BitVec 64}
    {tmp_s tmp_c : List (BitVec 32)} {bf : ShrinkScratch} {R : Mem 64 → Prop} {m : Mem 64}
    {Q : Post []} {X : XPost} {Jpost : Cont []}
    (hcv_bv : cv_bv.toNat = s.core.cur_vars) (hcv : s.core.cur_vars ≤ c.max_vars)
    (hclear : FullLitMarksClear c s)
    (hshrink : M6ShrinkLoopInv c F0 F_cur s orig_tlen tmp_s s.core.mrk orig_tlen bf)
    (hm : (FullMem c ({ bf with tmp := tmp_c }.st s) ⋆ R) m)
    (hJ : ∀ (mrk' : List (BitVec 8)) m',
      mrk'.length = c.max_vars → (∀ w < c.max_vars, mrk'[w]?.getD 0#8 = 0#8) →
      (FullMem c ({ bf with tmp := tmp_c, mrk := mrk' }.st s) ⋆ R) m' →
      wp Γ Q X (.jump Jpost ()) m') :
    wp Γ Q X (m6ClearMrkExpr c.hdr c.pMark cv_bv Jpost) m := by
  have hmx := c.hmaxv; unfold Ref.dimacsBound at hmx
  dsimp only [m6ClearMrkExpr]
  c0_hsteps_nogrp; c0_hsplit
  · refine wp_loop_group (ts := [i64]) (fun n (v_bv, ()) m_v =>
        n = s.core.cur_vars - v_bv.toNat ∧ v_bv.toNat ≤ s.core.cur_vars ∧
        ∃ mrk_v, mrk_v.length = c.max_vars ∧
          (∀ w < v_bv.toNat, mrk_v[w]? = some 0#8) ∧
          (∀ w, s.core.cur_vars ≤ w → mrk_v[w]? = bf.mrk[w]?) ∧
          (FullMem c ({ bf with tmp := tmp_c, mrk := mrk_v }.st s) ⋆ R) m_v) ?_ ?_
    · rintro Lv n_v ⟨v_bv, ⟨⟩⟩ m_v hLv ⟨rfl, hv_le, mrk_v, hmrk_v, hz_v, hab_v, hm_v⟩
      c0_hsplit
      · have hv_lt : v_bv.toNat < s.core.cur_vars := by c0_grind
        have hv_arr :
            v_bv.toNat < ({ bf with tmp := tmp_c, mrk := mrk_v }.st s).core.mrk.length := by
          rw [hmrk_v]; omega
        have hv1 : (v_bv + 1).toNat = v_bv.toNat + 1 := by c0_bound
        c0_hsteps!
        exact hLv (s.core.cur_vars - (v_bv.toNat + 1)) (v_bv + 1, ()) _ (by omega)
          ⟨by rw [hv1], by rw [hv1]; omega, mrk_v.set v_bv.toNat 0#8, by simp [hmrk_v],
            fun w hw => by
              rw [hv1] at hw
              by_cases hweq : w = v_bv.toNat
              · subst w; rw [List.getElem?_set_self hv_arr]
              · rw [List.getElem?_set_ne (Ne.symm hweq)]; exact hz_v w (by omega),
            fun w hw => by rw [List.getElem?_set_ne (by omega)]; exact hab_v w hw, hm⟩
      · have hveq : v_bv.toNat = s.core.cur_vars := by c0_grind
        rw [hveq] at hz_v
        exact hJ mrk_v m_v hmrk_v (m6_clear_full_done hclear hshrink.mrk_above hz_v hab_v) hm_v
    · intro Lv hLv; c0_hsteps!
      exact hLv s.core.cur_vars (0#64, ()) m ⟨rfl, Nat.zero_le _, bf.mrk, hshrink.len.mrk_len,
        fun _ h => by simp at h, fun _ _ => rfl, hm⟩
  · have hmcf0 : bf.mcf = 0#64 := by c0_grind
    c0_hsteps_nogrp
    refine wp_loop_group (ts := [i64]) (fun n (z_bv, ()) m_z =>
        n = bf.mcl - z_bv.toNat ∧
        ∃ mrk_z, M6ClearListInv c s bf.mclr bf.mcl z_bv.toNat mrk_z ∧
          (FullMem c ({ bf with tmp := tmp_c, mrk := mrk_z }.st s) ⋆ R) m_z) ?_ ?_
    · rintro Lz n_z ⟨z_bv, ⟨⟩⟩ m_z hLz ⟨rfl, mrk_z, hcinv_z, hm_z⟩
      c0_hsplit
      · have hz_lt : z_bv.toNat < bf.mcl := by
          have := hshrink.len.mcl_le; c0_grind
        have hz_arr :
            z_bv.toNat < ({ bf with tmp := tmp_c, mrk := mrk_z }.st s).core.min_clr.length := by
          rw [hshrink.len.mclr_len]; have := hshrink.len.mcl_le; omega
        c0_hsteps_nogrp
        refine wp_join_group (ts := []) (fun () m_n =>
            ∃ mrk', M6ClearListInv c s bf.mclr bf.mcl (z_bv.toNat + 1) mrk' ∧
              (FullMem c ({ bf with tmp := tmp_c, mrk := mrk' }.st s) ⋆ R) m_n) ?_ ?_
        · rintro _ ⟨⟩ m_n ⟨mrk', hcinv', hm'⟩
          have hz1 : (z_bv + 1).toNat = z_bv.toNat + 1 := by
            have := hshrink.len.mcl_le; c0_bound
          c0_hsteps!
          exact hLz (bf.mcl - (z_bv.toNat + 1)) (z_bv + 1, ()) m_n (by omega)
            ⟨by rw [hz1], mrk', by rw [hz1]; exact hcinv', hm'⟩
        · intro Jn hJn; c0_hsplit
          · have hzv_lt : (bf.mclr[z_bv.toNat]'hz_arr).toNat < s.core.cur_vars := by c0_grind
            have hzv_arr : ((bf.mclr[z_bv.toNat]'hz_arr).setWidth 64).toNat <
                ({ bf with tmp := tmp_c, mrk := mrk_z }.st s).core.mrk.length := by
              rw [bv_c0_zext32_64, hcinv_z.mrk_len]; omega
            c0_hsteps!
            refine hJn () _ ⟨_, ?_, hm⟩
            rw [bv_c0_zext32_64, ← Option.getD_some (b := 0#32) (a := bf.mclr[z_bv.toNat]'hz_arr),
              ← List.getElem?_eq_getElem hz_arr]
            exact m6_clear_list_step_lt hcinv_z hz_lt hcv (by
              rw [List.getElem?_eq_getElem hz_arr, Option.getD_some]; exact hzv_lt)
          · have hzv_ge : s.core.cur_vars ≤ (bf.mclr[z_bv.toNat]?.getD 0#32).toNat := by
              rw [List.getElem?_eq_getElem hz_arr, Option.getD_some]; c0_grind
            exact hJn () m_z ⟨mrk_z, m6_clear_list_step_ge hcinv_z hz_lt hzv_ge, hm_z⟩
      · have hzeq : z_bv.toNat = bf.mcl := by
          have := hshrink.len.mcl_le; have := hcinv_z.z_le; c0_grind
        rw [hzeq] at hcinv_z
        exact hJ mrk_z m_z hcinv_z.mrk_len (m6_clear_list_done hclear hcinv_z) hm_z
    · intro Lz hLz; c0_hsteps!
      exact hLz bf.mcl (0#64, ()) m ⟨rfl, bf.mrk, m6_clear_list_init hmcf0 hshrink (fun _ _ => rfl),
        hm⟩

/-! ## 2. Double-Reversal Output Phase -/

private def m6RevInnerExpr {V : Ty → Type} {C : List Ty → Type} {rs : List Ty}
    (pTmp pLvl keep : V i64) (Jfin : C []) : Expr V C rs :=
  let op64 (c : OpCode [i64, i64] [i64]) (a b : Arg V i64) := Op.mk c (a, b, ())
  .group (sig := [[i64]]) (fun Lrb => .cons (fun rb =>
    .let_ (Op.mk (.cmp .ult i64 .bool rfl) (.var rb.fst, .var keep, ())) fun hrb =>
    .jnz (.var hrb.fst)
      (.let_ (op64 (.mul i64) (.var rb.fst) (.imm 4)) fun rboff =>
       .let_ (op64 (.add i64) (.var pTmp) (.var rboff.fst)) fun rbaddr =>
       .load i32 (.var rbaddr.fst) fun rblit =>
       .let_ (Op.mk (.zext 32 64) (.var rblit, ())) fun rbl64 =>
       .let_ (Op.mk (.sext 32 64) (.imm 1, ())) fun one64 =>
       .let_ (Op.mk (.lshr i64) (.var rbl64.fst, .var one64.fst, ())) fun rbv64 =>
       .let_ (op64 (.mul i64) (.var rbv64.fst) (.imm 4)) fun rbloff =>
       .let_ (op64 (.add i64) (.var pLvl) (.var rbloff.fst)) fun rbladdr =>
       .load i32 (.var rbladdr.fst) fun rl =>
       .let_ (op64 (.add i64) (.var rb.fst) (.imm 1)) fun reb =>
       .group (sig := [[i64]]) (fun Lre => .cons (fun re =>
         .group (sig := [[]]) (fun _Jr => .cons (fun _ =>
           .let_ (op64 (.sub i64) (.var re.fst) (.imm 1)) fun rhi0 =>
           .group (sig := [[i64, i64]]) (fun Lsw => .cons (fun psw =>
             .let_ (Op.mk (.cmp .ult i64 .bool rfl) (.var psw.fst, .var psw.snd.fst, ()))
               fun hsw =>
             .jnz (.var hsw.fst)
               (.let_ (op64 (.mul i64) (.var psw.fst) (.imm 4)) fun o1 =>
                .let_ (op64 (.add i64) (.var pTmp) (.var o1.fst)) fun a1 =>
                .load i32 (.var a1.fst) fun v1 =>
                .let_ (op64 (.mul i64) (.var psw.fst) (.imm 4)) fun o2 =>
                .let_ (op64 (.add i64) (.var pTmp) (.var o2.fst)) fun a2 =>
                .let_ (op64 (.mul i64) (.var psw.snd.fst) (.imm 4)) fun o3 =>
                .let_ (op64 (.add i64) (.var pTmp) (.var o3.fst)) fun a3 =>
                .load i32 (.var a3.fst) fun v2 =>
                .store (.var v2) (.var a2.fst)
                  (.let_ (op64 (.mul i64) (.var psw.snd.fst) (.imm 4)) fun o4 =>
                   .let_ (op64 (.add i64) (.var pTmp) (.var o4.fst)) fun a4 =>
                   .store (.var v1) (.var a4.fst)
                     (.let_ (op64 (.add i64) (.var psw.fst) (.imm 1)) fun lo1 =>
                      .let_ (op64 (.sub i64) (.var psw.snd.fst) (.imm 1)) fun hi1 =>
                      .jump Lsw.fst (.var lo1.fst, .var hi1.fst, ()))))
               (.jump Lrb.fst (.var re.fst, ()))) .nil)
             (fun Lsw => .jump Lsw.fst (.var rb.fst, .var rhi0.fst, ()))) .nil)
           fun Jre =>
         .let_ (Op.mk (.cmp .ult i64 .bool rfl) (.var re.fst, .var keep, ())) fun hre =>
         .jnz (.var hre.fst)
           (.let_ (op64 (.mul i64) (.var re.fst) (.imm 4)) fun reoff =>
            .let_ (op64 (.add i64) (.var pTmp) (.var reoff.fst)) fun readdr =>
            .load i32 (.var readdr.fst) fun relit =>
            .let_ (Op.mk (.zext 32 64) (.var relit, ())) fun rel64 =>
            .let_ (Op.mk (.sext 32 64) (.imm 1, ())) fun one64b =>
            .let_ (Op.mk (.lshr i64) (.var rel64.fst, .var one64b.fst, ())) fun rev64 =>
            .let_ (op64 (.mul i64) (.var rev64.fst) (.imm 4)) fun reloff =>
            .let_ (op64 (.add i64) (.var pLvl) (.var reloff.fst)) fun reladdr =>
            .load i32 (.var reladdr.fst) fun rel =>
            .let_ (Op.mk (.cmp .eq i32 .bool rfl) (.var rel, .var rl, ())) fun heq =>
            .jnz (.var heq.fst)
              (.let_ (op64 (.add i64) (.var re.fst) (.imm 1)) fun re1 =>
               .jump Lre.fst (.var re1.fst, ()))
              (.jump Jre.fst ()))
           (.jump Jre.fst ())) .nil)
         (fun Lre => .jump Lre.fst (.var reb.fst, ())))
      (.jump Jfin ())) .nil) (fun Lrb => .jump Lrb.fst (.imm 1, ()))

private theorem m6_rev_inner_wp {Γ : Env} {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {orig_tlen : Nat} {keep_bv : BitVec 64}
    {tmp_r : List (BitVec 32)} {bf : ShrinkScratch} {conf' : BitVec 64}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post []} {X : XPost} {Jfin : Cont []}
    (hlvl_len : s.core.lvl.length = c.max_vars)
    (hot_le : orig_tlen ≤ s.core.cur_vars) (hcv : s.core.cur_vars ≤ c.max_vars)
    (hkeep_gt2 : 2 < keep_bv.toNat)
    (hout : M6TmpOutInv c F0 F_cur s orig_tlen keep_bv.toNat tmp_r)
    (hm : (FullMem c (m6KSt s { bf with tmp := tmp_r } keep_bv.toNat conf') ⋆ R) m)
    (hJ : ∀ (tmp_o : List (BitVec 32)) m_o,
      M6TmpOutInv c F0 F_cur s orig_tlen keep_bv.toNat tmp_o →
      (FullMem c (m6KSt s { bf with tmp := tmp_o } keep_bv.toNat conf') ⋆ R) m_o →
      wp Γ Q X (.jump Jfin ()) m_o) :
    wp Γ Q X (m6RevInnerExpr c.pTmp c.pLevel keep_bv Jfin) m := by
  have hmx := c.hmaxv; unfold Ref.dimacsBound at hmx
  dsimp only [m6RevInnerExpr]
  refine wp_loop_group (ts := [i64]) (fun n (rb_bv, ()) m_r =>
      n = keep_bv.toNat - rb_bv.toNat ∧ 1 ≤ rb_bv.toNat ∧ rb_bv.toNat ≤ keep_bv.toNat ∧
      ∃ tmp_1, M6TmpOutInv c F0 F_cur s orig_tlen keep_bv.toNat tmp_1 ∧
        (FullMem c (m6KSt s { bf with tmp := tmp_1 } keep_bv.toNat conf') ⋆ R) m_r) ?_ ?_
  · rintro Lrb n_r ⟨rb_bv, ⟨⟩⟩ m_r hLrb ⟨rfl, hrb1, hrbk, tmp_1, hout_1, hm_r⟩
    c0_hsplit
    · have hrb_lt : rb_bv.toNat < keep_bv.toNat := by c0_grind
      have hrb_arr : rb_bv.toNat < tmp_1.length := by
        rw [hout_1.tmp_len]; have := hout_1.keep_le; omega
      have hrb_lvl : (tmp_1[rb_bv.toNat]'hrb_arr).toNat / 2 < s.core.cur_vars := by
        have := (hout_1.elem_ok rb_bv.toNat hrb1 hrb_lt).1
        rw [List.getElem?_eq_getElem hrb_arr, Option.getD_some] at this; omega
      have hrb_larr : ((tmp_1[rb_bv.toNat]'hrb_arr).setWidth 64 >>>
          ((BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64)).toNat < s.core.lvl.length := by
        rw [m7_ushr1_mod, hlvl_len]; omega
      c0_hsteps_nogrp
      refine wp_loop_group (ts := [i64]) (fun n_e (re_bv, ()) m_e =>
          n_e = keep_bv.toNat - re_bv.toNat ∧ rb_bv.toNat + 1 ≤ re_bv.toNat ∧
          re_bv.toNat ≤ keep_bv.toNat ∧ m_e = m_r) ?_ ?_
      · rintro Lre n_e ⟨re_bv, ⟨⟩⟩ m_e hLre ⟨rfl, hre_ge, hre_le, rfl⟩
        rw [Blocks.get_here]
        refine wp_join_group (ts := []) (fun () m_j => m_j = m_e) ?_ ?_
        · rintro _ ⟨⟩ m_j rfl
          have hrhi_bv : (re_bv - 1).toNat = re_bv.toNat - 1 := m7_bv64_sub1 (by omega)
          c0_hsteps_nogrp
          refine wp_loop_group (ts := [i64, i64]) (fun n_s (lo_bv, hi_bv, ()) m_s =>
              n_s = hi_bv.toNat - lo_bv.toNat ∧ rb_bv.toNat ≤ lo_bv.toNat ∧
              hi_bv.toNat < re_bv.toNat ∧
              ∃ tmp_s1, M6TmpOutInv c F0 F_cur s orig_tlen keep_bv.toNat tmp_s1 ∧
                (FullMem c (m6KSt s { bf with tmp := tmp_s1 } keep_bv.toNat conf') ⋆ R) m_s)
            ?_ ?_
          · rintro Lsw n_s ⟨lo_bv, hi_bv, ⟨⟩⟩ m_s hLsw ⟨rfl, hlo_rb, hhi_re, tmp_s1, hout_s1, hm_s⟩
            c0_hsplit
            · have hlohi : lo_bv.toNat < hi_bv.toNat := by c0_grind
              have hlo_arr : lo_bv.toNat < tmp_s1.length := by
                rw [hout_s1.tmp_len]; have := hout_s1.keep_le; omega
              have hhi_arr : hi_bv.toNat < tmp_s1.length := by
                rw [hout_s1.tmp_len]; have := hout_s1.keep_le; omega
              have hlo1 : (lo_bv + 1).toNat = lo_bv.toNat + 1 := by
                have := hout_s1.keep_le; c0_bound
              have hhi1 : (hi_bv - 1).toNat = hi_bv.toNat - 1 := m7_bv64_sub1 (by omega)
              c0_hsteps!
              have hout_s3 := m6TmpOutInv_swap hot_le hcv hout_s1 (by omega) hlohi (by omega)
              have hhm_2 : (FullMem c (m6KSt s { bf with
                  tmp := (tmp_s1.set lo_bv.toNat (tmp_s1[hi_bv.toNat]?.getD 0#32)).set hi_bv.toNat
                    (tmp_s1[lo_bv.toNat]?.getD 0#32) } keep_bv.toNat conf') ⋆ R) m := by
                simpa only [List.getElem?_eq_getElem hlo_arr, List.getElem?_eq_getElem hhi_arr,
                  Option.getD_some] using hm
              exact hLsw ((hi_bv - 1).toNat - (lo_bv + 1).toNat)
                (lo_bv + 1, hi_bv - 1, ()) m (by omega)
                ⟨rfl, by rw [hlo1]; omega, by rw [hhi1]; omega, _, hout_s3, hhm_2⟩
            · exact hLrb (keep_bv.toNat - re_bv.toNat) (re_bv, ()) m_s (by omega)
                ⟨rfl, by omega, hre_le, tmp_s1, hout_s1, hm_s⟩
          · intro Lsw hLsw; c0_hsteps!
            exact hLsw ((re_bv - 1).toNat - rb_bv.toNat) (rb_bv, re_bv - 1, ()) m_j
              ⟨rfl, le_refl _, by rw [hrhi_bv]; omega, tmp_1, hout_1, hm_r⟩
        · intro Jre hJre; c0_hsplit
          · have hre_lt : re_bv.toNat < keep_bv.toNat := by c0_grind
            have hre_arr : re_bv.toNat < tmp_1.length := by
              rw [hout_1.tmp_len]; have := hout_1.keep_le; omega
            have hre_lvl : (tmp_1[re_bv.toNat]'hre_arr).toNat / 2 < s.core.cur_vars := by
              have := (hout_1.elem_ok re_bv.toNat (by omega) hre_lt).1
              rw [List.getElem?_eq_getElem hre_arr, Option.getD_some] at this; omega
            have hre_larr : ((tmp_1[re_bv.toNat]'hre_arr).setWidth 64 >>>
                ((BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64)).toNat < s.core.lvl.length := by
              rw [m7_ushr1_mod, hlvl_len]; omega
            c0_hsteps_nogrp; c0_hsplit
            · have hre1 : (re_bv + 1).toNat = re_bv.toNat + 1 := by
                have := hout_1.keep_le; c0_bound
              c0_hsteps!
              exact hLre (keep_bv.toNat - (re_bv.toNat + 1)) (re_bv + 1, ()) m_e
                (by omega) ⟨by rw [hre1], by rw [hre1]; omega, by rw [hre1]; omega, rfl⟩
            · exact hJre () m_e rfl
          · exact hJre () m_e rfl
      · intro Lre hLre
        have hrb1' : (rb_bv + 1).toNat = rb_bv.toNat + 1 := by
          have := hout_1.keep_le; c0_bound
        c0_hsteps!
        exact hLre (keep_bv.toNat - (rb_bv.toNat + 1)) (rb_bv + 1, ()) m_r
          ⟨by rw [hrb1'], by rw [hrb1']; exact le_refl _, by rw [hrb1']; omega, rfl⟩
    · exact hJ tmp_1 m_r hout_1 hm_r
  · intro Lrb hLrb; c0_hsteps!
    exact hLrb (keep_bv.toNat - 1) (1#64, ()) m ⟨rfl, by simp, by simp; omega, tmp_r, hout, hm⟩

private def m6RevOuterExpr {V : Ty → Type} {C : List Ty → Type} {rs : List Ty}
    (pTmp pLvl keep : V i64) (Jfin : C []) : Expr V C rs :=
  let op64 (c : OpCode [i64, i64] [i64]) (a b : Arg V i64) := Op.mk c (a, b, ())
  .let_ (Op.mk (.cmp .ugt i64 .bool rfl) (.var keep, .imm 2, ())) fun hgt2 =>
  .jnz (.var hgt2.fst)
    (.let_ (op64 (.sub i64) (.var keep) (.imm 1)) fun hi0 =>
     .group (sig := [[i64, i64]]) (fun Lsw => .cons (fun psw =>
       .let_ (Op.mk (.cmp .ult i64 .bool rfl) (.var psw.fst, .var psw.snd.fst, ())) fun hsw =>
       .jnz (.var hsw.fst)
         (.let_ (op64 (.mul i64) (.var psw.fst) (.imm 4)) fun o1 =>
          .let_ (op64 (.add i64) (.var pTmp) (.var o1.fst)) fun a1 =>
          .load i32 (.var a1.fst) fun v1 =>
          .let_ (op64 (.mul i64) (.var psw.fst) (.imm 4)) fun o2 =>
          .let_ (op64 (.add i64) (.var pTmp) (.var o2.fst)) fun a2 =>
          .let_ (op64 (.mul i64) (.var psw.snd.fst) (.imm 4)) fun o3 =>
          .let_ (op64 (.add i64) (.var pTmp) (.var o3.fst)) fun a3 =>
          .load i32 (.var a3.fst) fun v2 =>
          .store (.var v2) (.var a2.fst)
            (.let_ (op64 (.mul i64) (.var psw.snd.fst) (.imm 4)) fun o4 =>
             .let_ (op64 (.add i64) (.var pTmp) (.var o4.fst)) fun a4 =>
             .store (.var v1) (.var a4.fst)
               (.let_ (op64 (.add i64) (.var psw.fst) (.imm 1)) fun lo1 =>
                .let_ (op64 (.sub i64) (.var psw.snd.fst) (.imm 1)) fun hi1 =>
                .jump Lsw.fst (.var lo1.fst, .var hi1.fst, ()))))
         (m6RevInnerExpr pTmp pLvl keep Jfin)) .nil)
       (fun Lsw => .jump Lsw.fst (.imm 1, .var hi0.fst, ())))
    (.jump Jfin ())

private theorem m6_rev_outer_wp {Γ : Env} {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {orig_tlen : Nat} {keep_bv : BitVec 64}
    {tmp_c : List (BitVec 32)} {bf : ShrinkScratch} {conf' : BitVec 64}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post []} {X : XPost} {Jfin : Cont []}
    (hlvl_len : s.core.lvl.length = c.max_vars)
    (hot_le : orig_tlen ≤ s.core.cur_vars) (hcv : s.core.cur_vars ≤ c.max_vars)
    (hout : M6TmpOutInv c F0 F_cur s orig_tlen keep_bv.toNat tmp_c)
    (hm : (FullMem c (m6KSt s { bf with tmp := tmp_c } keep_bv.toNat conf') ⋆ R) m)
    (hJ : ∀ (tmp_o : List (BitVec 32)) m_o,
      M6TmpOutInv c F0 F_cur s orig_tlen keep_bv.toNat tmp_o →
      (FullMem c (m6KSt s { bf with tmp := tmp_o } keep_bv.toNat conf') ⋆ R) m_o →
      wp Γ Q X (.jump Jfin ()) m_o) :
    wp Γ Q X (m6RevOuterExpr c.pTmp c.pLevel keep_bv Jfin) m := by
  have hmx := c.hmaxv; unfold Ref.dimacsBound at hmx
  dsimp only [m6RevOuterExpr]
  c0_hsplit
  · have hkeep_gt2 : 2 < keep_bv.toNat := by c0_grind
    have hhi0 : (keep_bv - 1).toNat = keep_bv.toNat - 1 := m7_bv64_sub1 (by omega)
    refine wp_loop_group (ts := [i64, i64]) (fun n (lo_bv, hi_bv, ()) m_s =>
        n = hi_bv.toNat - lo_bv.toNat ∧ 1 ≤ lo_bv.toNat ∧ hi_bv.toNat < keep_bv.toNat ∧
        ∃ tmp_s1, M6TmpOutInv c F0 F_cur s orig_tlen keep_bv.toNat tmp_s1 ∧
          (FullMem c (m6KSt s { bf with tmp := tmp_s1 } keep_bv.toNat conf') ⋆ R) m_s) ?_ ?_
    · rintro Lsw n_s ⟨lo_bv, hi_bv, ⟨⟩⟩ m_s hLsw ⟨rfl, hlo1, hhik, tmp_s1, hout_s1, hm_s⟩
      c0_hsplit
      · have hlohi : lo_bv.toNat < hi_bv.toNat := by c0_grind
        have hlo_arr : lo_bv.toNat < tmp_s1.length := by
          rw [hout_s1.tmp_len]; have := hout_s1.keep_le; omega
        have hhi_arr : hi_bv.toNat < tmp_s1.length := by
          rw [hout_s1.tmp_len]; have := hout_s1.keep_le; omega
        have hlo1' : (lo_bv + 1).toNat = lo_bv.toNat + 1 := by
          have := hout_s1.keep_le; c0_bound
        have hhi1' : (hi_bv - 1).toNat = hi_bv.toNat - 1 := m7_bv64_sub1 (by omega)
        c0_hsteps!
        have hout_s3 := m6TmpOutInv_swap hot_le hcv hout_s1 hlo1 hlohi hhik
        have hhm_2 : (FullMem c (m6KSt s { bf with
            tmp := (tmp_s1.set lo_bv.toNat (tmp_s1[hi_bv.toNat]?.getD 0#32)).set hi_bv.toNat
              (tmp_s1[lo_bv.toNat]?.getD 0#32) } keep_bv.toNat conf') ⋆ R) m := by
          simpa only [List.getElem?_eq_getElem hlo_arr, List.getElem?_eq_getElem hhi_arr,
            Option.getD_some] using hm
        exact hLsw ((hi_bv - 1).toNat - (lo_bv + 1).toNat)
          (lo_bv + 1, hi_bv - 1, ()) m (by omega)
          ⟨rfl, by rw [hlo1']; omega, by rw [hhi1']; omega, _, hout_s3, hhm_2⟩
      · exact m6_rev_inner_wp hlvl_len hot_le hcv hkeep_gt2 hout_s1 hm_s hJ
    · intro Lsw hLsw; c0_hsteps!
      exact hLsw ((keep_bv - 1).toNat - 1) (1#64, keep_bv - 1, ()) m
        ⟨rfl, le_refl _, by rw [hhi0]; omega, tmp_c, hout, hm⟩
  · exact hJ tmp_c m hout hm

/-! ## 3. Main WP Theorem: `full_min_shrink_m6_wp` -/

public section

theorem full_min_shrink_m6_wp (Γ : Env)
    (hST : Γ.Has "full_sort_tmp" Spec.fullSortTmpSpec)
    (hMm : Γ.Has "full_min_mark" Spec.fullMinMarkSpec)
    (hSB : Γ.Has "full_shrink_blk_bool_m8" Spec.fullShrinkBlkBoolSpec)
    (hDfs : Γ.Has "full_min_lit_dfs_m8" Spec.fullMinLitDfsSpec) :
    ∀ args m Q X, Spec.fullMinShrinkSpec args m Q X →
      Func.wp Γ full_min_shrink_m6_body args m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X hs
  obtain ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hclear, ht_pos, ht_cv, hnd, hEnt, hlits, hlvls,
      h0lvl, hm, hQ⟩ := Spec.fullMinShrinkSpec_elim hs
  have hlen0 := hlen.core_ok; have hcv := hlen0.cur_vars_le
  have hmx := c.hmaxv; unfold Ref.dimacsBound at hmx
  have hot_bv : (BitVec.ofNat 64 s.core.tmp_len).toNat = s.core.tmp_len := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hcv_bv : (BitVec.ofNat 64 s.core.cur_vars).toNat = s.core.cur_vars := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  unfold Func.wp full_min_shrink_m6_body; dsimp only [full_min_shrink_m6_body]
  c0_hsteps_nogrp
  refine wp_join_group (ts := []) (fun () m_c =>
      ∃ conf', (FullMem c { s with scratch := { s.scratch with conflicts := conf' } } ⋆ R) m_c)
    ?_ ?_
  · rintro _ ⟨⟩ m_c ⟨conf', hm_c⟩
    let s_c : FullState := { s with scratch := { s.scratch with conflicts := conf' } }
    have hlen_c : s_c.LengthsOk c :=
      ⟨hlen.core_ok, by cases hlen.scratch_ok; constructor <;> assumption⟩
    have hcore_c : FullOtfsCoreInv c F0 s_c := ⟨hlen_c, F_cur, hw⟩
    c0_hsteps_nogrp
    refine wp_join_group (ts := []) (fun () m_e =>
        m_e = m_c ∧ s.core.tmp_len = 1) ?_ ?_
    · rintro _ ⟨⟩ m_e ⟨rfl, _⟩
      c0_hsteps!
      have hm1' : (FullMem c (Spec.fullMinShrinkState s s.core.tmp s.core.tmp_len s.core.mrk
          s.core.min_clr s.scratch.shrink_stk s.scratch.wsort s.scratch.work_stk1
          s.core.min_clr_len s.core.min_clr_full conf'
          (s.scratch.learned_lits + BitVec.ofNat 64 s.core.tmp_len)
          s.scratch.min_removed s.scratch.search_ticks s.scratch.res_sz) ⋆ R) m := hm
      have hlen_m1 : (Spec.fullMinShrinkState s s.core.tmp s.core.tmp_len s.core.mrk s.core.min_clr
          s.scratch.shrink_stk s.scratch.wsort s.scratch.work_stk1 s.core.min_clr_len
          s.core.min_clr_full conf' (s.scratch.learned_lits + BitVec.ofNat 64 s.core.tmp_len)
          s.scratch.min_removed s.scratch.search_ticks s.scratch.res_sz).LengthsOk c :=
        ⟨hlen.core_ok, by cases hlen.scratch_ok; constructor <;> assumption⟩
      exact hQ s.core.tmp s.core.tmp_len s.core.mrk s.core.min_clr s.scratch.shrink_stk
        s.scratch.wsort s.scratch.work_stk1 s.core.min_clr_len s.core.min_clr_full conf'
        (s.scratch.learned_lits + BitVec.ofNat 64 s.core.tmp_len) s.scratch.min_removed
        s.scratch.search_ticks s.scratch.res_sz m hlen_m1 (m6Witness_fin hw)
        (m6LitMarksClear_of hclear hclear.1 rfl) ht_pos (le_refl _) rfl hnd
        (fun j hj1 _ => absurd hj1 (by omega)) hEnt hm1'
    · intro _Jearly hJearly; c0_hsplit
      · exact hJearly () m_c ⟨rfl, by c0_grind⟩
      · c0_hsplit
        · exfalso; c0_grind
        · c0_hsteps_nogrp; apply wp_call_of_spec; apply hST
          refine Spec.fullSortTmpSpec_of hlen_c (by change s.core.tmp_len ≤ c.max_vars; omega)
            (fun k _ hk => by
              change (s.core.tmp[k]?.getD 0#32).toNat < 2 * c.max_vars
              have := (hlits k hk).1; omega)
            hm_c ?_
          intro tmp_s wsort_s m_s st_s hlen_s htmp_s _hw_s hperm_s h0_s hmap_s _hmap2_s
            hsorted_s _hex_s hm_s
          dsimp only [st_s, s_c] at hlen_s hm_s hsorted_s
          obtain ⟨hnd_s, hEnt_s, h0_eq_s, h0_lvl_s, hlits_s, hlvls_s⟩ := m6_sort_post hlen hw
            ht_pos ht_cv hnd hEnt hlits hlvls h0lvl htmp_s hperm_s h0_s hmap_s
          c0_hsteps_nogrp
          let s_w : FullState := { s_c with scratch := { s_c.scratch with wsort := wsort_s } }
          have hcore_w : FullOtfsCoreInv c F0 s_w :=
            ⟨⟨hlen_c.core_ok, { hlen_c.scratch_ok with wsort_len := hlen_s.scratch_ok.wsort_len }⟩,
              F_cur, hw⟩
          let b_pre : ShrinkScratch :=
            { ShrinkScratch.ofState s_w with tmp := tmp_s, mcl := 0, mcf := 0#64 }
          have hmin0 : FullMinMarkInv (b_pre.st s_w).core [] := by
            have hinit := fullMinMarkInv_init hcore_c
              (fun v hv => by dsimp only [s_c] at hv; exact hclear.1 v (by omega)) []
            exact ⟨hinit.mrk_dom, fun _ v hv hnz => by
              dsimp only [b_pre, ShrinkScratch.st, Spec.s13BlkState, s_w, s_c] at hv hnz
              rw [hclear.1 v (by omega)] at hnz; exact absurd rfl hnz, hinit.rem_sound⟩
          have hno8_0 : ∀ w < s_w.core.cur_vars, (s.core.mrk[w]?.getD 0#8 &&& 8#8) = 0#8 :=
            fun w hw' => by
              dsimp only [s_w, s_c] at hw'; rw [hclear.1 w (by omega)]; rfl
          refine m6_mark_loop_wp hMm hcore_w htmp_s hot_bv ht_cv
            (fun k hk => ⟨(hlits_s k hk).1, (hlits_s k hk).2.1⟩)
            hlen0.mrk_len hlen0.min_clr_len_arr hlen.scratch_ok.shrink_stk_len
            hlen_s.scratch_ok.wsort_len hlen.scratch_ok.work_stk1_len hno8_0 hmin0 hm
            fun b1 m_mk hbt hbs hbw hbw1 hbtk hbr hb1_len hmin1 hno8_1 hab1 hdone1 hm_mk => ?_
          have hnof := m6_take_map_filter_no_sent (by rw [htmp_s]; omega)
            (fun k hk => (hlits_s k hk).2.2)
          have hmin1_f : FullMinMarkInv (b1.st s_w).core
              (((tmp_s.take s.core.tmp_len).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat) := by
            rw [hnof]; exact hmin1
          have hinv1 : M6ShrinkLoopInv c F0 F_cur s_w s.core.tmp_len tmp_s s_w.core.mrk 1 b1 :=
            ⟨le_refl _, ht_pos, hb1_len, by rw [hbt], fun _ _ _ => by rw [hbt],
              fun k hk _ => by
                rw [hbt] at *; exact ⟨(hlits_s k hk).1, (hlits_s k hk).2.1, hdone1 k hk⟩,
              fun k hk1 hk2 _ => by rw [hbt]; exact hlvls_s k hk1 hk2,
              fun i j hi1 hij hj _ _ => by rw [hbt]; exact hsorted_s i j hi1 hij hj,
              fun _ k hk1 _ _ => absurd hk1 (by omega),
              by rw [hbt, hnof]; exact hnd_s, by rw [hbt]; exact hmin1_f,
              by rw [hbt, hnof]; exact hEnt_s, hno8_1, hab1⟩
          refine m6_shrink_loop_wp hSB hDfs hcore_w hw hcv_bv hot_bv ht_pos ht_cv h0_lvl_s
            hlits_s hlvls_s hsorted_s hinv1 hm_mk fun bf m_f hsh_f hm_f => ?_
          refine m6_compact_loop_wp (s := s_w)
            (after := fun keep =>
              let op64 (c : OpCode [i64, i64] [i64]) (a b : Arg Val i64) := Op.mk c (a, b, ())
              .let_ (op64 (.add i64) (.var c.hdr) (.imm 72)) fun pm0 =>
              .load i64 (.var pm0.fst) fun pMrk =>
              .group (sig := [[]]) (fun _Jpost => .cons (fun _ =>
                .let_ (op64 (.add i64) (.var c.hdr) (.imm 272)) fun pmcl =>
                .store (t := i64) (.imm 0) (.var pmcl.fst)
                  (.let_ (op64 (.add i64) (.var c.hdr) (.imm 280)) fun pmcf =>
                   .store (t := i64) (.imm 0) (.var pmcf.fst)
                     (.let_ (op64 (.add i64) (.var c.hdr) (.imm 192)) fun ptl =>
                      .store (.var keep) (.var ptl.fst)
                        (.group (sig := [[]]) (fun _Jfin => .cons (fun _ =>
                           .let_ (op64 (.add i64) (.var c.hdr) (.imm 352)) fun pmrem1 =>
                           .load i64 (.var pmrem1.fst) fun mrem =>
                           .let_ (op64 (.sub i64) (.var (BitVec.ofNat 64 s.core.tmp_len))
                             (.var keep)) fun diff =>
                           .let_ (op64 (.add i64) (.var mrem) (.var diff.fst)) fun mrem' =>
                           .let_ (op64 (.add i64) (.var c.hdr) (.imm 352)) fun pmrem2 =>
                           .store (.var mrem'.fst) (.var pmrem2.fst)
                             (.let_ (op64 (.add i64) (.var c.hdr) (.imm 344)) fun pll1 =>
                              .load i64 (.var pll1.fst) fun ll =>
                              .let_ (op64 (.add i64) (.var ll) (.var keep)) fun ll' =>
                              .let_ (op64 (.add i64) (.var c.hdr) (.imm 344)) fun pll2 =>
                              .store (.var ll'.fst) (.var pll2.fst) (.ret ()))) .nil) fun Jfin =>
                         m6RevOuterExpr c.pTmp c.pLevel keep Jfin.fst)))) .nil) fun Jpost =>
                m6ClearMrkExpr c.hdr pMrk (BitVec.ofNat 64 s.core.cur_vars) Jpost.fst)
            hot_bv ht_pos ht_cv hcv h0_eq_s (hlits_s 0 ht_pos).2.2 hsh_f hm_f
            fun keep_bv tmp_c m_c _hkeep_le hout_c hm_c => ?_
          c0_hsteps_nogrp
          refine wp_join_group (ts := []) (fun () m_mrk =>
              ∃ mrk', mrk'.length = c.max_vars ∧ (∀ w < c.max_vars, mrk'[w]?.getD 0#8 = 0#8) ∧
                (FullMem c ({ bf with tmp := tmp_c, mrk := mrk' }.st s_w) ⋆ R) m_mrk) ?_ ?_
          · rintro _ ⟨⟩ m_mrk ⟨mrk', hmrk_len', hmrk0', hm_mrk⟩
            c0_hsteps_nogrp
            refine wp_join_group (ts := []) (fun () m_fin =>
                ∃ tmp_o, M6TmpOutInv c F0 F_cur s_w s.core.tmp_len keep_bv.toNat tmp_o ∧
                  (FullMem c (m6KSt s_w { bf with tmp := tmp_o, mrk := mrk', mcl := 0, mcf := 0#64 }
                    keep_bv.toNat conf') ⋆ R) m_fin) ?_ ?_
            · rintro _ ⟨⟩ m_fin ⟨tmp_o, hout_o, hm_fin⟩
              c0_hsteps!
              obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ :=
                m6_finish_spec hcore_w.1 hw hclear ht_cv
                rfl hout_o hmrk_len' hsh_f.len.mclr_len hsh_f.len.sstk_len hsh_f.len.wsort_len
                hsh_f.len.ws1_len hmrk0' (conf' := conf')
                (llits' := s.scratch.learned_lits + keep_bv)
                (mrem' := s.scratch.min_removed + (BitVec.ofNat 64 s.core.tmp_len - keep_bv))
                (ticks' := bf.ticks) (resSz' := bf.resSz)
              exact hQ tmp_o keep_bv.toNat mrk' bf.mclr bf.sstk bf.wsort bf.ws1 0 0#64 conf'
                (s.scratch.learned_lits + keep_bv)
                (s.scratch.min_removed + (BitVec.ofNat 64 s.core.tmp_len - keep_bv))
                bf.ticks bf.resSz m h1 h2 h3 h4 h5 h6 h7 h8 h9 hm
            · intro Jfin hJfin
              exact m6_rev_outer_wp (s := s_w)
                (bf := { bf with mrk := mrk', mcl := 0, mcf := 0#64 }) (conf' := conf')
                hlen0.lvl_len ht_cv hcv hout_c hm fun tmp_o m_o hout_o hm_o => by
                  rw [wp]; exact hJfin () m_o ⟨tmp_o, hout_o, hm_o⟩
          · intro Jpost hJpost
            exact m6_clear_mrk_wp (s := s_w) hcv_bv hcv hclear hsh_f hm_c
              fun mrk' m' hml h0 hm' => by rw [wp]; exact hJpost () m' ⟨mrk', hml, h0, hm'⟩
  · intro _J0 hJ0; c0_hsplit
    · c0_hsteps!; exact hJ0 () _ ⟨s.scratch.conflicts + 1, hm⟩
    · exact hJ0 () m ⟨s.scratch.conflicts, hm⟩

end

end LeanQbe.T.Examples.Kissat.Proof.Minimize
