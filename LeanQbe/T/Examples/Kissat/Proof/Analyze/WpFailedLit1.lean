/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Analyze.WpFailedLit0
public import LeanQbe.T.Examples.Kissat.Proof.Analyze.Spec
import LeanQbe.T.Examples.Kissat.Proof.Analyze.WpFailedLitBase
import LeanQbe.T.Examples.Kissat.Proof.Analyze.Helpers
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Canonical Analyze Proof: Failed Literal Entry (`WpFailedLit1`)

Proves `full_ana_failed_lit_m6_hdr_wp` certifying `Analyze.Spec.fullAnaFailedLitM6HdrSpec`
for `Src.Analyze.full_ana_failed_lit_m6_hdr_body` (`0` legacy imports, `0` `@[expose]` on
theorems, every file `<= 1,500`L, every decl `<= 450`L, every line `<= 100` cols).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Analyze.WpFailedLit

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Analyze
open LeanQbe.T.Examples.Kissat.Proof.Analyze.Spec
open LeanQbe.T.Examples.Kissat.Proof.Analyze.Helpers
open LeanQbe.T.Examples.Kissat.Proof.Bump.Spec
open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics
open Kraken.Bedrock2.Test

section FlMainHelpers

attribute [local bv_c0] Bool.true_eq_false Bool.false_eq_true
private theorem fl1_bv32_lshr1 (x : BitVec 32) : (x >>> 1#32).toNat = x.toNat / 2 :=
  fl_bv32_lshr1 x
private theorem fl1_bv32_xor1 (x : BitVec 32) : (x ^^^ 1#32).toNat = x.toNat ^^^ 1 :=
  fl_bv32_xor1 x
private theorem fl1_bv32_zext64 (x : BitVec 32) : (x.setWidth 64).toNat = x.toNat :=
  fl_bv32_setWidth64 x
private theorem fl1_sext32_64_1 : BitVec.signExtend 64 (1#32 : BitVec 32) = 1#64 := rfl
private theorem fl1_bv32_lshr_nat1 (x : BitVec 32) : (x >>> 1).toNat = x.toNat / 2 :=
  fl_bv32_lshr1 x
private theorem fl1_bv32_0_add (x : BitVec 32) : 0#32 + x = x := by simp

attribute [local bv_c0] fl1_bv32_lshr1 fl1_bv32_xor1 fl1_bv32_zext64
  fl1_sext32_64_1 fl1_bv32_lshr_nat1 fl1_bv32_0_add

/-! ## 1. Trail Scan Helper (`s13FlFindLitExpr`, `s13_fl_find_lit_wp`) -/

private abbrev s13FlFindLitExpr (c : FullCfg) (cv t : BitVec 64) (err : Bool)
    (Jfind : Cont [i64, .bool, i32]) : Expr Val Cont [i64] :=
  let op64 (co : OpCode [i64, i64] [i64]) (a b : Arg Val i64) := Op.mk co (a, b, ())
  .group (sig := [[i64]]) (fun J64 => .cons (fun tc =>
    .jnz (.imm true)
      (.let_ (Op.mk (.cmp .eq i64 .bool rfl) (.var tc.fst, .imm 0, ())) fun b0 =>
       .jnz (.var b0.fst) (.jump Jfind (.var tc.fst, .imm true, .imm 4294967295, ()))
         (.let_ (op64 (.sub i64) (.var tc.fst) (.imm 1)) fun tc1 =>
          .let_ (op64 (.mul i64) (.var tc1.fst) (.imm 4)) fun off =>
          .let_ (op64 (.add i64) (.var c.pTrail) (.var off.fst)) fun pa =>
          .load i32 (.var pa.fst) fun tl =>
          .let_ (Op.mk (.lshr i32) (.var tl, .imm 1, ())) fun tv =>
          .let_ (Op.mk (.zext 32 64) (.var tv.fst, ())) fun ztv =>
          .let_ (Op.mk (.cmp .uge i64 .bool rfl) (.var ztv.fst, .var cv, ())) fun boob =>
          .jnz (.var boob.fst) (.jump Jfind (.var tc1.fst, .imm true, .imm 4294967295, ()))
            (.let_ (Op.mk (.zext 32 64) (.var tv.fst, ())) fun ztv2 =>
             .let_ (op64 (.add i64) (.var c.pMark) (.var ztv2.fst)) fun pm =>
             .load i8 (.var pm.fst) fun mk =>
             .let_ (Op.mk (.trunc 32 8) (.imm 0, ())) fun t0 =>
             .let_ (Op.mk (.zext 8 32) (.var mk, ())) fun zm =>
             .let_ (Op.mk (.zext 8 32) (.var t0.fst, ())) fun zt =>
             .let_ (Op.mk (.cmp .ne i32 .bool rfl) (.var zm.fst, .var zt.fst, ())) fun bnz =>
             .jnz (.var bnz.fst) (.jump Jfind (.var tc1.fst, .var err, .var tl, ()))
               (.jump J64.fst (.var tc1.fst, ())))))
      (.jump Jfind (.var tc.fst, .var err, .imm 4294967295, ()))) .nil)
    fun J64 => .jump J64.fst (.var t, ())

private theorem s13_fl_find_lit_wp {Γ Q X}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {cut unres t : Nat}
    {s s_lp : FullState} {R_hdr : Mem 64 → Prop} {err : Bool} {m1 : Mem 64}
    {Jfind : Cont [i64, .bool, i32]}
    (hcut : FullCutInvW c F0 F_cur cut s)
    (hok_lp : FailedStateOk c s s_lp cut) (ht_le : t ≤ s.core.trail_end) (herr_f : err = false)
    (hunres_len : unres = (flIdxs s_lp.core.mrk s.core.trl t).length)
    (hact_ent : (cnfOfClauses F_cur).EntailsClause (cnfClause (flLits s_lp.core.mrk s.core.trl t)))
    (hm1 : (FullMem c s_lp ⋆ R_hdr) m1)
    (hJfind : ∀ (t' : Nat) (err' : Bool) (lit' : BitVec 32) (m_f : Mem 64), m_f = m1 →
      (if err' then t' ≤ t
       else t' < t ∧ (s.core.trl[t']?.getD 0#32).toNat = lit'.toNat ∧
         lit'.toNat < 2 * s.core.cur_vars ∧ s_lp.core.mrk[lit'.toNat / 2]?.getD 0#8 ≠ 0#8 ∧
         unres = (flIdxs s_lp.core.mrk s.core.trl (t' + 1)).length ∧
         (cnfOfClauses F_cur).EntailsClause
           (cnfClause (flLits s_lp.core.mrk s.core.trl (t' + 1)))) →
      Jfind (BitVec.ofNat 64 t', err', lit', ()) m_f) :
    wp Γ Q X (s13FlFindLitExpr c (BitVec.ofNat 64 s.core.cur_vars) (BitVec.ofNat 64 t) err Jfind)
      m1 := by
  have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
  have ⟨hlen0, hw0, _, _, _, _⟩ := hcut
  have hcl := hlen0.core_ok; have hcv_le := hcl.cur_vars_le; have hte_le := hcl.trail_end_le
  dsimp only [s13FlFindLitExpr]
  refine wp_while_state (ts := [i64]) (α := Nat) (proj := fun tc => (BitVec.ofNat 64 tc, ()))
    (μ := fun tc => tc)
    (Inv := fun tc m_w => tc ≤ t ∧ flIdxs s_lp.core.mrk s.core.trl tc =
      flIdxs s_lp.core.mrk s.core.trl t ∧ m_w = m1) ?_ ?_
  · intro Jw hJw; c0_hsteps; exact hJw t m1 ⟨Nat.le_refl _, rfl, rfl⟩
  · intro Jw tc m_w ⟨htc_le, hfl_eq, hm_eq⟩ ih_w
    rw [Blocks.get_here]; dsimp only
    c0_hsplit
    · c0_hsplit
      · have htc0 : tc = 0 := by
          have hz : BitVec.ofNat 64 tc = 0#64 := by assumption
          have := congrArg BitVec.toNat hz; rwa [p2_bv64_ofNat_toNat (by omega)] at this
        c0_hsteps; refine hJfind tc true 0xFFFFFFFF#32 m_w hm_eq (by simp [htc_le])
      · have htc_pos : 0 < tc := Nat.pos_of_ne_zero fun hz =>
          (by assumption : BitVec.ofNat 64 tc ≠ 0#64) (by subst hz; rfl)
        have hsub_bv := fl_bv64_sub1_eq htc_pos (by omega : tc < 2 ^ 64)
        have htrl_lp : s_lp.core.trl = s.core.trl := by rw [hok_lp.core]
        have hcv_lp : s_lp.core.cur_vars = s.core.cur_vars := by rw [hok_lp.core]
        have htc1_lt : tc - 1 < s_lp.core.trl.length := by rw [hok_lp.len.core_ok.trl_len]; omega
        have htc1_te : tc - 1 < s.core.trail_end := by omega
        have htl_lt : (s_lp.core.trl[(BitVec.ofNat 64 (tc - 1)).toNat]'(by
            rw [p2_bv64_ofNat_toNat (by omega)]; exact htc1_lt)).toNat < 2 * s.core.cur_vars := by
          simp only [p2_bv64_ofNat_toNat (by omega : tc - 1 < 2 ^ 64), htrl_lp]
          have h1 := hw0.trail_lits_lt (tc - 1) htc1_te
          rwa [List.getElem?_eq_getElem (by rw [hcl.trl_len]; omega), Option.getD_some] at h1
        have htl_mrk_lt : (((s_lp.core.trl[(BitVec.ofNat 64 (tc - 1)).toNat]'(by
            rw [p2_bv64_ofNat_toNat (by omega)]; exact htc1_lt) >>> 1#32).setWidth 64).toNat) <
            s_lp.core.mrk.length := by
          rw [fl_bv32_setWidth64, fl_bv32_lshr1, hok_lp.len.core_ok.mrk_len]; omega
        have hm_w : (FullMem c s_lp ⋆ R_hdr) m_w := hm_eq ▸ hm1
        have hidx1 : (BitVec.ofNat 64 tc - 1).toNat = tc - 1 := by
          rw [hsub_bv, p2_bv64_ofNat_toNat (by omega)]
        have hbt1 : BitVec.toNat (1 : BitVec 64) = 1 := rfl
        have hidx2 : (2 ^ 64 - BitVec.toNat (1 : BitVec 64) + tc) % 2 ^ 64 = tc - 1 := by
          simp only [hbt1]; omega
        have h032 : BitVec.ofNat (OfNat.ofNat 32) (OfNat.ofNat 0) = 0#32 := rfl
        have hidx3 : (BitVec.ofNat 64 (tc - 1)).toNat = tc - 1 :=
          p2_bv64_ofNat_toNat (by omega)
        have htc1_bv_lt : (BitVec.ofNat 64 tc - 1).toNat < s_lp.core.trl.length := by
          rw [hidx1]; exact htc1_lt
        have htl_mrk_bv_lt : (((s_lp.core.trl[(BitVec.ofNat 64 tc - 1).toNat]'htc1_bv_lt >>>
            1#32).setWidth 64).toNat) < s_lp.core.mrk.length := by
          simpa only [hsub_bv] using htl_mrk_lt
        c0_hsplit
        · exfalso
          have htrl_d : ∀ (h1 : (2 ^ 64 - BitVec.toNat (1 : BitVec 64) + tc) % 2 ^ 64 <
                s_lp.core.trl.length) (h2 : tc - 1 < s_lp.core.trl.length),
              s_lp.core.trl[(2 ^ 64 - BitVec.toNat (1 : BitVec 64) + tc) % 2 ^ 64]'h1 =
              s_lp.core.trl[tc - 1]'h2 := fun _ _ => p2_getElem_congr_list rfl hidx2
          have hge := hc; rw [htrl_d _ htc1_lt] at hge; try rw [hcv_lp] at hge
          have hlt1 : (s_lp.core.trl[tc - 1]'htc1_lt).toNat < 2 * s.core.cur_vars := by
            have h1 := htl_lt; simp only [hidx3] at h1; exact h1
          rw [Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64)] at hge; omega
        · have hsub1 : (tc - 1) + 1 = tc := Nat.sub_add_cancel htc_pos
          let tl := s_lp.core.trl[(BitVec.ofNat 64 tc - 1).toNat]'htc1_bv_lt
          have htl_base : tl = s_lp.core.trl[tc - 1]'htc1_lt := p2_getElem_congr_list rfl hidx1
          have htl_lt' : tl.toNat < 2 * s.core.cur_vars := by
            rw [htl_base]; simpa only [hidx3] using htl_lt
          have htl_eq : (s.core.trl[tc - 1]?.getD 0#32).toNat = tl.toNat := by
            rw [htl_base]
            have hget := p2_getElem_congr_list (by rw [hok_lp.core]) rfl
              (hix := htc1_lt) (hjy := by rw [hcl.trl_len]; omega)
            rw [hget, List.getElem?_eq_getElem (by rw [hcl.trl_len]; omega), Option.getD_some]
          c0_hsplit
          · have hmrk_nz : s_lp.core.mrk[tl.toNat / 2]?.getD 0#8 ≠ 0#8 := by
              have hov_m : tl.toNat / 2 < s_lp.core.mrk.length := by
                rw [hok_lp.len.core_ok.mrk_len]; omega
              have hne0 : BitVec.setWidth 32 (s_lp.core.mrk[tl.toNat / 2]'hov_m) ≠ 0#32 := by
                have hhc := hc; try simp only [hidx2, h032] at hhc
                dsimp only [tl]; try simp only [hidx1]; exact hhc
              exact fl_mark_nz_eq hok_lp (by omega : tl.toNat / 2 < s.core.cur_vars) hne0
            c0_hsteps
            let fJ : BitVec 64 → Bool → Prop := fun a b => Jfind (a, b, tl, ()) m_w
            change fJ (BitVec.ofNat 64 tc - 1) err
            rw [show fJ (BitVec.ofNat 64 tc - 1) err = fJ (BitVec.ofNat 64 (tc - 1)) false by
              dsimp only [fJ]; rw [hsub_bv, herr_f]]
            refine hJfind (tc - 1) false tl m_w hm_eq ?_
            simp only [Bool.false_eq_true, ↓reduceIte]
            exact ⟨by omega, htl_eq, htl_lt', hmrk_nz, by rw [hsub1, hfl_eq]; exact hunres_len,
              by rw [hsub1, flLits_congr_idxs hfl_eq]; exact hact_ent⟩
          · have hmrk0_w : s_lp.core.mrk[(s.core.trl[tc - 1]?.getD 0#32).toNat / 2]?.getD 0#8 =
                0#8 := by
              have hov_m : tl.toNat / 2 < s_lp.core.mrk.length := by
                rw [hok_lp.len.core_ok.mrk_len]; omega
              have he0 : BitVec.setWidth 32 (s_lp.core.mrk[tl.toNat / 2]'hov_m) = 0#32 := by
                have hhc := hc; try simp only [hidx2, h032] at hhc
                dsimp only [tl]; try simp only [hidx1]; exact hhc
              rw [htl_eq]; exact fl_mark_zero_eq hok_lp (by omega) he0
            have hfl_next : flIdxs s_lp.core.mrk s.core.trl (tc - 1) =
                flIdxs s_lp.core.mrk s.core.trl t := by
              have hun : ∀ j, tc - 1 ≤ j → j < tc →
                  s_lp.core.mrk[(s.core.trl[j]?.getD 0#32).toNat / 2]?.getD 0#8 = 0#8 :=
                fun j hj1 hj2 => by obtain rfl : j = tc - 1 := (by omega); exact hmrk0_w
              exact (flIdxs_eq_of_unmarked_above (by omega) hun).symm.trans hfl_eq
            c0_hsteps; rw [hsub_bv]
            exact ih_w (tc - 1) m_w (by omega) ⟨by omega, hfl_next, hm_eq⟩

/-! ## 2. Binary Reason Branch (`s13FlRsnBinExpr`, `s13_fl_rsn_bin_wp`) -/

private abbrev s13FlRsnBinExpr (c : FullCfg) (cv unres ucnt t' : BitVec 64)
    (done brk : Bool) (nf unit' rsn : BitVec 32)
    (Jexit : Cont [i64, i64, .bool, i64, i32, .bool])
    (Jrsn : Cont [i64, .bool, .bool]) : Expr Val Cont [i64] :=
  let op64 (co : OpCode [i64, i64] [i64]) (a b : Arg Val i64) := Op.mk co (a, b, ())
  .let_ (Op.mk (.and i32) (.var rsn, .imm 2147483647, ())) fun ot =>
  .let_ (Op.mk (.cmp .eq i32 .bool rfl) (.var ot.fst, .var nf, ())) fun eqnf =>
  .jnz (.var eqnf.fst)
    (.jump Jexit (.var unres, .var ucnt, .imm true, .var t', .var unit', .var brk, ()))
    (.let_ (Op.mk (.lshr i32) (.var ot.fst, .imm 1, ())) fun ov =>
     .let_ (Op.mk (.zext 32 64) (.var ov.fst, ())) fun zov =>
     .let_ (Op.mk (.cmp .uge i64 .bool rfl) (.var zov.fst, .var cv, ())) fun oob =>
     .jnz (.var oob.fst)
       (.jump Jexit (.var unres, .var ucnt, .var done, .var t', .var unit', .imm true, ()))
       (.group (sig := [[i64]]) (fun _ => .cons (fun u =>
           .jump Jrsn (.var u.fst, .var done, .var brk, ())) .nil) fun J86 =>
         .let_ (Op.mk (.zext 32 64) (.var ov.fst, ())) fun x1 =>
         .let_ (op64 (.mul i64) (.var x1.fst) (.imm 4)) fun x2 =>
         .let_ (op64 (.add i64) (.var c.pLevel) (.var x2.fst)) fun x3 =>
         .load i32 (.var x3.fst) fun lv =>
         .let_ (Op.mk (.cmp .ugt i32 .bool rfl) (.var lv, .imm 0, ())) fun x4 =>
         .jnz (.var x4.fst)
           (.let_ (Op.mk (.zext 32 64) (.var ov.fst, ())) fun y1 =>
            .let_ (op64 (.add i64) (.var c.pMark) (.var y1.fst)) fun y2 =>
            .load i8 (.var y2.fst) fun mk =>
            .let_ (Op.mk (.trunc 32 8) (.imm 0, ())) fun t0 =>
            .let_ (Op.mk (.zext 8 32) (.var mk, ())) fun zm =>
            .let_ (Op.mk (.zext 8 32) (.var t0.fst, ())) fun zt =>
            .let_ (Op.mk (.cmp .eq i32 .bool rfl) (.var zm.fst, .var zt.fst, ())) fun eqm =>
            .jnz (.var eqm.fst)
              (.let_ (Op.mk (.zext 32 64) (.var ov.fst, ())) fun d1 =>
               .let_ (op64 (.add i64) (.var c.pMark) (.var d1.fst)) fun d2 =>
               .let_ (Op.mk (.trunc 32 8) (.imm 1, ())) fun t1 =>
               .store (t := i8) (.var t1.fst) (.var d2.fst)
                 (.group (sig := [[]]) (fun _ => .cons (fun _ =>
                     .let_ (op64 (.add i64) (.var unres) (.imm 1)) fun u1 =>
                     .jump J86.fst (.var u1.fst, ())) .nil) fun J102 =>
                   .let_ (op64 (.add i64) (.var c.hdr) (.imm 272)) fun m1 =>
                   .load i64 (.var m1.fst) fun lm1 =>
                   .let_ (Op.mk (.cmp .ult i64 .bool rfl) (.var lm1, .var cv, ())) fun b2 =>
                   .jnz (.var b2.fst)
                     (.let_ (op64 (.add i64) (.var c.hdr) (.imm 272)) fun m2 =>
                      .load i64 (.var m2.fst) fun lm2 =>
                      .let_ (op64 (.mul i64) (.var lm2) (.imm 4)) fun w1 =>
                      .let_ (op64 (.add i64) (.var c.pWorkStk1) (.var w1.fst)) fun w2 =>
                      .store (t := i32) (.var ov.fst) (.var w2.fst)
                        (.let_ (op64 (.add i64) (.var c.hdr) (.imm 272)) fun m3 =>
                         .load i64 (.var m3.fst) fun lm3 =>
                         .let_ (op64 (.add i64) (.var lm3) (.imm 1)) fun lm4 =>
                         .let_ (op64 (.add i64) (.var c.hdr) (.imm 272)) fun m4 =>
                         .store (t := i64) (.var lm4.fst) (.var m4.fst) (.jump J102.fst ())))
                     (.jump J102.fst ())))
              (.jump J86.fst (.var unres, ())))
           (.jump J86.fst (.var unres, ()))))

private theorem s13_fl_rsn_bin_wp {Γ Q X}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {cut unres ucnt' t' : Nat}
    {s s1 : FullState} {R_hdr : Mem 64 → Prop} {done brk : Bool}
    {not_failed lit' unit' rsn32 : BitVec 32} {m2 : Mem 64}
    {Jexit : Cont [i64, i64, .bool, i64, i32, .bool]} {Jrsn : Cont [i64, .bool, .bool]}
    (hcut : FullCutInvW c F0 F_cur cut s) (hcl1 : s.core.cur_level = 1)
    (hok1 : FailedStateOk c s s1 cut) (ht'_lt : t' < s.core.trail_end) (ht'_cut : t' < cut)
    (htrl_t' : (s.core.trl[t']?.getD 0#32).toNat = lit'.toNat)
    (hmrk_t'_trl : s1.core.mrk[(s.core.trl[t']?.getD 0#32).toNat / 2]?.getD 0#8 ≠ 0#8)
    (hunres_t'_s : unres = (flIdxs s1.core.mrk s.core.trl t').length + 1)
    (hunres_bd : unres ≤ s.core.cur_vars)
    (hact_t' : (cnfOfClauses F_cur).EntailsClause
      (cnfClause (flLits s1.core.mrk s.core.trl (t' + 1))))
    (hucnt'_le : ucnt' ≤ s.core.cur_vars)
    (htmp_ok' : ∀ k < ucnt', (s1.core.tmp[k]?.getD 0#32).toNat < 2 * s.core.cur_vars ∧
      (cnfOfClauses F_cur).EntailsClause (cnfClause [(s1.core.tmp[k]?.getD 0#32).toNat]))
    (_hrsn_eq : rsn32 = s.core.rsns[lit'.toNat / 2]?.getD 0xFFFFFFFF#32)
    (hbin : (rsn32 &&& 0x80000000#32) ≠ 0#32)
    (hri : (rsn32 &&& 0x7FFFFFFF#32).toNat < 2 * s.core.cur_vars ∧
      (cnfOfClauses F_cur).EntailsClause
        (cnfClause [lit'.toNat, (rsn32 &&& 0x7FFFFFFF#32).toNat]) ∧
      ∃ m_ot < t', (s.core.trl[m_ot]?.getD 0#32).toNat = (rsn32 &&& 0x7FFFFFFF#32).toNat ^^^ 1)
    (hm2 : (FullMem c s1 ⋆ R_hdr) m2)
    (hJexit : ∀ (u uc : Nat) (dn : Bool) (tt : Nat) (un : BitVec 32) (er : Bool) (sf : FullState)
      (mf : Mem 64), FailedStateOk c s sf cut → tt ≤ s.core.trail_end → uc ≤ s.core.cur_vars →
      (∀ k < uc, (sf.core.tmp[k]?.getD 0#32).toNat < 2 * s.core.cur_vars ∧
        (cnfOfClauses F_cur).EntailsClause (cnfClause [(sf.core.tmp[k]?.getD 0#32).toNat])) →
      (!er → !dn → u = (flIdxs sf.core.mrk s.core.trl tt).length ∧
        (cnfOfClauses F_cur).EntailsClause (cnfClause (flLits sf.core.mrk s.core.trl tt))) →
      (FullMem c sf ⋆ R_hdr) mf →
      Jexit (BitVec.ofNat 64 u, BitVec.ofNat 64 uc, dn, BitVec.ofNat 64 tt, un, er, ()) mf)
    (hJrsn : ∀ (u' : Nat) (dn' er' : Bool) (s3 : FullState) (m3 : Mem 64),
      FailedStateOk c s s3 cut → s3.core.tmp = s1.core.tmp →
      (!er' → !dn' → u' = (flIdxs s3.core.mrk s.core.trl t').length + 1 ∧
        (cnfOfClauses F_cur).EntailsClause (cnfClause (flLits s3.core.mrk s.core.trl t'))) →
      (FullMem c s3 ⋆ R_hdr) m3 → Jrsn (BitVec.ofNat 64 u', dn', er', ()) m3) :
    wp Γ Q X (s13FlRsnBinExpr c (BitVec.ofNat 64 s.core.cur_vars) (BitVec.ofNat 64 unres)
      (BitVec.ofNat 64 ucnt') (BitVec.ofNat 64 t') done brk not_failed unit' rsn32 Jexit Jrsn)
      m2 := by
  have _ := hbin
  have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
  have ⟨hlen0, hw0, _, _, _, _⟩ := hcut
  have hcv_le := hlen0.core_ok.cur_vars_le
  have hl1_cv := hok1.len.core_ok
  have hcv1 : s1.core.cur_vars = s.core.cur_vars := by rw [hok1.core]
  obtain ⟨hot_lt, hent_bin, m_ot, hm_ot_lt, hm_ot_eq⟩ := hri
  let ot32 := rsn32 &&& 0x7FFFFFFF#32
  dsimp only [s13FlRsnBinExpr]; c0_hsplit
  · c0_hsteps
    exact hJexit unres ucnt' true t' unit' brk s1 m2 hok1 (by omega) hucnt'_le htmp_ok'
      (fun _ hd => by simp at hd) hm2
  · have hov_lt : ot32.toNat / 2 < s.core.cur_vars := Nat.div_lt_of_lt_mul hot_lt
    have h7f : (2147483647 : BitVec 32) = 0x7FFFFFFF#32 := rfl
    have h032 : BitVec.ofNat (OfNat.ofNat 32) (OfNat.ofNat 0) = 0#32 := rfl
    have hov_lvl_lt : ot32.toNat / 2 < s1.core.lvl.length := by
      rw [hl1_cv.lvl_len]; omega
    have hov_mrk_lt : ot32.toNat / 2 < s1.core.mrk.length := by
      rw [hl1_cv.mrk_len]; omega
    c0_hsplit
    · exfalso
      have hge : s.core.cur_vars % 2 ^ 64 ≤ ot32.toNat / 2 := by
        dsimp only [ot32]; simpa only [h7f] using (by assumption : _)
      rw [Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64)] at hge; omega
    · c0_hsteps_nogrp
      refine wp_join_state (ts := [i64]) (α := Nat × FullState)
        (proj := fun st => (BitVec.ofNat 64 st.1, ()))
        (Inv := fun st m3 => FailedStateOk c s st.2 cut ∧ st.2.core.tmp = s1.core.tmp ∧
          st.1 = (flIdxs st.2.core.mrk s.core.trl t').length + 1 ∧
          (∀ l ∈ flLits s1.core.mrk s.core.trl t', l ∈ flLits st.2.core.mrk s.core.trl t') ∧
          ((cnfOfClauses F_cur).EntailsClause (cnfClause [ot32.toNat ^^^ 1]) ∨
            ot32.toNat ∈ flLits st.2.core.mrk s.core.trl t') ∧
          (FullMem c st.2 ⋆ R_hdr) m3) ?_ ?_
      · intro _ ⟨unres_b, s_b⟩ m3 ⟨hok_b, htmp_b, hunres_b, hpres_b, hot_in, hm3⟩
        dsimp only at hok_b htmp_b hunres_b hpres_b hot_in hm3; rw [Blocks.get_here]; dsimp only
        have hent_b : (cnfOfClauses F_cur).EntailsClause
            (cnfClause (flLits s_b.core.mrk s.core.trl t')) := by
          refine fl_resolve_step hmrk_t'_trl hact_t' hpres_b (by simpa [htrl_t'] using hent_bin)
            fun q hq => ?_
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
          rcases hq with rfl | rfl
          · exact Or.inl htrl_t'.symm
          · exact Or.inr hot_in
        c0_hsteps
        exact hJrsn unres_b done brk s_b m3 hok_b htmp_b (fun _ _ => ⟨hunres_b, hent_b⟩) hm3
      · intro Jbin hJbin; c0_hsplit
        · c0_hsplit
          · have hmrk0_ov := fl_mark_zero_eq hok1 hov_lt (by
              dsimp only [ot32]; simpa only [h7f, h032] using (by assumption : _))
            have hlvl_pos := p2_lvl_pos_of_lt hok1 hov_lvl_lt (by
              dsimp only [ot32]
              simpa only [h7f, show (0#32 : BitVec 32).toNat = BitVec.toNat 0 from rfl] using
                (by assumption : _))
            obtain ⟨hmcl_lt, hmcl64, hmcl_ws, hmcl1_bv, hok2, hfl_len, hfl_pres, hot_in⟩ :=
              p2_push_step hw0 hcl1 hok1 (by omega) hot_lt hmrk0_ov hlvl_pos
                ⟨m_ot, hm_ot_lt, hm_ot_eq⟩ ⟨m_ot, by omega, hm_ot_eq⟩
            let s2 : FullState :=
              { core := { s1.core with
                  mrk := s1.core.mrk.set (ot32.toNat / 2) 1#8,
                  min_clr_len := s1.core.min_clr_len + 1 },
                scratch := { s1.scratch with
                  work_stk1 := s1.scratch.work_stk1.set s1.core.min_clr_len (ot32 >>> 1) } }
            c0_hsplit
            c0_hsteps
            have hm2' : (FullMem c s2 ⋆ R_hdr) m := by
              simpa only [s2, ot32, fl_bv32_setWidth64, bv32_lshr_1,
                p2_bv64_ofNat_toNat hmcl64, hmcl1_bv, h7f,
                show BitVec.ofNat 8 1 = 1#8 from rfl] using hm
            rw [fl_bv64_add1_eq (by omega)]
            exact hJbin (unres + 1, s2) m ⟨hok2, rfl, by rw [hunres_t'_s, hfl_len], hfl_pres,
              hot_in, hm2'⟩
          · have hmrk_nz := fl_mark_nz_eq hok1 hov_lt (by
              dsimp only [ot32]; simpa only [h7f, h032] using (by assumption : _))
            have hot_in := fl_mark_lit_skip hw0 hcl1 (by omega)
              (fun _ => ⟨m_ot, by omega, hm_ot_eq⟩)
              (fun _ => ⟨hmrk_nz, m_ot, hm_ot_lt, hm_ot_eq⟩)
            c0_hsteps
            exact hJbin (unres, s1) m2 ⟨hok1, rfl, hunres_t'_s, fun _ hl => hl, hot_in, hm2⟩
        · have hlvl0 := p2_lvl0_of_nlt hok1 hov_lvl_lt (by
            dsimp only [ot32]
            simpa only [h7f, show (0#32 : BitVec 32).toNat = BitVec.toNat 0 from rfl] using
              (by assumption : _))
          have hot_in := fl_mark_lit_skip (s1 := s1) (t := t') (q := ot32.toNat) hw0 hcl1
            (by omega) (fun _ => ⟨m_ot, by omega, hm_ot_eq⟩) (fun hp => by omega)
          c0_hsteps
          exact hJbin (unres, s1) m2 ⟨hok1, rfl, hunres_t'_s, fun _ hl => hl, hot_in, hm2⟩

/-! ## 3. Large-Clause Reason Branch (`s13FlRsnLargeExpr`, `s13_fl_rsn_large_wp`) -/

private abbrev s13FlRsnLargeExpr (c : FullCfg) (cv unres ucnt t' : BitVec 64)
    (done brk : Bool) (nf lit' unit' rsn : BitVec 32)
    (Jexit : Cont [i64, i64, .bool, i64, i32, .bool])
    (Jrsn : Cont [i64, .bool, .bool]) : Expr Val Cont [i64] :=
  let op64 (co : OpCode [i64, i64] [i64]) (a b : Arg Val i64) := Op.mk co (a, b, ())
  .let_ (Op.mk (.zext 32 64) (.var rsn, ())) fun z1 =>
  .let_ (op64 (.add i64) (.var z1.fst) (.imm 3)) fun r3 =>
  .let_ (op64 (.add i64) (.var c.hdr) (.imm 48)) fun pa1 =>
  .load i64 (.var pa1.fst) fun al1 =>
  .let_ (Op.mk (.cmp .ugt i64 .bool rfl) (.var r3.fst, .var al1, ())) fun b0 =>
  .jnz (.var b0.fst)
    (.jump Jexit (.var unres, .var ucnt, .var done, .var t', .var unit', .imm true, ()))
    (.let_ (Op.mk (.zext 32 64) (.var rsn, ())) fun z2 =>
     .let_ (op64 (.add i64) (.var z2.fst) (.imm 2)) fun r2 =>
     .let_ (op64 (.mul i64) (.var r2.fst) (.imm 4)) fun off2 =>
     .let_ (op64 (.add i64) (.var c.pArena) (.var off2.fst)) fun p2 =>
     .load i32 (.var p2.fst) fun rsz =>
     .let_ (Op.mk (.cmp .ult i32 .bool rfl) (.var rsz, .imm 3, ())) fun b1 =>
     .jnz (.var b1.fst)
       (.jump Jexit (.var unres, .var ucnt, .var done, .var t', .var unit', .imm true, ()))
       (.let_ (Op.mk (.zext 32 64) (.var rsn, ())) fun z3 =>
        .let_ (op64 (.add i64) (.var z3.fst) (.imm 3)) fun r3' =>
        .let_ (Op.mk (.zext 32 64) (.var rsz, ())) fun zsz =>
        .let_ (op64 (.add i64) (.var r3'.fst) (.var zsz.fst)) fun rsz3 =>
        .let_ (op64 (.add i64) (.var c.hdr) (.imm 48)) fun pa2 =>
        .load i64 (.var pa2.fst) fun al2 =>
        .let_ (Op.mk (.cmp .ugt i64 .bool rfl) (.var rsz3.fst, .var al2, ())) fun b2 =>
        .jnz (.var b2.fst)
          (.jump Jexit (.var unres, .var ucnt, .var done, .var t', .var unit', .imm true, ()))
          (.group (sig := [[i64, .bool, .bool, i32]]) (fun _ => .cons (fun p =>
              .jump Jrsn (.var p.fst, .var p.snd.fst, .var p.snd.snd.fst, ())) .nil) fun J99 =>
            .group (sig := [[i64, i32]]) (fun J100 => .cons (fun p =>
              .let_ (Op.mk (.cmp .ult i32 .bool rfl) (.var p.snd.fst, .var rsz, ())) fun cmp =>
              .jnz (.var cmp.fst)
                (.let_ (Op.mk (.zext 32 64) (.var rsn, ())) fun a1 =>
                 .let_ (op64 (.add i64) (.var a1.fst) (.imm 3)) fun a2 =>
                 .let_ (Op.mk (.zext 32 64) (.var p.snd.fst, ())) fun a3 =>
                 .let_ (op64 (.add i64) (.var a2.fst) (.var a3.fst)) fun a4 =>
                 .let_ (op64 (.mul i64) (.var a4.fst) (.imm 4)) fun a5 =>
                 .let_ (op64 (.add i64) (.var c.pArena) (.var a5.fst)) fun a6 =>
                 .load i32 (.var a6.fst) fun ot =>
                 .group (sig := [[i64, .bool, .bool]]) (fun _ => .cons (fun q =>
                     .let_ (Op.mk (.add i32) (.var p.snd.fst, .imm 1, ())) fun j1 =>
                     .jump J100.fst (.var q.fst, .var j1.fst, ())) .nil) fun J111 =>
                   .let_ (Op.mk (.cmp .ne i32 .bool rfl) (.var ot, .var lit', ())) fun nel =>
                   .jnz (.var nel.fst)
                     (.let_ (Op.mk (.cmp .eq i32 .bool rfl) (.var ot, .var nf, ())) fun eqnf =>
                      .jnz (.var eqnf.fst)
                        (.jump J99.fst (.var p.fst, .imm true, .var brk, .var p.snd.fst, ()))
                        (.let_ (Op.mk (.lshr i32) (.var ot, .imm 1, ())) fun ov =>
                         .let_ (Op.mk (.zext 32 64) (.var ov.fst, ())) fun zov =>
                         .let_ (Op.mk (.cmp .uge i64 .bool rfl) (.var zov.fst, .var cv, ()))
                           fun oob =>
                         .jnz (.var oob.fst)
                           (.jump J99.fst
                             (.var p.fst, .var done, .imm true, .var p.snd.fst, ()))
                           (.group (sig := [[i64]]) (fun _ => .cons (fun u =>
                               .jump J111.fst (.var u.fst, .var done, .var brk, ())) .nil)
                             fun J117 =>
                             .let_ (Op.mk (.zext 32 64) (.var ov.fst, ())) fun x1 =>
                             .let_ (op64 (.mul i64) (.var x1.fst) (.imm 4)) fun x2 =>
                             .let_ (op64 (.add i64) (.var c.pLevel) (.var x2.fst)) fun x3 =>
                             .load i32 (.var x3.fst) fun lv =>
                             .let_ (Op.mk (.cmp .ugt i32 .bool rfl) (.var lv, .imm 0, ())) fun x4 =>
                             .jnz (.var x4.fst)
                               (.let_ (Op.mk (.zext 32 64) (.var ov.fst, ())) fun y1 =>
                                .let_ (op64 (.add i64) (.var c.pMark) (.var y1.fst)) fun y2 =>
                                .load i8 (.var y2.fst) fun mk =>
                                .let_ (Op.mk (.trunc 32 8) (.imm 0, ())) fun t0 =>
                                .let_ (Op.mk (.zext 8 32) (.var mk, ())) fun zm =>
                                .let_ (Op.mk (.zext 8 32) (.var t0.fst, ())) fun zt =>
                                .let_ (Op.mk (.cmp .eq i32 .bool rfl)
                                    (.var zm.fst, .var zt.fst, ()))
                                  fun eqm =>
                                .jnz (.var eqm.fst)
                                  (.let_ (Op.mk (.zext 32 64) (.var ov.fst, ())) fun d1 =>
                                   .let_ (op64 (.add i64) (.var c.pMark) (.var d1.fst)) fun d2 =>
                                   .let_ (Op.mk (.trunc 32 8) (.imm 1, ())) fun t1 =>
                                   .store (t := i8) (.var t1.fst) (.var d2.fst)
                                     (.group (sig := [[]]) (fun _ => .cons (fun _ =>
                                         .let_ (op64 (.add i64) (.var p.fst) (.imm 1)) fun u1 =>
                                         .jump J117.fst (.var u1.fst, ())) .nil) fun J133 =>
                                       .let_ (op64 (.add i64) (.var c.hdr) (.imm 272)) fun m1 =>
                                       .load i64 (.var m1.fst) fun lm1 =>
                                       .let_ (Op.mk (.cmp .ult i64 .bool rfl)
                                           (.var lm1, .var cv, ()))
                                         fun b3 =>
                                       .jnz (.var b3.fst)
                                         (.let_ (op64 (.add i64) (.var c.hdr) (.imm 272)) fun m2 =>
                                          .load i64 (.var m2.fst) fun lm2 =>
                                          .let_ (op64 (.mul i64) (.var lm2) (.imm 4)) fun w1 =>
                                          .let_ (op64 (.add i64) (.var c.pWorkStk1) (.var w1.fst))
                                            fun w2 =>
                                          .store (t := i32) (.var ov.fst) (.var w2.fst)
                                            (.let_ (op64 (.add i64) (.var c.hdr) (.imm 272))
                                              fun m3 =>
                                             .load i64 (.var m3.fst) fun lm3 =>
                                             .let_ (op64 (.add i64) (.var lm3) (.imm 1)) fun lm4 =>
                                             .let_ (op64 (.add i64) (.var c.hdr) (.imm 272))
                                               fun m4 =>
                                             .store (t := i64) (.var lm4.fst) (.var m4.fst)
                                               (.jump J133.fst ())))
                                         (.jump J133.fst ())))
                                  (.jump J117.fst (.var p.fst, ())))
                               (.jump J117.fst (.var p.fst, ())))))
                     (.jump J111.fst (.var p.fst, .var done, .var brk, ())))
                (.jump J99.fst (.var p.fst, .var done, .var brk, .var p.snd.fst, ()))) .nil)
            fun J100 => .jump J100.fst (.var unres, .imm 0, ()))))

private theorem s13_fl_rsn_large_wp {Γ Q X}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {cut unres ucnt' t' : Nat}
    {s s1 : FullState} {R_hdr : Mem 64 → Prop} {done brk : Bool}
    {not_failed lit' unit' rsn32 : BitVec 32} {m2 : Mem 64}
    {Jexit : Cont [i64, i64, .bool, i64, i32, .bool]} {Jrsn : Cont [i64, .bool, .bool]}
    (hcut : FullCutInvW c F0 F_cur cut s) (hcl1 : s.core.cur_level = 1)
    (hok1 : FailedStateOk c s s1 cut) (ht'_lt : t' < s.core.trail_end) (ht'_cut : t' < cut)
    (htrl_t' : (s.core.trl[t']?.getD 0#32).toNat = lit'.toNat)
    (hmrk_t'_trl : s1.core.mrk[(s.core.trl[t']?.getD 0#32).toNat / 2]?.getD 0#8 ≠ 0#8)
    (hunres_t'_s : unres = (flIdxs s1.core.mrk s.core.trl t').length + 1)
    (hact_t' : (cnfOfClauses F_cur).EntailsClause
      (cnfClause (flLits s1.core.mrk s.core.trl (t' + 1))))
    (hrsn_eq : rsn32.toNat = (s.core.rsns[lit'.toNat / 2]?.getD 0xFFFFFFFF#32).toNat)
    (href : (s.core.rsns[lit'.toNat / 2]?.getD 0xFFFFFFFF#32).toNat ∈
      fullArenaClauseRefsCore s.core)
    (hng : fullArenaClauseGarbCore s.core
      (s.core.rsns[lit'.toNat / 2]?.getD 0xFFFFFFFF#32).toNat = false)
    (hall : ∀ l ∈ fullArenaClauseLitsCore s.core
        (s.core.rsns[lit'.toNat / 2]?.getD 0xFFFFFFFF#32).toNat,
      l = lit'.toNat ∨ ∃ m_ot < t', (s.core.trl[m_ot]?.getD 0#32).toNat = l ^^^ 1)
    (hm2 : (FullMem c s1 ⋆ R_hdr) m2)
    (hJrsn : ∀ (u' : Nat) (dn' er' : Bool) (s3 : FullState) (m3 : Mem 64),
      FailedStateOk c s s3 cut → s3.core.tmp = s1.core.tmp →
      (!er' → !dn' → u' = (flIdxs s3.core.mrk s.core.trl t').length + 1 ∧
        (cnfOfClauses F_cur).EntailsClause (cnfClause (flLits s3.core.mrk s.core.trl t'))) →
      (FullMem c s3 ⋆ R_hdr) m3 → Jrsn (BitVec.ofNat 64 u', dn', er', ()) m3) :
    wp Γ Q X (s13FlRsnLargeExpr c (BitVec.ofNat 64 s.core.cur_vars) (BitVec.ofNat 64 unres)
      (BitVec.ofNat 64 ucnt') (BitVec.ofNat 64 t') done brk not_failed lit' unit' rsn32 Jexit Jrsn)
      m2 := by
  have hmaxv := c.hmaxv; have har_cap := c.harena; unfold dimacsBound at hmaxv har_cap
  have ⟨hlen0, hw0, _, _, _, _⟩ := hcut
  have hte_le := hlen0.core_ok.trail_end_le; have hwf := hw0.arena.refs_wf _ href
  have har_core1 : s1.core.arena = s.core.arena := by rw [hok1.core]
  have hal_eq : s1.core.arena_len = s.core.arena_len := by rw [hok1.core]
  have hal_c : s.core.arena_len ≤ c.arena_cap := hlen0.core_ok.arena_len_le
  obtain ⟨hrsn_add2_lt, hrsz_eq, hrsn_bd, hlits_len⟩ :=
    p2_arena_clause_sz hlen0 hok1.len har_core1 hal_eq hrsn_eq
      ⟨hwf.1, hwf.2.1, Nat.le_trans hwf.2.2.1 hwf.2.2.2.1, hal_c, hlen0.core_ok.arena_len_arr.symm⟩
  have hle3 : rsn32.toNat + 3 ≤ s.core.arena_len := by rw [hrsn_eq]; exact hwf.1
  dsimp only [s13FlRsnLargeExpr]; c0_hsplit
  · exfalso
    have hgt : s1.core.arena_len % 2 ^ 64 < (rsn32.toNat + 3) % 2 ^ 64 := by assumption
    rw [hal_eq, Nat.mod_eq_of_lt (by omega : s.core.arena_len < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : rsn32.toNat + 3 < 2 ^ 64)] at hgt; omega
  · let rsz := s1.core.arena[(rsn32.setWidth 64 + 2#64).toNat]'hrsn_add2_lt
    c0_hsplit
    · exfalso
      have hlt3 : rsz.toNat < 3 := by dsimp only [rsz]; assumption
      have hge3 : 3 ≤ rsz.toNat := by
        change 3 ≤ (s1.core.arena[(rsn32.setWidth 64 + 2#64).toNat]'hrsn_add2_lt).toNat
        rw [hrsz_eq, hrsn_eq]; exact hwf.2.1
      omega
    · c0_hsplit
      · exfalso
        have hle_a : rsn32.toNat + 3 + rsz.toNat ≤ s.core.arena_len := by
          change rsn32.toNat + 3 +
            (s1.core.arena[(rsn32.setWidth 64 + 2#64).toNat]'hrsn_add2_lt).toNat ≤
            s.core.arena_len
          rw [hrsz_eq, hrsn_eq]; have := hwf.2.2.1; have := hwf.2.2.2.1; omega
        have hgt : s1.core.arena_len % 2 ^ 64 < (rsn32.toNat + 3 + rsz.toNat) % 2 ^ 64 := by
          dsimp only [rsz]; assumption
        have hbd64 : rsn32.toNat + 3 + rsz.toNat < 2 ^ 64 := by have := rsz.isLt; omega
        rw [hal_eq, Nat.mod_eq_of_lt (by omega : s.core.arena_len < 2 ^ 64),
          Nat.mod_eq_of_lt hbd64] at hgt; omega
      · have hrsz_bd : rsz.toNat < 2 ^ 32 := rsz.isLt
        let BrkJ := Nat × Bool × Bool × BitVec 32 × FullState
        let RsnLp := Nat × BitVec 32 × FullState
        c0_hsteps_nogrp
        refine wp_join_state (ts := [i64, .bool, .bool, i32]) (α := BrkJ)
          (proj := fun st => (BitVec.ofNat 64 st.1, st.2.1, st.2.2.1, st.2.2.2.1, ()))
          (Inv := fun st m3 =>
            let u' := st.1; let d' := st.2.1; let e' := st.2.2.1; let s3 := st.2.2.2.2
            FailedStateOk c s s3 cut ∧ s3.core.tmp = s1.core.tmp ∧
            (!e' → !d' → u' = (flIdxs s3.core.mrk s.core.trl t').length + 1 ∧
              (cnfOfClauses F_cur).EntailsClause (cnfClause (flLits s3.core.mrk s.core.trl t'))) ∧
            (FullMem c s3 ⋆ R_hdr) m3) ?_ ?_
        · intro _ ⟨u', d', e', _j, s3⟩ m3 ⟨hok3, htmp3, hok_b, hm3⟩
          dsimp only at hok3 htmp3 hok_b hm3; rw [Blocks.get_here]; dsimp only
          c0_hsteps; exact hJrsn u' d' e' s3 m3 hok3 htmp3 hok_b hm3
        · intro Jb hJb
          refine wp_while_state (ts := [i64, i32]) (α := RsnLp)
            (proj := fun st => (BitVec.ofNat 64 st.1, st.2.1, ()))
            (μ := fun st => rsz.toNat - st.2.1.toNat)
            (Inv := fun st m3 =>
              let uj := st.1; let j := st.2.1; let sj := st.2.2
              j.toNat ≤ rsz.toNat ∧ FailedStateOk c s sj cut ∧ sj.core.tmp = s1.core.tmp ∧
              uj = (flIdxs sj.core.mrk s.core.trl t').length + 1 ∧
              (∀ l ∈ flLits s1.core.mrk s.core.trl t', l ∈ flLits sj.core.mrk s.core.trl t') ∧
              (∀ q ∈ (fullArenaClauseLitsCore s.core rsn32.toNat).take j.toNat,
                q = lit'.toNat ∨ (cnfOfClauses F_cur).EntailsClause (cnfClause [q ^^^ 1]) ∨
                q ∈ flLits sj.core.mrk s.core.trl t') ∧
              (FullMem c sj ⋆ R_hdr) m3) ?_ ?_
          · intro Jl hJl; c0_hsteps
            exact hJl (unres, 0#32, s1) m2 ⟨Nat.zero_le _, hok1, rfl, hunres_t'_s,
              fun _ hl => hl, fun _ hq => by simp at hq, hm2⟩
          · intro Jl ⟨uj, j, sj⟩ m3 ⟨hj_le, hokj, htmpj, huj_eq, hpresj, hcovj, hm3⟩ ih_j
            dsimp only at hj_le hokj htmpj huj_eq hpresj hcovj hm3 ih_j
            rw [Blocks.get_here]; dsimp only
            have hj_cv := hokj.len.core_ok
            have har_j : sj.core.arena = s.core.arena := by rw [hokj.core]
            have huj_bd : uj ≤ s.core.cur_vars + 1 := by
              rw [huj_eq]
              exact Nat.le_trans (Nat.succ_le_succ (flIdxs_length_le _ _ _)) (by omega)
            c0_hsplit
            · have hj_lt : j.toNat < rsz.toNat := by dsimp only [rsz]; assumption
              have hj_csz : j.toNat < fullArenaClauseSizeCore s.core rsn32.toNat := by
                rw [← hrsz_eq]; exact hj_lt
              obtain ⟨hot_ar_lt, hot_lits_len, hot_get, hot_mem⟩ :=
                p2_arena_clause_lit hlen0 hokj.len har_j rfl (hrsn_eq.symm ▸ hrsn_bd) hj_csz
              let ot32 := sj.core.arena[(rsn32.setWidth 64 + 3#64 + j.setWidth 64).toNat]'hot_ar_lt
              have hot_ar_lt_c : (rsn32.toNat + 3 + j.toNat) % 2 ^ 64 < sj.core.arena.length := by
                simpa only [BitVec.toNat_add, fl_bv32_setWidth64,
                  show (3#64 : BitVec 64).toNat = 3 from rfl,
                  Nat.mod_eq_of_lt (by omega : rsn32.toNat + 3 < 2 ^ 64)] using hot_ar_lt
              have hot_hc : sj.core.arena[(rsn32.toNat + 3 + j.toNat) % 2 ^ 64]'hot_ar_lt_c =
                  ot32 := by
                dsimp only [ot32]; congr 1
                rw [BitVec.toNat_add, BitVec.toNat_add, fl_bv32_setWidth64, fl_bv32_setWidth64,
                  show (3#64 : BitVec 64).toNat = 3 from rfl,
                  Nat.mod_eq_of_lt (by omega : rsn32.toNat + 3 < 2 ^ 64)]
              have hot_mem_c : ot32.toNat ∈ fullArenaClauseLitsCore s.core
                  (s.core.rsns[lit'.toNat / 2]?.getD 0xFFFFFFFF#32).toNat :=
                hrsn_eq ▸ hot_mem
              have hot_lt : ot32.toNat < 2 * s.core.cur_vars :=
                hw0.arena.lits_lt _ href hng _ hot_mem_c
              have hj1_bv : (j + 1#32).toNat = j.toNat + 1 :=
                fl_bv32_add1_toNat hj_lt (by have := rsz.isLt; omega)
              c0_hsteps_nogrp
              refine wp_join_state (ts := [i64, .bool, .bool]) (α := Nat × FullState)
                (proj := fun st => (BitVec.ofNat 64 st.1, done, brk, ()))
                (Inv := fun st m4 =>
                  let uj' := st.1; let sj' := st.2
                  FailedStateOk c s sj' cut ∧ sj'.core.tmp = s1.core.tmp ∧
                  (∀ l ∈ flLits s1.core.mrk s.core.trl t', l ∈ flLits sj'.core.mrk s.core.trl t') ∧
                  uj' = (flIdxs sj'.core.mrk s.core.trl t').length + 1 ∧
                  (∀ q ∈ (fullArenaClauseLitsCore s.core rsn32.toNat).take (j.toNat + 1),
                    q = lit'.toNat ∨ (cnfOfClauses F_cur).EntailsClause (cnfClause [q ^^^ 1]) ∨
                    q ∈ flLits sj'.core.mrk s.core.trl t') ∧
                  (FullMem c sj' ⋆ R_hdr) m4) ?_ ?_
              · intro _ ⟨uj', sj'⟩ m4 ⟨hokj', htmpj', hpresj', huj'_eq, hcov_j1, hm4⟩
                dsimp only at hokj' htmpj' hpresj' huj'_eq hcov_j1 hm4
                rw [Blocks.get_here]; dsimp only; c0_hsteps
                exact ih_j (uj', j + 1#32, sj') m4 (by dsimp only; omega)
                  ⟨by dsimp only; omega, hokj', htmpj', huj'_eq, hpresj',
                    by dsimp only; simpa only [hj1_bv] using hcov_j1, hm4⟩
              · intro Jc hJc; c0_hsplit
                · c0_hsplit
                  · c0_hsteps
                    exact hJb (uj, true, brk, j, sj) m3
                      ⟨hokj, htmpj, fun _ hd => by simp at hd, hm3⟩
                  · have hot_rsn := hall ot32.toNat hot_mem_c
                    have hot_ne : ot32.toNat ≠ lit'.toNat := fun he =>
                      (by rw [← hot_hc]; assumption : ot32 ≠ lit') (BitVec.eq_of_toNat_eq he)
                    obtain ⟨m_ot, hm_ot_lt, hm_ot_eq⟩ := hot_rsn.resolve_left hot_ne
                    have hov_lt := Nat.div_lt_of_lt_mul hot_lt
                    have hcvj : sj.core.cur_vars = s.core.cur_vars := by rw [hokj.core]
                    have hcv_le := hlen0.core_ok.cur_vars_le
                    have h032 : BitVec.ofNat (OfNat.ofNat 32) (OfNat.ofNat 0) = 0#32 := rfl
                    have hov_lvl_lt : ot32.toNat / 2 < sj.core.lvl.length := by
                      rw [hj_cv.lvl_len]; have := hj_cv.cur_vars_le; omega
                    have hov_mrk_lt : ot32.toNat / 2 < sj.core.mrk.length := by
                      rw [hj_cv.mrk_len]; have := hj_cv.cur_vars_le; omega
                    c0_hsplit
                    · exfalso
                      have hge : s.core.cur_vars % 2 ^ 64 ≤ ot32.toNat / 2 := by
                        rw [← hot_hc]; assumption
                      rw [Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64)] at hge; omega
                    · refine wp_join_state (ts := [i64]) (α := Nat × FullState)
                        (proj := fun st => (BitVec.ofNat 64 st.1, ()))
                        (Inv := fun st m4 =>
                          let uj' := st.1; let sj' := st.2
                          FailedStateOk c s sj' cut ∧ sj'.core.tmp = s1.core.tmp ∧
                          (∀ l ∈ flLits s1.core.mrk s.core.trl t',
                            l ∈ flLits sj'.core.mrk s.core.trl t') ∧
                          uj' = (flIdxs sj'.core.mrk s.core.trl t').length + 1 ∧
                          (∀ q ∈ (fullArenaClauseLitsCore s.core rsn32.toNat).take (j.toNat + 1),
                            q = lit'.toNat ∨
                            (cnfOfClauses F_cur).EntailsClause (cnfClause [q ^^^ 1]) ∨
                            q ∈ flLits sj'.core.mrk s.core.trl t') ∧
                          (FullMem c sj' ⋆ R_hdr) m4) ?_ ?_
                      · intro _ ⟨uj', sj'⟩ m4 ⟨hokj', htmpj', hpresj', huj', hcovj1, hm4⟩
                        dsimp only at hokj' htmpj' hpresj' huj' hcovj1 hm4
                        rw [Blocks.get_here]; dsimp only; c0_hsteps
                        exact hJc (uj', sj') m4 ⟨hokj', htmpj', hpresj', huj', hcovj1, hm4⟩
                      · intro Jo hJo; c0_hsplit
                        · c0_hsplit
                          · have hmrk0_ov := fl_mark_zero_eq hokj hov_lt (by
                              simpa only [← hot_hc, h032] using (by assumption : _))
                            have hlvl_pos := p2_lvl_pos_of_lt hokj hov_lvl_lt (by
                              simpa only [← hot_hc,
                                show (0#32 : BitVec 32).toNat = BitVec.toNat 0 from rfl] using
                                (by assumption : _))
                            obtain ⟨hmcl_lt, hmcl64, hmcl_ws, hmcl1_bv, hok2,
                                hfl_len, hfl_pres, hot_in⟩ :=
                              p2_push_step hw0 hcl1 hokj (by omega) hot_lt hmrk0_ov hlvl_pos
                                ⟨m_ot, hm_ot_lt, hm_ot_eq⟩ ⟨m_ot, by omega, hm_ot_eq⟩
                            let s2 : FullState :=
                              { core := { sj.core with
                                  mrk := sj.core.mrk.set (ot32.toNat / 2) 1#8,
                                  min_clr_len := sj.core.min_clr_len + 1 },
                                scratch := { sj.scratch with
                                  work_stk1 :=
                                    sj.scratch.work_stk1.set sj.core.min_clr_len (ot32 >>> 1) } }
                            have hpres2 : ∀ l ∈ flLits s1.core.mrk s.core.trl t',
                                l ∈ flLits s2.core.mrk s.core.trl t' :=
                              fun l hl => hfl_pres l (hpresj l hl)
                            have hcovj2 :
                                ∀ q ∈ (fullArenaClauseLitsCore s.core rsn32.toNat).take j.toNat,
                                q = lit'.toNat ∨
                                (cnfOfClauses F_cur).EntailsClause (cnfClause [q ^^^ 1]) ∨
                                q ∈ flLits s2.core.mrk s.core.trl t' := fun q hq =>
                              (hcovj q hq).elim Or.inl fun h =>
                                Or.inr (h.elim Or.inl fun hm => Or.inr (hfl_pres q hm))
                            have hcov2 := fl_take_succ_list _ hot_lits_len _ hcovj2
                              (hot_get ▸ hot_in.elim (fun h0 => Or.inr (Or.inl h0))
                                (fun hm => Or.inr (Or.inr hm)))
                            c0_hsplit
                            c0_hsteps
                            have hm2' : (FullMem c s2 ⋆ R_hdr) m := by
                              simpa only [s2, ot32, show (3 : BitVec 64) = 3#64 from rfl,
                                show BitVec.ofNat 8 1 = 1#8 from rfl, fl_bv32_setWidth64,
                                bv32_lshr_1, p2_bv64_ofNat_toNat hmcl64, hmcl1_bv] using hm
                            rw [fl_bv64_add1_eq (by omega)]
                            exact hJo (uj + 1, s2) m
                              ⟨hok2, htmpj, hpres2, by rw [huj_eq, hfl_len], hcov2, hm2'⟩
                          · have hmrk_nz := fl_mark_nz_eq hokj hov_lt (by
                              simpa only [← hot_hc, h032] using (by assumption : _))
                            have hot_in := fl_mark_lit_skip hw0 hcl1 (by omega)
                              (fun _ => ⟨m_ot, by omega, hm_ot_eq⟩)
                              (fun _ => ⟨hmrk_nz, m_ot, hm_ot_lt, hm_ot_eq⟩)
                            have hcov2 := fl_take_succ_list _ hot_lits_len _ hcovj
                              (hot_get ▸ hot_in.elim (fun h => Or.inr (Or.inl h))
                                (fun h => Or.inr (Or.inr h)))
                            c0_hsteps
                            exact hJo (uj, sj) m3 ⟨hokj, htmpj, hpresj, huj_eq, hcov2, hm3⟩
                        · have hlvl0 := p2_lvl0_of_nlt hokj hov_lvl_lt (by
                            simpa only [← hot_hc,
                              show (0#32 : BitVec 32).toNat = BitVec.toNat 0 from rfl] using
                              (by assumption : _))
                          have hot_in := fl_mark_lit_skip (s1 := sj) (t := t') (q := ot32.toNat)
                            hw0 hcl1 (by omega) (fun _ => ⟨m_ot, by omega, hm_ot_eq⟩)
                            (fun hp => by omega)
                          have hcov2 := fl_take_succ_list _ hot_lits_len _ hcovj
                            (hot_get ▸ hot_in.elim (fun h => Or.inr (Or.inl h))
                              (fun h => Or.inr (Or.inr h)))
                          c0_hsteps
                          exact hJo (uj, sj) m3 ⟨hokj, htmpj, hpresj, huj_eq, hcov2, hm3⟩
                · have hot_eq : ot32.toNat = lit'.toNat :=
                    congrArg BitVec.toNat (by simp only [← hot_hc]; assumption : ot32 = lit')
                  have hcov2 := fl_take_succ_list _ hot_lits_len _ hcovj (hot_get ▸ Or.inl hot_eq)
                  c0_hsteps; exact hJc (uj, sj) m3 ⟨hokj, htmpj, hpresj, huj_eq, hcov2, hm3⟩
            · have hrsz_lt_c : (rsn32.toNat + 2) % 2 ^ 64 < s1.core.arena.length := by
                simpa only [BitVec.toNat_add, fl_bv32_setWidth64,
                  show (2#64 : BitVec 64).toNat = 2 from rfl,
                  Nat.mod_eq_of_lt (by omega : rsn32.toNat + 2 < 2 ^ 64)] using hrsn_add2_lt
              have hrsz_hc : s1.core.arena[(rsn32.toNat + 2) % 2 ^ 64]'hrsz_lt_c = rsz := by
                dsimp only [rsz]; congr 1
                try rw [BitVec.toNat_add, fl_bv32_setWidth64,
                  show (2#64 : BitVec 64).toNat = 2 from rfl,
                  Nat.mod_eq_of_lt (by omega : rsn32.toNat + 2 < 2 ^ 64)]
              have hj_nge : ¬ j.toNat < rsz.toNat := by rw [← hrsz_hc]; assumption
              have hj_eq : j.toNat = rsz.toNat := by omega
              have htake_all : (fullArenaClauseLitsCore s.core rsn32.toNat).take j.toNat =
                  fullArenaClauseLitsCore s.core rsn32.toNat := by
                rw [hj_eq, hrsn_eq, ← hlits_len]; exact List.take_length
              rw [htake_all] at hcovj
              have hent_cl := hw0.arena.entails _ href hng; rw [← hrsn_eq] at hent_cl
              have hent_j := fl_resolve_step hmrk_t'_trl hact_t' hpresj hent_cl
                (by simpa only [htrl_t'] using hcovj)
              c0_hsteps
              exact hJb (uj, done, brk, j, sj) m3 ⟨hokj, htmpj, fun _ _ => ⟨huj_eq, hent_j⟩, hm3⟩

end FlMainHelpers

/-! ## 4. Top-Level `full_ana_failed_lit_m6_hdr_wp` -/

/-- Parametric `Func.wp` proof for `Src.Analyze.full_ana_failed_lit_m6_hdr_body` against
`Analyze.Spec.fullAnaFailedLitM6HdrSpec`. -/
theorem full_ana_failed_lit_m6_hdr_wp (Γ : Env)
    (hClear : ∀ a m Q X, fullClearAnaSpec a m Q X → Γ "full_clear_ana" [i64] [] a m Q X)
    (hBumpMode : ∀ a m Q X, fullBumpAnalyzedModeSpec a m Q X →
      Γ "full_bump_analyzed_mode_fid" [i64, .bool] [] a m Q X)
    (hBacktrackAc : ∀ a m Q X, fullBacktrackSpec a m Q X →
      Γ "full_backtrack_ac_fid" [i64, i64] [] a m Q X)
    (hAssignLvl : ∀ a m Q X, fullAssignLvlSpec a m Q X →
      Γ "full_assign_lvl" [i64, i32, i32, i32] [] a m Q X)
    (hTickRel : ∀ a m Q X, fullTickRelSpec a m Q X → Γ "full_tick_rel" [i64] [] a m Q X)
    (hEma : ∀ a m Q X, fullEmaUpdateSpec a m Q X → Γ "full_ema_update" [i64, i64] [] a m Q X) :
    ∀ a m Q X, fullAnaFailedLitM6HdrSpec a m Q X →
      Func.wp Γ Src.Analyze.full_ana_failed_lit_m6_hdr_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m0 Q X hspec
  obtain ⟨c, F0, F_cur, cut, ext, s, R, rfl, hcfg, hext, hcut, _, hconfl, hm0, hQ⟩ := hspec
  have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
  have ⟨hlen0, hw0, hlm0, _, _, _⟩ := hcut
  have hcl := hlen0.core_ok; have hcv_le := hcl.cur_vars_le
  have hte_le := hcl.trail_end_le; have hcur_le := hw0.cur_level_le
  let R_hdr : Mem 64 → Prop := m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R
  unfold Func.wp Src.Analyze.full_ana_failed_lit_m6_hdr_body; dsimp only
  refine wp_m6Hdr_focus_frame hm0 fun hm => ?_
  have hEarly : ∀ (m : Mem 64), (FullMem c s ⋆ R_hdr) m → Q (0#64, ()) m := fun m hm' =>
    hQ 0#64 ext s m hext (fun hi => ⟨hi, M6ExtW2bPres.refl ext⟩) hlen0 (Or.inl rfl) rfl rfl rfl
      (fun h => by cases h) (fun _ => hcut.toOtfs) (fun h => by cases h)
      (fullM6HdrMem_unfocus hm')
  c0_hsplit; · (c0_hsteps; exact hEarly m0 hm)
  have hcl1 : s.core.cur_level = 1 := by
    have h1 := congrArg BitVec.toNat (by assumption : BitVec.ofNat 64 s.core.cur_level = 1#64)
    rw [p2_bv64_ofNat_toNat (by omega)] at h1; exact h1
  c0_hsplit; · (c0_hsteps; exact hEarly m0 hm)
  have hcv_pos : 0 < s.core.cur_vars := by omega
  have hfdec1_len : 1 < s.core.frame_dec.length := by rw [hcl.frame_dec_len]; omega
  c0_hsplit; · (c0_hsteps; exact hEarly m0 hm)
  let failed := s.core.frame_dec[(1#64 : BitVec 64).toNat]'(by simpa using hfdec1_len)
  let fv := failed >>> 1; let not_failed := failed ^^^ 1#32
  have hfv_lt : fv.toNat < s.core.cur_vars := by
    have hnge : ¬ s.core.cur_vars % 2 ^ 64 ≤ failed.toNat / 2 := by assumption
    rw [Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64)] at hnge
    dsimp only [fv]; rw [bv32_lshr_1]; exact Nat.lt_of_not_le hnge
  have hfl_lt : failed.toNat < 2 * s.core.cur_vars := by
    dsimp only [fv] at hfv_lt; rw [bv32_lshr_1] at hfv_lt; omega
  have hfl_val_lt : (failed.setWidth 64).toNat < s.core.vals.length := by
    rw [fl_bv32_setWidth64, hcl.vals_len]; omega
  have hfv_lvl_lt : (fv.setWidth 64).toNat < s.core.lvl.length := by
    rw [fl_bv32_setWidth64, hcl.lvl_len]; omega
  have hfv_rsn_lt : (fv.setWidth 64).toNat < s.core.rsns.length := by
    rw [fl_bv32_setWidth64, hcl.rsns_len]; omega
  c0_hsplit; · (c0_hsteps; exact hEarly m0 hm)
  have hfl_val : s.core.vals[failed.toNat]?.getD 0#8 = 1#8 := by
    have hdom := hw0.vals_domain failed.toNat hfl_lt
    have hidx : failed.toNat < s.core.vals.length := by rw [hcl.vals_len]; omega
    rw [List.getElem?_eq_getElem hidx, Option.getD_some] at hdom ⊢
    rcases hdom with h | h | h
    · have hs : (BitVec.signExtend 32 s.core.vals[failed.toNat]).sle 0#32 = false := by
        simpa [failed] using (by assumption : _)
      rw [h] at hs; exact absurd hs (by decide)
    · exact h
    · have hs : (BitVec.signExtend 32 s.core.vals[failed.toNat]).sle 0#32 = false := by
        simpa [failed] using (by assumption : _)
      rw [h] at hs; exact absurd hs (by decide)
  c0_hsplit; · (c0_hsteps; exact hEarly m0 hm)
  have hfl_lvl1 : (s.core.lvl[failed.toNat / 2]?.getD 0#32).toNat = 1 := by
    have hidx : failed.toNat / 2 < s.core.lvl.length := by rw [hcl.lvl_len]; omega
    rw [List.getElem?_eq_getElem hidx, Option.getD_some]
    exact congrArg BitVec.toNat (by assumption : s.core.lvl[failed.toNat / 2]'hidx = 1#32)
  c0_hsplit; · (c0_hsteps; exact hEarly m0 hm)
  have hfl_rsn : s.core.rsns[failed.toNat / 2]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 := by
    have hidx : failed.toNat / 2 < s.core.rsns.length := by rw [hcl.rsns_len]; omega
    rw [List.getElem?_eq_getElem hidx, Option.getD_some]
    exact (by assumption : s.core.rsns[failed.toNat / 2]'hidx = 0xFFFFFFFF#32)
  have himp := fl_trail_imp hw0 hcl1 hfl_val hfl_lt hfl_lvl1 hfl_rsn
  have hnf_ent : (cnfOfClauses F_cur).EntailsClause (cnfClause [not_failed.toNat]) := by
    simpa only [not_failed, fl_bv32_xor1] using failedLit_not_failed_of_confl hw0 hcl1 hconfl himp
  have hnf_lt : not_failed.toNat < 2 * s.core.cur_vars := by
    rw [fl_bv32_xor1]; exact litNeg_lt_two_mul hfl_lt
  c0_hsteps_nogrp
  let s0 : FullState := { s with core := { s.core with min_clr_len := 0 } }
  have hok0 : FailedStateOk c s s0 cut :=
    ⟨⟨{ hcl with min_clr_len_le := Nat.zero_le _ }, hlen0.scratch_ok⟩, rfl, rfl,
     ⟨Nat.zero_le _, by simp [s0], fun _ hk => absurd hk (Nat.not_lt_zero _),
      fun v hv hnz => absurd (hlm0.1 v hv) hnz⟩, fl_mb_empty (fun v hv => hlm0.1 v (by omega))⟩
  have hm_s0 : (FullMem c s0 ⋆ R_hdr) m := by simpa [s0]
  refine wp_join_state (ts := [i64, .bool]) (α := Nat × Bool × FullState)
    (proj := fun st => (BitVec.ofNat 64 st.1, st.2.1, ()))
      (Inv := fun st m1 => st.1 ≤ s.core.cur_vars ∧ FailedStateOk c s st.2.2 cut ∧
        (!st.2.1 → st.1 = (flIdxs st.2.2.core.mrk s.core.trl s.core.trail_end).length ∧
          (cnfOfClauses F_cur).EntailsClause
            (cnfClause (flLits st.2.2.core.mrk s.core.trl s.core.trail_end))) ∧
        (FullMem c st.2.2 ⋆ R_hdr) m1) ?_ ?_
  · intro _ ⟨unres0, done0, s_sd⟩ m_sd ⟨hunres0_le, hok_sd, hact_sd, hm_sd⟩
    dsimp only at hunres0_le hok_sd hact_sd hm_sd; rw [Blocks.get_here]; dsimp only
    c0_hsteps_nogrp
    let LpIn := Nat × Nat × Bool × Nat × BitVec 32 × Bool × FullState
    refine wp_join_state (ts := [i64, i64, .bool, i64, i32, .bool]) (α := LpIn)
      (proj := fun st => (BitVec.ofNat 64 st.1, BitVec.ofNat 64 st.2.1, st.2.2.1,
        BitVec.ofNat 64 st.2.2.2.1, st.2.2.2.2.1, st.2.2.2.2.2.1, ()))
      (Inv := fun st m1 =>
        let unres := st.1; let ucnt := st.2.1; let done := st.2.2.1
        let t := st.2.2.2.1; let err := st.2.2.2.2.2.1; let s1 := st.2.2.2.2.2.2
        FailedStateOk c s s1 cut ∧ t ≤ s.core.trail_end ∧ ucnt ≤ s.core.cur_vars ∧
        (∀ k < ucnt, (s1.core.tmp[k]?.getD 0#32).toNat < 2 * s.core.cur_vars ∧
          (cnfOfClauses F_cur).EntailsClause (cnfClause [(s1.core.tmp[k]?.getD 0#32).toNat])) ∧
        (!err → !done → unres = (flIdxs s1.core.mrk s.core.trl t).length ∧
          (cnfOfClauses F_cur).EntailsClause (cnfClause (flLits s1.core.mrk s.core.trl t))) ∧
        (FullMem c s1 ⋆ R_hdr) m1) ?_ ?_
    · intro _ ⟨unres_f, ucnt_f, done_f, t_f, unit_f, err_f, s_f⟩ m_f
        ⟨hok_f, ht_f_le, hucnt_le, htmp_f, hact_f, hm_f⟩
      dsimp only
      exact s13_fl_post_loop_hdr_wp hClear hBumpMode hBacktrackAc hAssignLvl hTickRel hEma hcfg
        hext hcut hcl1 hnf_lt hnf_ent hQ hok_f ht_f_le hucnt_le htmp_f hact_f hm_f
    · intro Jexit hJexit; c0_hsteps_nogrp
      refine wp_while_state (ts := [i64, i64, .bool, i64, i32, .bool]) (α := LpIn)
        (proj := fun st => (BitVec.ofNat 64 st.1, BitVec.ofNat 64 st.2.1, st.2.2.1,
          BitVec.ofNat 64 st.2.2.2.1, st.2.2.2.2.1, st.2.2.2.2.2.1, ()))
        (μ := fun st => 2 * st.2.2.2.1 + if st.2.2.1 || st.2.2.2.2.2.1 then 0 else 1)
        (Inv := fun st m1 =>
          let unres := st.1; let ucnt := st.2.1; let done := st.2.2.1
          let t := st.2.2.2.1; let err := st.2.2.2.2.2.1; let s1 := st.2.2.2.2.2.2
          FailedStateOk c s s1 cut ∧ t ≤ s.core.trail_end ∧ ucnt ≤ s.core.cur_vars ∧
          (∀ k < ucnt, (s1.core.tmp[k]?.getD 0#32).toNat < 2 * s.core.cur_vars ∧
            (cnfOfClauses F_cur).EntailsClause (cnfClause [(s1.core.tmp[k]?.getD 0#32).toNat])) ∧
          (!err → !done → unres = (flIdxs s1.core.mrk s.core.trl t).length ∧
            (cnfOfClauses F_cur).EntailsClause (cnfClause (flLits s1.core.mrk s.core.trl t))) ∧
          (FullMem c s1 ⋆ R_hdr) m1) ?_ ?_
      · intro Jlp hJlp; c0_hsteps
        have hte_sd : s_sd.core.trail_end = s.core.trail_end := by rw [hok_sd.core]
        simpa only [show (0 : BitVec 64) = BitVec.ofNat 64 0 from rfl,
          show (4294967295 : BitVec 32) = 0xFFFFFFFF#32 from rfl, hte_sd] using
          hJlp (unres0, 0, done0, s.core.trail_end, 0xFFFFFFFF#32, false, s_sd) m_sd
            ⟨hok_sd, Nat.le_refl _, Nat.zero_le _, (fun _ hk => by cases hk),
              fun _ hnd => hact_sd hnd, hm_sd⟩
      · intro Jlp ⟨unres, ucnt, done, t, unit, err, s_lp⟩ m1
          ⟨hok_lp, ht_le, hucnt_le, htmp_ok, hact_ok, hm1⟩ ih_lp
        dsimp only at hok_lp ht_le hucnt_le htmp_ok hact_ok hm1 ih_lp
        rw [Blocks.get_here]; dsimp only
        c0_hsplit
        · c0_hsteps
          exact hJexit (unres, ucnt, done, t, unit, err, s_lp) m1
            ⟨hok_lp, ht_le, hucnt_le, htmp_ok, hact_ok, hm1⟩
        have hdone_f : done = false := by assumption
        c0_hsplit
        · c0_hsteps
          exact hJexit (unres, ucnt, done, t, unit, err, s_lp) m1
            ⟨hok_lp, ht_le, hucnt_le, htmp_ok, hact_ok, hm1⟩
        have herr_f : err = false := by assumption
        obtain ⟨hunres_len, hact_ent⟩ := hact_ok (by simp [herr_f]) (by simp [hdone_f])
        have hunres_bd : unres ≤ s.core.cur_vars :=
          Nat.le_trans (hunres_len ▸ flIdxs_length_le _ _ _) (by omega)
        c0_hsteps_nogrp
        refine wp_join_state (ts := [i64, .bool, i32]) (α := Nat × Bool × BitVec 32)
          (proj := fun st => (BitVec.ofNat 64 st.1, st.2.1, st.2.2, ()))
          (Inv := fun st m_f =>
            let t' := st.1; let err' := st.2.1; let lit' := st.2.2
            m_f = m1 ∧ if err' then t' ≤ t
            else t' < t ∧ (s.core.trl[t']?.getD 0#32).toNat = lit'.toNat ∧
              lit'.toNat < 2 * s.core.cur_vars ∧ s_lp.core.mrk[lit'.toNat / 2]?.getD 0#8 ≠ 0#8 ∧
              unres = (flIdxs s_lp.core.mrk s.core.trl (t' + 1)).length ∧
              (cnfOfClauses F_cur).EntailsClause
                (cnfClause (flLits s_lp.core.mrk s.core.trl (t' + 1)))) ?_ ?_
        · intro _ ⟨t', err', lit'⟩ m_f ⟨hm_eq, hfind⟩
          dsimp only at hfind; rw [Blocks.get_here]; dsimp only
          c0_hsplit
          · have he : err' = true := by assumption
            rw [ite_eq_left he] at hfind
            c0_hsteps; exact hJexit (unres, ucnt, done, t', unit, true, s_lp) m_f
              ⟨hok_lp, by dsimp only; omega, hucnt_le, htmp_ok, (fun h => by cases h), hm_eq ▸ hm1⟩
          · have he_f : err' = false := by assumption
            rw [ite_eq_right (he_f ▸ Bool.false_ne_true)] at hfind
            obtain ⟨ht'_lt, htrl_t', hlit'_lt, hmrk_t'_0, hunres_t'_0, hact_t'_0⟩ := hfind
            c0_hsplit
            · c0_hsteps
              have hff := congrArg BitVec.toNat (by assumption : lit' = 4294967295)
              rw [show (4294967295 : BitVec 32).toNat = 4294967295 from rfl] at hff; omega
            c0_hsteps_nogrp
            refine wp_join_state (ts := [i64, i32, .bool]) (α := Nat × BitVec 32 × Bool × FullState)
              (proj := fun st => (BitVec.ofNat 64 st.1, st.2.1, st.2.2.1, ()))
              (Inv := fun st m2 =>
                let ucnt' := st.1; let s1 := st.2.2.2
                st.2.2.1 = false ∧ FailedStateOk c s s1 cut ∧ s1.core.mrk = s_lp.core.mrk ∧
                s1.core.min_clr_len = s_lp.core.min_clr_len ∧
                s1.scratch.work_stk1 = s_lp.scratch.work_stk1 ∧
                ucnt' ≤ s.core.cur_vars ∧
                (∀ k < ucnt', (s1.core.tmp[k]?.getD 0#32).toNat < 2 * s.core.cur_vars ∧
                  (cnfOfClauses F_cur).EntailsClause
                    (cnfClause [(s1.core.tmp[k]?.getD 0#32).toNat])) ∧
                (FullMem c s1 ⋆ R_hdr) m2) ?_ ?_
            · intro _ ⟨ucnt', unit', _brk', s1⟩ m2
                ⟨hbrk', hok1, hmrk1_eq, hmcl1_eq, hws1_eq, hucnt'_le, htmp_ok', hm2⟩
              dsimp only at hbrk' hok1 hmrk1_eq hmcl1_eq hws1_eq hucnt'_le htmp_ok' hm2
              rw [Blocks.get_here]; dsimp only
              have hl1_cv := hok1.len.core_ok
              have hmrk_t' : s1.core.mrk[lit'.toNat / 2]?.getD 0#8 ≠ 0#8 := by
                rw [hmrk1_eq]; exact hmrk_t'_0
              have hmrk_t'_trl :
                  s1.core.mrk[(s.core.trl[t']?.getD 0#32).toNat / 2]?.getD 0#8 ≠ 0#8 := by
                rw [htrl_t']; exact hmrk_t'
              have hunres_t' : unres = (flIdxs s1.core.mrk s.core.trl (t' + 1)).length := by
                rw [hmrk1_eq]; exact hunres_t'_0
              have hact_t' : (cnfOfClauses F_cur).EntailsClause
                  (cnfClause (flLits s1.core.mrk s.core.trl (t' + 1))) := by
                rw [hmrk1_eq]; exact hact_t'_0
              have hcv_s1 : s1.core.cur_vars = s.core.cur_vars := by rw [hok1.core]
              have hlv_rsn : ((lit' >>> 1#32).setWidth 64).toNat < s1.core.rsns.length := by
                rw [fl_bv32_setWidth64, fl_bv32_lshr1, hl1_cv.rsns_len]
                have := hl1_cv.cur_vars_le; omega
              c0_hsplit
              · c0_hsteps
                exact hJexit (unres, ucnt', done, t', unit', true, s1) m2
                  ⟨hok1, by dsimp only; omega, hucnt'_le, htmp_ok', (fun h => by cases h), hm2⟩
              have hlv_rsn_d : lit'.toNat / 2 < s1.core.rsns.length := by
                rw [hl1_cv.rsns_len]; have := hl1_cv.cur_vars_le; omega
              have heq_rsn : s1.core.rsns[lit'.toNat / 2]?.getD 0xFFFFFFFF#32 =
                  s.core.rsns[lit'.toNat / 2]?.getD 0xFFFFFFFF#32 := by rw [hok1.core]
              have hrsn_ne : s.core.rsns[lit'.toNat / 2]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 := by
                rw [← heq_rsn, List.getElem?_eq_getElem hlv_rsn_d, Option.getD_some]
                simpa only [show (4294967295 : BitVec 32) = 0xFFFFFFFF#32 from rfl] using
                  (by assumption : s1.core.rsns[lit'.toNat / 2]'hlv_rsn_d ≠ 4294967295)
              have ht'_cut : t' < cut := by
                obtain ⟨_, m_c, hm_cut, hm_eq'⟩ :=
                  fl_mb_get hok1.mb (Nat.div_lt_of_lt_mul hlit'_lt) hmrk_t'
                have htm := hw0.trail_vars_nodup t' m_c (by omega)
                  (Nat.lt_of_lt_of_le hm_cut hw0.cut_le)
                  (by rw [htrl_t', hm_eq']); omega
              have hri := hw0.reason_inv_cut t' ht'_cut (by rwa [htrl_t'])
              rw [htrl_t'] at hri; c0_hsteps_nogrp
              refine wp_join_state (ts := [i64, .bool, .bool]) (α := Nat × Bool × Bool × FullState)
                (proj := fun st => (BitVec.ofNat 64 st.1, st.2.1, st.2.2.1, ()))
                (Inv := fun st m3 =>
                  let unres' := st.1; let done' := st.2.1; let err'' := st.2.2.1; let s3 := st.2.2.2
                  FailedStateOk c s s3 cut ∧ s3.core.tmp = s1.core.tmp ∧
                  (!err'' → !done' → unres' = (flIdxs s3.core.mrk s.core.trl t').length + 1 ∧
                    (cnfOfClauses F_cur).EntailsClause
                      (cnfClause (flLits s3.core.mrk s.core.trl t'))) ∧
                  (FullMem c s3 ⋆ R_hdr) m3) ?_ ?_
              · intro _ ⟨unres', done', err'', s3⟩ m3 ⟨hok3, htmp3, hrsn_ok, hm3⟩
                dsimp only at hok3 htmp3 hrsn_ok hm3; rw [Blocks.get_here]; dsimp only
                have htmp3' : ∀ k < ucnt', (s3.core.tmp[k]?.getD 0#32).toNat < 2 * s.core.cur_vars ∧
                    (cnfOfClauses F_cur).EntailsClause
                      (cnfClause [(s3.core.tmp[k]?.getD 0#32).toNat]) :=
                  fun k hk => by rw [htmp3]; exact htmp_ok' k hk
                c0_hsplit
                · have hd'_t : done' = true := by assumption
                  c0_hsteps
                  exact hJexit (unres', ucnt', done', t', unit', err'', s3) m3
                    ⟨hok3, by dsimp only; omega, hucnt'_le, htmp3',
                      (fun _ hd => by simp [hd'_t] at hd), hm3⟩
                · have hd'_f : done' = false := by assumption
                  c0_hsplit
                  · have he''_t : err'' = true := by assumption
                    c0_hsteps
                    exact hJexit (unres', ucnt', done', t', unit', err'', s3) m3
                      ⟨hok3, by dsimp only; omega, hucnt'_le, htmp3',
                        (fun he => by simp [he''_t] at he), hm3⟩
                  · have he''_f : err'' = false := by assumption
                    obtain ⟨hunres'_eq, hent3⟩ := hrsn_ok (by simp [he''_f]) (by simp [hd'_f])
                    have hunres'_bd : unres' ≤ s.core.cur_vars + 1 := by
                      rw [hunres'_eq]
                      exact Nat.le_trans (Nat.succ_le_succ (flIdxs_length_le _ _ _)) (by omega)
                    c0_hsplit
                    · have h0 :=
                        congrArg BitVec.toNat (by assumption : BitVec.ofNat 64 unres' = 0#64)
                      rw [p2_bv64_ofNat_toNat (by omega),
                        show (0#64 : BitVec 64).toNat = 0 from rfl] at h0; omega
                    · c0_hsteps; rw [fl_bv64_sub1_eq (by omega) (by omega)]
                      exact ih_lp (unres' - 1, ucnt', done', t', unit', err'', s3) m3
                        (by dsimp only; rw [hdone_f, herr_f, hd'_f, he''_f]; simp; omega)
                        ⟨hok3, by dsimp only; omega, hucnt'_le, htmp3',
                          fun _ _ => ⟨by dsimp only; omega, hent3⟩, hm3⟩
              · intro Jrsn hJrsn
                have hunres_t'_s : unres = (flIdxs s1.core.mrk s.core.trl t').length + 1 := by
                  rw [flIdxs_succ_marked hmrk_t'_trl, List.length_cons] at hunres_t'
                  exact hunres_t'
                let rsn32 := s1.core.rsns[lit'.toNat / 2]'hlv_rsn_d
                have hrsn_val : rsn32 = s.core.rsns[lit'.toNat / 2]?.getD 0xFFFFFFFF#32 := by
                  dsimp only [rsn32]
                  rw [← heq_rsn, List.getElem?_eq_getElem hlv_rsn_d, Option.getD_some]
                c0_hsplit
                · have hbin : (rsn32 &&& 0x80000000#32) ≠ 0#32 := by dsimp only [rsn32]; assumption
                  rw [← hrsn_val, ite_eq_left hbin] at hri
                  obtain ⟨hot_lt, hent_bin, m_ot, hm_ot_lt, hm_ot_eq, _⟩ := hri
                  exact s13_fl_rsn_bin_wp hcut hcl1 hok1 (by omega) ht'_cut htrl_t' hmrk_t'_trl
                    hunres_t'_s hunres_bd hact_t' hucnt'_le htmp_ok' hrsn_val hbin
                    ⟨hot_lt, hent_bin, m_ot, hm_ot_lt, hm_ot_eq⟩ hm2
                    (fun u uc dn tt un er sf mf a b d e f g =>
                      hJexit (u, uc, dn, tt, un, er, sf) mf ⟨a, b, d, e, f, g⟩)
                    (fun u' dn' er' s3 m3 a b d e => hJrsn (u', dn', er', s3) m3 ⟨a, b, d, e⟩)
                · have hlg : (rsn32 &&& 0x80000000#32) = 0#32 := by
                    dsimp only [rsn32]
                    simpa only [show (2147483648 : BitVec 32) = 0x80000000#32 from rfl,
                      show (0 : BitVec 32) = 0#32 from rfl] using (by assumption : _)
                  rw [ite_eq_right (fun h => absurd (hrsn_val ▸ hlg) h)] at hri
                  obtain ⟨href, hng, hall⟩ := hri
                  exact s13_fl_rsn_large_wp hcut hcl1 hok1 (by omega) ht'_cut htrl_t' hmrk_t'_trl
                    hunres_t'_s hact_t' (congrArg BitVec.toNat hrsn_val) href hng
                    (fun l hl =>
                      (hall l hl).elim Or.inl fun ⟨m', hm', heq', _⟩ => Or.inr ⟨m', hm', heq'⟩)
                    hm2
                    (fun u' dn' er' s3 m3 a b d e => hJrsn (u', dn', er', s3) m3 ⟨a, b, d, e⟩)
            · intro Juc hJuc; c0_hsplit
              · have hu1 : unres = 1 := by
                  have h0 := congrArg BitVec.toNat (by assumption : BitVec.ofNat 64 unres = 1)
                  rw [show (1 : BitVec 64) = 1#64 from rfl] at h0
                  rwa [p2_bv64_ofNat_toNat (by omega)] at h0
                let unit1 := lit' ^^^ 1#32
                have hunit_ent : (cnfOfClauses F_cur).EntailsClause (cnfClause [unit1.toNat]) := by
                  have hsng := flLits_eq_singleton_of_len1 (by rw [htrl_t']; exact hmrk_t'_0)
                    (by rw [← hunres_t'_0, hu1])
                  rw [hsng, htrl_t'] at hact_t'_0; simpa only [unit1, fl_bv32_xor1] using hact_t'_0
                have hunit_lt : unit1.toNat < 2 * s.core.cur_vars := by
                  dsimp [unit1]
                  exact litNeg_lt_two_mul hlit'_lt
                c0_hsplit
                · have huc_lt : ucnt < s.core.cur_vars := by
                    have hlt : ucnt % 2 ^ 64 < s.core.cur_vars % 2 ^ 64 := by
                      simpa only [hok_lp.core] using (by assumption : _)
                    rwa [Nat.mod_eq_of_lt (by omega : ucnt < 2 ^ 64),
                      Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64)] at hlt
                  have huc_tmp : (BitVec.ofNat 64 ucnt).toNat < s_lp.core.tmp.length := by
                    rw [p2_bv64_ofNat_toNat (by omega), hok_lp.len.core_ok.tmp_len_arr]; omega
                  let s2 : FullState :=
                    { s_lp with core := { s_lp.core with tmp := s_lp.core.tmp.set ucnt unit1 } }
                  have hok2 :=
                    fl_failedStateOk_with_tmp hok_lp (tmp' := s_lp.core.tmp.set ucnt unit1)
                    (by rw [List.length_set, hok_lp.len.core_ok.tmp_len_arr])
                  have htmp2 : ∀ k < ucnt + 1,
                      (s2.core.tmp[k]?.getD 0#32).toNat < 2 * s.core.cur_vars ∧
                      (cnfOfClauses F_cur).EntailsClause
                        (cnfClause [(s2.core.tmp[k]?.getD 0#32).toNat]) := fun k hk => by
                    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk) with hlt | rfl
                    · dsimp [s2]; rw [List.getElem?_set_ne (by omega)]; exact htmp_ok k hlt
                    · dsimp [s2]
                      rw [List.getElem?_set_self (by rw [hok_lp.len.core_ok.tmp_len_arr]; omega),
                        Option.getD_some]; exact ⟨hunit_lt, hunit_ent⟩
                  rw [hm_eq]; c0_hsteps
                  have hm2' : (FullMem c s2 ⋆ R_hdr) m := by
                    simpa only [s2, unit1, show (1 : BitVec 32) = 1#32 from rfl,
                      p2_bv64_ofNat_toNat (by omega : ucnt < 2 ^ 64)] using hm
                  rw [fl_bv64_add1_eq (by omega)]
                  exact hJuc (ucnt + 1, unit1, err', s2) m
                    ⟨he_f, hok2, rfl, rfl, rfl, by omega, htmp2, hm2'⟩
                · c0_hsteps; rw [hm_eq, show (lit' ^^^ (1 : BitVec 32)) = unit1 from rfl]
                  exact hJexit (unres, ucnt, done, t', unit1, true, s_lp) m1
                    ⟨hok_lp, by dsimp only; omega, hucnt_le, htmp_ok, (fun h => by cases h), hm1⟩
              · c0_hsteps; rw [hm_eq]
                exact hJuc (ucnt, unit, err', s_lp) m1
                  ⟨he_f, hok_lp, rfl, rfl, rfl, hucnt_le, htmp_ok, hm1⟩
        · intro Jfind hJfind
          exact s13_fl_find_lit_wp hcut hok_lp ht_le herr_f hunres_len hact_ent hm1
            (fun t' err' lit' mf heq hf => hJfind (t', err', lit') mf ⟨heq, hf⟩)
  · intro Jseed hJseed; c0_hsplit
    · have hct1 : s.core.confl_type = 1#64 := by simpa [s0] using (by assumption : _)
      exact s13_fl_seed_bin_wp hcut hcl1 hconfl hct1 hok0 hm_s0
        (fun un1 dn1 sb1 m1 a b d e => hJseed (un1, dn1, sb1) m1 ⟨a, b, d, e⟩)
    · have hct_ne : s.core.confl_type ≠ 1#64 := by simpa [s0] using (by assumption : _)
      exact s13_fl_seed_large_wp hcut hcl1 hconfl hct_ne hok0 hm_s0
        (fun un1 dn1 sb1 m1 a b d e => hJseed (un1, dn1, sb1) m1 ⟨a, b, d, e⟩)

end LeanQbe.T.Examples.Kissat.Proof.Analyze.WpFailedLit
