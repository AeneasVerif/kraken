/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Vivify.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Vivify.Tactics
public import LeanQbe.T.Examples.Kissat.Proof.Vivify.InvArena
public import LeanQbe.T.Examples.Kissat.Proof.Vivify.Inv
public import LeanQbe.T.Examples.Kissat.Src.Vivify

/-!
# Vivify Deduce Phase-1B & Helper WPs (`Proof.Vivify.WpDeduce0`)

Pre-compiled WP building blocks for `full_viv_deduce_m6` (`0` legacy imports, `0` SAT model
proofs):
- `deduce_push_branch_wp`, `vivDeduceSubWitness_of_pres`
- `s13DeduceClearExpr` / `s13_deduce_clear_wp`
- `s13DeduceLargeRsnExpr` / `s13_deduce_large_rsn_wp`
- `s13DeducePhase1bBinExpr` / `s13_deduce_phase1b_bin_wp`
- `s13DeducePhase1bLargeExpr` / `s13_deduce_phase1b_large_wp`
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Vivify

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.ProofUtil LeanQbe.T.C0Step LeanQbe.T.C0HeadStep
open LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src.Vivify
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Vivify.Spec
open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.Proof.Vivify.VivTactics
open Kraken.Bedrock2.Test

public section

/-! ## 1. Pure Subsumption Witness & Push Helpers -/

theorem vivDeduceSubWitness_of_pres {F_cur : List (List Nat)} {s s' : FullState} {sz : Nat}
    (hcv : s'.core.cur_vars = s.core.cur_vars) (htmp : s'.core.tmp = s.core.tmp)
    (hvals : s'.core.vals = s.core.vals) (hrsns : s'.core.rsns = s.core.rsns)
    (hlvl : s'.core.lvl = s.core.lvl) :
    VivDeduceSubWitness F_cur s' sz → VivDeduceSubWitness F_cur s sz := by
  rintro ⟨sub, hent, hl⟩; refine ⟨sub, hent, fun l hmem => ?_⟩
  have h := hl l hmem; rwa [hcv, htmp, hvals, hrsns, hlvl] at h

private theorem cl_subWitness {c : FullCfg} {F_cur : List (List Nat)} {s : FullState}
    {lm1 : List (BitVec 8)} {sz : Nat} {sub : List Nat}
    (hcv_le : s.core.cur_vars ≤ c.max_vars)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause sub))
    (hsub_lm : ∀ l ∈ sub, l < 2 * s.core.cur_vars ∧
      (lm1[l]?.getD 0#8 ≠ 0#8 ∨
        (s.core.vals[l]?.getD 0#8 = 0xFF#8 ∧ (s.core.lvl[l / 2]?.getD 0#32).toNat = 0)))
    (hfalse_or_rsn : ∀ l ∈ sub,
      s.core.vals[l]?.getD 0#8 ≠ 1#8 ∨ s.core.rsns[l / 2]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32)
    (hlm1_dom : ∀ l < 2 * c.max_vars, lm1[l]?.getD 0#8 ≠ 0#8 →
      ∃ k < sz, (s.core.tmp[k]?.getD 0#32).toNat = l) :
    VivDeduceSubWitness F_cur s sz := by
  refine ⟨sub, hent, fun l hl => ?_⟩
  obtain ⟨hl_lt, hcase⟩ := hsub_lm l hl
  exact ⟨hl_lt, hcase.elim
    (fun hmk => Or.inl ⟨hlm1_dom l (by omega) hmk, hfalse_or_rsn l hl⟩) Or.inr⟩

theorem deduce_push_branch_wp (Γ : Env) {c : FullCfg} {s : FullState}
    {mrk_c lm1 : List (BitVec 8)} {ws1_c ws2_c : List (BitVec 32)}
    {asz_c rsz_c : BitVec 64} {qlen : Val i64} {ov : Val i32} {R : Mem 64 → Prop}
    {m : Mem 64} {Q : Post [i32]} {X : XPost} {J : Cont [i64]}
    (hlen : s.LengthsOk c) (hq : VivQueueOk c s mrk_c ws1_c qlen.toNat)
    (hov_lt : ov.toNat < s.core.cur_vars)
    (hov_trl : ∃ idx < s.core.trail_end, (s.core.trl[idx]?.getD 0#32).toNat / 2 = ov.toNat)
    (hm : (FullMem c { s with
      core := { s.core with mrk := mrk_c, lit_mark := lm1 }
      scratch := { s.scratch with
        work_stk1 := ws1_c, work_stk2 := ws2_c, ant_sz := asz_c, res_sz := rsz_c } } ⋆ R) m)
    (hJ : ∀ (qlen' : Val i64) (mrk_n : List (BitVec 8)) (ws1_n : List (BitVec 32)) mn,
      qlen.toNat ≤ qlen'.toNat → qlen'.toNat ≤ s.core.cur_vars →
      (∀ j < qlen.toNat, ws1_n[j]? = ws1_c[j]?) →
      VivQueueOk c s mrk_n ws1_n qlen'.toNat →
      ((s.core.lvl[ov.toNat]?.getD 0#32).toNat = 0 ∨
        ov.toNat ∈ (ws1_n.take qlen'.toNat).map BitVec.toNat) →
      (FullMem c { s with
        core := { s.core with mrk := mrk_n, lit_mark := lm1 }
        scratch := { s.scratch with
          work_stk1 := ws1_n, work_stk2 := ws2_c, ant_sz := asz_c, res_sz := rsz_c } } ⋆ R) mn →
      J (qlen', ()) mn) :
    wp Γ Q X (deducePushExpr (BitVec.ofNat 64 s.core.cur_vars)
      c.pMark c.pLevel c.pWorkStk1 ov qlen J) m := by
  have hcl := hlen.core_ok; have hcv_le := hcl.cur_vars_le
  have hcap := c.harena; have hmx := c.hmaxv; unfold dimacsBound at hcap hmx
  have hov_lvl : ov.toNat < s.core.lvl.length := by rw [hcl.lvl_len]; omega
  have hov_mrk : ov.toNat < mrk_c.length := by rw [hq.1]; omega
  have hql_le := hq.2.2.1; have hcv_64 : s.core.cur_vars < 2 ^ 64 := by omega
  have hov_mod : (ov.setWidth 64).toNat = ov.toNat := by bv_omega
  have hov_lvl64 : (ov.setWidth 64).toNat < s.core.lvl.length := by rw [hov_mod]; exact hov_lvl
  have hov_mrk64 : (ov.setWidth 64).toNat < mrk_c.length := by rw [hov_mod]; exact hov_mrk
  dsimp only [deducePushExpr, fvOp]
  viv_hsteps_nogrp
  · have hlvl_pos : 0 < (s.core.lvl[ov.toNat]'hov_lvl).toNat := by c0_bound
    have hm0 : mrk_c[ov.toNat]'hov_mrk = 0#8 := by
      have hm032 : (mrk_c[ov.toNat]'hov_mrk).setWidth 32 = 0#32 := by assumption
      exact (bv8_zext32_eq0_iff _).mp hm032
    have hlvl_pos' : 0 < (s.core.lvl[ov.toNat]?.getD 0#32).toNat := by
      rwa [List.getElem?_eq_getElem hov_lvl, Option.getD_some]
    have hm0' : mrk_c[ov.toNat]?.getD 0#8 = 0#8 := by
      rwa [List.getElem?_eq_getElem hov_mrk, Option.getD_some]
    have hql_lt := push_queue_lt hq hcv_le hov_lt hm0'
    have hql_ws1 : qlen.toNat < ws1_c.length := by have := hq.2.1; omega
    have hql1 : (qlen + 1#64).toNat = qlen.toNat + 1 := by bv_omega
    obtain ⟨_, hq_next, hpre_next, _⟩ :=
      push_queue_step hq hcv_le hov_lt hlvl_pos' hm0' hov_trl
    viv_hsteps_nogrp
    have hov_mod2 : ov.toNat % 2 ^ 64 = ov.toNat := Nat.mod_eq_of_lt (by omega)
    refine hJ (qlen + 1#64) _ _ _ (by omega) (by omega) hpre_next ?_ (Or.inr ?_) (by assumption)
    · simpa [hql1, hov_mod2] using hq_next
    · rw [hql1]
      exact (mem_map_take_iff (by simp [hq.2.1]; omega)).mpr
        ⟨qlen.toNat, by omega, by rw [List.getElem?_set_self hql_ws1]; rfl⟩
  · have hm0 : mrk_c[ov.toNat]'hov_mrk = 0#8 := by
      have hm032 : (mrk_c[ov.toNat]'hov_mrk).setWidth 32 = 0#32 := by assumption
      exact (bv8_zext32_eq0_iff _).mp hm032
    have hm0' : mrk_c[ov.toNat]?.getD 0#8 = 0#8 := by
      rwa [List.getElem?_eq_getElem hov_mrk, Option.getD_some]
    have hql_lt := push_queue_lt hq hcv_le hov_lt hm0'
    have hcv_le_q : s.core.cur_vars % 2 ^ 64 ≤ qlen.toNat := by c0_bound
    rw [Nat.mod_eq_of_lt hcv_64] at hcv_le_q; omega
  · have hm_ne0 : mrk_c[ov.toNat]'hov_mrk ≠ 0#8 := fun h => by
      have hne32 : (mrk_c[ov.toNat]'hov_mrk).setWidth 32 ≠ 0#32 := by assumption
      exact hne32 ((bv8_zext32_eq0_iff _).mpr h)
    have hm1 : mrk_c[ov.toNat]?.getD 0#8 = 1#8 := by
      rcases hq.2.2.2.2.2.2.2.1 ov.toNat hov_lt with h0 | h1
      · rw [List.getElem?_eq_getElem hov_mrk, Option.getD_some] at h0; exact absurd h0 hm_ne0
      · exact h1
    exact hJ qlen mrk_c ws1_c m (Nat.le_refl _) hql_le (fun _ _ => rfl) hq
      (Or.inr ((hq.2.2.2.2.2.2.1 ov.toNat hov_lt).mp hm1)) hm
  · have hlvl0 : (s.core.lvl[ov.toNat]'hov_lvl).toNat = 0 := by c0_bound
    exact hJ qlen mrk_c ws1_c m (Nat.le_refl _) hql_le (fun _ _ => rfl) hq
      (Or.inl (by rwa [List.getElem?_eq_getElem hov_lvl, Option.getD_some])) hm

/-! ## 2. `s13_deduce_clear_wp` -/

abbrev s13DeduceClearExpr (h pMark pLitMark pTmp pWs1 : Val i64)
    (sz : Val i32) (qlen : Val i64) (olen : Val i32) (taut : Val .bool) : Expr Val Cont [i32] :=
  Expr.group (sig := [[i64]]) (fun Js => Blocks.cons (fun p19 =>
    fvOp (OpCode.cmp .ult i64 .bool (by decide)) (Arg.var p19.fst, Arg.var qlen, ()) fun p =>
    Expr.jnz (Arg.var p.fst)
      (fvOp (OpCode.mul i64) (Arg.var p19.fst, Arg.imm 4, ()) fun p =>
       fvOp (OpCode.add i64) (Arg.var pWs1, Arg.var p.fst, ()) fun p =>
       Expr.load i32 (Arg.var p.fst) fun ld =>
       fvOp (OpCode.zext 32 64) (Arg.var ld, ()) fun p =>
       fvOp (OpCode.add i64) (Arg.var pMark, Arg.var p.fst, ()) fun p =>
       fvOp (OpCode.trunc 32 8) (Arg.imm 0, ()) fun p0 =>
       Expr.store (Arg.var p0.fst) (Arg.var p.fst)
         (fvOp (OpCode.add i64) (Arg.var p19.fst, Arg.imm 1, ()) fun p =>
          Expr.jump Js.fst (Arg.var p.fst, ())))
      (Expr.group (sig := [[i32]]) (fun Js2 => Blocks.cons (fun p21 =>
        fvOp (OpCode.cmp .ult i32 .bool (by decide)) (Arg.var p21.fst, Arg.var sz, ()) fun p =>
        Expr.jnz (Arg.var p.fst)
          (fvOp (OpCode.zext 32 64) (Arg.var p21.fst, ()) fun p =>
           fvOp (OpCode.mul i64) (Arg.var p.fst, Arg.imm 4, ()) fun p =>
           fvOp (OpCode.add i64) (Arg.var pTmp, Arg.var p.fst, ()) fun p =>
           Expr.load i32 (Arg.var p.fst) fun ld =>
           fvOp (OpCode.zext 32 64) (Arg.var ld, ()) fun p =>
           fvOp (OpCode.add i64) (Arg.var pLitMark, Arg.var p.fst, ()) fun p =>
           fvOp (OpCode.trunc 32 8) (Arg.imm 0, ()) fun p0 =>
           Expr.store (Arg.var p0.fst) (Arg.var p.fst)
             (fvOp (OpCode.add i32) (Arg.var p21.fst, Arg.imm 1, ()) fun p =>
              Expr.jump Js2.fst (Arg.var p.fst, ())))
          (Expr.jnz (Arg.var taut)
            (fvOp (OpCode.add i64) (Arg.var h, Arg.imm 1136, ()) fun p =>
             Expr.store (Arg.imm (t := i64) 18446744073709551615) (Arg.var p.fst)
               (Expr.ret (Arg.imm 4294967295, ())))
            (Expr.ret (Arg.var olen, ())))) Blocks.nil)
        fun Js2 => Expr.jump Js2.fst (Arg.imm 0, ()))) Blocks.nil)
    fun Js => Expr.jump Js.fst (Arg.imm 0, ())

theorem s13_deduce_clear_wp (Γ : Env) {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} {R : Mem 64 → Prop}
    {mrk_b lm1 : List (BitVec 8)} {ws1_b ws2_b : List (BitVec 32)} {asz_b rsz_b : BitVec 64}
    {sz : Val i32} {qlen_c : Val i64} {olen_c : Val i32} {taut_c : Val .bool}
    {m : Mem 64} {Q : Post [i32]} {X : XPost}
    (hspW : FullSparseInvW c F0 F_cur s)
    (hsz_le : sz.toNat ≤ c.max_vars)
    (htmp_lt : ∀ k < sz.toNat, (s.core.tmp[k]?.getD 0#32).toNat < 2 * s.core.cur_vars)
    (hqb : VivQueueOk c s mrk_b ws1_b qlen_c.toNat)
    (hlm1_len : lm1.length = 2 * c.max_vars)
    (hlm1_dom : ∀ l < 2 * c.max_vars, lm1[l]?.getD 0#8 ≠ 0#8 →
      ∃ t < sz.toNat, (s.core.tmp[t]?.getD 0#32).toNat = l)
    (hws2_b : ws2_b.length = 2 * c.max_vars)
    (hsub_b : S13SubRefOk s asz_b)
    (hsub_w : asz_b ≠ 0xFFFFFFFFFFFFFFFF#64 → VivDeduceSubWitness F_cur s sz.toNat)
    (hm : (FullMem c { s with
      core := { s.core with mrk := mrk_b, lit_mark := lm1 }
      scratch := { s.scratch with
        work_stk1 := ws1_b, work_stk2 := ws2_b, ant_sz := asz_b, res_sz := rsz_b } } ⋆ R) m)
    (hQ : ∀ (ret : Val i32) mrk' lm' asz' mf,
      let s' : FullState := { s with
        core := { s.core with mrk := mrk', lit_mark := lm' }
        scratch := { s.scratch with
          work_stk1 := ws1_b, work_stk2 := ws2_b, ant_sz := asz', res_sz := rsz_b } }
      FullSparseInvW c F0 F_cur s' → S13SubRefOk s asz' →
      (asz' ≠ 0xFFFFFFFFFFFFFFFF#64 → VivDeduceSubWitness F_cur s sz.toNat) →
      (taut_c = true → ret = 0xFFFFFFFF#32) → (taut_c = false → ret = olen_c) →
      (FullMem c s' ⋆ R) mf → Q (ret, ()) mf) :
    wp Γ Q X (s13DeduceClearExpr c.hdr c.pMark c.pLitMark c.pTmp c.pWorkStk1
      sz qlen_c olen_c taut_c) m := by
  have hcl := hspW.1.core_ok; have hcv_le := hcl.cur_vars_le
  have hcap := c.harena; have hmx := c.hmaxv; unfold dimacsBound at hcap hmx
  have hnoM : S13SparseInvNoMark c F0 F_cur s :=
    ⟨hspW.1, hspW.2.1, hspW.2.2.2.1, hspW.2.2.2.2.1, hspW.2.2.2.2.2⟩
  dsimp only [s13DeduceClearExpr, fvOp]
  refine wp_loop_inv (ts := [i64])
    (fun (qi2, ()) mc => ∃ mrk_c : List (BitVec 8),
      qi2.toNat ≤ qlen_c.toNat ∧ mrk_c.length = c.max_vars ∧
      (∀ v < c.max_vars, mrk_c[v]?.getD 0#8 = 0#8 ∨
        ∃ k, qi2.toNat ≤ k ∧ k < qlen_c.toNat ∧ (ws1_b[k]?.getD 0#32).toNat = v) ∧
      (FullMem c { s with
        core := { s.core with mrk := mrk_c, lit_mark := lm1 }
        scratch := { s.scratch with
          work_stk1 := ws1_b, work_stk2 := ws2_b, ant_sz := asz_b, res_sz := rsz_b } } ⋆ R) mc)
    (fun (qi2, ()) _ => qlen_c.toNat - qi2.toNat)
    (fun Jc hJc => by
      viv_hsteps_nogrp
      exact hJc (0#64, ()) m ⟨mrk_b, by simp, hqb.1, viv_clear_mrk_init hqb hcv_le, hm⟩)
    (fun Jc (qi2, ()) mc ⟨mrk_c, hq2_le, hmrkc_len, hinv_c, hmc⟩ ihc => ?_)
  viv_hsteps_nogrp
  · have hqi2_lt : qi2.toNat < qlen_c.toNat := by c0_bound
    have hqi2_ws1 : qi2.toNat < ws1_b.length := by have := hqb.2.1; have := hqb.2.2.1; omega
    have hqi2_1 : (qi2 + 1#64).toNat = qi2.toNat + 1 := by bv_omega
    obtain ⟨hv_mrk, hinv_next⟩ := viv_clear_mrk_step hmrkc_len hqb.2.2.2.1 hcv_le hqi2_lt hinv_c
    have hidx_mrk : (ws1_b[qi2.toNat]'hqi2_ws1).toNat < mrk_c.length := by
      rwa [List.getElem?_eq_getElem hqi2_ws1, Option.getD_some] at hv_mrk
    have hidx_mrk64 : ((ws1_b[qi2.toNat]'hqi2_ws1).setWidth 64).toNat < mrk_c.length := by
      rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans (ws1_b[qi2.toNat]'hqi2_ws1).isLt
        (by decide))]; exact hidx_mrk
    have hidx_mod : (ws1_b[qi2.toNat]'hqi2_ws1).toNat % 2 ^ 64 =
        (ws1_b[qi2.toNat]'hqi2_ws1).toNat :=
      Nat.mod_eq_of_lt (Nat.lt_trans (ws1_b[qi2.toNat]'hqi2_ws1).isLt (by decide))
    viv_hsteps_nogrp; simp only [hidx_mod] at *
    exact ihc (qi2 + 1#64, ()) _ (by dsimp only; omega)
      ⟨mrk_c.set (ws1_b[qi2.toNat]'hqi2_ws1).toNat 0#8, by dsimp only; omega, by simp [hmrkc_len],
       fun u hu => by
         have h := hinv_next u hu
         rwa [List.getElem?_eq_getElem hqi2_ws1, Option.getD_some, ← hqi2_1] at h, by assumption⟩
  · have hqi2_eq : qi2.toNat = qlen_c.toNat := by c0_bound
    have hmrkc_clr : ∀ v < c.max_vars, mrk_c[v]?.getD 0#8 = 0#8 := fun v hv => by
      rcases hinv_c v hv with h0 | ⟨k, hk1, hk2, _⟩
      · exact h0
      · omega
    clear ihc Jc
    refine wp_loop_inv (ts := [i32])
      (fun (mi2, ()) mlm =>
        mi2.toNat ≤ sz.toNat ∧ ∃ lm2 : List (BitVec 8), lm2.length = 2 * c.max_vars ∧
          (∀ l < 2 * c.max_vars, lm2[l]?.getD 0#8 ≠ 0#8 →
            ∃ t, mi2.toNat ≤ t ∧ t < sz.toNat ∧ (s.core.tmp[t]?.getD 0#32).toNat = l) ∧
          (FullMem c { s with
            core := { s.core with mrk := mrk_c, lit_mark := lm2 }
            scratch := { s.scratch with
              work_stk1 := ws1_b, work_stk2 := ws2_b, ant_sz := asz_b, res_sz := rsz_b } }
            ⋆ R) mlm)
      (fun (mi2, ()) _ => sz.toNat - mi2.toNat)
      (fun Jl hJl => by
        viv_hsteps_nogrp
        exact hJl (0#32, ()) mc ⟨Nat.zero_le _, lm1, hlm1_len, fun l hl hnz => by
          obtain ⟨t, ht, hteq⟩ := hlm1_dom l hl hnz
          exact ⟨t, Nat.zero_le _, by omega, hteq⟩, hmc⟩)
      (fun Jl (mi2, ()) mlm ⟨hmi2_le, lm2, hlm2_len, hlm2_dom, hmlm⟩ ihl => ?_)
    rw [Blocks.get_here]; dsimp only; viv_step; rw [wp_jnz]; constructor <;> intro hc
    · have hmi2_lt : mi2.toNat < sz.toNat := by
        simp only [Arg.val_var, BitVec.ult] at hc; exact of_decide_eq_true hc
      have hmi2_1 : (mi2 + 1#32).toNat = mi2.toNat + 1 := by bv_omega
      have hmi2_tmp : (mi2.setWidth 64).toNat < s.core.tmp.length := by
        rw [hcl.tmp_len_arr, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]; omega
      have hmi2_mod : (mi2.setWidth 64).toNat = mi2.toNat := by bv_omega
      let lt2 := s.core.tmp[(mi2.setWidth 64).toNat]'hmi2_tmp
      have hlt2_lm : (lt2.setWidth 64).toNat < lm2.length := by
        have := htmp_lt mi2.toNat hmi2_lt
        rw [List.getElem?_eq_getElem (by rw [hcl.tmp_len_arr]; omega),
          Option.getD_some] at this
        have hlt2_eq : lt2.toNat =
            (s.core.tmp[mi2.toNat]'(by rw [hcl.tmp_len_arr]; omega)).toNat := by
          dsimp only [lt2]; simp only [hmi2_mod]
        rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega), hlt2_eq]; omega
      have hlt2_lm' : lt2.toNat < lm2.length := by
        rwa [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)] at hlt2_lm
      viv_hsteps_nogrp
      let lm2' := lm2.set lt2.toNat 0#8
      have hlt2_mod : (lt2.setWidth 64).toNat = lt2.toNat := by bv_omega
      have hlm2'_eq : lm2.set (lt2.setWidth 64).toNat 0#8 = lm2' := by rw [hlt2_mod]
      refine ihl (mi2 + 1#32, ()) _ (by dsimp only; omega)
        ⟨by omega, lm2', by simp [lm2', hlm2_len], fun q hq hnz => ?_, by
          simpa only [hlm2'_eq] using by assumption⟩
      by_cases hql : q = lt2.toNat
      · subst hql; dsimp only [lm2'] at hnz
        rw [List.getElem?_set_self hlt2_lm', Option.getD_some] at hnz; exact absurd rfl hnz
      · dsimp only [lm2'] at hnz; rw [List.getElem?_set_ne (Ne.symm hql)] at hnz
        obtain ⟨t, ht1, ht2, hteq⟩ := hlm2_dom q hq hnz
        have hne_t : t ≠ mi2.toNat := fun he => by
          subst he
          have hlt2_eq : lt2 = s.core.tmp[mi2.toNat]'(by rw [hcl.tmp_len_arr]; omega) := by
            dsimp only [lt2]; simp only [hmi2_mod]
          rw [List.getElem?_eq_getElem (by rw [hcl.tmp_len_arr]; omega), Option.getD_some] at hteq
          exact hql (hteq.symm.trans (congrArg BitVec.toNat hlt2_eq.symm))
        exact ⟨t, by omega, ht2, hteq⟩
    · have hmi2_eq : mi2.toNat = sz.toNat := by
        simp only [Arg.val_var, BitVec.ult] at hc; have := of_decide_eq_false hc; omega
      have hlm2_clr : ∀ l < 2 * c.max_vars, lm2[l]?.getD 0#8 = 0#8 := fun l hl =>
        Classical.byContradiction fun hnz => by
          obtain ⟨t, ht1, ht2, _⟩ := hlm2_dom l hl hnz; omega
      viv_hsteps_nogrp
      · exact hQ 0xFFFFFFFF#32 mrk_c lm2 0xFFFFFFFFFFFFFFFF#64 _
          (s13_deduce_finish_sparse hnoM hmrkc_len hlm2_len hqb.2.1 hws2_b hmrkc_clr hlm2_clr)
          ⟨Or.inl rfl, fun h => absurd rfl h⟩ (fun h => absurd rfl h)
          (fun _ => rfl) (fun h => by cases h.symm.trans hc) (by assumption)
      · exact hQ olen_c mrk_c lm2 asz_b mlm
          (s13_deduce_finish_sparse hnoM hmrkc_len hlm2_len hqb.2.1 hws2_b hmrkc_clr hlm2_clr)
          hsub_b hsub_w (fun h => by cases h.symm.trans hc) (fun _ => rfl) hmlm

/-! ## 3. `s13_deduce_large_rsn_wp` -/

abbrev s13DeduceLargeRsnExpr (h pVars pMark pLevel pArena pWs1 : Val i64)
    (cref sz rsn_bv v_bv : Val i32) (qlen qi1 : Val i64) (olen : Val i32) (taut : Val .bool)
    (Jexit : Cont [i64, i64, i32, .bool]) (Jnext : Cont [i64]) : Expr Val Cont [i32] :=
  Expr.group (sig := [[i64]]) (fun _ => Blocks.cons (fun p =>
    Expr.jump Jnext (Arg.var p.fst, ())) Blocks.nil) fun J53 =>
  fvOp (OpCode.zext 32 64) (Arg.var rsn_bv, ()) fun p =>
  fvOp (OpCode.add i64) (Arg.var p.fst, Arg.imm 3, ()) fun p3 =>
  fvOp (OpCode.add i64) (Arg.var h, Arg.imm 48, ()) fun p48 =>
  Expr.load i64 (Arg.var p48.fst) fun ld_len =>
  fvOp (OpCode.cmp .ule i64 .bool (by decide)) (Arg.var p3.fst, Arg.var ld_len, ()) fun pb =>
  Expr.jnz (Arg.var pb.fst)
    (Expr.group (sig := [[]]) (fun _ => Blocks.cons (fun (_ : Tup Val []) =>
      Expr.group (sig := [[]]) (fun _ => Blocks.cons (fun (_ : Tup Val []) =>
        fvOp (OpCode.zext 32 64) (Arg.var rsn_bv, ()) fun p =>
        fvOp (OpCode.add i64) (Arg.var p.fst, Arg.imm 2, ()) fun p =>
        fvOp (OpCode.mul i64) (Arg.var p.fst, Arg.imm 4, ()) fun p =>
        fvOp (OpCode.add i64) (Arg.var pArena, Arg.var p.fst, ()) fun p =>
        Expr.load i32 (Arg.var p.fst) fun ld_rsz =>
        Expr.group (sig := [[i64, i32]]) (fun J66 => Blocks.cons (fun p_38 =>
          fvOp (OpCode.cmp .ult i32 .bool (by decide))
            (Arg.var p_38.snd.fst, Arg.var ld_rsz, ()) fun p =>
          Expr.jnz (Arg.var p.fst)
            (fvOp (OpCode.zext 32 64) (Arg.var rsn_bv, ()) fun p =>
             fvOp (OpCode.add i64) (Arg.var p.fst, Arg.imm 3, ()) fun p =>
             fvOp (OpCode.zext 32 64) (Arg.var ld_rsz, ()) fun pz =>
             fvOp (OpCode.add i64) (Arg.var p.fst, Arg.var pz.fst, ()) fun p =>
             fvOp (OpCode.add i64) (Arg.var h, Arg.imm 48, ()) fun p48 =>
             Expr.load i64 (Arg.var p48.fst) fun ld_15 =>
             fvOp (OpCode.cmp .ule i64 .bool (by decide))
               (Arg.var p.fst, Arg.var ld_15, ()) fun p =>
             Expr.jnz (Arg.var p.fst)
               (fvOp (OpCode.zext 32 64) (Arg.var rsn_bv, ()) fun p =>
                fvOp (OpCode.add i64) (Arg.var p.fst, Arg.imm 3, ()) fun p =>
                fvOp (OpCode.zext 32 64) (Arg.var p_38.snd.fst, ()) fun pz =>
                fvOp (OpCode.add i64) (Arg.var p.fst, Arg.var pz.fst, ()) fun p =>
                fvOp (OpCode.mul i64) (Arg.var p.fst, Arg.imm 4, ()) fun p =>
                fvOp (OpCode.add i64) (Arg.var pArena, Arg.var p.fst, ()) fun p =>
                Expr.load i32 (Arg.var p.fst) fun ld =>
                fvOp (OpCode.lshr i32) (Arg.var ld, Arg.imm 1, ()) fun p_ov =>
                Expr.group (sig := [[i64]]) (fun _ => Blocks.cons (fun p =>
                  fvOp (OpCode.add i32) (Arg.var p_38.snd.fst, Arg.imm 1, ()) fun pj =>
                  Expr.jump J66.fst (Arg.var p.fst, Arg.var pj.fst, ())) Blocks.nil) fun J85 =>
                fvOp (OpCode.cmp .ne i32 .bool (by decide))
                  (Arg.var p_ov.fst, Arg.var v_bv, ()) fun p =>
                Expr.jnz (Arg.var p.fst)
                  (deducePushExpr pVars pMark pLevel pWs1 p_ov.fst p_38.fst J85.fst)
                  (Expr.jump J85.fst (Arg.var p_38.fst, ())))
               (Expr.jump J53.fst (Arg.var p_38.fst, ())))
            (Expr.jump J53.fst (Arg.var p_38.fst, ()))) Blocks.nil)
          fun J66 => Expr.jump J66.fst (Arg.var qlen, Arg.imm 0, ())) Blocks.nil)
        fun J60 =>
        fvOp (OpCode.cmp .ne i32 .bool (by decide)) (Arg.var rsn_bv, Arg.var cref, ()) fun p =>
        Expr.jnz (Arg.var p.fst)
          (Expr.call "full_viv_subsumes_cl_m6" (as := [i64, i32, i32]) (bs := [.bool])
             (Arg.var h, Arg.var rsn_bv, Arg.var sz, ()) fun ok =>
           Expr.jnz (Arg.var ok.fst)
             (fvOp (OpCode.zext 32 64) (Arg.var rsn_bv, ()) fun pr =>
              fvOp (OpCode.add i64) (Arg.var h, Arg.imm 1136, ()) fun p =>
              Expr.store (Arg.var pr.fst) (Arg.var p.fst)
                (Expr.jump Jexit (Arg.var qlen, Arg.var qi1, Arg.var olen, Arg.var taut, ())))
             (Expr.jump J60.fst ()))
          (Expr.jump J60.fst ())) Blocks.nil)
      fun J59 =>
      fvOp (OpCode.zext 32 64) (Arg.var rsn_bv, ()) fun p =>
      fvOp (OpCode.mul i64) (Arg.var p.fst, Arg.imm 4, ()) fun p =>
      fvOp (OpCode.add i64) (Arg.var pArena, Arg.var p.fst, ()) fun p =>
      Expr.load i32 (Arg.var p.fst) fun ld =>
      fvOp (OpCode.and i32) (Arg.var ld, Arg.imm 4194304, ()) fun p =>
      fvOp (OpCode.cmp .ne i32 .bool (by decide)) (Arg.var p.fst, Arg.imm 0, ()) fun p =>
      Expr.jnz (Arg.var p.fst)
        (fvOp (OpCode.add i64) (Arg.var h, Arg.imm 1144, ()) fun p =>
         Expr.store (Arg.imm (t := i64) 1) (Arg.var p.fst)
           (Expr.call "full_viv_recompute_promote_fid" (as := [i64, i32]) (bs := [])
              (Arg.var h, Arg.var rsn_bv, ()) fun _ => Expr.jump J59.fst ()))
        (Expr.jump J59.fst ()))
    (Expr.jump J53.fst (Arg.var qlen, ()))

private theorem s13_large_rsn_loop_wp (Γ : Env) {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {sp : FullState} {R : Mem 64 → Prop}
    {mrk_b lm1 : List (BitVec 8)} {ws1_b ws2_b : List (BitVec 32)} {asz_b rsz_p : BitVec 64}
    {qlen_c : Val i64} {rsn_bv v_bv : Val i32} {idx0 : Nat} {mp : Mem 64}
    {Q : Post [i32]} {X : XPost} {Jnext : Cont [i64]}
    (hspN : S13SparseInvNoMark c F0 F_cur sp)
    (hqb : VivQueueOk c sp mrk_b ws1_b qlen_c.toNat)
    (_hlm1_len : lm1.length = 2 * c.max_vars) (_hws2_b : ws2_b.length = 2 * c.max_vars)
    (href_r : rsn_bv.toNat ∈ fullArenaClauseRefs sp)
    (hng_r : fullArenaClauseGarb sp rsn_bv.toNat = false)
    (hidx0 : idx0 < sp.core.trail_end)
    (htrl0 : (sp.core.trl[idx0]?.getD 0#32).toNat / 2 = v_bv.toNat)
    (hlits_r : ∀ q ∈ fullArenaClauseLitsCore sp.core rsn_bv.toNat,
      q = (sp.core.trl[idx0]?.getD 0#32).toNat ∨
      ∃ m < idx0, (sp.core.trl[m]?.getD 0#32).toNat = q ^^^ 1 ∧
        (sp.core.lvl[q / 2]?.getD 0#32).toNat ≤
          (sp.core.lvl[(sp.core.trl[idx0]?.getD 0#32).toNat / 2]?.getD 0#32).toNat)
    (hmp : (FullMem c { sp with
      core := { sp.core with mrk := mrk_b, lit_mark := lm1 }
      scratch := { sp.scratch with
        work_stk1 := ws1_b, work_stk2 := ws2_b, ant_sz := asz_b, res_sz := rsz_p } } ⋆ R) mp)
    (hJnext : ∀ (qlen' : Val i64) mrk_n ws1_n mlg,
      qlen_c.toNat ≤ qlen'.toNat → qlen'.toNat ≤ sp.core.cur_vars →
      (∀ j < qlen_c.toNat, ws1_n[j]? = ws1_b[j]?) →
      VivQueueOk c sp mrk_n ws1_n qlen'.toNat →
      (∀ q ∈ fullArenaClauseLitsCore sp.core rsn_bv.toNat, q / 2 ≠ v_bv.toNat →
        (sp.core.lvl[q / 2]?.getD 0#32).toNat = 0 ∨
        q / 2 ∈ (ws1_n.take qlen'.toNat).map BitVec.toNat) →
      (FullMem c { sp with
        core := { sp.core with mrk := mrk_n, lit_mark := lm1 }
        scratch := { sp.scratch with
          work_stk1 := ws1_n, work_stk2 := ws2_b, ant_sz := asz_b, res_sz := rsz_p } } ⋆ R) mlg →
      Jnext (qlen', ()) mlg) :
    let h := c.hdr
    let pArena := c.pArena
    wp Γ Q X
      (fvOp (OpCode.zext 32 64) (Arg.var rsn_bv, ()) fun p =>
       fvOp (OpCode.add i64) (Arg.var p.fst, Arg.imm 2, ()) fun p =>
       fvOp (OpCode.mul i64) (Arg.var p.fst, Arg.imm 4, ()) fun p =>
       fvOp (OpCode.add i64) (Arg.var pArena, Arg.var p.fst, ()) fun p =>
       Expr.load i32 (Arg.var p.fst) fun ld_rsz =>
       Expr.group (sig := [[i64, i32]]) (fun J66 => Blocks.cons (fun p_38 =>
         fvOp (OpCode.cmp .ult i32 .bool (by decide))
           (Arg.var p_38.snd.fst, Arg.var ld_rsz, ()) fun p =>
         Expr.jnz (Arg.var p.fst)
           (fvOp (OpCode.zext 32 64) (Arg.var rsn_bv, ()) fun p =>
            fvOp (OpCode.add i64) (Arg.var p.fst, Arg.imm 3, ()) fun p =>
            fvOp (OpCode.zext 32 64) (Arg.var ld_rsz, ()) fun pz =>
            fvOp (OpCode.add i64) (Arg.var p.fst, Arg.var pz.fst, ()) fun p =>
            fvOp (OpCode.add i64) (Arg.var h, Arg.imm 48, ()) fun p48 =>
            Expr.load i64 (Arg.var p48.fst) fun ld_15 =>
            fvOp (OpCode.cmp .ule i64 .bool (by decide))
              (Arg.var p.fst, Arg.var ld_15, ()) fun p =>
            Expr.jnz (Arg.var p.fst)
              (fvOp (OpCode.zext 32 64) (Arg.var rsn_bv, ()) fun p =>
               fvOp (OpCode.add i64) (Arg.var p.fst, Arg.imm 3, ()) fun p =>
               fvOp (OpCode.zext 32 64) (Arg.var p_38.snd.fst, ()) fun pz =>
               fvOp (OpCode.add i64) (Arg.var p.fst, Arg.var pz.fst, ()) fun p =>
               fvOp (OpCode.mul i64) (Arg.var p.fst, Arg.imm 4, ()) fun p =>
               fvOp (OpCode.add i64) (Arg.var pArena, Arg.var p.fst, ()) fun p =>
               Expr.load i32 (Arg.var p.fst) fun ld =>
               fvOp (OpCode.lshr i32) (Arg.var ld, Arg.imm 1, ()) fun p_ov =>
               Expr.group (sig := [[i64]]) (fun _ => Blocks.cons (fun p =>
                 fvOp (OpCode.add i32) (Arg.var p_38.snd.fst, Arg.imm 1, ()) fun pj =>
                 Expr.jump J66.fst (Arg.var p.fst, Arg.var pj.fst, ())) Blocks.nil) fun J85 =>
               fvOp (OpCode.cmp .ne i32 .bool (by decide))
                 (Arg.var p_ov.fst, Arg.var v_bv, ()) fun p =>
               Expr.jnz (Arg.var p.fst)
                 (deducePushExpr (BitVec.ofNat 64 sp.core.cur_vars)
                   c.pMark c.pLevel c.pWorkStk1 p_ov.fst p_38.fst J85.fst)
                 (Expr.jump J85.fst (Arg.var p_38.fst, ())))
              (Expr.jump Jnext (Arg.var p_38.fst, ())))
           (Expr.jump Jnext (Arg.var p_38.fst, ()))) Blocks.nil)
         fun J66 => Expr.jump J66.fst (Arg.var qlen_c, Arg.imm 0, ())) mp := by
  have hw := hspN.2.1; have hcl := hspN.1.core_ok; have hcv_le := hcl.cur_vars_le
  have hcap := c.harena; have hmx := c.hmaxv; unfold dimacsBound at hcap hmx
  have har_len := hcl.arena_len_arr; have halen_le := hcl.arena_len_le
  have hwf_r := hw.arena.refs_wf rsn_bv.toNat href_r
  have hbd_r : rsn_bv.toNat + 3 + fullArenaClauseSizeCore sp.core rsn_bv.toNat ≤
      sp.core.arena.length := by omega
  have hrsn_2 : (rsn_bv.setWidth 64 + 2#64).toNat < sp.core.arena.length := by bv_omega
  have hrsn_2_eq : (rsn_bv.setWidth 64 + 2#64).toNat = rsn_bv.toNat + 2 := by bv_omega
  let rsz_bv := sp.core.arena[(rsn_bv.setWidth 64 + 2#64).toNat]'hrsn_2
  have hrsz_raw : sp.core.arena[rsn_bv.toNat + 2]'(by omega) = rsz_bv := by
    dsimp only [rsz_bv]; simp only [hrsn_2_eq]
  have hrsz_eq : rsz_bv.toNat = fullArenaClauseSizeCore sp.core rsn_bv.toNat := by
    unfold fullArenaClauseSizeCore; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
    exact congrArg BitVec.toNat hrsz_raw.symm
  dsimp only [fvOp]
  viv_hsteps_nogrp
  refine wp_loop_inv (ts := [i64, i32])
    (fun (qlen_j, j_c, ()) mj => ∃ (mrk_j : List (BitVec 8)) (ws1_j : List (BitVec 32)),
      j_c.toNat ≤ rsz_bv.toNat ∧ qlen_c.toNat ≤ qlen_j.toNat ∧
      qlen_j.toNat ≤ sp.core.cur_vars ∧ (∀ k < qlen_c.toNat, ws1_j[k]? = ws1_b[k]?) ∧
      VivQueueOk c sp mrk_j ws1_j qlen_j.toNat ∧
      (∀ t < j_c.toNat,
        (sp.core.arena[rsn_bv.toNat + 3 + t]?.getD 0#32).toNat / 2 ≠ v_bv.toNat →
        (sp.core.lvl[(sp.core.arena[rsn_bv.toNat + 3 + t]?.getD 0#32).toNat / 2]?.getD
          0#32).toNat = 0 ∨
        (sp.core.arena[rsn_bv.toNat + 3 + t]?.getD 0#32).toNat / 2 ∈
          (ws1_j.take qlen_j.toNat).map BitVec.toNat) ∧
      (FullMem c { sp with
        core := { sp.core with mrk := mrk_j, lit_mark := lm1 }
        scratch := { sp.scratch with
          work_stk1 := ws1_j, work_stk2 := ws2_b, ant_sz := asz_b, res_sz := rsz_p } } ⋆ R) mj)
    (fun (_, j_c, ()) _ => rsz_bv.toNat - j_c.toNat)
    (fun Jj hJj => by
      viv_hsteps_nogrp
      exact hJj (qlen_c, 0#32, ()) mp ⟨mrk_b, ws1_b, by simp, Nat.le_refl _, hqb.2.2.1,
        fun _ _ => rfl, hqb, fun _ h => absurd h (Nat.not_lt_zero _), hmp⟩)
    (fun Jj (qlen_j, j_c, ()) mj
        ⟨mrk_j, ws1_j, hj_le, hq_le_j, hql_j, heq_j, hqj, hcov_j, hmj⟩ ihj => ?_)
  rw [Blocks.get_here]; dsimp only; viv_step; rw [wp_jnz]; constructor <;> intro hc
  · have hj_lt : j_c.toNat < rsz_bv.toNat := by
      dsimp only [rsz_bv]; simp only [Arg.val_var, BitVec.ult] at hc; exact of_decide_eq_true hc
    have hj1 : (j_c + 1#32).toNat = j_c.toNat + 1 := by bv_omega
    have hlit_idx : (rsn_bv.setWidth 64 + 3#64 + j_c.setWidth 64).toNat =
        rsn_bv.toNat + 3 + j_c.toNat := by bv_omega
    have hlit_ar : (rsn_bv.setWidth 64 + 3#64 + j_c.setWidth 64).toNat <
        sp.core.arena.length := by omega
    viv_hsteps_nogrp
    · let ol_bv := sp.core.arena[(rsn_bv.setWidth 64 + 3#64 + j_c.setWidth 64).toNat]'hlit_ar
      let ov_bv := ol_bv >>> 1#32
      have hol_raw : sp.core.arena[rsn_bv.toNat + 3 + j_c.toNat]'(by omega) = ol_bv := by
        dsimp only [ol_bv]; simp only [hlit_idx]
      have hol_mem : ol_bv.toNat ∈ fullArenaClauseLitsCore sp.core rsn_bv.toNat :=
        (mem_fullArenaClauseLitsCore_iff hbd_r).mpr
          ⟨j_c.toNat, by rw [← hrsz_eq]; exact hj_lt, congrArg BitVec.toNat hol_raw⟩
      have hol_lt : ol_bv.toNat < 2 * sp.core.cur_vars :=
        hw.arena.lits_lt rsn_bv.toNat href_r hng_r ol_bv.toNat hol_mem
      have hov_val : ov_bv.toNat = ol_bv.toNat / 2 := bv32_lshr1_toNat _
      have hov_cv : ov_bv.toNat < sp.core.cur_vars := by rw [hov_val]; omega
      refine wp_join_group (ts := [i64])
        (fun (qlen', ()) ml => ∃ (mrk_l : List (BitVec 8)) (ws1_l : List (BitVec 32)),
          qlen_j.toNat ≤ qlen'.toNat ∧ qlen'.toNat ≤ sp.core.cur_vars ∧
          (∀ k < qlen_j.toNat, ws1_l[k]? = ws1_j[k]?) ∧
          VivQueueOk c sp mrk_l ws1_l qlen'.toNat ∧
          (ov_bv.toNat ≠ v_bv.toNat →
            (sp.core.lvl[ov_bv.toNat]?.getD 0#32).toNat = 0 ∨
            ov_bv.toNat ∈ (ws1_l.take qlen'.toNat).map BitVec.toNat) ∧
          (FullMem c { sp with
            core := { sp.core with mrk := mrk_l, lit_mark := lm1 }
            scratch := { sp.scratch with
              work_stk1 := ws1_l, work_stk2 := ws2_b, ant_sz := asz_b, res_sz := rsz_p } } ⋆ R) ml)
        (fun _ (qlen', ()) ml ⟨mrk_l, ws1_l, hq_jl, hql_l, heq_l, hql_ok, hcov_ov, hml⟩ => by
          rw [Blocks.get_here]; dsimp only
          viv_hsteps_nogrp
          have hws1_l_len : ws1_l.length = 2 * c.max_vars := hql_ok.2.1
          refine ihj (qlen', j_c + 1#32, ()) ml (by dsimp only; omega)
            ⟨mrk_l, ws1_l, by omega, by omega, hql_l,
             fun k hk => (heq_l k (by omega)).trans (heq_j k hk), hql_ok,
             fun t ht hne => ?_, hml⟩
          rcases (by omega : t < j_c.toNat ∨ t = j_c.toNat) with ht' | rfl
          · refine (hcov_j t ht' hne).elim Or.inl fun hm' => Or.inr ?_
            obtain ⟨k, hk, hkeq⟩ := (mem_map_take_iff (by have := hqj.2.1; omega)).mp hm'
            exact (mem_map_take_iff (by omega)).mpr ⟨k, by omega, by rw [heq_l k hk, hkeq]⟩
          · have hleq :
                (sp.core.arena[rsn_bv.toNat + 3 + j_c.toNat]?.getD 0#32).toNat / 2 =
                ov_bv.toNat := by
              rw [List.getElem?_eq_getElem (by omega), Option.getD_some, hol_raw, hov_val]
            rw [hleq] at hne ⊢; exact hcov_ov hne)
        (fun Jl hJl => by
          viv_step; rw [wp_jnz]; constructor <;> intro hc
          · have hne_bv : ov_bv ≠ v_bv := by
              simp only [Arg.val_var, bne_iff_ne] at hc; exact hc
            have hov_ne : ov_bv.toNat ≠ v_bv.toNat := fun he => hne_bv (BitVec.eq_of_toNat_eq he)
            have hov_trl : ∃ m < sp.core.trail_end,
                (sp.core.trl[m]?.getD 0#32).toNat / 2 = ov_bv.toNat := by
              rcases hlits_r ol_bv.toNat hol_mem with hsame | ⟨m, hm_lt, hmeq, _⟩
              · exfalso; exact hov_ne (by rw [hov_val, hsame, htrl0])
              · exact ⟨m, by omega, by rw [hmeq, fullInv_var_xor1, hov_val]⟩
            exact deduce_push_branch_wp Γ hspN.1 hqj hov_cv hov_trl hmj
              fun qlen' mrk_l ws1_l ml hq_jl hql_l heq_l hql_ok hcov_ov hml =>
                hJl (qlen', ()) ml ⟨mrk_l, ws1_l, hq_jl, hql_l, heq_l, hql_ok,
                  fun _ => hcov_ov, hml⟩
          · have heq_bv : ov_bv = v_bv := by
              simp only [Arg.val_var, bne_eq_false_iff_eq] at hc; exact hc
            viv_hsteps_nogrp
            exact hJl (qlen_j, ()) mj ⟨mrk_j, ws1_j, Nat.le_refl _, hql_j,
              fun _ _ => rfl, hqj, fun hne => absurd (congrArg BitVec.toNat heq_bv) hne, hmj⟩)
    · have h3 : BitVec.toNat (3 : BitVec 64) = 3 := rfl
      have h2_eq : (rsn_bv.toNat + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64 =
          (rsn_bv.setWidth 64 + 2#64).toNat := by bv_omega
      have h_le : (rsn_bv.toNat + 3 + rsz_bv.toNat) % 2 ^ 64 ≤ sp.core.arena_len % 2 ^ 64 →
          False := by
        dsimp only [rsz_bv] at hc ⊢
        simp only [h2_eq] at hc; rw [← h3]
        simpa only [BitVec.toNat_add, BitVec.toNat_setWidth, Nat.add_assoc] using hc
      have : rsn_bv.toNat + 3 + rsz_bv.toNat < 2 ^ 64 := by omega
      have : sp.core.arena_len < 2 ^ 64 := by omega
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h_le
      exact False.elim (h_le (by omega))
  · have hj_eq : j_c.toNat = rsz_bv.toNat := by
      dsimp only [rsz_bv]; simp only [Arg.val_var, BitVec.ult] at hc
      have hge : sp.core.arena[(rsn_bv.setWidth 64 + 2#64).toNat].toNat ≤ j_c.toNat :=
        Nat.le_of_not_lt (of_decide_eq_false hc)
      dsimp only [rsz_bv] at hj_le; omega
    have hcov_l : ∀ q ∈ fullArenaClauseLitsCore sp.core rsn_bv.toNat, q / 2 ≠ v_bv.toNat →
        (sp.core.lvl[q / 2]?.getD 0#32).toNat = 0 ∨
        q / 2 ∈ (ws1_j.take qlen_j.toNat).map BitVec.toNat := by
      intro q hq hne
      obtain ⟨t, ht, hqt⟩ := (mem_fullArenaClauseLitsCore_iff hbd_r).mp hq
      have ht_lt : rsn_bv.toNat + 3 + t < sp.core.arena.length := by omega
      rw [← hrsz_eq] at ht
      have hc' := hcov_j t (by omega)
        (by rw [List.getElem?_eq_getElem ht_lt, Option.getD_some, hqt]; exact hne)
      rwa [List.getElem?_eq_getElem ht_lt, Option.getD_some, hqt] at hc'
    exact hJnext qlen_j mrk_j ws1_j mj hq_le_j hql_j heq_j hqj hcov_l hmj

theorem s13_deduce_large_rsn_wp (Γ : Env)
    (hPromote : Γ.Has "full_viv_recompute_promote_fid" vivRecomputePromoteSpec)
    (hSubCl : Γ.Has "full_viv_subsumes_cl_m6" fullVivSubsumesClM6Spec)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState} {R : Mem 64 → Prop}
    {mrk_b lm1 : List (BitVec 8)} {ws1_b ws2_b : List (BitVec 32)} {asz_b rsz_b : BitVec 64}
    {qlen_c qi1 : Val i64} {cref sz rsn_bv v_bv : Val i32} {olen : Val i32} {taut : Val .bool}
    {idx0 : Nat} {m : Mem 64} {Q : Post [i32]} {X : XPost}
    {Jexit : Cont [i64, i64, i32, .bool]} {Jnext : Cont [i64]}
    (hspN : S13SparseInvNoMark c F0 F_cur s)
    (hqb : VivQueueOk c s mrk_b ws1_b qlen_c.toNat)
    (hlm1_len : lm1.length = 2 * c.max_vars)
    (hlm1_dom : ∀ l < 2 * c.max_vars, lm1[l]?.getD 0#8 ≠ 0#8 →
      ∃ t < sz.toNat, (s.core.tmp[t]?.getD 0#32).toNat = l)
    (hws2_b : ws2_b.length = 2 * c.max_vars)
    (href_r : rsn_bv.toNat ∈ fullArenaClauseRefs s)
    (hng_r : fullArenaClauseGarb s rsn_bv.toNat = false)
    (hrsn_ne : rsn_bv ≠ 0xFFFFFFFF#32)
    (hidx0 : idx0 < s.core.trail_end) (htrl0 : (s.core.trl[idx0]?.getD 0#32).toNat / 2 = v_bv.toNat)
    (hrsn_eq : s.core.rsns[v_bv.toNat]?.getD 0xFFFFFFFF#32 = rsn_bv)
    (hlits_r : ∀ q ∈ fullArenaClauseLitsCore s.core rsn_bv.toNat,
      q = (s.core.trl[idx0]?.getD 0#32).toNat ∨
      ∃ m < idx0, (s.core.trl[m]?.getD 0#32).toNat = q ^^^ 1 ∧
        (s.core.lvl[q / 2]?.getD 0#32).toNat ≤
          (s.core.lvl[(s.core.trl[idx0]?.getD 0#32).toNat / 2]?.getD 0#32).toNat)
    (hm : (FullMem c { s with
      core := { s.core with mrk := mrk_b, lit_mark := lm1 }
      scratch := { s.scratch with
        work_stk1 := ws1_b, work_stk2 := ws2_b, ant_sz := asz_b, res_sz := rsz_b } } ⋆ R) m)
    (hJexit : ∀ (ar' mclr' : List (BitVec 32)) (rsz_n : BitVec 64) mex,
      let s_n : FullState := { s with core := { s.core with arena := ar', min_clr := mclr' } }
      S13SparseInvNoMark c F0 F_cur s_n → S13ArPres s s_n →
      S13SubRefOk s_n (rsn_bv.setWidth 64) → VivDeduceSubWitness F_cur s_n sz.toNat →
      (FullMem c { s_n with
        core := { s_n.core with mrk := mrk_b, lit_mark := lm1 }
        scratch := { s_n.scratch with
          work_stk1 := ws1_b, work_stk2 := ws2_b,
          ant_sz := rsn_bv.setWidth 64, res_sz := rsz_n } } ⋆ R) mex →
      Jexit (qlen_c, qi1, olen, taut, ()) mex)
    (hJnext : ∀ (ar' mclr' : List (BitVec 32)) (qlen' : Val i64) (mrk_n : List (BitVec 8))
        (ws1_n : List (BitVec 32)) (rsz_n : BitVec 64) mlg,
      let s_n : FullState := { s with core := { s.core with arena := ar', min_clr := mclr' } }
      S13SparseInvNoMark c F0 F_cur s_n → S13ArPres s s_n →
      qlen_c.toNat ≤ qlen'.toNat → qlen'.toNat ≤ s.core.cur_vars →
      (∀ j < qlen_c.toNat, ws1_n[j]? = ws1_b[j]?) →
      VivQueueOk c s_n mrk_n ws1_n qlen'.toNat →
      (∀ q ∈ fullArenaClauseLitsCore s.core rsn_bv.toNat, q / 2 ≠ v_bv.toNat →
        (s.core.lvl[q / 2]?.getD 0#32).toNat = 0 ∨
        q / 2 ∈ (ws1_n.take qlen'.toNat).map BitVec.toNat) →
      (FullMem c { s_n with
        core := { s_n.core with mrk := mrk_n, lit_mark := lm1 }
        scratch := { s_n.scratch with
          work_stk1 := ws1_n, work_stk2 := ws2_b, ant_sz := asz_b, res_sz := rsz_n } } ⋆ R) mlg →
      Jnext (qlen', ()) mlg) :
    wp Γ Q X (s13DeduceLargeRsnExpr c.hdr (BitVec.ofNat 64 s.core.cur_vars)
      c.pMark c.pLevel c.pArena c.pWorkStk1 cref sz rsn_bv v_bv qlen_c qi1 olen taut
      Jexit Jnext) m := by
  have hw := hspN.2.1; have hcl := hspN.1.core_ok; have hcv_le := hcl.cur_vars_le
  have hcap := c.harena; have hmx := c.hmaxv; unfold dimacsBound at hcap hmx
  have har_len := hcl.arena_len_arr
  have hwf_r := hw.arena.refs_wf rsn_bv.toNat href_r
  dsimp only [s13DeduceLargeRsnExpr, fvOp]
  refine wp_join_group (ts := [i64])
    (fun (qlen', ()) mlg => ∃ (ar' mclr' : List (BitVec 32)) (mrk_n : List (BitVec 8))
        (ws1_n : List (BitVec 32)) (rsz_n : BitVec 64),
      let s_n : FullState := { s with core := { s.core with arena := ar', min_clr := mclr' } }
      S13SparseInvNoMark c F0 F_cur s_n ∧ S13ArPres s s_n ∧
      qlen_c.toNat ≤ qlen'.toNat ∧ qlen'.toNat ≤ s.core.cur_vars ∧
      (∀ j < qlen_c.toNat, ws1_n[j]? = ws1_b[j]?) ∧ VivQueueOk c s_n mrk_n ws1_n qlen'.toNat ∧
      (∀ q ∈ fullArenaClauseLitsCore s.core rsn_bv.toNat, q / 2 ≠ v_bv.toNat →
        (s.core.lvl[q / 2]?.getD 0#32).toNat = 0 ∨
        q / 2 ∈ (ws1_n.take qlen'.toNat).map BitVec.toNat) ∧
      (FullMem c { s_n with
        core := { s_n.core with mrk := mrk_n, lit_mark := lm1 }
        scratch := { s_n.scratch with
          work_stk1 := ws1_n, work_stk2 := ws2_b, ant_sz := asz_b, res_sz := rsz_n } } ⋆ R) mlg)
    (fun _ (qlen', ()) mlg ⟨ar', mclr', mrk_n, ws1_n, rsz_n,
        hsp_n, hpres_n, h1, h2, h3, h4, h5, hm_n⟩ => by
      rw [Blocks.get_here]; dsimp only
      exact hJnext ar' mclr' qlen' mrk_n ws1_n rsz_n mlg hsp_n hpres_n h1 h2 h3 h4 h5 hm_n)
    (fun _ hJ53 => ?_)
  have hrsn_0 : (rsn_bv.setWidth 64).toNat < s.core.arena.length := by
    have := hwf_r.1; have := hcl.arena_len_le; bv_omega
  viv_hsteps_nogrp
  · refine wp_join_group (ts := [])
      (fun () mp => ∃ (ar_p mclr_p : List (BitVec 32)) (rsz_p : BitVec 64),
        let s_p : FullState := { s with core := { s.core with arena := ar_p, min_clr := mclr_p } }
        S13SparseInvNoMark c F0 F_cur s_p ∧ S13ArPres s s_p ∧
        (FullMem c { s_p with
          core := { s_p.core with mrk := mrk_b, lit_mark := lm1 }
          scratch := { s_p.scratch with
            work_stk1 := ws1_b, work_stk2 := ws2_b, ant_sz := asz_b, res_sz := rsz_p } } ⋆ R) mp)
      (fun _ () mp ⟨ar_p, mclr_p, rsz_p, hsp_p, hpres_p, hm_p⟩ => by
        rw [Blocks.get_here]; dsimp only
        let s_p : FullState := { s with core := { s.core with arena := ar_p, min_clr := mclr_p } }
        have hqb_p : VivQueueOk c s_p mrk_b ws1_b qlen_c.toNat :=
          s13_vivQueue_ar_eq rfl rfl rfl rfl hqb
        have href_p : rsn_bv.toNat ∈ fullArenaClauseRefs s_p := hpres_p.1 ▸ href_r
        have hng_p : fullArenaClauseGarb s_p rsn_bv.toNat = false :=
          (hpres_p.2 rsn_bv.toNat href_r).1.trans hng_r
        have hlits_eq : fullArenaClauseLitsCore s_p.core rsn_bv.toNat =
            fullArenaClauseLitsCore s.core rsn_bv.toNat :=
          (hpres_p.2 rsn_bv.toNat href_r).2.2
        have hlits_p : ∀ q ∈ fullArenaClauseLitsCore s_p.core rsn_bv.toNat,
            q = (s_p.core.trl[idx0]?.getD 0#32).toNat ∨
            ∃ m < idx0, (s_p.core.trl[m]?.getD 0#32).toNat = q ^^^ 1 ∧
              (s_p.core.lvl[q / 2]?.getD 0#32).toNat ≤
                (s_p.core.lvl[(s_p.core.trl[idx0]?.getD 0#32).toNat / 2]?.getD 0#32).toNat := by
          simpa only [s_p, hlits_eq] using hlits_r
        refine wp_join_group (ts := [])
          (fun () mq => mq = mp)
          (fun _ () mq hmq => by
            subst mq; rw [Blocks.get_here]
            refine s13_large_rsn_loop_wp Γ (sp := s_p) hsp_p hqb_p hlm1_len hws2_b href_p hng_p
              hidx0 htrl0 hlits_p hm_p fun qlen' mrk_n ws1_n mlg hq1 hq2 hq3 hq4 hcov hmlg => ?_
            exact hJ53 (qlen', ()) mlg ⟨ar_p, mclr_p, mrk_n, ws1_n, rsz_p, hsp_p, hpres_p,
              hq1, hq2, hq3, hq4, (by simpa only [hlits_eq] using hcov), hmlg⟩)
          (fun _ hJ60 => by
            viv_hsteps_nogrp
            · viv_call hSubCl
              refine ⟨c, F0, F_cur, _, R, rfl,
                s13_deduce_state_len hsp_p.1 hqb.1 hlm1_len hqb.2.1 hws2_b,
                s13_deduce_state_witness hsp_p.2.1, href_p, hng_p, hm_p, fun ok hok => ?_⟩
              viv_hsteps_nogrp
              · have hsub_lits := hok (by assumption)
                have hw_sub : VivDeduceSubWitness F_cur s_p sz.toNat := by
                  have hent_p := hsp_p.2.1.arena.entails rsn_bv.toNat href_p hng_p
                  refine cl_subWitness (s := s_p) hcv_le hent_p
                    (fun l hl => hsub_lits l hl) (fun q hqm => ?_)
                    (by simpa only [s_p] using hlm1_dom)
                  rcases hlits_p q hqm with hq_trl | ⟨m1, hm1_lt, hm1_eq, _⟩
                  · right
                    exact (show q / 2 = v_bv.toNat by rw [hq_trl]; exact htrl0) ▸
                      hrsn_eq ▸ hrsn_ne
                  · left
                    have hq_lt := hsp_p.2.1.arena.lits_lt rsn_bv.toNat href_p hng_p q hqm
                    have hvf := (hsp_p.2.1.vals_false_iff q hq_lt).mpr
                      ⟨m1, by dsimp only [s_p]; omega, hm1_eq⟩
                    dsimp only [s_p] at hvf ⊢; rw [hvf]; decide
                have hsr_p := s13_subRef_set_ref href_p hng_p
                exact hJexit ar_p mclr_p rsz_p _ hsp_p hpres_p hsr_p hw_sub
                  (by simpa only [s_p] using by assumption)
              · exact hJ60 () mp rfl
            · exact hJ60 () mp rfl))
      (fun _ hJ59 => by
        viv_hsteps_nogrp
        · have hne0 : (s.core.arena[(rsn_bv.setWidth 64).toNat]'hrsn_0 &&& 0x400000#32) ≠ 0#32 :=
            by assumption
          let s_r : FullState := { s with
            core := { s.core with mrk := mrk_b, lit_mark := lm1 }
            scratch := { s.scratch with
              work_stk1 := ws1_b, work_stk2 := ws2_b, ant_sz := asz_b, res_sz := 1#64 } }
          have hsp_r : S13SparseInvNoMark c F0 F_cur s_r :=
            s13_deduce_state_noMark hspN hqb.1 hlm1_len hqb.2.1 hws2_b
          viv_call hPromote
          refine ⟨c, F0, F_cur, s_r, R, rfl, hsp_r, href_r, hng_r, hm,
            fun ar' mclr' mp hsp_p hrefs_p hpres_p hmp => ?_⟩
          let s_p : FullState := { s with core := { s.core with arena := ar', min_clr := mclr' } }
          have hsp_p' : S13SparseInvNoMark c F0 F_cur s_p :=
            s13_deduce_state_noMark hsp_p hcl.mrk_len hcl.lit_mark_len
              hspN.1.scratch_ok.work_stk1_len hspN.1.scratch_ok.work_stk2_len
          exact hJ59 () mp ⟨ar', mclr', 1#64, hsp_p', ⟨hrefs_p, hpres_p⟩, hmp⟩
        · exact hJ59 () m ⟨s.core.arena, s.core.min_clr, rsz_b, hspN, s13ArPres_refl s, hm⟩)
  · exact hJ53 (qlen_c, ()) m ⟨s.core.arena, s.core.min_clr, mrk_b, ws1_b, rsz_b, hspN,
      s13ArPres_refl s, Nat.le_refl _, hqb.2.2.1, fun _ _ => rfl, hqb,
      fun q hqm _ => False.elim (by
        have h3 : BitVec.toNat (3 : BitVec 64) = 3 := rfl
        have harc_len := hcl.arena_len_le
        have h_le : (rsn_bv.toNat + 3) % 2 ^ 64 ≤ s.core.arena_len % 2 ^ 64 → False := by
          rw [← h3]; exact hc
        have := hwf_r.1
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h_le
        exact h_le (by omega)),
      hm⟩

/-! ## 4. `s13_deduce_phase1b_bin_wp` -/

abbrev binPushExpr (pVars pMark pLevel pWs1 : Val i64) (lit : Val i32)
    (qArg : Arg Val i64) (J : Cont [i64]) : Expr Val Cont [i32] :=
  fvOp (OpCode.lshr i32) (Arg.var lit, Arg.imm 1, ()) fun p =>
  fvOp (OpCode.zext 32 64) (Arg.var p.fst, ()) fun p =>
  fvOp (OpCode.mul i64) (Arg.var p.fst, Arg.imm 4, ()) fun p =>
  fvOp (OpCode.add i64) (Arg.var pLevel, Arg.var p.fst, ()) fun p =>
  Expr.load i32 (Arg.var p.fst) fun ld =>
  fvOp (OpCode.cmp .ugt i32 .bool (by decide)) (Arg.var ld, Arg.imm 0, ()) fun p =>
  Expr.jnz (Arg.var p.fst)
    (fvOp (OpCode.lshr i32) (Arg.var lit, Arg.imm 1, ()) fun p =>
     fvOp (OpCode.zext 32 64) (Arg.var p.fst, ()) fun p =>
     fvOp (OpCode.add i64) (Arg.var pMark, Arg.var p.fst, ()) fun p =>
     Expr.load i8 (Arg.var p.fst) fun ld =>
     fvOp (OpCode.trunc 32 8) (Arg.imm 0, ()) fun p0 =>
     fvOp (OpCode.zext 8 32) (Arg.var ld, ()) fun p1 =>
     fvOp (OpCode.zext 8 32) (Arg.var p0.fst, ()) fun p2 =>
     fvOp (OpCode.cmp .eq i32 .bool (by decide)) (Arg.var p1.fst, Arg.var p2.fst, ()) fun p =>
     Expr.jnz (Arg.var p.fst)
       (fvOp (OpCode.cmp .ult i64 .bool (by decide)) (qArg, Arg.var pVars, ()) fun p =>
        Expr.jnz (Arg.var p.fst)
          (fvOp (OpCode.lshr i32) (Arg.var lit, Arg.imm 1, ()) fun p =>
           fvOp (OpCode.zext 32 64) (Arg.var p.fst, ()) fun p =>
           fvOp (OpCode.add i64) (Arg.var pMark, Arg.var p.fst, ()) fun p =>
           fvOp (OpCode.trunc 32 8) (Arg.imm 1, ()) fun p1 =>
           Expr.store (Arg.var p1.fst) (Arg.var p.fst)
             (fvOp (OpCode.mul i64) (qArg, Arg.imm 4, ()) fun p =>
              fvOp (OpCode.add i64) (Arg.var pWs1, Arg.var p.fst, ()) fun p =>
              fvOp (OpCode.lshr i32) (Arg.var lit, Arg.imm 1, ()) fun p2 =>
              Expr.store (Arg.var p2.fst) (Arg.var p.fst)
                (fvOp (OpCode.add i64) (qArg, Arg.imm 1, ()) fun p =>
                 Expr.jump J (Arg.var p.fst, ()))))
          (Expr.jump J (qArg, ())))
       (Expr.jump J (qArg, ())))
    (Expr.jump J (qArg, ()))

private theorem bin_push_step_wp (Γ : Env) {c : FullCfg} {s : FullState}
    {mrk_c lm1 : List (BitVec 8)} {ws1_c ws2_c : List (BitVec 32)}
    {asz_c rsz_c : BitVec 64} {qArg : Arg Val i64} {lit : Val i32} {R : Mem 64 → Prop}
    {m : Mem 64} {Q : Post [i32]} {X : XPost} {J : Cont [i64]}
    (hlen : s.LengthsOk c) (hq : VivQueueOk c s mrk_c ws1_c qArg.val.toNat)
    (hlit_lt : lit.toNat < 2 * s.core.cur_vars)
    (hlit_trl : ∃ idx < s.core.trail_end, (s.core.trl[idx]?.getD 0#32).toNat / 2 = lit.toNat / 2)
    (hm : (FullMem c { s with
      core := { s.core with mrk := mrk_c, lit_mark := lm1 }
      scratch := { s.scratch with
        work_stk1 := ws1_c, work_stk2 := ws2_c, ant_sz := asz_c, res_sz := rsz_c } } ⋆ R) m)
    (hJ : ∀ (qlen' : Val i64) (mrk_n : List (BitVec 8)) (ws1_n : List (BitVec 32)) mn,
      qArg.val.toNat ≤ qlen'.toNat → qlen'.toNat ≤ s.core.cur_vars →
      (∀ j < qArg.val.toNat, ws1_n[j]? = ws1_c[j]?) →
      VivQueueOk c s mrk_n ws1_n qlen'.toNat →
      ((s.core.lvl[lit.toNat / 2]?.getD 0#32).toNat = 0 ∨
        lit.toNat / 2 ∈ (ws1_n.take qlen'.toNat).map BitVec.toNat) →
      (FullMem c { s with
        core := { s.core with mrk := mrk_n, lit_mark := lm1 }
        scratch := { s.scratch with
          work_stk1 := ws1_n, work_stk2 := ws2_c, ant_sz := asz_c, res_sz := rsz_c } } ⋆ R) mn →
      J (qlen', ()) mn) :
    wp Γ Q X (binPushExpr (BitVec.ofNat 64 s.core.cur_vars)
      c.pMark c.pLevel c.pWorkStk1 lit qArg J) m := by
  have hcl := hlen.core_ok; have hcv_le := hcl.cur_vars_le
  have hcap := c.harena; have hmx := c.hmaxv; unfold dimacsBound at hcap hmx
  have hv_cv : (lit >>> 1#32).toNat < s.core.cur_vars := by rw [bv32_lshr1_toNat]; omega
  have hv_nat : (lit >>> 1#32).toNat = lit.toNat / 2 := bv32_lshr1_toNat _
  have hv_lvl : (lit >>> 1#32).toNat < s.core.lvl.length := by rw [hcl.lvl_len]; omega
  have hv_mrk : (lit >>> 1#32).toNat < mrk_c.length := by rw [hq.1]; omega
  have hv_mod : ((lit >>> 1#32).setWidth 64).toNat = (lit >>> 1#32).toNat := by bv_omega
  have hv_lvl64 : ((lit >>> 1#32).setWidth 64).toNat < s.core.lvl.length := by
    rw [hv_mod]; exact hv_lvl
  have hv_mrk64 : ((lit >>> 1#32).setWidth 64).toNat < mrk_c.length := by
    rw [hv_mod]; exact hv_mrk
  have hql_le := hq.2.2.1; have hcv_64 : s.core.cur_vars < 2 ^ 64 := by omega
  dsimp only [binPushExpr, fvOp]
  viv_hsteps_nogrp
  · have hlp : 0 < (s.core.lvl[(lit >>> 1#32).toNat]?.getD 0#32).toNat := by
      rw [List.getElem?_eq_getElem hv_lvl, Option.getD_some]; c0_bound
    have hm0 : mrk_c[(lit >>> 1#32).toNat]?.getD 0#8 = 0#8 := by
      rw [List.getElem?_eq_getElem hv_mrk, Option.getD_some]
      exact (bv8_zext32_eq0_iff _).mp (by assumption)
    have hql_lt := push_queue_lt hq hcv_le hv_cv hm0
    have hql_ws1 : qArg.val.toNat < ws1_c.length := by have := hq.2.1; omega
    have hql1 : (qArg.val + 1#64).toNat = qArg.val.toNat + 1 := by bv_omega
    obtain ⟨_, hq_next, hpre_next, _⟩ := push_queue_step hq hcv_le hv_cv hlp hm0
      (by simpa only [hv_nat] using hlit_trl)
    viv_hsteps_nogrp
    have hv_sh : (BitVec.setWidth 64 (lit >>> (1 : Val i32))).toNat = (lit >>> 1#32).toNat := hv_mod
    have hq_next' : VivQueueOk c s (mrk_c.set ((lit >>> (1 : Val i32)).setWidth 64).toNat
        (BitVec.ofNat (OfNat.ofNat 8) (OfNat.ofNat 1)))
        (ws1_c.set qArg.val.toNat (lit >>> 1#32)) (qArg.val + 1#64).toNat := by
      rw [hv_sh, hql1]; exact hq_next
    refine hJ (qArg.val + 1#64) _ _ _ (by omega) (by omega) hpre_next hq_next' (Or.inr ?_)
      (by assumption)
    · rw [hql1]
      exact (mem_map_take_iff (by simp [hq.2.1]; omega)).mpr
        ⟨qArg.val.toNat, by omega, by
          rw [List.getElem?_set_self hql_ws1, Option.getD_some, hv_nat]⟩
  · have hm0 : mrk_c[(lit >>> 1#32).toNat]?.getD 0#8 = 0#8 := by
      rw [List.getElem?_eq_getElem hv_mrk, Option.getD_some]
      exact (bv8_zext32_eq0_iff _).mp (by assumption)
    have hql_lt := push_queue_lt hq hcv_le hv_cv hm0
    have hcv_le_q : s.core.cur_vars % 2 ^ 64 ≤ qArg.val.toNat := by c0_bound
    rw [Nat.mod_eq_of_lt hcv_64] at hcv_le_q; omega
  · have hne0 : mrk_c[(lit >>> 1#32).toNat]'hv_mrk ≠ 0#8 := fun h => by
      have hne32 : (mrk_c[(lit >>> 1#32).toNat]'hv_mrk).setWidth 32 ≠ 0#32 := by assumption
      exact hne32 ((bv8_zext32_eq0_iff _).mpr h)
    have hm1 : mrk_c[(lit >>> 1#32).toNat]?.getD 0#8 = 1#8 := by
      rcases hq.2.2.2.2.2.2.2.1 _ hv_cv with h0 | h1
      · rw [List.getElem?_eq_getElem hv_mrk, Option.getD_some] at h0; exact absurd h0 hne0
      · exact h1
    exact hJ qArg.val mrk_c ws1_c m (Nat.le_refl _) hql_le (fun _ _ => rfl) hq
      (Or.inr (by have := (hq.2.2.2.2.2.2.1 _ hv_cv).mp hm1; rwa [hv_nat] at this)) hm
  · have hlv0 : (s.core.lvl[lit.toNat / 2]?.getD 0#32).toNat = 0 := by
      have hl_lt : lit.toNat / 2 < s.core.lvl.length := by rw [← hv_nat]; exact hv_lvl
      rw [List.getElem?_eq_getElem hl_lt, Option.getD_some]; exact Nat.eq_zero_of_not_pos hc
    exact hJ qArg.val mrk_c ws1_c m (Nat.le_refl _) hql_le (fun _ _ => rfl) hq (Or.inl hlv0) hm

abbrev s13DeducePhase1bBinExpr (h pVars pMark pLevel pWs1 : Val i64)
    (Jexit : Cont [i64]) : Expr Val Cont [i32] :=
  fvOp (OpCode.add i64) (Arg.var h, Arg.imm 536, ()) fun p =>
  Expr.load i64 (Arg.var p.fst) fun ld =>
  fvOp (OpCode.trunc 64 32) (Arg.var ld, ()) fun p_a =>
  fvOp (OpCode.add i64) (Arg.var h, Arg.imm 544, ()) fun p =>
  Expr.load i64 (Arg.var p.fst) fun ld =>
  fvOp (OpCode.trunc 64 32) (Arg.var ld, ()) fun p_b =>
  Expr.group (sig := [[i64]]) (fun _ => Blocks.cons (fun p =>
    Expr.jump Jexit (Arg.var p.fst, ())) Blocks.nil) fun J37 =>
  Expr.call "full_viv_subsumes_bin_m6" (as := [i64, i32, i32]) (bs := [.bool])
    (Arg.var h, Arg.var p_a.fst, Arg.var p_b.fst, ()) fun ok =>
  Expr.jnz (Arg.var ok.fst)
    (fvOp (OpCode.add i64) (Arg.var h, Arg.imm 1136, ()) fun p =>
     Expr.store (Arg.imm (t := i64) 18446744073709551614) (Arg.var p.fst)
       (Expr.jump J37.fst (Arg.imm 0, ())))
    (Expr.group (sig := [[i64]]) (fun _ => Blocks.cons (fun p40 =>
       Expr.group (sig := [[i64]]) (fun _ => Blocks.cons (fun p42 =>
         Expr.jump J37.fst (Arg.var p42.fst, ())) Blocks.nil) fun J41 =>
       binPushExpr pVars pMark pLevel pWs1 p_b.fst (Arg.var p40.fst) J41.fst) Blocks.nil) fun J39 =>
     binPushExpr pVars pMark pLevel pWs1 p_a.fst (Arg.imm 0) J39.fst)

theorem s13_deduce_phase1b_bin_wp (Γ : Env)
    (hSubBin : Γ.Has "full_viv_subsumes_bin_m6" fullVivSubsumesBinM6Spec)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState} {R : Mem 64 → Prop}
    {lm1 : List (BitVec 8)} {sz cref implied : Val i32} {m : Mem 64} {Q : Post [i32]} {X : XPost}
    {Jexit : Cont [i64]}
    (hspW : FullSparseInvW c F0 F_cur s)
    (hlm1_len : lm1.length = 2 * c.max_vars)
    (hlm1_dom : ∀ l < 2 * c.max_vars, lm1[l]?.getD 0#8 ≠ 0#8 →
      ∃ t < sz.toNat, (s.core.tmp[t]?.getD 0#32).toNat = l)
    (himp_eq : implied = 0xFFFFFFFF#32)
    (hct1 : s.core.confl_type = 1#64)
    (hconfl : implied = 0xFFFFFFFF#32 → FullVivConflictOk F_cur s ∨
      (s.core.confl_type = 0#64 ∧
        ∀ l ∈ fullArenaClauseLits s cref.toNat, s.core.vals[l]?.getD 0#8 = 0xFF#8))
    (hq0 : VivQueueOk c s s.core.mrk s.scratch.work_stk1 0)
    (hm : (FullMem c { s with
      core := { s.core with lit_mark := lm1 }
      scratch := { s.scratch with ant_sz := 0xFFFFFFFFFFFFFFFF#64, res_sz := 0#64 } } ⋆ R) m)
    (hJexit : ∀ (qlen_v : Val i64) (mrk1 : List (BitVec 8)) (ws1_1 : List (BitVec 32))
        (asz1 rsz1 : BitVec 64) m_q,
      qlen_v.toNat ≤ s.core.cur_vars → VivQueueOk c s mrk1 ws1_1 qlen_v.toNat →
      (asz1 = 0xFFFFFFFFFFFFFFFF#64 →
        VivSeedOk s cref implied ws1_1 s.scratch.work_stk2 qlen_v.toNat 0 false) →
      S13SubRefOk s asz1 →
      (asz1 ≠ 0xFFFFFFFFFFFFFFFF#64 → VivDeduceSubWitness F_cur s sz.toNat) →
      (FullMem c { s with
        core := { s.core with mrk := mrk1, lit_mark := lm1 }
        scratch := { s.scratch with
          work_stk1 := ws1_1, ant_sz := asz1, res_sz := rsz1 } } ⋆ R) m_q →
      Jexit (qlen_v, ()) m_q) :
    wp Γ Q X (s13DeducePhase1bBinExpr c.hdr (BitVec.ofNat 64 s.core.cur_vars)
      c.pMark c.pLevel c.pWorkStk1 Jexit) m := by
  have hw := hspW.2.1; have hcl := hspW.1.core_ok; have hscl := hspW.1.scratch_ok
  have hcap := c.harena; have hmx := c.hmaxv; unfold dimacsBound at hcap hmx
  have hcv_le := hcl.cur_vars_le; have hmrk_len := hcl.mrk_len
  have hws1_len := hscl.work_stk1_len; have hws2_len := hscl.work_stk2_len
  rcases hconfl himp_eq with (⟨_, ha_lt, hb_lt, hent_ab, hva, hvb⟩ | ⟨hct2, _⟩) | ⟨hct0, _⟩
  · have ha32 : s.core.confl_lit0.toNat < 2 ^ 32 := by omega
    have hb32 : s.core.confl_lit1.toNat < 2 ^ 32 := by omega
    let a_bv := s.core.confl_lit0.truncate 32
    let b_bv := s.core.confl_lit1.truncate 32
    have ha_eq : a_bv.toNat = s.core.confl_lit0.toNat := by dsimp only [a_bv]; bv_omega
    have hb_eq : b_bv.toNat = s.core.confl_lit1.toNat := by dsimp only [b_bv]; bv_omega
    have ha_trl : ∃ m < s.core.trail_end,
        (s.core.trl[m]?.getD 0#32).toNat / 2 = a_bv.toNat / 2 := by
      obtain ⟨m, hm_lt, hmeq⟩ := (hw.vals_false_iff _ ha_lt).mp hva
      exact ⟨m, hm_lt, by rw [hmeq, fullInv_var_xor1, ha_eq]⟩
    have hb_trl : ∃ m < s.core.trail_end,
        (s.core.trl[m]?.getD 0#32).toNat / 2 = b_bv.toNat / 2 := by
      obtain ⟨m, hm_lt, hmeq⟩ := (hw.vals_false_iff _ hb_lt).mp hvb
      exact ⟨m, hm_lt, by rw [hmeq, fullInv_var_xor1, hb_eq]⟩
    dsimp only [s13DeducePhase1bBinExpr, fvOp]
    viv_hsteps_nogrp
    refine wp_join_group (ts := [i64])
      (fun (qlen_v, ()) m_q => ∃ (mrk1 : List (BitVec 8)) (ws1_1 : List (BitVec 32))
          (asz1 : BitVec 64),
        qlen_v.toNat ≤ s.core.cur_vars ∧ VivQueueOk c s mrk1 ws1_1 qlen_v.toNat ∧
        (asz1 = 0xFFFFFFFFFFFFFFFF#64 →
          VivSeedOk s cref implied ws1_1 s.scratch.work_stk2 qlen_v.toNat 0 false) ∧
        S13SubRefOk s asz1 ∧
        (asz1 ≠ 0xFFFFFFFFFFFFFFFF#64 → VivDeduceSubWitness F_cur s sz.toNat) ∧
        (FullMem c { s with
          core := { s.core with mrk := mrk1, lit_mark := lm1 }
          scratch := { s.scratch with work_stk1 := ws1_1, ant_sz := asz1, res_sz := 0#64 } }
          ⋆ R) m_q)
      (fun _ (qlen_v, ()) m_q ⟨mrk1, ws1_1, asz1, hql, hq1, hsd, hsr, hsubw, hmq⟩ => by
        rw [Blocks.get_here]; dsimp only
        exact hJexit qlen_v mrk1 ws1_1 asz1 0#64 m_q hql hq1 hsd hsr hsubw hmq)
      (fun _ hJ37 => by
        viv_call hSubBin
        refine ⟨c, F0, F_cur, _, R, rfl,
          s13_deduce_state_len hspW.1 hmrk_len hlm1_len hws1_len hws2_len,
          s13_deduce_state_witness hw, (by rw [ha_eq]; exact ha_lt),
          (by rw [hb_eq]; exact hb_lt), hm, fun ok hok => ?_⟩
        viv_hsteps_nogrp
        · have hsub_ok := hok (by assumption)
          have hw_bin : VivDeduceSubWitness F_cur s sz.toNat := by
            refine cl_subWitness hcv_le hent_ab (fun l hl => ?_) (fun l hl => ?_) hlm1_dom
            · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
              rcases hl with rfl | rfl
              · exact ⟨ha_lt, by simpa only [← ha_eq] using hsub_ok.1⟩
              · exact ⟨hb_lt, by simpa only [← hb_eq] using hsub_ok.2⟩
            · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
              left
              rcases hl with rfl | rfl
              · rw [hva]; decide
              · rw [hvb]; decide
          exact hJ37 (0#64, ()) _ ⟨s.core.mrk, s.scratch.work_stk1, 0xFFFFFFFFFFFFFFFE#64,
            Nat.zero_le _, hq0, (fun h => absurd h (by decide)),
            ⟨Or.inr (Or.inl rfl), fun _ h => absurd rfl h⟩, (fun _ => hw_bin), by assumption⟩
        · refine wp_join_group (ts := [i64])
            (fun (qa, ()) ma => ∃ (mrk_a : List (BitVec 8)) (ws1_a : List (BitVec 32)),
              qa.toNat ≤ s.core.cur_vars ∧ VivQueueOk c s mrk_a ws1_a qa.toNat ∧
              ((s.core.lvl[s.core.confl_lit0.toNat / 2]?.getD 0#32).toNat = 0 ∨
                s.core.confl_lit0.toNat / 2 ∈ (ws1_a.take qa.toNat).map BitVec.toNat) ∧
              (FullMem c { s with
                core := { s.core with mrk := mrk_a, lit_mark := lm1 }
                scratch := { s.scratch with
                  work_stk1 := ws1_a, ant_sz := 0xFFFFFFFFFFFFFFFF#64, res_sz := 0#64 } } ⋆ R) ma)
            (fun _ (qa, ()) ma ⟨mrk_a, ws1_a, hqa_le, hqa, hcov_a, hma⟩ => by
              rw [Blocks.get_here]; dsimp only
              refine wp_join_group (ts := [i64])
                (fun (qb, ()) mb => ∃ (mrk_b : List (BitVec 8)) (ws1_b : List (BitVec 32)),
                  qb.toNat ≤ s.core.cur_vars ∧ VivQueueOk c s mrk_b ws1_b qb.toNat ∧
                  ((s.core.lvl[s.core.confl_lit0.toNat / 2]?.getD 0#32).toNat = 0 ∨
                    s.core.confl_lit0.toNat / 2 ∈ (ws1_b.take qb.toNat).map BitVec.toNat) ∧
                  ((s.core.lvl[s.core.confl_lit1.toNat / 2]?.getD 0#32).toNat = 0 ∨
                    s.core.confl_lit1.toNat / 2 ∈ (ws1_b.take qb.toNat).map BitVec.toNat) ∧
                  (FullMem c { s with
                    core := { s.core with mrk := mrk_b, lit_mark := lm1 }
                    scratch := { s.scratch with
                      work_stk1 := ws1_b,
                      ant_sz := 0xFFFFFFFFFFFFFFFF#64, res_sz := 0#64 } } ⋆ R) mb)
                (fun _ (qb, ()) mb ⟨mrk_b, ws1_b, hqb_le, hqb, hcov_a', hcov_b, hmb⟩ => by
                  rw [Blocks.get_here]; dsimp only
                  exact hJ37 (qb, ()) mb ⟨mrk_b, ws1_b, 0xFFFFFFFFFFFFFFFF#64, hqb_le, hqb,
                    fun _ _ => by
                      dsimp only [VivSeedOk]
                      rw [ite_eq_right (fun h => h himp_eq), ite_eq_left hct1]
                      exact ⟨hcov_a', hcov_b⟩,
                    ⟨Or.inl rfl, fun h => absurd rfl h⟩, fun h => absurd rfl h, hmb⟩)
                (fun _ hJ41 => by
                  refine bin_push_step_wp Γ hspW.1 hqa (by rw [hb_eq]; exact hb_lt) hb_trl hma
                    fun qb mrk_b ws1_b mb hqab hqb_le heq_ab hqb hcov_b hmb => ?_
                  have hq_ab : qa.toNat ≤ qb.toNat := hqab
                  have hcov_a' : (s.core.lvl[s.core.confl_lit0.toNat / 2]?.getD 0#32).toNat = 0 ∨
                      s.core.confl_lit0.toNat / 2 ∈ (ws1_b.take qb.toNat).map BitVec.toNat :=
                    hcov_a.elim Or.inl fun hm' => Or.inr (by
                      obtain ⟨k, hk, hkeq⟩ := (mem_map_take_iff (by have := hqa.2.1; omega)).mp hm'
                      exact (mem_map_take_iff (by have := hqb.2.1; omega)).mpr
                        ⟨k, by omega, by rw [heq_ab k hk, hkeq]⟩)
                  have hb_eq' : (s.core.confl_lit1.truncate 32).toNat = s.core.confl_lit1.toNat :=
                    hb_eq
                  simp only [hb_eq'] at hcov_b
                  exact hJ41 (qb, ()) mb ⟨mrk_b, ws1_b, hqb_le, hqb, hcov_a', hcov_b, hmb⟩))
            (fun _ hJ39 => by
              refine bin_push_step_wp Γ hspW.1 hq0 (by rw [ha_eq]; exact ha_lt) ha_trl hm
                fun qa mrk_a ws1_a ma _ hqa_le _ hqa hcov_a hma => ?_
              have ha_eq' : (s.core.confl_lit0.truncate 32).toNat = s.core.confl_lit0.toNat :=
                ha_eq
              simp only [ha_eq'] at hcov_a
              exact hJ39 (qa, ()) ma ⟨mrk_a, ws1_a, hqa_le, hqa, hcov_a, hma⟩))
  · exact absurd hct1 (by rw [hct2]; decide)
  · exact absurd hct1 (by rw [hct0]; decide)

/-! ## 5. `s13_deduce_phase1b_large_wp` -/

abbrev s13DeducePhase1bLargeExpr (h pVars pMark pLevel pArena pWs1 : Val i64)
    (cref sz src_cr : Val i32) (Jexit : Cont [i64]) : Expr Val Cont [i32] :=
  Expr.group (sig := [[i64]]) (fun _ => Blocks.cons (fun p =>
    Expr.jump Jexit (Arg.var p.fst, ())) Blocks.nil) fun J31 =>
  fvOp (OpCode.zext 32 64) (Arg.var src_cr, ()) fun p =>
  fvOp (OpCode.add i64) (Arg.var p.fst, Arg.imm 3, ()) fun p3 =>
  fvOp (OpCode.add i64) (Arg.var h, Arg.imm 48, ()) fun p48 =>
  Expr.load i64 (Arg.var p48.fst) fun ld_len =>
  fvOp (OpCode.cmp .ule i64 .bool (by decide)) (Arg.var p3.fst, Arg.var ld_len, ()) fun p =>
  Expr.jnz (Arg.var p.fst)
    (Expr.group (sig := [[]]) (fun _ => Blocks.cons (fun (_ : Tup Val []) =>
      Expr.group (sig := [[i64]]) (fun _ => Blocks.cons (fun p =>
        Expr.jump J31.fst (Arg.var p.fst, ())) Blocks.nil) fun J38 =>
      fvOp (OpCode.add i64) (Arg.var h, Arg.imm 1136, ()) fun p =>
      Expr.load i64 (Arg.var p.fst) fun ld =>
      fvOp (OpCode.cmp .eq i64 .bool (by decide))
        (Arg.var ld, Arg.imm 18446744073709551615, ()) fun p =>
      Expr.jnz (Arg.var p.fst)
        (fvOp (OpCode.zext 32 64) (Arg.var src_cr, ()) fun p =>
         fvOp (OpCode.add i64) (Arg.var p.fst, Arg.imm 2, ()) fun p =>
         fvOp (OpCode.mul i64) (Arg.var p.fst, Arg.imm 4, ()) fun p =>
         fvOp (OpCode.add i64) (Arg.var pArena, Arg.var p.fst, ()) fun p =>
         Expr.load i32 (Arg.var p.fst) fun csz_bv =>
         Expr.group (sig := [[i64, i32]]) (fun J47 => Blocks.cons (fun p_i =>
           fvOp (OpCode.cmp .ult i32 .bool (by decide))
             (Arg.var p_i.snd.fst, Arg.var csz_bv, ()) fun p =>
           Expr.jnz (Arg.var p.fst)
             (fvOp (OpCode.zext 32 64) (Arg.var src_cr, ()) fun p =>
              fvOp (OpCode.add i64) (Arg.var p.fst, Arg.imm 3, ()) fun p =>
              fvOp (OpCode.zext 32 64) (Arg.var p_i.snd.fst, ()) fun pz =>
              fvOp (OpCode.add i64) (Arg.var p.fst, Arg.var pz.fst, ()) fun p =>
              fvOp (OpCode.mul i64) (Arg.var p.fst, Arg.imm 4, ()) fun p =>
              fvOp (OpCode.add i64) (Arg.var pArena, Arg.var p.fst, ()) fun p =>
              Expr.load i32 (Arg.var p.fst) fun ld =>
              fvOp (OpCode.lshr i32) (Arg.var ld, Arg.imm 1, ()) fun p_lv =>
              Expr.group (sig := [[i64]]) (fun _ => Blocks.cons (fun p =>
                fvOp (OpCode.add i32) (Arg.var p_i.snd.fst, Arg.imm 1, ()) fun pi1 =>
                Expr.jump J47.fst (Arg.var p.fst, Arg.var pi1.fst, ())) Blocks.nil) fun J59 =>
              deducePushExpr pVars pMark pLevel pWs1 p_lv.fst p_i.fst J59.fst)
             (Expr.jump J38.fst (Arg.var p_i.fst, ()))) Blocks.nil)
           fun J47 => Expr.jump J47.fst (Arg.imm 0, Arg.imm 0, ()))
        (Expr.jump J38.fst (Arg.imm 0, ()))) Blocks.nil) fun J37 =>
     fvOp (OpCode.cmp .ne i32 .bool (by decide)) (Arg.var src_cr, Arg.var cref, ()) fun p =>
     Expr.jnz (Arg.var p.fst)
       (Expr.group (sig := [[]]) (fun _ => Blocks.cons (fun (_ : Tup Val []) =>
          Expr.group (sig := [[]]) (fun _ => Blocks.cons (fun (_ : Tup Val []) =>
            Expr.jump J37.fst ()) Blocks.nil) fun J40 =>
          Expr.call "full_viv_subsumes_cl_m6" (as := [i64, i32, i32]) (bs := [.bool])
            (Arg.var h, Arg.var src_cr, Arg.var sz, ()) fun ok =>
          Expr.jnz (Arg.var ok.fst)
            (fvOp (OpCode.zext 32 64) (Arg.var src_cr, ()) fun pr =>
             fvOp (OpCode.add i64) (Arg.var h, Arg.imm 1136, ()) fun p =>
             Expr.store (Arg.var pr.fst) (Arg.var p.fst) (Expr.jump J40.fst ()))
            (Expr.jump J40.fst ())) Blocks.nil) fun J39 =>
        fvOp (OpCode.zext 32 64) (Arg.var src_cr, ()) fun p =>
        fvOp (OpCode.mul i64) (Arg.var p.fst, Arg.imm 4, ()) fun p =>
        fvOp (OpCode.add i64) (Arg.var pArena, Arg.var p.fst, ()) fun p =>
        Expr.load i32 (Arg.var p.fst) fun ld =>
        fvOp (OpCode.and i32) (Arg.var ld, Arg.imm 4194304, ()) fun p =>
        fvOp (OpCode.cmp .ne i32 .bool (by decide)) (Arg.var p.fst, Arg.imm 0, ()) fun p =>
        Expr.jnz (Arg.var p.fst)
          (fvOp (OpCode.add i64) (Arg.var h, Arg.imm 1144, ()) fun p =>
           Expr.store (Arg.imm (t := i64) 1) (Arg.var p.fst)
             (Expr.call "full_viv_recompute_promote_fid" (as := [i64, i32]) (bs := [])
                (Arg.var h, Arg.var src_cr, ()) fun _ => Expr.jump J39.fst ()))
          (Expr.jump J39.fst ()))
       (Expr.jump J37.fst ()))
    (Expr.jump J31.fst (Arg.imm 0, ()))

private theorem s13_phase1b_large_loop_wp (Γ : Env) {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {sp : FullState} {R : Mem 64 → Prop}
    {lm1 : List (BitVec 8)} {cref src_cr implied : Val i32} {rsz_p : BitVec 64} {mp : Mem 64}
    {Q : Post [i32]} {X : XPost} {Jexit : Cont [i64]}
    (hspN : S13SparseInvNoMark c F0 F_cur sp)
    (himp_eq : implied = 0xFFFFFFFF#32)
    (hct_ne1 : sp.core.confl_type ≠ 1#64)
    (hsrc_eq : src_cr.toNat =
      (if sp.core.confl_type = 2#64 then sp.core.confl_ref.toNat else cref.toNat))
    (hsrc_ref : src_cr.toNat ∈ fullArenaClauseRefs sp)
    (hsrc_ng : fullArenaClauseGarb sp src_cr.toNat = false)
    (_hlm1_len : lm1.length = 2 * c.max_vars)
    (hfal_src : ∀ l ∈ fullArenaClauseLits sp src_cr.toNat, sp.core.vals[l]?.getD 0#8 = 0xFF#8)
    (hq0 : VivQueueOk c sp sp.core.mrk sp.scratch.work_stk1 0)
    (hmp : (FullMem c { sp with
      core := { sp.core with lit_mark := lm1 }
      scratch := { sp.scratch with ant_sz := 0xFFFFFFFFFFFFFFFF#64, res_sz := rsz_p } } ⋆ R) mp)
    (hJexit : ∀ (qlen_v : Val i64) (mrk1 : List (BitVec 8)) (ws1_1 : List (BitVec 32)) m_q,
      qlen_v.toNat ≤ sp.core.cur_vars → VivQueueOk c sp mrk1 ws1_1 qlen_v.toNat →
      VivSeedOk sp cref implied ws1_1 sp.scratch.work_stk2 qlen_v.toNat 0 false →
      (FullMem c { sp with
        core := { sp.core with mrk := mrk1, lit_mark := lm1 }
        scratch := { sp.scratch with
          work_stk1 := ws1_1, ant_sz := 0xFFFFFFFFFFFFFFFF#64, res_sz := rsz_p } } ⋆ R) m_q →
      Jexit (qlen_v, ()) m_q) :
    let pArena := c.pArena
    wp Γ Q X
      (Expr.load i32 (Arg.var (pArena + (src_cr.setWidth 64 + 2) * 4, ()).fst) fun csz_bv =>
       Expr.group (sig := [[i64, i32]]) (fun J47 => Blocks.cons (fun p_i =>
         fvOp (OpCode.cmp .ult i32 .bool (by decide))
           (Arg.var p_i.snd.fst, Arg.var csz_bv, ()) fun p =>
         Expr.jnz (Arg.var p.fst)
           (fvOp (OpCode.zext 32 64) (Arg.var src_cr, ()) fun p =>
            fvOp (OpCode.add i64) (Arg.var p.fst, Arg.imm 3, ()) fun p =>
            fvOp (OpCode.zext 32 64) (Arg.var p_i.snd.fst, ()) fun pz =>
            fvOp (OpCode.add i64) (Arg.var p.fst, Arg.var pz.fst, ()) fun p =>
            fvOp (OpCode.mul i64) (Arg.var p.fst, Arg.imm 4, ()) fun p =>
            fvOp (OpCode.add i64) (Arg.var pArena, Arg.var p.fst, ()) fun p =>
            Expr.load i32 (Arg.var p.fst) fun ld =>
            fvOp (OpCode.lshr i32) (Arg.var ld, Arg.imm 1, ()) fun p_lv =>
            Expr.group (sig := [[i64]]) (fun _ => Blocks.cons (fun p =>
              fvOp (OpCode.add i32) (Arg.var p_i.snd.fst, Arg.imm 1, ()) fun pi1 =>
              Expr.jump J47.fst (Arg.var p.fst, Arg.var pi1.fst, ())) Blocks.nil) fun J59 =>
            deducePushExpr (BitVec.ofNat 64 sp.core.cur_vars)
              c.pMark c.pLevel c.pWorkStk1 p_lv.fst p_i.fst J59.fst)
           (Expr.jump Jexit (Arg.var p_i.fst, ()))) Blocks.nil)
         fun J47 => Expr.jump J47.fst (Arg.imm 0, Arg.imm 0, ())) mp := by
  have hw := hspN.2.1; have hcl := hspN.1.core_ok; have hcv_le := hcl.cur_vars_le
  have hcap := c.harena; have hmx := c.hmaxv; unfold dimacsBound at hcap hmx
  have hsrc_wf := hw.arena.refs_wf src_cr.toNat hsrc_ref
  have hsrc_bd : src_cr.toNat + 3 + fullArenaClauseSizeCore sp.core src_cr.toNat ≤
      sp.core.arena.length := by
    have := hcl.arena_len_arr; have := hcl.arena_len_le; omega
  have hsrc2 : (src_cr.setWidth 64 + 2#64).toNat < sp.core.arena.length := by
    have := hsrc_wf.2.1; bv_omega
  have hsrc2_eq : (src_cr.setWidth 64 + 2#64).toNat = src_cr.toNat + 2 := by bv_omega
  let csz_bv := sp.core.arena[(src_cr.setWidth 64 + 2#64).toNat]'hsrc2
  have hcsz_eq : csz_bv.toNat = fullArenaClauseSizeCore sp.core src_cr.toNat := by
    unfold fullArenaClauseSizeCore; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
    dsimp only [csz_bv]; simp only [hsrc2_eq]
  dsimp only [fvOp]
  viv_hsteps_nogrp
  refine wp_loop_inv (ts := [i64, i32])
    (fun (qlen_i, i_c, ()) mi => ∃ (mrk_i : List (BitVec 8)) (ws1_i : List (BitVec 32)),
      i_c.toNat ≤ csz_bv.toNat ∧ qlen_i.toNat ≤ sp.core.cur_vars ∧
      VivQueueOk c sp mrk_i ws1_i qlen_i.toNat ∧
      (∀ t < i_c.toNat,
        (sp.core.lvl[(sp.core.arena[src_cr.toNat + 3 + t]?.getD 0#32).toNat / 2]?.getD
          0#32).toNat = 0 ∨
        (sp.core.arena[src_cr.toNat + 3 + t]?.getD 0#32).toNat / 2 ∈
          (ws1_i.take qlen_i.toNat).map BitVec.toNat) ∧
      (FullMem c { sp with
        core := { sp.core with mrk := mrk_i, lit_mark := lm1 }
        scratch := { sp.scratch with
          work_stk1 := ws1_i, ant_sz := 0xFFFFFFFFFFFFFFFF#64, res_sz := rsz_p } } ⋆ R) mi)
    (fun (_, i_c, ()) _ => csz_bv.toNat - i_c.toNat)
    (fun Ji hJi => by
      viv_hsteps_nogrp
      exact hJi (0#64, 0#32, ()) mp ⟨sp.core.mrk, sp.scratch.work_stk1, by simp, Nat.zero_le _,
        hq0, fun _ ht => by simp at ht, hmp⟩)
    (fun Ji (qlen_i, i_c, ()) mi ⟨mrk_i, ws1_i, hi_le, hql_i, hqi_ok, hcov_i, hmi⟩ ihi => ?_)
  viv_hsteps_nogrp
  · have hi_lt : i_c.toNat < csz_bv.toNat := by dsimp only [csz_bv]; c0_bound
    have hi1 : (i_c + 1#32).toNat = i_c.toNat + 1 := by bv_omega
    have hli_idx : (src_cr.setWidth 64 + 3#64 + i_c.setWidth 64).toNat =
        src_cr.toNat + 3 + i_c.toNat := by bv_omega
    have hli_ar : (src_cr.setWidth 64 + 3#64 + i_c.setWidth 64).toNat < sp.core.arena.length := by
      omega
    let l_bv := sp.core.arena[(src_cr.setWidth 64 + 3#64 + i_c.setWidth 64).toNat]'hli_ar
    let lv_bv := l_bv >>> 1#32
    have hl_eq : l_bv = sp.core.arena[src_cr.toNat + 3 + i_c.toNat]'(by omega) := by
      dsimp only [l_bv]; simp only [hli_idx]
    have hl_mem : l_bv.toNat ∈ fullArenaClauseLits sp src_cr.toNat :=
      (mem_fullArenaClauseLitsCore_iff hsrc_bd).mpr
        ⟨i_c.toNat, by rw [← hcsz_eq]; exact hi_lt, congrArg BitVec.toNat hl_eq.symm⟩
    have hl_lt : l_bv.toNat < 2 * sp.core.cur_vars :=
      hw.arena.lits_lt src_cr.toNat hsrc_ref hsrc_ng l_bv.toNat hl_mem
    have hlv_val : lv_bv.toNat = l_bv.toNat / 2 := bv32_lshr1_toNat _
    have hlv_cv : lv_bv.toNat < sp.core.cur_vars := by rw [hlv_val]; omega
    have hlv_trl : ∃ m < sp.core.trail_end,
        (sp.core.trl[m]?.getD 0#32).toNat / 2 = lv_bv.toNat := by
      obtain ⟨m, hm_lt, hmeq⟩ :=
        (hw.vals_false_iff l_bv.toNat hl_lt).mp (hfal_src l_bv.toNat hl_mem)
      exact ⟨m, hm_lt, by rw [hmeq, fullInv_var_xor1, hlv_val]⟩
    viv_hsteps_nogrp
    refine wp_join_group (ts := [i64])
      (fun (qlen_i', ()) mo => ∃ (mrk_o : List (BitVec 8)) (ws1_o : List (BitVec 32)),
        qlen_i.toNat ≤ qlen_i'.toNat ∧ qlen_i'.toNat ≤ sp.core.cur_vars ∧
        (∀ k < qlen_i.toNat, ws1_o[k]? = ws1_i[k]?) ∧ VivQueueOk c sp mrk_o ws1_o qlen_i'.toNat ∧
        ((sp.core.lvl[lv_bv.toNat]?.getD 0#32).toNat = 0 ∨
          lv_bv.toNat ∈ (ws1_o.take qlen_i'.toNat).map BitVec.toNat) ∧
        (FullMem c { sp with
          core := { sp.core with mrk := mrk_o, lit_mark := lm1 }
          scratch := { sp.scratch with
            work_stk1 := ws1_o, ant_sz := 0xFFFFFFFFFFFFFFFF#64, res_sz := rsz_p } } ⋆ R) mo)
      (fun _ (qlen_i', ()) mo ⟨mrk_o, ws1_o, hq_io, hql_o, heq_o, hqo, hcov_lv, hmo⟩ => by
        rw [Blocks.get_here]; dsimp only
        viv_hsteps_nogrp
        have hws1_o_len : ws1_o.length = 2 * c.max_vars := hqo.2.1
        refine ihi (qlen_i', i_c + 1#32, ()) mo (by dsimp only; omega)
          ⟨mrk_o, ws1_o, by omega, hql_o, hqo, fun t ht => ?_, hmo⟩
        rcases (by omega : t < i_c.toNat ∨ t = i_c.toNat) with ht' | rfl
        · refine (hcov_i t ht').elim Or.inl fun hm' => Or.inr ?_
          obtain ⟨k, hk, hkeq⟩ := (mem_map_take_iff (by have := hqi_ok.2.1; omega)).mp hm'
          exact (mem_map_take_iff (by omega)).mpr ⟨k, by omega, by rw [heq_o k hk, hkeq]⟩
        · have hleq : (sp.core.arena[src_cr.toNat + 3 + i_c.toNat]?.getD 0#32).toNat / 2 =
              lv_bv.toNat := by
            rw [List.getElem?_eq_getElem (by omega), Option.getD_some, ← hl_eq, hlv_val]
          rw [hleq]; exact hcov_lv)
      (fun Jo hJo => by
        exact deduce_push_branch_wp Γ hspN.1 hqi_ok hlv_cv hlv_trl hmi
          fun qlen' mrk_o ws1_o mo hq_io hql_o heq_o hqo hcov_lv hmo =>
            hJo (qlen', ()) mo ⟨mrk_o, ws1_o, hq_io, hql_o, heq_o, hqo, hcov_lv, hmo⟩)
  · have hge_csz : csz_bv.toNat ≤ i_c.toNat := by dsimp only [csz_bv]; c0_bound
    have hi_eq : i_c.toNat = csz_bv.toNat := by omega
    have hcov_src : ∀ l ∈ fullArenaClauseLits sp src_cr.toNat,
        (sp.core.lvl[l / 2]?.getD 0#32).toNat = 0 ∨
        l / 2 ∈ (ws1_i.take qlen_i.toNat).map BitVec.toNat := fun l hl => by
      obtain ⟨t, ht, hlt⟩ := (mem_fullArenaClauseLitsCore_iff hsrc_bd).mp hl
      have ht_bd : src_cr.toNat + 3 + t < sp.core.arena.length := by omega
      rw [← hcsz_eq] at ht; have hc' := hcov_i t (by omega)
      rwa [List.getElem?_eq_getElem ht_bd, Option.getD_some, hlt] at hc'
    exact hJexit qlen_i mrk_i ws1_i mi hql_i hqi_ok (fun _ => by
      dsimp only [VivSeedOk]; rw [ite_eq_right (fun h => h himp_eq), ite_eq_right hct_ne1]
      have hsrc_c :
          (if sp.core.confl_type = 2#64 then sp.core.confl_ref.toNat else cref.toNat) =
          src_cr.toNat := hsrc_eq.symm
      rwa [hsrc_c]) hmi

theorem s13_deduce_phase1b_large_wp (Γ : Env)
    (hPromote : Γ.Has "full_viv_recompute_promote_fid" vivRecomputePromoteSpec)
    (hSubCl : Γ.Has "full_viv_subsumes_cl_m6" fullVivSubsumesClM6Spec)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState} {R : Mem 64 → Prop}
    {lm1 : List (BitVec 8)} {cref sz src_cr implied : Val i32} {m : Mem 64}
    {Q : Post [i32]} {X : XPost} {Jexit : Cont [i64]}
    (hspW : FullSparseInvW c F0 F_cur s)
    (hlm1_len : lm1.length = 2 * c.max_vars)
    (hlm1_dom : ∀ l < 2 * c.max_vars, lm1[l]?.getD 0#8 ≠ 0#8 →
      ∃ t < sz.toNat, (s.core.tmp[t]?.getD 0#32).toNat = l)
    (himp_eq : implied = 0xFFFFFFFF#32)
    (hct_ne1 : s.core.confl_type ≠ 1#64)
    (hconfl : implied = 0xFFFFFFFF#32 → FullVivConflictOk F_cur s ∨
      (s.core.confl_type = 0#64 ∧
        ∀ l ∈ fullArenaClauseLits s cref.toNat, s.core.vals[l]?.getD 0#8 = 0xFF#8))
    (hsrc_eq : src_cr.toNat =
      (if s.core.confl_type = 2#64 then s.core.confl_ref.toNat else cref.toNat))
    (hsrc_ref : src_cr.toNat ∈ fullArenaClauseRefs s)
    (hsrc_ng : fullArenaClauseGarb s src_cr.toNat = false)
    (_hcr_ref : cref.toNat ∈ fullArenaClauseRefs s)
    (hq0 : VivQueueOk c s s.core.mrk s.scratch.work_stk1 0)
    (hm : (FullMem c { s with
      core := { s.core with lit_mark := lm1 }
      scratch := { s.scratch with ant_sz := 0xFFFFFFFFFFFFFFFF#64, res_sz := 0#64 } } ⋆ R) m)
    (hJexit : ∀ (ar' mclr' : List (BitVec 32)) (qlen_v : Val i64) (mrk1 : List (BitVec 8))
        (ws1_1 : List (BitVec 32)) (asz1 rsz1 : BitVec 64) m_q,
      let s_n : FullState := { s with core := { s.core with arena := ar', min_clr := mclr' } }
      S13SparseInvNoMark c F0 F_cur s_n → S13ArPres s s_n →
      qlen_v.toNat ≤ s.core.cur_vars → VivQueueOk c s_n mrk1 ws1_1 qlen_v.toNat →
      (asz1 = 0xFFFFFFFFFFFFFFFF#64 →
        VivSeedOk s_n cref implied ws1_1 s.scratch.work_stk2 qlen_v.toNat 0 false) →
      S13SubRefOk s_n asz1 →
      (asz1 ≠ 0xFFFFFFFFFFFFFFFF#64 → VivDeduceSubWitness F_cur s_n sz.toNat) →
      (FullMem c { s_n with
        core := { s_n.core with mrk := mrk1, lit_mark := lm1 }
        scratch := { s_n.scratch with
          work_stk1 := ws1_1, ant_sz := asz1, res_sz := rsz1 } } ⋆ R) m_q →
      Jexit (qlen_v, ()) m_q) :
    wp Γ Q X (s13DeducePhase1bLargeExpr c.hdr (BitVec.ofNat 64 s.core.cur_vars)
      c.pMark c.pLevel c.pArena c.pWorkStk1 cref sz src_cr Jexit) m := by
  have hw := hspW.2.1; have hcl := hspW.1.core_ok; have hscl := hspW.1.scratch_ok
  have hcap := c.harena; have hmx := c.hmaxv; unfold dimacsBound at hcap hmx
  have hcv_le := hcl.cur_vars_le; have har_len := hcl.arena_len_arr
  have hmrk_len := hcl.mrk_len; have hws1_len := hscl.work_stk1_len
  have hws2_len := hscl.work_stk2_len
  have hsrc_wf := hw.arena.refs_wf src_cr.toNat hsrc_ref
  have hnoM : S13SparseInvNoMark c F0 F_cur s :=
    ⟨hspW.1, hw, hspW.2.2.2.1, hspW.2.2.2.2.1, hspW.2.2.2.2.2⟩
  have hsrc_0 : (src_cr.setWidth 64).toNat < s.core.arena.length := by
    have := hsrc_wf.1; have := hcl.arena_len_le; bv_omega
  have hfal_s : ∀ l ∈ fullArenaClauseLits s src_cr.toNat, s.core.vals[l]?.getD 0#8 = 0xFF#8 := by
    rcases hconfl himp_eq with (⟨hct1, _⟩ | ⟨hct2, _, _, hfal2⟩) | ⟨hct0, hfal0⟩
    · exact absurd hct1 hct_ne1
    · have : src_cr.toNat = s.core.confl_ref.toNat := by simpa [hct2] using hsrc_eq
      rwa [this]
    · have hne2 : s.core.confl_type ≠ 2#64 := by rw [hct0]; decide
      have : src_cr.toNat = cref.toNat := by simpa [hne2] using hsrc_eq
      rwa [this]
  dsimp only [s13DeducePhase1bLargeExpr, fvOp]
  refine wp_join_group (ts := [i64])
    (fun (qlen_v, ()) m_q => ∃ (ar' mclr' : List (BitVec 32)) (mrk1 : List (BitVec 8))
        (ws1_1 : List (BitVec 32)) (asz1 rsz1 : BitVec 64),
      let s_n : FullState := { s with core := { s.core with arena := ar', min_clr := mclr' } }
      S13SparseInvNoMark c F0 F_cur s_n ∧ S13ArPres s s_n ∧
      qlen_v.toNat ≤ s.core.cur_vars ∧ VivQueueOk c s_n mrk1 ws1_1 qlen_v.toNat ∧
      (asz1 = 0xFFFFFFFFFFFFFFFF#64 →
        VivSeedOk s_n cref implied ws1_1 s.scratch.work_stk2 qlen_v.toNat 0 false) ∧
      S13SubRefOk s_n asz1 ∧
      (asz1 ≠ 0xFFFFFFFFFFFFFFFF#64 → VivDeduceSubWitness F_cur s_n sz.toNat) ∧
      (FullMem c { s_n with
        core := { s_n.core with mrk := mrk1, lit_mark := lm1 }
        scratch := { s_n.scratch with work_stk1 := ws1_1, ant_sz := asz1, res_sz := rsz1 } }
        ⋆ R) m_q)
    (fun _ (qlen_v, ()) m_q ⟨ar', mclr', mrk1, ws1_1, asz1, rsz1,
        h1, h2, h3, h4, h5, h6, h7, hmq⟩ => by
      rw [Blocks.get_here]; dsimp only
      exact hJexit ar' mclr' qlen_v mrk1 ws1_1 asz1 rsz1 m_q h1 h2 h3 h4 h5 h6 h7 hmq)
    (fun _ hJ31 => by
      viv_hsteps_nogrp
      · refine wp_join_group (ts := [])
          (fun () m_as => ∃ (ar_p mclr_p : List (BitVec 32)) (asz_p rsz_p : BitVec 64),
            let s_p : FullState := { s with
              core := { s.core with arena := ar_p, min_clr := mclr_p } }
            S13SparseInvNoMark c F0 F_cur s_p ∧ S13ArPres s s_p ∧ S13SubRefOk s_p asz_p ∧
            (asz_p ≠ 0xFFFFFFFFFFFFFFFF#64 → VivDeduceSubWitness F_cur s_p sz.toNat) ∧
            (FullMem c { s_p with
              core := { s_p.core with lit_mark := lm1 }
              scratch := { s_p.scratch with ant_sz := asz_p, res_sz := rsz_p } } ⋆ R) m_as)
          (fun _ () m_as ⟨ar_p, mclr_p, asz_p, rsz_p, hsp_p, hpres_p, hsub_p, hw_p, hm_as⟩ => by
            rw [Blocks.get_here]; dsimp only
            let s_p : FullState := { s with
              core := { s.core with arena := ar_p, min_clr := mclr_p } }
            have href_p : src_cr.toNat ∈ fullArenaClauseRefs s_p := hpres_p.1 ▸ hsrc_ref
            have hng_p : fullArenaClauseGarb s_p src_cr.toNat = false :=
              (hpres_p.2 src_cr.toNat hsrc_ref).1.trans hsrc_ng
            have hq0_p : VivQueueOk c s_p s_p.core.mrk s_p.scratch.work_stk1 0 :=
              s13_vivQueue_ar_eq rfl rfl rfl rfl hq0
            have hlits_eq : fullArenaClauseLits s_p src_cr.toNat =
                fullArenaClauseLits s src_cr.toNat :=
              (hpres_p.2 src_cr.toNat hsrc_ref).2.2
            have hfal_p : ∀ l ∈ fullArenaClauseLits s_p src_cr.toNat,
                s_p.core.vals[l]?.getD 0#8 = 0xFF#8 := by simpa only [s_p, hlits_eq] using hfal_s
            refine wp_join_group (ts := [i64])
              (fun (qlen_v, ()) m_q => ∃ (mrk1 : List (BitVec 8)) (ws1_1 : List (BitVec 32)),
                qlen_v.toNat ≤ s.core.cur_vars ∧ VivQueueOk c s_p mrk1 ws1_1 qlen_v.toNat ∧
                (asz_p = 0xFFFFFFFFFFFFFFFF#64 →
                  VivSeedOk s_p cref implied ws1_1 s.scratch.work_stk2 qlen_v.toNat 0 false) ∧
                (FullMem c { s_p with
                  core := { s_p.core with mrk := mrk1, lit_mark := lm1 }
                  scratch := { s_p.scratch with
                    work_stk1 := ws1_1, ant_sz := asz_p, res_sz := rsz_p } } ⋆ R) m_q)
              (fun _ (qlen_v, ()) m_q ⟨mrk1, ws1_1, hq1, hq2, hq3, hmq⟩ => by
                rw [Blocks.get_here]; dsimp only
                exact hJ31 (qlen_v, ()) m_q ⟨ar_p, mclr_p, mrk1, ws1_1, asz_p, rsz_p,
                  hsp_p, hpres_p, hq1, hq2, hq3, hsub_p, hw_p, hmq⟩)
              (fun _ hJ38 => by
                viv_hsteps_nogrp
                · have hasz_eq : asz_p = 0xFFFFFFFFFFFFFFFF#64 := by c0_bound
                  subst hasz_eq
                  refine s13_phase1b_large_loop_wp Γ (sp := s_p) hsp_p himp_eq hct_ne1 hsrc_eq
                    href_p hng_p hlm1_len hfal_p hq0_p hm_as
                    fun qlen_v mrk1 ws1_1 mq hq1 hq2 hq3 hmq => ?_
                  exact hJ38 (qlen_v, ()) mq ⟨mrk1, ws1_1, hq1, hq2, (fun _ => hq3), hmq⟩
                · exact hJ38 (0#64, ()) m_as ⟨s_p.core.mrk, s_p.scratch.work_stk1,
                    Nat.zero_le _, hq0_p, (fun he => absurd he (by assumption)), hm_as⟩))
          (fun _ hJ37 => by
            viv_hsteps_nogrp
            · have hne_cr : src_cr ≠ cref := by c0_bound
              refine wp_join_group (ts := [])
                (fun () mp => ∃ (ar_p mclr_p : List (BitVec 32)) (rsz_p : BitVec 64),
                  let s_p : FullState := { s with
                    core := { s.core with arena := ar_p, min_clr := mclr_p } }
                  S13SparseInvNoMark c F0 F_cur s_p ∧ S13ArPres s s_p ∧
                  (FullMem c { s_p with
                    core := { s_p.core with lit_mark := lm1 }
                    scratch := { s_p.scratch with
                      ant_sz := 0xFFFFFFFFFFFFFFFF#64, res_sz := rsz_p } } ⋆ R) mp)
                (fun _ () mp ⟨ar_p, mclr_p, rsz_p, hsp_p, hpres_p, hm_p⟩ => by
                  rw [Blocks.get_here]; dsimp only
                  let s_p : FullState := { s with
                    core := { s.core with arena := ar_p, min_clr := mclr_p } }
                  have href_p : src_cr.toNat ∈ fullArenaClauseRefs s_p := hpres_p.1 ▸ hsrc_ref
                  have hng_p : fullArenaClauseGarb s_p src_cr.toNat = false :=
                    (hpres_p.2 src_cr.toNat hsrc_ref).1.trans hsrc_ng
                  have hlits_eq : fullArenaClauseLits s_p src_cr.toNat =
                      fullArenaClauseLits s src_cr.toNat :=
                    (hpres_p.2 src_cr.toNat hsrc_ref).2.2
                  refine wp_join_group (ts := [])
                    (fun () mf => ∃ asz_f : BitVec 64,
                      S13SubRefOk s_p asz_f ∧
                      (asz_f ≠ 0xFFFFFFFFFFFFFFFF#64 → VivDeduceSubWitness F_cur s_p sz.toNat) ∧
                      (FullMem c { s_p with
                        core := { s_p.core with lit_mark := lm1 }
                        scratch := { s_p.scratch with ant_sz := asz_f, res_sz := rsz_p } } ⋆ R) mf)
                    (fun _ () mf ⟨asz_f, hsr_f, hw_f, hmf⟩ => by
                      rw [Blocks.get_here]
                      exact hJ37 () mf ⟨ar_p, mclr_p, asz_f, rsz_p, hsp_p, hpres_p,
                        hsr_f, hw_f, hmf⟩)
                    (fun _ hJ40 => by
                      viv_call hSubCl
                      refine ⟨c, F0, F_cur, _, R, rfl,
                        s13_deduce_state_len hsp_p.1 hmrk_len hlm1_len hws1_len hws2_len,
                        s13_deduce_state_witness hsp_p.2.1, href_p, hng_p, hm_p,
                        fun ok hok => ?_⟩
                      viv_hsteps_nogrp
                      · have hsub_lits := hok (by assumption)
                        have hw_sub : VivDeduceSubWitness F_cur s_p sz.toNat := by
                          have hent_p := hsp_p.2.1.arena.entails src_cr.toNat href_p hng_p
                          refine cl_subWitness (s := s_p) hcv_le hent_p
                            (fun l hl => hsub_lits l hl)
                            (fun l hlm => ?_) (by simpa only [s_p] using hlm1_dom)
                          left; have hvf : s.core.vals[l]?.getD 0#8 = 0xFF#8 :=
                            hfal_s l (hlits_eq ▸ hlm)
                          dsimp only [s_p]; rw [hvf]; decide
                        exact hJ40 () _ ⟨src_cr.setWidth 64, s13_subRef_set_ref href_p hng_p,
                          fun _ => hw_sub, by simpa only [s_p] using by assumption⟩
                      · exact hJ40 () mp
                          ⟨0xFFFFFFFFFFFFFFFF#64, ⟨Or.inl rfl, fun h => absurd rfl h⟩,
                           fun h => absurd rfl h, hm_p⟩))
                (fun _ hJ39 => by
                  viv_hsteps_nogrp
                  · have hne0 : (s.core.arena[(src_cr.setWidth 64).toNat]'hsrc_0 &&& 0x400000#32)
                        ≠ 0#32 := by assumption
                    let s_r : FullState := { s with
                      core := { s.core with lit_mark := lm1 }
                      scratch := { s.scratch with
                        ant_sz := 0xFFFFFFFFFFFFFFFF#64, res_sz := 1#64 } }
                    have hsp_r : S13SparseInvNoMark c F0 F_cur s_r :=
                      s13_deduce_state_noMark hnoM hmrk_len hlm1_len hws1_len hws2_len
                    viv_call hPromote
                    refine ⟨c, F0, F_cur, s_r, R, rfl, hsp_r, hsrc_ref, hsrc_ng, hm,
                      fun ar' mclr' mp hsp_p hrefs_p hpres_p hmp => ?_⟩
                    let s_p : FullState := { s with
                      core := { s.core with arena := ar', min_clr := mclr' } }
                    have hsp_p' : S13SparseInvNoMark c F0 F_cur s_p :=
                      s13_deduce_state_noMark hsp_p hmrk_len hcl.lit_mark_len hws1_len hws2_len
                    exact hJ39 () mp ⟨ar', mclr', 1#64, hsp_p', ⟨hrefs_p, hpres_p⟩, hmp⟩
                  · exact hJ39 () m ⟨s.core.arena, s.core.min_clr, 0#64,
                      hnoM, s13ArPres_refl s, hm⟩)
            · exact hJ37 () m ⟨s.core.arena, s.core.min_clr, 0xFFFFFFFFFFFFFFFF#64, 0#64, hnoM,
                s13ArPres_refl s, ⟨Or.inl rfl, fun h => absurd rfl h⟩,
                fun h => absurd rfl h, hm⟩)
      · have h3 : BitVec.toNat (3 : BitVec 64) = 3 := rfl
        have harc_len := hcl.arena_len_le
        have h_le : (src_cr.toNat + 3) % 2 ^ 64 ≤ s.core.arena_len % 2 ^ 64 → False := by
          rw [← h3]; exact hc
        have := hsrc_wf.1
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h_le
        exact False.elim (h_le (by omega)))

end

end LeanQbe.T.Examples.Kissat.Proof.Vivify
