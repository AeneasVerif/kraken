/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S5VivifyBackboneProof1a
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.ControlComb

/-!
# Kissat Fidelity Step 13 Shard S5-B — Vivify Deduce (`Proof1b`)

Proves UNSAT-sound `Func.wp` (`XPost := False`, `0` SAT model proofs) for
`FullFidelityStep13S5VivifyBackbone.full_viv_deduce_m6_body` against `step13VivDeduceM6Spec`
(including `full_viv_recompute_promote_fid` calls and `S13SubRefOk` preservation, with every
theorem `<= 390` lines).
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep13S5

open Std Std.Sat Std.ExtHashMap Kraken.Bedrock2.Test
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Full
open FullVivTopTactics FullM6VivBackbone FullVivifyHelpers
open scoped FullArenaTactics FullVivTopTactics

private theorem c0_store_ws1_z_s13 {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (v : BitVec 32) (hi : 0 < s.scratch.work_stk1.length) (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 (c.pWorkStk1 + 0#64) ∧ (FullMem c { s with
      scratch := { s.scratch with work_stk1 := s.scratch.work_stk1.set 0 v } } ⋆ R)
      (storeMem m i32 (c.pWorkStk1 + 0#64) v) := by
  simpa using FullArenaTactics.store_full_work_stk1 v hi hm
private theorem c0_store_ws1_b_s13 {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (v : BitVec 32) (hi : 0 < s.scratch.work_stk1.length) (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 c.pWorkStk1 ∧ (FullMem c { s with
      scratch := { s.scratch with work_stk1 := s.scratch.work_stk1.set 0 v } } ⋆ R)
      (storeMem m i32 c.pWorkStk1 v) := by
  simpa using FullArenaTactics.store_full_work_stk1 v hi hm
private theorem c0_store_ws2_z_s13 {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (v : BitVec 32) (hi : 0 < s.scratch.work_stk2.length) (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 (c.pWorkStk2 + 0#64) ∧ (FullMem c { s with
      scratch := { s.scratch with work_stk2 := s.scratch.work_stk2.set 0 v } } ⋆ R)
      (storeMem m i32 (c.pWorkStk2 + 0#64) v) := by
  simpa using FullArenaTactics.store_full_work_stk2 v hi hm
private theorem c0_store_ws2_b_s13 {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (v : BitVec 32) (hi : 0 < s.scratch.work_stk2.length) (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 c.pWorkStk2 ∧ (FullMem c { s with
      scratch := { s.scratch with work_stk2 := s.scratch.work_stk2.set 0 v } } ⋆ R)
      (storeMem m i32 c.pWorkStk2 v) := by
  simpa using FullArenaTactics.store_full_work_stk2 v hi hm
attribute [local c0_store] c0_store_ws1_z_s13 c0_store_ws1_b_s13
  c0_store_ws2_z_s13 c0_store_ws2_b_s13

section DeduceProof

private theorem s13_subRef_ff (s : FullState) : S13SubRefOk s 0xFFFFFFFFFFFFFFFF#64 :=
  ⟨Or.inl rfl, fun h => absurd rfl h⟩
private theorem s13_subRef_fe (s : FullState) : S13SubRefOk s 0xFFFFFFFFFFFFFFFE#64 :=
  ⟨Or.inr (Or.inl rfl), fun _ h => absurd rfl h⟩
private theorem s13_fullMem_eq {c : FullCfg} {s1 s2 : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (h : s1 = s2) (hm : (FullMem c s1 ⋆ R) m) : (FullMem c s2 ⋆ R) m := h ▸ hm

private theorem s13_confl_pres {F_cur : List (List Nat)} {s sp : FullState}
    (hpres : S13ArPres s sp) (hcv : sp.core.cur_vars = s.core.cur_vars)
    (hvals : sp.core.vals = s.core.vals) (hct : sp.core.confl_type = s.core.confl_type)
    (hcr : sp.core.confl_ref = s.core.confl_ref) (hcl0 : sp.core.confl_lit0 = s.core.confl_lit0)
    (hcl1 : sp.core.confl_lit1 = s.core.confl_lit1) {cref_n : Nat}
    (h : FullVivifySpecs.FullVivConflictOk F_cur s ∨ (s.core.confl_type = 0#64 ∧
      ∀ l ∈ fullArenaClauseLits s cref_n, s.core.vals[l]?.getD 0#8 = 0xFF#8))
    (href_c : cref_n ∈ fullArenaClauseRefs s) :
    FullVivifySpecs.FullVivConflictOk F_cur sp ∨ (sp.core.confl_type = 0#64 ∧
      ∀ l ∈ fullArenaClauseLits sp cref_n, sp.core.vals[l]?.getD 0#8 = 0xFF#8) := by
  rcases h with (⟨h1, ha, hb, he, hva, hvb⟩ | ⟨h2, hr2, hg2, hf2⟩) | ⟨h0, hf0⟩
  · exact Or.inl (Or.inl ⟨by rwa [hct], by rwa [hcl0, hcv], by rwa [hcl1, hcv],
      by rwa [hcl0, hcl1], by rwa [hvals, hcl0], by rwa [hvals, hcl1]⟩)
  · refine Or.inl (Or.inr ⟨by rwa [hct], by rw [hcr, hpres.1]; exact hr2,
      by rw [hcr, (hpres.2 _ hr2).1]; exact hg2, fun l hl => ?_⟩)
    rw [hcr] at hl
    have h2 := (hpres.2 _ hr2).2.2; unfold fullArenaClauseLits at h2 hl; rw [h2] at hl
    rw [hvals]; exact hf2 l hl
  · refine Or.inr ⟨by rwa [hct], fun l hl => ?_⟩
    have h2 := (hpres.2 _ href_c).2.2; unfold fullArenaClauseLits at h2 hl; rw [h2] at hl
    rw [hvals]; exact hf0 l hl

private abbrev s13DeducePhase2Expr
    (h pVars pMark pLitMark pTmp pLevel pRsns pArena pWs1 pWs2 : Val i64)
    (cref sz implied : Val i32) (qlen : Val i64) (olen : Val i32) : Expr Val Cont [i32] :=
  fvOp32 (OpCode.add i64) (Arg.var h, Arg.imm 96, ()) fun p =>
  Expr.load i64 (Arg.var p.fst) fun pTrl =>
  fvOp32 (OpCode.add i64) (Arg.var h, Arg.imm 360, ()) fun p =>
  Expr.load i64 (Arg.var p.fst) fun pTpos =>
  Expr.group (sig := [[i64, i64, i32, .bool]]) (fun _ => Blocks.cons (fun pb =>
    s13DeduceClearExpr h pMark pLitMark pTmp pWs1 sz pb.fst pb.snd.snd.fst pb.snd.snd.snd.fst)
    Blocks.nil) fun Js_brk =>
  Expr.group (sig := [[i64, i64, i32, .bool]]) (fun Js => Blocks.cons (fun p_17 =>
    fvOp32 (OpCode.cmp .ult i64 .bool (by decide))
      (Arg.var p_17.snd.fst, Arg.var p_17.fst, ()) fun p =>
    Expr.jnz (Arg.var p.fst)
      (fvOp32 (OpCode.add i64) (Arg.var h, Arg.imm 1136, ()) fun p =>
       Expr.load i64 (Arg.var p.fst) fun ld =>
       fvOp32 (OpCode.cmp .eq i64 .bool (by decide))
         (Arg.var ld, Arg.imm 18446744073709551615, ()) fun p =>
       Expr.jnz (Arg.var p.fst)
         (fvOp32 (OpCode.mul i64) (Arg.var p_17.snd.fst, Arg.imm 4, ()) fun p =>
          fvOp32 (OpCode.add i64) (Arg.var pWs1, Arg.var p.fst, ()) fun p =>
          Expr.load i32 (Arg.var p.fst) fun v_bv =>
          fvOp32 (OpCode.add i64) (Arg.var p_17.snd.fst, Arg.imm 1, ()) fun p_qi1 =>
          fvOp32 (OpCode.zext 32 64) (Arg.var v_bv, ()) fun p =>
          fvOp32 (OpCode.mul i64) (Arg.var p.fst, Arg.imm 4, ()) fun p =>
          fvOp32 (OpCode.add i64) (Arg.var pRsns, Arg.var p.fst, ()) fun p =>
          Expr.load i32 (Arg.var p.fst) fun rsn_bv =>
          Expr.group (sig := [[i64, i32, .bool]]) (fun _ => Blocks.cons (fun p =>
            Expr.jump Js.fst (Arg.var p.fst, Arg.var p_qi1.fst, Arg.var p.snd.fst,
              Arg.var p.snd.snd.fst, ())) Blocks.nil) fun Js_r =>
          fvOp32 (OpCode.cmp .eq i32 .bool (by decide))
            (Arg.var rsn_bv, Arg.imm 4294967295, ()) fun p =>
          Expr.jnz (Arg.var p.fst)
            (fvOp32 (OpCode.zext 32 64) (Arg.var v_bv, ()) fun p =>
             fvOp32 (OpCode.mul i64) (Arg.var p.fst, Arg.imm 4, ()) fun p =>
             fvOp32 (OpCode.add i64) (Arg.var pTpos, Arg.var p.fst, ()) fun p =>
             Expr.load i32 (Arg.var p.fst) fun tp =>
             fvOp32 (OpCode.zext 32 64) (Arg.var tp, ()) fun p =>
             fvOp32 (OpCode.mul i64) (Arg.var p.fst, Arg.imm 4, ()) fun p =>
             fvOp32 (OpCode.add i64) (Arg.var pTrl, Arg.var p.fst, ()) fun p =>
             Expr.load i32 (Arg.var p.fst) fun tl =>
             Expr.group (sig := [[i32, .bool]]) (fun _ => Blocks.cons (fun p =>
               Expr.jump Js_r.fst (Arg.var p_17.fst, Arg.var p.fst, Arg.var p.snd.fst, ()))
               Blocks.nil) fun Js_d =>
             fvOp32 (OpCode.cmp .eq i32 .bool (by decide))
               (Arg.var tl, Arg.var implied, ()) fun p =>
             Expr.jnz (Arg.var p.fst)
               (Expr.jump Js_d.fst (Arg.var p_17.snd.snd.fst, Arg.imm (t := .bool) true, ()))
               (Expr.group (sig := [[i32]]) (fun _ => Blocks.cons (fun p =>
                 Expr.jump Js_d.fst (Arg.var p.fst, Arg.var p_17.snd.snd.snd.fst, ()))
                 Blocks.nil) fun Js_o =>
                fvOp32 (OpCode.zext 32 64) (Arg.var p_17.snd.snd.fst, ()) fun po =>
                fvOp32 (OpCode.cmp .ult i64 .bool (by decide))
                  (Arg.var po.fst, Arg.var pVars, ()) fun p =>
                Expr.jnz (Arg.var p.fst)
                  (fvOp32 (OpCode.zext 32 64) (Arg.var p_17.snd.snd.fst, ()) fun p =>
                   fvOp32 (OpCode.mul i64) (Arg.var p.fst, Arg.imm 4, ()) fun p =>
                   fvOp32 (OpCode.add i64) (Arg.var pWs2, Arg.var p.fst, ()) fun p =>
                   fvOp32 (OpCode.xor i32) (Arg.var tl, Arg.imm 1, ()) fun px =>
                   Expr.store (Arg.var px.fst) (Arg.var p.fst)
                     (fvOp32 (OpCode.add i32) (Arg.var p_17.snd.snd.fst, Arg.imm 1, ()) fun p =>
                      Expr.jump Js_o.fst (Arg.var p.fst, ())))
                  (Expr.jump Js_o.fst (Arg.var p_17.snd.snd.fst, ()))))
            (Expr.group (sig := [[i64]]) (fun _ => Blocks.cons (fun p =>
               Expr.jump Js_r.fst (Arg.var p.fst, Arg.var p_17.snd.snd.fst,
                 Arg.var p_17.snd.snd.snd.fst, ())) Blocks.nil) fun Js_g =>
             fvOp32 (OpCode.and i32) (Arg.var rsn_bv, Arg.imm 2147483648, ()) fun p =>
             fvOp32 (OpCode.cmp .ne i32 .bool (by decide)) (Arg.var p.fst, Arg.imm 0, ()) fun p =>
             Expr.jnz (Arg.var p.fst)
               (fvOp32 (OpCode.and i32) (Arg.var rsn_bv, Arg.imm 2147483647, ()) fun p_ot =>
                fvOp32 (OpCode.zext 32 64) (Arg.var v_bv, ()) fun p =>
                fvOp32 (OpCode.mul i64) (Arg.var p.fst, Arg.imm 4, ()) fun p =>
                fvOp32 (OpCode.add i64) (Arg.var pTpos, Arg.var p.fst, ()) fun p =>
                Expr.load i32 (Arg.var p.fst) fun tp =>
                fvOp32 (OpCode.zext 32 64) (Arg.var tp, ()) fun p =>
                fvOp32 (OpCode.mul i64) (Arg.var p.fst, Arg.imm 4, ()) fun p =>
                fvOp32 (OpCode.add i64) (Arg.var pTrl, Arg.var p.fst, ()) fun p =>
                Expr.load i32 (Arg.var p.fst) fun tl =>
                Expr.call "full_viv_subsumes_bin_m6" (as := [i64, i32, i32]) (bs := [.bool])
                  (Arg.var h, Arg.var tl, Arg.var p_ot.fst, ()) fun ok =>
                Expr.jnz (Arg.var ok.fst)
                  (fvOp32 (OpCode.add i64) (Arg.var h, Arg.imm 1136, ()) fun p =>
                   Expr.store (Arg.imm (t := i64) 18446744073709551614) (Arg.var p.fst)
                     (Expr.jump Js_brk.fst (Arg.var p_17.fst, Arg.var p_qi1.fst,
                       Arg.var p_17.snd.snd.fst, Arg.var p_17.snd.snd.snd.fst, ())))
                  (fvOp32 (OpCode.lshr i32) (Arg.var p_ot.fst, Arg.imm 1, ()) fun p_ov =>
                   Expr.group (sig := [[i64]]) (fun _ => Blocks.cons (fun p =>
                     Expr.jump Js_g.fst (Arg.var p.fst, ())) Blocks.nil) fun Js_b =>
                   deducePushExpr pVars pMark pLevel pWs1 p_ov.fst p_17.fst Js_b.fst))
               (Expr.group (sig := [[i64]]) (fun _ => Blocks.cons (fun p =>
                  Expr.jump Js_g.fst (Arg.var p.fst, ())) Blocks.nil) fun Js_lg =>
                s13DeduceLargeRsnExpr h pVars pMark pLevel pArena pWs1 cref sz rsn_bv v_bv
                  p_17.fst p_qi1.fst p_17.snd.snd.fst p_17.snd.snd.snd.fst
                  Js_brk.fst Js_lg.fst)))
         (Expr.jump Js_brk.fst (Arg.var p_17.fst, Arg.var p_17.snd.fst,
           Arg.var p_17.snd.snd.fst, Arg.var p_17.snd.snd.snd.fst, ())))
      (Expr.jump Js_brk.fst (Arg.var p_17.fst, Arg.var p_17.snd.fst,
        Arg.var p_17.snd.snd.fst, Arg.var p_17.snd.snd.snd.fst, ()))) Blocks.nil)
    fun Js => Expr.jump Js.fst
      (Arg.var qlen, Arg.imm 0, Arg.var olen, Arg.imm (t := .bool) false, ())

private theorem s13_viv_hsdi_mono {c : FullCfg} {s1 : FullState} {implied : Val i32}
    {ws1_b ws1_n : List (BitVec 32)} {qlen_c qlen' : Val i64}
    (hb_len : ws1_b.length = 2 * c.max_vars) (hn_len : ws1_n.length = 2 * c.max_vars)
    (hle : qlen_c.toNat ≤ qlen'.toNat) (hql : qlen'.toNat ≤ s1.core.cur_vars)
    (hcv : s1.core.cur_vars ≤ c.max_vars)
    (heq : ∀ j < qlen_c.toNat, ws1_n[j]? = ws1_b[j]?)
    (hpre : implied ≠ 0xFFFFFFFF#32 →
      (s1.core.lvl[implied.toNat / 2]?.getD 0#32).toNat = 0 ∨
      implied.toNat / 2 ∈ (ws1_b.take qlen_c.toNat).map BitVec.toNat) :
    implied ≠ 0xFFFFFFFF#32 →
      (s1.core.lvl[implied.toNat / 2]?.getD 0#32).toNat = 0 ∨
      implied.toNat / 2 ∈ (ws1_n.take qlen'.toNat).map BitVec.toNat := fun hne =>
  (hpre hne).elim Or.inl fun hm' => Or.inr (by
    obtain ⟨k, hk, hkeq⟩ := (mem_map_take_iff (by omega)).mp hm'
    exact (mem_map_take_iff (by omega)).mpr ⟨k, by omega, by rw [heq k hk, hkeq]⟩)

private theorem s13_deduce_phase2_wp (Γ : Env)
    (hPromote : ∀ a m Q X, step13VivRecomputePromoteSpec a m Q X →
      Γ "full_viv_recompute_promote_fid" [i64, i32] [] a m Q X)
    (hSubBin : ∀ a m Q X, fullVivSubsumesBinM6Spec a m Q X →
      Γ "full_viv_subsumes_bin_m6" [i64, i32, i32] [.bool] a m Q X)
    (hSubCl : ∀ a m Q X, fullVivSubsumesClM6Spec a m Q X →
      Γ "full_viv_subsumes_cl_m6" [i64, i32, i32] [.bool] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s1 : FullState}
    {R : Mem 64 → Prop} {mrk1 lm1 : List (BitVec 8)} {ws1_1 ws2_1 : List (BitVec 32)}
    {asz1 rsz1 : BitVec 64} {qlen_v : Val i64} {cref sz implied olen_v : Val i32}
    {mp : Mem 64} {Q : Post [i32]} {X : XPost}
    (hspW : S13SparseInvNoMark c F0 F_cur s1)
    (href : cref.toNat ∈ fullArenaClauseRefs s1) (hng : fullArenaClauseGarb s1 cref.toNat = false)
    (hsz_le : sz.toNat ≤ c.max_vars)
    (htmp_lt : ∀ k < sz.toNat, (s1.core.tmp[k]?.getD 0#32).toNat < 2 * s1.core.cur_vars)
    (hconfl : implied = 0xFFFFFFFF#32 →
      FullVivifySpecs.FullVivConflictOk F_cur s1 ∨
      (s1.core.confl_type = 0#64 ∧
        ∀ l ∈ fullArenaClauseLits s1 cref.toNat, s1.core.vals[l]?.getD 0#8 = 0xFF#8))
    (himp : implied ≠ 0xFFFFFFFF#32 →
      implied.toNat < 2 * s1.core.cur_vars ∧ s1.core.vals[implied.toNat]?.getD 0#8 = 1#8)
    (hlm1_len : lm1.length = 2 * c.max_vars)
    (hlm1_dom : ∀ l < 2 * c.max_vars, lm1[l]?.getD 0#8 ≠ 0#8 →
      ∃ t < sz.toNat, (s1.core.tmp[t]?.getD 0#32).toNat = l)
    (hws2_1 : ws2_1.length = 2 * c.max_vars) (hql1 : qlen_v.toNat ≤ s1.core.cur_vars)
    (hq1 : VivQueueOk c s1 mrk1 ws1_1 qlen_v.toNat)
    (ho1 : VivOutOk s1 implied ws1_1 ws2_1 0 olen_v.toNat false)
    (hsd1 : asz1 = 0xFFFFFFFFFFFFFFFF#64 →
      VivSeedOk s1 cref implied ws1_1 ws2_1 qlen_v.toNat olen_v.toNat false)
    (hsub1 : S13SubRefOk s1 asz1)
    (hsdi1 : implied ≠ 0xFFFFFFFF#32 →
      (s1.core.lvl[implied.toNat / 2]?.getD 0#32).toNat = 0 ∨
      implied.toNat / 2 ∈ (ws1_1.take qlen_v.toNat).map BitVec.toNat)
    (hmp : (FullMem c { s1 with
      core := { s1.core with mrk := mrk1, lit_mark := lm1 }
      scratch := { s1.scratch with
        work_stk1 := ws1_1, work_stk2 := ws2_1, ant_sz := asz1, res_sz := rsz1 } } ⋆ R) mp)
    (hQ : ∀ olen ar' mclr' mrk' lm' ws1' ws2' asz' rsz' m',
      let s' : FullState := { s1 with
        core := { s1.core with arena := ar', min_clr := mclr', mrk := mrk', lit_mark := lm' }
        scratch := { s1.scratch with
          work_stk1 := ws1', work_stk2 := ws2', ant_sz := asz', res_sz := rsz' } }
      FullSparseInvW c F0 F_cur s' → S13ArPres s1 s' → S13SubRefOk s' asz' →
      (asz' = 0xFFFFFFFFFFFFFFFF#64 → olen ≠ 0xFFFFFFFF#32 →
        olen.toNat ≤ s1.core.cur_vars ∧
        (∀ i < olen.toNat, (ws2'[i]?.getD 0#32).toNat < 2 * s1.core.cur_vars) ∧
        ((ws2'.take olen.toNat).map fun x => x.toNat / 2).Nodup ∧
        (cnfOfClauses F_cur).EntailsClause
          (cnfClause ((ws2'.take olen.toNat).map BitVec.toNat))) →
      (FullMem c s' ⋆ R) m' → Q (olen, ()) m') :
    wp Γ Q X (s13DeducePhase2Expr c.hdr (BitVec.ofNat 64 s1.core.cur_vars)
      c.pMark c.pLitMark c.pTmp c.pLevel c.pReason c.pArena c.pWorkStk1 c.pWorkStk2
      cref sz implied qlen_v olen_v) mp := by
  have hw1 := hspW.2.1; have hcl1 := hspW.1.core_ok; have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcv_le := hcl1.cur_vars_le; have hte_le := hcl1.trail_end_le
  have hrsns_len := hcl1.rsns_len; have htrl_len := hcl1.trl_len; have htp_len := hcl1.trail_pos_len
  dsimp only [s13DeducePhase2Expr, fvOp32]; fvt_to_group
  refine wp_join_group (ts := [i64, i64, i32, .bool]) (fun (qlen_c, qi_c, olen_c, taut_c, ()) mb =>
    ∃ (ar_b mclr_b : List (BitVec 32)) (mrk_b : List (BitVec 8))
      (ws1_b ws2_b : List (BitVec 32)) (asz_b rsz_b : BitVec 64),
      let sb : FullState := { s1 with
        core := { s1.core with arena := ar_b, min_clr := mclr_b, mrk := mrk_b, lit_mark := lm1 }
        scratch := { s1.scratch with
          work_stk1 := ws1_b, work_stk2 := ws2_b, ant_sz := asz_b, res_sz := rsz_b } }
      S13SparseInvNoMark c F0 F_cur sb ∧ S13ArPres s1 sb ∧
      ws2_b.length = 2 * c.max_vars ∧ qi_c.toNat ≤ qlen_c.toNat ∧
      qlen_c.toNat ≤ s1.core.cur_vars ∧ VivQueueOk c s1 mrk_b ws1_b qlen_c.toNat ∧
      (asz_b = 0xFFFFFFFFFFFFFFFF#64 →
        qi_c.toNat = qlen_c.toNat ∧
        VivClosedOk s1 implied ws1_b ws2_b qi_c.toNat qlen_c.toNat olen_c.toNat taut_c ∧
        VivOutOk s1 implied ws1_b ws2_b qi_c.toNat olen_c.toNat taut_c ∧
        VivSeedOk s1 cref implied ws1_b ws2_b qlen_c.toNat olen_c.toNat taut_c) ∧
      S13SubRefOk sb asz_b ∧ (implied ≠ 0xFFFFFFFF#32 →
        (s1.core.lvl[implied.toNat / 2]?.getD 0#32).toNat = 0 ∨
        implied.toNat / 2 ∈ (ws1_b.take qlen_c.toNat).map BitVec.toNat) ∧ (FullMem c sb ⋆ R) mb)
    (fun _ ⟨qlen_c, qi_c, olen_c, taut_c, ⟨⟩⟩ mb ⟨ar_b, mclr_b, mrk_b, ws1_b, ws2_b, asz_b, rsz_b,
        hsp_b, hpres_b, hws2_b, hqi_le, hql_le, hqb, hfin_b, hsub_b, hsdi_b, hmb⟩ => by
      rw [Blocks.get_here]
      refine s13_deduce_clear_wp Γ hsp_b hsz_le htmp_lt (s13_vivQueue_ar_eq rfl rfl rfl rfl hqb)
        hlm1_len hlm1_dom hws2_b hsub_b hmb
        fun ret mrk' lm' asz' mf hsp' hsub' ht_eq hf_eq hasz_eq hmf =>
          hQ ret ar_b mclr_b mrk' lm' ws1_b ws2_b asz' rsz_b mf hsp'
            (s13ArPres_with_fields hpres_b) hsub' (fun hasz' hne_ff => by
              by_cases hasz_f : asz_b = 0xFFFFFFFFFFFFFFFF#64
              · obtain ⟨hqi_eq, hcb_imp, hob, hsdb_imp⟩ := hfin_b hasz_f
                have htf : taut_c = false := by
                  cases htc : taut_c with
                  | false => rfl | true => exact absurd (ht_eq htc) hne_ff
                have hret_eq : ret = olen_c := hf_eq htf
                rw [hret_eq]; rw [hqi_eq, htf] at hcb_imp hob; rw [htf] at hsdb_imp
                have hent := deduce_phase2_sound hw1 hqb hcv_le href hng hcb_imp hsdb_imp
                  himp hconfl hsdi_b
                have ho := hob rfl
                exact ⟨ho.1, ho.2.1,
                  by simpa only [List.map_map, Function.comp_def] using ho.2.2.1, hent⟩
              · cases htc : taut_c with
                | true => exact absurd (ht_eq htc) hne_ff
                | false => exact absurd ((hasz_eq htc).symm.trans hasz') hasz_f) hmf)
    (fun Jbrk hJbrk => ?_)
  refine wp_loop_inv (ts := [i64, i64, i32, .bool])
    (fun (qlen_c, qi_c, olen_c, taut_c, ()) mb =>
      ∃ (ar_b mclr_b : List (BitVec 32)) (mrk_b : List (BitVec 8))
        (ws1_b ws2_b : List (BitVec 32)) (asz_b rsz_b : BitVec 64),
        let sb : FullState := { s1 with
          core := { s1.core with arena := ar_b, min_clr := mclr_b, mrk := mrk_b, lit_mark := lm1 }
          scratch := { s1.scratch with
            work_stk1 := ws1_b, work_stk2 := ws2_b, ant_sz := asz_b, res_sz := rsz_b } }
        S13SparseInvNoMark c F0 F_cur sb ∧ S13ArPres s1 sb ∧
        ws2_b.length = 2 * c.max_vars ∧ qi_c.toNat ≤ qlen_c.toNat ∧
        qlen_c.toNat ≤ s1.core.cur_vars ∧
        VivQueueOk c s1 mrk_b ws1_b qlen_c.toNat ∧
        (asz_b = 0xFFFFFFFFFFFFFFFF#64 →
          VivClosedOk s1 implied ws1_b ws2_b qi_c.toNat qlen_c.toNat olen_c.toNat taut_c) ∧
        VivOutOk s1 implied ws1_b ws2_b qi_c.toNat olen_c.toNat taut_c ∧
        (asz_b = 0xFFFFFFFFFFFFFFFF#64 →
          VivSeedOk s1 cref implied ws1_b ws2_b qlen_c.toNat olen_c.toNat taut_c) ∧
        S13SubRefOk sb asz_b ∧
        (implied ≠ 0xFFFFFFFF#32 →
          (s1.core.lvl[implied.toNat / 2]?.getD 0#32).toNat = 0 ∨
          implied.toNat / 2 ∈ (ws1_b.take qlen_c.toNat).map BitVec.toNat) ∧
        (FullMem c sb ⋆ R) mb)
    (fun (_, qi_c, _, _, ()) _ => s1.core.cur_vars - qi_c.toNat) ?_ ?_
  · intro Jb hJb; fvt_steps
    have hsp_b0 := s13_deduce_state_noMark (asz' := asz1) (rsz' := rsz1)
      hspW hq1.1 hlm1_len hq1.2.1 hws2_1
    have hsub_b0 : S13SubRefOk _ asz1 :=
      s13_subRef_of_pres ⟨rfl, fun _ _ => ⟨rfl, rfl, rfl⟩⟩ hsub1
    exact hJb (qlen_v, 0#64, olen_v, false, ()) mp
      ⟨s1.core.arena, s1.core.min_clr, mrk1, ws1_1, ws2_1, asz1, rsz1, hsp_b0,
       s13ArPres_refl _, hws2_1, by simp, hql1, hq1,
       (fun _ _ h => absurd h (Nat.not_lt_zero _)), ho1, hsd1, hsub_b0, hsdi1, hmp⟩
  · rintro Jb ⟨qlen_c, qi_c, olen_c, taut_c, ⟨⟩⟩ mb
      ⟨ar_b, mclr_b, mrk_b, ws1_b, ws2_b, asz_b, rsz_b, hsp_b, hpres_b, hws2_b, hqi_le, hql_le,
       hqb, hcb_imp, hob, hsdb_imp, hsub_b, hsdi_b, hmb⟩ ihb
    let sb : FullState := { s1 with
      core := { s1.core with arena := ar_b, min_clr := mclr_b, mrk := mrk_b, lit_mark := lm1 }
      scratch := { s1.scratch with
        work_stk1 := ws1_b, work_stk2 := ws2_b, ant_sz := asz_b, res_sz := rsz_b } }
    have hwb := hsp_b.2.1; have hclb := hsp_b.1.core_ok
    fvt_step; fvt_step
    · fvt_step; fvt_step
      · have hqi_lt : qi_c.toNat < qlen_c.toNat := by c0_bound
        have hasz_ff : asz_b = 0xFFFFFFFFFFFFFFFF#64 := by c0_bound
        have hcb := hcb_imp hasz_ff; have hsdb := hsdb_imp hasz_ff
        have hqi1 : (qi_c + 1#64).toNat = qi_c.toNat + 1 := by bv_omega
        have hqi_ws1 : qi_c.toNat < ws1_b.length := by have := hqb.2.1; omega
        let v_bv := ws1_b[qi_c.toNat]'hqi_ws1
        have hv_lt : v_bv.toNat < s1.core.cur_vars := by
          have := hqb.2.2.2.1 qi_c.toNat hqi_lt
          rwa [List.getElem?_eq_getElem hqi_ws1, Option.getD_some] at this
        have hv_rsn : v_bv.toNat < s1.core.rsns.length := by omega
        have hv_tp : v_bv.toNat < s1.core.trail_pos.length := by omega
        have hv_lvl : 0 < (s1.core.lvl[v_bv.toNat]?.getD 0#32).toNat ∧
            ∃ idx < s1.core.trail_end, (s1.core.trl[idx]?.getD 0#32).toNat / 2 = v_bv.toNat := by
          have := hqb.2.2.2.2.2.1 qi_c.toNat hqi_lt
          rwa [List.getElem?_eq_getElem hqi_ws1, Option.getD_some] at this
        obtain ⟨idx0, hidx0, htrl0⟩ := hv_lvl.2
        have htp_eq : (s1.core.trail_pos[v_bv.toNat]'hv_tp).toNat = idx0 := by
          have h := hw1.trail_pos_inv idx0 hidx0
          rw [htrl0, List.getElem?_eq_getElem hv_tp, Option.getD_some] at h; exact h
        have htp_trl : (s1.core.trail_pos[v_bv.toNat]'hv_tp).toNat < s1.core.trl.length := by omega
        fvt_to_group
        refine wp_join_group (ts := [i64, i32, .bool])
          (fun (qlen', olen', taut', ()) mn =>
            ∃ (ar_n mclr_n : List (BitVec 32)) (mrk_n : List (BitVec 8))
              (ws1_n ws2_n : List (BitVec 32)) (asz_n rsz_n : BitVec 64),
              let sn : FullState := { s1 with
                core := { s1.core with
                  arena := ar_n, min_clr := mclr_n, mrk := mrk_n, lit_mark := lm1 }
                scratch := { s1.scratch with
                  work_stk1 := ws1_n, work_stk2 := ws2_n, ant_sz := asz_n, res_sz := rsz_n } }
              S13SparseInvNoMark c F0 F_cur sn ∧ S13ArPres s1 sn ∧
              ws2_n.length = 2 * c.max_vars ∧ qi_c.toNat + 1 ≤ qlen'.toNat ∧
              qlen'.toNat ≤ s1.core.cur_vars ∧ VivQueueOk c s1 mrk_n ws1_n qlen'.toNat ∧
              (asz_n = 0xFFFFFFFFFFFFFFFF#64 →
                VivClosedOk s1 implied ws1_n ws2_n (qi_c.toNat + 1) qlen'.toNat olen'.toNat taut') ∧
              VivOutOk s1 implied ws1_n ws2_n (qi_c.toNat + 1) olen'.toNat taut' ∧
              (asz_n = 0xFFFFFFFFFFFFFFFF#64 →
                VivSeedOk s1 cref implied ws1_n ws2_n qlen'.toNat olen'.toNat taut') ∧
              S13SubRefOk sn asz_n ∧
              (implied ≠ 0xFFFFFFFF#32 →
                (s1.core.lvl[implied.toNat / 2]?.getD 0#32).toNat = 0 ∨
                implied.toNat / 2 ∈ (ws1_n.take qlen'.toNat).map BitVec.toNat) ∧
              (FullMem c sn ⋆ R) mn)
          (fun _ ⟨qlen', olen', taut', ⟨⟩⟩ mn
              ⟨ar_n, mclr_n, mrk_n, ws1_n, ws2_n, asz_n, rsz_n, hsp_n, hpres_n, hws2_n, hqi1_le,
               hql_n, hqn, hcn, hon, hsdn, hsub_n, hsdin, hmn⟩ => by
            fvt_steps
            exact ihb (qlen', qi_c + 1#64, olen', taut', ()) mn (by dsimp only; omega)
              ⟨ar_n, mclr_n, mrk_n, ws1_n, ws2_n, asz_n, rsz_n, hsp_n, hpres_n, hws2_n,
               by omega, hql_n, hqn, fun ha => by rw [hqi1]; exact hcn ha,
               by rwa [hqi1], hsdn, hsub_n, hsdin, hmn⟩)
          (fun Jn hJn => ?_)
        fvt_to_group
        · -- Decision: `rsn == 0xFFFFFFFFu`
          have hrsn_ff : s1.core.rsns[v_bv.toNat]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 := by
            rw [List.getElem?_eq_getElem hv_rsn, Option.getD_some]; c0_bound
          have htrl0' : (s1.core.trl[idx0]?.getD 0#32).toNat / 2 =
              (ws1_b[qi_c.toNat]?.getD 0#32).toNat := by
            rw [List.getElem?_eq_getElem hqi_ws1, Option.getD_some]; exact htrl0
          have hrsn_ff' : s1.core.rsns[(ws1_b[qi_c.toNat]?.getD 0#32).toNat]?.getD 0xFFFFFFFF#32 =
              0xFFFFFFFF#32 := by
            rwa [List.getElem?_eq_getElem hqi_ws1, Option.getD_some]
          have hv64_tp : (BitVec.setWidth 64 (s1.core.trail_pos[
              (BitVec.setWidth 64 (ws1_b[qi_c.toNat]'hqi_ws1)).toNat]'(by
                rw [bv32_setWidth64_toNat]; exact hv_tp))).toNat = idx0 := by
            rw [bv32_setWidth64_toNat]
            have h := hw1.trail_pos_inv idx0 hidx0
            rw [htrl0, List.getElem?_eq_getElem hv_tp, Option.getD_some] at h
            simp only [bv32_setWidth64_toNat]; exact h
          have htl_eq : s1.core.trl[(BitVec.setWidth 64 (s1.core.trail_pos[
              (BitVec.setWidth 64 (ws1_b[qi_c.toNat]'hqi_ws1)).toNat]'(by
                rw [bv32_setWidth64_toNat]; exact hv_tp))).toNat]'(by rw [hv64_tp]; omega) =
              s1.core.trl[idx0]?.getD 0#32 := by
            rw [List.getElem?_eq_getElem (by omega), Option.getD_some]; congr 1
          rw [htl_eq]
          refine wp_unroll_group fun Js_d hJs_d => ?_
          dsimp only [Prod.fst]
          refine s13_deduce_phase2_dec_wp Γ hw1 hcv_le hws2_b hqb hcb hob hsdb himp
            hqi_lt hidx0 htrl0' hrsn_ff' rfl hmb
            fun olen' taut' md ws2_d hws2_d hcd hod hsdd hmd => hJs_d _ md (by
              fvt_steps
              exact hJn (qlen_c, olen', taut', ()) md
                ⟨ar_b, mclr_b, mrk_b, ws1_b, ws2_d, asz_b, rsz_b,
                 s13_deduce_state_noMark (asz' := asz_b) (rsz' := rsz_b)
                   hsp_b hqb.1 hlm1_len hqb.2.1 hws2_d,
                 s13ArPres_with_fields hpres_b, hws2_d, by omega, hql_le, hqb, fun _ => hcd, hod,
                 fun _ => hsdd, s13_subRef_of_pres ⟨rfl, fun _ _ => ⟨rfl, rfl, rfl⟩⟩ hsub_b,
                 hsdi_b, hmd⟩)
        · -- Non-decision (`rsn != 0xFFFFFFFFu`)
          have hv_set64 : (v_bv.setWidth 64).toNat = v_bv.toNat := by bv_omega
          let rsn_bv := s1.core.rsns[(v_bv.setWidth 64).toNat]'(by rw [hv_set64]; exact hv_rsn)
          have hrsn_ne : rsn_bv ≠ 0xFFFFFFFF#32 := by dsimp only [rsn_bv]; c0_bound
          have hrsn_get : s1.core.rsns[(ws1_b[qi_c.toNat]?.getD 0#32).toNat]?.getD 0xFFFFFFFF#32 =
              rsn_bv := by
            dsimp only [rsn_bv, v_bv]
            rw [List.getElem?_eq_getElem hqi_ws1, Option.getD_some,
              List.getElem?_eq_getElem hv_rsn, Option.getD_some]
            congr 1
          have htrl0' : (s1.core.trl[idx0]?.getD 0#32).toNat / 2 =
              (ws1_b[qi_c.toNat]?.getD 0#32).toNat := by
            rw [List.getElem?_eq_getElem hqi_ws1, Option.getD_some]; exact htrl0
          refine wp_join_group (ts := [i64])
            (fun (qlen', ()) mr =>
              ∃ (ar_r mclr_r : List (BitVec 32)) (mrk_r : List (BitVec 8))
                (ws1_r : List (BitVec 32)) (asz_r rsz_r : BitVec 64),
                let sr : FullState := { s1 with
                  core := { s1.core with
                    arena := ar_r, min_clr := mclr_r, mrk := mrk_r, lit_mark := lm1 }
                  scratch := { s1.scratch with
                    work_stk1 := ws1_r, work_stk2 := ws2_b, ant_sz := asz_r, res_sz := rsz_r } }
                S13SparseInvNoMark c F0 F_cur sr ∧ S13ArPres s1 sr ∧
                qi_c.toNat + 1 ≤ qlen'.toNat ∧ qlen'.toNat ≤ s1.core.cur_vars ∧
                VivQueueOk c s1 mrk_r ws1_r qlen'.toNat ∧
                (asz_r = 0xFFFFFFFFFFFFFFFF#64 →
                  VivClosedOk s1 implied ws1_r ws2_b (qi_c.toNat + 1) qlen'.toNat olen_c.toNat
                    taut_c) ∧
                VivOutOk s1 implied ws1_r ws2_b (qi_c.toNat + 1) olen_c.toNat taut_c ∧
                (asz_r = 0xFFFFFFFFFFFFFFFF#64 →
                  VivSeedOk s1 cref implied ws1_r ws2_b qlen'.toNat olen_c.toNat taut_c) ∧
                S13SubRefOk sr asz_r ∧
                (implied ≠ 0xFFFFFFFF#32 →
                  (s1.core.lvl[implied.toNat / 2]?.getD 0#32).toNat = 0 ∨
                  implied.toNat / 2 ∈ (ws1_r.take qlen'.toNat).map BitVec.toNat) ∧
                (FullMem c sr ⋆ R) mr)
            (fun _ ⟨qlen', ⟨⟩⟩ mr
                ⟨ar_r, mclr_r, mrk_r, ws1_r, asz_r, rsz_r, hsp_r, hpres_r, hq1_r, hql_r,
                 hqr, hcr, hor, hsdr, hsub_r, hsdir, hmr⟩ => by
              fvt_steps
              exact hJn (qlen', olen_c, taut_c, ()) mr
                ⟨ar_r, mclr_r, mrk_r, ws1_r, ws2_b, asz_r, rsz_r, hsp_r, hpres_r, hws2_b,
                 hq1_r, hql_r, hqr, hcr, hor, hsdr, hsub_r, hsdir, hmr⟩)
            (fun Jr hJr => ?_)
          fvt_to_group
          · -- Binary reason: `(rsn & PW_BIN_FLAG) != 0`
            have hbin : (rsn_bv &&& 0x80000000#32) ≠ 0#32 := by c0_bound
            have hri := hw1.reason_inv idx0 hidx0 (by rwa [← hrsn_get, ← htrl0'] at hrsn_ne)
            rw [htrl0', hrsn_get, ite_eq_left hbin] at hri
            obtain ⟨hot_lt, _, m_bin, hm_lt_bin, hmeq_bin, _⟩ := hri
            let ot_bv := rsn_bv &&& 0x7FFFFFFF#32
            let ov_bv := ot_bv >>> 1#32
            have hov_val : ov_bv.toNat = ot_bv.toNat / 2 := bv32_lshr1_toNat _
            have hov_cv : ov_bv.toNat < s1.core.cur_vars := by
              dsimp only [ot_bv] at hov_val; rw [hov_val]; omega
            have hov_trl : ∃ m < s1.core.trail_end,
                (s1.core.trl[m]?.getD 0#32).toNat / 2 = ov_bv.toNat :=
              ⟨m_bin, by omega, by rw [hmeq_bin, fullInv_var_xor1, hov_val]⟩
            have htl_lt :
                (s1.core.trl[(s1.core.trail_pos[v_bv.toNat]'hv_tp).toNat]'htp_trl).toNat <
                  2 * s1.core.cur_vars := by
              have h := hw1.trail_lits_lt idx0 hidx0
              rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at h
              simpa only [htp_eq] using h
            fvt_steps; c0_call hSubBin
            refine ⟨c, _, R, rfl,
              s13_deduce_state_len hsp_b.1 hqb.1 hlm1_len hqb.2.1 hws2_b,
              htl_lt, hot_lt, hmb, fun ok => ?_⟩
            c0_hsplit
            · fvt_steps
              exact hJbrk (qlen_c, qi_c + 1#64, olen_c, taut_c, ()) _
                ⟨ar_b, mclr_b, mrk_b, ws1_b, ws2_b, 0xFFFFFFFFFFFFFFFE#64, rsz_b,
                 s13_deduce_state_noMark hsp_b hqb.1 hlm1_len hqb.2.1 hws2_b,
                 s13ArPres_with_fields hpres_b, hws2_b, by omega, hql_le, hqb,
                 (fun h => by cases h), s13_subRef_fe _, hsdi_b, by assumption⟩
            · fvt_to_group; refine wp_unroll_group fun Js_b hJs_b => ?_
              have hlen_sb : sb.LengthsOk c :=
                s13_deduce_state_len hsp_b.1 hqb.1 hlm1_len hqb.2.1 hws2_b
              have hqb_sb : VivQueueOk c sb mrk_b ws1_b qlen_c.toNat :=
                s13_vivQueue_ar_eq rfl rfl rfl rfl hqb
              exact s13_push_branch_step (s := sb) hlen_sb hqb_sb hov_cv hov_trl hmb
                fun qlen' mrk_n ws1_n mn hq_le hql_n heq_n hqn hcov_b hmn => hJs_b _ mn (by
                  have hql_n' : qlen'.toNat ≤ s1.core.cur_vars := hql_n
                  have hws1_n_len : ws1_n.length = 2 * c.max_vars := hqn.2.1
                  have heq_qi : ws1_n[qi_c.toNat]? = ws1_b[qi_c.toNat]? := heq_n qi_c.toNat hqi_lt
                  have htrl0_n : (s1.core.trl[idx0]?.getD 0#32).toNat / 2 =
                      (ws1_n[qi_c.toNat]?.getD 0#32).toNat := by rwa [heq_qi]
                  have hcb1 := vivClosed_mono_q hcb (by omega) hq_le
                    (by have := hqb.2.1; omega) (by rw [hws1_n_len]; omega) heq_n
                  have hcb2 := vivClosed_step_bin hcb1 hw1.trail_vars_nodup hidx0 htrl0_n
                    (by rw [heq_qi, hrsn_get]; exact hrsn_ne) (by rw [heq_qi, hrsn_get]; exact hbin)
                    (by rw [heq_qi, hrsn_get, ← hov_val]; exact hcov_b)
                  have hob1 := vivOut_mono_qlen (qlen := qlen_c.toNat) hob (by omega)
                    (by have := hqb.2.1; omega) (by rw [hws1_n_len]; omega) heq_n
                  have hob2 := vivOut_mono_qi_len (qlen := qlen'.toNat) hob1 (by omega)
                    (by rw [hws1_n_len]; omega)
                    (Or.inr (Or.inr (by rw [heq_qi, hrsn_get]; exact hrsn_ne)))
                  have hsd1 := vivSeed_mono_q hsdb hq_le (by rw [hws1_n_len]; omega)
                    (by have := hqb.2.1; omega) heq_n
                  fvt_steps
                  exact hJr (qlen', ()) mn
                    ⟨ar_b, mclr_b, mrk_n, ws1_n, asz_b, rsz_b,
                     s13_deduce_state_noMark hsp_b hqn.1 hlm1_len hqn.2.1 hws2_b,
                     s13ArPres_with_fields hpres_b, by omega, hql_n',
                     s13_vivQueue_ar_eq rfl rfl rfl rfl hqn, fun _ => hcb2, hob2, fun _ => hsd1,
                     s13_subRef_of_pres ⟨rfl, fun _ _ => ⟨rfl, rfl, rfl⟩⟩ hsub_b,
                     s13_viv_hsdi_mono (by have := hqb.2.1; omega) hws1_n_len hq_le hql_n'
                       hcv_le heq_n hsdi_b, hmn⟩)
          · -- Large reason: `(rsn & PW_BIN_FLAG) == 0`
            obtain ⟨hpres_b1, hpres_b2⟩ := hpres_b
            have hlg : (rsn_bv &&& 0x80000000#32) = 0#32 := by c0_bound
            have hri := hw1.reason_inv idx0 hidx0 (by rwa [← hrsn_get, ← htrl0'] at hrsn_ne)
            rw [htrl0', hrsn_get, ite_eq_right (by simp [hlg])] at hri
            obtain ⟨href_r, hng_r, hlits_r⟩ := hri
            have hv_get : v_bv = ws1_b[qi_c.toNat]?.getD 0#32 := by
              dsimp only [v_bv]; rw [List.getElem?_eq_getElem hqi_ws1, Option.getD_some]
            have href_rb : rsn_bv.toNat ∈ fullArenaClauseRefs sb := hpres_b1.symm ▸ href_r
            have hng_rb : fullArenaClauseGarb sb rsn_bv.toNat = false :=
              (hpres_b2 _ href_r).1.trans hng_r
            have hlits_rb : ∀ q ∈ fullArenaClauseLitsCore sb.core rsn_bv.toNat,
                q = (sb.core.trl[idx0]?.getD 0#32).toNat ∨
                ∃ m < idx0, (sb.core.trl[m]?.getD 0#32).toNat = q ^^^ 1 ∧
                  (sb.core.lvl[q / 2]?.getD 0#32).toNat ≤
                    (sb.core.lvl[(sb.core.trl[idx0]?.getD 0#32).toNat / 2]?.getD 0#32).toNat :=
              fun q hq => by
                have h2 := (hpres_b2 _ href_r).2.2; unfold fullArenaClauseLits at h2
                dsimp only [sb]; have h := hlits_r q (h2 ▸ hq); rwa [← hv_get, ← htrl0] at h
            refine wp_unroll_group fun Js_lg hJs_lg => ?_
            exact s13_deduce_large_rsn_wp (s := sb) (qi1 := qi_c + 1#64) (olen := olen_c)
              (taut := taut_c) Γ hPromote hSubCl hsp_b
              (s13_vivQueue_ar_eq rfl rfl rfl rfl hqb) hlm1_len hws2_b hsub_b
              href_rb hng_rb hidx0 htrl0 hlits_rb hmb
              (fun qlen' ar_l mclr_l mrk_l ws1_l asz_l rsz_l mlg
                  hsp_l hpres_l hq_le_l hql_l heq_l hql_ok hsub_l hcov_l hmlg => hJs_lg _ mlg (by
                have hql_l' : qlen'.toNat ≤ s1.core.cur_vars := hql_l
                have hws1_l_len : ws1_l.length = 2 * c.max_vars := hql_ok.2.1
                have heq_qi : ws1_l[qi_c.toNat]? = ws1_b[qi_c.toNat]? := heq_l qi_c.toNat hqi_lt
                have htrl0_n : (s1.core.trl[idx0]?.getD 0#32).toNat / 2 =
                    (ws1_l[qi_c.toNat]?.getD 0#32).toNat := by rwa [heq_qi]
                have hcb1 := vivClosed_mono_q hcb (by omega) hq_le_l
                  (by have := hqb.2.1; omega) (by rw [hws1_l_len]; omega) heq_l
                have hcb2 := vivClosed_step_large hcb1 hw1.trail_vars_nodup hidx0 htrl0_n
                  (by rw [heq_qi, hrsn_get]; exact hrsn_ne) (by rw [heq_qi, hrsn_get]; exact hlg)
                  (by rw [heq_qi, hrsn_get, ← hv_get]; intro q hq hne
                      have h2 := (hpres_b2 _ href_r).2.2
                      unfold fullArenaClauseLits at h2; exact hcov_l q (h2.symm ▸ hq) hne)
                  (by rw [heq_qi, hrsn_get]; intro q hq
                      exact (hlits_r q hq).imp id fun ⟨m, hm', heq, _⟩ => ⟨m, hm', heq⟩)
                have hob1 := vivOut_mono_qlen (qlen := qlen_c.toNat) hob (by omega)
                  (by have := hqb.2.1; omega) (by rw [hws1_l_len]; omega) heq_l
                have hob2 := vivOut_mono_qi_len (qlen := qlen'.toNat) hob1 (by omega)
                  (by rw [hws1_l_len]; omega)
                  (Or.inr (Or.inr (by rw [heq_qi, hrsn_get]; exact hrsn_ne)))
                have hsd1 := vivSeed_mono_q hsdb hq_le_l (by rw [hws1_l_len]; omega)
                  (by have := hqb.2.1; omega) heq_l
                fvt_steps
                exact hJr (qlen', ()) mlg
                  ⟨ar_l, mclr_l, mrk_l, ws1_l, asz_l, rsz_l, hsp_l,
                   s13ArPres_trans ⟨hpres_b1, hpres_b2⟩ (s13ArPres_with_fields hpres_l), by omega,
                   hql_l', s13_vivQueue_ar_eq rfl rfl rfl rfl hql_ok, fun _ => hcb2, hob2,
                   fun _ => hsd1, hsub_l, s13_viv_hsdi_mono (by have := hqb.2.1; omega)
                     hws1_l_len hq_le_l hql_l' hcv_le heq_l hsdi_b, hmlg⟩))
              (fun ar_k mclr_k rsz_k mb hsp_k hpres_k hsub_k hmb' => by
                have hne_ff : rsn_bv.setWidth 64 ≠ 0xFFFFFFFFFFFFFFFF#64 := by
                  have := (hw1.arena.refs_wf rsn_bv.toNat href_r).1
                  have := hcl1.arena_len_le
                  have hlt : (rsn_bv.setWidth 64).toNat < 2 ^ 32 := by
                    rw [show (rsn_bv.setWidth 64).toNat = rsn_bv.toNat by bv_omega]
                    exact rsn_bv.isLt
                  intro he; rw [he] at hlt; simp at hlt
                exact hJbrk (qlen_c, qi_c + 1#64, olen_c, taut_c, ()) mb
                  ⟨ar_k, mclr_k, mrk_b, ws1_b, ws2_b, rsn_bv.setWidth 64, rsz_k, hsp_k,
                   s13ArPres_trans ⟨hpres_b1, hpres_b2⟩ (s13ArPres_with_fields hpres_k), hws2_b,
                   by omega, hql_le, hqb, (fun h => absurd h hne_ff), hsub_k, hsdi_b, hmb'⟩)
      · -- Early exit: `ant_sz ≠ 0xFFFFFFFFFFFFFFFF` -> jump to `Js_brk`
        have hasz_ne : asz_b ≠ 0xFFFFFFFFFFFFFFFF#64 := by c0_bound
        exact hJbrk (qlen_c, qi_c, olen_c, taut_c, ()) mb
          ⟨ar_b, mclr_b, mrk_b, ws1_b, ws2_b, asz_b, rsz_b, hsp_b, hpres_b, hws2_b, hqi_le,
           hql_le, hqb, (fun h => absurd h hasz_ne), hsub_b, hsdi_b, hmb⟩
    · -- Exit `qi == qlen`: jump to `Js_brk`
      have hqi_eq : qi_c.toNat = qlen_c.toNat := by c0_bound
      exact hJbrk (qlen_c, qi_c, olen_c, taut_c, ()) mb
        ⟨ar_b, mclr_b, mrk_b, ws1_b, ws2_b, asz_b, rsz_b, hsp_b, hpres_b, hws2_b, hqi_le,
         hql_le, hqb, (fun hasz => ⟨hqi_eq, hcb_imp hasz, hob, hsdb_imp hasz⟩), hsub_b, hsdi_b,
         hmb⟩

private abbrev s13DeducePhase1bBinExpr (h pVars pMark pLevel pWs1 : Val i64) (J : Cont [i64]) :
    Expr Val Cont [i32] :=
  fvOp32 (OpCode.add i64) (Arg.var h, Arg.imm 536, ()) fun p =>
  Expr.load i64 (Arg.var p.fst) fun ld => fvOp32 (OpCode.trunc 64 32) (Arg.var ld, ()) fun p_19 =>
  fvOp32 (OpCode.add i64) (Arg.var h, Arg.imm 544, ()) fun p =>
  Expr.load i64 (Arg.var p.fst) fun ld => fvOp32 (OpCode.trunc 64 32) (Arg.var ld, ()) fun p_21 =>
  Expr.group (sig := [[i64]]) (fun _ => Blocks.cons (fun p =>
    Expr.jump J (Arg.var p.fst, ())) Blocks.nil) fun Js_top =>
  Expr.call "full_viv_subsumes_bin_m6" (as := [i64, i32, i32]) (bs := [.bool])
    (Arg.var h, Arg.var p_19.fst, Arg.var p_21.fst, ()) fun p_22 =>
  Expr.jnz (Arg.var p_22.fst)
    (fvOp32 (OpCode.add i64) (Arg.var h, Arg.imm 1136, ()) fun p =>
     Expr.store (Arg.imm (t := i64) 18446744073709551614) (Arg.var p.fst)
       (Expr.jump Js_top.fst (Arg.imm 0, ())))
    (Expr.group (sig := [[i64]]) (fun _ => Blocks.cons (fun p =>
       Expr.group (sig := [[i64]]) (fun _ => Blocks.cons (fun p =>
         Expr.jump Js_top.fst (Arg.var p.fst, ())) Blocks.nil) fun Js =>
       fvOp32 (OpCode.lshr i32) (Arg.var p_21.fst, Arg.imm 1, ()) fun p_22 =>
       fvOp32 (OpCode.zext 32 64) (Arg.var p_22.fst, ()) fun p_23 =>
       fvOp32 (OpCode.mul i64) (Arg.var p_23.fst, Arg.imm 4, ()) fun p_24 =>
       fvOp32 (OpCode.add i64) (Arg.var pLevel, Arg.var p_24.fst, ()) fun p_25 =>
       Expr.load i32 (Arg.var p_25.fst) fun ld =>
       fvOp32 (OpCode.cmp .ugt i32 .bool (by decide)) (Arg.var ld, Arg.imm 0, ()) fun p_26 =>
       Expr.jnz (Arg.var p_26.fst)
         (fvOp32 (OpCode.lshr i32) (Arg.var p_21.fst, Arg.imm 1, ()) fun p_27 =>
          fvOp32 (OpCode.zext 32 64) (Arg.var p_27.fst, ()) fun p_28 =>
          fvOp32 (OpCode.add i64) (Arg.var pMark, Arg.var p_28.fst, ()) fun p_29 =>
          Expr.load i8 (Arg.var p_29.fst) fun ld =>
          fvOp32 (OpCode.trunc 32 8) (Arg.imm 0, ()) fun p_30 =>
          fvOp32 (OpCode.zext 8 32) (Arg.var ld, ()) fun p_31 =>
          fvOp32 (OpCode.zext 8 32) (Arg.var p_30.fst, ()) fun p_32 =>
          fvOp32 (OpCode.cmp .eq i32 .bool (by decide))
            (Arg.var p_31.fst, Arg.var p_32.fst, ()) fun p_33 =>
          Expr.jnz (Arg.var p_33.fst)
            (fvOp32 (OpCode.cmp .ult i64 .bool (by decide))
               (Arg.var p.fst, Arg.var pVars, ()) fun p_34 =>
             Expr.jnz (Arg.var p_34.fst)
               (fvOp32 (OpCode.lshr i32) (Arg.var p_21.fst, Arg.imm 1, ()) fun p_35 =>
                fvOp32 (OpCode.zext 32 64) (Arg.var p_35.fst, ()) fun p_36 =>
                fvOp32 (OpCode.add i64) (Arg.var pMark, Arg.var p_36.fst, ()) fun p_37 =>
                fvOp32 (OpCode.trunc 32 8) (Arg.imm 1, ()) fun p_38 =>
                Expr.store (Arg.var p_38.fst) (Arg.var p_37.fst)
                  (fvOp32 (OpCode.mul i64) (Arg.var p.fst, Arg.imm 4, ()) fun p_39 =>
                   fvOp32 (OpCode.add i64) (Arg.var pWs1, Arg.var p_39.fst, ()) fun p_40 =>
                   fvOp32 (OpCode.lshr i32) (Arg.var p_21.fst, Arg.imm 1, ()) fun p_41 =>
                   Expr.store (Arg.var p_41.fst) (Arg.var p_40.fst)
                     (fvOp32 (OpCode.add i64) (Arg.var p.fst, Arg.imm 1, ()) fun p =>
                      Expr.jump Js.fst (Arg.var p.fst, ()))))
               (Expr.jump Js.fst (Arg.var p.fst, ())))
            (Expr.jump Js.fst (Arg.var p.fst, ())))
         (Expr.jump Js.fst (Arg.var p.fst, ()))) Blocks.nil) fun Js =>
     fvOp32 (OpCode.lshr i32) (Arg.var p_19.fst, Arg.imm 1, ()) fun p =>
     fvOp32 (OpCode.zext 32 64) (Arg.var p.fst, ()) fun p =>
     fvOp32 (OpCode.mul i64) (Arg.var p.fst, Arg.imm 4, ()) fun p =>
     fvOp32 (OpCode.add i64) (Arg.var pLevel, Arg.var p.fst, ()) fun p =>
     Expr.load i32 (Arg.var p.fst) fun ld =>
     fvOp32 (OpCode.cmp .ugt i32 .bool (by decide)) (Arg.var ld, Arg.imm 0, ()) fun p =>
     Expr.jnz (Arg.var p.fst)
       (fvOp32 (OpCode.lshr i32) (Arg.var p_19.fst, Arg.imm 1, ()) fun p =>
        fvOp32 (OpCode.zext 32 64) (Arg.var p.fst, ()) fun p =>
        fvOp32 (OpCode.add i64) (Arg.var pMark, Arg.var p.fst, ()) fun p =>
        Expr.load i8 (Arg.var p.fst) fun ld =>
        fvOp32 (OpCode.trunc 32 8) (Arg.imm 0, ()) fun p =>
        fvOp32 (OpCode.zext 8 32) (Arg.var ld, ()) fun p_22 =>
        fvOp32 (OpCode.zext 8 32) (Arg.var p.fst, ()) fun p =>
        fvOp32 (OpCode.cmp .eq i32 .bool (by decide))
          (Arg.var p_22.fst, Arg.var p.fst, ()) fun p =>
        Expr.jnz (Arg.var p.fst)
          (fvOp32 (OpCode.cmp .ult i64 .bool (by decide))
             (Arg.imm 0, Arg.var pVars, ()) fun p =>
           Expr.jnz (Arg.var p.fst)
             (fvOp32 (OpCode.lshr i32) (Arg.var p_19.fst, Arg.imm 1, ()) fun p =>
              fvOp32 (OpCode.zext 32 64) (Arg.var p.fst, ()) fun p =>
              fvOp32 (OpCode.add i64) (Arg.var pMark, Arg.var p.fst, ()) fun p =>
              fvOp32 (OpCode.trunc 32 8) (Arg.imm 1, ()) fun p_23 =>
              Expr.store (Arg.var p_23.fst) (Arg.var p.fst)
                (fvOp32 (OpCode.mul i64) (Arg.imm 0, Arg.imm 4, ()) fun p =>
                 fvOp32 (OpCode.add i64) (Arg.var pWs1, Arg.var p.fst, ()) fun p =>
                 fvOp32 (OpCode.lshr i32) (Arg.var p_19.fst, Arg.imm 1, ()) fun p_24 =>
                 Expr.store (Arg.var p_24.fst) (Arg.var p.fst)
                   (fvOp32 (OpCode.add i64) (Arg.imm 0, Arg.imm 1, ()) fun p =>
                    Expr.jump Js.fst (Arg.var p.fst, ()))))
             (Expr.jump Js.fst (Arg.imm 0, ())))
          (Expr.jump Js.fst (Arg.imm 0, ())))
       (Expr.jump Js.fst (Arg.imm 0, ())))

private theorem s13_deduce_phase1b_bin_wp (Γ : Env)
    (hSubBin : ∀ a m Q X, fullVivSubsumesBinM6Spec a m Q X →
      Γ "full_viv_subsumes_bin_m6" [i64, i32, i32] [.bool] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState} {R : Mem 64 → Prop}
    {lm1 : List (BitVec 8)} {cref implied : Val i32} {m : Mem 64} {Q : Post [i32]} {X : XPost}
    {Jq : Cont [i64]}
    (hspW : FullSparseInvW c F0 F_cur s) (hlm1_len : lm1.length = 2 * c.max_vars)
    (himp_eq : implied = 0xFFFFFFFF#32) (hct1 : s.core.confl_type = 1#64)
    (hconfl : implied = 0xFFFFFFFF#32 →
      FullVivifySpecs.FullVivConflictOk F_cur s ∨
      (s.core.confl_type = 0#64 ∧
        ∀ l ∈ fullArenaClauseLits s cref.toNat, s.core.vals[l]?.getD 0#8 = 0xFF#8))
    (hq0 : VivQueueOk c s s.core.mrk s.scratch.work_stk1 0)
    (hm : (FullMem c { s with
      core := { s.core with lit_mark := lm1 }
      scratch := { s.scratch with ant_sz := 0xFFFFFFFFFFFFFFFF#64, res_sz := 0#64 } } ⋆ R) m)
    (hJq : ∀ (qlen_v : Val i64) (mrk1 : List (BitVec 8)) (ws1_1 : List (BitVec 32))
        (asz1 rsz1 : BitVec 64) m_q,
      let s_q : FullState := { s with
        core := { s.core with mrk := mrk1, lit_mark := lm1 }
        scratch := { s.scratch with work_stk1 := ws1_1, ant_sz := asz1, res_sz := rsz1 } }
      qlen_v.toNat ≤ s.core.cur_vars → VivQueueOk c s mrk1 ws1_1 qlen_v.toNat →
      (asz1 = 0xFFFFFFFFFFFFFFFF#64 →
        VivSeedOk s cref implied ws1_1 s.scratch.work_stk2 qlen_v.toNat 0 false) →
      S13SubRefOk s_q asz1 → (FullMem c s_q ⋆ R) m_q → Jq (qlen_v, ()) m_q) :
    wp Γ Q X (s13DeducePhase1bBinExpr c.hdr (BitVec.ofNat 64 s.core.cur_vars)
      c.pMark c.pLevel c.pWorkStk1 Jq) m := by
  have hw := hspW.2.1; have hcl := hspW.1.core_ok; have hscl := hspW.1.scratch_ok
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcv_le := hcl.cur_vars_le; have hmrk_len := hcl.mrk_len; have hlvl_len := hcl.lvl_len
  have hws1_len := hscl.work_stk1_len; have hws2_len := hscl.work_stk2_len
  rcases hconfl himp_eq with (⟨_, ha_lt, hb_lt, _, hva, hvb⟩ | ⟨hct2, _⟩) | ⟨hct0, _⟩
  · have ha32 : s.core.confl_lit0.toNat < 2 ^ 32 := by omega
    have hb32 : s.core.confl_lit1.toNat < 2 ^ 32 := by omega
    let a_bv := s.core.confl_lit0.truncate 32; let b_bv := s.core.confl_lit1.truncate 32
    have ha_eq : a_bv.toNat = s.core.confl_lit0.toNat := bv64_trunc32_toNat ha32
    have hb_eq : b_bv.toNat = s.core.confl_lit1.toNat := bv64_trunc32_toNat hb32
    have hav_cv : (a_bv >>> 1#32).toNat < s.core.cur_vars := by rw [bv32_lshr1_toNat, ha_eq]; omega
    have hbv_cv : (b_bv >>> 1#32).toNat < s.core.cur_vars := by rw [bv32_lshr1_toNat, hb_eq]; omega
    have ha_trl : ∃ m < s.core.trail_end,
        (s.core.trl[m]?.getD 0#32).toNat / 2 = (a_bv >>> 1#32).toNat := by
      obtain ⟨m, hm_lt, hmeq⟩ := (hw.vals_false_iff _ ha_lt).mp hva
      exact ⟨m, hm_lt, by rw [hmeq, fullInv_var_xor1, bv32_lshr1_toNat, ha_eq]⟩
    have hb_trl : ∃ m < s.core.trail_end,
        (s.core.trl[m]?.getD 0#32).toNat / 2 = (b_bv >>> 1#32).toNat := by
      obtain ⟨m, hm_lt, hmeq⟩ := (hw.vals_false_iff _ hb_lt).mp hvb
      exact ⟨m, hm_lt, by rw [hmeq, fullInv_var_xor1, bv32_lshr1_toNat, hb_eq]⟩
    dsimp only [s13DeducePhase1bBinExpr, fvOp32]; fvt_steps; c0_call hSubBin
    refine ⟨c, _, R, rfl, s13_deduce_state_len hspW.1 hmrk_len hlm1_len hws1_len hws2_len,
      by rw [ha_eq]; exact ha_lt, by rw [hb_eq]; exact hb_lt, hm, fun ok => ?_⟩
    c0_hsplit
    · fvt_steps; exact hJq 0#64 s.core.mrk s.scratch.work_stk1 0xFFFFFFFFFFFFFFFE#64 0#64 _
        (Nat.zero_le _) hq0 (fun h => by cases h) (s13_subRef_fe _) (by assumption)
    · refine wp_join_group (ts := [i64])
        (fun (qa, ()) ma => ∃ (mrk_a : List (BitVec 8)) (ws1_a : List (BitVec 32)),
          qa.toNat ≤ s.core.cur_vars ∧ VivQueueOk c s mrk_a ws1_a qa.toNat ∧
          ((s.core.lvl[s.core.confl_lit0.toNat / 2]?.getD 0#32).toNat = 0 ∨
            s.core.confl_lit0.toNat / 2 ∈ (ws1_a.take qa.toNat).map BitVec.toNat) ∧
          (FullMem c { s with
            core := { s.core with mrk := mrk_a, lit_mark := lm1 }
            scratch := { s.scratch with
              work_stk1 := ws1_a, ant_sz := 0xFFFFFFFFFFFFFFFF#64, res_sz := 0#64 } } ⋆ R) ma)
          (fun _ ⟨qa, ⟨⟩⟩ ma ⟨mrk_a, ws1_a, hqa_le, hqa, hcov_a, hma⟩ => by
          fvt_to_group
          have hbv_lvl : (b_bv >>> 1#32).toNat < s.core.lvl.length := by omega
          have hbv_mrk : (b_bv >>> 1#32).toNat < mrk_a.length := by rw [hqa.1]; omega
          have hbv_idx : (b_bv >>> 1#32).toNat = s.core.confl_lit1.toNat % 4294967296 / 2 := by
            rw [bv32_lshr1_toNat, hb_eq, Nat.mod_eq_of_lt (by omega)]
          have hbv_lvl' : s.core.confl_lit1.toNat % 4294967296 / 2 < s.core.lvl.length := by
            rw [← hbv_idx]; exact hbv_lvl
          have hbv_mrk' : s.core.confl_lit1.toNat % 4294967296 / 2 < mrk_a.length := by
            rw [← hbv_idx]; exact hbv_mrk
          have hqa_ws1 : qa.toNat < ws1_a.length := by have := hqa.2.1; omega
          have hfin : ∀ (qb : Val i64) mrk_b ws1_b mb, qa.toNat ≤ qb.toNat →
              qb.toNat ≤ s.core.cur_vars → (∀ j < qa.toNat, ws1_b[j]? = ws1_a[j]?) →
              VivQueueOk c s mrk_b ws1_b qb.toNat →
              ((s.core.lvl[s.core.confl_lit1.toNat / 2]?.getD 0#32).toNat = 0 ∨
                s.core.confl_lit1.toNat / 2 ∈ (ws1_b.take qb.toNat).map BitVec.toNat) →
              (FullMem c
                { s with
                  core := { s.core with mrk := mrk_b, lit_mark := lm1 }
                  scratch := { s.scratch with
                    work_stk1 := ws1_b, ant_sz := 0xFFFFFFFFFFFFFFFF#64
                    res_sz := 0#64 } } ⋆ R) mb →
              Jq (qb, ()) mb :=
            fun qb mrk_b ws1_b mb _ hqb_le heq_ab hqb hcov_b hmb => by
              fvt_steps
              exact hJq qb mrk_b ws1_b 0xFFFFFFFFFFFFFFFF#64 0#64 mb hqb_le hqb (fun _ _ => by
                simp only [himp_eq, ne_eq, not_true_eq_false, ↓reduceIte, hct1]
                refine ⟨hcov_a.elim Or.inl fun hm' => Or.inr ?_, hcov_b⟩
                obtain ⟨k, hk, hkeq⟩ := (mem_map_take_iff (by have := hqa.2.1; omega)).mp hm'
                exact (mem_map_take_iff (by have := hqb.2.1; omega)).mpr
                  ⟨k, by omega, by rw [heq_ab k hk, hkeq]⟩) (s13_subRef_ff _) hmb
          fvt_steps
          · have hlp : 0 < (s.core.lvl[(b_bv >>> 1#32).toNat]?.getD 0#32).toNat := by
              rw [List.getElem?_eq_getElem hbv_lvl, Option.getD_some]
              have hlv : s.core.lvl[(b_bv >>> 1#32).toNat]'hbv_lvl =
                  s.core.lvl[s.core.confl_lit1.toNat % 4294967296 / 2]'hbv_lvl' := by congr 1
              rw [hlv]; c0_bound
            have hm0_b : mrk_a[(b_bv >>> 1#32).toNat]?.getD 0#8 = 0#8 := by
              rw [List.getElem?_eq_getElem hbv_mrk, Option.getD_some]
              have hmk : mrk_a[(b_bv >>> 1#32).toNat]'hbv_mrk =
                  mrk_a[s.core.confl_lit1.toNat % 4294967296 / 2]'hbv_mrk' := by congr 1
              rw [hmk]; exact (bv8_zext32_eq0_iff _).mp (by assumption)
            have hqa1 : (qa + 1#64).toNat = qa.toNat + 1 := by bv_omega
            obtain ⟨_, hqb_ok, hpre_b, _⟩ := push_queue_step hqa hcv_le hbv_cv hlp hm0_b hb_trl
            have hb_mod : (b_bv >>> 1#32).toNat % 2 ^ 64 = (b_bv >>> 1#32).toNat :=
              Nat.mod_eq_of_lt (by omega)
            have hm_b_ok : (FullMem c { s with
                core := { s.core with mrk := mrk_a.set (b_bv >>> 1#32).toNat 1#8, lit_mark := lm1 }
                scratch := { s.scratch with
                  work_stk1 := ws1_a.set qa.toNat (b_bv >>> 1#32), ant_sz := 0xFFFFFFFFFFFFFFFF#64
                  res_sz := 0#64 } } ⋆ R) _ :=
              s13_fullMem_eq (by simp only [hbv_idx]; rfl) (by assumption)
            exact hfin (qa + 1#64) _ _ _ (by omega) (by omega) hpre_b
              (by simpa [hqa1, hb_mod] using hqb_ok) (Or.inr (by
                rw [hqa1]; exact (mem_map_take_iff (by simp [hqa.2.1]; omega)).mpr
                  ⟨qa.toNat, by omega, by
                    rw [List.getElem?_set_self hqa_ws1, Option.getD_some]
                    change (b_bv >>> 1#32).toNat = _; rw [bv32_lshr1_toNat, hb_eq]⟩)) hm_b_ok
          · have hm0_b : mrk_a[(b_bv >>> 1#32).toNat]?.getD 0#8 = 0#8 := by
              rw [List.getElem?_eq_getElem hbv_mrk, Option.getD_some]
              have hmk : mrk_a[(b_bv >>> 1#32).toNat]'hbv_mrk =
                  mrk_a[s.core.confl_lit1.toNat % 4294967296 / 2]'hbv_mrk' := by congr 1
              rw [hmk]; exact (bv8_zext32_eq0_iff _).mp (by assumption)
            have hlt := push_queue_lt hqa hcv_le hbv_cv hm0_b
            have hle : s.core.cur_vars % 2 ^ 64 ≤ qa.toNat := by c0_bound
            rw [Nat.mod_eq_of_lt (by omega)] at hle; omega
          · have hne0 : mrk_a[(b_bv >>> 1#32).toNat]'hbv_mrk ≠ 0#8 := fun h => by
              have hmk : mrk_a[(b_bv >>> 1#32).toNat]'hbv_mrk =
                  mrk_a[s.core.confl_lit1.toNat % 4294967296 / 2]'hbv_mrk' := by congr 1
              rw [hmk] at h
              exact (by assumption :
                (mrk_a[s.core.confl_lit1.toNat % 4294967296 / 2]'hbv_mrk').setWidth 32 ≠ 0#32)
                ((bv8_zext32_eq0_iff _).mpr h)
            have hm1 : mrk_a[(b_bv >>> 1#32).toNat]?.getD 0#8 = 1#8 := by
              rcases hqa.2.2.2.2.2.2.2.1 _ hbv_cv with h0 | h1
              · rw [List.getElem?_eq_getElem hbv_mrk, Option.getD_some] at h0; exact absurd h0 hne0
              · exact h1
            exact hfin qa mrk_a ws1_a ma (Nat.le_refl _) hqa_le (fun _ _ => rfl) hqa (Or.inr (by
              have := (hqa.2.2.2.2.2.2.1 _ hbv_cv).mp hm1; rwa [bv32_lshr1_toNat, hb_eq] at this))
              hma
          · have hlv0 : (s.core.lvl[(b_bv >>> 1#32).toNat]?.getD 0#32).toNat = 0 := by
              rw [List.getElem?_eq_getElem hbv_lvl, Option.getD_some]
              have hlv : s.core.lvl[(b_bv >>> 1#32).toNat]'hbv_lvl =
                  s.core.lvl[s.core.confl_lit1.toNat % 4294967296 / 2]'hbv_lvl' := by congr 1
              rw [hlv]; c0_bound
            exact hfin qa mrk_a ws1_a ma (Nat.le_refl _) hqa_le (fun _ _ => rfl) hqa
              (Or.inl (by rwa [bv32_lshr1_toNat, hb_eq] at hlv0)) hma)
        (fun Ja hJa => by
          have hav_lvl : (a_bv >>> 1#32).toNat < s.core.lvl.length := by omega
          have hav_mrk : (a_bv >>> 1#32).toNat < s.core.mrk.length := by omega
          have hws1_0 : 0 < s.scratch.work_stk1.length := by omega
          have hav_idx : (a_bv >>> 1#32).toNat = s.core.confl_lit0.toNat % 4294967296 / 2 := by
            rw [bv32_lshr1_toNat, ha_eq, Nat.mod_eq_of_lt (by omega)]
          have hav_lvl' : s.core.confl_lit0.toNat % 4294967296 / 2 < s.core.lvl.length := by
            rw [← hav_idx]; exact hav_lvl
          have hav_mrk' : s.core.confl_lit0.toNat % 4294967296 / 2 < s.core.mrk.length := by
            rw [← hav_idx]; exact hav_mrk
          fvt_steps
          · have hlp : 0 < (s.core.lvl[(a_bv >>> 1#32).toNat]?.getD 0#32).toNat := by
              rw [List.getElem?_eq_getElem hav_lvl, Option.getD_some]
              have hlv : s.core.lvl[(a_bv >>> 1#32).toNat]'hav_lvl =
                  s.core.lvl[s.core.confl_lit0.toNat % 4294967296 / 2]'hav_lvl' := by congr 1
              rw [hlv]; c0_bound
            have hm0_a : s.core.mrk[(a_bv >>> 1#32).toNat]?.getD 0#8 = 0#8 :=
              hspW.2.2.1.1 _ (by omega)
            obtain ⟨_, hqa_ok, _, _⟩ := push_queue_step hq0 hcv_le hav_cv hlp hm0_a ha_trl
            have ha_mod : (a_bv >>> 1#32).toNat % 2 ^ 64 = (a_bv >>> 1#32).toNat :=
              Nat.mod_eq_of_lt (by omega)
            have hm_a_ok : (FullMem c { s with
                core := { s.core with
                  mrk := s.core.mrk.set (a_bv >>> 1#32).toNat 1#8, lit_mark := lm1 }
                scratch := { s.scratch with
                  work_stk1 := s.scratch.work_stk1.set 0 (a_bv >>> 1#32)
                  ant_sz := 0xFFFFFFFFFFFFFFFF#64, res_sz := 0#64 } } ⋆ R) _ :=
              s13_fullMem_eq (by simp only [hav_idx]; rfl) (by assumption)
            exact hJa (1#64, ()) _ ⟨_, _, by show 1 ≤ _; omega, by simpa [ha_mod] using hqa_ok,
              Or.inr ((mem_map_take_iff (by simp [hws1_len]; omega)).mpr ⟨0, by decide, by
                rw [List.getElem?_set_self hws1_0, Option.getD_some]
                change (a_bv >>> 1#32).toNat = _; rw [bv32_lshr1_toNat, ha_eq]⟩), hm_a_ok⟩
          · exfalso
            have h0 : s.core.mrk[s.core.confl_lit0.toNat % 4294967296 / 2]'hav_mrk' = 0#8 := by
              have h := hspW.2.2.1.1 _
                (by omega : s.core.confl_lit0.toNat % 4294967296 / 2 < c.max_vars)
              rwa [List.getElem?_eq_getElem hav_mrk', Option.getD_some] at h
            exact hc ((bv8_zext32_eq0_iff _).mpr h0)
          · have hlv0 : (s.core.lvl[(a_bv >>> 1#32).toNat]?.getD 0#32).toNat = 0 := by
              rw [List.getElem?_eq_getElem hav_lvl, Option.getD_some]
              have hlv : s.core.lvl[(a_bv >>> 1#32).toNat]'hav_lvl =
                  s.core.lvl[s.core.confl_lit0.toNat % 4294967296 / 2]'hav_lvl' := by congr 1
              rw [hlv]; c0_bound
            exact hJa (0#64, ()) _ ⟨s.core.mrk, s.scratch.work_stk1, Nat.zero_le _, hq0,
              Or.inl (by rwa [bv32_lshr1_toNat, ha_eq] at hlv0), hm⟩)
  · exact absurd (hct1.symm.trans hct2) (by decide)
  · exact absurd (hct1.symm.trans hct0) (by decide)

private abbrev s13DeducePhase1bLargeExpr (h pVars pMark pLevel pArena pWs1 : Val i64)
    (cref sz src_cr : Val i32) (J : Cont [i64]) : Expr Val Cont [i32] :=
  Expr.group (sig := [[i64]]) (fun _ => Blocks.cons (fun p =>
    Expr.jump J (Arg.var p.fst, ())) Blocks.nil) fun Js_top =>
  fvOp32 (OpCode.zext 32 64) (Arg.var src_cr, ()) fun p =>
  fvOp32 (OpCode.add i64) (Arg.var p.fst, Arg.imm 3, ()) fun p3 =>
  fvOp32 (OpCode.add i64) (Arg.var h, Arg.imm 48, ()) fun p48 =>
  Expr.load i64 (Arg.var p48.fst) fun ld_al =>
  fvOp32 (OpCode.cmp .ule i64 .bool (by decide)) (Arg.var p3.fst, Arg.var ld_al, ()) fun pb =>
  Expr.jnz (Arg.var pb.fst)
    (Expr.group (sig := [[]]) (fun _ => Blocks.cons (fun (_ : Tup Val []) =>
       Expr.group (sig := [[i64]]) (fun _ => Blocks.cons (fun p =>
         Expr.jump Js_top.fst (Arg.var p.fst, ())) Blocks.nil) fun Js_in =>
       fvOp32 (OpCode.add i64) (Arg.var h, Arg.imm 1136, ()) fun p =>
       Expr.load i64 (Arg.var p.fst) fun ld =>
       fvOp32 (OpCode.cmp .eq i64 .bool (by decide))
         (Arg.var ld, Arg.imm 18446744073709551615, ()) fun p =>
       Expr.jnz (Arg.var p.fst)
         (fvOp32 (OpCode.zext 32 64) (Arg.var src_cr, ()) fun p =>
          fvOp32 (OpCode.add i64) (Arg.var p.fst, Arg.imm 2, ()) fun p =>
          fvOp32 (OpCode.mul i64) (Arg.var p.fst, Arg.imm 4, ()) fun p =>
          fvOp32 (OpCode.add i64) (Arg.var pArena, Arg.var p.fst, ()) fun p =>
          Expr.load i32 (Arg.var p.fst) fun csz_bv =>
          Expr.group (sig := [[i64, i32]]) (fun Ji => Blocks.cons (fun pi =>
            fvOp32 (OpCode.cmp .ult i32 .bool (by decide))
              (Arg.var pi.snd.fst, Arg.var csz_bv, ()) fun p =>
            Expr.jnz (Arg.var p.fst)
              (fvOp32 (OpCode.zext 32 64) (Arg.var src_cr, ()) fun p =>
               fvOp32 (OpCode.add i64) (Arg.var p.fst, Arg.imm 3, ()) fun p =>
               fvOp32 (OpCode.zext 32 64) (Arg.var pi.snd.fst, ()) fun pz =>
               fvOp32 (OpCode.add i64) (Arg.var p.fst, Arg.var pz.fst, ()) fun p =>
               fvOp32 (OpCode.mul i64) (Arg.var p.fst, Arg.imm 4, ()) fun p =>
               fvOp32 (OpCode.add i64) (Arg.var pArena, Arg.var p.fst, ()) fun p =>
               Expr.load i32 (Arg.var p.fst) fun ld =>
               fvOp32 (OpCode.lshr i32) (Arg.var ld, Arg.imm 1, ()) fun p_lv =>
               Expr.group (sig := [[i64]]) (fun _ => Blocks.cons (fun p =>
                 fvOp32 (OpCode.add i32) (Arg.var pi.snd.fst, Arg.imm 1, ()) fun pj =>
                 Expr.jump Ji.fst (Arg.var p.fst, Arg.var pj.fst, ())) Blocks.nil) fun Jin =>
               deducePushExpr pVars pMark pLevel pWs1 p_lv.fst pi.fst Jin.fst)
              (Expr.jump Js_in.fst (Arg.var pi.fst, ()))) Blocks.nil)
            fun Ji0 => Expr.jump Ji0.fst (Arg.imm 0, Arg.imm 0, ()))
         (Expr.jump Js_in.fst (Arg.imm 0, ()))) Blocks.nil) fun Js_ant =>
     fvOp32 (OpCode.cmp .ne i32 .bool (by decide)) (Arg.var src_cr, Arg.var cref, ()) fun p =>
     Expr.jnz (Arg.var p.fst)
       (Expr.group (sig := [[]]) (fun _ => Blocks.cons (fun (_ : Tup Val []) =>
          Expr.group (sig := [[]]) (fun _ => Blocks.cons (fun _ =>
            Expr.jump Js_ant.fst ()) Blocks.nil) fun Js_pr2 =>
          Expr.call "full_viv_subsumes_cl_m6" (as := [i64, i32, i32]) (bs := [.bool])
            (Arg.var h, Arg.var src_cr, Arg.var sz, ()) fun ok =>
          Expr.jnz (Arg.var ok.fst)
            (fvOp32 (OpCode.zext 32 64) (Arg.var src_cr, ()) fun pr =>
             fvOp32 (OpCode.add i64) (Arg.var h, Arg.imm 1136, ()) fun p =>
             Expr.store (Arg.var pr.fst) (Arg.var p.fst) (Expr.jump Js_pr2.fst ()))
            (Expr.jump Js_pr2.fst ())) Blocks.nil) fun Js_pr =>
        fvOp32 (OpCode.zext 32 64) (Arg.var src_cr, ()) fun p =>
        fvOp32 (OpCode.mul i64) (Arg.var p.fst, Arg.imm 4, ()) fun p =>
        fvOp32 (OpCode.add i64) (Arg.var pArena, Arg.var p.fst, ()) fun p =>
        Expr.load i32 (Arg.var p.fst) fun ld =>
        fvOp32 (OpCode.and i32) (Arg.var ld, Arg.imm 4194304, ()) fun p =>
        fvOp32 (OpCode.cmp .ne i32 .bool (by decide)) (Arg.var p.fst, Arg.imm 0, ()) fun p =>
        Expr.jnz (Arg.var p.fst)
          (fvOp32 (OpCode.add i64) (Arg.var h, Arg.imm 1144, ()) fun p =>
           Expr.store (Arg.imm (t := i64) 1) (Arg.var p.fst)
             (Expr.call "full_viv_recompute_promote_fid" (as := [i64, i32]) (bs := [])
                (Arg.var h, Arg.var src_cr, ()) fun _ => Expr.jump Js_pr.fst ()))
          (Expr.jump Js_pr.fst ()))
       (Expr.jump Js_ant.fst ()))
    (Expr.jump Js_top.fst (Arg.imm 0, ()))

private theorem s13_deduce_phase1b_large_wp (Γ : Env)
    (hPromote : ∀ a m Q X, step13VivRecomputePromoteSpec a m Q X →
      Γ "full_viv_recompute_promote_fid" [i64, i32] [] a m Q X)
    (hSubCl : ∀ a m Q X, fullVivSubsumesClM6Spec a m Q X →
      Γ "full_viv_subsumes_cl_m6" [i64, i32, i32] [.bool] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState} {R : Mem 64 → Prop}
    {lm1 : List (BitVec 8)} {cref sz implied src_cr : Val i32} {m : Mem 64}
    {Q : Post [i32]} {X : XPost} {Jq : Cont [i64]}
    (hspW : FullSparseInvW c F0 F_cur s) (hlm1_len : lm1.length = 2 * c.max_vars)
    (himp_eq : implied = 0xFFFFFFFF#32) (hct_ne1 : s.core.confl_type ≠ 1#64)
    (hsrc_eq : src_cr.toNat =
      (if s.core.confl_type = 2#64 then s.core.confl_ref.toNat else cref.toNat))
    (hsrc_ref : src_cr.toNat ∈ fullArenaClauseRefs s)
    (hsrc_ng : fullArenaClauseGarb s src_cr.toNat = false)
    (hconfl : implied = 0xFFFFFFFF#32 →
      FullVivifySpecs.FullVivConflictOk F_cur s ∨
      (s.core.confl_type = 0#64 ∧
        ∀ l ∈ fullArenaClauseLits s cref.toNat, s.core.vals[l]?.getD 0#8 = 0xFF#8))
    (hq0 : VivQueueOk c s s.core.mrk s.scratch.work_stk1 0)
    (hm : (FullMem c { s with
      core := { s.core with lit_mark := lm1 }
      scratch := { s.scratch with ant_sz := 0xFFFFFFFFFFFFFFFF#64, res_sz := 0#64 } } ⋆ R) m)
    (hJq : ∀ (qlen_v : Val i64) (ar1 mclr1 : List (BitVec 32)) (mrk1 : List (BitVec 8))
        (ws1_1 : List (BitVec 32)) (asz1 rsz1 : BitVec 64) m_q,
      let s1 : FullState := { s with
        core := { s.core with arena := ar1, min_clr := mclr1, mrk := mrk1, lit_mark := lm1 }
        scratch := { s.scratch with work_stk1 := ws1_1, ant_sz := asz1, res_sz := rsz1 } }
      S13SparseInvNoMark c F0 F_cur s1 → S13ArPres s s1 →
      qlen_v.toNat ≤ s.core.cur_vars → VivQueueOk c s1 mrk1 ws1_1 qlen_v.toNat →
      (asz1 = 0xFFFFFFFFFFFFFFFF#64 →
        VivSeedOk s1 cref implied ws1_1 s.scratch.work_stk2 qlen_v.toNat 0 false) →
      S13SubRefOk s1 asz1 → (FullMem c s1 ⋆ R) m_q → Jq (qlen_v, ()) m_q) :
    wp Γ Q X (s13DeducePhase1bLargeExpr c.hdr (BitVec.ofNat 64 s.core.cur_vars)
      c.pMark c.pLevel c.pArena c.pWorkStk1 cref sz src_cr Jq) m := by
  have hw := hspW.2.1; have hcl := hspW.1.core_ok; have hscl := hspW.1.scratch_ok
  have hcap := c.harena; have hmx := c.hmaxv; unfold dimacsBound at hcap hmx
  have hcv_le := hcl.cur_vars_le; have hmrk_len := hcl.mrk_len
  have hws1_len := hscl.work_stk1_len; have hws2_len := hscl.work_stk2_len
  have hsrc_wf := hw.arena.refs_wf src_cr.toNat hsrc_ref
  have hfal_src : ∀ l ∈ fullArenaClauseLits s src_cr.toNat, s.core.vals[l]?.getD 0#8 = 0xFF#8 := by
    rcases hconfl himp_eq with (⟨h1, _⟩ | ⟨h2, _, _, hf2⟩) | ⟨h0, hf0⟩
    · exact absurd h1 hct_ne1
    · have : src_cr.toNat = s.core.confl_ref.toNat := by simpa [h2] using hsrc_eq
      rwa [this]
    · have hne2 : s.core.confl_type ≠ 2#64 := by rw [h0]; decide
      have : src_cr.toNat = cref.toNat := by simpa [hne2] using hsrc_eq
      rwa [this]
  let hnm (rsz' : BitVec 64) := s13_deduce_state_noMark (asz' := 0xFFFFFFFFFFFFFFFF#64)
    (rsz' := rsz') (s13_noMark_of_sparseW hspW) hmrk_len hlm1_len hws1_len hws2_len
  dsimp only [s13DeducePhase1bLargeExpr, fvOp32]
  refine wp_unroll_group fun Js_top hJs_top => ?_; fvt_to_group
  · refine wp_join_group (ts := [])
      (fun _ m_rs => ∃ (ar_1 mclr_1 : List (BitVec 32)) (asz_1 rsz_1 : BitVec 64),
        let s1 : FullState := { s with
          core := { s.core with arena := ar_1, min_clr := mclr_1, lit_mark := lm1 }
          scratch := { s.scratch with ant_sz := asz_1, res_sz := rsz_1 } }
        S13SparseInvNoMark c F0 F_cur s1 ∧ S13ArPres s s1 ∧ S13SubRefOk s1 asz_1 ∧
        (FullMem c s1 ⋆ R) m_rs)
      (fun _ _ m_rs ⟨ar_1, mclr_1, asz_1, rsz_1, hsp_1, hpres_1, hsub_1, hm_rs⟩ => by
        let s1 : FullState := { s with
          core := { s.core with arena := ar_1, min_clr := mclr_1, lit_mark := lm1 }
          scratch := { s.scratch with ant_sz := asz_1, res_sz := rsz_1 } }
        have hw1 := hsp_1.2.1; have hcl1 := hsp_1.1.core_ok
        have href_1 : src_cr.toNat ∈ fullArenaClauseRefs s1 := hpres_1.1.symm ▸ hsrc_ref
        have hng_1 : fullArenaClauseGarb s1 src_cr.toNat = false :=
          (hpres_1.2 _ hsrc_ref).1.trans hsrc_ng
        have hwf_1 := hw1.arena.refs_wf src_cr.toNat href_1
        have hbd_1 : src_cr.toNat + 3 + fullArenaClauseSizeCore s1.core src_cr.toNat ≤
            ar_1.length := by
          have h1 := hwf_1.2.2.1; have hnx := hwf_1.2.2.2.1
          have h2 := hcl1.arena_len_le; have h3 := hcl1.arena_len_arr
          dsimp only [s1] at *; omega
        have hsrc_ar : (src_cr.setWidth 64).toNat < ar_1.length := by
          have := hwf_1.1; have := hcl1.arena_len_le; have := hcl1.arena_len_arr
          dsimp only [s1] at *; bv_omega
        have hsrc_2 : (src_cr.setWidth 64 + 2#64).toNat < ar_1.length := by
          have := hwf_1.1; have := hcl1.arena_len_le; bv_omega
        have hsrc_2_eq : (src_cr.setWidth 64 + 2#64).toNat = src_cr.toNat + 2 := by
          have := hwf_1.1; bv_omega
        rw [Blocks.get_here]; refine wp_unroll_group fun Js_in hJs_in => ?_; fvt_to_group
        · let csz_bv := ar_1[(src_cr.setWidth 64 + 2#64).toNat]'hsrc_2
          have hcsz_eq : csz_bv.toNat = fullArenaClauseSizeCore s1.core src_cr.toNat := by
            unfold fullArenaClauseSizeCore
            rw [List.getElem?_eq_getElem (by dsimp only [s1]; omega), Option.getD_some]
            dsimp only [csz_bv, s1]; simp only [hsrc_2_eq]
          fvt_to_group
          refine wp_loop_inv (ts := [i64, i32])
            (fun (qlen_i, i_c, ()) mi => ∃ (mrk_i : List (BitVec 8)) (ws1_i : List (BitVec 32)),
              i_c.toNat ≤ csz_bv.toNat ∧ qlen_i.toNat ≤ s.core.cur_vars ∧
              VivQueueOk c s1 mrk_i ws1_i qlen_i.toNat ∧
              (∀ t < i_c.toNat,
                (s.core.lvl[(ar_1[src_cr.toNat + 3 + t]?.getD 0#32).toNat / 2]?.getD 0#32).toNat =
                  0 ∨
                (ar_1[src_cr.toNat + 3 + t]?.getD 0#32).toNat / 2 ∈
                  (ws1_i.take qlen_i.toNat).map BitVec.toNat) ∧
              (FullMem c { s1 with core := { s1.core with mrk := mrk_i }
                                   scratch := { s1.scratch with work_stk1 := ws1_i } } ⋆ R) mi)
            (fun (_, i_c, ()) _ => csz_bv.toNat - i_c.toNat) ?_ ?_
          · intro Ji hJi; fvt_steps
            exact hJi (0#64, 0#32, ()) m_rs ⟨s.core.mrk, s.scratch.work_stk1, by simp,
              Nat.zero_le _, s13_vivQueue_ar_eq rfl rfl rfl rfl hq0,
              fun _ ht => by simp at ht, hm_rs⟩
          · rintro Ji ⟨qlen_i, i_c, ⟨⟩⟩ mi ⟨mrk_i, ws1_i, hi_le, hql_i, hqi_ok, hcov_i, hmi⟩ ihi
            fvt_step; fvt_step
            · have hi_lt : i_c.toNat < csz_bv.toNat := by
                dsimp only [csz_bv]
                simpa only [s1, hsrc_2_eq, show (src_cr.toNat + 2) % 2 ^ 64 = src_cr.toNat + 2 from
                  Nat.mod_eq_of_lt (by have := hwf_1.1; omega),
                  show BitVec.toNat (2 : BitVec 64) = 2 from rfl] using hc
              have hi1 : (i_c + 1#32).toNat = i_c.toNat + 1 := by bv_omega
              have hli_idx : (src_cr.setWidth 64 + 3#64 + i_c.setWidth 64).toNat =
                  src_cr.toNat + 3 + i_c.toNat := by bv_omega
              have hli_ar : (src_cr.setWidth 64 + 3#64 + i_c.setWidth 64).toNat < ar_1.length := by
                omega
              let l_bv := ar_1[(src_cr.setWidth 64 + 3#64 + i_c.setWidth 64).toNat]'hli_ar
              let lv_bv := l_bv >>> 1#32
              have hl_eq : l_bv = ar_1[src_cr.toNat + 3 + i_c.toNat]'(by omega) := by
                dsimp only [l_bv]; simp only [hli_idx]
              have hl_mem : l_bv.toNat ∈ fullArenaClauseLits s1 src_cr.toNat :=
                (mem_fullArenaClauseLitsCore_iff hbd_1).mpr
                  ⟨i_c.toNat, by rw [← hcsz_eq]; exact hi_lt, congrArg BitVec.toNat hl_eq.symm⟩
              have hl_lt : l_bv.toNat < 2 * s.core.cur_vars :=
                hw1.arena.lits_lt src_cr.toNat href_1 hng_1 l_bv.toNat hl_mem
              have hlv_val : lv_bv.toNat = l_bv.toNat / 2 := bv32_lshr1_toNat _
              have hlv_cv : lv_bv.toNat < s1.core.cur_vars := by
                change lv_bv.toNat < s.core.cur_vars; rw [hlv_val]; omega
              have hlv_trl : ∃ m < s1.core.trail_end,
                  (s1.core.trl[m]?.getD 0#32).toNat / 2 = lv_bv.toNat := by
                have hl_mem_s : l_bv.toNat ∈ fullArenaClauseLits s src_cr.toNat :=
                  (hpres_1.2 _ hsrc_ref).2.2 ▸ hl_mem
                obtain ⟨m, hm_lt, hmeq⟩ := (hw.vals_false_iff l_bv.toNat hl_lt).mp
                  (hfal_src l_bv.toNat hl_mem_s)
                exact ⟨m, hm_lt, by dsimp only [s1]; rw [hmeq, fullInv_var_xor1, hlv_val]⟩
              have hlen_i : s1.LengthsOk c :=
                s13_deduce_state_len hsp_1.1 hmrk_len hlm1_len hws1_len hws2_len
              fvt_to_group
              refine wp_unroll_group fun Jin hJin => ?_
              exact s13_push_branch_step (s := s1) hlen_i hqi_ok hlv_cv hlv_trl hmi
                fun qlen' mrk_o ws1_o mo hq_io hql_o heq_o hqo hcov_lv hmo =>
                  hJin (qlen', ()) mo (by
                    rw [Blocks.get_here]; fvt_steps
                    have hws1_o_len : ws1_o.length = 2 * c.max_vars := hqo.2.1
                    refine ihi (qlen', i_c + 1#32, ()) mo (by dsimp only; omega)
                      ⟨mrk_o, ws1_o, by omega, hql_o, hqo, fun t ht => ?_, hmo⟩
                    rcases (by omega : t < i_c.toNat ∨ t = i_c.toNat) with ht' | rfl
                    · refine (hcov_i t ht').elim Or.inl fun hm' => Or.inr ?_
                      obtain ⟨k, hk, hkeq⟩ :=
                        (mem_map_take_iff (by have := hqi_ok.2.1; omega)).mp hm'
                      exact (mem_map_take_iff (by
                        have := hcv_le; dsimp only [s1] at hql_o; rw [hws1_o_len]; omega)).mpr
                        ⟨k, by omega, by rw [heq_o k hk, hkeq]⟩
                    · have hleq : (ar_1[src_cr.toNat + 3 + i_c.toNat]?.getD 0#32).toNat / 2 =
                          lv_bv.toNat := by
                        rw [List.getElem?_eq_getElem (by omega), Option.getD_some, ← hl_eq, hlv_val]
                      rw [hleq]; exact hcov_lv)
            · have hge_csz : csz_bv.toNat ≤ i_c.toNat := Nat.not_lt.mp (by
                dsimp only [csz_bv] at *
                simpa only [s1, hsrc_2_eq, show (src_cr.toNat + 2) % 2 ^ 64 = src_cr.toNat + 2 from
                  Nat.mod_eq_of_lt (by have := hwf_1.1; omega),
                  show BitVec.toNat (2 : BitVec 64) = 2 from rfl] using hc)
              have hi_eq : i_c.toNat = csz_bv.toNat := Nat.le_antisymm hi_le hge_csz
              have hcov_src : ∀ l ∈ fullArenaClauseLits s1 src_cr.toNat,
                  (s1.core.lvl[l / 2]?.getD 0#32).toNat = 0 ∨
                  l / 2 ∈ (ws1_i.take qlen_i.toNat).map BitVec.toNat := fun l hl => by
                obtain ⟨t, ht, hlt⟩ := (mem_fullArenaClauseLitsCore_iff hbd_1).mp hl
                have ht_bd : src_cr.toNat + 3 + t < ar_1.length := by omega
                rw [← hcsz_eq] at ht; have hc' := hcov_i t (by omega)
                rwa [List.getElem?_eq_getElem ht_bd, Option.getD_some, hlt] at hc'
              exact hJs_in (qlen_i, ()) mi (by
                fvt_steps; exact hJq qlen_i ar_1 mclr_1 mrk_i ws1_i asz_1 rsz_1 mi
                  (s13_deduce_state_noMark hsp_1 hqi_ok.1 hlm1_len hqi_ok.2.1 hws2_len)
                  (s13ArPres_with_fields hpres_1) hql_i
                  (s13_vivQueue_ar_eq rfl rfl rfl rfl hqi_ok)
                  (fun _ => by
                    intro _; simp only [himp_eq, ne_eq, not_true_eq_false, ↓reduceIte, hct_ne1]
                    rwa [hsrc_eq.symm])
                  (s13_subRef_of_pres ⟨rfl, fun _ _ => ⟨rfl, rfl, rfl⟩⟩ hsub_1) hmi)
        · exact hJq 0#64 ar_1 mclr_1 s.core.mrk s.scratch.work_stk1 asz_1 rsz_1 m_rs
            hsp_1 hpres_1 (Nat.zero_le _) (s13_vivQueue_ar_eq rfl rfl rfl rfl hq0)
            (fun h => absurd h (by c0_bound)) hsub_1 hm_rs)
      (fun Jant hJant => by
        fvt_to_group
        · refine wp_join_group (ts := [])
            (fun _ m_r => ∃ (ar_1 mclr_1 : List (BitVec 32)) (rsz_1 : BitVec 64),
              let s1 : FullState := { s with
                core := { s.core with arena := ar_1, min_clr := mclr_1, lit_mark := lm1 }
                scratch := { s.scratch with ant_sz := 0xFFFFFFFFFFFFFFFF#64, res_sz := rsz_1 } }
              S13SparseInvNoMark c F0 F_cur s1 ∧ S13ArPres s s1 ∧ (FullMem c s1 ⋆ R) m_r)
            (fun _ _ m_r ⟨ar_1, mclr_1, rsz_1, hsp_1, hpres_1, hm_r⟩ => by
              have hw1 := hsp_1.2.1
              have href_1 : src_cr.toNat ∈ fullArenaClauseRefs _ := hpres_1.1.symm ▸ hsrc_ref
              have hng_1 : fullArenaClauseGarb _ src_cr.toNat = false :=
                (hpres_1.2 _ hsrc_ref).1.trans hsrc_ng
              rw [Blocks.get_here]; fvt_steps; c0_call hSubCl
              refine ⟨c, F0, F_cur, _, R, rfl,
                s13_deduce_state_len hsp_1.1 hmrk_len hlm1_len hws1_len hws2_len,
                s13_deduce_state_witness hw1, href_1, hng_1, hm_r, fun ok => ?_⟩
              fvt_steps
              · exact hJant () _ ⟨ar_1, mclr_1, src_cr.setWidth 64, rsz_1,
                  s13_deduce_state_noMark hsp_1 hmrk_len hlm1_len hws1_len hws2_len,
                  s13ArPres_with_fields hpres_1, s13_subRef_set_ref href_1 hng_1, by assumption⟩
              · exact hJant () m_r ⟨ar_1, mclr_1, 0xFFFFFFFFFFFFFFFF#64, rsz_1,
                  hsp_1, hpres_1, s13_subRef_ff _, hm_r⟩)
            (fun Jpr hJpr => by
              have hsrc_ar : (src_cr.setWidth 64).toNat < s.core.arena.length := by
                have := hsrc_wf.1; have := hsrc_wf.2.1
                have := hcl.arena_len_le; have := hcl.arena_len_arr; bv_omega
              c0_hsteps_nogrp; c0_hsplit
              · c0_hsteps_nogrp; c0_call hPromote
                refine ⟨c, F0, F_cur, _, R, rfl, hnm 1#64, hsrc_ref, hsrc_ng, (by assumption),
                  fun ar' mclr' mp hsp' hrefs' hpres' hmp => ?_⟩
                exact hJpr () mp ⟨ar', mclr', 1#64, hsp',
                  (by rcases s13ArPres_of_fields hrefs' hpres' with ⟨h1, h2⟩; exact ⟨h1, h2⟩), hmp⟩
              · c0_hsteps_nogrp; exact hJpr () m ⟨s.core.arena, s.core.min_clr, 0#64, hnm 0#64,
                  s13ArPres_refl _, hm⟩)
        · exact hJant () m ⟨s.core.arena, s.core.min_clr, 0xFFFFFFFFFFFFFFFF#64, 0#64, hnm 0#64,
            s13ArPres_refl _, s13_subRef_ff _, hm⟩)
  · have hno : ¬((src_cr.setWidth 64 + 3#64).toNat ≤
        (BitVec.ofNat 64 s.core.arena_len).toNat) := by c0_bound
    have h1 : (src_cr.setWidth 64 + 3#64).toNat = src_cr.toNat + 3 := by
      have := hsrc_wf.2.2.1; have := hsrc_wf.2.2.2.1; bv_omega
    have h2 : (BitVec.ofNat 64 s.core.arena_len).toNat = s.core.arena_len := by
      have := hcl.arena_len_le; bv_omega
    rw [h1, h2] at hno; have := hsrc_wf.2.2.1; have := hsrc_wf.2.2.2.1; omega

/-- Step-13 `full_viv_deduce_m6` satisfies `step13VivDeduceM6Spec` parametrically in `Γ`. -/
public theorem full_viv_deduce_m6_s5_wp (Γ : Env)
    (hPromote : ∀ a m Q X, step13VivRecomputePromoteSpec a m Q X →
      Γ "full_viv_recompute_promote_fid" [i64, i32] [] a m Q X)
    (hSubBin : ∀ a m Q X, fullVivSubsumesBinM6Spec a m Q X →
      Γ "full_viv_subsumes_bin_m6" [i64, i32, i32] [.bool] a m Q X)
    (hSubCl : ∀ a m Q X, fullVivSubsumesClM6Spec a m Q X →
      Γ "full_viv_subsumes_cl_m6" [i64, i32, i32] [.bool] a m Q X) :
    ∀ a m Q X, step13VivDeduceM6Spec a m Q X →
      Func.wp Γ FullFidelityStep13S5VivifyBackbone.full_viv_deduce_m6_body a m Q X := by
  rintro ⟨h, cref, sz, implied, ⟨⟩⟩ m0 Q X
    ⟨c, F0, F_cur, s, R, rfl, hspW, href, hng, hsz_le, htmp_lt, hconfl, himp, hm0, hQ⟩
  have hw := hspW.2.1; have hcl := hspW.1.core_ok; have hscl := hspW.1.scratch_ok
  have hcap := c.harena; have hmx := c.hmaxv; unfold dimacsBound at hcap hmx
  have hcv_le := hcl.cur_vars_le; have hte_le := hcl.trail_end_le; have hmrk_len := hcl.mrk_len
  have hlm_len := hcl.lit_mark_len; have hlvl_len := hcl.lvl_len; have htrl_len := hcl.trl_len
  have hws1_len := hscl.work_stk1_len; have hws2_len := hscl.work_stk2_len
  have hq0 : VivQueueOk c s s.core.mrk s.scratch.work_stk1 0 :=
    ⟨hmrk_len, hws1_len, Nat.zero_le _, (fun _ h => by cases h), by simp, (fun _ h => by simp at h),
     (fun v _ => ⟨(fun h => by rw [hspW.2.2.1.1 v (by omega)] at h; cases h),
       fun h => by simp at h⟩),
     (fun v _ => Or.inl (hspW.2.2.1.1 v (by omega))), fun v _ hv => hspW.2.2.1.1 v hv⟩
  unfold Func.wp FullFidelityStep13S5VivifyBackbone.full_viv_deduce_m6_body; fvt_to_group
  refine wp_loop_inv (ts := [i32]) (fun (mi, ()) m_lm =>
    mi.toNat ≤ sz.toNat ∧ ∃ lm1 : List (BitVec 8), lm1.length = 2 * c.max_vars ∧
      (∀ l < 2 * c.max_vars, lm1[l]?.getD 0#8 ≠ 0#8 →
        ∃ t < mi.toNat, (s.core.tmp[t]?.getD 0#32).toNat = l) ∧
      (FullMem c { s with core := { s.core with lit_mark := lm1 } } ⋆ R) m_lm)
    (fun (mi, _) _ => sz.toNat - mi.toNat) ?_ ?_
  · intro J0 hJ0; fvt_steps; exact hJ0 (0#32, ()) m0 ⟨Nat.zero_le _, s.core.lit_mark, hlm_len,
      fun l hl hnz => absurd (hspW.2.2.1.2 l hl) hnz, hm0⟩
  · rintro J0 ⟨mi, ⟨⟩⟩ m_lm ⟨hmk_le, lm1, hlm1_len, hlm1_dom, hm_lm⟩ ih0; fvt_step; fvt_step
    · have hmk_lt : mi.toNat < sz.toNat := by c0_bound
      have hmk1 : (mi + 1#32).toNat = mi.toNat + 1 := by bv_omega
      have hmk_tmp : mi.toNat < s.core.tmp.length := by rw [hcl.tmp_len_arr]; omega
      let lt := s.core.tmp[mi.toNat]'hmk_tmp
      have hlt_lm : lt.toNat < lm1.length := by
        have := htmp_lt mi.toNat hmk_lt
        rw [List.getElem?_eq_getElem hmk_tmp, Option.getD_some] at this; dsimp only [lt]; omega
      fvt_steps; let lm1' := lm1.set lt.toNat 1#8
      refine ih0 (mi + 1#32, ()) _ (by dsimp only; omega)
        ⟨by omega, lm1', by simp [lm1', hlm1_len], fun q hq hnz => ?_, by assumption⟩
      by_cases hql : q = lt.toNat
      · subst hql; exact ⟨mi.toNat, by omega,
          by rw [List.getElem?_eq_getElem hmk_tmp, Option.getD_some]⟩
      · dsimp only [lm1'] at hnz; rw [List.getElem?_set_ne (Ne.symm hql)] at hnz
        obtain ⟨t, ht, hteq⟩ := hlm1_dom q hq hnz; exact ⟨t, by omega, hteq⟩
    · have hmk_eq : mi.toNat = sz.toNat := by c0_bound
      have hlm1_dom' : ∀ l < 2 * c.max_vars, lm1[l]?.getD 0#8 ≠ 0#8 →
          ∃ t < sz.toNat, (s.core.tmp[t]?.getD 0#32).toNat = l := fun l hl hnz => by
        obtain ⟨t, ht, he⟩ := hlm1_dom l hl hnz; exact ⟨t, by omega, he⟩
      clear hc ih0 J0; fvt_to_group
      refine wp_join_group (ts := [i64, i32]) (fun (qlen_v, olen_v, ()) mp =>
        ∃ (ar1 mclr1 : List (BitVec 32)) (mrk1 : List (BitVec 8))
          (ws1_1 ws2_1 : List (BitVec 32)) (asz1 rsz1 : BitVec 64),
          let s1 : FullState := { s with
            core := { s.core with arena := ar1, min_clr := mclr1, mrk := mrk1, lit_mark := lm1 },
            scratch := { s.scratch with
              work_stk1 := ws1_1, work_stk2 := ws2_1, ant_sz := asz1, res_sz := rsz1 } }
          S13SparseInvNoMark c F0 F_cur s1 ∧ S13ArPres s s1 ∧
          ws2_1.length = 2 * c.max_vars ∧ qlen_v.toNat ≤ s.core.cur_vars ∧
          VivQueueOk c s1 mrk1 ws1_1 qlen_v.toNat ∧
          VivOutOk s1 implied ws1_1 ws2_1 0 olen_v.toNat false ∧
          (asz1 = 0xFFFFFFFFFFFFFFFF#64 →
            VivSeedOk s1 cref implied ws1_1 ws2_1 qlen_v.toNat olen_v.toNat false) ∧
          S13SubRefOk s1 asz1 ∧ (implied ≠ 0xFFFFFFFF#32 →
            (s1.core.lvl[implied.toNat / 2]?.getD 0#32).toNat = 0 ∨
            implied.toNat / 2 ∈ (ws1_1.take qlen_v.toNat).map BitVec.toNat) ∧ (FullMem c s1 ⋆ R) mp)
        (fun _ ⟨qlen_v, olen_v, ⟨⟩⟩ mp ⟨ar1, mclr1, mrk1, ws1_1, ws2_1, asz1, rsz1, hsp1,
            hpres1, hws2_1, hql1, hq1, ho1, hsd1, hsub1, hsdi1, hmp⟩ => by
          let s1a : FullState := { s with core := { s.core with arena := ar1, min_clr := mclr1 } }
          have hsp1a := s13_deduce_state_noMark (asz' := s.scratch.ant_sz)
            (rsz' := s.scratch.res_sz) hsp1 hmrk_len hlm_len hws1_len hws2_len
          rw [Blocks.get_here]
          refine s13_deduce_phase2_wp (s1 := s1a) Γ hPromote hSubBin hSubCl hsp1a
            (hpres1.1.symm ▸ href) ((hpres1.2 _ href).1.trans hng) hsz_le htmp_lt
            (fun he => s13_confl_pres hpres1 rfl rfl rfl rfl rfl rfl (hconfl he) href)
            himp hlm1_len hlm1_dom' hws2_1 hql1 hq1 ho1 hsd1 hsub1 hsdi1 hmp
            fun olen ar' mclr' mrk' lm' ws1' ws2' asz' rsz' m' hsp' hpres' hsub' hol_ok hm' =>
              let ⟨hp1_1, hp1_2⟩ := hpres1; let ⟨hp'_1, hp'_2⟩ := hpres'
              hQ olen ar' mclr' mrk' lm' ws1' ws2' asz' rsz' m' hsp' hsub'.1 hsub'.2
                (hp'_1.trans hp1_1) (fun r hr => let ⟨hg1, hs1, hl1⟩ := hp1_2 r hr
                  let ⟨hg2, hs2, hl2⟩ := hp'_2 r (hp1_1.symm ▸ hr)
                  ⟨hg2.trans hg1, hs2.trans hs1, hl2.trans hl1⟩) hol_ok hm')
        (fun Jp hJp => ?_)
      fvt_to_group
      · have himp_ne : implied ≠ 0xFFFFFFFF#32 := by c0_bound
        obtain ⟨himp_lt, himp_v1⟩ := himp himp_ne; let iv_bv := implied >>> 1#32
        have hiv_val : iv_bv.toNat = implied.toNat / 2 := bv32_lshr1_toNat _
        have hiv_cv : iv_bv.toNat < s.core.cur_vars := by rw [hiv_val]; omega
        have hiv_lvl : iv_bv.toNat < s.core.lvl.length := by omega
        have hiv_mrk : iv_bv.toNat < s.core.mrk.length := by omega
        have hws1_0 : 0 < s.scratch.work_stk1.length := by omega
        have hws2_0 : 0 < s.scratch.work_stk2.length := by omega
        have hiv_trl : ∃ m < s.core.trail_end,
            (s.core.trl[m]?.getD 0#32).toNat / 2 = iv_bv.toNat := by
          obtain ⟨m, hm_lt, hmeq⟩ := (hw.vals_true_iff _ himp_lt).mp himp_v1
          exact ⟨m, hm_lt, by rw [hmeq, hiv_val]⟩
        refine wp_join_group (ts := [i64]) (fun (qlen_v, ()) m1 =>
          ∃ (mrk1 : List (BitVec 8)) (ws1_1 : List (BitVec 32)),
            qlen_v.toNat ≤ s.core.cur_vars ∧ VivQueueOk c s mrk1 ws1_1 qlen_v.toNat ∧
            ((s.core.lvl[implied.toNat / 2]?.getD 0#32).toNat = 0 ∨
              implied.toNat / 2 ∈ (ws1_1.take qlen_v.toNat).map BitVec.toNat) ∧
            (FullMem c
              { s with
                core := { s.core with mrk := mrk1, lit_mark := lm1 }
                scratch := { s.scratch with
                  work_stk1 := ws1_1, ant_sz := 0xFFFFFFFFFFFFFFFF#64, res_sz := 0#64 } } ⋆ R) m1)
          (fun _ ⟨qlen_v, ⟨⟩⟩ m1 ⟨mrk1, ws1_1, hql1, hq1, hcov_i, hm1⟩ => by
            fvt_steps; let ws2_1 := s.scratch.work_stk2.set 0 implied
            have hws2_1 : ws2_1.length = 2 * c.max_vars := by simp [ws2_1, hws2_len]
            have hsp1 := s13_deduce_state_noMark (s13_noMark_of_sparseW hspW)
              (asz' := 0xFFFFFFFFFFFFFFFF#64) (rsz' := 0#64) hq1.1 hlm1_len hq1.2.1 hws2_1
            refine hJp (qlen_v, 1#32, ()) _ ⟨s.core.arena, s.core.min_clr, mrk1, ws1_1, ws2_1,
              0xFFFFFFFFFFFFFFFF#64, 0#64, hsp1, s13ArPres_with_fields (s13ArPres_refl _),
              hws2_1, hql1, s13_vivQueue_ar_eq rfl rfl rfl rfl hq1, ?_, fun _ => ?_,
              s13_subRef_ff _, fun _ => hcov_i, by assumption⟩
            · intro _; refine ⟨by show 1 ≤ s.core.cur_vars; omega, fun j hj => ?_, ?_, ?_, ?_, ?_⟩
              · obtain rfl : j = 0 := by change j < 1 at hj; omega
                dsimp only [ws2_1]; rw [List.getElem?_set_self hws2_0, Option.getD_some]
                exact himp_lt
              · show ((ws2_1.take 1).map BitVec.toNat |>.map (· / 2)).Nodup
                rw [List.take_one]; cases ws2_1.head? <;> simp
              · intro j hj; obtain rfl : j = 0 := by change j < 1 at hj; omega
                left; dsimp only [ws2_1]; rw [List.getElem?_set_self hws2_0, Option.getD_some]
                exact ⟨himp_ne, rfl, rfl⟩
              · intro _
                exact ⟨by decide, by dsimp only [ws2_1]; rw [List.getElem?_set_self hws2_0]⟩
              · intro _ h; exact absurd h (Nat.not_lt_zero _)
            · intro _; simp only [himp_ne, ne_eq, not_false_eq_true, ↓reduceIte]
              exact (mem_map_take_iff (by show 1 ≤ ws2_1.length; rw [hws2_1]; omega)).mpr
                ⟨0, by decide, by dsimp only [ws2_1]; rw [List.getElem?_set_self hws2_0]; rfl⟩)
          (fun J1 hJ1 => by
            fvt_steps
            · have hlvl_pos : 0 < (s.core.lvl[iv_bv.toNat]?.getD 0#32).toNat := by
                rw [List.getElem?_eq_getElem hiv_lvl, Option.getD_some]; c0_bound
              have hm0' : s.core.mrk[iv_bv.toNat]?.getD 0#8 = 0#8 :=
                hspW.2.2.1.1 iv_bv.toNat (by omega)
              obtain ⟨_, hq_next, _, _⟩ := push_queue_step hq0 hcv_le hiv_cv hlvl_pos hm0' hiv_trl
              have hiv_mod : iv_bv.toNat % 2 ^ 64 = iv_bv.toNat := Nat.mod_eq_of_lt (by omega)
              refine hJ1 (1#64, ()) _ ⟨_, _, by show 1 ≤ _; omega, by simpa [hiv_mod] using hq_next,
                Or.inr ((mem_map_take_iff (by simp [hws1_len]; omega)).mpr ⟨0, by decide,
                  by rw [List.getElem?_set_self hws1_0, Option.getD_some]; exact hiv_val⟩),
                s13_fullMem_eq (by simp only [hiv_val]; rfl) (by assumption)⟩
            · have hlvl0 : (s.core.lvl[iv_bv.toNat]?.getD 0#32).toNat = 0 := by
                rw [List.getElem?_eq_getElem hiv_lvl, Option.getD_some]
                have hlv : s.core.lvl[iv_bv.toNat]'hiv_lvl =
                    s.core.lvl[implied.toNat / 2]'(by rw [← hiv_val]; exact hiv_lvl) := by congr 1
                rw [hlv]; c0_bound
              exact hJ1 (0#64, ()) _ ⟨s.core.mrk, s.scratch.work_stk1, Nat.zero_le _, hq0,
                Or.inl (by rwa [← hiv_val]), hm⟩)
      · have himp_eq : implied = 0xFFFFFFFF#32 := by c0_bound
        refine wp_join_group (ts := [i32])
          (fun (src_cr, ()) m_src => m = m_src ∧ src_cr.toNat =
              (if s.core.confl_type = 2#64 then s.core.confl_ref.toNat else cref.toNat) ∧
            src_cr.toNat ∈ fullArenaClauseRefs s ∧ fullArenaClauseGarb s src_cr.toNat = false)
          (fun _ ⟨src_cr, ⟨⟩⟩ m_src ⟨hm_src, hsrc_eq, hsrc_ref, hsrc_ng⟩ => by
            subst hm_src
            have hvo : ∀ (s1 : FullState) ws1_1,
                VivOutOk s1 implied ws1_1 s.scratch.work_stk2 0 0 false := fun _ _ _ =>
              ⟨Nat.zero_le _, fun _ h => by simp at h, by simp, fun _ h => by simp at h,
               fun hne => absurd himp_eq hne, fun _ h => by omega⟩
            rw [Blocks.get_here]; refine wp_unroll_group fun Jq hJq => ?_
            fvt_step; fvt_step; rw [wp_jnz]; constructor <;> intro hc
            · have hct1 : s.core.confl_type = 1#64 := by simpa [Arg.val_var] using hc
              exact s13_deduce_phase1b_bin_wp Γ hSubBin hspW hlm1_len himp_eq hct1 hconfl hq0 hm
                fun qlen_v mrk1 ws1_1 asz1 rsz1 m_q hql1 hq1 hsd1 hsub1 hm_q =>
                  hJq (qlen_v, ()) m_q (by
                    rw [Blocks.get_here]; fvt_steps
                    exact hJp (qlen_v, 0#32, ()) m_q ⟨s.core.arena, s.core.min_clr, mrk1, ws1_1,
                      s.scratch.work_stk2, asz1, rsz1, s13_deduce_state_noMark
                        (s13_noMark_of_sparseW hspW) hq1.1 hlm1_len hq1.2.1 hws2_len,
                      s13ArPres_with_fields (s13ArPres_refl _), hws2_len, hql1,
                      s13_vivQueue_ar_eq rfl rfl rfl rfl hq1, hvo _ _, hsd1, hsub1,
                      fun hne => absurd himp_eq hne, hm_q⟩)
            · have hct_ne1 : s.core.confl_type ≠ 1#64 := by simpa [Arg.val_var] using hc
              exact s13_deduce_phase1b_large_wp Γ hPromote hSubCl hspW hlm1_len himp_eq hct_ne1
                hsrc_eq hsrc_ref hsrc_ng hconfl hq0 hm fun qlen_v ar1 mclr1 mrk1 ws1_1 asz1 rsz1
                  m_q hsp1 hpres1 hql1 hq1 hsd1 hsub1 hm_q => hJq (qlen_v, ()) m_q (by
                    rw [Blocks.get_here]; fvt_steps
                    exact hJp (qlen_v, 0#32, ()) m_q ⟨ar1, mclr1, mrk1, ws1_1,
                      s.scratch.work_stk2, asz1, rsz1, hsp1, hpres1, hws2_len, hql1, hq1,
                      hvo _ _, hsd1, hsub1, fun hne => absurd himp_eq hne, hm_q⟩))
          (fun Jsrc hJsrc => by
            fvt_steps
            · have hct2 : s.core.confl_type = 2#64 := by c0_bound
              rcases hconfl himp_eq with (⟨hct1, _⟩ | ⟨_, href2, hng2, _⟩) | ⟨hct0, _⟩
              · exact absurd (hct2.symm.trans hct1) (by decide)
              · have hlt32 : s.core.confl_ref.toNat < 2 ^ 32 := by
                  have := (hw.arena.refs_wf _ href2).1; have := hcl.arena_len_le; omega
                have htr := bv64_trunc32_toNat hlt32
                exact hJsrc (s.core.confl_ref.truncate 32, ()) _
                  ⟨rfl, by simp [hct2, htr], by rwa [htr], by rwa [htr]⟩
              · exact absurd (hct2.symm.trans hct0) (by decide)
            · have hne2 : s.core.confl_type ≠ 2#64 := by c0_bound
              exact hJsrc (cref, ()) _ ⟨rfl, by simp [hne2], href, hng⟩)
end DeduceProof
end LeanQbe.T.Examples.Kissat.FullFidelityStep13S5