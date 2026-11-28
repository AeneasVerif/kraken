/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Vivify.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Backtrack.Spec
public import LeanQbe.T.Examples.Kissat.Src.Vivify

import LeanQbe.T.Examples.Kissat.Proof.Vivify.Inv
import LeanQbe.T.Examples.Kissat.Proof.Vivify.InvArena
import LeanQbe.T.Examples.Kissat.Proof.Vivify.Tactics
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.ControlComb

/-!
# Kissat Vivify Finish WP Proof (`Proof.Vivify.WpFinish`)

Parametric `(Γ : Env)` `Func.wp` certification (`public section`, zero legacy imports) for
`full_viv_finish_m6` (`Spec.vivFinishM6Spec`): post-loop deduction dispatch, subsumption
irreducible promotion & glue lowering, commit, deletion, instantiation (`FullM6HdrMem`), and
2WL watch re-establishment.
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

/-! ## 1. Pure BitVector, Arena & State Helpers -/

private theorem bv32_setWidth64_toNat (x : BitVec 32) : (x.setWidth 64).toNat = x.toNat := by
  have := x.isLt; simp [BitVec.toNat_setWidth]; omega

private theorem bv32_clear_red_mask (x m : BitVec 32)
    (hm : (~~~0x400000#32 &&& m) = m) :
    ((x &&& ~~~0x400000#32) &&& m) = (x &&& m) := by
  rw [BitVec.and_assoc, hm]

private theorem bv32_set_glue_mask (shdr hdr m : BitVec 32)
    (h1 : (~~~0x7FFFF#32 &&& m) = m) (h2 : (0x7FFFF#32 &&& m) = 0#32) :
    (((shdr &&& ~~~0x7FFFF#32) ||| (hdr &&& 0x7FFFF#32)) &&& m) = (shdr &&& m) := by
  rw [BitVec.and_or_distrib_right, BitVec.and_assoc, h1, BitVec.and_assoc, h2,
    BitVec.and_zero, BitVec.or_zero]

private theorem finish_tmp_lits_lt {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {cref sz : BitVec 32}
    (hsp : FullSparseInvW c F0 F_cur s) (hsz_le : sz.toNat ≤ c.max_vars)
    (href : cref.toNat ∈ fullArenaClauseRefs s) (hng : fullArenaClauseGarb s cref.toNat = false)
    (hperm : ((s.core.tmp.take sz.toNat).map BitVec.toNat).Perm
      (fullArenaClauseLits s cref.toNat)) :
    ∀ k < sz.toNat, (s.core.tmp[k]?.getD 0#32).toNat < 2 * s.core.cur_vars := by
  intro k hk
  have hkt : k < s.core.tmp.length := by rw [hsp.1.core_ok.tmp_len_arr]; omega
  have hmem_take : s.core.tmp[k] ∈ s.core.tmp.take sz.toNat :=
    List.mem_take_iff_getElem.mpr ⟨k, by omega, rfl⟩
  have hmem_map : (s.core.tmp[k]?.getD 0#32).toNat ∈
      (s.core.tmp.take sz.toNat).map BitVec.toNat := by
    rw [List.getElem?_eq_getElem hkt, Option.getD_some]
    exact List.mem_map.mpr ⟨s.core.tmp[k], hmem_take, rfl⟩
  exact hsp.2.1.arena.lits_lt cref.toNat href hng _ (hperm.mem_iff.mp hmem_map)

private theorem finish_cur_level_lt64 {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hsp : FullSparseInvW c F0 F_cur s) : s.core.cur_level < 2 ^ 64 := by
  have := hsp.2.1.cur_level_le
  have := hsp.1.core_ok.trail_end_le
  have := hsp.1.core_ok.cur_vars_le
  have := c.hmaxv; unfold dimacsBound at this; omega

private abbrev VivFinishStateOk (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (ext0 : List (BitVec 64)) (s0 : FullState)
    (ext' : List (BitVec 64)) (s' : FullState) : Prop :=
  M6HdrExtOk ext' ∧
  (M6HdrExtInitOk ext0 → M6HdrExtInitOk ext' ∧ M6ExtW2bPres ext0 ext') ∧
  FullSparseInvW c F0 F_cur s' ∧
  s'.core.cur_vars = s0.core.cur_vars ∧
  s'.core.probing = s0.core.probing ∧
  s'.core.fuel.toNat ≤ s0.core.fuel.toNat ∧
  s'.core.arena_len = s0.core.arena_len ∧
  fullArenaClauseRefs s' = fullArenaClauseRefs s0 ∧
  s'.scratch.red_refs = s0.scratch.red_refs

private abbrev VivFinishQ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (ext0 : List (BitVec 64)) (s0 : FullState) (R : Mem 64 → Prop) (Q : Post [i64]) : Prop :=
  ∀ r ext' s' m',
    VivFinishStateOk c F0 F_cur ext0 s0 ext' s' →
    (r = 1#64 ∨ r = 2#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
    (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m'

private theorem vivFinishStateOk_refl {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {ext : List (BitVec 64)} {s : FullState}
    (hext : M6HdrExtOk ext) (hsp : FullSparseInvW c F0 F_cur s) :
    VivFinishStateOk c F0 F_cur ext s ext s :=
  ⟨hext, viv_ext_pres_refl _, hsp, rfl, rfl, Nat.le_refl _, rfl, rfl, rfl⟩

private theorem vivFinishStateOk_trans {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {ext0 ext1 ext2 : List (BitVec 64)} {s0 s1 s2 : FullState}
    (h1 : VivFinishStateOk c F0 F_cur ext0 s0 ext1 s1)
    (h2 : VivFinishStateOk c F0 F_cur ext1 s1 ext2 s2) :
    VivFinishStateOk c F0 F_cur ext0 s0 ext2 s2 :=
  ⟨h2.1, viv_ext_pres_trans h1.2.1 h2.2.1, h2.2.2.1,
   h2.2.2.2.1.trans h1.2.2.2.1,
   h2.2.2.2.2.1.trans h1.2.2.2.2.1,
   Nat.le_trans h2.2.2.2.2.2.1 h1.2.2.2.2.2.1,
   h2.2.2.2.2.2.2.1.trans h1.2.2.2.2.2.2.1,
   h2.2.2.2.2.2.2.2.1.trans h1.2.2.2.2.2.2.2.1,
   h2.2.2.2.2.2.2.2.2.trans h1.2.2.2.2.2.2.2.2⟩

/-! ## 2. Conditional Backtrack & Mark-Garbage Helpers -/

private abbrev finishCondBtExpr (h : Val i64) (confl : Val .bool) (J : Cont []) :
    Expr Val Cont [i64] :=
  Expr.jnz (Arg.var confl)
    (fvOp (OpCode.add i64) (Arg.var h, Arg.imm 160, ()) fun p =>
     Expr.load i64 (Arg.var p.fst) fun ld =>
     fvOp (OpCode.cmp .ugt i64 .bool (by decide)) (Arg.var ld, Arg.imm 0, ()) fun cnd =>
     Expr.jnz (Arg.var cnd.fst)
       (fvOp (OpCode.add i64) (Arg.var h, Arg.imm 160, ()) fun p =>
        Expr.load i64 (Arg.var p.fst) fun ld2 =>
        fvOp (OpCode.sub i64) (Arg.var ld2, Arg.imm 1, ()) fun tgt =>
        Expr.call (as := [i64, i64]) (bs := []) "full_backtrack"
          (Arg.var h, Arg.var tgt.fst, ()) fun _ => Expr.jump J ())
       (Expr.jump J ()))
    (Expr.jump J ())

private theorem finish_cond_bt_wp (Γ : Env)
    (hBt : Γ.Has "full_backtrack" fullBacktrackSpec)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {ext0 ext : List (BitVec 64)} {s0 s : FullState}
    {R : Mem 64 → Prop} {confl : Val .bool} {m : Mem 64}
    {Q : Post [i64]} {X : XPost} {J : Cont []}
    (hst : VivFinishStateOk c F0 F_cur ext0 s0 ext s)
    (hm : (FullMem c s ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R)) m)
    (hJ : ∀ s' m', VivFinishStateOk c F0 F_cur ext0 s0 ext s' →
      (FullMem c s' ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R)) m' → J () m') :
    wp Γ Q X (finishCondBtExpr c.hdr confl J) m := by
  have hsp := hst.2.2.1
  have hcl_lt := finish_cur_level_lt64 hsp
  dsimp only [finishCondBtExpr, fvOp]
  viv_hsteps_nogrp
  · have hpos : 0 < s.core.cur_level := by
      have hgt : (0#64 : BitVec 64) < BitVec.ofNat 64 s.core.cur_level := by c0_bound
      rw [BitVec.lt_def, BitVec.toNat_zero, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt hcl_lt] at hgt
      exact hgt
    have htgt_nat : (BitVec.ofNat 64 s.core.cur_level - 1).toNat =
        s.core.cur_level - 1 := by
      have h1 : (BitVec.ofNat 64 s.core.cur_level).toNat = s.core.cur_level := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcl_lt]
      bv_omega
    have hmax : s.core.cur_level ≤ c.max_vars := by
      have := hsp.2.1.cur_level_le
      have := hsp.1.core_ok.trail_end_le
      have := hsp.1.core_ok.cur_vars_le; omega
    viv_call hBt
    refine ⟨c, s, m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R, rfl, hsp.1, hcl_lt,
      fun _ => by rw [htgt_nat]; omega, hsp.2.1.trail_lits_lt, hm, ?_⟩
    intro vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m' _
      hlen' _ _ _ hps hsc_eq _ _ hfb _ hm'
    have hsp' := viv_sparseW_of_backtrack hsp (target_lvl := s.core.cur_level - 1)
      (by omega) hlen' hps (hfb F0 F_cur hsp.2.1 (by rw [htgt_nat]; omega))
    rcases hsc_eq with ⟨_, _, _, _, _, _, _, _, _, rfl⟩
    have hst' : VivFinishStateOk c F0 F_cur ext0 s0 ext _ :=
      vivFinishStateOk_trans hst
        ⟨hst.1, viv_ext_pres_refl _, hsp', rfl, rfl, Nat.le_refl _, rfl, rfl, rfl⟩
    try rw [wp_jump]
    exact hJ _ m' hst' hm'
  · exact hJ s m hst hm
  · exact hJ s m hst hm

private abbrev finishMarkBtRet1Expr (h : Val i64) (cref : Val i32) (confl : Val .bool) :
    Expr Val Cont [i64] :=
  Expr.call (as := [i64, i32]) (bs := []) "full_viv_mark_garb_m6"
    (Arg.var h, Arg.var cref, ()) fun _ =>
  Expr.group (sig := [[]]) (fun _ => Blocks.cons (fun (_ : Tup Val []) =>
    Expr.ret (Arg.imm 1, ())) Blocks.nil) fun J20 =>
  finishCondBtExpr h confl J20.fst

private theorem finish_mark_bt_ret1_wp (Γ : Env)
    (hMark : Γ.Has "full_viv_mark_garb_m6" fullVivMarkGarbM6Spec)
    (hBt : Γ.Has "full_backtrack" fullBacktrackSpec)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {ext0 ext : List (BitVec 64)} {s0 s : FullState}
    {R : Mem 64 → Prop} {cref : Val i32} {confl : Val .bool} {m : Mem 64}
    {Q : Post [i64]} {X : XPost}
    (hst : VivFinishStateOk c F0 F_cur ext0 s0 ext s)
    (href : cref.toNat ∈ fullArenaClauseRefs s)
    (hm : (FullMem c s ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R)) m)
    (hQ : VivFinishQ c F0 F_cur ext0 s0 R Q) :
    wp Γ Q X (finishMarkBtRet1Expr c.hdr cref confl) m := by
  dsimp only [finishMarkBtRet1Expr]
  viv_call hMark
  refine ⟨c, F0, F_cur, s, m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R, rfl, hst.2.2.1, href, hm, ?_⟩
  intro s1 m1 hsp1 hcv1 hal1 hpr1 hfu1 hrefs1 hrr1 _ _ hm1
  have hst1 : VivFinishStateOk c F0 F_cur ext0 s0 ext s1 :=
    vivFinishStateOk_trans hst
      ⟨hst.1, viv_ext_pres_refl _, hsp1, hcv1, hpr1,
        by rw [hfu1]; exact Nat.le_refl _, hal1, hrefs1, hrr1⟩
  refine wp_join0
    (fun m2 => ∃ s2, VivFinishStateOk c F0 F_cur ext0 s0 ext s2 ∧
      (FullMem c s2 ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R)) m2)
    (fun _ m2 ⟨s2, hst2, hm2⟩ => by
      rw [Blocks.get_here]
      viv_hsteps_nogrp
      exact hQ 1#64 ext s2 m2 hst2 (Or.inl rfl) (fun h => by cases h)
        (fullM6HdrMem_unfocus_full hm2))
    (fun _ hJ20 => finish_cond_bt_wp Γ hBt hst1 hm1 fun s2 m2 hst2 hm2 =>
      hJ20 m2 ⟨s2, hst2, hm2⟩)

/-! ## 3. Subsumption Promotion & Glue-Lowering Branch -/

private abbrev finishSubPromoLoopExpr (pArena pFlags sub_ref : Val i64) (ssz : Val i32)
    (Jexit : Cont []) : Expr Val Cont [i64] :=
  Expr.group (sig := [[i32]]) (fun J45 => Blocks.cons (fun p46 =>
    fvOp (OpCode.cmp .ult i32 .bool (by decide)) (Arg.var p46.fst, Arg.var ssz, ()) fun p47 =>
    Expr.jnz (Arg.var p47.fst)
      (fvOp (OpCode.add i64) (Arg.var sub_ref, Arg.imm 3, ()) fun p48 =>
       fvOp (OpCode.zext 32 64) (Arg.var p46.fst, ()) fun p49 =>
       fvOp (OpCode.add i64) (Arg.var p48.fst, Arg.var p49.fst, ()) fun p50 =>
       fvOp (OpCode.mul i64) (Arg.var p50.fst, Arg.imm 4, ()) fun p51 =>
       fvOp (OpCode.add i64) (Arg.var pArena, Arg.var p51.fst, ()) fun p52 =>
       Expr.load i32 (Arg.var p52.fst) fun ld53 =>
       Expr.group (sig := [[i32]]) (fun _ => Blocks.cons (fun p55 =>
         fvOp (OpCode.lshr i32) (Arg.var ld53, Arg.imm 1, ()) fun p56 =>
         fvOp (OpCode.zext 32 64) (Arg.var p56.fst, ()) fun p57 =>
         fvOp (OpCode.mul i64) (Arg.var p57.fst, Arg.imm 4, ()) fun p58 =>
         fvOp (OpCode.add i64) (Arg.var pFlags, Arg.var p58.fst, ()) fun p59 =>
         fvOp (OpCode.lshr i32) (Arg.var ld53, Arg.imm 1, ()) fun p60 =>
         fvOp (OpCode.zext 32 64) (Arg.var p60.fst, ()) fun p61 =>
         fvOp (OpCode.mul i64) (Arg.var p61.fst, Arg.imm 4, ()) fun p62 =>
         fvOp (OpCode.add i64) (Arg.var pFlags, Arg.var p62.fst, ()) fun p63 =>
         Expr.load i32 (Arg.var p63.fst) fun ld64 =>
         fvOp (OpCode.or i32) (Arg.var ld64, Arg.imm 8, ()) fun p65 =>
         fvOp (OpCode.or i32) (Arg.var p65.fst, Arg.imm 16, ()) fun p66 =>
         fvOp (OpCode.or i32) (Arg.var p66.fst, Arg.var p55.fst, ()) fun p67 =>
         Expr.store (Arg.var p67.fst) (Arg.var p59.fst)
           (fvOp (OpCode.add i32) (Arg.var p46.fst, Arg.imm 1, ()) fun p68 =>
            Expr.jump J45.fst (Arg.var p68.fst, ()))) Blocks.nil) fun J54 =>
       fvOp (OpCode.and i32) (Arg.var ld53, Arg.imm 1, ()) fun p55 =>
       fvOp (OpCode.cmp .ne i32 .bool (by decide)) (Arg.var p55.fst, Arg.imm 0, ()) fun p56 =>
       Expr.jnz (Arg.var p56.fst)
         (Expr.jump J54.fst (Arg.imm 64, ()))
         (Expr.jump J54.fst (Arg.imm 32, ())))
      (Expr.jump Jexit ())) Blocks.nil) fun J45 =>
  Expr.jump J45.fst (Arg.imm 0, ())

private theorem finish_sub_promo_loop_wp (Γ : Env)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    {R : Mem 64 → Prop} {sub_ref : Val i64} {ssz : Val i32} {m : Mem 64}
    {Q : Post [i64]} {X : XPost} {Jexit : Cont []}
    (hsp : FullSparseInvW c F0 F_cur s)
    (href : sub_ref.toNat ∈ fullArenaClauseRefs s)
    (hng : fullArenaClauseGarb s sub_ref.toNat = false)
    (hssz : ssz.toNat = fullArenaClauseSize s sub_ref.toNat)
    (hm : (FullMem c s ⋆ R) m)
    (hJexit : ∀ fl m', fl.length = c.max_vars →
      (FullMem c { s with core := { s.core with flags := fl } } ⋆ R) m' → Jexit () m') :
    wp Γ Q X (finishSubPromoLoopExpr c.pArena c.pFlags sub_ref ssz Jexit) m := by
  have hcl := hsp.1.core_ok
  have hw := hsp.2.1
  have hwf := hw.arena.refs_wf sub_ref.toNat href
  have har_len : s.core.arena.length = c.arena_cap := hcl.arena_len_arr
  have har_le : s.core.arena_len ≤ c.arena_cap := hcl.arena_len_le
  have hmx_a := c.harena; unfold dimacsBound at hmx_a
  have hmx_v := c.hmaxv; unfold dimacsBound at hmx_v
  have hbd_all : sub_ref.toNat + 3 + fullArenaClauseSizeCore s.core sub_ref.toNat ≤
      s.core.arena.length := by
    have h1 := hwf.2.2.1; have h2 := hwf.2.2.2.1; omega
  change ssz.toNat = fullArenaClauseSizeCore s.core sub_ref.toNat at hssz
  dsimp only [finishSubPromoLoopExpr, fvOp]
  let Inv : Val i32 × PUnit → Mem 64 → Prop := fun (k, ()) mk =>
    k.toNat ≤ ssz.toNat ∧ ∃ fl : List (BitVec 32), fl.length = c.max_vars ∧
      (FullMem c { s with core := { s.core with flags := fl } } ⋆ R) mk
  refine wp_loop_inv Inv (fun (k, ()) _ => ssz.toNat - k.toNat)
    (fun _ hJs => by
      rw [wp_jump]
      exact hJs (0#32, ()) m ⟨Nat.zero_le _, s.core.flags, hcl.flags_len, hm⟩)
    (fun _ (k, ()) mk ⟨hk_le, fl, hfl_len, hmk⟩ hrec => ?_)
  rw [Blocks.get_here]; dsimp only
  viv_hsteps_nogrp
  · have hk_lt : k.toNat < ssz.toNat := by c0_bound
    have hk1 : (k + 1#32).toNat = k.toNat + 1 := by bv_omega
    have hidx_eq : (sub_ref + 3#64 + k.setWidth 64).toNat = sub_ref.toNat + 3 + k.toNat := by
      have := bv32_setWidth64_toNat k
      have : sub_ref.toNat + 3 + k.toNat < s.core.arena.length := by omega
      bv_omega
    have hidx_lt : (sub_ref + 3#64 + k.setWidth 64).toNat < s.core.arena.length := by
      rw [hidx_eq]; omega
    viv_hsteps_nogrp
    let lp := s.core.arena[(sub_ref + 3#64 + k.setWidth 64).toNat]'hidx_lt
    have hlp_mem : lp.toNat ∈ fullArenaClauseLitsCore s.core sub_ref.toNat := by
      refine (mem_fullArenaClauseLitsCore_iff hbd_all).mpr ⟨k.toNat, by omega, ?_⟩
      dsimp only [lp]
      exact congrArg BitVec.toNat (Option.some.inj (by
        rw [← List.getElem?_eq_getElem hidx_lt, hidx_eq, List.getElem?_eq_getElem (by omega)]))
    have hlp_lt : lp.toNat < 2 * s.core.cur_vars :=
      hw.arena.lits_lt sub_ref.toNat href hng _ hlp_mem
    have hvar_lt : ((lp >>> 1#32).setWidth 64).toNat < fl.length := by
      rw [bv32_setWidth64_toNat, bv32_lshr1_toNat, hfl_len]
      have := hcl.cur_vars_le; omega
    refine wp_join_group (ts := [i32]) (fun (_, ()) m54 => m54 = mk)
      (fun _ (fbit, ()) m54 hm54 => by
        subst hm54
        rw [Blocks.get_here]; dsimp only
        viv_hsteps_nogrp
        refine hrec (k + 1#32, ()) _ (by dsimp only; rw [hk1]; omega)
          ⟨by rw [hk1]; omega, _, ?_, by assumption⟩
        rw [List.length_set]; exact hfl_len)
      (fun _ hJ54 => by
        viv_hsteps_nogrp
        · exact hJ54 (64#32, ()) mk rfl
        · exact hJ54 (32#32, ()) mk rfl)
  · exact hJexit fl mk hfl_len hmk

private abbrev finishSubBranchExpr (h pArena sub_ref : Val i64) (cref hdr : Val i32)
    (is_red confl : Val .bool) : Expr Val Cont [i64] :=
  Expr.group (sig := [[]]) (fun _ => Blocks.cons (fun (_ : Tup Val []) =>
    finishMarkBtRet1Expr h cref confl) Blocks.nil) fun J19 =>
  fvOp (OpCode.add i64) (Arg.var h, Arg.imm 48, ()) fun p20 =>
  Expr.load i64 (Arg.var p20.fst) fun ld21 =>
  fvOp (OpCode.cmp .ult i64 .bool (by decide)) (Arg.var sub_ref, Arg.var ld21, ()) fun p22 =>
  Expr.jnz (Arg.var p22.fst)
    (fvOp (OpCode.mul i64) (Arg.var sub_ref, Arg.imm 4, ()) fun p23 =>
     fvOp (OpCode.add i64) (Arg.var pArena, Arg.var p23.fst, ()) fun p24 =>
     Expr.load i32 (Arg.var p24.fst) fun ld25 =>
     Expr.group (sig := [[]]) (fun _ => Blocks.cons (fun (_ : Tup Val []) =>
       Expr.jump J19.fst ()) Blocks.nil) fun J26 =>
     Expr.group (sig := [[]]) (fun _ => Blocks.cons (fun (_ : Tup Val []) =>
       Expr.group (sig := [[]]) (fun _ => Blocks.cons (fun (_ : Tup Val []) =>
         Expr.jump J26.fst ()) Blocks.nil) fun J28 =>
       Expr.jnz (Arg.var is_red)
         (fvOp (OpCode.and i32) (Arg.var ld25, Arg.imm 4194304, ()) fun p29 =>
          fvOp (OpCode.cmp .ne i32 .bool (by decide)) (Arg.var p29.fst, Arg.imm 0, ()) fun p30 =>
          Expr.jnz (Arg.var p30.fst)
            (fvOp (OpCode.and i32) (Arg.var hdr, Arg.imm 524287, ()) fun p31 =>
             fvOp (OpCode.and i32) (Arg.var ld25, Arg.imm 524287, ()) fun p32 =>
             Expr.group (sig := [[]]) (fun _ => Blocks.cons (fun (_ : Tup Val []) =>
               Expr.jump J28.fst ()) Blocks.nil) fun J33 =>
             fvOp (OpCode.cmp .ult i32 .bool (by decide))
               (Arg.var p31.fst, Arg.var p32.fst, ()) fun p34 =>
             Expr.jnz (Arg.var p34.fst)
               (fvOp (OpCode.mul i64) (Arg.var sub_ref, Arg.imm 4, ()) fun p35 =>
                fvOp (OpCode.add i64) (Arg.var pArena, Arg.var p35.fst, ()) fun p36 =>
                fvOp (OpCode.not i32) (Arg.imm 524287, ()) fun p37 =>
                fvOp (OpCode.and i32) (Arg.var ld25, Arg.var p37.fst, ()) fun p38 =>
                fvOp (OpCode.or i32) (Arg.var p38.fst, Arg.var p31.fst, ()) fun p39 =>
                Expr.store (Arg.var p39.fst) (Arg.var p36.fst) (Expr.jump J33.fst ()))
               (Expr.jump J33.fst ()))
            (Expr.jump J28.fst ()))
         (Expr.jump J28.fst ())) Blocks.nil) fun J27 =>
     Expr.jnz (Arg.var is_red)
       (Expr.jump J27.fst ())
       (fvOp (OpCode.and i32) (Arg.var ld25, Arg.imm 4194304, ()) fun p28 =>
        fvOp (OpCode.cmp .ne i32 .bool (by decide)) (Arg.var p28.fst, Arg.imm 0, ()) fun p29 =>
        Expr.jnz (Arg.var p29.fst)
          (fvOp (OpCode.mul i64) (Arg.var sub_ref, Arg.imm 4, ()) fun p30 =>
           fvOp (OpCode.add i64) (Arg.var pArena, Arg.var p30.fst, ()) fun p31 =>
           fvOp (OpCode.not i32) (Arg.imm 4194304, ()) fun p32 =>
           fvOp (OpCode.and i32) (Arg.var ld25, Arg.var p32.fst, ()) fun p33 =>
           Expr.store (Arg.var p33.fst) (Arg.var p31.fst)
             (Expr.group (sig := [[]]) (fun _ => Blocks.cons (fun (_ : Tup Val []) =>
                fvOp (OpCode.add i64) (Arg.var h, Arg.imm 488, ()) fun p35 =>
                Expr.load i64 (Arg.var p35.fst) fun ld36 =>
                fvOp (OpCode.add i64) (Arg.var ld36, Arg.imm 1, ()) fun p37 =>
                fvOp (OpCode.add i64) (Arg.var h, Arg.imm 488, ()) fun p38 =>
                Expr.store (Arg.var p37.fst) (Arg.var p38.fst)
                  (fvOp (OpCode.add i64) (Arg.var h, Arg.imm 800, ()) fun p39 =>
                   Expr.load i64 (Arg.var p39.fst) fun ld40 =>
                   fvOp (OpCode.add i64) (Arg.var sub_ref, Arg.imm 2, ()) fun p41 =>
                   fvOp (OpCode.mul i64) (Arg.var p41.fst, Arg.imm 4, ()) fun p42 =>
                   fvOp (OpCode.add i64) (Arg.var pArena, Arg.var p42.fst, ()) fun p43 =>
                   Expr.load i32 (Arg.var p43.fst) fun ld44 =>
                   finishSubPromoLoopExpr pArena ld40 sub_ref ld44 J26.fst)) Blocks.nil) fun J34 =>
              fvOp (OpCode.add i64) (Arg.var h, Arg.imm 496, ()) fun p35 =>
              Expr.load i64 (Arg.var p35.fst) fun ld36 =>
              fvOp (OpCode.cmp .ugt i64 .bool (by decide))
                (Arg.var ld36, Arg.imm 0, ()) fun p37 =>
              Expr.jnz (Arg.var p37.fst)
                (fvOp (OpCode.add i64) (Arg.var h, Arg.imm 496, ()) fun p38 =>
                 Expr.load i64 (Arg.var p38.fst) fun ld39 =>
                 fvOp (OpCode.sub i64) (Arg.var ld39, Arg.imm 1, ()) fun p40 =>
                 fvOp (OpCode.add i64) (Arg.var h, Arg.imm 496, ()) fun p41 =>
                 Expr.store (Arg.var p40.fst) (Arg.var p41.fst) (Expr.jump J34.fst ()))
                (Expr.jump J34.fst ())))
          (Expr.jump J27.fst ())))
    (Expr.jump J19.fst ())

private theorem finish_sub_branch_wp (Γ : Env)
    (hMark : Γ.Has "full_viv_mark_garb_m6" fullVivMarkGarbM6Spec)
    (hBt : Γ.Has "full_backtrack" fullBacktrackSpec)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {ext0 ext : List (BitVec 64)} {s0 s1 : FullState}
    {R : Mem 64 → Prop} {sub_ref : Val i64} {cref hdr : Val i32}
    {is_red confl : Val .bool} {m1 : Mem 64} {Q : Post [i64]} {X : XPost}
    (hst1 : VivFinishStateOk c F0 F_cur ext0 s0 ext s1)
    (hcref : cref.toNat ∈ fullArenaClauseRefs s1)
    (hsub_ne1 : sub_ref ≠ 0xFFFFFFFFFFFFFFFF#64)
    (hsub_ref : sub_ref ≠ 0xFFFFFFFFFFFFFFFF#64 → sub_ref ≠ 0xFFFFFFFFFFFFFFFE#64 →
      sub_ref.toNat ∈ fullArenaClauseRefs s1 ∧ fullArenaClauseGarb s1 sub_ref.toNat = false)
    (hm1 : (FullMem c s1 ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R)) m1)
    (hQ : VivFinishQ c F0 F_cur ext0 s0 R Q) :
    wp Γ Q X (finishSubBranchExpr c.hdr c.pArena sub_ref cref hdr is_red confl) m1 := by
  have hsp1 := hst1.2.2.1
  have hcl1 := hsp1.1.core_ok
  have hmx_a := c.harena; unfold dimacsBound at hmx_a
  let R' := m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R
  let J19Inv : Mem 64 → Prop := fun m' =>
    ∃ s', VivFinishStateOk c F0 F_cur ext0 s0 ext s' ∧
      cref.toNat ∈ fullArenaClauseRefs s' ∧ (FullMem c s' ⋆ R') m'
  dsimp only [finishSubBranchExpr, fvOp]
  refine wp_join0 J19Inv
    (fun _ m' ⟨s', hst', hcr', hm'⟩ => by
      rw [Blocks.get_here]
      exact finish_mark_bt_ret1_wp Γ hMark hBt hst' hcr' hm' hQ)
    (fun _ hJ19 => ?_)
  viv_hsteps_nogrp
  · have hsub_lt_al : sub_ref.toNat < s1.core.arena_len := by
      have hlt : sub_ref < BitVec.ofNat 64 s1.core.arena_len := by c0_bound
      have hal : s1.core.arena_len < 2 ^ 64 := by have := hcl1.arena_len_le; omega
      rw [BitVec.lt_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hal] at hlt
      exact hlt
    have hsub_ne2 : sub_ref ≠ 0xFFFFFFFFFFFFFFFE#64 := by
      intro h; subst h; have := hcl1.arena_len_le
      have hval : (0xFFFFFFFFFFFFFFFE#64 : BitVec 64).toNat = 2 ^ 64 - 2 := by decide
      omega
    obtain ⟨hsub_in, hsub_ng⟩ := hsub_ref hsub_ne1 hsub_ne2
    have hsub_wf := hsp1.2.1.arena.refs_wf sub_ref.toNat hsub_in
    have hsub_ar : sub_ref.toNat < s1.core.arena.length := by
      rw [hcl1.arena_len_arr]; have := hcl1.arena_len_le; omega
    viv_hsteps_nogrp
    let shdr := s1.core.arena[sub_ref.toNat]'hsub_ar
    have hshdr_eq : shdr = fullArenaHdr s1 sub_ref.toNat := by
      unfold fullArenaHdr fullArenaHdrCore
      rw [List.getElem?_eq_getElem hsub_ar, Option.getD_some]
    refine wp_join0 J19Inv
      (fun _ m' hinv => by rw [Blocks.get_here]; rw [wp_jump]; exact hJ19 m' hinv)
      (fun _ hJ26 => ?_)
    refine wp_join0 (fun m' => m' = m1)
      (fun _ m' hm' => by
        subst m'; rw [Blocks.get_here]; try dsimp only
        refine wp_join0 J19Inv
          (fun _ m2 hinv => by rw [Blocks.get_here]; rw [wp_jump]; exact hJ26 m2 hinv)
          (fun _ hJ28 => ?_)
        viv_hsteps_nogrp
        · refine wp_join0 J19Inv
            (fun _ m2 hinv => by rw [Blocks.get_here]; rw [wp_jump]; exact hJ28 m2 hinv)
            (fun _ hJ33 => ?_)
          viv_hsteps_nogrp
          · let nhdr := (shdr &&& ~~~0x7FFFF#32) ||| (hdr &&& 0x7FFFF#32)
            have h19 : (nhdr &&& 0x80000#32) =
                (fullArenaHdr s1 sub_ref.toNat &&& 0x80000#32) := by
              rw [← hshdr_eq]
              exact bv32_set_glue_mask shdr hdr 0x80000#32 (by decide) (by decide)
            have h23 : (nhdr &&& 0x800000#32) =
                (fullArenaHdr s1 sub_ref.toNat &&& 0x800000#32) := by
              rw [← hshdr_eq]
              exact bv32_set_glue_mask shdr hdr 0x800000#32 (by decide) (by decide)
            obtain ⟨hsp2, hrefs2, _⟩ := fullArena_setHdr_preserves_sparseW hsp1 hsub_in h19 h23
            have hst2 : VivFinishStateOk c F0 F_cur ext0 s0 ext _ :=
              vivFinishStateOk_trans hst1
                ⟨hst1.1, viv_ext_pres_refl _, hsp2, rfl, rfl,
                  Nat.le_refl _, rfl, hrefs2, rfl⟩
            exact hJ33 _ ⟨_, hst2, hrefs2.symm ▸ hcref, by assumption⟩
          · exact hJ33 m1 ⟨s1, hst1, hcref, hm1⟩
        · exact hJ28 m1 ⟨s1, hst1, hcref, hm1⟩
        · exact hJ28 m1 ⟨s1, hst1, hcref, hm1⟩)
      (fun _ hJ27 => ?_)
    viv_hsteps_nogrp
    · exact hJ27 m1 rfl
    · let chdr := shdr &&& ~~~0x400000#32
      have h19 : (chdr &&& 0x80000#32) = (fullArenaHdr s1 sub_ref.toNat &&& 0x80000#32) := by
        rw [← hshdr_eq]; exact bv32_clear_red_mask shdr 0x80000#32 (by decide)
      have h23 : (chdr &&& 0x800000#32) = (fullArenaHdr s1 sub_ref.toNat &&& 0x800000#32) := by
        rw [← hshdr_eq]; exact bv32_clear_red_mask shdr 0x800000#32 (by decide)
      refine wp_join0
        (fun m34 => ∃ nr' : BitVec 64,
          (FullMem c { s1 with core :=
            { s1.core with arena := s1.core.arena.set sub_ref.toNat chdr,
                           num_redundant := nr' } } ⋆ R') m34)
        (fun _ m34 ⟨nr', hm34⟩ => by
          rw [Blocks.get_here]; try dsimp only
          let ni' := s1.core.num_irred + 1#64
          obtain ⟨hsp2, hrefs2, hall2⟩ :=
            fullSparseInvW_set_hdr_non_gs hsp1 hsub_in chdr ni' nr' h19 h23
          let s2 : FullState := { s1 with core :=
            { s1.core with arena := s1.core.arena.set sub_ref.toNat chdr,
                           num_irred := ni', num_redundant := nr' } }
          have hsub2_in : sub_ref.toNat ∈ fullArenaClauseRefs s2 := hrefs2.symm ▸ hsub_in
          have hsub2_ng : fullArenaClauseGarb s2 sub_ref.toNat = false :=
            (hall2 sub_ref.toNat hsub_in).1.trans hsub_ng
          have hsub2_2_eq : (sub_ref + 2#64).toNat = sub_ref.toNat + 2 := by
            have := hcl1.arena_len_le; bv_omega
          have hsub2_2_lt : (sub_ref + 2#64).toNat < s2.core.arena.length := by
            rw [hsub2_2_eq, hsp2.1.core_ok.arena_len_arr]; have := hcl1.arena_len_le; omega
          viv_hsteps_nogrp
          have hssz_eq : (s2.core.arena[(sub_ref + 2#64).toNat]'hsub2_2_lt).toNat =
              fullArenaClauseSize s2 sub_ref.toNat := by
            unfold fullArenaClauseSize fullArenaClauseSizeCore
            have hget : s2.core.arena[sub_ref.toNat + 2]? =
                some (s2.core.arena[(sub_ref + 2#64).toNat]'hsub2_2_lt) := by
              rw [← hsub2_2_eq, List.getElem?_eq_getElem hsub2_2_lt]
            rw [hget, Option.getD_some]
          refine finish_sub_promo_loop_wp Γ hsp2 hsub2_in hsub2_ng hssz_eq (by assumption)
            fun fl m3 hfl_len hm3 => ?_
          have hsp3 := viv_with_flags hsp2 hfl_len
          have hst3 : VivFinishStateOk c F0 F_cur ext0 s0 ext _ :=
            vivFinishStateOk_trans hst1
              ⟨hst1.1, viv_ext_pres_refl _, hsp3, rfl, rfl,
                Nat.le_refl _, rfl, hrefs2, rfl⟩
          exact hJ26 m3 ⟨_, hst3, hrefs2.symm ▸ hcref, hm3⟩)
        (fun _ hJ34 => by
          viv_hsteps_nogrp
          · exact hJ34 _ ⟨_, by assumption⟩
          · exact hJ34 _ ⟨_, by assumption⟩)
    · exact hJ27 m1 rfl
  · exact hJ19 m1 ⟨s1, hst1, hcref, hm1⟩

/-! ## 4. Non-Subsumption Branch (Commit, Delete, Instantiate, Re-establish) -/

private abbrev finishNonsubBranchExpr (h : Val i64) (cref sz olen implied : Val i32)
    (has_ded used_red is_red confl all_done : Val .bool) : Expr Val Cont [i64] :=
  Expr.group (sig := [[]]) (fun _ => Blocks.cons (fun (_ : Tup Val []) =>
    Expr.group (sig := [[]]) (fun _ => Blocks.cons (fun (_ : Tup Val []) =>
      Expr.group (sig := [[]]) (fun _ => Blocks.cons (fun (_ : Tup Val []) =>
        Expr.group (sig := [[]]) (fun _ => Blocks.cons (fun (_ : Tup Val []) =>
          Expr.call (as := [i64, i32]) (bs := []) "full_viv_reestablish_m6"
            (Arg.var h, Arg.var cref, ()) fun _ => Expr.ret (Arg.imm 1, ())) Blocks.nil) fun J22 =>
        finishCondBtExpr h confl J22.fst) Blocks.nil) fun J21 =>
      Expr.jnz (Arg.var confl)
        (Expr.jump J21.fst ())
        (fvOp (OpCode.cmp .eq i32 .bool (by decide))
           (Arg.var implied, Arg.imm 4294967295, ()) fun p22 =>
         Expr.jnz (Arg.var p22.fst)
           (Expr.jnz (Arg.var all_done)
              (Expr.call (as := [i64, i32, i32]) (bs := [i64]) "full_viv_inst_m6"
                 (Arg.var h, Arg.var cref, Arg.var sz, ()) fun p23 =>
               fvOp (OpCode.cmp .ne i64 .bool (by decide))
                 (Arg.var p23.fst, Arg.imm 0, ()) fun p24 =>
               Expr.jnz (Arg.var p24.fst)
                 (Expr.group (sig := [[]]) (fun _ => Blocks.cons (fun (_ : Tup Val []) =>
                    Expr.ret (Arg.var p23.fst, ())) Blocks.nil) fun J25 =>
                  fvOp (OpCode.cmp .eq i64 .bool (by decide))
                    (Arg.var p23.fst, Arg.imm 1, ()) fun p26 =>
                  Expr.jnz (Arg.var p26.fst)
                    (Expr.call (as := [i64, i32]) (bs := []) "full_viv_reestablish_m6"
                       (Arg.var h, Arg.var cref, ()) fun _ => Expr.jump J25.fst ())
                    (Expr.jump J25.fst ()))
                 (Expr.jump J21.fst ()))
              (Expr.jump J21.fst ()))
           (Expr.jump J21.fst ()))) Blocks.nil) fun J20 =>
    Expr.jnz (Arg.var has_ded)
      (Expr.group (sig := [[]]) (fun _ => Blocks.cons (fun (_ : Tup Val []) =>
         Expr.group (sig := [[]]) (fun _ => Blocks.cons (fun (_ : Tup Val []) =>
           finishMarkBtRet1Expr h cref confl) Blocks.nil) fun J22 =>
         Expr.jnz (Arg.var is_red)
           (Expr.jump J22.fst ())
           (Expr.jnz (Arg.var used_red) (Expr.jump J20.fst ()) (Expr.jump J22.fst ())))
         Blocks.nil) fun J21 =>
       Expr.jnz (Arg.var confl)
         (Expr.jump J21.fst ())
         (fvOp (OpCode.cmp .ne i32 .bool (by decide))
            (Arg.var implied, Arg.imm 4294967295, ()) fun p22 =>
          Expr.jnz (Arg.var p22.fst) (Expr.jump J21.fst ()) (Expr.jump J20.fst ())))
      (Expr.jump J20.fst ())) Blocks.nil) fun J19 =>
  Expr.jnz (Arg.var has_ded)
    (fvOp (OpCode.cmp .ult i32 .bool (by decide)) (Arg.var olen, Arg.var sz, ()) fun p20 =>
     Expr.jnz (Arg.var p20.fst)
       (Expr.group (sig := [[i32]]) (fun _ => Blocks.cons (fun p22 =>
          Expr.call (as := [i64, i32, i32, i32]) (bs := [i64]) "full_viv_commit_m6"
            (Arg.var h, Arg.var cref, Arg.var olen, Arg.var p22.fst, ()) fun p23 =>
          Expr.group (sig := [[]]) (fun _ => Blocks.cons (fun (_ : Tup Val []) =>
            Expr.ret (Arg.var p23.fst, ())) Blocks.nil) fun J24 =>
          fvOp (OpCode.cmp .eq i64 .bool (by decide))
            (Arg.var p23.fst, Arg.imm 1, ()) fun p25 =>
          Expr.jnz (Arg.var p25.fst)
            (Expr.call (as := [i64, i32]) (bs := []) "full_viv_reestablish_m6"
               (Arg.var h, Arg.var cref, ()) fun _ => Expr.jump J24.fst ())
            (Expr.jump J24.fst ())) Blocks.nil) fun J21 =>
        Expr.jnz (Arg.var confl)
          (Expr.jump J21.fst (Arg.imm 4294967295, ()))
          (Expr.jump J21.fst (Arg.var implied, ())))
       (Expr.jump J19.fst ()))
    (Expr.jump J19.fst ())

private theorem finish_reest_ret_wp (Γ : Env)
    (hReest : Γ.Has "full_viv_reestablish_m6" fullVivReestablishM6Spec)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {ext0 ext : List (BitVec 64)} {s0 s : FullState}
    {R : Mem 64 → Prop} {cref : Val i32} {r : Val i64} {m : Mem 64}
    {Q : Post [i64]} {X : XPost}
    (hst : VivFinishStateOk c F0 F_cur ext0 s0 ext s)
    (hcref : cref.toNat ∈ fullArenaClauseRefs s)
    (hr : r = 1#64 ∨ r = 2#64 ∨ r = 20#64) (hunsat : r = 20#64 → F0.Unsat)
    (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hQ : VivFinishQ c F0 F_cur ext0 s0 R Q) :
    wp Γ Q X
      (Expr.group (sig := [[]]) (fun _ => Blocks.cons (fun (_ : Tup Val []) =>
        Expr.ret (Arg.var r, ())) Blocks.nil) fun J =>
       fvOp (OpCode.cmp .eq i64 .bool (by decide)) (Arg.var r, Arg.imm 1, ()) fun peq =>
       Expr.jnz (Arg.var peq.fst)
         (Expr.call (as := [i64, i32]) (bs := []) "full_viv_reestablish_m6"
            (Arg.var c.hdr, Arg.var cref, ()) fun _ => Expr.jump J.fst ())
         (Expr.jump J.fst ())) m := by
  dsimp only [fvOp]
  refine wp_join0
    (fun m' => ∃ s', VivFinishStateOk c F0 F_cur ext0 s0 ext s' ∧ (FullM6HdrMem c ext s' ⋆ R) m')
    (fun _ m' ⟨s', hst', hm'⟩ => by
      rw [Blocks.get_here]
      viv_hsteps_nogrp
      exact hQ r ext s' m' hst' hr hunsat hm')
    (fun _ hJ => ?_)
  viv_hsteps_nogrp
  · viv_call hReest
    refine ⟨c, F0, F_cur, s, m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R, rfl, hst.2.2.1, hcref,
      fullM6HdrMem_focus_full hm, ?_⟩
    intro s' m' hsp' hcv' har' hal' hpr' hfu' hrr' _ hmF'
    have hrefs' : fullArenaClauseRefs s' = fullArenaClauseRefs s := by
      unfold fullArenaClauseRefs fullArenaClauseRefsCore; rw [har', hal']
    have hst' : VivFinishStateOk c F0 F_cur ext0 s0 ext s' :=
      vivFinishStateOk_trans hst
        ⟨hst.1, viv_ext_pres_refl _, hsp', hcv', hpr',
          by rw [hfu']; exact Nat.le_refl _, hal', hrefs', hrr'⟩
    try rw [wp_jump]
    exact hJ m' ⟨s', hst', fullM6HdrMem_unfocus_full hmF'⟩
  · exact hJ m ⟨s, hst, hm⟩

private theorem finish_nonsub_branch_wp (Γ : Env)
    (hMark : Γ.Has "full_viv_mark_garb_m6" fullVivMarkGarbM6Spec)
    (hBt : Γ.Has "full_backtrack" fullBacktrackSpec)
    (hCommit : Γ.Has "full_viv_commit_m6" fullVivCommitM6Spec)
    (hReest : Γ.Has "full_viv_reestablish_m6" fullVivReestablishM6Spec)
    (hInst : Γ.Has "full_viv_inst_m6" vivInstM6Spec)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {ext0 ext : List (BitVec 64)} {s0 s1 : FullState}
    {R : Mem 64 → Prop} {cref sz olen implied : Val i32}
    {has_ded used_red is_red confl all_done : Val .bool}
    {m1 : Mem 64} {Q : Post [i64]} {X : XPost}
    (hcfg : FullM6HdrCfgOk c)
    (hst1 : VivFinishStateOk c F0 F_cur ext0 s0 ext s1)
    (hsz_le : sz.toNat ≤ c.max_vars)
    (hcref : cref.toNat ∈ fullArenaClauseRefs s1)
    (hng1 : fullArenaClauseGarb s1 cref.toNat = false)
    (hsz1 : fullArenaClauseSize s1 cref.toNat = sz.toNat)
    (hperm1 : ((s1.core.tmp.take sz.toNat).map BitVec.toNat).Perm
      (fullArenaClauseLits s1 cref.toNat))
    (hded : has_ded = true →
      olen.toNat ≤ s1.core.cur_vars ∧
      (∀ k < olen.toNat, (s1.scratch.work_stk2[k]?.getD 0#32).toNat < 2 * s1.core.cur_vars) ∧
      ((s1.scratch.work_stk2.take olen.toNat).map fun x => x.toNat / 2).Nodup ∧
      (cnfOfClauses F_cur).EntailsClause
        (cnfClause ((s1.scratch.work_stk2.take olen.toNat).map BitVec.toNat)))
    (hm1 : (FullMem c s1 ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R)) m1)
    (hQ : VivFinishQ c F0 F_cur ext0 s0 R Q) :
    wp Γ Q X (finishNonsubBranchExpr c.hdr cref sz olen implied
      has_ded used_red is_red confl all_done) m1 := by
  dsimp only [finishNonsubBranchExpr, fvOp]
  refine wp_join0 (fun m' => m' = m1)
    (fun _ m' hm' => by
      subst m'; rw [Blocks.get_here]; try dsimp only
      refine wp_join0 (fun m' => m' = m1)
        (fun _ m' hm' => by
          subst m'; rw [Blocks.get_here]; try dsimp only
          refine wp_join0
            (fun m2 => ∃ (ext2 : List (BitVec 64)) (s2 : FullState),
              VivFinishStateOk c F0 F_cur ext0 s0 ext2 s2 ∧
              cref.toNat ∈ fullArenaClauseRefs s2 ∧ (FullM6HdrMem c ext2 s2 ⋆ R) m2)
            (fun _ m2 ⟨ext2, s2, hst2, hcr2, hm2⟩ => by
              rw [Blocks.get_here]; try dsimp only
              refine wp_join0
                (fun m3 => ∃ s3, VivFinishStateOk c F0 F_cur ext0 s0 ext2 s3 ∧
                  cref.toNat ∈ fullArenaClauseRefs s3 ∧
                  (FullMem c s3 ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext2 ⋆ R)) m3)
                (fun _ m3 ⟨s3, hst3, hcr3, hm3⟩ => by
                  rw [Blocks.get_here]; try dsimp only
                  viv_call hReest
                  refine ⟨c, F0, F_cur, s3, m6ExtMem (m6ExtAddr c.hdr) ext2 ⋆ R, rfl,
                    hst3.2.2.1, hcr3, hm3, ?_⟩
                  intro s4 m4 hsp4 hcv4 har4 hal4 hpr4 hfu4 hrr4 _ hm4
                  have hrefs4 : fullArenaClauseRefs s4 = fullArenaClauseRefs s3 := by
                    unfold fullArenaClauseRefs fullArenaClauseRefsCore; rw [har4, hal4]
                  have hst4 : VivFinishStateOk c F0 F_cur ext0 s0 ext2 s4 :=
                    vivFinishStateOk_trans hst3
                      ⟨hst3.1, viv_ext_pres_refl _, hsp4, hcv4, hpr4,
                        by rw [hfu4]; exact Nat.le_refl _, hal4, hrefs4, hrr4⟩
                  viv_hsteps_nogrp
                  exact hQ 1#64 ext2 s4 m4 hst4 (Or.inl rfl) (fun h => by cases h)
                    (fullM6HdrMem_unfocus_full hm4))
                (fun _ hJ22 => finish_cond_bt_wp Γ hBt hst2 (fullM6HdrMem_focus_full hm2)
                  fun s3 m3 hst3 hm3 => hJ22 m3 ⟨s3, hst3,
                    by rw [hst3.2.2.2.2.2.2.2.1, ← hst2.2.2.2.2.2.2.2.1]; exact hcr2, hm3⟩))
            (fun _ hJ21 => ?_)
          viv_hsteps_nogrp
          · exact hJ21 m1 ⟨ext, s1, hst1, hcref, fullM6HdrMem_unfocus_full hm1⟩
          · viv_call hInst
            refine ⟨c, F0, F_cur, ext, s1, R, rfl, hcfg, hst1.1, hst1.2.2.1,
              hcref, hng1, hsz1, hsz_le, hperm1, fullM6HdrMem_unfocus_full hm1, ?_⟩
            intro ir ext2 s2 m2 hext2 hpr_ext2 hsp2 hcv2 hpr2 hfu2 hal2 hrefs2 hrr2
              hir hunsat2 hm2
            have hst2 : VivFinishStateOk c F0 F_cur ext0 s0 ext2 s2 :=
              vivFinishStateOk_trans hst1
                ⟨hext2, hpr_ext2, hsp2, hcv2, hpr2, hfu2, hal2, hrefs2, hrr2⟩
            have hcr2 : cref.toNat ∈ fullArenaClauseRefs s2 := hrefs2.symm ▸ hcref
            viv_hsteps_nogrp
            · have hir_ne0 : ir ≠ 0#64 := by c0_bound
              have hir' : ir = 1#64 ∨ ir = 2#64 ∨ ir = 20#64 := by
                rcases hir with rfl | hrest
                · exact absurd rfl hir_ne0
                · exact hrest
              exact finish_reest_ret_wp Γ hReest hst2 hcr2 hir' hunsat2 hm2 hQ
            · exact hJ21 m2 ⟨ext2, s2, hst2, hcr2, hm2⟩
          · exact hJ21 m1 ⟨ext, s1, hst1, hcref, fullM6HdrMem_unfocus_full hm1⟩
          · exact hJ21 m1 ⟨ext, s1, hst1, hcref, fullM6HdrMem_unfocus_full hm1⟩)
        (fun _ hJ20 => ?_)
      viv_hsteps_nogrp
      · refine wp_join0 (fun m' => m' = m1)
          (fun _ m' hm' => by
            subst m'; rw [Blocks.get_here]; try dsimp only
            refine wp_join0 (fun m' => m' = m1)
              (fun _ m' hm' => by
                subst m'; rw [Blocks.get_here]; try dsimp only
                exact finish_mark_bt_ret1_wp Γ hMark hBt hst1 hcref hm1 hQ)
              (fun _ hJ22 => by
                viv_hsteps_nogrp
                · exact hJ22 m1 rfl
                · exact hJ20 m1 rfl
                · exact hJ22 m1 rfl))
          (fun _ hJ21 => by
            viv_hsteps_nogrp
            · exact hJ21 m1 rfl
            · exact hJ21 m1 rfl
            · exact hJ20 m1 rfl)
      · exact hJ20 m1 rfl)
    (fun _ hJ19 => ?_)
  viv_hsteps_nogrp
  · have hhd : has_ded = true := by c0_bound
    have holen_lt : olen.toNat < sz.toNat := by c0_bound
    obtain ⟨_, hws2_lt, hws2_nd, hws2_ent⟩ := hded hhd
    refine wp_join_group (ts := [i32]) (fun (_, ()) m' => m' = m1)
      (fun _ (imp_c, ()) m' hm' => by
        subst m'; rw [Blocks.get_here]; try dsimp only
        viv_call hCommit
        refine ⟨c, F0, F_cur, s1, m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R, rfl, hst1.2.2.1,
          hcref, hng1, by omega, fun _ => ⟨hws2_lt, hws2_nd, hws2_ent⟩, hm1, ?_⟩
        intro cr s2 m2 hsp2 hcv2 hal2 hpr2 hfu2 hrefs2 hrr2 _ hcr hunsat2 hm2
        have hst2 : VivFinishStateOk c F0 F_cur ext0 s0 ext s2 :=
          vivFinishStateOk_trans hst1
            ⟨hst1.1, viv_ext_pres_refl _, hsp2, hcv2, hpr2,
              by rw [hfu2]; exact Nat.le_refl _, hal2, hrefs2, hrr2⟩
        exact finish_reest_ret_wp Γ hReest hst2 (hrefs2.symm ▸ hcref) hcr hunsat2
          (fullM6HdrMem_unfocus_full hm2) hQ)
      (fun _ hJ21 => by
        viv_hsteps_nogrp
        · exact hJ21 (0xFFFFFFFF#32, ()) m1 rfl
        · exact hJ21 (implied, ()) m1 rfl)
  · exact hJ19 m1 rfl
  · exact hJ19 m1 rfl

/-! ## 5. Top-Level `full_viv_finish_m6_wp` Certification -/

/-- Certification of `full_viv_finish_m6` against `Spec.vivFinishM6Spec`. -/
theorem full_viv_finish_m6_wp (Γ : Env)
    (hDed : Γ.Has "full_viv_deduce_m6" Spec.vivDeduceM6Spec)
    (hMark : Γ.Has "full_viv_mark_garb_m6" Spec.fullVivMarkGarbM6Spec)
    (hBt : Γ.Has "full_backtrack" fullBacktrackSpec)
    (hCommit : Γ.Has "full_viv_commit_m6" Spec.fullVivCommitM6Spec)
    (hReest : Γ.Has "full_viv_reestablish_m6" Spec.fullVivReestablishM6Spec)
    (hInst : Γ.Has "full_viv_inst_m6" Spec.vivInstM6Spec) :
    ∀ a m Q X, Spec.vivFinishM6Spec a m Q X →
      Func.wp Γ full_viv_finish_m6_body a m Q X := by
  rintro ⟨h, cref, sz, confl, implied, all_done, ⟨⟩⟩ m0 Q X
    ⟨c, F0, F_cur, ext, s0, R, rfl, hcfg, hext, hsp0, hsz_le, href0, hng0, hsz0, hperm0,
      hconfl0, himp0, hall0, hm0, hQ0⟩
  have hQ : VivFinishQ c F0 F_cur ext s0 R Q :=
    fun r ext' s' m' hst hr hunsat hm' =>
      hQ0 r ext' s' m' hst.1 hst.2.1 hst.2.2.1 hst.2.2.2.1 hst.2.2.2.2.1
        hst.2.2.2.2.2.1 hst.2.2.2.2.2.2.1 hst.2.2.2.2.2.2.2.1 hst.2.2.2.2.2.2.2.2
        hr hunsat hm'
  have htmp_lt0 := finish_tmp_lits_lt hsp0 hsz_le href0 hng0 hperm0
  let R' := m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R
  have hm0F := fullM6HdrMem_focus_full hm0
  unfold Func.wp full_viv_finish_m6_body
  viv_hsteps_nogrp
  let s_pre : FullState :=
    { s0 with scratch := { s0.scratch with ant_sz := 0xFFFFFFFFFFFFFFFF#64, res_sz := 0#64 } }
  have hsp_pre : FullSparseInvW c F0 F_cur s_pre := viv_with_ant_res hsp0 (-1#64) 0#64
  have hst_pre : VivFinishStateOk c F0 F_cur ext s0 ext s_pre :=
    ⟨hext, viv_ext_pres_refl _, hsp_pre, rfl, rfl, Nat.le_refl _, rfl, rfl, rfl⟩
  let J4Inv : Tup Val [i32, .bool] → Mem 64 → Prop := fun (olen, has_ded, ()) m1 =>
    ∃ s1 : FullState,
      VivFinishStateOk c F0 F_cur ext s0 ext s1 ∧
      s1.core.tmp = s0.core.tmp ∧
      cref.toNat ∈ fullArenaClauseRefs s1 ∧
      fullArenaClauseGarb s1 cref.toNat = false ∧
      fullArenaClauseSize s1 cref.toNat = sz.toNat ∧
      fullArenaClauseLits s1 cref.toNat = fullArenaClauseLits s0 cref.toNat ∧
      (s1.scratch.ant_sz ≠ 0xFFFFFFFFFFFFFFFF#64 → s1.scratch.ant_sz ≠ 0xFFFFFFFFFFFFFFFE#64 →
        s1.scratch.ant_sz.toNat ∈ fullArenaClauseRefs s1 ∧
        fullArenaClauseGarb s1 s1.scratch.ant_sz.toNat = false) ∧
      (has_ded = true → s1.scratch.ant_sz = 0xFFFFFFFFFFFFFFFF#64 →
        olen.toNat ≤ s1.core.cur_vars ∧
        (∀ k < olen.toNat, (s1.scratch.work_stk2[k]?.getD 0#32).toNat < 2 * s1.core.cur_vars) ∧
        ((s1.scratch.work_stk2.take olen.toNat).map fun x => x.toNat / 2).Nodup ∧
        (cnfOfClauses F_cur).EntailsClause
          (cnfClause ((s1.scratch.work_stk2.take olen.toNat).map BitVec.toNat))) ∧
      (FullMem c s1 ⋆ R') m1
  refine wp_join_group (ts := [i32, .bool]) J4Inv
    (fun _ (olen, has_ded, ()) m1 ⟨s1, hst1, htmp1, hcr1, hng1, hsz1, hlits1, hasz_ref,
        hded1, hm1⟩ => by
      rw [Blocks.get_here]; dsimp only
      have hsp1 := hst1.2.2.1
      have hcl1 := hsp1.1.core_ok
      have hcr1_wf := hsp1.2.1.arena.refs_wf cref.toNat hcr1
      have hcr1_ar : (cref.setWidth 64).toNat < s1.core.arena.length := by
        rw [bv32_setWidth64_toNat, hcl1.arena_len_arr]; have := hcl1.arena_len_le; omega
      viv_hsteps_nogrp
      · have hsub_ne1 : s1.scratch.ant_sz ≠ 0xFFFFFFFFFFFFFFFF#64 := by c0_bound
        exact finish_sub_branch_wp Γ hMark hBt hst1 hcr1 hsub_ne1 hasz_ref hm1 hQ
      · have hsub_eq1 : s1.scratch.ant_sz = 0xFFFFFFFFFFFFFFFF#64 := by c0_bound
        have hperm1 : ((s1.core.tmp.take sz.toNat).map BitVec.toNat).Perm
            (fullArenaClauseLits s1 cref.toNat) := by rw [htmp1, hlits1]; exact hperm0
        exact finish_nonsub_branch_wp Γ hMark hBt hCommit hReest hInst hcfg hst1 hsz_le
          hcr1 hng1 hsz1 hperm1 (fun hd => hded1 hd hsub_eq1) hm1 hQ)
    (fun _ hJ4 => ?_)
  refine wp_join0
    (fun mj => (confl = true ∨ implied ≠ 0xFFFFFFFF#32 ∨ all_done = true) ∧
      (FullMem c s_pre ⋆ R') mj)
    (fun _ mj ⟨hdisj, hmj⟩ => by
      rw [Blocks.get_here]; dsimp only
      refine wp_join_group (ts := [i32])
        (fun (imp_arg, ()) mk =>
          (imp_arg = 0xFFFFFFFF#32 →
            FullVivConflictOk F_cur s_pre ∨
            s_pre.core.confl_type = 0#64 ∧
              ∀ l ∈ fullArenaClauseLits s_pre cref.toNat, s_pre.core.vals[l]?.getD 0#8 = 0xFF#8) ∧
          (imp_arg ≠ 0xFFFFFFFF#32 →
            imp_arg.toNat < 2 * s_pre.core.cur_vars ∧
              s_pre.core.vals[imp_arg.toNat]?.getD 0#8 = 1#8) ∧
          (FullMem c s_pre ⋆ R') mk)
        (fun _ (imp_arg, ()) mk ⟨hcf_d, himp_d, hmk⟩ => by
          rw [Blocks.get_here]; dsimp only
          viv_call hDed
          refine ⟨c, F0, F_cur, s_pre, R', rfl, hsp_pre, href0, hng0, hsz_le, htmp_lt0,
            hcf_d, himp_d, hmk, ?_⟩
          intro olen ar' mclr' mrk' lm' ws1' ws2' asz' rsz' m1 _
            hsp1 _ hasz_ref hrefs1 hcl1 hent1 _ hm1
          let s1 : FullState :=
            { s_pre with
              core := { s_pre.core with
                arena := ar', min_clr := mclr', mrk := mrk', lit_mark := lm' }
              scratch := { s_pre.scratch with
                work_stk1 := ws1', work_stk2 := ws2', ant_sz := asz', res_sz := rsz' } }
          have hst1 : VivFinishStateOk c F0 F_cur ext s0 ext s1 :=
            ⟨hext, viv_ext_pres_refl _, hsp1, rfl, rfl, Nat.le_refl _,
              rfl, hrefs1, rfl⟩
          obtain ⟨hg1, hsz1_eq, hl1⟩ := hcl1 cref.toNat href0
          viv_hsteps_nogrp
          refine hJ4 (olen, decide (olen ≠ 0xFFFFFFFF#32), ()) m1
            ⟨s1, hst1, rfl, hrefs1.symm ▸ href0, hg1.trans hng0, hsz1_eq.trans hsz0, hl1,
              hasz_ref, fun hhd hasz => hent1 hasz (of_decide_eq_true hhd), hm1⟩)
        (fun _ hJ6 => by
          viv_hsteps_nogrp
          · have hcf_t : confl = true := by c0_bound
            exact hJ6 (0xFFFFFFFF#32, ()) mj
              ⟨fun _ => Or.inl (viv_conflictOkW_to_viv (hconfl0 hcf_t)),
                fun h => absurd rfl h, hmj⟩
          · have hcf_f : confl = false := by c0_bound
            refine hJ6 (implied, ()) mj ⟨fun himp => ?_, himp0 hcf_f, hmj⟩
            rcases hdisj with ht | hne | had
            · rw [hcf_f] at ht; cases ht
            · exact absurd himp hne
            · exact Or.inr (hall0 hcf_f himp had)))
    (fun _ hJ5 => ?_)
  viv_hsteps_nogrp
  · have hcf_t : confl = true := by c0_bound
    exact hJ5 _ ⟨Or.inl hcf_t, by assumption⟩
  · have hne : implied ≠ 0xFFFFFFFF#32 := by c0_bound
    exact hJ5 _ ⟨Or.inr (Or.inl hne), by assumption⟩
  · have had : all_done = true := by c0_bound
    exact hJ5 _ ⟨Or.inr (Or.inr had), by assumption⟩
  · exact hJ4 (sz, false, ()) _
      ⟨s_pre, hst_pre, rfl, href0, hng0, hsz0, rfl,
        fun h => absurd rfl h, fun h => Bool.noConfusion h, by assumption⟩

end

end LeanQbe.T.Examples.Kissat.Proof.Vivify
