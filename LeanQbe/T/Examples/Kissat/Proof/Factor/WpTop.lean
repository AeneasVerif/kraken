/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Src.Factor
public import LeanQbe.T.Examples.Kissat.Proof.Factor.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Factor.WpTop0
public import LeanQbe.T.Logic.CanonicalEnv
import LeanQbe.T.Examples.Kissat.Proof.Factor.Helpers
import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena
import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena1
import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts
import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts1
import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts3
import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts4
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics1
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Top-Level BVA Literal Trial WP (`Proof.Factor.WpTop`)

Proves `full_bva_try_lit_wp` (`14/15`) for `Src.Factor.full_bva_try_lit_body` against
`Spec.step7BvaTryLitSpec` (`0` legacy imports, `0` placeholders, `XPost`-polymorphic,
explicit `Γ.Has` parameters for all callees).
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Factor

open Std Std.Sat Std.ExtHashMap Kraken.Bedrock2.Test
open LeanQbe.T LeanQbe.T.ProofUtil LeanQbe.T.C0Step LeanQbe.T.C0HeadStep
open LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Ref LeanQbe.T.Examples.Kissat.Src.Factor
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Spec.FullBvaHeapHelpers
open LeanQbe.T.Examples.Kissat.Proof.Spec.FullBvaHeapTactics
open LeanQbe.T.Examples.Kissat.Proof.Spec.FullBvaHeapScanHelpers
open LeanQbe.T.Examples.Kissat.Proof.Factor.Spec
open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullBvaHeapTactics

/-! ## 1. Row-0 Watch Scan Helpers -/

private theorem step0_row0_cap {cap : Nat} (hcap : cap < 2 ^ 28)
    (hc : ¬((BitVec.ofNat 64 cap -
      BitVec.setWidth 64 (BitVec.ofNat 32 (fidStepsCap (cap % 2 ^ 64)) <<< OfNat.ofNat 2)) /
      3).toNat % 2 ^ 32 < BitVec.toNat (2 : BitVec 32)) : 2 ≤ (cap - 4 * fidStepsCap cap) / 3 := by
  have hsc_le := fidStepsCap_le_256 cap; have h4sc := fidStepsCap_mul4_le cap
  have hmod : cap % 2 ^ 64 = cap := Nat.mod_eq_of_lt (by omega)
  rw [hmod] at hc
  have hlt : ((BitVec.ofNat 64 cap -
      BitVec.setWidth 64 (BitVec.ofNat 32 (fidStepsCap cap) <<< OfNat.ofNat 2)) / 3).toNat =
      (cap - 4 * fidStepsCap cap) / 3 := by
    simp only [BitVec.toNat_udiv, BitVec.toNat_sub, BitVec.toNat_setWidth,
      BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, show (OfNat.ofNat 2 : Nat) = 2 from rfl,
      show (3 : BitVec 64).toNat = 3 from rfl, Nat.shiftLeft_eq]
    rw [show fidStepsCap cap % 2 ^ 32 * 2 ^ 2 % 2 ^ 32 % 2 ^ 64 = 4 * fidStepsCap cap by omega,
      hmod, show (2 ^ 64 - 4 * fidStepsCap cap + cap) % 2 ^ 64 = cap - 4 * fidStepsCap cap by omega]
  rw [hlt, show BitVec.toNat (2 : BitVec 32) = 2 from rfl, Nat.mod_eq_of_lt (by omega)] at hc
  omega

private theorem step0_rowOk_push {F_cur : List (List Nat)} {s : FullState} {f0 : Nat}
    {sb : List (BitVec 32)} {sc r0n : Nat} {entry : BitVec 32}
    (hsb : sb.length = s.scratch.scratch_buf.length) (h4sc : 4 * sc + r0n < sb.length)
    (hprev : step0RowOk F_cur s f0 sb sc r0n)
    (hnew : ∃ res, (∀ x ∈ res, x < 2 * s.core.cur_vars) ∧ (res.map (· / 2)).Nodup ∧
      FidBvaRowEntryOk F_cur s f0 entry res ∧
      (cnfOfClauses F_cur).EntailsClause (cnfClause (f0 :: res))) :
    step0RowOk F_cur s f0 (sb.set (4 * sc + r0n) entry) sc (r0n + 1) := by
  intro j hj; rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj_lt | rfl
  · obtain ⟨res, h1, h2, h3, h4⟩ := hprev j hj_lt; refine ⟨res, h1, h2, ?_, h4⟩
    rw [List.getElem?_eq_getElem (by rw [List.length_set]; omega), Option.getD_some,
      List.getElem_set_ne (by omega)]
    simpa only [List.getElem?_eq_getElem (by omega : 4 * sc + j < sb.length), Option.getD_some]
      using h3
  · obtain ⟨res, h1, h2, h3, h4⟩ := hnew
    exact ⟨res, h1, h2, by rw [List.getElem?_set_self h4sc, Option.getD_some]; exact h3, h4⟩

private theorem step0_dinv_sb_asz {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    {sb : List (BitVec 32)} {asz : BitVec 64} (h : FullDenseInv c F0 s)
    (hsb : sb.length = c.scratch_cap) :
    FullDenseInv c F0
      { core := s.core, scratch := { s.scratch with scratch_buf := sb, ant_sz := asz } } :=
  ⟨⟨⟨h.1.lengths.core_ok, { h.1.lengths.scratch_ok with scratch_buf_len := hsb }⟩, h.1.witness⟩,
   h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

private theorem step0_arena_lit_mem {k : FullCoreState} {cr j : Nat}
    (hcr_lt : cr + 3 + fullArenaClauseSizeCore k cr ≤ k.arena.length)
    (hj : j < fullArenaClauseSizeCore k cr) :
    (k.arena[cr + 3 + j]?.getD 0#32).toNat ∈ fullArenaClauseLitsCore k cr := by
  unfold fullArenaClauseLitsCore; rw [List.mem_map]
  refine ⟨k.arena[cr + 3 + j]'(by omega), ?_,
    by simp [List.getElem?_eq_getElem (show cr + 3 + j < k.arena.length by omega)]⟩
  rw [List.mem_take_iff_getElem]
  exact ⟨j, Nat.lt_min.mpr ⟨hj, by rw [List.length_drop]; omega⟩, by simp [List.getElem_drop]⟩

private def step0ClauseExpr (pScratchBuf pArena pVals : Val i64)
    (sc4 r0n f0 cr_bv sz_c : Val i32) (Js : Cont [i32]) : Expr Val Cont [.bool] :=
  Expr.group (sig := [[i32, .bool, .bool]]) (fun Js2 => Blocks.cons (fun p =>
    Expr.group (sig := [[i32]]) (fun Js3 => Blocks.cons (fun q => Expr.jump Js (Arg.var q.fst, ()))
      Blocks.nil) (fun Js3 => Expr.jnz (Arg.var p.snd.snd.fst)
      (Expr.jump Js3.fst (Arg.var r0n, ())) (Expr.jnz (Arg.var p.snd.fst)
        (Expr.let_ (Op.mk (.add i32) (Arg.var sc4, Arg.var r0n, ())) fun p1 =>
         Expr.let_ (Op.mk (.zext 32 64) (Arg.var p1.fst, ())) fun p2 =>
         Expr.let_ (Op.mk (.mul i64) (Arg.var p2.fst, Arg.imm 4, ())) fun p3 =>
         Expr.let_ (Op.mk (.add i64) (Arg.var pScratchBuf, Arg.var p3.fst, ())) fun p4 =>
         Expr.store (Arg.var cr_bv) (Arg.var p4.fst) (Expr.let_ (Op.mk (.add i32)
           (Arg.var r0n, Arg.imm 1, ())) fun p5 => Expr.jump Js3.fst (Arg.var p5.fst, ())))
        (Expr.jump Js3.fst (Arg.var r0n, ()))))) Blocks.nil)
  (fun Js2 => Expr.group (sig := [[i32, .bool]]) (fun Js3 => Blocks.cons (fun q =>
    Expr.let_ (Op.mk (.cmp .ult i32) (Arg.var q.fst, Arg.var sz_c, ())) fun p67 =>
    Expr.jnz (Arg.var p67.fst)
    (Expr.let_ (Op.mk (.zext 32 64) (Arg.var cr_bv, ())) fun p68 =>
     Expr.let_ (Op.mk (.add i64) (Arg.var p68.fst, Arg.imm 3, ())) fun p69 =>
     Expr.let_ (Op.mk (.zext 32 64) (Arg.var q.fst, ())) fun p70 =>
     Expr.let_ (Op.mk (.add i64) (Arg.var p69.fst, Arg.var p70.fst, ())) fun p71 =>
     Expr.let_ (Op.mk (.mul i64) (Arg.var p71.fst, Arg.imm 4, ())) fun p72 =>
     Expr.let_ (Op.mk (.add i64) (Arg.var pArena, Arg.var p72.fst, ())) fun p73 =>
     Expr.load i32 (Arg.var p73.fst) fun lit =>
     Expr.let_ (Op.mk (.zext 32 64) (Arg.var lit, ())) fun p74 =>
     Expr.let_ (Op.mk (.add i64) (Arg.var pVals, Arg.var p74.fst, ())) fun p75 =>
     Expr.load i8 (Arg.var p75.fst) fun val =>
     Expr.let_ (Op.mk (.trunc 32 8) (Arg.imm 0, ())) fun p76 =>
     Expr.let_ (Op.mk (.sext 8 32) (Arg.var val, ())) fun p77 =>
     Expr.let_ (Op.mk (.sext 8 32) (Arg.var p76.fst, ())) fun p78 =>
     Expr.let_ (Op.mk (.cmp .sgt i32) (Arg.var p77.fst, Arg.var p78.fst, ())) fun p79 =>
     Expr.jnz (Arg.var p79.fst)
       (Expr.jump Js2.fst (Arg.var q.fst, Arg.var q.snd.fst, Arg.imm true, ()))
       (Expr.group (sig := [[.bool]]) (fun Js4 => Blocks.cons (fun r =>
         Expr.let_ (Op.mk (.add i32) (Arg.var q.fst, Arg.imm 1, ())) fun p80 =>
         Expr.jump Js3.fst (Arg.var p80.fst, Arg.var r.fst, ())) Blocks.nil)
       (fun Js4 => Expr.let_ (Op.mk (.cmp .eq i32) (Arg.var lit, Arg.var f0, ())) fun p81 =>
         Expr.jnz (Arg.var p81.fst) (Expr.jump Js4.fst (Arg.imm true, ()))
           (Expr.jump Js4.fst (Arg.var q.snd.fst, ())))))
    (Expr.jump Js2.fst (Arg.var q.fst, Arg.var q.snd.fst, Arg.imm false, ()))) Blocks.nil)
  (fun Js3 => Expr.jump Js3.fst (Arg.imm (0 : BitVec 32), Arg.imm false, ())))

private theorem step0_clause_wp (Γ : Env) {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {R : Mem 64 → Prop} {Q : Post [.bool]} {X : XPost} {m : Mem 64}
    (Js : Cont [i32]) (sc : Nat) (sc4 r0n f0 cr_bv sz_c : Val i32) (hsc4 : sc4.toNat = 4 * sc)
    (_hsc_pos : 0 < sc) (_hsc_le : sc ≤ 256) (_h4sc_cap : 4 * sc ≤ c.scratch_cap)
    (hlen : FullState.LengthsOk c s) (hdinv : FullDenseInvW c F0 F_cur s)
    (hcr_ref : cr_bv.toNat ∈ fullArenaClauseRefsCore s.core)
    (hcr_garb : fullArenaClauseGarbCore s.core cr_bv.toNat = false)
    (hsz_eq : fullArenaClauseSizeCore s.core cr_bv.toNat = sz_c.toNat)
    (h3le : 3 ≤ sz_c.toNat) (hle5 : sz_c.toNat ≤ 5) (_hf0_lt : f0.toNat < 2 * s.core.cur_vars)
    (_hr0n_lt : r0n.toNat < (c.scratch_cap - 4 * sc) / 3)
    (h4sc_r0 : 4 * sc + r0n.toNat < c.scratch_cap) (hm : (FullMem c s ⋆ R) m)
    (hJs_same : ∀ m', (FullMem c s ⋆ R) m' → Js (r0n, ()) m')
    (hJs_push : ∀ (m' : Mem 64) (res : List Nat),
      (∀ x ∈ res, x < 2 * s.core.cur_vars) → (res.map (· / 2)).Nodup →
      FidBvaRowEntryOk F_cur s f0.toNat cr_bv res →
      (cnfOfClauses F_cur).EntailsClause (cnfClause (f0.toNat :: res)) →
      (FullMem c { core := s.core, scratch := { s.scratch with
        scratch_buf := s.scratch.scratch_buf.set (4 * sc + r0n.toNat) cr_bv } } ⋆ R) m' →
      Js (r0n + 1#32, ()) m') :
    wp Γ Q X (step0ClauseExpr c.pScratchBuf c.pArena c.pVals sc4 r0n f0 cr_bv sz_c Js) m := by
  have hcl := hlen.core_ok; have hsc_l := hlen.scratch_ok
  have hmx : c.max_vars < 2 * 2 ^ 28 := c.hmaxv; have har_b : c.arena_cap < 2 * 2 ^ 28 := c.harena
  have hsc_c : c.scratch_cap < 2 ^ 28 := c.hscr; have hwit := hdinv.2.1
  have hcr_wf := hwit.arena.refs_wf cr_bv.toNat hcr_ref; have hcv_le := hcl.cur_vars_le
  have har_len := hcl.arena_len_le; have har_arr := hcl.arena_len_arr
  have hvals_len := hcl.vals_len; have hsb_len := hsc_l.scratch_buf_len
  refine wp_loop_break_group
    (fun (_jf, found_f, sat_f, ()) m' =>
      m' = m ∧ (sat_f = false → found_f = true →
        f0.toNat ∈ fullArenaClauseLitsCore s.core cr_bv.toNat))
    (fun n (j, found, ()) m' =>
      m' = m ∧ j.toNat ≤ sz_c.toNat ∧ n = sz_c.toNat - j.toNat ∧
      (found = true → ∃ k < j.toNat,
        (s.core.arena[cr_bv.toNat + 3 + k]?.getD 0#32).toNat = f0.toNat))
    ?_ ?_ ?_
  · intro B (_, found_f, sat_f, ()) ml ⟨hml, hsat⟩; subst ml
    refine wp_join_group (ts := [i32]) (fun r' ml' => Js r' ml')
      (fun _ ⟨r', _⟩ ml' h => by c0_hsteps_nogrp; exact h) fun Js3 hJs3 => ?_
    have hidx_eq : (BitVec.setWidth 64 (sc4 + r0n)).toNat = 4 * sc + r0n.toNat := by
      simp only [BitVec.toNat_setWidth, BitVec.toNat_add, hsc4]
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    have hidx_lt : (BitVec.setWidth 64 (sc4 + r0n)).toNat < s.scratch.scratch_buf.length := by omega
    c0_hsteps_nogrp
    · exact hJs3 _ _ (hJs_same m hm)
    · rcases top_rowEntryOk_of_large_f0 hdinv hcr_ref hcr_garb (by omega) (by omega)
        (hsat (by assumption) (by assumption)) with ⟨res, h1, h2, h3, h4⟩
      exact hJs3 _ _ (hJs_push _ res h1 h2 h3 h4
        (by dsimp only at *; rw [hidx_eq] at *; assumption))
    · exact hJs3 _ _ (hJs_same m hm)
  · intro B L n (j, found, ()) ml hB ihL ⟨hml, hj_le, hn_eq, hfound⟩; subst ml
    have har1 : (BitVec.setWidth 64 cr_bv + 3 + BitVec.setWidth 64 j).toNat =
        cr_bv.toNat + 3 + j.toNat := by
      simp only [BitVec.toNat_add, BitVec.toNat_setWidth, show (3 : BitVec 64).toNat = 3 from rfl]
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    c0_hsteps_nogrp
    · have hj_lt : j.toNat < sz_c.toNat := by assumption
      have har_lt : (BitVec.setWidth 64 cr_bv + 3 + BitVec.setWidth 64 j).toNat <
          s.core.arena.length := by omega
      let lit_bv := s.core.arena[(BitVec.setWidth 64 cr_bv + 3 + BitVec.setWidth 64 j).toNat]'har_lt
      have hlit_mem : lit_bv.toNat ∈ fullArenaClauseLitsCore s.core cr_bv.toNat := by
        have hm := step0_arena_lit_mem (k := s.core) (cr := cr_bv.toNat) (j := j.toNat)
          (by omega) (by omega)
        rwa [show (s.core.arena[cr_bv.toNat + 3 + j.toNat]?.getD 0#32).toNat = lit_bv.toNat by
          simp only [lit_bv, har1]
          rw [List.getElem?_eq_getElem (by omega), Option.getD_some]] at hm
      have hlit_lt := hwit.arena.lits_lt cr_bv.toNat hcr_ref hcr_garb lit_bv.toNat hlit_mem
      have hvals_idx : (BitVec.setWidth 64 lit_bv).toNat < s.core.vals.length := by
        simp only [BitVec.toNat_setWidth]; rw [Nat.mod_eq_of_lt (by omega)]; omega
      c0_hsteps_nogrp
      · exact hB _ _ ⟨rfl, fun h => by contradiction⟩
      · refine wp_join_group (ts := [.bool]) (fun (f', ()) ml' =>
          ml' = m ∧ (f' = true → ∃ k < j.toNat + 1,
            (s.core.arena[cr_bv.toNat + 3 + k]?.getD 0#32).toNat = f0.toNat)) ?_ ?_
        · rintro _ ⟨f', _⟩ ml' ⟨hml', hf'⟩; subst ml'
          have hj1_eq : (j + 1).toNat = j.toNat + 1 := by
            rw [BitVec.toNat_add, show (1 : BitVec 32).toNat = 1 from rfl]; omega
          c0_hsteps_nogrp
          exact ihL (sz_c.toNat - (j.toNat + 1)) _ _ (by omega)
            ⟨rfl, by omega, by rw [hj1_eq], fun h => by rw [hj1_eq]; exact hf' h⟩
        · intro Js4 hJs4; c0_hsteps_nogrp
          · refine hJs4 (true, ()) m ⟨rfl, fun _ => ⟨j.toNat, by omega, ?_⟩⟩
            have hlt64 : (cr_bv.toNat + (3 : BitVec 64).toNat + j.toNat) % 2 ^ 64 <
                s.core.arena.length := by
              rw [show (3 : BitVec 64).toNat = 3 from rfl, Nat.mod_eq_of_lt (by omega)]; omega
            have hc' : s.core.arena[(cr_bv.toNat +
                (3 : BitVec 64).toNat + j.toNat) % 2 ^ 64]'hlt64 = f0 := by assumption
            have heq_f0 : lit_bv =
                s.core.arena[(cr_bv.toNat + (3 : BitVec 64).toNat + j.toNat) % 2 ^ 64]'hlt64 :=
              Option.some.inj (by
                dsimp only [lit_bv]; rw [← List.getElem?_eq_getElem har_lt,
                  ← List.getElem?_eq_getElem hlt64, har1,
                  show (3 : BitVec 64).toNat = 3 from rfl, Nat.mod_eq_of_lt (by omega)])
            rw [← heq_f0.trans hc']
            simp only [lit_bv, har1, List.getElem?_eq_getElem (by omega :
              cr_bv.toNat + 3 + j.toNat < s.core.arena.length), Option.getD_some]
          · refine hJs4 (found, ()) m ⟨rfl, fun hf => ?_⟩
            rcases hfound hf with ⟨k, hk, heq⟩; exact ⟨k, by omega, heq⟩
    · exact hB _ _ ⟨rfl, fun _ hf => by
        rcases hfound hf with ⟨k, hk, heq⟩
        rw [← heq]; exact step0_arena_lit_mem (by omega) (by omega)⟩
  · intro B L hB hL; c0_hsteps_nogrp
    have h0 : (0#32 : BitVec 32).toNat = 0 := rfl
    exact hL sz_c.toNat (0#32, false, ()) m
      ⟨rfl, by rw [h0]; omega, by simp [h0], fun h => by contradiction⟩

private def step0OccExpr (pWstk pArena pVals pScratchBuf wi1 off_w sz_w : Val i64)
    (sc4 r0n f0 : Val i32) (tks : Val i64) (Jw1 : Cont [i64, i32, i64]) :
    Expr Val Cont [.bool] :=
  Expr.let_ (Op.mk (.cmp .ult i64) (Arg.var wi1, Arg.var sz_w, ())) fun p48 =>
  Expr.jnz (Arg.var p48.fst)
    (Expr.let_ (Op.mk (.add i64) (Arg.var off_w, Arg.var wi1, ())) fun p49 =>
     Expr.let_ (Op.mk (.mul i64) (Arg.var p49.fst, Arg.imm 4, ())) fun p50 =>
     Expr.let_ (Op.mk (.add i64) (Arg.var pWstk, Arg.var p50.fst, ())) fun p51 =>
     Expr.load i32 (Arg.var p51.fst) fun cr_bv =>
     Expr.let_ (Op.mk (.add i64) (Arg.var wi1, Arg.imm 1, ())) fun p52 =>
     Expr.let_ (Op.mk (.add i64) (Arg.var tks, Arg.imm 1, ())) fun p53 =>
     Expr.let_ (Op.mk (.zext 32 64) (Arg.var cr_bv, ())) fun p54 =>
     Expr.let_ (Op.mk (.add i64) (Arg.var p54.fst, Arg.imm 2, ())) fun p55 =>
     Expr.let_ (Op.mk (.mul i64) (Arg.var p55.fst, Arg.imm 4, ())) fun p56 =>
     Expr.let_ (Op.mk (.add i64) (Arg.var pArena, Arg.var p56.fst, ())) fun p57 =>
     Expr.load i32 (Arg.var p57.fst) fun sz_c =>
     Expr.let_ (Op.mk (.zext 32 64) (Arg.var cr_bv, ())) fun p58 =>
     Expr.let_ (Op.mk (.mul i64) (Arg.var p58.fst, Arg.imm 4, ())) fun p59 =>
     Expr.let_ (Op.mk (.add i64) (Arg.var pArena, Arg.var p59.fst, ())) fun p60 =>
     Expr.load i32 (Arg.var p60.fst) fun hdr_c =>
     Expr.group (sig := [[i32]]) (fun Js2 => Blocks.cons (fun p =>
       Expr.jump Jw1 (Arg.var p52.fst, Arg.var p.fst, Arg.var p53.fst, ())) Blocks.nil)
     (fun Js => Expr.let_ (Op.mk (.or i32) (Arg.imm 524288, Arg.imm 4194304, ())) fun p61 =>
       Expr.let_ (Op.mk (.and i32) (Arg.var hdr_c, Arg.var p61.fst, ())) fun p62 =>
       Expr.let_ (Op.mk (.cmp .eq i32) (Arg.var p62.fst, Arg.imm 0, ())) fun p63 =>
       Expr.jnz (Arg.var p63.fst)
         (Expr.let_ (Op.mk (.cmp .uge i32) (Arg.var sz_c, Arg.imm 3, ())) fun p64 =>
          Expr.jnz (Arg.var p64.fst)
            (Expr.let_ (Op.mk (.cmp .ule i32) (Arg.var sz_c, Arg.imm 5, ())) fun p65 =>
             Expr.jnz (Arg.var p65.fst)
               (step0ClauseExpr pScratchBuf pArena pVals sc4 r0n f0 cr_bv sz_c Js.fst)
               (Expr.jump Js.fst (Arg.var r0n, ())))
            (Expr.jump Js.fst (Arg.var r0n, ())))
         (Expr.jump Js.fst (Arg.var r0n, ()))))
    (Expr.jump Jw1 (Arg.var wi1, Arg.var r0n, Arg.var tks, ()))

private theorem step0_occ_wp (Γ : Env) {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {R : Mem 64 → Prop} {Q : Post [.bool]} {X : XPost} {m : Mem 64}
    (Jw1 : Cont [i64, i32, i64]) (wi1 off_w sz_w tks : Val i64) (sc : Nat)
    (sc4 r0n f0 cr_bv : Val i32) (hsc4 : sc4.toNat = 4 * sc) (hsc_pos : 0 < sc)
    (hsc_le : sc ≤ 256) (h4sc_cap : 4 * sc ≤ c.scratch_cap) (hlen : FullState.LengthsOk c s)
    (hdinv : FullDenseInvW c F0 F_cur s) (hf0_lt : f0.toNat < 2 * s.core.cur_vars)
    (hr0n_lt : r0n.toNat < (c.scratch_cap - 4 * sc) / 3)
    (h4sc_r0 : 4 * sc + r0n.toNat < c.scratch_cap)
    (hoff_val : off_w.toNat = fullWatchOffCore s.core f0.toNat)
    (hsz_val : sz_w.toNat = fullWatchSizeCore s.core f0.toNat)
    (hwi1_lt : wi1.toNat < fullWatchSizeCore s.core f0.toNat)
    (hoff_bound : fullWatchOffCore s.core f0.toNat + wi1.toNat < c.wcap)
    (hcr_some : s.core.wstk[fullWatchOffCore s.core f0.toNat + wi1.toNat]? = some cr_bv)
    (hcr_ref : cr_bv.toNat ∈ fullArenaClauseRefsCore s.core) (hm : (FullMem c s ⋆ R) m)
    (hJw_same : ∀ m', (FullMem c s ⋆ R) m' → Jw1 (wi1 + 1#64, r0n, tks + 1#64, ()) m')
    (hJw_push : ∀ (m' : Mem 64) (res : List Nat),
      (∀ x ∈ res, x < 2 * s.core.cur_vars) → (res.map (· / 2)).Nodup →
      FidBvaRowEntryOk F_cur s f0.toNat cr_bv res →
      (cnfOfClauses F_cur).EntailsClause (cnfClause (f0.toNat :: res)) →
      (FullMem c { core := s.core, scratch := { s.scratch with
        scratch_buf := s.scratch.scratch_buf.set (4 * sc + r0n.toNat) cr_bv } } ⋆ R) m' →
      Jw1 (wi1 + 1#64, r0n + 1#32, tks + 1#64, ()) m') :
    wp Γ Q X (step0OccExpr c.pWstk c.pArena c.pVals c.pScratchBuf wi1 off_w sz_w sc4
      r0n f0 tks Jw1) m := by
  have hcl := hlen.core_ok; have hmx := c.hmaxv; have har_b := c.harena
  have hwc_c := c.hwcap; have hsc_c := c.hscr; unfold dimacsBound at hmx har_b hwc_c hsc_c
  have hwit := hdinv.2.1; have hcr_wf := hwit.arena.refs_wf cr_bv.toNat hcr_ref
  have har_len := hcl.arena_len_le; have har_arr := hcl.arena_len_arr
  have hwl_le := hcl.wlen_le; have hwstk_len := hcl.wstk_len_arr
  have hwstk_idx : (off_w + wi1).toNat < s.core.wstk.length := by
    simp only [BitVec.toNat_add, hoff_val]; rw [Nat.mod_eq_of_lt (by omega)]; omega
  have hcr_eq : s.core.wstk[(off_w + wi1).toNat]'hwstk_idx = cr_bv := by
    have hidx : (off_w + wi1).toNat = fullWatchOffCore s.core f0.toNat + wi1.toNat := by
      simp only [BitVec.toNat_add, hoff_val]; rw [Nat.mod_eq_of_lt (by omega)]
    rw [← Option.some_inj, ← List.getElem?_eq_getElem (by omega), hidx]; exact hcr_some
  have hcr_ar : (BitVec.setWidth 64 cr_bv).toNat < s.core.arena.length := by
    simp only [BitVec.toNat_setWidth]; rw [Nat.mod_eq_of_lt (by omega)]; omega
  have hcr2_ar : (BitVec.setWidth 64 cr_bv + 2).toNat < s.core.arena.length := by
    simp only [BitVec.toNat_add, BitVec.toNat_setWidth, show (2 : BitVec 64).toNat = 2 from rfl]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
  unfold step0OccExpr; c0_hsteps_nogrp
  refine wp_join_group (ts := [i32]) (fun (r', ()) ml3 => Jw1 (wi1 + 1#64, r', tks + 1#64, ()) ml3)
    (fun _ ⟨_, _⟩ _ hr => by
      c0_hsteps_nogrp; simpa only [show (1 : BitVec 64) = 1#64 from rfl] using hr)
    fun Js hJs => ?_
  have hcr0_eq : (BitVec.setWidth 64 cr_bv).toNat = cr_bv.toNat := by
    simp only [BitVec.toNat_setWidth]; rw [Nat.mod_eq_of_lt (by omega)]
  have hcr2_eq : (BitVec.setWidth 64 cr_bv + 2).toNat = cr_bv.toNat + 2 := by
    simp only [BitVec.toNat_add, BitVec.toNat_setWidth, show (2 : BitVec 64).toNat = 2 from rfl]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  simp only [hcr_eq]; c0_hsteps_nogrp
  · have hgarb0 : fullArenaClauseGarbCore s.core cr_bv.toNat = false := by
      unfold fullArenaClauseGarbCore fullArenaHdrCore
      have hcmp : s.core.arena[(BitVec.setWidth 64 cr_bv).toNat] &&&
          (524288#32 ||| 4194304#32) = 0#32 := by assumption
      have h524 : s.core.arena[(BitVec.setWidth 64 cr_bv).toNat] &&& 524288#32 = 0#32 := by
        calc s.core.arena[(BitVec.setWidth 64 cr_bv).toNat] &&& 524288#32
            = (s.core.arena[(BitVec.setWidth 64 cr_bv).toNat] &&& (524288#32 ||| 4194304#32)) &&&
                524288#32 := by
                rw [BitVec.and_assoc,
                  show (524288#32 ||| 4194304#32) &&& 524288#32 = 524288#32 from rfl]
          _ = 0#32 := by rw [hcmp]; rfl
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
      have h524' : s.core.arena[cr_bv.toNat]'(by omega) &&& 524288#32 = 0#32 := by
        simpa only [hcr0_eq] using h524
      simp only [h524']; rfl
    have hsz_eq : fullArenaClauseSizeCore s.core cr_bv.toNat =
        (s.core.arena[(BitVec.setWidth 64 cr_bv + 2).toNat]).toNat := by
      unfold fullArenaClauseSizeCore
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some]; simp only [hcr2_eq]
    exact step0_clause_wp Γ Js sc sc4 r0n f0 cr_bv _ hsc4 hsc_pos hsc_le h4sc_cap hlen hdinv
      hcr_ref hgarb0 hsz_eq (by assumption) (by assumption) hf0_lt hr0n_lt h4sc_r0 hm
      (fun m' hm' => hJs _ _ (hJw_same m' hm'))
      (fun m' res h1 h2 h3 h4 hm' => hJs _ _ (hJw_push m' res h1 h2 h3 h4 hm'))
  all_goals exact hJs _ _ (hJw_same m hm)

private theorem step0_occ_case_wp (Γ : Env) {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {sb : List (BitVec 32)} {R : Mem 64 → Prop} {Q : Post [.bool]} {X : XPost}
    {ml2 : Mem 64} (Jw1 Jw : Cont [i64, i32, i64]) (wi off_w sz_w tks : Val i64)
    (r0n f0 cr_bv : Val i32) (rem_w : Nat) (hsc_pos : 0 < fidStepsCap c.scratch_cap)
    (hsc_le : fidStepsCap c.scratch_cap ≤ 256)
    (h4sc_cap : 4 * fidStepsCap c.scratch_cap ≤ c.scratch_cap) (hlen : FullState.LengthsOk c s)
    (hwit : FullWitnessInv c F0 F_cur s.core) (hlm : FullLitMarksClear c s)
    (hnodup : FullArenaVarsNodup s) (hext : FullExtScratchOk c s) (hlev : s.core.cur_level = 0)
    (hdm : s.core.dense_mode ≠ 0#64) (hsb_l : sb.length = c.scratch_cap)
    (hf0_lt : f0.toNat < 2 * s.core.cur_vars)
    (hr0n_lt : r0n.toNat < (c.scratch_cap - 4 * fidStepsCap c.scratch_cap) / 3)
    (hwi1_mod : (wi + 1).toNat = wi.toNat + 1)
    (hwi2_le : wi.toNat + 2 ≤ fullWatchSizeCore s.core f0.toNat)
    (hrem : rem_w = fullWatchSizeCore s.core f0.toNat - (wi.toNat + 2))
    (hoff_eq_w : off_w.toNat = fullWatchOffCore s.core f0.toNat)
    (hsz_eq_w : sz_w.toNat = fullWatchSizeCore s.core f0.toNat)
    (hoff_bd : fullWatchOffCore s.core f0.toNat + (wi.toNat + 1) < c.wcap)
    (hcr_some : s.core.wstk[fullWatchOffCore s.core f0.toNat + (wi.toNat + 1)]? = some cr_bv)
    (hcr_ref : cr_bv.toNat ∈ fullArenaClauseRefsCore s.core)
    (hsl' : DenseWatchSliceOk F_cur s.core f0.toNat
      (fullWatchOffCore s.core f0.toNat + wi.toNat + 2) rem_w)
    (hrows : step0RowOk F_cur s f0.toNat sb (fidStepsCap c.scratch_cap) r0n.toNat)
    (hm2 : (FullMem c { core := s.core, scratch := { s.scratch with scratch_buf := sb } } ⋆ R) ml2)
    (hJw1 : ∀ ys ml3, Jw ys ml3 → Jw1 ys ml3)
    (hJw : ∀ ys ml3, (∃ sb', sb'.length = c.scratch_cap ∧
      ys.fst.toNat ≤ fullWatchSizeCore s.core f0.toNat ∧
      ys.snd.fst.toNat ≤ (c.scratch_cap - 4 * fidStepsCap c.scratch_cap) / 3 ∧
      4 * fidStepsCap c.scratch_cap + ys.snd.fst.toNat ≤ c.scratch_cap ∧
      DenseWatchSliceOk F_cur s.core f0.toNat (fullWatchOffCore s.core f0.toNat + ys.fst.toNat)
        (fullWatchSizeCore s.core f0.toNat - ys.fst.toNat) ∧
      step0RowOk F_cur s f0.toNat sb' (fidStepsCap c.scratch_cap) ys.snd.fst.toNat ∧
      (FullMem c { core := s.core, scratch := { s.scratch with scratch_buf := sb' } } ⋆ R) ml3 ∧
      fullWatchSizeCore s.core f0.toNat - ys.fst.toNat <
        fullWatchSizeCore s.core f0.toNat - wi.toNat) → Jw ys ml3) :
    wp Γ Q X (step0OccExpr c.pWstk c.pArena c.pVals c.pScratchBuf (wi + 1) off_w sz_w
      (BitVec.ofNat 32 (fidStepsCap (BitVec.ofNat 64 c.scratch_cap).toNat) <<< OfNat.ofNat 2)
      r0n f0 tks Jw1) ml2 := by
  have hmx := c.hmaxv; have hsc_c := c.hscr; have har_b := c.harena; have hwc_c := c.hwcap
  unfold dimacsBound at hmx hsc_c har_b hwc_c
  have hcl := hlen.core_ok; have hsc := hlen.scratch_ok
  have hcv_le := hcl.cur_vars_le; have hsb_len := hsc.scratch_buf_len
  have hwi1_lt : (wi + 1).toNat < fullWatchSizeCore s.core f0.toNat := by omega
  have hwi2_mod : ((wi + 1) + 1#64).toNat = wi.toNat + 2 := by
    rw [BitVec.toNat_add, hwi1_mod, show (1#64 : BitVec 64).toNat = 1 from rfl]; omega
  have hwi2_lt : ((wi + 1) + 1#64).toNat ≤ fullWatchSizeCore s.core f0.toNat := by
    rw [hwi2_mod]; omega
  have hcap_mod : (BitVec.ofNat 64 c.scratch_cap).toNat = c.scratch_cap := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hsc4_eq : (BitVec.ofNat 32 (fidStepsCap (BitVec.ofNat 64 c.scratch_cap).toNat) <<<
      OfNat.ofNat 2).toNat = 4 * fidStepsCap c.scratch_cap := by
    rw [hcap_mod]; simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat,
      show (OfNat.ofNat 2 : Nat) = 2 from rfl, Nat.shiftLeft_eq]
    exact show fidStepsCap c.scratch_cap % 2 ^ 32 * 2 ^ 2 % 2 ^ 32 =
      4 * fidStepsCap c.scratch_cap by omega
  let s_sb : FullState := { core := s.core, scratch := { s.scratch with scratch_buf := sb } }
  have hlen_sb : FullState.LengthsOk c s_sb := ⟨hcl, { hsc with scratch_buf_len := hsb_l }⟩
  have hdinv_sb : FullDenseInvW c F0 F_cur s_sb :=
    ⟨hlen_sb, hwit, hlm, hnodup, FullExtScratchOk.of_pres hext ⟨rfl, rfl⟩ fun _ hr => hr, hlev, hdm⟩
  have hsl_occ : DenseWatchSliceOk F_cur s.core f0.toNat
      (fullWatchOffCore s.core f0.toNat + ((wi + 1) + 1#64).toNat)
      (fullWatchSizeCore s.core f0.toNat - ((wi + 1) + 1#64).toNat) := by
    rw [hwi2_mod, show fullWatchOffCore s.core f0.toNat + (wi.toNat + 2) =
        fullWatchOffCore s.core f0.toNat + wi.toNat + 2 from by omega,
      show fullWatchSizeCore s.core f0.toNat - (wi.toNat + 2) = rem_w from by omega]; exact hsl'
  exact step0_occ_wp Γ (c := c) (F0 := F0) (F_cur := F_cur) (s := s_sb) (R := R) Jw1 (wi + 1)
    off_w sz_w tks (fidStepsCap c.scratch_cap)
    (BitVec.ofNat 32 (fidStepsCap (BitVec.ofNat 64 c.scratch_cap).toNat) <<< OfNat.ofNat 2)
    r0n f0 cr_bv hsc4_eq hsc_pos hsc_le h4sc_cap hlen_sb hdinv_sb hf0_lt hr0n_lt (by omega)
    hoff_eq_w hsz_eq_w hwi1_lt (by rw [hwi1_mod]; exact hoff_bd)
    (by dsimp only [s_sb]; rw [hwi1_mod]; exact hcr_some) hcr_ref hm2
    (fun m' hm' => hJw1 _ _ (hJw _ _ ⟨sb, hsb_l, hwi2_lt, by dsimp only; omega,
      by dsimp only; omega, hsl_occ, hrows, hm', by dsimp only; rw [hwi2_mod]; omega⟩))
    (fun m' res h1 h2 h3 h4 hm' => by
      have hr0_1 : (r0n + 1#32).toNat = r0n.toNat + 1 := by
        rw [BitVec.toNat_add, show (1#32 : BitVec 32).toNat = 1 from rfl]; omega
      have hrows' : step0RowOk F_cur s f0.toNat
          (sb.set (4 * fidStepsCap c.scratch_cap + r0n.toNat) cr_bv)
          (fidStepsCap c.scratch_cap) (r0n + 1#32).toNat :=
        hr0_1 ▸ step0_rowOk_push (by omega) (by omega) hrows ⟨res, h1, h2, h3, h4⟩
      exact hJw1 _ _ (hJw _ _ ⟨sb.set _ cr_bv, by rw [List.length_set, hsb_l], hwi2_lt,
        by dsimp only; rw [hr0_1]; omega, by dsimp only; rw [hr0_1]; omega,
        hsl_occ, hrows', hm', by dsimp only; rw [hwi2_mod]; omega⟩))

/-! ## 2. Top-Level `full_bva_try_lit_wp` -/

public section

/-- Top-level `CanonicalEnv` WP theorem for `full_bva_try_lit` (`14/15`). -/
theorem full_bva_try_lit_wp (Γ : Env)
    (hCap : Γ.Has "full_bva_steps_cap_fid" fidBvaStepsCapSpec)
    (hScan : Γ.Has "full_bva_scan_cands" step13BvaScanCandsSpec)
    (hPick : Γ.Has "full_bva_pick_cand" step13BvaPickCandSpec)
    (hFilter : Γ.Has "full_bva_filter_row" fidBvaFilterRowSpec)
    (hCommit : Γ.Has "full_bva_commit" step7BvaCommitSpec) :
    ∀ a m Q X, step7BvaTryLitSpec a m Q X → Func.wp Γ full_bva_try_lit_body a m Q X := by
  intro ⟨hdr, f0, init_cv, _⟩ m Q X ⟨c, F0, s, R, h_eq, hdinv, hf0_lt, hm, hpost⟩
  subst h_eq
  have hmx := c.hmaxv; have hsc_c := c.hscr; have har_b := c.harena; have hwc_c := c.hwcap
  unfold dimacsBound at hmx hsc_c har_b hwc_c
  rcases hdinv with ⟨⟨hlen, F_cur, hwit⟩, hlm, hnodup, hext, hlev, hdm⟩
  have hcl := hlen.core_ok; have hsc := hlen.scratch_ok
  have hcv_le := hcl.cur_vars_le; have hsb_len := hsc.scratch_buf_len; have hwv_len := hcl.wvec_len
  have hvals_len := hcl.vals_len; have hlm_len := hcl.lit_mark_len; have har_len := hcl.arena_len_le
  have hwl_le := hcl.wlen_le; have hwstk_len := hcl.wstk_len_arr; have har_arr := hcl.arena_len_arr
  have hdinv_orig : FullDenseInv c F0 s := ⟨⟨hlen, F_cur, hwit⟩, hlm, hnodup, hext, hlev, hdm⟩
  have hret_false : Q (false, ()) m :=
    hpost false s m hdinv_orig (Nat.le_refl _) (fun h => by cases h) (fun h => by cases h)
      rfl rfl rfl hm
  have hdw : DenseWatchesInv F_cur s.core := by
    have h := hwit.watches; unfold ModeWatchesInv at h
    rwa [ite_eq_right (fun heq => absurd heq hdm)] at h
  unfold Func.wp full_bva_try_lit_body; c0_hsteps_nogrp
  apply fid_wp_call_steps_cap Γ hCap; c0_hsteps_nogrp
  · exact hret_false
  · exact hret_false
  · exact hret_false
  · have hsc_pos : 0 < fidStepsCap c.scratch_cap := by
      have hne : BitVec.ofNat 32 (fidStepsCap (c.scratch_cap % 2 ^ 64)) ≠ 0#32 := by
        simpa using ‹¬BitVec.ofNat 32 (fidStepsCap (c.scratch_cap % 2 ^ 64)) = 0›
      rw [Nat.mod_eq_of_lt (by omega)] at hne; exact fid_sc_pos_of_ne_zero hne
    refine wp_join_group (ts := [i64]) (fun il ml => ml = m ∧ il.fst.toNat ≤ 2 * s.core.cur_vars)
      ?_ ?_
    · intro _ ⟨il, _⟩ ml ⟨rfl, hil_le⟩; c0_hsteps_nogrp
      · exact hret_false
      · have hbd := hdw.layout.bounds f0.toNat hf0_lt
        have hsl_init := hdw.slices f0.toNat hf0_lt
        have hsc_le : fidStepsCap c.scratch_cap ≤ 256 := fidStepsCap_le_256 c.scratch_cap
        have h4sc_cap : 4 * fidStepsCap c.scratch_cap ≤ c.scratch_cap :=
          fidStepsCap_mul4_le c.scratch_cap
        have hrow0_cap_pos : 2 ≤ (c.scratch_cap - 4 * fidStepsCap c.scratch_cap) / 3 :=
          step0_row0_cap (cap := c.scratch_cap) (by omega) hc
        refine wp_loop_inv (fun (wi, r0n, tks, _) ml2 => ∃ sb, sb.length = c.scratch_cap ∧
            wi.toNat ≤ fullWatchSizeCore s.core f0.toNat ∧
            r0n.toNat ≤ (c.scratch_cap - 4 * fidStepsCap c.scratch_cap) / 3 ∧
            4 * fidStepsCap c.scratch_cap + r0n.toNat ≤ c.scratch_cap ∧
            DenseWatchSliceOk F_cur s.core f0.toNat (fullWatchOffCore s.core f0.toNat + wi.toNat)
              (fullWatchSizeCore s.core f0.toNat - wi.toNat) ∧
            step0RowOk F_cur s f0.toNat sb (fidStepsCap c.scratch_cap) r0n.toNat ∧
            (FullMem c { core := s.core, scratch := { s.scratch with scratch_buf := sb } } ⋆ R) ml2)
          (fun (wi, _, _) _ => fullWatchSizeCore s.core f0.toNat - wi.toNat)
          (fun Js hJs => by
            c0_hsteps_nogrp
            exact hJs (0#64, 0#32, 0#64, ()) ml ⟨s.scratch.scratch_buf, hsb_len,
              by simp only [BitVec.toNat_zero]; omega, by simp only [BitVec.toNat_zero]; omega,
              by simp only [BitVec.toNat_zero]; omega,
              by simpa only [BitVec.toNat_zero, Nat.add_zero, Nat.sub_zero] using hsl_init,
              fun _ hj => by simp only [BitVec.toNat_zero] at hj; omega, hm⟩)
          (fun Js (wi, r0n, tks, _) ml2 ⟨sb, hsb_l, hwi_le, hr0n_le, h4sc, hsl, hrows, hm2⟩
              ih => ?_)
        c0_hsteps_nogrp
        refine wp_join_group (ts := []) (fun _ ml3 => ml3 = ml2) ?_ ?_
        · intro _ _ ml3 hml3; subst ml3; c0_hsteps_nogrp
          refine wp_join_group (ts := [i64]) (fun _ ml4 => ml4 = ml2) ?_ ?_
          · intro _ ⟨asz', _⟩ ml4 hml4; rcases hml4 with rfl
            have hcap_mod : c.scratch_cap % 2 ^ 64 = c.scratch_cap := Nat.mod_eq_of_lt (by omega)
            have hsc_bv32' : BitVec.ofNat 32 (fidStepsCap c.scratch_cap) <<< OfNat.ofNat 2 =
                BitVec.ofNat 32 (4 * fidStepsCap c.scratch_cap) := by
              apply BitVec.eq_of_toNat_eq
              simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
                show (OfNat.ofNat 2 : Nat) = 2 from rfl]
              rw [Nat.mod_eq_of_lt (by omega)]; omega
            have hsc_bv32 : BitVec.ofNat 32 (fidStepsCap (BitVec.ofNat 64 c.scratch_cap).toNat) <<<
                OfNat.ofNat 2 = BitVec.ofNat 32 (4 * fidStepsCap c.scratch_cap) := by
              simpa [BitVec.toNat_ofNat, hcap_mod] using hsc_bv32'
            have h0_lt : (BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 0)).toNat < sb.length := by
              rw [show (BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 0)).toNat = 0 from rfl]; omega
            have hsc_lt : (BitVec.setWidth 64
                (BitVec.ofNat 32 (fidStepsCap (BitVec.ofNat 64 c.scratch_cap).toNat))).toNat <
                (sb.set (BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 0)).toNat f0).length := by
              simp only [List.length_set, fid_bv64_32, BitVec.toNat_ofNat, hcap_mod]
              rw [Nat.mod_eq_of_lt (by omega)]; omega
            have h2sc_lt : (BitVec.setWidth 64 (2#32 *
                BitVec.ofNat 32 (fidStepsCap (BitVec.ofNat 64 c.scratch_cap).toNat))).toNat <
                ((sb.set (BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 0)).toNat f0).set
                  (BitVec.setWidth 64
                    (BitVec.ofNat 32 (fidStepsCap (BitVec.ofNat 64 c.scratch_cap).toNat))).toNat
                  (BitVec.ofNat 32 (fidStepsCap (BitVec.ofNat 64 c.scratch_cap).toNat) <<<
                    OfNat.ofNat 2)).length := by
              simp only [List.length_set, fid_bv64_32, BitVec.toNat_mul, BitVec.toNat_ofNat,
                hcap_mod]; rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
            have h3sc_lt : (BitVec.setWidth 64 (3#32 *
                BitVec.ofNat 32 (fidStepsCap (BitVec.ofNat 64 c.scratch_cap).toNat))).toNat <
                (((sb.set (BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 0)).toNat f0).set
                  (BitVec.setWidth 64
                    (BitVec.ofNat 32 (fidStepsCap (BitVec.ofNat 64 c.scratch_cap).toNat))).toNat
                  (BitVec.ofNat 32 (fidStepsCap (BitVec.ofNat 64 c.scratch_cap).toNat) <<<
                    OfNat.ofNat 2)).set (BitVec.setWidth 64 (2#32 *
                    BitVec.ofNat 32 (fidStepsCap (BitVec.ofNat 64 c.scratch_cap).toNat))).toNat
                  r0n).length := by
              simp only [List.length_set, fid_bv64_32, BitVec.toNat_mul, BitVec.toNat_ofNat,
                hcap_mod]; rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
            have hlm_f0 : (BitVec.setWidth 64 f0).toNat < s.core.lit_mark.length := by
              rw [fid_bv64_32]; omega
            c0_hsteps_nogrp
            · exact hpost false { core := s.core, scratch := { s.scratch with
                scratch_buf := sb, ant_sz := asz' } } m (step0_dinv_sb_asz hdinv_orig hsb_l)
                (Nat.le_refl _) (fun h => by cases h) (fun h => by cases h) rfl rfl rfl
                (by dsimp only at hm; exact hm)
            · have h1_bv : (BitVec.setWidth 64
                  (BitVec.ofNat 32 (fidStepsCap (BitVec.ofNat 64 c.scratch_cap).toNat))).toNat =
                  fidStepsCap c.scratch_cap := by
                simp only [fid_bv64_32, BitVec.toNat_ofNat, hcap_mod]
                rw [Nat.mod_eq_of_lt (by omega)]
              have h2_bv : (BitVec.setWidth 64 (2 *
                  BitVec.ofNat 32 (fidStepsCap (BitVec.ofNat 64 c.scratch_cap).toNat))).toNat =
                  2 * fidStepsCap c.scratch_cap := by
                simp only [fid_bv64_32, BitVec.toNat_mul, BitVec.toNat_ofNat, hcap_mod,
                  show (2 : BitVec 32).toNat = 2 from rfl]
                rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
              have h3_bv : (BitVec.setWidth 64 (3 *
                  BitVec.ofNat 32 (fidStepsCap (BitVec.ofNat 64 c.scratch_cap).toNat))).toNat =
                  3 * fidStepsCap c.scratch_cap := by
                simp only [fid_bv64_32, BitVec.toNat_mul, BitVec.toNat_ofNat, hcap_mod,
                  show (3 : BitVec 32).toNat = 3 from rfl]
                rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
              have hr0n_ge2 : 2 ≤ r0n.toNat := by
                have hnot := (by assumption : ¬ r0n.toNat < BitVec.toNat (2 : BitVec 32))
                rw [show BitVec.toNat (2 : BitVec 32) = 2 from rfl] at hnot; omega
              have hmem_cur : (FullMem c
                  { core := { s.core with lit_mark := s.core.lit_mark.set f0.toNat 1#8 }
                    scratch := { s.scratch with
                      scratch_buf := (((sb.set 0 f0).set (fidStepsCap c.scratch_cap)
                        (BitVec.ofNat 32 (4 * fidStepsCap c.scratch_cap))).set
                        (2 * fidStepsCap c.scratch_cap) r0n).set
                        (3 * fidStepsCap c.scratch_cap)
                        (BitVec.ofNat 32 (4 * fidStepsCap c.scratch_cap))
                      ant_sz := asz' } } ⋆ R) m := by
                dsimp only at hm
                simpa only [hcap_mod, hsc_bv32, h1_bv, h2_bv, h3_bv, fid_bv64_32,
                  show (BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 0)).toNat = 0 from rfl,
                  show BitVec.ofNat (OfNat.ofNat 8) (OfNat.ofNat 1) = 1#8 from rfl] using hm
              simpa only [show BitVec.ofNat 32 (fidStepsCap (BitVec.ofNat 64 c.scratch_cap).toNat) =
                  BitVec.ofNat 32 (fidStepsCap c.scratch_cap) by simp [hcap_mod], hsc_bv32'] using
                step0_post_exit_wp Γ hScan hPick hFilter hCommit (init_cv := init_cv)
                  (init_lits := il) (lim_bv := s.scratch.elim_bound) hlen hwit hlm hnodup hext hlev
                  hdm hf0_lt hil_le hsb_l hsc_pos hsc_le h4sc hr0n_ge2 hrows hmem_cur hpost
          · intro _ hJa; c0_hsteps_nogrp; exact hJa (_, ()) ml2 rfl; exact hJa (_, ()) ml2 rfl
        · intro Jex hJex; c0_hsteps_nogrp
          · have hsh1 : (2 * f0.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 =
                2 * f0.toNat + 1 := by show (2 * f0.toNat + 1) % 2 ^ 64 = 2 * f0.toNat + 1; omega
            have hsz_val :
                s.core.wvec[(2 * f0.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64].toNat =
                fullWatchSizeCore s.core f0.toNat := by
              simp only [hsh1]; unfold fullWatchSizeCore
              rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
            have hwi_lt : wi.toNat < fullWatchSizeCore s.core f0.toNat := by
              rw [← hsz_val]; assumption
            have hr0n_lt : r0n.toNat < (c.scratch_cap - 4 * fidStepsCap c.scratch_cap) / 3 := by
              have hsub_cap : (BitVec.ofNat 64 c.scratch_cap - BitVec.setWidth 64
                  (BitVec.ofNat 32 (fidStepsCap (c.scratch_cap % 2 ^ 64)) <<<
                    OfNat.ofNat 2)).toNat =
                  c.scratch_cap - 4 * fidStepsCap c.scratch_cap := by
                have hmod : c.scratch_cap % 2 ^ 64 = c.scratch_cap := Nat.mod_eq_of_lt (by omega)
                simp only [BitVec.toNat_sub, BitVec.toNat_setWidth, BitVec.toNat_shiftLeft,
                  BitVec.toNat_ofNat, hmod, show (OfNat.ofNat 2 : Nat) = 2 from rfl,
                  Nat.shiftLeft_eq]
                rw [show fidStepsCap c.scratch_cap % 2 ^ 32 * 2 ^ 2 % 2 ^ 32 % 2 ^ 64 =
                  4 * fidStepsCap c.scratch_cap by omega]; omega
              have hc1 :
                  r0n.toNat < (c.scratch_cap - 4 * fidStepsCap c.scratch_cap) / 3 % 2 ^ 32 := by
                have hc_raw := hc
                simp only [BitVec.toNat_udiv, show (3 : BitVec 64).toNat = 3 from rfl, hsub_cap]
                  at hc_raw; exact hc_raw
              rwa [Nat.mod_eq_of_lt (by omega)] at hc1
            have hw_off : fullWatchOffCore s.core f0.toNat + wi.toNat < c.wcap := by omega
            have hsh_f0 : (BitVec.setWidth 64 f0 <<< OfNat.ofNat 1).toNat = 2 * f0.toNat := by
              simp only [BitVec.toNat_shiftLeft, BitVec.toNat_setWidth,
                show (OfNat.ofNat 1 : Nat) = 1 from rfl, Nat.shiftLeft_eq]
              rw [Nat.mod_eq_of_lt (by omega : f0.toNat < 2 ^ 64)]; omega
            have hw_idx_eq : s.core.wvec[(BitVec.setWidth 64 f0 <<< OfNat.ofNat 1).toNat] =
                s.core.wvec[2 * f0.toNat] := by simp only [hsh_f0]
            have hw_off_val : s.core.wvec[2 * f0.toNat].toNat =
                fullWatchOffCore s.core f0.toNat := by
              unfold fullWatchOffCore; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
            have hw_mod1 : fullWatchOffCore s.core f0.toNat % 2 ^ 64 =
                fullWatchOffCore s.core f0.toNat := by
              unfold fullWatchOffCore
              exact Nat.mod_eq_of_lt
                (by have := BitVec.isLt (s.core.wvec[2 * f0.toNat]?.getD 0#32); omega)
            have hwstk_idx : (BitVec.setWidth 64
                s.core.wvec[(BitVec.setWidth 64 f0 <<< OfNat.ofNat 1).toNat] + wi).toNat <
                s.core.wstk.length := by
              simp only [BitVec.toNat_add, BitVec.toNat_setWidth, hw_idx_eq, hw_off_val, hw_mod1]
              rw [Nat.mod_eq_of_lt (by
                have := BitVec.isLt (s.core.wvec[2 * f0.toNat]?.getD 0#32)
                unfold fullWatchOffCore at *; omega)]; omega
            c0_hsteps_nogrp
            refine wp_join_group (ts := [i64, i32, i64]) (fun (wi', r0n', _, _) ml3 => ∃ sb',
                sb'.length = c.scratch_cap ∧ wi'.toNat ≤ fullWatchSizeCore s.core f0.toNat ∧
                r0n'.toNat ≤ (c.scratch_cap - 4 * fidStepsCap c.scratch_cap) / 3 ∧
                4 * fidStepsCap c.scratch_cap + r0n'.toNat ≤ c.scratch_cap ∧
                DenseWatchSliceOk F_cur s.core f0.toNat
                  (fullWatchOffCore s.core f0.toNat + wi'.toNat)
                  (fullWatchSizeCore s.core f0.toNat - wi'.toNat) ∧
                step0RowOk F_cur s f0.toNat sb' (fidStepsCap c.scratch_cap) r0n'.toNat ∧
                (FullMem c { core := s.core, scratch := { s.scratch with scratch_buf := sb' } } ⋆ R)
                  ml3 ∧
                fullWatchSizeCore s.core f0.toNat - wi'.toNat <
                  fullWatchSizeCore s.core f0.toNat - wi.toNat) ?_ ?_
            · intro _ ⟨wi', r0n', tks', _⟩ ml3 ⟨sb', h1, h2, h3, h4, h5, h6, h7, hlt⟩
              exact ih (wi', r0n', tks', ()) ml3 hlt ⟨sb', h1, h2, h3, h4, h5, h6, h7⟩
            · intro Jw hJw
              have hwi1_mod : (wi + 1 : BitVec 64).toNat = wi.toNat + 1 := by
                rw [BitVec.toNat_add, show (1 : BitVec 64).toNat = 1 from rfl]; omega
              have hidx_eq : (BitVec.setWidth 64
                  s.core.wvec[(BitVec.setWidth 64 f0 <<< OfNat.ofNat 1).toNat] + wi).toNat =
                  fullWatchOffCore s.core f0.toNat + wi.toNat := by
                simp only [BitVec.toNat_add, BitVec.toNat_setWidth, hw_idx_eq, hw_off_val, hw_mod1]
                exact Nat.mod_eq_of_lt (by
                  have := BitVec.isLt (s.core.wvec[2 * f0.toNat]?.getD 0#32)
                  unfold fullWatchOffCore at *; omega)
              have hidx_nat : (s.core.wvec[(2 * f0.toNat) % 2 ^ 64].toNat + wi.toNat) % 2 ^ 64 =
                  fullWatchOffCore s.core f0.toNat + wi.toNat := by
                simp only [Nat.mod_eq_of_lt (by omega : 2 * f0.toNat < 2 ^ 64), hw_off_val]
                exact Nat.mod_eq_of_lt (by
                  have := BitVec.isLt (s.core.wvec[2 * f0.toNat]?.getD 0#32)
                  unfold fullWatchOffCore at *; omega)
              generalize hrem_eq : fullWatchSizeCore s.core f0.toNat - wi.toNat = rem at hsl
              cases hsl with
              | empty => omega
              | bin hw0_some hw0_bin _hw0_ne hq_lt hq_ent hsl' =>
                rename_i rem_w w0_bv
                have hwi1_lt : (wi + 1 : BitVec 64).toNat ≤ fullWatchSizeCore s.core f0.toNat := by
                  omega
                have hsl'' : DenseWatchSliceOk F_cur s.core f0.toNat
                    (fullWatchOffCore s.core f0.toNat + (wi + 1 : BitVec 64).toNat)
                    (fullWatchSizeCore s.core f0.toNat - (wi + 1 : BitVec 64).toNat) := by
                  simpa only [hwi1_mod, Nat.add_assoc,
                    show fullWatchSizeCore s.core f0.toNat - (wi.toNat + 1) = rem_w from by omega]
                    using hsl'
                have hw0_load : s.core.wstk[(s.core.wvec[(2 * f0.toNat) % 2 ^ 64].toNat +
                    wi.toNat) % 2 ^ 64] = w0_bv := by
                  rw [← Option.some_inj, ← List.getElem?_eq_getElem (by omega), hidx_nat]
                  exact hw0_some
                have hw0_rhs :
                    ({ core := s.core, scratch := { s.scratch with scratch_buf := sb } } :
                      FullState).core.wstk[(BitVec.setWidth 64
                        s.core.wvec[(BitVec.setWidth 64 f0 <<< OfNat.ofNat 1).toNat] +
                        wi).toNat]'hwstk_idx = w0_bv := by
                  dsimp only; rw [← Option.some_inj, ← List.getElem?_eq_getElem (by omega), hidx_eq]
                  exact hw0_some
                have hq_vals : (BitVec.setWidth 64 (w0_bv &&& 2147483647#32)).toNat <
                    s.core.vals.length := by
                  simp only [BitVec.toNat_setWidth]
                  rw [Nat.mod_eq_of_lt (by have := BitVec.isLt (w0_bv &&& 2147483647#32); omega)]
                  omega
                have hcap_mod : (BitVec.ofNat 64 c.scratch_cap).toNat = c.scratch_cap := by
                  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
                have hsb_idx : (BitVec.setWidth 64 (BitVec.ofNat 32 (fidStepsCap
                      (BitVec.ofNat 64 c.scratch_cap).toNat) <<< OfNat.ofNat 2 + r0n)).toNat =
                    4 * fidStepsCap c.scratch_cap + r0n.toNat := by
                  simp only [hcap_mod, BitVec.toNat_setWidth, BitVec.toNat_add,
                    BitVec.toNat_shiftLeft, BitVec.toNat_ofNat,
                    show (OfNat.ofNat 2 : Nat) = 2 from rfl, Nat.shiftLeft_eq]
                  rw [show fidStepsCap c.scratch_cap % 2 ^ 32 * 2 ^ 2 % 2 ^ 32 =
                    4 * fidStepsCap c.scratch_cap by omega, Nat.mod_eq_of_lt (by omega),
                    Nat.mod_eq_of_lt (by omega)]
                have hsb_r0n : (BitVec.setWidth 64 (BitVec.ofNat 32 (fidStepsCap
                      (BitVec.ofNat 64 c.scratch_cap).toNat) <<< OfNat.ofNat 2 + r0n)).toNat <
                    sb.length := by rw [hsb_idx]; omega
                have hr0n1 : (r0n + 1 : BitVec 32).toNat = r0n.toNat + 1 := by
                  rw [BitVec.toNat_add, show (1 : BitVec 32).toNat = 1 from rfl]; omega
                c0_hsteps_nogrp
                · simp only [hw0_rhs]; c0_hsteps
                  · apply hJw; refine ⟨sb.set (4 * fidStepsCap c.scratch_cap + r0n.toNat) w0_bv,
                      by simp [hsb_l], hwi1_lt, by omega, by omega, hsl'', ?_, ?_, by omega⟩
                    · rw [hr0n1]; exact step0_rowOk_push (by omega) (by omega) hrows
                        ⟨[(w0_bv &&& 2147483647#32).toNat],
                         fun x hx => by simp at hx; subst hx; exact hq_lt,
                         by simp,
                         by unfold FidBvaRowEntryOk; rw [ite_eq_left hw0_bin]
                            exact ⟨hq_lt, rfl, hq_ent⟩,
                         hq_ent⟩
                    · dsimp only at *; rw [hsb_idx] at *; assumption
                  · exact hJw _ _ ⟨sb, hsb_l, hwi1_lt, by omega, h4sc, hsl'', hrows, hm2, by omega⟩
                · exfalso
                  have h_eq0 : s.core.wstk[(s.core.wvec[(2 * f0.toNat) % 2 ^ 64].toNat + wi.toNat) %
                      2 ^ 64] &&& 2147483648 = 0 := by assumption
                  rw [hw0_load] at h_eq0
                  exact hw0_bin
                    (by simpa only [show (2147483648 : BitVec 32) = 2147483648#32 from rfl,
                      show (0 : BitVec 32) = 0#32 from rfl] using h_eq0)
              | occ hw0_some hcr_some hw0_nbin _h3le _hcr_lt hcr_ref hsl' =>
                rename_i rem_w w0_bv cr_bv
                have hw0_load : s.core.wstk[(s.core.wvec[(2 * f0.toNat) % 2 ^ 64].toNat +
                    wi.toNat) % 2 ^ 64] = w0_bv := by
                  rw [← Option.some_inj, ← List.getElem?_eq_getElem (by omega), hidx_nat]
                  exact hw0_some
                c0_hsteps_nogrp
                · exfalso
                  have h_neg : ¬ s.core.wstk[(s.core.wvec[(2 * f0.toNat) % 2 ^ 64].toNat +
                      wi.toNat) % 2 ^ 64] &&& 2147483648 = 0 := by assumption
                  exact h_neg (by simpa only [hw0_load,
                    show (2147483648 : BitVec 32) = 2147483648#32 from rfl,
                    show (0 : BitVec 32) = 0#32 from rfl] using hw0_nbin)
                · refine wp_join_group (ts := [i64, i32, i64]) (fun ys ml3 => Jw ys ml3)
                    (fun _ (a, b, d, ()) ml3 hy => by c0_hsteps_nogrp; exact hy) ?_
                  intro Jw1 hJw1
                  have hidx_sz1 : (BitVec.setWidth 64 f0 <<< OfNat.ofNat 1 + 1).toNat =
                      (2 * f0.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 := by
                    simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth,
                      show (OfNat.ofNat 1 : Nat) = 1 from rfl, Nat.shiftLeft_eq]
                    rw [Nat.mod_eq_of_lt (by omega), show (1 : BitVec 64).toNat = 1 from rfl]; omega
                  have hsz_ok1 : (BitVec.setWidth 64 f0 <<< OfNat.ofNat 1 + 1).toNat <
                      s.core.wvec.length := by rw [hidx_sz1]; omega
                  have hoff_eq_w : (BitVec.setWidth 64
                      s.core.wvec[(BitVec.setWidth 64 f0 <<< OfNat.ofNat 1).toNat]).toNat =
                      fullWatchOffCore s.core f0.toNat := by
                    simp only [BitVec.toNat_setWidth, hw_idx_eq, hw_off_val]
                    exact Nat.mod_eq_of_lt (by omega)
                  have hsz_eq_w : (BitVec.setWidth 64
                      s.core.wvec[(BitVec.setWidth 64 f0 <<< OfNat.ofNat 1 + 1).toNat]).toNat =
                      fullWatchSizeCore s.core f0.toNat := by
                    simp only [BitVec.toNat_setWidth, hidx_sz1, hsz_val]
                    exact Nat.mod_eq_of_lt (by omega)
                  exact step0_occ_case_wp Γ Jw1 Jw wi _ _ tks r0n f0 cr_bv rem_w hsc_pos hsc_le
                    h4sc_cap hlen hwit hlm hnodup hext hlev hdm hsb_l hf0_lt hr0n_lt hwi1_mod
                    (by omega) (by omega) hoff_eq_w hsz_eq_w (by omega) hcr_some hcr_ref hsl'
                    hrows hm2 hJw1 hJw
          · exact hJex () ml2 rfl
          · exact hJex () ml2 rfl
    · intro Js hJs; c0_hsteps_nogrp
      · have hclt : BitVec.toNat init_cv ≤ s.core.cur_vars := by
          have := hc; rwa [Nat.mod_eq_of_lt (by omega)] at this
        have hsh : (init_cv <<< OfNat.ofNat 1).toNat ≤ 2 * s.core.cur_vars := by
          simp only [BitVec.toNat_shiftLeft, show (OfNat.ofNat 1 : Nat) = 1 from rfl]
          rw [Nat.mod_eq_of_lt (by omega)]; omega
        exact hJs (_, ()) m ⟨rfl, hsh⟩
      · have hsh : (BitVec.ofNat 64 s.core.cur_vars <<< OfNat.ofNat 1).toNat ≤
            2 * s.core.cur_vars := by
          simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat,
            show (OfNat.ofNat 1 : Nat) = 1 from rfl]
          rw [Nat.mod_eq_of_lt (by omega)]; omega
        exact hJs (_, ()) m ⟨rfl, hsh⟩

end

end LeanQbe.T.Examples.Kissat.Proof.Factor
