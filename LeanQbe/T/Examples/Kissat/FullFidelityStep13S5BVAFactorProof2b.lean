/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S5BVAFactorProof2a
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Examples.Kissat.FullArena1
import LeanQbe.T.Examples.Kissat.FullBvaFwdLemmas1
import LeanQbe.T.Examples.Kissat.FullFidelityStep7Proof2a0
import LeanQbe.T.Examples.Kissat.FullM6ProofUtil
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Fidelity Step 13 Shard S5-C — Factor Proofs Part 2b (`Proof2b`)

Proves `fac13_qi_scan_wp`, `fac13_try_ok_wp`, `fac13_exit_wp`, and `full_factor_s5_wp`
(`FullBvaHeap.fullFactorHeapSpec`, every theorem `<= 220` lines, `<= 100` cols) for
`FullFidelityStep13S5BVAFactor.full_factor_body`.
-/

set_option autoImplicit false

local elab "c0_hfast_nogrp" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps { unrollGroup := false, pruneJnz := false } 10000

local elab "c0_hfast" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps { pruneJnz := false } 10000

local elab "c0_hstraight" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps
    { splitJnz := false, unrollGroup := false, pruneJnz := false } 10000

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep13S5

open Std Std.Sat Std.ExtHashMap Kraken.Bedrock2.Test
open LeanQbe.T LeanQbe.T.ProofUtil LeanQbe.T.C0Step LeanQbe.T.C0HeadStep
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Full
open FullArenaTactics
open FullBvaHeap FullBvaHeap.FullBvaHeapHelpers FullBvaHeap.FullBvaHeapTactics
open FullFidelityBva FullFidelityStep7 FullFidelityStep9
open scoped FullArenaTactics FullBvaHeapTactics

/-! ## 1. `qi` Sub-Loop (`s13FacQiScanExpr` & `fac13_qi_scan_wp`) -/

@[expose] def s13FacQiScanExpr (c : FullCfg) (qn_bv ro_bv : BitVec 32) (nl64 : BitVec 64)
    (fac_lit qs_dec : BitVec 32) (nt2 : BitVec 64) (Ja : Cont [i64, i32]) :
    Expr Val Cont [i64] :=
  Expr.group (sig := [[i64, i32]])
    (fun Js =>
      Blocks.cons
        (fun p =>
          Expr.let_ (Op.mk (.cmp .ult i32 .bool rfl) (Arg.var p.snd.fst, Arg.var qn_bv, ()))
            fun p_1 =>
            Expr.jnz (Arg.var p_1.fst)
              (Expr.let_ (Op.mk (.add i32) (Arg.var ro_bv, Arg.var p.snd.fst, ())) fun p_2 =>
                Expr.let_ (Op.mk (.zext 32 64) (Arg.var p_2.fst, ())) fun p_3 =>
                  Expr.let_ (Op.mk (.mul i64) (Arg.var p_3.fst, Arg.imm 4, ())) fun p_4 =>
                    Expr.let_ (Op.mk (.add i64) (Arg.var c.pScratchBuf, Arg.var p_4.fst, ()))
                      fun p_5 =>
                      Expr.load i32 (Arg.var p_5.fst) fun ld =>
                        Expr.group (sig := [[i64]])
                          (fun _Js_1 =>
                            Blocks.cons
                              (fun p_6 =>
                                Expr.let_ (Op.mk (.add i32) (Arg.var p.snd.fst, Arg.imm 1, ()))
                                  fun p => Expr.jump Js.fst (Arg.var p_6.fst, Arg.var p.fst, ()))
                              Blocks.nil)
                          fun Js =>
                          Expr.let_ (Op.mk (.and i32) (Arg.var ld, Arg.imm 2147483648, ()))
                            fun p_6 =>
                            Expr.let_ (Op.mk (.cmp .ne i32 .bool rfl)
                                (Arg.var p_6.fst, Arg.imm 0, ())) fun p_7 =>
                              Expr.jnz (Arg.var p_7.fst)
                                (Expr.let_ (Op.mk (.and i32) (Arg.var ld, Arg.imm 2147483647, ()))
                                  fun p_8 =>
                                  Expr.group (sig := [[i64]])
                                    (fun _Js_1 =>
                                      Blocks.cons (fun p => Expr.jump Js.fst (Arg.var p.fst, ()))
                                        Blocks.nil)
                                    fun Js =>
                                    Expr.let_ (Op.mk (.zext 32 64) (Arg.var p_8.fst, ())) fun p_9 =>
                                      Expr.let_ (Op.mk (.cmp .ult i64 .bool rfl)
                                          (Arg.var p_9.fst, Arg.var nl64, ())) fun p_10 =>
                                        Expr.jnz (Arg.var p_10.fst)
                                          (Expr.let_ (Op.mk (.zext 32 64) (Arg.var p_8.fst, ()))
                                            fun p_11 =>
                                            Expr.let_ (Op.mk (.add i64)
                                                (Arg.var c.pLitMark, Arg.var p_11.fst, ()))
                                              fun p_12 =>
                                              Expr.load i8 (Arg.var p_12.fst) fun ld =>
                                                Expr.let_ (Op.mk (.trunc 32 8) (Arg.imm 0, ()))
                                                  fun p_13 =>
                                                  Expr.let_ (Op.mk (.zext 8 32) (Arg.var ld, ()))
                                                    fun p_14 =>
                                                    Expr.let_ (Op.mk (.zext 8 32)
                                                        (Arg.var p_13.fst, ())) fun p_15 =>
                                                      Expr.let_ (Op.mk (.cmp .eq i32 .bool rfl)
                                                          (Arg.var p_14.fst, Arg.var p_15.fst, ()))
                                                        fun p_16 =>
                                                        Expr.jnz (Arg.var p_16.fst)
                                                          (Expr.let_ (Op.mk (.cmp .ult i64 .bool
                                                         rfl) (Arg.var p.fst, Arg.var nl64, ()))
                                                            fun p_17 =>
                                                            Expr.jnz (Arg.var p_17.fst)
                                                              (Expr.let_ (Op.mk (.zext 32 64)
                                                                  (Arg.var p_8.fst, ())) fun p_18 =>
                                                                Expr.let_ (Op.mk (.add i64)
                                                                    (Arg.var c.pLitMark,
                                                                     Arg.var p_18.fst, ()))
                                                                  fun p_19 =>
                                                                  Expr.let_ (Op.mk (.trunc 32 8)
                                                                      (Arg.imm 1, ())) fun p_20 =>
                                                                    Expr.store (Arg.var p_20.fst)
                                                                      (Arg.var p_19.fst)
                                                                      (Expr.let_ (Op.mk (.mul i64)
                                                                          (Arg.var p.fst, Arg.imm 4,
                                                                           ())) fun p_21 =>
                                                                        Expr.let_ (Op.mk (.add i64)
                                                                            (Arg.var c.pWorkStk2,
                                                                             Arg.var p_21.fst, ()))
                                                                          fun p_22 =>
                                                                          Expr.store
                                                                            (Arg.var p_8.fst)
                                                                            (Arg.var p_22.fst)
                                                                            (Expr.let_
                                                                              (Op.mk (.add i64)
                                                                                (Arg.var p.fst,
                                                                                 Arg.imm 1, ()))
                                                                              fun p => Expr.jump
                                                                                Js.fst (Arg.var
                                                                                  p.fst, ()))))
                                                         (Expr.jump Js.fst (Arg.var p.fst, ())))
                                                          (Expr.jump Js.fst (Arg.var p.fst, ())))
                                          (Expr.jump Js.fst (Arg.var p.fst, ())))
                                (Expr.let_ (Op.mk (.zext 32 64) (Arg.var ld, ())) fun p_8 =>
                                  Expr.let_ (Op.mk (.add i64) (Arg.var p_8.fst, Arg.imm 2, ()))
                                    fun p_9 =>
                                    Expr.let_ (Op.mk (.mul i64) (Arg.var p_9.fst, Arg.imm 4, ()))
                                      fun p_10 =>
                                      Expr.let_ (Op.mk (.add i64)
                                          (Arg.var c.pArena, Arg.var p_10.fst, ())) fun p_11 =>
                                        Expr.load i32 (Arg.var p_11.fst) fun ld_1 =>
                                          Expr.group (sig := [[i64, i32]])
                                            (fun Js_1 =>
                                              Blocks.cons
                                                (fun p =>
                                                  Expr.let_ (Op.mk (.cmp .ult i32 .bool rfl)
                                                      (Arg.var p.snd.fst, Arg.var ld_1, ()))
                                                    fun p_12 =>
                                                    Expr.jnz (Arg.var p_12.fst)
                                                      (Expr.let_ (Op.mk (.zext 32 64)
                                                          (Arg.var ld, ())) fun p_13 =>
                                                        Expr.let_ (Op.mk (.add i64)
                                                            (Arg.var p_13.fst, Arg.imm 3, ()))
                                                          fun p_14 =>
                                                          Expr.let_ (Op.mk (.zext 32 64)
                                                              (Arg.var p.snd.fst, ())) fun p_15 =>
                                                            Expr.let_ (Op.mk (.add i64)
                                                                (Arg.var p_14.fst, Arg.var p_15.fst,
                                                                 ())) fun p_16 =>
                                                              Expr.let_ (Op.mk (.mul i64)
                                                                  (Arg.var p_16.fst, Arg.imm 4, ()))
                                                                fun p_17 =>
                                                                Expr.let_ (Op.mk (.add i64)
                                                                    (Arg.var c.pArena,
                                                                     Arg.var p_17.fst, ()))
                                                                  fun p_18 =>
                                                                  Expr.load i32 (Arg.var p_18.fst)
                                                                    fun ld =>
                                                                    Expr.group (sig := [[i64]])
                                                                      (fun _Js =>
                                                                        Blocks.cons
                                                                          (fun p_19 =>
                                                                            Expr.let_
                                                                              (Op.mk (.add i32)
                                                                                (Arg.var p.snd.fst,
                                                                                 Arg.imm 1, ()))
                                                                              fun p =>
                                                                              Expr.jump Js_1.fst
                                                                                (Arg.var p_19.fst,
                                                                                 Arg.var p.fst, ()))
                                                                          Blocks.nil)
                                                                      fun Js =>
                                                                      Expr.let_
                                                                        (Op.mk (.cmp .ne i32 .bool
                                                                            rfl) (Arg.var ld,
                                                                            Arg.var fac_lit, ()))
                                                                        fun p_19 =>
                                                                        Expr.jnz (Arg.var p_19.fst)
                                                                          (Expr.let_
                                                                            (Op.mk (.zext 32 64)
                                                                              (Arg.var ld, ()))
                                                                            fun p_20 =>
                                                                            Expr.let_
                                                                              (Op.mk (.cmp .ult i64
                                                                                .bool rfl)
                                                                                (Arg.var p_20.fst,
                                                                                 Arg.var nl64, ()))
                                                                              fun p_21 =>
                                                                              Expr.jnz
                                                                                (Arg.var p_21.fst)
                                                                                (Expr.let_
                                                                                  (Op.mk
                                                                                    (.zext 32 64)
                                                                                    (Arg.var ld,
                                                                                     ()))
                                                                                  fun p_22 =>
                                                                                  Expr.let_
                                                                                    (Op.mk (.add
                                                                                      i64) (Arg.var
                                                                                      c.pLitMark,
                                                                                      Arg.var
                                                                                        p_22.fst,
                                                                                      ()))
                                                                                    fun p_23 =>
                                                                                    Expr.load i8
                                                                                      (Arg.var
                                                                                        p_23.fst)
                                                                                      fun ld_2 =>
                                                                                      Expr.let_
                                                                                        (Op.mk
                                                                                          (.trunc 32
                                                                                            8)
                                                                                          (Arg.imm
                                                                                            0, ()))
                                                                                        fun p_24 =>
                                                                                        Expr.let_
                                                                                          (Op.mk
                                                                                            (.zext 8
                                                                                              32)
                                                                                            (Arg.var
                                                                                              ld_2,
                                                                                             ()))
                                                                                     fun p_25 =>
                                                                                          Expr.let_
                                                                                            (Op.mk
                                                                                              (.zext
                                                                                                8
                                                                                                32)
                                                                                        (Arg.var
                                                                                       p_24.fst,
                                                                                               ()))
                                                                                     fun p_26 =>
                                                                                       Expr.let_
                                                                                              (Op.mk
                                                                                           (.cmp
                                                                                             .eq
                                                                                             i32
                                                                                           .bool
                                                                                            rfl)
                                                                                        (Arg.var
                                                                                       p_25.fst,
                                                                                         Arg.var
                                                                                       p_26.fst,
                                                                                            ()))
                                                                                     fun p_27 =>
                                                                                        Expr.jnz
                                                                                        (Arg.var
                                                                                       p_27.fst)
                                                                                      (Expr.let_
                                                                                          (Op.mk
                                                                                           (.cmp
                                                                                            .ult
                                                                                             i64
                                                                                           .bool
                                                                                            rfl)
                                                                                        (Arg.var
                                                                                          p.fst,
                                                                                         Arg.var
                                                                                           nl64,
                                                                                            ()))
                                                                                     fun p_28 =>
                                                                                        Expr.jnz
                                                                                        (Arg.var
                                                                                       p_28.fst)
                                                                                      (Expr.let_
                                                                                          (Op.mk
                                                                                          (.zext
                                                                                              32
                                                                                             64)
                                                                                        (Arg.var
                                                                                             ld,
                                                                                            ()))
                                                                                     fun p_29 =>
                                                                                       Expr.let_
                                                                                          (Op.mk
                                                                                           (.add
                                                                                            i64)
                                                                                        (Arg.var
                                                                                     c.pLitMark,
                                                                                         Arg.var
                                                                                       p_29.fst,
                                                                                            ()))
                                                                                     fun p_30 =>
                                                                                       Expr.let_
                                                                                          (Op.mk
                                                                                         (.trunc
                                                                                              32
                                                                                              8)
                                                                                        (Arg.imm
                                                                                              1,
                                                                                            ()))
                                                                                     fun p_31 =>
                                                                                      Expr.store
                                                                                        (Arg.var
                                                                                       p_31.fst)
                                                                                        (Arg.var
                                                                                       p_30.fst)
                                                                                      (Expr.let_
                                                                                          (Op.mk
                                                                                           (.mul
                                                                                            i64)
                                                                                        (Arg.var
                                                                                          p.fst,
                                                                                         Arg.imm
                                                                                              4,
                                                                                            ()))
                                                                                     fun p_32 =>
                                                                                       Expr.let_
                                                                                          (Op.mk
                                                                                           (.add
                                                                                            i64)
                                                                                        (Arg.var
                                                                                    c.pWorkStk2,
                                                                                         Arg.var
                                                                                       p_32.fst,
                                                                                            ()))
                                                                                     fun p_33 =>
                                                                                      Expr.store
                                                                                        (Arg.var
                                                                                             ld)
                                                                                        (Arg.var
                                                                                       p_33.fst)
                                                                                      (Expr.let_
                                                                                          (Op.mk
                                                                                           (.add
                                                                                            i64)
                                                                                        (Arg.var
                                                                                          p.fst,
                                                                                         Arg.imm
                                                                                              1,
                                                                                            ()))
                                                                                        fun p =>
                                                                                       Expr.jump
                                                                                          Js.fst
                                                                                        (Arg.var
                                                                                          p.fst,
                                                                                           ()))))
                                                                                      (Expr.jump
                                                                                          Js.fst
                                                                                        (Arg.var
                                                                                          p.fst,
                                                                                           ())))
                                                                                      (Expr.jump
                                                                                          Js.fst
                                                                                        (Arg.var
                                                                                          p.fst,
                                                                                           ())))
                                                                                (Expr.jump
                                                                                  Js.fst
                                                                                  (Arg.var p.fst,
                                                                                   ())))
                                                                          (Expr.jump Js.fst
                                                                            (Arg.var p.fst, ())))
                                                      (Expr.jump Js.fst (Arg.var p.fst, ())))
                                                Blocks.nil)
                                            fun Js =>
                                            Expr.jump Js.fst (Arg.var p.fst, Arg.imm 0, ())))
              (Expr.jump Ja (Arg.var p.fst, Arg.var qs_dec, ())))
        Blocks.nil)
    fun Js => Expr.jump Js.fst (Arg.var nt2, Arg.imm 0, ())

theorem fac13_qi_scan_wp {Γ : Env} {Q : Post [i64]} {X : XPost}
    {c : FullCfg} {F0 : CNF Nat} {st3 : FullState} {R : Mem 64 → Prop}
    {qn_bv ro_bv : BitVec 32} {nl64 : BitVec 64} {fac_lit qs_dec : BitVec 32}
    {nt2 : BitVec 64} {tmk2 : List (BitVec 8)} {tlits2 : List (BitVec 32)} {mP2 : Mem 64}
    {Ja : Cont [i64, i32]}
    (hmx : c.max_vars < 2 * dimacsBound) (hscr_b : c.scratch_cap < 2 ^ 28)
    (hinv3 : FullDenseInv c F0 st3) (hnl64 : nl64.toNat = 2 * st3.core.cur_vars)
    (hroqn_bnd : ro_bv.toNat + qn_bv.toNat ≤ c.scratch_cap)
    (hrow_ok : ∀ qi_n < qn_bv.toNat,
      Step7RowRefOk st3 (st3.scratch.scratch_buf[ro_bv.toNat + qi_n]?.getD 0#32))
    (hT2 : S13TouchInv c st3 R nt2 tmk2 tlits2 mP2)
    (hJa_next : ∀ ntQ mQ, (∃ tmkQ tlitsQ, S13TouchInv c st3 R ntQ tmkQ tlitsQ mQ) →
      Ja (ntQ, qs_dec, ()) mQ) :
    wp Γ Q X (s13FacQiScanExpr c qn_bv ro_bv nl64 fac_lit qs_dec nt2 Ja) mP2 := by
  unfold dimacsBound at hmx
  have h3l := hinv3.1.lengths
  have h3_cv_le := h3l.core_ok.cur_vars_le
  have h3_cv32 : 2 * c.max_vars < 2 ^ 30 := by omega
  obtain ⟨htmk2_l, htlits2_l, hnt2_le, htlits2_b, hcov2, hmP2⟩ := hT2
  unfold s13FacQiScanExpr
  refine wp_loop_inv (ts := [i64, i32])
    (fun (ntQ, qi, ()) mQ => qi.toNat ≤ qn_bv.toNat ∧ ∃ tmkQ tlitsQ,
      S13TouchInv c st3 R ntQ tmkQ tlitsQ mQ)
    (fun (_, qi, ()) _ => qn_bv.toNat - qi.toNat)
    (fun Jq hJq => by
      c0_hfast_nogrp
      exact hJq (nt2, 0#32, ()) mP2 ⟨Nat.zero_le _, tmk2, tlits2,
        htmk2_l, htlits2_l, hnt2_le, htlits2_b, hcov2, hmP2⟩)
    (fun Jq (ntQ, qi, ()) mQ
        ⟨hqi_le, tmkQ, tlitsQ, htmkQ_l, htlitsQ_l, hntQ_le, htlitsQ_b, hcovQ, hmQ⟩ ihq => ?_)
  · c0_hfast_nogrp
    · have hqi_lt : qi.toNat < qn_bv.toNat := BitVec.lt_def.mp (by assumption)
      have hqi1 : (qi + 1#32).toNat = qi.toNat + 1 :=
        fac13_bv32_add1 (Nat.lt_of_le_of_lt hqi_lt qn_bv.isLt)
      have hro_add_qi : ro_bv.toNat + qi.toNat < c.scratch_cap :=
        Nat.lt_of_lt_of_le (Nat.add_lt_add_left hqi_lt _) hroqn_bnd
      have hcw_idx : (ro_bv + qi).toNat = ro_bv.toNat + qi.toNat := by
        rw [BitVec.toNat_add, Nat.mod_eq_of_lt
          (Nat.lt_trans hro_add_qi (Nat.lt_trans hscr_b (by decide)))]
      have hcw_sc : (BitVec.setWidth 64 (ro_bv + qi)).toNat <
          st3.scratch.scratch_buf.length := by
        rw [fid_bv64_32, hcw_idx, h3l.scratch_ok.scratch_buf_len]; exact hro_add_qi
      let cw := st3.scratch.scratch_buf[(BitVec.setWidth 64 (ro_bv + qi)).toNat]'hcw_sc
      have hcw_ok : Step7RowRefOk st3 cw := by
        have h := hrow_ok qi.toNat hqi_lt
        rw [List.getElem?_eq_getElem (by rw [h3l.scratch_ok.scratch_buf_len]; exact hro_add_qi),
          Option.getD_some] at h
        simpa only [cw, fid_bv64_32, hcw_idx] using h
      have hcw_sc_Q : (BitVec.setWidth 64 (ro_bv + qi)).toNat <
          (s13SetLmWs2 st3 tmkQ tlitsQ).scratch.scratch_buf.length := by
        dsimp only [s13SetLmWs2]; exact hcw_sc
      c0_hfast_nogrp
      refine wp_join_group (ts := [i64]) (fun (nt', ()) mQ' =>
          ∃ tmk' tlits', S13TouchInv c st3 R nt' tmk' tlits' mQ') ?_ ?_
      · rintro _ ⟨nt', ⟨⟩⟩ mQ' ⟨tmk', tlits', hT'⟩
        c0_hstraight
        exact ihq (nt', qi + 1#32, ()) mQ'
          (by dsimp only; rw [hqi1]; exact fac13_sub1_lt hqi_lt)
          ⟨by rw [hqi1]; exact hqi_lt, tmk', tlits', hT'⟩
      · intro _ hJs
        c0_hstraight
        refine LeanQbe.T.C0HeadStep.head_wp_jnz rfl ?_ ?_
        · intro hcBin
          have hbin : (cw &&& 0x80000000#32) ≠ 0#32 := by
            have h1 := bne_iff_ne.mp hcBin
            dsimp only [s13SetLmWs2] at h1; exact h1
          have hol_lt : (cw &&& 0x7FFFFFFF#32).toNat < 2 * st3.core.cur_vars := by
            unfold Step7RowRefOk at hcw_ok; rwa [ite_eq_left hbin] at hcw_ok
          c0_hstraight
          refine wp_join_group (ts := [i64]) (fun (nt', ()) mQ' =>
              ∃ tmk' tlits', S13TouchInv c st3 R nt' tmk' tlits' mQ') ?_ ?_
          · rintro _ ⟨nt', ⟨⟩⟩ mQ' ⟨tmk', tlits', hT'⟩
            c0_hstraight; exact hJs (nt', ()) mQ' ⟨tmk', tlits', hT'⟩
          · intro _ hJo
            c0_hfast_nogrp
            · have hlm_x : (BitVec.setWidth 64 (cw &&& 0x7FFFFFFF#32)).toNat < tmkQ.length := by
                rw [fid_bv64_32, htmkQ_l]
                exact Nat.lt_of_lt_of_le hol_lt (Nat.mul_le_mul_left 2 h3_cv_le)
              c0_hfast_nogrp
              · have hntQ_lt : ntQ.toNat < 2 * st3.core.cur_vars := by
                  have h1 : ntQ.toNat < nl64.toNat := BitVec.lt_def.mp (by assumption)
                  rwa [hnl64] at h1
                have hntQ1 : (ntQ + 1#64).toNat = ntQ.toNat + 1 :=
                  fac13_bv64_add1 (Nat.lt_trans (Nat.add_lt_add_right hntQ_lt 1)
                    (Nat.lt_of_le_of_lt (Nat.add_le_add_right (Nat.mul_le_mul_left 2 h3_cv_le) 1)
                      (Nat.lt_trans (Nat.add_lt_add_right h3_cv32 1) (by decide))))
                have hws_nt : ntQ.toNat < tlitsQ.length := by
                  rw [htlitsQ_l]; exact Nat.lt_of_lt_of_le hntQ_lt (Nat.mul_le_mul_left 2 h3_cv_le)
                c0_hfast_nogrp
                have hpsQ := s13_push_touched_step h3_cv_le htmkQ_l htlitsQ_l hol_lt hntQ_lt hntQ1
                  htlitsQ_b hcovQ
                exact hJo (ntQ + 1#64, ()) _ ⟨_, _,
                  hpsQ.1, hpsQ.2.1, hpsQ.2.2.1, hpsQ.2.2.2.1, hpsQ.2.2.2.2, by assumption⟩
              all_goals
                exact hJo (ntQ, ()) mQ ⟨tmkQ, tlitsQ, htmkQ_l, htlitsQ_l,
                  hntQ_le, htlitsQ_b, hcovQ, hmQ⟩
            · exact hJo (ntQ, ()) mQ ⟨tmkQ, tlitsQ, htmkQ_l, htlitsQ_l,
                hntQ_le, htlitsQ_b, hcovQ, hmQ⟩
        · intro hcCls
          have hnbin : (cw &&& 0x80000000#32) = 0#32 := by
            exact if h : (cw &&& 0x80000000#32) = 0#32 then h else
              False.elim <| by
                have hb := bne_iff_ne.mpr h
                have hfl : ((cw &&& 0x80000000#32) != 0#32) = false := by
                  have h1 := hcCls; dsimp only [s13SetLmWs2] at h1; exact h1
                rw [hfl] at hb; cases hb
          have hcw_lg : cw.toNat ∈ fullArenaClauseRefs st3 ∧
              cw.toNat + 3 + fullArenaClauseSize st3 cw.toNat ≤ st3.core.arena_len ∧
              ∀ l ∈ fullArenaClauseLits st3 cw.toNat, l < 2 * st3.core.cur_vars := by
            unfold Step7RowRefOk at hcw_ok; rwa [ite_eq_right (fun h => h hnbin)] at hcw_ok
          have har_lt32 : st3.core.arena_len < 2 ^ 32 := by
            have := h3l.core_ok.arena_len_le; have := h3l.core_ok.arena_len_arr
            have := c.harena; unfold dimacsBound at *; omega
          have har2_lt : (BitVec.setWidth 64 cw + 2#64).toNat < st3.core.arena.length := by
            rw [BitVec.toNat_add, fid_bv64_32, show (2#64 : BitVec 64).toNat = 2 from rfl,
              Nat.mod_eq_of_lt (fac13_cw_32_add2 hcw_lg.2.1 har_lt32), h3l.core_ok.arena_len_arr]
            exact fac13_cw_ar2_lt hcw_lg.2.1
              (h3l.core_ok.arena_len_arr ▸ h3l.core_ok.arena_len_le)
          c0_hstraight
          let csz_bv := st3.core.arena[(BitVec.setWidth 64 cw + 2#64).toNat]'har2_lt
          have hcsz_eq : csz_bv.toNat = fullArenaClauseSizeCore st3.core cw.toNat := by
            dsimp only [csz_bv]; unfold fullArenaClauseSizeCore
            have hidx : (BitVec.setWidth 64 cw + 2#64).toNat = cw.toNat + 2 := by
              rw [BitVec.toNat_add, fid_bv64_32, show (2#64 : BitVec 64).toNat = 2 from rfl,
                Nat.mod_eq_of_lt (fac13_cw_32_add2 hcw_lg.2.1 har_lt32)]
            simp only [hidx]
            rw [List.getElem?_eq_getElem (by
              rw [h3l.core_ok.arena_len_arr]
              exact fac13_cw_ar2_lt hcw_lg.2.1
                (h3l.core_ok.arena_len_arr ▸ h3l.core_ok.arena_len_le)), Option.getD_some]
          refine wp_loop_inv (ts := [i64, i32])
            (fun (ntL, lj, ()) mL => lj.toNat ≤ csz_bv.toNat ∧
              ∃ tmkL tlitsL, S13TouchInv c st3 R ntL tmkL tlitsL mL)
            (fun (_, lj, ()) _ => csz_bv.toNat - lj.toNat)
            (fun Jl hJl => by
              c0_hstraight
              exact hJl (ntQ, 0#32, ()) mQ ⟨Nat.zero_le _, tmkQ, tlitsQ,
                htmkQ_l, htlitsQ_l, hntQ_le, htlitsQ_b, hcovQ, hmQ⟩)
            (fun Jl (ntL, lj, ()) mL
                ⟨hlj_le, tmkL, tlitsL, htmkL_l, htlitsL_l, hntL_le, htlitsL_b, hcovL, hmL⟩
                ihl => ?_)
          · c0_hfast_nogrp
            · have hlj_lt : lj.toNat < csz_bv.toNat := BitVec.lt_def.mp (by assumption)
              have hcsz_le_ar : csz_bv.toNat ≤ st3.core.arena_len := by
                rw [hcsz_eq]; exact Nat.le_trans (Nat.le_add_left _ _) hcw_lg.2.1
              have hlj1 : (lj + 1#32).toNat = lj.toNat + 1 := fac13_bv32_add1 (by omega)
              have hcsz_cl : csz_bv.toNat = fullArenaClauseSize st3 cw.toNat := hcsz_eq
              have harl_idx : (BitVec.setWidth 64 cw + 3#64 + BitVec.setWidth 64 lj).toNat =
                  cw.toNat + 3 + lj.toNat := by
                rw [BitVec.toNat_add, BitVec.toNat_add, fid_bv64_32, fid_bv64_32,
                  show (3#64 : BitVec 64).toNat = 3 from rfl,
                  Nat.mod_eq_of_lt (fac13_arl_idx_lt1 hcw_lg.2.1 har_lt32),
                  Nat.mod_eq_of_lt (fac13_arl_idx_lt2 (hcsz_cl ▸ hlj_lt) hcw_lg.2.1 har_lt32)]
              have harl_lt : (BitVec.setWidth 64 cw + 3#64 + BitVec.setWidth 64 lj).toNat <
                  st3.core.arena.length := by
                rw [harl_idx, h3l.core_ok.arena_len_arr]
                exact fac13_arl_ar_lt (hcsz_cl ▸ hlj_lt) hcw_lg.2.1
                  (h3l.core_ok.arena_len_arr ▸ h3l.core_ok.arena_len_le)
              have hl_lt : (st3.core.arena[(BitVec.setWidth 64 cw + 3#64 +
                  BitVec.setWidth 64 lj).toNat]'harl_lt).toNat < 2 * st3.core.cur_vars := by
                have hg := FullBvaFwdHelpers.fullArenaClauseLitsCore_getElem
                  (k := st3.core) (r := cw.toNat) (j := lj.toNat)
                  (by rw [← hcsz_eq]; exact hlj_lt) (by rw [← harl_idx]; exact harl_lt)
                have hmem : (st3.core.arena[(BitVec.setWidth 64 cw + 3#64 +
                    BitVec.setWidth 64 lj).toNat]'harl_lt).toNat ∈
                    fullArenaClauseLits st3 cw.toNat := by
                  apply List.mem_iff_getElem?.mpr; refine ⟨lj.toNat, ?_⟩
                  simpa only [harl_idx] using hg
                exact hcw_lg.2.2 _ hmem
              c0_hfast_nogrp
              · refine wp_join_group (ts := [i64]) (fun (ntL', ()) mL' =>
                    ∃ tmkL' tlitsL', S13TouchInv c st3 R ntL' tmkL' tlitsL' mL') ?_ ?_
                · rintro _ ⟨ntL', ⟨⟩⟩ mL' ⟨tmkL', tlitsL', hTL'⟩
                  c0_hfast_nogrp
                  exact ihl (ntL', lj + 1#32, ()) mL'
                    (by dsimp only; rw [hlj1]; exact fac13_sub1_lt hlj_lt)
                    ⟨by rw [hlj1]; exact hlj_lt, tmkL', tlitsL', hTL'⟩
                · intro _ hJl'
                  c0_hfast_nogrp
                  · have hlm_l : (BitVec.setWidth 64 (st3.core.arena[(BitVec.setWidth 64 cw + 3#64 +
                        BitVec.setWidth 64 lj).toNat]'harl_lt)).toNat < tmkL.length := by
                      rw [fid_bv64_32, htmkL_l]
                      exact Nat.lt_of_lt_of_le hl_lt (Nat.mul_le_mul_left 2 h3_cv_le)
                    c0_hfast_nogrp
                    · have hntL_lt : ntL.toNat < 2 * st3.core.cur_vars := by
                        have h1 : ntL.toNat < nl64.toNat := BitVec.lt_def.mp (by assumption)
                        rwa [hnl64] at h1
                      have hntL1 : (ntL + 1#64).toNat = ntL.toNat + 1 :=
                        fac13_bv64_add1 (by omega)
                      have hws_nt : ntL.toNat < tlitsL.length := by
                        rw [htlitsL_l]
                        exact Nat.lt_of_lt_of_le hntL_lt (Nat.mul_le_mul_left 2 h3_cv_le)
                      c0_hfast_nogrp
                      have hpsL := s13_push_touched_step h3_cv_le htmkL_l htlitsL_l hl_lt hntL_lt
                        hntL1 htlitsL_b hcovL
                      exact hJl' (ntL + 1#64, ()) _ ⟨_, _,
                        hpsL.1, hpsL.2.1, hpsL.2.2.1, hpsL.2.2.2.1, hpsL.2.2.2.2, by assumption⟩
                    all_goals
                      exact hJl' (ntL, ()) mL ⟨tmkL, tlitsL, htmkL_l, htlitsL_l,
                        hntL_le, htlitsL_b, hcovL, hmL⟩
                  all_goals
                    exact hJl' (ntL, ()) mL ⟨tmkL, tlitsL, htmkL_l, htlitsL_l,
                      hntL_le, htlitsL_b, hcovL, hmL⟩
            · exact hJs (ntL, ()) mL ⟨tmkL, tlitsL, htmkL_l, htlitsL_l,
                hntL_le, htlitsL_b, hcovL, hmL⟩
    · exact hJa_next ntQ mQ ⟨tmkQ, tlitsQ, htmkQ_l, htlitsQ_l, hntQ_le, htlitsQ_b, hcovQ, hmQ⟩

/-! ## 2. Exit Loop & `full_factor_s5_wp` Helpers -/

@[expose] def s13FacExitExpr (c : FullCfg) (st : FullState) (init_cv : Nat) (_Q : Post [i64]) :
    Expr Val Cont [i64] :=
  Expr.group (sig := [[i64]])
    (fun Js =>
      Blocks.cons
        (fun (p : Tup Val [i64]) =>
          Expr.let_ (Op.mk (.cmp .ult i64 .bool rfl)
              (Arg.var p.fst, Arg.var (BitVec.ofNat 64 st.core.cur_vars <<< (1 : Nat)), ()))
            fun p_1 =>
            Expr.jnz (Arg.var p_1.fst)
              (Expr.let_ (Op.mk (.mul i64) (Arg.var p.fst, Arg.imm 4, ())) fun p_2 =>
                Expr.let_ (Op.mk (.add i64) (Arg.var c.pTarjanMark, Arg.var p_2.fst, ()))
                  fun p_3 =>
                  Expr.store (t := i32) (Arg.imm 0) (Arg.var p_3.fst)
                    (Expr.let_ (Op.mk (.mul i64) (Arg.var p.fst, Arg.imm 4, ())) fun p_4 =>
                      Expr.let_ (Op.mk (.add i64) (Arg.var c.pTarjanReach, Arg.var p_4.fst, ()))
                        fun p_5 =>
                        Expr.store (t := i32) (Arg.imm 0) (Arg.var p_5.fst)
                          (Expr.let_ (Op.mk (.add i64) (Arg.var p.fst, Arg.imm 1, ())) fun p6 =>
                            Expr.jump Js.fst (Arg.var p6.fst, ()))))
              (Expr.group (sig := [[]])
                (fun _ =>
                  Blocks.cons (fun (_ : Tup Val []) => Expr.ret (Arg.imm (t := i64) 1, ()))
                    Blocks.nil)
                fun Js_ret =>
                Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 776, ())) fun p_2 =>
                  Expr.load i64 (Arg.var p_2.fst) fun ld =>
                    Expr.let_ (Op.mk (.cmp .ugt i64 .bool rfl)
                        (Arg.var ld, Arg.var (BitVec.ofNat 64 init_cv), ())) fun p_3 =>
                      Expr.jnz (Arg.var p_3.fst)
                        (Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 776, ())) fun p_4 =>
                          Expr.load i64 (Arg.var p_4.fst) fun ld =>
                            Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 376, ()))
                              fun p_5 =>
                              Expr.load i64 (Arg.var p_5.fst) fun ld_1 =>
                                Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 384, ()))
                                  fun p_6 =>
                                  Expr.load i64 (Arg.var p_6.fst) fun ld_2 =>
                                    Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 608, ()))
                                      fun p_7 =>
                                      Expr.load i64 (Arg.var p_7.fst) fun ld_3 =>
                                        Expr.group (sig := [[i64, i64]])
                                          (fun Js1 =>
                                            Blocks.cons
                                              (fun (p : Tup Val [i64, i64]) =>
                                                Expr.group (sig := [[]])
                                                  (fun _ =>
                                                    Blocks.cons
                                                      (fun (_ : Tup Val []) =>
                                                        Expr.let_ (Op.mk (.add i64)
                                                            (Arg.var c.hdr, Arg.imm 640, ()))
                                                          fun p_10 =>
                                                          Expr.store (t := i64) (Arg.var p.snd.fst)
                                                            (Arg.var p_10.fst)
                                                            (Expr.let_ (Op.mk (.add i64)
                                                                (Arg.var c.hdr, Arg.imm 616, ()))
                                                              fun p_11 =>
                                                              Expr.load i64 (Arg.var p_11.fst)
                                                                fun ld_4 =>
                                                                Expr.let_ (Op.mk (.add i64)
                                                                    (Arg.var c.hdr, Arg.imm 624,
                                                                     ())) fun p_12 =>
                                                                  Expr.store (t := i64)
                                                                    (Arg.var ld_4)
                                                                    (Arg.var p_12.fst)
                                                                    (Expr.let_ (Op.mk (.add i64)
                                                                        (Arg.var c.hdr,
                                                                         Arg.imm 632, ()))
                                                                      fun p_13 =>
                                                                      Expr.store (t := i64)
                                                                        (Arg.var p.snd.fst)
                                                                        (Arg.var p_13.fst)
                                                                        (Expr.jump Js_ret.fst
                                                                          ()))))
                                                      Blocks.nil)
                                                  fun Jbr =>
                                                  Expr.let_ (Op.mk (.cmp .ult i64 .bool rfl)
                                                      (Arg.var p.fst, Arg.var ld, ())) fun p_8 =>
                                                    Expr.jnz (Arg.var p_8.fst)
                                                      (Expr.let_ (Op.mk (.cmp .ult i64 .bool rfl)
                                                          (Arg.var p.snd.fst, Arg.var ld, ()))
                                                        fun p_9 =>
                                                        Expr.jnz (Arg.var p_9.fst)
                                                          (Expr.let_ (Op.mk (.add i64)
                                                              (Arg.var p.snd.fst, Arg.imm 1, ()))
                                                            fun p_10 =>
                                                            Expr.let_ (Op.mk (.mul i64)
                                                                (Arg.var p.fst, Arg.imm 4, ()))
                                                              fun p_11 =>
                                                              Expr.let_ (Op.mk (.add i64)
                                                                  (Arg.var ld_2, Arg.var p_11.fst,
                                                                   ())) fun p_12 =>
                                                                Expr.let_ (Op.mk (.trunc 64 32)
                                                                    (Arg.var p_10.fst, ()))
                                                                  fun p_13 =>
                                                                  Expr.store (t := i32)
                                                                    (Arg.var p_13.fst)
                                                                    (Arg.var p_12.fst)
                                                                    (Expr.let_ (Op.mk (.mul i64)
                                                                        (Arg.var p.fst, Arg.imm 4,
                                                                         ())) fun p_14 =>
                                                                      Expr.let_ (Op.mk (.add i64)
                                                                          (Arg.var ld_1,
                                                                           Arg.var p_14.fst, ()))
                                                                        fun p_15 =>
                                                                        Expr.load i32
                                                                          (Arg.var p_15.fst)
                                                                          fun ld_n =>
                                                                          Expr.let_
                                                                            (Op.mk (.zext 32 64)
                                                                              (Arg.var ld_n, ()))
                                                                            fun p_16 =>
                                                                            Expr.jump Js1.fst
                                                                              (Arg.var p_16.fst,
                                                                               Arg.var p_10.fst,
                                                                               ())))
                                                          (Expr.jump Jbr.fst ()))
                                                      (Expr.jump Jbr.fst ()))
                                              Blocks.nil)
                                          fun Js1 =>
                                            Expr.jump Js1.fst (Arg.var ld_3, Arg.imm 0, ()))
                        (Expr.jump Js_ret.fst ())))
        Blocks.nil)
    fun Js => Expr.jump Js.fst (Arg.imm 0, ())

private theorem fac13_exit_wp {Γ : Env} {Q : Post [i64]} {X : XPost}
    {c : FullCfg} {F0 : CNF Nat} {st : FullState} {R : Mem 64 → Prop} {mw : Mem 64}
    {init_cv : Nat} {init_fuel : BitVec 64}
    (hcv_st : init_cv ≤ st.core.cur_vars) (hfu_st : st.core.fuel = init_fuel)
    (hinv_st : FullDenseInv c F0 st) (hmw : (FullMem c st ⋆ R) mw)
    (hQ : ∀ (res : BitVec 64) (s' : FullState) (m' : Mem 64),
      FullDenseInv c F0 s' → init_cv ≤ s'.core.cur_vars → s'.core.fuel = init_fuel →
      res = 1#64 → (FullMem c s' ⋆ R) m' → Q (res, ()) m') :
    wp Γ Q X (s13FacExitExpr c st init_cv Q) mw := by
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hstl := hinv_st.1.lengths; have hst_cv_le := hstl.core_ok.cur_vars_le
  have henl_eq : (BitVec.ofNat 64 st.core.cur_vars <<< (1 : Nat)).toNat = 2 * st.core.cur_vars := by
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]; omega
  unfold s13FacExitExpr
  refine wp_loop_inv (ts := [i64])
    (fun (ci, ()) mf => ci.toNat ≤ 2 * st.core.cur_vars ∧ ∃ hpf psf,
      hpf.length = 2 * c.max_vars ∧ psf.length = 2 * c.max_vars ∧
      (FullMem c { st with scratch := { st.scratch with tarjan_mark := hpf, tarjan_reach := psf } }
        ⋆ R) mf)
    (fun (ci, ()) _ => 2 * st.core.cur_vars - ci.toNat) ?_ ?_
  · intro J4 hJ4
    c0_hfast_nogrp
    exact hJ4 (0#64, ()) mw ⟨Nat.zero_le _, st.scratch.tarjan_mark,
      st.scratch.tarjan_reach, hstl.scratch_ok.tarjan_mark_len,
      hstl.scratch_ok.tarjan_reach_len, hmw⟩
  · intro J4 (ci, ()) mf ⟨hci_le, hpf, psf, hhpf, hpsf, hmf⟩ ih4
    c0_hfast_nogrp
    · have hci_lt : ci.toNat < 2 * st.core.cur_vars := by
        have h1 := BitVec.lt_def.mp
          (by assumption : ci < (BitVec.ofNat 64 st.core.cur_vars <<< (1 : Nat)))
        rwa [henl_eq] at h1
      have hci1 : (ci + 1#64).toNat = ci.toNat + 1 := fac13_bv64_add1 (by omega)
      c0_hfast_nogrp
      refine ih4 (ci + 1#64, ()) _ (by dsimp only; rw [hci1]; omega)
        ⟨by rw [hci1]; omega, _, _, ?_, ?_, by assumption⟩ <;> simp [hhpf, hpsf]
    · clear ih4
      let stf : FullState :=
        { st with scratch := { st.scratch with tarjan_mark := hpf, tarjan_reach := psf } }
      have hinvf := s13_dense_set_fheap hinv_st hhpf hpsf
      have hfl := hinvf.1.lengths; have hstf_cv_le : stf.core.cur_vars ≤ c.max_vars :=
        hfl.core_ok.cur_vars_le
      refine wp_join_group (ts := []) (fun _ mEx => ∃ s' : FullState,
          FullDenseInv c F0 s' ∧ init_cv ≤ s'.core.cur_vars ∧ s'.core.fuel = init_fuel ∧
          (FullMem c s' ⋆ R) mEx)
        (fun _ _ mEx ⟨s', hinv', hcv', hfu', hmEx⟩ => by
          c0_hfast_nogrp
          exact hQ 1#64 s' mEx hinv' hcv' hfu' rfl hmEx)
        (fun Js_ret hJs_ret => ?_)
      c0_hfast_nogrp
      · refine wp_loop_inv (ts := [i64, i64])
          (fun (qidx, qst, ()) mq => qst.toNat ≤ stf.core.cur_vars ∧
            ∃ qs' : List (BitVec 32), qs'.length = c.max_vars ∧
            (FullMem c { stf with scratch := { stf.scratch with q_stamp := qs' } } ⋆ R) mq)
          (fun (_, qst, ()) _ => stf.core.cur_vars - qst.toNat) ?_ ?_
        · intro J9 hJ9
          c0_hfast_nogrp
          exact hJ9 (_, 0#64, ()) mf
            ⟨Nat.zero_le _, stf.scratch.q_stamp, hfl.scratch_ok.q_stamp_len, hmf⟩
        · intro J9 (qidx, qst, ()) mq ⟨hqst_le, qs', hqs', hmq⟩ ih9
          refine wp_join_group (ts := []) (fun _ mq' => mq' = mq) ?_ ?_
          · rintro _ ⟨⟩ mq' rfl
            c0_hfast_nogrp
            let stq : FullState :=
              { stf with scratch := { stf.scratch with
                q_stamp := qs', q_cur_stamp := qst,
                q_search_idx := stf.scratch.q_last, q_search_stamp := qst } }
            have hinvq : FullDenseInv c F0 stq :=
              hinvf.of_safetySlice ⟨hfl.core_ok, { hfl.scratch_ok with q_stamp_len := hqs' }⟩
                rfl ⟨rfl, rfl⟩
            exact hJs_ret () _ ⟨stq, hinvq, hcv_st, hfu_st, by assumption⟩
          · intro _ hJbr
            c0_hfast_nogrp
            · have hqi_lt : qidx.toNat < stf.core.cur_vars := by
                have h1 := BitVec.lt_def.mp
                  (by assumption : qidx < BitVec.ofNat 64 st.core.cur_vars)
                rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h1
              have hqs_lt : qst.toNat < stf.core.cur_vars := by
                have h1 := BitVec.lt_def.mp
                  (by assumption : qst < BitVec.ofNat 64 st.core.cur_vars)
                rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h1
              have hqs_idx : qidx.toNat < qs'.length := by rw [hqs']; omega
              have hqn_idx : qidx.toNat < stf.scratch.q_next.length := by
                rw [hfl.scratch_ok.q_next_len]; omega
              have hqst1 : (qst + 1#64).toNat = qst.toNat + 1 := fac13_bv64_add1 (by omega)
              c0_hfast_nogrp
              refine ih9 (BitVec.setWidth 64 (stf.scratch.q_next[qidx.toNat]'hqn_idx),
                  qst + 1#64, ()) _ (by dsimp only; rw [hqst1]; omega)
                ⟨by rw [hqst1]; omega,
                  qs'.set qidx.toNat (BitVec.setWidth 32 (qst + 1#64)),
                  by rw [List.length_set, hqs'], by assumption⟩
            all_goals exact hJbr () mq rfl
      · exact hJs_ret () mf ⟨stf, hinvf, hcv_st, hfu_st, hmf⟩

private theorem fac13_bv32_xor1_lt {fv : BitVec 32} {lim : Nat} (h : fv.toNat < lim)
    (heven : lim % 2 = 0) : (fv ^^^ 1#32).toNat < lim := by
  have h1 : (fv ^^^ 1#32).toNat = 2 * (fv.toNat / 2) + (1 - fv.toNat % 2) := by
    rw [BitVec.toNat_xor, show (1#32 : BitVec 32).toNat = 1 from rfl]
    apply Nat.eq_of_testBit_eq; intro i; rw [Nat.testBit_xor]
    cases i with
    | zero =>
      simp only [Nat.testBit_zero]
      rcases Nat.mod_two_eq_zero_or_one fv.toNat with r | r <;> simp [r]
    | succ k =>
      simp only [Nat.testBit_succ]
      have h1_sh : 1 / 2 = 0 := by decide
      have h1_rhs : (2 * (fv.toNat / 2) + (1 - fv.toNat % 2)) / 2 = fv.toNat / 2 := by omega
      simp [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul, h1_rhs, h1_sh]
  omega

theorem full_factor_s5_wp (Γ : Env)
    (hSteps : ∀ a m Q X, fidBvaStepsCapSpec a m Q X →
      Γ "full_bva_steps_cap_fid" [i64] [i32] a m Q X)
    (hConnect : ∀ a m Q X, fidBvaConnectClausesSpec a m Q X →
      Γ "full_bva_connect_clauses_fid" [i64] [] a m Q X)
    (hUp : ∀ a m Q X, fidFheapUpSpec a m Q X →
      Γ "full_fheap_up_fid" [i64, i64, i64, i32] [] a m Q X)
    (hDown : ∀ a m Q X, fidFheapDownSpec a m Q X →
      Γ "full_fheap_down_fid" [i64, i64, i64, i32, i32] [] a m Q X)
    (hTryLit : ∀ a m Q X, step7BvaTryLitSpec a m Q X →
      Γ "full_bva_try_lit" [i64, i32, i64] [.bool] a m Q X)
    (hUpd : ∀ a m Q X, step9BvaUpdLitSpec a m Q X →
      Γ "full_bva_upd_lit_fid" [i64, i64, i64, i64, i64, i64] [i32] a m Q X) :
    ∀ args m Q X, fullFactorHeapSpec args m Q X →
      Func.wp Γ FullFidelityStep13S5BVAFactor.full_factor_body args m Q X := by
  rintro ⟨h, budget, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hinv, hm, hQ⟩
  unfold Func.wp FullFidelityStep13S5BVAFactor.full_factor_body
  have hmx := c.hmaxv; have hmx_n : c.max_vars < 2 * 2 ^ 28 := by simpa [dimacsBound] using hmx
  have hscr_b := c.hscr; unfold dimacsBound at hscr_b
  have hlen := hinv.1.lengths; have hcv_le := hlen.core_ok.cur_vars_le
  c0_hfast_nogrp
  refine s13_call_steps_cap hSteps fun scb _hscb => ?_
  c0_hsplit; · c0_hfast; exact hQ 1#64 s m hinv (Nat.le_refl _) rfl rfl hm
  c0_hsplit; · c0_hfast; exact hQ 1#64 s m hinv (Nat.le_refl _) rfl rfl hm
  c0_hsplit; · c0_hfast; exact hQ 1#64 s m hinv (Nat.le_refl _) rfl rfl hm
  obtain ⟨F_cur0, hw0⟩ := hinv.1.witness
  have hdw0 : FullDenseInvW c F0 F_cur0 s :=
    ⟨hlen, hw0, hinv.2.1, hinv.2.2.1, hinv.2.2.2.1, hinv.2.2.2.2.1, hinv.2.2.2.2.2⟩
  refine wp_call_of_spec _ _ (hConnect (c.hdr, ()) m (fun r m' => wp Γ Q X _ m') X
    ⟨c, F0, F_cur0, s, R, rfl, hdw0, hm, fun s0 m0 hdw1 hcv0 hfu0 _ _ _ hm0 => ?_⟩)
  have hinv0 : FullDenseInv c F0 s0 :=
    ⟨⟨hdw1.1, F_cur0, hdw1.2.1⟩, hdw1.2.2.1, hdw1.2.2.2.1, hdw1.2.2.2.2.1,
     hdw1.2.2.2.2.2.1, hdw1.2.2.2.2.2.2⟩
  c0_hfast_nogrp
  · exact hQ 1#64 s0 m0 hinv0 (Nat.le_of_eq hcv0.symm) hfu0 rfl hm0
  let s1 : FullState := { s0 with scratch := { s0.scratch with ant_sz := budget } }
  have hinv1 : FullDenseInv c F0 s1 :=
    hinv0.of_safetySlice ⟨hdw1.1.core_ok, s13_lengths_set_ant_sz hdw1.1.scratch_ok budget⟩
      rfl ⟨rfl, rfl⟩
  let init_cv := s1.core.cur_vars; let init_fuel := s1.core.fuel
  have hinit_cv_eq : init_cv = s.core.cur_vars := hcv0
  have hinit_fuel_eq : init_fuel = s.core.fuel := hfu0
  have hmnl_64 : (BitVec.ofNat 64 c.max_vars <<< (1 : Nat)).toNat = 2 * c.max_vars := by
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]; omega
  refine fac13_zero_wp (R := R) hmx hinv1 hmnl_64 (by assumption)
    fun _wsZ _hpZ _psZ mz _hwsZ _hhpZ _hpsZ hinvZ hmz => ?_
  refine fac13_build_wp hUp hmx hinvZ rfl rfl hmz
    fun hsz _vi mh ⟨st1, hhsz_1, hinv_1, hcv_1, hfu_1, hhp1, hmh⟩ => ?_
  c0_hfast_nogrp
  refine wp_while_state (ts := [i32]) (α := FullState × BitVec 32)
    (fun p => (p.2, ()))
    (fun p => (c.max_vars - p.1.core.cur_vars) * (2 * c.max_vars + 1) + p.2.toNat)
    (fun (st, hsz) mw => init_cv ≤ st.core.cur_vars ∧ st.core.fuel = init_fuel ∧
      hsz.toNat ≤ 2 * st.core.cur_vars ∧ FullDenseInv c F0 st ∧
      (∀ i < hsz.toNat, (st.scratch.tarjan_mark[i]?.getD 0#32).toNat < 2 * st.core.cur_vars) ∧
      (FullMem c st ⋆ R) mw)
    (fun Jm hJm => by
      c0_hfast_nogrp
      exact hJm (st1, hsz) mh ⟨Nat.le_of_eq hcv_1.symm, hfu_1,
        by rw [hcv_1]; exact hhsz_1, hinv_1, fun i hi => by rw [hcv_1]; exact hhp1 i hi, hmh⟩)
    (fun Jm (st, hsz) mw ⟨hcv_st, hfu_st, hhsz_st, hinv_st, hhp_st, hmw⟩ ihm => ?_)
  c0_hfast_nogrp
  refine wp_join_group (ts := []) (fun _ mEx => mEx = mw) ?_ ?_
  · rintro _ ⟨⟩ mEx rfl; clear ihm; c0_hfast_nogrp
    exact fac13_exit_wp hcv_st hfu_st hinv_st hmw fun res s' m' hinv' hcv' hfu' hr' hm' =>
      hQ res s' m' hinv' (by rw [← hinit_cv_eq]; exact hcv') (hfu'.trans hinit_fuel_eq) hr' hm'
  · intro Jex hJex; c0_hfast_nogrp; rotate_left 1; iterate 4 exact hJex () mw rfl
    have hhsz_pos : 0 < hsz.toNat :=
      by simpa using (by assumption : BitVec.toNat 0 < hsz.toNat)
    have hhsz1 : (hsz - 1#32).toNat = hsz.toNat - 1 := fac13_bv32_sub1 hhsz_pos
    have hstl := hinv_st.1.lengths; have hst_cv_le := hstl.core_ok.cur_vars_le
    have hf0_lt : (st.scratch.tarjan_mark[0]'(by
        rw [hstl.scratch_ok.tarjan_mark_len]; omega)).toNat < 2 * st.core.cur_vars := by
      have h := hhp_st 0 hhsz_pos
      rwa [List.getElem?_eq_getElem (by rw [hstl.scratch_ok.tarjan_mark_len]; omega),
        Option.getD_some] at h
    let f0 := st.scratch.tarjan_mark[0]'(by rw [hstl.scratch_ok.tarjan_mark_len]; omega)
    have hf0_lt' : f0.toNat < 2 * st.core.cur_vars := hf0_lt
    have hf0_ps_lt : (BitVec.setWidth 64 f0).toNat < st.scratch.tarjan_reach.length := by
      rw [fid_bv64_32, hstl.scratch_ok.tarjan_reach_len]; omega
    have htm0 : 0 < st.scratch.tarjan_mark.length := by
      rw [hstl.scratch_ok.tarjan_mark_len]; omega
    c0_hfast_nogrp
    let st1a : FullState :=
      { st with scratch := { st.scratch with
        tarjan_reach := st.scratch.tarjan_reach.set (BitVec.setWidth 64 f0).toNat
          0xFFFFFFFF#32 } }
    have hinv1a : FullDenseInv c F0 st1a :=
      s13_dense_set_fheap hinv_st hstl.scratch_ok.tarjan_mark_len
        (by simp [hstl.scratch_ok.tarjan_reach_len])
    refine wp_join_group (ts := []) (fun _ mf => ∃ st2 : FullState,
        init_cv ≤ st2.core.cur_vars ∧ st2.core.fuel = init_fuel ∧
        st2.core.cur_vars = st.core.cur_vars ∧ FullDenseInv c F0 st2 ∧
        (∀ i < (hsz - 1#32).toNat,
          (st2.scratch.tarjan_mark[i]?.getD 0#32).toNat < 2 * st2.core.cur_vars) ∧
        (FullMem c st2 ⋆ R) mf) ?_ ?_
    · rintro _ ⟨⟩ mf ⟨st2, hcv2, hfu2, hcv2_eq, hinv2, hhp2, hmf⟩
      have h2l := hinv2.1.lengths; have h2_cv_le := h2l.core_ok.cur_vars_le
      have hf0_lt2 : f0.toNat < 2 * st2.core.cur_vars := hcv2_eq ▸ hf0_lt
      have hfv_lt : (BitVec.setWidth 64 (f0 >>> (1 : Nat))).toNat < st2.core.flags.length := by
        rw [fid_bv64_32, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.pow_one,
          h2l.core_ok.flags_len]; omega
      have hval_lt : (BitVec.setWidth 64 f0).toNat < st2.core.vals.length := by
        rw [fid_bv64_32, h2l.core_ok.vals_len]; omega
      have hdeg_lt : (BitVec.setWidth 64 f0).toNat < st2.core.repr.length := by
        rw [fid_bv64_32, h2l.core_ok.repr_len]; omega
      have hhsz1_lt : (hsz - 1#32).toNat < hsz.toNat := by omega
      c0_hfast_nogrp
      refine wp_join_group (ts := [i32])
        (fun (fbit, ()) mf0 => (fbit = 32#32 ∨ fbit = 64#32) ∧ (FullMem c st2 ⋆ R) mf0)
        ?_ (fun _ hJfb => by
          c0_hfast_nogrp
          · exact hJfb (64#32, ()) mf ⟨Or.inr rfl, hmf⟩
          · exact hJfb (32#32, ()) mf ⟨Or.inl rfl, hmf⟩)
      rintro _ ⟨fbit, ⟨⟩⟩ mf ⟨_, hmf⟩
      have hdec_hsz : ∀ st' : FullState, st'.core.cur_vars = st.core.cur_vars →
          (c.max_vars - st'.core.cur_vars) * (2 * c.max_vars + 1) + (hsz - 1#32).toNat <
            (c.max_vars - st.core.cur_vars) * (2 * c.max_vars + 1) + hsz.toNat :=
        fun st' h => by rw [h, hhsz1]; omega
      have hhsz1_le : (hsz - 1#32).toNat ≤ 2 * st2.core.cur_vars := by rw [hcv2_eq, hhsz1]; omega
      have h_jm_st2a : ∀ {fl' : List (BitVec 32)} {m' : Mem 64},
          (FullMem c { st2 with core := { st2.core with flags := fl' } } ⋆ R) m' →
          fl'.length = c.max_vars → Jm (hsz - 1#32, ()) m' := fun {fl' m'} hm' hlen =>
        ihm ({ st2 with core := { st2.core with flags := fl' } }, hsz - 1#32) m'
          (hdec_hsz _ hcv2_eq) ⟨hcv2, hfu2, hhsz1_le, s13_dense_set_flags hinv2 hlen, hhp2, hm'⟩
      c0_hfast_nogrp
      all_goals try
        (c0_hfast_nogrp; exact ihm (st2, hsz - 1#32) mf (hdec_hsz st2 hcv2_eq)
          ⟨hcv2, hfu2, hhsz1_le, hinv2, hhp2, hmf⟩)
      all_goals try
        (c0_hfast_nogrp; refine h_jm_st2a hm ?_; rw [List.length_set]; exact h2l.core_ok.flags_len)
      · obtain ⟨fl', hfl'_len, hm2a⟩ : ∃ fl' : List (BitVec 32), fl'.length = c.max_vars ∧
            (FullMem c { st2 with core := { st2.core with flags := fl' } } ⋆ R) m :=
          ⟨_, by rw [List.length_set]; exact h2l.core_ok.flags_len, hm⟩
        let st2a : FullState := { st2 with core := { st2.core with flags := fl' } }
        have hinv2a : FullDenseInv c F0 st2a := s13_dense_set_flags hinv2 hfl'_len
        refine wp_join_group (ts := [i32]) Jm
          (fun _ p_j m_j h_j => by c0_hfast_nogrp; exact h_j) (fun _ hJs => ?_)
        refine wp_call_of_spec _ _ (hTryLit _ _ _ _ ?_)
        refine ⟨c, F0, st2a, R, rfl, hinv2a, hf0_lt2, hm2a, ?_⟩
        intro ok3 st3 m3 hinv3 hcv3_le hcv3_lt hcom3 hfu3 htm3 _ hm3
        c0_hsplit
        · have hok_t : ok3 = true := by assumption
          have hcv3_gt : st2.core.cur_vars < st3.core.cur_vars := hcv3_lt hok_t
          obtain ⟨bkNat, hbk⟩ := hcom3 hok_t
          have h3l := hinv3.1.lengths; have h3_cv_le := h3l.core_ok.cur_vars_le
          have h3_cv32 : 2 * c.max_vars < 2 ^ 30 := by omega
          c0_hfast_nogrp
          refine s13_call_steps_cap hSteps fun sc_b hsc_b => ?_
          c0_hfast_nogrp
          have hbk_sc : bkNat < fidStepsCap c.scratch_cap := hbk.1
          have hbk_eq : (BitVec.setWidth 32 st3.scratch.res_sz).toNat = bkNat := by
            rw [hbk.2.1, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
              Nat.mod_eq_of_lt (by have := fidStepsCap_le_256 c.scratch_cap; omega),
              Nat.mod_eq_of_lt (by have := fidStepsCap_le_256 c.scratch_cap; omega)]
          have hq0_bnd : bkNat + 1 < 2 ^ 32 := by have := fidStepsCap_le_256 c.scratch_cap; omega
          have hcnl_eq : (BitVec.ofNat 64 st3.core.cur_vars <<< (1 : Nat)).toNat =
              2 * st3.core.cur_vars := by
            rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
              Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]; omega
          refine wp_loop_inv (ts := [i64, i32])
            (fun (nt, qs_idx, ()) mA => qs_idx.toNat ≤ bkNat + 1 ∧ ∃ tmk tlits,
              S13TouchInv c st3 R nt tmk tlits mA)
            (fun (_, qs_idx, ()) _ => qs_idx.toNat)
            (fun Ja hJa => by
              c0_hfast_nogrp
              exact hJa (0#64, BitVec.setWidth 32 st3.scratch.res_sz + 1#32, ()) m3
                ⟨by rw [fac13_bv32_add1 (by rw [hbk_eq]; omega), hbk_eq]; omega,
                 st3.core.lit_mark, st3.scratch.work_stk2, h3l.core_ok.lit_mark_len,
                 h3l.scratch_ok.work_stk2_len, Nat.zero_le _,
                 fun _ hi => absurd hi (Nat.not_lt_zero _),
                 fun l hl hnz => absurd (hinv3.2.1.2 l hl) hnz, hm3⟩)
            (fun Ja (nt, qs_idx, ()) mA
                ⟨hqs_le, tmk, tlits, htmk_l, htlits_l, hnt_le, htlits_b, hcov, hmA⟩ iha => ?_)
          · c0_hfast_nogrp
            · have hqs_pos : 0 < qs_idx.toNat := by
                first
                | exact Nat.pos_of_ne_zero
                    (fun h => (by assumption : qs_idx ≠ 0#32) (BitVec.eq_of_toNat_eq h))
                | simpa using BitVec.lt_def.mp (by assumption : 0#32 < qs_idx)
              have hqs1 : (qs_idx - 1#32).toNat = qs_idx.toNat - 1 := fac13_bv32_sub1 hqs_pos
              have hrow := hbk.2.2 (qs_idx - 1#32).toNat (by omega)
              have hsc_lt : (qs_idx - 1#32).toNat < st3.scratch.scratch_buf.length := by
                rw [h3l.scratch_ok.scratch_buf_len]
                have := fidStepsCap_mul4_le c.scratch_cap; have := hbk.1; omega
              have hfac_lt : (st3.scratch.scratch_buf[(qs_idx - 1#32).toNat]'hsc_lt).toNat <
                  2 * st3.core.cur_vars := by
                have h := hrow.1; rwa [List.getElem?_eq_getElem hsc_lt, Option.getD_some] at h
              have hfneg_lt : ((st3.scratch.scratch_buf[(qs_idx - 1#32).toNat]'hsc_lt) ^^^
                  1#32).toNat < 2 * st3.core.cur_vars := fac13_bv32_xor1_lt hfac_lt (by omega)
              c0_hfast_nogrp
              refine wp_join_group (ts := [i64]) (fun (nt1, ()) mP1 => ∃ tmk1 tlits1,
                  S13TouchInv c st3 R nt1 tmk1 tlits1 mP1) ?_ ?_
              · rintro _ ⟨nt1, ⟨⟩⟩ mP1
                  ⟨tmk1, tlits1, htmk1_l, htlits1_l, hnt1_le, htlits1_b, hcov1, hmP1⟩
                c0_hfast_nogrp
                refine wp_join_group (ts := [i64]) (fun (nt2, ()) mP2 => ∃ tmk2 tlits2,
                    S13TouchInv c st3 R nt2 tmk2 tlits2 mP2) ?_ ?_
                · rintro _ ⟨nt2, ⟨⟩⟩ mP2
                    ⟨tmk2, tlits2, htmk2_l, htlits2_l, hnt2_le, htlits2_b, hcov2, hmP2⟩
                  have hro_idx : (sc_b + (qs_idx - 1#32)).toNat =
                      sc_b.toNat + (qs_idx - 1#32).toNat := by
                    rw [BitVec.toNat_add, hsc_b, Nat.mod_eq_of_lt (by
                      have := fidStepsCap_le_256 c.scratch_cap; omega)]
                  have hro_sc : (BitVec.setWidth 64 (sc_b + (qs_idx - 1#32))).toNat <
                      st3.scratch.scratch_buf.length := by
                    rw [fid_bv64_32, hro_idx, h3l.scratch_ok.scratch_buf_len]
                    have := fidStepsCap_mul4_le c.scratch_cap; have := hbk.1; omega
                  have hqn_idx : (2#32 * sc_b + (qs_idx - 1#32)).toNat =
                      2 * sc_b.toNat + (qs_idx - 1#32).toNat := by
                    rw [BitVec.toNat_add, BitVec.toNat_mul, hsc_b,
                      show (2#32 : BitVec 32).toNat = 2 from rfl,
                      Nat.mod_eq_of_lt (by have := fidStepsCap_le_256 c.scratch_cap; omega),
                      Nat.mod_eq_of_lt (by have := fidStepsCap_le_256 c.scratch_cap; omega)]
                  have hqn_sc : (BitVec.setWidth 64 (2#32 * sc_b + (qs_idx - 1#32))).toNat <
                      st3.scratch.scratch_buf.length := by
                    rw [fid_bv64_32, hqn_idx, h3l.scratch_ok.scratch_buf_len]
                    have := fidStepsCap_mul4_le c.scratch_cap; have := hbk.1; omega
                  let ro_bv := st3.scratch.scratch_buf[(BitVec.setWidth 64
                    (sc_b + (qs_idx - 1#32))).toNat]'hro_sc
                  let qn_bv := st3.scratch.scratch_buf[(BitVec.setWidth 64
                    (2#32 * sc_b + (qs_idx - 1#32))).toNat]'hqn_sc
                  have hroqn_bnd : ro_bv.toNat + qn_bv.toNat ≤ c.scratch_cap := by
                    have h := hrow.2.1; dsimp only [ro_bv, qn_bv]
                    simp only [fid_bv64_32, hro_idx, hqn_idx, hsc_b]
                    rw [List.getElem?_eq_getElem (by
                          rw [h3l.scratch_ok.scratch_buf_len]
                          have := fidStepsCap_mul4_le c.scratch_cap; omega),
                        List.getElem?_eq_getElem (by
                          rw [h3l.scratch_ok.scratch_buf_len]
                          have := fidStepsCap_mul4_le c.scratch_cap; omega),
                        Option.getD_some, Option.getD_some] at h
                    exact h
                  c0_hfast_nogrp
                  refine fac13_qi_scan_wp hmx hscr_b hinv3 hcnl_eq hroqn_bnd ?_
                    ⟨htmk2_l, htlits2_l, hnt2_le, htlits2_b, hcov2, hmP2⟩
                    (fun ntQ mQ ⟨tmkQ, tlitsQ, hT⟩ =>
                      iha (ntQ, qs_idx - 1#32, ()) mQ (by dsimp only; rw [hqs1]; omega)
                        ⟨by rw [hqs1]; omega, tmkQ, tlitsQ, hT⟩)
                  · intro qi_n hqi_n
                    change qi_n < st3.scratch.scratch_buf[
                      (2#32 * sc_b + (qs_idx - 1#32)).toNat].toNat at hqi_n
                    have hro_sc' : fidStepsCap c.scratch_cap + (qs_idx - 1#32).toNat <
                        st3.scratch.scratch_buf.length := by
                      rw [← hsc_b, ← hro_idx, ← fid_bv64_32]; exact hro_sc
                    have hqn_sc' : 2 * fidStepsCap c.scratch_cap + (qs_idx - 1#32).toNat <
                        st3.scratch.scratch_buf.length := by
                      rw [← hsc_b, ← hqn_idx, ← fid_bv64_32]; exact hqn_sc
                    have heq_ro : ro_bv.toNat = (st3.scratch.scratch_buf[
                        fidStepsCap c.scratch_cap + (qs_idx - 1#32).toNat]?.getD 0#32).toNat := by
                      simp only [ro_bv, fid_bv64_32, hro_idx, hsc_b]
                      rw [List.getElem?_eq_getElem hro_sc', Option.getD_some]
                    have hqi_row : qi_n < (st3.scratch.scratch_buf[
                        2 * fidStepsCap c.scratch_cap + (qs_idx - 1#32).toNat]?.getD
                        0#32).toNat := by
                      rw [List.getElem?_eq_getElem hqn_sc', Option.getD_some]
                      simpa only [hqn_idx, hsc_b] using hqi_n
                    have h := hrow.2.2 qi_n hqi_row
                    first | rwa [← heq_ro] at h | (
                      have heq_ro' : (st3.scratch.scratch_buf[(sc_b + (qs_idx - 1#32)).toNat]'(by
                            rw [hro_idx, hsc_b]; exact hro_sc')).toNat = (st3.scratch.scratch_buf[
                            fidStepsCap c.scratch_cap + (qs_idx - 1#32).toNat]?.getD
                            0#32).toNat := by
                          simp only [List.getElem?_eq_getElem hro_sc', Option.getD_some,
                            hro_idx, hsc_b]
                      change Step7RowRefOk st3 (st3.scratch.scratch_buf[
                        (st3.scratch.scratch_buf[(sc_b + (qs_idx - 1#32)).toNat]'(by
                          rw [hro_idx, hsc_b]; exact hro_sc')).toNat + qi_n]?.getD 0#32)
                      rwa [← heq_ro'] at h)
                · intro Jp2 hJp2; c0_hfast_nogrp
                  · have hlm_fn : (BitVec.setWidth 64
                        ((st3.scratch.scratch_buf[(qs_idx - 1#32).toNat]'hsc_lt) ^^^
                          1#32)).toNat < tmk1.length := by
                      rw [fid_bv64_32, htmk1_l]
                      exact Nat.lt_of_lt_of_le hfneg_lt (Nat.mul_le_mul_left 2 h3_cv_le)
                    c0_hfast_nogrp
                    · have hnt1_lt : nt1.toNat < 2 * st3.core.cur_vars := by
                        have h1 : nt1.toNat <
                            (BitVec.ofNat 64 st3.core.cur_vars <<< (1 : Nat)).toNat := by
                          assumption
                        rw [hcnl_eq] at h1; exact h1
                      have hnt1_1 : (nt1 + 1#64).toNat = nt1.toNat + 1 :=
                        fac13_bv64_add1 (by omega)
                      have hws_nt1 : nt1.toNat < tlits1.length := by
                        rw [htlits1_l]
                        exact Nat.lt_of_lt_of_le hnt1_lt (Nat.mul_le_mul_left 2 h3_cv_le)
                      c0_hfast_nogrp
                      have hps1 := s13_push_touched_step h3_cv_le htmk1_l htlits1_l
                        hfneg_lt hnt1_lt hnt1_1 htlits1_b hcov1
                      exact hJp2 (nt1 + 1#64, ()) _ ⟨_, _,
                        hps1.1, hps1.2.1, hps1.2.2.1, hps1.2.2.2.1, hps1.2.2.2.2, by assumption⟩
                    all_goals exact hJp2 (nt1, ()) mP1 ⟨tmk1, tlits1, htmk1_l, htlits1_l, hnt1_le,
                      htlits1_b, hcov1, hmP1⟩
                  · exact hJp2 (nt1, ()) mP1 ⟨tmk1, tlits1, htmk1_l, htlits1_l, hnt1_le,
                      htlits1_b, hcov1, hmP1⟩
              · intro Jp1 hJp1; c0_hfast_nogrp
                · have hlm_f : (BitVec.setWidth 64
                      (st3.scratch.scratch_buf[(qs_idx - 1#32).toNat]'hsc_lt)).toNat <
                      tmk.length := by
                    rw [fid_bv64_32, htmk_l]
                    exact Nat.lt_of_lt_of_le hfac_lt (Nat.mul_le_mul_left 2 h3_cv_le)
                  c0_hfast_nogrp
                  · have hnt_lt : nt.toNat < 2 * st3.core.cur_vars := by
                      have h1 : nt.toNat <
                          (BitVec.ofNat 64 st3.core.cur_vars <<< (1 : Nat)).toNat := by assumption
                      rw [hcnl_eq] at h1; exact h1
                    have hnt1 : (nt + 1#64).toNat = nt.toNat + 1 := fac13_bv64_add1 (by omega)
                    have hws_nt : nt.toNat < tlits.length := by
                      rw [htlits_l]
                      exact Nat.lt_of_lt_of_le hnt_lt (Nat.mul_le_mul_left 2 h3_cv_le)
                    c0_hfast_nogrp
                    have hpsF := s13_push_touched_step h3_cv_le htmk_l htlits_l
                      hfac_lt hnt_lt hnt1 htlits_b hcov
                    exact hJp1 (nt + 1#64, ()) _ ⟨_, _,
                      hpsF.1, hpsF.2.1, hpsF.2.2.1, hpsF.2.2.2.1, hpsF.2.2.2.2, by assumption⟩
                  all_goals exact (hJp1 (nt, ()) mA
                    ⟨tmk, tlits, htmk_l, htlits_l, hnt_le, htlits_b, hcov, hmA⟩)
                · exact hJp1 (nt, ()) mA ⟨tmk, tlits, htmk_l, htlits_l, hnt_le, htlits_b,
                    hcov, hmA⟩
            · clear iha; c0_hfast_nogrp
              have hcv3_ge2 : st2.core.cur_vars ≤ st3.core.cur_vars := hcv3_le
              have hhsz'_le : (hsz - 1#32).toNat ≤ 2 * st3.core.cur_vars := by omega
              have hhp3 : ∀ i < (hsz - 1#32).toNat,
                  (st3.scratch.tarjan_mark[i]?.getD 0#32).toNat < 2 * st3.core.cur_vars :=
                fun i hi => by
                  rw [htm3]; dsimp only [st2a]; have := hhp2 i hi; omega
              refine fac13_clear_upd_wp hUpd hinv3 htmk_l htlits_l hnt_le htlits_b hcov
                hhsz'_le hhp3 hmA fun hsz_u mU ⟨st_end, hinv_end, hcv_end, hfu_end,
                  hhsz_end, hhp_end, hm_end⟩ => ?_
              exact hJs (hsz_u, ()) mU (ihm (st_end, hsz_u) mU
                (fac13_lex_dec_cv (by dsimp only; rw [hcv_end, ← hcv2_eq]; exact hcv3_gt)
                  hinv_end.1.lengths.core_ok.cur_vars_le (by dsimp only; omega))
                ⟨by omega, hfu_end.trans (hfu3.trans hfu2), hhsz_end, hinv_end, hhp_end, hm_end⟩)
        · c0_hfast_nogrp
          refine hJs (hsz - 1#32, ()) m3 (ihm (st3, hsz - 1#32) m3 ?_ ?_)
          · rcases Nat.lt_or_eq_of_le (hcv3_le : st2.core.cur_vars ≤ st3.core.cur_vars) with
              hcv3_gt | hcv3_eq
            · exact fac13_lex_dec_cv (by dsimp only; rw [← hcv2_eq]; exact hcv3_gt)
                hinv3.1.lengths.core_ok.cur_vars_le (by dsimp only; omega)
            · exact hdec_hsz st3 (by rw [← hcv3_eq, hcv2_eq])
          · have hcv3_le' : st2.core.cur_vars ≤ st3.core.cur_vars := hcv3_le
            refine ⟨Nat.le_trans hcv2 hcv3_le', hfu3.trans hfu2, by omega, hinv3, fun i hi => by
              rw [htm3]; dsimp only [st2a]; have := hhp2 i hi; omega, hm3⟩
    · intro Jf hJf
      exact fac13_fheap_pop_wp hDown hhsz_pos hhsz1 hhsz_st hcv_st hfu_st hinv1a
        rfl rfl hhp_st (by assumption) hJf

end LeanQbe.T.Examples.Kissat.FullFidelityStep13S5

end
