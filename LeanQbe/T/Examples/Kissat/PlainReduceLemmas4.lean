module

public import LeanQbe.T.Examples.Kissat.PlainReduceLemmas3

/-!
# Kissat `D-Plain` Compaction GC (`plain_sweep`) (`Wave 2b`)

Provides verified parametric `(Γ : Env)` `Func.wp` contract for:
- `plain_sweep` (`plainSweepSpec`)
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Plain

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.C0Step
open Kraken.Bedrock2.Test


section
open scoped PlainReduceTactics

namespace PlainReduceHelpers


@[expose] def sweepP1Expr {Val : Ty → Type} {Cont : List Ty → Type}
    (cHdr mv2 pVals pLvl pWvec pWstk : Val i64)
    (rest : Expr Val Cont [i64]) : Expr Val Cont [i64] :=
  .group (sig := [[i64]]) (fun Js => .cons (fun p11 =>
    .let_ (Op.mk (.cmp .ult i64 .bool) (.var p11.fst, .var mv2, ())) fun p12 => .jnz (.var p12.fst)
      (.let_ (Op.mk (.sext 32 64) (.imm 1, ())) fun p13 =>
  .let_ (Op.mk (.shl i64) (.var p11.fst, .var p13.fst, ())) fun p14 =>
  .let_ (Op.mk (.mul i64) (.var p14.fst, .imm 4, ())) fun _q75 =>
  .let_ (Op.mk (.add i64) (.var pWvec, .var _q75.fst, ())) fun _q74 =>
  .load i32 (.var _q74.fst) fun ld =>
  .let_ (Op.mk (.zext 32 64) (.var ld, ())) fun p17 =>
  .let_ (Op.mk (.sext 32 64) (.imm 1, ())) fun p18 =>
  .let_ (Op.mk (.shl i64) (.var p11.fst, .var p18.fst, ())) fun p19 =>
  .let_ (Op.mk (.add i64) (.var p19.fst, .imm 1, ())) fun _q71 =>
  .let_ (Op.mk (.mul i64) (.var _q71.fst, .imm 4, ())) fun _q73 =>
  .let_ (Op.mk (.add i64) (.var pWvec, .var _q73.fst, ())) fun _q72 =>
  .load i32 (.var _q72.fst) fun ld =>
  .let_ (Op.mk (.zext 32 64) (.var ld, ())) fun p23 =>
  .group (sig := [[.bool]]) (fun _Js1 => .cons (fun p24 =>
    .let_ (Op.mk (.cmp .eq i64 .bool) (.var p23.fst, .imm 0, ())) fun p25 => .jnz (.var p25.fst)
      (.let_ (Op.mk (.add i64) (.var p11.fst, .imm 1, ())) fun _p58 =>
      .jump Js.fst (.var _p58.fst, ()))
      (.group (sig := [[]]) (fun _Js2 => .cons (fun _ =>
         .let_ (Op.mk (.add i64) (.var p11.fst, .imm 1, ())) fun _p59 =>
      .jump Js.fst (.var _p59.fst, ())) .nil)
       fun Js => .jnz (.var p24.fst)
         (.let_ (Op.mk (.add i64) (.var p17.fst, .var p23.fst, ())) fun p26 =>
      .group (sig := [[i64]]) (fun Js2 => .cons (fun p27 =>
      .let_ (Op.mk (.cmp .ult i64 .bool) (.var p27.fst, .var p26.fst, ()))
        fun p28 => .jnz (.var p28.fst)
        (.let_ (Op.mk (.mul i64) (.var p27.fst, .imm 4, ())) fun _q20 =>
        .let_ (Op.mk (.add i64) (.var pWstk, .var _q20.fst, ())) fun _q19 =>
        .load i32 (.var _q19.fst) fun ld =>
        .group (sig := [[i64]]) (fun _ => .cons (fun p => .jump Js2.fst
          (.var p.fst, ())) .nil) fun Js =>
        .let_ (Op.mk (.and i32) (.var ld, .imm 2147483648, ())) fun p31 =>
        .let_ (Op.mk (.cmp .ne i32 .bool) (.var p31.fst, .imm 0, ())) fun p32 => .jnz (.var p32.fst)
          (.let_ (Op.mk (.and i32) (.var ld, .imm 2147483647, ())) fun p33 =>
           .group (sig := [[]]) (fun _ => .cons (fun _ =>
             .let_ (Op.mk (.add i64) (.var p27.fst, .imm 1, ())) fun _p10 =>
            .jump Js.fst (.var _p10.fst, ())) .nil) fun Js =>
           .let_ (Op.mk (.zext 32 64) (.var p33.fst, ())) fun p34 =>
           .let_ (Op.mk (.cmp .ult i64 .bool) (.var p11.fst, .var p34.fst, ())) fun p35 =>
           .jnz (.var p35.fst)
             (.let_ (Op.mk (.add i64) (.var cHdr, .imm 504, ())) fun _d2 =>
              .load i64 (.var _d2.fst) fun _dl3 =>
              .let_ (Op.mk (.cmp .ugt i64 .bool) (.var _dl3, .imm 0, ())) fun _d4 =>
              .jnz (.var _d4.fst)
                (.let_ (Op.mk (.add i64) (.var cHdr, .imm 504, ())) fun _d5 =>
                .load i64 (.var _d5.fst) fun _dl6 =>
                .let_ (Op.mk (.sub i64) (.var _dl6, .imm 1, ())) fun _d7 =>
                .let_ (Op.mk (.add i64) (.var cHdr, .imm 504, ())) fun _q8 =>
                .store (t := i64) (.var _d7.fst) (.var _q8.fst)
                  (.jump Js.fst ()))
                (.jump Js.fst ()))
             (.jump Js.fst ()))
          (.let_ (Op.mk (.add i64) (.var p27.fst, .imm 2, ())) fun _p11 =>
            .jump Js.fst (.var _p11.fst, ())))
        (.group (sig := [[i64]]) (fun Js3 => .cons (fun p29 =>
            .let_ (Op.mk (.cmp .ult i64 .bool) (.var p29.fst, .var p26.fst, ()))
              fun p30 => .jnz (.var p30.fst)
              (.let_ (Op.mk (.mul i64) (.var p29.fst, .imm 4, ())) fun _q15 =>
              .let_ (Op.mk (.add i64) (.var pWstk, .var _q15.fst, ())) fun _q14 =>
              .store (t := i32) (.imm 4294967295) (.var _q14.fst)
                (.let_ (Op.mk (.add i64) (.var p29.fst, .imm 1, ())) fun _f13 =>
              .jump Js3.fst (.var _f13.fst, ())))
              (.let_ (Op.mk (.sext 32 64) (.imm 1, ())) fun p31 =>
              .let_ (Op.mk (.shl i64) (.var p11.fst, .var p31.fst, ())) fun p32 =>
              .let_ (Op.mk (.add i64) (.var p32.fst, .imm 1, ())) fun _f16 =>
              .let_ (Op.mk (.mul i64) (.var _f16.fst, .imm 4, ())) fun _q18 =>
              .let_ (Op.mk (.add i64) (.var pWvec, .var _q18.fst, ())) fun p35 =>
              .store (t := i32) (.imm 0) (.var p35.fst) (.let_ (Op.mk (.add i64)
                (.var cHdr, .imm 464, ())) fun _f17 =>
              .load i64 (.var _f17.fst) fun ld =>
              .let_ (Op.mk (.add i64) (.var ld, .var p23.fst, ())) fun p37 =>
              .let_ (Op.mk (.add i64) (.var cHdr, .imm 464, ())) fun _q12 =>
              .store (t := i64) (.var p37.fst) (.var _q12.fst)
                (.jump Js.fst ())))) .nil)
            (fun Js => .jump Js.fst (.var p17.fst, ())))) .nil)
      fun Js => .jump Js.fst (.var p17.fst, ()))
         (.let_ (Op.mk (.add i64) (.var p17.fst, .var p23.fst, ())) fun p26 =>
      .group (sig := [[i64, i64]]) (fun Js2 => .cons (fun p27 =>
      .let_ (Op.mk (.cmp .ult i64 .bool) (.var p27.fst, .var p26.fst, ()))
        fun p28 => .jnz (.var p28.fst)
        (.let_ (Op.mk (.mul i64) (.var p27.fst, .imm 4, ())) fun _q57 =>
        .let_ (Op.mk (.add i64) (.var pWstk, .var _q57.fst, ())) fun _q56 =>
        .load i32 (.var _q56.fst) fun ld =>
        .group (sig := [[i64, i64]]) (fun _ => .cons (fun p =>
          .jump Js2.fst (.var p.fst, .var p.snd.fst, ())) .nil) fun Js =>
        .let_ (Op.mk (.and i32) (.var ld, .imm 2147483648, ())) fun p31 =>
        .let_ (Op.mk (.cmp .ne i32 .bool) (.var p31.fst, .imm 0, ())) fun p32 => .jnz (.var p32.fst)
          (.let_ (Op.mk (.and i32) (.var ld, .imm 2147483647, ())) fun p33 =>
           .group (sig := [[.bool]]) (fun _Js3 => .cons (fun p34 =>
             .group (sig := [[i64]]) (fun _Js4 => .cons (fun _p22 =>
               .let_ (Op.mk (.add i64) (.var p27.fst, .imm 1, ())) fun p35 =>
            .jump Js.fst (.var p35.fst, .var _p22.fst, ())) .nil) fun Js =>
             .jnz (.var p34.fst)
               (.group (sig := [[]]) (fun _Js4 => .cons (fun _ =>
                  .jump Js.fst (.var p27.snd.fst, ())) .nil) fun Js =>
                .let_ (Op.mk (.zext 32 64) (.var p33.fst, ())) fun p35 =>
                .let_ (Op.mk (.cmp .ult i64 .bool) (.var p11.fst, .var p35.fst, ())) fun p36 =>
                .jnz (.var p36.fst)
                  (.let_ (Op.mk (.add i64) (.var cHdr, .imm 504, ())) fun _d23 =>
                .load i64 (.var _d23.fst) fun _dl24 =>
                .let_ (Op.mk (.cmp .ugt i64 .bool) (.var _dl24, .imm 0, ())) fun _d25 =>
                .jnz (.var _d25.fst)
                  (.let_ (Op.mk (.add i64) (.var cHdr, .imm 504, ())) fun _d26 =>
                  .load i64 (.var _d26.fst) fun _dl27 =>
                  .let_ (Op.mk (.sub i64) (.var _dl27, .imm 1, ())) fun _d28 =>
                  .let_ (Op.mk (.add i64) (.var cHdr, .imm 504, ())) fun _q29 =>
                  .store (t := i64) (.var _d28.fst) (.var _q29.fst)
                    (.jump Js.fst ()))
                  (.jump Js.fst ()))
                  (.jump Js.fst ()))
               (.let_ (Op.mk (.mul i64) (.var p27.snd.fst, .imm 4, ())) fun _q32 =>
              .let_ (Op.mk (.add i64) (.var pWstk, .var _q32.fst, ())) fun _q31 =>
              .store (t := i32) (.var ld) (.var _q31.fst)
                (.let_ (Op.mk (.add i64) (.var p27.snd.fst, .imm 1, ())) fun _p30 =>
              .jump Js.fst (.var _p30.fst, ())))) .nil)
             fun Js => .let_ (Op.mk (.zext 32 64) (.var p33.fst, ())) fun _c33 =>
            .let_ (Op.mk (.cmp .ult i64 .bool) (.var _c33.fst, .var mv2, ())) fun _c34 =>
            .jnz (.var _c34.fst)
              (.let_ (Op.mk (.lshr i32) (.var p33.fst, .imm 1, ())) fun _c36 =>
              .let_ (Op.mk (.zext 32 64) (.var _c36.fst, ())) fun _c37 =>
              .let_ (Op.mk (.mul i64) (.var _c37.fst, .imm 4, ())) fun _q47 =>
              .let_ (Op.mk (.add i64) (.var pLvl, .var _q47.fst, ())) fun _q46 =>
              .load i32 (.var _q46.fst) fun _c38 =>
              .let_ (Op.mk (.cmp .eq i32 .bool) (.var _c38, .imm 0, ())) fun _c39 =>
              .jnz (.var _c39.fst)
                (.let_ (Op.mk (.zext 32 64) (.var p33.fst, ())) fun _c40 =>
                .let_ (Op.mk (.add i64) (.var pVals, .var _c40.fst, ())) fun _c41 =>
                .load i8 (.var _c41.fst) fun _c42 =>
                .let_ (Op.mk (.trunc 32 8) (.imm 0, ())) fun _c43 =>
                .let_ (Op.mk (.sext 8 32) (.var _c42, ())) fun p34 =>
                .let_ (Op.mk (.sext 8 32) (.var _c43.fst, ())) fun _c44 =>
                .let_ (Op.mk (.cmp .ne i32 .bool) (.var p34.fst, .var _c44.fst, ())) fun _c45 =>
                .jnz (.var _c45.fst) (.jump Js.fst (.imm true, ())) (.jump Js.fst (.imm false, ())))
                (.jump Js.fst (.imm false, ())))
              (.jump Js.fst (.imm false, ())))
          (.let_ (Op.mk (.add i64) (.var p27.fst, .imm 2, ())) fun _p48 =>
          .jump Js.fst (.var _p48.fst, .var p27.snd.fst, ())))
        (.group (sig := [[i64]]) (fun Js3 => .cons (fun p29 =>
            .let_ (Op.mk (.cmp .ult i64 .bool) (.var p29.fst, .var p26.fst, ()))
              fun p30 => .jnz (.var p30.fst)
              (.let_ (Op.mk (.mul i64) (.var p29.fst, .imm 4, ())) fun _q52 =>
              .let_ (Op.mk (.add i64) (.var pWstk, .var _q52.fst, ())) fun _q51 =>
              .store (t := i32) (.imm 4294967295) (.var _q51.fst)
                (.let_ (Op.mk (.add i64) (.var p29.fst, .imm 1, ())) fun _f50 =>
              .jump Js3.fst (.var _f50.fst, ())))
              (.let_ (Op.mk (.sext 32 64) (.imm 1, ())) fun p31 =>
              .let_ (Op.mk (.shl i64) (.var p11.fst, .var p31.fst, ())) fun p32 =>
              .let_ (Op.mk (.add i64) (.var p32.fst, .imm 1, ())) fun _f53 =>
              .let_ (Op.mk (.mul i64) (.var _f53.fst, .imm 4, ())) fun _q55 =>
              .let_ (Op.mk (.add i64) (.var pWvec, .var _q55.fst, ())) fun p35 =>
              .let_ (Op.mk (.sub i64) (.var p27.snd.fst, .var p17.fst, ())) fun p36 =>
              .let_ (Op.mk (.trunc 64 32) (.var p36.fst, ())) fun p37 =>
              .store (t := i32) (.var p37.fst) (.var p35.fst) (.let_ (Op.mk (.add i64)
                (.var cHdr, .imm 464, ())) fun _f54 =>
              .load i64 (.var _f54.fst) fun ld =>
              .let_ (Op.mk (.sub i64) (.var p26.fst, .var p27.snd.fst, ())) fun p39 =>
.let_ (Op.mk (.add i64) (.var ld, .var p39.fst, ())) fun p40 =>
              .let_ (Op.mk (.add i64) (.var cHdr, .imm 464, ())) fun _q49 =>
              .store (t := i64) (.var p40.fst) (.var _q49.fst)
                (.jump Js.fst ())))) .nil)
            (fun Js => .jump Js.fst (.var p27.snd.fst, ())))) .nil)
      fun Js => .jump Js.fst (.var p17.fst, .var p17.fst, ())))) .nil)
    fun Js => .let_ (Op.mk (.sext 32 64) (.imm 1, ())) fun _a60 =>
    .let_ (Op.mk (.lshr i64) (.var p11.fst, .var _a60.fst, ())) fun _a61 =>
    .let_ (Op.mk (.mul i64) (.var _a61.fst, .imm 4, ())) fun _q70 =>
    .let_ (Op.mk (.add i64) (.var pLvl, .var _q70.fst, ())) fun _q69 =>
    .load i32 (.var _q69.fst) fun _a62 =>
    .let_ (Op.mk (.cmp .eq i32 .bool) (.var _a62, .imm 0, ())) fun _a63 =>
    .jnz (.var _a63.fst)
      (.let_ (Op.mk (.add i64) (.var pVals, .var p11.fst, ())) fun _a64 =>
      .load i8 (.var _a64.fst) fun _a65 =>
      .let_ (Op.mk (.trunc 32 8) (.imm 0, ())) fun _a66 =>
      .let_ (Op.mk (.sext 8 32) (.var _a65, ())) fun p34 =>
      .let_ (Op.mk (.sext 8 32) (.var _a66.fst, ())) fun _a67 =>
      .let_ (Op.mk (.cmp .ne i32 .bool) (.var p34.fst, .var _a67.fst, ())) fun _a68 =>
      .jnz (.var _a68.fst) (.jump Js.fst (.imm true, ())) (.jump Js.fst (.imm false, ())))
      (.jump Js.fst (.imm false, ())))
      rest) .nil)
    (fun Js => .jump Js.fst (.imm 0, ()))

@[expose] def sweepP3Expr {Val : Ty → Type} {Cont : List Ty → Type}
    (cHdr pVals pLvl pArena : Val i64) (b0 : Val .bool)
    (p15 : Tup Val [i64, i64, i64, i64, i64, .bool, .bool]) : Expr Val Cont [i64] :=
  .let_ (Op.mk (.add i64) (.var cHdr, .imm 48, ())) fun _h122 =>
  .store (t := i64) (.var p15.snd.fst) (.var _h122.fst) (
    .let_ (Op.mk (.add i64) (.var cHdr, .imm 472, ())) fun _h121 =>
    .store (t := i64) (.imm 0) (.var _h121.fst) (
      .let_ (Op.mk (.add i64) (.var cHdr, .imm 480, ())) fun _h120 =>
      .store (t := i64) (.var p15.snd.snd.fst) (.var _h120.fst) (
        .let_ (Op.mk (.add i64) (.var cHdr, .imm 488, ())) fun _h119 =>
        .store (t := i64) (.var p15.snd.snd.snd.fst) (.var _h119.fst) (
          .let_ (Op.mk (.add i64) (.var cHdr, .imm 496, ())) fun _h118 =>
          .store (t := i64) (.var p15.snd.snd.snd.snd.fst) (.var _h118.fst) (
            .jnz (.var p15.snd.snd.snd.snd.snd.fst) (.ret (.imm 2, ())) (
            .let_ (Op.mk (.add i64) (.var cHdr, .imm 760, ())) fun _h117 =>
              .load i64 (.var _h117.fst) fun ld =>
              .let_ (Op.mk (.cmp .ne i64 .bool) (.var ld, .imm 0, ())) fun p22 =>
              .jnz (.var p22.fst) (.ret (.imm 3, ())) (
              .group (sig := [[i64]]) (fun Js => .cons (fun p23 =>
                  .let_ (Op.mk (.cmp .ult i64 .bool) (.var p23.fst, .var p15.snd.fst, ()))
                    fun p24 => .jnz (.var p24.fst)
                    (.let_ (Op.mk (.add i64) (.var p23.fst, .imm 2, ())) fun _q114 =>
                    .let_ (Op.mk (.mul i64) (.var _q114.fst, .imm 4, ())) fun _q116 =>
                    .let_ (Op.mk (.add i64) (.var pArena, .var _q116.fst, ())) fun _q115 =>
                    .load i32 (.var _q115.fst) fun ld =>
                    .group (sig := [[]]) (fun _Js1 => .cons (fun _ =>
                      .let_ (Op.mk (.add i64) (.var p23.fst, .imm 1, ())) fun _q111 =>
                      .let_ (Op.mk (.mul i64) (.var _q111.fst, .imm 4, ())) fun _q113 =>
                      .let_ (Op.mk (.add i64) (.var pArena, .var _q113.fst, ())) fun _q112 =>
                      .store (t := i32) (.imm 2) (.var _q112.fst)
                        (.let_ (Op.mk (.add i64) (.var p23.fst, .imm 3, ())) fun _q108 =>
                      .let_ (Op.mk (.mul i64) (.var _q108.fst, .imm 4, ())) fun _q110 =>
                      .let_ (Op.mk (.add i64) (.var pArena, .var _q110.fst, ())) fun _q109 =>
                      .load i32 (.var _q109.fst) fun ld9 =>
                      .let_ (Op.mk (.add i64) (.var p23.fst, .imm 4, ())) fun _q105 =>
                      .let_ (Op.mk (.mul i64) (.var _q105.fst, .imm 4, ())) fun _q107 =>
                      .let_ (Op.mk (.add i64) (.var pArena, .var _q107.fst, ())) fun _q106 =>
                      .load i32 (.var _q106.fst) fun ld10 =>
                      .group (sig := [[]]) (fun _ => .cons (fun _ =>
                        .let_ (Op.mk (.add i64) (.var cHdr, .imm 760, ())) fun _q104 =>
                        .store (t := i64) (.imm 1) (.var _q104.fst)
                          (.ret (.imm 3, ()))) .nil) fun Js2 =>
                      .let_ (Op.mk (.and i32) (.var ld10, .imm 2147483647, ())) fun p38 =>
                      .let_ (Op.mk (.trunc 64 32) (.var p23.fst, ())) fun p39 =>
                      .call (as := [i64, i32, i32, i32, i32]) (bs := [.bool]) "plain_watch_push"
                        (.var cHdr, .var ld9, .var p38.fst, .var p39.fst, .imm 2, ()) fun p40 =>
                      .jnz (.var p40.fst)
                        (.let_ (Op.mk (.and i32) (.var ld9, .imm 2147483647, ())) fun p41 =>
                         .let_ (Op.mk (.trunc 64 32) (.var p23.fst, ())) fun p42 =>
                         .call (as := [i64, i32, i32, i32, i32]) (bs := [.bool]) "plain_watch_push"
                           (.var cHdr, .var ld10, .var p41.fst, .var p42.fst, .imm 2, ()) fun p =>
                         .jnz (.var p.fst)
                           (.let_ (Op.mk (.add i64) (.var p23.fst, .imm 3, ())) fun _p102 =>
                           .let_ (Op.mk (.zext 32 64) (.var ld, ())) fun p43 =>
                           .let_ (Op.mk (.add i64) (.var _p102.fst, .var p43.fst, ())) fun _p103 =>
                           .jump Js.fst (.var _p103.fst, ()))
                           (.jump Js2.fst ()))
                        (.jump Js2.fst ()))) .nil) fun Js =>
                    .jnz (.var b0) (.jump Js.fst ())
                      (.let_ (Op.mk (.cmp .uge i32 .bool) (.var ld, .imm 3, ()))
                        fun p => .jnz (.var p.fst)
                        (.let_ (Op.mk (.add i64) (.var p23.fst, .imm 3, ())) fun _q99 =>
                        .let_ (Op.mk (.mul i64) (.var _q99.fst, .imm 4, ())) fun _q101 =>
                        .let_ (Op.mk (.add i64) (.var pArena, .var _q101.fst, ())) fun _q100 =>
                        .load i32 (.var _q100.fst) fun ld9 =>
                        .call (as := [i64, i64, i32]) (bs := [i64]) "plain_lit_rank"
                          (.var pVals, .var pLvl, .var ld9, ()) fun p =>
                        .group (sig := [[i32, i64, i32]]) (fun Js1 => .cons (fun p =>
                          .let_ (Op.mk (.cmp .ult i32 .bool)
                            (.var p.snd.snd.fst, .var ld, ())) fun p28 => .jnz (.var p28.fst)
                            (.let_ (Op.mk (.add i64) (.var p23.fst, .imm 3, ())) fun p29 =>
                            .let_ (Op.mk (.zext 32 64) (.var p.snd.snd.fst, ())) fun p30 =>
                            .let_ (Op.mk (.add i64) (.var p29.fst, .var p30.fst, ())) fun p31 =>
                            .let_ (Op.mk (.mul i64) (.var p31.fst, .imm 4, ())) fun _q90 =>
                            .let_ (Op.mk (.add i64) (.var pArena, .var _q90.fst, ())) fun _q89 =>
                            .load i32 (.var _q89.fst) fun ld =>
                            .call (as := [i64, i64, i32]) (bs := [i64]) "plain_lit_rank"
                              (.var pVals, .var pLvl, .var ld, ()) fun p34 =>
                            .group (sig := [[i32, i64]]) (fun _ => .cons (fun p35 =>
                              .let_ (Op.mk (.add i32) (.var p.snd.snd.fst, .imm 1, ())) fun p_ =>
                              .jump Js1.fst
                                (.var p35.fst, .var p35.snd.fst, .var p_.fst, ())) .nil) fun Js =>
                            .let_ (Op.mk (.cmp .ugt i64 .bool)
                              (.var p34.fst, .var p.snd.fst, ())) fun p35 =>
                            .jnz (.var p35.fst)
                              (.jump Js.fst (.var p.snd.snd.fst, .var p34.fst, ()))
                              (.jump Js.fst (.var p.fst, .var p.snd.fst, ())))
                            (.group (sig := [[]]) (fun _Js2 => .cons (fun _ =>
                               .let_ (Op.mk (.add i64) (.var p23.fst, .imm 4, ())) fun _q86 =>
                               .let_ (Op.mk (.mul i64) (.var _q86.fst, .imm 4, ())) fun _q88 =>
                               .let_ (Op.mk (.add i64) (.var pArena, .var _q88.fst, ())) fun _q87 =>
                               .load i32 (.var _q87.fst) fun ld10 =>
                               .call (as := [i64, i64, i32]) (bs := [i64]) "plain_lit_rank"
                                 (.var pVals, .var pLvl, .var ld10, ()) fun p =>
                               .group (sig := [[i32, i32, i64]]) (fun Js3 => .cons (fun p =>
                                 .let_ (Op.mk (.cmp .ult i32 .bool) (.var p.fst, .var ld, ()))
                                   fun p29 =>
                                 .jnz (.var p29.fst)
                                   (.let_ (Op.mk (.add i64) (.var p23.fst, .imm 3, ())) fun p30 =>
                                   .let_ (Op.mk (.zext 32 64) (.var p.fst, ())) fun p31 =>
                                   .let_ (Op.mk (.add i64) (.var p30.fst, .var p31.fst, ()))
                                     fun p32 =>
                                   .let_ (Op.mk (.mul i64) (.var p32.fst, .imm 4, ())) fun _q82 =>
                                   .let_ (Op.mk (.add i64) (.var pArena, .var _q82.fst, ()))
                                     fun _q81 =>
                                   .load i32 (.var _q81.fst) fun ld =>
                                   .call (as := [i64, i64, i32]) (bs := [i64]) "plain_lit_rank"
                                     (.var pVals, .var pLvl, .var ld, ()) fun p35 =>
                                   .group (sig := [[i32, i64]]) (fun _ => .cons (fun p36 =>
                                     .let_ (Op.mk (.add i32) (.var p.fst, .imm 1, ())) fun p_ =>
                                     .jump Js3.fst
                                       (.var p_.fst, .var p36.fst, .var p36.snd.fst, ())) .nil)
                                         fun Js =>
                                   .let_ (Op.mk (.cmp .ugt i64 .bool)
                                     (.var p35.fst, .var p.snd.snd.fst, ())) fun p36 =>
                                   .jnz (.var p36.fst)
                                     (.jump Js.fst (.var p.fst, .var p35.fst, ()))
                                     (.jump Js.fst (.var p.snd.fst, .var p.snd.snd.fst, ())))
                                   (.group (sig := [[]]) (fun _Js4 => .cons (fun _ => .jump Js.fst
                                     ()) .nil) fun Js =>
                                   .let_ (Op.mk (.cmp .ne i32 .bool)
                                     (.var p.snd.fst, .imm 1, ())) fun p30 =>
                                   .jnz (.var p30.fst)
                                     (.let_ (Op.mk (.add i64) (.var p23.fst, .imm 4, ()))
                                       fun _q83 =>
                                     .let_ (Op.mk (.mul i64) (.var _q83.fst, .imm 4, ()))
                                       fun _q85 =>
                                     .let_ (Op.mk (.add i64) (.var pArena, .var _q85.fst, ()))
                                       fun _q84 =>
                                     .load i32 (.var _q84.fst) fun ld =>
                                     .let_ (Op.mk (.add i64) (.var p23.fst, .imm 4, ())) fun p34 =>
                                     .let_ (Op.mk (.mul i64) (.var p34.fst, .imm 4, ())) fun _q80 =>
                                     .let_ (Op.mk (.add i64) (.var pArena, .var _q80.fst, ()))
                                       fun p36 =>
                                     .let_ (Op.mk (.add i64) (.var p23.fst, .imm 3, ())) fun p37 =>
                                     .let_ (Op.mk (.zext 32 64) (.var p.snd.fst, ())) fun p38 =>
                                     .let_ (Op.mk (.add i64) (.var p37.fst, .var p38.fst, ()))
                                       fun p39 =>
                                     .let_ (Op.mk (.mul i64) (.var p39.fst, .imm 4, ())) fun _q79 =>
                                     .let_ (Op.mk (.add i64) (.var pArena, .var _q79.fst, ()))
                                       fun _q78 =>
                                     .load i32 (.var _q78.fst) fun ld11 =>
                                     .store (t := i32) (.var ld11) (.var p36.fst)
                                       (.let_ (Op.mk (.add i64) (.var p23.fst, .imm 3, ()))
                                         fun p42 =>
                                       .let_ (Op.mk (.zext 32 64) (.var p.snd.fst, ())) fun _p3a =>
                                     .let_ (Op.mk (.add i64)
                                       (.var p42.fst, .var _p3a.fst, ())) fun _p3b =>
                                       .let_ (Op.mk (.mul i64) (.var _p3b.fst, .imm 4, ()))
                                         fun _q77 =>
                                       .let_ (Op.mk (.add i64)
                                         (.var pArena, .var _q77.fst, ())) fun _q76 =>
                                       .store (t := i32) (.var ld) (.var _q76.fst)
                                         (.jump Js.fst ())))
                                     (.jump Js.fst ()))) .nil)
                                 fun Js => .jump Js.fst (.imm 2, .imm 1, .var p.fst, ())) .nil)
                                   fun Js =>
                             .let_ (Op.mk (.cmp .ne i32 .bool) (.var p.fst, .imm 0, ())) fun p29 =>
                             .jnz (.var p29.fst)
                               (.let_ (Op.mk (.add i64) (.var p23.fst, .imm 3, ())) fun _q96 =>
                               .let_ (Op.mk (.mul i64) (.var _q96.fst, .imm 4, ())) fun _q98 =>
                               .let_ (Op.mk (.add i64) (.var pArena, .var _q98.fst, ())) fun _q97 =>
                               .load i32 (.var _q97.fst) fun ld =>
                               .let_ (Op.mk (.add i64) (.var p23.fst, .imm 3, ())) fun p33 =>
                               .let_ (Op.mk (.mul i64) (.var p33.fst, .imm 4, ())) fun _q95 =>
                               .let_ (Op.mk (.add i64) (.var pArena, .var _q95.fst, ())) fun p35 =>
                               .let_ (Op.mk (.add i64) (.var p23.fst, .imm 3, ())) fun p36 =>
                               .let_ (Op.mk (.zext 32 64) (.var p.fst, ())) fun p37 =>
                               .let_ (Op.mk (.add i64) (.var p36.fst, .var p37.fst, ())) fun p38 =>
                               .let_ (Op.mk (.mul i64) (.var p38.fst, .imm 4, ())) fun _q94 =>
                               .let_ (Op.mk (.add i64) (.var pArena, .var _q94.fst, ())) fun _q93 =>
                               .load i32 (.var _q93.fst) fun ld10 =>
                               .store (t := i32) (.var ld10) (.var p35.fst)
                                 (.let_ (Op.mk (.add i64) (.var p23.fst, .imm 3, ())) fun p41 =>
                                 .let_ (Op.mk (.zext 32 64) (.var p.fst, ())) fun _p3c =>
                               .let_ (Op.mk (.add i64) (.var p41.fst, .var _p3c.fst, ()))
                                 fun _p3d =>
                                 .let_ (Op.mk (.mul i64) (.var _p3d.fst, .imm 4, ())) fun _q92 =>
                                 .let_ (Op.mk (.add i64) (.var pArena, .var _q92.fst, ()))
                                   fun _q91 =>
                                 .store (t := i32) (.var ld) (.var _q91.fst)
                                   (.jump Js.fst ())))
                               (.jump Js.fst ()))) .nil)
                          fun Js => .jump Js.fst (.imm 0, .var p.fst, .imm 1, ()))
                        (.jump Js.fst ())))
                    (.group (sig := [[i64]]) (fun _ => .cons (fun p => .ret
                      (.var p.fst, ())) .nil) fun Js =>
                     .jnz (.var p15.snd.snd.snd.snd.snd.snd.fst)
                       (.jump Js.fst (.imm 1, ())) (.jump Js.fst (.imm 0, ()))) ) .nil)
                  (fun Js => .jump Js.fst (.imm 0, ())))))))))



theorem plain_sweep_p1_wp (Γ : Env) (rest : Expr Val Cont [i64])
    {c : PlainCfg} {F0 : CNF Nat} {s0 : PlainState} {R : Mem 64 → Prop}
    {mv2 : BitVec 64} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (hinv0 : PlainCoreInv c F0 s0)
    (hmv2 : mv2 = BitVec.ofNat 64 c.mv <<< (1 : Nat))
    (hm0 : (PlainMem c s0 ⋆ R) m)
    (hrest : ∀ (s1 : PlainState) (m1 : Mem 64),
      SwP1Inv c F0 s0 (2 * c.mv) s1 → s1.arena_garbage = s0.arena_garbage →
      BinWatchesOnly c F0 s1 (2 * c.mv) → (PlainMem c s1 ⋆ R) m1 →
      wp Γ Q X rest m1) :
    wp Γ Q X (sweepP1Expr c.hdr mv2 c.pVals c.pLevel c.pWvec c.pWstk rest) m := by
  subst hmv2
  have hlen0 := hinv0.lengths; have hmv := c.hmv; have har := c.harena; have hcw := c.hwcap
  unfold dimacsBound at hmv har hcw
  have hb0 : BinWatchesOnly c F0 s0 0 :=
    ⟨hinv0.watches, fun _ hl => absurd hl (Nat.not_lt_zero _)⟩
  have hsame0 : SameSwPre s0 s0 :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  refine wp_loop_inv (ts := [i64])
    (fun v m1 => ∃ s1 : PlainState,
      SwP1Inv c F0 s0 v.1.toNat s1 ∧ s1.arena_garbage = s0.arena_garbage ∧
      (PlainMem c s1 ⋆ R) m1)
    (fun v _ => 2 * c.mv - v.1.toNat) ?_ ?_
  · intro J0 hJ0; c0_unmdata; pr_steps!
    exact hJ0 (0#64, ()) m ⟨s0, ⟨Nat.zero_le _, hlen0, hsame0, rfl, rfl, rfl, rfl, rfl, rfl,
      rfl, rfl, rfl, rfl, rfl, rfl, hb0⟩, rfl, hm0⟩
  · rintro J0 ⟨l, ⟨⟩⟩ m1 ⟨s1, hs1, hag1, hm1⟩ hJ0
    have ⟨hl_le, hlen1, hsame1, _, _, _, _, _, _, _, _, _, _, _, _, hb1⟩ := hs1
    dsimp only at *
    pr_jnz
    · change l.toNat < (BitVec.ofNat 64 c.mv <<< (1 : Nat)).toNat at hc
      rw [PlainReduceTactics.bv_c0_shl1n_64, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega)] at hc
      have hl_lt : l.toNat < 2 * c.mv := by omega
      have hl1_eq : (l + 1).toNat = l.toNat + 1 := by bv_omega
      have h2l : (l <<< (1 : Nat)).toNat = 2 * l.toNat := by
        rw [PlainReduceTactics.bv_c0_shl1n_64]; omega
      have h2l1 : ((l <<< (1 : Nat)) + 1#64).toNat = 2 * l.toNat + 1 := by
        rw [bv64_add_toNat (by omega), h2l]
      have h2l_m : (2 * l.toNat) % 2 ^ 64 = (l <<< (1 : Nat)).toNat := by
        rw [h2l, Nat.mod_eq_of_lt (by omega)]
      have h2l1_m : (2 * l.toNat + 1) % 2 ^ 64 = ((l <<< (1 : Nat)) + 1#64).toNat := by
        rw [h2l1, Nat.mod_eq_of_lt (by omega)]
      have hw0_len : (l <<< (1 : Nat)).toNat < s1.wvec.length := by rw [hlen1.wvec_len]; omega
      have hw1_len : ((l <<< (1 : Nat)) + 1#64).toNat < s1.wvec.length := by
        rw [hlen1.wvec_len]; omega
      have hl_div2 : (l >>> (1 : Nat)).toNat < s1.lvl.length := by
        rw [PlainReduceTactics.bv_c0_shr1n_64, hlen1.lvl_len]; omega
      have hl_vals : l.toNat < s1.vals.length := by rw [hlen1.vals_len]; omega
      have hoff64 : (s1.wvec[(l <<< (1 : Nat)).toNat].setWidth 64).toNat = watchOff s1 l.toNat := by
        rw [bv_c0_zext32_64]; unfold watchOff
        rw [← h2l, List.getElem?_eq_getElem hw0_len, Option.getD_some]
      have hsz64 : (s1.wvec[((l <<< (1 : Nat)) + 1#64).toNat].setWidth 64).toNat =
          watchSize s1 l.toNat := by
        rw [bv_c0_zext32_64]; unfold watchSize
        rw [← h2l1, List.getElem?_eq_getElem hw1_len, Option.getD_some]
      have hlay := hb1.1.layout; have hbdd := hlay.bounds l.toNat hl_lt
      have hend_le : watchOff s1 l.toNat + watchSize s1 l.toNat ≤ c.wcap := by
        have := hlen1.wlen_le; omega
      have hws_len : s1.wstk.length = c.wcap := hlen1.wstk_len_arr
      c0_unmdata; pr_let
      refine wp_load_of (c0_load_arena_wvec (i := l <<< (1 : Nat)) hw0_len hm1) ?_; pr_let
      refine wp_load_of (c0_load_arena_wvec (i := (l <<< (1 : Nat)) + 1#64) hw1_len hm1) ?_; pr_let
      refine wp_join_group (ts := [.bool]) (fun _ ml => (PlainMem c s1 ⋆ R) ml) ?_ ?_
      · rintro _ ⟨lfix, ⟨⟩⟩ ml hml
        clear_except [Γ Q X c F0 s0 R hinv0 hmv har hcw hrest l hl_lt hl1_eq
          h2l h2l1 h2l_m h2l1_m hw0_len hw1_len s1 hs1 hlen1 hsame1 hag1 hb1 hoff64 hsz64 hbdd
          hend_le hws_len lfix ml hml hJ0]
        pr_jnz
        · simp only [h2l1_m] at hc
          have hsz0 : watchSize s1 l.toNat = 0 := by rw [← hsz64]; bv_omega
          c0_unmdata; pr_steps!
          exact hJ0 (l + 1, ()) ml (by dsimp only; omega)
            ⟨s1, sw1_skip_zero hs1 hl_lt hl1_eq hsz0, hag1, hml⟩
        · refine wp_join_group (ts := [])
            (fun _ m_end => ∃ s2 : PlainState, SwP1Inv c F0 s0 (l.toNat + 1) s2 ∧
              s2.arena_garbage = s0.arena_garbage ∧ (PlainMem c s2 ⋆ R) m_end) ?_ ?_
          · rintro _ ⟨⟩ m_end ⟨s2, hs2, hag2, hm_end⟩
            c0_unmdata; pr_steps!
            exact hJ0 (l + 1, ()) m_end (by dsimp only; omega)
              ⟨s2, by simpa only [hl1_eq] using hs2, hag2, hm_end⟩
          · intro J_s hJs; pr_jnz
            · refine wp_loop_inv (ts := [i64])
                (fun v mp => ∃ nb' : BitVec 64,
                  watchOff s1 l.toNat ≤ v.1.toNat ∧
                  v.1.toNat ≤ watchOff s1 l.toNat + watchSize s1 l.toNat ∧
                  WatchSliceOk c F0 s1 l.toNat v.1.toNat
                    (watchOff s1 l.toNat + watchSize s1 l.toNat - v.1.toNat) ∧
                  (PlainMem c { s1 with num_binary := nb' } ⋆ R) mp)
                (fun v _ => watchOff s1 l.toNat + watchSize s1 l.toNat - v.1.toNat) ?_ ?_
              · intro Jp hJp; c0_unmdata; pr_steps!
                have hsub : watchOff s1 l.toNat + watchSize s1 l.toNat - watchOff s1 l.toNat =
                    watchSize s1 l.toNat := by omega
                exact hJp (_, ()) ml ⟨s1.num_binary,
                  by dsimp only; rw [hoff64]; exact Nat.le_refl _,
                  by dsimp only; rw [hoff64]; omega,
                  by simpa only [hoff64, hsub] using hb1.1.slices l.toNat hl_lt, hml⟩
              · rintro Jp ⟨p, ⟨⟩⟩ mp ⟨nb', hp_lo, hp_hi, hws_p, hmp⟩ hJp
                dsimp only at *
                have hsum_eq : (s1.wvec[(l <<< (1 : Nat)).toNat].setWidth 64 +
                    s1.wvec[((l <<< (1 : Nat)) + 1#64).toNat].setWidth 64).toNat =
                    watchOff s1 l.toNat + watchSize s1 l.toNat := by bv_omega
                pr_jnz
                · simp only [h2l_m, h2l1_m] at hc
                  have hp_lt : p.toNat < watchOff s1 l.toNat + watchSize s1 l.toNat := by bv_omega
                  have hp_ws : p.toNat < ({ s1 with num_binary := nb' } : PlainState).wstk.length :=
                    by change p.toNat < s1.wstk.length; omega
                  have hstep := watchSliceOk_step hws_p hp_lt (List.getElem?_eq_getElem (by omega))
                  c0_unmdata; pr_let
                  refine wp_load_of (c0_load_arena_wstk (i := p) hp_ws hmp) ?_; pr_let
                  refine wp_join_group (ts := [i64])
                    (fun v mp' => ∃ nb'' : BitVec 64,
                      watchOff s1 l.toNat ≤ v.1.toNat ∧
                      v.1.toNat ≤ watchOff s1 l.toNat + watchSize s1 l.toNat ∧
                      p.toNat < v.1.toNat ∧
                      WatchSliceOk c F0 s1 l.toNat v.1.toNat
                        (watchOff s1 l.toNat + watchSize s1 l.toNat - v.1.toNat) ∧
                      (PlainMem c { s1 with num_binary := nb'' } ⋆ R) mp') ?_ ?_
                  · rintro _ ⟨p', ⟨⟩⟩ mp' ⟨nb'', hlo', hhi', hinc', hws', hmp'⟩
                    c0_unmdata; pr_steps!
                    exact hJp (p', ()) mp' (by dsimp only at *; omega)
                      ⟨nb'', hlo', hhi', hws', hmp'⟩
                  · intro Jstep hJstep; pr_jnz
                    · have hbin := hstep.1 (by assumption)
                      have hp1 : (p + 1).toNat = p.toNat + 1 := by bv_omega
                      refine wp_join_group (ts := [])
                        (fun _ mb => ∃ nb'' : BitVec 64,
                          (PlainMem c { s1 with num_binary := nb'' } ⋆ R) mb) ?_ ?_
                      · rintro _ ⟨⟩ mb ⟨nb'', hmb⟩
                        c0_unmdata; pr_steps!
                        exact hJstep (p + 1, ()) mb ⟨nb'', by dsimp only; omega,
                          by dsimp only; omega, by dsimp only; omega,
                          by simpa only [hp1] using hbin.2.2, hmb⟩
                      · intro Jnb hJnb; pr_jnz
                        · c0_unmdata; pr_let
                          refine wp_load_of (load_arena_num_binary hmp) ?_; pr_let
                          pr_jnz
                          · c0_unmdata; pr_let
                            refine wp_load_of (load_arena_num_binary hmp) ?_; pr_let
                            refine wp_store_sep
                              (store_arena_num_binary (s := { s1 with num_binary := nb' })
                                (nb' - 1#64) hmp) fun _ hms => ?_
                            pr_steps!; exact hJnb () _ ⟨nb' - 1#64, hms⟩
                          · pr_steps!; exact hJnb () mp ⟨nb', hmp⟩
                        · pr_steps!; exact hJnb () mp ⟨nb', hmp⟩
                    · have hlg := hstep.2 (by assumption)
                      have hp2 : (p + 2).toNat = p.toNat + 2 := by bv_omega
                      c0_unmdata; pr_steps!
                      exact hJstep (p + 2, ()) mp ⟨nb', by dsimp only; omega,
                        by dsimp only; omega, by dsimp only; omega,
                        by simpa only [hp2] using hlg.2, hmp⟩
                · refine wp_loop_inv (ts := [i64])
                    (fun v mk => ∃ wstk' : List (BitVec 32),
                      watchOff s1 l.toNat ≤ v.1.toNat ∧
                      v.1.toNat ≤ watchOff s1 l.toNat + watchSize s1 l.toNat ∧
                      wstk'.length = c.wcap ∧
                      (∀ q, q < watchOff s1 l.toNat ∨
                        watchOff s1 l.toNat + watchSize s1 l.toNat ≤ q → wstk'[q]? = s1.wstk[q]?) ∧
                      (PlainMem c { s1 with wstk := wstk', num_binary := nb' } ⋆ R) mk)
                    (fun v _ => watchOff s1 l.toNat + watchSize s1 l.toNat - v.1.toNat) ?_ ?_
                  · intro Jk hJk; c0_unmdata; pr_steps!
                    exact hJk (_, ()) mp ⟨s1.wstk, by dsimp only; rw [hoff64]; exact Nat.le_refl _,
                      by dsimp only; rw [hoff64]; omega, hws_len, fun _ _ => rfl, hmp⟩
                  · rintro Jk ⟨k, ⟨⟩⟩ mk ⟨wstk', hk_lo, hk_hi, hlen_w, hout, hmk⟩ hJk
                    dsimp only at *
                    pr_jnz
                    · simp only [h2l_m, h2l1_m] at hc
                      have hk_lt : k.toNat < watchOff s1 l.toNat + watchSize s1 l.toNat := by
                        bv_omega
                      have hk_w : k.toNat < wstk'.length := by omega
                      have hk1 : (k + 1).toNat = k.toNat + 1 := by bv_omega
                      have hfill := sweep_fill_sentinels (ws0 := s1.wstk) (ws1 := s1.wstk)
                        (off := watchOff s1 l.toNat)
                        (end_ := watchOff s1 l.toNat + watchSize s1 l.toNat)
                        (q := watchOff s1 l.toNat) hk_lo hk_lo hk_lt (hlen_w.trans hws_len.symm)
                        hout (fun _ h1 h2 => by omega)
                      c0_unmdata; pr_steps!
                      exact hJk (k + 1, ()) _ (by dsimp only; omega)
                        ⟨wstk'.set k.toNat 0xFFFFFFFF#32, by dsimp only; omega,
                          by dsimp only; omega, hfill.1.trans hws_len, hfill.2.1, by assumption⟩
                    · c0_unmdata; pr_let
                      refine wp_store_sep (sw_store_wvec (i := (l <<< (1 : Nat)) + 1#64) 0#32
                        hmk hw1_len) fun mw hms1 => ?_
                      have hms1' : (PlainMem c { s1 with
                          wstk := wstk', wvec := s1.wvec.set (2 * l.toNat + 1) 0#32,
                          num_binary := nb' } ⋆ R) mw := by simpa only [h2l1] using hms1
                      c0_unmdata; pr_steps!
                      have hfin := sw1_finish_z hs1 hag1 hl_lt hl1_eq h2l1 hw1_len hlen_w hout
                        (by assumption)
                      exact hJs () _ (hl1_eq ▸ hfin)
            · refine wp_loop_inv (ts := [i64, i64])
                (fun v mp => ∃ (wstk' : List (BitVec 32)) (nb' : BitVec 64),
                  watchOff s1 l.toNat ≤ v.2.1.toNat ∧ v.2.1.toNat ≤ v.1.toNat ∧
                  v.1.toNat ≤ watchOff s1 l.toNat + watchSize s1 l.toNat ∧
                  wstk'.length = c.wcap ∧
                  (∀ m, m < watchOff s1 l.toNat ∨
                    watchOff s1 l.toNat + watchSize s1 l.toNat ≤ m → wstk'[m]? = s1.wstk[m]?) ∧
                  (∀ m, v.1.toNat ≤ m → m < watchOff s1 l.toNat + watchSize s1 l.toNat →
                    wstk'[m]? = s1.wstk[m]?) ∧
                  WatchSliceOk c F0 s1 l.toNat v.1.toNat
                    (watchOff s1 l.toNat + watchSize s1 l.toNat - v.1.toNat) ∧
                  (∀ k < v.2.1.toNat - watchOff s1 l.toNat,
                    ∃ w, wstk'[watchOff s1 l.toNat + k]? = some w ∧ BinWatchOk c F0 l.toNat w) ∧
                  (PlainMem c { s1 with wstk := wstk', num_binary := nb' } ⋆ R) mp)
                (fun v _ => watchOff s1 l.toNat + watchSize s1 l.toNat - v.1.toNat) ?_ ?_
              · intro Jpq hJpq; c0_unmdata; pr_steps!
                have hsub : watchOff s1 l.toNat + watchSize s1 l.toNat - watchOff s1 l.toNat =
                    watchSize s1 l.toNat := by omega
                exact hJpq (_, _, ()) ml ⟨s1.wstk, s1.num_binary, by dsimp only; rw [hoff64]; omega,
                  by dsimp only; rw [hoff64]; omega, by dsimp only; rw [hoff64]; omega, hws_len,
                  fun _ _ => rfl, fun _ _ _ => rfl,
                  (by simpa only [hoff64, hsub] using hb1.1.slices l.toNat hl_lt),
                  fun _ h => by dsimp only at h; rw [hoff64] at h; omega, hml⟩
              · rintro Jpq ⟨p, q, ⟨⟩⟩ mp ⟨wstk', nb', hq_lo, hqp, hp_hi, hlen_w, hout, hsuf,
                  hws_p, hbin_q, hmp⟩ hJpq
                dsimp only at *
                have hsum_eq : (s1.wvec[(l <<< (1 : Nat)).toNat].setWidth 64 +
                    s1.wvec[((l <<< (1 : Nat)) + 1#64).toNat].setWidth 64).toNat =
                    watchOff s1 l.toNat + watchSize s1 l.toNat := by bv_omega
                pr_jnz
                · simp only [h2l_m, h2l1_m] at hc
                  have hp_lt : p.toNat < watchOff s1 l.toNat + watchSize s1 l.toNat := by bv_omega
                  have hp_w : p.toNat < wstk'.length := by omega
                  have hw0_eq : wstk'[p.toNat]? = s1.wstk[p.toNat]? :=
                    hsuf p.toNat (by omega) hp_lt
                  have hstep := watchSliceOk_step hws_p hp_lt
                    (hw0_eq.symm.trans (List.getElem?_eq_getElem hp_w))
                  c0_unmdata; pr_let
                  refine wp_load_of (c0_load_arena_wstk (i := p) hp_w hmp) ?_; pr_let
                  refine wp_join_group (ts := [i64, i64])
                    (fun v mp' => ∃ (wstk'' : List (BitVec 32)) (nb'' : BitVec 64),
                      watchOff s1 l.toNat ≤ v.2.1.toNat ∧ v.2.1.toNat ≤ v.1.toNat ∧
                      v.1.toNat ≤ watchOff s1 l.toNat + watchSize s1 l.toNat ∧
                      p.toNat < v.1.toNat ∧ wstk''.length = c.wcap ∧
                      (∀ m, m < watchOff s1 l.toNat ∨
                        watchOff s1 l.toNat + watchSize s1 l.toNat ≤ m →
                        wstk''[m]? = s1.wstk[m]?) ∧
                      (∀ m, v.1.toNat ≤ m → m < watchOff s1 l.toNat + watchSize s1 l.toNat →
                        wstk''[m]? = s1.wstk[m]?) ∧
                      WatchSliceOk c F0 s1 l.toNat v.1.toNat
                        (watchOff s1 l.toNat + watchSize s1 l.toNat - v.1.toNat) ∧
                      (∀ k < v.2.1.toNat - watchOff s1 l.toNat,
                        ∃ w, wstk''[watchOff s1 l.toNat + k]? = some w ∧
                          BinWatchOk c F0 l.toNat w) ∧
                      (PlainMem c { s1 with wstk := wstk'', num_binary := nb'' } ⋆ R) mp') ?_ ?_
                  · rintro _ ⟨p', q', ⟨⟩⟩ mp'
                      ⟨wstk'', nb'', hq', hqp', hp', hinc', hlw', hout', hsuf', hws', hbin', hmp'⟩
                    c0_unmdata; pr_steps!
                    exact hJpq (p', q', ()) mp' (by dsimp only at *; omega)
                      ⟨wstk'', nb'', hq', hqp', hp', hlw', hout', hsuf', hws', hbin', hmp'⟩
                  · intro Jstep hJstep; pr_jnz
                    · have hbin := hstep.1 (by assumption)
                      have hp1 : (p + 1).toNat = p.toNat + 1 := by bv_omega
                      have hq1 : (q + 1).toNat = q.toNat + 1 := by bv_omega
                      have hq_w : q.toNat < wstk'.length := by omega
                      let ot := wstk'[p.toNat] &&& 0x7FFFFFFF#32
                      let s1w : PlainState := { s1 with wstk := wstk', num_binary := nb' }
                      have hot_lt : ot.toNat < 2 * c.mv := hbin.1.2.1
                      have hot_lvl : ((ot >>> (1 : Nat)).setWidth 64).toNat < s1w.lvl.length := by
                        dsimp only [s1w]; rw [bv_c0_zext32_64,
                          PlainReduceTactics.bv_c0_shr1n_32, hlen1.lvl_len]; omega
                      have hot_vals : (ot.setWidth 64).toNat < s1w.vals.length := by
                        dsimp only [s1w]; rw [bv_c0_zext32_64, hlen1.vals_len]; exact hot_lt
                      refine wp_join_group (ts := [.bool]) (fun _ mo =>
                        (PlainMem c { s1 with wstk := wstk', num_binary := nb' } ⋆ R) mo) ?_ ?_
                      · rintro _ ⟨ofix, ⟨⟩⟩ mo hmo
                        refine wp_join_group (ts := [i64])
                          (fun v mb => ∃ (wstk'' : List (BitVec 32)) (nb'' : BitVec 64),
                            watchOff s1 l.toNat ≤ v.1.toNat ∧ v.1.toNat ≤ p.toNat + 1 ∧
                            p.toNat + 1 ≤ watchOff s1 l.toNat + watchSize s1 l.toNat ∧
                            wstk''.length = c.wcap ∧
                            (∀ m, m < watchOff s1 l.toNat ∨
                              watchOff s1 l.toNat + watchSize s1 l.toNat ≤ m →
                              wstk''[m]? = s1.wstk[m]?) ∧
                            (∀ m, p.toNat + 1 ≤ m → m < watchOff s1 l.toNat + watchSize s1 l.toNat →
                              wstk''[m]? = s1.wstk[m]?) ∧
                            (∀ k < v.1.toNat - watchOff s1 l.toNat,
                              ∃ w, wstk''[watchOff s1 l.toNat + k]? = some w ∧
                                BinWatchOk c F0 l.toNat w) ∧
                            (PlainMem c { s1 with wstk := wstk'', num_binary := nb'' } ⋆ R) mb)
                          ?_ ?_
                        · rintro _ ⟨q', ⟨⟩⟩ mb ⟨wstk'', nb'', hq', hqp', hp1_hi, hlen'', hout'',
                            hsuf'', hbin'', hmb⟩
                          c0_unmdata; pr_steps!
                          exact hJstep (p + 1, q', ()) mb ⟨wstk'', nb'', hq',
                            by dsimp only at *; omega, by dsimp only at *; omega,
                            by dsimp only; omega, hlen'', hout'',
                            fun m hm1 hm2 => hsuf'' m (by dsimp only at hm1; omega) hm2,
                            by simpa only [hp1] using hbin.2.2, hbin'', hmb⟩
                        · intro Jq' hJq'; pr_jnz
                          · refine wp_join_group (ts := [])
                              (fun _ mb => ∃ nb'' : BitVec 64,
                                (PlainMem c { s1 with wstk := wstk', num_binary := nb'' } ⋆ R)
                                  mb) ?_ ?_
                            · rintro _ ⟨⟩ mb ⟨nb'', hmb⟩
                              c0_unmdata; pr_steps!
                              exact hJq' (q, ()) mb ⟨wstk', nb'', hq_lo, by dsimp only; omega,
                                by omega, hlen_w, hout, fun m hm1 hm2 => hsuf m (by omega) hm2,
                                hbin_q, hmb⟩
                            · intro Jnb hJnb; pr_jnz
                              · c0_unmdata; pr_let
                                refine wp_load_of (load_arena_num_binary hmo) ?_; pr_let
                                pr_jnz
                                · c0_unmdata; pr_let
                                  refine wp_load_of (load_arena_num_binary hmo) ?_; pr_let
                                  refine wp_store_sep (store_arena_num_binary
                                    (s := { s1 with wstk := wstk', num_binary := nb' })
                                    (nb' - 1#64) hmo) fun _ hms => ?_
                                  pr_steps!; exact hJnb () _ ⟨nb' - 1#64, hms⟩
                                · pr_steps!; exact hJnb () mo ⟨nb', hmo⟩
                              · pr_steps!; exact hJnb () mo ⟨nb', hmo⟩
                          · c0_unmdata; pr_let
                            refine wp_store_sep
                              (c0_store_arena_wstk (i := q) wstk'[p.toNat] hq_w hmo)
                              fun mb hmb => ?_; pr_steps!
                            obtain ⟨wstk'', nb'', hq', hqp', hp1_hi, _, hlen'', hout'', hsuf'', _,
                                hbin'', hmb'⟩ := sw1_bin_step hq_lo hqp hp_lt hws_len hlen_w hout
                              hsuf hbin_q hp1 hq1 hp_w hq_w ⟨hbin.1, by omega, hbin.2.2⟩ hmb
                            exact hJq' (q + 1, ()) mb ⟨wstk'', nb'', hq', by dsimp only; omega,
                              by omega, hlen'', hout'', by simpa only [hp1] using hsuf'', hbin'',
                              hmb'⟩
                      · intro Jofix hJofix; pr_jnz
                        · c0_unmdata; pr_let
                          refine wp_load_of (c0_load_arena_lvl (s := s1w) ?_ hmp) ?_
                          · dsimp only [ot, s1w] at hot_lt ⊢
                            rw [hlen1.lvl_len, bv_c0_zext32_64]
                            simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
                            rw [show (BitVec.toNat (1 : BitVec 32) % 32) = 1 from rfl, Nat.pow_one]
                            omega
                          · pr_let; pr_jnz
                            · c0_unmdata; pr_let
                              refine wp_load_of (c0_load_arena_vals (s := s1w) ?_ hmp) ?_
                              · dsimp only [ot, s1w] at hot_lt ⊢
                                simp only [LeanQbe.T.Arg.val_var, hlen1.vals_len, bv_c0_zext32_64]
                                exact hot_lt
                              · pr_let; pr_jnz <;> (c0_unmdata; pr_steps!; first
                                  | exact hJofix (true, ()) mp hmp
                                  | exact hJofix (false, ()) mp hmp)
                            · c0_unmdata; pr_steps!; exact hJofix (false, ()) mp hmp
                        · exfalso; refine hc ?_
                          rw [Nat.mod_eq_of_lt (show c.mv < 2 ^ 64 by omega),
                            Nat.mod_eq_of_lt (show 2 * c.mv < 2 ^ 64 by omega),
                            Nat.mod_eq_of_lt (Nat.lt_trans (BitVec.isLt _) (by decide))]
                          exact hot_lt
                    · have hlg := hstep.2 (by assumption)
                      have hp2 : (p + 2).toNat = p.toNat + 2 := by bv_omega
                      c0_unmdata; pr_steps!
                      exact hJstep (p + 2, q, ()) mp ⟨wstk', nb', hq_lo, by dsimp only; omega,
                        by dsimp only; omega, by dsimp only; omega, hlen_w, hout,
                        fun m hm1 hm2 => hsuf m (by dsimp only at hm1; omega) hm2,
                        by simpa only [hp2] using hlg.2, hbin_q, hmp⟩
                · refine wp_loop_inv (ts := [i64])
                    (fun v mk => ∃ wstk'' : List (BitVec 32),
                      q.toNat ≤ v.1.toNat ∧
                      v.1.toNat ≤ watchOff s1 l.toNat + watchSize s1 l.toNat ∧
                      wstk''.length = c.wcap ∧
                      (∀ m, m < watchOff s1 l.toNat ∨
                        watchOff s1 l.toNat + watchSize s1 l.toNat ≤ m →
                        wstk''[m]? = s1.wstk[m]?) ∧
                      (∀ m, watchOff s1 l.toNat ≤ m → m < q.toNat → wstk''[m]? = wstk'[m]?) ∧
                      (PlainMem c { s1 with wstk := wstk'', num_binary := nb' } ⋆ R) mk)
                    (fun v _ => watchOff s1 l.toNat + watchSize s1 l.toNat - v.1.toNat) ?_ ?_
                  · intro Jk hJk; c0_unmdata; pr_steps!
                    exact hJk (q, ()) mp ⟨wstk', Nat.le_refl _, Nat.le_trans hqp hp_hi, hlen_w,
                      hout, fun _ _ _ => rfl, hmp⟩
                  · rintro Jk ⟨k, ⟨⟩⟩ mk ⟨wstk'', hk_lo, hk_hi, hlen'', hout'', hpre'', hmk⟩ hJk
                    dsimp only at hk_lo hk_hi hJk
                    pr_jnz
                    · simp only [h2l_m, h2l1_m] at hc
                      have hk_lt : k.toNat < watchOff s1 l.toNat + watchSize s1 l.toNat := by
                        bv_omega
                      have hk_w : k.toNat < wstk''.length := by omega
                      have hk1 : (k + 1).toNat = k.toNat + 1 := by bv_omega
                      have hfill := sweep_fill_sentinels (ws0 := s1.wstk) (ws1 := wstk')
                        (off := watchOff s1 l.toNat)
                        (end_ := watchOff s1 l.toNat + watchSize s1 l.toNat)
                        (q := q.toNat) (by omega) hk_lo hk_lt (hlen''.trans hws_len.symm)
                        hout'' hpre''
                      c0_unmdata; pr_steps!
                      exact hJk (k + 1, ()) _ (by dsimp only; omega)
                        ⟨wstk''.set k.toNat 0xFFFFFFFF#32, by dsimp only; omega,
                          by dsimp only; omega, hfill.1.trans hws_len, hfill.2.1, hfill.2.2,
                          by assumption⟩
                    · have hbin_ex : ∀ k < q.toNat - watchOff s1 l.toNat,
                          ∃ w, wstk''[watchOff s1 l.toNat + k]? = some w ∧
                            BinWatchOk c F0 l.toNat w := fun k hk => by
                        obtain ⟨w, hw, hok⟩ := hbin_q k hk
                        exact ⟨w, (hpre'' (watchOff s1 l.toNat + k) (by omega) (by omega)).trans hw,
                          hok⟩
                      c0_unmdata; pr_let
                      refine wp_store_sep (sw_store_wvec (i := (l <<< (1 : Nat)) + 1#64)
                        ((q - s1.wvec[(l <<< (1 : Nat)).toNat].setWidth 64).truncate 32)
                        hmk hw1_len) fun mw hms1 => ?_
                      have hms1' : (PlainMem c { s1 with
                          wstk := wstk'',
                          wvec := s1.wvec.set (2 * l.toNat + 1)
                            ((q - s1.wvec[(l <<< (1 : Nat)).toNat].setWidth 64).truncate 32),
                          num_binary := nb' } ⋆ R) mw := by simpa only [h2l1] using hms1
                      c0_unmdata; pr_steps!
                      have hfin := sw1_finish_q hs1 hag1 hl_lt hl1_eq h2l h2l1 hw0_len hw1_len hq_lo
                        (Nat.le_trans hqp hp_hi) hlen'' hout'' hbin_ex (by assumption)
                      exact hJs () _ (hl1_eq ▸ hfin)
      · intro Jl hJl; c0_unmdata; pr_let
        c0_unmdata; pr_steps! <;> first
          | exact hJl (true, ()) m1 hm1 | exact hJl (false, ()) m1 hm1
    · change ¬ l.toNat < (BitVec.ofNat 64 c.mv <<< (1 : Nat)).toNat at hc
      rw [PlainReduceTactics.bv_c0_shl1n_64] at hc
      have hl_eq : l.toNat = 2 * c.mv := by bv_omega
      have hb1_all : BinWatchesOnly c F0 s1 (2 * c.mv) := by simpa only [hl_eq] using hb1
      have hs1_all : SwP1Inv c F0 s0 (2 * c.mv) s1 := by simpa only [hl_eq] using hs1
      exact hrest s1 m1 hs1_all hag1 hb1_all hm1

theorem plain_sweep_p3_wp (Γ : Env)
    (hWP : ∀ args m Q X, plainWatchPushSpec args m Q X →
      Γ "plain_watch_push" [i64, i32, i32, i32, i32] [.bool] args m Q X)
    (hLR : ∀ args m Q X, plainLitRankSpec args m Q X →
      Γ "plain_lit_rank" [i64, i64, i32] [i64] args m Q X)
    {c : PlainCfg} {F0 : CNF Nat} {s0 s_e : PlainState} {R : Mem 64 → Prop}
    {p15_0 dst fred irred redd : BitVec 64} {unsat new_unit b0 : Bool}
    {m3 : Mem 64} {Q : Post [i64]} {X : XPost}
    (hinv0 : PlainCoreInv c F0 s0)
    (he : SwP2ExitInv c F0 s0 dst.toNat unsat new_unit s_e)
    (hm3 : (PlainMem c s_e ⋆ R) m3)
    (hQ : ∀ (r : BitVec 64) (vals' : List (BitVec 8))
        (lvl' rsns' trl' tp' : List (BitVec 32)) (te' : Nat) (unfl' : BitVec 64)
        (wvec' wstk' arena' : List (BitVec 32)) (alen' wlen' : Nat)
        (wu' fred' ni' nr' nb' oom' : BitVec 64) (heur' : PlainHeur) (m' : Mem 64),
      let s' : PlainState :=
        { s0 with
          arena_len := alen', wlen := wlen', wusable := wu', arena_garbage := 0#64,
          first_reducible := fred', num_irred := ni', num_redundant := nr', num_binary := nb',
          unflushed := unfl', trail_end := te', oom := oom', vals := vals', lvl := lvl',
          rsns := rsns', trl := trl', trail_pos := tp', wvec := wvec', arena := arena',
          wstk := wstk', heur := heur' }
      PlainState.LengthsOk c s' →
      (r = 0#64 ∨ r = 1#64 ∨ r = 2#64 ∨ r = 3#64) →
      heur'.rel_trigger = s0.heur.rel_trigger →
      (∀ i, i < te' → (trl'[i]?.getD 0#32).toNat < 2 * c.mv) →
      (r = 0#64 ∨ r = 1#64 → PlainCoreInv c F0 s' ∧ oom' = 0#64) →
      (0 < s0.cur_level → r = 0#64 →
        vals' = s0.vals ∧ lvl' = s0.lvl ∧ trl' = s0.trl ∧ tp' = s0.trail_pos ∧
        te' = s0.trail_end) →
      (r = 1#64 → s0.cur_level = 0 ∧ s0.trail_end < te') →
      (r = 2#64 → s0.cur_level = 0 ∧ F0.Unsat) →
      (PlainMem c s' ⋆ R) m' → Q (r, ()) m') :
    wp Γ Q X (sweepP3Expr c.hdr c.pVals c.pLevel c.pArena b0
      (p15_0, dst, fred, irred, redd, unsat, new_unit, ())) m3 := by
  have hmv := c.hmv; have har := c.harena
  unfold dimacsBound at hmv har
  have ⟨hlen_e, hsame_e, hrt_e, hdst_le, htrl_e, hu_e, hok_e⟩ := he
  c0_unmdata
  refine wp_store_sep (c0_store_arena_len (s := s_e) dst hm3) fun ms1 hms1 => ?_; pr_let
  refine wp_store_sep (store_arena_garbage 0#64 hms1) fun ms2 hms2 => ?_; pr_let
  refine wp_store_sep (store_arena_first_reducible fred hms2) fun ms3 hms3 => ?_; pr_let
  refine wp_store_sep (store_arena_num_irred irred hms3) fun ms4 hms4 => ?_; pr_let
  refine wp_store_sep (store_arena_num_redundant redd hms4) fun ms5 hms5 => ?_
  let s_fin : PlainState :=
    { s_e with
      arena_len := dst.toNat, arena_garbage := 0#64, first_reducible := fred,
      num_irred := irred, num_redundant := redd }
  have hms5' : (PlainMem c s_fin ⋆ R) ms5 := hms5
  obtain ⟨hlen_f, hsame_f, hok_f⟩ :=
    sw2_exit_to_p3 (fred := fred) (irred := irred) (redd := redd) hinv0 he
  clear_except [Γ hWP hLR Q X c F0 s0 R hinv0 hmv har hQ dst new_unit unsat s_fin hlen_f
    hsame_f hrt_e htrl_e hu_e hok_f hms5']
  pr_jnz
  · c0_unmdata; pr_steps!
    exact sweep_ret hQ hsame_f rfl hlen_f (Or.inr (Or.inr (Or.inl rfl))) hrt_e htrl_e
      (fun h => by rcases h with h | h <;> cases h) (fun _ h => by cases h)
      (fun h => by cases h) (fun _ => hu_e (by assumption)) hms5'
  · have huf : unsat = false := by cases unsat <;> first | rfl | contradiction
    c0_unmdata; pr_let
    refine wp_load_of (load_arena_oom hms5') ?_
    pr_let; pr_jnz
    · c0_unmdata; pr_steps!
      exact sweep_ret hQ hsame_f rfl hlen_f (Or.inr (Or.inr (Or.inr rfl))) hrt_e htrl_e
        (fun h => by rcases h with h | h <;> cases h) (fun _ h => by cases h)
        (fun h => by cases h) (fun h => by cases h) hms5'
    · have hoom0 : s_fin.oom = 0#64 := by bv_omega
      have hp3_0 := hok_f huf hoom0
      refine wp_loop_inv (ts := [i64])
        (fun v m4 => ∃ s_p : PlainState,
          v.1.toNat ≤ dst.toNat ∧
          (v.1.toNat = dst.toNat ∨ v.1.toNat ∈ arenaClauseRefs s_p) ∧
          SwP3Inv c F0 s0 dst.toNat new_unit s_p ∧ (PlainMem c s_p ⋆ R) m4)
        (fun v _ => dst.toNat - v.1.toNat) ?_ ?_
      · intro Jp3 hJp3; c0_unmdata; pr_steps!
        have hp0 := (arenaScan_zero hp3_0.1.arena.len_ok).imp
          (fun h => by rw [hp3_0.2.2.2.2.1] at h; exact h.symm) id
        exact hJp3 (0#64, ()) _ ⟨s_fin, Nat.zero_le _, hp0, hp3_0, hms5'⟩
      · rintro Jp3 ⟨p, ⟨⟩⟩ m4 ⟨s_p, hp_le, hp_ref, hsw_p, hm4⟩ hJp3
        dsimp only at hp_le hp_ref hJp3
        have hlen_p := hsw_p.1.lengths
        pr_jnz
        · have hp_lt : p.toNat < dst.toNat := by bv_omega
          have href_p : p.toNat ∈ arenaClauseRefs s_p := hp_ref.resolve_left (by omega)
          have hwf_p := hsw_p.1.arena.refs_wf p.toNat href_p
          have hng_pr := hsw_p.2.2.2.2.2.2.2.2 p.toNat href_p
          have har_p_len := hlen_p.arena_len_arr; have har_p_le := hlen_p.arena_len_le
          have hp2_eq : (p + 2#64).toNat = p.toNat + 2 := by bv_omega
          have hp2_lt : (p + 2#64).toNat < s_p.arena.length := by omega
          c0_unmdata; pr_let
          refine wp_load_of (c0_load_arena_arena (s := s_p) (i := p + 2#64) hp2_lt hm4) ?_
          pr_let
          refine wp_join_group (ts := [])
            (fun _ m_r => ∃ s_r : PlainState, p.toNat ∈ arenaClauseRefs s_r ∧
              SwP3Inv c F0 s0 dst.toNat new_unit s_r ∧
              arenaClauseSize s_r p.toNat = arenaClauseSize s_p p.toNat ∧
              (PlainMem c s_r ⋆ R) m_r) ?_ ?_
          · rintro _ ⟨⟩ m_r ⟨s_r, href_r, hsw_r, hsz_rp, hmr⟩
            have hlen_r := hsw_r.1.lengths
            have hwf_r := hsw_r.1.arena.refs_wf p.toNat href_r
            have hng_rr := hsw_r.2.2.2.2.2.2.2.2 p.toNat href_r
            have har_r_len := hlen_r.arena_len_arr; have har_r_le := hlen_r.arena_len_le
            have h1_eq : (p + 1#64).toNat = p.toNat + 1 := bv64_add_toNat (by omega)
            have h1_lt : (p + 1#64).toNat < s_r.arena.length := by
              rw [h1_eq, har_r_len]; omega
            have ⟨hcore_s2, hrefs_s2, hng_s2⟩ := setSrch2_core hsw_r.1 href_r
            let s_r2 : PlainState := { s_r with arena := s_r.arena.set (p.toNat + 1) 2#32 }
            have href_r2 : p.toNat ∈ arenaClauseRefs s_r2 := hrefs_s2.symm ▸ href_r
            have hng_r2 : arenaClauseGarb s_r2 p.toNat = false :=
              (hng_s2 p.toNat href_r).trans hng_rr
            have hpp := phase3_push_prep hcore_s2 href_r2 hng_r2
            have hwf_r2 := hcore_s2.arena.refs_wf p.toNat href_r2
            have hp3_eq : (p + 3#64).toNat = p.toNat + 3 :=
              bv64_add_toNat (by have := hwf_r2.2.1; have := hwf_r2.2.2.1; omega)
            have hp4_eq : (p + 4#64).toNat = p.toNat + 4 :=
              bv64_add_toNat (by have := hwf_r2.2.1; have := hwf_r2.2.2.1; omega)
            have hp3_lt : (p + 3#64).toNat < s_r2.arena.length := by
              rw [hp3_eq]; dsimp [s_r2]; rw [List.length_set, har_r_len]; omega
            have hp4_lt : (p + 4#64).toNat < s_r2.arena.length := by
              rw [hp4_eq]; dsimp [s_r2]; rw [List.length_set, har_r_len]
              have := hwf_r2.2.1; have := hwf_r2.2.2.1; omega
            c0_unmdata
            refine wp_store_sep (c0_store_arena_arena (s := s_r) (i := p + 1#64) 2#32
              h1_lt hmr) fun m_s2 hms2 => ?_
            have hms2' : (PlainMem c s_r2 ⋆ R) m_s2 := by simpa only [s_r2, h1_eq] using hms2
            pr_let
            refine wp_load_of (c0_load_arena_arena (i := p + 3#64) hp3_lt hms2') ?_; pr_let
            refine wp_load_of (c0_load_arena_arena (i := p + 4#64) hp4_lt hms2') ?_; pr_let
            refine wp_join_group (ts := [])
              (fun _ m_o => ∃ s_o : PlainState,
                s_o.LengthsOk c ∧ SameSwPre s0 s_o ∧ s_o.arena_garbage = 0#64 ∧
                s_o.heur.rel_trigger = s0.heur.rel_trigger ∧ s_o.arena_len = dst.toNat ∧
                (∀ i < s_o.trail_end, (s_o.trl[i]?.getD 0#32).toNat < 2 * c.mv) ∧
                (PlainMem c s_o ⋆ R) m_o) ?_ ?_
            · rintro _ ⟨⟩ m_o ⟨s_o, hlen_o, hsame_o, hag_o, hrt_o, hal_o, htrl_o, hmo⟩
              c0_unmdata; pr_steps!
              exact sweep_ret hQ (s1 := { s_o with oom := 1#64 }) hsame_o hag_o
                { hlen_o with } (Or.inr (Or.inr (Or.inr rfl))) hrt_o htrl_o
                (fun h => by rcases h with h | h <;> cases h) (fun _ h => by cases h)
                (fun h => by cases h) (fun h => by cases h) (by assumption)
            · intro J_oom hJ_oom
              c0_unmdata; pr_let
              have hpp' := hpp; simp only [hp3_eq, hp4_eq] at hpp' ⊢
              have hpt_eq : p.truncate 32 = BitVec.ofNat 32 p.toNat :=
                bv64_truncate32 (by omega)
              have hl1_m : s_r2.arena[p.toNat + 4] &&& 2147483647 =
                  s_r2.arena[p.toNat + 4] := hpp'.2.2.1
              have hl0_m : s_r2.arena[p.toNat + 3] &&& 2147483647 =
                  s_r2.arena[p.toNat + 3] := hpp'.2.2.2.1
              have hp_32 : BitVec.ofNat 32 p.toNat ≠ 0xFFFFFFFF#32 :=
                PlainReduceTactics.bv32_ne_allOnes_of_ult (by
                  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
                  exact hpp'.2.2.2.2.2.2.2.2)
              refine wp_call_of_spec _ _ (hWP (c.hdr, _, _, _, 2#32, ()) m_s2 _ X
                ⟨c, s_r2, R, rfl, hcore_s2.lengths, hcore_s2.watches.layout,
                  fun h => absurd h (by decide), fun _ => by
                    simp only [LeanQbe.T.Arg.val_var, LeanQbe.T.Arg.val_imm,
                      LeanQbe.T.lift2, hl1_m]
                    rw [show (BitVec.setWidth 32 p : BitVec 32) = p.truncate 32 from rfl,
                      hpt_eq]
                    exact ⟨hpp'.2.2.2.2.1, hp_32⟩,
                  hms2',
                  fun ok1 wv1 ws1 wl1 wu1 wso1 m_w1 hlen_w1 hlay_w1 hoth1 hok1 _ hm_w1 => ?_⟩)
              · pr_jnz
                · obtain ⟨hl0_v, _, hsz1, hpre1, hw1a, hw1b⟩ := hok1 (by assumption)
                  simp only [LeanQbe.T.Arg.val_var] at hl0_v hoth1 hsz1 hpre1 hw1b
                  simp only [LeanQbe.T.Arg.val_var, LeanQbe.T.Arg.val_imm,
                    LeanQbe.T.lift2, hl1_m] at hw1a
                  let s_w1 := pushWatchState s_r2 wv1 ws1 wso1 wl1 wu1
                  have hcw1 := pushClWatches_step_core hcore_s2 hlay_w1 hlen_w1
                    (cref := p.truncate 32) hpp'.2.2.2.2.2.2.1
                    (by rw [hpt_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
                        exact hpp'.2.2.2.2.2.2.2.2)
                    (by rw [hpt_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
                        exact href_r2)
                    hoth1 hl0_v hsz1 hpre1 hw1a (hw1b rfl)
                  c0_unmdata; pr_let
                  refine wp_call_of_spec _ _ (hWP (c.hdr, _, _, _, 2#32, ()) m_w1 _ X
                    ⟨c, s_w1, R, rfl, hcw1.lengths, hcw1.watches.layout,
                      fun h => absurd h (by decide), fun _ => by
                        simp only [LeanQbe.T.Arg.val_var, LeanQbe.T.Arg.val_imm,
                          LeanQbe.T.lift2, hl0_m]
                        rw [show (BitVec.setWidth 32 p : BitVec 32) = p.truncate 32 from rfl,
                          hpt_eq]
                        exact ⟨hpp'.2.2.2.2.2.1, hp_32⟩,
                      hm_w1,
                      fun ok2 wv2 ws2 wl2 wu2 wso2 m_w2 hlen_w2 hlay_w2 hoth2 hok2 _
                        hm_w2 => ?_⟩)
                  · pr_jnz
                    · obtain ⟨_, _, hsz2, hpre2, hw2a, hw2b⟩ := hok2 (by assumption)
                      simp only [LeanQbe.T.Arg.val_var] at hoth2 hsz2 hpre2 hw2b
                      simp only [LeanQbe.T.Arg.val_var, LeanQbe.T.Arg.val_imm,
                        LeanQbe.T.lift2, hl0_m] at hw2a
                      have hp2_lt_r : (p + 2#64).toNat < s_r.arena.length := by
                        rw [hp2_eq, har_r_len]; rw [hsw_r.2.2.2.2.1] at hwf_r; omega
                      obtain ⟨s_w2, hgt_n, hle_n, href_n, hsw2, hm_w2'⟩ := sw3_push_done hsw_r
                        href_r hp3_eq hp4_eq hp2_eq hpt_eq hm_w2
                        (List.getElem?_eq_getElem (by rw [← hp3_eq]; exact hp3_lt))
                        (List.getElem?_eq_getElem (by rw [← hp4_eq]; exact hp4_lt))
                        hlen_w1 hlay_w1 hoth1 hsz1 hpre1 hw1a (hw1b rfl) hlen_w2 hlay_w2 hoth2
                        hsz2 hpre2 hw2a (hw2b rfl) hp2_lt_r
                      have har2_eq : s_r.arena[(p + 2#64).toNat]'hp2_lt_r =
                          s_p.arena[(p + 2#64).toNat]'hp2_lt := by
                        apply BitVec.eq_of_toNat_eq
                        have h1 := hsz_rp; unfold arenaClauseSize at h1
                        rwa [← hp2_eq, List.getElem?_eq_getElem hp2_lt_r,
                          List.getElem?_eq_getElem hp2_lt, Option.getD_some,
                          Option.getD_some] at h1
                      rw [har2_eq] at hgt_n hle_n href_n
                      rw [show (3#64 : BitVec 64) = 3 from rfl] at hgt_n
                      c0_unmdata; pr_steps!
                      exact hJp3 _ m_w2 (by dsimp only; omega)
                        ⟨s_w2, by dsimp only; exact hle_n, by dsimp only; exact href_n,
                          hsw2, hm_w2'⟩
                    · exact hJ_oom () m_w2 ⟨pushWatchState s_w1 wv2 ws2 wso2 wl2 wu2,
                        hlen_w2, hsw_r.2.1, hsw_r.2.2.1, hsw_r.2.2.2.1, hsw_r.2.2.2.2.1,
                        hcw1.trail_lits_lt, hm_w2⟩
                · exact hJ_oom () m_w1 ⟨pushWatchState s_r2 wv1 ws1 wso1 wl1 wu1,
                    hlen_w1, hsw_r.2.1, hsw_r.2.2.1, hsw_r.2.2.2.1, hsw_r.2.2.2.2.1,
                    hcore_s2.trail_lits_lt, hm_w1⟩
          · intro J_rk hJ_rk; pr_jnz
            · c0_unmdata; pr_steps!; exact hJ_rk () m4 ⟨s_p, href_p, hsw_p, rfl, hm4⟩
            · pr_jnz
              · have hsz3 : 3 ≤ arenaClauseSize s_p p.toNat := hwf_p.2.1
                have hbd_p : p.toNat + 3 + arenaClauseSize s_p p.toNat ≤
                    s_p.arena.length := by
                  have := hwf_p.2.2.1; have := hwf_p.2.2.2.1; omega
                have hp3_eq : (p + 3#64).toNat = p.toNat + 3 := by bv_omega
                have hp3_len : (p + 3#64).toNat < s_p.arena.length := by omega
                have hl0_lt : s_p.arena[(p + 3#64).toNat].toNat < 2 * c.mv := by
                  refine hsw_p.1.arena.lits_lt p.toNat href_p hng_pr _ ?_
                  rw [mem_arenaClauseLits_iff hbd_p]
                  refine ⟨0, by omega, ?_⟩
                  simp only [hp3_eq, Nat.add_zero]
                c0_unmdata; pr_steps!
                refine sweep_call_lr hLR hlen_p hl0_lt hm4 fun r0 => ?_; pr_let
                refine wp_loop_inv (ts := [i32, i64, i32])
                  (fun v m_a => v.1.toNat < arenaClauseSize s_p p.toNat ∧
                    1 ≤ v.2.2.1.toNat ∧ v.2.2.1.toNat ≤ arenaClauseSize s_p p.toNat ∧
                    (PlainMem c s_p ⋆ R) m_a)
                  (fun v _ => arenaClauseSize s_p p.toNat - v.2.2.1.toNat) ?_ ?_
                · intro J_a hJ_a; c0_unmdata; pr_steps!
                  exact hJ_a (0#32, r0, 1#32, ()) m4 ⟨by dsimp only; bv_omega,
                    by dsimp only; decide, by dsimp only; bv_omega, hm4⟩
                · rintro J_a ⟨i0, r0_cur, i, ⟨⟩⟩ m_a ⟨hi0_lt, hi_lo, hi_hi, hma⟩ hJ_a
                  dsimp only at hi0_lt hi_lo hi_hi hJ_a
                  have hsz_e : s_p.arena[p.toNat + 2]?.getD 0#32 =
                      BitVec.ofNat 32 (arenaClauseSize s_p p.toNat) := by
                    apply BitVec.eq_of_toNat_eq; unfold arenaClauseSize
                    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt
                      (by have := (s_p.arena[p.toNat + 2]?.getD 0#32).isLt; omega)]
                  pr_jnz
                  · have hi_lt : i.toNat < arenaClauseSize s_p p.toNat := by
                      have hc' : i.toNat < (s_p.arena[p.toNat + 2]?.getD 0#32).toNat := by
                        rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
                        simpa only [Nat.mod_eq_of_lt
                          (show p.toNat + 2 < 2 ^ 64 by omega)] using hc
                      rw [hsz_e, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hc'
                      exact hc'
                    have hi1_eq : (i + 1#32).toNat = i.toNat + 1 := by bv_omega
                    have hk_eq : (p + 3#64 + i.setWidth 64).toNat =
                        p.toNat + 3 + i.toNat := by bv_omega
                    have hk_len : (p + 3#64 + i.setWidth 64).toNat < s_p.arena.length := by
                      rw [hk_eq]; omega
                    have hlk_lt : s_p.arena[(p + 3#64 + i.setWidth 64).toNat].toNat <
                        2 * c.mv := by
                      refine hsw_p.1.arena.lits_lt p.toNat href_p hng_pr _ ?_
                      rw [mem_arenaClauseLits_iff hbd_p]
                      exact ⟨i.toNat, hi_lt, by simp only [hk_eq]⟩
                    c0_unmdata; pr_steps!
                    refine sweep_call_lr hLR hlen_p hlk_lt hma fun rk => ?_; pr_let
                    refine wp_join_group (ts := [i32, i64])
                      (fun va ma' => va.1.toNat < arenaClauseSize s_p p.toNat ∧
                        (PlainMem c s_p ⋆ R) ma') ?_ ?_
                    · rintro _ ⟨i0', r0', ⟨⟩⟩ m_a' ⟨hi0', hma'⟩
                      c0_unmdata; pr_steps!
                      exact hJ_a (i0', r0', i + 1#32, ()) m_a' (by dsimp only; omega)
                        ⟨hi0', by dsimp only; omega, by dsimp only; omega, hma'⟩
                    · intro J_ia hJ_ia; pr_jnz <;> (c0_unmdata; pr_steps!)
                      · exact hJ_ia (i, rk, ()) m_a ⟨hi_lt, hma⟩
                      · exact hJ_ia (i0, r0_cur, ()) m_a ⟨hi0_lt, hma⟩
                  · refine wp_join_group (ts := [])
                      (fun _ m_sa => ∃ s_a : PlainState, p.toNat ∈ arenaClauseRefs s_a ∧
                        SwP3Inv c F0 s0 dst.toNat new_unit s_a ∧
                        arenaClauseSize s_a p.toNat = arenaClauseSize s_p p.toNat ∧
                        (PlainMem c s_a ⋆ R) m_sa) ?_ ?_
                    · rintro _ ⟨⟩ m_sa ⟨s_a, href_a, hsw_a, hsz_a, hma_s⟩
                      have hlen_a := hsw_a.1.lengths
                      have hwf_a := hsw_a.1.arena.refs_wf p.toNat href_a
                      have hng_ar := hsw_a.2.2.2.2.2.2.2.2 p.toNat href_a
                      have har_a_len := hlen_a.arena_len_arr
                      have har_a_le := hlen_a.arena_len_le
                      have hbd_a : p.toNat + 3 + arenaClauseSize s_a p.toNat ≤
                          s_a.arena.length := by
                        have := hwf_a.2.2.1; have := hwf_a.2.2.2.1; omega
                      have hp4_eq : (p + 4#64).toNat = p.toNat + 4 := by bv_omega
                      have hp4_a : (p + 4#64).toNat < s_a.arena.length := by
                        rw [hp4_eq]; rw [hsz_a] at hbd_a; omega
                      have hl1_a : s_a.arena[(p + 4#64).toNat].toNat < 2 * c.mv := by
                        refine hsw_a.1.arena.lits_lt p.toNat href_a hng_ar _ ?_
                        rw [mem_arenaClauseLits_iff hbd_a]
                        exact ⟨1, by rw [hsz_a]; omega, by simp only [hp4_eq]⟩
                      c0_unmdata; pr_steps!
                      refine sweep_call_lr hLR hlen_a hl1_a hma_s fun r1 => ?_; pr_let
                      refine wp_loop_inv (ts := [i32, i32, i64])
                        (fun v m_b => 2 ≤ v.1.toNat ∧
                          v.1.toNat ≤ arenaClauseSize s_a p.toNat ∧
                          v.2.1.toNat < arenaClauseSize s_a p.toNat ∧
                          (PlainMem c s_a ⋆ R) m_b)
                        (fun v _ => arenaClauseSize s_a p.toNat - v.1.toNat) ?_ ?_
                      · intro J_b hJ_b; c0_unmdata; pr_steps!
                        exact hJ_b (2#32, 1#32, r1, ()) m_sa ⟨by dsimp only; decide,
                          by dsimp only; bv_omega, by dsimp only; bv_omega, hma_s⟩
                      · rintro J_b ⟨ib, i1, r1_cur, ⟨⟩⟩ m_b ⟨hib_lo, hib_hi, hi1_lt, hmb⟩ hJ_b
                        dsimp only at hib_lo hib_hi hi1_lt hJ_b
                        have hp2_a : (p + 2#64).toNat = p.toNat + 2 := by bv_omega
                        have hp2_a_lt : (p + 2#64).toNat < s_a.arena.length := by
                          rw [hp2_a]; omega
                        have hsz_b : s_a.arena[p.toNat + 2]?.getD 0#32 =
                            BitVec.ofNat 32 (arenaClauseSize s_a p.toNat) := by
                          apply BitVec.eq_of_toNat_eq; unfold arenaClauseSize
                          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt
                            (by have := (s_a.arena[p.toNat + 2]?.getD 0#32).isLt; omega)]
                        pr_jnz
                        · have hib_lt : ib.toNat < arenaClauseSize s_a p.toNat := by
                            have hc' :
                                ib.toNat < (s_p.arena[p.toNat + 2]?.getD 0#32).toNat := by
                              rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
                              simpa only [Nat.mod_eq_of_lt
                                (show p.toNat + 2 < 2 ^ 64 by omega)] using hc
                            rw [hsz_e, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hc'
                            rw [hsz_a]; exact hc'
                          have hib1 : (ib + 1#32).toNat = ib.toNat + 1 := by bv_omega
                          have hkb_eq : (p + 3#64 + ib.setWidth 64).toNat =
                              p.toNat + 3 + ib.toNat := by bv_omega
                          have hkb_len : (p + 3#64 + ib.setWidth 64).toNat <
                              s_a.arena.length := by rw [hkb_eq]; omega
                          have hlb_lt : s_a.arena[(p + 3#64 + ib.setWidth 64).toNat].toNat <
                              2 * c.mv := by
                            refine hsw_a.1.arena.lits_lt p.toNat href_a hng_ar _ ?_
                            rw [mem_arenaClauseLits_iff hbd_a]
                            exact ⟨ib.toNat, hib_lt, by simp only [hkb_eq]⟩
                          c0_unmdata; pr_steps!
                          refine sweep_call_lr hLR hlen_a hlb_lt hmb fun rk => ?_; pr_let
                          refine wp_join_group (ts := [i32, i64])
                            (fun vb mb' => vb.1.toNat < arenaClauseSize s_a p.toNat ∧
                              (PlainMem c s_a ⋆ R) mb') ?_ ?_
                          · rintro _ ⟨i1', r1', ⟨⟩⟩ m_b' ⟨hi1', hmb'⟩
                            c0_unmdata; pr_steps!
                            exact hJ_b (ib + 1#32, i1', r1', ()) m_b' (by dsimp only; omega)
                              ⟨by dsimp only; omega, by dsimp only; omega, hi1', hmb'⟩
                          · intro J_ib hJ_ib; pr_jnz <;> (c0_unmdata; pr_steps!)
                            · exact hJ_ib (ib, rk, ()) m_b ⟨hib_lt, hmb⟩
                            · exact hJ_ib (i1, r1_cur, ()) m_b ⟨hi1_lt, hmb⟩
                        · refine wp_join_group (ts := [])
                            (fun _ m_sb => ∃ s_b : PlainState, p.toNat ∈ arenaClauseRefs s_b ∧
                              SwP3Inv c F0 s0 dst.toNat new_unit s_b ∧
                              arenaClauseSize s_b p.toNat = arenaClauseSize s_a p.toNat ∧
                              (PlainMem c s_b ⋆ R) m_sb) ?_ ?_
                          · rintro _ ⟨⟩ m_sb ⟨s_b, href_b, hsw_b, hsz_ba, hmb_s⟩
                            c0_unmdata; pr_steps!
                            exact hJ_rk () m_sb
                              ⟨s_b, href_b, hsw_b, hsz_ba.trans hsz_a, hmb_s⟩
                          · intro J_sb hJ_sb; pr_jnz
                            · have hpeq4 : (p + 4#64).toNat = p.toNat + 3 + 1 := by bv_omega
                              have hpeqi1 : (p + 3#64 + i1.setWidth 64).toNat =
                                  p.toNat + 3 + i1.toNat := by bv_omega
                              have h4a_lt : (p + 4#64).toNat < s_a.arena.length := by omega
                              have hkb_lt : (p + 3#64 + i1.setWidth 64).toNat <
                                  s_a.arena.length := by rw [hpeqi1]; omega
                              c0_unmdata; pr_let
                              refine wp_load_of (c0_load_arena_arena (s := s_a)
                                (i := p + 4#64) h4a_lt hmb) ?_; pr_let
                              refine wp_load_of (c0_load_arena_arena (s := s_a)
                                (i := p + 3#64 + i1.setWidth 64) hkb_lt hmb) ?_; pr_let
                              refine wp_store_sep (c0_store_arena_arena (s := s_a)
                                (i := p + 4#64) _ h4a_lt hmb) fun _ hm_sb1 => ?_; pr_let
                              refine wp_store_sep (c0_store_arena_arena (s := { s_a with
                                  arena := s_a.arena.set (p + 4#64).toNat
                                    (s_a.arena[(p + 3#64 + i1.setWidth 64).toNat]'hkb_lt) })
                                (i := p + 3#64 + i1.setWidth 64) _
                                (by dsimp only; rw [List.length_set]; exact hkb_lt) hm_sb1)
                                fun _ hm_sb2 => ?_; pr_let
                              obtain ⟨s_b, href_b, hsw_b, hsz_b, hmb_s⟩ := sw3_swap_step hsw_a
                                href_a (k1 := 1) (k2 := i1) (by rw [hsz_a]; omega) hi1_lt
                                h4a_lt hkb_lt hpeq4 hpeqi1 hm_sb2
                              exact hJ_sb () _ ⟨s_b, href_b, hsw_b, hsz_b, hmb_s⟩
                            · c0_unmdata; pr_steps!
                              exact hJ_sb () m_b ⟨s_a, href_a, hsw_a, rfl, hmb⟩
                    · intro J_sa hJ_sa; pr_jnz
                      · have hpeq3 : (p + 3#64).toNat = p.toNat + 3 + 0 := by bv_omega
                        have hpeqi0 : (p + 3#64 + i0.setWidth 64).toNat =
                            p.toNat + 3 + i0.toNat := by bv_omega
                        have h3p_lt : (p + 3#64).toNat < s_p.arena.length := by omega
                        have hka_lt : (p + 3#64 + i0.setWidth 64).toNat < s_p.arena.length :=
                          by rw [hpeqi0]; omega
                        c0_unmdata; pr_let
                        refine wp_load_of (c0_load_arena_arena (s := s_p)
                          (i := p + 3#64) h3p_lt hma) ?_; pr_let
                        refine wp_load_of (c0_load_arena_arena (s := s_p)
                          (i := p + 3#64 + i0.setWidth 64) hka_lt hma) ?_; pr_let
                        refine wp_store_sep (c0_store_arena_arena (s := s_p)
                          (i := p + 3#64) _ h3p_lt hma) fun _ hm_sw1 => ?_; pr_let
                        refine wp_store_sep (c0_store_arena_arena (s := { s_p with
                            arena := s_p.arena.set (p + 3#64).toNat
                              (s_p.arena[(p + 3#64 + i0.setWidth 64).toNat]'hka_lt) })
                          (i := p + 3#64 + i0.setWidth 64) _
                          (by dsimp only; rw [List.length_set]; exact hka_lt) hm_sw1)
                          fun _ hm_sw2 => ?_; pr_steps!
                        exact hJ_sa () _ (sw3_swap_step hsw_p href_p (k1 := 0) (k2 := i0)
                          (by omega) hi0_lt h3p_lt hka_lt hpeq3 hpeqi0 hm_sw2)
                      · c0_unmdata; pr_steps!
                        exact hJ_sa () m_a ⟨s_p, href_p, hsw_p, rfl, hma⟩
              · c0_unmdata; pr_steps!; exact hJ_rk () m4 ⟨s_p, href_p, hsw_p, rfl, hm4⟩
        · c0_unmdata; pr_let
          refine wp_join_group (ts := [i64])
            (fun vr mr => (new_unit = true ∧ vr.1 = 1#64 ∨
              new_unit = false ∧ vr.1 = 0#64) ∧ mr = m4) ?_ ?_
          · rintro _ ⟨r_ret, ⟨⟩⟩ mr ⟨hr, rfl⟩
            c0_unmdata; pr_steps!
            rcases hr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact sweep_ret hQ hsw_p.2.1 hsw_p.2.2.1 hlen_p (Or.inr (Or.inl rfl))
                hsw_p.2.2.2.1 hsw_p.1.trail_lits_lt (fun _ => ⟨hsw_p.1, hsw_p.2.2.2.2.2.1⟩)
                (fun _ h => by cases h) (fun _ => hsw_p.2.2.2.2.2.2.1 rfl)
                (fun h => by cases h) hm4
            · exact sweep_ret hQ hsw_p.2.1 hsw_p.2.2.1 hlen_p (Or.inl rfl) hsw_p.2.2.2.1
                hsw_p.1.trail_lits_lt (fun _ => ⟨hsw_p.1, hsw_p.2.2.2.2.2.1⟩)
                (fun hpos _ => hsw_p.2.2.2.2.2.2.2.1 hpos)
                (fun h => by cases h) (fun h => by cases h) hm4
          · intro Jret hJret; pr_jnz <;> (c0_unmdata; pr_steps!)
            · exact hJret (1#64, ()) m4 ⟨Or.inl ⟨by assumption, rfl⟩, rfl⟩
            · exact hJret (0#64, ()) m4 ⟨Or.inr ⟨by cases new_unit <;>
                first | rfl | contradiction, rfl⟩, rfl⟩

end PlainReduceHelpers

end

end LeanQbe.T.Examples.Kissat.Plain
