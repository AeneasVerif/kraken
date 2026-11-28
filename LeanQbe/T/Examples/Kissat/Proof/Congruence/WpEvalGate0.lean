/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Congruence.Inv
public import LeanQbe.T.Examples.Kissat.Src.Congruence

/-!
# Congruence Gate Re-Evaluation Shared AST & Frame Helpers (`WpEvalGate0`)

Transparent AST sub-expressions, core invariants (`EvCoreOk`, `EvHashGateOk`),
frame lemmas, and shared WP helpers (`ev_unit_wp`, `ev_equiv_enq2_wp`, `ev_trail_wp`)
for `full_cong_eval_gate`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Congruence

open Std Std.Sat
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src.Congruence
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Congruence.Spec
open Kraken.Bedrock2.Test

open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.Proof.Congruence.CongTactics

public section

/-! ## 0. Transparent AST Sub-Expressions -/

abbrev evL2 {V : Ty → Type} {L : List Ty → Type} {a b r : Ty}
    (c : OpCode [a, b] [r]) (x : Arg V a) (y : Arg V b)
    (k : V r → Expr V L [i64]) : Expr V L [i64] :=
  .let_ ⟨c, (x, (y, ()))⟩ fun (z, ()) => k z

abbrev evCmp32 {V : Ty → Type} {L : List Ty → Type}
    (op : CmpOp) (x y : Arg V i32) (k : V .bool → Expr V L [i64]) : Expr V L [i64] :=
  .let_ ⟨.cmp op i32 .bool rfl, (x, (y, ()))⟩ fun (z, ()) => k z

abbrev evCmp64 {V : Ty → Type} {L : List Ty → Type}
    (op : CmpOp) (x y : Arg V i64) (k : V .bool → Expr V L [i64]) : Expr V L [i64] :=
  .let_ ⟨.cmp op i64 .bool rfl, (x, (y, ()))⟩ fun (z, ()) => k z

abbrev evLd32 {V : Ty → Type} {L : List Ty → Type}
    (arr : V i64) (idx : V i32) (k : V i32 → Expr V L [i64]) : Expr V L [i64] :=
  .let_ ⟨.zext 32 64, (.var idx, ())⟩ fun (a, ()) =>
  .let_ ⟨.mul i64, (.var a, (.imm 4, ()))⟩ fun (b, ()) =>
  .let_ ⟨.add i64, (.var arr, (.var b, ()))⟩ fun (c, ()) =>
  .load i32 (.var c) k

abbrev evLdK32 {V : Ty → Type} {L : List Ty → Type}
    (arr : V i64) (imm : BitVec 32) (k : V i32 → Expr V L [i64]) : Expr V L [i64] :=
  .let_ ⟨.sext 32 64, (.imm imm, ())⟩ fun (a, ()) =>
  .let_ ⟨.mul i64, (.var a, (.imm 4, ()))⟩ fun (b, ()) =>
  .let_ ⟨.add i64, (.var arr, (.var b, ()))⟩ fun (c, ()) =>
  .load i32 (.var c) k

abbrev evLd8 {V : Ty → Type} {L : List Ty → Type}
    (arr : V i64) (idx : V i32) (k : V i8 → Expr V L [i64]) : Expr V L [i64] :=
  .let_ ⟨.zext 32 64, (.var idx, ())⟩ fun (a, ()) =>
  .let_ ⟨.add i64, (.var arr, (.var a, ()))⟩ fun (b, ()) =>
  .load i8 (.var b) k

abbrev evSgn0 {V : Ty → Type} {L : List Ty → Type}
    (op : CmpOp) (x : V i8) (k : V .bool → Expr V L [i64]) : Expr V L [i64] :=
  .let_ ⟨.trunc 32 8, (.imm 0, ())⟩ fun (a, ()) =>
  .let_ ⟨.sext 8 32, (.var x, ())⟩ fun (b, ()) =>
  .let_ ⟨.sext 8 32, (.var a, ())⟩ fun (c, ()) =>
  .let_ ⟨.cmp op i32 .bool rfl, (.var b, (.var c, ()))⟩ fun (d, ()) => k d

@[expose] def evUnitExpr {V : Ty → Type} {L : List Ty → Type}
    (h : V i64) (lit next_ep : V i32) (chgVal : Arg V .bool)
    (k : V .bool → Expr V L [i64]) : Expr V L [i64] :=
  .call "full_cong_unit_fold" (as := [i64, i32, i32]) (bs := [i64])
    (.var h, (.var lit, (.var next_ep, ()))) fun (r, ()) =>
  .let_ ⟨.cmp .eq i64 .bool rfl, (.var r, (.imm 2, ()))⟩ fun (v2, ()) =>
  .jnz (.var v2) (.ret (.imm 2, ())) (
    .group (sig := [[.bool]]) (fun (_J, ()) => .cons (fun (p, ()) => k p) .nil) fun (J, ()) =>
      .let_ ⟨.cmp .eq i64 .bool rfl, (.var r, (.imm 1, ()))⟩ fun (v1, ()) =>
      .jnz (.var v1) (.jump J (.imm true, ())) (.jump J (chgVal, ())))

@[expose] def evEquivEnq2bExpr {V : Ty → Type} {L : List Ty → Type}
    (h ctrl_off : V i64) (a b b_enq next_ep : V i32) (chgVal : Arg V .bool)
    (k : V .bool → Expr V L [i64]) : Expr V L [i64] :=
  .call "full_cong_equiv_fold" (as := [i64, i32, i32, i32]) (bs := [i64])
    (.var h, (.var a, (.var b, (.var next_ep, ())))) fun (r, ()) =>
  .let_ ⟨.cmp .eq i64 .bool rfl, (.var r, (.imm 2, ()))⟩ fun (v2, ()) =>
  .jnz (.var v2) (.ret (.imm 2, ())) (
    .group (sig := [[.bool]]) (fun (_J, ()) => .cons (fun (p, ()) => k p) .nil) fun (J, ()) =>
      .let_ ⟨.cmp .eq i64 .bool rfl, (.var r, (.imm 1, ()))⟩ fun (v1, ()) =>
      .jnz (.var v1) (
        .let_ ⟨.lshr i32, (.var a, (.imm 1, ()))⟩ fun (va, ()) =>
        .call "full_cong_enq_var" (as := [i64, i64, i32]) (bs := [])
          (.var h, (.var ctrl_off, (.var va, ()))) fun () =>
        .let_ ⟨.lshr i32, (.var b_enq, (.imm 1, ()))⟩ fun (vb, ()) =>
        .call "full_cong_enq_var" (as := [i64, i64, i32]) (bs := [])
          (.var h, (.var ctrl_off, (.var vb, ()))) fun () =>
        .jump J (.imm true, ())
      ) (.jump J (chgVal, ())))

@[expose] def evEquivEnq2Expr {V : Ty → Type} {L : List Ty → Type}
    (h ctrl_off : V i64) (a b next_ep : V i32) (chgVal : Arg V .bool)
    (k : V .bool → Expr V L [i64]) : Expr V L [i64] :=
  evEquivEnq2bExpr h ctrl_off a b b next_ep chgVal k

@[expose] def evTrailExpr {V : Ty → Type} {L : List Ty → Type}
    (h ctrl_off ld3 ld9 ld36 : V i64) (p46 p47 : V .bool) : Expr V L [i64] :=
  .group (sig := [[i64]]) (fun Js => .cons (fun (p49, ()) =>
  evL2 (.add i64) (.var h) (.imm 144) fun v50 => .load i64 (.var v50) fun ld51 =>
  evCmp64 .ult (.var p49) (.var ld51) fun v52 => .jnz (.var v52) (
  evL2 (.mul i64) (.var p49) (.imm 4) fun v53 => evL2 (.add i64) (.var ld9) (.var v53) fun v54 =>
  .load i32 (.var v54) fun ld55 => evL2 (.lshr i32) (.var ld55) (.imm 1) fun v56 =>
  .call "full_cong_enq_var" (as := [i64, i64, i32]) (bs := []) (.var h, (.var ctrl_off, (.var
    v56, ()))) fun () =>
  .call "full_cong_find" (as := [i64, i32]) (bs := [i32]) (.var ld3, (.var ld55, ())) fun (r57,
    ()) => evL2 (.lshr i32) (.var r57) (.imm 1) fun v58 =>
  .call "full_cong_enq_var" (as := [i64, i64, i32]) (bs := []) (.var h, (.var ctrl_off, (.var
    v58, ()))) fun () => evL2 (.add i64) (.var p49) (.imm 1) fun v59 => .jump Js.fst (.var v59, ())
  ) ( evL2 (.add i64) (.var h) (.imm 1024) fun v53 => .load i64 (.var v53) fun ld54 =>
  evCmp64 .ne (.var ld54) (.imm 0) fun v55 => .jnz (.var v55) ( .ret (.imm 2, ()) ) (
  .group (sig := [[i64]]) (fun (_J56, ()) => .cons (fun (p57, ()) =>
  .group (sig := [[i64]]) (fun (_J58, ()) => .cons (fun (p59, ()) =>
  evL2 (.or i64) (.var p57) (.var p59) fun v60 => .ret (.var v60, ()) ) .nil) fun (J58, ()) =>
  .jnz (.var p47) ( .jump J58 (.imm 4, ()) ) ( .jump J58 (.imm 0, ()) ) ) .nil) fun (J56, ()) =>
  .jnz (.var p46) ( .jump J56 (.imm 1, ()) ) ( .jump J56 (.imm 0, ()) ) ) )
  ) .nil) fun Js => .jump Js.fst (.var ld36, ())

@[expose] def evHashExpr {V : Ty → Type} {L : List Ty → Type}
    (h g ht_off ht_sz ctrl_off ld1 ld3 ld5 v34 : V i64) (next_ep p21 p38 p39 p40 p41 : V i32)
    (p42 p43 : V .bool) (J44 : L [i32, .bool, .bool]) : Expr V L [i64] :=
  .jnz (.var p42) ( evL2 (.add i64) (.var h) (.imm 1024) fun v45 =>
  .load i64 (.var v45) fun ld46 => evCmp64 .eq (.var ld46) (.imm 0) fun v47 => .jnz (.var v47) (
  .let_ ⟨.zext 32 64, (.var p40, ())⟩ fun (v48, ()) =>
  evL2 (.mul i64) (.var v48) (.imm 2654435761) fun v49 =>
  .let_ ⟨.zext 32 64, (.var p41, ())⟩ fun (v50, ()) =>
  evL2 (.add i64) (.var v49) (.var v50) fun v51 =>
  .group (sig := [[i32, i64]]) (fun (J52, ()) => .cons (fun (p53, (p54, ())) =>
  evCmp32 .ult (.var p53) (.var p41) fun v55 => .jnz (.var v55) (
  evL2 (.mul i64) (.var p54) (.imm 2246822519) fun v56 => evLd32 ld5 p53 fun ld60 =>
  .let_ ⟨.zext 32 64, (.var ld60, ())⟩ fun (v61, ()) =>
  evL2 (.add i64) (.var v56) (.var v61) fun v62 => evL2 (.add i64) (.var v62) (.imm 1) fun v63 =>
  evL2 (.add i32) (.var p53) (.imm 1) fun v64 => .jump J52 (.var v64, (.var v63, ())) ) (
  evL2 (.sub i64) (.var ht_sz) (.imm 1) fun v56 =>
  evL2 (.and i64) (.var p54) (.var v56) fun v57 =>
  .group (sig := [[.bool, .bool, i64, i64, .bool]]) (fun (_J58, ()) => .cons (fun (p59, (p60,
    (_p61, (_p62, (_p63, ()))))) => .jump J44 (.var p53, (.var p59, (.var p60, ())))
  ) .nil) fun (J58, ()) =>
  .group (sig := [[i64, i64, .bool]]) (fun (J59, ()) => .cons (fun (p60, (p61, (p62, ()))) =>
  evCmp64 .ult (.var p61) (.imm 128) fun v63 => .jnz (.var v63) (
  evL2 (.add i64) (.var ht_off) (.var p60) fun v64 =>
  evL2 (.mul i64) (.var v64) (.imm 4) fun v65 => evL2 (.add i64) (.var ld1) (.var v65) fun v66 =>
  .load i32 (.var v66) fun ld67 => evCmp32 .eq (.var ld67) (.imm 4294967295) fun v68 =>
  .jnz (.var v68) (
  .group (sig := [[]]) (fun (_J69, ()) => .cons (fun () =>
  .jump J58 (.var p43, (.imm true, (.var p60, (.var p61, (.var p62, ())))))
  ) .nil) fun (J69, ()) => .jnz (.var p62) ( .jump J69 () ) (
  evCmp32 .eq (.var p40) (.var p21) fun v70 => .jnz (.var v70) (
  evL2 (.add i64) (.var h) (.imm 1144) fun v71 => .load i64 (.var v71) fun ld72 =>
  evCmp64 .ult (.var ld72) (.var v34) fun v73 => .jnz (.var v73) (
  evL2 (.add i64) (.var ht_off) (.var p60) fun v74 =>
  evL2 (.mul i64) (.var v74) (.imm 4) fun v75 => evL2 (.add i64) (.var ld1) (.var v75) fun v76 =>
  .let_ ⟨.trunc 64 32, (.var g, ())⟩ fun (v77, ()) => .store (t := i32) (.var v77) (.var v76) (
  evL2 (.add i64) (.var h) (.imm 1144) fun v78 => .load i64 (.var v78) fun ld79 =>
  evL2 (.add i64) (.var ld79) (.imm 1) fun v80 => evL2 (.add i64) (.var h) (.imm 1144) fun v81 =>
  .store (t := i64) (.var v80) (.var v81) ( .jump J69 ())) ) ( .jump J69 () ) ) ( .jump J69 () ) )
  ) ( .let_ ⟨.trunc 64 32, (.var g, ())⟩ fun (v69, ()) =>
  evCmp32 .eq (.var ld67) (.var v69) fun v70 => .jnz (.var v70) (
  evL2 (.add i64) (.var p60) (.imm 1) fun v71 => evL2 (.sub i64) (.var ht_sz) (.imm 1) fun v72 =>
  evL2 (.and i64) (.var v71) (.var v72) fun v73 => evL2 (.add i64) (.var p61) (.imm 1) fun v74 =>
  .jump J59 (.var v73, (.var v74, (.imm true, ()))) ) (
  .let_ ⟨.zext 32 64, (.var ld67, ())⟩ fun (v71, ()) =>
  evL2 (.add i64) (.var v71) (.imm 1) fun v72 => evL2 (.mul i64) (.var v72) (.imm 4) fun v73 =>
  evL2 (.add i64) (.var ld1) (.var v73) fun v74 => .load i32 (.var v74) fun ld75 =>
  evL2 (.lshr i32) (.var ld75) (.imm 28) fun v76 =>
  .group (sig := [[i32]]) (fun (_J77, ()) => .cons (fun (p78, ()) =>
  .group (sig := [[.bool, .bool]]) (fun (_J79, ()) => .cons (fun (_p80, (_p81, ())) =>
  evL2 (.add i64) (.var p60) (.imm 1) fun v82 => evL2 (.sub i64) (.var ht_sz) (.imm 1) fun v83 =>
  evL2 (.and i64) (.var v82) (.var v83) fun v84 => evL2 (.add i64) (.var p61) (.imm 1) fun v85 =>
  .jump J59 (.var v84, (.var v85, (.var p62, ()))) ) .nil) fun (J79, ()) =>
  evCmp32 .eq (.var p78) (.var p40) fun v80 => .jnz (.var v80) ( evLd32 ld1 ld67 fun ld84 =>
  .group (sig := [[.bool, i32]]) (fun (_J85, ()) => .cons (fun (p86, (p87, ())) =>
  .jnz (.var p86) (
  .call "full_cong_equiv_fold" (as := [i64, i32, i32, i32]) (bs := [i64]) (.var h, (.var p38,
    (.var p87, (.var next_ep, ())))) fun (r88, ()) => evCmp64 .eq (.var r88) (.imm 2) fun v89 =>
  .jnz (.var v89) ( .ret (.imm 2, ()) ) (
  .group (sig := [[.bool]]) (fun (_J90, ()) => .cons (fun (p91, ()) =>
  .jump J58 (.var p91, (.imm false, (.var p60, (.var p61, (.var p62, ())))))
  ) .nil) fun (J90, ()) => evCmp64 .eq (.var r88) (.imm 1) fun v91 => .jnz (.var v91) (
  evL2 (.lshr i32) (.var p38) (.imm 1) fun v92 =>
  .call "full_cong_enq_var" (as := [i64, i64, i32]) (bs := []) (.var h, (.var ctrl_off, (.var
    v92, ()))) fun () => evL2 (.lshr i32) (.var p87) (.imm 1) fun v93 =>
  .call "full_cong_enq_var" (as := [i64, i64, i32]) (bs := []) (.var h, (.var ctrl_off, (.var
    v93, ()))) fun () =>
  .call "full_cong_find" (as := [i64, i32]) (bs := [i32]) (.var ld3, (.var p38, ())) fun (r94,
    ()) => evL2 (.lshr i32) (.var r94) (.imm 1) fun v95 =>
  .call "full_cong_enq_var" (as := [i64, i64, i32]) (bs := []) (.var h, (.var ctrl_off, (.var
    v95, ()))) fun () =>
  .call "full_cong_find" (as := [i64, i32]) (bs := [i32]) (.var ld3, (.var p87, ())) fun (r96,
    ()) => evL2 (.lshr i32) (.var r96) (.imm 1) fun v97 =>
  .call "full_cong_enq_var" (as := [i64, i64, i32]) (bs := []) (.var h, (.var ctrl_off, (.var
    v97, ()))) fun () => .jump J90 (.imm true, ()) ) ( .jump J90 (.var p43, ()) ) ) ) (
  .jump J79 (.var p43, (.imm true, ())) ) ) .nil) fun (J85, ()) =>
  evCmp32 .eq (.var p40) (.imm 0) fun v86 => .jnz (.var v86) (
  .call "full_cong_and_match" (as := [i64, i32, i32]) (bs := [.bool]) (.var h, (.var ld67, (.var
    p41, ()))) fun (r87, ()) => .jump J85 (.var r87, (.var ld84, ())) ) (
  .group (sig := [[.bool, i32]]) (fun (_J87, ()) => .cons (fun (p88, (p89, ())) =>
  .jump J85 (.var p88, (.var p89, ())) ) .nil) fun (J87, ()) =>
  evCmp32 .eq (.var p40) (.imm 1) fun v88 => .jnz (.var v88) (
  .call "full_cong_xor_match" (as := [i64, i32, i32]) (bs := [i32]) (.var h, (.var ld67, (.var
    p41, ()))) fun (r89, ()) =>
  .group (sig := [[.bool, i32]]) (fun (_J90, ()) => .cons (fun (p91, (p92, ())) =>
  .jump J87 (.var p91, (.var p92, ())) ) .nil) fun (J90, ()) =>
  evCmp32 .ne (.var r89) (.imm 4294967295) fun v91 => .jnz (.var v91) (
  .jump J90 (.imm true, (.var r89, ())) ) ( .jump J90 (.imm false, (.var ld84, ())) ) ) (
  .group (sig := [[.bool, i32]]) (fun (_J89, ()) => .cons (fun (p90, (p91, ())) =>
  .jump J87 (.var p90, (.var p91, ())) ) .nil) fun (J89, ()) =>
  evCmp32 .eq (.var p40) (.imm 2) fun v90 => .jnz (.var v90) (
  evL2 (.and i32) (.var ld75) (.imm 255) fun v91 => evCmp32 .eq (.var v91) (.imm 3) fun v92 =>
  .jnz (.var v92) ( .let_ ⟨.zext 32 64, (.var ld67, ())⟩ fun (v93, ()) =>
  evL2 (.add i64) (.var v93) (.imm 2) fun v94 => evL2 (.mul i64) (.var v94) (.imm 4) fun v95 =>
  evL2 (.add i64) (.var ld1) (.var v95) fun v96 => .load i32 (.var v96) fun ld97 =>
  .call "full_cong_find" (as := [i64, i32]) (bs := [i32]) (.var ld3, (.var ld97, ())) fun (r98,
    ()) => .let_ ⟨.zext 32 64, (.var ld67, ())⟩ fun (v99, ()) =>
  evL2 (.add i64) (.var v99) (.imm 3) fun v100 => evL2 (.mul i64) (.var v100) (.imm 4) fun v101 =>
  evL2 (.add i64) (.var ld1) (.var v101) fun v102 => .load i32 (.var v102) fun ld103 =>
  .call "full_cong_find" (as := [i64, i32]) (bs := [i32]) (.var ld3, (.var ld103, ())) fun (r104,
    ()) => .let_ ⟨.zext 32 64, (.var ld67, ())⟩ fun (v105, ()) =>
  evL2 (.add i64) (.var v105) (.imm 4) fun v106 =>
  evL2 (.mul i64) (.var v106) (.imm 4) fun v107 =>
  evL2 (.add i64) (.var ld1) (.var v107) fun v108 => .load i32 (.var v108) fun ld109 =>
  .call "full_cong_find" (as := [i64, i32]) (bs := [i32]) (.var ld3, (.var ld109, ())) fun (r110,
    ()) =>
  .group (sig := [[i32, i32, i32]]) (fun (_J111, ()) => .cons (fun (p112, (p113, (p114, ()))) =>
  .group (sig := [[i32, i32, i32]]) (fun (_J115, ()) => .cons (fun (p116, (p117, (p118, ()))) =>
  .group (sig := [[.bool]]) (fun (_J119, ()) => .cons (fun (p120, ()) =>
  .jump J89 (.var p120, (.var p116, ())) ) .nil) fun (J119, ()) => evLdK32 ld5 0 fun ld123 =>
  evCmp32 .eq (.var p112) (.var ld123) fun v124 => .jnz (.var v124) ( evLdK32 ld5 1 fun ld128 =>
  evCmp32 .eq (.var p117) (.var ld128) fun v129 => .jnz (.var v129) ( evLdK32 ld5 2 fun ld133 =>
  evCmp32 .eq (.var p118) (.var ld133) fun v134 => .jnz (.var v134) ( .jump J119 (.imm true, ())
  ) ( .jump J119 (.imm false, ()) ) ) ( .jump J119 (.imm false, ()) ) ) (
  .jump J119 (.imm false, ()) ) ) .nil) fun (J115, ()) =>
  evL2 (.and i32) (.var p113) (.imm 1) fun v116 => evCmp32 .ne (.var v116) (.imm 0) fun v117 =>
  .jnz (.var v117) ( evL2 (.xor i32) (.var ld84) (.imm 1) fun v118 =>
  evL2 (.xor i32) (.var p113) (.imm 1) fun v119 =>
  evL2 (.xor i32) (.var p114) (.imm 1) fun v120 =>
  .jump J115 (.var v118, (.var v119, (.var v120, ()))) ) (
  .jump J115 (.var ld84, (.var p113, (.var p114, ()))) ) ) .nil) fun (J111, ()) =>
  evL2 (.and i32) (.var r98) (.imm 1) fun v112 => evCmp32 .ne (.var v112) (.imm 0) fun v113 =>
  .jnz (.var v113) ( evL2 (.xor i32) (.var r98) (.imm 1) fun v114 =>
  .jump J111 (.var v114, (.var r110, (.var r104, ()))) ) (
  .jump J111 (.var r98, (.var r104, (.var r110, ()))) ) ) (
  .jump J89 (.imm false, (.var ld84, ())) ) ) ( .jump J89 (.imm false, (.var ld84, ())) ) ) ) ) (
  .jump J79 (.var p43, (.imm true, ())) ) ) .nil) fun (J77, ()) =>
  evCmp32 .eq (.var v76) (.imm 3) fun v78 => .jnz (.var v78) ( .jump J77 (.imm 0, ()) ) (
  .jump J77 (.var v76, ()) ) ) ) ) (
  .jump J58 (.var p43, (.imm true, (.var p60, (.var p61, (.var p62, ()))))) )
  ) .nil) fun (J59, ()) => .jump J59 (.var v57, (.imm 0, (.imm false, ()))) )
  ) .nil) fun (J52, ()) => .jump J52 (.imm 0, (.var v51, ())) ) (
  .jump J44 (.var p39, (.var p43, (.imm false, ()))) ) ) (
  .jump J44 (.var p39, (.var p43, (.imm false, ()))) )

@[expose] def evTag0Expr {V : Ty → Type} {L : List Ty → Type}
    (h ctrl_off ld5 ld7 : V i64) (next_ep p19 p21 r28 : V i32)
    (J37 : L [i32, i32, i32, i32, .bool, .bool]) : Expr V L [i64] :=
  .group (sig := [[i32, .bool, i32]]) (fun (_J39, ()) => .cons (fun (p40, (p41, (p42, ()))) =>
  .group (sig := [[i32, .bool, .bool]]) (fun (_J43, ()) => .cons (fun (p44, (p45, (p46, ()))) =>
  .jump J37 (.var r28, (.var p40, (.var p21, (.var p44, (.var p45, (.var p46, ()))))))
  ) .nil) fun (J43, ()) => .jnz (.var p41) ( evL2 (.xor i32) (.var r28) (.imm 1) fun v44 =>
  evUnitExpr h v44 next_ep (.imm false) (fun p48 =>
  .jump J43 (.var p19, (.imm false, (.var p48, ()))) ) ) (
  .group (sig := [[i32, .bool, .bool]]) (fun (_J44, ()) => .cons (fun (p45, (p46, (p47, ()))) =>
  .jump J43 (.var p45, (.var p46, (.var p47, ()))) ) .nil) fun (J44, ()) =>
  evCmp32 .eq (.var p42) (.imm 0) fun v45 => .jnz (.var v45) (
  evUnitExpr h r28 next_ep (.imm false) (fun p49 =>
  .jump J44 (.var p19, (.imm false, (.var p49, ()))) ) ) (
  .group (sig := [[]]) (fun (_J46, ()) => .cons (fun () =>
  .group (sig := [[.bool, i32, i32]]) (fun (_J47, ()) => .cons (fun (p48, (p49, (_p50, ()))) =>
  .group (sig := [[i32, .bool, .bool]]) (fun (_J51, ()) => .cons (fun (p52, (p53, (p54, ()))) =>
  .jump J44 (.var p52, (.var p53, (.var p54, ()))) ) .nil) fun (J51, ()) => .jnz (.var p48) (
  evL2 (.xor i32) (.var r28) (.imm 1) fun v52 => evUnitExpr h v52 next_ep (.imm false) (fun p56 =>
  .jump J51 (.var p19, (.imm false, (.var p56, ()))) ) ) (
  .group (sig := [[i32, .bool, .bool]]) (fun (_J52, ()) => .cons (fun (p53, (p54, (p55, ()))) =>
  .jump J51 (.var p53, (.var p54, (.var p55, ()))) ) .nil) fun (J52, ()) =>
  evCmp32 .eq (.var p49) (.imm 0) fun v53 => .jnz (.var v53) (
  evUnitExpr h r28 next_ep (.imm false) (fun p57 =>
  .jump J52 (.var p19, (.imm false, (.var p57, ()))) ) ) (
  .group (sig := [[i32, .bool, .bool]]) (fun (_J54, ()) => .cons (fun (p55, (p56, (p57, ()))) =>
  .jump J52 (.var p55, (.var p56, (.var p57, ()))) ) .nil) fun (J54, ()) =>
  evCmp32 .eq (.var p49) (.imm 1) fun v55 => .jnz (.var v55) ( evLdK32 ld5 0 fun ld59 =>
  evEquivEnq2Expr h ctrl_off r28 ld59 next_ep (.imm false) (fun p63 =>
  .jump J54 (.var p19, (.imm false, (.var p63, ()))) ) ) (
  .group (sig := [[i32, .bool, .bool]]) (fun (_J56, ()) => .cons (fun (p57, (p58, (p59, ()))) =>
  .jump J54 (.var p57, (.var p58, (.var p59, ()))) ) .nil) fun (J56, ()) =>
  evLd8 ld7 r28 fun ld59 => evSgn0 .sgt ld59 fun v63 => .jnz (.var v63) (
  .group (sig := [[.bool, i32]]) (fun (J64, ()) => .cons (fun (p65, (p66, ())) =>
  evCmp32 .ult (.var p66) (.var p49) fun v67 => .jnz (.var v67) ( evLd32 ld5 p66 fun ld71 =>
  evUnitExpr h ld71 next_ep (.var p65) (fun p75 =>
  evL2 (.add i32) (.var p66) (.imm 1) fun v76 => .jump J64 (.var p75, (.var v76, ())) ) ) (
  .jump J56 (.var p19, (.imm false, (.var p65, ()))) ) ) .nil) fun (J64, ()) =>
  .jump J64 (.imm false, (.imm 0, ())) ) ( .jump J56 (.var p49, (.imm true, (.imm false, ()))) ) )
  ) ) ) .nil) fun (J47, ()) =>
  .group (sig := [[i32, i32]]) (fun (J48, ()) => .cons (fun (p49, (p50, ())) =>
  evCmp32 .ult (.var p50) (.var p42) fun v51 => .jnz (.var v51) ( evLd32 ld5 p50 fun ld55 =>
  evL2 (.add i32) (.var p50) (.imm 1) fun v56 => evL2 (.xor i32) (.var r28) (.imm 1) fun v57 =>
  evCmp32 .eq (.var ld55) (.var v57) fun v58 => .jnz (.var v58) (
  .jump J47 (.imm true, (.var p49, (.var v56, ()))) ) (
  .group (sig := [[.bool, i32]]) (fun (_J59, ()) => .cons (fun (_p60, (p61, ())) =>
  .jump J48 (.var p61, (.var v56, ())) ) .nil) fun (J59, ()) =>
  evCmp32 .eq (.var p49) (.imm 0) fun v60 => .jnz (.var v60) (
  .let_ ⟨.sext 32 64, (.imm 0, ())⟩ fun (v61, ()) =>
  evL2 (.mul i64) (.var v61) (.imm 4) fun v62 => evL2 (.add i64) (.var ld5) (.var v62) fun v63 =>
  .store (t := i32) (.var ld55) (.var v63) ( .jump J59 (.imm false, (.imm 1, ()))) ) (
  evL2 (.sub i32) (.var p49) (.imm 1) fun v61 => evLd32 ld5 v61 fun ld65 =>
  evCmp32 .eq (.var ld55) (.var ld65) fun v66 => .jnz (.var v66) (
  .jump J48 (.var p49, (.var v56, ())) ) ( evL2 (.xor i32) (.var ld65) (.imm 1) fun v67 =>
  evCmp32 .eq (.var ld55) (.var v67) fun v68 => .jnz (.var v68) (
  .jump J47 (.imm true, (.var p49, (.var v56, ()))) ) (
  .let_ ⟨.zext 32 64, (.var p49, ())⟩ fun (v69, ()) =>
  evL2 (.mul i64) (.var v69) (.imm 4) fun v70 => evL2 (.add i64) (.var ld5) (.var v70) fun v71 =>
  .store (t := i32) (.var ld55) (.var v71) ( evL2 (.add i32) (.var p49) (.imm 1) fun v72 =>
  .jump J59 (.imm false, (.var v72, ()))) ) ) ) ) ) (
  .jump J47 (.imm false, (.var p49, (.var p50, ()))) ) ) .nil) fun (J48, ()) =>
  .jump J48 (.imm 0, (.imm 0, ())) ) .nil) fun (J46, ()) =>
  evCmp32 .ugt (.var p42) (.imm 1) fun v47 => .jnz (.var v47) (
  .call "full_sort_u32" (as := [i64, i32]) (bs := []) (.var ld5, (.var p42, ())) fun () =>
  .jump J46 () ) ( .jump J46 () ) ) ) ) .nil) fun (J39, ()) =>
  .group (sig := [[i32, i32]]) (fun (J40, ()) => .cons (fun (p41, (p42, ())) =>
  evCmp32 .ult (.var p41) (.var p19) fun v43 => .jnz (.var v43) ( evLd32 ld5 p41 fun ld47 =>
  evLd8 ld7 ld47 fun ld50 => evSgn0 .slt ld50 fun v54 => .jnz (.var v54) (
  .jump J39 (.var p41, (.imm true, (.var p42, ()))) ) (
  .group (sig := [[i32]]) (fun (_J55, ()) => .cons (fun (p56, ()) =>
  evL2 (.add i32) (.var p41) (.imm 1) fun v57 => .jump J40 (.var v57, (.var p56, ()))
  ) .nil) fun (J55, ()) => evSgn0 .eq ld50 fun v59 => .jnz (.var v59) (
  .let_ ⟨.zext 32 64, (.var p42, ())⟩ fun (v60, ()) =>
  evL2 (.mul i64) (.var v60) (.imm 4) fun v61 => evL2 (.add i64) (.var ld5) (.var v61) fun v62 =>
  .store (t := i32) (.var ld47) (.var v62) ( evL2 (.add i32) (.var p42) (.imm 1) fun v63 =>
  .jump J55 (.var v63, ())) ) ( .jump J55 (.var p42, ()) ) ) ) (
  .jump J39 (.var p41, (.imm false, (.var p42, ()))) ) ) .nil) fun (J40, ()) =>
  .jump J40 (.imm 0, (.imm 0, ()))

@[expose] def evTag2Expr {V : Ty → Type} {L : List Ty → Type}
    (h ctrl_off ld5 ld7 : V i64) (next_ep p19 p21 r28 p30 : V i32)
    (J39 : L [i32, i32, i32, i32, .bool, .bool]) : Expr V L [i64] :=
  .group (sig := [[i32, i32, i32, .bool, .bool]]) (fun (_J41, ()) => .cons (fun (p42, (p43, (p44,
    (p45, (p46, ()))))) =>
  .jump J39 (.var p42, (.var p30, (.var p43, (.var p44, (.var p45, (.var p46, ()))))))
  ) .nil) fun (J41, ()) => evCmp32 .eq (.var p21) (.imm 2) fun v42 => .jnz (.var v42) (
  evCmp32 .eq (.var p19) (.imm 3) fun v43 => .jnz (.var v43) ( evLdK32 ld5 0 fun ld47 =>
  evLdK32 ld5 1 fun ld51 => evLdK32 ld5 2 fun ld55 => evLd8 ld7 ld47 fun ld58 =>
  evLd8 ld7 ld51 fun ld61 => evLd8 ld7 ld55 fun ld64 =>
  .group (sig := [[i32, i32, i32, .bool, .bool, i32, i32, i32]]) (fun (_J65, ()) => .cons (fun
    (p66, (p67, (p68, (p69, (p70, (_p71, (_p72, (_p73, ())))))))) =>
  .jump J41 (.var p66, (.var p67, (.var p68, (.var p69, (.var p70, ())))))
  ) .nil) fun (J65, ()) => evSgn0 .ne ld58 fun v69 => .jnz (.var v69) (
  .group (sig := [[i32]]) (fun (_J70, ()) => .cons (fun (p71, ()) =>
  evEquivEnq2Expr h ctrl_off r28 p71 next_ep (.imm false) (fun p75 =>
  .jump J65 (.var r28, (.var p21, (.var p19, (.imm false, (.var p75, (.var ld47, (.var ld51,
    (.var ld55, ())))))))) ) ) .nil) fun (J70, ()) => evSgn0 .sgt ld58 fun v74 =>
  .jnz (.var v74) ( .jump J70 (.var ld51, ()) ) ( .jump J70 (.var ld55, ()) ) ) (
  .group (sig := [[i32, i32, i32, .bool, .bool, i32, i32, i32]]) (fun (_J70, ()) => .cons (fun
    (p71, (p72, (p73, (p74, (p75, (p76, (p77, (p78, ())))))))) =>
  .jump J65 (.var p71, (.var p72, (.var p73, (.var p74, (.var p75, (.var p76, (.var p77, (.var
    p78, ())))))))) ) .nil) fun (J70, ()) => evCmp32 .eq (.var ld51) (.var ld55) fun v71 =>
  .jnz (.var v71) ( evEquivEnq2Expr h ctrl_off r28 ld51 next_ep (.imm false) (fun p75 =>
  .jump J70 (.var r28, (.var p21, (.var p19, (.imm false, (.var p75, (.var ld47, (.var ld51,
    (.var ld55, ())))))))) ) ) (
  .group (sig := [[i32, i32, i32, .bool, .bool, i32, i32, i32]]) (fun (_J72, ()) => .cons (fun
    (p73, (p74, (p75, (p76, (p77, (p78, (p79, (p80, ())))))))) =>
  .jump J70 (.var p73, (.var p74, (.var p75, (.var p76, (.var p77, (.var p78, (.var p79, (.var
    p80, ())))))))) ) .nil) fun (J72, ()) =>
  .group (sig := [[]]) (fun (_J73, ()) => .cons (fun () =>
  .group (sig := [[i32, i32, i32, .bool, .bool, i32, i32, i32]]) (fun (_J74, ()) => .cons (fun
    (p75, (p76, (p77, (p78, (p79, (p80, (p81, (p82, ())))))))) =>
  .jump J72 (.var p75, (.var p76, (.var p77, (.var p78, (.var p79, (.var p80, (.var p81, (.var
    p82, ())))))))) ) .nil) fun (J74, ()) =>
  .group (sig := [[]]) (fun (_J75, ()) => .cons (fun () =>
  .group (sig := [[i32, i32, i32, .bool, .bool, i32, i32, i32]]) (fun (_J76, ()) => .cons (fun
    (p77, (p78, (p79, (p80, (p81, (p82, (p83, (p84, ())))))))) =>
  .jump J74 (.var p77, (.var p78, (.var p79, (.var p80, (.var p81, (.var p82, (.var p83, (.var
    p84, ())))))))) ) .nil) fun (J76, ()) =>
  .group (sig := [[]]) (fun (_J77, ()) => .cons (fun () =>
  .group (sig := [[i32, i32, i32, .bool, .bool, i32, i32, i32]]) (fun (_J78, ()) => .cons (fun
    (p79, (p80, (p81, (p82, (p83, (p84, (p85, (p86, ())))))))) =>
  .jump J76 (.var p79, (.var p80, (.var p81, (.var p82, (.var p83, (.var p84, (.var p85, (.var
    p86, ())))))))) ) .nil) fun (J78, ()) =>
  .group (sig := [[]]) (fun (_J79, ()) => .cons (fun () =>
  .group (sig := [[i32, i32, i32, .bool, .bool, i32, i32, i32]]) (fun (_J80, ()) => .cons (fun
    (p81, (p82, (p83, (p84, (p85, (p86, (p87, (p88, ())))))))) =>
  .jump J78 (.var p81, (.var p82, (.var p83, (.var p84, (.var p85, (.var p86, (.var p87, (.var
    p88, ())))))))) ) .nil) fun (J80, ()) =>
  .group (sig := [[]]) (fun (_J81, ()) => .cons (fun () =>
  .group (sig := [[i32, .bool, i32, i32]]) (fun (_J82, ()) => .cons (fun (p83, (p84, (p85, (p86,
    ())))) =>
  .group (sig := [[i32, i32, i32, .bool, .bool, i32, i32, i32]]) (fun (_J87, ()) => .cons (fun
    (p88, (p89, (p90, (p91, (p92, (p93, (p94, (p95, ())))))))) =>
  .jump J80 (.var p88, (.var p89, (.var p90, (.var p91, (.var p92, (.var p93, (.var p94, (.var
    p95, ())))))))) ) .nil) fun (J87, ()) => .jnz (.var p84) (
  .group (sig := [[i32, i32, .bool, .bool]]) (fun (_J88, ()) => .cons (fun (p89, (p90, (p91,
    (p92, ())))) =>
  .jump J87 (.var p83, (.var p89, (.var p90, (.var p91, (.var p92, (.var ld47, (.var ld51, (.var
    ld55, ())))))))) ) .nil) fun (J88, ()) => evCmp32 .eq (.var p85) (.var p86) fun v89 =>
  .jnz (.var v89) ( evEquivEnq2Expr h ctrl_off p83 p85 next_ep (.imm false) (fun p93 =>
  .jump J88 (.var p21, (.var p19, (.imm false, (.var p93, ())))) ) ) (
  .group (sig := [[i32, i32, .bool, .bool]]) (fun (_J90, ()) => .cons (fun (p91, (p92, (p93,
    (p94, ())))) => .jump J88 (.var p91, (.var p92, (.var p93, (.var p94, ()))))
  ) .nil) fun (J90, ()) => .group (sig := [[]]) (fun (_J91, ()) => .cons (fun () =>
  evL2 (.xor i32) (.var p83) (.imm 1) fun v92 => evUnitExpr h v92 next_ep (.imm false) (fun p96 =>
  .jump J90 (.var p21, (.var p19, (.imm false, (.var p96, ())))) ) ) .nil) fun (J91, ()) =>
  evL2 (.xor i32) (.var p86) (.imm 1) fun v92 => evCmp32 .eq (.var p85) (.var v92) fun v93 =>
  .jnz (.var v93) ( .jump J91 () ) ( evL2 (.xor i32) (.var p83) (.imm 1) fun v94 =>
  evCmp32 .eq (.var p85) (.var v94) fun v95 => .jnz (.var v95) ( .jump J91 () ) (
  evL2 (.xor i32) (.var p83) (.imm 1) fun v96 => evCmp32 .eq (.var p86) (.var v96) fun v97 =>
  .jnz (.var v97) ( .jump J91 () ) (
  .group (sig := [[i32, i32, .bool, .bool]]) (fun (_J98, ()) => .cons (fun (p99, (p100, (p101,
    (p102, ())))) => .jump J90 (.var p99, (.var p100, (.var p101, (.var p102, ()))))
  ) .nil) fun (J98, ()) => evLd8 ld7 p83 fun ld101 => evSgn0 .sgt ld101 fun v105 =>
  .jnz (.var v105) ( evUnitExpr h p85 next_ep (.imm false) (fun p109 =>
  evUnitExpr h p86 next_ep (.var p109) (fun p113 =>
  .jump J98 (.var p21, (.var p19, (.imm false, (.var p113, ())))) ) ) ) (
  .let_ ⟨.sext 32 64, (.imm 0, ())⟩ fun (v106, ()) =>
  evL2 (.mul i64) (.var v106) (.imm 4) fun v107 =>
  evL2 (.add i64) (.var ld5) (.var v107) fun v108 =>
  .group (sig := [[i32]]) (fun (_J109, ()) => .cons (fun (p110, ()) =>
  .store (t := i32) (.var p110) (.var v108) ( .let_ ⟨.sext 32 64, (.imm 1, ())⟩ fun (v111, ()) =>
  evL2 (.mul i64) (.var v111) (.imm 4) fun v112 =>
  evL2 (.add i64) (.var ld5) (.var v112) fun v113 =>
  .group (sig := [[i32]]) (fun (_J114, ()) => .cons (fun (p115, ()) =>
  .store (t := i32) (.var p115) (.var v113) (
  .jump J98 (.imm 0, (.imm 2, (.imm true, (.imm false, ()))))) ) .nil) fun (J114, ()) =>
  evCmp32 .ult (.var p85) (.var p86) fun v115 => .jnz (.var v115) ( .jump J114 (.var p86, ()) ) (
  .jump J114 (.var p85, ()) )) ) .nil) fun (J109, ()) =>
  evCmp32 .ult (.var p85) (.var p86) fun v110 => .jnz (.var v110) ( .jump J109 (.var p85, ()) ) (
  .jump J109 (.var p86, ()) ) ) ) ) ) ) ) (
  .group (sig := [[i32, i32, i32]]) (fun (_J88, ()) => .cons (fun (p89, (p90, (p91, ()))) =>
  .group (sig := [[i32, i32, i32]]) (fun (_J92, ()) => .cons (fun (p93, (p94, (p95, ()))) =>
  .let_ ⟨.sext 32 64, (.imm 0, ())⟩ fun (v96, ()) =>
  evL2 (.mul i64) (.var v96) (.imm 4) fun v97 => evL2 (.add i64) (.var ld5) (.var v97) fun v98 =>
  .store (t := i32) (.var p89) (.var v98) ( .let_ ⟨.sext 32 64, (.imm 1, ())⟩ fun (v99, ()) =>
  evL2 (.mul i64) (.var v99) (.imm 4) fun v100 =>
  evL2 (.add i64) (.var ld5) (.var v100) fun v101 => .store (t := i32) (.var p94) (.var v101) (
  .let_ ⟨.sext 32 64, (.imm 2, ())⟩ fun (v102, ()) =>
  evL2 (.mul i64) (.var v102) (.imm 4) fun v103 =>
  evL2 (.add i64) (.var ld5) (.var v103) fun v104 => .store (t := i32) (.var p95) (.var v104) (
  .jump J87 (.var p93, (.var p21, (.var p19, (.imm true, (.imm false, (.var p89, (.var p94, (.var
    p95, ()))))))))))) ) .nil) fun (J92, ()) => evL2 (.and i32) (.var p90) (.imm 1) fun v93 =>
  evCmp32 .ne (.var v93) (.imm 0) fun v94 => .jnz (.var v94) (
  evL2 (.xor i32) (.var p83) (.imm 1) fun v95 => evL2 (.xor i32) (.var p90) (.imm 1) fun v96 =>
  evL2 (.xor i32) (.var p91) (.imm 1) fun v97 => .jump J92 (.var v95, (.var v96, (.var v97, ())))
  ) ( .jump J92 (.var p83, (.var p90, (.var p91, ()))) ) ) .nil) fun (J88, ()) =>
  evL2 (.and i32) (.var ld47) (.imm 1) fun v89 => evCmp32 .ne (.var v89) (.imm 0) fun v90 =>
  .jnz (.var v90) ( evL2 (.xor i32) (.var ld47) (.imm 1) fun v91 =>
  .jump J88 (.var v91, (.var ld55, (.var ld51, ()))) ) (
  .jump J88 (.var ld47, (.var ld51, (.var ld55, ()))) ) ) ) .nil) fun (J82, ()) =>
  evSgn0 .sgt ld61 fun v86 => .jnz (.var v86) ( evL2 (.xor i32) (.var r28) (.imm 1) fun v87 =>
  evL2 (.xor i32) (.var ld47) (.imm 1) fun v88 => evL2 (.xor i32) (.var ld55) (.imm 1) fun v89 =>
  .jump J82 (.var v87, (.imm true, (.var v88, (.var v89, ())))) ) (
  .group (sig := [[i32, .bool, i32, i32]]) (fun (_J87, ()) => .cons (fun (p88, (p89, (p90, (p91,
    ())))) => .jump J82 (.var p88, (.var p89, (.var p90, (.var p91, ()))))
  ) .nil) fun (J87, ()) => evSgn0 .slt ld61 fun v91 => .jnz (.var v91) (
  evL2 (.xor i32) (.var ld47) (.imm 1) fun v92 =>
  .jump J87 (.var r28, (.imm true, (.var v92, (.var ld55, ())))) ) (
  .group (sig := [[i32, .bool, i32, i32]]) (fun (_J92, ()) => .cons (fun (p93, (p94, (p95, (p96,
    ())))) => .jump J87 (.var p93, (.var p94, (.var p95, (.var p96, ()))))
  ) .nil) fun (J92, ()) => evSgn0 .sgt ld64 fun v96 => .jnz (.var v96) (
  evL2 (.xor i32) (.var r28) (.imm 1) fun v97 => evL2 (.xor i32) (.var ld51) (.imm 1) fun v98 =>
  .jump J92 (.var v97, (.imm true, (.var ld47, (.var v98, ())))) ) (
  .group (sig := [[i32, .bool, i32, i32]]) (fun (_J97, ()) => .cons (fun (p98, (p99, (p100,
    (p101, ())))) => .jump J92 (.var p98, (.var p99, (.var p100, (.var p101, ()))))
  ) .nil) fun (J97, ()) => evSgn0 .slt ld64 fun v101 => .jnz (.var v101) (
  .jump J97 (.var r28, (.imm true, (.var ld47, (.var ld51, ())))) ) (
  .group (sig := [[i32, .bool, i32, i32]]) (fun (_J102, ()) => .cons (fun (p103, (p104, (p105,
    (p106, ())))) => .jump J97 (.var p103, (.var p104, (.var p105, (.var p106, ()))))
  ) .nil) fun (J102, ()) => evCmp32 .eq (.var ld47) (.var ld51) fun v103 => .jnz (.var v103) (
  evL2 (.xor i32) (.var r28) (.imm 1) fun v104 => evL2 (.xor i32) (.var ld47) (.imm 1) fun v105 =>
  evL2 (.xor i32) (.var ld55) (.imm 1) fun v106 =>
  .jump J102 (.var v104, (.imm true, (.var v105, (.var v106, ())))) ) (
  .group (sig := [[i32, .bool, i32, i32]]) (fun (_J104, ()) => .cons (fun (p105, (p106, (p107,
    (p108, ())))) => .jump J102 (.var p105, (.var p106, (.var p107, (.var p108, ()))))
  ) .nil) fun (J104, ()) => evL2 (.xor i32) (.var ld51) (.imm 1) fun v105 =>
  evCmp32 .eq (.var ld47) (.var v105) fun v106 => .jnz (.var v106) (
  evL2 (.xor i32) (.var ld47) (.imm 1) fun v107 =>
  .jump J104 (.var r28, (.imm true, (.var v107, (.var ld55, ())))) ) (
  .group (sig := [[i32, .bool, i32, i32]]) (fun (_J107, ()) => .cons (fun (p108, (p109, (p110,
    (p111, ())))) => .jump J104 (.var p108, (.var p109, (.var p110, (.var p111, ()))))
  ) .nil) fun (J107, ()) => evL2 (.xor i32) (.var ld55) (.imm 1) fun v108 =>
  evCmp32 .eq (.var ld47) (.var v108) fun v109 => .jnz (.var v109) (
  evL2 (.xor i32) (.var r28) (.imm 1) fun v110 => evL2 (.xor i32) (.var ld51) (.imm 1) fun v111 =>
  .jump J107 (.var v110, (.imm true, (.var ld47, (.var v111, ())))) ) (
  .group (sig := [[.bool, i32, i32]]) (fun (_J110, ()) => .cons (fun (p111, (p112, (p113, ()))) =>
  .jump J107 (.var r28, (.var p111, (.var p112, (.var p113, ())))) ) .nil) fun (J110, ()) =>
  evCmp32 .eq (.var ld47) (.var ld55) fun v111 => .jnz (.var v111) (
  .jump J110 (.imm true, (.var ld47, (.var ld51, ()))) ) (
  .jump J110 (.imm false, (.imm 0, (.imm 0, ()))) ) ) ) ) ) ) ) ) ) .nil) fun (J81, ()) =>
  evSgn0 .eq ld61 fun v85 => .jnz (.var v85) ( evSgn0 .eq ld64 fun v89 => .jnz (.var v89) (
  evL2 (.xor i32) (.var ld55) (.imm 1) fun v90 => evCmp32 .eq (.var ld51) (.var v90) fun v91 =>
  .jnz (.var v91) ( evL2 (.xor i32) (.imm 1) (.var ld47) fun v92 =>
  evL2 (.xor i32) (.var v92) (.var ld51) fun v93 => evL2 (.and i32) (.var v93) (.imm 1) fun v94 =>
  evL2 (.xor i32) (.var r28) (.var v94) fun v95 => .let_ ⟨.not i32, (.imm 1, ())⟩ fun (v96, ()) =>
  evL2 (.and i32) (.var ld47) (.var v96) fun v97 =>
  .let_ ⟨.not i32, (.imm 1, ())⟩ fun (v98, ()) =>
  evL2 (.and i32) (.var ld51) (.var v98) fun v99 =>
  .group (sig := [[i32, i32, .bool, .bool]]) (fun (_J100, ()) => .cons (fun (p101, (p102, (p103,
    (p104, ())))) =>
  .jump J80 (.var v95, (.var p101, (.var p102, (.var p103, (.var p104, (.var ld47, (.var ld51,
    (.var ld55, ())))))))) ) .nil) fun (J100, ()) => evCmp32 .eq (.var v97) (.var v99) fun v101 =>
  .jnz (.var v101) ( evL2 (.xor i32) (.var v95) (.imm 1) fun v102 =>
  evUnitExpr h v102 next_ep (.imm false) (fun p106 =>
  .jump J100 (.var p21, (.var p19, (.imm false, (.var p106, ())))) ) ) (
  .group (sig := [[i32, i32, .bool, .bool]]) (fun (_J102, ()) => .cons (fun (p103, (p104, (p105,
    (p106, ())))) => .jump J100 (.var p103, (.var p104, (.var p105, (.var p106, ()))))
  ) .nil) fun (J102, ()) => evLd8 ld7 v95 fun ld105 => evSgn0 .ne ld105 fun v109 =>
  .jnz (.var v109) (
  .group (sig := [[i32]]) (fun (_J110, ()) => .cons (fun (p111, ()) =>
  evEquivEnq2Expr h ctrl_off p111 v99 next_ep (.imm false) (fun p115 =>
  .jump J102 (.var p21, (.var p19, (.imm false, (.var p115, ())))) ) ) .nil) fun (J110, ()) =>
  evLd8 ld7 v95 fun ld113 => evSgn0 .sgt ld113 fun v117 => .jnz (.var v117) (
  evL2 (.xor i32) (.var v97) (.imm 1) fun v118 => .jump J110 (.var v118, ()) ) (
  .jump J110 (.var v97, ()) ) ) ( .let_ ⟨.sext 32 64, (.imm 0, ())⟩ fun (v110, ()) =>
  evL2 (.mul i64) (.var v110) (.imm 4) fun v111 =>
  evL2 (.add i64) (.var ld5) (.var v111) fun v112 =>
  .group (sig := [[i32]]) (fun (_J113, ()) => .cons (fun (p114, ()) =>
  .store (t := i32) (.var p114) (.var v112) ( .let_ ⟨.sext 32 64, (.imm 1, ())⟩ fun (v115, ()) =>
  evL2 (.mul i64) (.var v115) (.imm 4) fun v116 =>
  evL2 (.add i64) (.var ld5) (.var v116) fun v117 =>
  .group (sig := [[i32]]) (fun (_J118, ()) => .cons (fun (p119, ()) =>
  .store (t := i32) (.var p119) (.var v117) (
  .jump J102 (.imm 1, (.imm 2, (.imm true, (.imm false, ()))))) ) .nil) fun (J118, ()) =>
  evCmp32 .ult (.var v97) (.var v99) fun v119 => .jnz (.var v119) ( .jump J118 (.var v99, ()) ) (
  .jump J118 (.var v97, ()) )) ) .nil) fun (J113, ()) =>
  evCmp32 .ult (.var v97) (.var v99) fun v114 => .jnz (.var v114) ( .jump J113 (.var v97, ()) ) (
  .jump J113 (.var v99, ()) ) ) ) ) ( .jump J81 () ) ) ( .jump J81 () ) ) ( .jump J81 () )
  ) .nil) fun (J79, ()) => evSgn0 .slt ld61 fun v83 => .jnz (.var v83) (
  evSgn0 .slt ld64 fun v87 => .jnz (.var v87) ( evL2 (.xor i32) (.var r28) (.imm 1) fun v88 =>
  evUnitExpr h v88 next_ep (.imm false) (fun p92 =>
  .jump J78 (.var r28, (.var p21, (.var p19, (.imm false, (.var p92, (.var ld47, (.var ld51,
    (.var ld55, ())))))))) ) ) ( .jump J79 () ) ) ( .jump J79 () ) ) .nil) fun (J77, ()) =>
  evSgn0 .sgt ld61 fun v81 => .jnz (.var v81) ( evSgn0 .sgt ld64 fun v85 => .jnz (.var v85) (
  evUnitExpr h r28 next_ep (.imm false) (fun p89 =>
  .jump J76 (.var r28, (.var p21, (.var p19, (.imm false, (.var p89, (.var ld47, (.var ld51,
    (.var ld55, ())))))))) ) ) ( .jump J77 () ) ) ( .jump J77 () ) ) .nil) fun (J75, ()) =>
  evSgn0 .slt ld61 fun v79 => .jnz (.var v79) ( evSgn0 .sgt ld64 fun v83 => .jnz (.var v83) (
  evL2 (.xor i32) (.var ld47) (.imm 1) fun v84 =>
  evEquivEnq2bExpr h ctrl_off r28 v84 ld47 next_ep (.imm false) (fun p88 =>
  .jump J74 (.var r28, (.var p21, (.var p19, (.imm false, (.var p88, (.var ld47, (.var ld51,
    (.var ld55, ())))))))) ) ) ( .jump J75 () ) ) ( .jump J75 () ) ) .nil) fun (J73, ()) =>
  evSgn0 .sgt ld61 fun v77 => .jnz (.var v77) ( evSgn0 .slt ld64 fun v81 => .jnz (.var v81) (
  evEquivEnq2Expr h ctrl_off r28 ld47 next_ep (.imm false) (fun p85 =>
  .jump J72 (.var r28, (.var p21, (.var p19, (.imm false, (.var p85, (.var ld47, (.var ld51,
    (.var ld55, ())))))))) ) ) ( .jump J73 () ) ) ( .jump J73 () ) ) ) ) (
  .jump J41 (.var r28, (.var p21, (.var p19, (.imm false, (.imm false, ()))))) ) ) (
  .jump J41 (.var r28, (.var p21, (.var p19, (.imm false, (.imm false, ()))))) )

@[expose] def evTag1SelfCancelExpr {V : Ty → Type} {L : List Ty → Type}
    (h ld5 ctrl_off : V i64) (next_ep v49 p52 p53 : V i32)
    (J55 : L [i32, .bool, .bool, i32]) : Expr V L [i64] :=
  evCmp32 .ugt (.var p53) (.imm 0) fun v56 => .jnz (.var v56) (
  .let_ ⟨.not i32, (.imm 1, ())⟩ fun (v57, ()) => evL2 (.and i32) (.var v49) (.var v57) fun v58 =>
  .group (sig := [[i32, i32]]) (fun (_J59, ()) => .cons (fun (p60, (p61, ())) =>
  .group (sig := [[.bool, .bool, i32]]) (fun (_J62, ()) => .cons (fun (p63, (p64, (p65, ()))) =>
  .jump J55 (.var p60, (.var p63, (.var p64, (.var p65, ())))) ) .nil) fun (J62, ()) =>
  evCmp32 .ult (.var p61) (.var p53) fun v63 => .jnz (.var v63) (
  .group (sig := [[i32]]) (fun (J64, ()) => .cons (fun (p65, ()) =>
  evL2 (.add i32) (.var p65) (.imm 1) fun v66 => evCmp32 .ult (.var v66) (.var p53) fun v67 =>
  .jnz (.var v67) ( .let_ ⟨.zext 32 64, (.var p65, ())⟩ fun (v68, ()) =>
  evL2 (.mul i64) (.var v68) (.imm 4) fun v69 => evL2 (.add i64) (.var ld5) (.var v69) fun v70 =>
  evL2 (.add i32) (.var p65) (.imm 1) fun v71 => evLd32 ld5 v71 fun ld75 =>
  .store (t := i32) (.var ld75) (.var v70) ( evL2 (.add i32) (.var p65) (.imm 1) fun v76 =>
  .jump J64 (.var v76, ())) ) ( evL2 (.sub i32) (.var p53) (.imm 1) fun v68 =>
  evL2 (.and i32) (.var v49) (.imm 1) fun v69 =>
  .group (sig := [[.bool, .bool]]) (fun (_J70, ()) => .cons (fun (p71, (p72, ())) =>
  .jump J62 (.var p71, (.var p72, (.var v68, ()))) ) .nil) fun (J70, ()) =>
  evCmp32 .eq (.var v68) (.imm 0) fun v71 => .jnz (.var v71) (
  evCmp32 .ne (.var v69) (.imm 0) fun v72 => .jnz (.var v72) (
  evL2 (.add i64) (.var h) (.imm 1024) fun v73 => .store (t := i64) (.imm 1) (.var v73) (
  .ret (.imm 2, ())) ) ( .jump J70 (.imm false, (.imm false, ())) ) ) (
  .group (sig := [[.bool, .bool]]) (fun (_J72, ()) => .cons (fun (p73, (p74, ())) =>
  .jump J70 (.var p73, (.var p74, ())) ) .nil) fun (J72, ()) =>
  evCmp32 .eq (.var v68) (.imm 1) fun v73 => .jnz (.var v73) ( evLdK32 ld5 0 fun ld77 =>
  evL2 (.xor i32) (.imm 1) (.var v69) fun v78 => evL2 (.xor i32) (.var ld77) (.var v78) fun v79 =>
  evUnitExpr h v79 next_ep (.imm false) (fun p83 => .jump J72 (.imm false, (.var p83, ())) ) ) (
  .group (sig := [[.bool, .bool]]) (fun (_J74, ()) => .cons (fun (p75, (p76, ())) =>
  .jump J72 (.var p75, (.var p76, ())) ) .nil) fun (J74, ()) =>
  evCmp32 .eq (.var v68) (.imm 2) fun v75 => .jnz (.var v75) ( evLdK32 ld5 0 fun ld79 =>
  evL2 (.xor i32) (.var ld79) (.var v69) fun v80 => evLdK32 ld5 1 fun ld84 =>
  evEquivEnq2Expr h ctrl_off v80 ld84 next_ep (.imm false) (fun p88 =>
  .jump J74 (.imm false, (.var p88, ())) ) ) ( .jump J74 (.imm false, (.imm false, ())) ) ) ) )
  ) .nil) fun (J64, ()) => .jump J64 (.var p61, ()) ) (
  .jump J62 (.imm true, (.imm false, (.var p53, ()))) ) ) .nil) fun (J59, ()) =>
  .group (sig := [[i32]]) (fun (J60, ()) => .cons (fun (p61, ()) =>
  evCmp32 .ult (.var p61) (.var p53) fun v62 => .jnz (.var v62) ( evLd32 ld5 p61 fun ld66 =>
  evCmp32 .eq (.var ld66) (.var v58) fun v67 => .jnz (.var v67) (
  .jump J59 (.var p61, (.var p61, ())) ) ( evL2 (.add i32) (.var p61) (.imm 1) fun v68 =>
  .jump J60 (.var v68, ()) ) ) ( .jump J59 (.var p61, (.var p53, ())) ) ) .nil) fun (J60, ()) =>
  .jump J60 (.imm 0, ()) ) ( .jump J55 (.var p52, (.imm true, (.imm false, (.var p53, ())))) )

@[expose] def evTag1Expr {V : Ty → Type} {L : List Ty → Type}
    (h ctrl_off ld5 ld7 : V i64) (next_ep p19 p21 r28 : V i32)
    (J39 : L [i32, i32, i32, i32, .bool, .bool]) (J40 : L []) : Expr V L [i64] :=
  evCmp32 .eq (.var p21) (.imm 1) fun v41 => .jnz (.var v41) (
  evCmp32 .uge (.var p19) (.imm 2) fun v42 => .jnz (.var v42) (
  evCmp32 .ule (.var p19) (.imm 4) fun v43 => .jnz (.var v43) (
  .group (sig := [[i32, i32, i32]]) (fun (J44, ()) => .cons (fun (p45, (p46, (p47, ()))) =>
  evCmp32 .ult (.var p45) (.var p19) fun v48 => .jnz (.var v48) ( evLd32 ld5 p45 fun ld52 =>
  evLd8 ld7 ld52 fun ld55 =>
  .group (sig := [[i32, i32]]) (fun (_J56, ()) => .cons (fun (p57, (p58, ())) =>
  evL2 (.add i32) (.var p45) (.imm 1) fun v59 => .jump J44 (.var v59, (.var p57, (.var p58, ())))
  ) .nil) fun (J56, ()) => evSgn0 .ne ld55 fun v60 => .jnz (.var v60) (
  .group (sig := [[i32]]) (fun (_J61, ()) => .cons (fun (p62, ()) =>
  .jump J56 (.var p62, (.var p47, ())) ) .nil) fun (J61, ()) => evSgn0 .sgt ld55 fun v65 =>
  .jnz (.var v65) ( evL2 (.xor i32) (.var p46) (.imm 1) fun v66 => .jump J61 (.var v66, ()) ) (
  .jump J61 (.var p46, ()) ) ) ( evL2 (.and i32) (.var ld52) (.imm 1) fun v61 =>
  evL2 (.xor i32) (.var p46) (.var v61) fun v62 =>
  .let_ ⟨.zext 32 64, (.var p47, ())⟩ fun (v63, ()) =>
  evL2 (.mul i64) (.var v63) (.imm 4) fun v64 => evL2 (.add i64) (.var ld5) (.var v64) fun v65 =>
  .let_ ⟨.not i32, (.imm 1, ())⟩ fun (v66, ()) =>
  evL2 (.and i32) (.var ld52) (.var v66) fun v67 => .store (t := i32) (.var v67) (.var v65) (
  evL2 (.add i32) (.var p47) (.imm 1) fun v68 => .jump J56 (.var v62, (.var v68, ()))) ) ) (
  evL2 (.xor i32) (.var r28) (.var p46) fun v49 =>
  .group (sig := [[]]) (fun (_J50, ()) => .cons (fun () =>
  .group (sig := [[i32, i32]]) (fun (J51, ()) => .cons (fun (p52, (p53, ())) =>
  evCmp32 .ult (.var p52) (.var p47) fun v54 => .jnz (.var v54) (
  .group (sig := [[i32, i32]]) (fun (_J55, ()) => .cons (fun (p56, (p57, ())) =>
  .jump J51 (.var p56, (.var p57, ())) ) .nil) fun (J55, ()) =>
  .group (sig := [[]]) (fun (_J56, ()) => .cons (fun () =>
  .let_ ⟨.zext 32 64, (.var p53, ())⟩ fun (v57, ()) =>
  evL2 (.mul i64) (.var v57) (.imm 4) fun v58 => evL2 (.add i64) (.var ld5) (.var v58) fun v59 =>
  evLd32 ld5 p52 fun ld63 => .store (t := i32) (.var ld63) (.var v59) (
  evL2 (.add i32) (.var p53) (.imm 1) fun v64 => evL2 (.add i32) (.var p52) (.imm 1) fun v65 =>
  .jump J55 (.var v65, (.var v64, ()))) ) .nil) fun (J56, ()) =>
  evL2 (.add i32) (.var p52) (.imm 1) fun v57 => evCmp32 .ult (.var v57) (.var p47) fun v58 =>
  .jnz (.var v58) ( evLd32 ld5 p52 fun ld62 => evL2 (.add i32) (.var p52) (.imm 1) fun v63 =>
  evLd32 ld5 v63 fun ld67 => evCmp32 .eq (.var ld62) (.var ld67) fun v68 => .jnz (.var v68) (
  evL2 (.add i32) (.var p52) (.imm 2) fun v69 => .jump J55 (.var v69, (.var p53, ())) ) (
  .jump J56 () ) ) ( .jump J56 () ) ) (
  .group (sig := [[i32, .bool, .bool, i32]]) (fun (_J55, ()) => .cons (fun (p56, (p57, (p58,
    (p59, ())))) =>
  .group (sig := [[i32, .bool, .bool]]) (fun (_J60, ()) => .cons (fun (p61, (p62, (p63, ()))) =>
  .jump J39 (.var v49, (.var p56, (.var p21, (.var p61, (.var p62, (.var p63, ()))))))
  ) .nil) fun (J60, ()) => .jnz (.var p57) (
  .group (sig := [[i32, .bool, .bool]]) (fun (_J61, ()) => .cons (fun (p62, (p63, (p64, ()))) =>
  .jump J60 (.var p62, (.var p63, (.var p64, ()))) ) .nil) fun (J61, ()) =>
  evCmp32 .eq (.var p59) (.imm 0) fun v62 => .jnz (.var v62) (
  evL2 (.xor i32) (.var v49) (.imm 1) fun v63 => evUnitExpr h v63 next_ep (.var p58) (fun p67 =>
  .jump J61 (.var p19, (.imm false, (.var p67, ()))) ) ) (
  .group (sig := [[i32, .bool, .bool]]) (fun (_J63, ()) => .cons (fun (p64, (p65, (p66, ()))) =>
  .jump J61 (.var p64, (.var p65, (.var p66, ()))) ) .nil) fun (J63, ()) =>
  evCmp32 .eq (.var p59) (.imm 1) fun v64 => .jnz (.var v64) ( evLdK32 ld5 0 fun ld68 =>
  evEquivEnq2Expr h ctrl_off v49 ld68 next_ep (.var p58) (fun p72 =>
  .jump J63 (.var p19, (.imm false, (.var p72, ()))) ) ) (
  .group (sig := [[i32, .bool, .bool]]) (fun (_J65, ()) => .cons (fun (p66, (p67, (p68, ()))) =>
  .jump J63 (.var p66, (.var p67, (.var p68, ()))) ) .nil) fun (J65, ()) =>
  evCmp32 .eq (.var p59) (.imm 2) fun v66 => .jnz (.var v66) ( evLd8 ld7 v49 fun ld69 =>
  evSgn0 .ne ld69 fun v73 => .jnz (.var v73) (
  .group (sig := [[i32]]) (fun (_J74, ()) => .cons (fun (p75, ()) => evLdK32 ld5 1 fun ld79 =>
  evEquivEnq2Expr h ctrl_off p75 ld79 next_ep (.var p58) (fun p83 =>
  .jump J65 (.var p19, (.imm false, (.var p83, ()))) ) ) .nil) fun (J74, ()) =>
  evLd8 ld7 v49 fun ld77 => evSgn0 .sgt ld77 fun v81 => .jnz (.var v81) (
  evLdK32 ld5 0 fun ld85 => evL2 (.xor i32) (.var ld85) (.imm 1) fun v86 =>
  .jump J74 (.var v86, ()) ) ( evLdK32 ld5 0 fun ld85 => .jump J74 (.var ld85, ()) ) ) (
  .jump J65 (.var p59, (.var p57, (.var p58, ()))) ) ) (
  .jump J65 (.var p59, (.var p57, (.var p58, ()))) ) ) ) ) (
  .jump J60 (.var p19, (.var p57, (.var p58, ()))) ) ) .nil) fun (J55, ()) =>
  evTag1SelfCancelExpr h ld5 ctrl_off next_ep v49 p52 p53 J55 )
  ) .nil) fun (J51, ()) => .jump J51 (.imm 0, (.imm 0, ())) ) .nil) fun (J50, ()) =>
  evCmp32 .ugt (.var p47) (.imm 1) fun v51 => .jnz (.var v51) (
  .call "full_sort_u32" (as := [i64, i32]) (bs := []) (.var ld5, (.var p47, ())) fun () =>
  .jump J50 () ) ( .jump J50 () ) ) ) .nil) fun (J44, ()) =>
  .jump J44 (.imm 0, (.imm 0, (.imm 0, ()))) ) ( .jump J40 () ) ) ( .jump J40 () ) ) (
  .jump J40 () )


local macro "ev_unfold_ast" : tactic =>
  `(tactic| try dsimp only [evL2, evCmp32, evCmp64, evLd32, evLdK32, evLd8, evSgn0])

local macro "ev_split" : tactic =>
  `(tactic| (
    ev_unfold_ast
    c0_hsteps_nogrp
    repeat (
      refine LeanQbe.T.wp_unroll_group fun _ _ => ?_
      ev_unfold_ast
      c0_hsteps_nogrp)
    c0_hsplit))

/-! ## 1. Core Invariants, Constant-Index `tmp` Rules & State Framing -/

@[expose] def EvCoreOk (maxA : Nat) (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (cv0 : Nat) (fl0 : BitVec 64) (ar0 : List (BitVec 32)) (arl0 g_len ctrl_off ht_off
      ht_sz : Nat) (scr0 scr_in : List (BitVec 32)) (s : FullState) : Prop :=
  FullDenseInvW c F0 F_cur s ∧
  s.core.cur_vars = cv0 ∧ s.core.fuel = fl0 ∧
  s.core.arena = ar0 ∧ s.core.arena_len = arl0 ∧
  FullCongReprInv F_cur (2 * cv0) s.core.repr ∧
  (∀ idx < g_len, s.scratch.scratch_buf[idx]? = scr0[idx]?) ∧
  CongHtInv maxA F_cur cv0 scr0 s.scratch.scratch_buf g_len ht_off ht_sz ∧
  CongQueueCtx c s.scratch.scratch_buf g_len ctrl_off ht_off ht_sz ∧
  (∀ idx < c.scratch_cap, idx < ht_off →
    (ctrl_off = c.scratch_cap → s.scratch.scratch_buf[idx]? = scr_in[idx]?) ∧
    (∀ o b i q, CongCtrlLayout c scr_in g_len ctrl_off o b i q ht_off ht_sz →
      idx ≠ ctrl_off + 5 → ¬ (q ≤ idx ∧ idx < q + o) → ¬ (i ≤ idx ∧ idx < i + o) →
      s.scratch.scratch_buf[idx]? = scr_in[idx]?))

@[expose] def EvHashGateOk (maxA : Nat) (F_cur : List (List Nat)) (cv : Nat)
    (gtype htag harity lhs : BitVec 32) (tmp : List (BitVec 32)) : Prop :=
  lhs.toNat < 2 * cv ∧ harity.toNat ≤ cv ∧ harity.toNat ≤ maxA ∧ 2 ≤ harity.toNat ∧
  (∀ k < harity.toNat, (tmp[k]?.getD 0#32).toNat < 2 * cv) ∧
  (htag = gtype ∨ htag = 0#32 ∨ htag = 1#32) ∧
  (htag = 0#32 → ∀ α : Nat → Bool, (cnfOfClauses F_cur).Sat α →
    evalLitVal α lhs.toNat =
      (List.range harity.toNat).all fun k => evalLitVal α (tmp[k]?.getD 0#32).toNat) ∧
  (htag = 1#32 → harity.toNat ≤ 4 ∧ ∀ α : Nat → Bool, (cnfOfClauses F_cur).Sat α →
    evalLitVal α lhs.toNat = xorEvalList α ((tmp.take harity.toNat).map BitVec.toNat)) ∧
  (htag = 2#32 → harity = 3#32 ∧ ∀ α : Nat → Bool, (cnfOfClauses F_cur).Sat α →
    evalLitVal α lhs.toNat =
      if evalLitVal α (tmp[0]?.getD 0#32).toNat
      then evalLitVal α (tmp[1]?.getD 0#32).toNat
      else evalLitVal α (tmp[2]?.getD 0#32).toNat) ∧
  (htag = 0#32 ∨ htag = 1#32 ∨ htag = 2#32)

theorem ev_c0_load_full_tmp0 {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (FullMem c s ⋆ R) m) (h0 : 0 < s.core.tmp.length) :
    loadVal m i32 (c.pTmp + 0#64) = some (s.core.tmp[0]'h0) := by
  simpa using FullArenaTactics.c0_load_full_tmp (i := 0#64) (by simpa using h0) hm

theorem ev_c0_load_full_tmp1 {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (FullMem c s ⋆ R) m) (h1 : 1 < s.core.tmp.length) :
    loadVal m i32 (c.pTmp + 4#64) = some (s.core.tmp[1]'h1) := by
  simpa using FullArenaTactics.c0_load_full_tmp (i := 1#64) (by simpa using h1) hm

theorem ev_c0_load_full_tmp2 {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (FullMem c s ⋆ R) m) (h2 : 2 < s.core.tmp.length) :
    loadVal m i32 (c.pTmp + 8#64) = some (s.core.tmp[2]'h2) := by
  simpa using FullArenaTactics.c0_load_full_tmp (i := 2#64) (by simpa using h2) hm

theorem ev_c0_store_full_tmp0 {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (v : BitVec 32) (h0 : 0 < s.core.tmp.length) (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 (c.pTmp + 0#64) ∧
      (FullMem c { s with core := { s.core with tmp := s.core.tmp.set 0 v } } ⋆ R)
        (storeMem m i32 (c.pTmp + 0#64) v) := by
  simpa using FullArenaTactics.c0_store_full_tmp (i := 0#64) v (by simpa using h0) hm

theorem ev_c0_store_full_tmp1 {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (v : BitVec 32) (h1 : 1 < s.core.tmp.length) (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 (c.pTmp + 4#64) ∧
      (FullMem c { s with core := { s.core with tmp := s.core.tmp.set 1 v } } ⋆ R)
        (storeMem m i32 (c.pTmp + 4#64) v) := by
  simpa using FullArenaTactics.c0_store_full_tmp (i := 1#64) v (by simpa using h1) hm

theorem ev_c0_store_full_tmp2 {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (v : BitVec 32) (h2 : 2 < s.core.tmp.length) (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 (c.pTmp + 8#64) ∧
      (FullMem c { s with core := { s.core with tmp := s.core.tmp.set 2 v } } ⋆ R)
        (storeMem m i32 (c.pTmp + 8#64) v) := by
  simpa using FullArenaTactics.c0_store_full_tmp (i := 2#64) v (by simpa using h2) hm

theorem ev_denseInvW_with_mclr {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hd : FullDenseInvW c F0 F_cur s)
    {mc' : List (BitVec 32)} (hl : mc'.length = c.max_vars) :
    FullDenseInvW c F0 F_cur { s with core := { s.core with min_clr := mc' } } :=
  ⟨⟨{ hd.1.core_ok with min_clr_len_arr := hl }, hd.1.scratch_ok⟩,
   { hd.2.1 with
     arena := { hd.2.1.arena with len_ok := hd.2.1.arena.len_ok }
     watches := hd.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) },
   fullLitMarksClear_of_eq hd.2.2.1 rfl rfl, fullArenaVarsNodup_of_eq hd.2.2.2.1 rfl rfl,
   fullExtScratchOk_of_eq hd.2.2.2.2.1 rfl rfl rfl rfl, hd.2.2.2.2.2.1, hd.2.2.2.2.2.2⟩

theorem evCoreOk_repr {maxA : Nat} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {cv0 : Nat} {fl0 : BitVec 64} {ar0 : List (BitVec 32)}
    {arl0 g_len ctrl_off ht_off ht_sz : Nat} {scr0 scr_in repr' : List (BitVec 32)}
    {s : FullState}
    (hok : EvCoreOk maxA c F0 F_cur cv0 fl0 ar0 arl0 g_len ctrl_off ht_off ht_sz scr0 scr_in s)
    (hlen : repr'.length = 2 * c.max_vars) (hrepr : FullCongReprInv F_cur (2 * cv0) repr') :
    EvCoreOk maxA c F0 F_cur cv0 fl0 ar0 arl0 g_len ctrl_off ht_off ht_sz scr0 scr_in
      { s with core := { s.core with repr := repr' } } :=
  ⟨fullDenseInvW_with_repr hok.1 hlen, hok.2.1, hok.2.2.1, hok.2.2.2.1, hok.2.2.2.2.1,
   hrepr, hok.2.2.2.2.2.2.1, hok.2.2.2.2.2.2.2.1, hok.2.2.2.2.2.2.2.2.1,
   hok.2.2.2.2.2.2.2.2.2⟩

theorem evCoreOk_tmp {maxA : Nat} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {cv0 : Nat} {fl0 : BitVec 64} {ar0 : List (BitVec 32)}
    {arl0 g_len ctrl_off ht_off ht_sz : Nat} {scr0 scr_in tmp' : List (BitVec 32)}
    {s : FullState}
    (hok : EvCoreOk maxA c F0 F_cur cv0 fl0 ar0 arl0 g_len ctrl_off ht_off ht_sz scr0 scr_in s)
    (hlen : tmp'.length = c.max_vars) :
    EvCoreOk maxA c F0 F_cur cv0 fl0 ar0 arl0 g_len ctrl_off ht_off ht_sz scr0 scr_in
      { s with core := { s.core with tmp := tmp' } } :=
  ⟨⟨⟨{ hok.1.1.core_ok with tmp_len_arr := hlen }, hok.1.1.scratch_ok⟩,
    fullWitnessInv_with_tmp hok.1.2.1 tmp', hok.1.2.2.1, hok.1.2.2.2.1, hok.1.2.2.2.2.1,
    hok.1.2.2.2.2.2.1, hok.1.2.2.2.2.2.2⟩,
   hok.2.1, hok.2.2.1, hok.2.2.2.1, hok.2.2.2.2.1, hok.2.2.2.2.2.1, hok.2.2.2.2.2.2.1,
   hok.2.2.2.2.2.2.2.1, hok.2.2.2.2.2.2.2.2.1, hok.2.2.2.2.2.2.2.2.2⟩

theorem evCoreOk_inc {maxA : Nat} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {cv0 : Nat} {fl0 : BitVec 64} {ar0 : List (BitVec 32)}
    {arl0 g_len ctrl_off ht_off ht_sz : Nat} {scr0 scr_in : List (BitVec 32)} {s : FullState}
    (hok : EvCoreOk maxA c F0 F_cur cv0 fl0 ar0 arl0 g_len ctrl_off ht_off ht_sz scr0 scr_in s)
    (huns : (cnfOfClauses F_cur).Unsat) :
    EvCoreOk maxA c F0 F_cur cv0 fl0 ar0 arl0 g_len ctrl_off ht_off ht_sz scr0 scr_in
      { s with core := { s.core with inconsistent := 1#64 } } :=
  ⟨⟨⟨{ hok.1.1.core_ok with }, hok.1.1.scratch_ok⟩,
    fullWitnessInv_with_inconsistent hok.1.2.1 1#64 (fun _ => huns),
    hok.1.2.2.1, hok.1.2.2.2.1, hok.1.2.2.2.2.1, hok.1.2.2.2.2.2.1, hok.1.2.2.2.2.2.2⟩,
   hok.2⟩

theorem evCoreOk_and_match {maxA : Nat} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {cv0 : Nat} {fl0 : BitVec 64} {ar0 : List (BitVec 32)}
    {arl0 g_len ctrl_off ht_off ht_sz : Nat} {scr0 scr_in repr' : List (BitVec 32)}
    {lm'' : List (BitVec 8)} {s : FullState}
    (hok : EvCoreOk maxA c F0 F_cur cv0 fl0 ar0 arl0 g_len ctrl_off ht_off ht_sz scr0 scr_in s)
    (hr : repr'.length = 2 * c.max_vars) (hlm : lm''.length = 2 * c.max_vars)
    (hmk : FullLitMarksClear c { s with core := { s.core with repr := repr', lit_mark := lm'' } })
    (hrepr : FullCongReprInv F_cur (2 * cv0) repr') :
    EvCoreOk maxA c F0 F_cur cv0 fl0 ar0 arl0 g_len ctrl_off ht_off ht_sz scr0 scr_in
      { s with core := { s.core with repr := repr', lit_mark := lm'' } } := by
  have hd : FullDenseInvW c F0 F_cur
      { s with core := { s.core with repr := repr', lit_mark := lm'' } } :=
    ⟨⟨{ hok.1.1.core_ok with repr_len := hr, lit_mark_len := hlm }, hok.1.1.scratch_ok⟩,
     { hok.1.2.1 with
       arena := { hok.1.2.1.arena with len_ok := hok.1.2.1.arena.len_ok }
       watches := hok.1.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) },
     hmk, hok.1.2.2.2.1, fullExtScratchOk_of_eq hok.1.2.2.2.2.1 rfl rfl rfl rfl,
     hok.1.2.2.2.2.2.1, hok.1.2.2.2.2.2.2⟩
  exact ⟨hd, hok.2.1, hok.2.2.1, hok.2.2.2.1, hok.2.2.2.2.1, hrepr, hok.2.2.2.2.2.2.1,
    hok.2.2.2.2.2.2.2.1, hok.2.2.2.2.2.2.2.2.1, hok.2.2.2.2.2.2.2.2.2⟩

theorem evCoreOk_xor_match {maxA : Nat} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {cv0 : Nat} {fl0 : BitVec 64} {ar0 : List (BitVec 32)}
    {arl0 g_len ctrl_off ht_off ht_sz : Nat} {scr0 scr_in repr' mclr' : List (BitVec 32)}
    {s : FullState}
    (hok : EvCoreOk maxA c F0 F_cur cv0 fl0 ar0 arl0 g_len ctrl_off ht_off ht_sz scr0 scr_in s)
    (hr : repr'.length = 2 * c.max_vars) (hmc : mclr'.length = c.max_vars)
    (hrepr : FullCongReprInv F_cur (2 * cv0) repr') :
    EvCoreOk maxA c F0 F_cur cv0 fl0 ar0 arl0 g_len ctrl_off ht_off ht_sz scr0 scr_in
      { s with core := { s.core with repr := repr', min_clr := mclr' } } :=
  ⟨ev_denseInvW_with_mclr (fullDenseInvW_with_repr hok.1 hr) hmc,
   hok.2.1, hok.2.2.1, hok.2.2.2.1, hok.2.2.2.2.1, hrepr, hok.2.2.2.2.2.2.1,
   hok.2.2.2.2.2.2.2.1, hok.2.2.2.2.2.2.2.2.1, hok.2.2.2.2.2.2.2.2.2⟩

theorem evCoreOk_enq {maxA : Nat} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {cv0 : Nat} {fl0 : BitVec 64} {ar0 : List (BitVec 32)}
    {arl0 g_len ctrl_off ht_off ht_sz : Nat} {scr0 scr_in scr' : List (BitVec 32)}
    {s : FullState} (hg_ht : g_len ≤ ht_off)
    (hok : EvCoreOk maxA c F0 F_cur cv0 fl0 ar0 arl0 g_len ctrl_off ht_off ht_sz scr0 scr_in s)
    (hlen : scr'.length = c.scratch_cap) (hq' : CongQueueCtx c scr' g_len ctrl_off ht_off ht_sz)
    (hcap : ctrl_off = c.scratch_cap → scr' = s.scratch.scratch_buf)
    (hlay_eq : ∀ o b i q,
      CongCtrlLayout c s.scratch.scratch_buf g_len ctrl_off o b i q ht_off ht_sz →
      scr'[ctrl_off]? = some (BitVec.ofNat 32 o) ∧
      scr'[ctrl_off + 1]? = some (BitVec.ofNat 32 b) ∧
      scr'[ctrl_off + 2]? = some (BitVec.ofNat 32 i) ∧
      scr'[ctrl_off + 3]? = some (BitVec.ofNat 32 q) ∧
      scr'[ctrl_off + 4]? = s.scratch.scratch_buf[ctrl_off + 4]? ∧
      scr'[ctrl_off + 6]? = some (BitVec.ofNat 32 ht_off) ∧
      scr'[ctrl_off + 7]? = some (BitVec.ofNat 32 ht_sz) ∧
      (∀ idx, idx ≠ ctrl_off + 5 → ¬ (q ≤ idx ∧ idx < q + o) →
        ¬ (i ≤ idx ∧ idx < i + o) → scr'[idx]? = s.scratch.scratch_buf[idx]?)) :
    EvCoreOk maxA c F0 F_cur cv0 fl0 ar0 arl0 g_len ctrl_off ht_off ht_sz scr0 scr_in
      { s with scratch := { s.scratch with scratch_buf := scr' } } := by
  have hkeep : ∀ idx, idx < ht_off →
      (ctrl_off = c.scratch_cap → scr'[idx]? = s.scratch.scratch_buf[idx]?) ∧
      (∀ o b i q, CongCtrlLayout c scr_in g_len ctrl_off o b i q ht_off ht_sz →
        idx ≠ ctrl_off + 5 → ¬ (q ≤ idx ∧ idx < q + o) → ¬ (i ≤ idx ∧ idx < i + o) →
        scr'[idx]? = s.scratch.scratch_buf[idx]?) := by
    intro idx hht; constructor
    · intro hc; rw [hcap hc]
    · intro o b i q hlin hn5 hnq hni
      rcases hok.2.2.2.2.2.2.2.2.1 with hc | ⟨o', b', i', q', hlo⟩
      · have := hlin.2.1; omega
      · have hctrl : ∀ j < 4, s.scratch.scratch_buf[ctrl_off + j]? = scr_in[ctrl_off + j]? :=
          fun j hj => (hok.2.2.2.2.2.2.2.2.2 (ctrl_off + j) (by have := hlin.2.1; omega)
            (by rcases hlin with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, h1, h2, h3, h4, _⟩
                omega)).2 o b i q hlin (by omega)
            (by have := hlin.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; omega)
            (by rcases hlin with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, h1, h2, _⟩; omega)
        have hkeep_eq : ∀ a1 a2 : Nat, a1 < 2 ^ 32 → a2 < 2 ^ 32 →
            BitVec.ofNat 32 a1 = BitVec.ofNat 32 a2 → a1 = a2 := fun _ _ h1 h2 he => by
          have := congrArg BitVec.toNat he
          rwa [bv32_ofNat_toNat_lt h1, bv32_ofNat_toNat_lt h2] at this
        have hlo' := hlo
        rcases hlin with ⟨_, _, _, _, l0, _, l2, l3, _, _, _, ho_lt, _, _, l_1, l_2, l_3, l_4, _⟩
        rcases hlo with ⟨_, _, _, _, o0, _, o2, o3, _, _, _, ho'_lt, _, _, o_1, o_2, o_3, o_4, _⟩
        have ho_eq : o' = o := by
          have h0 := hctrl 0 (by omega); rw [Nat.add_zero] at h0
          have heq := (congrArg (Option.getD · 0#32) h0).trans l0
          have hsc := c.hscr; unfold dimacsBound at hsc; unfold congOccBktMax at *
          exact hkeep_eq _ _ (by omega) (by omega) (o0.symm.trans (by simpa using heq))
        have hq_eq : q' = q := by
          have heq := (congrArg (Option.getD · 0#32) (hctrl 3 (by omega))).trans l3
          have hsc := c.hscr; unfold dimacsBound at hsc
          exact hkeep_eq _ _ (by omega) (by omega) (o3.symm.trans heq)
        have hi_eq : i' = i := by
          have heq := (congrArg (Option.getD · 0#32) (hctrl 2 (by omega))).trans l2
          have hsc := c.hscr; unfold dimacsBound at hsc
          exact hkeep_eq _ _ (by omega) (by omega) (o2.symm.trans heq)
        subst ho_eq hq_eq hi_eq
        exact (hlay_eq o' b' i' q' hlo').2.2.2.2.2.2.2 idx hn5 hnq hni
  have hpref' : ∀ idx < g_len, scr'[idx]? = scr0[idx]? := fun idx hidx => by
    have hpre : scr'[idx]? = s.scratch.scratch_buf[idx]? := by
      rcases hok.2.2.2.2.2.2.2.2.1 with hc | ⟨o, b, i, q, hlo⟩
      · exact (hkeep idx (by omega)).1 hc
      · have hlo' := hlo
        rcases hlo with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, h1, h2, _⟩
        exact (hlay_eq o b i q hlo').2.2.2.2.2.2.2 idx (by omega) (by omega) (by omega)
    rw [hpre]; exact hok.2.2.2.2.2.2.1 idx hidx
  have hht' : CongHtInv maxA F_cur cv0 scr0 scr' g_len ht_off ht_sz := fun k hk => by
    have heq : scr'[ht_off + k]? = s.scratch.scratch_buf[ht_off + k]? := by
      rcases hok.2.2.2.2.2.2.2.2.1 with hc | ⟨o, b, i, q, hlo⟩
      · rw [hcap hc]
      · have hlo' := hlo
        rcases hlo with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, h1, h2, h3, h4, _⟩
        exact (hlay_eq o b i q hlo').2.2.2.2.2.2.2 (ht_off + k)
          (by omega) (by omega) (by omega)
    rw [heq]; exact hok.2.2.2.2.2.2.2.1 k hk
  refine ⟨fullDenseInvW_with_scr hok.1 hlen, hok.2.1, hok.2.2.1, hok.2.2.2.1, hok.2.2.2.2.1,
    hok.2.2.2.2.2.1, hpref', hht', hq',
    fun idx hcap_i hht_i => ⟨fun hc => ?_, fun o b i q hl hn5 hnq hni => ?_⟩⟩
  · rw [(hkeep idx hht_i).1 hc]; exact (hok.2.2.2.2.2.2.2.2.2 idx hcap_i hht_i).1 hc
  · rw [(hkeep idx hht_i).2 o b i q hl hn5 hnq hni]
    exact (hok.2.2.2.2.2.2.2.2.2 idx hcap_i hht_i).2 o b i q hl hn5 hnq hni

theorem evCoreOk_unit_equiv {maxA : Nat} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {cv0 : Nat} {fl0 : BitVec 64} {ar0 : List (BitVec 32)}
    {arl0 g_len ctrl_off ht_off ht_sz : Nat} {scr0 scr_in : List (BitVec 32)} {s s' : FullState}
    (hok : EvCoreOk maxA c F0 F_cur cv0 fl0 ar0 arl0 g_len ctrl_off ht_off ht_sz scr0 scr_in s)
    (hlen' : s'.LengthsOk c) (hw' : FullWitnessInv c F0 F_cur s'.core)
    (hmk' : FullLitMarksClear c s') (hnd' : FullArenaVarsNodup s')
    (hext' : FullExtScratchOk c s') (hcl' : s'.core.cur_level = 0)
    (hdm' : s'.core.dense_mode ≠ 0#64) (hcv' : s'.core.cur_vars = s.core.cur_vars)
    (hfl' : s'.core.fuel = s.core.fuel) (har' : s'.core.arena = s.core.arena)
    (hal' : s'.core.arena_len = s.core.arena_len)
    (hsb' : s'.scratch.scratch_buf = s.scratch.scratch_buf)
    (hrepr' : FullCongReprInv F_cur (2 * s'.core.cur_vars) s'.core.repr) :
    EvCoreOk maxA c F0 F_cur cv0 fl0 ar0 arl0 g_len ctrl_off ht_off ht_sz scr0 scr_in s' := by
  have hcv0 : s'.core.cur_vars = cv0 := hcv'.trans hok.2.1
  refine ⟨⟨hlen', hw', hmk', hnd', hext', hcl', hdm'⟩, hcv0, hfl'.trans hok.2.2.1,
    har'.trans hok.2.2.2.1, hal'.trans hok.2.2.2.2.1, hcv0 ▸ hrepr', ?_, ?_, ?_, ?_⟩
  · intro idx hi; rw [hsb']; exact hok.2.2.2.2.2.2.1 idx hi
  · rw [hsb']; exact hok.2.2.2.2.2.2.2.1
  · rw [hsb']; exact hok.2.2.2.2.2.2.2.2.1
  · intro idx hi1 hi2; rw [hsb']; exact hok.2.2.2.2.2.2.2.2.2 idx hi1 hi2

theorem evCoreOk_set_ht {maxA : Nat} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {cv0 : Nat} {fl0 : BitVec 64} {ar0 : List (BitVec 32)}
    {arl0 g_len ctrl_off ht_off ht_sz : Nat} {scr0 scr_in : List (BitVec 32)} {s : FullState}
    {slot : Nat} {gv : BitVec 32} (hg_ht : g_len ≤ ht_off) (hslot : slot < ht_sz)
    (hht_cap : ht_off + ht_sz ≤ c.scratch_cap)
    (hok : EvCoreOk maxA c F0 F_cur cv0 fl0 ar0 arl0 g_len ctrl_off ht_off ht_sz scr0 scr_in s)
    (hgat : CongGateAt maxA F_cur cv0 scr0 g_len gv.toNat) (rsz' : BitVec 64) :
    EvCoreOk maxA c F0 F_cur cv0 fl0 ar0 arl0 g_len ctrl_off ht_off ht_sz scr0 scr_in
      { s with scratch := { s.scratch with
        scratch_buf := s.scratch.scratch_buf.set (ht_off + slot) gv, res_sz := rsz' } } := by
  have hlen := hok.1.1.scratch_ok.scratch_buf_len
  have hne : ∀ idx, idx < ht_off →
      (s.scratch.scratch_buf.set (ht_off + slot) gv)[idx]? = s.scratch.scratch_buf[idx]? :=
    fun idx hi => List.getElem?_set_ne (by omega)
  have hq' : CongQueueCtx c (s.scratch.scratch_buf.set (ht_off + slot) gv) g_len ctrl_off
      ht_off ht_sz := by
    rcases hok.2.2.2.2.2.2.2.2.1 with hc | ⟨o, b, i, q, hlo⟩
    · exact Or.inl hc
    · right; refine ⟨o, b, i, q, ?_⟩
      have hlay_l := hlo
      rcases hlo with ⟨_, _, _, _, _, _, _, _, _, _, h5, _, _, _, h1, h2, h3, h4, _, _, hql, hqok⟩
      exact congCtrlLayout_same_tail hlay_l (by simp [hlen])
        (by rw [hne (ctrl_off + 5) (by omega)]; exact hql)
        (fun j hj _ => hne (ctrl_off + j) (by omega))
        (fun k hk => by
          rw [hne (ctrl_off + 5) (by omega)] at hk
          have hmd := Nat.mod_lt ((s.scratch.scratch_buf[ctrl_off + 4]?.getD 0#32).toNat + k) h5
          rw [hne (ctrl_off + 4) (by omega),
            hne (q + ((s.scratch.scratch_buf[ctrl_off + 4]?.getD 0#32).toNat + k) % o) (by omega)]
          exact hqok k hk)
  refine ⟨fullDenseInvW_with_scr (fullDenseInvW_with_rsz hok.1 rsz') (by simp [hlen]),
    hok.2.1, hok.2.2.1, hok.2.2.2.1, hok.2.2.2.2.1, hok.2.2.2.2.2.1,
    fun idx hi => by rw [hne idx (by omega)]; exact hok.2.2.2.2.2.2.1 idx hi,
    congHtInv_set_gate hok.2.2.2.2.2.2.2.1 hslot (by rw [hlen]; omega) hgat, hq',
    fun idx hi1 hi2 => by rw [hne idx hi2]; exact hok.2.2.2.2.2.2.2.2.2 idx hi1 hi2⟩

/-! ## 2. Shared Sub-Block WP Lemmas (`ev_unit_wp`, `ev_equiv_enq2_wp`, `ev_trail_wp`) -/

theorem ev_unit_wp (Γ : Env)
    (hUnit : Γ.Has "full_cong_unit_fold" Spec.fullCongUnitFoldSpec)
    {maxA : Nat} {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {cv0 : Nat}
    {fl0 : BitVec 64} {ar0 : List (BitVec 32)} {arl0 g_len ctrl_off ht_off ht_sz : Nat}
    {scr0 scr_in : List (BitVec 32)} {s : FullState} {m : Mem 64} {lit next_ep : BitVec 32}
    {chgVal : Arg Val .bool} {k : Bool → Expr Val (fun ts => Tup Val ts → Mem 64 → Prop) [i64]}
    {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost}
    (hok : EvCoreOk maxA c F0 F_cur cv0 fl0 ar0 arl0 g_len ctrl_off ht_off ht_sz scr0 scr_in s)
    (hlit : lit.toNat < 2 * cv0)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause [lit.toNat]))
    (hm : (FullMem c s ⋆ R) m)
    (hQ2 : ∀ s' m', EvCoreOk maxA c F0 F_cur cv0 fl0 ar0 arl0 g_len ctrl_off ht_off ht_sz
      scr0 scr_in s' → F0.Unsat → (FullMem c s' ⋆ R) m' → Q (2#64, ()) m')
    (hk : ∀ chg' s' m', (chg' = true ∨ chg' = chgVal.val) →
      s'.core.tmp = s.core.tmp →
      EvCoreOk maxA c F0 F_cur cv0 fl0 ar0 arl0 g_len ctrl_off ht_off ht_sz scr0 scr_in s' →
      (FullMem c s' ⋆ R) m' → wp Γ Q X (k chg') m') :
    wp Γ Q X (evUnitExpr c.hdr lit next_ep chgVal k) m := by
  unfold evUnitExpr
  c0_call hUnit
  refine ⟨c, F0, F_cur, s, R, rfl, hok.1.1, hok.1.2.1, hok.1.2.2.1, hok.1.2.2.2.1,
    hok.1.2.2.2.2.1, hok.1.2.2.2.2.2.1, hok.1.2.2.2.2.2.2, hok.2.1 ▸ hok.2.2.2.2.2.1,
    hok.2.1 ▸ hlit, hent, hm, fun r s' m' hlen' hw' hmk' hnd' hext' hcl' hdm' hcv' hfl' har' hal'
      htmp' hsb' hrepr' _ hr2 hm' => ?_⟩
  have hok' := evCoreOk_unit_equiv hok hlen' hw' hmk' hnd' hext' hcl' hdm' hcv' hfl' har' hal'
    hsb' hrepr'
  ev_split
  · have ⟨_, huns⟩ := hr2 (by simpa using hc)
    c0_hsteps!; exact hQ2 s' m' hok' huns hm'
  · clear hc; c0_hsteps_nogrp
    refine LeanQbe.T.wp_join_group (ts := [.bool]) (fun (p, ()) m'' => (p = true ∨ p = chgVal.val) ∧
      EvCoreOk maxA c F0 F_cur cv0 fl0 ar0 arl0 g_len ctrl_off ht_off ht_sz scr0 scr_in s' ∧
      (FullMem c s' ⋆ R) m'')
      (fun _ ⟨p, ⟨⟩⟩ _ ⟨hp, hs', hm''⟩ => hk p s' _ hp htmp' hs' hm'') (fun J hJ => ?_)
    c0_hsplit
    · c0_hsteps!; exact hJ (true, ()) m' ⟨Or.inl rfl, hok', hm'⟩
    · c0_hsteps!; exact hJ (chgVal.val, ()) m' ⟨Or.inr rfl, hok', hm'⟩

theorem ev_equiv_enq2b_wp (Γ : Env)
    (hEquiv : Γ.Has "full_cong_equiv_fold" Spec.fullCongEquivFoldSpec)
    (hEnq : Γ.Has "full_cong_enq_var" Spec.fullCongEnqVarSpec)
    {maxA : Nat} {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {cv0 : Nat}
    {fl0 : BitVec 64} {ar0 : List (BitVec 32)} {arl0 g_len ctrl_off ht_off ht_sz : Nat}
    {scr0 scr_in : List (BitVec 32)} {s : FullState} {m : Mem 64} {a b b_enq next_ep : BitVec 32}
    {ctrl64 : BitVec 64} {chgVal : Arg Val .bool}
    {k : Bool → Expr Val (fun ts => Tup Val ts → Mem 64 → Prop) [i64]}
    {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost}
    (hg_ht : g_len ≤ ht_off) (hctrl : ctrl64.toNat = ctrl_off)
    (hok : EvCoreOk maxA c F0 F_cur cv0 fl0 ar0 arl0 g_len ctrl_off ht_off ht_sz scr0 scr_in s)
    (ha : a.toNat < 2 * cv0) (hb : b.toNat < 2 * cv0)
    (heqv : LitEquiv (cnfOfClauses F_cur) a.toNat b.toNat)
    (hm : (FullMem c s ⋆ R) m)
    (hQ2 : ∀ s' m', EvCoreOk maxA c F0 F_cur cv0 fl0 ar0 arl0 g_len ctrl_off ht_off ht_sz
      scr0 scr_in s' → F0.Unsat → (FullMem c s' ⋆ R) m' → Q (2#64, ()) m')
    (hk : ∀ chg' s' m', (chg' = true ∨ chg' = chgVal.val) →
      EvCoreOk maxA c F0 F_cur cv0 fl0 ar0 arl0 g_len ctrl_off ht_off ht_sz scr0 scr_in s' →
      (FullMem c s' ⋆ R) m' → wp Γ Q X (k chg') m') :
    wp Γ Q X (evEquivEnq2bExpr c.hdr ctrl64 a b b_enq next_ep chgVal k) m := by
  unfold evEquivEnq2bExpr; subst hctrl
  c0_call hEquiv
  refine ⟨c, F0, F_cur, s, R, rfl, hok.1.1, hok.1.2.1, hok.1.2.2.1, hok.1.2.2.2.1,
    hok.1.2.2.2.2.1, hok.1.2.2.2.2.2.1, hok.1.2.2.2.2.2.2, hok.2.1 ▸ hok.2.2.2.2.2.1,
    hok.2.1 ▸ ha, hok.2.1 ▸ hb, heqv, hm, fun r s' m' hlen' hw' hmk' hnd' hext' hcl' hdm' hcv'
      hfl' har' hal' _ hsb' hrepr' _ hr2 hm' => ?_⟩
  have hok' := evCoreOk_unit_equiv hok hlen' hw' hmk' hnd' hext' hcl' hdm' hcv' hfl' har' hal'
    hsb' hrepr'
  ev_split
  · have huns := hr2 (by simpa using hc); c0_hsteps!; exact hQ2 s' m' hok' huns hm'
  · clear hc; c0_hsteps_nogrp
    refine LeanQbe.T.wp_join_group (ts := [.bool])
      (fun (p, ()) m'' => (p = true ∨ p = chgVal.val) ∧
        ∃ sf, EvCoreOk maxA c F0 F_cur cv0 fl0 ar0 arl0 g_len ctrl64.toNat ht_off ht_sz
          scr0 scr_in sf ∧ (FullMem c sf ⋆ R) m'')
      (fun _ ⟨p, ⟨⟩⟩ _ ⟨hp, sf, hsf, hm''⟩ => hk p sf _ hp hsf hm'') (fun J hJ => ?_)
    c0_hsplit
    · clear hc; c0_hsteps!; c0_call hEnq
      refine ⟨c, s', g_len, ht_off, ht_sz, R, rfl, hok'.1.1, hok'.2.2.2.2.2.2.2.2.1, hm',
        fun scr1 m1 hl1 hq1 hcap1 hlay1 hm1 => ?_⟩
      let s1 : FullState := { s' with scratch := { s'.scratch with scratch_buf := scr1 } }
      have hok1 := evCoreOk_enq hg_ht hok' hl1 hq1 hcap1 hlay1
      c0_hsteps!; c0_call hEnq
      refine ⟨c, s1, g_len, ht_off, ht_sz, R, rfl, hok1.1.1, hok1.2.2.2.2.2.2.2.2.1, hm1,
        fun scr2 m2 hl2 hq2 hcap2 hlay2 hm2 => ?_⟩
      let s2 : FullState := { s1 with scratch := { s1.scratch with scratch_buf := scr2 } }
      have hok2 := evCoreOk_enq hg_ht hok1 hl2 hq2 hcap2 hlay2
      c0_hsteps!; exact hJ (true, ()) m2 ⟨Or.inl rfl, s2, hok2, hm2⟩
    · c0_hsteps!; exact hJ (chgVal.val, ()) m' ⟨Or.inr rfl, s', hok', hm'⟩

theorem ev_equiv_enq2_wp (Γ : Env)
    (hEquiv : Γ.Has "full_cong_equiv_fold" Spec.fullCongEquivFoldSpec)
    (hEnq : Γ.Has "full_cong_enq_var" Spec.fullCongEnqVarSpec)
    {maxA : Nat} {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {cv0 : Nat}
    {fl0 : BitVec 64} {ar0 : List (BitVec 32)} {arl0 g_len ctrl_off ht_off ht_sz : Nat}
    {scr0 scr_in : List (BitVec 32)} {s : FullState} {m : Mem 64} {a b next_ep : BitVec 32}
    {ctrl64 : BitVec 64} {chgVal : Arg Val .bool}
    {k : Bool → Expr Val (fun ts => Tup Val ts → Mem 64 → Prop) [i64]}
    {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost}
    (hg_ht : g_len ≤ ht_off) (hctrl : ctrl64.toNat = ctrl_off)
    (hok : EvCoreOk maxA c F0 F_cur cv0 fl0 ar0 arl0 g_len ctrl_off ht_off ht_sz scr0 scr_in s)
    (ha : a.toNat < 2 * cv0) (hb : b.toNat < 2 * cv0)
    (heqv : LitEquiv (cnfOfClauses F_cur) a.toNat b.toNat)
    (hm : (FullMem c s ⋆ R) m)
    (hQ2 : ∀ s' m', EvCoreOk maxA c F0 F_cur cv0 fl0 ar0 arl0 g_len ctrl_off ht_off ht_sz
      scr0 scr_in s' → F0.Unsat → (FullMem c s' ⋆ R) m' → Q (2#64, ()) m')
    (hk : ∀ chg' s' m', (chg' = true ∨ chg' = chgVal.val) →
      EvCoreOk maxA c F0 F_cur cv0 fl0 ar0 arl0 g_len ctrl_off ht_off ht_sz scr0 scr_in s' →
      (FullMem c s' ⋆ R) m' → wp Γ Q X (k chg') m') :
    wp Γ Q X (evEquivEnq2Expr c.hdr ctrl64 a b next_ep chgVal k) m :=
  ev_equiv_enq2b_wp Γ hEquiv hEnq hg_ht hctrl hok ha hb heqv hm hQ2 hk

theorem ev_trail_wp (Γ : Env)
    (hFind : Γ.Has "full_cong_find" Spec.fullCongFindSpec)
    (hEnq : Γ.Has "full_cong_enq_var" Spec.fullCongEnqVarSpec)
    {maxA : Nat} {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {cv0 : Nat}
    {fl0 : BitVec 64} {ar0 : List (BitVec 32)} {arl0 g_len ctrl_off ht_off ht_sz : Nat}
    {scr0 scr_in : List (BitVec 32)} {s0 : FullState} {m0 : Mem 64} {ctrl64 te0 : BitVec 64}
    {chg keep : Bool} {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost}
    (hg_ht : g_len ≤ ht_off) (hctrl : ctrl64.toNat = ctrl_off)
    (hok0 : EvCoreOk maxA c F0 F_cur cv0 fl0 ar0 arl0 g_len ctrl_off ht_off ht_sz scr0 scr_in s0)
    (hte0 : te0.toNat ≤ s0.core.trail_end)
    (hm0 : (FullMem c s0 ⋆ R) m0)
    (hQ : ∀ (r : BitVec 64) s' m',
      EvCoreOk maxA c F0 F_cur cv0 fl0 ar0 arl0 g_len ctrl_off ht_off ht_sz scr0 scr_in s' →
      ((r &&& 2#64) = 0#64 →
        r = (if chg then 1#64 else 0#64) ||| (if keep then 4#64 else 0#64)) →
      ((r &&& 2#64) ≠ 0#64 → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m') :
    wp Γ Q X (evTrailExpr c.hdr ctrl64 c.pRepr c.pTrail te0 chg keep) m0 := by
  unfold evTrailExpr; subst hctrl; ev_unfold_ast; c0_hsteps_nogrp
  refine wp_loop_inv
    (Inv := fun (te, ()) mi => ∃ si : FullState, te.toNat ≤ si.core.trail_end ∧
      EvCoreOk maxA c F0 F_cur cv0 fl0 ar0 arl0 g_len ctrl64.toNat ht_off ht_sz scr0 scr_in si ∧
      (FullMem c si ⋆ R) mi)
    (μ := fun (te, ()) _ => c.max_vars - te.toNat)
    (fun _ hJ => by c0_hsteps!; exact hJ (te0, ()) m0 ⟨s0, hte0, hok0, hm0⟩)
    (fun _ ⟨te, ⟨⟩⟩ mi ⟨si, hte_i, hoki, hmi⟩ ihi => ?_)
  have hte_le : si.core.trail_end ≤ c.max_vars :=
    Nat.le_trans hoki.1.1.core_ok.trail_end_le hoki.1.1.core_ok.cur_vars_le
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have htl_len : si.core.trl.length = c.max_vars := hoki.1.1.core_ok.trl_len
  c0_hsteps_nogrp; c0_hsplit
  · have hlt : te.toNat < si.core.trail_end := by omega
    have hte_arr : te.toNat < si.core.trl.length := by omega
    have htl_lt : (si.core.trl[te.toNat]'hte_arr).toNat < 2 * cv0 := by
      rw [← hoki.2.1]
      simpa [List.getElem?_eq_getElem hte_arr] using hoki.1.2.1.trail_lits_lt te.toNat hlt
    c0_hsteps!; c0_call hEnq
    refine ⟨c, si, g_len, ht_off, ht_sz, R, rfl, hoki.1.1, hoki.2.2.2.2.2.2.2.2.1, hmi,
      fun scr1 m1 hl1 hq1 hcap1 hlay1 hm1 => ?_⟩
    let s1 : FullState := { si with scratch := { si.scratch with scratch_buf := scr1 } }
    have hok1 := evCoreOk_enq hg_ht hoki hl1 hq1 hcap1 hlay1
    c0_call hFind
    refine ⟨F_cur, 2 * cv0, s1.core.repr, ArrayField.repr.rest c s1 ⋆ R,
      hok1.2.2.2.2.2.1, htl_lt, focus_full_repr hm1,
      fun r repr2 m2 hrl2 hrepr2 _ _ _ hm2 => ?_⟩
    let s2 : FullState := { s1 with core := { s1.core with repr := repr2 } }
    have hok2 := evCoreOk_repr hok1 (hrl2.trans hok1.1.1.core_ok.repr_len) hrepr2
    have hm2' := unfocus_full_repr hm2
    c0_hsteps!; c0_call hEnq
    refine ⟨c, s2, g_len, ht_off, ht_sz, R, rfl, hok2.1.1, hok2.2.2.2.2.2.2.2.2.1, hm2',
      fun scr3 m3 hl3 hq3 hcap3 hlay3 hm3 => ?_⟩
    let s3 : FullState := { s2 with scratch := { s2.scratch with scratch_buf := scr3 } }
    have hok3 := evCoreOk_enq hg_ht hok2 hl3 hq3 hcap3 hlay3
    have hte1 : (te + 1#64).toNat = te.toNat + 1 := bv64_add1_lt (by omega)
    c0_hsteps!
    exact ihi (te + 1#64, ()) m3 (by dsimp only; rw [hte1]; omega)
      ⟨s3, by rw [hte1]; exact hlt, hok3, hm3⟩
  · have huns : F0.Unsat := unsat_of_inconsistent_w hoki.1.2.1 (by simpa using hc)
    c0_hsteps!
    exact hQ 2#64 si mi hoki (fun h => absurd h (by decide)) (fun _ => huns) hmi
  · clear hc ihi
    refine LeanQbe.T.wp_join_group (ts := [i64]) (fun (b1, ()) mc =>
      b1 = (if chg then 1#64 else 0#64) ∧ mc = mi) ?_ ?_
    · rintro _ ⟨b1, ⟨⟩⟩ mc ⟨rfl, hmc⟩; subst hmc
      refine LeanQbe.T.wp_join_group (ts := [i64]) (fun (b4, ()) md =>
        b4 = (if keep then 4#64 else 0#64) ∧ md = mc) ?_ ?_
      · rintro _ ⟨b4, ⟨⟩⟩ md ⟨rfl, hmd⟩; subst hmd
        c0_hsteps!
        have h0 : (((if chg then 1#64 else 0#64) |||
            (if keep then 4#64 else 0#64)) &&& 2#64) = 0#64 := by
          cases chg <;> cases keep <;> decide
        exact hQ _ si md hoki (fun _ => rfl) (fun h => absurd h0 h) hmi
      · intro J4 hJ4; c0_hsplit
        · c0_hsteps!; exact hJ4 _ mc ⟨by simp [hc], rfl⟩
        · c0_hsteps!; exact hJ4 _ mc ⟨by simp [hc], rfl⟩
    · intro J1 hJ1; c0_hsplit
      · c0_hsteps!; exact hJ1 _ mi ⟨by simp [hc], rfl⟩
      · c0_hsteps!; exact hJ1 _ mi ⟨by simp [hc], rfl⟩

/-! ## 3. Shared Pure Semantic, BitVec & List Lemmas -/

theorem ev_bv8_dom_eval {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) (hcl0 : k.cur_level = 0)
    {l : BitVec 32} (hl : l.toNat < 2 * k.cur_vars) {v : BitVec 8}
    (hv : k.vals[l.toNat]?.getD 0#8 = v) :
    (v = 1#8 → ∀ α : Nat → Bool, (cnfOfClauses F_cur).Sat α → evalLitVal α l.toNat = true) ∧
    (v = 0xFF#8 → ∀ α : Nat → Bool, (cnfOfClauses F_cur).Sat α → evalLitVal α l.toNat = false) :=
  ⟨fun h1 _ hα => entails_eval_true (vals1_entails hw hcl0 hl (hv.trans h1)) hα,
   fun hff _ hα => entails_neg_eval_false (valsff_entails_neg hw hcl0 hl (hv.trans hff)) hα⟩

theorem ev_litEquiv_of_eval {F : CNF Nat} {a b : Nat}
    (h : ∀ α : Nat → Bool, F.Sat α → evalLitVal α a = evalLitVal α b) :
    LitEquiv F a b := by
  refine ⟨entails_of_eval_mem fun α hα => ?_, entails_of_eval_mem fun α hα => ?_⟩
  · have he := h α hα
    cases ha : evalLitVal α a <;> cases hb : evalLitVal α b <;> simp_all [evalLitVal_litNeg]
  · have he := h α hα
    cases ha : evalLitVal α a <;> cases hb : evalLitVal α b <;> simp_all [evalLitVal_litNeg]

theorem ev_entails_of_eval {F : CNF Nat} {l : Nat}
    (h : ∀ α : Nat → Bool, F.Sat α → evalLitVal α l = true) :
    F.EntailsClause (cnfClause [l]) :=
  entails_of_eval_mem fun α hα => ⟨l, by simp, h α hα⟩

theorem ev_bv32_xor1_lt_cv {x : BitVec 32} {cv : Nat} (hx : x.toNat < 2 * cv) :
    (x ^^^ 1#32).toNat < 2 * cv := by
  rw [bv32_xor1_eq_litNeg, litNeg_eq]; split <;> omega

theorem ev_bv32_and1_eq01 (x : BitVec 32) : (x &&& 1#32) = 0#32 ∨ (x &&& 1#32) = 1#32 := by
  have hlt : (x &&& 1#32).toNat < 2 := by
    rw [BitVec.toNat_and, show (1#32 : BitVec 32).toNat = 1 from rfl, Nat.and_one_is_mod]
    exact Nat.mod_lt _ (by decide)
  rcases (by omega : (x &&& 1#32).toNat = 0 ∨ (x &&& 1#32).toNat = 1) with h0 | h1
  · exact Or.inl (BitVec.eq_of_toNat_eq h0)
  · exact Or.inr (BitVec.eq_of_toNat_eq h1)

theorem ev_xor1_bit01_lt {x b : BitVec 32} {cv : Nat} (hx : x.toNat < 2 * cv)
    (hb : b = 0#32 ∨ b = 1#32) : (x ^^^ b).toNat < 2 * cv := by
  rcases hb with rfl | rfl
  · simpa using hx
  · exact ev_bv32_xor1_lt_cv hx

theorem ev_bv32_sub1_toNat {x : BitVec 32} (hx : 0 < x.toNat) :
    (x - 1#32).toNat = x.toNat - 1 := by
  bv_omega

theorem ev_bv32_add2_lt_of {x : BitVec 32} (h : x.toNat + 2 < 2 ^ 32) :
    (x + 2#32).toNat = x.toNat + 2 := by
  bv_omega

theorem ev_bv32_ule_le {a b : BitVec 32} (h : a.ule b = true) : a.toNat ≤ b.toNat := by
  unfold BitVec.ule at h; simpa using h

theorem ev_bv32_ule_not_le {a b : BitVec 32} (h : a.ule b = false) : b.toNat < a.toNat := by
  unfold BitVec.ule at h; simp only [decide_eq_false_iff_not, Nat.not_le] at h; exact h

theorem ev_bv32_truncate_u64_of_lt (g : BitVec 64) (hg : g.toNat < 2 ^ 32) :
    (g.truncate 32).toNat = g.toNat := by
  change (g.setWidth 32).toNat = g.toNat
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt hg]

theorem ev_ht_slot_lt {hv ht_sz : BitVec 64} (hpos : 0 < ht_sz.toNat) :
    (hv &&& (ht_sz - 1#64)).toNat < ht_sz.toNat := by
  rw [BitVec.toNat_and, bv64_sub1_pos hpos]
  exact Nat.lt_of_le_of_lt Nat.and_le_right (by omega)

theorem ev_mem_take_of_lt {α : Type} {xs : List α} {n k : Nat} (hk : k < n) (hn : n ≤ xs.length) :
    xs[k]'(by omega) ∈ xs.take n := by
  have hlt : k < (xs.take n).length := by rw [List.length_take]; omega
  simpa [List.getElem_take] using List.getElem_mem hlt

theorem ev_lt_take_of_mem {α : Type} {xs : List α} {n : Nat} {x : α} (h : x ∈ xs.take n) :
    ∃ k < min n xs.length, xs[k]? = some x := by
  obtain ⟨k, hk, hget⟩ := List.mem_iff_getElem.mp h
  rw [List.length_take] at hk; rw [List.getElem_take] at hget
  exact ⟨k, hk, by rw [List.getElem?_eq_getElem (by omega), hget]⟩

theorem ev_list_drop_take_succ {α : Type} (xs : List α) {i k : Nat} (hi : i < xs.length) :
    (xs.drop i).take (k + 1) = xs[i]'hi :: (xs.drop (i + 1)).take k := by
  rw [List.drop_eq_getElem_cons hi, List.take_succ_cons]

theorem ev_xor_bit0_eval (α : Nat → Bool) (x : BitVec 32) :
    evalLitVal α (x &&& ~~~1#32).toNat =
      (evalLitVal α x.toNat != decide ((x &&& 1#32) = 1#32)) := by
  rcases Nat.mod_two_eq_zero_or_one x.toNat with hp | hp
  · have h0 : x &&& 1#32 = 0#32 := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_and, show (1#32 : BitVec 32).toNat = 2 ^ 1 - 1 from rfl,
        Nat.and_two_pow_sub_one_eq_mod, hp]; rfl
    have he : (x &&& ~~~1#32) = x := by
      apply BitVec.eq_of_toNat_eq; rw [m6_bv32_and_not1_toNat]; omega
    rw [h0, he]; simp
  · have h1 : x &&& 1#32 = 1#32 := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_and, show (1#32 : BitVec 32).toNat = 2 ^ 1 - 1 from rfl,
        Nat.and_two_pow_sub_one_eq_mod, hp]
    have he : (x &&& ~~~1#32).toNat = litNeg x.toNat := by
      rw [m6_bv32_and_not1_toNat, litNeg_eq]
      split <;> first | exact absurd hp (by omega) | omega
    rw [h1, he, evalLitVal_litNeg]; simp

theorem ev_ite_eval_congr {f : CNF Nat} {lhs0 c0 t0 e0 lhs c t e : Nat}
    (hi : IteGateDef f lhs0 c0 t0 e0)
    (hl : LitEquiv f lhs0 lhs) (hc : LitEquiv f c0 c)
    (ht : LitEquiv f t0 t) (he : LitEquiv f e0 e) :
    IteGateDef f lhs c t e :=
  iteGateDef_of_eval_eq fun α hα => by
    rw [← litEquiv_eval hα hl, ← litEquiv_eval hα hc, ← litEquiv_eval hα ht,
      ← litEquiv_eval hα he, iteGateDef_eval hα hi]

theorem ev_iteGateDef_flip_cond {f : CNF Nat} {lhs c t e : Nat}
    (h : IteGateDef f lhs c t e) : IteGateDef f lhs (litNeg c) e t :=
  iteGateDef_of_eval_eq fun α hα => by
    rw [iteGateDef_eval hα h, evalLitVal_litNeg]; cases evalLitVal α c <;> rfl

theorem ev_iteGateDef_flip_out {f : CNF Nat} {lhs c t e : Nat}
    (h : IteGateDef f lhs c t e) : IteGateDef f (litNeg lhs) c (litNeg t) (litNeg e) :=
  iteGateDef_of_eval_eq fun α hα => by
    rw [evalLitVal_litNeg, evalLitVal_litNeg, evalLitVal_litNeg, iteGateDef_eval hα h]
    cases evalLitVal α c <;> rfl

end

end LeanQbe.T.Examples.Kissat.Proof.Congruence
