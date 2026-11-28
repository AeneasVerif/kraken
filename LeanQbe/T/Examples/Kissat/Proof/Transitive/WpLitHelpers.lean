/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Transitive.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Transitive.UnrollInv
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics1
public import LeanQbe.T.Examples.Kissat.Src.Transitive

/-!
# Factored Sub-Proofs for `full_trans_lit_m6` (`Proof.Transitive.WpLitHelpers`)

Defines the extracted AST subexpressions `trLitPostExpr` (post-loop compaction and unit-addition)
and `trLitBfsExpr` (BFS watch-list scan step), together with their weakest-precondition lemmas
`tr_lit_post_wp` and `tr_lit_bfs_wp`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Transitive

open Std.Sat
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.C0HeadStep
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Transitive.Spec
open LeanQbe.T.Examples.Kissat.Src.Transitive
open Kraken.Bedrock2.Test
open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics

private theorem tr_lit_push_bounds {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 st_pre st : FullState} {src saved ot : Nat} (hw0 : FullWitnessInv c F0 F_cur s0.core)
    (hpre_vals : st_pre.core.vals = s0.core.vals)
    (hpre_te : st_pre.core.trail_end = s0.core.trail_end)
    (hpre_trl : ∀ i < s0.core.trail_end, st_pre.core.trl[i]? = s0.core.trl[i]?)
    (hpre_cv : st_pre.core.cur_vars = s0.core.cur_vars)
    (h : TransUnrollInv c F0 F_cur s0 st_pre src saved st) (hot : ot < 2 * st_pre.core.cur_vars)
    (hzero : st.core.vals[ot]?.getD 0#8 = 0#8)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause [src, ot])) :
    let te := st.core.trail_end
    te < st.core.cur_vars ∧ te < st.core.trl.length ∧ ot < st.core.vals.length ∧
    (ot ^^^ 1) < st.core.vals.length ∧
    (BitVec.setWidth 64 (BitVec.ofNat 32 ot)).toNat = ot ∧
    (BitVec.setWidth 64 ((BitVec.ofNat 32 ot) ^^^ 1#32)).toNat = ot ^^^ 1 ∧
    (te < 2 ^ 64 ∧ (BitVec.ofNat 64 te + 1#64).toNat = te + 1) ∧
    TransUnrollInv c F0 F_cur s0 st_pre src saved
      { st with core := { st.core with
        vals := (st.core.vals.set ot 1#8).set (ot ^^^ 1) 0xFF#8,
        trl := st.core.trl.set te (BitVec.ofNat 32 ot), trail_end := te + 1 } } := by
  obtain ⟨hte_lt, hpush⟩ := h.push hw0 hpre_vals hpre_te hpre_trl hpre_cv hot hzero hent
  have hcv : st.core.cur_vars = st_pre.core.cur_vars := by rw [h.same_core]
  have hmx := h.len_ok.core_ok.cur_vars_le
  have htrl_l := h.len_ok.core_ok.trl_len
  have hte_bv : st.core.trail_end < 2 ^ 64 := (tr_bnds h.len_ok.core_ok).2.2.2
  have hv_ot := tr_vals_lt h.len_ok.core_ok (by rw [hcv]; exact hot)
  have hv_not := tr_vals_lt h.len_ok.core_ok (by rw [hcv]; exact litNeg_lt_two_mul hot)
  have hot_bv : (BitVec.ofNat 32 ot).toNat = ot := tr_bv32_ofNat_eq (c := c) (by omega)
  have hsw : (BitVec.setWidth 64 (BitVec.ofNat 32 ot)).toNat = ot := by
    rw [tr_bv32_setWidth64, hot_bv]
  have hsw_not : (BitVec.setWidth 64 ((BitVec.ofNat 32 ot) ^^^ 1#32)).toNat = ot ^^^ 1 := by
    rw [tr_bv32_setWidth64, tr_bv32_xor1, hot_bv]
  have hcmv := c.hmaxv; unfold dimacsBound at hcmv
  exact ⟨hcv ▸ hte_lt, by omega, hv_ot, hv_not, hsw, hsw_not, ⟨hte_bv, by bv_omega⟩, hpush⟩

private theorem tr_lit_push_watch_mono {F_cur : List (List Nat)} {st : FullState}
    {nql wp rem nt : Nat} {vals' : List (BitVec 8)} {trl' : List (BitVec 32)} {te' : Nat}
    (hts : TombWatchSliceOk F_cur st.core nql wp rem nt) :
    TombWatchSliceOk F_cur { st.core with vals := vals', trl := trl', trail_end := te' }
      nql wp rem nt :=
  TombWatchSliceOk.mono (k := st.core)
    (k' := { st.core with vals := vals', trl := trl', trail_end := te' })
    (Nat.le_refl _) (fun _ h => h) (fun _ _ _ => rfl) hts

private theorem tr_lit_bfs_falsified {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 st_pre st : FullState} {src saved ql ot : Nat} (hw0 : FullWitnessInv c F0 F_cur s0.core)
    (hpre_vals : st_pre.core.vals = s0.core.vals)
    (hpre_cv : st_pre.core.cur_vars = s0.core.cur_vars)
    (hcl0 : s0.core.cur_level = 0) (h : TransUnrollInv c F0 F_cur s0 st_pre src saved st)
    (hot : ot < 2 * st.core.cur_vars)
    (hslt : (st.core.vals[ot]'(tr_vals_lt h.len_ok.core_ok hot) |>.signExtend 32).slt 0#32 = true)
    (h_src_ql : (cnfOfClauses F_cur).EntailsClause (cnfClause [src, ql]))
    (h_nql_ot : (cnfOfClauses F_cur).EntailsClause (cnfClause [ql ^^^ 1, ot])) :
    (cnfOfClauses F_cur).EntailsClause (cnfClause [src]) := by
  have hcv : st.core.cur_vars = st_pre.core.cur_vars := by rw [h.same_core]
  have hot_pre : ot < 2 * st_pre.core.cur_vars := hcv ▸ hot
  have hdom := h.vals_domain hw0 hpre_vals hpre_cv hot_pre
  have hget : st.core.vals[ot]?.getD 0#8 =
      st.core.vals[ot]'(tr_vals_lt h.len_ok.core_ok hot) := by
    simp [List.getElem?_eq_getElem (tr_vals_lt h.len_ok.core_ok hot)]
  have hff : st.core.vals[ot]?.getD 0#8 = 0xFF#8 := by
    rw [hget]; exact tr_vals_ff_of_domain (hget ▸ hdom) rfl hslt
  exact h.entails_src_of_falsified hw0 hpre_vals hpre_cv hcl0 hot_pre hff
    (entails_pair_trans h_src_ql h_nql_ot)

private theorem tr_lit_bfs_watch_end {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 st_pre st : FullState} {src off p end_v red saved nql : Nat}
    (ho : TransOuterInv c F0 F_cur s0 src off p end_v red st_pre)
    (hu : TransUnrollInv c F0 F_cur s0 st_pre src saved st) (hnql : nql < 2 * st.core.cur_vars) :
    let woff := fullWatchOffCore st.core nql
    let wsz := fullWatchSizeCore st.core nql
    woff + wsz ≤ st.core.wlen ∧
    (BitVec.setWidth 64 (st.core.wvec[2 * nql]'(by
      have := hu.len_ok.core_ok.wvec_len; have := hu.len_ok.core_ok.cur_vars_le; omega))).toNat =
      woff ∧
    (BitVec.setWidth 64 (st.core.wvec[2 * nql + 1]'(by
      have := hu.len_ok.core_ok.wvec_len; have := hu.len_ok.core_ok.cur_vars_le; omega))).toNat =
      wsz ∧
    ∃ nt, TombWatchSliceOk F_cur st.core nql woff wsz nt := by
  have ⟨hb, nt, hts⟩ := hu.watch_slice ho hnql
  have hvw := hu.len_ok.core_ok.wvec_len; have hcv := hu.len_ok.core_ok.cur_vars_le
  refine ⟨hb, ?_, ?_, nt, hts⟩
  · rw [tr_bv32_setWidth64]
    simp only [fullWatchOffCore,
      List.getElem?_eq_getElem (by omega : 2 * nql < st.core.wvec.length), Option.getD_some]
  · rw [tr_bv32_setWidth64]
    simp only [fullWatchSizeCore,
      List.getElem?_eq_getElem (by omega : 2 * nql + 1 < st.core.wvec.length), Option.getD_some]

/-- Post-loop watch-compaction and optional unit-addition subexpression of
`full_trans_lit_m6_body`. -/
abbrev trLitPostExpr (V : Ty → Type) (L : List Ty → Type)
    (p : Tup V [i64, i32, Ty.bool]) (ld_2 ld_3 : V i64)
    (p_19 p_29 : Tup V [i64]) (p_30 : Tup V [Ty.bool, i64, i64]) :
    Expr V L [Ty.bool] :=
  Expr.group (fun (_Js : Tup L [[i64]]) => Blocks.cons (fun (_p_31 : Tup V [i64]) => Expr.jnz
    (Arg.var p_30.fst) (Expr.let_
    { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var p.fst, Arg.imm 1048, ()) } fun
    (p_32 : Tup V [i64]) => Expr.load i64 (Arg.var p_32.fst) fun (ld : V i64) => Expr.let_
    { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var ld, Arg.imm 1, ()) } fun (p_33
    : Tup V [i64]) => Expr.let_
    { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var p.fst, Arg.imm 1048, ()) } fun
    (p_34 : Tup V [i64]) => Expr.store (Arg.var p_33.fst) (Arg.var p_34.fst) (Expr.call (as :=
    [i64, i32]) (bs := [Ty.bool]) "full_add_unit" (Arg.var p.fst, Arg.var p.snd.fst, ()) fun (p
    : Tup V [Ty.bool]) => Expr.ret (Arg.var p.fst, ()))) (Expr.ret (Arg.imm true, ())))
    Blocks.nil) fun (Js : Tup L [[i64]]) => Expr.let_
    { sig := [i64, i64],
      code := OpCode.cmp CmpOp.ugt i64 Ty.bool rfl,
      args := (Arg.var p_30.snd.fst, Arg.imm 0, ()) }
    fun (p_31 : Tup V [Ty.bool]) => Expr.jnz (Arg.var p_31.fst) (Expr.group (fun (Js_1 : Tup L
    [[i64, i64]]) => Blocks.cons (fun (p_32 : Tup V [i64, i64]) => Expr.let_
    { sig := [i64, i64],
      code := OpCode.cmp CmpOp.ult i64 Ty.bool rfl,
      args := (Arg.var p_32.fst, Arg.var p_29.fst, ()) }
    fun (p_33 : Tup V [Ty.bool]) => Expr.jnz (Arg.var p_33.fst) (Expr.let_
    { sig := [i64, i64], code := OpCode.mul i64, args := (Arg.var p_32.fst, Arg.imm 4, ()) } fun
    (p : Tup V [i64]) => Expr.let_
    { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var ld_3, Arg.var p.fst, ()) } fun
    (p : Tup V [i64]) => Expr.load i32 (Arg.var p.fst) fun (ld : V i32) => Expr.group (fun (_Js
    : Tup L [[i64, i64]]) => Blocks.cons (fun (p : Tup V [i64, i64]) => Expr.jump Js_1.fst
    (Arg.var p.fst, Arg.var p.snd.fst, ())) Blocks.nil) fun (Js : Tup L [[i64, i64]]) =>
    Expr.let_
    { sig := [i32, i32],
      code := OpCode.cmp CmpOp.eq i32 Ty.bool rfl,
      args := (Arg.var ld, Arg.imm 4294967295, ()) }
    fun (p : Tup V [Ty.bool]) => Expr.jnz (Arg.var p.fst) (Expr.let_
    { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var p_32.fst, Arg.imm 1, ()) } fun
    (p : Tup V [i64]) => Expr.jump Js.fst (Arg.var p.fst, Arg.var p_32.snd.fst, ())) (Expr.group
    (fun (_Js_2 : Tup L [[i64, i64]]) => Blocks.cons (fun (p : Tup V [i64, i64]) => Expr.jump
    Js.fst (Arg.var p.fst, Arg.var p.snd.fst, ())) Blocks.nil) fun (Js : Tup L [[i64, i64]]) =>
    Expr.let_
    { sig := [i32, i32], code := OpCode.and i32, args := (Arg.var ld, Arg.imm 2147483648, ()) }
    fun (p : Tup V [i32]) => Expr.let_
    { sig := [i32, i32],
      code := OpCode.cmp CmpOp.ne i32 Ty.bool rfl,
      args := (Arg.var p.fst, Arg.imm 0, ()) }
    fun (p : Tup V [Ty.bool]) => Expr.jnz (Arg.var p.fst) (Expr.let_
    { sig := [i64, i64], code := OpCode.mul i64, args := (Arg.var p_32.snd.fst, Arg.imm 4, ()) }
    fun (p : Tup V [i64]) => Expr.let_
    { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var ld_3, Arg.var p.fst, ()) } fun
    (p : Tup V [i64]) => Expr.store (Arg.var ld) (Arg.var p.fst) (Expr.let_
    { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var p_32.snd.fst, Arg.imm 1, ()) }
    fun (p : Tup V [i64]) => Expr.let_
    { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var p_32.fst, Arg.imm 1, ()) } fun
    (p_34 : Tup V [i64]) => Expr.jump Js.fst (Arg.var p_34.fst, Arg.var p.fst, ()))) (Expr.group
    (fun (_Js_2 : Tup L [[i64, i64]]) => Blocks.cons (fun (p : Tup V [i64, i64]) => Expr.jump
    Js.fst (Arg.var p.fst, Arg.var p.snd.fst, ())) Blocks.nil) fun (Js : Tup L [[i64, i64]]) =>
    Expr.let_
    { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var p_32.fst, Arg.imm 1, ()) } fun
    (p : Tup V [i64]) => Expr.let_
    { sig := [i64, i64],
      code := OpCode.cmp CmpOp.ult i64 Ty.bool rfl,
      args := (Arg.var p.fst, Arg.var p_29.fst, ()) }
    fun (p : Tup V [Ty.bool]) => Expr.jnz (Arg.var p.fst) (Expr.let_
    { sig := [i64, i64], code := OpCode.mul i64, args := (Arg.var p_32.snd.fst, Arg.imm 4, ()) }
    fun (p : Tup V [i64]) => Expr.let_
    { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var ld_3, Arg.var p.fst, ()) } fun
    (p : Tup V [i64]) => Expr.store (Arg.var ld) (Arg.var p.fst) (Expr.let_
    { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var p_32.snd.fst, Arg.imm 1, ()) }
    fun (p : Tup V [i64]) => Expr.let_
    { sig := [i64, i64], code := OpCode.mul i64, args := (Arg.var p.fst, Arg.imm 4, ()) } fun (p
    : Tup V [i64]) => Expr.let_
    { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var ld_3, Arg.var p.fst, ()) } fun
    (p : Tup V [i64]) => Expr.let_
    { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var p_32.fst, Arg.imm 1, ()) } fun
    (p_34 : Tup V [i64]) => Expr.let_
    { sig := [i64, i64], code := OpCode.mul i64, args := (Arg.var p_34.fst, Arg.imm 4, ()) } fun
    (p_35 : Tup V [i64]) => Expr.let_
    { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var ld_3, Arg.var p_35.fst, ()) }
    fun (p_36 : Tup V [i64]) => Expr.load i32 (Arg.var p_36.fst) fun (ld : V i32) => Expr.store
    (Arg.var ld) (Arg.var p.fst) (Expr.let_
    { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var p_32.snd.fst, Arg.imm 2, ()) }
    fun (p : Tup V [i64]) => Expr.let_
    { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var p_32.fst, Arg.imm 2, ()) } fun
    (p_37 : Tup V [i64]) => Expr.jump Js.fst (Arg.var p_37.fst, Arg.var p.fst, ())))) (Expr.let_
    { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var p_32.fst, Arg.imm 1, ()) } fun
    (p : Tup V [i64]) => Expr.jump Js.fst (Arg.var p.fst, Arg.var p_32.snd.fst, ())))))
    (Expr.group (fun (Js_2 : Tup L [[i64]]) => Blocks.cons (fun (p_34 : Tup V [i64]) =>
    Expr.let_
    { sig := [i64, i64],
      code := OpCode.cmp CmpOp.ult i64 Ty.bool rfl,
      args := (Arg.var p_34.fst, Arg.var p_29.fst, ()) }
    fun (p_35 : Tup V [Ty.bool]) => Expr.jnz (Arg.var p_35.fst) (Expr.let_
    { sig := [i64, i64], code := OpCode.mul i64, args := (Arg.var p_34.fst, Arg.imm 4, ()) } fun
    (p : Tup V [i64]) => Expr.let_
    { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var ld_3, Arg.var p.fst, ()) } fun
    (p : Tup V [i64]) => Expr.store (t := i32) (Arg.imm 4294967295) (Arg.var p.fst) (Expr.let_
    { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var p_34.fst, Arg.imm 1, ()) } fun
    (p : Tup V [i64]) => Expr.jump Js_2.fst (Arg.var p.fst, ()))) (Expr.let_
    { sig := [i32], code := OpCode.zext 32 64, args := (Arg.var p.snd.fst, ()) } fun (p_36 : Tup
    V [i64]) => Expr.let_ { sig := [i32], code := OpCode.sext 32 64, args := (Arg.imm 1, ()) }
    fun (p_37 : Tup V [i64]) => Expr.let_
    { sig := [i64, i64],
      code := OpCode.shl i64,
      args := (Arg.var p_36.fst, Arg.var p_37.fst, ()) }
    fun (p_38 : Tup V [i64]) => Expr.let_
    { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var p_38.fst, Arg.imm 1, ()) } fun
    (p_39 : Tup V [i64]) => Expr.let_
    { sig := [i64, i64], code := OpCode.mul i64, args := (Arg.var p_39.fst, Arg.imm 4, ()) } fun
    (p_40 : Tup V [i64]) => Expr.let_
    { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var ld_2, Arg.var p_40.fst, ()) }
    fun (p_41 : Tup V [i64]) => Expr.let_
    { sig := [i64, i64],
      code := OpCode.sub i64,
      args := (Arg.var p_29.fst, Arg.var p_19.fst, ()) }
    fun (p_42 : Tup V [i64]) => Expr.let_
    { sig := [i64, i64],
      code := OpCode.sub i64,
      args := (Arg.var p_42.fst, Arg.var p_30.snd.fst, ()) }
    fun (p_43 : Tup V [i64]) => Expr.let_
    { sig := [i64], code := OpCode.trunc 64 32, args := (Arg.var p_43.fst, ()) } fun (p_44 : Tup
    V [i32]) => Expr.store (Arg.var p_44.fst) (Arg.var p_41.fst) (Expr.let_
    { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var p.fst, Arg.imm 464, ()) } fun
    (p_45 : Tup V [i64]) => Expr.load i64 (Arg.var p_45.fst) fun (ld : V i64) => Expr.let_
    { sig := [i64, i64],
      code := OpCode.add i64,
      args := (Arg.var ld, Arg.var p_30.snd.fst, ()) }
    fun (p_46 : Tup V [i64]) => Expr.let_
    { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var p.fst, Arg.imm 464, ()) } fun
    (p_47 : Tup V [i64]) => Expr.store (Arg.var p_46.fst) (Arg.var p_47.fst) (Expr.group (fun
    (_Js_3 : Tup L [[]]) => Blocks.cons (fun (_p : Tup V []) => Expr.jump Js.fst (Arg.var
    p_32.fst, ())) Blocks.nil) fun (Js : Tup L [[]]) => Expr.let_
    { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var p.fst, Arg.imm 504, ()) } fun
    (p_48 : Tup V [i64]) => Expr.load i64 (Arg.var p_48.fst) fun (ld : V i64) => Expr.let_
    { sig := [i64, i64],
      code := OpCode.cmp CmpOp.uge i64 Ty.bool rfl,
      args := (Arg.var ld, Arg.var p_30.snd.fst, ()) }
    fun (p_49 : Tup V [Ty.bool]) => Expr.jnz (Arg.var p_49.fst) (Expr.let_
    { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var p.fst, Arg.imm 504, ()) } fun
    (p_50 : Tup V [i64]) => Expr.load i64 (Arg.var p_50.fst) fun (ld : V i64) => Expr.let_
    { sig := [i64, i64],
      code := OpCode.sub i64,
      args := (Arg.var ld, Arg.var p_30.snd.fst, ()) }
    fun (p_51 : Tup V [i64]) => Expr.let_
    { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var p.fst, Arg.imm 504, ()) } fun
    (p : Tup V [i64]) => Expr.store (Arg.var p_51.fst) (Arg.var p.fst) (Expr.jump Js.fst ()))
    (Expr.jump Js.fst ()))))) Blocks.nil) fun (Js : Tup L [[i64]]) => Expr.jump Js.fst (Arg.var
    p_32.snd.fst, ()))) Blocks.nil) fun (Js : Tup L [[i64, i64]]) => Expr.jump Js.fst (Arg.var
    p_19.fst, Arg.var p_19.fst, ())) (Expr.jump Js.fst (Arg.var p_30.snd.snd.fst, ()))

/-- WP lemma for `trLitPostExpr` (watch compaction + optional `full_add_unit` tail). -/
theorem tr_lit_post_wp {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    (Γ : Env) (hAu : Γ.Has "full_add_unit" fullAddUnitSpec)
    {s : FullState} {src : BitVec 32} {stop_early : Bool}
    {off sz end_v red : Nat} {w0_64 wend_64 p_fin : Val i64} {failed : Bool}
    {st_c : FullState} {R : Mem 64 → Prop} {Q : Post [Ty.bool]}
    {X : XPost} {mb : Mem 64}
    (hsp : FullSparseInv c F0 s) (hw0 : FullWitnessInv c F0 F_cur s.core)
    (_hcl0 : s.core.cur_level = 0) (hsrc_lt : src.toNat < 2 * s.core.cur_vars)
    (hoff_def : off = fullWatchOffCore s.core src.toNat)
    (hsz_def : sz = fullWatchSizeCore s.core src.toNat) (hend_def : end_v = off + sz)
    (hend_le_wlen : off + sz ≤ s.core.wlen)
    (hw0_to : w0_64.toNat = off) (hwend_to : wend_64.toNat = end_v)
    (hred_le : red ≤ end_v - off)
    (hto_c : TransOuterInv c F0 F_cur s src.toNat off p_fin.toNat end_v red st_c)
    (hws1_c : st_c.scratch.work_stk1 = s.scratch.work_stk1)
    (hfail_c : failed = true → (cnfOfClauses F_cur).EntailsClause (cnfClause [src.toNat]))
    (hmb : (FullMem c st_c ⋆ R) mb)
    (hQ : ∀ ok s' m', FullSparseInv c F0 s' → s'.core.cur_level = 0 →
      s'.core.cur_vars = s.core.cur_vars → s'.core.fuel = s.core.fuel →
      s'.scratch.work_stk1 = s.scratch.work_stk1 →
      (ok = false → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m') :
    wp Γ Q X (trLitPostExpr Val Cont (c.hdr, src, stop_early, ()) c.pWvec c.pWstk
      (w0_64, ()) (wend_64, ()) (failed, BitVec.ofNat 64 red, p_fin, ())) mb := by
  have hlen0 := hsp.1.lengths
  have hwc := c.hwcap; unfold dimacsBound at hwc
  have hbnds := tr_bnds hlen0.core_ok
  have hcv0 := hlen0.core_ok.cur_vars_le
  have hmv := c.hmv; have hmaxv := c.hmaxv; unfold dimacsBound at hmv hmaxv
  have hend_u64 : end_v < 2 ^ 64 := by
    have := hend_le_wlen; have := hlen0.core_ok.wlen_le; omega
  have hoff_u64 : off < 2 ^ 64 := by omega
  refine wp_join_group (ts := [i64])
    (fun _ m_au => ∃ st_f, FullSparseInv c F0 st_f ∧ FullWitnessInv c F0 F_cur st_f.core ∧
      st_f.core.cur_level = 0 ∧ st_f.core.cur_vars = s.core.cur_vars ∧
      st_f.core.fuel = s.core.fuel ∧ st_f.scratch.work_stk1 = s.scratch.work_stk1 ∧
      (FullMem c st_f ⋆ R) m_au)
    (fun _ ⟨_, ⟨⟩⟩ m_au ⟨st_f, hsp_f, hw_f, hcl_f, hcv_f, hfu_f, hws1_f, hm_au⟩ => by
      c0_hsteps_nogrp
      · let st_t : FullState := { st_f with
          scratch := { st_f.scratch with trans_cnt := st_f.scratch.trans_cnt + 1#64 } }
        have ⟨hsp_t, hw_t⟩ :=
          fullSparseInv_with_trans_cnt hsp_f hw_f (st_f.scratch.trans_cnt + 1#64)
        refine wp_call_of_spec _ _ (hAu (c.hdr, src, ()) _ _ _
          ⟨c, F0, F_cur, st_t, R, rfl, hsp_t.1.lengths, hw_t,
           (fun _ => hfail_c (by assumption)), (by assumption), ?_⟩)
        intro ok vals' flags' lvl' rsns' trl' tp' te' prop' cl' unass' unfl' inc'
          phases' ta' ba' pt' pb' hp' ps' hl' qsi' qss' m'
        dsimp only
        intro hlen' hw' hcl' hok1 _ hm'
        let s' : FullState := {
          core := { st_t.core with
            vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
            trail_pos := tp', trail_end := te', propagated := prop', cur_level := cl',
            unassigned := unass', unflushed := unfl', inconsistent := inc' }
          scratch := { st_t.scratch with
            phases := phases', target_assigned := ta', best_assigned := ba',
            phases_target := pt', phases_best := pb', heap := hp', pos := ps',
            heap_len := hl', q_search_idx := qsi', q_search_stamp := qss' } }
        dsimp only [st_t] at hlen' hw'
        have hsp' := fullAddUnit_sparse hsp_t (s' := s') rfl ⟨rfl, rfl⟩ hlen' hw'
        c0_hsteps
        exact hQ ok s' m' hsp' hcl' hcv_f hfu_f hws1_f
          (fun h => (hok1 (by rw [hcv_f]; exact hsrc_lt) h).1) hm'
      · c0_hsteps
        exact hQ true st_f m_au hsp_f hcl_f hcv_f hfu_f hws1_f (fun h => by cases h) hm_au)
    (fun Js hJs => by
      c0_hsplit
      · have hred_pos : 0 < red := by c0_bound
        refine wp_loop_inv (ts := [i64, i64])
          (fun (p_v, q_v, ()) mc => ∃ p_c q_c st_c,
            p_v = BitVec.ofNat 64 p_c ∧ q_v = BitVec.ofNat 64 q_c ∧
            TransCompactInv c F0 F_cur s src.toNat off q_c p_c end_v red st_c ∧
            st_c.scratch.work_stk1 = s.scratch.work_stk1 ∧ (FullMem c st_c ⋆ R) mc)
          (fun (p_v, _) _ => end_v - p_v.toNat)
          (fun Jc hJc => by
            c0_hsteps
            have hpoff : w0_64 = BitVec.ofNat 64 off := by
              apply BitVec.eq_of_toNat_eq
              rw [hw0_to, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hoff_u64]
            exact hJc _ mb ⟨off, off, st_c, hpoff, hpoff,
              TransCompactInv.init hto_c, hws1_c, hmb⟩)
          (fun Jc ⟨p_v, q_v, ⟨⟩⟩ mc ⟨p_c, q_c, st_c, hp_ev, hq_ev, hci, hws1_ci, hmc⟩ ihc => by
            subst hp_ev hq_ev
            have hpe_bnd : end_v ≤ c.wcap :=
              Nat.le_trans hci.base.end_le_wlen hci.base.len_ok.core_ok.wlen_le
            have hpc_mod : p_c % 2 ^ 64 = p_c :=
              Nat.mod_eq_of_lt (by have := hci.q_range; omega)
            have hqc_mod : q_c % 2 ^ 64 = q_c :=
              Nat.mod_eq_of_lt (by have := hci.q_range; omega)
            have hp_bv : (BitVec.ofNat 64 p_c).toNat = p_c := by rw [BitVec.toNat_ofNat, hpc_mod]
            have hq_bv : (BitVec.ofNat 64 q_c).toNat = q_c := by rw [BitVec.toNat_ofNat, hqc_mod]
            let CInv := fun (p' q' : Val i64) (mn : Mem 64) => ∃ p2 q2 st2,
              p' = BitVec.ofNat 64 p2 ∧ q' = BitVec.ofNat 64 q2 ∧ end_v - p2 < end_v - p_c ∧
              TransCompactInv c F0 F_cur s src.toNat off q2 p2 end_v red st2 ∧
              st2.scratch.work_stk1 = s.scratch.work_stk1 ∧ (FullMem c st2 ⋆ R) mn
            c0_hsplit
            · have hp_lt : p_c < end_v := by
                have hcw := hc; rw [hpc_mod, hwend_to] at hcw; exact hcw
              have hqr := hci.q_range
              have hp_wlen : p_c < st_c.core.wstk.length := by
                rw [hci.base.len_ok.core_ok.wstk_len_arr]; omega
              have hq_wlen : q_c < st_c.core.wstk.length := by
                rw [hci.base.len_ok.core_ok.wstk_len_arr]; omega
              let w := st_c.core.wstk[p_c]'hp_wlen
              have hw_get : st_c.core.wstk[p_c]? = some w := List.getElem?_eq_getElem hp_wlen
              c0_hstraight
              refine wp_join_group (ts := [i64, i64])
                (fun (p', q', ()) mn => CInv p' q' mn)
                (fun _ ⟨p', q', ⟨⟩⟩ mn ⟨p2, q2, st2, hp2, hq2, hdec, hci2, hws1_2, hmn⟩ => by
                  subst hp2; subst hq2
                  have hpn_bv : (BitVec.ofNat 64 p2).toNat = p2 := by
                    have := hci2.q_range; bv_omega
                  exact ihc (BitVec.ofNat 64 p2, BitVec.ofNat 64 q2, ()) mn
                    (by dsimp only; rw [hpn_bv, hp_bv]; exact hdec)
                    ⟨p2, q2, st2, rfl, rfl, hci2, hws1_2, hmn⟩)
                (fun Jc1 hJc1 => by
                  c0_hsplit
                  · have htomb : w = 0xFFFFFFFF#32 := by
                      dsimp only [w]; simp only [hpc_mod] at hc; exact hc
                    c0_hsteps
                    exact hJc1 _ mc ⟨p_c + 1, q_c, st_c, by bv_omega, rfl, by omega,
                      hci.step_tomb hp_lt hw_get htomb, hws1_ci, hmc⟩
                  · have hne_tomb : w ≠ 0xFFFFFFFF#32 := by
                      dsimp only [w]; simp only [hpc_mod] at hc; exact hc
                    refine wp_join_group (ts := [i64, i64])
                      (fun (p', q', ()) mn => CInv p' q' mn)
                      (fun _ ⟨p', q', ⟨⟩⟩ mn h => hJc1 _ mn h)
                      (fun Jc2 hJc2 => by
                        c0_hsplit
                        · have hfl : (w &&& 0x80000000#32) ≠ 0#32 := by
                            dsimp only [w]; simp only [hpc_mod] at hc; exact hc
                          have hsrc_c : src.toNat < 2 * st_c.core.cur_vars := by
                            rw [hci.base.core_pres.1]; exact hsrc_lt
                          c0_hsteps
                          have hm_b : (FullMem c { st_c with core := { st_c.core with
                              wstk := st_c.core.wstk.set q_c w } } ⋆ R) m := by
                            simpa only [hq_bv, hp_bv] using hm
                          exact hJc2 _ m ⟨p_c + 1, q_c + 1, _, by bv_omega, by bv_omega, by omega,
                            hci.step_bin hp_lt hsrc_c hw_get hne_tomb hfl, hws1_ci, hm_b⟩
                        · have hfl0 : (w &&& 0x80000000#32) = 0#32 := by
                            dsimp only [w]; simp only [hpc_mod] at hc; exact hc
                          have hsrc_c : src.toNat < 2 * st_c.core.cur_vars := by
                            rw [hci.base.core_pres.1]; exact hsrc_lt
                          obtain ⟨hp1_lt, w1, hw1_get, hstep_lg⟩ :=
                            hci.step_large hp_lt hsrc_c hw_get hfl0
                          have hp1_wlen : p_c + 1 < (st_c.core.wstk.set q_c w).length := by
                            rw [List.length_set, hci.base.len_ok.core_ok.wstk_len_arr]; omega
                          have hq1_wlen : q_c + 1 < (st_c.core.wstk.set q_c w).length := by
                            rw [List.length_set, hci.base.len_ok.core_ok.wstk_len_arr]; omega
                          have hw1_eq : (st_c.core.wstk.set q_c w)[p_c + 1]'hp1_wlen = w1 := by
                            have h1 := List.getElem?_eq_getElem hp1_wlen
                            rw [List.getElem?_set_ne (by omega : q_c ≠ p_c + 1), hw1_get] at h1
                            exact Option.some.inj h1.symm
                          refine wp_join_group (ts := [i64, i64])
                            (fun (p', q', ()) mn => CInv p' q' mn)
                            (fun _ ⟨p', q', ⟨⟩⟩ mn h => hJc2 _ mn h)
                            (fun Jc3 hJc3 => by
                              c0_hsplit
                              · have hp1_bv : (BitVec.ofNat 64 p_c + 1#64).toNat = p_c + 1 := by
                                  bv_omega
                                have hq1_bv : (BitVec.ofNat 64 q_c + 1#64).toNat = q_c + 1 := by
                                  bv_omega
                                have hp1_wlen' : (BitVec.ofNat 64 p_c + 1#64).toNat <
                                    (st_c.core.wstk.set q_c w).length := by
                                  rw [hp1_bv]; exact hp1_wlen
                                have hq1_wlen' : (BitVec.ofNat 64 q_c + 1#64).toNat <
                                    (st_c.core.wstk.set q_c w).length := by
                                  rw [hq1_bv]; exact hq1_wlen
                                c0_hsteps
                                dsimp only [w] at hw1_eq
                                have h1_bv : (1 : BitVec 64) = 1#64 := rfl
                                have hm_fin : (FullMem c { st_c with core := { st_c.core with
                                    wstk := (st_c.core.wstk.set q_c w).set (q_c + 1) w1 } } ⋆ R)
                                    m := by
                                  dsimp only [w]
                                  simpa only [h1_bv, hq_bv, hp_bv, hq1_bv, hp1_bv, hw1_eq] using hm
                                refine hJc3 _ m ⟨p_c + 2, q_c + 2, _, ?_, ?_,
                                  by omega, hstep_lg, hws1_ci, hm_fin⟩ <;> bv_omega
                              · exfalso
                                have hcw := hc; rw [hwend_to] at hcw
                                have hp1_mod : (p_c + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 =
                                    p_c + 1 := by
                                  rw [show BitVec.toNat (1 : BitVec 64) = 1 from rfl,
                                    Nat.mod_eq_of_lt (by omega)]
                                rw [hp1_mod] at hcw; exact hcw hp1_lt)))
            · have hp_eq : p_c = end_v := by
                have := hci.q_range
                have hcw := hc; rw [hpc_mod, hwend_to] at hcw
                omega
              subst p_c
              obtain ⟨hq_eq, hq_ge, hq_le, hsl_c⟩ := hci.at_end
              subst hq_eq
              refine wp_loop_inv (ts := [i64])
                (fun (qv, ()) ms => ∃ q_s st_s, qv = BitVec.ofNat 64 q_s ∧
                  end_v - red ≤ q_s ∧ q_s ≤ end_v ∧
                  TransOuterBase c F0 F_cur s src.toNat off end_v st_s ∧
                  WatchSliceOk F_cur st_s.core src.toNat off (end_v - off - red) ∧
                  st_s.scratch.work_stk1 = s.scratch.work_stk1 ∧ (FullMem c st_s ⋆ R) ms)
                (fun (qv, ()) _ => end_v - qv.toNat)
                (fun Jq hJq => by
                  c0_hsteps
                  exact hJq _ mc ⟨end_v - red, st_c, rfl, Nat.le_refl _, hq_le, hci.base, hsl_c,
                    hws1_ci, hmc⟩)
                (fun Jq ⟨qv, ⟨⟩⟩ ms ⟨q_s, st_s, hq_ev, hq_ge2, hq_le2, hb_s, hsl_s, hws1_s, hms⟩
                    ihq => by
                  subst hq_ev
                  have hbnd_s := Nat.le_trans hb_s.end_le_wlen hb_s.len_ok.core_ok.wlen_le
                  have hqs_mod : q_s % 2 ^ 64 = q_s := Nat.mod_eq_of_lt (by omega)
                  have hq_bv2 : (BitVec.ofNat 64 q_s).toNat = q_s := by
                    rw [BitVec.toNat_ofNat, hqs_mod]
                  c0_hsplit
                  · have hq_lt : q_s < end_v := by
                      have hcw := hc; rw [hqs_mod, hwend_to] at hcw; exact hcw
                    have hq_wlen : q_s < st_s.core.wstk.length := by
                      rw [hb_s.len_ok.core_ok.wstk_len_arr]; omega
                    have hsrc_s : src.toNat < 2 * st_s.core.cur_vars := by
                      rw [hb_s.core_pres.1]; exact hsrc_lt
                    obtain ⟨hb_s', hsl_s'⟩ := hb_s.sentinel_fill_step hsrc_s
                      ⟨by have := hb_s.off_le_end; omega, hq_ge2, hq_lt⟩
                      (by rwa [Nat.sub_right_comm] at hsl_s)
                    c0_hsteps
                    have hms' : (FullMem c { st_s with core := { st_s.core with
                        wstk := st_s.core.wstk.set q_s 0xFFFFFFFF#32 } } ⋆ R) m := by
                      simpa only [hq_bv2,
                        show (4294967295 : BitVec 32) = 0xFFFFFFFF#32 from rfl] using hm
                    have hqs1_bv :
                        BitVec.ofNat 64 q_s + 1#64 = BitVec.ofNat 64 (q_s + 1) := by
                      bv_omega
                    exact ihq (BitVec.ofNat 64 q_s + 1#64, ()) m
                      (by dsimp only; rw [hqs1_bv, hq_bv2]; bv_omega)
                      ⟨q_s + 1, _, hqs1_bv, by omega, by omega, hb_s',
                        (by rwa [Nat.sub_right_comm]), hws1_s, hms'⟩
                  · have hno_lt : ¬ q_s < end_v := by
                      have hcw := hc; rw [hqs_mod, hwend_to] at hcw; exact hcw
                    have hwv_b_s : 2 * src.toNat + 1 < st_s.core.wvec.length := by
                      rw [hb_s.len_ok.core_ok.wvec_len]; omega
                    have hidx_eq : (BitVec.setWidth 64 src <<< (1 : Nat) + 1#64).toNat =
                        2 * src.toNat + 1 := by bv_omega
                    have hsz_fin : BitVec.setWidth 32 (wend_64 - w0_64 - BitVec.ofNat 64 red) =
                        BitVec.ofNat 32 (end_v - off - red) := by
                      apply BitVec.eq_of_toNat_eq
                      have := hb_s.off_le_end
                      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), BitVec.toNat_setWidth,
                        BitVec.toNat_sub, BitVec.toNat_sub, BitVec.toNat_ofNat,
                        hw0_to, hwend_to, Nat.mod_eq_of_lt (by omega),
                        Nat.mod_eq_of_lt (by omega : red < 2 ^ 64)]
                      omega
                    c0_hsteps_nogrp
                    refine wp_join_group (ts := [])
                      (fun () mn => ∃ nb' : BitVec 64,
                        (FullMem c { st_s with core := { st_s.core with
                          wvec := st_s.core.wvec.set (2 * src.toNat + 1)
                            (BitVec.ofNat 32 (end_v - off - red)),
                          wusable := st_s.core.wusable + BitVec.ofNat 64 red,
                          num_binary := nb' } } ⋆ R) mn)
                      (fun _ ⟨⟩ mn ⟨nb', hmn⟩ => by
                        have hsrc_s : src.toNat < 2 * st_s.core.cur_vars := by
                          rw [hb_s.core_pres.1]; exact hsrc_lt
                        obtain ⟨hsp_fin, hw_fin⟩ := tr_compact_done_eq hsp hw0 hb_s hsrc_s hred_le
                          hsl_s rfl rfl (wu' := st_s.core.wusable + BitVec.ofNat 64 red)
                          (nb_bv := nb')
                        c0_hsteps
                        exact hJs _ mn ⟨_, hsp_fin, hw_fin, hb_s.core_pres.2.1, hb_s.core_pres.1,
                          hb_s.core_pres.2.2.2.1, hws1_s, hmn⟩)
                      (fun Jn hJn => by
                        c0_hsplit
                        · c0_hsteps
                          refine hJn () _ ⟨st_s.core.num_binary - BitVec.ofNat 64 red, ?_⟩
                          simpa only [← hsz_fin, ← hidx_eq] using (by assumption)
                        · c0_hsteps
                          refine hJn () _ ⟨st_s.core.num_binary, ?_⟩
                          simpa only [← hsz_fin, ← hidx_eq] using (by assumption))))
      · have hred0 : red = 0 := Classical.byContradiction fun h => by
          have : (0 : Nat) < (BitVec.ofNat 64 red).toNat := by
            have := Nat.pos_of_ne_zero h; bv_omega
          c0_bound
        subst hred0
        obtain ⟨hsp_fin, hw_fin⟩ := hto_c.of_reduced0_full hsp hw0
        c0_hsteps
        exact hJs _ mb ⟨st_c, hsp_fin, hw_fin, hto_c.base.core_pres.2.1,
          hto_c.base.core_pres.1, hto_c.base.core_pres.2.2.2.1, hws1_c, hmb⟩)

/-- BFS watch-scan step subexpression of `full_trans_lit_m6_body`. -/
abbrev trLitBfsExpr (V : Ty → Type) (L : List Ty → Type)
    (Js : Tup L [[Ty.bool, i64, i64, Ty.bool]]) (Js_2 : Tup L [[]])
    (p : Tup V [i64, i32, Ty.bool]) (ld ld_2 ld_3 ld_4 : V i64)
    (p_13 : Tup V [i64]) (p_30 : Tup V [Ty.bool, i64, i64])
    (p_38 : Tup V [i32]) (p_62 : Tup V [Ty.bool, i64, i64, Ty.bool]) :
    Expr V L [Ty.bool] :=
  Expr.jnz (Arg.var p_62.snd.snd.snd.fst) (Expr.jump Js_2.fst ()) (Expr.jnz (Arg.var p_62.fst)
    (Expr.jump Js_2.fst ()) (Expr.let_
    { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var p.fst, Arg.imm 144, ()) } fun
    p_63 => Expr.load i64 (Arg.var p_63.fst) fun ld_13 => Expr.let_
    { sig := [i64, i64],
      code := OpCode.cmp CmpOp.ult i64 Ty.bool rfl,
      args := (Arg.var p_62.snd.snd.fst, Arg.var ld_13, ()) }
    fun p_64 => Expr.jnz (Arg.var p_64.fst) (Expr.let_
    { sig := [i64, i64],
      code := OpCode.cmp CmpOp.ugt i64 Ty.bool rfl,
      args := (Arg.var p_62.snd.fst, Arg.imm 0, ()) }
    fun p_65 => Expr.jnz (Arg.var p_65.fst) (Expr.let_
    { sig := [i64, i64],
      code := OpCode.mul i64,
      args := (Arg.var p_62.snd.snd.fst, Arg.imm 4, ()) }
    fun p_66 => Expr.let_
    { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var ld_4, Arg.var p_66.fst, ()) }
    fun p_67 => Expr.load i32 (Arg.var p_67.fst) fun ld_14 => Expr.let_
    { sig := [i64, i64],
      code := OpCode.add i64,
      args := (Arg.var p_62.snd.snd.fst, Arg.imm 1, ()) }
    fun p_68 => Expr.let_
    { sig := [i32, i32], code := OpCode.xor i32, args := (Arg.var ld_14, Arg.imm 1, ()) } fun
    p_69 => Expr.let_
    { sig := [i32], code := OpCode.zext 32 64, args := (Arg.var p_69.fst, ()) } fun p_70 =>
    Expr.let_ { sig := [i32], code := OpCode.sext 32 64, args := (Arg.imm 1, ()) } fun p_71 =>
    Expr.let_
    { sig := [i64, i64],
      code := OpCode.shl i64,
      args := (Arg.var p_70.fst, Arg.var p_71.fst, ()) }
    fun p_72 => Expr.let_
    { sig := [i64, i64], code := OpCode.mul i64, args := (Arg.var p_72.fst, Arg.imm 4, ()) } fun
    p_73 => Expr.let_
    { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var ld_2, Arg.var p_73.fst, ()) }
    fun p_74 => Expr.load i32 (Arg.var p_74.fst) fun ld_15 => Expr.let_
    { sig := [i32], code := OpCode.zext 32 64, args := (Arg.var ld_15, ()) } fun p_75 =>
    Expr.let_ { sig := [i32], code := OpCode.zext 32 64, args := (Arg.var p_69.fst, ()) } fun
    p_76 => Expr.let_ { sig := [i32], code := OpCode.sext 32 64, args := (Arg.imm 1, ()) } fun
    p_77 => Expr.let_
    { sig := [i64, i64],
      code := OpCode.shl i64,
      args := (Arg.var p_76.fst, Arg.var p_77.fst, ()) }
    fun p_78 => Expr.let_
    { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var p_78.fst, Arg.imm 1, ()) } fun
    p_79 => Expr.let_
    { sig := [i64, i64], code := OpCode.mul i64, args := (Arg.var p_79.fst, Arg.imm 4, ()) } fun
    p_80 => Expr.let_
    { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var ld_2, Arg.var p_80.fst, ()) }
    fun p_81 => Expr.load i32 (Arg.var p_81.fst) fun ld_16 => Expr.let_
    { sig := [i32], code := OpCode.zext 32 64, args := (Arg.var ld_16, ()) } fun p_82 =>
    Expr.let_
    { sig := [i64, i64],
      code := OpCode.add i64,
      args := (Arg.var p_75.fst, Arg.var p_82.fst, ()) }
    fun p_83 => Expr.let_
    { sig := [i64, i64], code := OpCode.sub i64, args := (Arg.var p_62.snd.fst, Arg.imm 1, ()) }
    fun p_84 => Expr.group (fun (_Js_3 : Tup L [[Ty.bool, i64, Ty.bool, i64]]) => Blocks.cons
    (fun (p : Tup V [Ty.bool, i64, Ty.bool, i64]) => Expr.jump Js.fst (Arg.var p.fst, Arg.var
    p.snd.fst, Arg.var p_68.fst, Arg.var p.snd.snd.fst, ())) Blocks.nil) fun (Js : Tup L
    [[Ty.bool, i64, Ty.bool, i64]]) => Expr.group (fun (Js_3 : Tup L [[i64, i64]]) =>
    Blocks.cons (fun (p_85 : Tup V [i64, i64]) => Expr.let_
    { sig := [i64, i64],
      code := OpCode.cmp CmpOp.ult i64 Ty.bool rfl,
      args := (Arg.var p_85.snd.fst, Arg.var p_83.fst, ()) }
    fun p_86 => Expr.jnz (Arg.var p_86.fst) (Expr.let_
    { sig := [i64, i64], code := OpCode.mul i64, args := (Arg.var p_85.snd.fst, Arg.imm 4, ()) }
    fun p_87 => Expr.let_
    { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var ld_3, Arg.var p_87.fst, ()) }
    fun p_88 => Expr.load i32 (Arg.var p_88.fst) fun ld_17 => Expr.let_
    { sig := [i32, i32],
      code := OpCode.cmp CmpOp.eq i32 Ty.bool rfl,
      args := (Arg.var ld_17, Arg.imm 4294967295, ()) }
    fun p_89 => Expr.jnz (Arg.var p_89.fst) (Expr.let_
    { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var p_85.snd.fst, Arg.imm 1, ()) }
    fun p => Expr.jump Js_3.fst (Arg.var p_85.fst, Arg.var p.fst, ())) (Expr.let_
    { sig := [i32, i32],
      code := OpCode.and i32,
      args := (Arg.var ld_17, Arg.imm 2147483648, ()) }
    fun p_90 => Expr.let_
    { sig := [i32, i32],
      code := OpCode.cmp CmpOp.eq i32 Ty.bool rfl,
      args := (Arg.var p_90.fst, Arg.imm 0, ()) }
    fun p_91 => Expr.jnz (Arg.var p_91.fst) (Expr.jnz (Arg.var p.snd.snd.fst) (Expr.jump Js.fst
    (Arg.var p_62.fst, Arg.var p_85.fst, Arg.var p_62.snd.snd.snd.fst, Arg.var p_85.snd.fst,
    ())) (Expr.let_
    { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var p_85.snd.fst, Arg.imm 2, ()) }
    fun p => Expr.group (fun (_Js : Tup L [[i64]]) => Blocks.cons (fun (p_92 : Tup V [i64]) =>
    Expr.jump Js_3.fst (Arg.var p_92.fst, Arg.var p.fst, ())) Blocks.nil) fun (Js : Tup L
    [[i64]]) => Expr.let_
    { sig := [i64, i64], code := OpCode.sub i64, args := (Arg.var p.fst, Arg.var p_75.fst, ()) }
    fun p => Expr.let_
    { sig := [i64, i64], code := OpCode.and i64, args := (Arg.var p.fst, Arg.imm 31, ()) } fun p
    => Expr.let_
    { sig := [i64, i64],
      code := OpCode.cmp CmpOp.eq i64 Ty.bool rfl,
      args := (Arg.var p.fst, Arg.imm 0, ()) }
    fun p => Expr.jnz (Arg.var p.fst) (Expr.let_
    { sig := [i64, i64],
      code := OpCode.cmp CmpOp.ugt i64 Ty.bool rfl,
      args := (Arg.var p_85.fst, Arg.imm 0, ()) }
    fun p => Expr.jnz (Arg.var p.fst) (Expr.let_
    { sig := [i64, i64], code := OpCode.sub i64, args := (Arg.var p_85.fst, Arg.imm 1, ()) } fun
    p => Expr.jump Js.fst (Arg.var p.fst, ())) (Expr.jump Js.fst (Arg.var p_85.fst, ())))
    (Expr.jump Js.fst (Arg.var p_85.fst, ())))) (Expr.group (fun (_Js_4 : Tup L [[]]) =>
    Blocks.cons (fun (_p_92 : Tup V []) => Expr.let_
    { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var p_85.snd.fst, Arg.imm 1, ()) }
    fun p_93 => Expr.group (fun (_Js_5 : Tup L [[i64]]) => Blocks.cons (fun (p_94 : Tup V [i64])
    => Expr.let_
    { sig := [i32, i32],
      code := OpCode.and i32,
      args := (Arg.var ld_17, Arg.imm 2147483647, ()) }
    fun p_95 => Expr.let_
    { sig := [i32, i32],
      code := OpCode.cmp CmpOp.eq i32 Ty.bool rfl,
      args := (Arg.var p_95.fst, Arg.var p_38.fst, ()) }
    fun p_96 => Expr.jnz (Arg.var p_96.fst) (Expr.jump Js.fst (Arg.var p_62.fst, Arg.var
    p_94.fst, Arg.imm true, Arg.var p_93.fst, ())) (Expr.group (fun (_Js : Tup L [[Ty.bool]]) =>
    Blocks.cons (fun (_p : Tup V [Ty.bool]) => Expr.jump Js_3.fst (Arg.var p_94.fst, Arg.var
    p_93.fst, ())) Blocks.nil) fun (Js_6 : Tup L [[Ty.bool]]) => Expr.let_
    { sig := [i32], code := OpCode.zext 32 64, args := (Arg.var p_95.fst, ()) } fun p_97 =>
    Expr.let_
    { sig := [i64, i64],
      code := OpCode.cmp CmpOp.ult i64 Ty.bool rfl,
      args := (Arg.var p_97.fst, Arg.var p_13.fst, ()) }
    fun p_98 => Expr.jnz (Arg.var p_98.fst) (Expr.let_
    { sig := [i32], code := OpCode.zext 32 64, args := (Arg.var p_95.fst, ()) } fun p_99 =>
    Expr.let_
    { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var ld, Arg.var p_99.fst, ()) }
    fun p_100 => Expr.load i8 (Arg.var p_100.fst) fun ld_18 => Expr.let_
    { sig := [i32], code := OpCode.trunc 32 8, args := (Arg.imm 0, ()) } fun p_101 => Expr.let_
    { sig := [i8], code := OpCode.sext 8 32, args := (Arg.var ld_18, ()) } fun p_102 =>
    Expr.let_ { sig := [i8], code := OpCode.sext 8 32, args := (Arg.var p_101.fst, ()) } fun
    p_103 => Expr.let_
    { sig := [i32, i32],
      code := OpCode.cmp CmpOp.slt i32 Ty.bool rfl,
      args := (Arg.var p_102.fst, Arg.var p_103.fst, ()) }
    fun p_104 => Expr.jnz (Arg.var p_104.fst) (Expr.jump Js.fst (Arg.imm true, Arg.var p_94.fst,
    Arg.var p_62.snd.snd.snd.fst, Arg.var p_93.fst, ())) (Expr.group (fun (_Js : Tup L [[]]) =>
    Blocks.cons (fun (_p : Tup V []) => Expr.jump Js_6.fst (Arg.var p_62.fst, ())) Blocks.nil)
    fun (Js : Tup L [[]]) => Expr.let_
    { sig := [i32], code := OpCode.zext 32 64, args := (Arg.var p_95.fst, ()) } fun p_105 =>
    Expr.let_
    { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var ld, Arg.var p_105.fst, ()) }
    fun p_106 => Expr.load i8 (Arg.var p_106.fst) fun ld_19 => Expr.let_
    { sig := [i32], code := OpCode.trunc 32 8, args := (Arg.imm 0, ()) } fun p_107 => Expr.let_
    { sig := [i8], code := OpCode.sext 8 32, args := (Arg.var ld_19, ()) } fun p_108 =>
    Expr.let_ { sig := [i8], code := OpCode.sext 8 32, args := (Arg.var p_107.fst, ()) } fun
    p_109 => Expr.let_
    { sig := [i32, i32],
      code := OpCode.cmp CmpOp.eq i32 Ty.bool rfl,
      args := (Arg.var p_108.fst, Arg.var p_109.fst, ()) }
    fun p_110 => Expr.jnz (Arg.var p_110.fst) (Expr.let_
    { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var p.fst, Arg.imm 144, ()) } fun
    p_111 => Expr.load i64 (Arg.var p_111.fst) fun ld_20 => Expr.let_
    { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var p.fst, Arg.imm 768, ()) } fun
    p_112 => Expr.load i64 (Arg.var p_112.fst) fun ld_21 => Expr.let_
    { sig := [i64, i64],
      code := OpCode.cmp CmpOp.ult i64 Ty.bool rfl,
      args := (Arg.var ld_20, Arg.var ld_21, ()) }
    fun p_113 => Expr.jnz (Arg.var p_113.fst) (Expr.let_
    { sig := [i32], code := OpCode.zext 32 64, args := (Arg.var p_95.fst, ()) } fun p_114 =>
    Expr.let_
    { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var ld, Arg.var p_114.fst, ()) }
    fun p_115 => Expr.let_ { sig := [i32], code := OpCode.trunc 32 8, args := (Arg.imm 1, ()) }
    fun p_116 => Expr.store (Arg.var p_116.fst) (Arg.var p_115.fst) (Expr.let_
    { sig := [i32, i32], code := OpCode.xor i32, args := (Arg.var p_95.fst, Arg.imm 1, ()) } fun
    p_117 => Expr.let_
    { sig := [i32], code := OpCode.zext 32 64, args := (Arg.var p_117.fst, ()) } fun p_118 =>
    Expr.let_
    { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var ld, Arg.var p_118.fst, ()) }
    fun p_119 => Expr.let_ { sig := [i32], code := OpCode.neg i32, args := (Arg.imm 1, ()) } fun
    p_120 => Expr.let_
    { sig := [i32], code := OpCode.trunc 32 8, args := (Arg.var p_120.fst, ()) } fun p_121 =>
    Expr.store (Arg.var p_121.fst) (Arg.var p_119.fst) (Expr.let_
    { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var p.fst, Arg.imm 144, ()) } fun
    p_122 => Expr.load i64 (Arg.var p_122.fst) fun ld => Expr.let_
    { sig := [i64, i64], code := OpCode.mul i64, args := (Arg.var ld, Arg.imm 4, ()) } fun p_123
    => Expr.let_
    { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var ld_4, Arg.var p_123.fst, ()) }
    fun p_124 => Expr.store (Arg.var p_95.fst) (Arg.var p_124.fst) (Expr.let_
    { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var p.fst, Arg.imm 144, ()) } fun
    p_125 => Expr.load i64 (Arg.var p_125.fst) fun ld => Expr.let_
    { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var ld, Arg.imm 1, ()) } fun p_126
    => Expr.let_
    { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var p.fst, Arg.imm 144, ()) } fun
    p => Expr.store (Arg.var p_126.fst) (Arg.var p.fst) (Expr.jump Js.fst ()))))) (Expr.jump
    Js.fst ())) (Expr.jump Js.fst ()))) (Expr.jump Js_6.fst (Arg.var p_62.fst, ()))))
    Blocks.nil) fun (Js : Tup L [[i64]]) => Expr.let_
    { sig := [i64, i64],
      code := OpCode.sub i64,
      args := (Arg.var p_93.fst, Arg.var p_75.fst, ()) }
    fun p => Expr.let_
    { sig := [i64, i64], code := OpCode.and i64, args := (Arg.var p.fst, Arg.imm 31, ()) } fun p
    => Expr.let_
    { sig := [i64, i64],
      code := OpCode.cmp CmpOp.eq i64 Ty.bool rfl,
      args := (Arg.var p.fst, Arg.imm 0, ()) }
    fun p => Expr.jnz (Arg.var p.fst) (Expr.let_
    { sig := [i64, i64],
      code := OpCode.cmp CmpOp.ugt i64 Ty.bool rfl,
      args := (Arg.var p_85.fst, Arg.imm 0, ()) }
    fun p => Expr.jnz (Arg.var p.fst) (Expr.let_
    { sig := [i64, i64], code := OpCode.sub i64, args := (Arg.var p_85.fst, Arg.imm 1, ()) } fun
    p => Expr.jump Js.fst (Arg.var p.fst, ())) (Expr.jump Js.fst (Arg.var p_85.fst, ())))
    (Expr.jump Js.fst (Arg.var p_85.fst, ()))) Blocks.nil) fun (Js : Tup L [[]]) => Expr.let_
    { sig := [i32, i32],
      code := OpCode.cmp CmpOp.eq i32 Ty.bool rfl,
      args := (Arg.var p_69.fst, Arg.var p.snd.fst, ()) }
    fun p => Expr.jnz (Arg.var p.fst) (Expr.let_
    { sig := [i64, i64],
      code := OpCode.cmp CmpOp.eq i64 Ty.bool rfl,
      args := (Arg.var p_85.snd.fst, Arg.var p_30.snd.snd.fst, ()) }
    fun p => Expr.jnz (Arg.var p.fst) (Expr.let_
    { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var p_85.snd.fst, Arg.imm 1, ()) }
    fun p => Expr.jump Js_3.fst (Arg.var p_85.fst, Arg.var p.fst, ())) (Expr.jump Js.fst ()))
    (Expr.jump Js.fst ())))) (Expr.jump Js.fst (Arg.var p_62.fst, Arg.var p_85.fst, Arg.var
    p_62.snd.snd.snd.fst, Arg.var p_85.snd.fst, ()))) Blocks.nil) fun (Js : Tup L [[i64, i64]])
    => Expr.jump Js.fst (Arg.var p_84.fst, Arg.var p_75.fst, ())) (Expr.jump Js_2.fst ()))
    (Expr.jump Js_2.fst ())))

/-- WP lemma for `trLitBfsExpr` (one queue iteration scanning negated binary watches). -/
theorem tr_lit_bfs_wp {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    (Γ : Env) {s st_l st_b : FullState} {src : BitVec 32} {stop_early : Bool}
    {off p_v end_v red saved : Nat}
    {Jbfs : Cont [.bool, i64, i64, .bool]} {Jex : Cont []}
    {p_13_v : Val i64} {p_30 : Tup Val [.bool, i64, i64]} {p_38 : Tup Val [i32]}
    {fail_b hit_b : Bool} {ticks_b qhead_b : Val i64}
    {R : Mem 64 → Prop} {Q : Post [Ty.bool]} {X : XPost} {m_b : Mem 64}
    (hw0 : FullWitnessInv c F0 F_cur s.core) (hcl0 : s.core.cur_level = 0)
    (_hsrc_lt : src.toNat < 2 * s.core.cur_vars)
    (hto_l : TransOuterInv c F0 F_cur s src.toNat off p_v end_v red st_l)
    (_hws1_l : st_l.scratch.work_stk1 = s.scratch.work_stk1)
    (hp13 : p_13_v.toNat = 2 * s.core.cur_vars)
    (hu_b : TransUnrollInv c F0 F_cur s st_l src.toNat saved st_b)
    (hqh_ge : saved ≤ qhead_b.toNat) (hqh_le : qhead_b.toNat ≤ st_b.core.trail_end)
    (hte_gt : saved < st_b.core.trail_end)
    (hws1_b : st_b.scratch.work_stk1 = s.scratch.work_stk1)
    (hfail_b : fail_b = true → (cnfOfClauses F_cur).EntailsClause (cnfClause [src.toNat]))
    (hm_b : (FullMem c st_b ⋆ R) m_b)
    (hJex : ∀ u m, (FullMem c st_b ⋆ R) m → Jex u m)
    (hJbfs : ∀ fb tb qhb hb m,
      st_l.core.cur_vars - qhb.toNat < st_l.core.cur_vars - qhead_b.toNat →
      (∃ st', TransUnrollInv c F0 F_cur s st_l src.toNat saved st' ∧
        saved ≤ qhb.toNat ∧ qhb.toNat ≤ st'.core.trail_end ∧
        saved < st'.core.trail_end ∧ st'.scratch.work_stk1 = s.scratch.work_stk1 ∧
        (fb = true → (cnfOfClauses F_cur).EntailsClause (cnfClause [src.toNat])) ∧
        (FullMem c st' ⋆ R) m) →
      Jbfs (fb, tb, qhb, hb, ()) m) :
    wp Γ Q X (trLitBfsExpr Val Cont (Jbfs, ()) (Jex, ()) (c.hdr, src, stop_early, ())
      c.pVals c.pWvec c.pWstk c.pTrail (p_13_v, ()) p_30 p_38
      (fail_b, ticks_b, qhead_b, hit_b, ())) m_b := by
  have hb_l := hto_l.base
  unfold trLitBfsExpr
  c0_hsplit
  · exact hJex () m_b hm_b
  · c0_hsplit
    · exact hJex () m_b hm_b
    · have hte_bv_b : st_b.core.trail_end < 2 ^ 64 := (tr_bnds hu_b.len_ok.core_ok).2.2.2
      c0_hsteps_nogrp
      · have hqh_lt : qhead_b.toNat < st_b.core.trail_end := by c0_bound
        have htk_pos : 0 < ticks_b.toNat := by c0_bound
        have hqh_trl : qhead_b.toNat < st_b.core.trl.length := by
          rw [hu_b.len_ok.core_ok.trl_len]
          have := hu_b.len_ok.core_ok.trail_end_le
          have := hu_b.len_ok.core_ok.cur_vars_le; omega
        obtain ⟨ql, hql_get, hql_lt, _, _, _, h_src_ql⟩ :=
          hu_b.bfs_trl_inv qhead_b.toNat hqh_ge hqh_lt
        have hql_eq : st_b.core.trl[qhead_b.toNat]'hqh_trl = ql :=
          Option.some.inj ((List.getElem?_eq_getElem hqh_trl).symm.trans hql_get)
        let nql := ql ^^^ 1#32
        have hnql_lt : nql.toNat < 2 * st_b.core.cur_vars := by
          rw [congrArg FullCoreState.cur_vars hu_b.same_core,
            show nql = ql ^^^ 1#32 from rfl, tr_bv32_xor1]
          exact litNeg_lt_two_mul hql_lt
        have hvw_b : 2 * nql.toNat + 1 < st_b.core.wvec.length := by
          rw [hu_b.len_ok.core_ok.wvec_len]
          have := hu_b.len_ok.core_ok.cur_vars_le; omega
        have hnql_shl : (BitVec.setWidth 64 nql <<< (1 : Nat)).toNat = 2 * nql.toNat := by
          bv_omega
        have hw0_nql : (BitVec.setWidth 64 nql <<< (1 : Nat)).toNat < st_b.core.wvec.length := by
          rw [hnql_shl, hu_b.len_ok.core_ok.wvec_len]
          have := hu_b.len_ok.core_ok.cur_vars_le; omega
        obtain ⟨hwend_le, hwoff_nat, hwsz_nat, nt0, hts0⟩ :=
          tr_lit_bfs_watch_end hto_l hu_b hnql_lt
        let woff := fullWatchOffCore st_b.core nql.toNat
        let wsz := fullWatchSizeCore st_b.core nql.toNat
        let wend := woff + wsz
        have h1_32 : (1 : BitVec 32) = 1#32 := rfl
        have hw0_nql' : (BitVec.setWidth 64
            (st_b.core.trl[qhead_b.toNat] ^^^ (1 : BitVec 32)) <<< (1 : Nat)).toNat <
            st_b.core.wvec.length := by rw [hql_eq, h1_32]; exact hw0_nql
        have hvw_b' : (BitVec.setWidth 64
            (st_b.core.trl[qhead_b.toNat] ^^^ (1 : BitVec 32)) <<< (1 : Nat) + 1).toNat <
            st_b.core.wvec.length := by
          rw [hql_eq, h1_32]
          change (BitVec.setWidth 64 nql <<< (1 : Nat) + 1).toNat < st_b.core.wvec.length
          have := hu_b.len_ok.core_ok.wvec_len; have := hu_b.len_ok.core_ok.cur_vars_le
          rw [BitVec.toNat_add, show BitVec.toNat (1 : BitVec 64) = 1 from rfl, hnql_shl,
            Nat.mod_eq_of_lt (by omega)]
          exact hvw_b
        c0_hsteps_nogrp
        refine wp_loop_break_group (brkTs := [.bool, i64, .bool, i64]) (lpTs := [i64, i64])
          (BrkPost := fun (fb', tb', hb', wp') mw => ∃ st_w,
            TransUnrollInv c F0 F_cur s st_l src.toNat saved st_w ∧
            saved < st_w.core.trail_end ∧ st_b.core.trail_end ≤ st_w.core.trail_end ∧
            st_w.scratch.work_stk1 = s.scratch.work_stk1 ∧
            (fb' = true → (cnfOfClauses F_cur).EntailsClause (cnfClause [src.toNat])) ∧
            (FullMem c st_w ⋆ R) mw)
          (Inv := fun r_w (tw, wp, ()) mw => ∃ nt_w st_w,
            r_w = wend - wp.toNat ∧ woff ≤ wp.toNat ∧ wp.toNat ≤ wend ∧
            TransUnrollInv c F0 F_cur s st_l src.toNat saved st_w ∧
            saved < st_w.core.trail_end ∧ st_b.core.trail_end ≤ st_w.core.trail_end ∧
            st_w.scratch.work_stk1 = s.scratch.work_stk1 ∧
            TombWatchSliceOk F_cur st_w.core nql.toNat wp.toNat (wend - wp.toNat) nt_w ∧
            (FullMem c st_w ⋆ R) mw)
          ?_ ?_ ?_
        · rintro _ ⟨fb', tb', hb', wp', ⟨⟩⟩ mw
            ⟨st_w, hu_w, hte_w, hte_mono, hws1_w, hf_w, hm_w⟩
          have hqh1_eq : (qhead_b + 1#64).toNat = qhead_b.toNat + 1 := tr_bv64_add1 (by omega)
          have hcv_b : st_b.core.cur_vars = st_l.core.cur_vars := by rw [hu_b.same_core]
          have hte_le_b := hu_b.len_ok.core_ok.trail_end_le
          have hqh_lt_cv : qhead_b.toNat < st_l.core.cur_vars := by rw [← hcv_b]; omega
          c0_hsteps
          exact hJbfs fb' tb' (qhead_b + 1#64) hb' mw (by rw [hqh1_eq]; omega)
            ⟨st_w, hu_w, by rw [hqh1_eq]; omega,
              by rw [hqh1_eq]; exact Nat.le_trans (by omega) hte_mono,
              hte_w, hws1_w, hf_w, hm_w⟩
        · rintro Bw Lw rw ⟨tw, wp, ⟨⟩⟩ mw hBw hLw
            ⟨nt_w, st_w, rfl, hwp_ge, hwp_le, hu_w, hte_w, hte_mono, hws1_w, hts_w, hm_w⟩
          have hw_bnd : wend ≤ c.wcap :=
            Nat.le_trans hwend_le hu_b.len_ok.core_ok.wlen_le
          c0_hsplit
          · have hwp_lt : wp.toNat < wend := by
              have hql_n : st_b.core.trl[qhead_b.toNat].toNat ^^^ 1 = nql.toNat := by
                rw [hql_eq]; exact (tr_bv32_xor1 ql).symm
              have h0_mod : (2 * nql.toNat) % 2 ^ 64 = 2 * nql.toNat :=
                Nat.mod_eq_of_lt (by have := hu_b.len_ok.core_ok.cur_vars_le; omega)
              have h1_mod : (2 * nql.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 =
                  2 * nql.toNat + 1 := by
                rw [show BitVec.toNat (1 : BitVec 64) = 1 from rfl]
                exact Nat.mod_eq_of_lt (by have := hu_b.len_ok.core_ok.cur_vars_le; omega)
              have hlt_bv : wp.toNat < (BitVec.setWidth 64 st_b.core.wvec[2 * nql.toNat] +
                  BitVec.setWidth 64 st_b.core.wvec[2 * nql.toNat + 1]).toNat := by
                have hcw := hc
                simp only [hql_n, h0_mod, h1_mod] at hcw
                rw [BitVec.toNat_add, tr_bv32_setWidth64, tr_bv32_setWidth64]
                exact hcw
              rw [BitVec.toNat_add, hwoff_nat, hwsz_nat,
                Nat.mod_eq_of_lt (by have := hu_b.len_ok.core_ok.wlen_le; omega)] at hlt_bv
              exact hlt_bv
            have hwp_wlen : wp.toNat < st_w.core.wstk.length := by
              rw [hu_w.len_ok.core_ok.wstk_len_arr]; omega
            let ww := st_w.core.wstk[wp.toNat]'hwp_wlen
            have hww_get : st_w.core.wstk[wp.toNat]? = some ww := List.getElem?_eq_getElem hwp_wlen
            have hstep_ts := hts_w.inv_step (by omega) hww_get
            c0_hsteps_nogrp
            · have hwt : ww = 0xFFFFFFFF#32 := by c0_bound
              rw [hwt] at hstep_ts
              simp only [tr_tomb_bin_flag, ↓reduceIte] at hstep_ts
              have hwp1 : (wp + 1#64).toNat = wp.toNat + 1 := tr_bv64_add1 (by omega)
              c0_hsteps
              exact hLw (wend - (wp.toNat + 1)) (tw, wp + 1#64, ()) mw
                (by omega) ⟨nt_w - 1, st_w, by rw [hwp1], by rw [hwp1]; omega,
                  by rw [hwp1]; omega, hu_w, hte_w, hte_mono, hws1_w, by
                    rw [hwp1, show wend - (wp.toNat + 1) = wend - wp.toNat - 1 by omega]
                    exact hstep_ts.2, hm_w⟩
            · c0_hsteps
              exact hBw _ mw
                ⟨st_w, hu_w, hte_w, hte_mono, hws1_w, fun h => by cases h; contradiction, hm_w⟩
            · have hww_ne : ww ≠ 0xFFFFFFFF#32 := by
                intro h; dsimp only [ww] at h; c0_bound
              have hfl0 : (ww &&& 0x80000000#32) = 0#32 := by c0_bound
              simp only [hfl0, ↓reduceIte] at hstep_ts
              obtain ⟨_, cref, _, _, _, hts2⟩ := hstep_ts
              have hwp2 : (wp + 2#64).toNat = wp.toNat + 2 := tr_bv64_add2 (by omega)
              refine wp_join_group (ts := [i64]) (fun _ mk => mk = mw) ?_ ?_
              · rintro _ ⟨tw', ⟨⟩⟩ mk hmk
                rw [hmk]
                c0_hsteps
                exact hLw (wend - (wp.toNat + 2)) (tw', wp + 2#64, ()) mw
                  (by omega) ⟨nt_w, st_w, by rw [hwp2], by rw [hwp2]; omega,
                    by rw [hwp2]; omega, hu_w, hte_w, hte_mono, hws1_w, by
                      rw [hwp2, show wend - (wp.toNat + 2) = wend - wp.toNat - 2 by omega]
                      exact hts2, hm_w⟩
              · intro Jtk hJtk
                c0_hsplit
                · c0_hsteps_nogrp <;> (c0_hsteps; exact hJtk _ mw rfl)
                · c0_hsteps; exact hJtk _ mw rfl
            · have hww_ne : ww ≠ 0xFFFFFFFF#32 := by
                intro h; dsimp only [ww] at h; c0_bound
              have hfl_bw : (ww &&& 0x80000000#32) ≠ 0#32 := by c0_bound
              simp only [hfl_bw, ↓reduceIte, hww_ne] at hstep_ts
              obtain ⟨h_ot_lt, h_nql_ot, hts_bin⟩ := hstep_ts
              have hwp1 : (wp + 1#64).toNat = wp.toNat + 1 := tr_bv64_add1 (by omega)
              refine wp_join_group (ts := []) (fun () mk => mk = mw) ?_ ?_
              · rintro _ ⟨⟩ mk hmk
                rw [hmk]
                c0_hsteps_nogrp
                refine wp_join_group (ts := [i64]) (fun _ mt => mt = mw) ?_ ?_
                · rintro _ ⟨tw', ⟨⟩⟩ mt hmt
                  rw [hmt]
                  c0_hsteps_nogrp
                  · c0_hsteps
                    exact hBw _ mw
                      ⟨st_w, hu_w, hte_w, hte_mono, hws1_w,
                        fun h => by cases h; contradiction, hm_w⟩
                  · refine wp_join_group (ts := [.bool])
                        (fun _ mk => ∃ st_p,
                          TransUnrollInv c F0 F_cur s st_l src.toNat saved st_p ∧
                          saved < st_p.core.trail_end ∧
                          st_b.core.trail_end ≤ st_p.core.trail_end ∧
                          st_p.scratch.work_stk1 = s.scratch.work_stk1 ∧
                          TombWatchSliceOk F_cur st_p.core nql.toNat
                            (wp.toNat + 1) (wend - (wp.toNat + 1)) nt_w ∧
                          (FullMem c st_p ⋆ R) mk) ?_ ?_
                    · rintro _ ⟨_, ⟨⟩⟩ mk ⟨st_p, hu_p, hte_p, hte_mp, hws1_p, hts_p, hm_p⟩
                      c0_hsteps
                      exact hLw (wend - (wp.toNat + 1)) (tw', wp + 1#64, ()) mk (by omega)
                        ⟨nt_w, st_p, by rw [hwp1], by rw [hwp1]; omega, by rw [hwp1]; omega,
                          hu_p, hte_p, hte_mp, hws1_p, by simpa only [hwp1] using hts_p, hm_p⟩
                    · intro Jbl hJbl
                      let other := ww &&& 0x7FFFFFFF#32
                      have hot_vlen : other.toNat < st_w.core.vals.length :=
                        tr_vals_lt hu_w.len_ok.core_ok h_ot_lt
                      have hot1_vlen :
                          (BitVec.setWidth 64 (other ^^^ 1#32)).toNat <
                            (st_w.core.vals.set (BitVec.setWidth 64 other).toNat 1#8).length := by
                        rw [List.length_set, tr_bv32_setWidth64, tr_bv32_xor1]
                        exact tr_vals_lt hu_w.len_ok.core_ok (litNeg_lt_two_mul h_ot_lt)
                      have htrl_w : st_w.core.trl.length = c.max_vars := hu_w.len_ok.core_ok.trl_len
                      have hte_bv_w : st_w.core.trail_end < 2 ^ 64 :=
                        (tr_bnds hu_w.len_ok.core_ok).2.2.2
                      have hcv_w : st_w.core.cur_vars = st_l.core.cur_vars := by
                        rw [hu_w.same_core]
                      c0_hsteps_nogrp
                      · c0_hsplit
                        c0_hsteps
                        exact hBw _ mw ⟨st_w, hu_w, hte_w, hte_mono, hws1_w,
                          fun _ => tr_lit_bfs_falsified hw0
                            hb_l.core_pres.2.2.2.2.2.2.2.2.2.2.1 hb_l.core_pres.1 hcl0 hu_w
                            h_ot_lt (by assumption) h_src_ql
                            (by simpa [nql, tr_bv32_xor1] using h_nql_ot),
                          hm_w⟩
                      · refine wp_join_group (ts := [])
                            (fun () mp => ∃ st_p,
                              TransUnrollInv c F0 F_cur s st_l src.toNat saved st_p ∧
                              saved < st_p.core.trail_end ∧
                              st_b.core.trail_end ≤ st_p.core.trail_end ∧
                              st_p.scratch.work_stk1 = s.scratch.work_stk1 ∧
                              TombWatchSliceOk F_cur st_p.core nql.toNat
                                (wp.toNat + 1) (wend - (wp.toNat + 1)) nt_w ∧
                              (FullMem c st_p ⋆ R) mp) ?_ ?_
                        · rintro _ ⟨⟩ mp h; c0_hsteps; exact hJbl _ mp h
                        · intro Jp hJp
                          have hJp_noop : Jp () mw :=
                            hJp () mw ⟨st_w, hu_w, hte_w, hte_mono, hws1_w, by
                              simpa only [show wend - wp.toNat - 1 = wend - (wp.toNat + 1)
                                by omega] using hts_bin,
                              hm_w⟩
                          c0_hsteps_nogrp
                          · c0_hsplit
                            have hot_z_sxt :
                                (st_w.core.vals[other.toNat]'hot_vlen).signExtend 32 =
                                  0#32 := by c0_bound
                            have hdom_o := hu_w.vals_domain hw0
                              hb_l.core_pres.2.2.2.2.2.2.2.2.2.2.1 hb_l.core_pres.1
                              (by rw [← hcv_w]; exact h_ot_lt)
                            have hg_o : st_w.core.vals[other.toNat]?.getD 0#8 =
                                st_w.core.vals[other.toNat]'hot_vlen := by
                              simp [List.getElem?_eq_getElem hot_vlen]
                            have hot_z := hg_o ▸
                              tr_vals_zero_of_domain (hg_o ▸ hdom_o) rfl hot_z_sxt
                            have hpre_trl : ∀ i < s.core.trail_end,
                                st_l.core.trl[i]? = s.core.trl[i]? :=
                              hb_l.core_pres.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
                            have hpb := tr_lit_push_bounds hw0
                              hb_l.core_pres.2.2.2.2.2.2.2.2.2.2.1
                              hb_l.core_pres.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
                              hpre_trl hb_l.core_pres.1 hu_w
                              (by rw [← hcv_w]; exact h_ot_lt)
                              hot_z (entails_pair_trans h_src_ql
                                (by simpa [other, nql, tr_bv32_xor1] using h_nql_ot))
                            obtain ⟨hte_lt_w, hte_trl_w, hv_o, hv_no, hsw_o, hsw_no,
                              ⟨_, hte1_w⟩, hpush⟩ := hpb
                            c0_hsteps
                            have hte_s' : (st_w.core.trail_end + 1) % 2 ^ 64 =
                                st_w.core.trail_end + 1 := by
                              have := hu_w.len_ok.core_ok.cur_vars_le
                              have hcmv := c.hmaxv; unfold dimacsBound at hcmv; omega
                            have hte_0' : st_w.core.trail_end % 2 ^ 64 = st_w.core.trail_end :=
                              Nat.mod_eq_of_lt hte_bv_w
                            have hneg1_32 : BitVec.setWidth 8 (-1 : BitVec 32) = 255#8 := by decide
                            have hneg1_64 : BitVec.setWidth 8 (-1 : BitVec 64) = 255#8 := by decide
                            have hte_hm : (BitVec.ofNat 64 st_w.core.trail_end +
                                (1 : BitVec 64)).toNat = st_w.core.trail_end + 1 := by
                              rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hte_bv_w]
                              exact hte_s'
                            have hte0_hm : (BitVec.ofNat 64 st_w.core.trail_end).toNat =
                                st_w.core.trail_end := by
                              rw [BitVec.toNat_ofNat]; exact hte_0'
                            refine hJp () _ ⟨_, hpush, by
                                have := hpush.saved_le_te; dsimp only at *; omega,
                              by dsimp only; exact Nat.le_trans hte_mono (Nat.le_succ _),
                              hu_w.same_scratch ▸ hws1_w, tr_lit_push_watch_mono (by
                                simpa only [show wend - wp.toNat - 1 = wend - (wp.toNat + 1)
                                  by omega] using hts_bin), ?_⟩
                            have h1_bv32 : (1 : BitVec 32).toNat = 1 := by decide
                            rw [tr_bv32_setWidth64, tr_bv32_setWidth64, BitVec.toNat_xor,
                              h1_bv32, hte_hm, hte0_hm] at hm
                            try rw [hneg1_64] at hm
                            try rw [hneg1_32] at hm
                            have h_w0 : (st_w.core.wstk[wp.toNat] &&&
                                (2147483647 : BitVec 32)) = other := rfl
                            have h_v1 : BitVec.ofNat (OfNat.ofNat 8) (OfNat.ofNat 1) =
                                1#8 := rfl
                            rw [h_w0, h_v1] at hm
                            rw [tr_bv32_ofNat_toNat]
                            exact hm
                          · c0_hsteps; exact hJp_noop
                          · c0_hsteps; exact hJp_noop
                      · exfalso
                        have h_ot' :
                            (st_w.core.wstk[wp.toNat] &&& 2147483647#32).toNat < p_13_v.toNat := by
                          rw [hp13, ← hb_l.core_pres.1, ← hcv_w]; exact h_ot_lt
                        exact absurd h_ot' (by assumption)
                · intro Jtk hJtk
                  c0_hsplit
                  · c0_hsteps_nogrp <;> (c0_hsteps; exact hJtk _ mw rfl)
                  · c0_hsteps; exact hJtk _ mw rfl
              · intro Jsk hJsk
                c0_hsplit
                · c0_hsteps_nogrp
                  c0_hsplit
                  · c0_hsteps
                    exact hLw (wend - (wp.toNat + 1)) (tw, wp + 1#64, ()) mw
                      (by omega) ⟨nt_w, st_w, by rw [hwp1], by rw [hwp1]; omega,
                        by rw [hwp1]; omega, hu_w, hte_w, hte_mono, hws1_w, by
                          simpa only [hwp1, show wend - wp.toNat - 1 = wend - (wp.toNat + 1)
                            by omega] using hts_bin,
                        hm_w⟩
                  · c0_hsteps; exact hJsk () mw rfl
                · c0_hsteps; exact hJsk () mw rfl
          · c0_hsteps
            exact hBw _ mw
              ⟨st_w, hu_w, hte_w, hte_mono, hws1_w, (fun h => by cases h; contradiction), hm_w⟩
        · rintro _ _ _ hLw
          c0_hsteps
          have hw0_eq : (BitVec.setWidth 64
              (st_b.core.trl[qhead_b.toNat] ^^^ (1 : BitVec 32)) <<< (1 : Nat)).toNat =
              2 * nql.toNat := by rw [hql_eq, h1_32]; exact hnql_shl
          refine hLw (wend - woff) _ m_b
            ⟨nt0, st_b, ?_, ?_, ?_, hu_b, hte_gt, Nat.le_refl _, hws1_b, ?_, hm_b⟩
          · simp only [hw0_eq, hwoff_nat]; rfl
          · simp only [hw0_eq, hwoff_nat]; exact Nat.le_refl _
          · simp only [hw0_eq, hwoff_nat]; omega
          · simp only [hw0_eq, hwoff_nat]
            change TombWatchSliceOk F_cur st_b.core nql.toNat woff (wend - woff) nt0
            rw [show wend - woff = wsz by dsimp only [wend]; omega]; exact hts0
      · exact hJex () m_b hm_b
      · exact hJex () m_b hm_b

end LeanQbe.T.Examples.Kissat.Proof.Transitive
