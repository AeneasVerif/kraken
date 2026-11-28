/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Backbone.Spec
import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena1
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.ControlComb
meta import LeanQbe.T.Logic.C0Step

/-!
# Kissat Backbone WP Proofs — Round Sweep (`Proof.Backbone.WpRound`)

Canonical `(Γ : Env)` `Func.wp` proof (`0` `@[expose]` on theorems/lemmas) for
`full_backbone_round_m6_wp` (`fullBackboneRoundM6Spec`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Backbone

open Std Std.Sat Std.ExtHashMap Kraken.Bedrock2.Test
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src.Backbone
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Backbone.Spec
open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics

/-! ## 1. File-Local Helpers & Tail Sub-Expression (`BbRoundHelpers`) -/

private theorem rd_strip_le_32_64 {P : Prop} (h : P) : 32 ≤ 64 ∧ P := ⟨by decide, h⟩
private theorem rd_strip_le_8_32 {P : Prop} (h : P) : 8 ≤ 32 ∧ P := ⟨by decide, h⟩
private theorem rd_strip_le_8_64 {P : Prop} (h : P) : 8 ≤ 64 ∧ P := ⟨by decide, h⟩

local macro "bb_strip" : tactic =>
  `(tactic| first
    | apply rd_strip_le_32_64 | apply rd_strip_le_8_32 | apply rd_strip_le_8_64)
local macro "bb_unmdata" : tactic =>
  `(tactic| first | change Func.wp _ _ _ _ _ _ | change wp _ _ _ _ _)
local macro "bb_steps" : tactic =>
  `(tactic| (
      (try bb_unmdata)
      (repeat bb_strip)
      c0_steps
      repeat (any_goals (bb_strip; repeat bb_strip); c0_steps)))

local macro "bb_call" h:term : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_))

private abbrev bbS0Fl (s0 st : FullState) : FullState :=
  { s0 with core := { s0.core with flags := st.core.flags } }

private theorem bb_with_flags_set {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 st : FullState} {saved0 max_lvl : Nat}
    (hbt : BbTrailInv c F0 F_cur (bbS0Fl s0 st) st saved0 max_lvl) (i : Nat) (v : BitVec 32) :
    let st' := { st with core := { st.core with flags := st.core.flags.set i v } }
    BbTrailInv c F0 F_cur (bbS0Fl s0 st') st' saved0 max_lvl :=
  { hbt with
    len_ok := ⟨{ hbt.len_ok.core_ok with flags_len := by simp [hbt.len_ok.core_ok.flags_len] },
      hbt.len_ok.scratch_ok⟩
    same_core := by dsimp only [bbS0Fl]; rw [hbt.same_core] }

private theorem bb_lit_push_bnds {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 st : FullState} {saved0 max_lvl : Nat}
    (hbt : BbTrailInv c F0 F_cur (bbS0Fl s0 st) st saved0 max_lvl)
    {lit : BitVec 32} (hlit : lit.toNat < 2 * s0.core.cur_vars) :
    (lit.setWidth 64).toNat = lit.toNat ∧
    ((lit ^^^ 1#32).setWidth 64).toNat = lit.toNat ^^^ 1 ∧
    ((lit >>> 1#32).setWidth 64).toNat = lit.toNat / 2 ∧
    (lit ^^^ 1#32).toNat < (st.core.vals.set lit.toNat 1#8).length ∧
    (lit >>> 1#32).toNat < st.core.lvl.length ∧
    (lit >>> 1#32).toNat < st.core.rsns.length ∧
    ((lit >>> 1#32).setWidth 64).toNat < st.core.lvl.length ∧
    ((lit >>> 1#32).setWidth 64).toNat < st.core.rsns.length := by
  have hcl := hbt.len_ok.core_ok
  have hcv_st : st.core.cur_vars = s0.core.cur_vars := by rw [hbt.same_core]
  have hcv_le := hcl.cur_vars_le
  have hl64 : (lit.setWidth 64).toNat = lit.toNat := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans lit.isLt (by decide))]
  have hln64 : ((lit ^^^ 1#32).setWidth 64).toNat = lit.toNat ^^^ 1 := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans (lit ^^^ 1#32).isLt (by decide))]
    exact bb_bv32_xor1 lit
  have hlr64 : ((lit >>> 1#32).setWidth 64).toNat = lit.toNat / 2 := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans (lit >>> 1#32).isLt (by decide))]
    exact bb_bv32_lshr1 lit
  refine ⟨hl64, hln64, hlr64, ?_, ?_, ?_, ?_, ?_⟩
  · rw [List.length_set, bb_bv32_xor1, hcl.vals_len]
    exact Nat.lt_of_lt_of_le (litNeg_lt_two_mul hlit) (by omega)
  all_goals simp only [hlr64, bb_bv32_lshr1, hcl.lvl_len, hcl.rsns_len] <;> omega

private theorem bb_fullMem_symm {c : FullCfg} {s1 s2 : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} (hm : (FullMem c s1 ⋆ R) m) (h : s1 = s2) : (FullMem c s2 ⋆ R) m := h ▸ hm

private theorem bb_fl_mem {c : FullCfg} {sf : FullState} {fl' : List (BitVec 32)}
    {R : Mem 64 → Prop} {m : Mem 64} {idx1 idx2 : Nat} {v : BitVec 32} (hi : idx1 = idx2)
    (hm : (FullMem c { sf with core := { sf.core with flags := fl'.set idx1 v } } ⋆ R) m) :
    (FullMem c { sf with core := { sf.core with flags := fl'.set idx2 v } } ⋆ R) m := hi ▸ hm

private theorem bb_fl_ws1_mem {c : FullCfg} {sf : FullState}
    {fl' ws1' : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64} {idx1 idx2 : Nat}
    {v : BitVec 32} (hi : idx1 = idx2)
    (hm : (FullMem c
      { sf with
        core := { sf.core with flags := fl'.set idx1 v }
        scratch := { sf.scratch with work_stk1 := ws1' } } ⋆ R) m) :
    (FullMem c
      { sf with
        core := { sf.core with flags := fl'.set idx2 v }
        scratch := { sf.scratch with work_stk1 := ws1' } } ⋆ R) m := hi ▸ hm

private theorem bb_rsns_saved_ff {_c : FullCfg} {probe : BitVec 32}
    {trl_d trl_p rsns_d rsns_p : List (BitVec 32)} {sav : Nat}
    (hsav_lt : sav < trl_d.length) (hv_lt : probe.toNat / 2 < rsns_d.length)
    (htrl_d : trl_d[sav]? = some probe) (hrsn_d : rsns_d[probe.toNat / 2]? = some 0xFFFFFFFF#32)
    (htp_p : ∀ i < sav + 1, trl_p[i]? = trl_d[i]?)
    (hlp_p : ∀ i < sav + 1,
      let v := (trl_d[i]?.getD 0#32).toNat / 2
      rsns_p[v]? = rsns_d[v]?) :
    rsns_p[(trl_p[sav]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 := by
  have _ := hsav_lt; have _ := hv_lt
  rw [htp_p sav (Nat.lt_succ_self sav), htrl_d, Option.getD_some]
  have hr := hlp_p sav (Nat.lt_succ_self sav)
  rw [htrl_d, Option.getD_some] at hr
  rw [hr, hrsn_d]; rfl

private theorem bb_ws1_keep {ws1 : List (BitVec 32)} {k ci lim bnd : Nat} {x : BitVec 32}
    (hlen : k < ws1.length) (hkle : k ≤ ci) (hx : x.toNat < bnd)
    (hprev : ∀ i < k, (ws1[i]?.getD 0#32).toNat < bnd)
    (hrem : ∀ i, ci ≤ i → i < lim → (ws1[i]?.getD 0#32).toNat < bnd) :
    (∀ i < k + 1, ((ws1.set k x)[i]?.getD 0#32).toNat < bnd) ∧
    (∀ i, ci + 1 ≤ i → i < lim → ((ws1.set k x)[i]?.getD 0#32).toNat < bnd) :=
  ⟨fun i hi => by
     rcases (by omega : i < k ∨ i = k) with hlt | rfl
     · rw [List.getElem?_set_ne (by omega)]; exact hprev i hlt
     · rw [List.getElem?_set_self hlen, Option.getD_some]; exact hx,
   fun i hi1 hi2 => by
     rw [List.getElem?_set_ne (by omega)]; exact hrem i (by omega) hi2⟩

private theorem bb_ws1_skip {ws1 : List (BitVec 32)} {ci lim bnd : Nat}
    (hrem : ∀ i, ci ≤ i → i < lim → (ws1[i]?.getD 0#32).toNat < bnd) :
    ∀ i, ci + 1 ≤ i → i < lim → (ws1[i]?.getD 0#32).toNat < bnd :=
  fun i hi1 hi2 => hrem i (by omega) hi2

private theorem bb_ws2_push {F_cur : List (List Nat)} {ws2 : List (BitVec 32)}
    {u bnd : Nat} {x : BitVec 32} (hlen : u < ws2.length)
    (hx : x.toNat < bnd ∧ (cnfOfClauses F_cur).EntailsClause (cnfClause [x.toNat]))
    (hprev : ∀ i < u, (ws2[i]?.getD 0#32).toNat < bnd ∧
      (cnfOfClauses F_cur).EntailsClause (cnfClause [(ws2[i]?.getD 0#32).toNat])) :
    ∀ i < u + 1, ((ws2.set u x)[i]?.getD 0#32).toNat < bnd ∧
      (cnfOfClauses F_cur).EntailsClause (cnfClause [((ws2.set u x)[i]?.getD 0#32).toNat]) :=
  fun i hi => by
    rcases (by omega : i < u ∨ i = u) with hlt | rfl
    · rw [List.getElem?_set_ne (by omega)]; exact hprev i hlt
    · rw [List.getElem?_set_self hlen, Option.getD_some]; exact hx

private theorem bb_ucnt_mask (ucnt mask : BitVec 64)
    (huc : ucnt.toNat < 2 ^ 63) (hm : mask = 0#64 ∨ mask = 0x8000000000000000#64) :
    (ucnt ||| mask) &&& 0x7FFFFFFFFFFFFFFF#64 = ucnt := by
  have h1 : (ucnt &&& 0x7FFFFFFFFFFFFFFF#64) = ucnt := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, show (0x7FFFFFFFFFFFFFFF#64 : BitVec 64).toNat = 2 ^ 63 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt huc]
  rcases hm with rfl | rfl
  · simpa using h1
  · rw [BitVec.and_or_distrib_right,
      show (0x8000000000000000#64 &&& 0x7FFFFFFFFFFFFFFF#64) = 0#64 from rfl, BitVec.or_zero]
    exact h1

private theorem bb_probeSeg_single {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 st : FullState} {saved0 max_lvl : Nat}
    (hbt : BbTrailInv c F0 F_cur s0 st saved0 max_lvl)
    {probe nlvl_bv : BitVec 32} (hpr_lt : probe.toNat < 2 * s0.core.cur_vars)
    (h0 : st.core.vals[probe.toNat]?.getD 0#8 = 0#8) (hte_lt : st.core.trail_end < c.max_vars)
    (hnlv : nlvl_bv.toNat = max_lvl + 1) :
    let v := probe.toNat / 2
    let st' : FullState :=
      { st with core := { st.core with
        vals := (st.core.vals.set probe.toNat 1#8).set (probe.toNat ^^^ 1) 0xFF#8
        lvl := st.core.lvl.set v nlvl_bv
        rsns := st.core.rsns.set v 0xFFFFFFFF#32
        trl := st.core.trl.set st.core.trail_end probe
        trail_end := st.core.trail_end + 1
        cur_level := max_lvl + 1 } }
    BackboneProbeSeg F_cur st' st.core.trail_end (max_lvl + 1) := by
  intro v st'
  have hcl := hbt.len_ok.core_ok
  have hcv_st : st.core.cur_vars = s0.core.cur_vars := by rw [hbt.same_core]
  have hcv_le : s0.core.cur_vars ≤ c.max_vars := hcv_st ▸ hcl.cur_vars_le
  have hmiss := BbTrailInv.var_unassigned hbt hpr_lt h0
  have hte_trl : st.core.trail_end < st.core.trl.length := by rw [hcl.trl_len]; omega
  have hv_lvl : v < st.core.lvl.length := by rw [hcl.lvl_len]; omega
  refine ⟨by dsimp only [st']; omega, fun i hi => ?_, fun i hi1 hi2 => ?_⟩
  · dsimp only [st']
    have hti : (st.core.trl.set st.core.trail_end probe)[i]? = st.core.trl[i]? :=
      List.getElem?_set_ne (by omega)
    rw [hti, List.getElem?_set_ne (Ne.symm (hmiss i hi))]
    have := hbt.lvl_le_max i hi; omega
  · dsimp only [st'] at hi2 ⊢
    have hi_eq : i = st.core.trail_end := by omega
    subst hi_eq
    rw [List.getElem?_set_self hte_trl, Option.getD_some,
      List.getElem?_set_self hv_lvl, Option.getD_some, hnlv]
    exact ⟨rfl, fun h => absurd h (Nat.lt_irrefl _)⟩

private def bbRoundTailExpr {V : Ty → Type} {L : List Ty → Type}
    (h cand_n saved0 vals fl cands : V i64)
    (ucnt keep ci : V i64) (incons : V Ty.bool) : Expr V L [i64] :=
  Expr.group (sig := [[i64, i64]])
    (fun Js => Blocks.cons (fun p_13 =>
      Expr.let_ (Op.mk (.cmp .ult i64 .bool rfl) (Arg.var p_13.snd.fst, Arg.var cand_n, ()))
        fun p_14 =>
      Expr.jnz (Arg.var p_14.fst)
        (Expr.let_ (Op.mk (.mul i64) (Arg.var p_13.fst, Arg.imm 4, ())) fun pa =>
         Expr.let_ (Op.mk (.add i64) (Arg.var cands, Arg.var pa.fst, ())) fun pb =>
         Expr.let_ (Op.mk (.mul i64) (Arg.var p_13.snd.fst, Arg.imm 4, ())) fun p_15 =>
         Expr.let_ (Op.mk (.add i64) (Arg.var cands, Arg.var p_15.fst, ())) fun p_16 =>
         Expr.load i32 (Arg.var p_16.fst) fun ld =>
         Expr.store (Arg.var ld) (Arg.var pb.fst)
           (Expr.let_ (Op.mk (.add i64) (Arg.var p_13.fst, Arg.imm 1, ())) fun pc =>
            Expr.let_ (Op.mk (.add i64) (Arg.var p_13.snd.fst, Arg.imm 1, ())) fun p_17 =>
            Expr.jump Js.fst (Arg.var pc.fst, Arg.var p_17.fst, ())))
        (Expr.call (as := [i64, i64, i64]) (bs := []) "full_backbone_unwind_m6"
          (Arg.var h, Arg.var saved0, Arg.imm 0, ()) fun _ =>
         Expr.group (sig := [[i64]])
           (fun _ => Blocks.cons (fun p_16 =>
             Expr.group (sig := [[i64]])
               (fun _ => Blocks.cons (fun p_17 =>
                 Expr.let_ (Op.mk (.or i64) (Arg.var ucnt, Arg.var p_17.fst, ())) fun p_18 =>
                 Expr.let_ (Op.mk (.add i64) (Arg.var h, Arg.imm 1144, ())) fun pr =>
                 Expr.store (Arg.var p_18.fst) (Arg.var pr.fst)
                   (Expr.ret (Arg.var p_16.fst, ()))) Blocks.nil)
               fun Js => Expr.jnz (Arg.var incons)
                 (Expr.jump Js.fst (Arg.imm 9223372036854775808, ()))
                 (Expr.jump Js.fst (Arg.imm 0, ()))) Blocks.nil)
           fun Js => Expr.jnz (Arg.var incons) (Expr.jump Js.fst (Arg.var p_13.fst, ()))
             (Expr.group (sig := [[i64, i64]])
               (fun Js_1 => Blocks.cons (fun pf =>
                 Expr.let_ (Op.mk (.cmp .ult i64 .bool rfl) (Arg.var pf.fst, Arg.var p_13.fst, ()))
                   fun p_16 =>
                 Expr.jnz (Arg.var p_16.fst)
                   (Expr.let_ (Op.mk (.mul i64) (Arg.var pf.fst, Arg.imm 4, ())) fun p_17 =>
                    Expr.let_ (Op.mk (.add i64) (Arg.var cands, Arg.var p_17.fst, ())) fun p_18 =>
                    Expr.load i32 (Arg.var p_18.fst) fun ld =>
                    Expr.let_ (Op.mk (.add i64) (Arg.var pf.fst, Arg.imm 1, ())) fun p_19 =>
                    Expr.group (sig := [[i64]])
                      (fun _ => Blocks.cons (fun p =>
                        Expr.jump Js_1.fst (Arg.var p_19.fst, Arg.var p.fst, ())) Blocks.nil)
                      fun Js =>
                    Expr.let_ (Op.mk (.zext 32 64) (Arg.var ld, ())) fun p_20 =>
                    Expr.let_ (Op.mk (.add i64) (Arg.var vals, Arg.var p_20.fst, ())) fun p_21 =>
                    Expr.load i8 (Arg.var p_21.fst) fun ld_9 =>
                    Expr.let_ (Op.mk (.trunc 32 8) (Arg.imm 0, ())) fun p_22 =>
                    Expr.let_ (Op.mk (.sext 8 32) (Arg.var ld_9, ())) fun p_23 =>
                    Expr.let_ (Op.mk (.sext 8 32) (Arg.var p_22.fst, ())) fun p_24 =>
                    Expr.let_ (Op.mk (.cmp .sgt i32 .bool rfl)
                      (Arg.var p_23.fst, Arg.var p_24.fst, ())) fun p_25 =>
                    Expr.jnz (Arg.var p_25.fst)
                      (Expr.let_ (Op.mk (.lshr i32) (Arg.var ld, Arg.imm 1, ())) fun p_26 =>
                       Expr.let_ (Op.mk (.zext 32 64) (Arg.var p_26.fst, ())) fun p_27 =>
                       Expr.let_ (Op.mk (.mul i64) (Arg.var p_27.fst, Arg.imm 4, ())) fun p_28 =>
                       Expr.let_ (Op.mk (.add i64) (Arg.var fl, Arg.var p_28.fst, ())) fun p_29 =>
                       Expr.let_ (Op.mk (.zext 32 64) (Arg.var p_26.fst, ())) fun p_30 =>
                       Expr.let_ (Op.mk (.mul i64) (Arg.var p_30.fst, Arg.imm 4, ())) fun p_31 =>
                       Expr.let_ (Op.mk (.add i64) (Arg.var fl, Arg.var p_31.fst, ())) fun p_32 =>
                       Expr.load i32 (Arg.var p_32.fst) fun ld_10 =>
                       Expr.group (sig := [[i32]])
                         (fun _ => Blocks.cons (fun p_33 =>
                           Expr.let_ (Op.mk (.not i32) (Arg.var p_33.fst, ())) fun p_34 =>
                           Expr.let_ (Op.mk (.and i32) (Arg.var ld_10, Arg.var p_34.fst, ()))
                             fun p_35 =>
                           Expr.store (Arg.var p_35.fst) (Arg.var p_29.fst)
                             (Expr.jump Js.fst (Arg.var pf.snd.fst, ()))) Blocks.nil)
                         fun Js_2 =>
                       Expr.let_ (Op.mk (.and i32) (Arg.var ld, Arg.imm 1, ())) fun p1 =>
                       Expr.let_ (Op.mk (.cmp .ne i32 .bool rfl) (Arg.var p1.fst, Arg.imm 0, ()))
                         fun p2 =>
                       Expr.jnz (Arg.var p2.fst) (Expr.jump Js_2.fst (Arg.imm 256, ()))
                         (Expr.jump Js_2.fst (Arg.imm 128, ())))
                      (Expr.let_ (Op.mk (.mul i64) (Arg.var pf.snd.fst, Arg.imm 4, ()))
                         fun p_26 =>
                       Expr.let_ (Op.mk (.add i64) (Arg.var cands, Arg.var p_26.fst, ()))
                         fun p_27 =>
                       Expr.store (Arg.var ld) (Arg.var p_27.fst)
                         (Expr.let_ (Op.mk (.add i64) (Arg.var pf.snd.fst, Arg.imm 1, ())) fun p3 =>
                          Expr.jump Js.fst (Arg.var p3.fst, ()))))
                   (Expr.jump Js.fst (Arg.var pf.snd.fst, ()))) Blocks.nil)
               fun Js => Expr.jump Js.fst (Arg.imm 0, Arg.imm 0, ())))) Blocks.nil)
    fun Js => Expr.jump Js.fst (Arg.var keep, Arg.var ci, ())

private theorem bb_round_tail_wp {Γ : Env} {Q : Post [i64]} {X : XPost}
    (hUnwind : ∀ a m Q X, fullBackboneUnwindM6Spec a m Q X →
      Γ "full_backbone_unwind_m6" [i64, i64, i64] [] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s0 st : FullState}
    {cand_n ucnt keep ci : BitVec 64} {incons : Bool} {R : Mem 64 → Prop} {mb : Mem 64}
    (hsp0 : FullSparseInvW c F0 F_cur s0) (hl0 : s0.core.cur_level = 0)
    (hbt : BbTrailInv c F0 F_cur (bbS0Fl s0 st) st s0.core.trail_end st.core.cur_level)
    (_hcl_le : st.core.cur_level ≤ c.max_vars) (hkp_le : keep.toNat ≤ ci.toNat)
    (hci_le : ci.toNat ≤ cand_n.toNat)
    (hcn_le : cand_n.toNat ≤ 2 * s0.core.cur_vars)
    (huc_le : ucnt.toNat ≤ 2 * s0.core.cur_vars)
    (hkp_lt : ∀ i < keep.toNat, (st.scratch.work_stk1[i]?.getD 0#32).toNat < 2 * s0.core.cur_vars)
    (hrem_lt : ∀ i, ci.toNat ≤ i → i < cand_n.toNat →
      (st.scratch.work_stk1[i]?.getD 0#32).toNat < 2 * s0.core.cur_vars)
    (huc_ok : ∀ i < ucnt.toNat, (st.scratch.work_stk2[i]?.getD 0#32).toNat < 2 * s0.core.cur_vars ∧
      (cnfOfClauses F_cur).EntailsClause (cnfClause [(st.scratch.work_stk2[i]?.getD 0#32).toNat]))
    (hmb : (FullMem c st ⋆ R) mb)
    (hQ : ∀ keep' s' m',
      FullSparseInvW c F0 F_cur s' → s'.core.cur_level = 0 →
      s'.core.cur_vars = s0.core.cur_vars → s'.core.fuel = s0.core.fuel →
      keep'.toNat ≤ 2 * s0.core.cur_vars →
      (∀ i < keep'.toNat, (s'.scratch.work_stk1[i]?.getD 0#32).toNat < 2 * s0.core.cur_vars) →
      (s'.scratch.res_sz &&& 0x7FFFFFFFFFFFFFFF#64).toNat ≤ 2 * s0.core.cur_vars →
      (∀ i < (s'.scratch.res_sz &&& 0x7FFFFFFFFFFFFFFF#64).toNat,
        (s'.scratch.work_stk2[i]?.getD 0#32).toNat < 2 * s0.core.cur_vars ∧
        (cnfOfClauses F_cur).EntailsClause
          (cnfClause [(s'.scratch.work_stk2[i]?.getD 0#32).toNat])) →
      (FullMem c s' ⋆ R) m' → Q (keep', ()) m') :
    wp Γ Q X
      (bbRoundTailExpr c.hdr cand_n (BitVec.ofNat 64 s0.core.trail_end)
        c.pVals c.pFlags c.pWorkStk1 ucnt keep ci incons) mb := by
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcl0 := hsp0.1.core_ok; have hcv_le := hcl0.cur_vars_le; have hte0_le := hcl0.trail_end_le
  have hs0_to : (BitVec.ofNat 64 s0.core.trail_end).toNat = s0.core.trail_end := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  unfold bbRoundTailExpr
  refine wp_loop_inv (ts := [i64, i64]) (fun (kt, ct, ()) mt => ∃ ws1 : List (BitVec 32),
    ws1.length = 2 * c.max_vars ∧ kt.toNat ≤ ct.toNat ∧ ct.toNat ≤ cand_n.toNat ∧
    (∀ i < kt.toNat, (ws1[i]?.getD 0#32).toNat < 2 * s0.core.cur_vars) ∧
    (∀ i, ct.toNat ≤ i → i < cand_n.toNat →
      (ws1[i]?.getD 0#32).toNat < 2 * s0.core.cur_vars) ∧
    (FullMem c { st with scratch := { st.scratch with work_stk1 := ws1 } } ⋆ R) mt)
    (fun (_, ct, ()) _ => cand_n.toNat - ct.toNat) (fun Jt hJt => by
      bb_steps; exact hJt (keep, ci, ()) mb ⟨st.scratch.work_stk1,
        hbt.len_ok.scratch_ok.work_stk1_len, hkp_le, hci_le, hkp_lt, hrem_lt, hmb⟩)
    (fun Jt ⟨kt, ct, ⟨⟩⟩ mt ⟨ws1, hws1, hkt_le, hct_le, hkt_lt, hct_rem, hmt⟩ iht => ?_)
  c0_hsplit
  · have hct_lt : ct.toNat < cand_n.toNat := by c0_bound
    have hct1 : (ct + 1#64).toNat = ct.toNat + 1 := by bv_omega
    have hkt1 : (kt + 1#64).toNat = kt.toNat + 1 := by bv_omega
    have hct_ws1 : ct.toNat < ws1.length := by omega
    have hkt_ws1 : kt.toNat < ws1.length := by omega
    let rem := ws1[ct.toNat]'hct_ws1
    have hrem_b : rem.toNat < 2 * s0.core.cur_vars := by
      have := hct_rem ct.toNat (Nat.le_refl _) hct_lt
      rwa [List.getElem?_eq_getElem hct_ws1, Option.getD_some] at this
    c0_hsteps; obtain ⟨h1, h2⟩ := bb_ws1_keep hkt_ws1 hkt_le hrem_b hkt_lt hct_rem
    exact iht (kt + 1#64, ct + 1#64, ()) _ (by dsimp only; omega)
      ⟨ws1.set kt.toNat rem, by simp [hws1], by rw [hkt1, hct1]; omega,
       by rw [hct1]; omega, by rwa [hkt1], by rwa [hct1], by assumption⟩
  · have hct_eq : ct.toNat = cand_n.toNat := by
      have h1 : ¬ ct.toNat < cand_n.toNat := by c0_bound
      omega
    let st_w : FullState := { st with scratch := { st.scratch with work_stk1 := ws1 } }
    have hbt_w := BbTrailInv.with_ws1_ws2 hbt (rsz' := st.scratch.res_sz) hws1
      hbt.len_ok.scratch_ok.work_stk2_len
    have hlvl_s0 : ∀ i < s0.core.trail_end,
        (st_w.core.lvl[(st_w.core.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ 0 :=
        fun i hi => by
      have ht0 := hbt_w.trl_prefix i hi; have hlp := (hbt_w.lvl_prefix i hi).1
      dsimp only [bbS0Fl, st_w] at ht0 hlp ⊢; rw [ht0, hlp]
      have := hsp0.2.1.lvl_le i hi; omega
    bb_steps; bb_call hUnwind
    refine ⟨c, F0, F_cur, bbS0Fl s0 st, st_w, s0.core.trail_end, st.core.cur_level, R, rfl,
      bb_sparseW_with_flags hsp0 hbt.len_ok.core_ok.flags_len, hbt_w,
      by dsimp only [Arg.val_var]; omega,
      by dsimp only [Arg.val_var, bbS0Fl]; rw [hs0_to]; exact hbt_w.saved0_le,
      by simp, by dsimp only [Arg.val_var]; simpa [hs0_to] using hlvl_s0,
      hmt, fun vals_f mf hbt_f hmf => ?_⟩
    let sf0 : FullState := { st_w with core := { st_w.core with
      vals := vals_f, trail_end := s0.core.trail_end, cur_level := 0 } }
    have hbt_f' := BbTrailInv.with_ws1_ws2 (by simpa [hs0_to] using hbt_f)
      (rsz' := st_w.scratch.res_sz) hws1 hbt.len_ok.scratch_ok.work_stk2_len
    have hsp_f0 := BbTrailInv.to_fullSparseInvW
      (bb_sparseW_with_flags hsp0 hbt.len_ok.core_ok.flags_len) hbt_f' rfl rfl
    have hmf' : (FullMem c sf0 ⋆ R) mf := by simpa [sf0, hs0_to] using hmf
    have hkt_b : kt.toNat ≤ 2 * s0.core.cur_vars := by omega
    refine wp_join_group (ts := [i64]) (fun (kp', ()) mk' => ∃ fl' ws1' : List (BitVec 32),
      fl'.length = c.max_vars ∧ ws1'.length = 2 * c.max_vars ∧ kp'.toNat ≤ 2 * s0.core.cur_vars ∧
      (∀ i < kp'.toNat, (ws1'[i]?.getD 0#32).toNat < 2 * s0.core.cur_vars) ∧
      (FullMem c { sf0 with core := { sf0.core with flags := fl' },
                            scratch := { sf0.scratch with work_stk1 := ws1' } } ⋆ R) mk')
      (fun _ ⟨kp', ⟨⟩⟩ mk' ⟨fl', ws1', hfl', hws1', hkp', hkp_lt', hmk'⟩ => by
        let sf1 : FullState := { sf0 with
          core := { sf0.core with flags := fl' },
          scratch := { sf0.scratch with work_stk1 := ws1' } }
        have hsp_f1 := bb_sparseW_with_flags (BbTrailInv.to_fullSparseInvW
          (bb_sparseW_with_flags hsp0 hbt.len_ok.core_ok.flags_len)
          (BbTrailInv.with_ws1_ws2 hbt_f'
            (rsz' := sf0.scratch.res_sz) hws1' hbt.len_ok.scratch_ok.work_stk2_len) rfl rfl) hfl'
        refine wp_join_group (ts := [i64])
          (fun (mask, ()) mm => (mask = 0#64 ∨ mask = 0x8000000000000000#64) ∧ mm = mk')
          (fun _ ⟨mask, ⟨⟩⟩ mm ⟨hm_eq, hmm⟩ => by
            subst hmm; c0_hsteps
            let sf := { sf1 with scratch := { sf1.scratch with res_sz := ucnt ||| mask } }
            have huc_msk : (sf.scratch.res_sz &&& 0x7FFFFFFFFFFFFFFF#64) = ucnt :=
              bb_ucnt_mask ucnt mask (by omega) hm_eq
            have hsp_f : FullSparseInvW c F0 F_cur sf :=
              ⟨⟨hsp_f1.1.core_ok, { hsp_f1.1.scratch_ok with work_stk1_len := hws1' }⟩,
               hsp_f1.2.1, hsp_f1.2.2.1, hsp_f1.2.2.2.1, hsp_f1.2.2.2.2.1, hsp_f1.2.2.2.2.2⟩
            have hcv_f : sf.core.cur_vars = s0.core.cur_vars := by
              change st.core.cur_vars = s0.core.cur_vars; rw [hbt.same_core]
            have hfu_f : sf.core.fuel = s0.core.fuel := by
              change st.core.fuel = s0.core.fuel; rw [hbt.same_core]
            exact hQ kp' sf _ hsp_f rfl hcv_f hfu_f hkp' hkp_lt'
              (by simpa [huc_msk] using huc_le) (by simpa [huc_msk] using huc_ok)
              (bb_fullMem_eq (by dsimp only [sf, sf1]) (by assumption)))
          (fun _ hJm => by
            c0_hsplit
            · c0_hsteps; exact hJm (0x8000000000000000#64, ()) mk' ⟨Or.inr rfl, rfl⟩
            · c0_hsteps; exact hJm (0#64, ()) mk' ⟨Or.inl rfl, rfl⟩))
      (fun Jk hJk => by
        c0_hsplit
        · c0_hsteps; exact hJk (kt, ()) mf ⟨sf0.core.flags, ws1,
            hbt_f'.len_ok.core_ok.flags_len, hws1, hkt_b, hkt_lt, hmf'⟩
        · refine wp_loop_inv (ts := [i64, i64]) (fun (fk, fo, ()) mk =>
            ∃ fl' ws1' : List (BitVec 32), fk.toNat ≤ kt.toNat ∧ fo.toNat ≤ fk.toNat ∧
            fl'.length = c.max_vars ∧ ws1'.length = 2 * c.max_vars ∧
            (∀ i < fo.toNat, (ws1'[i]?.getD 0#32).toNat < 2 * s0.core.cur_vars) ∧
            (∀ i, fk.toNat ≤ i → i < kt.toNat →
              (ws1'[i]?.getD 0#32).toNat < 2 * s0.core.cur_vars) ∧
            (FullMem c { sf0 with core := { sf0.core with flags := fl' },
                                  scratch := { sf0.scratch with work_stk1 := ws1' } } ⋆ R) mk)
            (fun (fk, _, ()) _ => kt.toNat - fk.toNat) (fun Jf hJf => by
              c0_hsteps; exact hJf (0#64, 0#64, ()) mf ⟨sf0.core.flags, ws1, Nat.zero_le _,
                Nat.le_refl _, hbt_f'.len_ok.core_ok.flags_len, hws1, (fun _ h => by cases h),
                (fun i _ hi => hkt_lt i hi), hmf'⟩)
            (fun Jf ⟨fk, fo, ⟨⟩⟩ mk ⟨fl', ws1', hfk_le, hfo_le, hfl', hws1', hfo_lt, hfk_rem, hmk⟩
                ihf => ?_)
          c0_hsplit
          · have hfk_lt : fk.toNat < kt.toNat := by c0_bound
            have hfk1 : (fk + 1#64).toNat = fk.toNat + 1 := by bv_omega
            have hfo1 : (fo + 1#64).toNat = fo.toNat + 1 := by bv_omega
            have hfk_ws1 : fk.toNat < ws1'.length := by omega
            have hfo_ws1 : fo.toNat < ws1'.length := by omega
            let rem := ws1'[fk.toNat]'hfk_ws1
            have hrem_b : rem.toNat < 2 * s0.core.cur_vars := by
              have := hfk_rem fk.toNat (Nat.le_refl _) hfk_lt
              rwa [List.getElem?_eq_getElem hfk_ws1, Option.getD_some] at this
            have hrem_val : rem.toNat < sf0.core.vals.length := by
              rw [hbt_f'.len_ok.core_ok.vals_len]; omega
            have hrlv_fl : (rem >>> 1#32).toNat < fl'.length := by
              rw [bb_bv32_lshr1, hfl']; omega
            have hrlv64 :
                (BitVec.setWidth 64 (rem >>> (1 : Nat))).toNat = rem.toNat / 2 := by
              rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt
                (Nat.lt_trans (rem >>> (1 : Nat)).isLt (by decide))]
              exact bb_bv32_lshr1 rem
            have hrlv64_fl : (BitVec.setWidth 64 (rem >>> (1 : Nat))).toNat < fl'.length := by
              rw [hrlv64, hfl']; omega
            c0_hsteps_nogrp
            refine wp_join_group (ts := [i64])
              (fun (fo', ()) mn => ∃ fl'' ws1'' : List (BitVec 32),
                fo'.toNat ≤ fk.toNat + 1 ∧ fl''.length = c.max_vars ∧
                ws1''.length = 2 * c.max_vars ∧
                (∀ i < fo'.toNat, (ws1''[i]?.getD 0#32).toNat < 2 * s0.core.cur_vars) ∧
                (∀ i, fk.toNat + 1 ≤ i → i < kt.toNat →
                  (ws1''[i]?.getD 0#32).toNat < 2 * s0.core.cur_vars) ∧
                (FullMem c { sf0 with core := { sf0.core with flags := fl'' },
                                      scratch := { sf0.scratch with work_stk1 := ws1'' } } ⋆ R)
                  mn)
              (fun _ ⟨fo', ⟨⟩⟩ mn ⟨fl'', ws1'', hfo', hfl'', hws1'', hfo_lt', hrem', hmn⟩ => by
                c0_hsteps
                exact ihf (fk + 1#64, fo', ()) mn (by dsimp only; omega)
                  ⟨fl'', ws1'', by rw [hfk1]; omega, by rw [hfk1]; exact hfo', hfl'', hws1'',
                   hfo_lt', by rwa [hfk1], hmn⟩)
              (fun Jn hJn => by
                c0_hsplit
                · c0_hsteps_nogrp; refine wp_unroll_group fun Jm hJm => ?_; c0_hsplit
                  · c0_hsteps
                    have hm_f := bb_fl_ws1_mem hrlv64 (by assumption)
                    exact hJn (fo, ()) _ ⟨_, ws1', by omega, by rw [List.length_set]; exact hfl',
                      hws1', hfo_lt, bb_ws1_skip hfk_rem, hm_f⟩
                  · c0_hsteps
                    have hm_f := bb_fl_ws1_mem hrlv64 (by assumption)
                    exact hJn (fo, ()) _ ⟨_, ws1', by omega, by rw [List.length_set]; exact hfl',
                      hws1', hfo_lt, bb_ws1_skip hfk_rem, hm_f⟩
                · c0_hsteps
                  obtain ⟨h1, h2⟩ := bb_ws1_keep hfo_ws1 hfo_le hrem_b hfo_lt hfk_rem
                  exact hJn (fo + 1#64, ()) _ ⟨fl', ws1'.set fo.toNat rem, by rw [hfo1]; omega,
                    hfl', by simp [hws1'], by rwa [hfo1], h2,
                    bb_fullMem_symm (by assumption) (by simp [rem])⟩)
          · c0_hsteps; exact hJk (fo, ()) mk ⟨fl', ws1', hfl', hws1', by omega, hfo_lt, hmk⟩)

/-! ## 2. `full_backbone_round_m6_wp` (`fullBackboneRoundM6Spec`) -/

theorem full_backbone_round_m6_wp (Γ : Env)
    (hProp : ∀ a m Q X, fullBackbonePropM6Spec a m Q X →
      Γ "full_backbone_prop_m6" [i64, i64, .bool] [.bool] a m Q X)
    (hAnalyze : ∀ a m Q X, fullBackboneAnalyzeM6Spec a m Q X →
      Γ "full_backbone_analyze_m6" [i64, i32, i32, i64] [i32] a m Q X)
    (hUnwind : ∀ a m Q X, fullBackboneUnwindM6Spec a m Q X →
      Γ "full_backbone_unwind_m6" [i64, i64, i64] [] a m Q X) :
    ∀ a m Q X, fullBackboneRoundM6Spec a m Q X →
      Func.wp Γ full_backbone_round_m6_body a m Q X := by
  rintro ⟨h, cand_n, stop_early, ⟨⟩⟩ m0 Q X
    ⟨c, F0, F_cur, s0, R, rfl, hsp0, hl0, hcn_le, hlt_c, hm0, hQ⟩
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcl0 := hsp0.1.core_ok; have hscl0 := hsp0.1.scratch_ok
  have hcv_le := hcl0.cur_vars_le; have hte0_le := hcl0.trail_end_le
  have hnlits_eq :
      ((BitVec.ofNat 64 s0.core.cur_vars) <<< (BitVec.signExtend 64 1#32)).toNat =
        2 * s0.core.cur_vars := by
    rw [bb_bv64_shl1_sext _ (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega),
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hs0_bv : (BitVec.ofNat 64 s0.core.trail_end).toNat = s0.core.trail_end := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  unfold Func.wp full_backbone_round_m6_body
  let roundInv (ucnt keep ci : BitVec 64) (m : Mem 64) : Prop :=
    ∃ st : FullState,
      BbTrailInv c F0 F_cur (bbS0Fl s0 st) st s0.core.trail_end st.core.cur_level ∧
      st.core.cur_level ≤ c.max_vars ∧ keep.toNat ≤ ci.toNat ∧ ci.toNat ≤ cand_n.toNat ∧
      ucnt.toNat ≤ 2 * s0.core.cur_vars ∧
      (∀ i < keep.toNat, (st.scratch.work_stk1[i]?.getD 0#32).toNat < 2 * s0.core.cur_vars) ∧
      (∀ i, ci.toNat ≤ i → i < cand_n.toNat →
        (st.scratch.work_stk1[i]?.getD 0#32).toNat < 2 * s0.core.cur_vars) ∧
      (∀ i < ucnt.toNat, (st.scratch.work_stk2[i]?.getD 0#32).toNat < 2 * s0.core.cur_vars ∧
        (cnfOfClauses F_cur).EntailsClause
          (cnfClause [(st.scratch.work_stk2[i]?.getD 0#32).toNat])) ∧
      (FullMem c st ⋆ R) m
  c0_hsteps_nogrp
  refine wp_join_group (ts := [i64, i64, i64, .bool])
    (fun (ucnt, keep, ci, _incons, ()) mb => roundInv ucnt keep ci mb)
    (fun _ ⟨ucnt, keep, ci, incons, ⟨⟩⟩ mb
        ⟨st, hbt, _hcl_le, hkp_le, hci_le, huc_le, hkp_lt, hrem_lt, huc_ok, hmb⟩ =>
      bb_round_tail_wp (X := X) (incons := incons) hUnwind hsp0 hl0 hbt ‹_› hkp_le hci_le
        hcn_le huc_le hkp_lt hrem_lt huc_ok hmb hQ)
    (fun Jbr hJbr => ?_)
  refine wp_loop_inv (ts := [i64, i64, i64])
    (fun (ucnt, keep, ci, ()) m1 => roundInv ucnt keep ci m1)
    (fun (_, _, ci, ()) _ => cand_n.toNat - ci.toNat)
    (fun J1 hJ1 => by
      c0_hsteps_nogrp
      exact hJ1 (0#64, 0#64, 0#64, ()) m0 ⟨s0, by rw [hl0]; exact BbTrailInv.init hsp0 hl0,
        by omega, Nat.le_refl _, Nat.zero_le _, Nat.zero_le _, (fun _ h => by cases h),
        fun i _ hi => hlt_c i hi, (fun _ h => by cases h), hm0⟩)
    (fun J1 ⟨ucnt, keep, ci, ⟨⟩⟩ m1
        ⟨st, hbt, hcl_le, hkp_le, hci_le, huc_le, hkp_lt, hrem_lt, huc_ok, hm1⟩ ih1 => ?_)
  have hcl := hbt.len_ok.core_ok; have hscl := hbt.len_ok.scratch_ok
  have hcv_st : st.core.cur_vars = s0.core.cur_vars := by rw [hbt.same_core]
  have hte_le : st.core.trail_end ≤ c.max_vars := Nat.le_trans hcl.trail_end_le (by omega)
  c0_hsplit
  · have hci_lt : ci.toNat < cand_n.toNat := by c0_bound
    c0_hsplit
    · c0_hsplit
      · have hte_lt : st.core.trail_end < c.max_vars := by
          have h1 : st.core.trail_end % 2 ^ 64 < c.max_vars % 2 ^ 64 := by c0_bound
          rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h1
        have hci1 : (ci + 1#64).toNat = ci.toNat + 1 := by bv_omega
        have hkp1 : (keep + 1#64).toNat = keep.toNat + 1 := by bv_omega
        have hci_ws1 : ci.toNat < st.scratch.work_stk1.length := by rw [hscl.work_stk1_len]; omega
        have hkp_ws1 : keep.toNat < st.scratch.work_stk1.length := by rw [hscl.work_stk1_len]; omega
        let probe := st.scratch.work_stk1[ci.toNat]'hci_ws1
        have hpr_lt : probe.toNat < 2 * s0.core.cur_vars := by
          have := hrem_lt ci.toNat (Nat.le_refl _) hci_lt
          rwa [List.getElem?_eq_getElem hci_ws1, Option.getD_some] at this
        have hpr_val : probe.toNat < st.core.vals.length := by rw [hcl.vals_len]; omega
        have hpr_fl : (probe >>> 1#32).toNat < st.core.flags.length := by
          rw [bb_bv32_lshr1, hcl.flags_len]; omega
        have hpr_lvl : (probe >>> 1#32).toNat < st.core.lvl.length := by
          rw [bb_bv32_lshr1, hcl.lvl_len]; omega
        have hprr64 : (BitVec.setWidth 64 (probe >>> (1 : Nat))).toNat = probe.toNat / 2 := by
          rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt
            (Nat.lt_trans (probe >>> (1 : Nat)).isLt (by decide))]
          exact bb_bv32_lshr1 probe
        have hprr64_lvl :
            (BitVec.setWidth 64 (probe >>> (1 : Nat))).toNat < st.core.lvl.length := by
          rw [hprr64, hcl.lvl_len]; omega
        have hprr64_fl :
            (BitVec.setWidth 64 (probe >>> (1 : Nat))).toNat < st.core.flags.length := by
          rw [hprr64, hcl.flags_len]; omega
        have hpr_dom := hbt.vals_dom probe.toNat hpr_lt
        rw [List.getElem?_eq_getElem hpr_val, Option.getD_some] at hpr_dom
        c0_hsplit
        · c0_hsteps_nogrp; refine wp_unroll_group fun Jm hJm => ?_; c0_hsplit
          · c0_hsteps
            exact ih1 (ucnt, keep, ci + 1#64, ()) _ (by dsimp only; omega)
              ⟨_, bb_with_flags_set hbt (probe.toNat / 2) _, hcl_le, by omega, by omega,
               huc_le, hkp_lt, by rw [hci1]; exact bb_ws1_skip hrem_lt, huc_ok,
               bb_fl_mem (sf := st) hprr64 (by assumption)⟩
          · c0_hsteps
            exact ih1 (ucnt, keep, ci + 1#64, ()) _ (by dsimp only; omega)
              ⟨_, bb_with_flags_set hbt (probe.toNat / 2) _, hcl_le, by omega, by omega,
               huc_le, hkp_lt, by rw [hci1]; exact bb_ws1_skip hrem_lt, huc_ok,
               bb_fl_mem (sf := st) hprr64 (by assumption)⟩
        · rename_i h_ngt; c0_hsplit
          · c0_hsteps_nogrp; refine wp_unroll_group fun J hJ => ?_; c0_hsplit
            · c0_hsteps
              obtain ⟨h1, h2⟩ := bb_ws1_keep hkp_ws1 hkp_le hpr_lt hkp_lt hrem_lt
              exact ih1 (ucnt, keep + 1#64, ci + 1#64, ()) _ (by dsimp only; omega)
                ⟨{ st with scratch := { st.scratch with
                    work_stk1 := st.scratch.work_stk1.set keep.toNat probe } },
                 BbTrailInv.with_ws1_ws2 hbt (rsz' := st.scratch.res_sz)
                   (by simp [hscl.work_stk1_len]) hscl.work_stk2_len,
                 hcl_le, by omega, by omega, huc_le, by rwa [hkp1], by rwa [hci1], huc_ok,
                 (by assumption)⟩
            · c0_hsteps
              exact ih1 (ucnt, keep, ci + 1#64, ()) m1 (by dsimp only; omega)
                ⟨st, hbt, hcl_le, by omega, by omega, huc_le, hkp_lt,
                 by rw [hci1]; exact bb_ws1_skip hrem_lt, huc_ok, hm1⟩
          · rename_i h_nlt
            have hpr_z : st.core.vals[probe.toNat]?.getD 0#8 = 0#8 := by
              rw [List.getElem?_eq_getElem hpr_val, Option.getD_some]
              rcases hpr_dom with hz | h1 | hff
              · exact hz
              · exfalso; dsimp only [probe] at h1; rw [h1] at h_nlt; exact absurd h_nlt (by decide)
              · exfalso; dsimp only [probe] at hff; rw [hff] at hc; exact absurd hc (by decide)
            have hte_bv : (BitVec.ofNat 64 st.core.trail_end).toNat = st.core.trail_end := by
              rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
            have hold_bv : (BitVec.ofNat 64 st.core.cur_level).toNat = st.core.cur_level := by
              rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
            have hnlvl_add : (BitVec.ofNat 64 st.core.cur_level + 1).toNat =
                st.core.cur_level + 1 := by
              rw [BitVec.toNat_add, hold_bv, show (1 : BitVec 64).toNat = 1 from rfl,
                Nat.mod_eq_of_lt (by omega)]
            c0_hsplit
            · c0_hsteps
              obtain ⟨h1, h2⟩ := bb_ws1_keep hkp_ws1 hkp_le hpr_lt hkp_lt hrem_lt
              exact hJbr (ucnt, keep + 1#64, ci + 1#64, false, ()) _
                ⟨{ st with scratch := { st.scratch with
                    work_stk1 := st.scratch.work_stk1.set keep.toNat probe } },
                 BbTrailInv.with_ws1_ws2 hbt (rsz' := st.scratch.res_sz)
                   (by simp [hscl.work_stk1_len]) hscl.work_stk2_len,
                 hcl_le, by omega, by omega, huc_le, by rwa [hkp1], by rwa [hci1], huc_ok,
                 (by assumption)⟩
            · have hnlvl_le : st.core.cur_level + 1 ≤ c.max_vars := by
                have h1 : (BitVec.ofNat 64 st.core.cur_level + 1).toNat ≤
                    (BitVec.ofNat 64 c.max_vars).toNat := by c0_bound
                rwa [hnlvl_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h1
              have hnlvl_tr : ((BitVec.ofNat 64 st.core.cur_level + 1).truncate 32).toNat =
                  st.core.cur_level + 1 := by
                rw [BitVec.toNat_setWidth, hnlvl_add, Nat.mod_eq_of_lt (by omega)]
              have ⟨hpr64, hprn64, _, hprn_vlen, _, hpr_rsns, hprr64_lvl, hprr64_rsn⟩ :=
                bb_lit_push_bnds hbt hpr_lt
              have hte_trl : (BitVec.ofNat 64 st.core.trail_end).toNat < st.core.trl.length := by
                rw [hte_bv, hcl.trl_len]; omega
              have hte_add : (BitVec.ofNat 64 st.core.trail_end + 1).toNat =
                  st.core.trail_end + 1 := by
                rw [BitVec.toNat_add, hte_bv, show (1 : BitVec 64).toNat = 1 from rfl,
                  Nat.mod_eq_of_lt (by omega)]
              let st_d : FullState := { st with core := { st.core with
                vals := (st.core.vals.set probe.toNat 1#8).set (probe.toNat ^^^ 1) 0xFF#8
                lvl := st.core.lvl.set (probe.toNat / 2)
                  ((BitVec.ofNat 64 st.core.cur_level + 1).truncate 32)
                rsns := st.core.rsns.set (probe.toNat / 2) 0xFFFFFFFF#32
                trl := st.core.trl.set st.core.trail_end probe
                trail_end := st.core.trail_end + 1, cur_level := st.core.cur_level + 1 } }
              have hbt_d := BbTrailInv.push hbt (Nat.le_succ _) (rsn := 0xFFFFFFFF#32)
                hpr_lt hpr_z hte_lt
                (by rw [hnlvl_tr]; omega) (Nat.le_refl _) (by rw [hnlvl_tr]; omega)
              have hseg_d := bb_probeSeg_single hbt hpr_lt hpr_z hte_lt hnlvl_tr
              have hsp0_fl := bb_sparseW_with_flags hsp0 hcl.flags_len
              c0_hsteps_nogrp; bb_call hProp
              refine ⟨c, F0, F_cur, bbS0Fl s0 st_d, st_d, s0.core.trail_end,
                st.core.cur_level + 1, R, rfl, hsp0_fl, hbt_d,
                by rw [Arg.val_var, hte_bv]; exact hbt.saved0_le,
                by dsimp only [Arg.val_var, st_d]; rw [hte_bv]; omega,
                Or.inr ⟨by dsimp only [Arg.val_var, st_d]; omega,
                  by dsimp only [Arg.val_var, st_d]; omega⟩, ?_,
                fun pok vals_p lvl_p rsns_p trl_p te_p c0_p c1_p asz_p mp
                  hbt_p hte_p htp_p hlp_p hseg_p hcf_p hmp => ?_⟩
              · refine bb_fullMem_eq ?_ (by assumption)
                simp only [st_d, probe, hnlvl_add, hpr64, hprr64, hte_bv, hte_add]
                erw [hprn64]; rfl
              let st_p : FullState :=
                { st_d with
                  core := { st_d.core with
                    vals := vals_p, lvl := lvl_p, rsns := rsns_p, trl := trl_p
                    trail_end := te_p, confl_lit0 := c0_p, confl_lit1 := c1_p }
                  scratch := { st_d.scratch with ant_sz := asz_p } }
              have hseg_p' := hseg_p st.core.trail_end hbt.saved0_le
                (by rw [Arg.val_var, hte_bv]; exact Nat.le_refl _)
                (by dsimp only [st_d]; omega) hseg_d
              have hlvl_saved : ∀ i < st.core.trail_end,
                  (lvl_p[(trl_p[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
                    st.core.cur_level := fun i hi => by
                have h1 := hseg_p'.2.1 i hi; dsimp only [st_p, st_d] at h1; omega
              c0_hsplit
              · c0_hsteps
                exact ih1 (ucnt, keep, ci + 1#64, ()) mp (by dsimp only; omega)
                  ⟨st_p, hbt_p, hnlvl_le, by omega, by omega, huc_le, hkp_lt,
                   by rw [hci1]; exact bb_ws1_skip hrem_lt, huc_ok, hmp⟩
              · obtain ⟨hc0_lt, hc1_lt, hc0_ff, hc1_ff, hent_cf, idx0, hidx0_ge, hidx0_lt,
                  hidx0_eq⟩ := hcf_p (by c0_bound)
                dsimp only [bbS0Fl] at hc0_lt hc1_lt
                have hc0_tr : (c0_p.truncate 32).toNat = c0_p.toNat := by
                  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
                have hc1_tr : (c1_p.truncate 32).toNat = c1_p.toNat := by
                  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
                let st_pr : FullState :=
                  { st_p with scratch := { st_p.scratch with
                    res_sz := BitVec.ofNat 64 s0.core.trail_end } }
                have hbt_pr := BbTrailInv.with_ws1_ws2 hbt_p
                  (rsz' := BitVec.ofNat 64 s0.core.trail_end) hscl.work_stk1_len hscl.work_stk2_len
                have hrsn_sav := bb_rsns_saved_ff (_c := c) (probe := probe)
                  (trl_d := st_d.core.trl) (trl_p := trl_p) (rsns_d := st_d.core.rsns)
                  (rsns_p := rsns_p) (sav := st.core.trail_end)
                  (by dsimp only [st_d]; rw [List.length_set, hcl.trl_len]; omega)
                  (by dsimp only [st_d]; rw [List.length_set, hcl.rsns_len]; omega)
                  (List.getElem?_set_self (by rwa [hte_bv] at hte_trl))
                  (List.getElem?_set_self (by rw [bb_bv32_lshr1] at hpr_rsns; exact hpr_rsns))
                  htp_p (fun i hi => (hlp_p i hi).2)
                c0_hsteps_nogrp; bb_call hAnalyze
                refine ⟨c, F0, F_cur, bbS0Fl s0 st_pr, st_pr, s0.core.trail_end,
                  st.core.cur_level + 1, R, rfl, hsp0_fl, hbt_pr,
                  by dsimp only [Arg.val_var, st_pr, st_p, st_d]; omega, rfl,
                  by dsimp only [Arg.val_var, st_pr]; rw [hte_bv]; exact hbt.saved0_le,
                  by dsimp only [Arg.val_var, st_pr, st_p]; rw [hte_bv]; exact hrsn_sav,
                  by simp only [Arg.val_var, hte_bv]; exact ⟨hseg_p'.1, hseg_p'.2.1, hseg_p'.2.2⟩,
                  by dsimp only [Arg.val_var]; rwa [hc0_tr],
                  by dsimp only [Arg.val_var]; rwa [hc1_tr],
                  by dsimp only [Arg.val_var]; rwa [hc0_tr],
                  by dsimp only [Arg.val_var]; rwa [hc1_tr],
                  by dsimp only [Arg.val_var]; rwa [hc0_tr, hc1_tr],
                  ⟨idx0, by simpa only [Arg.val_var, hte_bv] using hidx0_ge,
                   hidx0_lt, by dsimp only [Arg.val_var]; rwa [hc0_tr]⟩,
                  (by first | assumption | exact bb_fullMem_symm (by assumption) rfl),
                  fun uip mrk_a ma hma_len hma_z huip_ok hma => ?_⟩
                have hmrk_eq := BbTrailInv.with_mrk hbt_pr hsp0_fl hma_len hma_z
                have hma' : (FullMem c st_pr ⋆ R) ma := by
                  refine bb_fullMem_eq ?_ hma
                  have h1 : st.core.mrk = s0.core.mrk := by rw [hbt.same_core]
                  dsimp only [st_pr, st_p, st_d]; rw [hmrk_eq, h1]
                bb_call hUnwind
                refine ⟨c, F0, F_cur, bbS0Fl s0 st_pr, st_pr, s0.core.trail_end,
                  st.core.cur_level + 1, R, rfl, hsp0_fl, hbt_pr,
                  by dsimp only [Arg.val_var]; rw [hte_bv]; exact hbt.saved0_le,
                  by dsimp only [Arg.val_var, st_pr, st_p, st_d] at hte_p ⊢; rw [hte_bv]; omega,
                  by dsimp only [Arg.val_var]; rw [hold_bv]; exact hcl_le,
                  by dsimp only [Arg.val_var]; simpa [hte_bv, hold_bv] using hlvl_saved,
                  hma', fun vals_u mu hbt_u hmu => ?_⟩
                let st_u : FullState := { st_pr with core := { st_pr.core with
                  vals := vals_u, trail_end := st.core.trail_end, cur_level := st.core.cur_level } }
                have hbt_u' : BbTrailInv c F0 F_cur (bbS0Fl s0 st_u) st_u s0.core.trail_end
                    st.core.cur_level := by simpa [st_u, bbS0Fl, hte_bv, hold_bv] using hbt_u
                have hmu' : (FullMem c st_u ⋆ R) mu := by simpa [st_u, hte_bv, hold_bv] using hmu
                clear hmu
                c0_hsplit
                · c0_hsteps
                  obtain ⟨h1, h2⟩ := bb_ws1_keep hkp_ws1 hkp_le hpr_lt hkp_lt hrem_lt
                  exact ih1 (ucnt, keep + 1#64, ci + 1#64, ()) _ (by dsimp only; omega)
                    ⟨{ st_u with scratch := { st_u.scratch with
                        work_stk1 := st.scratch.work_stk1.set keep.toNat probe } },
                     BbTrailInv.with_ws1_ws2 hbt_u' (rsz' := st_u.scratch.res_sz)
                      (by rw [List.length_set]; exact hscl.work_stk1_len) hscl.work_stk2_len,
                     hcl_le, by omega, by omega, huc_le,
                     by rwa [hkp1], by rwa [hci1], huc_ok, (by assumption)⟩
                · have huip_ne : uip ≠ 0xFFFFFFFF#32 := by c0_bound
                  obtain ⟨huip_lt, hent_nu⟩ := huip_ok huip_ne
                  let not_uip := uip ^^^ 1#32
                  have hnu_eq : not_uip.toNat = uip.toNat ^^^ 1 := bb_bv32_xor1 uip
                  have hnu_lt : not_uip.toNat < 2 * s0.core.cur_vars := by
                    rw [hnu_eq]; exact litNeg_lt_two_mul huip_lt
                  have hnu_ent :
                      (cnfOfClauses F_cur).EntailsClause (cnfClause [not_uip.toNat]) := by
                    rwa [hnu_eq]
                  c0_hsteps_nogrp
                  refine wp_join_group (ts := [i64])
                    (fun (ucnt', ()) m_u => ∃ ws2' : List (BitVec 32),
                      ws2'.length = 2 * c.max_vars ∧ ucnt'.toNat ≤ 2 * s0.core.cur_vars ∧
                      (∀ i < ucnt'.toNat, (ws2'[i]?.getD 0#32).toNat < 2 * s0.core.cur_vars ∧
                        (cnfOfClauses F_cur).EntailsClause
                          (cnfClause [(ws2'[i]?.getD 0#32).toNat])) ∧
                      (FullMem c { st_u with scratch := { st_u.scratch with work_stk2 := ws2' } }
                        ⋆ R) m_u)
                    ?_ ?_
                  · rintro _ ⟨ucnt', ⟨⟩⟩ m_u ⟨ws2', hws2', huc', huc_ok', hm_u⟩
                    rw [Blocks.get_here]
                    let st_u2 : FullState :=
                      { st_u with scratch := { st_u.scratch with work_stk2 := ws2' } }
                    have hbt_u2 := BbTrailInv.with_ws1_ws2 hbt_u' (rsz' := st_u.scratch.res_sz)
                      hscl.work_stk1_len hws2'
                    have hnu_val : not_uip.toNat < vals_u.length := by
                      rw [hbt_u2.len_ok.core_ok.vals_len]; omega
                    have hnu_dom := hbt_u2.vals_dom not_uip.toNat hnu_lt
                    rw [List.getElem?_eq_getElem hnu_val, Option.getD_some] at hnu_dom
                    c0_hsplit
                    · c0_hsteps
                      exact hJbr (ucnt', keep, ci + 1#64, true, ()) m_u
                        ⟨st_u2, hbt_u2, hcl_le, by rw [hci1]; omega, by omega, huc', hkp_lt,
                         by rw [hci1]; exact bb_ws1_skip hrem_lt, huc_ok', hm_u⟩
                    · clear hc; refine wp_unroll_group fun Jn hJn => ?_
                      c0_hsplit
                      · have hnu_z : vals_u[not_uip.toNat]?.getD 0#8 = 0#8 := by
                          rw [List.getElem?_eq_getElem hnu_val, Option.getD_some]
                          exact (bb_bv8_sext32_eq0 _).mp hc
                        c0_hsplit
                        · have ⟨hnu64, _huip64, hnur64, hnu_not_v, hnu_lvl, hnu_rsn, hnu_lvl64,
                              hnu_rsn64⟩ := bb_lit_push_bnds (st := st_u2) hbt_u2 hnu_lt
                          have huip_v : uip.toNat < (vals_u.set not_uip.toNat 1#8).length := by
                            rwa [← show (not_uip ^^^ 1#32).toNat = uip.toNat by
                              dsimp only [not_uip]
                              rw [bb_bv32_xor1, bb_bv32_xor1, Nat.xor_assoc,
                                Nat.xor_self, Nat.xor_zero]]
                          have huip_v64 : (uip.setWidth 64).toNat <
                              (vals_u.set not_uip.toNat 1#8).length := by
                            rw [BitVec.toNat_setWidth,
                              Nat.mod_eq_of_lt (Nat.lt_trans uip.isLt (by decide))]
                            exact huip_v
                          have hnu_trl :
                              (BitVec.ofNat 64 st.core.trail_end).toNat <
                                st_u2.core.trl.length := by
                            rw [hte_bv, hbt_u2.len_ok.core_ok.trl_len]; omega
                          let st_l0 : FullState := { st_u2 with core := { st_u2.core with
                            vals := (vals_u.set not_uip.toNat 1#8).set
                              (not_uip.toNat ^^^ 1) 0xFF#8
                            lvl := st_u2.core.lvl.set (not_uip.toNat / 2)
                              ((BitVec.ofNat 64 st.core.cur_level).truncate 32)
                            rsns := st_u2.core.rsns.set (not_uip.toNat / 2) 0xFFFFFFFF#32
                            trl := st_u2.core.trl.set st.core.trail_end not_uip
                            trail_end := st.core.trail_end + 1 } }
                          have hbt_l0 : BbTrailInv c F0 F_cur (bbS0Fl s0 st_l0) st_l0
                              s0.core.trail_end st.core.cur_level :=
                            BbTrailInv.push hbt_u2 (Nat.le_refl _) hnu_lt hnu_z hte_lt
                              (by rw [BitVec.toNat_setWidth, hold_bv,
                                    Nat.mod_eq_of_lt (by omega)]; exact Nat.le_refl _)
                              (Nat.le_refl _) (fun _ => hnu_ent)
                          have hl0_mode : (st_l0.core.cur_level = 0 ∧
                              ∀ i, (BitVec.ofNat 64 st.core.trail_end).toNat ≤ i →
                                i < st_l0.core.trail_end →
                                (st_l0.core.lvl[(st_l0.core.trl[i]?.getD 0#32).toNat / 2]?.getD
                                  0#32).toNat = 0) ∨
                              (0 < st_l0.core.cur_level ∧ st_l0.core.cur_level ≤ c.max_vars) := by
                            by_cases h0 : st.core.cur_level = 0
                            · refine Or.inl ⟨h0, fun i hi1 hi2 => ?_⟩
                              dsimp only [st_l0] at hi2 ⊢; rw [hte_bv] at hi1
                              obtain rfl : i = st.core.trail_end := by omega
                              rw [List.getElem?_set_self
                                  (by rw [hbt_u2.len_ok.core_ok.trl_len]; omega),
                                Option.getD_some, List.getElem?_set_self
                                  (by rw [hbt_u2.len_ok.core_ok.lvl_len]; omega),
                                Option.getD_some, BitVec.toNat_setWidth, hold_bv,
                                Nat.mod_eq_of_lt (by omega), h0]
                            · exact Or.inr ⟨Nat.pos_of_ne_zero h0, hcl_le⟩
                          c0_hsteps_nogrp; bb_call hProp
                          refine ⟨c, F0, F_cur, bbS0Fl s0 st_l0, st_l0, s0.core.trail_end,
                            st.core.cur_level, R, rfl, hsp0_fl, hbt_l0,
                            by dsimp only [Arg.val_var]; rw [hte_bv]; exact hbt.saved0_le,
                            by dsimp only [Arg.val_var, st_l0]; rw [hte_bv]; omega,
                            by dsimp only [Arg.val_var]; exact hl0_mode, ?_,
                            fun pok2 vals2 lvl2 rsns2 trl2 te2 c02 c12 asz2 m2
                              hbt2 _ _ _ _ _ hm2 => ?_⟩
                          · refine bb_fullMem_eq ?_ (by assumption)
                            have huip64' : (BitVec.setWidth 64 uip).toNat = uip.toNat := by
                              rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
                            have hnu64' : (BitVec.setWidth 64 (uip ^^^ 1)).toNat =
                                not_uip.toNat := hnu64
                            have hnur64' : (BitVec.setWidth 64 ((uip ^^^ 1) >>> 1)).toNat =
                                not_uip.toNat / 2 := hnur64
                            dsimp only [Arg.val_var, st_l0, st_u2, st_u, st_pr, st_p, st_d]
                            dsimp only [not_uip] at hnu_eq ⊢
                            rw [hnu64', huip64', hnur64', hte_bv, hte_add, hnu_eq,
                              Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]; rfl
                          let st_r : FullState :=
                            { st_l0 with
                              core := { st_l0.core with
                                vals := vals2, lvl := lvl2, rsns := rsns2, trl := trl2,
                                trail_end := te2, confl_lit0 := c02, confl_lit1 := c12 }
                              scratch := { st_l0.scratch with ant_sz := asz2 } }
                          c0_hsplit
                          · c0_hsteps
                            exact ih1 (ucnt', keep, ci + 1#64, ()) m2 (by dsimp only; omega)
                              ⟨st_r, hbt2, hcl_le, by rw [hci1]; omega, by omega, huc', hkp_lt,
                               by rw [hci1]; exact bb_ws1_skip hrem_lt, huc_ok', hm2⟩
                          · c0_hsteps
                            exact hJbr (ucnt', keep, ci + 1#64, true, ()) m2
                              ⟨st_r, hbt2, hcl_le, by rw [hci1]; omega, by omega, huc', hkp_lt,
                               by rw [hci1]; exact bb_ws1_skip hrem_lt, huc_ok', hm2⟩
                        · c0_hsteps
                          exact ih1 (ucnt', keep, ci + 1#64, ()) m_u (by dsimp only; omega)
                            ⟨st_u2, hbt_u2, hcl_le, by rw [hci1]; omega, by omega, huc', hkp_lt,
                             by rw [hci1]; exact bb_ws1_skip hrem_lt, huc_ok', hm_u⟩
                      · c0_hsteps
                        exact ih1 (ucnt', keep, ci + 1#64, ()) m_u (by dsimp only; omega)
                          ⟨st_u2, hbt_u2, hcl_le, by rw [hci1]; omega, by omega, huc', hkp_lt,
                           by rw [hci1]; exact bb_ws1_skip hrem_lt, huc_ok', hm_u⟩
                  · intro Ju hJu
                    c0_hsplit
                    · have huc_lt : ucnt.toNat < 2 * s0.core.cur_vars := by
                        have h1 : ucnt.toNat < ((BitVec.ofNat 64 s0.core.cur_vars) <<<
                            (BitVec.signExtend 64 1#32)).toNat := by c0_bound
                        rwa [hnlits_eq] at h1
                      have huc1 : (ucnt + 1#64).toNat = ucnt.toNat + 1 := by bv_omega
                      have huc_ws2 : ucnt.toNat < st.scratch.work_stk2.length := by
                        rw [hscl.work_stk2_len]; omega
                      c0_hsteps
                      exact hJu (ucnt + 1#64, ()) _
                        ⟨st.scratch.work_stk2.set ucnt.toNat not_uip,
                         by simp [hscl.work_stk2_len], by omega,
                         by rw [huc1]; exact bb_ws2_push huc_ws2 ⟨hnu_lt, hnu_ent⟩ huc_ok,
                         (by assumption)⟩
                    · c0_hsteps; exact hJu (ucnt, ()) mu
                        ⟨st.scratch.work_stk2, hscl.work_stk2_len, huc_le, huc_ok, hmu'⟩
      · c0_hsteps; exact hJbr (ucnt, keep, ci, false, ()) m1
          ⟨st, hbt, hcl_le, hkp_le, hci_le, huc_le, hkp_lt, hrem_lt, huc_ok, hm1⟩
    · c0_hsteps; exact hJbr (ucnt, keep, ci, false, ()) m1
        ⟨st, hbt, hcl_le, hkp_le, hci_le, huc_le, hkp_lt, hrem_lt, huc_ok, hm1⟩
  · c0_hsteps; exact hJbr (ucnt, keep, ci, false, ()) m1
      ⟨st, hbt, hcl_le, hkp_le, hci_le, huc_le, hkp_lt, hrem_lt, huc_ok, hm1⟩

end LeanQbe.T.Examples.Kissat.Proof.Backbone
