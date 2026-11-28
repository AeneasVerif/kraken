/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Learn.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Learn.WpOneLitHelpers
public import LeanQbe.T.Examples.Kissat.Src.Learn
import LeanQbe.T.Examples.Kissat.Proof.Learn.Helpers
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Binary-Conflict Branch for `full_one_lit_confl` (`Proof.Learn.WpOneLitBin`)

Proves `oneLit_bin_branch_wp` directly on `Src.Learn.full_one_lit_confl_body` when
`s.core.confl_type = 1#64`, preserving binary `jumpreasons` (`jr_ol`) via `s13_bin_resolve` (`0`
legacy imports, `0` `@[expose]` on theorems/sections, `<= 100` cols, every decl `<= 450` lines).
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Learn

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0HeadStep LeanQbe.T.C0Step LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Src.Learn
open LeanQbe.T.Examples.Kissat.Proof.Learn.Helpers
open Kraken.Bedrock2.Test

open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.Proof.Learn.Helpers

private theorem oneLit_bin_assign_wp {Γ : Env} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {cut1 clvl jlvl : Nat} {s s1 s2 : FullState}
    {forced other : BitVec 32} {jlvlv nlvl : BitVec 64}
    {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost} {m2 : Mem 64}
    (hAss : ∀ args m Q X, fullAssignLvlSpec args m Q X →
      Γ "full_assign_lvl" [i64, i32, i32, i32] [] args m Q X)
    (hobt : OneLitBtInv c F0 F_cur s s1 cut1 clvl)
    (hjv_eq : jlvlv.toNat = jlvl) (hj_lt32 : jlvl < 2 ^ 32)
    (hjlvl_le : jlvl ≤ nlvl.toNat) (hnlvl_lt : nlvl.toNat < clvl)
    (hforced_lt : forced.toNat < 2 * s1.core.cur_vars)
    (hother_lt : other.toNat < 2 * s1.core.cur_vars)
    (hforced_lvl : (s1.core.lvl[forced.toNat / 2]?.getD 0#32).toNat = clvl)
    (hother_lvl : (s1.core.lvl[other.toNat / 2]?.getD 0#32).toNat = jlvl)
    (hother_f : s1.core.vals[other.toNat]?.getD 0#8 = 0xFF#8)
    (hent_fo : (cnfOfClauses F_cur).EntailsClause (cnfClause [forced.toNat, other.toNat]))
    (hs2_len : s2.LengthsOk c) (hs2_cl : s2.core.cur_level = nlvl.toNat)
    (hs2_fu : s2.core.fuel = s1.core.fuel) (hs2_ws2 : s2.scratch.work_stk2 = s1.scratch.work_stk2)
    (hs2_ll : s2.scratch.last_learned = s1.scratch.last_learned)
    (hs2_el : s2.scratch.extend_len = s1.scratch.extend_len)
    (hs2_dm : s2.core.dense_mode = 0#64) (hs2_pr : s2.core.probing = s1.core.probing)
    (hs2_cv : s2.core.cur_vars = s1.core.cur_vars)
    (hs2_mk : s2.core.mrk = s1.core.mrk) (hs2_lm : s2.core.lit_mark = s1.core.lit_mark)
    (hs2_ar : s2.core.arena = s1.core.arena) (hs2_al : s2.core.arena_len = s1.core.arena_len)
    (hs2_vals : ∀ l < 2 * s1.core.cur_vars, s2.core.vals[l]?.getD 0#8 =
      if (s1.core.lvl[l / 2]?.getD 0#32).toNat ≤ nlvl.toNat then s1.core.vals[l]?.getD 0#8 else 0#8)
    (hs2_lvl : ∀ i < s1.core.trail_end, let v := (s1.core.trl[i]?.getD 0#32).toNat / 2
      s2.core.lvl[v]?.getD 0#32 =
        if (s1.core.lvl[v]?.getD 0#32).toNat ≤ nlvl.toNat then s1.core.lvl[v]?.getD 0#32 else 0#32)
    (hw2 : FullWitnessInv c F0 F_cur s2.core) (hm2 : (FullMem c s2 ⋆ R) m2)
    (hQ : OneLitPost c F0 F_cur s R Q) :
    wp Γ Q X
      (Expr.let_ { sig := [i32, i32], code := OpCode.and i32,
                   args := (Arg.var other, Arg.imm 2147483647#32, ()) } fun p26 =>
       Expr.let_ { sig := [i32, i32], code := OpCode.or i32,
                   args := (Arg.var p26.fst, Arg.imm 2147483648#32, ()) } fun p27 =>
       Expr.group (sig := [[i32]]) (fun _Jol => Blocks.cons (fun (jr_ol : Tup Val [i32]) =>
         Expr.let_ { sig := [i64], code := OpCode.trunc 64 32, args := (Arg.var jlvlv, ()) }
           fun p28 =>
         Expr.call (as := [i64, i32, i32, i32]) "full_assign_lvl"
           (Arg.var c.hdr, Arg.var forced, Arg.var jr_ol.fst, Arg.var p28.fst, ())
           fun (_ : Tup Val []) => Expr.ret (Arg.imm 1#64, ())) Blocks.nil) fun Jol =>
       Expr.let_ { sig := [i64, i64], code := OpCode.cmp CmpOp.ugt i64 Ty.bool rfl,
                   args := (Arg.var jlvlv, Arg.imm 0#64, ()) } fun p29 =>
       Expr.jnz (Arg.var p29.fst)
         (Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                      args := (Arg.var c.hdr, Arg.imm 88#64, ()) } fun p30 =>
          Expr.load i64 (Arg.var p30.fst) fun rsns_ol =>
          Expr.let_ { sig := [i32, i32], code := OpCode.lshr i32,
                      args := (Arg.var other, Arg.imm 1#32, ()) } fun p31 =>
          Expr.let_ { sig := [i32], code := OpCode.zext 32 64, args := (Arg.var p31.fst, ()) }
            fun p32 =>
          Expr.let_ { sig := [i64, i64], code := OpCode.mul i64,
                      args := (Arg.var p32.fst, Arg.imm 4#64, ()) } fun p33 =>
          Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                      args := (Arg.var rsns_ol, Arg.var p33.fst, ()) } fun p34 =>
          Expr.load i32 (Arg.var p34.fst) fun nr_ol =>
          Expr.group (sig := [[i32]]) (fun _Js1 => Blocks.cons (fun (p : Tup Val [i32]) =>
            Expr.jump Jol.fst (Arg.var p.fst, ())) Blocks.nil) fun Js =>
          Expr.let_ { sig := [i32, i32], code := OpCode.cmp CmpOp.ne i32 Ty.bool rfl,
                      args := (Arg.var nr_ol, Arg.imm 4294967295#32, ()) } fun p35 =>
          Expr.jnz (Arg.var p35.fst)
            (Expr.let_ { sig := [i32, i32], code := OpCode.and i32,
                         args := (Arg.var nr_ol, Arg.imm 2147483648#32, ()) } fun p36 =>
             Expr.let_ { sig := [i32, i32], code := OpCode.cmp CmpOp.ne i32 Ty.bool rfl,
                         args := (Arg.var p36.fst, Arg.imm 0#32, ()) } fun p37 =>
             Expr.jnz (Arg.var p37.fst)
               (Expr.jump Js.fst (Arg.var nr_ol, ()))
               (Expr.jump Js.fst (Arg.var p27.fst, ())))
            (Expr.jump Js.fst (Arg.var p27.fst, ())))
         (Expr.jump Jol.fst (Arg.var p27.fst, ()))) m2 := by
  have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
  have hcv2 := hs2_len.core_ok.cur_vars_le
  have h2cv2 : 2 * s2.core.cur_vars < 2 ^ 31 - 1 := by omega
  have hother_lt2 : other.toNat < 2 * s2.core.cur_vars := hs2_cv ▸ hother_lt
  have hforced_lt2 : forced.toNat < 2 * s2.core.cur_vars := hs2_cv ▸ hforced_lt
  have hf_un : s2.core.vals[forced.toNat]?.getD 0#8 = 0#8 := by
    rw [hs2_vals _ hforced_lt, ite_eq_right (by omega)]
  have hother_f2 : s2.core.vals[other.toNat]?.getD 0#8 = 0xFF#8 := by
    rw [hs2_vals _ hother_lt, ite_eq_left (by omega)]; exact hother_f
  have hother_lvl2 : (s2.core.lvl[other.toNat / 2]?.getD 0#32).toNat = jlvl := by
    obtain ⟨m0, hm0, hm0_eq⟩ := (hobt.hw1.vals_false_iff other.toNat hother_lt).mp hother_f
    have hlv := hs2_lvl m0 hm0; dsimp only at hlv; rw [hm0_eq, fullInv_var_xor1] at hlv
    rw [hother_lvl, ite_eq_left hjlvl_le] at hlv
    have : (s2.core.lvl[other.toNat / 2]?.getD 0#32).toNat =
        (s1.core.lvl[other.toNat / 2]?.getD 0#32).toNat := congrArg BitVec.toNat hlv
    omega
  have htr_eq : jlvlv.setWidth 32 = BitVec.ofNat 32 jlvl := BitVec.eq_of_toNat_eq (by
    rw [BitVec.toNat_setWidth, hjv_eq, Proof.Spec.bv32_ofNat_toNat hj_lt32,
      Nat.mod_eq_of_lt hj_lt32])
  have hj_z : (jlvlv.setWidth 32 = 0#32) ↔ jlvl = 0 := by
    rw [htr_eq]; constructor
    · intro h; simpa [Proof.Spec.bv32_ofNat_toNat hj_lt32] using congrArg BitVec.toNat h
    · intro h; simp [h]
  have hng_guard : ¬ (s2.core.cur_vars ≤ forced.toNat / 2 ∨
      c.max_vars ≤ s2.core.trail_end ∨ s2.core.vals[forced.toNat]?.getD 0#8 ≠ 0#8) := by
    have hte2_lt := hw2.trail_end_lt_of_unassigned hforced_lt2 hf_un
    exact not_or.mpr ⟨Nat.not_le.mpr (Nat.div_lt_of_lt_mul hforced_lt2), not_or.mpr
      ⟨Nat.not_le.mpr (by omega), fun h => h hf_un⟩⟩
  let jr0 := (other &&& 0x7FFFFFFF#32) ||| 0x80000000#32
  have hbin_p := bin_rsn_mask_props (l := other) (by omega)
  c0_to_group
  refine wp_join_group (ts := [i32]) (fun (jr, ()) m_j =>
    m_j = m2 ∧ jr ≠ 0xFFFFFFFF#32 ∧ (jr &&& 0x80000000#32) ≠ 0#32 ∧
    let ot := (jr &&& 0x7FFFFFFF#32).toNat
    ot < 2 * s2.core.cur_vars ∧ (cnfOfClauses F_cur).EntailsClause (cnfClause [forced.toNat, ot]) ∧
    s2.core.vals[ot]?.getD 0#8 = 0xFF#8 ∧ (s2.core.lvl[ot / 2]?.getD 0#32).toNat ≤ jlvl) ?_ ?_
  · rintro _ ⟨jr, ⟨⟩⟩ m_j ⟨rfl, hjr_ne, hjr_hi, hot_lt, hent_j, hot_f, hot_lvl⟩
    c0_hsteps_nogrp
    c0_call hAss
    refine ⟨c, s2, R, rfl, hs2_len, hm2, ?_⟩
    simp only [hng_guard, ↓reduceIte]
    intro fl' unass3 ph' m3 hfl3 hph3 hm3
    let v := forced.toNat / 2
    let rsn' := if jlvlv.setWidth 32 = 0#32 then 0xFFFFFFFF#32 else jr
    let s3 : FullState :=
      { s2 with
        core :=
          { s2.core with
            vals := (s2.core.vals.set forced.toNat 1#8).set (forced.toNat ^^^ 1) 0xFF#8
            flags := fl', lvl := s2.core.lvl.set v (jlvlv.setWidth 32)
            rsns := s2.core.rsns.set v rsn', trl := s2.core.trl.set s2.core.trail_end forced
            trail_pos := s2.core.trail_pos.set v (BitVec.ofNat 32 s2.core.trail_end)
            trail_end := s2.core.trail_end + 1, unassigned := unass3
            unflushed := if jlvlv.setWidth 32 = 0#32
              then s2.core.unflushed + 1#64 else s2.core.unflushed }
        scratch := { s2.scratch with phases := ph' } }
    have hsc3 : s3.scratch.LengthsOk c := { hs2_len.scratch_ok with phases_len := hph3 }
    have h_s2_false : ∃ m_ot < s2.core.trail_end,
        (s2.core.trl[m_ot]?.getD 0#32).toNat = (jr &&& 0x7FFFFFFF#32).toNat ^^^ 1 ∧
        (s2.core.lvl[(jr &&& 0x7FFFFFFF#32).toNat / 2]?.getD 0#32).toNat ≤ jlvl := by
      obtain ⟨m_ot, hm_ot, hmeq⟩ := (hw2.vals_false_iff _ hot_lt).mp hot_f
      exact ⟨m_ot, hm_ot, hmeq, hot_lvl⟩
    have hl0 : jlvl = 0 → (cnfOfClauses F_cur).EntailsClause (cnfClause [forced.toNat]) := by
      intro hj0; subst hj0
      obtain ⟨m_ot, hm_ot, hmeq, hml0⟩ := h_s2_false
      have htr0 : (s2.core.lvl[(s2.core.trl[m_ot]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 := by
        rw [hmeq, fullInv_var_xor1]; omega
      exact entails_of_mem_or_false hent_j fun l hl => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
        exact hl.elim (fun h => h ▸ Or.inl List.mem_cons_self) fun h =>
          Or.inr (h ▸ by have hs := hw2.level0_sound m_ot hm_ot htr0; rwa [hmeq] at hs)
    have hrsn2 : 0 < jlvl → jr ≠ 0xFFFFFFFF#32 →
        if (jr &&& 0x80000000#32) ≠ 0#32 then
          let ot := (jr &&& 0x7FFFFFFF#32).toNat
          ot < 2 * s2.core.cur_vars ∧ (cnfOfClauses F_cur).EntailsClause
            (cnfClause [forced.toNat, ot]) ∧
          ∃ m < s2.core.trail_end, (s2.core.trl[m]?.getD 0#32).toNat = ot ^^^ 1 ∧
            (s2.core.lvl[ot / 2]?.getD 0#32).toNat ≤ jlvl
        else
          jr.toNat ∈ fullArenaClauseRefsCore s2.core ∧
          fullArenaClauseGarbCore s2.core jr.toNat = false ∧
          ∀ q ∈ fullArenaClauseLitsCore s2.core jr.toNat,
            q = forced.toNat ∨
            ∃ m < s2.core.trail_end, (s2.core.trl[m]?.getD 0#32).toNat = q ^^^ 1 ∧
              (s2.core.lvl[q / 2]?.getD 0#32).toNat ≤ jlvl := fun _ _ => by
      rw [ite_eq_left hjr_hi]; exact ⟨hot_lt, hent_j, h_s2_false⟩
    have hrsn_mem2 : 0 < jlvl → jr ≠ 0xFFFFFFFF#32 → (jr &&& 0x80000000#32) = 0#32 →
        forced.toNat ∈ fullArenaClauseLitsCore s2.core jr.toNat :=
      fun _ _ hlg => absurd hlg hjr_hi
    obtain ⟨hlen3_pre, hw3_pre⟩ := chronoAssign_preserves_fullWitness hw2 hs2_len hsc3 hfl3
      hforced_lt2 hf_un (hs2_cl ▸ hjlvl_le) (fun _ => hjr_ne) hl0 hrsn2 hrsn_mem2
      (unassigned' := unass3) (unflushed' := s3.core.unflushed)
    have hrsn_eq : (if jlvlv.setWidth 32 = 0#32 then 0xFFFFFFFF#32 else jr) =
        if jlvl = 0 then 0xFFFFFFFF#32 else jr := by
      by_cases hj : jlvl = 0
      · rw [ite_eq_left (hj_z.mpr hj), ite_eq_left hj]
      · rw [ite_eq_right (fun h => hj (hj_z.mp h)), ite_eq_right hj]
    have hs3_eq : { s2 with
        core := { s2.core with
          vals := (s2.core.vals.set forced.toNat 1#8).set (forced.toNat ^^^ 1) 0xFF#8
          flags := fl', lvl := s2.core.lvl.set v (BitVec.ofNat 32 jlvl)
          rsns := s2.core.rsns.set v (if jlvl = 0 then 0xFFFFFFFF#32 else jr)
          trl := s2.core.trl.set s2.core.trail_end forced
          trail_pos := s2.core.trail_pos.set v (BitVec.ofNat 32 s2.core.trail_end)
          trail_end := s2.core.trail_end + 1, unassigned := unass3, unflushed := s3.core.unflushed }
        scratch := { s2.scratch with phases := ph' } } = s3 := by
      dsimp only [s3, rsn', v]; rw [hrsn_eq, htr_eq]
    have hlen3 : s3.LengthsOk c := hs3_eq ▸ hlen3_pre
    have hw3 : FullWitnessInv c F0 F_cur s3.core :=
      congrArg FullState.core hs3_eq ▸ hw3_pre
    have hmarks3 : FullLitMarksClear c s3 :=
      ⟨fun w hw => by
        change s2.core.mrk[w]?.getD 0#8 = 0#8; rw [hs2_mk]; exact hobt.marks1.1 w hw,
       fun l hl => by
        change s2.core.lit_mark[l]?.getD 0#8 = 0#8; rw [hs2_lm]; exact hobt.marks1.2 l hl⟩
    have hrefs : fullArenaClauseRefsCore s3.core = fullArenaClauseRefsCore s1.core := by
      simp [fullArenaClauseRefsCore, s3, hs2_ar, hs2_al]
    have hnd3 : FullArenaVarsNodup s3 := fun r hr hng => by
      change r ∈ fullArenaClauseRefsCore s3.core at hr; rw [hrefs] at hr
      change ((fullArenaClauseLitsCore s3.core r).map (· / 2)).Nodup
      simp only [fullArenaClauseLitsCore, fullArenaClauseSizeCore, s3, hs2_ar]
      exact hobt.nodup1 r hr
        (by simpa [fullArenaClauseGarbCore, fullArenaHdrCore, s3, hs2_ar] using hng)
    have hext3 : FullExtScratchOk c s3 := ⟨fun i hi => by
      change _ = _ ∨ _ ∈ fullArenaClauseRefsCore s3.core
      rw [hrefs, hs2_ll]; exact hobt.ext1.1 i hi,
      by change s2.scratch.extend_len ≤ c.extend_cap; rw [hs2_el]; exact hobt.ext1.2⟩
    c0_hsteps
    exact hQ 1#64 s3 m3 hlen3 (Or.inr (Or.inl rfl)) (hs2_cv.trans hobt.cv_eq)
      (hs2_fu.trans hobt.fuel_eq) (hs2_ws2.trans hobt.ws2_eq) hs2_dm
      (hs2_pr.trans hobt.prob_eq) hmarks3 hnd3 hext3 (fun _ h => by cases h)
      (fun h => by cases h) (fun _ => ⟨hw3, by dsimp [s3]; have := hobt.cl_le; omega⟩)
      (fun h => by cases h) (fun h => by cases h)
      (oneLit_fullMem_of_eq hm3 rfl rfl)
  · intro Jol hJol
    have hjr0_ok : jr0 ≠ 0xFFFFFFFF#32 ∧ (jr0 &&& 0x80000000#32) ≠ 0#32 ∧
        (jr0 &&& 0x7FFFFFFF#32).toNat < 2 * s2.core.cur_vars ∧
        (cnfOfClauses F_cur).EntailsClause
          (cnfClause [forced.toNat, (jr0 &&& 0x7FFFFFFF#32).toNat]) ∧
        s2.core.vals[(jr0 &&& 0x7FFFFFFF#32).toNat]?.getD 0#8 = 0xFF#8 ∧
        (s2.core.lvl[(jr0 &&& 0x7FFFFFFF#32).toNat / 2]?.getD 0#32).toNat ≤ jlvl := by
      refine ⟨hbin_p.1, hbin_p.2.1, ?_⟩
      rw [hbin_p.2.2]
      exact ⟨hother_lt2, hent_fo, hother_f2, Nat.le_of_eq hother_lvl2⟩
    c0_hsplit
    · have hjpos : 0 < jlvl := by
        have hlt : 0 < jlvlv.toNat := by assumption
        omega
      have hv_lt : other.toNat / 2 < c.max_vars := by omega
      have hidx_o : ((other >>> 1#32).setWidth 64).toNat = other.toNat / 2 := by
        rw [bv_c0_zext32_64]; simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
      have hbd_rsns : ((other >>> 1#32).setWidth 64).toNat < s2.core.rsns.length := by
        rw [hidx_o, hs2_len.core_ok.rsns_len]; exact hv_lt
      c0_hsteps_nogrp
      refine wp_load_of (FullArenaTactics.load_full_reason_ptr hm2) ?_
      c0_hsteps_nogrp
      refine wp_load_of (FullArenaTactics.c0_load_full_rsns hbd_rsns hm2) ?_
      let nr_ol := s2.core.rsns[((other >>> 1#32).setWidth 64).toNat]'hbd_rsns
      c0_to_group
      refine wp_join_group (ts := [i32]) (fun (jr2, ()) m_j2 =>
        m_j2 = m2 ∧ jr2 ≠ 0xFFFFFFFF#32 ∧ (jr2 &&& 0x80000000#32) ≠ 0#32 ∧
        let ot := (jr2 &&& 0x7FFFFFFF#32).toNat
        ot < 2 * s2.core.cur_vars ∧
        (cnfOfClauses F_cur).EntailsClause (cnfClause [forced.toNat, ot]) ∧
        s2.core.vals[ot]?.getD 0#8 = 0xFF#8 ∧ (s2.core.lvl[ot / 2]?.getD 0#32).toNat ≤ jlvl) ?_ ?_
      · rintro _ ⟨jr2, ⟨⟩⟩ m_j2 hok
        c0_hsteps
        exact hJol (jr2, ()) m_j2 hok
      · intro Js hJs
        c0_hsplit
        · c0_hsplit
          · have hnr_ne : nr_ol ≠ 0xFFFFFFFF#32 := by assumption
            have hnr_hi : (nr_ol &&& 0x80000000#32) ≠ 0#32 := by assumption
            obtain ⟨m_o, hm_o, hm_oeq⟩ := (hw2.vals_false_iff other.toNat hother_lt2).mp hother_f2
            have hvar_o : (s2.core.trl[m_o]?.getD 0#32).toNat / 2 = other.toNat / 2 := by
              rw [hm_oeq, fullInv_var_xor1]
            have hrsn_get : s2.core.rsns[(s2.core.trl[m_o]?.getD 0#32).toNat / 2]?.getD
                0xFFFFFFFF#32 = nr_ol := by
              rw [hvar_o, List.getElem?_eq_getElem (by rw [hs2_len.core_ok.rsns_len]; exact hv_lt),
                Option.getD_some]
              exact Option.some.inj (by
                rw [← List.getElem?_eq_getElem (by rw [hs2_len.core_ok.rsns_len]; exact hv_lt),
                    ← List.getElem?_eq_getElem hbd_rsns, hidx_o])
            have hinv_r := hw2.reason_inv m_o hm_o (by rw [hrsn_get]; exact hnr_ne)
            rw [hrsn_get, ite_eq_left (fun h => absurd h hnr_hi)] at hinv_r
            obtain ⟨hot_lt, hent_ot, m_t, hm_t, hmt_eq, hot_lv⟩ := hinv_r
            have hot_f : s2.core.vals[(nr_ol &&& 0x7FFFFFFF#32).toNat]?.getD 0#8 = 0xFF#8 :=
              (hw2.vals_false_iff _ hot_lt).mpr ⟨m_t, Nat.lt_trans hm_t hm_o, hmt_eq⟩
            have hent_neg_other : (cnfOfClauses F_cur).EntailsClause
                (cnfClause [other.toNat ^^^ 1, (nr_ol &&& 0x7FFFFFFF#32).toNat]) := by
              rwa [← hm_oeq]
            have hent_res := s13_bin_resolve hent_neg_other
              (entails_of_mem_or_false hent_fo fun l hl =>
              Or.inl (by
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hl ⊢
                rcases hl with rfl | rfl
                · exact Or.inr rfl
                · exact Or.inl rfl))
            c0_hsteps
            exact hJs (nr_ol, ()) m2 ⟨rfl, hnr_ne, hnr_hi, hot_lt, hent_res, hot_f,
              by rw [← hother_lvl2, ← hvar_o]; exact hot_lv⟩
          · c0_hsteps; exact hJs (jr0, ()) m2 ⟨rfl, hjr0_ok⟩
        · c0_hsteps; exact hJs (jr0, ()) m2 ⟨rfl, hjr0_ok⟩
    · c0_hsteps; exact hJol (jr0, ()) m2 ⟨rfl, hjr0_ok⟩

private theorem oneLit_bin_swap_if {Γ : Env} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {cut1 clvl : Nat} {s s1 : FullState} {a b la lb : BitVec 32}
    {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost} {m1 : Mem 64}
    (hBt : ∀ args m Q X, fullBacktrackSpec args m Q X →
      Γ "full_backtrack_ac_fid" [i64, i64] [] args m Q X)
    (hAss : ∀ args m Q X, fullAssignLvlSpec args m Q X →
      Γ "full_assign_lvl" [i64, i32, i32, i32] [] args m Q X)
    (hobt : OneLitBtInv c F0 F_cur s s1 cut1 clvl)
    (ha_lt : a.toNat < 2 * s.core.cur_vars) (hb_lt : b.toNat < 2 * s.core.cur_vars)
    (hla_val : la.toNat = (s.core.lvl[a.toNat / 2]?.getD 0#32).toNat)
    (hlb_val : lb.toNat = (s.core.lvl[b.toNat / 2]?.getD 0#32).toNat)
    (hmax : clvl = max la.toNat lb.toNat) (hne : la ≠ lb)
    (hfa : s.core.vals[a.toNat]?.getD 0#8 = 0xFF#8)
    (hfb : s.core.vals[b.toNat]?.getD 0#8 = 0xFF#8)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause [a.toNat, b.toNat]))
    (hm1 : (FullMem c s1 ⋆ R) m1) (hQ : OneLitPost c F0 F_cur s R Q) :
    let forced := if la > lb then a else b
    let other := if la > lb then b else a
    let jlvl : Nat := if la > lb then lb.toNat else la.toNat
    ∀ nlvl : BitVec 64,
      (0 < s1.core.cur_level → jlvl < s1.core.cur_level →
        jlvl ≤ nlvl.toNat ∧ nlvl.toNat < s1.core.cur_level) →
      wp Γ Q X
        (Expr.call (as := [i64, i64]) "full_backtrack_ac_fid"
            (Arg.var c.hdr, Arg.var nlvl, ()) fun (_ : Tup Val []) =>
          Expr.let_ { sig := [i32, i32], code := OpCode.and i32,
                      args := (Arg.var other, Arg.imm 2147483647#32, ()) } fun p26 =>
          Expr.let_ { sig := [i32, i32], code := OpCode.or i32,
                      args := (Arg.var p26.fst, Arg.imm 2147483648#32, ()) } fun p27 =>
          Expr.group (sig := [[i32]]) (fun _Jol => Blocks.cons (fun (jr_ol : Tup Val [i32]) =>
            Expr.let_ { sig := [i64], code := OpCode.trunc 64 32,
                        args := (Arg.var (BitVec.ofNat 64 jlvl), ()) } fun p28 =>
            Expr.call (as := [i64, i32, i32, i32]) "full_assign_lvl"
              (Arg.var c.hdr, Arg.var forced, Arg.var jr_ol.fst, Arg.var p28.fst, ())
              fun (_ : Tup Val []) => Expr.ret (Arg.imm 1#64, ())) Blocks.nil) fun Jol =>
          Expr.let_ { sig := [i64, i64], code := OpCode.cmp CmpOp.ugt i64 Ty.bool rfl,
                      args := (Arg.var (BitVec.ofNat 64 jlvl), Arg.imm 0#64, ()) } fun p29 =>
          Expr.jnz (Arg.var p29.fst)
            (Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                         args := (Arg.var c.hdr, Arg.imm 88#64, ()) } fun p30 =>
             Expr.load i64 (Arg.var p30.fst) fun rsns_ol =>
             Expr.let_ { sig := [i32, i32], code := OpCode.lshr i32,
                         args := (Arg.var other, Arg.imm 1#32, ()) } fun p31 =>
             Expr.let_ { sig := [i32], code := OpCode.zext 32 64, args := (Arg.var p31.fst, ()) }
               fun p32 =>
             Expr.let_ { sig := [i64, i64], code := OpCode.mul i64,
                         args := (Arg.var p32.fst, Arg.imm 4#64, ()) } fun p33 =>
             Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                         args := (Arg.var rsns_ol, Arg.var p33.fst, ()) } fun p34 =>
             Expr.load i32 (Arg.var p34.fst) fun nr_ol =>
             Expr.group (sig := [[i32]]) (fun _Js1 => Blocks.cons (fun (p : Tup Val [i32]) =>
               Expr.jump Jol.fst (Arg.var p.fst, ())) Blocks.nil) fun Js =>
             Expr.let_ { sig := [i32, i32], code := OpCode.cmp CmpOp.ne i32 Ty.bool rfl,
                         args := (Arg.var nr_ol, Arg.imm 4294967295#32, ()) } fun p35 =>
             Expr.jnz (Arg.var p35.fst)
               (Expr.let_ { sig := [i32, i32], code := OpCode.and i32,
                            args := (Arg.var nr_ol, Arg.imm 2147483648#32, ()) } fun p36 =>
                Expr.let_ { sig := [i32, i32], code := OpCode.cmp CmpOp.ne i32 Ty.bool rfl,
                            args := (Arg.var p36.fst, Arg.imm 0#32, ()) } fun p37 =>
                Expr.jnz (Arg.var p37.fst)
                  (Expr.jump Js.fst (Arg.var nr_ol, ()))
                  (Expr.jump Js.fst (Arg.var p27.fst, ())))
               (Expr.jump Js.fst (Arg.var p27.fst, ())))
            (Expr.jump Jol.fst (Arg.var p27.fst, ()))) m1 := by
  intro forced other jlvl nlvl hnlvl
  have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv; have hcv := hobt.len1.core_ok.cur_vars_le
  have h2cv : 2 * s.core.cur_vars < 2 ^ 31 - 1 := by have := hobt.cv_eq; omega
  have hjlt : jlvl < clvl := by
    dsimp only [jlvl]; split <;> rename_i hgt
    · have : lb.toNat < la.toNat := hgt; omega
    · have : la.toNat ≤ lb.toNat := Nat.not_lt.mp hgt
      have hneq : la.toNat ≠ lb.toNat := fun he => hne (BitVec.eq_of_toNat_eq he); omega
  obtain ⟨hjl_le_nl, hnl_lt⟩ := hnlvl (hobt.cl1_eq ▸ hobt.cl_pos) (hobt.cl1_eq ▸ hjlt)
  rw [hobt.cl1_eq] at hnl_lt
  c0_call hBt
  refine ⟨c, s1, R, rfl, hobt.len1, by
    have := hobt.hw1.cur_level_le; have := hobt.len1.core_ok.trail_end_le; omega,
    fun _ => by
      have := hobt.hw1.cur_level_le; have := hobt.len1.core_ok.trail_end_le; omega,
    hobt.hw1.trail_lits_lt, hm1, ?_⟩
  dsimp only
  intro vals2 lvl2 rsns2 trl2 tp2 te2 prop2 cl2 unass2 sc2 m2 hlen2 _ _ hcl2 hpres _ _ hvl2 _ hw2
    hm2
  have hcl2_eq : cl2 = nlvl.toNat := by rw [hcl2, hobt.cl1_eq]; omega
  have hw2' := hw2 F0 F_cur hobt.hw1.toFullOtfsWitnessInv (by rw [hobt.cl1_eq]; exact hnl_lt)
  obtain ⟨hvals2, hlvl2⟩ := hvl2 ⟨F0, F_cur, Or.inr hobt.hw1.toFullOtfsWitnessInv⟩
  have hforced_lt : forced.toNat < 2 * s1.core.cur_vars := by
    rw [hobt.cv_eq]; dsimp only [forced]; split <;> assumption
  have hother_lt : other.toNat < 2 * s1.core.cur_vars := by
    rw [hobt.cv_eq]; dsimp only [other]; split <;> assumption
  have hforced_lvl : (s1.core.lvl[forced.toNat / 2]?.getD 0#32).toNat = clvl := by
    dsimp only [forced]; split
    · have : lb.toNat < la.toNat := ‹la > lb›
      rw [hobt.lvl_keep _ ha_lt hfa (by omega), ← hla_val]; omega
    · have : la.toNat ≤ lb.toNat := Nat.not_lt.mp ‹¬ la > lb›
      rw [hobt.lvl_keep _ hb_lt hfb (by omega), ← hlb_val]; omega
  have hother_lvl : (s1.core.lvl[other.toNat / 2]?.getD 0#32).toNat = jlvl := by
    dsimp only [other, jlvl]; split
    · rw [hobt.lvl_keep _ hb_lt hfb (by rw [← hlb_val]; omega), hlb_val]
    · rw [hobt.lvl_keep _ ha_lt hfa (by rw [← hla_val]; omega), hla_val]
  have hother_f : s1.core.vals[other.toNat]?.getD 0#8 = 0xFF#8 := by
    dsimp only [other]; split
    · rw [hobt.vals_keep _ hb_lt (by rw [← hlb_val]; omega)]; exact hfb
    · rw [hobt.vals_keep _ ha_lt (by rw [← hla_val]; omega)]; exact hfa
  have hent_fo : (cnfOfClauses F_cur).EntailsClause (cnfClause [forced.toNat, other.toNat]) := by
    dsimp only [forced, other]; split
    · exact hent
    · exact entails_of_mem_or_false hent fun l hl => Or.inl (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hl ⊢
        rcases hl with rfl | rfl <;> simp)
  have hj_lt32 : jlvl < 2 ^ 32 := by
    have := fullInv_max_vars_lt32 c; have := hobt.hw1.cur_level_le
    have := hobt.len1.core_ok.trail_end_le; have := hobt.cl1_eq; omega
  exact oneLit_bin_assign_wp hAss hobt
    (Proof.Spec.bv64_ofNat_toNat (lt_trans hj_lt32 (by decide)))
    hj_lt32 hjl_le_nl hnl_lt hforced_lt hother_lt hforced_lvl hother_lvl hother_f hent_fo
    hlen2 hcl2_eq rfl hpres.2.2.1 hpres.1.1 hpres.1.2 hobt.dm0 rfl rfl rfl rfl rfl rfl
    hvals2 hlvl2 hw2' hm2 hQ

public section

/-- Binary-conflict branch of `full_one_lit_confl` when `s.core.confl_type = 1#64`. -/
theorem oneLit_bin_branch_wp (Γ : Env)
    (hDet : ∀ args m Q X, fullDetNewLevelSpec args m Q X →
      Γ "full_det_new_level" [i64, i64] [i64] args m Q X)
    (hBt : ∀ args m Q X, fullBacktrackSpec args m Q X →
      Γ "full_backtrack_ac_fid" [i64, i64] [] args m Q X)
    (hAss : ∀ args m Q X, fullAssignLvlSpec args m Q X →
      Γ "full_assign_lvl" [i64, i32, i32, i32] [] args m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {cut : Nat} {s : FullState}
    {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost} {m : Mem 64}
    (hlen : s.LengthsOk c) (hdm : s.core.dense_mode = 0#64)
    (hw : FullWitnessCutInv c F0 F_cur cut s.core) (hmarks : FullLitMarksClear c s)
    (hnd : FullArenaVarsNodup s) (hext : FullExtScratchOk c s)
    (hconfl : FullConflictOkCut F_cur cut s)
    (hbin : s.core.confl_type = 1#64) (hm : (FullMem c s ⋆ R) m)
    (hQ : OneLitPost c F0 F_cur s R Q) :
    Func.wp Γ full_one_lit_confl_body (c.hdr, ()) m Q X := by
  have hmax32 := fullInv_max_vars_lt32 c; have hcv_le := hlen.core_ok.cur_vars_le
  have hlvl_len := hlen.core_ok.lvl_len; have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
  have hcl_lt64 : s.core.cur_level < 2 ^ 64 := by
    have := hw.cur_level_le; have := hlen.core_ok.trail_end_le; omega
  have hret_bt0 {cut1 clvl : Nat} {s1 : FullState} {m1 : Mem 64}
      (hobt : OneLitBtInv c F0 F_cur s s1 cut1 clvl)
      (hm1 : (FullMem c s1 ⋆ R) m1) : Q (0#64, ()) m1 :=
    hQ 0#64 s1 m1 hobt.len1 (Or.inl rfl) hobt.cv_eq hobt.fuel_eq hobt.ws2_eq hobt.dm0 hobt.prob_eq
      hobt.marks1 hobt.nodup1 hobt.ext1 (fun _ h => by cases h) (fun h => by cases h)
      (fun h => by cases h) (fun h => by cases h)
      (fun _ => ⟨cut1, hobt.cut1_le, hobt.hw1, hobt.cl1_eq ▸ hobt.cl_pos,
        hobt.cl1_eq ▸ hobt.cl_le, hobt.confl1⟩) hm1
  have hconfl0 : FullConflictOkCut F_cur cut s := hconfl
  have hbin_cf : s.core.confl_lit0.toNat < 2 * s.core.cur_vars ∧
      s.core.confl_lit1.toNat < 2 * s.core.cur_vars ∧
      s.core.vals[s.core.confl_lit0.toNat]?.getD 0#8 = 0xFF#8 ∧
      s.core.vals[s.core.confl_lit1.toNat]?.getD 0#8 = 0xFF#8 ∧
      (cnfOfClauses F_cur).EntailsClause
        (cnfClause [s.core.confl_lit0.toNat, s.core.confl_lit1.toNat]) := by
    rcases hconfl.1 with ⟨_, h0, h1, fa, fb, he⟩ | ⟨hbad, _⟩
    · exact ⟨h0, h1, fa, fb, he⟩
    · exact absurd (hbin.symm.trans hbad) (by decide)
  obtain ⟨h0lt, h1lt, hfa, hfb, hent⟩ := hbin_cf
  dsimp only [Func.wp, full_one_lit_confl_body]
  c0_hsteps_nogrp
  c0_hsplit
  · have h0_32 : s.core.confl_lit0.toNat < 2 ^ 32 := by omega
    have h1_32 : s.core.confl_lit1.toNat < 2 ^ 32 := by omega
    let a := s.core.confl_lit0.setWidth 32; let b := s.core.confl_lit1.setWidth 32
    have ha_eq : a.toNat = s.core.confl_lit0.toNat := by
      rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt h0_32]
    have hb_eq : b.toNat = s.core.confl_lit1.toNat := by
      rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt h1_32]
    have ha_bd : (BitVec.setWidth 64 (a >>> 1)).toNat < s.core.lvl.length := by
      rw [bv_c0_zext32_64, bv32_lshr_1, hlvl_len, ha_eq]; omega
    have hb_bd : (BitVec.setWidth 64 (b >>> 1)).toNat < s.core.lvl.length := by
      rw [bv_c0_zext32_64, bv32_lshr_1, hlvl_len, hb_eq]; omega
    let la := s.core.lvl[(BitVec.setWidth 64 (a >>> 1)).toNat]'ha_bd
    let lb := s.core.lvl[(BitVec.setWidth 64 (b >>> 1)).toNat]'hb_bd
    have hla_64 : la.setWidth 64 = BitVec.ofNat 64 la.toNat := BitVec.eq_of_toNat_eq (by
      rw [BitVec.toNat_setWidth, Proof.Spec.bv64_ofNat_toNat (by omega),
        Nat.mod_eq_of_lt (by omega)])
    have hlb_64 : lb.setWidth 64 = BitVec.ofNat 64 lb.toNat := BitVec.eq_of_toNat_eq (by
      rw [BitVec.toNat_setWidth, Proof.Spec.bv64_ofNat_toNat (by omega),
        Nat.mod_eq_of_lt (by omega)])
    have hla_val : la.toNat = (s.core.lvl[a.toNat / 2]?.getD 0#32).toNat := by
      dsimp only [la]; rw [List.getElem?_eq_getElem (by rw [hlvl_len]; omega), Option.getD_some]
      have hidx : (BitVec.setWidth 64 (a >>> 1)).toNat = a.toNat / 2 := by
        rw [bv_c0_zext32_64, bv32_lshr_1]
      exact congrArg BitVec.toNat (Option.some.inj (by
        rw [← List.getElem?_eq_getElem ha_bd,
            ← List.getElem?_eq_getElem (by rw [hlvl_len]; omega), hidx]))
    have hlb_val : lb.toNat = (s.core.lvl[b.toNat / 2]?.getD 0#32).toNat := by
      dsimp only [lb]; rw [List.getElem?_eq_getElem (by rw [hlvl_len]; omega), Option.getD_some]
      have hidx : (BitVec.setWidth 64 (b >>> 1)).toNat = b.toNat / 2 := by
        rw [bv_c0_zext32_64, bv32_lshr_1]
      exact congrArg BitVec.toNat (Option.some.inj (by
        rw [← List.getElem?_eq_getElem hb_bd,
            ← List.getElem?_eq_getElem (by rw [hlvl_len]; omega), hidx]))
    have hla_le : la.toNat ≤ s.core.cur_level := by
      obtain ⟨ma, hma, hma_eq⟩ := (hw.vals_false_iff _ h0lt).mp hfa
      have h1 := hw.lvl_le ma hma; rw [hma_eq, fullInv_var_xor1, ← ha_eq] at h1; omega
    have hlb_le : lb.toNat ≤ s.core.cur_level := by
      obtain ⟨mb, hmb, hmb_eq⟩ := (hw.vals_false_iff _ h1lt).mp hfb
      have h1 := hw.lvl_le mb hmb; rw [hmb_eq, fullInv_var_xor1, ← hb_eq] at h1; omega
    c0_hsteps_nogrp
    refine wp_join_group (ts := [i64]) (fun (clvlv, ()) m0 =>
        m0 = m ∧ clvlv = BitVec.ofNat 64 (max la.toNat lb.toNat)) ?_ ?_
    · rintro _ ⟨clvlv, ⟨⟩⟩ m0 ⟨rfl, rfl⟩
      let clvl := max la.toNat lb.toNat
      have hcl_le : clvl ≤ s.core.cur_level := Nat.max_le.mpr ⟨hla_le, hlb_le⟩
      c0_hsteps_nogrp
      · have hcl0 : clvl = 0 := ofNat64_eq_zero (by omega) ‹_›
        have hl0a : (s.core.lvl[a.toNat / 2]?.getD 0#32).toNat = 0 := by omega
        have hl0b : (s.core.lvl[b.toNat / 2]?.getD 0#32).toNat = 0 := by omega
        exact hQ 20#64 s m0 hlen (Or.inr (Or.inr (Or.inr rfl))) rfl rfl rfl hdm rfl hmarks hnd
          hext (fun _ h => by cases h)
          (fun _ => ⟨unsat_of_level0_bin_conflict hw h0lt h1lt
            (ha_eq ▸ hl0a) (hb_eq ▸ hl0b) hfa hfb hent, rfl⟩)
          (fun h => by cases h) (fun h => by cases h) (fun h => by cases h) hm
      · have hcl_pos : 0 < clvl := ofNat64_pos ‹_›
        have hbt_lt : ∀ l, (s.core.confl_type = 1#64 ∧
            (l = s.core.confl_lit0.toNat ∨ l = s.core.confl_lit1.toNat)) ∨
            (s.core.confl_type ≠ 1#64 ∧ l ∈ fullArenaClauseLits s s.core.confl_ref.toNat) →
            (s.core.lvl[l / 2]?.getD 0#32).toNat ≤ clvl := fun l hl => by
          rcases hl with ⟨_, rfl | rfl⟩ | ⟨hbad, _⟩
          · rw [← ha_eq, ← hla_val]; exact Nat.le_max_left _ _
          · rw [← hb_eq, ← hlb_val]; exact Nat.le_max_right _ _
          · exact absurd hbin hbad
        refine wp_join_group (ts := []) (fun () m1 =>
            ∃ s1 cut1, OneLitBtInv c F0 F_cur s s1 cut1 clvl ∧ (FullMem c s1 ⋆ R) m1) ?_ ?_
        · rintro _ ⟨⟩ m1 ⟨s1, cut1, hobt, hm1⟩
          c0_hsteps_nogrp
          · exact hret_bt0 hobt hm1
          · have hne : la ≠ lb := ‹_›
            refine wp_join_group (ts := [i32]) (fun (fc, ()) mf =>
                mf = m1 ∧ fc = if la > lb then a else b) ?_ ?_
            · rintro _ ⟨fc, ⟨⟩⟩ mf ⟨rfl, rfl⟩
              refine wp_join_group (ts := [i32]) (fun (oc, ()) mo =>
                  mo = mf ∧ oc = if la > lb then b else a) ?_ ?_
              · rintro _ ⟨oc, ⟨⟩⟩ mo ⟨rfl, rfl⟩
                refine wp_join_group (ts := [i64]) (fun (jc, ()) mj =>
                    mj = mo ∧ jc = BitVec.ofNat 64
                      (if la > lb then lb.toNat else la.toNat)) ?_ ?_
                · rintro _ ⟨jc, ⟨⟩⟩ mj ⟨rfl, rfl⟩
                  c0_hsteps_nogrp; c0_call hDet
                  refine ⟨c, s1, R, rfl, hobt.len1, by
                    have := hobt.hw1.cur_level_le; have := hobt.len1.core_ok.trail_end_le
                    have := hobt.len1.core_ok.cur_vars_le; omega,
                    hm1, fun nlvl _ hnlvl => ?_⟩
                  have hjl_lt64 : (if la > lb then lb.toNat else la.toNat) < 2 ^ 64 := by
                    split <;> omega
                  exact oneLit_bin_swap_if hBt hAss hobt (ha_eq ▸ h0lt) (hb_eq ▸ h1lt)
                    hla_val hlb_val rfl hne (ha_eq ▸ hfa) (hb_eq ▸ hfb)
                    (ha_eq ▸ hb_eq ▸ hent) hm1 hQ nlvl
                    (by simpa only [Proof.Spec.bv64_ofNat_toNat hjl_lt64] using hnlvl)
                · intro Jj hJj; c0_hsteps
                  · have hgt : la > lb := BitVec.lt_def.mpr (by dsimp only [la, lb]; assumption)
                    exact hJj _ _ ⟨rfl, by rw [ite_eq_left hgt]; exact hlb_64⟩
                  · have hng : ¬ la > lb := fun h =>
                      (by dsimp only [la, lb]; assumption : ¬ lb.toNat < la.toNat)
                        (BitVec.lt_def.mp h)
                    exact hJj _ _ ⟨rfl, by rw [ite_eq_right hng]; exact hla_64⟩
              · intro Jo hJo; c0_hsteps
                · have hgt : la > lb := BitVec.lt_def.mpr (by dsimp only [la, lb]; assumption)
                  exact hJo _ _ ⟨rfl, by simp [hgt, b]⟩
                · have hng : ¬ la > lb := fun h =>
                    (by dsimp only [la, lb]; assumption : ¬ lb.toNat < la.toNat)
                      (BitVec.lt_def.mp h)
                  exact hJo _ _ ⟨rfl, by simp [hng, a]⟩
            · intro Jf hJf; c0_hsteps
              · have hgt : la > lb := BitVec.lt_def.mpr (by dsimp only [la, lb]; assumption)
                exact hJf _ _ ⟨rfl, by simp [hgt, a]⟩
              · have hng : ¬ la > lb := fun h =>
                  (by dsimp only [la, lb]; assumption : ¬ lb.toNat < la.toNat) (BitVec.lt_def.mp h)
                exact hJf _ _ ⟨rfl, by simp [hng, b]⟩
        · intro Jbt hJbt; c0_hsteps_nogrp
          · have hlt_cl : s.core.cur_level > clvl := by
              have hb : clvl % 2 ^ 64 < s.core.cur_level % 2 ^ 64 := ‹_›
              rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hcl_lt64] at hb; exact hb
            c0_call hBt
            refine ⟨c, s, R, rfl, hlen, hcl_lt64,
              fun _ => by have := hw.cur_level_le; have := hlen.core_ok.trail_end_le; omega,
              hw.trail_lits_lt, hm, ?_⟩
            have hcl_lt64' : clvl < 2 ^ 64 := by omega
            dsimp only
            intro vals1 lvl1 rsns1 trl1 tp1 te1 prop1 cl1 unass1 sc1 m1 hlen1 _ _ hcl1 hpres _ _
              hvl1 _ hw1 hm1
            have hcl1_eq : cl1 = clvl := by
              rw [hcl1, Proof.Spec.bv64_ofNat_toNat hcl_lt64']; omega
            obtain ⟨hvs1, hls1⟩ := hvl1 ⟨F0, F_cur, Or.inr hw.toFullOtfsWitnessInv⟩
            obtain ⟨cut1, hobt⟩ := oneLit_after_bt hlen hdm hw hmarks hnd hext hw.cut_le hconfl0
              hcl_pos hcl_le hbt_lt (Or.inr ⟨hlt_cl, hlen1, hcl1_eq,
                rfl, hpres.2.2.1, hpres.1.1, hpres.1.2, hdm, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
                rfl, rfl, rfl, rfl, rfl, rfl, rfl,
                fun l hl => by
                  have h := hvs1 l hl; rw [Proof.Spec.bv64_ofNat_toNat hcl_lt64'] at h; exact h,
                fun i hi => by
                  have h := hls1 i hi; rw [Proof.Spec.bv64_ofNat_toNat hcl_lt64'] at h; exact h,
                hw1 F0 F_cur hw.toFullOtfsWitnessInv
                  (by rw [Proof.Spec.bv64_ofNat_toNat hcl_lt64']; omega)⟩)
            exact hJbt () m1 ⟨_, cut1, hobt, hm1⟩
          · have hle_cl : s.core.cur_level ≤ clvl := by
              have hb : ¬ clvl % 2 ^ 64 < s.core.cur_level % 2 ^ 64 := ‹_›
              rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hcl_lt64] at hb; omega
            obtain ⟨cut1, hobt⟩ := oneLit_after_bt hlen hdm hw hmarks hnd hext hw.cut_le hconfl0
              hcl_pos hcl_le hbt_lt (Or.inl ⟨hle_cl, rfl⟩)
            exact hJbt () m0 ⟨s, cut1, hobt, hm⟩
    · intro Jmx hJmx
      have ha_i : s.core.confl_lit0.toNat % 2 ^ 32 / 2 = (BitVec.setWidth 64 (a >>> 1)).toNat := by
        rw [bv_c0_zext32_64, bv32_lshr_1, ha_eq, Nat.mod_eq_of_lt h0_32]
      have hb_i : s.core.confl_lit1.toNat % 2 ^ 32 / 2 = (BitVec.setWidth 64 (b >>> 1)).toNat := by
        rw [bv_c0_zext32_64, bv32_lshr_1, hb_eq, Nat.mod_eq_of_lt h1_32]
      c0_hsteps
      · have hle : lb.toNat ≤ la.toNat := by
          have hc : (s.core.lvl[s.core.confl_lit1.toNat % 2 ^ 32 / 2]'(by
              rw [hlvl_len]; omega)).toNat ≤
              (s.core.lvl[s.core.confl_lit0.toNat % 2 ^ 32 / 2]'(by
              rw [hlvl_len]; omega)).toNat := ‹_›
          simpa only [la, lb, ← ha_i, ← hb_i] using hc
        exact hJmx _ _ ⟨rfl, by rw [Nat.max_eq_left hle]; exact hla_64⟩
      · have hgt : la.toNat < lb.toNat := by
          have hc : ¬ (s.core.lvl[s.core.confl_lit1.toNat % 2 ^ 32 / 2]'(by
              rw [hlvl_len]; omega)).toNat ≤
              (s.core.lvl[s.core.confl_lit0.toNat % 2 ^ 32 / 2]'(by
              rw [hlvl_len]; omega)).toNat := ‹_›
          have h1 : la.toNat = (s.core.lvl[s.core.confl_lit0.toNat % 2 ^ 32 / 2]'(by
              rw [hlvl_len]; omega)).toNat := congrArg BitVec.toNat (Option.some.inj (by
            rw [← List.getElem?_eq_getElem ha_bd,
                ← List.getElem?_eq_getElem (by rw [hlvl_len]; omega), ha_i]))
          have h2 : lb.toNat = (s.core.lvl[s.core.confl_lit1.toNat % 2 ^ 32 / 2]'(by
              rw [hlvl_len]; omega)).toNat := congrArg BitVec.toNat (Option.some.inj (by
            rw [← List.getElem?_eq_getElem hb_bd,
                ← List.getElem?_eq_getElem (by rw [hlvl_len]; omega), hb_i]))
          omega
        exact hJmx _ _ ⟨rfl, by rw [Nat.max_eq_right (Nat.le_of_lt hgt)]; exact hlb_64⟩

end

end LeanQbe.T.Examples.Kissat.Proof.Learn
