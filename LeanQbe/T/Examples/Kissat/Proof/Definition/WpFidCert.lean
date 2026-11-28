/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Src.Definition
public import LeanQbe.T.Examples.Kissat.Proof.Definition.WpFidCert0

/-!
# Fid `full_bve_certify_unit_fid` Phase 2, Tail & Main WP (`Proof.Definition.WpFidCert`)

Proves `full_bve_certify_unit_fid_wp : Γ.Has "full_bve_certify_unit_fid" fidBveCertifyUnitSpec`
on flat `CanonicalEnv` using `WpFidCert0` helpers and `Kitten.Spec` (`full_m6_max_v`,
`full_k6_init`, `full_k6_add_clause`, `full_k6_solve`).
Zero legacy `Full*` imports; zero `@[expose]` on theorems/lemmas/sections.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Definition

open Std Std.Sat Std.ExtHashMap Kraken.Bedrock2.Test
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Src.Definition
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Definition.Spec
open LeanQbe.T.Examples.Kissat.Proof.Kitten
open LeanQbe.T.Examples.Kissat.Proof.Kitten.Spec

open scoped FullArenaTactics FidK6cTactics

public section

/-! ## 1. Kitten Bridge, Layout, & State Update Lemmas -/

theorem fid_cert_assump_nil (L : K6Layout) (scr : List (BitVec 32))
    (h : (k6StateOfScratch L scr).nassump = 0#32) :
    k6AssumpLitsS L scr = [] := by
  simp [k6AssumpLitsS, k6AssumpLits, h]

theorem fid_cert_unitsCnf_nil (β : Nat → Bool) :
    Std.Sat.CNF.Sat β (unitsCnf []) :=
  (sat_unitsCnf_iff β []).mpr (fun _ h => by cases h)

theorem fid_cert_gu_lengths {c : FullCfg} {s : FullState} {gu : List (BitVec 32)}
    (hl : s.LengthsOk c) (hgu : gu.length = 64) :
    (FidCertGu s gu).LengthsOk c :=
  ⟨hl.core_ok,
   { hl.scratch_ok with
     glue_used_len := hgu }⟩

theorem fid_cert_p6work_lengths {c : FullCfg} {s : FullState}
    {tmp wsort tmk gu scr : List (BitVec 32)}
    (hl : s.LengthsOk c) (htp : tmp.length = c.max_vars)
    (hws : wsort.length = 2 * c.max_vars) (htm : tmk.length = 2 * c.max_vars)
    (hgu : gu.length = 64) (hscr : scr.length = c.scratch_cap) :
    (FidP6Work (FidCertGu s gu) tmp wsort tmk scr).LengthsOk c :=
  ⟨{ hl.core_ok with tmp_len_arr := htp },
   { hl.scratch_ok with
     wsort_len := hws,
     tarjan_mark_len := htm,
     glue_used_len := hgu,
     scratch_buf_len := hscr }⟩

theorem fid_cert_maxv_props {cap : Nat} (hlt : cap < dimacsBound)
    (hne : BitVec.truncate 32 (BitVec.ofNat 64 (k6MaxV cap)) ≠ 0#32)
    (hk6 : ¬ ((1280#32 : BitVec 32) +
      (BitVec.truncate 32 (BitVec.ofNat 64 (k6MaxV cap)) <<< 1) < 4192#32)) :
    k6MinScr ≤ cap ∧
    (BitVec.truncate 32 (BitVec.ofNat 64 (k6MaxV cap))).toNat = k6MaxV cap ∧
    512 ≤ k6MaxV cap ∧ k6MaxV cap ≤ 8192 ∧
    4192 ≤ (k6LayoutOfCap cap (by
      by_cases hge : k6MinScr ≤ cap
      · exact hge
      · exfalso
        have hz : k6MaxV cap = 0 := by
          unfold k6MaxV; rw [ite_eq_left (Nat.lt_of_not_ge hge)]
        apply hne; simp [hz]) hlt).k6Base := by
  have hge : k6MinScr ≤ cap := by
    by_cases h : k6MinScr ≤ cap
    · exact h
    · exfalso
      have hz : k6MaxV cap = 0 := by
        unfold k6MaxV; rw [ite_eq_left (Nat.lt_of_not_ge h)]
      apply hne; simp [hz]
  let L := k6LayoutOfCap cap hge hlt
  have hmaxV := L.hmaxV
  have hLmv : L.maxV = k6MaxV cap := rfl
  rw [hLmv] at hmaxV
  have htr : (BitVec.truncate 32 (BitVec.ofNat 64 (k6MaxV cap))).toNat = k6MaxV cap := by
    rw [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : k6MaxV cap < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : k6MaxV cap < 2 ^ 32)]
  have hbase : 4192 ≤ L.k6Base := by
    have hLbase : L.k6Base = 1280 + 2 * k6MaxV cap := rfl
    have hlt32 : (1280#32 +
        (BitVec.truncate 32 (BitVec.ofNat 64 (k6MaxV cap)) <<< 1)).toNat =
        1280 + 2 * k6MaxV cap := by
      bv_omega
    have hk6' : ¬ (1280#32 +
        (BitVec.truncate 32 (BitVec.ofNat 64 (k6MaxV cap)) <<< 1)).toNat < 4192 := by
      intro hlt; apply hk6; exact hlt
    rw [hlt32] at hk6'
    rw [hLbase]; omega
  exact ⟨hge, htr, hmaxV.1, hmaxV.2, hbase⟩

/-! ## 2. Phase 2 Large Clause Loop (`@L1068`) -/

@[expose] def fidCertPhase2LargeExpr (c : FullCfg) (nv unit v24 w sz : BitVec 32)
    (all_ok : Bool) (L868 : Cont [Ty.bool, Ty.bool, i32, i32]) :
    Expr Val Cont [Ty.bool] :=
  Expr.group (fun L1068 : Tup Cont [[i32, i32]] =>
    Blocks.cons (fun p43 : Tup Val [i32, i32] =>
      let u_cnt := p43.fst; let k := p43.snd.fst
      Expr.let_ (Op.mk (OpCode.cmp .ult i32 .bool rfl) (Arg.var k, Arg.var sz, ())) fun p44 =>
      Expr.jnz (Arg.var p44.fst)
        (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var w, ())) fun p45 =>
         Expr.let_ (Op.mk (OpCode.add i64) (Arg.var p45.fst, Arg.imm 3, ())) fun p46 =>
         Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var k, ())) fun p47 =>
         Expr.let_ (Op.mk (OpCode.add i64) (Arg.var p46.fst, Arg.var p47.fst, ())) fun p48 =>
         Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p48.fst, Arg.imm 4, ())) fun p49 =>
         Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pArena, Arg.var p49.fst, ())) fun p50 =>
         Expr.load i32 (Arg.var p50.fst) fun lit_k =>
         Expr.group (fun _ : Tup Cont [[Ty.bool, Ty.bool, i32]] =>
           Blocks.cons (fun pl : Tup Val [Ty.bool, Ty.bool, i32] =>
             Expr.let_ (Op.mk (OpCode.add i32) (Arg.var k, Arg.imm 1, ())) fun k1 =>
             Expr.jump L1068.fst (Arg.var pl.snd.snd.fst, Arg.var k1.fst, ()))
           Blocks.nil)
         fun Js_5 =>
         Expr.let_ (Op.mk (OpCode.cmp .ne i32 .bool rfl) (Arg.var lit_k, Arg.var unit, ()))
           fun pn =>
         Expr.jnz (Arg.var pn.fst)
           (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var lit_k, ())) fun pa1 =>
            Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pVals, Arg.var pa1.fst, ())) fun pa2 =>
            Expr.load i8 (Arg.var pa2.fst) fun kv =>
            Expr.let_ (Op.mk (OpCode.trunc 32 8) (Arg.imm (t := i32) 0, ())) fun pz1 =>
            Expr.let_ (Op.mk (OpCode.sext 8 32) (Arg.var kv, ())) fun pz2 =>
            Expr.let_ (Op.mk (OpCode.sext 8 32) (Arg.var pz1.fst, ())) fun pz3 =>
            Expr.let_ (Op.mk (OpCode.cmp .sgt i32 .bool rfl) (Arg.var pz2.fst, Arg.var pz3.fst, ()))
              fun p_sgt =>
            Expr.jnz (Arg.var p_sgt.fst)
              (Expr.jump L868 (Arg.imm all_ok, Arg.imm true, Arg.var u_cnt, Arg.var k, ()))
              (Expr.group (fun _ : Tup Cont [[Ty.bool, i32]] =>
                 Blocks.cons (fun pl6 : Tup Val [Ty.bool, i32] =>
                   Expr.jump Js_5.fst
                     (Arg.var pl6.fst, Arg.imm (t := Ty.bool) false, Arg.var pl6.snd.fst, ()))
                 Blocks.nil)
               fun Js_6 =>
               Expr.let_ (Op.mk (OpCode.trunc 32 8) (Arg.imm (t := i32) 0, ())) fun q1 =>
               Expr.let_ (Op.mk (OpCode.sext 8 32) (Arg.var kv, ())) fun q2 =>
               Expr.let_ (Op.mk (OpCode.sext 8 32) (Arg.var q1.fst, ())) fun q3 =>
               Expr.let_ (Op.mk (OpCode.cmp .eq i32 .bool rfl) (Arg.var q2.fst, Arg.var q3.fst, ()))
                 fun p_eq0 =>
               Expr.jnz (Arg.var p_eq0.fst)
                 (Expr.let_ (Op.mk (OpCode.lshr i32) (Arg.var lit_k, Arg.imm 1, ())) fun lv =>
                  Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var lv.fst, ())) fun pt1 =>
                  Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var pt1.fst, Arg.imm 4, ())) fun pt2 =>
                  Expr.let_ (Op.mk (OpCode.add i64)
                    (Arg.var c.pTarjanMark, Arg.var pt2.fst, ())) fun pt3 =>
                  Expr.load i32 (Arg.var pt3.fst) fun tmkv =>
                  Expr.let_ (Op.mk (OpCode.cmp .eq i32 .bool rfl)
                    (Arg.var tmkv, Arg.imm 0, ())) fun p_tz =>
                  Expr.jnz (Arg.var p_tz.fst)
                    (Expr.jump L868
                      (Arg.imm false, Arg.imm false, Arg.var u_cnt, Arg.var k, ()))
                    (Expr.let_ (Op.mk (OpCode.cmp .ugt i32 .bool rfl)
                       (Arg.var tmkv, Arg.var nv, ())) fun p_tov =>
                     Expr.jnz (Arg.var p_tov.fst)
                       (Expr.jump L868
                         (Arg.imm false, Arg.imm false, Arg.var u_cnt, Arg.var k, ()))
                       (Expr.let_ (Op.mk (OpCode.cmp .uge i32 .bool rfl)
                          (Arg.var u_cnt, Arg.var v24, ())) fun p_uov =>
                        Expr.jnz (Arg.var p_uov.fst)
                          (Expr.jump L868
                            (Arg.imm false, Arg.imm false, Arg.var u_cnt, Arg.var k, ()))
                          (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var u_cnt, ())) fun pu1 =>
                           Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var pu1.fst, Arg.imm 4, ()))
                             fun pu2 =>
                           Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pTmp, Arg.var pu2.fst, ()))
                             fun pu3 =>
                           Expr.let_ (Op.mk (OpCode.sub i32) (Arg.var tmkv, Arg.imm 1, ()))
                             fun pk1 =>
                           Expr.let_ (Op.mk (OpCode.shl i32) (Arg.var pk1.fst, Arg.imm 1, ()))
                             fun pk2 =>
                           Expr.let_ (Op.mk (OpCode.and i32) (Arg.var lit_k, Arg.imm 1, ()))
                             fun pk3 =>
                           Expr.let_ (Op.mk (OpCode.or i32) (Arg.var pk2.fst, Arg.var pk3.fst, ()))
                             fun pk4 =>
                           Expr.store (t := i32) (Arg.var pk4.fst) (Arg.var pu3.fst)
                             (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var u_cnt, Arg.imm 1, ()))
                                fun u1 =>
                              Expr.jump Js_6.fst (Arg.imm all_ok, Arg.var u1.fst, ()))))))
                 (Expr.jump Js_6.fst (Arg.imm all_ok, Arg.var u_cnt, ()))))
           (Expr.jump Js_5.fst (Arg.imm all_ok, Arg.imm false, Arg.var u_cnt, ())))
        (Expr.jump L868 (Arg.imm all_ok, Arg.imm false, Arg.var u_cnt, Arg.var k, ())))
      Blocks.nil)
    fun L1068 => Expr.jump L1068.fst (Arg.imm 0, Arg.imm 0, ())

theorem fid_cert_phase2_large_wp {Γ : Env} {Q : Post [Ty.bool]} {X : XPost}
    {L868 : Cont [Ty.bool, Ty.bool, i32, i32]}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s0 : FullState}
    {R : Mem 64 → Prop} {m : Mem 64}
    {tmp wsort tmk gu scr : List (BitVec 32)} {nv unit v24 w sz : BitVec 32}
    {all_ok : Bool}
    (hinv : FullDenseInvW c F0 F_cur s0)
    (htp : tmp.length = c.max_vars) (_hws : wsort.length = 2 * c.max_vars)
    (htm : tmk.length = 2 * c.max_vars) (_hscr : scr.length = c.scratch_cap)
    (hall : all_ok = true) (hv24 : v24.toNat ≤ c.max_vars) (hnv_cv : nv.toNat ≤ s0.core.cur_vars)
    (hr : w.toNat ∈ fullArenaClauseRefs s0) (hgarb : fullArenaClauseGarb s0 w.toNat = false)
    (hsz : sz.toNat = fullArenaClauseSize s0 w.toNat)
    (htreg : FidK6cTmkReg nv.toNat s0.core.cur_vars wsort tmk)
    (hm : (FullMem c (FidP6Work (FidCertGu s0 gu) tmp wsort tmk scr) ⋆ R) m)
    (hL868 : ∀ (ab' sat' : Bool) (u' k' : BitVec 32) (tmp' : List (BitVec 32)) (m' : Mem 64),
      tmp'.length = c.max_vars →
      (ab' = true → sat' = false →
        u'.toNat ≤ tmp'.length ∧ u'.toNat ≤ v24.toNat ∧ u'.toNat ≤ sz.toNat ∧
        (∀ i < u'.toNat, (tmp'[i]?.getD 0#32).toNat < 2 * nv.toNat) ∧
        (∀ q < sz.toNat,
          let ol := (s0.core.arena[w.toNat + 3 + q]?.getD 0#32).toNat
          ol = unit.toNat ∨ s0.core.vals[ol]?.getD 0#8 = 255#8 ∨
            ∃ j < u'.toNat, FidCertLitMap nv.toNat wsort (tmp'[j]?.getD 0#32).toNat ol)) →
      (FullMem c (FidP6Work (FidCertGu s0 gu) tmp' wsort tmk scr) ⋆ R) m' →
      L868 (ab', sat', u', k', ()) m') :
    wp Γ Q X (fidCertPhase2LargeExpr c nv unit v24 w sz all_ok L868) m := by
  subst hall
  have hwf := hinv.2.1.arena.refs_wf w.toNat hr
  have hlits_lt := hinv.2.1.arena.lits_lt w.toNat hr hgarb
  have hal_le : s0.core.arena_len ≤ c.arena_cap := hinv.1.core_ok.arena_len_le
  have har_len : s0.core.arena.length = c.arena_cap := hinv.1.core_ok.arena_len_arr
  have har_lt : c.arena_cap < 2 * dimacsBound := c.harena
  have hmax_lt : c.max_vars < 2 * dimacsBound := c.hmaxv
  have hcv_le : s0.core.cur_vars ≤ c.max_vars := hinv.1.core_ok.cur_vars_le
  have hsz_end : w.toNat + 3 + sz.toNat ≤ s0.core.arena.length := by
    rw [hsz]; dsimp only [fullArenaClauseSize] at *; omega
  have hsz_bd : sz.toNat ≤ c.arena_cap := by omega
  have hw_lt28 : w.toNat < 2 ^ 30 := by unfold dimacsBound at har_lt; omega
  refine wp_loop_group (ts := [i32, i32])
    (fun rem pl m1 => ∃ tmp1 : List (BitVec 32),
      let u1 := pl.fst; let k1 := pl.snd.fst
      k1.toNat ≤ sz.toNat ∧ u1.toNat ≤ k1.toNat ∧ u1.toNat ≤ v24.toNat ∧
      u1.toNat ≤ c.max_vars ∧
      rem = sz.toNat - k1.toNat ∧ tmp1.length = c.max_vars ∧
      (∀ i < u1.toNat, (tmp1[i]?.getD 0#32).toNat < 2 * nv.toNat) ∧
      (∀ q < k1.toNat,
        let ol := (s0.core.arena[w.toNat + 3 + q]?.getD 0#32).toNat
        ol = unit.toNat ∨ s0.core.vals[ol]?.getD 0#8 = 255#8 ∨
          ∃ j < u1.toNat, FidCertLitMap nv.toNat wsort (tmp1[j]?.getD 0#32).toNat ol) ∧
      (FullMem c (FidP6Work (FidCertGu s0 gu) tmp1 wsort tmk scr) ⋆ R) m1)
    ?_ ?_
  · intro J n ⟨u1, k1, ⟨⟩⟩ m1 hcont
      ⟨tmp1, hk_le, hu_le, hu_v24, hu_mv, hn, htp1, hu_bd, hcov, hm1⟩
    dsimp only at hk_le hu_le hu_v24 hu_mv hn hcov
    dsimp only [Blocks.get, Member.here]
    c0_hsteps_nogrp
    · have hk_lt : k1.toNat < sz.toNat := by bv_omega
      have hk1_toNat : (k1 + 1#32).toNat = k1.toNat + 1 :=
        fid_k6c_add1_toNat hk_lt (by unfold dimacsBound at har_lt; omega)
      have ha_idx : (BitVec.setWidth 64 w + 3#64 + BitVec.setWidth 64 k1).toNat =
          w.toNat + 3 + k1.toNat := by
        rw [BitVec.toNat_add, BitVec.toNat_add, fid_zext32_toNat, fid_zext32_toNat]
        have : (3#64 : BitVec 64).toNat = 3 := rfl
        rw [this]; unfold dimacsBound at har_lt
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      have ha_mod : (w.toNat + BitVec.toNat (3 : BitVec 64) + k1.toNat) % 2 ^ 64 =
          (BitVec.setWidth 64 w + 3#64 + BitVec.setWidth 64 k1).toNat := by
        rw [ha_idx, show (BitVec.toNat (3 : BitVec 64)) = 3 from rfl]
        unfold dimacsBound at har_lt; rw [Nat.mod_eq_of_lt (by omega)]
      have ha_lt : (BitVec.setWidth 64 w + 3#64 + BitVec.setWidth 64 k1).toNat <
          s0.core.arena.length := by
        rw [ha_idx]; omega
      have hdrop_len : sz.toNat ≤ (s0.core.arena.drop (w.toNat + 3)).length := by
        rw [List.length_drop]; omega
      have hsz_core : sz.toNat = fullArenaClauseSizeCore s0.core w.toNat := hsz
      let lit_k := s0.core.arena[(BitVec.setWidth 64 w + 3#64 + BitVec.setWidth 64 k1).toNat]
      have hlit_mem : lit_k.toNat ∈ fullArenaClauseLits s0 w.toNat := by
        dsimp only [fullArenaClauseLits, fullArenaClauseLitsCore]
        refine List.mem_map.mpr ⟨lit_k, List.mem_iff_getElem.mpr ⟨k1.toNat, ?_, ?_⟩, rfl⟩
        · rw [List.length_take_of_le (by rw [← hsz_core]; exact hdrop_len), ← hsz_core]; exact hk_lt
        · simp [List.getElem_take, List.getElem_drop, lit_k, ha_idx]
      have hlit_lt : lit_k.toNat < 2 * s0.core.cur_vars := hlits_lt lit_k.toNat hlit_mem
      have hlit_get : s0.core.arena[w.toNat + 3 + k1.toNat]?.getD 0#32 = lit_k := by
        dsimp only [lit_k]
        rw [List.getElem?_eq_getElem (by rw [← ha_idx]; exact ha_lt), Option.getD_some]
        congr 1; exact ha_idx.symm
      c0_hsteps_nogrp
      apply wp_unroll_group; intro Js_5 hJs_5
      have hJ5 : ∀ (sat_o : Bool) (u' : BitVec 32) (tmp' : List (BitVec 32)) (m' : Mem 64),
          tmp'.length = c.max_vars → u'.toNat ≤ k1.toNat + 1 → u'.toNat ≤ v24.toNat →
          u'.toNat ≤ c.max_vars →
          (∀ i < u'.toNat, (tmp'[i]?.getD 0#32).toNat < 2 * nv.toNat) →
          (∀ q < k1.toNat + 1,
            let ol := (s0.core.arena[w.toNat + 3 + q]?.getD 0#32).toNat
            ol = unit.toNat ∨ s0.core.vals[ol]?.getD 0#8 = 255#8 ∨
              ∃ j < u'.toNat, FidCertLitMap nv.toNat wsort (tmp'[j]?.getD 0#32).toNat ol) →
          (FullMem c (FidP6Work (FidCertGu s0 gu) tmp' wsort tmk scr) ⋆ R) m' →
          Js_5 (true, sat_o, u', ()) m' := by
        intro sat_o u' tmp' m' htp' hu' huv' humv' hub' hcov' hm'
        apply hJs_5; try dsimp only [Blocks.get, Member.here]
        c0_hsteps
        exact hcont (sz.toNat - (k1 + 1#32).toNat) (u', k1 + 1#32, ()) m'
          (by dsimp only at *; rw [hk1_toNat, hn]; omega)
          ⟨tmp', by dsimp only; rw [hk1_toNat]; omega,
           by dsimp only; rw [hk1_toNat]; exact hu', huv', humv', rfl, htp', hub',
           by simpa [hk1_toNat] using hcov', hm'⟩
      clear hJs_5
      c0_hsteps_nogrp
      · have hvals_lt : (BitVec.setWidth 64 lit_k).toNat < s0.core.vals.length := by
          rw [fid_zext32_toNat]; have := hinv.1.core_ok.vals_len; omega
        have hval_get : s0.core.vals[(BitVec.setWidth 64 lit_k).toNat] =
            s0.core.vals[lit_k.toNat]?.getD 0#8 := by
          have hget := List.getElem?_eq_getElem (l := s0.core.vals) (i := lit_k.toNat)
            (by have := hinv.1.core_ok.vals_len; omega)
          simp only [fid_zext32_toNat, hget, Option.getD_some]
        have hdom : s0.core.vals[(BitVec.setWidth 64 lit_k).toNat] = 0#8 ∨
            s0.core.vals[(BitVec.setWidth 64 lit_k).toNat] = 1#8 ∨
            s0.core.vals[(BitVec.setWidth 64 lit_k).toNat] = 255#8 := by
          rw [hval_get]; exact hinv.2.1.vals_domain lit_k.toNat hlit_lt
        c0_hsteps_nogrp
        · exact hL868 true true u1 k1 tmp1 m1 htp1
            (fun _ hs => False.elim (Bool.false_ne_true hs.symm)) hm1
        · have hkv_ngt := hc
          apply wp_unroll_group; intro Js_6 hJs_6
          have hJ6 : ∀ (u' : BitVec 32) (tmp' : List (BitVec 32)) (m' : Mem 64),
              tmp'.length = c.max_vars → u'.toNat ≤ k1.toNat + 1 → u'.toNat ≤ v24.toNat →
              u'.toNat ≤ c.max_vars →
              (∀ i < u'.toNat, (tmp'[i]?.getD 0#32).toNat < 2 * nv.toNat) →
              (∀ q < k1.toNat + 1,
                let ol := (s0.core.arena[w.toNat + 3 + q]?.getD 0#32).toNat
                ol = unit.toNat ∨ s0.core.vals[ol]?.getD 0#8 = 255#8 ∨
                  ∃ j < u'.toNat, FidCertLitMap nv.toNat wsort (tmp'[j]?.getD 0#32).toNat ol) →
              (FullMem c (FidP6Work (FidCertGu s0 gu) tmp' wsort tmk scr) ⋆ R) m' →
              Js_6 (true, u', ()) m' := by
            intro u' tmp' m' htp' hu' huv' humv' hub' hcov' hm'
            apply hJs_6; try dsimp only [Blocks.get, Member.here]
            c0_hsteps; exact hJ5 false u' tmp' m' htp' hu' huv' humv' hub' hcov' hm'
          clear hJs_6
          c0_hsteps_nogrp
          · have hlv : (lit_k >>> 1).toNat = lit_k.toNat / 2 := by bv_omega
            have htmk_lt : (BitVec.setWidth 64 (lit_k >>> 1)).toNat < tmk.length := by
              rw [fid_zext32_toNat]; omega
            c0_hsteps_nogrp
            · exact hL868 false false u1 k1 tmp1 m1 htp1
                (fun ha => False.elim (Bool.false_ne_true ha)) hm1
            · exact hL868 false false u1 k1 tmp1 m1 htp1
                (fun ha => False.elim (Bool.false_ne_true ha)) hm1
            · exact hL868 false false u1 k1 tmp1 m1 htp1
                (fun ha => False.elim (Bool.false_ne_true ha)) hm1
            · rename_i htz_ne htov_ok
              have hu_lt_v24 : u1.toNat < v24.toNat := by bv_omega
              have hu1_toNat : (u1 + 1#32).toNat = u1.toNat + 1 :=
                fid_k6c_add1_toNat hu_lt_v24 (by unfold dimacsBound at hmax_lt; omega)
              have htmp_lt : (BitVec.setWidth 64 u1).toNat < tmp1.length := by
                rw [fid_zext32_toNat]; omega
              have hlit_c0 : s0.core.arena[(w.toNat + BitVec.toNat (3 : BitVec 64) +
                  k1.toNat) % 2 ^ 64] = lit_k := by
                dsimp only [lit_k]; congr 1
              simp only [hlit_c0] at htz_ne htov_ok
              let tv := tmk[(BitVec.setWidth 64 (lit_k >>> 1)).toNat]
              have htidx : (BitVec.setWidth 64 (lit_k >>> 1)).toNat = lit_k.toNat / 2 := by
                rw [fid_zext32_toNat, hlv]
              have htv_eq : tmk[lit_k.toNat / 2]?.getD 0#32 = tv := by
                dsimp only [tv]
                rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
                simp only [htidx]
              have htv_nz : tv ≠ 0#32 := fun h0 => htz_ne h0
              have htv_le : tv.toNat ≤ nv.toNat := by
                have : ¬ (nv < tv) := fun hc' => htov_ok hc'
                bv_omega
              have hmap := fid_cert_litMap_build htreg hnv_cv
                (by unfold dimacsBound at hmax_lt; omega) hlit_lt htv_nz htv_le htv_eq
              let kl := (tv - 1#32) <<< 1 ||| lit_k &&& 1#32
              c0_hsteps
              have htp' : (tmp1.set (BitVec.setWidth 64 u1).toNat kl).length = c.max_vars := by
                simp [htp1]
              refine hJ6 (u1 + 1#32) _ ‹_› htp' (by rw [hu1_toNat]; omega)
                (by rw [hu1_toNat]; omega) (by rw [hu1_toNat]; omega) ?_ ?_ ‹_›
              · intro i hi
                rw [hu1_toNat] at hi
                have hui : (BitVec.setWidth 64 u1).toNat = u1.toNat := fid_zext32_toNat u1
                rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
                · rw [List.getElem?_set_ne (by rw [hui]; omega)]
                  exact hu_bd i hi'
                · rw [show (tmp1.set (BitVec.setWidth 64 u1).toNat kl)[u1.toNat]? =
                      (tmp1.set u1.toNat kl)[u1.toNat]? by simp only [hui],
                    List.getElem?_set_self (by omega), Option.getD_some]
                  exact hmap.1
              · intro q hq
                have hui : (BitVec.setWidth 64 u1).toNat = u1.toNat := fid_zext32_toNat u1
                rcases Nat.lt_succ_iff_lt_or_eq.mp hq with hq' | rfl
                · rcases hcov q hq' with h1v | h2v | ⟨j, hj, hjm⟩
                  · exact Or.inl h1v
                  · exact Or.inr (Or.inl h2v)
                  · refine Or.inr (Or.inr ⟨j, by rw [hu1_toNat]; omega, ?_⟩)
                    rw [List.getElem?_set_ne (by rw [hui]; omega)]
                    exact hjm
                · refine Or.inr (Or.inr ⟨u1.toNat, by rw [hu1_toNat]; omega, ?_⟩)
                  rw [show (tmp1.set (BitVec.setWidth 64 u1).toNat kl)[u1.toNat]? =
                      (tmp1.set u1.toNat kl)[u1.toNat]? by simp only [hui],
                    List.getElem?_set_self (by omega), Option.getD_some]
                  rw [hlit_get]; exact hmap.2
          · have hkv_nz := hc
            have hlit_c0 : s0.core.arena[(w.toNat + BitVec.toNat (3 : BitVec 64) +
                k1.toNat) % 2 ^ 64] = lit_k := by
              dsimp only [lit_k]; congr 1
            simp only [hlit_c0] at hkv_ngt hkv_nz
            have hv_n0 : s0.core.vals[(BitVec.setWidth 64 lit_k).toNat] ≠ 0#8 := fun h => by
              simp only [fid_zext32_toNat] at h; simp [h] at hkv_nz
            have hv_n1 : s0.core.vals[(BitVec.setWidth 64 lit_k).toNat] ≠ 1#8 := fun h => by
              have hs := (fid_cert_bv8_sgt_iff hdom).mpr h
              simp only [fid_zext32_toNat] at hs
              exact absurd (hs.symm.trans hkv_ngt) Bool.false_ne_true.symm
            have hv_255 : s0.core.vals[(BitVec.setWidth 64 lit_k).toNat] = 255#8 := by
              rcases hdom with h0 | h1v | h255
              · exact absurd h0 hv_n0
              · exact absurd h1v hv_n1
              · exact h255
            have hvals255 : s0.core.vals[lit_k.toNat]?.getD 0#8 = 255#8 := by
              rw [← hval_get, hv_255]
            refine hJ6 u1 tmp1 m1 htp1 (by omega) hu_v24 hu_mv hu_bd ?_ hm1
            intro q hq
            rcases Nat.lt_succ_iff_lt_or_eq.mp hq with hq' | rfl
            · exact hcov q hq'
            · exact Or.inr (Or.inl (by rw [hlit_get]; exact hvals255))
      · have hlit_eq_raw := hc
        have hlit_eq : lit_k = unit := by
          have hlit_c0 : s0.core.arena[(w.toNat + BitVec.toNat (3 : BitVec 64) +
              k1.toNat) % 2 ^ 64] = lit_k := by
            dsimp only [lit_k]; congr 1
          rw [hlit_c0] at hlit_eq_raw; bv_omega
        refine hJ5 false u1 tmp1 m1 htp1 (by omega) hu_v24 hu_mv hu_bd ?_ hm1
        intro q hq
        rcases Nat.lt_succ_iff_lt_or_eq.mp hq with hq' | rfl
        · exact hcov q hq'
        · exact Or.inl (by rw [hlit_get, hlit_eq])
    · have hk_eq : k1.toNat = sz.toNat := by bv_omega
      exact hL868 true false u1 k1 tmp1 m1 htp1
        (fun _ _ => ⟨by omega, hu_v24, by omega, hu_bd, fun q hq =>
          hcov q (by rw [hk_eq]; exact hq)⟩)
        hm1
  · intro J hJ; c0_hsteps
    exact hJ sz.toNat _ _ ⟨tmp, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _,
      rfl, htp, fun _ hi => absurd hi (Nat.not_lt_zero _),
      fun _ hq => absurd hq (Nat.not_lt_zero _), hm⟩

/-! ## 3. Phase 2 Outer Loop (`@L441`) -/

@[expose] def fidCertPhase2Expr (c : FullCfg)
    (nv unit side_off side_cnt side_mask v24 : BitVec 32)
    (L241 : Cont [i32, Ty.bool]) : Expr Val Cont [Ty.bool] :=
  Expr.group (fun L441 : Tup Cont [[i32, Ty.bool]] =>
    Blocks.cons (fun p22 : Tup Val [i32, Ty.bool] =>
      let j := p22.fst; let all_ok := p22.snd.fst
      Expr.let_ (Op.mk (OpCode.cmp .ult i32 .bool rfl) (Arg.var j, Arg.var side_cnt, ()))
        fun p23 =>
      Expr.jnz (Arg.var p23.fst)
        (Expr.jnz (Arg.var all_ok)
          (Expr.group (fun _ : Tup Cont [[Ty.bool]] =>
             Blocks.cons (fun p : Tup Val [Ty.bool] =>
               Expr.let_ (Op.mk (OpCode.add i32) (Arg.var j, Arg.imm 1, ())) fun p24 =>
               Expr.jump L441.fst (Arg.var p24.fst, Arg.var p.fst, ()))
             Blocks.nil)
           fun Js_2 =>
           Expr.let_ (Op.mk (OpCode.lshr i32) (Arg.var j, Arg.imm 5, ())) fun p24 =>
           Expr.let_ (Op.mk (OpCode.add i32) (Arg.var side_mask, Arg.var p24.fst, ())) fun p25 =>
           Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p25.fst, ())) fun p26 =>
           Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p26.fst, Arg.imm 4, ())) fun p27 =>
           Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p27.fst, ()))
             fun p28 =>
           Expr.load i32 (Arg.var p28.fst) fun ld_8 =>
           Expr.let_ (Op.mk (OpCode.and i32) (Arg.var j, Arg.imm 31, ())) fun p29 =>
           Expr.let_ (Op.mk (OpCode.lshr i32) (Arg.var ld_8, Arg.var p29.fst, ())) fun p30 =>
           Expr.let_ (Op.mk (OpCode.and i32) (Arg.var p30.fst, Arg.imm 1, ())) fun p31 =>
           Expr.let_ (Op.mk (OpCode.cmp .ne i32 .bool rfl) (Arg.var p31.fst, Arg.imm 0, ()))
             fun p32 =>
           Expr.jnz (Arg.var p32.fst)
             (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var side_off, Arg.var j, ())) fun p33 =>
              Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p33.fst, ())) fun p34 =>
              Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p34.fst, Arg.imm 4, ())) fun p35 =>
              Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p35.fst, ()))
                fun p36 =>
              Expr.load i32 (Arg.var p36.fst) fun w =>
              Expr.group (fun _ : Tup Cont [[Ty.bool]] =>
                Blocks.cons (fun p : Tup Val [Ty.bool] => Expr.jump Js_2.fst (Arg.var p.fst, ()))
                  Blocks.nil)
              fun Js_3 =>
              Expr.let_ (Op.mk (OpCode.and i32) (Arg.var w, Arg.imm 2147483648, ())) fun p37 =>
              Expr.let_ (Op.mk (OpCode.cmp .ne i32 .bool rfl) (Arg.var p37.fst, Arg.imm 0, ()))
                fun p38 =>
              Expr.jnz (Arg.var p38.fst)
                (Expr.let_ (Op.mk (OpCode.and i32) (Arg.var w, Arg.imm 2147483647, ())) fun p39 =>
                 Expr.group (fun _ : Tup Cont [[Ty.bool]] =>
                   Blocks.cons (fun p : Tup Val [Ty.bool] =>
                     Expr.jump Js_3.fst (Arg.var p.fst, ()))
                   Blocks.nil)
                 fun Js_4 =>
                 Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p39.fst, ())) fun p40 =>
                 Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pVals, Arg.var p40.fst, ()))
                   fun p41 =>
                 Expr.load i8 (Arg.var p41.fst) fun bv =>
                 Expr.let_ (Op.mk (OpCode.trunc 32 8) (Arg.imm (t := i32) 0, ())) fun p42 =>
                 Expr.let_ (Op.mk (OpCode.sext 8 32) (Arg.var bv, ())) fun p43 =>
                 Expr.let_ (Op.mk (OpCode.sext 8 32) (Arg.var p42.fst, ())) fun p44 =>
                 Expr.let_ (Op.mk (OpCode.cmp .eq i32 .bool rfl)
                   (Arg.var p43.fst, Arg.var p44.fst, ())) fun p45 =>
                 Expr.jnz (Arg.var p45.fst)
                   (Expr.let_ (Op.mk (OpCode.lshr i32) (Arg.var p39.fst, Arg.imm 1, ())) fun p46 =>
                    Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p46.fst, ())) fun p47 =>
                    Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p47.fst, Arg.imm 4, ())) fun p48 =>
                    Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pTarjanMark, Arg.var p48.fst, ()))
                      fun p49 =>
                    Expr.load i32 (Arg.var p49.fst) fun tmkv =>
                    Expr.let_ (Op.mk (OpCode.cmp .eq i32 .bool rfl) (Arg.var tmkv, Arg.imm 0, ()))
                      fun p50 =>
                    Expr.jnz (Arg.var p50.fst)
                      (Expr.jump L241 (Arg.var j, Arg.imm false, ()))
                      (Expr.let_ (Op.mk (OpCode.cmp .ugt i32 .bool rfl)
                         (Arg.var tmkv, Arg.var nv, ())) fun p51 =>
                       Expr.jnz (Arg.var p51.fst)
                         (Expr.jump L241 (Arg.var j, Arg.imm false, ()))
                         (Expr.let_ (Op.mk (OpCode.sext 32 64) (Arg.imm (t := i32) 0, ()))
                            fun p52 =>
                          Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p52.fst, Arg.imm 4, ()))
                            fun p53 =>
                          Expr.let_ (Op.mk (OpCode.add i64)
                            (Arg.var c.pTmp, Arg.var p53.fst, ())) fun p54 =>
                          Expr.let_ (Op.mk (OpCode.sub i32)
                            (Arg.var tmkv, Arg.imm 1, ())) fun p55 =>
                          Expr.let_ (Op.mk (OpCode.shl i32) (Arg.var p55.fst, Arg.imm 1, ()))
                            fun p56 =>
                          Expr.let_ (Op.mk (OpCode.and i32) (Arg.var p39.fst, Arg.imm 1, ()))
                            fun p57 =>
                          Expr.let_ (Op.mk (OpCode.or i32) (Arg.var p56.fst, Arg.var p57.fst, ()))
                            fun p58 =>
                          Expr.store (t := i32) (Arg.var p58.fst) (Arg.var p54.fst)
                            (Expr.call (as := [i64, i64, i32]) (bs := [Ty.bool])
                              "full_k6_add_clause"
                              (Arg.var c.hdr, Arg.var c.pTmp, Arg.imm 1, ())
                              fun ok =>
                              Expr.jnz (Arg.var ok.fst)
                                (Expr.jump Js_4.fst (Arg.var all_ok, ()))
                                (Expr.jump L241 (Arg.var j, Arg.imm false, ()))))))
                   (Expr.jump Js_4.fst (Arg.var all_ok, ())))
                (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var w, ())) fun p39 =>
                 Expr.let_ (Op.mk (OpCode.add i64) (Arg.var p39.fst, Arg.imm 2, ())) fun p40 =>
                 Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p40.fst, Arg.imm 4, ())) fun p41 =>
                 Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pArena, Arg.var p41.fst, ()))
                   fun p42 =>
                 Expr.load i32 (Arg.var p42.fst) fun sz =>
                 Expr.group (fun _ : Tup Cont [[Ty.bool, Ty.bool, i32, i32]] =>
                   Blocks.cons (fun p43 : Tup Val [Ty.bool, Ty.bool, i32, i32] =>
                     Expr.jnz (Arg.var p43.fst)
                       (Expr.group (fun _ : Tup Cont [[Ty.bool]] =>
                          Blocks.cons (fun p : Tup Val [Ty.bool] =>
                            Expr.jump Js_3.fst (Arg.var p.fst, ()))
                          Blocks.nil)
                        fun Js_5 =>
                        Expr.jnz (Arg.var p43.snd.fst)
                          (Expr.jump Js_5.fst (Arg.var p43.fst, ()))
                          (Expr.call (as := [i64, i64, i32]) (bs := [Ty.bool])
                            "full_k6_add_clause"
                            (Arg.var c.hdr, Arg.var c.pTmp, Arg.var p43.snd.snd.fst, ())
                            fun ok =>
                            Expr.jnz (Arg.var ok.fst)
                              (Expr.jump Js_5.fst (Arg.var p43.fst, ()))
                              (Expr.jump L241 (Arg.var j, Arg.imm false, ()))))
                       (Expr.jump L241 (Arg.var j, Arg.var p43.fst, ())))
                   Blocks.nil)
                 fun L868 => fidCertPhase2LargeExpr c nv unit v24 w sz all_ok L868.fst))
             (Expr.jump Js_2.fst (Arg.var all_ok, ())))
          (Expr.jump L241 (Arg.var j, Arg.var all_ok, ())))
        (Expr.jump L241 (Arg.var j, Arg.var all_ok, ())))
      Blocks.nil)
    fun L441 => Expr.jump L441.fst (Arg.imm 0, Arg.imm true, ())

theorem fid_cert_phase2_wp {Γ : Env} {Q : Post [Ty.bool]} {X : XPost}
    {L241 : Cont [i32, Ty.bool]}
    (hAdd : Γ.Has "full_k6_add_clause" step13K6AddClauseSpec)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s0 : FullState}
    {L : K6Layout} {R : Mem 64 → Prop} {m : Mem 64}
    {tmp wsort tmk gu0 scr_init : List (BitVec 32)}
    {nv unit side_off side_cnt side_mask v24 : BitVec 32}
    (hinv : FullDenseInvW c F0 F_cur s0)
    (htp : tmp.length = c.max_vars) (hws : wsort.length = 2 * c.max_vars)
    (htm : tmk.length = 2 * c.max_vars) (hgu0 : gu0.length = 64)
    (hscr0 : scr_init.length = c.scratch_cap)
    (hL_len : L.scrLen = c.scratch_cap) (hL_mv : L.maxV = k6MaxV c.scratch_cap)
    (hL_base : 4192 ≤ L.k6Base)
    (hscr_pre : ∀ i < 4192, scr_init[i]? = s0.scratch.scratch_buf[i]?)
    (h16k : 16384 ≤ c.scratch_cap) (_hunit : unit.toNat < 2 * s0.core.cur_vars)
    (hcnt : side_cnt.toNat ≤ 2001) (hoff : side_off.toNat + side_cnt.toNat ≤ 4002)
    (hmask : side_mask = 4002#32 ∨ side_mask = 4066#32)
    (hent : ∀ i < side_cnt.toNat,
      FullBveEntryOkW F_cur s0 unit.toNat (s0.scratch.scratch_buf[side_off.toNat + i]?.getD 0#32))
    (hv24 : v24.toNat ≤ c.max_vars) (hv24_le : v24.toNat ≤ 65535)
    (hnv_cv : nv.toNat ≤ s0.core.cur_vars)
    (hmax_pos : 0 < c.max_vars) (htreg : FidK6cTmkReg nv.toNat s0.core.cur_vars wsort tmk)
    (hhwm0 : K6HwmClean L (gu0[33]?.getD 0#32) (k6StateOfScratch L scr_init))
    (hkinv0 : K6Inv L (fidCertP F_cur wsort nv.toNat unit.toNat) (k6StateOfScratch L scr_init))
    (hkts0 : K6TrailSynced (k6StateOfScratch L scr_init))
    (hklvl0 : (k6StateOfScratch L scr_init).lvl = 0#32)
    (hknv0 : (k6StateOfScratch L scr_init).nv = nv)
    (hknas0 : (k6StateOfScratch L scr_init).nassump = 0#32)
    (hm : (FullMem c (FidP6Work (FidCertGu s0 gu0) tmp wsort tmk scr_init) ⋆ R) m)
    (hL241 : ∀ (j' : BitVec 32) (ab' : Bool) (tmp' gu' scr' : List (BitVec 32)) (m' : Mem 64),
      tmp'.length = c.max_vars → gu'.length = 64 → scr'.length = c.scratch_cap →
      (∀ i < L.k6Base, scr'[i]? = scr_init[i]?) →
      K6Inv L (fidCertP F_cur wsort nv.toNat unit.toNat) (k6StateOfScratch L scr') →
      (k6StateOfScratch L scr').nassump = 0#32 →
      (FullMem c (FidP6Work (FidCertGu s0 gu') tmp' wsort tmk scr') ⋆ R) m' →
      L241 (j', ab', ()) m') :
    wp Γ Q X (fidCertPhase2Expr c nv unit side_off side_cnt side_mask v24 L241) m := by
  have har_lt : c.arena_cap < 2 * dimacsBound := c.harena
  have hal_le : s0.core.arena_len ≤ c.arena_cap := hinv.1.core_ok.arena_len_le
  have har_len : s0.core.arena.length = c.arena_cap := hinv.1.core_ok.arena_len_arr
  have hmax_lt : c.max_vars < 2 * dimacsBound := c.hmaxv
  have hcv_le : s0.core.cur_vars ≤ c.max_vars := hinv.1.core_ok.cur_vars_le
  refine wp_loop_group (ts := [i32, Ty.bool])
    (fun rem pl m1 => ∃ tmp1 gu1 scr1 : List (BitVec 32),
      let j1 := pl.fst; let ab1 := pl.snd.fst
      j1.toNat ≤ side_cnt.toNat ∧ rem = side_cnt.toNat - j1.toNat ∧
      tmp1.length = c.max_vars ∧ gu1.length = 64 ∧ scr1.length = c.scratch_cap ∧
      (∀ i < L.k6Base, scr1[i]? = scr_init[i]?) ∧
      K6HwmClean L (gu1[33]?.getD 0#32) (k6StateOfScratch L scr1) ∧
      K6Inv L (fidCertP F_cur wsort nv.toNat unit.toNat) (k6StateOfScratch L scr1) ∧
      K6TrailSynced (k6StateOfScratch L scr1) ∧
      (k6StateOfScratch L scr1).lvl = 0#32 ∧ (k6StateOfScratch L scr1).nv = nv ∧
      (k6StateOfScratch L scr1).nassump = 0#32 ∧
      (FullMem c (FidP6Work (FidCertGu s0 gu1) tmp1 wsort tmk scr1) ⋆ R) m1)
    ?_ ?_
  · intro J n ⟨j1, ab1, ⟨⟩⟩ m1 hcont
      ⟨tmp1, gu1, scr1, hj_le, hn, htp1, hgu1, hscr1, hpre1, hhwm1, hk1, hts1, hlvl1, hnv1,
       hnas1, hm1⟩
    dsimp only at hj_le hn
    dsimp only [Blocks.get, Member.here]
    c0_hsteps_nogrp
    · have hj_lt : j1.toNat < side_cnt.toNat := by bv_omega
      have hj1 : (j1 + 1#32).toNat = j1.toNat + 1 := fid_k6c_add1_toNat hj_lt (by omega)
      have hab_t : ab1 = true := by assumption
      subst hab_t
      apply wp_unroll_group; intro Js_2 hJs_2
      have hJ2 : ∀ (ab' : Bool) (tmp' gu' scr' : List (BitVec 32)) (m' : Mem 64),
          tmp'.length = c.max_vars → gu'.length = 64 → scr'.length = c.scratch_cap →
          (∀ i < L.k6Base, scr'[i]? = scr_init[i]?) →
          K6HwmClean L (gu'[33]?.getD 0#32) (k6StateOfScratch L scr') →
          K6Inv L (fidCertP F_cur wsort nv.toNat unit.toNat) (k6StateOfScratch L scr') →
          K6TrailSynced (k6StateOfScratch L scr') →
          (k6StateOfScratch L scr').lvl = 0#32 → (k6StateOfScratch L scr').nv = nv →
          (k6StateOfScratch L scr').nassump = 0#32 →
          (FullMem c (FidP6Work (FidCertGu s0 gu') tmp' wsort tmk scr') ⋆ R) m' →
          Js_2 (ab', ()) m' := by
        intro ab' tmp' gu' scr' m' ht' hg' hs' hp' hw' hk' hts' hl' hnv' hna' hm'
        apply hJs_2; try dsimp only [Blocks.get, Member.here]
        c0_hsteps
        exact hcont (side_cnt.toNat - (j1 + 1#32).toNat) (j1 + 1#32, ab', ()) m'
          (by dsimp only at *; rw [hj1, hn]; omega)
          ⟨tmp', gu', scr', by dsimp only; rw [hj1]; omega, rfl, ht', hg', hs', hp',
           hw', hk', hts', hl', hnv', hna', hm'⟩
      clear hJs_2
      have hm_idx := fid_k6c_mask_widx hmask (by omega : j1.toNat < 2001)
      have hscr_m : (BitVec.setWidth 64 (side_mask + (j1 >>> 5))).toNat < scr1.length := by
        rw [fid_zext32_toNat]; omega
      c0_hsteps_nogrp
      · have hoff_idx : (BitVec.setWidth 64 (side_off + j1)).toNat =
            side_off.toNat + j1.toNat := by
          rw [fid_zext32_toNat, BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
        have hscr_o : (BitVec.setWidth 64 (side_off + j1)).toNat < scr1.length := by
          rw [hoff_idx]; omega
        c0_hsteps_nogrp
        apply wp_unroll_group; intro Js_3 hJs_3
        have hJ3 : ∀ (ab' : Bool) (tmp' gu' scr' : List (BitVec 32)) (m' : Mem 64),
            tmp'.length = c.max_vars → gu'.length = 64 → scr'.length = c.scratch_cap →
            (∀ i < L.k6Base, scr'[i]? = scr_init[i]?) →
            K6HwmClean L (gu'[33]?.getD 0#32) (k6StateOfScratch L scr') →
            K6Inv L (fidCertP F_cur wsort nv.toNat unit.toNat) (k6StateOfScratch L scr') →
            K6TrailSynced (k6StateOfScratch L scr') →
            (k6StateOfScratch L scr').lvl = 0#32 → (k6StateOfScratch L scr').nv = nv →
            (k6StateOfScratch L scr').nassump = 0#32 →
            (FullMem c (FidP6Work (FidCertGu s0 gu') tmp' wsort tmk scr') ⋆ R) m' →
            Js_3 (ab', ()) m' := by
          intro ab' tmp' gu' scr' m' ht' hg' hs' hp' hw' hk' hts' hl' hnv' hna' hm'
          apply hJs_3; try dsimp only [Blocks.get, Member.here]
          c0_hsteps; exact hJ2 ab' tmp' gu' scr' m' ht' hg' hs' hp' hw' hk' hts' hl' hnv' hna' hm'
        clear hJs_3
        let w := scr1[(BitVec.setWidth 64 (side_off + j1)).toNat]
        have hw_c0 : scr1[(side_off.toNat + BitVec.toNat j1) % 4294967296] = w := by
          dsimp only [w]; congr 1
        have hw_eq : s0.scratch.scratch_buf[side_off.toNat + j1.toNat]?.getD 0#32 = w := by
          have h0 : scr1[side_off.toNat + j1.toNat]? =
              scr_init[side_off.toNat + j1.toNat]? := hpre1 _ (by omega)
          have h1 : scr_init[side_off.toNat + j1.toNat]? =
              s0.scratch.scratch_buf[side_off.toNat + j1.toNat]? := hscr_pre _ (by omega)
          rw [← h1, ← h0]
          dsimp only [w]
          rw [← hoff_idx, List.getElem?_eq_getElem hscr_o, Option.getD_some]
        have hent_w := hent j1.toNat hj_lt
        rw [hw_eq] at hent_w
        c0_hsteps_nogrp
        · have hw_bin := hc
          rw [hw_c0] at hw_bin
          dsimp only [FullBveEntryOkW] at hent_w
          rw [ite_eq_left (by simpa using hw_bin)] at hent_w
          have hbl_lt : (w &&& 2147483647#32).toNat < 2 * s0.core.cur_vars := hent_w.1
          let bl := w &&& 2147483647#32
          have hbl_lt' : bl.toNat < 2 * s0.core.cur_vars := hbl_lt
          apply wp_unroll_group; intro Js_4 hJs_4
          have hJ4 : ∀ (ab' : Bool) (tmp' gu' scr' : List (BitVec 32)) (m' : Mem 64),
              tmp'.length = c.max_vars → gu'.length = 64 → scr'.length = c.scratch_cap →
              (∀ i < L.k6Base, scr'[i]? = scr_init[i]?) →
              K6HwmClean L (gu'[33]?.getD 0#32) (k6StateOfScratch L scr') →
              K6Inv L (fidCertP F_cur wsort nv.toNat unit.toNat) (k6StateOfScratch L scr') →
              K6TrailSynced (k6StateOfScratch L scr') →
              (k6StateOfScratch L scr').lvl = 0#32 → (k6StateOfScratch L scr').nv = nv →
              (k6StateOfScratch L scr').nassump = 0#32 →
              (FullMem c (FidP6Work (FidCertGu s0 gu') tmp' wsort tmk scr') ⋆ R) m' →
              Js_4 (ab', ()) m' := by
            intro ab' tmp' gu' scr' m' ht' hg' hs' hp' hw' hk' hts' hl' hnv' hna' hm'
            apply hJs_4; try dsimp only [Blocks.get, Member.here]
            c0_hsteps
            exact hJ3 ab' tmp' gu' scr' m' ht' hg' hs' hp' hw' hk' hts' hl' hnv' hna' hm'
          clear hJs_4
          have hvals_lt : (BitVec.setWidth 64 bl).toNat < s0.core.vals.length := by
            rw [fid_zext32_toNat]; have := hinv.1.core_ok.vals_len; omega
          c0_hsteps_nogrp
          · have hlv : (bl >>> 1).toNat = bl.toNat / 2 := by bv_omega
            have htmk_lt : (BitVec.setWidth 64 (bl >>> 1)).toNat < tmk.length := by
              rw [fid_zext32_toNat]; omega
            c0_hsteps_nogrp
            · exact hL241 j1 false tmp1 gu1 scr1 m1 htp1 hgu1 hscr1 hpre1 hk1 hnas1 hm1
            · exact hL241 j1 false tmp1 gu1 scr1 m1 htp1 hgu1 hscr1 hpre1 hk1 hnas1 hm1
            · rename_i _ htz_ne
              have htp_nz : (0 : BitVec 64).toNat < tmp1.length := by rw [htp1]; exact hmax_pos
              let tv := tmk[(BitVec.setWidth 64 (bl >>> 1)).toNat]
              have htidx : (BitVec.setWidth 64 (bl >>> 1)).toNat = bl.toNat / 2 := by
                rw [fid_zext32_toNat, hlv]
              have htv_eq : tmk[bl.toNat / 2]?.getD 0#32 = tv := by
                dsimp only [tv]
                rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
                simp only [htidx]
              have htv_nz : tv ≠ 0#32 := fun h0 => htz_ne h0
              have htv_le : tv.toNat ≤ nv.toNat := by
                have htov_ok : ¬ (nv < tv) := hc
                bv_omega
              have hmap := fid_cert_litMap_build htreg hnv_cv
                (by unfold dimacsBound at hmax_lt; omega) hbl_lt' htv_nz htv_le htv_eq
              let kl := (tv - 1#32) <<< 1 ||| bl &&& 1#32
              c0_hsteps
              let tmp2 := tmp1.set
                (BitVec.setWidth 64 (BitVec.signExtend 64 (0 : BitVec 32))).toNat kl
              have htp2 : tmp2.length = c.max_vars := by simp [tmp2, htp1]
              have hkl_bd : kl.toNat < 2 * nv.toNat := hmap.1
              have hkl_map : FidCertLitMap nv.toNat wsort kl.toNat bl.toNat := hmap.2
              have htmp2_0 : (tmp2[0]?.getD 0#32) = kl := by
                dsimp only [tmp2]
                have hz : (BitVec.setWidth 64 (BitVec.signExtend 64 (0 : BitVec 32))).toNat = 0 :=
                  rfl
                rw [show (tmp1.set
                    (BitVec.setWidth 64 (BitVec.signExtend 64 (0 : BitVec 32))).toNat kl)[0]? =
                    (tmp1.set 0 kl)[0]? by simp only [hz],
                  List.getElem?_set_self (by rw [htp1]; exact hmax_pos), Option.getD_some]
              have hsem : SemEntails (fidCertP F_cur wsort nv.toNat unit.toNat)
                  (List.map BitVec.toNat (List.take 1 tmp2)) := by
                have htk : List.take 1 tmp2 = [kl] := by
                  cases h2 : tmp2 with
                  | nil =>
                    exfalso; have : tmp2.length = 0 := by simp [h2]
                    omega
                  | cons a tl =>
                    have ha : a = kl := by have := htmp2_0; simp [h2] at this; exact this
                    simp [ha]
                rw [htk, List.map_singleton]
                exact fid_cert_semEntails_bin hent_w.2 hkl_map
              have hsplit := fid_cert_add_clause_split (R := R) ‹_›
              apply wp_call_of_spec; apply hAdd
              refine ⟨c, FidP6Work (FidCertGu s0 gu1) tmp2 wsort tmk scr1,
                fidCertP F_cur wsort nv.toNat unit.toNat, L, scr1, gu1, tmp2,
                fidCertAddClauseOuter c (FidP6Work (FidCertGu s0 gu1) tmp2 wsort tmk scr1) ⋆ R,
                rfl, fid_cert_p6work_lengths hinv.1 htp2 hws htm hgu1 hscr1, rfl, rfl,
                hL_len, hL_mv, hk1, hts1, hlvl1,
                by rw [htp2]; change 1 ≤ c.max_vars; exact hmax_pos,
                by decide, ?_, ?_, hhwm1, hsplit, ?_⟩
              · intro i hi
                have hi0 : i = 0 := by change i < 1 at hi; omega
                subst hi0; rw [htmp2_0, hnv1]; exact hkl_bd
              · simpa using hsem
              · intro ok scr' gu' m' _ _ _ hl' hscr_eq hgu_eq hhwm' hk' hts' hlvl' hnv' hnas'
                  _ _ _ _ hm'
                have hm_join := fid_cert_add_clause_join hm'
                have hscr'_len : scr'.length = c.scratch_cap := hl'.scratch_ok.scratch_buf_len
                have hgu'_len : gu'.length = 64 := hl'.scratch_ok.glue_used_len
                have hpre' : ∀ i < L.k6Base, scr'[i]? = scr_init[i]? := fun i hi => by
                  rw [hscr_eq i hi]; exact hpre1 i hi
                c0_hsteps_nogrp
                · exact hJ4 true tmp2 gu' scr' m' htp2 hgu'_len hscr'_len hpre' hhwm' hk' hts'
                    hlvl' (by rw [hnv', hnv1]) (by rw [hnas', hnas1]) hm_join
                · exact hL241 j1 false tmp2 gu' scr' m' htp2 hgu'_len hscr'_len hpre' hk'
                    (by rw [hnas', hnas1]) hm_join
          · exact hJ4 true tmp1 gu1 scr1 m1 htp1 hgu1 hscr1 hpre1 hhwm1 hk1 hts1 hlvl1 hnv1
              hnas1 hm1
        · have hw_nbin := hc
          rw [hw_c0] at hw_nbin
          dsimp only [FullBveEntryOkW] at hent_w
          rw [ite_eq_right (by simpa using hw_nbin)] at hent_w
          have hwf := hinv.2.1.arena.refs_wf w.toNat hent_w.1
          have har_idx : (BitVec.setWidth 64 w + 2#64).toNat = w.toNat + 2 := by
            rw [BitVec.toNat_add, fid_zext32_toNat, show (2#64 : BitVec 64).toNat = 2 from rfl]
            unfold dimacsBound at har_lt; rw [Nat.mod_eq_of_lt (by omega)]
          have har2_lt : (BitVec.setWidth 64 w + 2#64).toNat < s0.core.arena.length := by
            rw [har_idx]; have := hwf.1; omega
          c0_hsteps_nogrp
          apply wp_unroll_group; intro L868 hL868_raw
          have hL868 : ∀ (ab' sat' : Bool) (u' k' : BitVec 32) (tmp' : List (BitVec 32))
              (m' : Mem 64),
              tmp'.length = c.max_vars →
              (ab' = true → sat' = false →
                u'.toNat ≤ tmp'.length ∧ u'.toNat ≤ v24.toNat ∧
                u'.toNat ≤ s0.core.arena[(BitVec.setWidth 64 w + 2#64).toNat].toNat ∧
                (∀ i < u'.toNat, (tmp'[i]?.getD 0#32).toNat < 2 * nv.toNat) ∧
                (∀ q < s0.core.arena[(BitVec.setWidth 64 w + 2#64).toNat].toNat,
                  let ol := (s0.core.arena[w.toNat + 3 + q]?.getD 0#32).toNat
                  ol = unit.toNat ∨ s0.core.vals[ol]?.getD 0#8 = 255#8 ∨
                    ∃ j < u'.toNat, FidCertLitMap nv.toNat wsort (tmp'[j]?.getD 0#32).toNat ol)) →
              (FullMem c (FidP6Work (FidCertGu s0 gu1) tmp' wsort tmk scr1) ⋆ R) m' →
              L868 (ab', sat', u', k', ()) m' := by
            intro ab' sat' u' k' tmp' m' htp' hcov' hm'
            apply hL868_raw; try dsimp only [Blocks.get, Member.here]
            c0_hsteps_nogrp
            · apply wp_unroll_group; intro Js_5 hJs_5
              have hJ5 : ∀ (ab'' : Bool) (tmp'' gu'' scr'' : List (BitVec 32)) (m'' : Mem 64),
                  tmp''.length = c.max_vars → gu''.length = 64 → scr''.length = c.scratch_cap →
                  (∀ i < L.k6Base, scr''[i]? = scr_init[i]?) →
                  K6HwmClean L (gu''[33]?.getD 0#32) (k6StateOfScratch L scr'') →
                  K6Inv L (fidCertP F_cur wsort nv.toNat unit.toNat) (k6StateOfScratch L scr'') →
                  K6TrailSynced (k6StateOfScratch L scr'') →
                  (k6StateOfScratch L scr'').lvl = 0#32 → (k6StateOfScratch L scr'').nv = nv →
                  (k6StateOfScratch L scr'').nassump = 0#32 →
                  (FullMem c (FidP6Work (FidCertGu s0 gu'') tmp'' wsort tmk scr'') ⋆ R) m'' →
                  Js_5 (ab'', ()) m'' := by
                intro ab'' tmp'' gu'' scr'' m'' ht'' hg'' hs'' hp'' hw'' hk'' hts'' hl'' hnv''
                  hna'' hm''
                apply hJs_5; try dsimp only [Blocks.get, Member.here]
                c0_hsteps
                exact hJ3 ab'' tmp'' gu'' scr'' m'' ht'' hg'' hs'' hp'' hw'' hk'' hts'' hl''
                  hnv'' hna'' hm''
              clear hJs_5
              have hab_t' : ab' = true := by assumption
              c0_hsteps_nogrp
              · exact hJ5 ab' tmp' gu1 scr1 m' htp' hgu1 hscr1 hpre1 hhwm1 hk1 hts1 hlvl1 hnv1
                  hnas1 hm'
              · have hsat_f : sat' = false := hc
                rcases hcov' hab_t' hsat_f with ⟨hu_tp, hu_v24, hu_sz, hu_bd, hcov_q⟩
                have har2_lt' : w.toNat + 2 < s0.core.arena.length := by
                  rw [← har_idx]; exact har2_lt
                have har_sz : s0.core.arena[(BitVec.setWidth 64 w + 2#64).toNat] =
                    s0.core.arena[w.toNat + 2]?.getD 0#32 := by
                  rw [List.getElem?_eq_getElem har2_lt', Option.getD_some]; congr 1
                have hsz_bd : u'.toNat < 2 ^ 28 := by omega
                have hsem : SemEntails (fidCertP F_cur wsort nv.toNat unit.toNat)
                    (List.map BitVec.toNat (List.take u'.toNat tmp')) := by
                  refine fid_cert_semEntails_large hinv hent_w.1 hent_w.2 hu_tp ?_
                  intro q hq
                  apply hcov_q q
                  dsimp only [fullArenaClauseSize, fullArenaClauseSizeCore] at hq
                  rw [har_sz]; exact hq
                have hsplit := fid_cert_add_clause_split (R := R) hm'
                apply wp_call_of_spec; apply hAdd
                refine ⟨c, FidP6Work (FidCertGu s0 gu1) tmp' wsort tmk scr1,
                  fidCertP F_cur wsort nv.toNat unit.toNat, L, scr1, gu1, tmp',
                  fidCertAddClauseOuter c (FidP6Work (FidCertGu s0 gu1) tmp' wsort tmk scr1) ⋆ R,
                  rfl, fid_cert_p6work_lengths hinv.1 htp' hws htm hgu1 hscr1, rfl, rfl,
                  hL_len, hL_mv, hk1, hts1, hlvl1, hu_tp, hsz_bd,
                  by rw [hnv1]; exact hu_bd, hsem, hhwm1, hsplit, ?_⟩
                intro ok scr' gu' m'' _ _ _ hl' hscr_eq hgu_eq hhwm' hk' hts' hlvl' hnv' hnas'
                  _ _ _ _ hm''
                have hm_join := fid_cert_add_clause_join hm''
                have hscr'_len : scr'.length = c.scratch_cap := hl'.scratch_ok.scratch_buf_len
                have hgu'_len : gu'.length = 64 := hl'.scratch_ok.glue_used_len
                have hpre' : ∀ i < L.k6Base, scr'[i]? = scr_init[i]? := fun i hi => by
                  rw [hscr_eq i hi]; exact hpre1 i hi
                c0_hsteps_nogrp
                · exact hJ5 ab' tmp' gu' scr' m'' htp' hgu'_len hscr'_len hpre' hhwm' hk' hts'
                    hlvl' (by rw [hnv', hnv1]) (by rw [hnas', hnas1]) hm_join
                · exact hL241 j1 false tmp' gu' scr' m'' htp' hgu'_len hscr'_len hpre' hk'
                    (by rw [hnas', hnas1]) hm_join
            · exact hL241 j1 ab' tmp' gu1 scr1 m' htp' hgu1 hscr1 hpre1 hk1 hnas1 hm'
          clear hL868_raw
          exact fid_cert_phase2_large_wp hinv htp1 hws htm hscr1 rfl hv24 hnv_cv hent_w.1 hent_w.2
            (by
              dsimp only [fullArenaClauseSize, fullArenaClauseSizeCore]
              rw [← har_idx, List.getElem?_eq_getElem har2_lt]; rfl)
            htreg hm1 hL868
      · exact hJ2 true tmp1 gu1 scr1 m1 htp1 hgu1 hscr1 hpre1 hhwm1 hk1 hts1 hlvl1 hnv1 hnas1 hm1
    · exact hL241 j1 ab1 tmp1 gu1 scr1 m1 htp1 hgu1 hscr1 hpre1 hk1 hnas1 hm1
    · exact hL241 j1 ab1 tmp1 gu1 scr1 m1 htp1 hgu1 hscr1 hpre1 hk1 hnas1 hm1
  · intro J hJ; c0_hsteps
    exact hJ side_cnt.toNat _ _ ⟨tmp, gu0, scr_init, Nat.zero_le _, rfl, htp, hgu0, hscr0,
      fun _ _ => rfl, hhwm0, hkinv0, hkts0, hklvl0, hknv0, hknas0, hm⟩

/-! ## 4. Solve & Clear Tail (`@L241`) & Full `full_bve_certify_unit_fid_wp` -/

@[expose] def fidCertTailExpr (c : FullCfg) (nv unit : BitVec 32) (all_ok : Bool) :
    Expr Val Cont [Ty.bool] :=
  fidCertTmkClearExpr c nv
    (Expr.jnz (Arg.imm all_ok)
      (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.imm (t := i32) 1000000, ())) fun p25 =>
       Expr.call (as := [i64, i64]) (bs := [i64]) "full_k6_solve"
         (Arg.var c.hdr, Arg.var p25.fst, ())
         fun r =>
         Expr.let_ (Op.mk (OpCode.cmp .ne i64 .bool rfl) (Arg.var r.fst, Arg.imm 20, ()))
           fun p27 =>
         Expr.jnz (Arg.var p27.fst)
           (Expr.ret (Arg.imm (t := Ty.bool) false, ()))
           (fidCertUnitCommitExpr c unit))
      (Expr.ret (Arg.imm (t := Ty.bool) false, ())))

theorem fid_cert_tail_wp {Γ : Env} {Q : Post [Ty.bool]} {X : XPost}
    (hSolve : Γ.Has "full_k6_solve" step13K6SolveSpec)
    (hAssign : Γ.Has "full_assign_lvl" fullAssignLvlSpec)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s0 : FullState}
    {L : K6Layout} {R : Mem 64 → Prop} {m : Mem 64}
    {tmp wsort tmk gu scr : List (BitVec 32)} {nv unit : BitVec 32} {all_ok : Bool}
    (hinv : FullDenseInvW c F0 F_cur s0)
    (htp : tmp.length = c.max_vars) (hws : wsort.length = 2 * c.max_vars)
    (htm : tmk.length = 2 * c.max_vars) (hgu : gu.length = 64) (hscr : scr.length = c.scratch_cap)
    (hL_len : L.scrLen = c.scratch_cap) (hL_mv : L.maxV = k6MaxV c.scratch_cap)
    (hL_base : 4192 ≤ L.k6Base)
    (hscr_pre : ∀ i < 4192, scr[i]? = s0.scratch.scratch_buf[i]?)
    (hunit : unit.toNat < 2 * s0.core.cur_vars) (hnv_cv : nv.toNat ≤ s0.core.cur_vars)
    (htreg : FidK6cTmkReg nv.toNat s0.core.cur_vars wsort tmk)
    (hkinv : K6Inv L (fidCertP F_cur wsort nv.toNat unit.toNat) (k6StateOfScratch L scr))
    (hknas : (k6StateOfScratch L scr).nassump = 0#32)
    (hm : (FullMem c (FidP6Work (FidCertGu s0 gu) tmp wsort tmk scr) ⋆ R) m)
    (hQ : ∀ (ok : Bool) (s' : FullState) (m' : Mem 64),
      FullDenseInvW c F0 F_cur s' → TmkZero s' →
      s'.core.cur_vars = s0.core.cur_vars → s'.core.arena = s0.core.arena →
      s'.core.arena_len = s0.core.arena_len → s'.core.fuel.toNat ≤ s0.core.fuel.toNat →
      (∀ i < 4192, s'.scratch.scratch_buf[i]? = s0.scratch.scratch_buf[i]?) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m') :
    wp Γ Q X (fidCertTailExpr c nv unit all_ok) m := by
  dsimp only [fidCertTailExpr]
  refine fid_cert_tmk_clear_wp hinv hws htm hnv_cv htreg hm ?_
  intro tmk' m_clr htm' htmk0 hm_clr
  let s_clr := FidP6Work (FidCertGu s0 gu) tmp wsort tmk' scr
  have hinv_clr : FullDenseInvW c F0 F_cur s_clr :=
    fid_cert_denseInvW_gu hinv htp hws htm' hgu hscr
  have hltmk0 : TmkZero s_clr := htmk0
  have hpre_clr : ∀ i < 4192, s_clr.scratch.scratch_buf[i]? = s0.scratch.scratch_buf[i]? :=
    hscr_pre
  cases all_ok with
  | false =>
    c0_hsteps
    exact hQ false s_clr m_clr hinv_clr hltmk0 rfl rfl rfl (Nat.le_refl _) hpre_clr hm_clr
  | true =>
    c0_hsteps_nogrp
    · apply wp_call_of_spec; apply hSolve
      refine ⟨c, s_clr, fidCertP F_cur wsort nv.toNat unit.toNat, L, R,
        rfl, hinv_clr.1, hL_len, hL_mv, hkinv, hm_clr, ?_⟩
      intro r fuel' scr' m' _ _ _ hl' hfuel hscr_eq _ _ _ _ _ hassump _ _ hunsat hm'
      c0_hsteps_nogrp
      · have hne20 : r ≠ 20#64 := by bv_omega
        let s_ret := { s_clr with
          core := { s_clr.core with fuel := fuel' }
          scratch := { s_clr.scratch with scratch_buf := scr' } }
        have hinv_ret : FullDenseInvW c F0 F_cur s_ret :=
          m8_fullDenseInvW_fuel
            (fid_cert_denseInvW_gu hinv htp hws htm' hgu hl'.scratch_ok.scratch_buf_len) fuel'
        have hpre_ret : ∀ i < 4192, s_ret.scratch.scratch_buf[i]? = s0.scratch.scratch_buf[i]? :=
          fun i hi => by
            dsimp only [s_ret]; rw [hscr_eq i (by omega)]; exact hscr_pre i hi
        exact hQ false s_ret m' hinv_ret hltmk0 rfl rfl rfl hfuel hpre_ret hm'
      · have heq20 : r = 20#64 := by bv_omega
        have hass_nil : k6AssumpLitsS L scr' = [] := by
          rw [hassump]; exact fid_cert_assump_nil L scr hknas
        have hP_unsat : ∀ β, ¬ fidCertP F_cur wsort nv.toNat unit.toNat β := fun β hP => by
          have hbad := hunsat heq20 β hP
          rw [hass_nil] at hbad
          exact hbad (fid_cert_unitsCnf_nil β)
        have hent_u := fid_cert_P_unsat_entails_unit hP_unsat
        let s_sol := { s_clr with
          core := { s_clr.core with fuel := fuel' }
          scratch := { s_clr.scratch with scratch_buf := scr' } }
        have hinv_sol : FullDenseInvW c F0 F_cur s_sol :=
          m8_fullDenseInvW_fuel
            (fid_cert_denseInvW_gu hinv htp hws htm' hgu hl'.scratch_ok.scratch_buf_len) fuel'
        have hpre_sol : ∀ i < 4192, s_sol.scratch.scratch_buf[i]? = s0.scratch.scratch_buf[i]? :=
          fun i hi => by
            dsimp only [s_sol]; rw [hscr_eq i (by omega)]; exact hscr_pre i hi
        exact fid_cert_unit_commit_wp (s0 := s0) hAssign hinv_sol hltmk0 hunit rfl rfl rfl
          hfuel hpre_sol hent_u hm' hQ
    · exact Bool.noConfusion hc

theorem full_bve_certify_unit_fid_wp (Γ : Env)
    (hMaxV : Γ.Has "full_m6_max_v" m6MaxVSpec)
    (hInit : Γ.Has "full_k6_init" step13K6InitSpec)
    (hAdd : Γ.Has "full_k6_add_clause" step13K6AddClauseSpec)
    (hSolve : Γ.Has "full_k6_solve" step13K6SolveSpec)
    (hAssign : Γ.Has "full_assign_lvl" fullAssignLvlSpec) :
    ∀ a m Q X, fidBveCertifyUnitSpec a m Q X →
      Func.wp Γ full_bve_certify_unit_fid_body a m Q X := by
  rintro ⟨h, _v, unit, side_off, side_cnt, side_mask, ⟨⟩⟩ m Q X hsp
  rcases fidBveCertifyUnitSpec_elim hsp with
    ⟨c, F0, F_cur, s0, R, rfl, hinv, htmk0, h16k, hunit, hcnt, hoff, hmask, hent, hm, hQ⟩
  have hmax_lt : c.max_vars < 2 * dimacsBound := c.hmaxv
  have hscr_lt : c.scratch_cap < dimacsBound := c.hscr
  have htp0 := hinv.1.core_ok.tmp_len_arr
  have hws0 := hinv.1.scratch_ok.wsort_len
  have htm0 := hinv.1.scratch_ok.tarjan_mark_len
  have hgu0 := hinv.1.scratch_ok.glue_used_len
  have hscr0 := hinv.1.scratch_ok.scratch_buf_len
  unfold Func.wp full_bve_certify_unit_fid_body
  c0_hsteps_nogrp
  apply wp_call_of_spec; apply hMaxV
  dsimp only [m6MaxVSpec, vals, Arg.val]
  have hcap64 : (BitVec.ofNat 64 c.scratch_cap).toNat = c.scratch_cap := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold dimacsBound at hscr_lt; omega)]
  rw [hcap64]
  let mv_s : BitVec 32 := BitVec.truncate 32 (BitVec.ofNat 64 (k6MaxV c.scratch_cap))
  c0_hsteps_nogrp
  refine wp_join_state (ts := [i32]) (fun v24 => (v24, ()))
    (fun v24 m' => v24.toNat ≤ c.max_vars ∧ v24.toNat ≤ 65535 ∧ m' = m) ?_ ?_
  · intro _ v24 m_j ⟨hv24, hv24_le, hm_j⟩
    subst hm_j
    dsimp only [Blocks.get, Member.here]
    apply wp_unroll_group; intro L25 hL25_raw
    have hL25 : ∀ (nv' j' : BitVec 32) (ok' ab' : Bool)
        (tmp' wsort' tmk' : List (BitVec 32)) (m' : Mem 64),
        tmp'.length = c.max_vars → wsort'.length = 2 * c.max_vars →
        tmk'.length = 2 * c.max_vars →
        nv'.toNat ≤ mv_s.toNat → nv'.toNat ≤ s0.core.cur_vars →
        FidK6cTmkReg nv'.toNat s0.core.cur_vars wsort' tmk' →
        (ok' = true → (cnfOfClauses F_cur).EntailsClause (cnfClause [unit.toNat])) →
        (FullMem c (FidP6Work s0 tmp' wsort' tmk' s0.scratch.scratch_buf) ⋆ R) m' →
        L25 (nv', ok', ab', j', ()) m' := by
      intro nv' j' ok' ab' tmp' wsort' tmk' m' htp' hws' htm' hnv_mv hnv_cv htreg' hent_u hm'
      apply hL25_raw; try dsimp only [Blocks.get, Member.here]
      c0_hsteps_nogrp
      · have hok_t : ok' = true := by assumption
        have hinv_w := fid_k6c_fullDenseInvW_work hinv htp' hws' htm' hscr0
        refine fid_cert_tmk_clear_wp hinv_w hws' htm' hnv_cv htreg' hm' ?_
        intro tmk'' m'' htm'' htmk0'' hm''
        have hinv_clr := fid_k6c_fullDenseInvW_work hinv htp' hws' htm'' hscr0
        exact fid_cert_unit_commit_wp (s0 := s0) hAssign hinv_clr htmk0'' hunit rfl rfl rfl
          (Nat.le_refl _) (fun _ _ => rfl) (hent_u hok_t) hm'' hQ
      · apply wp_unroll_group; intro Js_abort hJs_abort
        have hAbort : ∀ (tmk1 : List (BitVec 32)) (m1 : Mem 64),
            tmk1.length = 2 * c.max_vars →
            FidK6cTmkReg nv'.toNat s0.core.cur_vars wsort' tmk1 →
            (FullMem c (FidP6Work s0 tmp' wsort' tmk1 s0.scratch.scratch_buf) ⋆ R) m1 →
            Js_abort () m1 := by
          intro tmk1 m1 htm1 htreg1 hm1
          apply hJs_abort; try dsimp only [Blocks.get, Member.here]
          have hinv_w := fid_k6c_fullDenseInvW_work hinv htp' hws' htm1 hscr0
          refine fid_cert_tmk_clear_wp hinv_w hws' htm1 hnv_cv htreg1 hm1 ?_
          intro tmk'' m'' htm'' htmk0'' hm''
          c0_hsteps
          let s_ab := FidP6Work s0 tmp' wsort' tmk'' s0.scratch.scratch_buf
          have hinv_ab := fid_k6c_fullDenseInvW_work hinv htp' hws' htm'' hscr0
          exact hQ false s_ab m'' hinv_ab htmk0'' rfl rfl rfl (Nat.le_refl _) (fun _ _ => rfl)
            hm''
        clear hJs_abort
        c0_hsteps_nogrp
        · exact hAbort tmk' m' htm' htreg' hm'
        · exact hAbort tmk' m' htm' htreg' hm'
        · exact hAbort tmk' m' htm' htreg' hm'
        · exact hAbort tmk' m' htm' htreg' hm'
        · rename_i h_mv_ne
          have hmv_ne : mv_s ≠ 0#32 := h_mv_ne
          have hk6_nlt : ¬ ((1280#32 : BitVec 32) + (mv_s <<< 1) < 4192#32) := hc
          rcases fid_cert_maxv_props hscr_lt hmv_ne hk6_nlt with
            ⟨hge, hmv_nat, _, _, hk6_base⟩
          let L := k6LayoutOfCap c.scratch_cap hge hscr_lt
          have hL_len : L.scrLen = c.scratch_cap := k6LayoutOfCap_scrLen hge hscr_lt
          have hL_mv : L.maxV = k6MaxV c.scratch_cap := rfl
          have hL_base : 4192 ≤ L.k6Base := hk6_base
          have hgu33 : (33#64 : BitVec 64).toNat <
              (FidP6Work s0 tmp' wsort' tmk' s0.scratch.scratch_buf).scratch.glue_used.length := by
            dsimp only [FidP6Work]; rw [show (33#64 : BitVec 64).toNat = 33 from rfl, hgu0]; decide
          c0_hsteps_nogrp
          let gu_set := s0.scratch.glue_used.set 33 4294967295#32
          have hgu_set_len : gu_set.length = 64 := by simp [gu_set, hgu0]
          have hgu_set_33 : gu_set[33]?.getD 0#32 = 4294967295#32 := by
            simp [gu_set, hgu0]
          let s_pre := FidP6Work (FidCertGu s0 gu_set) tmp' wsort' tmk' s0.scratch.scratch_buf
          apply wp_call_of_spec; apply hInit
          refine ⟨c, s_pre, R, rfl,
            fid_cert_p6work_lengths hinv.1 htp' hws' htm' hgu_set_len hscr0, ‹_›, ?_, ?_⟩
          · intro hbad; exfalso
            rcases hbad with hbad | hbad
            · omega
            · dsimp only [vals, Arg.val] at hbad
              rw [← hmv_nat] at hbad
              exact absurd hbad (Nat.not_lt.mpr hnv_mv)
          · intro _ _
            refine ⟨L, hL_len, hL_mv, Or.inl hgu_set_33, ?_⟩
            intro scr_init gu_init m_init _ _ hl_init hscr_init _ _ _ hhwm_init hkinv_init
              hts_init hnv_init _ hlvl_init _ _ _ _ hnas_init _ _ _ hm_init
            have hscr_i_len : scr_init.length = c.scratch_cap :=
              hl_init.scratch_ok.scratch_buf_len
            have hgu_i_len : gu_init.length = 64 := hl_init.scratch_ok.glue_used_len
            c0_hsteps_nogrp
            apply wp_unroll_group; intro L241 hL241_raw
            have hL241 : ∀ (j' : BitVec 32) (ab' : Bool) (tmp'' gu'' scr'' : List (BitVec 32))
                (m'' : Mem 64),
                tmp''.length = c.max_vars → gu''.length = 64 → scr''.length = c.scratch_cap →
                (∀ i < L.k6Base, scr''[i]? = scr_init[i]?) →
                K6Inv L (fidCertP F_cur wsort' nv'.toNat unit.toNat)
                  (k6StateOfScratch L scr'') →
                (k6StateOfScratch L scr'').nassump = 0#32 →
                (FullMem c (FidP6Work (FidCertGu s0 gu'') tmp'' wsort' tmk' scr'') ⋆ R) m'' →
                L241 (j', ab', ()) m'' := by
              intro j' ab' tmp'' gu'' scr'' m'' ht'' hg'' hs'' hp'' hk'' hna'' hm''
              apply hL241_raw; try dsimp only [Blocks.get, Member.here]
              c0_hsteps_nogrp
              have hscr_pre' : ∀ i < 4192, scr''[i]? = s0.scratch.scratch_buf[i]? :=
                fun i hi => by rw [hp'' i (by omega), hscr_init i (by omega)]
              exact fid_cert_tail_wp (all_ok := ab') hSolve hAssign hinv ht'' hws' htm' hg'' hs''
                hL_len hL_mv hL_base hscr_pre' hunit hnv_cv htreg' hk'' hna'' hm'' hQ
            clear hL241_raw
            have hmax_pos : 0 < c.max_vars := by
              have := hinv.1.core_ok.cur_vars_le; omega
            exact fid_cert_phase2_wp hAdd hinv htp' hws' htm' hgu_i_len hscr_i_len
              hL_len hL_mv hL_base (fun i hi => hscr_init i (by omega))
              h16k hunit hcnt hoff hmask hent hv24 hv24_le hnv_cv hmax_pos htreg' hhwm_init
              (hkinv_init (fidCertP F_cur wsort' nv'.toNat unit.toNat)) hts_init hlvl_init
              hnv_init hnas_init hm_init hL241
    clear hL25_raw
    exact fid_cert_phase1_wp (v24 := v24) hinv hscr0 h16k hunit hcnt hoff hmask hent htmk0 hm hL25
  · intro J33 hJ33
    c0_hsplit
    · have hmv_lt : c.max_vars < 65535 := by
        have hc' : c.max_vars % 2 ^ 64 < 65535 := by assumption
        have := c.hmaxv; rw [show dimacsBound = 2 ^ 28 from rfl] at this
        rwa [Nat.mod_eq_of_lt (by omega)] at hc'
      c0_hsteps!
      have h64 : c.max_vars % 2 ^ 64 = c.max_vars :=
        Nat.mod_eq_of_lt (by unfold dimacsBound at hmax_lt; omega)
      have h32 : c.max_vars % 2 ^ 32 = c.max_vars := by omega
      have htr : (BitVec.truncate 32 (BitVec.ofNat 64 c.max_vars)).toNat = c.max_vars := by
        rw [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ofNat, h64, h32]
      exact hJ33 (BitVec.truncate 32 (BitVec.ofNat 64 c.max_vars)) m
        ⟨by rw [htr]; exact Nat.le_refl _, by rw [htr]; omega, rfl⟩
    · have hmv_ge : 65535 ≤ c.max_vars := by
        have hc' : ¬ (c.max_vars % 2 ^ 64 < 65535) := by assumption
        have := c.hmaxv; rw [show dimacsBound = 2 ^ 28 from rfl] at this
        rw [Nat.mod_eq_of_lt (by omega)] at hc'; omega
      c0_hsteps!
      exact hJ33 65535#32 m ⟨hmv_ge, by decide, rfl⟩

end

end LeanQbe.T.Examples.Kissat.Proof.Definition
