/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Definition.WpFidExtract1

/-!
# Kissat Fidelity BVE WP Proofs — K6c Extraction Inner Loop (`Proof.Definition.WpFidExtract2`)

`CanonicalEnv`-clean inner-loop helpers for `full_k6_extract_and_solve_fid` (`0` legacy imports;
zero `@[expose]` on theorems; every decl `<= 450` LOC; `<= 100` cols):
1. `fid_k6c_bin_branch_wp`: binary entry branch (`w &&& 0x80000000 ≠ 0`).
2. `fid_k6c_large_branch_wp`: large entry branch (`scan_large` + `copy_clause`).
3. `fid_k6c_inner_loop_wp`: inner entry scan loop `@L484`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Definition

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src.Definition
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Definition.Spec
open Kraken.Bedrock2.Test

open scoped FullArenaTactics FidK6Tactics M8K6bTactics FidK6cTactics

public section

private theorem fid_k6c_tmkReg_congr {nv1 nv2 cv : Nat} {e1 e2 t1 t2 : List (BitVec 32)}
    (h : FidK6cTmkReg nv1 cv e1 t1) (hn : nv1 = nv2) (he : e1 = e2) (ht : t1 = t2) :
    FidK6cTmkReg nv2 cv e2 t2 := by subst hn he ht; exact h

abbrev fidK6cBinTmkExpr (c : FullCfg) (mv_s nv _v708 v920 : BitVec 32) (abort_in : Bool)
    (j1 : BitVec 32)
    (K284 : Cont [i32, i32, i32, i32, i32, Ty.bool, i32])
    (K921 : Cont [i32, Ty.bool])
    (nc alen n_units triv_unit : BitVec 32) : Expr Val Cont [Ty.bool] :=
  Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var v920, ())) fun p_20 =>
  Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_20.fst, Arg.imm 4, ())) fun p_21 =>
  Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pTarjanMark, Arg.var p_21.fst, ())) fun p_22 =>
  Expr.load i32 (Arg.var p_22.fst) fun ld =>
  Expr.let_ (Op.mk (OpCode.cmp .eq i32 .bool rfl) (Arg.var ld, Arg.imm 0, ())) fun p_23 =>
  Expr.jnz (Arg.var p_23.fst)
    (Expr.let_ (Op.mk (OpCode.cmp .uge i32 .bool rfl) (Arg.var nv, Arg.var mv_s, ())) fun p_24 =>
    Expr.jnz (Arg.var p_24.fst)
      (Expr.jump K284 (Arg.var nv, Arg.var nc, Arg.var alen, Arg.var n_units,
        Arg.var triv_unit, Arg.imm true, Arg.var j1, ()))
      (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var nv, ())) fun p_25 =>
      Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.hdr, Arg.imm 776, ())) fun p_26 =>
      Expr.load i64 (Arg.var p_26.fst) fun ld_1 =>
      Expr.let_ (Op.mk (OpCode.sext 32 64) (Arg.imm 1, ())) fun p_27 =>
      Expr.let_ (Op.mk (OpCode.shl i64) (Arg.var ld_1, Arg.var p_27.fst, ())) fun p_28 =>
      Expr.let_ (Op.mk (OpCode.cmp .uge i64 .bool rfl) (Arg.var p_25.fst, Arg.var p_28.fst, ()))
        fun p_29 =>
      Expr.jnz (Arg.var p_29.fst)
        (Expr.jump K284 (Arg.var nv, Arg.var nc, Arg.var alen, Arg.var n_units,
          Arg.var triv_unit, Arg.imm true, Arg.var j1, ()))
        (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var nv, ())) fun p_30 =>
        Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_30.fst, Arg.imm 4, ())) fun p_31 =>
        Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pWsort, Arg.var p_31.fst, ())) fun p_32 =>
        Expr.store (t := i32) (Arg.var v920) (Arg.var p_32.fst)
          (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var nv, Arg.imm 1, ())) fun p_33 =>
          Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var v920, ())) fun p_34 =>
          Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_34.fst, Arg.imm 4, ())) fun p_35 =>
          Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pTarjanMark, Arg.var p_35.fst, ()))
            fun p_36 =>
          Expr.store (t := i32) (Arg.var p_33.fst) (Arg.var p_36.fst)
            (Expr.jump K921 (Arg.var p_33.fst, Arg.var abort_in, ()))))))
    (Expr.jump K921 (Arg.var nv, Arg.var abort_in, ()))

abbrev fidK6cBinEmitExpr (c : FullCfg)
    (mv2 acap_s o_cl_off o_cl_meta o_cl_aux o_cl_units o_arena : BitVec 32)
    (nc alen n_units triv_unit eid j1 v708 v920 nv' : BitVec 32) (ab' : Bool)
    (K284 : Cont [i32, i32, i32, i32, i32, Ty.bool, i32])
    (K716 : Cont [i32, i32, i32, i32, Ty.bool]) : Expr Val Cont [Ty.bool] :=
  Expr.let_ (Op.mk (OpCode.cmp .uge i32 .bool rfl) (Arg.var nc, Arg.var mv2, ())) fun p_20 =>
  Expr.jnz (Arg.var p_20.fst)
    (Expr.jump K284 (Arg.var nv', Arg.var nc, Arg.var alen, Arg.var n_units,
      Arg.var triv_unit, Arg.imm true, Arg.var j1, ()))
    (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var alen, Arg.imm 1, ())) fun p_21 =>
    Expr.let_ (Op.mk (OpCode.cmp .ugt i32 .bool rfl) (Arg.var p_21.fst, Arg.var acap_s, ()))
      fun p_22 =>
    Expr.jnz (Arg.var p_22.fst)
      (Expr.jump K284 (Arg.var nv', Arg.var nc, Arg.var alen, Arg.var n_units,
        Arg.var triv_unit, Arg.imm true, Arg.var j1, ()))
      (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var o_arena, Arg.var alen, ())) fun p_23 =>
      Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p_23.fst, ())) fun p_24 =>
      Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_24.fst, Arg.imm 4, ())) fun p_25 =>
      Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p_25.fst, ()))
        fun p_26 =>
      Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var v920, ())) fun p_27 =>
      Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_27.fst, Arg.imm 4, ())) fun p_28 =>
      Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pTarjanMark, Arg.var p_28.fst, ()))
        fun p_29 =>
      Expr.load i32 (Arg.var p_29.fst) fun ld =>
      Expr.let_ (Op.mk (OpCode.sub i32) (Arg.var ld, Arg.imm 1, ())) fun p_30 =>
      Expr.let_ (Op.mk (OpCode.shl i32) (Arg.var p_30.fst, Arg.imm 1, ())) fun p_31 =>
      Expr.let_ (Op.mk (OpCode.and i32) (Arg.var v708, Arg.imm 1, ())) fun p_32 =>
      Expr.let_ (Op.mk (OpCode.or i32) (Arg.var p_31.fst, Arg.var p_32.fst, ())) fun p_33 =>
      Expr.store (t := i32) (Arg.var p_33.fst) (Arg.var p_26.fst)
        (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var o_cl_off, Arg.var nc, ())) fun p_34 =>
        Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p_34.fst, ())) fun p_35 =>
        Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_35.fst, Arg.imm 4, ())) fun p_36 =>
        Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p_36.fst, ()))
          fun p_37 =>
        Expr.store (t := i32) (Arg.var alen) (Arg.var p_37.fst)
          (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var o_cl_meta, Arg.var nc, ())) fun p_38 =>
          Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p_38.fst, ())) fun p_39 =>
          Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_39.fst, Arg.imm 4, ())) fun p_40 =>
          Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p_40.fst, ()))
            fun p_41 =>
          Expr.store (t := i32) (Arg.imm 1) (Arg.var p_41.fst)
            (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var o_cl_aux, Arg.var nc, ())) fun p_42 =>
            Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p_42.fst, ())) fun p_43 =>
            Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_43.fst, Arg.imm 4, ())) fun p_44 =>
            Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p_44.fst, ()))
              fun p_45 =>
            Expr.store (t := i32) (Arg.var eid) (Arg.var p_45.fst)
              (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var o_cl_units, Arg.var n_units, ()))
                fun p_46 =>
              Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p_46.fst, ())) fun p_47 =>
              Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_47.fst, Arg.imm 4, ())) fun p_48 =>
              Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p_48.fst, ()))
                fun p_49 =>
              Expr.store (t := i32) (Arg.var nc) (Arg.var p_49.fst)
                (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var n_units, Arg.imm 1, ())) fun p_50 =>
                Expr.let_ (Op.mk (OpCode.add i32) (Arg.var nc, Arg.imm 1, ())) fun p_51 =>
                Expr.let_ (Op.mk (OpCode.add i32) (Arg.var alen, Arg.imm 1, ())) fun p_52 =>
                Expr.jump K716 (Arg.var nv', Arg.var p_51.fst, Arg.var p_52.fst,
                  Arg.var p_50.fst, Arg.var ab', ()))))))))

abbrev fidK6cBinBranchExpr (c : FullCfg)
    (mv_s mv2 acap_s o_cl_off o_cl_meta o_cl_aux o_cl_units o_arena : BitVec 32)
    (nv nc alen n_units triv_unit : BitVec 32) (abort_in : Bool)
    (eid j1 w : BitVec 32)
    (K284 : Cont [i32, i32, i32, i32, i32, Ty.bool, i32])
    (K506 : Cont [i32, i32, i32, i32, i32, Ty.bool]) : Expr Val Cont [Ty.bool] :=
  Expr.let_ (Op.mk (OpCode.and i32) (Arg.var w, Arg.imm 2147483647, ())) fun v708 =>
  Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var v708.fst, ())) fun p_9 =>
  Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pVals, Arg.var p_9.fst, ())) fun p_10 =>
  Expr.load i8 (Arg.var p_10.fst) fun v711 =>
  Expr.let_ (Op.mk (OpCode.trunc 32 8) (Arg.imm 0, ())) fun p_11 =>
  Expr.let_ (Op.mk (OpCode.sext 8 32) (Arg.var v711, ())) fun p_12 =>
  Expr.let_ (Op.mk (OpCode.sext 8 32) (Arg.var p_11.fst, ())) fun p_13 =>
  Expr.let_ (Op.mk (OpCode.cmp .slt i32 .bool rfl) (Arg.var p_12.fst, Arg.var p_13.fst, ()))
    fun p_14 =>
  Expr.jnz (Arg.var p_14.fst)
    (Expr.jump K284 (Arg.var nv, Arg.var nc, Arg.var alen, Arg.var n_units,
      Arg.var eid, Arg.var abort_in, Arg.var j1, ()))
    (Expr.group (fun _ : Tup Cont [[i32, i32, i32, i32, Ty.bool]] =>
      Blocks.cons (fun p : Tup Val [i32, i32, i32, i32, Ty.bool] =>
        Expr.jump K506 (Arg.var p.fst, Arg.var p.snd.fst, Arg.var p.snd.snd.fst,
          Arg.var p.snd.snd.snd.fst, Arg.var triv_unit, Arg.var p.snd.snd.snd.snd.fst, ()))
      Blocks.nil)
    fun Js_716 =>
    Expr.let_ (Op.mk (OpCode.trunc 32 8) (Arg.imm 0, ())) fun p_15 =>
    Expr.let_ (Op.mk (OpCode.sext 8 32) (Arg.var v711, ())) fun p_16 =>
    Expr.let_ (Op.mk (OpCode.sext 8 32) (Arg.var p_15.fst, ())) fun p_17 =>
    Expr.let_ (Op.mk (OpCode.cmp .eq i32 .bool rfl) (Arg.var p_16.fst, Arg.var p_17.fst, ()))
      fun p_18 =>
    Expr.jnz (Arg.var p_18.fst)
      (Expr.let_ (Op.mk (OpCode.lshr i32) (Arg.var v708.fst, Arg.imm 1, ())) fun v920 =>
      Expr.group (fun _ : Tup Cont [[i32, Ty.bool]] =>
        Blocks.cons (fun p921 : Tup Val [i32, Ty.bool] =>
          fidK6cBinEmitExpr c mv2 acap_s o_cl_off o_cl_meta o_cl_aux o_cl_units o_arena
            nc alen n_units triv_unit eid j1 v708.fst v920.fst p921.fst p921.snd.fst
            K284 Js_716.fst)
        Blocks.nil)
      fun Js_921 =>
      fidK6cBinTmkExpr c mv_s nv v708.fst v920.fst abort_in j1 K284 Js_921.fst
        nc alen n_units triv_unit)
      (Expr.jump Js_716.fst (Arg.var nv, Arg.var nc, Arg.var alen, Arg.var n_units,
        Arg.var abort_in, ())))

private theorem fid_k6c_bin_emit_wp {Γ : Env} {Q : Post [Ty.bool]} {X : XPost}
    {K284 : Cont [i32, i32, i32, i32, i32, Ty.bool, i32]}
    {K716 : Cont [i32, i32, i32, i32, Ty.bool]}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64}
    {tmp wsort tmk scr scr0 : List (BitVec 32)}
    {mv_s mv2 acap_s o_cl_off o_cl_meta o_cl_aux o_cl_units o_arena : BitVec 32}
    {nc alen n_units triv_unit eid j1 v708 v920 nv' : BitVec 32} {ab' : Bool}
    (hinv : FullDenseInvW c F0 F_cur s)
    (hmv_lo : 256 ≤ mv_s.toNat) (hmv_hi : mv_s.toNat ≤ 8192)
    (hmv2 : mv2.toNat = 2 * mv_s.toNat)
    (hcap : 4224 + 45 * mv_s.toNat + acap_s.toNat ≤ c.scratch_cap)
    (htmp : tmp.length = c.max_vars) (hwsort : wsort.length = 2 * c.max_vars)
    (htmk : tmk.length = 2 * c.max_vars) (hscr : scr.length = c.scratch_cap)
    (hoff_off : o_cl_off = 4224#32 + 29#32 * mv_s)
    (hoff_meta : o_cl_meta = 4224#32 + 33#32 * mv_s)
    (hoff_aux : o_cl_aux = 4224#32 + 37#32 * mv_s)
    (hoff_units : o_cl_units = 4224#32 + 41#32 * mv_s)
    (hoff_ar : o_arena = 4224#32 + 45#32 * mv_s)
    (hnv'_le : nv'.toNat ≤ mv_s.toNat) (hnv'_cv : nv'.toNat ≤ 2 * s.core.cur_vars)
    (hnc_le : nc.toNat ≤ 2 * mv_s.toNat) (hal_le : alen.toNat ≤ acap_s.toNat)
    (hnu_le : n_units.toNat ≤ nc.toNat)
    (heid : eid.toNat < 4096 ∧ (eid &&& 2047#32).toNat < 2001)
    (hv920 : v920.toNat < s.core.cur_vars)
    (htreg' : FidK6cTmkReg nv'.toNat s.core.cur_vars wsort tmk)
    (hcls : FidK6cClsOk mv_s.toNat nc.toNat alen.toNat n_units.toNat scr)
    (hpre0 : ∀ i, i < 4002 → scr[i]? = scr0[i]?)
    (hpre1 : ∀ i, 4132 ≤ i → i < 4192 → scr[i]? = scr0[i]?)
    (hm : (FullMem c (FidP6Work s tmp wsort tmk scr) ⋆ R) m)
    (hK284 : ∀ (nv'' nc'' alen'' n_units'' triv'' : BitVec 32) (ab'' : Bool)
      (tmp' wsort' tmk' scr' : List (BitVec 32)) (m' : Mem 64),
      tmp'.length = c.max_vars → wsort'.length = 2 * c.max_vars →
      tmk'.length = 2 * c.max_vars → scr'.length = c.scratch_cap →
      nv''.toNat ≤ mv_s.toNat → nv''.toNat ≤ 2 * s.core.cur_vars →
      nc''.toNat ≤ 2 * mv_s.toNat → alen''.toNat ≤ acap_s.toNat →
      n_units''.toNat ≤ nc''.toNat →
      (triv'' ≠ 4294967295#32 → (triv'' &&& 2047#32).toNat < 2001) →
      FidK6cTmkReg nv''.toNat s.core.cur_vars wsort' tmk' →
      FidK6cClsOk mv_s.toNat nc''.toNat alen''.toNat n_units''.toNat scr' →
      (∀ i, i < 4002 → scr'[i]? = scr0[i]?) →
      (∀ i, 4132 ≤ i → i < 4192 → scr'[i]? = scr0[i]?) →
      (FullMem c (FidP6Work s tmp' wsort' tmk' scr') ⋆ R) m' →
      K284 (nv'', nc'', alen'', n_units'', triv'', ab'', j1, ()) m')
    (hK716 : ∀ (nv'' nc'' alen'' n_units'' : BitVec 32) (ab'' : Bool)
      (tmp' wsort' tmk' scr' : List (BitVec 32)) (m' : Mem 64),
      tmp'.length = c.max_vars → wsort'.length = 2 * c.max_vars →
      tmk'.length = 2 * c.max_vars → scr'.length = c.scratch_cap →
      nv''.toNat ≤ mv_s.toNat → nv''.toNat ≤ 2 * s.core.cur_vars →
      nc''.toNat ≤ 2 * mv_s.toNat → alen''.toNat ≤ acap_s.toNat →
      n_units''.toNat ≤ nc''.toNat →
      FidK6cTmkReg nv''.toNat s.core.cur_vars wsort' tmk' →
      FidK6cClsOk mv_s.toNat nc''.toNat alen''.toNat n_units''.toNat scr' →
      (∀ i, i < 4002 → scr'[i]? = scr0[i]?) →
      (∀ i, 4132 ≤ i → i < 4192 → scr'[i]? = scr0[i]?) →
      (FullMem c (FidP6Work s tmp' wsort' tmk' scr') ⋆ R) m' →
      K716 (nv'', nc'', alen'', n_units'', ab'', ()) m') :
    (triv_unit ≠ 4294967295#32 → (triv_unit &&& 2047#32).toNat < 2001) →
    wp Γ Q X (fidK6cBinEmitExpr c mv2 acap_s o_cl_off o_cl_meta o_cl_aux o_cl_units o_arena
      nc alen n_units triv_unit eid j1 v708 v920 nv' ab' K284 K716) m := by
  intro htriv
  have _hlok := fid_k6c_work_lengthsOk hinv.1 htmp hwsort htmk hscr
  have hcur_le : s.core.cur_vars ≤ c.max_vars := hinv.1.core_ok.cur_vars_le
  have hscr_lt : scr.length < 2 ^ 30 := by
    have := c.hscr; have : dimacsBound = 2 ^ 28 := rfl; omega
  dsimp only [fidK6cBinEmitExpr]
  c0_hsteps
  · exact hK284 nv' nc alen n_units triv_unit true tmp wsort tmk scr m
      htmp hwsort htmk hscr hnv'_le hnv'_cv hnc_le hal_le hnu_le htriv htreg' hcls hpre0 hpre1 hm
  · exact hK284 nv' nc alen n_units triv_unit true tmp wsort tmk scr m
      htmp hwsort htmk hscr hnv'_le hnv'_cv hnc_le hal_le hnu_le htriv htreg' hcls hpre0 hpre1 hm
  · have hnc_lt : nc.toNat < 2 * mv_s.toNat := by bv_omega
    have hal1_le : alen.toNat + 1 ≤ acap_s.toNat := by
      have : (alen + 1#32).toNat = alen.toNat + 1 :=
        fid_k6c_add1_toNat (lim := 2 ^ 30) (by omega) (by decide)
      bv_omega
    have hidx_ar : (BitVec.setWidth 64 (o_arena + alen)).toNat =
        4224 + 45 * mv_s.toNat + alen.toNat := by
      rw [hoff_ar]; exact fid_k6_off_add (k := 45) hmv_hi (by omega) (by omega)
    have hidx_of : (BitVec.setWidth 64 (o_cl_off + nc)).toNat =
        4224 + 29 * mv_s.toNat + nc.toNat := by
      rw [hoff_off]; exact fid_k6_off_add (k := 29) hmv_hi (by omega) (by omega)
    have hidx_mt : (BitVec.setWidth 64 (o_cl_meta + nc)).toNat =
        4224 + 33 * mv_s.toNat + nc.toNat := by
      rw [hoff_meta]; exact fid_k6_off_add (k := 33) hmv_hi (by omega) (by omega)
    have hidx_ax : (BitVec.setWidth 64 (o_cl_aux + nc)).toNat =
        4224 + 37 * mv_s.toNat + nc.toNat := by
      rw [hoff_aux]; exact fid_k6_off_add (k := 37) hmv_hi (by omega) (by omega)
    have hidx_un : (BitVec.setWidth 64 (o_cl_units + n_units)).toNat =
        4224 + 41 * mv_s.toNat + n_units.toNat := by
      rw [hoff_units]; exact fid_k6_off_add (k := 41) hmv_hi (by omega) (by omega)
    have hb_ar : (o_arena + alen).toNat % 2 ^ 64 < scr.length := by
      rw [← fid_zext32_toNat (o_arena + alen), hidx_ar] at *
      have := BitVec.isLt (o_arena + alen); rw [Nat.mod_eq_of_lt (by omega)]; omega
    have ht_lt : (BitVec.setWidth 64 v920).toNat < tmk.length := by
      rw [fid_zext32_toNat]; omega
    let v1 : BitVec 32 :=
      ((tmk[(BitVec.setWidth 64 v920).toNat] - 1#32) <<< (1 : Nat)) ||| (v708 &&& 1#32)
    let scr1 := scr.set (BitVec.setWidth 64 (o_arena + alen)).toNat v1
    let scr2 := scr1.set (BitVec.setWidth 64 (o_cl_off + nc)).toNat alen
    let scr3 := scr2.set (BitVec.setWidth 64 (o_cl_meta + nc)).toNat 1#32
    let scr4 := scr3.set (BitVec.setWidth 64 (o_cl_aux + nc)).toNat eid
    have hb_of : (o_cl_off + nc).toNat % 2 ^ 64 < scr1.length := by
      simp only [scr1, List.length_set]
      have := BitVec.isLt (o_cl_off + nc); rw [Nat.mod_eq_of_lt (by omega)]
      rw [← fid_zext32_toNat (o_cl_off + nc), hidx_of]; omega
    have hb_mt : (o_cl_meta + nc).toNat % 2 ^ 64 < scr2.length := by
      simp only [scr2, scr1, List.length_set]
      have := BitVec.isLt (o_cl_meta + nc); rw [Nat.mod_eq_of_lt (by omega)]
      rw [← fid_zext32_toNat (o_cl_meta + nc), hidx_mt]; omega
    have hb_ax : (o_cl_aux + nc).toNat % 2 ^ 64 < scr3.length := by
      simp only [scr3, scr2, scr1, List.length_set]
      have := BitVec.isLt (o_cl_aux + nc); rw [Nat.mod_eq_of_lt (by omega)]
      rw [← fid_zext32_toNat (o_cl_aux + nc), hidx_ax]; omega
    have hb_un : (o_cl_units + n_units).toNat % 2 ^ 64 < scr4.length := by
      simp only [scr4, scr3, scr2, scr1, List.length_set]
      have := BitVec.isLt (o_cl_units + n_units); rw [Nat.mod_eq_of_lt (by omega)]
      rw [← fid_zext32_toNat (o_cl_units + n_units), hidx_un]; omega
    c0_hsteps
    rw [hidx_ar, hidx_of, hidx_mt, hidx_ax, hidx_un] at hm
    let scr' := ((((scr.set (4224 + 45 * mv_s.toNat + alen.toNat)
        (((tmk[v920.toNat] - 1) <<< (1 : Nat)) ||| (v708 &&& 1))).set
      (4224 + 29 * mv_s.toNat + nc.toNat) alen).set
      (4224 + 33 * mv_s.toNat + nc.toNat) 1#32).set
      (4224 + 37 * mv_s.toNat + nc.toNat) eid).set
      (4224 + 41 * mv_s.toNat + n_units.toNat) nc
    have hnc1 : (nc + 1#32).toNat = nc.toNat + 1 := fid_k6c_add1_toNat hnc_lt (by omega)
    have hal1 : (alen + 1#32).toNat = alen.toNat + 1 :=
      fid_k6c_add1_toNat (lim := 2 ^ 30) (by omega) (by decide)
    have hnu1 : (n_units + 1#32).toNat = n_units.toNat + 1 :=
      fid_k6c_add1_toNat (lim := 2 ^ 30) (by omega) (by decide)
    have hlen' : scr'.length = c.scratch_cap := by simp [scr', hscr]
    have hpre0' : ∀ i, i < 4002 → scr'[i]? = scr0[i]? := fun i hi => by
      dsimp only [scr']
      (repeat rw [List.getElem?_set_ne (by omega)]); exact hpre0 i hi
    have hpre1' : ∀ i, 4132 ≤ i → i < 4192 → scr'[i]? = scr0[i]? := fun i h1 h2 => by
      dsimp only [scr']
      (repeat rw [List.getElem?_set_ne (by omega)]); exact hpre1 i h1 h2
    have hcls' : FidK6cClsOk mv_s.toNat (nc + 1#32).toNat (alen + 1#32).toNat
        (n_units + 1#32).toNat scr' := by
      refine ⟨by rw [hnc1]; omega, fun cid hcid => ?_, by rw [hnc1, hnu1]; omega⟩
      rw [hnc1] at hcid
      by_cases hcur : cid < nc.toNat
      · have hc0 := hcls.2.1 cid hcur
        have h1 : scr'[4224 + 29 * mv_s.toNat + cid]? = scr[4224 + 29 * mv_s.toNat + cid]? := by
          dsimp only [scr']; repeat rw [List.getElem?_set_ne (by omega)]
        have h2 : scr'[4224 + 33 * mv_s.toNat + cid]? = scr[4224 + 33 * mv_s.toNat + cid]? := by
          dsimp only [scr']; repeat rw [List.getElem?_set_ne (by omega)]
        have h3 : scr'[4224 + 37 * mv_s.toNat + cid]? = scr[4224 + 37 * mv_s.toNat + cid]? := by
          dsimp only [scr']; repeat rw [List.getElem?_set_ne (by omega)]
        rw [h1, h2, h3, hal1]
        exact ⟨by omega, hc0.2.1, hc0.2.2.1, hc0.2.2.2⟩
      · have heq : cid = nc.toNat := by omega
        subst heq
        have h1 : scr'[4224 + 29 * mv_s.toNat + nc.toNat]? = some alen := by
          dsimp only [scr']
          rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
            List.getElem?_set_ne (by omega), List.getElem?_set_self (by simp [hscr]; omega)]
        have h2 : scr'[4224 + 33 * mv_s.toNat + nc.toNat]? = some 1#32 := by
          dsimp only [scr']
          rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
            List.getElem?_set_self (by simp [hscr]; omega)]
        have h3 : scr'[4224 + 37 * mv_s.toNat + nc.toNat]? = some eid := by
          dsimp only [scr']
          rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by simp [hscr]; omega)]
        simp only [h1, h2, h3, Option.getD_some, hal1]
        refine ⟨?_, by decide, heid.1, heid.2⟩
        rw [show (1#32 &&& 65535#32).toNat = 1 from rfl]; omega
    have hm' : (FullMem c (FidP6Work s tmp wsort tmk scr') ⋆ R) m := by
      dsimp only [FidP6Work, scr']
      simp only [fid_zext32_toNat] at hm
      exact hm
    exact hK716 nv' (nc + 1#32) (alen + 1#32) (n_units + 1#32) ab' tmp wsort tmk scr' m
      htmp hwsort htmk hlen' hnv'_le hnv'_cv (by omega) (by omega) (by omega)
      htreg' hcls' hpre0' hpre1' hm'

theorem fid_k6c_bin_branch_wp {Γ : Env} {Q : Post [Ty.bool]} {X : XPost}
    {K284 : Cont [i32, i32, i32, i32, i32, Ty.bool, i32]}
    {K506 : Cont [i32, i32, i32, i32, i32, Ty.bool]}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64}
    {tmp wsort tmk scr scr0 : List (BitVec 32)}
    {mv_s mv2 acap_s o_cl_off o_cl_meta o_cl_aux o_cl_units o_arena : BitVec 32}
    {nv nc alen n_units triv_unit eid j1 w : BitVec 32} {abort_in : Bool} {lit : Nat}
    (hinv : FullDenseInvW c F0 F_cur s)
    (hmv_lo : 256 ≤ mv_s.toNat) (hmv_hi : mv_s.toNat ≤ 8192)
    (hmv2 : mv2.toNat = 2 * mv_s.toNat)
    (hcap : 4224 + 45 * mv_s.toNat + acap_s.toNat ≤ c.scratch_cap)
    (htmp : tmp.length = c.max_vars) (hwsort : wsort.length = 2 * c.max_vars)
    (htmk : tmk.length = 2 * c.max_vars) (hscr : scr.length = c.scratch_cap)
    (hoff_off : o_cl_off = 4224#32 + 29#32 * mv_s)
    (hoff_meta : o_cl_meta = 4224#32 + 33#32 * mv_s)
    (hoff_aux : o_cl_aux = 4224#32 + 37#32 * mv_s)
    (hoff_units : o_cl_units = 4224#32 + 41#32 * mv_s)
    (hoff_ar : o_arena = 4224#32 + 45#32 * mv_s)
    (hnv_le : nv.toNat ≤ mv_s.toNat) (hnv_cv : nv.toNat ≤ 2 * s.core.cur_vars)
    (hnc_le : nc.toNat ≤ 2 * mv_s.toNat) (hal_le : alen.toNat ≤ acap_s.toNat)
    (hnu_le : n_units.toNat ≤ nc.toNat)
    (htriv : triv_unit ≠ 4294967295#32 → (triv_unit &&& 2047#32).toNat < 2001)
    (heid : eid.toNat < 4096 ∧ (eid &&& 2047#32).toNat < 2001)
    (htreg : FidK6cTmkReg nv.toNat s.core.cur_vars wsort tmk)
    (hcls : FidK6cClsOk mv_s.toNat nc.toNat alen.toNat n_units.toNat scr)
    (hpre0 : ∀ i, i < 4002 → scr[i]? = scr0[i]?)
    (hpre1 : ∀ i, 4132 ≤ i → i < 4192 → scr[i]? = scr0[i]?)
    (hent : FullBveEntryOkW F_cur s lit w) (hbin : w &&& 2147483648#32 ≠ 0#32)
    (hm : (FullMem c (FidP6Work s tmp wsort tmk scr) ⋆ R) m)
    (hK284 : ∀ (nv'' nc'' alen'' n_units'' triv'' : BitVec 32) (ab'' : Bool)
      (tmp' wsort' tmk' scr' : List (BitVec 32)) (m' : Mem 64),
      tmp'.length = c.max_vars → wsort'.length = 2 * c.max_vars →
      tmk'.length = 2 * c.max_vars → scr'.length = c.scratch_cap →
      nv''.toNat ≤ mv_s.toNat → nv''.toNat ≤ 2 * s.core.cur_vars →
      nc''.toNat ≤ 2 * mv_s.toNat → alen''.toNat ≤ acap_s.toNat →
      n_units''.toNat ≤ nc''.toNat →
      (triv'' ≠ 4294967295#32 → (triv'' &&& 2047#32).toNat < 2001) →
      FidK6cTmkReg nv''.toNat s.core.cur_vars wsort' tmk' →
      FidK6cClsOk mv_s.toNat nc''.toNat alen''.toNat n_units''.toNat scr' →
      (∀ i, i < 4002 → scr'[i]? = scr0[i]?) →
      (∀ i, 4132 ≤ i → i < 4192 → scr'[i]? = scr0[i]?) →
      (FullMem c (FidP6Work s tmp' wsort' tmk' scr') ⋆ R) m' →
      K284 (nv'', nc'', alen'', n_units'', triv'', ab'', j1, ()) m')
    (hK506 : ∀ (nv'' nc'' alen'' n_units'' triv'' : BitVec 32) (ab'' : Bool)
      (tmp' wsort' tmk' scr' : List (BitVec 32)) (m' : Mem 64),
      tmp'.length = c.max_vars → wsort'.length = 2 * c.max_vars →
      tmk'.length = 2 * c.max_vars → scr'.length = c.scratch_cap →
      nv''.toNat ≤ mv_s.toNat → nv''.toNat ≤ 2 * s.core.cur_vars →
      nc''.toNat ≤ 2 * mv_s.toNat → alen''.toNat ≤ acap_s.toNat →
      n_units''.toNat ≤ nc''.toNat →
      (triv'' ≠ 4294967295#32 → (triv'' &&& 2047#32).toNat < 2001) →
      FidK6cTmkReg nv''.toNat s.core.cur_vars wsort' tmk' →
      FidK6cClsOk mv_s.toNat nc''.toNat alen''.toNat n_units''.toNat scr' →
      (∀ i, i < 4002 → scr'[i]? = scr0[i]?) →
      (∀ i, 4132 ≤ i → i < 4192 → scr'[i]? = scr0[i]?) →
      (FullMem c (FidP6Work s tmp' wsort' tmk' scr') ⋆ R) m' →
      K506 (nv'', nc'', alen'', n_units'', triv'', ab'', ()) m') :
    wp Γ Q X (fidK6cBinBranchExpr c mv_s mv2 acap_s o_cl_off o_cl_meta o_cl_aux o_cl_units
      o_arena nv nc alen n_units triv_unit abort_in eid j1 w K284 K506) m := by
  have _hlok := fid_k6c_work_lengthsOk hinv.1 htmp hwsort htmk hscr
  have hcur_le : s.core.cur_vars ≤ c.max_vars := hinv.1.core_ok.cur_vars_le
  have hvals_len : s.core.vals.length = 2 * c.max_vars := hinv.1.core_ok.vals_len
  have hcv_lt : 2 * s.core.cur_vars < 2 ^ 30 := by
    have := c.hmaxv; simp only [dimacsBound] at this; omega
  have hb := fid_k6c_entry_bin_bounds hent hbin
  have hval_lt : (BitVec.setWidth 64 (w &&& 2147483647#32)).toNat < s.core.vals.length := by
    rw [fid_zext32_toNat]; omega
  dsimp only [fidK6cBinBranchExpr]
  c0_hsteps_nogrp
  · exact hK284 nv nc alen n_units eid abort_in tmp wsort tmk scr m
      htmp hwsort htmk hscr hnv_le hnv_cv hnc_le hal_le hnu_le (fun _ => heid.2) htreg hcls
      hpre0 hpre1 hm
  · apply wp_unroll_group
    intro Js_716 hJs_716
    have hJ716 : ∀ nv'' nc'' alen'' n_units'' ab'' tmp' wsort' tmk' scr' m',
        tmp'.length = c.max_vars → wsort'.length = 2 * c.max_vars →
        tmk'.length = 2 * c.max_vars → scr'.length = c.scratch_cap →
        nv''.toNat ≤ mv_s.toNat → nv''.toNat ≤ 2 * s.core.cur_vars →
        nc''.toNat ≤ 2 * mv_s.toNat → alen''.toNat ≤ acap_s.toNat →
        n_units''.toNat ≤ nc''.toNat →
        FidK6cTmkReg nv''.toNat s.core.cur_vars wsort' tmk' →
        FidK6cClsOk mv_s.toNat nc''.toNat alen''.toNat n_units''.toNat scr' →
        (∀ i, i < 4002 → scr'[i]? = scr0[i]?) →
        (∀ i, 4132 ≤ i → i < 4192 → scr'[i]? = scr0[i]?) →
        (FullMem c (FidP6Work s tmp' wsort' tmk' scr') ⋆ R) m' →
        Js_716 (nv'', nc'', alen'', n_units'', ab'', ()) m' := by
      intro nv'' nc'' alen'' n_units'' ab'' tmp' wsort' tmk' scr' m'
        ht' hw' hm' hs' h1 h2 h3 h4 h5 hr' hc' p0 p1 hmm
      apply hJs_716; try dsimp only [Blocks.get, Member.here]
      exact hK506 nv'' nc'' alen'' n_units'' triv_unit ab'' tmp' wsort' tmk' scr' m'
        ht' hw' hm' hs' h1 h2 h3 h4 h5 htriv hr' hc' p0 p1 hmm
    clear hJs_716
    c0_hsteps_nogrp
    · have hv_lt : ((w &&& 2147483647#32) >>> 1).toNat < s.core.cur_vars := by
        rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; exact hb.2.1
      have htmk_lt : (BitVec.setWidth 64 ((w &&& 2147483647#32) >>> 1)).toNat < tmk.length := by
        rw [fid_zext32_toNat]; omega
      apply wp_unroll_group
      intro Js_921 hJs_921
      have hJ921 : ∀ nv' ab' wsort' tmk' m',
          wsort'.length = 2 * c.max_vars → tmk'.length = 2 * c.max_vars →
          nv'.toNat ≤ mv_s.toNat → nv'.toNat ≤ 2 * s.core.cur_vars →
          FidK6cTmkReg nv'.toNat s.core.cur_vars wsort' tmk' →
          (FullMem c (FidP6Work s tmp wsort' tmk' scr) ⋆ R) m' →
          Js_921 (nv', ab', ()) m' := by
        intro nv' ab' wsort' tmk' m' hw' hm' h1 h2 hr' hmm
        apply hJs_921; try dsimp only [Blocks.get, Member.here]
        exact fid_k6c_bin_emit_wp hinv hmv_lo hmv_hi hmv2 hcap htmp hw' hm' hscr
          hoff_off hoff_meta hoff_aux hoff_units hoff_ar h1 h2 hnc_le hal_le hnu_le heid
          hv_lt hr' hcls hpre0 hpre1 hmm hK284 hJ716 htriv
      clear hJs_921
      dsimp only [fidK6cBinTmkExpr]
      c0_hsteps
      · exact hK284 nv nc alen n_units triv_unit true tmp wsort tmk scr m
          htmp hwsort htmk hscr hnv_le hnv_cv hnc_le hal_le hnu_le htriv htreg hcls
          hpre0 hpre1 hm
      · exact hK284 nv nc alen n_units triv_unit true tmp wsort tmk scr m
          htmp hwsort htmk hscr hnv_le hnv_cv hnc_le hal_le hnu_le htriv htreg hcls
          hpre0 hpre1 hm
      · have hnv_lt_mv : nv.toNat < mv_s.toNat := by bv_omega
        have hnv_lt_cv : nv.toNat < 2 * s.core.cur_vars := by
          have hc' := hc
          rw [Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64),
            Nat.mod_eq_of_lt (by omega : 2 * s.core.cur_vars < 2 ^ 64)] at hc'
          exact Nat.lt_of_not_le hc'
        have hws_lt : (BitVec.setWidth 64 nv).toNat < wsort.length := by
          rw [fid_zext32_toNat]; omega
        have htmk_lt1 : ((w &&& 2147483647#32) >>> 1).toNat < tmk.length := by
          rw [← fid_zext32_toNat]; exact htmk_lt
        have hand : (w &&& 2147483647#32).toNat = w.toNat % 2 ^ 31 := by
          rw [BitVec.toNat_and, show (2147483647#32 : BitVec 32).toNat = 2 ^ 31 - 1 from rfl]
          apply Nat.eq_of_testBit_eq; intro k
          rw [Nat.testBit_and, Nat.testBit_two_pow_sub_one, Nat.testBit_mod_two_pow]
          by_cases hk : k < 31 <;> simp [hk]
        have ht0 : tmk[((w &&& 2147483647#32) >>> 1).toNat]?.getD 0#32 = 0#32 := by
          have hidx : ((w &&& 2147483647#32) >>> 1).toNat = w.toNat % 2 ^ 31 / 2 := by
            rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.pow_one, hand]
          have hs : tmk[((w &&& 2147483647#32) >>> 1).toNat]? = some 0#32 := by
            rw [List.getElem?_eq_getElem htmk_lt1]; congr 1
            simp only [hidx]; assumption
          rw [hs, Option.getD_some]
        c0_hsteps
        refine hJ921 (nv + 1#32) abort_in _ _ m (by simp [hwsort]) (by simp [htmk])
          (by bv_omega) (by bv_omega) ?_ hm
        have hreg' := fid_k6c_tmkReg_step htreg hnv_lt_cv hv_lt ht0 (Or.inr (by omega))
          htmk_lt1 hcv_lt
        have hnv_z : (BitVec.setWidth 64 nv).toNat = nv.toNat := fid_zext32_toNat nv
        have hv_v : ((w &&& 2147483647#32) >>> 1) =
            BitVec.ofNat 32 ((w &&& 2147483647#32) >>> 1).toNat := by
          apply BitVec.eq_of_toNat_eq
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (BitVec.isLt _)]
        have hnv_v : (nv + 1#32) = BitVec.ofNat 32 (nv.toNat + 1) := by
          apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat, BitVec.toNat_add,
            show (1#32 : BitVec 32).toNat = 1 from rfl, Nat.mod_eq_of_lt (by omega)]
        dsimp only [FidP6Work]; rw [hnv_z, fid_zext32_toNat _]
        exact fid_k6c_tmkReg_congr hreg' (by bv_omega)
          (congrArg (wsort.set nv.toNat) hv_v.symm)
          (congrArg (tmk.set ((w &&& 2147483647#32) >>> 1).toNat) hnv_v.symm)
      · exact hJ921 nv abort_in wsort tmk m hwsort htmk hnv_le hnv_cv htreg hm
    · exact hJ716 nv nc alen n_units abort_in tmp wsort tmk scr m
        htmp hwsort htmk hscr hnv_le hnv_cv hnc_le hal_le hnu_le htreg hcls hpre0 hpre1 hm

abbrev fidK6cLargeBranchExpr (c : FullCfg)
    (mv_s mv2 acap_s max_csz o_cl_off o_cl_meta o_cl_aux o_cl_units o_arena : BitVec 32)
    (nv nc alen n_units triv_unit : BitVec 32) (abort_in : Bool)
    (lit_cur eid j1 w : BitVec 32)
    (K284 : Cont [i32, i32, i32, i32, i32, Ty.bool, i32])
    (K506 : Cont [i32, i32, i32, i32, i32, Ty.bool]) : Expr Val Cont [Ty.bool] :=
  Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var w, ())) fun p_9 =>
  Expr.let_ (Op.mk (OpCode.add i64) (Arg.var p_9.fst, Arg.imm 2, ())) fun p_10 =>
  Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_10.fst, Arg.imm 4, ())) fun p_11 =>
  Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pArena, Arg.var p_11.fst, ())) fun p_12 =>
  Expr.load i32 (Arg.var p_12.fst) fun lsz =>
  Expr.group (fun _ : Tup Cont [[i32, Ty.bool, Ty.bool, i32, i32]] =>
    Blocks.cons (fun p713 : Tup Val [i32, Ty.bool, Ty.bool, i32, i32] =>
      Expr.jnz (Arg.var p713.snd.fst)
        (Expr.jump K284 (Arg.var p713.fst, Arg.var nc, Arg.var alen, Arg.var n_units,
          Arg.var triv_unit, Arg.var p713.snd.fst, Arg.var j1, ()))
        (Expr.group (fun _ : Tup Cont [[i32, i32, i32, i32, Ty.bool, i32]] =>
          Blocks.cons (fun p720 : Tup Val [i32, i32, i32, i32, Ty.bool, i32] =>
            Expr.jump K506 (Arg.var p713.fst, Arg.var p720.fst, Arg.var p720.snd.fst,
              Arg.var p720.snd.snd.fst, Arg.var p720.snd.snd.snd.fst,
              Arg.var p720.snd.snd.snd.snd.fst, ()))
          Blocks.nil)
        fun Js_720 =>
        Expr.jnz (Arg.var p713.snd.snd.fst)
          (Expr.jump Js_720.fst (Arg.var nc, Arg.var alen, Arg.var n_units, Arg.var triv_unit,
            Arg.var p713.snd.fst, Arg.var p713.snd.snd.snd.snd.fst, ()))
          (Expr.let_ (Op.mk (OpCode.cmp .eq i32 .bool rfl)
            (Arg.var p713.snd.snd.snd.fst, Arg.imm 0, ())) fun p_13 =>
          Expr.jnz (Arg.var p_13.fst)
            (Expr.jump K284 (Arg.var p713.fst, Arg.var nc, Arg.var alen, Arg.var n_units,
              Arg.var eid, Arg.var p713.snd.fst, Arg.var j1, ()))
            (Expr.let_ (Op.mk (OpCode.cmp .uge i32 .bool rfl) (Arg.var nc, Arg.var mv2, ()))
              fun p_14 =>
            Expr.jnz (Arg.var p_14.fst)
              (Expr.jump K284 (Arg.var p713.fst, Arg.var nc, Arg.var alen, Arg.var n_units,
                Arg.var triv_unit, Arg.imm true, Arg.var j1, ()))
              (Expr.let_ (Op.mk (OpCode.add i32)
                (Arg.var alen, Arg.var p713.snd.snd.snd.fst, ())) fun p_15 =>
              Expr.let_ (Op.mk (OpCode.cmp .ugt i32 .bool rfl)
                (Arg.var p_15.fst, Arg.var acap_s, ()))
                fun p_16 =>
              Expr.jnz (Arg.var p_16.fst)
                (Expr.jump K284 (Arg.var p713.fst, Arg.var nc, Arg.var alen, Arg.var n_units,
                  Arg.var triv_unit, Arg.imm true, Arg.var j1, ()))
                (Expr.group (fun Js : Tup Cont [[i32]] => Blocks.cons (fun p : Tup Val [i32] =>
                  Expr.let_ (Op.mk (OpCode.cmp .ult i32 .bool rfl)
                    (Arg.var p.fst, Arg.var p713.snd.snd.snd.fst, ())) fun p_17 =>
                  Expr.jnz (Arg.var p_17.fst)
                    (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var o_arena, Arg.var alen, ()))
                      fun p_18 =>
                    Expr.let_ (Op.mk (OpCode.add i32) (Arg.var p_18.fst, Arg.var p.fst, ()))
                      fun p_19 =>
                    Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p_19.fst, ())) fun p_20 =>
                    Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_20.fst, Arg.imm 4, ())) fun p_21 =>
                    Expr.let_ (Op.mk (OpCode.add i64)
                      (Arg.var c.pScratchBuf, Arg.var p_21.fst, ())) fun p_22 =>
                    Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p.fst, ())) fun p_23 =>
                    Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_23.fst, Arg.imm 4, ())) fun p_24 =>
                    Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pTmp, Arg.var p_24.fst, ()))
                      fun p_25 =>
                    Expr.load i32 (Arg.var p_25.fst) fun ld_1 =>
                    Expr.store (Arg.var ld_1) (Arg.var p_22.fst)
                      (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var p.fst, Arg.imm 1, ())) fun p_26 =>
                      Expr.jump Js.fst (Arg.var p_26.fst, ())))
                    (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var o_cl_off, Arg.var nc, ()))
                      fun p_18 =>
                    Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p_18.fst, ())) fun p_19 =>
                    Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_19.fst, Arg.imm 4, ())) fun p_20 =>
                    Expr.let_ (Op.mk (OpCode.add i64)
                      (Arg.var c.pScratchBuf, Arg.var p_20.fst, ())) fun p_21 =>
                    Expr.store (t := i32) (Arg.var alen) (Arg.var p_21.fst)
                      (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var o_cl_meta, Arg.var nc, ()))
                        fun p_22 =>
                      Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p_22.fst, ())) fun p_23 =>
                      Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_23.fst, Arg.imm 4, ()))
                        fun p_24 =>
                      Expr.let_ (Op.mk (OpCode.add i64)
                        (Arg.var c.pScratchBuf, Arg.var p_24.fst, ())) fun p_25 =>
                      Expr.store (t := i32) (Arg.var p713.snd.snd.snd.fst) (Arg.var p_25.fst)
                        (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var o_cl_aux, Arg.var nc, ()))
                          fun p_26 =>
                        Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p_26.fst, ())) fun p_27 =>
                        Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_27.fst, Arg.imm 4, ()))
                          fun p_28 =>
                        Expr.let_ (Op.mk (OpCode.add i64)
                          (Arg.var c.pScratchBuf, Arg.var p_28.fst, ())) fun p_29 =>
                        Expr.store (t := i32) (Arg.var eid) (Arg.var p_29.fst)
                          (Expr.group (fun _Js_1 : Tup Cont [[i32]] =>
                            Blocks.cons (fun pu : Tup Val [i32] =>
                              Expr.let_ (Op.mk (OpCode.add i32) (Arg.var nc, Arg.imm 1, ()))
                                fun p_30 =>
                              Expr.let_ (Op.mk (OpCode.add i32)
                                (Arg.var alen, Arg.var p713.snd.snd.snd.fst, ())) fun p_31 =>
                              Expr.jump Js_720.fst (Arg.var p_30.fst, Arg.var p_31.fst,
                                Arg.var pu.fst, Arg.var triv_unit, Arg.var p713.snd.fst,
                                Arg.var p.fst, ())) Blocks.nil)
                          fun Js_1 =>
                          Expr.let_ (Op.mk (OpCode.cmp .eq i32 .bool rfl)
                            (Arg.var p713.snd.snd.snd.fst, Arg.imm 1, ())) fun p_30 =>
                          Expr.jnz (Arg.var p_30.fst)
                            (Expr.let_ (Op.mk (OpCode.add i32)
                              (Arg.var o_cl_units, Arg.var n_units, ())) fun p_31 =>
                            Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p_31.fst, ())) fun p_32 =>
                            Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_32.fst, Arg.imm 4, ()))
                              fun p_33 =>
                            Expr.let_ (Op.mk (OpCode.add i64)
                              (Arg.var c.pScratchBuf, Arg.var p_33.fst, ())) fun p_34 =>
                            Expr.store (t := i32) (Arg.var nc) (Arg.var p_34.fst)
                              (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var n_units, Arg.imm 1, ()))
                                fun p_35 =>
                              Expr.jump Js_1.fst (Arg.var p_35.fst, ())))
                            (Expr.jump Js_1.fst (Arg.var n_units, ()))))))) Blocks.nil)
                fun Js => Expr.jump Js.fst (Arg.imm 0, ())))))))
      Blocks.nil)
  fun Js_713 =>
  Expr.group (fun Js : Tup Cont [[i32, i32, i32]] =>
    Blocks.cons (fun pl : Tup Val [i32, i32, i32] =>
    Expr.let_ (Op.mk (OpCode.cmp .ult i32 .bool rfl) (Arg.var pl.snd.snd.fst, Arg.var lsz, ()))
      fun p_1 =>
    Expr.jnz (Arg.var p_1.fst)
      (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var w, ())) fun p_2 =>
      Expr.let_ (Op.mk (OpCode.add i64) (Arg.var p_2.fst, Arg.imm 3, ())) fun p_3 =>
      Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var pl.snd.snd.fst, ())) fun p_4 =>
      Expr.let_ (Op.mk (OpCode.add i64) (Arg.var p_3.fst, Arg.var p_4.fst, ())) fun p_5 =>
      Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_5.fst, Arg.imm 4, ())) fun p_6 =>
      Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pArena, Arg.var p_6.fst, ())) fun p_7 =>
      Expr.load i32 (Arg.var p_7.fst) fun ld =>
      Expr.group (fun _ : Tup Cont [[i32, Ty.bool, Ty.bool, i32]] => Blocks.cons (fun p_8 =>
        Expr.let_ (Op.mk (OpCode.add i32) (Arg.var pl.snd.snd.fst, Arg.imm 1, ())) fun p_9 =>
        Expr.jump Js.fst (Arg.var p_8.fst, Arg.var p_8.snd.snd.snd.fst, Arg.var p_9.fst, ()))
        Blocks.nil) fun Js_1 =>
        Expr.let_ (Op.mk (OpCode.cmp .ne i32 .bool rfl) (Arg.var ld, Arg.var lit_cur, ()))
          fun p_8 =>
        Expr.jnz (Arg.var p_8.fst)
          (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var ld, ())) fun p_9 =>
          Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pVals, Arg.var p_9.fst, ())) fun p_10 =>
          Expr.load i8 (Arg.var p_10.fst) fun ld_1 =>
          Expr.let_ (Op.mk (OpCode.trunc 32 8) (Arg.imm 0, ())) fun p_11 =>
          Expr.let_ (Op.mk (OpCode.sext 8 32) (Arg.var ld_1, ())) fun p_12 =>
          Expr.let_ (Op.mk (OpCode.sext 8 32) (Arg.var p_11.fst, ())) fun p_13 =>
          Expr.let_ (Op.mk (OpCode.cmp .sgt i32 .bool rfl) (Arg.var p_12.fst, Arg.var p_13.fst, ()))
            fun p_14 =>
          Expr.jnz (Arg.var p_14.fst)
            (Expr.jump Js_713.fst (Arg.var pl.fst, Arg.var abort_in, Arg.imm true,
              Arg.var pl.snd.fst, Arg.var pl.snd.snd.fst, ()))
            (Expr.group (fun _ : Tup Cont [[i32, Ty.bool, i32]] => Blocks.cons (fun p_15 =>
              Expr.jump Js_1.fst (Arg.var p_15.fst, Arg.var p_15.snd.fst, Arg.imm false,
                Arg.var p_15.snd.snd.fst, ())) Blocks.nil) fun Js_2 =>
              Expr.let_ (Op.mk (OpCode.trunc 32 8) (Arg.imm 0, ())) fun p_15 =>
              Expr.let_ (Op.mk (OpCode.sext 8 32) (Arg.var ld_1, ())) fun p_16 =>
              Expr.let_ (Op.mk (OpCode.sext 8 32) (Arg.var p_15.fst, ())) fun p_17 =>
              Expr.let_ (Op.mk (OpCode.cmp .eq i32 .bool rfl)
                (Arg.var p_16.fst, Arg.var p_17.fst, ())) fun p_18 =>
              Expr.jnz (Arg.var p_18.fst)
                (Expr.let_ (Op.mk (OpCode.lshr i32) (Arg.var ld, Arg.imm 1, ())) fun p_19 =>
                Expr.group (fun _ : Tup Cont [[i32, Ty.bool]] =>
                  Blocks.cons (fun p_20 : Tup Val [i32, Ty.bool] =>
                  Expr.let_ (Op.mk (OpCode.cmp .uge i32 .bool rfl)
                    (Arg.var pl.snd.fst, Arg.var max_csz, ())) fun p_21 =>
                  Expr.jnz (Arg.var p_21.fst)
                    (Expr.jump Js_713.fst (Arg.var p_20.fst, Arg.imm true, Arg.imm false,
                      Arg.var pl.snd.fst, Arg.var pl.snd.snd.fst, ()))
                    (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var pl.snd.fst, ())) fun p_22 =>
                    Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_22.fst, Arg.imm 4, ())) fun p_23 =>
                    Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pTmp, Arg.var p_23.fst, ()))
                      fun p_24 =>
                    Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p_19.fst, ())) fun p_25 =>
                    Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_25.fst, Arg.imm 4, ())) fun p_26 =>
                    Expr.let_ (Op.mk (OpCode.add i64)
                      (Arg.var c.pTarjanMark, Arg.var p_26.fst, ())) fun p_27 =>
                    Expr.load i32 (Arg.var p_27.fst) fun ld_2 =>
                    Expr.let_ (Op.mk (OpCode.sub i32) (Arg.var ld_2, Arg.imm 1, ())) fun p_28 =>
                    Expr.let_ (Op.mk (OpCode.shl i32) (Arg.var p_28.fst, Arg.imm 1, ())) fun p_29 =>
                    Expr.let_ (Op.mk (OpCode.and i32) (Arg.var ld, Arg.imm 1, ())) fun p_30 =>
                    Expr.let_ (Op.mk (OpCode.or i32) (Arg.var p_29.fst, Arg.var p_30.fst, ()))
                      fun p_31 =>
                    Expr.store (Arg.var p_31.fst) (Arg.var p_24.fst)
                      (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var pl.snd.fst, Arg.imm 1, ()))
                        fun p_32 =>
                      Expr.jump Js_2.fst (Arg.var p_20.fst, Arg.var p_20.snd.fst,
                        Arg.var p_32.fst, ())))) Blocks.nil)
                  fun Js_3 =>
                  Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p_19.fst, ())) fun p_20 =>
                  Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_20.fst, Arg.imm 4, ())) fun p_21 =>
                  Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pTarjanMark, Arg.var p_21.fst, ()))
                    fun p_22 =>
                  Expr.load i32 (Arg.var p_22.fst) fun ld_2 =>
                  Expr.let_ (Op.mk (OpCode.cmp .eq i32 .bool rfl) (Arg.var ld_2, Arg.imm 0, ()))
                    fun p_23 =>
                  Expr.jnz (Arg.var p_23.fst)
                    (Expr.let_ (Op.mk (OpCode.cmp .uge i32 .bool rfl)
                      (Arg.var pl.fst, Arg.var mv_s, ())) fun p_24 =>
                    Expr.jnz (Arg.var p_24.fst)
                      (Expr.jump Js_713.fst (Arg.var pl.fst, Arg.imm true, Arg.imm false,
                        Arg.var pl.snd.fst, Arg.var pl.snd.snd.fst, ()))
                      (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var pl.fst, ())) fun p_25 =>
                      Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.hdr, Arg.imm 776, ()))
                        fun p_26 =>
                      Expr.load i64 (Arg.var p_26.fst) fun ld_3 =>
                      Expr.let_ (Op.mk (OpCode.sext 32 64) (Arg.imm 1, ())) fun p_27 =>
                      Expr.let_ (Op.mk (OpCode.shl i64) (Arg.var ld_3, Arg.var p_27.fst, ()))
                        fun p_28 =>
                      Expr.let_ (Op.mk (OpCode.cmp .uge i64 .bool rfl)
                        (Arg.var p_25.fst, Arg.var p_28.fst, ())) fun p_29 =>
                      Expr.jnz (Arg.var p_29.fst)
                        (Expr.jump Js_713.fst (Arg.var pl.fst, Arg.imm true, Arg.imm false,
                          Arg.var pl.snd.fst, Arg.var pl.snd.snd.fst, ()))
                        (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var pl.fst, ())) fun p_30 =>
                        Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_30.fst, Arg.imm 4, ()))
                          fun p_31 =>
                        Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pWsort, Arg.var p_31.fst, ()))
                          fun p_32 =>
                        Expr.store (Arg.var p_19.fst) (Arg.var p_32.fst)
                          (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var pl.fst, Arg.imm 1, ()))
                            fun p_33 =>
                          Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p_19.fst, ())) fun p_34 =>
                          Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_34.fst, Arg.imm 4, ()))
                            fun p_35 =>
                          Expr.let_ (Op.mk (OpCode.add i64)
                            (Arg.var c.pTarjanMark, Arg.var p_35.fst, ())) fun p_36 =>
                          Expr.store (Arg.var p_33.fst) (Arg.var p_36.fst)
                            (Expr.jump Js_3.fst (Arg.var p_33.fst, Arg.var abort_in, ()))))))
                    (Expr.jump Js_3.fst (Arg.var pl.fst, Arg.var abort_in, ())))
                (Expr.jump Js_2.fst (Arg.var pl.fst, Arg.var abort_in, Arg.var pl.snd.fst, ()))))
          (Expr.jump Js_1.fst (Arg.var pl.fst, Arg.var abort_in, Arg.imm false,
            Arg.var pl.snd.fst, ())))
      (Expr.jump Js_713.fst (Arg.var pl.fst, Arg.var abort_in, Arg.imm false,
        Arg.var pl.snd.fst, Arg.var pl.snd.snd.fst, ()))) Blocks.nil)
  fun Js => Expr.jump Js.fst (Arg.var nv, Arg.imm 0, Arg.imm 0, ())

theorem fid_k6c_large_branch_wp {Γ : Env} {Q : Post [Ty.bool]} {X : XPost}
    {K284 : Cont [i32, i32, i32, i32, i32, Ty.bool, i32]}
    {K506 : Cont [i32, i32, i32, i32, i32, Ty.bool]}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64}
    {tmp wsort tmk scr scr0 : List (BitVec 32)}
    {mv_s mv2 acap_s max_csz o_cl_off o_cl_meta o_cl_aux o_cl_units o_arena : BitVec 32}
    {nv nc alen n_units triv_unit lit_cur eid j1 w : BitVec 32} {abort_in : Bool}
    {lit : Nat}
    (hinv : FullDenseInvW c F0 F_cur s)
    (hmv_lo : 256 ≤ mv_s.toNat) (hmv_hi : mv_s.toNat ≤ 8192)
    (hmv2 : mv2.toNat = 2 * mv_s.toNat)
    (hcap : 4224 + 45 * mv_s.toNat + acap_s.toNat ≤ c.scratch_cap)
    (hmax_csz : max_csz.toNat ≤ c.max_vars ∧ max_csz.toNat ≤ 65535)
    (htmp : tmp.length = c.max_vars) (hwsort : wsort.length = 2 * c.max_vars)
    (htmk : tmk.length = 2 * c.max_vars) (hscr : scr.length = c.scratch_cap)
    (hoff_off : o_cl_off = 4224#32 + 29#32 * mv_s)
    (hoff_meta : o_cl_meta = 4224#32 + 33#32 * mv_s)
    (hoff_aux : o_cl_aux = 4224#32 + 37#32 * mv_s)
    (hoff_units : o_cl_units = 4224#32 + 41#32 * mv_s)
    (hoff_ar : o_arena = 4224#32 + 45#32 * mv_s)
    (hnv_le : nv.toNat ≤ mv_s.toNat) (hnv_cv : nv.toNat ≤ 2 * s.core.cur_vars)
    (hnc_le : nc.toNat ≤ 2 * mv_s.toNat) (hal_le : alen.toNat ≤ acap_s.toNat)
    (hnu_le : n_units.toNat ≤ nc.toNat)
    (htriv : triv_unit ≠ 4294967295#32 → (triv_unit &&& 2047#32).toNat < 2001)
    (heid : eid.toNat < 4096 ∧ (eid &&& 2047#32).toNat < 2001)
    (htreg : FidK6cTmkReg nv.toNat s.core.cur_vars wsort tmk)
    (hcls : FidK6cClsOk mv_s.toNat nc.toNat alen.toNat n_units.toNat scr)
    (hpre0 : ∀ i, i < 4002 → scr[i]? = scr0[i]?)
    (hpre1 : ∀ i, 4132 ≤ i → i < 4192 → scr[i]? = scr0[i]?)
    (hent : FullBveEntryOkW F_cur s lit w) (hnbin : w &&& 2147483648#32 = 0#32)
    (hm : (FullMem c (FidP6Work s tmp wsort tmk scr) ⋆ R) m)
    (hK284 : ∀ (nv'' nc'' alen'' n_units'' triv'' : BitVec 32) (ab'' : Bool)
      (tmp' wsort' tmk' scr' : List (BitVec 32)) (m' : Mem 64),
      tmp'.length = c.max_vars → wsort'.length = 2 * c.max_vars →
      tmk'.length = 2 * c.max_vars → scr'.length = c.scratch_cap →
      nv''.toNat ≤ mv_s.toNat → nv''.toNat ≤ 2 * s.core.cur_vars →
      nc''.toNat ≤ 2 * mv_s.toNat → alen''.toNat ≤ acap_s.toNat →
      n_units''.toNat ≤ nc''.toNat →
      (triv'' ≠ 4294967295#32 → (triv'' &&& 2047#32).toNat < 2001) →
      FidK6cTmkReg nv''.toNat s.core.cur_vars wsort' tmk' →
      FidK6cClsOk mv_s.toNat nc''.toNat alen''.toNat n_units''.toNat scr' →
      (∀ i, i < 4002 → scr'[i]? = scr0[i]?) →
      (∀ i, 4132 ≤ i → i < 4192 → scr'[i]? = scr0[i]?) →
      (FullMem c (FidP6Work s tmp' wsort' tmk' scr') ⋆ R) m' →
      K284 (nv'', nc'', alen'', n_units'', triv'', ab'', j1, ()) m')
    (hK506 : ∀ (nv'' nc'' alen'' n_units'' triv'' : BitVec 32) (ab'' : Bool)
      (tmp' wsort' tmk' scr' : List (BitVec 32)) (m' : Mem 64),
      tmp'.length = c.max_vars → wsort'.length = 2 * c.max_vars →
      tmk'.length = 2 * c.max_vars → scr'.length = c.scratch_cap →
      nv''.toNat ≤ mv_s.toNat → nv''.toNat ≤ 2 * s.core.cur_vars →
      nc''.toNat ≤ 2 * mv_s.toNat → alen''.toNat ≤ acap_s.toNat →
      n_units''.toNat ≤ nc''.toNat →
      (triv'' ≠ 4294967295#32 → (triv'' &&& 2047#32).toNat < 2001) →
      FidK6cTmkReg nv''.toNat s.core.cur_vars wsort' tmk' →
      FidK6cClsOk mv_s.toNat nc''.toNat alen''.toNat n_units''.toNat scr' →
      (∀ i, i < 4002 → scr'[i]? = scr0[i]?) →
      (∀ i, 4132 ≤ i → i < 4192 → scr'[i]? = scr0[i]?) →
      (FullMem c (FidP6Work s tmp' wsort' tmk' scr') ⋆ R) m' →
      K506 (nv'', nc'', alen'', n_units'', triv'', ab'', ()) m') :
    wp Γ Q X (fidK6cLargeBranchExpr c mv_s mv2 acap_s max_csz o_cl_off o_cl_meta o_cl_aux
      o_cl_units o_arena nv nc alen n_units triv_unit abort_in lit_cur eid j1 w K284 K506) m := by
  have hlok := fid_k6c_work_lengthsOk hinv.1 htmp hwsort htmk hscr
  have hscr_lt : scr.length < 2 ^ 30 := by
    have := c.hscr; have : dimacsBound = 2 ^ 28 := rfl; omega
  have hlb := fid_k6c_entry_large_bounds hinv.1 hinv.2.1.arena hent hnbin
  have har_len2 : (BitVec.setWidth 64 w + 2#64).toNat < s.core.arena.length := by
    have har2 : s.core.arena_len ≤ c.arena_cap := hlb.2.2.2.1
    have har3 : s.core.arena.length = c.arena_cap := hinv.1.core_ok.arena_len_arr
    have hw0 : w.toNat < 2 ^ 64 := Nat.lt_trans (BitVec.isLt w) (by decide)
    have hadd : (BitVec.setWidth 64 w + 2#64).toNat = w.toNat + 2 := by
      simp only [BitVec.toNat_add, BitVec.toNat_setWidth, Nat.mod_eq_of_lt hw0,
        show (2#64 : BitVec 64).toNat = 2 from rfl]
      rw [Nat.mod_eq_of_lt (by omega)]
    rw [hadd]; omega
  dsimp only [fidK6cLargeBranchExpr]
  c0_hsteps_nogrp
  have hlsz : (s.core.arena[(BitVec.setWidth 64 w + 2#64).toNat]'har_len2).toNat =
      fullArenaClauseSizeCore s.core w.toNat := by
    have hw0 : w.toNat < 2 ^ 64 := Nat.lt_trans (BitVec.isLt w) (by decide)
    have hadd : (BitVec.setWidth 64 w + 2#64).toNat = w.toNat + 2 := by
      simp only [BitVec.toNat_add, BitVec.toNat_setWidth, Nat.mod_eq_of_lt hw0,
        show (2#64 : BitVec 64).toNat = 2 from rfl]
      rw [Nat.mod_eq_of_lt (by omega)]
    have hget : s.core.arena[w.toNat + 2]? =
        some (s.core.arena[(BitVec.setWidth 64 w + 2#64).toNat]'har_len2) := by
      rw [← hadd]; exact List.getElem?_eq_getElem har_len2
    simp only [fullArenaClauseSizeCore, hget, Option.getD_some]
  apply wp_unroll_group
  intro Js_713 hJs_713
  refine fid_k6c_scan_large_wp hinv hmv_lo hmv_hi hmax_csz htmp hwsort htmk hscr
    hnv_le hnv_cv htreg hlb hlsz hm ?_
  intro nv' ab' sat' csz' j' tmp' wsort' tmk'
    htp' hws' htm' hnv'_le hnv'_cv hcsz' htreg' m' hm'
  apply hJs_713; try dsimp only [Blocks.get, Member.here]
  c0_hsteps_nogrp
  · exact hK284 nv' nc alen n_units triv_unit ab' tmp' wsort' tmk' scr m'
      htp' hws' htm' hscr hnv'_le hnv'_cv hnc_le hal_le hnu_le htriv htreg' hcls
      hpre0 hpre1 hm'
  · apply wp_unroll_group
    intro Js_720 hJs_720
    have hJ720 : ∀ nc'' alen'' n_units'' triv'' ab'' (k_out : BitVec 32) scr'' m'',
        scr''.length = c.scratch_cap → nc''.toNat ≤ 2 * mv_s.toNat →
        alen''.toNat ≤ acap_s.toNat → n_units''.toNat ≤ nc''.toNat →
        (triv'' ≠ 4294967295#32 → (triv'' &&& 2047#32).toNat < 2001) →
        FidK6cClsOk mv_s.toNat nc''.toNat alen''.toNat n_units''.toNat scr'' →
        (∀ i, i < 4002 → scr''[i]? = scr0[i]?) →
        (∀ i, 4132 ≤ i → i < 4192 → scr''[i]? = scr0[i]?) →
        (FullMem c (FidP6Work s tmp' wsort' tmk' scr'') ⋆ R) m'' →
        Js_720 (nc'', alen'', n_units'', triv'', ab'', k_out, ()) m'' := by
      intro nc'' alen'' n_units'' triv'' ab'' k_out scr'' m'' hs'' h1 h2 h3 htv hc'' p0 p1 hmm
      apply hJs_720; try dsimp only [Blocks.get, Member.here]
      exact hK506 nv' nc'' alen'' n_units'' triv'' ab'' tmp' wsort' tmk' scr'' m''
        htp' hws' htm' hs'' hnv'_le hnv'_cv h1 h2 h3 htv htreg' hc'' p0 p1 hmm
    clear hJs_720
    c0_hsteps_nogrp
    · exact hJ720 nc alen n_units triv_unit ab' j' scr m'
        hscr hnc_le hal_le hnu_le htriv hcls hpre0 hpre1 hm'
    · exact hK284 nv' nc alen n_units eid ab' tmp' wsort' tmk' scr m'
        htp' hws' htm' hscr hnv'_le hnv'_cv hnc_le hal_le hnu_le (fun _ => heid.2)
        htreg' hcls hpre0 hpre1 hm'
    · exact hK284 nv' nc alen n_units triv_unit true tmp' wsort' tmk' scr m'
        htp' hws' htm' hscr hnv'_le hnv'_cv hnc_le hal_le hnu_le htriv htreg' hcls
        hpre0 hpre1 hm'
    · exact hK284 nv' nc alen n_units triv_unit true tmp' wsort' tmk' scr m'
        htp' hws' htm' hscr hnv'_le hnv'_cv hnc_le hal_le hnu_le htriv htreg' hcls
        hpre0 hpre1 hm'
    · have hcsz_pos : 1 ≤ csz'.toNat := by bv_omega
      have hnc_lt : nc.toNat < 2 * mv_s.toNat := by bv_omega
      have hal_add : alen.toNat + csz'.toNat ≤ acap_s.toNat := by bv_omega
      apply fid_k6c_copy_clause_wp hmv_lo hmv_hi hcap hscr_lt hscr htp'
        hoff_off hoff_meta hoff_aux hoff_units hoff_ar
        hcsz_pos (by omega) (by omega) hnc_lt hnu_le hal_add heid hcls hm'
      intro scr' pu k_out m'' hlen' hag' hcls' hpu hm''
      have hnc1 : (nc + 1#32).toNat = nc.toNat + 1 := fid_k6c_add1_toNat hnc_lt (by omega)
      have hal1 : (alen + csz').toNat = alen.toNat + csz'.toNat := by bv_omega
      have hpre0' : ∀ i, i < 4002 → scr'[i]? = scr0[i]? := fun i hi => by
        rw [hag' i (by omega), hpre0 i hi]
      have hpre1' : ∀ i, 4132 ≤ i → i < 4192 → scr'[i]? = scr0[i]? := fun i h1 h2 => by
        rw [hag' i (by omega), hpre1 i h1 h2]
      refine hJ720 (nc + 1#32) (alen + csz') pu triv_unit ab' k_out scr' m''
        hlen' (by omega) (by omega) ?_ htriv hcls' hpre0' hpre1' hm''
      rw [hpu, hnc1]; split <;> omega

abbrev fidK6cInnerLoopExpr (c : FullCfg)
    (mv_s mv2 acap_s max_csz o_cl_off o_cl_meta o_cl_aux o_cl_units o_arena : BitVec 32)
    (nv nc alen n_units triv_unit : BitVec 32) (abort_in : Bool)
    (side cnt off mask_off lit : BitVec 32) (second_pass : Bool)
    (K284 : Cont [i32, i32, i32, i32, i32, Ty.bool, i32]) : Expr Val Cont [Ty.bool] :=
  Expr.group (fun L484 : Tup Cont [[i32, i32, i32, i32, Ty.bool, i32]] =>
    Blocks.cons (fun pl : Tup Val [i32, i32, i32, i32, Ty.bool, i32] =>
      let v_nv := pl.fst; let v_nc := pl.snd.fst; let v_al := pl.snd.snd.fst
      let v_nu := pl.snd.snd.snd.fst; let v_ab := pl.snd.snd.snd.snd.fst
      let v_j := pl.snd.snd.snd.snd.snd.fst
      Expr.let_ (Op.mk (OpCode.cmp .ult i32 .bool rfl) (Arg.var v_j, Arg.var cnt, ())) fun p_1 =>
      Expr.jnz (Arg.var p_1.fst)
        (Expr.jnz (Arg.var v_ab)
          (Expr.jump K284 (Arg.var v_nv, Arg.var v_nc, Arg.var v_al, Arg.var v_nu,
            Arg.var triv_unit, Arg.var v_ab, Arg.var v_j, ()))
          (Expr.group (fun _ : Tup Cont [[i32]] => Blocks.cons (fun p493 : Tup Val [i32] =>
            Expr.let_ (Op.mk (OpCode.add i32) (Arg.var v_j, Arg.imm 1, ())) fun v496 =>
            Expr.group (fun _ : Tup Cont [[]] => Blocks.cons (fun _ : Tup Val [] =>
              Expr.let_ (Op.mk (OpCode.add i32) (Arg.var off, Arg.var p493.fst, ())) fun p_2 =>
              Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p_2.fst, ())) fun p_3 =>
              Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_3.fst, Arg.imm 4, ())) fun p_4 =>
              Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p_4.fst, ()))
                fun p_5 =>
              Expr.load i32 (Arg.var p_5.fst) fun w =>
              Expr.let_ (Op.mk (OpCode.shl i32) (Arg.var side, Arg.imm 11, ())) fun p_6 =>
              Expr.let_ (Op.mk (OpCode.or i32) (Arg.var p_6.fst, Arg.var p493.fst, ())) fun eid =>
              Expr.group (fun _ : Tup Cont [[i32, i32, i32, i32, i32, Ty.bool]] =>
                Blocks.cons (fun p506 : Tup Val [i32, i32, i32, i32, i32, Ty.bool] =>
                  Expr.jump L484.fst (Arg.var p506.fst, Arg.var p506.snd.fst,
                    Arg.var p506.snd.snd.fst, Arg.var p506.snd.snd.snd.fst,
                    Arg.var p506.snd.snd.snd.snd.snd.fst, Arg.var v496.fst, ()))
                Blocks.nil)
              fun Js_506 =>
              Expr.let_ (Op.mk (OpCode.and i32) (Arg.var w, Arg.imm 2147483648, ())) fun p_7 =>
              Expr.let_ (Op.mk (OpCode.cmp .ne i32 .bool rfl) (Arg.var p_7.fst, Arg.imm 0, ()))
                fun p_8 =>
              Expr.jnz (Arg.var p_8.fst)
                (fidK6cBinBranchExpr c mv_s mv2 acap_s o_cl_off o_cl_meta o_cl_aux o_cl_units
                  o_arena v_nv v_nc v_al v_nu triv_unit v_ab eid.fst v496.fst w
                  K284 Js_506.fst)
                (fidK6cLargeBranchExpr c mv_s mv2 acap_s max_csz o_cl_off o_cl_meta o_cl_aux
                  o_cl_units o_arena v_nv v_nc v_al v_nu triv_unit v_ab lit eid.fst v496.fst w
                  K284 Js_506.fst))
              Blocks.nil)
            fun Js_497 =>
            Expr.jnz (Arg.var second_pass)
              (Expr.let_ (Op.mk (OpCode.lshr i32) (Arg.var p493.fst, Arg.imm 5, ())) fun p_2 =>
              Expr.let_ (Op.mk (OpCode.add i32) (Arg.var mask_off, Arg.var p_2.fst, ())) fun p_3 =>
              Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p_3.fst, ())) fun p_4 =>
              Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_4.fst, Arg.imm 4, ())) fun p_5 =>
              Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p_5.fst, ()))
                fun p_6 =>
              Expr.load i32 (Arg.var p_6.fst) fun ld =>
              Expr.let_ (Op.mk (OpCode.and i32) (Arg.var p493.fst, Arg.imm 31, ())) fun p_7 =>
              Expr.let_ (Op.mk (OpCode.lshr i32) (Arg.var ld, Arg.var p_7.fst, ())) fun p_8 =>
              Expr.let_ (Op.mk (OpCode.and i32) (Arg.var p_8.fst, Arg.imm 1, ())) fun p_9 =>
              Expr.let_ (Op.mk (OpCode.cmp .eq i32 .bool rfl) (Arg.var p_9.fst, Arg.imm 0, ()))
                fun p_10 =>
              Expr.jnz (Arg.var p_10.fst)
                (Expr.jump L484.fst (Arg.var v_nv, Arg.var v_nc, Arg.var v_al, Arg.var v_nu,
                  Arg.var v_ab, Arg.var v496.fst, ()))
                (Expr.jump Js_497.fst ()))
              (Expr.jump Js_497.fst ()))
            Blocks.nil)
          fun Js_493 =>
          Expr.jnz (Arg.var second_pass)
            (Expr.let_ (Op.mk (OpCode.sub i32) (Arg.var cnt, Arg.imm 1, ())) fun p_2 =>
            Expr.let_ (Op.mk (OpCode.sub i32) (Arg.var p_2.fst, Arg.var v_j, ())) fun p_3 =>
            Expr.jump Js_493.fst (Arg.var p_3.fst, ()))
            (Expr.jump Js_493.fst (Arg.var v_j, ()))))
        (Expr.jump K284 (Arg.var v_nv, Arg.var v_nc, Arg.var v_al, Arg.var v_nu,
          Arg.var triv_unit, Arg.var v_ab, Arg.var v_j, ()))) Blocks.nil)
  fun Js => Expr.jump Js.fst (Arg.var nv, Arg.var nc, Arg.var alen, Arg.var n_units,
    Arg.var abort_in, Arg.imm 0, ())

theorem fid_k6c_inner_loop_wp {Γ : Env} {Q : Post [Ty.bool]} {X : XPost}
    {K284 : Cont [i32, i32, i32, i32, i32, Ty.bool, i32]}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64}
    {tmp wsort tmk scr scr0 : List (BitVec 32)}
    {mv_s mv2 acap_s max_csz o_cl_off o_cl_meta o_cl_aux o_cl_units o_arena : BitVec 32}
    {nv nc alen n_units triv_unit side cnt off mask_off lit : BitVec 32}
    {abort_in second_pass : Bool}
    (hinv : FullDenseInvW c F0 F_cur s)
    (hmv_lo : 256 ≤ mv_s.toNat) (hmv_hi : mv_s.toNat ≤ 8192)
    (hmv2 : mv2.toNat = 2 * mv_s.toNat)
    (hcap : 4224 + 45 * mv_s.toNat + acap_s.toNat ≤ c.scratch_cap)
    (hmax_csz : max_csz.toNat ≤ c.max_vars ∧ max_csz.toNat ≤ 65535)
    (htmp : tmp.length = c.max_vars) (hwsort : wsort.length = 2 * c.max_vars)
    (htmk : tmk.length = 2 * c.max_vars) (hscr : scr.length = c.scratch_cap)
    (hoff_off : o_cl_off = 4224#32 + 29#32 * mv_s)
    (hoff_meta : o_cl_meta = 4224#32 + 33#32 * mv_s)
    (hoff_aux : o_cl_aux = 4224#32 + 37#32 * mv_s)
    (hoff_units : o_cl_units = 4224#32 + 41#32 * mv_s)
    (hoff_ar : o_arena = 4224#32 + 45#32 * mv_s)
    (hnv_le : nv.toNat ≤ mv_s.toNat) (hnv_cv : nv.toNat ≤ 2 * s.core.cur_vars)
    (hnc_le : nc.toNat ≤ 2 * mv_s.toNat) (hal_le : alen.toNat ≤ acap_s.toNat)
    (hnu_le : n_units.toNat ≤ nc.toNat)
    (htriv : triv_unit ≠ 4294967295#32 → (triv_unit &&& 2047#32).toNat < 2001)
    (hside : side = 0#32 ∨ side = 1#32)
    (hcnt : cnt.toNat ≤ 2001)
    (hoff_val : (side = 0#32 ∧ off = 0#32 ∧ mask_off = 4002#32) ∨
      (side = 1#32 ∧ off = 2001#32 ∧ mask_off = 4066#32))
    (hent : ∀ k < cnt.toNat,
      FullBveEntryOkW F_cur s lit.toNat (scr0[off.toNat + k]?.getD 0#32))
    (htreg : FidK6cTmkReg nv.toNat s.core.cur_vars wsort tmk)
    (hcls : FidK6cClsOk mv_s.toNat nc.toNat alen.toNat n_units.toNat scr)
    (hpre0 : ∀ i, i < 4002 → scr[i]? = scr0[i]?)
    (hpre1 : ∀ i, 4132 ≤ i → i < 4192 → scr[i]? = scr0[i]?)
    (hm : (FullMem c (FidP6Work s tmp wsort tmk scr) ⋆ R) m)
    (hK284 : ∀ (nv'' nc'' alen'' n_units'' triv'' : BitVec 32) (ab'' : Bool)
      (j_out : BitVec 32) (tmp' wsort' tmk' scr' : List (BitVec 32)) (m' : Mem 64),
      tmp'.length = c.max_vars → wsort'.length = 2 * c.max_vars →
      tmk'.length = 2 * c.max_vars → scr'.length = c.scratch_cap →
      nv''.toNat ≤ mv_s.toNat → nv''.toNat ≤ 2 * s.core.cur_vars →
      nc''.toNat ≤ 2 * mv_s.toNat → alen''.toNat ≤ acap_s.toNat →
      n_units''.toNat ≤ nc''.toNat →
      (triv'' ≠ 4294967295#32 → (triv'' &&& 2047#32).toNat < 2001) →
      FidK6cTmkReg nv''.toNat s.core.cur_vars wsort' tmk' →
      FidK6cClsOk mv_s.toNat nc''.toNat alen''.toNat n_units''.toNat scr' →
      (∀ i, i < 4002 → scr'[i]? = scr0[i]?) →
      (∀ i, 4132 ≤ i → i < 4192 → scr'[i]? = scr0[i]?) →
      (FullMem c (FidP6Work s tmp' wsort' tmk' scr') ⋆ R) m' →
      K284 (nv'', nc'', alen'', n_units'', triv'', ab'', j_out, ()) m') :
    wp Γ Q X (fidK6cInnerLoopExpr c mv_s mv2 acap_s max_csz o_cl_off o_cl_meta o_cl_aux
      o_cl_units o_arena nv nc alen n_units triv_unit abort_in side cnt off mask_off lit
      second_pass K284) m := by
  have hmbase : mask_off = 4002#32 ∨ mask_off = 4066#32 := by
    rcases hoff_val with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hoff_bnd : off.toNat + cnt.toNat ≤ 4002 := by
    rcases hoff_val with ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩
    · rw [show (0#32 : BitVec 32).toNat = 0 from rfl]; omega
    · rw [show (2001#32 : BitVec 32).toNat = 2001 from rfl]; omega
  apply wp_loop_inv
    (Inv := fun (pl : Tup Val [i32, i32, i32, i32, Ty.bool, i32]) m1 =>
      ∃ tmp1 wsort1 tmk1 scr1,
        pl.2.2.2.2.2.1.toNat ≤ cnt.toNat ∧
        pl.1.toNat ≤ mv_s.toNat ∧ pl.1.toNat ≤ 2 * s.core.cur_vars ∧
        pl.2.1.toNat ≤ 2 * mv_s.toNat ∧ pl.2.2.1.toNat ≤ acap_s.toNat ∧
        pl.2.2.2.1.toNat ≤ pl.2.1.toNat ∧
        tmp1.length = c.max_vars ∧ wsort1.length = 2 * c.max_vars ∧
        tmk1.length = 2 * c.max_vars ∧ scr1.length = c.scratch_cap ∧
        FidK6cTmkReg pl.1.toNat s.core.cur_vars wsort1 tmk1 ∧
        FidK6cClsOk mv_s.toNat pl.2.1.toNat pl.2.2.1.toNat pl.2.2.2.1.toNat scr1 ∧
        (∀ i, i < 4002 → scr1[i]? = scr0[i]?) ∧
        (∀ i, 4132 ≤ i → i < 4192 → scr1[i]? = scr0[i]?) ∧
        (FullMem c (FidP6Work s tmp1 wsort1 tmk1 scr1) ⋆ R) m1)
    (μ := fun (pl : Tup Val [i32, i32, i32, i32, Ty.bool, i32]) _ =>
      cnt.toNat - pl.2.2.2.2.2.1.toNat)
  · intro J hJ; c0_hsteps
    exact hJ _ _ ⟨tmp, wsort, tmk, scr, Nat.zero_le _, hnv_le, hnv_cv, hnc_le, hal_le, hnu_le,
      htmp, hwsort, htmk, hscr, htreg, hcls, hpre0, hpre1, hm⟩
  · intro J pl m1 ⟨tmp1, wsort1, tmk1, scr1, hj_le, h1, h2, h3, h4, h5,
        htp1, hws1, htm1, hs1, hr1, hc1, hp0, hp1, hm1⟩ hcont
    try dsimp only [Blocks.get, Member.here]
    c0_hsteps_nogrp
    · have hj_lt : pl.2.2.2.2.2.fst.toNat < cnt.toNat := by bv_omega
      have hj1 : (pl.2.2.2.2.2.fst + 1#32).toNat = pl.2.2.2.2.2.fst.toNat + 1 :=
        fid_k6c_add1_toNat hj_lt (by omega)
      exact hK284 pl.fst pl.snd.fst pl.snd.snd.fst pl.snd.snd.snd.fst triv_unit
        pl.snd.snd.snd.snd.fst pl.2.2.2.2.2.fst tmp1 wsort1 tmk1 scr1 m1 htp1 hws1 htm1 hs1
        h1 h2 h3 h4 h5 htriv hr1 hc1 hp0 hp1 hm1
    · have hj_lt : pl.2.2.2.2.2.fst.toNat < cnt.toNat := by bv_omega
      have hj1 : (pl.2.2.2.2.2.fst + 1#32).toNat = pl.2.2.2.2.2.fst.toNat + 1 :=
        fid_k6c_add1_toNat hj_lt (by omega)
      apply wp_unroll_group
      intro Js_493 hJs_493
      have hJ493 : ∀ idx : BitVec 32, idx.toNat < cnt.toNat → Js_493 (idx, ()) m1 := by
        intro idx hidx_lt
        apply hJs_493; try dsimp only [Blocks.get, Member.here]
        c0_hsteps_nogrp
        apply wp_unroll_group
        intro Js_497 hJs_497
        have hJ497 : Js_497 () m1 := by
          apply hJs_497; try dsimp only [Blocks.get, Member.here]
          have hscr_off : (BitVec.setWidth 64 (off + idx)).toNat < scr1.length := by
            rw [fid_zext32_toNat]
            have : (off + idx).toNat = off.toNat + idx.toNat := by
              rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
            omega
          have hscr_off' : (BitVec.setWidth 64 (off + idx)).toNat % 2 ^ 64 <
              (FidP6Work s tmp1 wsort1 tmk1 scr1).scratch.scratch_buf.length := by
            dsimp only [FidP6Work]
            have := BitVec.isLt (BitVec.setWidth 64 (off + idx))
            rw [Nat.mod_eq_of_lt (by omega)]; exact hscr_off
          c0_hsteps_nogrp
          apply wp_unroll_group
          intro Js_506 hJs_506
          have hJ506 : ∀ nv'' nc'' alen'' n_units'' triv'' ab''
              tmp' wsort' tmk' scr' m',
              tmp'.length = c.max_vars → wsort'.length = 2 * c.max_vars →
              tmk'.length = 2 * c.max_vars → scr'.length = c.scratch_cap →
              nv''.toNat ≤ mv_s.toNat → nv''.toNat ≤ 2 * s.core.cur_vars →
              nc''.toNat ≤ 2 * mv_s.toNat → alen''.toNat ≤ acap_s.toNat →
              n_units''.toNat ≤ nc''.toNat →
              (triv'' ≠ 4294967295#32 → (triv'' &&& 2047#32).toNat < 2001) →
              FidK6cTmkReg nv''.toNat s.core.cur_vars wsort' tmk' →
              FidK6cClsOk mv_s.toNat nc''.toNat alen''.toNat n_units''.toNat scr' →
              (∀ i, i < 4002 → scr'[i]? = scr0[i]?) →
              (∀ i, 4132 ≤ i → i < 4192 → scr'[i]? = scr0[i]?) →
              (FullMem c (FidP6Work s tmp' wsort' tmk' scr') ⋆ R) m' →
              Js_506 (nv'', nc'', alen'', n_units'', triv'', ab'', ()) m' := by
            intro nv'' nc'' alen'' n_units'' triv'' ab'' tmp' wsort' tmk' scr' m'
              ht' hw' hm' hs' j1 j2 j3 j4 j5 _ jr' jc' q0 q1 qm
            apply hJs_506; try dsimp only [Blocks.get, Member.here]
            exact hcont (nv'', nc'', alen'', n_units'', ab'', pl.2.2.2.2.2.fst + 1#32, ()) m'
              (by dsimp only; rw [hj1]; omega)
              ⟨tmp', wsort', tmk', scr', by dsimp only; rw [hj1]; omega,
                j1, j2, j3, j4, j5, ht', hw', hm', hs', jr', jc', q0, q1, qm⟩
          clear hJs_506
          have heid_ok := fid_k6c_eid_bits hside (by omega : idx.toNat < 2001)
          have hidx_eq : (BitVec.setWidth 64 (off + idx)).toNat = off.toNat + idx.toNat := by
            rw [fid_zext32_toNat, BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
          have hent_w : FullBveEntryOkW F_cur s lit.toNat (scr1[off.toNat + idx.toNat]'
              (by omega)) := by
            have h0 := hent idx.toNat hidx_lt
            have hg : scr1[off.toNat + idx.toNat]? = scr0[off.toNat + idx.toNat]? :=
              hp0 (off.toNat + idx.toNat) (by omega)
            rw [← hg, List.getElem?_eq_getElem (by omega), Option.getD_some] at h0
            exact h0
          have hent_w' : FullBveEntryOkW F_cur s lit.toNat
              (scr1[(BitVec.setWidth 64 (off + idx)).toNat]'hscr_off) := by
            simpa only [hidx_eq] using hent_w
          have hoidx : (off.toNat + idx.toNat) % 2 ^ 32 =
              (BitVec.setWidth 64 (off + idx)).toNat := by
            rw [fid_zext32_toNat, BitVec.toNat_add]
          c0_hsteps_nogrp
          · exact fid_k6c_bin_branch_wp hinv hmv_lo hmv_hi hmv2 hcap htp1 hws1 htm1 hs1
              hoff_off hoff_meta hoff_aux hoff_units hoff_ar h1 h2 h3 h4 h5 htriv
              ⟨heid_ok.1, by rw [heid_ok.2.2.2]; exact Nat.lt_of_lt_of_le hidx_lt hcnt⟩
              hr1 hc1 hp0 hp1 hent_w'
              (by have hc' := hc; simp only [hoidx] at hc'; exact hc')
              hm1
              (fun a b d e f g t' w' tk' s' m' hta hwa hma hsa ha hb hd he hf hg hr hc' p0 p1 hm' =>
                hK284 a b d e f g (pl.2.2.2.2.2.fst + 1#32) t' w' tk' s' m'
                  hta hwa hma hsa ha hb hd he hf hg hr hc' p0 p1 hm')
              hJ506
          · exact fid_k6c_large_branch_wp hinv hmv_lo hmv_hi hmv2 hcap hmax_csz htp1 hws1 htm1 hs1
              hoff_off hoff_meta hoff_aux hoff_units hoff_ar h1 h2 h3 h4 h5 htriv
              ⟨heid_ok.1, by rw [heid_ok.2.2.2]; exact Nat.lt_of_lt_of_le hidx_lt hcnt⟩
              hr1 hc1 hp0 hp1 hent_w'
              (by have hc' := hc; simp only [hoidx] at hc'; exact hc')
              hm1
              (fun a b d e f g t' w' tk' s' m' hta hwa hma hsa ha hb hd he hf hg hr hc' p0 p1 hm' =>
                hK284 a b d e f g (pl.2.2.2.2.2.fst + 1#32) t' w' tk' s' m'
                  hta hwa hma hsa ha hb hd he hf hg hr hc' p0 p1 hm')
              hJ506
        clear hJs_497
        cases second_pass
        · c0_hsplit; exact hJ497
        · c0_hsplit
          · have mw := fid_k6c_mask_widx hmbase (by omega : idx.toNat < 2001)
            have hscr_m : (BitVec.setWidth 64 (mask_off + idx >>> 5)).toNat < scr1.length := by
              rw [fid_zext32_toNat]; omega
            c0_hsteps
            · exact hcont (pl.fst, pl.snd.fst, pl.snd.snd.fst, pl.snd.snd.snd.fst,
                pl.snd.snd.snd.snd.fst, pl.2.2.2.2.2.fst + 1#32, ()) m1
                (by dsimp only; rw [hj1]; omega)
                ⟨tmp1, wsort1, tmk1, scr1, by dsimp only; rw [hj1]; omega,
                  h1, h2, h3, h4, h5, htp1, hws1, htm1, hs1, hr1, hc1, hp0, hp1, hm1⟩
            · exact hJ497
          · cases hc
      clear hJs_493
      cases second_pass
      · c0_hsplit; c0_hsteps
        exact hJ493 pl.2.2.2.2.2.fst hj_lt
      · c0_hsplit
        · c0_hsteps
          exact hJ493 (cnt - 1#32 - pl.2.2.2.2.2.fst) (by bv_omega)
        · cases hc
    · exact hK284 pl.fst pl.snd.fst pl.snd.snd.fst pl.snd.snd.snd.fst triv_unit
        pl.snd.snd.snd.snd.fst pl.2.2.2.2.2.fst tmp1 wsort1 tmk1 scr1 m1 htp1 hws1 htm1 hs1
        h1 h2 h3 h4 h5 htriv hr1 hc1 hp0 hp1 hm1

end

end LeanQbe.T.Examples.Kissat.Proof.Definition
