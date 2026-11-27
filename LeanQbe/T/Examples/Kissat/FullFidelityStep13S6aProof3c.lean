/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S6aLiftsSpec
public import LeanQbe.T.Examples.Kissat.FullFidelityBacktrackCs
public import LeanQbe.T.Examples.Kissat.FullFidelityStep11ProofAnalyze
public import LeanQbe.T.Examples.Kissat.FullSpec
import LeanQbe.T.Examples.Kissat.FullFidelityStep13S6aProof3c0
import LeanQbe.T.Examples.Kissat.FullFidelityBacktrackCsProof0
import LeanQbe.T.Examples.Kissat.FullM6HdrProof0
import LeanQbe.T.Examples.Kissat.FullM6OrchProof0
import LeanQbe.T.Examples.Kissat.FullAnalyzeLemmas1
import LeanQbe.T.Examples.Kissat.FullAnalyzeLemmas2
import LeanQbe.T.Examples.Kissat.FullDeduce1UipLemmas1
import LeanQbe.T.Examples.Kissat.FullM6ProofUtil
import LeanQbe.T.Flat
import LeanQbe.T.FlatLemmas
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.ControlComb
import LeanQbe.T.Logic.MemLemmas
import LeanQbe.T.WPLemmas
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Wave-4F Step-13 Callee-Parametric WP Lifts — Part 3c
(`full_deduce_1uip_m6_hdr_step13_wp`)
Adapts `FullFidelityBacktrackCsProof` Sections 2–3 over `FullFidelityStep13S6aProof3c0`
(`min_clr'` via `s6aFidAnalyzeRsnSpec`) and `step13OtfsLargeSpec` (`flags'`) to certify
`FullFidelityBacktrackCs.fid11Deduce1uipM6HdrFn.body` against `s11Deduce1uipHdrSpec`
over `step13AnalyzeRsnHdrSpec` and `step13OtfsLargeSpec`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep13S6a
open Std Std.Sat Std.ExtHashMap LeanQbe.T LeanQbe.T.ProofUtil LeanQbe.T.C0Step
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullAnalyzeTactics
open LeanQbe.T.Examples.Kissat.Full.FullAnalyzeHelpers
open LeanQbe.T.Examples.Kissat.FullM6Hdr LeanQbe.T.Examples.Kissat.FullM6Orch
open LeanQbe.T.Examples.Kissat.FullM6ProofUtil LeanQbe.T.Examples.Kissat.FullFidelityBacktrackCs
open scoped LeanQbe.T.Examples.Kissat.Full.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.Full.FullAnalyzeTactics
open scoped LeanQbe.T.Examples.Kissat.Full.Deduce1UipTactics
open Kraken.Bedrock2.Test

private theorem s6aFidAnalyzeRsnSpec_monoX {a m Q X₁ X₂}
    (h : s6aFidAnalyzeRsnSpec a m Q X₁) : s6aFidAnalyzeRsnSpec a m Q X₂ := by
  rcases s6aFidAnalyzeRsnSpec_elim h with
    ⟨c, F0, F_cur, cut, s, R, h1, h2, h3, h4, h5, h6, h7, h8, hQ⟩
  exact s6aFidAnalyzeRsnSpec_intro h1 h2 h3 h4 h5 h6 h7 h8 hQ
private structure s6aFidCoreHyps (Γ : Env) : Prop where
  alit : ∀ a m Q X, Full.fullAnalyzeLitSpec a m Q X →
    Γ "full_analyze_lit" [i64, i32, i32] [.bool] a m Q X
  arsn : ∀ a m Q X, s6aFidAnalyzeRsnSpec a m Q X →
    Γ "full_analyze_rsn" [i64, i32, i32] [.bool] a m Q X
  clear : ∀ a m Q X, Full.fullClearAnaSpec a m Q X → Γ "full_clear_ana" [i64] [] a m Q X
  otfsLarge : ∀ a m Q X, step13OtfsLargeSpec a m Q X →
    Γ "full_otfs_large" [i64, i32, i32] [.bool] a m Q X
  otfsBin : ∀ a m Q X, Full.fullOtfsBinSpec a m Q X →
    Γ "full_otfs_bin" [i64, i32, i32] [.bool] a m Q X
  otfsSub : ∀ a m Q X, Full.fullOtfsSubsumeSpec a m Q X →
    Γ "full_otfs_subsume" [i64, i32, i64, i64, .bool] [] a m Q X
private abbrev rL {ts rs : List Ty} (op : OpCode ts rs) (args : Tup (Arg Val) ts)
    (k : Tup Val rs → Expr Val Cont [i64]) : Expr Val Cont [i64] :=
  Expr.let_ { sig := ts, code := op, args := args } k
private abbrev rA64 (a b : Arg Val i64) := rL (OpCode.add i64) (a, b, ())
private abbrev rS64 (a b : Arg Val i64) := rL (OpCode.sub i64) (a, b, ())
private abbrev rM64 (a b : Arg Val i64) := rL (OpCode.mul i64) (a, b, ())
private abbrev rZ32 (a : Arg Val i32) := rL (OpCode.zext 32 64) (a, ())
private abbrev rN32 (a b : Arg Val i32) := rL (OpCode.and i32) (a, b, ())
private abbrev rC32 (op : CmpOp) (a b : Arg Val i32) :=
  rL (OpCode.cmp op i32 Ty.bool rfl) (a, b, ())
private abbrev rC64 (op : CmpOp) (a b : Arg Val i64) :=
  rL (OpCode.cmp op i64 Ty.bool rfl) (a, b, ())
private abbrev rFld (hdr off : BitVec 64) (k : Val i64 → Expr Val Cont [i64]) :
    Expr Val Cont [i64] :=
  rA64 (Arg.var hdr) (Arg.imm off) fun p => Expr.load i64 (Arg.var p.fst) k
private abbrev rStoreFld (hdr off : BitVec 64) (v : Arg Val i64)
    (k : Expr Val Cont [i64]) : Expr Val Cont [i64] :=
  rA64 (Arg.var hdr) (Arg.imm off) fun p => Expr.store v (Arg.var p.fst) k
private abbrev rSkipJump (outerJs : Cont []) (k : Tup Cont [[]] → Expr Val Cont [i64]) :
    Expr Val Cont [i64] :=
  Expr.group (fun _ => Blocks.cons (ts := []) (fun _ => Expr.jump outerJs ()) Blocks.nil) k
private abbrev rDecCnt (outerJs : Cont []) (hdr off : BitVec 64) : Expr Val Cont [i64] :=
  rSkipJump outerJs fun Js => rFld hdr off fun ld =>
    rC64 CmpOp.ugt (Arg.var ld) (Arg.imm 0) fun p => Expr.jnz (Arg.var p.fst)
      (rFld hdr off fun ld => rS64 (Arg.var ld) (Arg.imm 1) fun p =>
        rStoreFld hdr off (Arg.var p.fst) (Expr.jump Js.fst ()))
      (Expr.jump Js.fst ())
private abbrev rSubBlk (c : FullCfg) (rsn_arg : Arg Val i32)
    (resolved_v init_rsz ld ld_3 : BitVec 64) (to_bin : Bool) : Expr Val Cont [i64] :=
  Expr.group (fun _ => Blocks.cons (ts := []) (fun _ => rFld c.hdr 272 fun ld =>
    rStoreFld c.hdr 1144 (Arg.var ld)
      (Expr.call (as := [i64]) (bs := []) "full_clear_ana" (Arg.var c.hdr, ()) fun _ =>
        Expr.ret (Arg.imm 2, ()))) Blocks.nil)
    fun Js => rC64 CmpOp.eq (Arg.var resolved_v) (Arg.imm 1) fun p => Expr.jnz (Arg.var p.fst)
      (rFld c.hdr 1144 fun ld_4 => rC64 CmpOp.ult (Arg.var ld_4) (Arg.var init_rsz) fun p =>
        Expr.jnz (Arg.var p.fst)
          (Expr.call (as := [i64, i32, i64, i64, .bool]) (bs := []) "full_otfs_subsume"
            (Arg.var c.hdr, rsn_arg, Arg.var ld, Arg.var ld_3, Arg.imm to_bin, ())
            fun _ => Expr.jump Js.fst ())
          (Expr.jump Js.fst ()))
      (Expr.jump Js.fst ())

private abbrev s6aFidRsnExpr (c : FullCfg) (p_bv rsn : BitVec 32)
    (resolved_v init_rsz : BitVec 64) (J2 : Cont [i64, i32, i64]) : Expr Val Cont [i64] :=
  Expr.call (as := [i64, i32, i32]) (bs := [.bool]) "full_analyze_rsn"
    (Arg.var c.hdr, Arg.var rsn, Arg.var (p_bv >>> 1), ()) fun p =>
    Expr.jnz (Arg.var p.fst)
      (rFld c.hdr 184 fun ld => rFld c.hdr 1144 fun ld_1 =>
        Expr.group (fun _ => Blocks.cons (ts := [i64]) (fun p => rFld c.hdr 1136 fun ld_2 =>
          Expr.group (fun _ => Blocks.cons (ts := []) (fun _ =>
            Expr.jump J2 (Arg.var ld, Arg.imm 4294967295, Arg.var resolved_v, ())) Blocks.nil)
            fun Js => rC64 CmpOp.uge (Arg.var ld_2) (Arg.imm 3) fun p_2 =>
              Expr.jnz (Arg.var p_2.fst)
              (rC64 CmpOp.ult (Arg.var p.fst) (Arg.var ld_2) fun p => Expr.jnz (Arg.var p.fst)
                (rN32 (Arg.var rsn) (Arg.imm 2147483648) fun p =>
                  rC32 CmpOp.eq (Arg.var p.fst) (Arg.imm 0) fun p => Expr.jnz (Arg.var p.fst)
                    (rFld c.hdr 528 fun ld => rFld c.hdr 176 fun ld_3 =>
                      rSkipJump Js.fst fun Js => rC64 CmpOp.eq (Arg.var ld_2) (Arg.imm 3) fun p =>
                        Expr.jnz (Arg.var p.fst)
                          (Expr.call (as := [i64, i32, i32]) (bs := [.bool]) "full_otfs_bin"
                            (Arg.var c.hdr, Arg.var rsn, Arg.var p_bv, ()) fun p =>
                            Expr.jnz (Arg.var p.fst)
                              (rFld c.hdr 112 fun ld_4 => rZ32 (Arg.var rsn) fun p =>
                                rM64 (Arg.var p.fst) (Arg.imm 4) fun p =>
                                rA64 (Arg.var ld_4) (Arg.var p.fst) fun p =>
                                Expr.load i32 (Arg.var p.fst) fun ld_5 =>
                                rN32 (Arg.var ld_5) (Arg.imm 4194304) fun p =>
                                rC32 CmpOp.ne (Arg.var p.fst) (Arg.imm 0) fun p =>
                                Expr.group (fun _ => Blocks.cons (ts := []) (fun _ =>
                                  rSubBlk c (Arg.imm 0) resolved_v init_rsz ld ld_3 true)
                                  Blocks.nil) fun Js => Expr.jnz (Arg.var p.fst)
                                    (rDecCnt Js.fst c.hdr 496) (rDecCnt Js.fst c.hdr 488))
                              (Expr.jump Js.fst ()))
                          (Expr.call (as := [i64, i32, i32]) (bs := [.bool]) "full_otfs_large"
                            (Arg.var c.hdr, Arg.var rsn, Arg.var p_bv, ()) fun p =>
                            Expr.jnz (Arg.var p.fst) (rStoreFld c.hdr 528 (Arg.imm 2)
                              (rZ32 (Arg.var rsn) fun p => rStoreFld c.hdr 176 (Arg.var p.fst)
                                (rSubBlk c (Arg.var rsn) resolved_v init_rsz ld ld_3 false)))
                              (Expr.jump Js.fst ())))
                    (Expr.jump Js.fst ()))
                (Expr.jump Js.fst ()))
              (Expr.jump Js.fst ())) Blocks.nil)
          fun Js => rC64 CmpOp.ugt (Arg.var ld_1) (Arg.imm 0) fun p => Expr.jnz (Arg.var p.fst)
            (rS64 (Arg.var ld_1) (Arg.imm 1) fun p =>
              rStoreFld c.hdr 1144 (Arg.var p.fst) (Expr.jump Js.fst (Arg.var p.fst, ())))
            (Expr.jump Js.fst (Arg.var ld_1, ())))
      (Expr.call (as := [i64]) (bs := []) "full_clear_ana" (Arg.var c.hdr, ()) fun _ =>
        Expr.ret (Arg.imm 0, ()))
private abbrev s6aFidR1Ok (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s s' : FullState) : Prop :=
  Full.FullOtfsInvW c F0 F_cur s' ∧ s'.core.cur_level = s.core.cur_level ∧
  1 ≤ s'.core.tmp_len ∧ s'.core.tmp_len ≤ s'.core.cur_vars ∧
  (List.map (fun x => x.toNat / 2) (List.take s'.core.tmp_len s'.core.tmp)).Nodup ∧
  (∀ k < s'.core.tmp_len, let l := (s'.core.tmp[k]?.getD 0#32).toNat
    l < 2 * s'.core.cur_vars ∧ s'.core.vals[l]?.getD 0#8 = 255#8) ∧
  (∀ k, 1 ≤ k → k < s'.core.tmp_len →
    let lv := (s'.core.lvl[(s'.core.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat
    0 < lv ∧ lv < s'.core.cur_level) ∧
  (s'.core.lvl[(s'.core.tmp[0]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = s'.core.cur_level ∧
  (cnfOfClauses F_cur).EntailsClause
    (cnfClause (List.map BitVec.toNat (List.take s'.core.tmp_len s'.core.tmp)))

private abbrev s6aFidPost (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s : FullState) (R : Mem 64 → Prop) (Q : Post [i64]) : Prop :=
  ∀ r s' m', s'.LengthsOk c → (r = 0#64 ∨ r = 1#64 ∨ r = 2#64 ∨ r = 20#64) →
    s'.core.cur_vars = s.core.cur_vars → s'.core.fuel = s.core.fuel →
    s'.scratch.work_stk2 = s.scratch.work_stk2 →
    (r = 20#64 → F0.Unsat ∧ Full.FullOtfsInvW c F0 F_cur s' ∧
      s'.core.cur_level ≤ s.core.cur_level ∧ s'.core.dense_mode = s.core.dense_mode) →
    (r = 0#64 → Full.FullOtfsInvW c F0 F_cur s') → (r = 1#64 → s6aFidR1Ok c F0 F_cur s s') →
    (r = 2#64 → ∃ cut', cut' ≤ s'.core.trail_end ∧ Full.FullCutInvW c F0 F_cur cut' s' ∧
      s'.core.cur_level = s.core.cur_level ∧ Full.FullConflictOkCut F_cur cut' s') →
    (FullMem c s' ⋆ R) m' → Q (r, ()) m'
private abbrev s6aFidHdrPost (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s : FullState) (R : Mem 64 → Prop) (Q : Post [i64]) : Prop :=
  ∀ (r : BitVec 64) (ext' : List (BitVec 64)) (s' : FullState) (m' : Mem 64),
    M6HdrExtOk ext' → s'.LengthsOk c → (r = 0#64 ∨ r = 1#64 ∨ r = 2#64 ∨ r = 20#64) →
    s'.core.cur_vars = s.core.cur_vars → s'.core.fuel = s.core.fuel →
    s'.scratch.work_stk2 = s.scratch.work_stk2 →
    (r = 20#64 → F0.Unsat ∧ FullOtfsInvW c F0 F_cur s' ∧
      s'.core.cur_level ≤ s.core.cur_level ∧ s'.core.dense_mode = s.core.dense_mode) →
    (r = 0#64 → FullOtfsInvW c F0 F_cur s') → (r = 1#64 → s6aFidR1Ok c F0 F_cur s s') →
    (r = 2#64 → ∃ cut', cut' ≤ s'.core.trail_end ∧ FullCutInvW c F0 F_cur cut' s' ∧
      s'.core.cur_level = s.core.cur_level ∧ FullConflictOkCut F_cur cut' s') →
    (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m'
private abbrev s6aFidJ2Inv (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (cut idx' : Nat) (s : FullState) (R : Mem 64 → Prop) (ys2 : Tup Val [i64, i32, i64])
    (ml : Mem 64) : Prop :=
  ∃ (cut_n res_n : Nat) (sn : FullState),
    ys2.1 = BitVec.ofNat 64 sn.core.tmp_cnt ∧ ys2.2.2.1 = BitVec.ofNat 64 res_n ∧
    idx' + res_n ≤ sn.core.trail_end ∧ Full.FullDeduceStateInv c F0 F_cur cut_n idx' s sn ∧
    0 < sn.core.tmp_cnt ∧
    (res_n = 0 → cut_n = cut ∧ sn.core.confl_type = s.core.confl_type ∧
      sn.core.confl_ref = s.core.confl_ref) ∧ (FullMem c sn ⋆ R) ml
private abbrev s6aFidSeedCore (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (cut : Nat) (s s1 : FullState) : Prop :=
  s1.LengthsOk c ∧ Full.FullWitnessCutInv c F0 F_cur cut s1.core ∧ Full.FullAnaMarksCov c s1 ∧
  Full.FullExtScratchPres s s1 ∧ s1.scratch.work_stk2 = s.scratch.work_stk2 ∧
  Full.FullArenaVarsNodup s1 ∧ Full.fullArenaClauseRefs s1 = Full.fullArenaClauseRefs s ∧
  Full.FullDeduceStaticEq s.core s1.core

private theorem s6a_fid_skip_lit_step {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut cut_cur idx idx' resolved : Nat} {s sl : FullState} {R : Mem 64 → Prop}
    {m_l : Mem 64} {p_bv : BitVec 32} {J2 : Cont [i64, i32, i64]}
    (hJ2 : ∀ ys2 ml, s6aFidJ2Inv c F0 F_cur cut idx' s R ys2 ml → J2 ys2 ml)
    (hidx_res : idx + resolved ≤ sl.core.trail_end) (hhi : idx' + 1 = idx)
    (hp_get : (sl.core.trl[idx']?.getD 0#32).toNat = p_bv.toNat)
    (hstate : Full.FullDeduceStateInv c F0 F_cur cut_cur idx s sl)
    (htc_pos_l : 0 < sl.core.tmp_cnt)
    (hzero : resolved = 0 → cut_cur = cut ∧
      sl.core.confl_type = s.core.confl_type ∧ sl.core.confl_ref = s.core.confl_ref)
    (hnot : ¬ (sl.core.mrk[p_bv.toNat / 2]?.getD 0#8 ≠ 0#8 ∧
      (sl.core.lvl[p_bv.toNat / 2]?.getD 0#32).toNat = sl.core.cur_level))
    (hml : (FullMem c sl ⋆ R) m_l) :
    J2 (BitVec.ofNat 64 sl.core.tmp_cnt, 0xFFFFFFFF#32, BitVec.ofNat 64 resolved, ()) m_l := by
  obtain ⟨hlen_l, hw_l, hcov_l, hext_l, hws2_l, hnd_l, hrefs_l, hstat_l, htl_ge, htl_cv, htc_eq,
    hlow_l, hmcov_l, hcm_l, hent_l, hres_l⟩ := hstate
  have hnot' : ¬ (sl.core.mrk[(sl.core.trl[idx']?.getD 0#32).toNat / 2]?.getD 0#8 ≠ 0#8 ∧
      (sl.core.lvl[(sl.core.trl[idx']?.getD 0#32).toNat / 2]?.getD 0#32).toNat =
        sl.core.cur_level) := by rwa [hp_get]
  refine hJ2 _ m_l ⟨cut_cur, resolved, sl, rfl, rfl, by omega,
    ⟨hlen_l, hw_l, hcov_l, hext_l, hws2_l, hnd_l, hrefs_l, hstat_l, htl_ge, htl_cv,
      by rw [htc_eq, show idx = idx' + 1 from hhi.symm, Full.fullCurTrailIdxs_succ_eq_self hnot'],
      hlow_l, hmcov_l, fun j hj => hcm_l j (by omega),
      by simpa only [Full.fullActiveResolvent, show idx = idx' + 1 from hhi.symm,
        Full.fullCurLits_succ_eq_self hnot'] using hent_l,
      hres_l⟩, htc_pos_l, hzero, hml⟩
private theorem s6a_fid_deduce_loop_rsn_wp {Γ : Env} (hΓ : s6aFidCoreHyps Γ)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {cut cut_cur idx idx' resolved : Nat}
    {s sl sl1 sl2 : FullState} {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost} {m : Mem 64}
    {p_bv rsn rsn_raw : BitVec 32} {init_res_sz : BitVec 64} {J2 : Cont [i64, i32, i64]}
    (hw0 : Full.FullWitnessCutInv c F0 F_cur cut s.core) (hcur_pos : 0 < s.core.cur_level)
    (hconfl : Full.FullConflictOkCut F_cur cut s) (hext0 : Full.FullExtScratchOk c s)
    (hdm0 : s.core.dense_mode = 0#64) (hlm0 : Full.FullLitMarksClear c s)
    (hQ : s6aFidPost c F0 F_cur s R Q)
    (hJ2 : ∀ ys2 ml, s6aFidJ2Inv c F0 F_cur cut idx' s R ys2 ml → J2 ys2 ml)
    (hidx_res : idx + resolved ≤ sl.core.trail_end) (hhi : idx' + 1 = idx)
    (hcv_le_l : sl.core.cur_vars ≤ c.max_vars)
    (hstate : Full.FullDeduceStateInv c F0 F_cur cut_cur idx s sl)
    (hzero : resolved = 0 → cut_cur = cut ∧
      sl.core.confl_type = s.core.confl_type ∧ sl.core.confl_ref = s.core.confl_ref)
    (hiu_te : idx' < sl.core.trail_end) (hp_lt : p_bv.toNat < 2 * sl.core.cur_vars)
    (hp_get : (sl.core.trl[idx']?.getD 0#32).toNat = p_bv.toNat)
    (hmnz : sl.core.mrk[p_bv.toNat / 2]?.getD 0#8 ≠ 0#8)
    (hpl_cl : (sl.core.lvl[p_bv.toNat / 2]?.getD 0#32).toNat = sl.core.cur_level)
    (htc1_pos : 0 < sl.core.tmp_cnt - 1) (hiu_cut : idx' < cut_cur)
    (hr_get : sl.core.rsns[p_bv.toNat / 2]?.getD 0xFFFFFFFF#32 = rsn)
    (hrsn_raw : rsn_raw = rsn) (hres1_lt64 : resolved + 1 < 2 ^ 64)
    (hsl1_eq : sl1 = { sl with core := { sl.core with tmp_cnt := sl.core.tmp_cnt - 1 } })
    (hsl2_eq : sl2 = { sl1 with scratch := { sl1.scratch with ant_sz := 0#64 } })
    (hlen_2 : sl2.LengthsOk c) (hw_2 : Full.FullWitnessCutInv c F0 F_cur cut_cur sl2.core)
    (hcov_2 : Full.FullAnaMarksCov c sl2) (hext_2 : Full.FullExtScratchPres s sl2)
    (hstat_2 : Full.FullDeduceStaticEq s.core sl2.core)
    (hrsn_ref : rsn ≠ 0xFFFFFFFF#32 → (rsn &&& 0x80000000#32) = 0#32 →
      rsn.toNat ∈ Full.fullArenaClauseRefs sl2)
    (hres_add1 : BitVec.ofNat 64 resolved + 1#64 = BitVec.ofNat 64 (resolved + 1))
    (htc2_eq : sl2.core.tmp_cnt = (Full.fullCurTrailIdxs sl2.core sl2.core.mrk idx').length)
    (hent_2 : (cnfOfClauses F_cur).EntailsClause
      (cnfClause (Full.fullActiveResolvent sl2.core sl2.core.tmp sl2.core.mrk
        sl2.core.tmp_len (idx' + 1))))
    (hsl2_res : sl2.scratch.res_sz =
      BitVec.ofNat 64 ((sl2.core.tmp_len - 1) + sl2.core.tmp_cnt + 1))
    (hm : (FullMem c sl2 ⋆ R) m) :
    wp Γ Q X (s6aFidRsnExpr c p_bv rsn_raw (BitVec.ofNat 64 resolved + 1#64) init_res_sz J2) m := by
  subst rsn_raw; have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
  obtain ⟨hlen_l, hw_l, _, _, hws2_l, hnd_l, hrefs_l, hstat_l, htl_ge, htl_cv,
    htc_eq, hlow_l, hmcov_l, hcm_l, hent_l, _⟩ := hstate
  subst hsl2_eq hsl1_eq; let sl_sub : FullState :=
    { sl with core := { sl.core with tmp_cnt := sl.core.tmp_cnt - 1 },
              scratch := { sl.scratch with ant_sz := 0#64 } }
  have htl_cv2 : sl_sub.core.tmp_len ≤ sl_sub.core.cur_vars := htl_cv
  have htc_sum2 : sl_sub.core.tmp_cnt + sl_sub.core.cur_vars + 1 < 2 ^ 64 := by
    have hact_le : (sl.core.tmp_len - 1) + sl.core.tmp_cnt ≤ sl.core.cur_vars := by
      have := Full.fullActiveResolvent_le_cur_vars (by omega : idx ≤ sl.core.trail_end)
        htl_ge (by rw [hlen_l.core_ok.tmp_len_arr]; exact Nat.le_trans htl_cv hcv_le_l)
        hlow_l hw_l.trail_lits_lt hw_l.trail_vars_nodup
      rwa [← htc_eq] at this
    dsimp only [sl_sub]; omega
  dsimp only [s6aFidRsnExpr, rSubBlk, rDecCnt, rSkipJump, rFld, rStoreFld, rC32, rC64,
    rN32, rZ32, rM64, rS64, rA64, rL]
  refine wp_call_of_spec _ _ (hΓ.arsn (c.hdr, rsn, p_bv >>> 1#32, ()) _ _ _
    (s6aFidAnalyzeRsnSpec_intro rfl hlen_2 hw_2 hcov_2 htl_cv2
      htc_sum2 (fun hne hlg => hrsn_ref hne hlg) hm ?_))
  intro ok2 mrk2 tmp2 tc2 tl2 mclr2 mcl2 arena2 sc2 m2 _ hlen2 hw2 hcov2 hext2 hws2_2
  intro htl2_ge htl2_cv htc2_ge hrefs2 hprops2 hmp2 htp2 hnm2 hnt2 hnd2_t hcnt2 hres2 hok2 hm2
  dsimp only at hlen2 hw2 hcov2 hext2 hws2_2 htl2_ge htl2_cv htc2_ge
  dsimp only at hrefs2 hprops2 hmp2 htp2 hnm2 hnt2 hnd2_t hcnt2 hres2 hok2 hm2
  let s2_sem : FullState :=
    { sl with
      core := { sl.core with mrk := mrk2, tmp := tmp2, tmp_cnt := tc2, tmp_len := tl2,
                             min_clr_len := mcl2, arena := arena2 },
      scratch := sc2 }
  let s2 : FullState := { s2_sem with core := { s2_sem.core with min_clr := mclr2 } }
  have hnd2 : Full.FullArenaVarsNodup s2 := fun r hr hngr => by
    change r ∈ Full.fullArenaClauseRefs s2 at hr; rw [hrefs2] at hr
    have hll := hprops2 r hr; change ((Full.fullArenaClauseLits s2 r).map (· / 2)).Nodup
    rw [hll.2.2]; refine hnd_l r hr ?_
    unfold Full.fullArenaClauseGarb Full.fullArenaClauseGarbCore
      Full.fullArenaHdrCore at hll hngr ⊢
    rw [← hll.2.1]; exact hngr
  have hext_s2 : Full.FullExtScratchPres s s2 := Full.fullExtScratchPres_trans hext_2 hext2
  have hrefs_s2 : Full.fullArenaClauseRefs s2 = Full.fullArenaClauseRefs s := hrefs2.trans hrefs_l
  have hstat_s2 : Full.FullDeduceStaticEq s.core s2.core :=
    ⟨hstat_2.1, hstat_2.2, hstat_2.3, hstat_2.4, hstat_2.5, hstat_2.6, hstat_2.7,
     hstat_2.8, hstat_2.9, hstat_2.10⟩
  cases ok2 with
  | false =>
    fa_fast_steps
    exact fid_deduce_clear_ret0_wp hΓ.clear hQ hlen2 hw2 hcov2 hext0 hext_s2
      (hws2_2.trans hws2_l) hnd2 hrefs_s2 hstat_s2 hdm0 hlm0 hm2
  | true =>
    have hskip_pv : (p_bv >>> 1#32).toNat = p_bv.toNat / 2 := bv32_lshr_1 p_bv
    obtain ⟨hok_ne, hok_ant, hok_lits⟩ := hok2 rfl
    have hlen2_s : s2_sem.LengthsOk c :=
      ⟨{ hlen2.core_ok with min_clr_len_arr := hlen_2.core_ok.min_clr_len_arr }, hlen2.scratch_ok⟩
    have hw2_s : Full.FullWitnessCutInv c F0 F_cur cut_cur s2_sem.core :=
      s6a_fid_witness_with_min_clr hw2 sl.core.min_clr
    have hcov2_s : Full.FullAnaMarksCov c s2_sem := fid_anaMarksCov_of_same hcov2 rfl rfl rfl rfl
    have hnd2_s : Full.FullArenaVarsNodup s2_sem := hnd2
    have hsem2 := Full.deduce_loop_rsn_sem hlen_2 hw_2 hstat_2 hsl2_res htl_ge
      htc2_eq hlow_l hmcov_l (fun j hj => hcm_l j (by omega)) hent_2 hiu_cut hiu_te
      hp_get hr_get hmnz hpl_cl hw2_s hlen2_s hcov2_s hext2 hws2_2 htl2_ge htl2_cv
      htc2_ge hrefs2 hnd2_s
      (fun w hw hnz => hmp2 w (Nat.lt_of_lt_of_le hw hcv_le_l) hnz) htp2
      (fun w hw h0 hnz => by
        obtain ⟨l, hl, h1, _, hsk, h3, h4⟩ := hnm2 w (Nat.lt_of_lt_of_le hw hcv_le_l) h0 hnz
        exact ⟨l, hl, h1, hskip_pv ▸ hsk, h3, h4⟩)
      (fun j hj1 hj2 => by
        obtain ⟨h1, h2, hsk, h4⟩ := hnt2 j hj1 hj2
        exact ⟨h1, h2, hskip_pv ▸ hsk, h4⟩)
      hnd2_t hcnt2 hres2
      ⟨hok_ne, fun l hl => by
        obtain ⟨hl_lt, hl_r⟩ := hok_lits l hl
        exact ⟨hl_lt, fun hne => hl_r (hskip_pv ▸ hne)⟩⟩
      hext_2 hws2_l hrefs_l
    obtain ⟨hlen_s2, hw_s2, hcov_s2, hext_s2', hws2_s2, hnd_s2, hrefs_s2',
      hstat_s2', htl2_1, htl2_cv', htc2_eq', hlow2, hmcov2, hcm2, hent2, hres2_eq,
      hall_mrk⟩ := hsem2
    have htc2_pos : 0 < tc2 := Nat.lt_of_lt_of_le htc1_pos htc2_ge
    have htc2_eq_sl : tc2 = (Full.fullCurTrailIdxs sl.core mrk2 idx').length := htc2_eq'
    have hres2_sum : (tl2 - 1) + tc2 + 1 < 2 ^ 64 := by
      have := Full.fullActiveResolvent_le_cur_vars (Nat.le_of_lt hiu_te) htl2_1
        (by rw [hlen_s2.core_ok.tmp_len_arr]
            exact Nat.le_trans htl2_cv' hcv_le_l)
        hlow2 hw_s2.trail_lits_lt hw_s2.trail_vars_nodup
      rw [← htc2_eq_sl] at this; omega
    have hres2_pos : (0#64 : BitVec 64).ult sc2.res_sz = true := by
      rw [hres2_eq]; simp only [BitVec.ult, decide_eq_true_eq,
        show (0#64 : BitVec 64).toNat = 0 from rfl, bv64_ofNat_toNat hres2_sum]
      omega
    let s3 : FullState :=
      { s2 with
        scratch := { s2.scratch with res_sz := BitVec.ofNat 64 ((tl2 - 1) + tc2) } }
    have hs3_res_bv : sc2.res_sz - 1#64 = BitVec.ofNat 64 ((tl2 - 1) + tc2) := by
      rw [hres2_eq]; apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_sub, bv64_ofNat_toNat hres2_sum,
        show (1#64 : BitVec 64).toNat = 1 from rfl,
        bv64_ofNat_toNat (by omega : (tl2 - 1) + tc2 < 2 ^ 64)]
      omega
    let s3_sem : FullState := { s2_sem with scratch := s3.scratch }
    have hst_s3_sem : Full.FullDeduceStateInv c F0 F_cur cut_cur idx' s s3_sem :=
      ⟨⟨hlen_s2.core_ok, { hlen_s2.scratch_ok with }⟩, hw_s2, hcov_s2, hext_s2',
       hws2_s2, hnd_s2, hrefs_s2', hstat_s2', htl2_1, htl2_cv', htc2_eq', hlow2,
       hmcov2, hcm2, hent2, rfl⟩
    have hlen_s3 : s3.LengthsOk c := ⟨hlen2.core_ok, { hlen_s2.scratch_ok with }⟩
    have hw_s3 : Full.FullWitnessCutInv c F0 F_cur cut_cur s3.core := hw2
    have hcov_s3 : Full.FullAnaMarksCov c s3 := hcov2
    have hext_s3 : Full.FullExtScratchPres s s3 := hext_s2'
    have hrefs_s3 : Full.fullArenaClauseRefs s3 = Full.fullArenaClauseRefs s := hrefs_s2'
    have hstat_s3 : Full.FullDeduceStaticEq s.core s3.core :=
      ⟨hstat_s2'.1, hstat_s2'.2, hstat_s2'.3, hstat_s2'.4, hstat_s2'.5,
       hstat_s2'.6, hstat_s2'.7, hstat_s2'.8, hstat_s2'.9, hstat_s2'.10⟩
    have hst_s3 : Full.FullDeduceStateInv c F0 F_cur cut_cur idx' s s3 :=
      s6a_fid_state_with_min_clr hst_s3_sem hlen_s3 hw_s3 hcov_s3 rfl rfl
    fa_fast_steps_nogrp
    refine wp_join_group (ts := [i64]) (fun (rsz_v, ()) ml =>
      rsz_v = s3.scratch.res_sz ∧ (FullMem c s3 ⋆ R) ml)
      (fun _ ⟨rsz_v, ⟨⟩⟩ ml ⟨hrsz_eq, hm3⟩ => ?_) ?_
    · subst hrsz_eq
      fa_fast_steps_nogrp
      refine wp_join_group (ts := []) (fun _ ml =>
        ∃ (cut_n : Nat) (s_n : FullState), idx' + (resolved + 1) ≤ s_n.core.trail_end ∧
          Full.FullDeduceStateInv c F0 F_cur cut_n idx' s s_n ∧
          s_n.core.tmp_cnt = tc2 ∧ 0 < s_n.core.tmp_cnt ∧ (FullMem c s_n ⋆ R) ml)
        (fun _ ⟨⟩ ml ⟨cut_n, s_n, hir_n, hst_n, htc_eq_n, htc_n, hmn⟩ => by
          fa_fast_steps
          exact hJ2 (BitVec.ofNat 64 tc2, 0xFFFFFFFF#32, BitVec.ofNat 64 resolved + 1#64, ()) _
            ⟨cut_n, resolved + 1, s_n, by rw [htc_eq_n], hres_add1, hir_n, hst_n,
             htc_n, fun h => by omega, hmn⟩) ?_
      intro J_ot hJot
      have hir3 : idx' + (resolved + 1) ≤ s3.core.trail_end := by
        rw [hstat_s3.te, ← hstat_l.te]; omega
      fa_fast_steps_nogrp
      · have hrsn_lg : (rsn &&& 0x80000000#32) = 0#32 := by assumption
        have hant_pos_nat : 3 ≤ sc2.ant_sz.toNat := by
          have h0 : 3 % 2 ^ 64 ≤ s3.scratch.ant_sz.toNat := by assumption
          simpa [s3] using h0
        have hres_ult : s3.scratch.res_sz.ult sc2.ant_sz = true := by
          have h0 : s3.scratch.res_sz.toNat < s3.scratch.ant_sz.toNat := by assumption
          simpa only [BitVec.ult, decide_eq_true_eq, s3] using h0
        refine wp_join_group (ts := []) (fun _ ml =>
          ∃ (cut_n : Nat) (s_n : FullState), idx' + (resolved + 1) ≤ s_n.core.trail_end ∧
            Full.FullDeduceStateInv c F0 F_cur cut_n idx' s s_n ∧
            s_n.core.tmp_cnt = tc2 ∧ 0 < s_n.core.tmp_cnt ∧ (FullMem c s_n ⋆ R) ml)
          (fun _ ⟨⟩ ml h => hJot () ml h) ?_
        intro J_in hJin
        have hri2 := hw_s3.reason_inv_cut idx' hiu_cut; dsimp only at hri2
        have hp_get_s2 : (s2.core.trl[idx']?.getD 0#32).toNat = p_bv.toNat := by
          rw [hstat_s2'.trl, ← hstat_l.trl, hp_get]
        have hr_get_s2 : s2.core.rsns[p_bv.toNat / 2]?.getD 0xFFFFFFFF#32 = rsn := by
          rw [hstat_s2'.rsns, ← hstat_l.rsns, hr_get]
        rw [hp_get_s2, hr_get_s2] at hri2
        have hri2 := hri2 hok_ne; rw [ite_eq_right (fun h => absurd hrsn_lg h)] at hri2
        obtain ⟨href_s2, hng_s2, _⟩ := hri2
        have hte_s3 : idx' < s3.core.trail_end := by rw [hstat_s3.te, ← hstat_l.te]; exact hiu_te
        have hpl_s3 : (s3.core.lvl[p_bv.toNat / 2]?.getD 0#32).toNat = s3.core.cur_level := by
          rw [hstat_s3.lvl, hstat_s3.cl, ← hstat_l.lvl, ← hstat_l.cl, hpl_cl]
        have hcl_s3_pos : 0 < s3.core.cur_level := by rw [hstat_s3.cl]; exact hcur_pos
        have hp_lt_s3 : p_bv.toNat < 2 * s3.core.cur_vars := by
          rw [hstat_s3.cv, ← hstat_l.cv]; exact hp_lt
        have heq_s2 : Full.fullArenaClauseLits s2 rsn.toNat = Full.fullRsnLits sl_sub rsn := by
          have hll := (hprops2 rsn.toNat (hrefs_l ▸ (hrsn_ref hok_ne hrsn_lg))).2.2
          change Full.fullArenaClauseLits s2 rsn.toNat =
            Full.fullArenaClauseLits sl_sub rsn.toNat at hll
          unfold Full.fullRsnLits; rw [ite_eq_right (fun h => hok_ne h),
            ite_eq_right (fun h => absurd hrsn_lg h)]
          exact hll
        have hant_s2 : sc2.ant_sz = BitVec.ofNat 64
            ((Full.fullRsnLits s2 rsn).countP fun l =>
            decide (l / 2 < s2.core.cur_vars ∧ 0 < (s2.core.lvl[l / 2]?.getD 0#32).toNat ∧
              (s2.core.lvl[l / 2]?.getD 0#32).toNat ≤ s2.core.cur_level)) := by
          have heq_r : Full.fullRsnLits s2 rsn = Full.fullRsnLits sl_sub rsn := by
            unfold Full.fullRsnLits; rw [ite_eq_right (fun h => hok_ne h),
              ite_eq_right (fun h => absurd hrsn_lg h)]
            exact heq_s2
          simpa only [heq_r, BitVec.zero_add] using hok_ant
        have hall_s3 : ∀ l ∈ Full.fullArenaClauseLitsCore s3.core rsn.toNat,
            l / 2 ≠ p_bv.toNat / 2 → 0 < (s3.core.lvl[l / 2]?.getD 0#32).toNat →
            mrk2[l / 2]?.getD 0#8 ≠ 0#8 := by
          intro l hl hne hpos
          have hl_sl2 : l ∈ Full.fullRsnLits sl_sub rsn := heq_s2 ▸ hl
          have hpos' : 0 < (s2.core.lvl[l / 2]?.getD 0#32).toNat := by simpa [s3] using hpos
          exact hall_mrk l hl_sl2 hne hpos'
        have hzero_b : resolved = 0 → cut = cut ∧ idx' < cut ∧
            (s.core.trl[idx']?.getD 0#32).toNat = p_bv.toNat ∧
            s.core.rsns[p_bv.toNat / 2]?.getD 0xFFFFFFFF#32 = rsn ∧
            rsn ≠ 0xFFFFFFFF#32 ∧ (rsn &&& 0x80000000#32) = 0#32 ∧
            sl.core.confl_type = s.core.confl_type ∧
            sl.core.confl_ref = s.core.confl_ref := by
          intro hr0; obtain ⟨hc_eq, hct_eq, hcr_eq⟩ := hzero hr0
          refine ⟨rfl, hc_eq ▸ hiu_cut, ?_, ?_, hok_ne, hrsn_lg, hct_eq, hcr_eq⟩
          · rw [← hstat_l.trl, hp_get]
          · rw [← hstat_l.rsns, hr_get]
        fa_fast_steps_nogrp
        · have hant3 : sc2.ant_sz = 3#64 := by assumption
          have hbin_ent := Full.otfs_entails_bin_of_res_lt_ant hw_s3 hnd2 hlen_s3 htl2_1 htl2_cv'
            (by rw [hlen_s2.core_ok.tmp_len_arr]
                exact Nat.le_trans htl2_cv' hcv_le_l)
            hlow2 hmcov2 htc2_eq' hent2 hiu_cut hte_s3 hp_get_s2 hr_get_s2
            hpl_s3 hcl_s3_pos hok_ne hrsn_lg hall_s3 rfl hant_s2 hres_ult
            (by rw [hant3])
          refine wp_call_of_spec _ _ (hΓ.otfsBin (c.hdr, rsn, p_bv, ()) _ _ _
            ⟨c, F0, F_cur, cut_cur, idx', s3, R, rfl, hlen_s3, hw_s3, hnd2,
             hstat_s3.dm.trans hdm0, href_s2, hng_s2, hp_lt_s3, hiu_cut, hp_get_s2,
             hr_get_s2, hpl_s3, hbin_ent, hm3, ?_⟩)
          intro ok_b ar_b ag_b wv_b ws_b wl_b wu_b nb_b ct_b cr_b c0_b c1_b oom_b
            sc_b m_b _ hlen_b hw_b hnd_b hext_b hws1_b hws2_b hres_b hrefs_b hok_b
            hm_b
          dsimp only [s3, s2] at hlen_b hw_b hnd_b hext_b hws1_b hws2_b hres_b
          dsimp only [s3, s2] at hrefs_b hok_b hm_b; let s_b : FullState :=
            { s3 with
              core := { s3.core with arena := ar_b, arena_garbage := ag_b,
                                     wvec := wv_b, wstk := ws_b, wlen := wl_b,
                                     wusable := wu_b, num_binary := nb_b,
                                     confl_type := ct_b, confl_ref := cr_b,
                                     confl_lit0 := c0_b, confl_lit1 := c1_b,
                                     oom := oom_b }
              scratch := sc_b }
          have hcov_b := fid_anaMarksCov_of_same (s2 := s_b) hcov_s3 rfl rfl rfl hws1_b
          have hext_sb := Full.fullExtScratchPres_trans hext_s3 hext_b; have hrefs_sb :
              Full.fullArenaClauseRefs s_b = Full.fullArenaClauseRefs s :=
            hrefs_b.trans hrefs_s3
          cases ok_b with
          | true =>
            obtain ⟨hct_b, hconfl_b⟩ := hok_b rfl
            have href_sb : rsn.toNat ∈ Full.fullArenaClauseRefs s_b := by
              rw [hrefs_b]; exact href_s2
            have har_rsn_lt : (BitVec.setWidth 64 rsn).toNat < s_b.core.arena.length := by
              rw [bv32_setWidth64_toNat, hlen_b.core_ok.arena_len_arr]
              have hwf_r := (hw_b.arena.refs_wf rsn.toNat href_sb).1
              have hal_b := hlen_b.core_ok.arena_len_le; omega
            fa_fast_steps_nogrp
            refine wp_join_group (ts := []) (fun () ml =>
              ∃ ni_d nr_d : BitVec 64,
                (FullMem c { s_b with core := { s_b.core with
                  num_irred := ni_d, num_redundant := nr_d } } ⋆ R) ml)
              (fun _ ⟨⟩ ml ⟨ni_d, nr_d, hm_d⟩ => by
                let s_d : FullState :=
                  { s_b with core := { s_b.core with
                    num_irred := ni_d, num_redundant := nr_d } }
                have hlen_d : s_d.LengthsOk c := ⟨{ hlen_b.core_ok with }, hlen_b.scratch_ok⟩
                have hw_d : Full.FullWitnessCutInv c F0 F_cur idx' s_d.core :=
                  { hw_b with
                    arena := { hw_b.arena with len_ok := hw_b.arena.len_ok }
                    watches := hw_b.watches.with_wstk rfl rfl rfl rfl rfl fun _ hr => hr }
                have hcov_d := fid_anaMarksCov_of_same (s2 := s_d) hcov_b rfl rfl rfl rfl
                have hconfl_d := Full.deduce_conflOk_same_of_clear hconfl_b
                  rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
                have hstat_d : Full.FullDeduceStaticEq s.core s_d.core :=
                  ⟨hstat_s3.1, hstat_s3.2, hstat_s3.3, hstat_s3.4, hstat_s3.5,
                   hstat_s3.6, hstat_s3.7, hstat_s3.8, hstat_s3.9, hstat_s3.10⟩
                fa_fast_steps_nogrp
                refine fid_deduce_otfs_ret2_subsume_wp (init_res_sz := init_res_sz)
                  (p := p_bv) (rsn := rsn) (new_confl_arg := Arg.imm 0#32)
                  (to_bin := true) hΓ.clear hΓ.otfsSub hQ hw0
                  hconfl hext0 hdm0 hlm0 hlen_d hw_d hcov_d hext_sb
                  (hws2_b.trans hws2_s2) hnd_b hrefs_sb hstat_d hconfl_d hte_s3
                  hres1_lt64 (fun _ => hct_b)
                  (fun hr0 => by
                    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hzero_b hr0
                    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, fun hc => by cases hc⟩)
                  hm_d)
              (fun _ hJdec => by
                fa_fast_steps
                all_goals first
                  | exact hJdec () _ ⟨_, _, by assumption⟩
                  | exact hJdec () _ ⟨s_b.core.num_irred, s_b.core.num_redundant, hm_b⟩)
          | false =>
            fa_fast_steps
            exact hJin () m_b ⟨idx', s_b, hir3,
              ⟨hlen_b, hw_b, hcov_b, hext_sb, hws2_b.trans hws2_s2, hnd_b, hrefs_sb,
               hstat_s3.repack, htl2_1, htl2_cv', htc2_eq', hlow2, hmcov2,
               fun j hj _ _ => hj, hent2, hres_b⟩,
              rfl, htc2_pos, hm_b⟩
        · have hlarge_ent := Full.otfs_entails_large_of_res_lt_ant hw_s3 hnd2
            hlen_s3 htl2_1
            (by rw [hlen_s2.core_ok.tmp_len_arr]
                exact Nat.le_trans htl2_cv' hcv_le_l)
            hlow2 hmcov2 htc2_eq' hent2 hiu_cut hte_s3 hp_get_s2 hr_get_s2 hpl_s3
            hcl_s3_pos hok_ne hrsn_lg hall_s3 rfl hant_s2 hres_ult
          refine wp_call_of_spec _ _ (hΓ.otfsLarge (c.hdr, rsn, p_bv, ()) _ _ _
            ⟨c, F0, F_cur, cut_cur, idx', s3, R, rfl, hlen_s3, hw_s3, hnd2,
             hstat_s3.dm.trans hdm0, href_s2, hng_s2, hp_lt_s3, hiu_cut, hp_get_s2,
             hr_get_s2, hpl_s3, hlarge_ent, hm3, ?_⟩)
          intro ok_l flags_l ar_l wv_l ws_l wl_l wu_l oom_l sc_l m_l _ hlen_l hw_l hnd_l
          intro hext_l hws1_l hws2_l hres_l hrefs_l hok_l hm_l
          dsimp only [s3, s2] at hlen_l hw_l hnd_l hext_l hws1_l hws2_l hres_l
          dsimp only [s3, s2] at hrefs_l hok_l hm_l; let s_l : FullState :=
            { s3 with
              core := { s3.core with flags := flags_l, arena := ar_l, wvec := wv_l, wstk := ws_l,
                                     wlen := wl_l, wusable := wu_l, oom := oom_l }
              scratch := sc_l }
          have hcov_l' := fid_anaMarksCov_of_same (s2 := s_l) hcov_s3 rfl rfl rfl hws1_l
          have hext_sl := Full.fullExtScratchPres_trans hext_s3 hext_l; have hrefs_sl :
              Full.fullArenaClauseRefs s_l = Full.fullArenaClauseRefs s :=
            hrefs_l.trans hrefs_s3
          cases ok_l with
          | true =>
            obtain ⟨href_l, hng_l, hlits_l⟩ := hok_l rfl
            fa_fast_steps_nogrp
            let s_ot : FullState :=
              { s_l with core := { s_l.core with confl_type := 2#64,
                                                 confl_ref := rsn.setWidth 64 } }
            have hlen_ot : s_ot.LengthsOk c := ⟨{ hlen_l.core_ok with }, hlen_l.scratch_ok⟩
            have hw_ot : Full.FullWitnessCutInv c F0 F_cur idx' s_ot.core :=
              fid_cut_with_confl hw_l 2#64 (rsn.setWidth 64)
            have hconfl_ot : Full.FullConflictOkCut F_cur idx' s_ot :=
              Full.deduce_large_conflOk_of href_l hng_l hlits_l
            refine fid_deduce_otfs_ret2_subsume_wp (init_res_sz := init_res_sz)
              (p := p_bv) (rsn := rsn)
              (new_confl_arg := Arg.var rsn)
              (to_bin := false) hΓ.clear hΓ.otfsSub hQ hw0
              hconfl hext0 hdm0 hlm0 hlen_ot hw_ot hcov_l' hext_sl
              (hws2_l.trans hws2_s2) hnd_l hrefs_sl hstat_s3.repack hconfl_ot hte_s3
              hres1_lt64 (fun h => by cases h) (fun hr0 => by
                obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hzero_b hr0
                have hz : (rsn.setWidth 64).toNat = rsn.toNat := by
                  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans rsn.isLt (by decide))]
                exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, fun _ => ⟨href_l, rfl, hz⟩⟩)
              ?_
            exact (by assumption : (FullMem c s_ot ⋆ R) _)
          | false =>
            fa_fast_steps
            exact hJin () m_l ⟨idx', s_l, hir3,
              ⟨hlen_l, hw_l, hcov_l', hext_sl, hws2_l.trans hws2_s2, hnd_l,
               hrefs_sl, hstat_s3.repack, htl2_1, htl2_cv', htc2_eq', hlow2, hmcov2,
               fun j hj _ _ => hj, hent2, hres_l⟩,
              rfl, htc2_pos, hm_l⟩
      · fa_fast_steps
        exact hJot () ml ⟨cut_cur, s3, hir3, hst_s3, rfl, htc2_pos, hm3⟩
      · fa_fast_steps
        exact hJot () ml ⟨cut_cur, s3, hir3, hst_s3, rfl, htc2_pos, hm3⟩
      · fa_fast_steps
        exact hJot () ml ⟨cut_cur, s3, hir3, hst_s3, rfl, htc2_pos, hm3⟩
    · intro J_res hJres
      fa_fast_steps
      · refine hJres (sc2.res_sz - 1#64, ()) _ ⟨hs3_res_bv, ?_⟩
        dsimp only [s3]; rw [← hs3_res_bv]
        exact (by assumption)
      · exfalso
        have hbad : ¬ 0 % 2 ^ 64 < sc2.res_sz.toNat := by assumption
        have hlt : (0#64 : BitVec 64).toNat < sc2.res_sz.toNat := by
          simpa only [BitVec.ult, decide_eq_true_eq] using hres2_pos
        exact hbad (by simpa using hlt)
private theorem s6a_fid11_deduce_1uip_m6_wp (Γ : Env) (hΓ : s6aFidCoreHyps Γ) :
    ∀ a m Q X, Full.fullDeduce1uipSpec a m Q X → Func.wp Γ fid11Deduce1uipM6Fn.body a m Q X := by
  have hAlit := hΓ.alit; have hArsn := hΓ.arsn; have hClear := hΓ.clear
  rintro ⟨h, ⟨⟩⟩ m0 Q X ⟨c, F0, F_cur, cut, s, R, rfl, hinv, hcur_pos, hconfl, hm0, hQ⟩
  unfold Func.wp fid11Deduce1uipM6Fn fid11_deduce_1uip_m6_body; dsimp only
  have ⟨hlen0, hw0, hlm0, hnd0, hext0, hdm0⟩ := hinv
  have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
  have hcv_le := hlen0.core_ok.cur_vars_le; have hte_le := hlen0.core_ok.trail_end_le
  fa_fast_steps_nogrp
  refine wp_join_group (ts := [.bool]) (fun ys m_sd =>
    ∃ s1 : FullState, s6aFidSeedCore c F0 F_cur cut s s1 ∧ 1 ≤ s1.core.tmp_len ∧
      s1.core.tmp_len ≤ s1.core.cur_vars ∧
      s1.core.confl_type = s.core.confl_type ∧ s1.core.confl_ref = s.core.confl_ref ∧
      (ys.fst = true → Full.FullDeduceStateInv c F0 F_cur cut s1.core.trail_end s s1) ∧
      (FullMem c s1 ⋆ R) m_sd) ?_ ?_
  · rintro _ ⟨seed_ok, ⟨⟩⟩ m_sd ⟨s1, ⟨hlen1, hw1, hcov1, hext1, hws2_1, hnd1, hrefs1, hstat1⟩,
      htl1, htl_cv1, hct_s1, hcr_s1, hsd1, hm1⟩
    fa_fast_steps_nogrp
    refine wp_join_group (ts := []) (fun _ m_cl =>
      ∃ s_cl : FullState, s6aFidSeedCore c F0 F_cur cut s s_cl ∧
        (seed_ok = true → s_cl.core.tmp_len = 1 → F0.Unsat) ∧
        (FullMem c s_cl ⋆ R) m_cl)
      (fun _ ⟨⟩ m_cl ⟨s_cl, ⟨hlen_cl, hw_cl, hcov_cl, hext_cl, hws2_cl, hnd_cl, hrefs_cl, hstat_cl⟩,
          hunsat, hm_cl⟩ =>
        fid_deduce_clear_unsat_goal_wp hClear hQ hlen_cl hw_cl hcov_cl hext0 hext_cl hws2_cl
          hnd_cl hrefs_cl hstat_cl hdm0 hlm0 hunsat hm_cl) ?_
    intro J_cl hJcl
    fa_fast_steps_nogrp
    · have hso_t : (seed_ok, ()).fst = true := by assumption
      have hst1 := hsd1 hso_t
      have htc_lt : s1.core.tmp_cnt < 2 ^ 64 := by
        have := Full.fullActiveResolvent_le_cur_vars (le_refl _) htl1
          (by rw [hlen1.core_ok.tmp_len_arr]
              exact Nat.le_trans htl_cv1 (by rw [hstat1.cv]; exact hcv_le))
          hst1.low hw1.trail_lits_lt hw1.trail_vars_nodup
        rw [← hst1.tc_eq] at this; have := hstat1.cv; omega
      exact hJcl () m_sd ⟨s1, ⟨hlen1, hw1, hcov1, hext1, hws2_1, hnd1, hrefs1, hstat1⟩,
        fun _ htl_eq => by
          have htc0 : s1.core.tmp_cnt = 0 := by
            have h := congrArg BitVec.toNat (by assumption : BitVec.ofNat 64 s1.core.tmp_cnt = 0#64)
            rw [bv64_ofNat_toNat htc_lt] at h; exact h
          have hcur0 : Full.fullCurLits s1.core s1.core.mrk s1.core.trail_end = [] := by
            have hnil : Full.fullCurTrailIdxs s1.core s1.core.mrk s1.core.trail_end = [] :=
              List.eq_nil_of_length_eq_zero (by rw [← hst1.tc_eq, htc0])
            unfold Full.fullCurLits; rw [hnil]; rfl
          have hlow0 : Full.fullLowerLits s1.core.tmp 1 = [] := by
            unfold Full.fullLowerLits; cases s1.core.tmp <;> rfl
          have hent_nil : (cnfOfClauses F_cur).EntailsClause (cnfClause []) := by
            simpa [Full.fullActiveResolvent, htl_eq, hlow0, hcur0] using hst1.ent
          exact hw1.ext_sound.2 (unsat_of_entails_nil hent_nil), hm1⟩
    · have hso_t : (seed_ok, ()).fst = true := by assumption
      have hst1 := hsd1 hso_t
      have htc_pos : 0 < s1.core.tmp_cnt := by
        rcases Nat.eq_zero_or_pos s1.core.tmp_cnt with h0 | hp
        · exfalso; apply (by assumption : BitVec.ofNat 64 s1.core.tmp_cnt ≠ 0#64)
          rw [h0]; rfl
        · exact hp
      have hcl32 : s.core.cur_level < 2 ^ 32 := by have := hw0.cur_level_le; omega
      have hcl_bv32 :
          (BitVec.ofNat 64 s1.core.cur_level).setWidth 32 = BitVec.ofNat 32 s.core.cur_level := by
        rw [hstat1.cl]; exact fid_bv64_setWidth32_ofNat hcl32
      let init_res_sz := s1.scratch.res_sz
      refine wp_join_group (ts := [i64, i64, i32, i64]) (fun ys m_u =>
        ∃ (cut_u idx_u : Nat) (su : FullState) (p_u : BitVec 32),
          su.LengthsOk c ∧ Full.FullWitnessCutInv c F0 F_cur cut_u su.core ∧
          Full.FullAnaMarksCov c su ∧ Full.FullExtScratchPres s su ∧
          su.scratch.work_stk2 = s.scratch.work_stk2 ∧ Full.FullArenaVarsNodup su ∧
          Full.fullArenaClauseRefs su = Full.fullArenaClauseRefs s ∧
          Full.FullDeduceStaticEq s.core su.core ∧ 1 ≤ su.core.tmp_len ∧
          su.core.tmp_len ≤ su.core.cur_vars ∧
          Full.FullLowerInv c su.core su.core.tmp su.core.mrk su.core.tmp_len ∧
          idx_u < su.core.trail_end ∧ (su.core.trl[idx_u]?.getD 0#32).toNat = p_u.toNat ∧
          (su.core.lvl[p_u.toNat / 2]?.getD 0#32).toNat = su.core.cur_level ∧
          ys.2.2.1 = p_u ^^^ 1#32 ∧
          (cnfOfClauses F_cur).EntailsClause
            (cnfClause ((p_u ^^^ 1#32).toNat :: Full.fullLowerLits su.core.tmp su.core.tmp_len)) ∧
          (FullMem c su ⋆ R) m_u)
        (fun _ ⟨_tcnt_u, _idx_u_bv, uip_bv, _res_u_bv, ⟨⟩⟩ _m_u ⟨cut_u, idx_u, su, p_u, hlu, hwu,
            hcu, heu, hwu2, hndu, hru, hsu, htl_u1, htl_ucv, hlowu, hiu_te, hpu_get, hplu,
            hys_u, hentu, hmu⟩ => by
          dsimp only at hys_u; subst uip_bv
          rw [Blocks.get_here]; try dsimp only
          exact fid_deduce_uip_exit_body_wp hClear hQ hext0 hdm0 hlm0 hlu hwu hcu heu hwu2
            hndu hru hsu htl_u1 htl_ucv hlowu hiu_te hpu_get hplu hentu hmu) ?_
      intro J_uip hJuip
      rw [hcl_bv32]; refine wp_loop_inv (ts := [i64, i64, i64])
        (fun ys ml =>
          ∃ (cut_n idx_n res_n : Nat) (sn : FullState),
            ys = (BitVec.ofNat 64 sn.core.tmp_cnt, BitVec.ofNat 64 idx_n,
                  BitVec.ofNat 64 res_n, ()) ∧
            idx_n + res_n ≤ sn.core.trail_end ∧
            Full.FullDeduceStateInv c F0 F_cur cut_n idx_n s sn ∧ 0 < sn.core.tmp_cnt ∧
            (res_n = 0 → cut_n = cut ∧
              sn.core.confl_type = s.core.confl_type ∧ sn.core.confl_ref = s.core.confl_ref) ∧
            (FullMem c sn ⋆ R) ml)
        (fun ys _ => ys.2.1.toNat) ?_ ?_
      · intro J_loop hJloop
        fa_fast_steps
        exact hJloop (BitVec.ofNat 64 s1.core.tmp_cnt, BitVec.ofNat 64 s1.core.trail_end,
            0#64, ()) m_sd
          ⟨cut, s1.core.trail_end, 0, s1, rfl, by omega, hst1, htc_pos,
           fun _ => ⟨rfl, hct_s1, hcr_s1⟩, hm1⟩
      · intro J_loop ys m_l hinv_l hJloop
        rw [Blocks.get_here]; try dsimp only
        obtain ⟨cut_cur, idx, resolved, sl, rfl, hidx_res, hstate, htc_pos_l, hzero, hml⟩ := hinv_l
        have hstate_cp := hstate
        obtain ⟨hlen_l, hw_l, hcov_l, hext_l, hws2_l, hnd_l, hrefs_l, hstat_l, htl_ge, htl_cv,
          htc_eq, hlow_l, hmcov_l, hcm_l, hent_l, hres_l⟩ := hstate
        have hcv_le_l := hlen_l.core_ok.cur_vars_le; have hte_le_l := hlen_l.core_ok.trail_end_le
        have htrl_len := hlen_l.core_ok.trl_len; have hmrk_len := hlen_l.core_ok.mrk_len
        have hlvl_len := hlen_l.core_ok.lvl_len; have hrsns_len := hlen_l.core_ok.rsns_len
        have htmp_len := hlen_l.core_ok.tmp_len_arr
        have hact_le : (sl.core.tmp_len - 1) + sl.core.tmp_cnt ≤ sl.core.cur_vars := by
          have := Full.fullActiveResolvent_le_cur_vars (by omega : idx ≤ sl.core.trail_end)
            htl_ge (by omega) hlow_l hw_l.trail_lits_lt hw_l.trail_vars_nodup
          rwa [← htc_eq] at this
        have htc_lt64 : sl.core.tmp_cnt < 2 ^ 64 := by omega
        have hidx_lt64 : idx < 2 ^ 64 := by omega
        have hres_lt64 : resolved < 2 ^ 64 := by omega
        have hres1_lt64 : resolved + 1 < 2 ^ 64 := by omega
        have hcv_s1_sl : s1.core.cur_vars = sl.core.cur_vars := by rw [hstat1.cv, hstat_l.cv]
        fa_fast_steps_nogrp
        · have hidx_eq0 : idx = 0 := by
            have h0 : BitVec.ofNat 64 idx = 0#64 := by assumption
            have h := congrArg BitVec.toNat h0
            rw [bv64_ofNat_toNat hidx_lt64] at h; exact h
          subst hidx_eq0
          have htc0 : sl.core.tmp_cnt = 0 := by
            have h : Full.fullCurTrailIdxs sl.core sl.core.mrk 0 = [] := rfl
            rw [htc_eq, h]; rfl
          omega
        · have hidx_pos : 0 < idx := by
            rcases Nat.eq_zero_or_pos idx with rfl | hpos
            · exact absurd rfl (by assumption : BitVec.ofNat 64 0 ≠ 0#64)
            · exact hpos
          let idx' := idx - 1
          have hiu_te : idx' < sl.core.trail_end := by omega
          have hidx'_bv : BitVec.ofNat 64 idx - 1#64 = BitVec.ofNat 64 idx' := by
            apply BitVec.eq_of_toNat_eq
            simp only [BitVec.toNat_sub, bv64_ofNat_toNat hidx_lt64,
              show (1#64 : BitVec 64).toNat = 1 from rfl, BitVec.toNat_ofNat]
            omega
          have hidx'_nat : (BitVec.ofNat 64 idx - 1#64).toNat = idx' := by
            rw [hidx'_bv, bv64_ofNat_toNat (by omega : idx' < 2 ^ 64)]
          let p_bv : BitVec 32 := sl.core.trl[idx']'(by omega)
          have hp_get : (sl.core.trl[idx']?.getD 0#32).toNat = p_bv.toNat := by
            rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
          have hp_lt : p_bv.toNat < 2 * sl.core.cur_vars := hp_get ▸ hw_l.trail_lits_lt idx' hiu_te
          have hidx_m : (2 ^ 64 - (1 : BitVec 64).toNat + idx) % 2 ^ 64 = idx' := by
            simp only [show (1 : BitVec 64).toNat = 1 from rfl]; omega
          have hge := hc; simp only [hidx_m, hcv_s1_sl,
            Nat.mod_eq_of_lt (by omega : sl.core.cur_vars < 2 ^ 64)] at hge
          change sl.core.cur_vars ≤ p_bv.toNat / 2 at hge
          omega
        · have hidx_pos : 0 < idx := by
            rcases Nat.eq_zero_or_pos idx with rfl | hpos
            · exact absurd rfl (by assumption : BitVec.ofNat 64 0 ≠ 0#64)
            · exact hpos
          let idx' := idx - 1
          have hiu_te : idx' < sl.core.trail_end := by omega
          have hidx'_bv : BitVec.ofNat 64 idx - 1#64 = BitVec.ofNat 64 idx' := by
            apply BitVec.eq_of_toNat_eq
            simp only [BitVec.toNat_sub, bv64_ofNat_toNat hidx_lt64,
              show (1#64 : BitVec 64).toNat = 1 from rfl, BitVec.toNat_ofNat]
            omega
          have hidx'_lt : (BitVec.ofNat 64 idx - 1#64).toNat < (BitVec.ofNat 64 idx).toNat := by
            rw [hidx'_bv, bv64_ofNat_toNat hidx_lt64, bv64_ofNat_toNat (by omega : idx' < 2 ^ 64)]
            omega
          have hidx'_nat : (BitVec.ofNat 64 idx - 1#64).toNat = idx' := by
            rw [hidx'_bv, bv64_ofNat_toNat (by omega : idx' < 2 ^ 64)]
          let p_bv : BitVec 32 := sl.core.trl[idx']'(by omega)
          have hp_get : (sl.core.trl[idx']?.getD 0#32).toNat = p_bv.toNat := by
            rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
          have hp_lt : p_bv.toNat < 2 * sl.core.cur_vars := hp_get ▸ hw_l.trail_lits_lt idx' hiu_te
          have hpv_lt : p_bv.toNat / 2 < sl.core.cur_vars := by omega
          have htrl_eq : sl.core.trl[(BitVec.ofNat 64 idx - 1).toNat]'(by
              rw [show (1 : BitVec 64) = 1#64 from rfl, hidx'_nat]; omega) = p_bv := by
            simp only [p_bv, show (1 : BitVec 64) = 1#64 from rfl, hidx'_nat]
          have hlt_pow : p_bv.toNat / 2 < 2 ^ 64 := by omega
          have hpv_lt_bv : ((p_bv >>> 1#32).setWidth 64).toNat = p_bv.toNat / 2 := by
            rw [BitVec.toNat_setWidth, Full.Deduce1UipTactics.d1_bv32_lshr_1,
              Nat.mod_eq_of_lt hlt_pow]
          have hpv_mrk : ((p_bv >>> 1#32).setWidth 64).toNat < sl.core.mrk.length := by
            rw [hpv_lt_bv]; omega
          have hpv_lvl : ((p_bv >>> 1#32).setWidth 64).toNat < sl.core.lvl.length := by
            rw [hpv_lt_bv]; omega
          have hpv_rsns : ((p_bv >>> 1#32).setWidth 64).toNat < sl.core.rsns.length := by
            rw [hpv_lt_bv]; omega
          rw [htrl_eq]
          · refine wp_join_group (ts := [i64, i32, i64]) (s6aFidJ2Inv c F0 F_cur cut idx' s R)
                (fun _ ys2 _ml ⟨cut_n, res_n, sn, hys1, hys3, hir, hst, htc, hz, hmn⟩ => by
                  fa_fast_steps
                  exact hJloop (ys2.1, BitVec.ofNat 64 idx - 1#64, ys2.2.2.1, ()) _ hidx'_lt
                    ⟨cut_n, idx', res_n, sn, by rw [hys1, hidx'_bv, hys3],
                     hir, hst, htc, hz, hmn⟩)
                ?_
            intro J2 hJ2
            c0_hsplit
            · have hmnz : sl.core.mrk[p_bv.toNat / 2]?.getD 0#8 ≠ 0#8 := by
                have hm1 : sl.core.mrk[p_bv.toNat / 2] ≠ 0#8 := by assumption
                rw [List.getElem?_eq_getElem (by omega), Option.getD_some]; exact hm1
              have hpv_nat : (BitVec.setWidth 64 (p_bv >>> 1)).toNat = p_bv.toNat / 2 := by
                rw [BitVec.toNat_setWidth, bv32_lshr_1, Nat.mod_eq_of_lt hlt_pow]
              have hpv_lvl' : (BitVec.setWidth 64 (p_bv >>> 1)).toNat < sl.core.lvl.length := by
                rw [hpv_nat]; omega
              c0_let_simp
              refine wp_load_of (a := Arg.var _) (FullArenaTactics.c0_load_full_lvl hpv_lvl' hml) ?_
              rw [getElem_eq_of_idx (hi := hpv_lvl') (hj := by omega) hpv_nat]
              c0_let_simp
              refine wp_jnz_of (fun hl1 => ?_) (fun hne => ?_)
              · have hpl_eq : sl.core.lvl[p_bv.toNat / 2] = BitVec.ofNat 32 s.core.cur_level :=
                  beq_iff_eq.mp hl1
                have hpl_cl :
                    (sl.core.lvl[p_bv.toNat / 2]?.getD 0#32).toNat = sl.core.cur_level := by
                  have hcl32_l : sl.core.cur_level < 2 ^ 32 := by have := hw_l.cur_level_le; omega
                  rw [List.getElem?_eq_getElem (by omega), Option.getD_some, hpl_eq, ← hstat_l.cl,
                    bv32_ofNat_toNat hcl32_l]
                have hmnz_tr :
                    sl.core.mrk[(sl.core.trl[idx']?.getD 0#32).toNat / 2]?.getD 0#8 ≠ 0#8 := by
                  rwa [hp_get]
                have hpl_tr :
                    (sl.core.lvl[(sl.core.trl[idx']?.getD 0#32).toNat / 2]?.getD 0#32).toNat =
                    sl.core.cur_level := by
                  rwa [hp_get]
                have htc1_bv : (BitVec.ofNat 64 sl.core.tmp_cnt - 1#64).toNat =
                    sl.core.tmp_cnt - 1 := by
                  rw [BitVec.toNat_sub, bv64_ofNat_toNat htc_lt64,
                    show (1#64 : BitVec 64).toNat = 1 from rfl]
                  omega
                let sl1 : FullState :=
                  { sl with core := { sl.core with tmp_cnt := sl.core.tmp_cnt - 1 } }
                have hw_1 : Full.FullWitnessCutInv c F0 F_cur cut_cur sl1.core :=
                  Full.deduce_same_core_cut hw_l sl.core.mrk sl.core.tmp (sl.core.tmp_cnt - 1)
                    sl.core.tmp_len sl.core.min_clr_len
                have hlen_1 : sl1.LengthsOk c :=
                  ⟨{ hlen_l.core_ok with }, { hlen_l.scratch_ok with }⟩
                have hcov_1 : Full.FullAnaMarksCov c sl1 := hcov_l
                have hext_1 : Full.FullExtScratchPres s sl1 := hext_l
                have hstat_1 : Full.FullDeduceStaticEq s.core sl1.core :=
                  ⟨hstat_l.1, hstat_l.2, hstat_l.3, hstat_l.4, hstat_l.5, hstat_l.6, hstat_l.7,
                   hstat_l.8, hstat_l.9, hstat_l.10⟩
                fa_fast_steps_nogrp
                · have htc1 : sl.core.tmp_cnt = 1 := by
                    have heq : BitVec.ofNat 64 sl.core.tmp_cnt - 1#64 = 0#64 := by assumption
                    have hn := congrArg BitVec.toNat heq
                    rw [htc1_bv, show (0#64 : BitVec 64).toNat = 0 from rfl] at hn; omega
                  have hsucc := Full.fullCurTrailIdxs_succ_true hmnz_tr hpl_tr
                  have hct0 : (Full.fullCurTrailIdxs sl1.core sl1.core.mrk idx').length = 0 := by
                    have hl := congrArg List.length hsucc
                    simp only [List.length_append, List.length_singleton] at hl
                    have hi' : idx' + 1 = idx := by omega
                    change (Full.fullCurTrailIdxs sl.core sl.core.mrk idx').length = 0
                    rw [hi', ← htc_eq, htc1] at hl; omega
                  have hcl_s := Full.fullCurLits_succ_true hmnz_tr hpl_tr; rw [hp_get] at hcl_s
                  have hent_uip := Full.fullDeduce_uip_entails hct0 hcl_s
                    (by simpa only [Full.fullActiveResolvent, Full.fullCurLits,
                      Full.fullCurTrailIdxs, sl1, show idx' + 1 = idx by omega] using hent_l)
                  fa_fast_steps_nogrp
                  refine hJuip (BitVec.ofNat 64 sl.core.tmp_cnt - 1#64,
                      BitVec.ofNat 64 idx - 1#64, p_bv ^^^ 1#32, BitVec.ofNat 64 resolved, ()) _
                    ⟨cut_cur, idx', sl1, p_bv, hlen_1, hw_1, hcov_1, hext_1, hws2_l, hnd_l, hrefs_l,
                     hstat_1, htl_ge, htl_cv, hlow_l, hiu_te, hp_get, hpl_cl, rfl,
                     hent_uip, ?_⟩
                  simpa only [sl1, show (1 : BitVec 64) = 1#64 from rfl, htc1_bv] using hm
                · have htc1_pos : 0 < sl.core.tmp_cnt - 1 := by
                    have hne : BitVec.ofNat 64 sl.core.tmp_cnt - 1#64 ≠ 0#64 := by assumption
                    rcases Nat.eq_zero_or_pos (sl.core.tmp_cnt - 1) with h0 | hpos
                    · have h1 : sl.core.tmp_cnt = 1 := by omega
                      exact absurd (by rw [h1]; decide) hne
                    · exact hpos
                  let rsn : BitVec 32 := sl.core.rsns[p_bv.toNat / 2]'(by omega)
                  have hiu_cut : idx' < cut_cur := hcm_l idx' (by omega) hmnz_tr hpl_tr
                  have hr_get : sl.core.rsns[p_bv.toNat / 2]?.getD 0xFFFFFFFF#32 = rsn := by
                    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
                  have hri := hw_l.reason_inv_cut idx' hiu_cut
                  dsimp only at hri; rw [hp_get, hr_get] at hri
                  let sl2 : FullState :=
                    { sl1 with scratch := { sl1.scratch with ant_sz := 0#64 } }
                  have hlen_2 : sl2.LengthsOk c := ⟨hlen_1.core_ok, { hlen_1.scratch_ok with }⟩
                  have hw_2 : Full.FullWitnessCutInv c F0 F_cur cut_cur sl2.core := hw_1
                  have hcov_2 : Full.FullAnaMarksCov c sl2 := hcov_1
                  have hext_2 : Full.FullExtScratchPres s sl2 := hext_1
                  have hstat_2 : Full.FullDeduceStaticEq s.core sl2.core := hstat_1
                  have hrsn_ref : rsn ≠ 0xFFFFFFFF#32 → (rsn &&& 0x80000000#32) = 0#32 →
                      rsn.toNat ∈ Full.fullArenaClauseRefs sl2 := fun hne hlg => by
                    have hri' := hri hne; rw [ite_eq_right (fun h => absurd hlg h)] at hri'
                    exact hri'.1
                  have hres_add1 :
                      BitVec.ofNat 64 resolved + 1#64 = BitVec.ofNat 64 (resolved + 1) := by
                    apply BitVec.eq_of_toNat_eq
                    rw [BitVec.toNat_add, bv64_ofNat_toNat hres_lt64,
                      show (1#64 : BitVec 64).toNat = 1 from rfl, bv64_ofNat_toNat hres1_lt64,
                      Nat.mod_eq_of_lt hres1_lt64]
                  have htc2_eq : sl2.core.tmp_cnt =
                      (Full.fullCurTrailIdxs sl2.core sl2.core.mrk idx').length := by
                    have hsucc := Full.fullCurTrailIdxs_succ_true hmnz_tr hpl_tr
                    have hl := congrArg List.length hsucc
                    simp only [List.length_append, List.length_singleton] at hl
                    have hi' : idx' + 1 = idx := by omega
                    change sl.core.tmp_cnt - 1 =
                      (Full.fullCurTrailIdxs sl.core sl.core.mrk idx').length
                    rw [hi', ← htc_eq] at hl; omega
                  have hent_2 : (cnfOfClauses F_cur).EntailsClause
                      (cnfClause (Full.fullActiveResolvent sl2.core sl2.core.tmp sl2.core.mrk
                        sl2.core.tmp_len (idx' + 1))) := by
                    simpa only [Full.fullActiveResolvent, Full.fullCurLits, Full.fullCurTrailIdxs,
                      sl2, sl1, show idx' + 1 = idx by omega] using hent_l
                  have hsl2_res : sl2.scratch.res_sz =
                      BitVec.ofNat 64 ((sl2.core.tmp_len - 1) + sl2.core.tmp_cnt + 1) := by
                    change sl.scratch.res_sz =
                      BitVec.ofNat 64 ((sl.core.tmp_len - 1) + (sl.core.tmp_cnt - 1) + 1)
                    rw [hres_l, show (sl.core.tmp_len - 1) + (sl.core.tmp_cnt - 1) + 1 =
                      (sl.core.tmp_len - 1) + sl.core.tmp_cnt by omega]
                  have hpv_nat1 : (BitVec.setWidth 64 (p_bv >>> 1)).toNat = p_bv.toNat / 2 := by
                    rw [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
                      Nat.shiftRight_eq_div_pow, Nat.pow_one, Nat.mod_eq_of_lt hlt_pow]
                  have hpv_rsns1 :
                      (BitVec.setWidth 64 (p_bv >>> 1)).toNat < sl.core.rsns.length := by
                    rw [hpv_nat1]; omega
                  have hrsn_eq : sl.core.rsns[(BitVec.setWidth 64 (p_bv >>> 1)).toNat]'hpv_rsns1 =
                      rsn := getElem_eq_of_idx (hi := hpv_rsns1) (hj := by omega) hpv_nat1
                  exact s6a_fid_deduce_loop_rsn_wp hΓ hw0 hcur_pos hconfl hext0 hdm0 hlm0
                    hQ hJ2 hidx_res (by omega) hcv_le_l hstate_cp hzero hiu_te hp_lt hp_get
                    hmnz hpl_cl htc1_pos hiu_cut hr_get hrsn_eq hres1_lt64 rfl rfl hlen_2 hw_2
                    hcov_2 hext_2 hstat_2 hrsn_ref hres_add1 htc2_eq hent_2 hsl2_res
                    (by simpa only [sl2, sl1, show (1 : BitVec 64) = 1#64 from rfl,
                      show (0 : BitVec 64) = 0#64 from rfl, htc1_bv] using hm)
              · fa_fast_steps
                have hnot : ¬ (sl.core.mrk[p_bv.toNat / 2]?.getD 0#8 ≠ 0#8 ∧
                    (sl.core.lvl[p_bv.toNat / 2]?.getD 0#32).toNat = sl.core.cur_level) := by
                  intro ⟨_, hcl⟩
                  have hl_eq : sl.core.lvl[p_bv.toNat / 2] = BitVec.ofNat 32 s.core.cur_level := by
                    apply BitVec.eq_of_toNat_eq
                    have hcl32' : sl.core.cur_level < 2 ^ 32 := by have := hw_l.cur_level_le; omega
                    rw [bv32_ofNat_toNat (hstat_l.cl ▸ hcl32'), ← hstat_l.cl]
                    simpa [List.getElem?_eq_getElem
                      (by omega : p_bv.toNat / 2 < sl.core.lvl.length)] using hcl
                  rw [beq_iff_eq.mpr hl_eq] at hne; cases hne
                exact s6a_fid_skip_lit_step hJ2 hidx_res (by omega) hp_get hstate_cp htc_pos_l
                  hzero hnot hml
            · fa_fast_steps
              have hnot : ¬ (sl.core.mrk[p_bv.toNat / 2]?.getD 0#8 ≠ 0#8 ∧
                  (sl.core.lvl[p_bv.toNat / 2]?.getD 0#32).toNat = sl.core.cur_level) := by
                intro ⟨hm_k, _⟩
                have hm0 : sl.core.mrk[p_bv.toNat / 2] = 0#8 := by assumption
                apply hm_k; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]; exact hm0
              exact s6a_fid_skip_lit_step hJ2 hidx_res (by omega) hp_get hstate_cp htc_pos_l
                hzero hnot hml
        · exfalso
          have hbad : ¬ (0 : BitVec 64).toNat < sl.core.tmp_cnt % 2 ^ 64 := by assumption
          rw [Nat.mod_eq_of_lt htc_lt64] at hbad
          exact hbad (by simpa using htc_pos_l)
    · exact hJcl () m_sd ⟨s1, ⟨hlen1, hw1, hcov1, hext1, hws2_1, hnd1, hrefs1, hstat1⟩,
        (fun h => by
          have hf : seed_ok = false := by assumption
          exact absurd (h.symm.trans hf) (by decide)), hm1⟩
  · intro J hJ
    exact wp_mono (fun _ _ h => h.elim) (fun _ _ _ _ h => h) _ _
      (fid_deduce_seed_wp hAlit hArsn hinv hcur_pos hconfl (by assumption) fun seed_ok m_sd h =>
        let ⟨s1, h1, h2, h3, h4, h5, h6, h7, h8, hrest⟩ := h
      hJ (seed_ok, ()) m_sd ⟨s1, ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩, hrest⟩)
section Deduce1UipHdrFid
private def fidArsnLiftEnv : Env := fun f as bs xs m Q X =>
  match f, as, bs, xs, Q with
  | "full_analyze_rsn", [.bits 64, .bits 32, .bits 32], [.bool], xs, Q =>
    s6aFidAnalyzeRsnSpec xs m Q X
  | "full_analyze_lit", [.bits 64, .bits 32, .bits 32], [.bool], xs, Q =>
    Full.fullAnalyzeLitSpec xs m Q X
  | "full_clear_ana", [.bits 64], [], xs, Q => Full.fullClearAnaSpec xs m Q X
  | "full_otfs_large", [.bits 64, .bits 32, .bits 32], [.bool], xs, Q =>
    step13OtfsLargeSpec xs m Q X
  | "full_otfs_bin", [.bits 64, .bits 32, .bits 32], [.bool], xs, Q =>
    Full.fullOtfsBinSpec xs m Q X
  | "full_otfs_subsume", [.bits 64, .bits 32, .bits 64, .bits 64, .bool], [], xs, Q =>
    Full.fullOtfsSubsumeSpec xs m Q X
  | _, _, _, _, _ => False
private def fidTflatMapArsnCall {as : List Ty} (bs : List Ty) (args : Tup (Arg K) as) (nv : Nat) :
    Option (Arg K i64) :=
  match as, bs, args with
  | [.bits 64, .bits 32, .bits 32], [.bool], (a0, _, _, ()) =>
    match a0 with
    | .var i => if decide (0 < nv ∧ i = nv - 1) then some a0 else none
    | _ => none
  | _, _, _ => none
mutual
private def fidTflatMapArsn {rs : List Ty} (nv : Nat) : TFlat rs → Option (TFlat rs)
  | .let_ (ts := ts) op k => (fidTflatMapArsn (nv + ts.length) k).map (.let_ op)
  | .load t a k => (fidTflatMapArsn (nv + 1) k).map (.load t a)
  | .store v a k => (fidTflatMapArsn nv k).map (.store v a)
  | .call f bs args k =>
    if f = "full_analyze_rsn" then
      match fidTflatMapArsnCall bs args nv with
      | some _ => (fidTflatMapArsn (nv + bs.length) k).map (.call "full_analyze_rsn_m6_hdr" bs args)
      | none => none
    else (fidTflatMapArsn (nv + bs.length) k).map (.call f bs args)
  | .jnz c t e =>
    match fidTflatMapArsn nv t, fidTflatMapArsn nv e with
    | some t', some e' => some (.jnz c t' e')
    | _, _ => none
  | .jump j args => some (.jump j args)
  | .ret vs => some (.ret vs)
  | .exit f args => some (.exit f args)
  | .hlt => some .hlt
  | .group bodies k =>
    match fidTblocksMapArsn nv bodies, fidTflatMapArsn nv k with
    | some bodies', some k' => some (.group bodies' k')
    | _, _ => none
private def fidTblocksMapArsn {rs : List Ty} (nv : Nat) :
    {sig : List (List Ty)} → TBlocks rs sig → Option (TBlocks rs sig)
  | _, .nil => some .nil
  | _, .cons (ts := ts) b bs =>
    match fidTflatMapArsn (nv + ts.length) b, fidTblocksMapArsn nv bs with
    | some b', some bs' => some (.cons b' bs')
    | _, _ => none
end
private theorem fid_listGet?_cons_last {α : Type _} (x : α) (xs : List α) (hle : 0 < xs.length) :
    listGet? (x :: xs) ((x :: xs).length - 1) = listGet? xs (xs.length - 1) := by
  rw [show (x :: xs).length - 1 = (xs.length - 1) + 1 from by simp; omega]; rfl
private theorem fid_listGet?_pushTup_last {ts : List Ty} (xs : Tup Val ts)
    (vs : List ((t : Ty) × Val t)) (hle : 0 < vs.length) :
    listGet? (pushTup xs vs) ((pushTup xs vs).length - 1) = listGet? vs (vs.length - 1) := by
  induction ts generalizing vs with
  | nil => cases xs; rfl
  | cons t ts ih =>
    rcases xs with ⟨x, xs⟩
    exact (ih xs (⟨t, x⟩ :: vs) (by simp)).trans (fid_listGet?_cons_last ⟨t, x⟩ vs hle)
private def fidLiftContHdr {ts : List Ty} (c : FullCfg) (J₂ : Cont ts) : Cont ts :=
  fun xs m_s => ∀ ext m_f, M6HdrExtOk ext →
    (Eq m_s ⋆ array64 (c.hdr - 2304) ext) m_f → J₂ xs m_f
private def fidLiftTupContHdr (c : FullCfg) :
    {sig : List (List Ty)} → Tup Cont sig → Tup Cont sig
  | [], () => ()
  | _ :: _, (J, Js) => (fidLiftContHdr c J, fidLiftTupContHdr c Js)
private def FidLabelsLiftRel (c : FullCfg) (ls₁ ls₂ : List ((ts : List Ty) × Cont ts)) : Prop :=
  (∀ (ts : List Ty) (idx : Nat), (lookupL ls₁ ts idx).isSome = (lookupL ls₂ ts idx).isSome) ∧
  ∀ (ts : List Ty) (idx : Nat) (j₁ j₂ : Cont ts),
    lookupL ls₁ ts idx = some j₁ → lookupL ls₂ ts idx = some j₂ →
    ∀ xs m_s m_f ext, M6HdrExtOk ext →
      (Eq m_s ⋆ array64 (c.hdr - 2304) ext) m_f → j₁ xs m_s → j₂ xs m_f
private theorem fid_labelsLiftRel_cons {c : FullCfg} {ts : List Ty}
    {ls₁ ls₂ : List ((us : List Ty) × Cont us)} {J₂ : Cont ts}
    (h : FidLabelsLiftRel c ls₁ ls₂) :
    FidLabelsLiftRel c (⟨ts, fidLiftContHdr c J₂⟩ :: ls₁) (⟨ts, J₂⟩ :: ls₂) := by
  refine ⟨fun ts' idx => ?_, fun ts' idx j₁ j₂ hj₁ hj₂ => ?_⟩
  · cases idx with
    | zero => dsimp only [lookupL, listGet?, castListTy]; cases listTyDecEq ts ts' <;> rfl
    | succ k => exact h.1 ts' k
  · cases idx with
    | succ k => exact h.2 ts' k j₁ j₂ hj₁ hj₂
    | zero =>
      dsimp only [lookupL, listGet?, castListTy] at hj₁ hj₂
      cases hdec : listTyDecEq ts ts' with
      | isFalse _ => simp [hdec] at hj₁
      | isTrue heq =>
        subst heq; simp only [hdec, Option.some.injEq] at hj₁ hj₂; subst hj₁ hj₂
        exact fun _ _ _ _ hext hsep hJ => hJ _ _ hext hsep
private theorem fid_labelsLiftRel_pushTup {c : FullCfg} :
    {sig : List (List Ty)} → (Js₂ : Tup Cont sig) →
    {ls₁ ls₂ : List ((ts : List Ty) × Cont ts)} → FidLabelsLiftRel c ls₁ ls₂ →
    FidLabelsLiftRel c (pushTup (fidLiftTupContHdr c Js₂) ls₁) (pushTup Js₂ ls₂)
  | [], (), _, _, h => h
  | _ :: _, (_J, Js), _, _, h => fid_labelsLiftRel_pushTup Js (fid_labelsLiftRel_cons h)
private theorem fid_sep_extract_eq {A B : Mem 64 → Prop} {m : Mem 64} (h : (A ⋆ B) m) :
    ∃ m_b, B m_b ∧ (Eq m_b ⋆ A) m := by
  have hB : B = (fun m' => ∃ m_b, B m_b ∧ Eq m_b m') :=
    funext fun m' => propext ⟨fun hb => ⟨m', hb, rfl⟩, fun ⟨_, hb, heq⟩ => heq ▸ hb⟩
  have h1 : (A ⋆ (fun m' => ∃ m_b, B m_b ∧ Eq m_b m')) m := hB ▸ h
  rw [sep_ex_r] at h1; rcases h1 with ⟨m_b, h2⟩; rw [sep_pure_r, sep_comm] at h2; exact ⟨m_b, h2⟩
private theorem fid_sep_join_eq {A P : Mem 64 → Prop} {m_b m : Mem 64}
    (hp : P m_b) (h : (Eq m_b ⋆ A) m) : (A ⋆ P) m := by
  rw [sep_comm]; exact sep_mono (fun _ heq => heq ▸ hp) h
private theorem fid_sep_frame_enter {E M R : Mem 64 → Prop} {m_s m_f : Mem 64}
    (hm : (M ⋆ R) m_s) (hsep : (Eq m_s ⋆ E) m_f) : (M ⋆ (E ⋆ R)) m_f := by
  have h1 : (E ⋆ (M ⋆ R)) m_f := fid_sep_join_eq hm hsep
  rwa [← sep_assoc, sep_comm E M, sep_assoc] at h1
private theorem fid_sep_frame_exit {E M R : Mem 64 → Prop} {m_f : Mem 64}
    (hm : (M ⋆ (E ⋆ R)) m_f) : ∃ m_s, (M ⋆ R) m_s ∧ (Eq m_s ⋆ E) m_f := by
  rw [← sep_assoc, sep_comm M E, sep_assoc] at hm; exact fid_sep_extract_eq hm
private theorem fid_sep_split_ext {c : FullCfg} {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (FullM6HdrMem c ext s ⋆ R) m) :
    ∃ m_s, (FullMem c s ⋆ R) m_s ∧ (Eq m_s ⋆ array64 (c.hdr - 2304) ext) m :=
  fid_sep_extract_eq (fullM6HdrMem_ext_focus hm)
private theorem fid_sep_join_fullM6Hdr {c : FullCfg} {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m_s m_f : Mem 64}
    (hs : (FullMem c s ⋆ R) m_s) (hsep : (Eq m_s ⋆ array64 (c.hdr - 2304) ext) m_f) :
    (FullM6HdrMem c ext s ⋆ R) m_f := fullM6HdrMem_ext_unfocus (fid_sep_join_eq hs hsep)
private structure FidArsnLiftHyps (Γ : Env) : Prop where
  alit : ∀ a m Q X, Full.fullAnalyzeLitSpec a m Q X →
    Γ "full_analyze_lit" [i64, i32, i32] [.bool] a m Q X
  arsn : ∀ a m Q X, step13AnalyzeRsnHdrSpec a m Q X →
    Γ "full_analyze_rsn_m6_hdr" [i64, i32, i32] [.bool] a m Q X
  clear : ∀ a m Q X, Full.fullClearAnaSpec a m Q X → Γ "full_clear_ana" [i64] [] a m Q X
  otfsLarge : ∀ a m Q X, step13OtfsLargeSpec a m Q X →
    Γ "full_otfs_large" [i64, i32, i32] [.bool] a m Q X
  otfsBin : ∀ a m Q X, Full.fullOtfsBinSpec a m Q X →
    Γ "full_otfs_bin" [i64, i32, i32] [.bool] a m Q X
  otfsSub : ∀ a m Q X, Full.fullOtfsSubsumeSpec a m Q X →
    Γ "full_otfs_subsume" [i64, i32, i64, i64, .bool] [] a m Q X
private theorem fid_frame_unchanged_call {Γ : Env} (hΓ : FidArsnLiftHyps Γ)
    {c : FullCfg} {ext : List (BitVec 64)} {rs : List Ty}
    {f : String} {as bs : List Ty} (hf_ne : f ≠ "full_analyze_rsn")
    (args' : Tup (Arg Val) as) (k₂ : Tup Val bs → Expr Val Cont rs)
    {m_s m_f : Mem 64} {P : Post bs} {Q₂ : Post rs}
    {E' : XPost} (hG : fidArsnLiftEnv f as bs (vals args') m_s P E')
    (hk : ∀ rv m_s' m_f', P rv m_s' → (Eq m_s' ⋆ array64 (c.hdr - 2304) ext) m_f' →
      wp Γ Q₂ (fun _ _ _ _ => False) (k₂ rv) m_f')
    (hsep : (Eq m_s ⋆ array64 (c.hdr - 2304) ext) m_f) :
    wp Γ Q₂ (fun _ _ _ _ => False) (.call f (as := as) (bs := bs) args' k₂) m_f := by
  let E := array64 (c.hdr - 2304) ext; dsimp only [fidArsnLiftEnv] at hG
  split at hG
  · exact absurd rfl hf_ne
  · rcases hG with ⟨c', s', R', hc, h1, h2, h3, h4, h5, hm_s, hP'⟩
    rcases args' with ⟨a0, a1, a2, ⟨⟩⟩; dsimp only [vals] at hc
    refine wp_call_of_spec (as := [i64, i32, i32]) (bs := [.bool]) (a0, a1, a2, ()) k₂ ?_
    dsimp only [vals]; rw [hc]
    refine hΓ.alit (c'.hdr, a1.val, a2.val, ()) m_f _ _
      ⟨c', s', E ⋆ R', rfl, h1, h2, h3, h4, h5, fid_sep_frame_enter hm_s hsep,
        fun ok mrk' tmp' tc' tl' mcl' ws1' ant' res' m_f' a b d e f g h i j k l n o p hm' => ?_⟩
    rcases fid_sep_frame_exit hm' with ⟨m_s', hm_s', hsep'⟩
    exact hk (ok, ()) m_s' m_f'
      (hP' ok mrk' tmp' tc' tl' mcl' ws1' ant' res' m_s' a b d e f g h i j k l n o p hm_s') hsep'
  · rcases hG with ⟨c', s', R', hc, hlen', hm_s, hP'⟩
    rcases args' with ⟨a0, ⟨⟩⟩; dsimp only [vals] at hc
    refine wp_call_of_spec (as := [i64]) (bs := []) (a0, ()) k₂ ?_
    dsimp only [vals]; rw [hc]
    refine hΓ.clear (c'.hdr, ()) m_f _ _
      ⟨c', s', E ⋆ R', rfl, hlen', fid_sep_frame_enter hm_s hsep, fun mrk' m_f' a b d e hm' => ?_⟩
    rcases fid_sep_frame_exit hm' with ⟨m_s', hm_s', hsep'⟩
    exact hk () m_s' m_f' (hP' mrk' m_s' a b d e hm_s') hsep'
  · rcases hG with ⟨c', F0', F_cur', cut', idx_u', s', R', hc, a, b, d, e, f, g, h, i, j, k, l, n,
      hm_s, hP'⟩
    rcases args' with ⟨a0, a1, a2, ⟨⟩⟩; dsimp only [vals] at hc
    refine wp_call_of_spec (as := [i64, i32, i32]) (bs := [.bool]) (a0, a1, a2, ()) k₂ ?_
    dsimp only [vals]; rw [hc]
    refine hΓ.otfsLarge (c'.hdr, a1.val, a2.val, ()) m_f _ _
      ⟨c', F0', F_cur', cut', idx_u', s', E ⋆ R', rfl, a, b, d, e, f, g, h, i, j, k, l, n,
        fid_sep_frame_enter hm_s hsep,
        fun ok flags' ar' wv' ws' wl' wu' oom' sc' m_f' p1 p2 p3 p4 p5 p6 p7 p8 p9 hm' => ?_⟩
    rcases fid_sep_frame_exit hm' with ⟨m_s', hm_s', hsep'⟩
    exact hk (ok, ()) m_s' m_f'
      (hP' ok flags' ar' wv' ws' wl' wu' oom' sc' m_s' p1 p2 p3 p4 p5 p6 p7 p8 p9 hm_s') hsep'
  · rcases hG with ⟨c', F0', F_cur', cut', idx_u', s', R', hc, a, b, d, e, f, g, h, i, j, k, l, n,
      hm_s, hP'⟩
    rcases args' with ⟨a0, a1, a2, ⟨⟩⟩; dsimp only [vals] at hc
    refine wp_call_of_spec (as := [i64, i32, i32]) (bs := [.bool]) (a0, a1, a2, ()) k₂ ?_
    dsimp only [vals]; rw [hc]
    refine hΓ.otfsBin (c'.hdr, a1.val, a2.val, ()) m_f _ _
      ⟨c', F0', F_cur', cut', idx_u', s', E ⋆ R', rfl, a, b, d, e, f, g, h, i, j, k, l, n,
        fid_sep_frame_enter hm_s hsep,
        fun ok ar' ag' wv' ws' wl' wu' nb' ct' cr' c0' c1' oom' sc' m_f'
          p1 p2 p3 p4 p5 p6 p7 p8 p9 hm' => ?_⟩
    rcases fid_sep_frame_exit hm' with ⟨m_s', hm_s', hsep'⟩
    exact hk (ok, ()) m_s' m_f' (hP' ok ar' ag' wv' ws' wl' wu' nb' ct' cr' c0' c1'
      oom' sc' m_s' p1 p2 p3 p4 p5 p6 p7 p8 p9 hm_s') hsep'
  · rcases hG with ⟨c', F0', F_cur', cut', s', R', hc, a, b, d, e, hm_s, hP'⟩
    rcases args' with ⟨a0, a1, a2, a3, a4, ⟨⟩⟩; dsimp only [vals] at hc
    refine wp_call_of_spec (as := [i64, i32, i64, i64, .bool]) (bs := [])
      (a0, a1, a2, a3, a4, ()) k₂ ?_
    dsimp only [vals]; rw [hc]
    refine hΓ.otfsSub (c'.hdr, a1.val, a2.val, a3.val, a4.val, ()) m_f _ _
      ⟨c', F0', F_cur', cut', s', E ⋆ R', rfl, a, b, d, e, fid_sep_frame_enter hm_s hsep,
        fun ar' ag' ni' nr' m_f' p1 p2 p3 p4 p5 hm' => ?_⟩
    rcases fid_sep_frame_exit hm' with ⟨m_s', hm_s', hsep'⟩
    exact hk () m_s' m_f' (hP' ar' ag' ni' nr' m_s' p1 p2 p3 p4 p5 hm_s') hsep'
  · exact False.elim hG
private theorem fid_denoteArgs3_inv {t0 t1 t2 : Ty} {vs : List ((t : Ty) × Val t)}
    {a0 : Arg K t0} {a1 : Arg K t1} {a2 : Arg K t2} {args' : Tup (Arg Val) [t0, t1, t2]}
    (hd : denoteArgs (ts := [t0, t1, t2]) vs (a0, a1, a2, ()) = some args') :
    ∃ a0' a1' a2', denoteArg vs a0 = some a0' ∧ denoteArg vs a1 = some a1' ∧
      denoteArg vs a2 = some a2' ∧ args' = (a0', a1', a2', ()) := by
  dsimp only [denoteArgs] at hd
  cases h0 : denoteArg vs a0 with | none => simp [h0] at hd | some x0 =>
  cases h1 : denoteArg vs a1 with | none => simp [h0, h1] at hd | some x1 =>
  cases h2 : denoteArg vs a2 with | none => simp [h0, h1, h2] at hd | some x2 =>
  simp [h0, h1, h2] at hd; subst hd; exact ⟨x0, x1, x2, rfl, rfl, rfl, rfl⟩
mutual
private theorem fid_denote_wp_arsn_lift {Γ : Env} (hΓ : FidArsnLiftHyps Γ)
    {c : FullCfg} (hcfg : FullM6HdrCfgOk c) {rs : List Ty} :
    ∀ (tf₁ tf₂ : TFlat rs)
      (vs : List ((t : Ty) × Val t)) (ls₁ ls₂ : List ((ts : List Ty) × Cont ts)),
      0 < vs.length → listGet? vs (vs.length - 1) = some ⟨i64, c.hdr⟩ →
      FidLabelsLiftRel c ls₁ ls₂ → fidTflatMapArsn vs.length tf₁ = some tf₂ →
      ∀ (Q₁ Q₂ : Post rs), (∀ rv m_s ext m_f, M6HdrExtOk ext →
          (Eq m_s ⋆ array64 (c.hdr - 2304) ext) m_f → Q₁ rv m_s → Q₂ rv m_f) →
        ∀ m_s ext m_f, M6HdrExtOk ext → (Eq m_s ⋆ array64 (c.hdr - 2304) ext) m_f →
          wp fidArsnLiftEnv Q₁ (fun _ _ _ _ => False) (denote Val Cont tf₁ vs ls₁) m_s →
          wp Γ Q₂ (fun _ _ _ _ => False) (denote Val Cont tf₂ vs ls₂) m_f
  | .let_ (ts := ts) op k, tf₂, vs, ls₁, ls₂, hv_pos, hlast, hls, hmap, Q₁, Q₂, hQ,
      m_s, ext, m_f, hext, hsep, hwp => by
    dsimp only [fidTflatMapArsn] at hmap
    cases hk_eq : fidTflatMapArsn (vs.length + ts.length) k with
    | none => simp [hk_eq] at hmap | some k' =>
    simp only [hk_eq, Option.map_some, Option.some.injEq] at hmap; subst tf₂
    dsimp only [denote] at hwp ⊢
    cases hd : denoteArgs vs op.args with | none => rw [hd] at hwp; cases hwp | some args' =>
    rw [hd] at hwp; dsimp only at hwp ⊢; dsimp only [wp] at hwp ⊢
    refine OpCode.wp_mono op.code _ (fun r h => ?_) hwp
    have hp := pushTup_length r vs
    exact fid_denote_wp_arsn_lift hΓ hcfg k k' (pushTup r vs) ls₁ ls₂ (by rw [hp]; omega)
      (by simpa using (fid_listGet?_pushTup_last r vs hv_pos).trans hlast) hls
      (by rw [hp]; exact hk_eq) Q₁ Q₂ hQ m_s ext m_f hext hsep h
  | .load t a k, tf₂, vs, ls₁, ls₂, hv_pos, hlast, hls, hmap, Q₁, Q₂, hQ,
      m_s, ext, m_f, hext, hsep, hwp => by
    dsimp only [fidTflatMapArsn] at hmap
    cases hk_eq : fidTflatMapArsn (vs.length + 1) k with
    | none => simp [hk_eq] at hmap | some k' =>
    simp only [hk_eq, Option.map_some, Option.some.injEq] at hmap; subst tf₂
    dsimp only [denote] at hwp ⊢
    cases hd : denoteArg vs a with | none => rw [hd] at hwp; cases hwp | some a' =>
    rw [hd] at hwp; dsimp only at hwp ⊢; rcases hwp with ⟨v, hld, hwp⟩
    exact ⟨v, loadVal_frame hsep hld, fid_denote_wp_arsn_lift hΓ hcfg k k' (⟨t, v⟩ :: vs) ls₁ ls₂
      (by simp) ((fid_listGet?_cons_last ⟨t, v⟩ vs hv_pos).trans hlast) hls hk_eq Q₁ Q₂ hQ m_s ext
      m_f hext hsep hwp⟩
  | .store v a k, tf₂, vs, ls₁, ls₂, hv_pos, hlast, hls, hmap, Q₁, Q₂, hQ,
      m_s, ext, m_f, hext, hsep, hwp => by
    dsimp only [fidTflatMapArsn] at hmap
    cases hk_eq : fidTflatMapArsn vs.length k with | none => simp [hk_eq] at hmap | some k' =>
    simp only [hk_eq, Option.map_some, Option.some.injEq] at hmap; subst tf₂
    dsimp only [denote] at hwp ⊢
    cases hv : denoteArg vs v with | none => rw [hv] at hwp; cases hwp | some v' =>
    cases ha : denoteArg vs a with | none => rw [hv, ha] at hwp; cases hwp | some a' =>
    rw [hv, ha] at hwp; dsimp only at hwp ⊢; rcases hwp with ⟨hok, hwp⟩
    exact ⟨storeOk_frame hsep hok, fid_denote_wp_arsn_lift hΓ hcfg k k' vs ls₁ ls₂
      hv_pos hlast hls hk_eq Q₁ Q₂ hQ _ ext _ hext (storeMem_frame hsep hok v'.val) hwp⟩
  | .call f bs args k, tf₂, vs, ls₁, ls₂, hv_pos, hlast, hls, hmap, Q₁, Q₂, hQ,
      m_s, ext, m_f, hext, hsep, hwp => by
    dsimp only [fidTflatMapArsn] at hmap; by_cases hf_arsn : f = "full_analyze_rsn"
    · subst hf_arsn; simp only [↓reduceIte] at hmap
      cases ht_eq : fidTflatMapArsnCall bs args vs.length with
      | none => simp [ht_eq] at hmap | some a0 =>
      cases hk_eq : fidTflatMapArsn (vs.length + bs.length) k with
      | none => simp [ht_eq, hk_eq] at hmap
      | some k' =>
        simp only [ht_eq, hk_eq, Option.map_some, Option.some.injEq] at hmap; subst tf₂
        dsimp only [fidTflatMapArsnCall] at ht_eq
        split at ht_eq <;> try cases ht_eq
        rename_i _i a1 a2; split at ht_eq <;> try cases ht_eq
        rename_i _iv idx; split at ht_eq <;> try cases ht_eq
        rename_i hdec
        have hiv : idx = vs.length - 1 := by rw [decide_eq_true_eq] at hdec; exact hdec.2
        subst hiv; dsimp only [denote] at hwp ⊢
        cases hd : denoteArgs (ts := [i64, i32, i32]) vs
            (Arg.var (vs.length - 1), a1, a2, ()) with
        | none => rw [hd] at hwp; cases hwp
        | some args' =>
          rw [hd] at hwp; dsimp only at hwp ⊢; rcases hwp with ⟨P, _E, hG, hP, _hE⟩
          have hspec : s6aFidAnalyzeRsnSpec (vals args') m_s P (fun _ _ _ _ => False) :=
            s6aFidAnalyzeRsnSpec_monoX hG
          rcases fid_denoteArgs3_inv hd with ⟨a0', a1', a2', ha0, _ha1, _ha2, h_eq⟩
          have ha0_eq : a0' = .var c.hdr := by
            simpa only [denoteArg, lookupV, hlast, castTy, ↓reduceDIte,
              Option.some.injEq] using ha0.symm
          have hargs_v : vals args' = (c.hdr, a1'.val, a2'.val, ()) := by rw [h_eq, ha0_eq]; rfl
          rw [hargs_v] at hspec
          rcases s6aFidAnalyzeRsnSpec_elim hspec with ⟨c', F0', F_cur', cut', s', R', hc'_eq,
            hlen', hcut', hcov', htl', htc', href', hm_s, hP'⟩
          have hcfg' := M6HdrCfgOk_of_le (hc'_eq ▸ M6HdrCfgOk_le hcfg)
          rw [hc'_eq] at hargs_v; refine wp_call_of_spec args' _ ?_; rw [hargs_v]
          refine hΓ.arsn (c'.hdr, a1'.val, a2'.val, ()) m_f _ _
            ⟨c', F0', F_cur', cut', ext, s', R', rfl, hcfg', hext,
              hlen', hcut', hcov', htl', htc', href',
              fid_sep_join_fullM6Hdr hm_s (by rwa [← hc'_eq]),
              fun ok mrk' tmp' mclr' tc' tl' mcl' arena' sc' ext' m_f' hext' _ hlen2 hcut2 hcov2
                hpre2 hws2 htl2 htl_cv htc2 hrefs2 har2 hmrk2 htmp2 hnew2 hjok2 hjnodup2 hdiff2
                hres2 hok2 hm_f' => ?_⟩
          rcases fid_sep_split_ext hm_f' with ⟨m_s', hm_s', hsep'⟩
          have hp_ok := hP' ok mrk' tmp' tc' tl' mclr' mcl' arena' sc' m_s' hlen2 hcut2 hcov2
            hpre2 hws2 htl2 htl_cv htc2 hrefs2 har2 hmrk2 htmp2 hnew2 hjok2 hjnodup2 hdiff2 hres2
            hok2 hm_s'
          have hlen_p := pushTup_length (as := [.bool]) (ok, ()) vs
          exact fid_denote_wp_arsn_lift hΓ hcfg k k'
            (pushTup (as := [.bool]) (f := Val) (ok, ()) vs) ls₁ ls₂ (by rw [hlen_p]; omega)
            ((fid_listGet?_pushTup_last (ts := [.bool]) (ok, ()) vs hv_pos).trans hlast) hls
            (by simpa [hlen_p] using hk_eq) Q₁ Q₂ hQ m_s' ext' m_f' hext' (by rwa [hc'_eq])
            (hP ((ok, ()) : Tup Val [.bool]) m_s' hp_ok)
    · simp only [hf_arsn, ↓reduceIte] at hmap
      cases hk_eq : fidTflatMapArsn (vs.length + bs.length) k with
      | none => simp [hk_eq] at hmap
      | some k' =>
        simp only [hk_eq, Option.map_some, Option.some.injEq] at hmap; subst tf₂
        dsimp only [denote] at hwp ⊢
        cases hd : denoteArgs vs args with | none => rw [hd] at hwp; cases hwp | some args' =>
        rw [hd] at hwp; dsimp only at hwp ⊢; rcases hwp with ⟨P, _E, hG, hP, _hE⟩
        refine fid_frame_unchanged_call hΓ hf_arsn args'
          (fun rv => denote Val Cont k' (pushTup rv vs) ls₂) hG
          (fun rv m_s' m_f' hp hsep' => ?_) hsep
        have hlen_p := pushTup_length rv vs
        exact fid_denote_wp_arsn_lift hΓ hcfg k k' (pushTup rv vs) ls₁ ls₂ (by rw [hlen_p]; omega)
          ((fid_listGet?_pushTup_last rv vs hv_pos).trans hlast) hls (by rw [hlen_p]; exact hk_eq)
          Q₁ Q₂ hQ m_s' ext m_f' hext hsep' (hP rv m_s' hp)
  | .jnz cd t e, tf₂, vs, ls₁, ls₂, hv_pos, hlast, hls, hmap, Q₁, Q₂, hQ,
      m_s, ext, m_f, hext, hsep, hwp => by
    dsimp only [fidTflatMapArsn] at hmap
    cases ht_eq : fidTflatMapArsn vs.length t with | none => simp [ht_eq] at hmap | some t' =>
    cases he_eq : fidTflatMapArsn vs.length e with
    | none => simp [ht_eq, he_eq] at hmap | some e' =>
    simp only [ht_eq, he_eq, Option.some.injEq] at hmap; subst tf₂; dsimp only [denote] at hwp ⊢
    cases hd : denoteArg vs cd with | none => rw [hd] at hwp; cases hwp | some c' =>
    rw [hd] at hwp; dsimp only at hwp ⊢
    exact ⟨fun hc => fid_denote_wp_arsn_lift hΓ hcfg t t' vs ls₁ ls₂ hv_pos hlast hls ht_eq
        Q₁ Q₂ hQ m_s ext m_f hext hsep (hwp.1 hc),
      fun hc => fid_denote_wp_arsn_lift hΓ hcfg e e' vs ls₁ ls₂ hv_pos hlast hls he_eq
        Q₁ Q₂ hQ m_s ext m_f hext hsep (hwp.2 hc)⟩
  | .jump (ts := ts) j args, tf₂, vs, ls₁, ls₂, _, _, hls, hmap, _, _, _,
      m_s, ext, m_f, hext, hsep, hwp => by
    dsimp only [fidTflatMapArsn] at hmap; injection hmap with hmap'; subst tf₂
    dsimp only [denote] at hwp ⊢
    cases hj1 : lookupL ls₁ ts j with | none => rw [hj1] at hwp; cases hwp | some j₁ =>
    cases hj2 : lookupL ls₂ ts j with
    | none => have hs := hls.1 ts j; rw [hj1, hj2] at hs; simp at hs | some j₂ =>
      cases ha : denoteArgs vs args with | none => rw [hj1, ha] at hwp; cases hwp | some args' =>
      rw [hj1, ha] at hwp; dsimp only at hwp ⊢
      exact hls.2 ts j j₁ j₂ hj1 hj2 (vals args') m_s m_f ext hext hsep hwp
  | .ret vs', tf₂, vs, _, _, _, _, _, hmap, Q₁, Q₂, hQ, m_s, ext, m_f, hext, hsep, hwp => by
    dsimp only [fidTflatMapArsn] at hmap; injection hmap with hmap'; subst tf₂
    dsimp only [denote] at hwp ⊢
    cases ha : denoteArgs vs vs' with | none => rw [ha] at hwp; cases hwp | some vs'' =>
    rw [ha] at hwp; dsimp only at hwp ⊢; exact hQ (vals vs'') m_s ext m_f hext hsep hwp
  | .exit _ args, tf₂, vs, _, _, _, _, _, hmap, _, _, _, _, _, _, _, _, hwp => by
    dsimp only [fidTflatMapArsn] at hmap; injection hmap with hmap'; subst tf₂
    dsimp only [denote] at hwp ⊢
    cases ha : denoteArgs vs args <;> (rw [ha] at hwp; cases hwp)
  | .hlt, tf₂, _, _, _, _, _, _, hmap, _, _, _, _, _, _, _, _, hwp => by
    dsimp only [fidTflatMapArsn] at hmap; injection hmap with hmap'; subst tf₂; exact hwp
  | .group bodies k, tf₂, vs, ls₁, ls₂, hv_pos, hlast, hls, hmap, Q₁, Q₂, hQ,
      m_s, ext, m_f, hext, hsep, hwp => by
    dsimp only [fidTflatMapArsn] at hmap
    cases hb_eq : fidTblocksMapArsn vs.length bodies with
    | none => simp [hb_eq] at hmap | some bodies' =>
    cases hk_eq : fidTflatMapArsn vs.length k with
    | none => simp [hb_eq, hk_eq] at hmap
    | some k' =>
      simp only [hb_eq, hk_eq, Option.some.injEq] at hmap; subst tf₂
      dsimp only [denote, wp] at hwp ⊢; intro Js₂ hc₂; let Js₁ := fidLiftTupContHdr c Js₂
      have hls' := fid_labelsLiftRel_pushTup Js₂ hls
      exact fid_denote_wp_arsn_lift hΓ hcfg k k' vs (pushTup Js₁ ls₁) (pushTup Js₂ ls₂)
        hv_pos hlast hls' hk_eq Q₁ Q₂ hQ m_s ext m_f hext hsep (hwp Js₁ (fid_denoteB_wp_arsn_lift
          hΓ hcfg bodies bodies' vs (pushTup Js₁ ls₁) (pushTup Js₂ ls₂)
          hv_pos hlast hls' hb_eq Q₁ Q₂ hQ Js₂ hc₂))
private theorem fid_denoteB_wp_arsn_lift {Γ : Env} (hΓ : FidArsnLiftHyps Γ)
    {c : FullCfg} (hcfg : FullM6HdrCfgOk c) {rs : List Ty} :
    {sig : List (List Ty)} → (tb₁ tb₂ : TBlocks rs sig) →
      (vs : List ((t : Ty) × Val t)) → (ls₁ ls₂ : List ((ts : List Ty) × Cont ts)) →
      0 < vs.length → listGet? vs (vs.length - 1) = some ⟨i64, c.hdr⟩ →
      FidLabelsLiftRel c ls₁ ls₂ → fidTblocksMapArsn vs.length tb₁ = some tb₂ →
      ∀ (Q₁ Q₂ : Post rs), (∀ rv m_s ext m_f, M6HdrExtOk ext →
          (Eq m_s ⋆ array64 (c.hdr - 2304) ext) m_f → Q₁ rv m_s → Q₂ rv m_f) →
        ∀ (Js₂ : Tup Cont sig),
          Closed Γ Q₂ (fun _ _ _ _ => False) (denoteB Val Cont tb₂ vs ls₂) Js₂ →
          Closed fidArsnLiftEnv Q₁ (fun _ _ _ _ => False) (denoteB Val Cont tb₁ vs ls₁)
            (fidLiftTupContHdr c Js₂)
  | [], .nil, tb₂, _, _, _, _, _, _, hmap, _, _, _, (), _ => by
    dsimp only [fidTblocksMapArsn] at hmap; injection hmap with hmap'; subst tb₂; trivial
  | _, .cons (ts := ts) b bs, tb₂, vs, ls₁, ls₂, hv_pos, hlast, hls, hmap, Q₁, Q₂, hQ,
      (J, Js), hc => by
    dsimp only [fidTblocksMapArsn] at hmap
    cases hb_eq : fidTflatMapArsn (vs.length + ts.length) b with
    | none => simp [hb_eq] at hmap
    | some b' =>
      cases hbs_eq : fidTblocksMapArsn vs.length bs with
      | none => simp [hb_eq, hbs_eq] at hmap
      | some bs' =>
        simp only [hb_eq, hbs_eq, Option.some.injEq] at hmap; subst tb₂
        dsimp only [denoteB, Closed] at hc ⊢; refine ⟨fun xs m_s hb ext m_f hext hsep => ?_,
          fid_denoteB_wp_arsn_lift hΓ hcfg bs bs' vs ls₁ ls₂ hv_pos hlast hls hbs_eq Q₁ Q₂ hQ Js
            hc.2⟩
        have hp := pushTup_length xs vs
        exact hc.1 xs m_f (fid_denote_wp_arsn_lift hΓ hcfg b b' (pushTup xs vs) ls₁ ls₂
          (by rw [hp]; omega) ((fid_listGet?_pushTup_last xs vs hv_pos).trans hlast) hls
          (by rw [hp]; exact hb_eq) Q₁ Q₂ hQ m_s ext m_f hext hsep hb)
end
private theorem fid11_deduce_1uip_m6_hdr_aux {Γ : Env} (hΓ : FidArsnLiftHyps Γ)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {cut : Nat}
    {ext : List (BitVec 64)} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {Q : Post [i64]} {X : XPost}
    (hcfg : FullM6HdrCfgOk c) (hext : M6HdrExtOk ext) (hcut : FullCutInvW c F0 F_cur cut s)
    (hlvl : 0 < s.core.cur_level) (hcf : FullConflictOkCut F_cur cut s)
    (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hQ : s6aFidHdrPost c F0 F_cur s R Q) :
    Func.wp Γ fid11Deduce1uipM6HdrFn.body (c.hdr, ()) m Q X := by
  have hmap : fidTflatMapArsn 1 (reifyFunc fid11_deduce_1uip_m6_body) =
      some (reifyFunc fid11Deduce1uipM6HdrFn.body) := by t_kernel_rfl
  rcases fid_sep_split_ext hm with ⟨m_s, hm_s, hsep⟩
  let Q_s : Post [i64] := fun (r, ()) m_s' => ∀ ext' m_f', M6HdrExtOk ext' →
    (Eq m_s' ⋆ array64 (c.hdr - 2304) ext') m_f' → Q (r, ()) m_f'
  have hwp_old : Func.wp fidArsnLiftEnv fid11_deduce_1uip_m6_body
      (c.hdr, ()) m_s Q_s (fun _ _ _ _ => False) :=
    s6a_fid11_deduce_1uip_m6_wp fidArsnLiftEnv ⟨fun _ _ _ _ h => h, fun _ _ _ _ h => h,
      fun _ _ _ _ h => h, fun _ _ _ _ h => h, fun _ _ _ _ h => h, fun _ _ _ _ h => h⟩
      (c.hdr, ()) m_s Q_s (fun _ _ _ _ => False) ⟨c, F0, F_cur, cut, s, R, rfl, hcut, hlvl, hcf,
        hm_s, fun r s' m_s' h1 h2 h3 h4 h5 h6 h7 h8 h9 hm_s' ext' m_f' hext' hsep' =>
          hQ r ext' s' m_f' hext' h1 h2 h3 h4 h5 h6 h7 h8 h9 (fid_sep_join_fullM6Hdr hm_s' hsep')⟩
  have hden_old : wp fidArsnLiftEnv Q_s (fun _ _ _ _ => False)
      (denote Val Cont (reifyFunc fid11_deduce_1uip_m6_body) [⟨i64, c.hdr⟩] []) m_s :=
    Func.renorm_spec fid11_deduce_1uip_m6_wf hwp_old
  have hden_new : wp Γ Q (fun _ _ _ _ => False)
      (denote Val Cont (reifyFunc fid11Deduce1uipM6HdrFn.body) [⟨i64, c.hdr⟩] []) m :=
    fid_denote_wp_arsn_lift hΓ hcfg
      (reifyFunc fid11_deduce_1uip_m6_body) (reifyFunc fid11Deduce1uipM6HdrFn.body)
      [⟨i64, c.hdr⟩] [] [] (by simp) rfl ⟨fun _ _ => rfl, fun _ _ _ _ hj => by cases hj⟩ hmap
      Q_s Q (fun (r, ()) m_s' ext' m_f' hext' hsep' hq => hq ext' m_f' hext' hsep')
      m_s ext m hext hsep hden_old
  have hren_hdr : Func.renorm fid11Deduce1uipM6HdrFn.body = fid11Deduce1uipM6HdrFn.body := by
    t_kernel_rfl
  exact wp_mono (fun _ _ h => h) (fun _ _ _ _ h => False.elim h) _ _
    (by rw [← hren_hdr]; exact hden_new)
/-- Step-13 callee-parametric `WP` lift for `fid11Deduce1uipM6HdrFn.body` against
`FullFidelityStep11.s11Deduce1uipHdrSpec`. -/
theorem full_deduce_1uip_m6_hdr_step13_wp (Γ : Env)
    (hAlit : ∀ a m Q X, Full.fullAnalyzeLitSpec a m Q X →
      Γ "full_analyze_lit" [i64, i32, i32] [.bool] a m Q X)
    (hArsn : ∀ a m Q X, step13AnalyzeRsnHdrSpec a m Q X →
      Γ "full_analyze_rsn_m6_hdr" [i64, i32, i32] [.bool] a m Q X)
    (hClear : ∀ a m Q X, Full.fullClearAnaSpec a m Q X → Γ "full_clear_ana" [i64] [] a m Q X)
    (hOtfsLarge : ∀ a m Q X, step13OtfsLargeSpec a m Q X →
      Γ "full_otfs_large" [i64, i32, i32] [.bool] a m Q X)
    (hOtfsBin : ∀ a m Q X, Full.fullOtfsBinSpec a m Q X →
      Γ "full_otfs_bin" [i64, i32, i32] [.bool] a m Q X)
    (hOtfsSub : ∀ a m Q X, Full.fullOtfsSubsumeSpec a m Q X →
      Γ "full_otfs_subsume" [i64, i32, i64, i64, .bool] [] a m Q X) :
    ∀ a m Q X, FullFidelityStep11.s11Deduce1uipHdrSpec a m Q X →
      Func.wp Γ fid11Deduce1uipM6HdrFn.body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X hs
  rcases FullFidelityStep11.s11Deduce1uipHdrSpec_elim hs with
    ⟨c, F0, F_cur, cut, ext, s, R, rfl, hcfg, hext, hcut, hlvl, hcf, hm, hQ⟩
  exact fid11_deduce_1uip_m6_hdr_aux ⟨hAlit, hArsn, hClear, hOtfsLarge, hOtfsBin, hOtfsSub⟩
    hcfg hext hcut hlvl hcf hm hQ

end Deduce1UipHdrFid
end LeanQbe.T.Examples.Kissat.FullFidelityStep13S6a
