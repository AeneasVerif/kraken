module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S6aLiftsSpec
public import LeanQbe.T.Examples.Kissat.FullM7BveGates
public import LeanQbe.T.Examples.Kissat.FullM7BveGatesProof0
public import LeanQbe.T.Examples.Kissat.FullM6BveFwd
public import LeanQbe.T.Examples.Kissat.FullSpec
import LeanQbe.T.Examples.Kissat.FullFidelityStep13S6aProof3d0
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Examples.Kissat.FullBvaFwdSpec
import LeanQbe.T.Examples.Kissat.FullDenseWatchLemmas1
import LeanQbe.T.Examples.Kissat.FullM6BveFwdProof1
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Wave-4F Step-13 Callee-Parametric WP Lifts — Part 3d (`full_fwd_check_cl_m7_step13_wp`)
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep13S6a

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullBvaFwdHelpers
open LeanQbe.T.Examples.Kissat.Full.FullDenseWatchHelpers
open LeanQbe.T.Examples.Kissat.FullFastBveBudgets
open LeanQbe.T.Examples.Kissat.FullM6BveFwd
open LeanQbe.T.Examples.Kissat.FullM7BveGates
open Kraken.Bedrock2.Test

open scoped FullArenaTactics

local macro "m7_call" h:term : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_))

private abbrev qL {ts rs : List Ty} (op : OpCode ts rs) (args : Tup (Arg Val) ts)
    (k : Tup Val rs → Expr Val Cont [Ty.bool]) : Expr Val Cont [Ty.bool] :=
  Expr.let_ { sig := ts, code := op, args := args } k
private abbrev qA64 (a b : Arg Val i64) := qL (OpCode.add i64) (a, b, ())
private abbrev qS64 (a b : Arg Val i64) := qL (OpCode.sub i64) (a, b, ())
private abbrev qM64 (a b : Arg Val i64) := qL (OpCode.mul i64) (a, b, ())
private abbrev qShl (a b : Arg Val i64) := qL (OpCode.shl i64) (a, b, ())
private abbrev qA32 (a b : Arg Val i32) := qL (OpCode.add i32) (a, b, ())
private abbrev qO32 (a b : Arg Val i32) := qL (OpCode.or i32) (a, b, ())
private abbrev qN32 (a b : Arg Val i32) := qL (OpCode.and i32) (a, b, ())
private abbrev qX32 (a b : Arg Val i32) := qL (OpCode.xor i32) (a, b, ())
private abbrev qZ32 (a : Arg Val i32) := qL (OpCode.zext 32 64) (a, ())
private abbrev qSx (a : Arg Val i32) := qL (OpCode.sext 32 64) (a, ())
private abbrev qTr (a : Arg Val i32) := qL (OpCode.trunc 32 8) (a, ())
private abbrev qC32 (c : CmpOp) (a b : Arg Val i32) := qL (OpCode.cmp c i32 Ty.bool) (a, b, ())
private abbrev qC64 (c : CmpOp) (a b : Arg Val i64) := qL (OpCode.cmp c i64 Ty.bool) (a, b, ())


private abbrev s6aFwdPostFilterExpr (c : FullCfg) (cref hdr sz iv nsz : Val i32)
    (L : Cont [i32, i32]) : Expr Val Cont [Ty.bool] :=
    (qC32 CmpOp.uge (Arg.var (iv, nsz, ()).snd.fst) (Arg.var (hdr, sz, ()).snd.fst) fun p =>
    Expr.jnz (Arg.var p.fst) (Expr.ret (Arg.imm true, ()))
      (qC32 CmpOp.eq (Arg.var (iv, nsz, ()).snd.fst) (Arg.imm 0) fun p =>
      Expr.jnz (Arg.var p.fst)
        (qZ32 (Arg.var (c.hdr, cref, ()).snd.fst) fun p =>
        qM64 (Arg.var p.fst) (Arg.imm 4) fun p =>
        qA64 (Arg.var c.pArena) (Arg.var p.fst) fun p =>
        qO32 (Arg.var (hdr, sz, ()).fst) (Arg.imm 524288) fun p_1 =>
        Expr.store (Arg.var p_1.fst) (Arg.var p.fst)
          (qA64 (Arg.var (c.hdr, cref, ()).fst) (Arg.imm 472) fun p =>
          Expr.load i64 (Arg.var p.fst) fun ld =>
          qA64 (Arg.var ld) (Arg.imm 3) fun p =>
          qZ32 (Arg.var (hdr, sz, ()).snd.fst) fun p_2 =>
          qA64 (Arg.var p.fst) (Arg.var p_2.fst) fun p =>
          qA64 (Arg.var (c.hdr, cref, ()).fst) (Arg.imm 472) fun p_3 =>
          Expr.store (Arg.var p.fst) (Arg.var p_3.fst)
            (qA64 (Arg.var (c.hdr, cref, ()).fst) (Arg.imm 1024) fun p =>
            Expr.store (t := i64) (Arg.imm 1) (Arg.var p.fst) (Expr.ret (Arg.imm false, ())))))
        (qC32 CmpOp.eq (Arg.var (iv, nsz, ()).snd.fst) (Arg.imm 1) fun p =>
        Expr.jnz (Arg.var p.fst)
          (qZ32 (Arg.var (c.hdr, cref, ()).snd.fst) fun p =>
          qM64 (Arg.var p.fst) (Arg.imm 4) fun p =>
          qA64 (Arg.var c.pArena) (Arg.var p.fst) fun p =>
          qO32 (Arg.var (hdr, sz, ()).fst) (Arg.imm 524288) fun p_1 =>
          Expr.store (Arg.var p_1.fst) (Arg.var p.fst)
            (qA64 (Arg.var (c.hdr, cref, ()).fst) (Arg.imm 472) fun p =>
            Expr.load i64 (Arg.var p.fst) fun ld =>
            qA64 (Arg.var ld) (Arg.imm 3) fun p =>
            qZ32 (Arg.var (hdr, sz, ()).snd.fst) fun p_2 =>
            qA64 (Arg.var p.fst) (Arg.var p_2.fst) fun p =>
            qA64 (Arg.var (c.hdr, cref, ()).fst) (Arg.imm 472) fun p_3 =>
            Expr.store (Arg.var p.fst) (Arg.var p_3.fst)
              (qSx (Arg.imm 0) fun p =>
              qM64 (Arg.var p.fst) (Arg.imm 4) fun p =>
              qA64 (Arg.var c.pTmp) (Arg.var p.fst) fun p =>
              Expr.load i32 (Arg.var p.fst) fun ld =>
              Expr.call (as := [i64, i32]) (bs := [.bool]) "full_add_unit"
                (Arg.var (c.hdr, cref, ()).fst, Arg.var ld, ())
                fun p =>
              Expr.jnz (Arg.var p.fst)
                (Expr.call (as := [i64]) (bs := [.bool]) "full_dense_flush_units_m7"
                  (Arg.var (c.hdr, cref, ()).fst, ()) fun p
                  =>
                Expr.ret (Arg.var p.fst, ())) (Expr.ret (Arg.imm false, ())))))
          (qC32 CmpOp.eq (Arg.var (iv, nsz, ()).snd.fst) (Arg.imm 2) fun p =>
          Expr.jnz (Arg.var p.fst)
            (qSx (Arg.imm 0) fun p =>
            qM64 (Arg.var p.fst) (Arg.imm 4) fun p =>
            qA64 (Arg.var c.pTmp) (Arg.var p.fst) fun p =>
            Expr.load i32 (Arg.var p.fst) fun ld =>
            qSx (Arg.imm 1) fun p =>
            qM64 (Arg.var p.fst) (Arg.imm 4) fun p =>
            qA64 (Arg.var c.pTmp) (Arg.var p.fst) fun p =>
            Expr.load i32 (Arg.var p.fst) fun ld_1 =>
            Expr.call (as := [i64, i32, i32]) (bs := [i64]) "full_add_bin"
              (Arg.var (c.hdr, cref, ()).fst, Arg.var ld,
              Arg.var ld_1, ())
              fun p =>
            qC64 CmpOp.eq (Arg.var p.fst) (Arg.imm 20) fun p_1 =>
            Expr.jnz (Arg.var p_1.fst) (Expr.ret (Arg.imm false, ()))
              (qC64 CmpOp.eq (Arg.var p.fst) (Arg.imm 2) fun p =>
              Expr.jnz (Arg.var p.fst) (Expr.ret (Arg.imm true, ()))
                (qZ32 (Arg.var (c.hdr, cref, ()).snd.fst) fun p =>
                qM64 (Arg.var p.fst) (Arg.imm 4) fun p =>
                qA64 (Arg.var c.pArena) (Arg.var p.fst) fun p =>
                qO32 (Arg.var (hdr, sz, ()).fst) (Arg.imm 524288) fun p_2 =>
                qO32 (Arg.var p_2.fst) (Arg.imm 16777216) fun p_3 =>
                Expr.store (Arg.var p_3.fst) (Arg.var p.fst)
                  (qZ32 (Arg.var (c.hdr, cref, ()).snd.fst) fun p =>
                  qA64 (Arg.var p.fst) (Arg.imm 3) fun p =>
                  qM64 (Arg.var p.fst) (Arg.imm 4) fun p =>
                  qA64 (Arg.var c.pArena) (Arg.var p.fst) fun p =>
                  Expr.store (Arg.var ld) (Arg.var p.fst)
                    (qZ32 (Arg.var (c.hdr, cref, ()).snd.fst) fun p =>
                    qA64 (Arg.var p.fst) (Arg.imm 4) fun p =>
                    qM64 (Arg.var p.fst) (Arg.imm 4) fun p =>
                    qA64 (Arg.var c.pArena) (Arg.var p.fst) fun p =>
                    Expr.store (Arg.var ld_1) (Arg.var p.fst)
                      (qA64 (Arg.var (c.hdr, cref, ()).fst) (Arg.imm 472) fun p =>
                      Expr.load i64 (Arg.var p.fst) fun ld =>
                      qA64 (Arg.var ld) (Arg.imm 3) fun p =>
                      qZ32 (Arg.var (hdr, sz, ()).snd.fst) fun p_4 =>
                      qA64 (Arg.var p.fst) (Arg.var p_4.fst) fun p =>
                      qA64 (Arg.var (c.hdr, cref, ()).fst) (Arg.imm 472) fun p_5 =>
                      Expr.store (Arg.var p.fst) (Arg.var p_5.fst)
                        (Expr.call (as := [i64]) (bs := [.bool]) "full_dense_flush_units_m7"
                          (Arg.var (c.hdr, cref, ()).fst, ())
                          fun p =>
                        Expr.ret (Arg.var p.fst, ()))))))))
            (Expr.group (fun (Js : Tup Cont [[i32]]) =>
      Blocks.cons (fun (p : Tup Val [i32]) =>
                qC32 CmpOp.ult (Arg.var p.fst) (Arg.var (iv, nsz, ()).snd.fst) fun p_1 =>
                Expr.jnz (Arg.var p_1.fst)
                  (qZ32 (Arg.var (c.hdr, cref, ()).snd.fst) fun p_2 =>
                  qA64 (Arg.var p_2.fst) (Arg.imm 3) fun p_3 =>
                  qZ32 (Arg.var p.fst) fun p_4 =>
                  qA64 (Arg.var p_3.fst) (Arg.var p_4.fst) fun p_5 =>
                  qM64 (Arg.var p_5.fst) (Arg.imm 4) fun p_6 =>
                  qA64 (Arg.var c.pArena) (Arg.var p_6.fst) fun p_7 =>
                  qZ32 (Arg.var p.fst) fun p_8 =>
                  qM64 (Arg.var p_8.fst) (Arg.imm 4) fun p_9 =>
                  qA64 (Arg.var c.pTmp) (Arg.var p_9.fst) fun p_10 =>
                  Expr.load i32 (Arg.var p_10.fst) fun ld =>
                  Expr.store (Arg.var ld) (Arg.var p_7.fst)
                    (qA32 (Arg.var p.fst) (Arg.imm 1) fun p =>
                    Expr.jump Js.fst (Arg.var p.fst, ())))
                  (qZ32 (Arg.var (c.hdr, cref, ()).snd.fst) fun p =>
                  qA64 (Arg.var p.fst) (Arg.imm 2) fun p =>
                  qM64 (Arg.var p.fst) (Arg.imm 4) fun p =>
                  qA64 (Arg.var c.pArena) (Arg.var p.fst) fun p =>
                  Expr.store (Arg.var (iv, nsz, ()).snd.fst) (Arg.var p.fst)
                    (qZ32 (Arg.var (c.hdr, cref, ()).snd.fst) fun p =>
                    qA64 (Arg.var p.fst) (Arg.imm 1) fun p =>
                    qM64 (Arg.var p.fst) (Arg.imm 4) fun p =>
                    qA64 (Arg.var c.pArena) (Arg.var p.fst) fun p =>
                    Expr.store (t := i32) (Arg.imm 2) (Arg.var p.fst)
                      (Expr.group (fun (_Js : Tup Cont [[i32]]) =>
      Blocks.cons (fun (p : Tup Val [i32]) =>
                          qO32 (Arg.var p.fst) (Arg.imm 16777216) fun p =>
                          qZ32 (Arg.var (c.hdr, cref, ()).snd.fst) fun p_2 =>
                          qM64 (Arg.var p_2.fst) (Arg.imm 4) fun p_3 =>
                          qA64 (Arg.var c.pArena) (Arg.var p_3.fst) fun p_4 =>
                          Expr.store (Arg.var p.fst) (Arg.var p_4.fst)
                            (Expr.jump (L, ()).fst
                              (Arg.var p.fst, Arg.var (iv, nsz, ()).snd.fst, ()))) Blocks.nil) fun
                        Js =>
                      qN32 (Arg.var (hdr, sz, ()).fst) (Arg.imm 8388608) fun p =>
                      qC32 CmpOp.eq (Arg.var p.fst) (Arg.imm 0) fun p =>
                      Expr.jnz (Arg.var p.fst)
                        (qZ32 (Arg.var (c.hdr, cref, ()).snd.fst) fun p =>
                        qA64 (Arg.var p.fst) (Arg.imm 3) fun p =>
                        qZ32 (Arg.var (hdr, sz, ()).snd.fst) fun p_2 =>
                        qA64 (Arg.var p.fst) (Arg.var p_2.fst) fun p =>
                        qS64 (Arg.var p.fst) (Arg.imm 1) fun p =>
                        qM64 (Arg.var p.fst) (Arg.imm 4) fun p =>
                        qA64 (Arg.var c.pArena) (Arg.var p.fst) fun p =>
                        Expr.store (t := i32) (Arg.imm 4294967295) (Arg.var p.fst)
                          (qO32 (Arg.var (hdr, sz, ()).fst) (Arg.imm 8388608) fun p =>
                          qZ32 (Arg.var (c.hdr, cref, ()).snd.fst) fun p_3 =>
                          qM64 (Arg.var p_3.fst) (Arg.imm 4) fun p_4 =>
                          qA64 (Arg.var c.pArena) (Arg.var p_4.fst) fun p_5 =>
                          Expr.store (Arg.var p.fst) (Arg.var p_5.fst)
                            (Expr.jump Js.fst (Arg.var p.fst, ()))))
                        (Expr.jump Js.fst (Arg.var (hdr, sz, ()).fst, ())))))) Blocks.nil) fun Js
              =>
            Expr.jump Js.fst (Arg.imm 0, ()))))))

private theorem s6a_fwd_post_filter_wp (Γ : Env)
    (hAddUnit : ∀ a m Q X, fullAddUnitSpec a m Q X →
      Γ "full_add_unit" [i64, i32] [.bool] a m Q X)
    (hAddBin : ∀ a m Q X, fullAddBinSpec a m Q X →
      Γ "full_add_bin" [i64, i32, i32] [i64] a m Q X)
    (hFlushUnits : ∀ a m Q X, fullDenseFlushUnitsM6Spec a m Q X →
      Γ "full_dense_flush_units_m7" [i64] [.bool] a m Q X)
    (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s0 st sf' : FullState)
    (R : Mem 64 → Prop) (cref hdr sz iv nsz : Val i32) (mf : Mem 64)
    (Q : Post [Ty.bool]) (X : XPost) (L : Cont [i32, i32])
    (hQ : ∀ ok s' m', FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s0.core.cur_vars →
      s'.core.arena_len = s0.core.arena_len → s'.core.fuel = s0.core.fuel →
      fullArenaClauseRefs s' = fullArenaClauseRefs s0 →
      s'.scratch.tarjan_mark = s0.scratch.tarjan_mark →
      s'.scratch.red_refs = s0.scratch.red_refs →
      (ok = false → F0.Unsat) → (FullMem c s' ⋆ R) m' → Q (ok, ()) m')
    (hL : ∀ n' xs m', n' < sz.toNat →
      (match xs with
      | (hdr, sz, ()) => ∃ st : FullState,
        n' = sz.toNat ∧ 3 ≤ sz.toNat ∧ FullDenseInvW c F0 F_cur st ∧
        st.core.cur_vars = s0.core.cur_vars ∧ st.core.arena_len = s0.core.arena_len ∧
        st.core.fuel = s0.core.fuel ∧ fullArenaClauseRefs st = fullArenaClauseRefs s0 ∧
        st.scratch.tarjan_mark = s0.scratch.tarjan_mark ∧
        st.scratch.red_refs = s0.scratch.red_refs ∧
        hdr = fullArenaHdr st cref.toNat ∧ sz.toNat = fullArenaClauseSizeCore st.core cref.toNat ∧
        fullArenaClauseGarb st cref.toNat = false ∧ (FullMem c st ⋆ R) m') →
      L xs m')
    (hmx : c.max_vars < 2 * 2 ^ 28) (harc : c.arena_cap < 2 * 2 ^ 28)
    (hsz3 : 3 ≤ sz.toNat) (hdwt : FullDenseInvW c F0 F_cur st)
    (hcvt : st.core.cur_vars = s0.core.cur_vars) (halt : st.core.arena_len = s0.core.arena_len)
    (hflt : st.core.fuel = s0.core.fuel) (hrefst : fullArenaClauseRefs st = fullArenaClauseRefs s0)
    (htmkt : st.scratch.tarjan_mark = s0.scratch.tarjan_mark)
    (hrrt : st.scratch.red_refs = s0.scratch.red_refs)
    (hhdrt : hdr = fullArenaHdr st cref.toNat)
    (hszt : sz.toNat = fullArenaClauseSizeCore st.core cref.toNat)
    (hngt : fullArenaClauseGarb st cref.toNat = false)
    (href_t : cref.toNat ∈ fullArenaClauseRefs st)
    (hsz_le_cv : sz.toNat ≤ st.core.cur_vars)
    (hdw_f' : FullDenseInvW c F0 F_cur sf') (href_u : cref.toNat ∈ fullArenaClauseRefs sf')
    (har_len_u : cref.toNat < sf'.core.arena.length)
    (hcr_aru : (cref.setWidth 64).toNat < sf'.core.arena.length)
    (harf : sf'.core.arena = st.core.arena)
    (hcvf : sf'.core.cur_vars = st.core.cur_vars) (half : sf'.core.arena_len = st.core.arena_len)
    (hflf : sf'.core.fuel = st.core.fuel)
      (hrefsf : fullArenaClauseRefs sf' = fullArenaClauseRefs st)
    (hhdr_f : hdr = fullArenaHdr sf' cref.toNat)
    (hsf'_tm_st : sf'.scratch.tarjan_mark = st.scratch.tarjan_mark)
    (hsf'_rr_st : sf'.scratch.red_refs = st.scratch.red_refs)
    (htl' : sf'.core.tmp.length = c.max_vars) (_hnsz_le : nsz.toNat ≤ iv.toNat)
    (hmf : (FullMem c sf' ⋆ R) mf)
    (hi_eq : iv.toNat = sz.toNat) (htmp_ent : (cnfOfClauses F_cur).EntailsClause
      (cnfClause ((sf'.core.tmp.take nsz.toNat).map BitVec.toNat)))
    (htmp_nd : (((sf'.core.tmp.take nsz.toNat).map BitVec.toNat).map (· / 2)).Nodup)
    (htmp_lt : ∀ l ∈ (sf'.core.tmp.take nsz.toNat).map BitVec.toNat, l < 2 * sf'.core.cur_vars) :
    wp Γ Q X (s6aFwdPostFilterExpr c cref hdr sz iv nsz L) mf := by
  have hsf'_tm : sf'.scratch.tarjan_mark = s0.scratch.tarjan_mark := hsf'_tm_st.trans htmkt
  have hsf'_rr : sf'.scratch.red_refs = s0.scratch.red_refs := hsf'_rr_st.trans hrrt
  have hwf_t := hdwt.2.1.arena.refs_wf cref.toNat href_t
  have hal_t := hdwt.1.core_ok.arena_len_le
  have hwf_u := hdw_f'.2.1.arena.refs_wf cref.toNat href_u
  have hal_u := hdw_f'.1.core_ok.arena_len_le
  dsimp only [s6aFwdPostFilterExpr, qL, qA64, qS64, qM64, qShl, qA32, qO32, qN32, qX32,
    qZ32, qSx, qTr, qC32, qC64]
  c0_hsplit
  · -- `nsz >= sz`: no-op return `true`
    c0_hsteps!
    exact hQ true sf' mf hdw_f' (hcvf.trans hcvt) (half.trans halt)
      (hflf.trans hflt) (hrefsf.trans hrefst) hsf'_tm hsf'_rr (fun h => by cases h) hmf
  · have hnsz_lt_sz : nsz.toNat < sz.toNat := by omega
    c0_hsplit
    · -- `nsz == 0`: empty clause entailed → UNSAT!
      have hnsz0 : nsz.toNat = 0 := by rw [hc]; rfl
      rw [hnsz0, List.take_zero, List.map_nil] at htmp_ent
      have hunsat : (cnfOfClauses F_cur).Unsat :=
        m7_p3_unsat_of_entails_nil htmp_ent
      c0_hsteps!
      let ag' := sf'.core.arena_garbage + 3#64 + sz.setWidth 64
      let ar' := sf'.core.arena.set (cref.setWidth 64).toNat (hdr ||| 0x00080000#32)
      let smg : FullState :=
        { sf' with core :=
          { sf'.core with arena := ar', arena_garbage := ag' } }
      have hmg := m6_fullDenseInvW_markGarb hdw_f' href_u (arena' := ar')
        (ag' := ag') (by simp [ar', hdw_f'.1.core_ok.arena_len_arr]) (Or.inl (by
          dsimp only [ar']; rw [m6_zext32_toNat, hhdr_f]
          exact List.getElem?_set_self har_len_u))
        (fun idx hne _ => by
          dsimp only [ar']; rw [m6_zext32_toNat]
          exact List.getElem?_set_ne hne.symm)
      let sinc := { smg with core := { smg.core with inconsistent := 1#64 } }
      exact hQ false sinc _ (m6_fullDenseInvW_set_inc hmg.1 hunsat)
        (hcvf.trans hcvt) (half.trans halt) (hflf.trans hflt)
        (hmg.2.trans (hrefsf.trans hrefst)) hsf'_tm hsf'_rr
        (fun _ => hdw_f'.2.1.ext_sound.2 hunsat) hm
    · c0_hsplit
      · -- `nsz == 1`: unit clause → mark `PH_GARB`, `add_unit`, `flush_units`
        have hnsz1 : nsz.toNat = 1 := by rw [hc]; rfl
        have h0_tmp : 0 < sf'.core.tmp.length := by
          rw [htl']; have := hdwt.1.core_ok.cur_vars_le; omega
        have htake1 : (sf'.core.tmp.take nsz.toNat).map BitVec.toNat =
            [(sf'.core.tmp[0]'h0_tmp).toNat] := by
          rw [hnsz1, show sf'.core.tmp.take 1 = [sf'.core.tmp[0]'h0_tmp] from
            match sf'.core.tmp, h0_tmp with | _ :: _, _ => rfl]
          rfl
        rw [htake1] at htmp_ent
        c0_hsteps_nogrp
        let ag' := sf'.core.arena_garbage + 3#64 + sz.setWidth 64
        let ar' := sf'.core.arena.set (cref.setWidth 64).toNat (hdr ||| 0x00080000#32)
        let smg : FullState :=
          { sf' with core :=
            { sf'.core with arena := ar', arena_garbage := ag' } }
        have hmg := m6_fullDenseInvW_markGarb hdw_f' href_u (arena' := ar')
          (ag' := ag') (by simp [ar', hdw_f'.1.core_ok.arena_len_arr]) (Or.inl (by
            dsimp only [ar']; rw [m6_zext32_toNat, hhdr_f]
            exact List.getElem?_set_self har_len_u))
          (fun idx hne _ => by
            dsimp only [ar']; rw [m6_zext32_toNat]
            exact List.getElem?_set_ne hne.symm)
        have ht0_lt : (sf'.core.tmp[0]'h0_tmp).toNat < 2 * smg.core.cur_vars :=
          htmp_lt _ (by rw [htake1]; exact List.mem_singleton_self _)
        m7_call hAddUnit
        refine ⟨c, F0, F_cur, smg, R, rfl, hmg.1.1, hmg.1.2.1, fun _ => htmp_ent, hm, ?_⟩
        intro ok vals' flags' lvl' rsns' trl' tp' te' prop' cl' unass' unfl'
          inc' phases' ta' ba' pt' pb' hp' ps' hl' qsi' qss' m_au s_au
          hlen_au hw_au hcl_au hfu_au _ hm_au
        have hdw_au := m6_fullDenseInvW_of_addUnit hmg.1 hlen_au hw_au hcl_au
          rfl rfl rfl rfl rfl rfl rfl
        c0_hsplit
        · c0_hsteps_nogrp
          m7_call hFlushUnits
          refine fullDenseFlushUnitsM6Spec_intro rfl hdw_au hm_au ?_
          intro ok2 s2 m2 hdw2 hcv2 hal2 hfl2 hrefs2 htmk2 hrr2 _ _ _ _ hf2 hm2
          c0_hsteps!
          exact hQ ok2 s2 m2 hdw2 (hcv2.trans (hcvf.trans hcvt))
            (hal2.trans (half.trans halt)) (hfl2.trans (hflf.trans hflt))
            (hrefs2.trans (hmg.2.trans (hrefsf.trans hrefst))) (htmk2.trans hsf'_tm)
            (hrr2.trans hsf'_rr) hf2 hm2
        · c0_hsteps!
          exact hQ false s_au m_au hdw_au (hcvf.trans hcvt) (half.trans halt)
            (hflf.trans hflt) (hmg.2.trans (hrefsf.trans hrefst)) hsf'_tm hsf'_rr
            (fun _ => (hfu_au ht0_lt (by simpa using hc)).1) hm_au
      · c0_hsplit
        · -- `nsz == 2`: OOM-safe `full_add_bin`, then `PH_GARB | PH_SUBSUME`
          have hnsz2 : nsz.toNat = 2 := by rw [hc]; rfl
          have h0_tmp : 0 < sf'.core.tmp.length := by
            rw [htl']; have := hdwt.1.core_ok.cur_vars_le; omega
          have h1_tmp : 1 < sf'.core.tmp.length := by
            rw [htl']; have := hdwt.1.core_ok.cur_vars_le; omega
          have htake2 : (sf'.core.tmp.take nsz.toNat).map BitVec.toNat =
              [(sf'.core.tmp[0]'h0_tmp).toNat, (sf'.core.tmp[1]'h1_tmp).toNat] := by
            rw [hnsz2, show sf'.core.tmp.take 2 =
                [sf'.core.tmp[0]'h0_tmp, sf'.core.tmp[1]'h1_tmp] from
              match sf'.core.tmp, h0_tmp, h1_tmp with | _ :: _ :: _, _, _ => rfl]
            rfl
          rw [htake2] at htmp_ent
          c0_hsteps_nogrp
          m7_call hAddBin
          refine ⟨c, F0, F_cur, sf', R, rfl, hdw_f'.1, hdw_f'.2.1,
            hdw_f'.2.2.2.2.2.1, fun _ _ => htmp_ent, hmf, ?_⟩
          intro br vals' flags' lvl' rsns' trl' tp' te' unass' unfl' wvec'
            wstk' wlen' wu' nb' oom' inc' phases' wsort' m_b s_b hlen_b hw_b hbr_b h20_b _ hm_b
          have hdw_b : FullDenseInvW c F0 F_cur s_b :=
            m7_p3_fullDenseInvW_of_addBin hdw_f' hlen_b hw_b rfl rfl rfl rfl rfl rfl rfl rfl
          c0_hsplit
          · c0_hsteps!
            exact hQ false s_b m_b hdw_b (hcvf.trans hcvt) (half.trans halt)
              (hflf.trans hflt) (hrefsf.trans hrefst) hsf'_tm hsf'_rr
              (fun _ => (h20_b hc).1) hm_b
          · c0_hsplit
            · c0_hsteps!
              exact hQ true s_b m_b hdw_b (hcvf.trans hcvt) (half.trans halt)
                (hflf.trans hflt) (hrefsf.trans hrefst) hsf'_tm hsf'_rr
                (fun h => by cases h) hm_b
            · have hcr3_ar : (cref.setWidth 64 + 3#64).toNat < s_b.core.arena.length := by
                rw [hdw_b.1.core_ok.arena_len_arr]; c0_bound
              have hcr4_ar : (cref.setWidth 64 + 4#64).toNat < s_b.core.arena.length := by
                rw [hdw_b.1.core_ok.arena_len_arr]; c0_bound
              c0_hsteps_nogrp
              have hmg := m7_p3_fwd_nsz2_garb_post hdw_b href_u (by
                change fullArenaClauseSizeCore sf'.core cref.toNat = sz.toNat
                unfold fullArenaClauseSizeCore; rw [harf]; exact hszt.symm) (by
                  unfold fullArenaHdr fullArenaHdrCore
                  change sf'.core.arena[cref.toNat]?.getD 0#32 = hdr
                  rw [harf]; exact hhdrt.symm) h0_tmp h1_tmp
              m7_call hFlushUnits
              refine fullDenseFlushUnitsM6Spec_intro rfl hmg.1 hm ?_
              intro ok2 s2 m2 hdw2 hcv2 hal2 hfl2 hrefs2 htmk2 hrr2 _ _ _ _ hf2 hm2
              c0_hsteps!
              exact hQ ok2 s2 m2 hdw2 (hcv2.trans (hcvf.trans hcvt))
                (hal2.trans (half.trans halt)) (hfl2.trans (hflf.trans hflt))
                (hrefs2.trans (hmg.2.trans (hrefsf.trans hrefst))) (htmk2.trans hsf'_tm)
                (hrr2.trans hsf'_rr) hf2 hm2
        · -- `nsz >= 3`: copy `tmp[0..nsz)` in-place, shrink, set `PH_SUBSUME`
          have hnsz3 : 3 ≤ nsz.toNat := by
            have h0 : nsz.toNat ≠ 0 := fun h =>
              ‹nsz ≠ 0#32› (BitVec.eq_of_toNat_eq h)
            have h1 : nsz.toNat ≠ 1 := fun h =>
              ‹nsz ≠ 1#32› (BitVec.eq_of_toNat_eq h)
            have h2 : nsz.toNat ≠ 2 := fun h =>
              hc (BitVec.eq_of_toNat_eq h)
            omega
          c0_hsteps_nogrp
          refine wp_loop_group (ts := [i32])
            (fun rem_c (ic, ()) mc => ∃ ar_c : List (BitVec 32),
              let sc : FullState :=
                { sf' with core := { sf'.core with arena := ar_c } }
              ar_c.length = c.arena_cap ∧ ic.toNat ≤ nsz.toNat ∧ rem_c = nsz.toNat - ic.toNat ∧
              (∀ idx, idx < cref.toNat + 3 ∨ cref.toNat + 3 + ic.toNat ≤ idx →
                ar_c[idx]? = sf'.core.arena[idx]?) ∧
              (∀ idx < ic.toNat, ar_c[cref.toNat + 3 + idx]? = sf'.core.tmp[idx]?) ∧
              (FullMem c sc ⋆ R) mc)
            ?_ ?_
          · rintro Lc rem_c ⟨ic, ⟨⟩⟩ mc hLc ⟨ar_c, harc_l, hic_le, rfl, hout_c, hcopy_c, hmc⟩
            c0_hsplit
            · have hic_lt : ic.toNat < nsz.toNat := hc
              have hic_tmp : (ic.setWidth 64).toNat < sf'.core.tmp.length := by
                rw [htl', m6_zext32_toNat]
                have := hdwt.1.core_ok.cur_vars_le; omega
              have hic_ar : (cref.setWidth 64 + 3#64 + ic.setWidth 64).toNat <
                  ar_c.length := by rw [harc_l]; c0_bound
              have hic1 : (ic + 1#32).toNat = ic.toNat + 1 := by c0_bound
              have hcp := m7_p3_copy_iter hdwt href_t hszt hnsz_lt_sz
                harc_l htl' hout_c hcopy_c hic_lt hic_tmp hic_ar hic1
              c0_hsteps!
              exact hLc (nsz.toNat - (ic + 1#32).toNat) (ic + 1#32, ()) _
                (by omega) ⟨_, hcp.1, hcp.2.1, rfl, hcp.2.2.1, hcp.2.2.2, hm⟩
            · have hic_eq : ic.toNat = nsz.toNat := by omega
              have hcr2_arc : (cref.setWidth 64 + 2#64).toNat <
                  ar_c.length := by rw [harc_l]; c0_bound
              have hcr1_arc : (cref.setWidth 64 + 1#64).toNat <
                  ar_c.length := by rw [harc_l]; c0_bound
              c0_hsteps_nogrp
              let ar_w := (ar_c.set (cref.setWidth 64 + 2#64).toNat nsz).set
                (cref.setWidth 64 + 1#64).toNat 2#32
              -- Optional `PH_SHRK` sentinel + bit23 write
              refine wp_join_state (ts := [i32]) (α := BitVec 32 × List (BitVec 32))
                (fun x => (x.1, ())) (fun x ms' =>
                  let sx : FullState :=
                    { sf' with core := { sf'.core with arena := x.2 } }
                  FullDenseInvW c F0 F_cur sx ∧
                  fullArenaClauseRefs sx = fullArenaClauseRefs sf' ∧
                  x.1 = fullArenaHdr sx cref.toNat ∧
                  fullArenaClauseSizeCore sx.core cref.toNat = nsz.toNat ∧
                  fullArenaClauseGarb sx cref.toNat = false ∧ (FullMem c sx ⋆ R) ms')
                (fun _ ⟨hdr_s, ar_s⟩ ms' ⟨hdws, hrefss, hhdrs, hszs, hngs, hms'⟩ => by
                  have href_s : cref.toNat ∈ fullArenaClauseRefs
                      { sf' with core := { sf'.core with arena := ar_s } } :=
                    hrefss.symm ▸ href_u
                  have hcr_ars : (cref.setWidth 64).toNat < ar_s.length := by
                    rw [hdws.1.core_ok.arena_len_arr, m6_zext32_toNat]; omega
                  c0_hsteps!
                  obtain ⟨hdw_sub, hrefs_sub', hhdr_sub, hsz_sub, hng_sub⟩ :=
                    m7_p3_fwd_nsz3_sub_post hdws href_s hhdrs hszs hngs
                  let v_sub := hdr_s ||| 0x01000000#32
                  let s_sub : FullState :=
                    { sf' with core := { sf'.core with
                      arena := ar_s.set (cref.setWidth 64).toNat v_sub } }
                  exact hL nsz.toNat (v_sub, nsz, ()) _ hnsz_lt_sz
                    ⟨s_sub, rfl, hnsz3, hdw_sub, hcvf.trans hcvt,
                     half.trans halt, hflf.trans hflt,
                     hrefs_sub'.trans (hrefss.trans (hrefsf.trans hrefst)), hsf'_tm, hsf'_rr,
                     hhdr_sub, hsz_sub, hng_sub, hm⟩)
                (fun Js hJs => by
                  have hsz_sf' : fullArenaClauseSizeCore sf'.core cref.toNat = sz.toNat := by
                    change fullArenaClauseSizeCore sf'.core cref.toNat = sz.toNat
                    unfold fullArenaClauseSizeCore; rw [harf]; exact hszt.symm
                  have hhdr_sf' : fullArenaHdrCore sf'.core cref.toNat = hdr :=
                    hhdr_f.symm
                  have hpad_orig :=
                    m7_p3_fwd_pad_orig hdwt hdw_f' href_t hngt hszt (nsz := nsz) harf
                  have hcr0_eq : (cref.setWidth 64).toNat = cref.toNat :=
                    m6_zext32_toNat cref
                  have hcr1_eq : (cref.setWidth 64 + 1#64).toNat = cref.toNat + 1 := by c0_bound
                  have hcr2_eq : (cref.setWidth 64 + 2#64).toNat = cref.toNat + 2 := by c0_bound
                  have hsent_eq : (cref.setWidth 64 + 3#64 + sz.setWidth 64 -
                      1#64).toNat = cref.toNat + 3 + sz.toNat - 1 := by
                    c0_bound
                  have hcr1_eq' : (cref.setWidth 64 + (1 : BitVec 64)).toNat
                      = cref.toNat + 1 := hcr1_eq
                  have hcr2_eq' : (cref.setWidth 64 + (2 : BitVec 64)).toNat
                      = cref.toNat + 2 := hcr2_eq
                  have hsent_eq' : (cref.setWidth 64 + (3 : BitVec 64) +
                      sz.setWidth 64 - (1 : BitVec 64)).toNat =
                      cref.toNat + 3 + sz.toNat - 1 := hsent_eq
                  have h2_32 : (2 : BitVec 32) = 2#32 := rfl
                  have hfff_32 : (4294967295 : BitVec 32) = 0xFFFFFFFF#32 :=
                    rfl
                  have h80_32 : (8388608 : BitVec 32) = 0x00800000#32 := rfl
                  have hcv_f' : sz.toNat ≤ sf'.core.cur_vars := by
                    change sz.toNat ≤ sf'.core.cur_vars
                    rw [hcvf]; exact hsz_le_cv
                  have hngt_sf' : fullArenaClauseGarb sf' cref.toNat = false := by
                    unfold fullArenaClauseGarb fullArenaClauseGarbCore
                    rw [hhdr_sf']
                    change (fullArenaHdr st cref.toNat &&& 0x00080000#32 !=
                      0#32) = false at hngt
                    rwa [← hhdrt] at hngt
                  c0_hsplit
                  · have hsh0 : (hdr &&& 0x00800000#32) = 0#32 := hc
                    have hsent_ar : (cref.setWidth 64 + 3#64 + sz.setWidth 64 -
                          1#64).toNat < ar_w.length := by
                      rw [hsent_eq]; simp only [ar_w, List.length_set, harc_l]; omega
                    have hcr_arw : (cref.setWidth 64).toNat < ar_w.length := by
                      simp only [ar_w, List.length_set, harc_l, hcr0_eq]; omega
                    c0_hsteps!
                    have hstep := m7_p3_check_cl_shrink0 hdw_f' href_u
                      hngt_sf' hnsz3 (by omega) hsz_sf' hhdr_sf' hcv_f' htl'
                      harc_l (fun idx hidx => hout_c idx (by omega))
                      (fun k hk => hcopy_c k (by omega)) htmp_lt htmp_nd
                      htmp_ent hpad_orig hsh0 hcr2_eq' hcr1_eq' hsent_eq'
                      hcr0_eq h2_32 hfff_32 h80_32
                    exact hJs (hdr ||| 0x00800000#32, _) m
                      ⟨hstep.1, hstep.2.1, hstep.2.2.1, hstep.2.2.2.1, hstep.2.2.2.2, hm⟩
                  · have hsh1 : (hdr &&& 0x00800000#32) ≠ 0#32 := hc
                    c0_hsteps!
                    have hstep := m7_p3_check_cl_shrink1 hdw_f' href_u
                      hngt_sf' hnsz3 (by omega) hsz_sf' hhdr_sf' hcv_f' htl'
                      harc_l (fun idx hidx => hout_c idx (by omega))
                      (fun k hk => hcopy_c k (by omega)) htmp_lt htmp_nd
                      htmp_ent hpad_orig hsh1 hcr2_eq' hcr1_eq' h2_32
                    exact hJs (hdr, _) m ⟨hstep.1, hstep.2.1, hstep.2.2.1, hstep.2.2.2.1,
                       hstep.2.2.2.2, hm⟩)
          · intro Lc hLc; c0_hsteps!
            exact hLc nsz.toNat (0#32, ()) mf
              ⟨sf'.core.arena, hdw_f'.1.core_ok.arena_len_arr, Nat.zero_le _,
               by simp, fun _ _ => rfl, fun _ h => by
                 rw [show (0#32).toNat = 0 from rfl] at h; omega, hmf⟩

private abbrev s6aFwdMarkScanExpr (c : FullCfg) (cref hdr sz : Val i32)
    (sat_b : Bool) (drop_b unk_b : Val i32) (Jm : Cont [i32, i32, Ty.bool]) :
    Expr Val Cont [Ty.bool] :=
    (qC32 CmpOp.eq (Arg.var (sat_b, drop_b, unk_b, ()).snd.fst) (Arg.imm 4294967295) fun p =>
    Expr.jnz (Arg.var p.fst)
      (qZ32 (Arg.var (c.hdr, cref, ()).snd.fst) fun p =>
      qA64 (Arg.var p.fst) (Arg.imm 3) fun p =>
      qM64 (Arg.var p.fst) (Arg.imm 4) fun p =>
      qA64 (Arg.var c.pArena) (Arg.var p.fst) fun p =>
      Expr.load i32 (Arg.var p.fst) fun ld =>
      qZ32 (Arg.var ld) fun p =>
      qSx (Arg.imm 1) fun p_1 =>
      qShl (Arg.var p.fst) (Arg.var p_1.fst) fun p =>
      qA64 (Arg.var p.fst) (Arg.imm 1) fun p =>
      qM64 (Arg.var p.fst) (Arg.imm 4) fun p =>
      qA64 (Arg.var c.pWvec) (Arg.var p.fst) fun p =>
      Expr.load i32 (Arg.var p.fst) fun ld_1 =>
      Expr.group
        (fun (Js : Tup Cont [[i32, i32, i32]]) =>
          Blocks.cons (fun (p : Tup Val [i32, i32, i32]) => qC32 CmpOp.ult (Arg.var p.fst)
            (Arg.var (hdr, sz, ()).snd.fst)
          fun p_2 =>
          Expr.jnz (Arg.var p_2.fst)
            (qZ32 (Arg.var (c.hdr, cref, ()).snd.fst) fun p_3 =>
            qA64 (Arg.var p_3.fst) (Arg.imm 3) fun p_4 =>
            qZ32 (Arg.var p.fst) fun p_5 =>
            qA64 (Arg.var p_4.fst) (Arg.var p_5.fst) fun p_6 =>
            qM64 (Arg.var p_6.fst) (Arg.imm 4) fun p_7 =>
            qA64 (Arg.var c.pArena) (Arg.var p_7.fst) fun p_8 =>
            Expr.load i32 (Arg.var p_8.fst) fun ld =>
            qZ32 (Arg.var ld) fun p_9 =>
            qA64 (Arg.var c.pLitMark) (Arg.var p_9.fst) fun p_10 =>
            qTr (Arg.imm 1) fun p_11 =>
            Expr.store (Arg.var p_11.fst) (Arg.var p_10.fst)
              (qZ32 (Arg.var ld) fun p_12 =>
              qSx (Arg.imm 1) fun p_13 =>
              qShl (Arg.var p_12.fst) (Arg.var p_13.fst) fun p_14 =>
              qA64 (Arg.var p_14.fst) (Arg.imm 1) fun p_15 =>
              qM64 (Arg.var p_15.fst) (Arg.imm 4) fun p_16 =>
              qA64 (Arg.var c.pWvec) (Arg.var p_16.fst) fun p_17 =>
              Expr.load i32 (Arg.var p_17.fst) fun ld_2 =>
              Expr.group
                (fun (_Js_1 : Tup Cont [[i32, i32]]) =>
                Blocks.cons
                  (fun (p_18 : Tup Val [i32, i32]) =>
                  qA32 (Arg.var p.fst) (Arg.imm 1) fun p =>
                  Expr.jump Js.fst (Arg.var p.fst, Arg.var p_18.fst, Arg.var p_18.snd.fst, ()))
                  Blocks.nil) fun Js =>
              qC32 CmpOp.ult (Arg.var ld_2) (Arg.var p.snd.snd.fst) fun p_18 =>
              Expr.jnz (Arg.var p_18.fst) (Expr.jump Js.fst (Arg.var ld, Arg.var ld_2, ()))
                (Expr.jump Js.fst (Arg.var p.snd.fst, Arg.var p.snd.snd.fst, ()))))
            (Expr.group
              (fun (_Js : Tup Cont [[i32, i32, .bool]]) =>
                Blocks.cons (fun (p : Tup Val [i32, i32, .bool]) => Expr.group
                  (fun (Js : Tup Cont [[i32]]) => Blocks.cons (fun (p_3 : Tup Val [i32]) =>
                    qC32 CmpOp.ult (Arg.var p_3.fst) (Arg.var (hdr, sz, ()).snd.fst) fun p_4 =>
                    Expr.jnz (Arg.var p_4.fst)
                      (qZ32 (Arg.var (c.hdr, cref, ()).snd.fst) fun p =>
                      qA64 (Arg.var p.fst) (Arg.imm 3) fun p =>
                      qZ32 (Arg.var p_3.fst) fun p_5 =>
                      qA64 (Arg.var p.fst) (Arg.var p_5.fst) fun p =>
                      qM64 (Arg.var p.fst) (Arg.imm 4) fun p =>
                      qA64 (Arg.var c.pArena) (Arg.var p.fst) fun p =>
                      Expr.load i32 (Arg.var p.fst) fun ld =>
                      qZ32 (Arg.var ld) fun p =>
                      qA64 (Arg.var c.pLitMark) (Arg.var p.fst) fun p =>
                      qTr (Arg.imm 0) fun p_6 =>
                      Expr.store (Arg.var p_6.fst) (Arg.var p.fst)
                        (qA32 (Arg.var p_3.fst) (Arg.imm 1) fun p =>
                        Expr.jump Js.fst (Arg.var p.fst, ())))
                      (Expr.jump (Jm, ()).fst
                        (Arg.var p.fst, Arg.var p_3.fst, Arg.var p.snd.snd.fst, ()))) Blocks.nil)
                  fun Js =>
                Expr.jump Js.fst (Arg.imm 0, ())) Blocks.nil) fun Js =>
            Expr.group
              (fun (Js_1 : Tup Cont [[i32]]) =>

                Blocks.cons (fun (p_3 : Tup Val [i32]) => qC32 CmpOp.ult (Arg.var p_3.fst)
                  (Arg.var (hdr, sz, ()).snd.fst)
                fun p_4 =>
                Expr.jnz (Arg.var p_4.fst)
                  (Expr.jnz (Arg.imm false)
                    (Expr.jump Js.fst
                      (Arg.var (sat_b, drop_b, unk_b, ()).snd.fst, Arg.var p_3.fst, Arg.imm false,
                        ()))
                    (qC32 CmpOp.eq (Arg.var (sat_b, drop_b, unk_b, ()).snd.fst) (Arg.imm 4294967295)
                      fun p_5 =>
                    Expr.jnz (Arg.var p_5.fst)
                      (Expr.group
                        (fun (_Js_2 : Tup Cont [[i32]]) =>
                        Blocks.cons
                          (fun (p_6 : Tup Val [i32]) =>
                          Expr.group
                            (fun (_Js_3 : Tup Cont [[i32]]) =>
                            Blocks.cons (fun (p : Tup Val [i32]) =>
                              Expr.call (as := [i64, i32, i32, i32,
                                .bool]) (bs := [i32]) "full_fwd_scan_lit_m7"

                                (Arg.var (c.hdr, cref, ()).fst, Arg.var (c.hdr, cref, ()).snd.fst,
                                  Arg.var (hdr, sz, ()).snd.fst, Arg.var p.fst, Arg.imm true, ())
                                fun p_7 =>
                              qC32 CmpOp.eq (Arg.var p_7.fst) (Arg.imm 4294967294) fun p_8 =>
                              Expr.jnz (Arg.var p_8.fst)
                                (Expr.jump Js.fst
                                  (Arg.var (sat_b, drop_b, unk_b, ()).snd.fst, Arg.var p_3.fst,
                                    Arg.imm true, ()))
                                (qC32 CmpOp.ne (Arg.var p_7.fst) (Arg.imm 4294967295) fun p_9 =>
                                Expr.jnz (Arg.var p_9.fst)
                                  (Expr.jump Js.fst
                                    (Arg.var p_7.fst, Arg.var p_3.fst, Arg.imm false, ()))
                                  (qX32 (Arg.var p.fst) (Arg.imm 1) fun p =>
                                  Expr.call (as := [i64, i32, i32, i32,
                                    .bool]) (bs := [i32]) "full_fwd_scan_lit_m7"

                                    (Arg.var (c.hdr, cref, ()).fst, Arg.var
                                      (c.hdr, cref, ()).snd.fst, Arg.var (hdr, sz, ()).snd.fst,
                                      Arg.var p.fst, Arg.imm false, ()) fun p =>
                                  qC32 CmpOp.eq (Arg.var p.fst) (Arg.imm 4294967294) fun p_10 =>
                                  Expr.jnz (Arg.var p_10.fst)
                                    (Expr.jump Js.fst
                                      (Arg.var (sat_b, drop_b, unk_b, ()).snd.fst, Arg.var
                                        p_3.fst, Arg.imm true, ()))
                                    (qC32 CmpOp.ne (Arg.var p.fst) (Arg.imm 4294967295) fun p_11
                                      =>
                                    Expr.jnz (Arg.var p_11.fst)
                                      (Expr.jump Js.fst
                                        (Arg.var p.fst, Arg.var p_3.fst, Arg.imm false, ()))
                                      (qA32 (Arg.var p_3.fst) (Arg.imm 1) fun p =>
                                      Expr.jump Js_1.fst (Arg.var p.fst, ())))))) Blocks.nil) fun
                            Js =>
                          qC32 CmpOp.ugt (Arg.var p_3.fst) (Arg.imm 0) fun p_7 =>
                          Expr.jnz (Arg.var p_7.fst)
                            (qC32 CmpOp.eq (Arg.var p_6.fst) (Arg.var p.snd.fst) fun p =>
                            Expr.jnz (Arg.var p.fst)
                              (qZ32 (Arg.var (c.hdr, cref, ()).snd.fst) fun p =>
                              qA64 (Arg.var p.fst) (Arg.imm 3) fun p =>
                              qM64 (Arg.var p.fst) (Arg.imm 4) fun p =>
                              qA64 (Arg.var c.pArena) (Arg.var p.fst) fun p =>
                              Expr.load i32 (Arg.var p.fst) fun ld =>
                              Expr.jump Js.fst (Arg.var ld, ()))
                              (Expr.jump Js.fst (Arg.var p_6.fst, ())))
                            (Expr.jump Js.fst (Arg.var p_6.fst, ()))) Blocks.nil) fun Js =>
                      qC32 CmpOp.eq (Arg.var p_3.fst) (Arg.imm 0) fun p_6 =>
                      Expr.jnz (Arg.var p_6.fst) (Expr.jump Js.fst (Arg.var p.snd.fst, ()))
                        (qZ32 (Arg.var (c.hdr, cref, ()).snd.fst) fun p =>
                        qA64 (Arg.var p.fst) (Arg.imm 3) fun p =>
                        qZ32 (Arg.var p_3.fst) fun p_7 =>
                        qA64 (Arg.var p.fst) (Arg.var p_7.fst) fun p =>
                        qM64 (Arg.var p.fst) (Arg.imm 4) fun p =>
                        qA64 (Arg.var c.pArena) (Arg.var p.fst) fun p =>
                        Expr.load i32 (Arg.var p.fst) fun ld =>
                        Expr.jump Js.fst (Arg.var ld, ())))
                      (Expr.jump Js.fst
                        (Arg.var (sat_b, drop_b, unk_b, ()).snd.fst, Arg.var p_3.fst, Arg.imm
                          false, ()))))
                  (Expr.jump Js.fst
                    (Arg.var (sat_b, drop_b, unk_b, ()).snd.fst, Arg.var p_3.fst, Arg.imm false,
                      ()))) Blocks.nil) fun Js =>
            Expr.jump Js.fst (Arg.imm 0, ()))) Blocks.nil) fun Js =>
      Expr.jump Js.fst (Arg.imm 0, Arg.var ld, Arg.var ld_1, ()))
      (Expr.jump (Jm, ()).fst
        (Arg.var (sat_b, drop_b, unk_b, ()).snd.fst, Arg.var
          (sat_b, drop_b, unk_b, ()).snd.snd.fst, Arg.imm false, ())))

private theorem s6a_fwd_mark_scan_wp (Γ : Env)
    (hScanLit : ∀ a m Q X, step13FwdScanLitSpec a m Q X →
      Γ "full_fwd_scan_lit_m7" [i64, i32, i32, i32, .bool] [i32] a m Q X)
    (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (_s0 st : FullState)
    (R : Mem 64 → Prop) (cref hdr sz : Val i32) (sat_b : Bool) (drop_b unk_b : Val i32)
      (m1 : Mem 64)
    (Q : Post [Ty.bool]) (X : XPost) (Jm : Cont [i32, i32, Ty.bool])
    (hJm : ∀ st_1 : Bool × BitVec 32 × BitVec 32 × FullState, ∀ m',
      st_1.2.2.2.core.cur_vars = st.core.cur_vars ∧ st_1.2.2.2.core.arena = st.core.arena ∧
      st_1.2.2.2.core.arena_len = st.core.arena_len ∧ st_1.2.2.2.core.fuel = st.core.fuel ∧
      st_1.2.2.2.scratch = st.scratch ∧ FullDenseInvW c F0 F_cur st_1.2.2.2 ∧
      (st_1.1 = false → st_1.2.1 ≠ 0xFFFFFFFF#32 → (cnfOfClauses F_cur).EntailsClause
        (cnfClause ((fullArenaClauseLits st cref.toNat).filter (· != st_1.2.1.toNat)))) ∧
      (FullMem c st_1.2.2.2 ⋆ R) m' → Jm (st_1.2.1, st_1.2.2.1, st_1.1, ()) m')
    (_hmx : c.max_vars < 2 * 2 ^ 28) (harc : c.arena_cap < 2 * 2 ^ 28)
    (hsz3 : 3 ≤ sz.toNat) (hdwt : FullDenseInvW c F0 F_cur st)
    (_hhdrt : hdr = fullArenaHdr st cref.toNat)
    (hszt : sz.toNat = fullArenaClauseSizeCore st.core cref.toNat)
    (hngt : fullArenaClauseGarb st cref.toNat = false)
    (href_t : cref.toNat ∈ fullArenaClauseRefs st)
    (hm1 : (FullMem c st ⋆ R) m1) (_hc_sat : sat_b = false)
    (hdrop_ent0 : drop_b ≠ 0xFFFFFFFF#32 → (cnfOfClauses F_cur).EntailsClause
      (cnfClause ((fullArenaClauseLits st cref.toNat).filter (· != drop_b.toNat)))) :
    wp Γ Q X (s6aFwdMarkScanExpr c cref hdr sz sat_b drop_b unk_b Jm) m1 := by
  have hwf_t := hdwt.2.1.arena.refs_wf cref.toNat href_t
  have hal_t := hdwt.1.core_ok.arena_len_le
  have har_len_t : cref.toNat < st.core.arena.length := by rw [hdwt.1.core_ok.arena_len_arr]; omega
  have hcr_art : (cref.setWidth 64).toNat < st.core.arena.length := by
    rw [hdwt.1.core_ok.arena_len_arr, m6_zext32_toNat]; omega
  have hms : (FullMem c st ⋆ R) m1 := hm1
  dsimp only [s6aFwdMarkScanExpr, qL, qA64, qS64, qM64, qShl, qA32, qO32, qN32, qX32,
    qZ32, qSx, qTr, qC32, qC64]
  c0_hsplit
  · -- `drop_b == 0xFFFFFFFFu`: mark `lm`, scan `l` and `l^1`, clear `lm`
    have hdrop_ff : drop_b = 0xFFFFFFFF#32 := hc
    have hcr3_t : (cref.setWidth 64 + 3#64).toNat < st.core.arena.length := by
      rw [hdwt.1.core_ok.arena_len_arr]; c0_bound
    have hl0_lt : (st.core.arena[(cref.setWidth 64 + 3#64).toNat]'hcr3_t).toNat <
        2 * st.core.cur_vars := by
      have hmem : (st.core.arena[(cref.setWidth 64 + 3#64).toNat]'hcr3_t).toNat ∈
          fullArenaClauseLitsCore st.core cref.toNat := by
        rw [mem_fullArenaClauseLitsCore_iff (by
          rw [hdwt.1.core_ok.arena_len_arr]; omega)]
        exact ⟨0, by omega, congrArg BitVec.toNat (m6_getElem_congr (by c0_bound) _ _)⟩
      exact hdwt.2.1.arena.lits_lt cref.toNat href_t hngt _ hmem
    have hl0_wv : ((st.core.arena[(cref.setWidth 64 + 3#64).toNat]'hcr3_t).setWidth
        64 <<< (1 : Nat) + 1#64).toNat < st.core.wvec.length := by
      rw [hdwt.1.core_ok.wvec_len]; have := hdwt.1.core_ok.cur_vars_le; c0_bound
    c0_hsteps_nogrp
    -- Mark `lm[l] = 1` & find `min_l`
    refine wp_loop_group (ts := [i32, i32, i32])
      (fun rem_m (i, min_l, min_deg, ()) mm => ∃ lm' : List (BitVec 8),
        let sm : FullState := { st with core := { st.core with lit_mark := lm' } }
        lm'.length = 2 * c.max_vars ∧ i.toNat ≤ sz.toNat ∧ rem_m = sz.toNat - i.toNat ∧
        min_l.toNat ∈ fullArenaClauseLits st cref.toNat ∧ (∀ x < 2 * c.max_vars,
          lm'[x]?.getD 0#8 ≠ 0#8 ↔ x ∈ (fullArenaClauseLits st cref.toNat).take i.toNat) ∧
        (FullMem c sm ⋆ R) mm)
      ?_ ?_
    · rintro Lm rem_m ⟨i, min_l, min_deg, ⟨⟩⟩ mm hLm
        ⟨lm', hlml, hi_le, rfl, hml_mem, hlm_tk, hmm⟩
      let sm : FullState := { st with core := { st.core with lit_mark := lm' } }
      c0_hsplit
      · have hi_lt : i.toNat < sz.toNat := hc
        have hcri : (cref.setWidth 64 + 3#64 + i.setWidth 64).toNat < st.core.arena.length := by
          rw [hdwt.1.core_ok.arena_len_arr]; c0_bound
        let li :=
          st.core.arena[(cref.setWidth 64 + 3#64 + i.setWidth 64).toNat]'hcri
        have hli_at := m7_p3_fwd_cl_lit_at hdwt href_t hszt hi_lt
        have hli_eq : (fullArenaClauseLits st cref.toNat)[i.toNat]'hli_at.1 =
            li.toNat := hli_at.2.trans (congrArg BitVec.toNat
          (m6_getElem_congr (by c0_bound) _ _))
        have hli_mem : li.toNat ∈ fullArenaClauseLits st cref.toNat :=
          hli_eq ▸ List.getElem_mem hli_at.1
        have hli_lt : li.toNat < 2 * st.core.cur_vars :=
          hdwt.2.1.arena.lits_lt cref.toNat href_t hngt _ hli_mem
        have hli_lm : (li.setWidth 64).toNat < lm'.length := by
          rw [hlml, m6_zext32_toNat]; have := hdwt.1.core_ok.cur_vars_le; omega
        have hli_wv : (li.setWidth 64 <<< (1 : Nat) + 1#64).toNat < st.core.wvec.length := by
          rw [hdwt.1.core_ok.wvec_len]; have := hdwt.1.core_ok.cur_vars_le; c0_bound
        have hi1 : (i + 1#32).toNat = i.toNat + 1 := by c0_bound
        have hlm_next : ∀ x < 2 * c.max_vars,
            (lm'.set (li.setWidth 64).toNat 1#8)[x]?.getD 0#8 ≠ 0#8 ↔
              x ∈ (fullArenaClauseLits st cref.toNat).take (i + 1#32).toNat := by
          rw [hi1, m6_zext32_toNat]
          exact m7_p3_fwd_lm_set_iff hlml hdwt.1.core_ok.cur_vars_le hli_lt hli_at.1
            hli_eq hlm_tk
        c0_hsteps_nogrp
        refine wp_join_state (ts := [i32, i32]) (α := BitVec 32 × BitVec 32)
          (fun x => (x.1, x.2, ())) (fun x mj =>
            x.1.toNat ∈ fullArenaClauseLits st cref.toNat ∧
            (FullMem c { st with core := { st.core with
              lit_mark := lm'.set (li.setWidth 64).toNat 1#8 } } ⋆ R) mj)
          (fun _ ⟨ml', md'⟩ mj ⟨hml_m, hmj⟩ => by
            c0_hsteps!
            exact hLm (sz.toNat - (i + 1#32).toNat) (i + 1#32, ml', md', ()) mj
              (by omega) ⟨lm'.set (li.setWidth 64).toNat 1#8, by simp [hlml],
               by omega, rfl, hml_m, hlm_next, hmj⟩)
          (fun J68 hJ68 => by
            c0_hsplit
            · c0_hsteps!; exact hJ68 (li, _) _ ⟨hli_mem, by assumption⟩
            · c0_hsteps!; exact hJ68 (min_l, min_deg) _ ⟨hml_mem, by assumption⟩)
      · -- Scan loop: call `full_fwd_scan_lit_m7` on `l` and `l ^ 1`
        have hi_eq : i.toNat = sz.toNat := by omega
        have hC_len : (fullArenaClauseLits st cref.toNat).length = sz.toNat :=
          m7_p3_fwd_cl_lits_len hdwt href_t hszt
        have hlm_full : ∀ x < 2 * c.max_vars,
            lm'[x]?.getD 0#8 ≠ 0#8 ↔ x ∈ fullArenaClauseLits st cref.toNat := by
          intro x hx
          simpa only [hi_eq, ← hC_len, List.take_length] using hlm_tk x hx
        have hlen_sm : sm.LengthsOk c :=
          ⟨{ hdwt.1.core_ok with lit_mark_len := hlml }, hdwt.1.scratch_ok⟩
        have hw_sm : FullWitnessInv c F0 F_cur sm.core :=
          { hdwt.2.1 with
            arena := { hdwt.2.1.arena with len_ok := hdwt.2.1.arena.len_ok }
            watches := hdwt.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) }
        c0_hsteps_nogrp
        refine wp_loop_break_group (brkTs := [i32, i32, .bool]) (lpTs := [i32])
          (fun (drop_s, _, sub_s, ()) m_s => m_s = mm ∧
            (sub_s = false → drop_s ≠ 0xFFFFFFFF#32 → (cnfOfClauses F_cur).EntailsClause
                (cnfClause ((fullArenaClauseLits st cref.toNat).filter (· != drop_s.toNat)))))
          (fun rem_s (is, ()) m_s => m_s = mm ∧
            is.toNat ≤ sz.toNat ∧ rem_s = sz.toNat - is.toNat)
          ?_ ?_ ?_
        · rintro _ ⟨drop_s, _, sub_s, ⟨⟩⟩ m_s ⟨rfl, hscan_post⟩
          -- Unmark `lm` for all `i < sz`
          c0_hsteps_nogrp
          refine wp_loop_group (ts := [i32]) (fun rem_u (iu, ()) mu => ∃ lm_u : List (BitVec 8),
              let su' : FullState :=
                { st with core := { st.core with lit_mark := lm_u } }
              lm_u.length = 2 * c.max_vars ∧ iu.toNat ≤ sz.toNat ∧ rem_u = sz.toNat - iu.toNat ∧
              (∀ x < 2 * c.max_vars, lm_u[x]?.getD 0#8 ≠ 0#8 →
                  x ∈ (fullArenaClauseLits st cref.toNat).drop iu.toNat) ∧
              (FullMem c su' ⋆ R) mu)
            ?_ ?_
          · rintro Lu rem_u ⟨iu, ⟨⟩⟩ mu hLu ⟨lm_u, hlmu, hiu_le, rfl, hrem_lm, hmu⟩
            c0_hsplit
            · have hiu_lt : iu.toNat < sz.toNat := hc
              obtain ⟨hcri, hli_lm, hiu1, hlm_next⟩ :=
                m7_p3_unmark_iter hdwt href_t hngt hszt hlmu hiu_lt hrem_lm
              c0_hsteps!
              exact hLu (sz.toNat - (iu + 1#32).toNat) (iu + 1#32, ()) _ (by omega)
                ⟨_, by simp [hlmu], by omega, rfl, hlm_next, hm⟩
            · have hiu_eq : iu.toNat = sz.toNat := by omega
              have hlm_clr : ∀ x < 2 * c.max_vars, lm_u[x]?.getD 0#8 = 0#8 :=
                fun x hx => Classical.byContradiction fun hnz => by
                  have hmem := hrem_lm x hx hnz
                  rw [hiu_eq, ← hC_len, List.drop_length] at hmem; cases hmem
              let su_clr : FullState :=
                { st with core := { st.core with lit_mark := lm_u } }
              have hdw_clr := m7_p3_fullDenseInvW_with_lit_mark hdwt hlmu hlm_clr
              c0_hsteps!
              exact hJm (sub_s, drop_s, _, su_clr) mu
                ⟨rfl, rfl, rfl, rfl, rfl, hdw_clr, hscan_post, hmu⟩
          · intro Lu hLu; c0_hsteps!
            exact hLu sz.toNat (0#32, ()) _ ⟨lm', hlml, Nat.zero_le _, by simp,
                fun x hx hnz => (hlm_full x hx).mp hnz, hmm⟩
        · rintro Bs Ls rem_s ⟨is, ⟨⟩⟩ m_s hBs hLs ⟨rfl, his_le, rfl⟩
          c0_hsplit
          · have his_lt : is.toNat < sz.toNat := hc
            have hcri :
                (cref.setWidth 64 + 3#64 + is.setWidth 64).toNat < st.core.arena.length := by
              rw [hdwt.1.core_ok.arena_len_arr]; c0_bound
            have hli_mem : (st.core.arena[(cref.setWidth 64 + 3#64 +
                is.setWidth 64).toNat]'hcri).toNat ∈ fullArenaClauseLits st cref.toNat := by
              have hat := m7_p3_fwd_cl_lit_at hdwt href_t hszt his_lt
              have hli_eq : (fullArenaClauseLits st cref.toNat)[is.toNat]'hat.1 =
                  (st.core.arena[(cref.setWidth 64 + 3#64 +
                    is.setWidth 64).toNat]'hcri).toNat :=
                hat.2.trans (congrArg BitVec.toNat (m6_getElem_congr (by c0_bound) _ hcri))
              rw [← hli_eq]; exact List.getElem_mem hat.1
            have hl0_mem : (st.core.arena[(cref.setWidth 64 + 3#64).toNat]'
                hcr3_t).toNat ∈ fullArenaClauseLits st cref.toNat := by
              have hat := m7_p3_fwd_cl_lit_at hdwt href_t hszt (i := 0) (by omega)
              have hl0_eq : (fullArenaClauseLits st cref.toNat)[0]'hat.1 =
                  (st.core.arena[(cref.setWidth 64 + 3#64).toNat]'hcr3_t).toNat :=
                hat.2.trans (congrArg BitVec.toNat (m6_getElem_congr (by c0_bound) _ hcr3_t))
              rw [← hl0_eq]; exact List.getElem_mem hat.1
            have his1 : (is + 1#32).toNat = is.toNat + 1 := by c0_bound
            c0_hsplit
            c0_hsplit
            · -- `l = (is == 0 ? min_l : ar[cref+3+is])`, swap if `l == min_l`
              refine wp_join_state_pure (ts := [i32]) (α := BitVec 32) (fun l => (l, ()))
                (fun l => l.toNat ∈ fullArenaClauseLits st cref.toNat) (fun _ l1 hl1_mem => by
                  refine wp_join_state_pure (ts := [i32]) (α := BitVec 32) (fun l => (l, ()))
                    (fun l => l.toNat ∈ fullArenaClauseLits st cref.toNat)
                    (fun _ l_use hl_mem => by
                      have hl_lt : l_use.toNat < 2 * sm.core.cur_vars :=
                        hdwt.2.1.arena.lits_lt cref.toNat href_t hngt _ hl_mem
                      have hln_lt : (l_use ^^^ 1#32).toNat < 2 * sm.core.cur_vars := by
                        change l_use.toNat ^^^ 1 < 2 * sm.core.cur_vars
                        have := fullInv_var_xor1 l_use.toNat; omega
                      c0_hsteps_nogrp
                      m7_call hScanLit
                      refine step13FwdScanLitSpec_intro rfl hlen_sm hw_sm
                        hdwt.2.2.2.2.2.1 hdwt.2.2.2.2.2.2 hdwt.2.2.2.1 href_t
                        hngt hszt hl_lt (fun _ => hl_mem)
                        (fun x hx => hlm_full x (Nat.lt_of_lt_of_le hx
                          (Nat.mul_le_mul_left 2 hdwt.1.core_ok.cur_vars_le)))
                        hmm ?_
                      intro r1 hr1
                      c0_hsplit
                      · c0_hsteps!
                        exact hBs (drop_b, is, true, ()) _ ⟨rfl, by simp⟩
                      · c0_hsplit
                        · have hr1_ent : (cnfOfClauses F_cur).EntailsClause
                              (cnfClause ((fullArenaClauseLits st cref.toNat).filter
                                (· != r1.toNat))) := by
                            rcases hr1 with h1 | h2 | ⟨_, h3⟩
                            · exact absurd h1 hc
                            · exact absurd h2 ‹r1 ≠ 0xFFFFFFFE#32›
                            · exact h3
                          c0_hsteps!
                          exact hBs (r1, _, false, ()) _ ⟨rfl, fun _ _ => hr1_ent⟩
                        · c0_hsteps_nogrp
                          m7_call hScanLit
                          refine step13FwdScanLitSpec_intro rfl hlen_sm hw_sm
                            hdwt.2.2.2.2.2.1 hdwt.2.2.2.2.2.2 hdwt.2.2.2.1
                            href_t hngt hszt hln_lt (fun h => False.elim (Bool.noConfusion h))
                            (fun x hx => hlm_full x (Nat.lt_of_lt_of_le hx
                              (Nat.mul_le_mul_left 2 hdwt.1.core_ok.cur_vars_le)))
                            hmm ?_
                          intro r2 hr2
                          c0_hsplit
                          · c0_hsteps!
                            exact hBs (drop_b, is, true, ()) _ ⟨rfl, by simp⟩
                          · c0_hsplit
                            · have hr2_ent : (cnfOfClauses F_cur).EntailsClause
                                  (cnfClause ((fullArenaClauseLits st
                                    cref.toNat).filter (· != r2.toNat))) := by
                                rcases hr2 with h1 | h2 | ⟨_, h3⟩
                                · exact absurd h1 hc
                                · exact absurd h2 ‹r2 ≠ 0xFFFFFFFE#32›
                                · exact h3
                              c0_hsteps!
                              exact hBs (r2, _, false, ()) _ ⟨rfl, fun _ _ => hr2_ent⟩
                            · c0_hsteps!
                              exact hLs (sz.toNat - (is + 1#32).toNat)
                                (is + 1#32, ()) _ (by omega) ⟨rfl, by omega, rfl⟩)
                    (fun Jl2 hJl2 => by
                      c0_hsplit
                      · c0_hsplit
                        · c0_hsteps!; exact hJl2 _ hl0_mem
                        · c0_hsteps!; exact hJl2 l1 hl1_mem
                      · c0_hsteps!; exact hJl2 l1 hl1_mem))
                (fun Jl1 hJl1 => by
                  c0_hsplit
                  · c0_hsteps!; exact hJl1 min_l hml_mem
                  · c0_hsteps!; exact hJl1 _ hli_mem)
            · c0_hsteps!; exact absurd hdrop_ff hc
          · c0_hsteps!
            exact hBs (drop_b, is, false, ()) _ ⟨rfl, fun _ h => absurd hdrop_ff h⟩
        · intro _ Ls _ hLs; c0_hsteps!
          exact hLs sz.toNat (0#32, ()) _ ⟨rfl, Nat.zero_le _, by simp⟩
    · intro Lm hLm; c0_hsteps!
      have hl0_mem : (st.core.arena[(cref.setWidth 64 + 3#64).toNat]'
          hcr3_t).toNat ∈ fullArenaClauseLits st cref.toNat := by
        have hat := m7_p3_fwd_cl_lit_at hdwt href_t hszt (i := 0) (by omega)
        have hl0_eq : (fullArenaClauseLits st cref.toNat)[0]'hat.1 =
            (st.core.arena[(cref.setWidth 64 + 3#64).toNat]'hcr3_t).toNat :=
          hat.2.trans (congrArg BitVec.toNat (m6_getElem_congr (by c0_bound) _ hcr3_t))
        rw [← hl0_eq]; exact List.getElem_mem hat.1
      exact hLm sz.toNat (0#32, _, _, ()) _
        ⟨st.core.lit_mark, hdwt.1.core_ok.lit_mark_len, Nat.zero_le _, by simp,
         hl0_mem, fun x hx => by
           rw [show (0#32).toNat = 0 from rfl]
           simp only [List.take_zero, List.not_mem_nil]
           exact ⟨fun h => h (hdwt.2.2.1.2 x hx), False.elim⟩, hms⟩
  · c0_hsteps!
    exact hJm (false, drop_b, unk_b, _) _
      ⟨rfl, rfl, rfl, rfl, rfl, hdwt, fun _ hne => hdrop_ent0 hne, hms⟩
theorem full_fwd_check_cl_m7_step13_wp (Γ : Env)
    (hScanLit : ∀ a m Q X, step13FwdScanLitSpec a m Q X →
      Γ "full_fwd_scan_lit_m7" [i64, i32, i32, i32, .bool] [i32] a m Q X)
    (hUnwatch : ∀ a m Q X, fullUnwatchLargeSpec a m Q X →
      Γ "full_unwatch_large" [i64, i32, i32] [] a m Q X)
    (hAddUnit : ∀ a m Q X, fullAddUnitSpec a m Q X →
      Γ "full_add_unit" [i64, i32] [.bool] a m Q X)
    (hAddBin : ∀ a m Q X, fullAddBinSpec a m Q X →
      Γ "full_add_bin" [i64, i32, i32] [i64] a m Q X)
    (hFlushUnits : ∀ a m Q X, fullDenseFlushUnitsM6Spec a m Q X →
      Γ "full_dense_flush_units_m7" [i64] [.bool] a m Q X) :
    ∀ a m Q X, fullFwdCheckClM7Spec a m Q X →
      Func.wp Γ full_fwd_check_cl_m7_body a m Q X := by
  rintro ⟨h, cref, ⟨⟩⟩ m0 Q X hSpec
  obtain ⟨c, F0, F_cur, s0, R, rfl, hdw0, href0, hm0, hQ⟩ :=
    fullFwdCheckClM7Spec_elim hSpec
  have hmx := c.hmaxv; have harc := c.harena; unfold dimacsBound at hmx harc
  have hwf0 := hdw0.2.1.arena.refs_wf cref.toNat href0
  have hal0_le := hdw0.1.core_ok.arena_len_le
  have har_len0 : cref.toNat < s0.core.arena.length := by
    rw [hdw0.1.core_ok.arena_len_arr]; omega
  have hcr_ar0 : (cref.setWidth 64).toNat < s0.core.arena.length := by
    rw [hdw0.1.core_ok.arena_len_arr, m6_zext32_toNat]; omega
  have hcr2_ar0 : (cref.setWidth 64 + 2#64).toNat < s0.core.arena.length := by
    rw [hdw0.1.core_ok.arena_len_arr]; c0_bound
  let hdr0 := s0.core.arena[(cref.setWidth 64).toNat]'hcr_ar0
  let sz0 := s0.core.arena[(cref.setWidth 64 + 2#64).toNat]'hcr2_ar0
  unfold Func.wp full_fwd_check_cl_m7_body
  c0_hsplit
  · c0_hsteps!; exact hQ true s0 m0 hdw0 rfl rfl rfl rfl rfl rfl (fun h => by cases h) hm0
  · have hng0 : fullArenaClauseGarb s0 cref.toNat = false := by
      unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore
      rw [List.getElem?_eq_getElem har_len0, Option.getD_some]
      have hget : s0.core.arena[cref.toNat]'har_len0 = hdr0 :=
        m6_getElem_congr (m6_zext32_toNat cref).symm _ _
      rw [hget]
      have h0 : (hdr0 &&& 0x00080000#32) = 0#32 := by
        change (hdr0 &&& (0x00080000#32 ||| 0x00400000#32)) = 0#32 at hc
        have hsub : (0x00080000#32 : BitVec 32) &&& (0x00080000#32 ||| 0x00400000#32) =
            0x00080000#32 := by decide
        have hc' := congrArg (· &&& 0x00080000#32) hc
        rw [BitVec.and_assoc, BitVec.and_comm _ 0x00080000#32, hsub, BitVec.zero_and] at hc'
        exact hc'
      rw [h0]; rfl
    c0_hsplit
    · c0_hsteps!; exact hQ true s0 m0 hdw0 rfl rfl rfl rfl rfl rfl (fun h => by cases h) hm0
    · have hsz0_eq : sz0.toNat = fullArenaClauseSizeCore s0.core cref.toNat := by
        unfold sz0 fullArenaClauseSizeCore
        rw [List.getElem?_eq_getElem (by rw [hdw0.1.core_ok.arena_len_arr]; omega),
          Option.getD_some]
        exact congrArg BitVec.toNat (m6_getElem_congr (by c0_bound) _ _)
      have hhdr0_eq : hdr0 = fullArenaHdr s0 cref.toNat := by
        unfold hdr0 fullArenaHdr fullArenaHdrCore
        rw [List.getElem?_eq_getElem har_len0, Option.getD_some]
        exact m6_getElem_congr (m6_zext32_toNat cref) _ _
      c0_hsteps_nogrp
      -- Outer multi-shrink `while (true)` loop (measure: `sz.toNat`)
      refine wp_loop_group (ts := [i32, i32]) (fun rem (hdr, sz, ()) ms => ∃ st : FullState,
          rem = sz.toNat ∧ 3 ≤ sz.toNat ∧ FullDenseInvW c F0 F_cur st ∧
          st.core.cur_vars = s0.core.cur_vars ∧ st.core.arena_len = s0.core.arena_len ∧
          st.core.fuel = s0.core.fuel ∧ fullArenaClauseRefs st = fullArenaClauseRefs s0 ∧
          st.scratch.tarjan_mark = s0.scratch.tarjan_mark ∧
          st.scratch.red_refs = s0.scratch.red_refs ∧ hdr = fullArenaHdr st cref.toNat ∧
          sz.toNat = fullArenaClauseSizeCore st.core cref.toNat ∧
          fullArenaClauseGarb st cref.toNat = false ∧ (FullMem c st ⋆ R) ms)
        ?_ ?_
      · rintro L rem ⟨hdr, sz, ⟨⟩⟩ ms hL
          ⟨st, rfl, hsz3, hdwt, hcvt, halt, hflt, hrefst, htmkt, hrrt, hhdrt, hszt, hngt, hms⟩
        have href_t : cref.toNat ∈ fullArenaClauseRefs st := hrefst.symm ▸ href0
        have hwf_t := hdwt.2.1.arena.refs_wf cref.toNat href_t
        have hal_t := hdwt.1.core_ok.arena_len_le
        have har_len_t : cref.toNat < st.core.arena.length := by
          rw [hdwt.1.core_ok.arena_len_arr]; omega
        have hcr_art : (cref.setWidth 64).toNat < st.core.arena.length := by
          rw [hdwt.1.core_ok.arena_len_arr, m6_zext32_toNat]; omega
        have hsz_le_cv : sz.toNat ≤ st.core.cur_vars := by
          have := m6_clause_nodup_len_le hdwt href_t hngt
          change fullArenaClauseSizeCore st.core cref.toNat ≤ st.core.cur_vars at this; omega
        have hent_C := hdwt.2.1.arena.entails cref.toNat href_t hngt
        -- Step 1: scan `cref` for root-SAT or first level-0 false lit
        c0_hsplit
        · refine wp_loop_break_group (brkTs := [.bool, i32, i32]) (lpTs := [i32, i32])
            (fun (sat_b, drop_b, _, ()) m1 => m1 = ms ∧
              (sat_b = false → drop_b ≠ 0xFFFFFFFF#32 → drop_b.toNat < 2 * st.core.cur_vars ∧
                st.core.vals[drop_b.toNat]?.getD 0#8 = 0xFF#8))
            (fun rem_i (drop_i, i, ()) mi => mi = ms ∧
              i.toNat ≤ sz.toNat ∧ rem_i = sz.toNat - i.toNat ∧ (drop_i ≠ 0xFFFFFFFF#32 →
                drop_i.toNat < 2 * st.core.cur_vars ∧
                st.core.vals[drop_i.toNat]?.getD 0#8 = 0xFF#8))
            ?_ ?_ ?_
          · rintro _ ⟨sat_b, drop_b, _, ⟨⟩⟩ m1 ⟨rfl, hfalse_drop⟩
            c0_hsplit
            · -- Root-SAT: mark `PH_GARB` and return `true`
              c0_hsteps!
              let ag' := st.core.arena_garbage + 3#64 + sz.setWidth 64
              let ar' := st.core.arena.set (cref.setWidth 64).toNat (hdr ||| 0x00080000#32)
              let smg : FullState :=
                { st with core := { st.core with arena := ar', arena_garbage := ag' } }
              have hmg := m6_fullDenseInvW_markGarb hdwt href_t (arena' := ar') (ag' := ag')
                (by simp [ar', hdwt.1.core_ok.arena_len_arr]) (Or.inl (by
                  dsimp only [ar']; rw [m6_zext32_toNat, hhdrt]
                  exact List.getElem?_set_self har_len_t))
                (fun i hne _ => by
                  dsimp only [ar']; rw [m6_zext32_toNat]; exact List.getElem?_set_ne hne.symm)
              exact hQ true smg _ hmg.1 hcvt halt hflt (hmg.2.trans hrefst) htmkt hrrt
                (fun h => by cases h) hm
            · have hdrop_ent0 : drop_b ≠ 0xFFFFFFFF#32 → (cnfOfClauses F_cur).EntailsClause
                    (cnfClause ((fullArenaClauseLits st cref.toNat).filter
                      (· != drop_b.toNat))) :=
                fun hne => by
                  obtain ⟨hlt_d, hff_d⟩ := hfalse_drop hc hne
                  exact m7_p3_drop_false_lit hdwt.2.1 hdwt.2.2.2.2.2.1 hent_C hlt_d hff_d
              -- Step 2: if `drop_b == 0xFFFFFFFFu`, mark `lm`, scan `l` & `l^1`, unmark `lm`
              refine wp_join_state (ts := [i32, i32, .bool])
                (α := Bool × BitVec 32 × BitVec 32 × FullState)
                (fun x => (x.2.1, x.2.2.1, x.1, ())) (fun x mj =>
                  x.2.2.2.core.cur_vars = st.core.cur_vars ∧
                  x.2.2.2.core.arena = st.core.arena ∧
                  x.2.2.2.core.arena_len = st.core.arena_len ∧
                  x.2.2.2.core.fuel = st.core.fuel ∧ x.2.2.2.scratch = st.scratch ∧
                  FullDenseInvW c F0 F_cur x.2.2.2 ∧ (x.1 = false → x.2.1 ≠ 0xFFFFFFFF#32 →
                    (cnfOfClauses F_cur).EntailsClause
                      (cnfClause ((fullArenaClauseLits st cref.toNat).filter
                        (· != x.2.1.toNat)))) ∧
                  (FullMem c x.2.2.2 ⋆ R) mj)
                (fun _ ⟨sub_b, drop_f, _unk, sf⟩ mj
                    ⟨hcvf, harf, half, hflf, hscrf, hdwf, hdrop_ent, hmj⟩ => by
                have hrefsf : fullArenaClauseRefs sf = fullArenaClauseRefs st := by
                  unfold fullArenaClauseRefs fullArenaClauseRefsCore; rw [harf, half]
                have href_f : cref.toNat ∈ fullArenaClauseRefs sf := hrefsf.symm ▸ href_t
                have hhdr_f : hdr = fullArenaHdr sf cref.toNat := by
                  unfold fullArenaHdr fullArenaHdrCore; rw [harf]; exact hhdrt
                have har_len_f : cref.toNat < sf.core.arena.length := by
                  rw [hdwf.1.core_ok.arena_len_arr]; omega
                have hcr_arf : (cref.setWidth 64).toNat < sf.core.arena.length := by
                  rw [hdwf.1.core_ok.arena_len_arr, m6_zext32_toNat]; omega
                c0_hsplit
                · -- Subsumed: mark `PH_GARB`, bump `fwd_sub_cnt`, return `true`
                  c0_hsteps!
                  let ag' := sf.core.arena_garbage + 3#64 + sz.setWidth 64
                  let ar' := sf.core.arena.set (cref.setWidth 64).toNat (hdr ||| 0x00080000#32)
                  let smg : FullState :=
                    { sf with
                      core := { sf.core with arena := ar', arena_garbage := ag' }
                      scratch := { sf.scratch with fwd_sub_cnt := sf.scratch.fwd_sub_cnt + 1#64 } }
                  have hmg := m6_fullDenseInvW_markGarb hdwf href_f (arena' := ar') (ag' := ag')
                    (by simp [ar', hdwf.1.core_ok.arena_len_arr]) (Or.inl (by
                      dsimp only [ar']; rw [m6_zext32_toNat, hhdr_f]
                      exact List.getElem?_set_self har_len_f))
                    (fun i hne _ => by
                      dsimp only [ar']; rw [m6_zext32_toNat]; exact List.getElem?_set_ne hne.symm)
                  have hdw_sub := m6_fullDenseInvW_with_scratch hmg.1
                    (sc' := smg.scratch) { hdwf.1.scratch_ok with } rfl rfl
                  exact hQ true smg _ hdw_sub (hcvf.trans hcvt) (half.trans halt) (hflf.trans hflt)
                    (hmg.2.trans (hrefsf.trans hrefst))
                    (by dsimp only [smg]; rw [hscrf]; exact htmkt)
                    (by dsimp only [smg]; rw [hscrf]; exact hrrt) (fun h => by cases h) hm
                · c0_hsplit
                  · c0_hsteps!
                    exact hQ true sf mj hdwf (hcvf.trans hcvt) (half.trans halt) (hflf.trans hflt)
                      (hrefsf.trans hrefst) (by rw [hscrf, htmkt]) (by rw [hscrf, hrrt])
                      (fun h => by cases h) hmj
                  · have hent_drop := hdrop_ent ‹sub_b = false› hc
                    c0_hsteps_nogrp
                    let sf1 : FullState :=
                      { sf with scratch := { sf.scratch with
                          fwd_str_cnt := sf.scratch.fwd_str_cnt + 1#64 } }
                    have hdwf1 : FullDenseInvW c F0 F_cur sf1 :=
                      m6_fullDenseInvW_with_scratch hdwf (sc' := sf1.scratch)
                        { hdwf.1.scratch_ok with } rfl rfl
                    m7_call hUnwatch
                    refine ⟨c, sf1, R, rfl, hdwf1.1, (m6_denseWatchesInv_of_w hdwf1).layout, hm, ?_⟩
                    intro wvec' wstk' wu' m_u su hlen_u _ hwm_u hm_u
                    have hdw_u : FullDenseInvW c F0 F_cur su :=
                      m7_p3_fullDenseInvW_of_unwatch hdwf1 hlen_u (hwm_u F_cur hdwf1.2.1.watches)
                    have href_u : cref.toNat ∈ fullArenaClauseRefs su := href_f
                    have har_len_u : cref.toNat < su.core.arena.length := har_len_f
                    have hcr_aru : (cref.setWidth 64).toNat < su.core.arena.length := hcr_arf
                    -- Filter `l != drop_f` into `tmp[0 ..< nsz)`
                    c0_hsteps_nogrp
                    refine wp_loop_group (ts := [i32, i32])
                      (fun rem_f (i, nsz, ()) mf => ∃ tmp' : List (BitVec 32),
                        let sf' : FullState := { su with core := { su.core with tmp := tmp' } }
                        tmp'.length = c.max_vars ∧
                        i.toNat ≤ sz.toNat ∧ rem_f = sz.toNat - i.toNat ∧ nsz.toNat ≤ i.toNat ∧
                        (tmp'.take nsz.toNat).map BitVec.toNat =
                          (((fullArenaClauseLits st cref.toNat).take i.toNat).filter
                            (· != drop_f.toNat)) ∧
                        (FullMem c sf' ⋆ R) mf)
                      ?_ ?_
                    · rintro Lf rem_f ⟨i, nsz, ⟨⟩⟩ mf hLf
                        ⟨tmp', htl', hi_le, rfl, hnsz_le, hfilt, hmf⟩
                      let sf' : FullState := { su with core := { su.core with tmp := tmp' } }
                      c0_hsplit
                      · have hi_lt : i.toNat < sz.toNat := hc
                        have hcri : (cref.setWidth 64 + 3#64 + i.setWidth 64).toNat <
                            su.core.arena.length := by
                          rw [hdw_u.1.core_ok.arena_len_arr]; c0_bound
                        let l_i := su.core.arena[(cref.setWidth 64 + 3#64 + i.setWidth 64).toNat]'
                          hcri
                        have hli_eq : (fullArenaClauseLits st cref.toNat)[i.toNat]'(by
                              unfold fullArenaClauseLits fullArenaClauseLitsCore
                              simp only [List.length_take, List.length_drop, List.length_map]
                              rw [hdwt.1.core_ok.arena_len_arr]; omega) = l_i.toNat := by
                          unfold fullArenaClauseLits fullArenaClauseLitsCore
                          simp only [List.getElem_map, List.getElem_take, List.getElem_drop]
                          have hopt : some (st.core.arena[cref.toNat + 3 + i.toNat]'(by
                                rw [hdwt.1.core_ok.arena_len_arr]; omega)) = some l_i := by
                            have hsu_ar : su.core.arena = st.core.arena := by
                              dsimp only [su, sf1]; exact harf
                            dsimp only [l_i]
                            rw [← List.getElem?_eq_getElem (by
                              rw [hdwt.1.core_ok.arena_len_arr]; omega),
                              ← List.getElem?_eq_getElem hcri, hsu_ar]
                            exact congrArg (st.core.arena[·]?) (by c0_bound)
                          exact congrArg BitVec.toNat (Option.some.inj hopt)
                        have htake_succ :
                            (fullArenaClauseLits st cref.toNat).take (i.toNat + 1) =
                            (fullArenaClauseLits st cref.toNat).take i.toNat ++ [l_i.toNat] := by
                          rw [List.take_succ_eq_append_getElem (by
                            unfold fullArenaClauseLits fullArenaClauseLitsCore
                            simp only [List.length_take, List.length_drop, List.length_map]
                            rw [hdwt.1.core_ok.arena_len_arr]; omega), hli_eq]
                        have hi1 : (i + 1#32).toNat = i.toNat + 1 := by c0_bound
                        c0_hsteps_nogrp
                        refine wp_join_state (ts := [i32]) (α := BitVec 32 × List (BitVec 32))
                          (fun x => (x.1, ())) (fun x mj =>
                            x.2.length = c.max_vars ∧ x.1.toNat ≤ i.toNat + 1 ∧
                            (x.2.take x.1.toNat).map BitVec.toNat =
                              ((fullArenaClauseLits st cref.toNat).take (i.toNat + 1)).filter
                                (· != drop_f.toNat) ∧
                            (FullMem c { su with core := { su.core with tmp := x.2 } } ⋆ R) mj)
                          (fun _ ⟨nsz', tmp''⟩ mj ⟨htl'', hnsz_le', hfilt', hmj⟩ => by
                            c0_hsteps!
                            exact hLf (sz.toNat - (i + 1#32).toNat) (i + 1#32, nsz', ()) mj
                              (by omega) ⟨tmp'', htl'', by omega, rfl,
                                by rw [hi1]; exact hnsz_le', by rw [hi1]; exact hfilt', hmj⟩)
                          (fun J52 hJ52 => by
                            c0_hsplit
                            · have hnsz_tmp : (nsz.setWidth 64).toNat < tmp'.length := by
                                rw [htl', m6_zext32_toNat]
                                have := hdwt.1.core_ok.cur_vars_le; omega
                              have hnsz1 : (nsz + 1#32).toNat = nsz.toNat + 1 := by c0_bound
                              c0_hsteps!
                              let tmp'' := tmp'.set (nsz.setWidth 64).toNat l_i
                              have htake_set : (tmp''.take (nsz.toNat + 1)).map BitVec.toNat =
                                  (tmp'.take nsz.toNat).map BitVec.toNat ++ [l_i.toNat] := by
                                have hlt_m : nsz.toNat + 1 ≤ tmp''.length := by
                                  simp only [tmp'', List.length_set, htl']
                                  have := hdwt.1.core_ok.cur_vars_le; omega
                                rw [List.take_succ_eq_append_getElem hlt_m, List.map_append,
                                  List.map_singleton]
                                congr 1
                                · rw [List.take_set_of_le (by
                                    rw [m6_zext32_toNat]; exact Nat.le_refl _)]
                                · have h1 : tmp''[nsz.toNat]'(by
                                      simp only [tmp'', List.length_set, htl']
                                      have := hdwt.1.core_ok.cur_vars_le; omega) = l_i := by
                                    dsimp only [tmp'']
                                    rw [m6_getElem_congr (m6_zext32_toNat nsz).symm _
                                      (by simp only [List.length_set]; exact hnsz_tmp)]
                                    exact List.getElem_set_self
                                      (by rw [List.length_set]; exact hnsz_tmp)
                                  exact congrArg (fun x => [x.toNat]) h1
                              have hl_c0 :
                                  su.core.arena[(cref.toNat + BitVec.toNat (3 : BitVec 64) +
                                    i.toNat) % 2 ^ 64]'(by
                                      rw [hdw_u.1.core_ok.arena_len_arr]; c0_bound) = l_i :=
                                m6_getElem_congr (by c0_bound) _ _
                              rw [hl_c0] at hc
                              exact hJ52 (nsz + 1#32, tmp'') _ ⟨by simp [tmp'', htl'],
                                by rw [hnsz1]; omega, by
                                rw [hnsz1, htake_set, htake_succ, List.filter_append, hfilt]
                                have hne_n : (l_i.toNat != drop_f.toNat) = true :=
                                  bne_iff_ne.mpr fun h => hc (BitVec.eq_of_toNat_eq h)
                                simp [hne_n], hm⟩
                            · have hl_c0 :
                                  su.core.arena[(cref.toNat + BitVec.toNat (3 : BitVec 64) +
                                    i.toNat) % 2 ^ 64]'(by
                                      rw [hdw_u.1.core_ok.arena_len_arr]; c0_bound) = l_i :=
                                m6_getElem_congr (by c0_bound) _ _
                              rw [hl_c0] at hc
                              c0_hsteps!
                              exact hJ52 (nsz, tmp') mf ⟨htl', Nat.le_succ_of_le hnsz_le, by
                                rw [htake_succ, List.filter_append, hfilt]
                                have heq_n : (l_i.toNat != drop_f.toNat) = false :=
                                  bne_eq_false_iff_eq.mpr (congrArg BitVec.toNat hc)
                                simp [heq_n], hmf⟩)
                      · -- Post-filter: `tmp'[0..nsz)` equals `C.filter (· != drop_f)`
                        have hdw_f' : FullDenseInvW c F0 F_cur sf' :=
                          m6_fullDenseInvW_with_tmp hdw_u htl'
                        have hi_eq : i.toNat = sz.toNat := by omega
                        have hC_len : (fullArenaClauseLits st cref.toNat).length = sz.toNat := by
                          unfold fullArenaClauseLits fullArenaClauseLitsCore
                          simp only [List.length_map, List.length_take, List.length_drop]
                          rw [hdwt.1.core_ok.arena_len_arr]; omega
                        have htmp_eq : (tmp'.take nsz.toNat).map BitVec.toNat =
                            (fullArenaClauseLits st cref.toNat).filter (· != drop_f.toNat) := by
                          rw [hi_eq, ← hC_len, List.take_length] at hfilt; exact hfilt
                        have htmp_ent : (cnfOfClauses F_cur).EntailsClause
                            (cnfClause ((tmp'.take nsz.toNat).map BitVec.toNat)) := by
                          rw [htmp_eq]; exact hent_drop
                        have htmp_nd : (((tmp'.take nsz.toNat).map BitVec.toNat).map
                            (· / 2)).Nodup := by
                          rw [htmp_eq]
                          exact m7_p3_sublist_map_nodup (List.filter_sublist)
                            (hdwt.2.2.2.1 cref.toNat href_t hngt)
                        have htmp_lt : ∀ l ∈ (tmp'.take nsz.toNat).map BitVec.toNat,
                            l < 2 * sf'.core.cur_vars := fun l hl => by
                          rw [htmp_eq] at hl
                          have hmC := (List.mem_filter.mp hl).1
                          have hlt := hdwt.2.1.arena.lits_lt cref.toNat href_t hngt l hmC
                          dsimp only [sf', su, sf1]; rw [hcvf]; exact hlt
                        have hsf'_tm_st : sf'.scratch.tarjan_mark = st.scratch.tarjan_mark := by
                          dsimp only [sf', su, sf1]; exact hscrf ▸ rfl
                        have hsf'_rr_st : sf'.scratch.red_refs = st.scratch.red_refs := by
                          dsimp only [sf', su, sf1]; exact hscrf ▸ rfl
                        exact s6a_fwd_post_filter_wp Γ hAddUnit hAddBin hFlushUnits c F0 F_cur s0
                          st sf' R cref hdr sz i nsz mf Q X L hQ hL hmx harc hsz3
                          hdwt hcvt halt hflt hrefst htmkt hrrt hhdrt hszt hngt href_t hsz_le_cv
                          hdw_f' href_u har_len_u hcr_aru harf hcvf half hflf hrefsf hhdr_f
                          hsf'_tm_st hsf'_rr_st htl' hnsz_le hmf hi_eq htmp_ent htmp_nd htmp_lt
                    · intro Lf hLf; c0_hsteps!
                      exact hLf sz.toNat (0#32, 0#32, ()) m_u
                        ⟨su.core.tmp, hdw_u.1.core_ok.tmp_len_arr, Nat.zero_le _, by simp,
                         Nat.zero_le _, by simp, hm_u⟩)
                (fun Jm hJm => by
                  exact s6a_fwd_mark_scan_wp Γ hScanLit c F0 F_cur s0 st R cref hdr sz
                    sat_b drop_b _ m1 Q X Jm (fun st_1 m' h => hJm st_1 m' h) hmx harc hsz3
                    hdwt hhdrt hszt hngt href_t hms hc hdrop_ent0)
          · rintro Bi Li rem_i ⟨drop_i, i, ⟨⟩⟩ mi hBi hLi ⟨rfl, hi_le, rfl, hdrop_ok⟩
            c0_hsplit
            · have hi_lt : i.toNat < sz.toNat := hc
              have hcri :
                  (cref.setWidth 64 + 3#64 + i.setWidth 64).toNat < st.core.arena.length := by
                rw [hdwt.1.core_ok.arena_len_arr]; c0_bound
              let li := st.core.arena[(cref.setWidth 64 + 3#64 + i.setWidth 64).toNat]'hcri
              have hli_lt : li.toNat < 2 * st.core.cur_vars := by
                have hmem : li.toNat ∈ fullArenaClauseLitsCore st.core cref.toNat := by
                  rw [mem_fullArenaClauseLitsCore_iff (by rw [hdwt.1.core_ok.arena_len_arr]; omega)]
                  exact ⟨i.toNat, by omega,
                    congrArg BitVec.toNat (m6_getElem_congr (by c0_bound) _ _)⟩
                exact hdwt.2.1.arena.lits_lt cref.toNat href_t hngt _ hmem
              have hli_v : (li.setWidth 64).toNat < st.core.vals.length := by
                rw [hdwt.1.core_ok.vals_len, m6_zext32_toNat]; have := hdwt.1.core_ok.cur_vars_le
                omega
              have hi1 : (i + 1#32).toNat = i.toNat + 1 := by c0_bound
              c0_hsplit
              · c0_hsteps!; exact hBi (true, drop_i, i, ()) _ ⟨rfl, by simp⟩
              · refine wp_join_state_pure (ts := [i32]) (α := BitVec 32) (fun d => (d, ()))
                  (fun d => d ≠ 0xFFFFFFFF#32 →
                    d.toNat < 2 * st.core.cur_vars ∧ st.core.vals[d.toNat]?.getD 0#8 = 0xFF#8)
                  (fun _ d hd => by
                    c0_hsteps!
                    exact hLi (sz.toNat - (i + 1#32).toNat) (d, i + 1#32, ()) _ (by omega)
                      ⟨rfl, by omega, rfl, hd⟩)
                  (fun Jd hJd => by
                    c0_hsplit
                    · have hff_i : st.core.vals[li.toNat]?.getD 0#8 = 0xFF#8 := by
                        have hdom := hdwt.2.1.vals_domain li.toNat hli_lt
                        have hlt_v : li.toNat < st.core.vals.length := by
                          rw [hdwt.1.core_ok.vals_len]; have := hdwt.1.core_ok.cur_vars_le; omega
                        have hli_idx : (cref.toNat + BitVec.toNat (3 : BitVec 64) +
                            i.toNat) % 2 ^ 64 =
                            (cref.setWidth 64 + 3#64 + i.setWidth 64).toNat := by
                          have := hdwt.2.1.arena.refs_wf cref.toNat href_t
                          have := hdwt.1.core_ok.arena_len_le
                          rw [BitVec.toNat_add, BitVec.toNat_add, m6_zext32_toNat,
                            m6_zext32_toNat, show (3#64).toNat = 3 from rfl,
                            show BitVec.toNat (3 : BitVec 64) = 3 from rfl,
                            Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
                            Nat.mod_eq_of_lt (by omega)]
                        have hli_c0 : st.core.arena[(cref.toNat + BitVec.toNat (3 : BitVec 64) +
                            i.toNat) % 2 ^ 64]'(by rw [hli_idx]; exact hcri) = li :=
                          m6_getElem_congr hli_idx (by rw [hli_idx]; exact hcri) hcri
                        have hval_c0 : st.core.vals[(st.core.arena[(cref.toNat +
                                BitVec.toNat (3 : BitVec 64) + i.toNat) % 2 ^ 64]'(by
                                  rw [hli_idx]; exact hcri)).toNat]'(by
                                    rw [hli_c0]; exact hlt_v) =
                              st.core.vals[li.toNat]'hlt_v :=
                          m6_getElem_congr (congrArg BitVec.toNat hli_c0) _ hlt_v
                        rw [List.getElem?_eq_getElem hlt_v, Option.getD_some] at hdom ⊢
                        exact m6_bv8_dom_neg_slt hdom (by simpa only [hval_c0] using hc)
                      c0_hsplit
                      · c0_hsteps!; exact hJd li (fun _ => ⟨hli_lt, hff_i⟩)
                      · c0_hsteps!; exact hJd drop_i hdrop_ok
                    · c0_hsteps!; exact hJd drop_i hdrop_ok)
            · c0_hsteps!; exact hBi (false, drop_i, i, ()) _ ⟨rfl, fun _ => hdrop_ok⟩
          · intro _ Li _ hLi; c0_hsteps!
            exact hLi sz.toNat (0xFFFFFFFF#32, 0#32, ()) _
              ⟨rfl, Nat.zero_le _, by simp, fun h => absurd rfl h⟩
        · exact absurd hc (by decide)
      · intro L hL; c0_hsteps!
        exact hL sz0.toNat (hdr0, sz0, ()) m0
          ⟨s0, rfl, by omega, hdw0, rfl, rfl, rfl, rfl, rfl, rfl, hhdr0_eq, hsz0_eq, hng0, hm0⟩


end LeanQbe.T.Examples.Kissat.FullFidelityStep13S6a
