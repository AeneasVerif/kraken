/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S1SweepDenseProof2a
import LeanQbe.T.Examples.Kissat.FullM6SweepProofEls
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Examples.Kissat.FullDenseWatchLemmas
import LeanQbe.T.Examples.Kissat.FullCongLemmas1
import LeanQbe.T.Examples.Kissat.FullReduceLemmas1
import LeanQbe.T.Examples.Kissat.FullSpec1
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Fidelity Step 13 Shard S1-A Proofs — Part 2b (`full_m6_els_ar`)

Parametric `(Γ : Env)` proof (`public section`, `0` `@[expose]`, `0` `import all`,
`<= 100` cols, `< 1,400` LOC, every theorem `<= 420` lines):
1. `full_m6_els_ar_s13_wp` (`step13ElsArSpec`)
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep13S1

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM6Sweep
open FullM6Sweep.M6ElsBv
open Kraken.Bedrock2.Test

open scoped FullArenaTactics FullM6Sweep.M6SweepTactics

private def s13ElsArPostL3Expr (h : Val i64) (cr rl : Val i32)
    (pArena _pLitMark pTmp : Val i64) (hdr sz32 : Val i32)
    (taut2 : Val .bool) (nsz2 : Val i32) (has_rl : Val .bool) :
    Expr Val Cont [.bool] :=
  Expr.group (sig := [[]]) (fun _Js => Blocks.cons (fun _ =>
    Expr.let_ (Op.mk (.zext 32 64) (Arg.var cr, ())) (fun (cr64, ()) =>
    Expr.let_ (Op.mk (.mul i64) (Arg.var cr64, Arg.imm 4, ())) (fun (o_cr, ()) =>
    Expr.let_ (Op.mk (.add i64) (Arg.var pArena, Arg.var o_cr, ())) (fun (a_cr, ()) =>
    Expr.let_ (Op.mk (.or i32) (Arg.var hdr, Arg.imm 524288, ())) (fun (hdr_g, ()) =>
    Expr.store (Arg.var hdr_g) (Arg.var a_cr)
      (Expr.let_ (Op.mk (.add i64) (Arg.var h, Arg.imm 472, ())) (fun (pag0, ()) =>
      Expr.load i64 (Arg.var pag0) (fun ag0 =>
      Expr.let_ (Op.mk (.add i64) (Arg.var ag0, Arg.imm 3, ())) (fun (ag3, ()) =>
      Expr.let_ (Op.mk (.zext 32 64) (Arg.var sz32, ())) (fun (sz64, ()) =>
      Expr.let_ (Op.mk (.add i64) (Arg.var ag3, Arg.var sz64, ())) (fun (ag_new, ()) =>
      Expr.let_ (Op.mk (.add i64) (Arg.var h, Arg.imm 472, ())) (fun (pag1, ()) =>
      Expr.store (Arg.var ag_new) (Arg.var pag1)
        (Expr.group (sig := [[]]) (fun _Js => Blocks.cons (fun _ =>
          Expr.group (sig := [[]]) (fun _Js => Blocks.cons (fun _ =>
            Expr.group (sig := [[]]) (fun _Js => Blocks.cons (fun _ =>
              Expr.ret (Arg.imm true, ())) Blocks.nil)
            (fun Js =>
              Expr.jnz (Arg.var taut2) (Expr.jump Js.fst ())
                (Expr.let_ (Op.mk (.cmp .eq i32 .bool rfl)
                    (Arg.var nsz2, Arg.imm 2, ())) (fun (bn2, ()) =>
                  Expr.jnz (Arg.var bn2)
                    (Expr.let_ (Op.mk (.sext 32 64) (Arg.imm 0, ())) (fun (z0, ()) =>
                    Expr.let_ (Op.mk (.mul i64) (Arg.var z0, Arg.imm 4, ())) (fun (o0, ()) =>
                    Expr.let_ (Op.mk (.add i64) (Arg.var pTmp, Arg.var o0, ())) (fun (a0, ()) =>
                    Expr.load i32 (Arg.var a0) (fun t0 =>
                    Expr.let_ (Op.mk (.sext 32 64) (Arg.imm 1, ())) (fun (z1, ()) =>
                    Expr.let_ (Op.mk (.mul i64) (Arg.var z1, Arg.imm 4, ())) (fun (o1, ()) =>
                    Expr.let_ (Op.mk (.add i64) (Arg.var pTmp, Arg.var o1, ())) (fun (a1, ()) =>
                    Expr.load i32 (Arg.var a1) (fun t1 =>
                    Expr.call (as := [i64, i32, i32]) (bs := [i64]) "full_add_bin"
                      (Arg.var h, Arg.var t0, Arg.var t1, ()) (fun (rB, ()) =>
                    Expr.let_ (Op.mk (.cmp .eq i64 .bool rfl)
                        (Arg.var rB, Arg.imm 20, ())) (fun (b20, ()) =>
                    Expr.jnz (Arg.var b20) (Expr.ret (Arg.imm false, ()))
                      (Expr.group (sig := [[]]) (fun _Js1 => Blocks.cons (fun _ =>
                        Expr.jump Js.fst ()) Blocks.nil)
                      (fun Js =>
                        Expr.let_ (Op.mk (.cmp .eq i64 .bool rfl)
                            (Arg.var rB, Arg.imm 2, ())) (fun (b2, ()) =>
                        Expr.jnz (Arg.var b2)
                          (Expr.let_ (Op.mk (.add i64) (Arg.var h, Arg.imm 760, ()))
                              (fun (po, ()) =>
                            Expr.store (t := i64) (Arg.imm 1) (Arg.var po) (Expr.jump Js.fst ())))
                          (Expr.jump Js.fst ())))))))))))))))
                    (Expr.jump Js.fst ()))))) Blocks.nil)
          (fun Js =>
            Expr.jnz (Arg.var taut2) (Expr.jump Js.fst ())
              (Expr.let_ (Op.mk (.cmp .eq i32 .bool rfl)
                  (Arg.var nsz2, Arg.imm 1, ())) (fun (bn1, ()) =>
                Expr.jnz (Arg.var bn1)
                  (Expr.let_ (Op.mk (.sext 32 64) (Arg.imm 0, ())) (fun (z0, ()) =>
                  Expr.let_ (Op.mk (.mul i64) (Arg.var z0, Arg.imm 4, ())) (fun (o0, ()) =>
                  Expr.let_ (Op.mk (.add i64) (Arg.var pTmp, Arg.var o0, ())) (fun (a0, ()) =>
                  Expr.load i32 (Arg.var a0) (fun t0 =>
                  Expr.call (as := [i64, i32]) (bs := [.bool]) "full_add_unit"
                    (Arg.var h, Arg.var t0, ()) (fun (okU, ()) =>
                  Expr.jnz (Arg.var okU) (Expr.jump Js.fst ())
                    (Expr.ret (Arg.imm false, ()))))))))
                  (Expr.jump Js.fst ()))))) Blocks.nil)
        (fun Js =>
          Expr.jnz (Arg.var taut2) (Expr.jump Js.fst ())
            (Expr.let_ (Op.mk (.cmp .eq i32 .bool rfl)
                (Arg.var nsz2, Arg.imm 0, ())) (fun (bn0, ()) =>
              Expr.jnz (Arg.var bn0)
                (Expr.let_ (Op.mk (.add i64) (Arg.var h, Arg.imm 1024, ())) (fun (pin, ()) =>
                  Expr.store (t := i64) (Arg.imm 1) (Arg.var pin)
                    (Expr.ret (Arg.imm false, ()))))
                (Expr.jump Js.fst ()))))))))))))))))) Blocks.nil)
  (fun Js =>
    Expr.jnz (Arg.var taut2) (Expr.jump Js.fst ())
      (Expr.let_ (Op.mk (.cmp .ule i32 .bool rfl) (Arg.var nsz2, Arg.imm 2, ())) (fun (ble2, ()) =>
        Expr.jnz (Arg.var ble2) (Expr.jump Js.fst ())
          (Expr.group (sig := [[i32]]) (fun Js1 => Blocks.cons (fun (k4, ()) =>
            Expr.let_ (Op.mk (.cmp .ult i32 .bool rfl) (Arg.var k4, Arg.var nsz2, ()))
              (fun (bk4, ()) =>
            Expr.jnz (Arg.var bk4)
              (Expr.let_ (Op.mk (.zext 32 64) (Arg.var cr, ())) (fun (cr64, ()) =>
              Expr.let_ (Op.mk (.add i64) (Arg.var cr64, Arg.imm 3, ())) (fun (cr3, ()) =>
              Expr.let_ (Op.mk (.zext 32 64) (Arg.var k4, ())) (fun (k4_64, ()) =>
              Expr.let_ (Op.mk (.add i64) (Arg.var cr3, Arg.var k4_64, ())) (fun (cr3k, ()) =>
              Expr.let_ (Op.mk (.mul i64) (Arg.var cr3k, Arg.imm 4, ())) (fun (oar, ()) =>
              Expr.let_ (Op.mk (.add i64) (Arg.var pArena, Arg.var oar, ())) (fun (aar, ()) =>
              Expr.let_ (Op.mk (.zext 32 64) (Arg.var k4, ())) (fun (k4_64b, ()) =>
              Expr.let_ (Op.mk (.mul i64) (Arg.var k4_64b, Arg.imm 4, ())) (fun (otm, ()) =>
              Expr.let_ (Op.mk (.add i64) (Arg.var pTmp, Arg.var otm, ())) (fun (atm, ()) =>
              Expr.load i32 (Arg.var atm) (fun tv =>
              Expr.store (Arg.var tv) (Arg.var aar)
                (Expr.let_ (Op.mk (.add i32) (Arg.var k4, Arg.imm 1, ())) (fun (k4n, ()) =>
                Expr.jump Js1.fst (Arg.var k4n, ()))))))))))))))
              (Expr.group (sig := [[]]) (fun _Js2 => Blocks.cons (fun _ =>
                Expr.group (sig := [[]]) (fun _Js3 => Blocks.cons (fun _ =>
                  Expr.ret (Arg.imm true, ())) Blocks.nil)
                (fun Js =>
                  Expr.jnz (Arg.var has_rl) (Expr.jump Js.fst ())
                    (Expr.let_ (Op.mk (.and i32) (Arg.var nsz2, Arg.imm 2147483647, ()))
                        (fun (nmask, ()) =>
                      Expr.call (as := [i64, i32, i32, i32, i32]) (bs := [.bool]) "full_watch_push"
                        (Arg.var h, Arg.var rl, Arg.var nmask, Arg.var cr, Arg.imm 2, ())
                        (fun (okp, ()) =>
                      Expr.jnz (Arg.var okp) (Expr.jump Js.fst ())
                        (Expr.let_ (Op.mk (.add i64) (Arg.var h, Arg.imm 760, ()))
                            (fun (po, ()) =>
                          Expr.store (t := i64) (Arg.imm 1) (Arg.var po)
                            (Expr.jump Js.fst ())))))))) Blocks.nil)
              (fun Js =>
                Expr.let_ (Op.mk (.cmp .ult i32 .bool rfl) (Arg.var nsz2, Arg.var sz32, ()))
                  (fun (blt, ()) =>
                Expr.jnz (Arg.var blt)
                  (Expr.let_ (Op.mk (.zext 32 64) (Arg.var cr, ())) (fun (cr64, ()) =>
                  Expr.let_ (Op.mk (.add i64) (Arg.var cr64, Arg.imm 2, ())) (fun (cr2, ()) =>
                  Expr.let_ (Op.mk (.mul i64) (Arg.var cr2, Arg.imm 4, ())) (fun (o2, ()) =>
                  Expr.let_ (Op.mk (.add i64) (Arg.var pArena, Arg.var o2, ())) (fun (a2, ()) =>
                  Expr.store (Arg.var nsz2) (Arg.var a2)
                    (Expr.let_ (Op.mk (.zext 32 64) (Arg.var cr, ())) (fun (cr64b, ()) =>
                    Expr.let_ (Op.mk (.add i64) (Arg.var cr64b, Arg.imm 1, ())) (fun (cr1, ()) =>
                    Expr.let_ (Op.mk (.mul i64) (Arg.var cr1, Arg.imm 4, ())) (fun (o1, ()) =>
                    Expr.let_ (Op.mk (.add i64) (Arg.var pArena, Arg.var o1, ())) (fun (a1, ()) =>
                    Expr.store (t := i32) (Arg.imm 2) (Arg.var a1)
                      (Expr.group (sig := [[]]) (fun _Js3 => Blocks.cons (fun _ =>
                        Expr.jump Js.fst ()) Blocks.nil)
                      (fun Js =>
                        Expr.let_ (Op.mk (.and i32) (Arg.var hdr, Arg.imm 8388608, ()))
                            (fun (hs, ()) =>
                        Expr.let_ (Op.mk (.cmp .eq i32 .bool rfl) (Arg.var hs, Arg.imm 0, ()))
                            (fun (hs0, ()) =>
                        Expr.jnz (Arg.var hs0)
                          (Expr.let_ (Op.mk (.zext 32 64) (Arg.var cr, ())) (fun (cr64c, ()) =>
                          Expr.let_ (Op.mk (.mul i64) (Arg.var cr64c, Arg.imm 4, ()))
                              (fun (o0, ()) =>
                          Expr.let_ (Op.mk (.add i64) (Arg.var pArena, Arg.var o0, ()))
                              (fun (a0, ()) =>
                          Expr.let_ (Op.mk (.or i32) (Arg.var hdr, Arg.imm 8388608, ()))
                              (fun (hdr_s, ()) =>
                          Expr.store (Arg.var hdr_s) (Arg.var a0)
                            (Expr.let_ (Op.mk (.zext 32 64) (Arg.var cr, ())) (fun (cr64d, ()) =>
                            Expr.let_ (Op.mk (.add i64) (Arg.var cr64d, Arg.imm 3, ()))
                                (fun (cr3, ()) =>
                            Expr.let_ (Op.mk (.zext 32 64) (Arg.var sz32, ())) (fun (sz64, ()) =>
                            Expr.let_ (Op.mk (.add i64) (Arg.var cr3, Arg.var sz64, ()))
                                (fun (cr3s, ()) =>
                            Expr.let_ (Op.mk (.sub i64) (Arg.var cr3s, Arg.imm 1, ()))
                                (fun (last_i, ()) =>
                            Expr.let_ (Op.mk (.mul i64) (Arg.var last_i, Arg.imm 4, ()))
                                (fun (olast, ()) =>
                            Expr.let_ (Op.mk (.add i64) (Arg.var pArena, Arg.var olast, ()))
                                (fun (alast, ()) =>
                            Expr.store (t := i32) (Arg.imm 4294967295) (Arg.var alast)
                              (Expr.jump Js.fst ()))))))))))))))
                          (Expr.jump Js.fst ())))))))))))))))
                  (Expr.jump Js.fst ())))))) Blocks.nil)
          (fun Js => Expr.jump Js.fst (Arg.imm 0, ()))))))

private theorem s13_els_ar_post_l3_wp {Γ : Env} {Q : Post [.bool]} {X : XPost}
    (hWatch : M6EnvSpec Γ "full_watch_push" Full.fullWatchPushSpec)
    (hAddUnit : M6EnvSpec Γ "full_add_unit" Full.fullAddUnitSpec)
    (hAddBin : M6EnvSpec Γ "full_add_bin" Full.fullAddBinSpec)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s sC : FullState}
    {cr rl sz32 nsz2 : BitVec 32} {taut2 has_rl : Bool}
    {lm2 : List (BitVec 8)} {tmp2 : List (BitVec 32)}
    {R : Mem 64 → Prop} {mC : Mem 64}
    (hinvC : FullDenseInvW c F0 F_cur sC)
    (hoC : S13ElsArOut c F0 F_cur s sC)
    (hsC_ar : sC.core.arena = s.core.arena) (hsC_tmp : sC.core.tmp = tmp2)
    (_hcr_ref : cr.toNat ∈ fullArenaClauseRefs s)
    (hcr_refC : cr.toNat ∈ fullArenaClauseRefs sC)
    (hng_cr : fullArenaClauseGarb s cr.toNat = false)
    (hcr_bd : cr.toNat < s.core.arena.length) (hcr2_bd : cr.toNat + 2 < s.core.arena.length)
    (hsz_def : sz32.toNat = fullArenaClauseSize s cr.toNat)
    (hsz_ar_bd : cr.toNat + 3 + sz32.toNat ≤ s.core.arena.length)
    (hsz_lt_dim : sz32.toNat < 2 ^ 31)
    (hcr_lt_dim : cr.toNat < 0x80000000) (hcr_ne : cr ≠ 0xFFFFFFFF#32)
    (hnsz_sz : nsz2.toNat ≤ sz32.toNat)
    (hmap2 : S13ElsLitMap c s lm2 tmp2 nsz2.toNat)
    (hhent : taut2 = false →
      (cnfOfClauses F_cur).EntailsClause (cnfClause ((tmp2.take nsz2.toNat).map BitVec.toNat)))
    (hmC : (FullMem c sC ⋆ R) mC)
    (hQ : ∀ (ok : Bool) (s' : FullState) (m' : Mem 64),
      FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.fuel = s.core.fuel → FullCongReprInv F_cur (2 * s.core.cur_vars) s'.core.repr →
      s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
      s'.scratch.tarjan_reach = s.scratch.tarjan_reach →
      s'.scratch.scratch_buf = s.scratch.scratch_buf →
      s'.scratch.work_stk1 = s.scratch.work_stk1 →
      s'.scratch.work_stk2 = s.scratch.work_stk2 →
      s'.scratch.glue_used = s.scratch.glue_used →
      (ok = false → F0.Unsat ∧ s'.core.inconsistent ≠ 0#64) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m') :
    wp Γ Q X
      (s13ElsArPostL3Expr c.hdr cr rl c.pArena c.pLitMark c.pTmp
        (s.core.arena[cr.toNat]'hcr_bd) sz32 taut2 nsz2 has_rl) mC := by
  unfold s13ElsArPostL3Expr
  have hclC := hinvC.1.core_ok
  have har_len := hinvC.1.core_ok.arena_len_arr
  have har_s_len : s.core.arena.length = c.arena_cap := hsC_ar ▸ har_len
  have hcr_bdC : cr.toNat < sC.core.arena.length := by rw [hsC_ar]; exact hcr_bd
  have hmx := c.hmaxv; have har := c.harena; unfold dimacsBound at hmx har
  have hcr64_eq : (BitVec.setWidth 64 cr).toNat = cr.toNat := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
  have hcr2_eq : (cr.setWidth 64 + 2#64).toNat = cr.toNat + 2 := by bv_omega
  have hcr1_eq : (cr.setWidth 64 + 1#64).toNat = cr.toNat + 1 := by bv_omega
  refine wp_join_group (ts := []) (fun () m_garb =>
      (taut2 = true ∨ nsz2.toNat ≤ 2) ∧ (FullMem c sC ⋆ R) m_garb) ?_ ?_
  · rintro _ ⟨⟩ m_garb ⟨_htg, hm_g0⟩
    let ag' := sC.core.arena_garbage + 3#64 + sz32.setWidth 64
    obtain ⟨hinvG, _⟩ := s13_denseInvW_markGarb hinvC hcr_refC ag'
    let sG : FullState :=
      { sC with core :=
        { sC.core with
          arena := sC.core.arena.set cr.toNat (fullArenaHdr sC cr.toNat ||| 0x00080000#32)
          arena_garbage := ag' } }
    have hoG : S13ElsArOut c F0 F_cur s sG :=
      ⟨hinvG, hoC.cv, hoC.fuel, hoC.repr, hoC.tmk, hoC.trh, hoC.scr, hoC.ws1, hoC.ws2, hoC.gu⟩
    have hhd_sC : s.core.arena[cr.toNat]'hcr_bd = fullArenaHdr sC cr.toNat := by
      unfold fullArenaHdr fullArenaHdrCore; rw [hsC_ar]
      change s.core.arena[cr.toNat]'hcr_bd = s.core.arena[cr.toNat]?.getD 0#32
      rw [List.getElem?_eq_getElem hcr_bd, Option.getD_some]
    c0_hsteps_nogrp
    have hsG_eq :
        ({ sC with core := { sC.core with
            arena := sC.core.arena.set (BitVec.setWidth 64 cr).toNat
              ((s.core.arena[cr.toNat]'hcr_bd) ||| 0x00080000#32),
            arena_garbage := sC.core.arena_garbage + 3#64 + BitVec.setWidth 64 sz32 } } :
          FullState) = sG := by
      dsimp only [sG, ag']; rw [hcr64_eq, hhd_sC]
    refine wp_join_group (ts := []) (fun () mU =>
        (FullMem c sG ⋆ R) mU ∧ ¬ (taut2 = false ∧ nsz2.toNat = 0)) ?_ ?_
    · rintro _ ⟨⟩ mU ⟨hmU, _⟩
      refine wp_join_group (ts := []) (fun () mB => ∃ sB : FullState,
          S13ElsArOut c F0 F_cur s sB ∧ sB.core.tmp = tmp2 ∧ (FullMem c sB ⋆ R) mB) ?_ ?_
      · rintro _ ⟨⟩ mB ⟨sB, hoB, htmpB, hmB⟩
        refine wp_join_group (ts := []) (fun () mRet => ∃ sR : FullState,
            S13ElsArOut c F0 F_cur s sR ∧ (FullMem c sR ⋆ R) mRet) ?_ ?_
        · rintro _ ⟨⟩ mRet ⟨sR, hoR, hmR⟩
          c0_hsteps!; exact s13_els_ar_ret_bool hoR hmR hQ
        · intro JW hJW
          c0_hsplit
          · c0_hsteps!; exact hJW () mB ⟨sB, hoB, hmB⟩
          · have htf : taut2 = false := by cases taut2 <;> first | rfl | contradiction
            c0_hsplit
            · have hn2 : nsz2.toNat = 2 := by bv_omega
              have htmp2_l := hmap2.tmp_len; have hnsz2_l := hmap2.nsz_le
              have hcv2_l := hmap2.cv_le
              have hent2 := hhent htf
              have htake2 : (tmp2.take 2).map BitVec.toNat =
                  [(tmp2[0]'(by omega)).toNat, (tmp2[1]'(by omega)).toNat] := by
                have hl2 : 2 ≤ tmp2.length := by omega
                rcases tmp2 with _ | ⟨a, _ | ⟨b, _⟩⟩
                · exfalso; simp at hl2
                · exfalso; simp at hl2
                · rfl
              rw [hn2, htake2] at hent2
              have htmp_lenB : sB.core.tmp.length = c.max_vars := hoB.dinv.1.core_ok.tmp_len_arr
              have htmp0_posB : 0 < sB.core.tmp.length := by omega
              have htmp1_posB : 1 < sB.core.tmp.length := by omega
              c0_hsteps_nogrp
              refine s13_els_ar_call_addBin hAddBin rfl
                (by simp only [Arg.val, htmpB]; rfl)
                (by simp only [Arg.val, htmpB]; rfl) hoB
                (by simpa only [← htmpB, BitVec.toNat_ofNat, Nat.zero_mod,
                  Nat.mod_eq_of_lt (by decide : 1 < 2 ^ 64)] using hent2) hmB ?_
              intro rB sBn mBn hoBn hr20 hmBn
              c0_hsplit
              · have hrB : rB = 20#64 := by bv_omega
                c0_hsteps!; exact s13_els_ar_ret_false hoBn (hr20 hrB) hmBn hQ
              · refine wp_join_group (ts := []) (fun () mRet => ∃ sR : FullState,
                    S13ElsArOut c F0 F_cur s sR ∧ (FullMem c sR ⋆ R) mRet) ?_ ?_
                · rintro _ ⟨⟩ mRet ⟨sR, hoR, hmR⟩; c0_hsteps!; exact hJW () mRet ⟨sR, hoR, hmR⟩
                · intro J2 hJ2; c0_hsplit
                  · c0_hsteps!
                    exact hJ2 () _ ⟨{ sBn with core := { sBn.core with oom := 1#64 } },
                      ⟨s13_denseInvW_set_oom hoBn.dinv, hoBn.cv, hoBn.fuel, hoBn.repr,
                       hoBn.tmk, hoBn.trh, hoBn.scr, hoBn.ws1, hoBn.ws2, hoBn.gu⟩, by assumption⟩
                  · c0_hsteps!; exact hJ2 () mBn ⟨sBn, hoBn, hmBn⟩
            · c0_hsteps!; exact hJW () mB ⟨sB, hoB, hmB⟩
      · intro J5 hJ5; c0_hsplit
        · c0_hsteps!; exact hJ5 () mU ⟨sG, hoG, hsC_tmp, hmU⟩
        · have htf : taut2 = false := by cases taut2 <;> first | rfl | contradiction
          c0_hsplit
          · have hn1 : nsz2.toNat = 1 := by bv_omega
            have htmp2_l := hmap2.tmp_len; have hnsz2_l := hmap2.nsz_le
            have hcv2_l := hmap2.cv_le
            have hent1 := hhent htf
            have htake1 : (tmp2.take 1).map BitVec.toNat = [(tmp2[0]'(by omega)).toNat] := by
              have hl1 : 1 ≤ tmp2.length := by omega
              rcases tmp2 with _ | ⟨a, _⟩
              · exfalso; simp at hl1
              · rfl
            rw [hn1, htake1] at hent1
            have htmp0_lt : (tmp2[0]'(by omega)).toNat < 2 * sG.core.cur_vars := by
              rw [hoG.cv]
              have := hmap2.tmp_lt 0 (by omega)
              rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at this
            have htmp_lenG : sG.core.tmp.length = c.max_vars := hoG.dinv.1.core_ok.tmp_len_arr
            have htmp_posG : 0 < sG.core.tmp.length := by omega
            c0_hsteps_nogrp
            refine s13_els_ar_call_addUnit hAddUnit rfl
              (by dsimp only [Arg.val, sG]
                  simp only [hsC_tmp, BitVec.toNat_ofNat, Nat.zero_mod])
              hoG htmp0_lt (by simpa only [← hsC_tmp] using hent1) hmU ?_
            intro okU sU mUn hoU htmpU hfail hmUn
            c0_hsplit
            · c0_hsteps!; exact hJ5 () mUn ⟨sU, hoU, htmpU.trans hsC_tmp, hmUn⟩
            · have hokf : okU = false := by cases okU <;> first | rfl | contradiction
              c0_hsteps!; exact s13_els_ar_ret_false hoU (hfail hokf) hmUn hQ
          · c0_hsteps!; exact hJ5 () mU ⟨sG, hoG, hsC_tmp, hmU⟩
    · intro J4 hJ4; c0_hsplit
      · c0_hsteps!
        refine hJ4 () _ ⟨?_, fun h => Bool.noConfusion (h.1.symm.trans ‹_›)⟩
        rw [← hsG_eq]; exact (by assumption)
      · have htf : taut2 = false := by cases taut2 <;> first | rfl | contradiction
        c0_hsplit
        · have hnz : nsz2.toNat = 0 := by bv_omega
          have hent0 := hhent htf; rw [hnz, List.take_zero, List.map_nil] at hent0
          have huns : (cnfOfClauses F_cur).Unsat := s13_unsat_of_nil_entails hent0
          c0_hsteps!
          let sI : FullState := { sG with core := { sG.core with inconsistent := 1#64 } }
          have hinvI := m6_denseInvW_set_inconsistent hinvG huns
          have hoI : S13ElsArOut c F0 F_cur s sI :=
            ⟨hinvI, hoG.cv, hoG.fuel, hoG.repr, hoG.tmk, hoG.trh, hoG.scr, hoG.ws1, hoG.ws2,
              hoG.gu⟩
          refine s13_els_ar_ret_false hoI ⟨hinvG.2.1.ext_sound.2 huns, by simp [sI]⟩ ?_ hQ
          dsimp only [sI]; rw [← hsG_eq]; exact (by assumption)
        · c0_hsteps!
          refine hJ4 () _ ⟨?_, fun h => by bv_omega⟩
          rw [← hsG_eq]; exact (by assumption)
  · intro J3 hJ3
    c0_hsplit
    · c0_hsteps!; exact hJ3 () mC ⟨Or.inl ‹_›, hmC⟩
    c0_hsplit
    · c0_hsteps!; exact hJ3 () mC ⟨Or.inr ‹_›, hmC⟩
    · have htf : taut2 = false := by cases taut2 <;> first | rfl | contradiction
      have h3n : 3 ≤ nsz2.toNat := by bv_omega
      have hnsz_le := hmap2.nsz_le
      c0_hsteps_nogrp
      refine wp_while_state (ts := [i32]) (proj := fun k : BitVec 32 => (k, ()))
        (μ := fun k => nsz2.toNat - k.toNat)
        (Inv := fun k ml => k.toNat ≤ nsz2.toNat ∧ ∃ ar4 : List (BitVec 32),
          ar4.length = c.arena_cap ∧
          (∀ i, i < cr.toNat + 3 ∨ cr.toNat + 3 + k.toNat ≤ i → ar4[i]? = sC.core.arena[i]?) ∧
          (∀ j < k.toNat, ar4[cr.toNat + 3 + j]? = tmp2[j]?) ∧
          (FullMem c { sC with core := { sC.core with arena := ar4 } } ⋆ R) ml) ?_ ?_
      · intro J4 hJ4; c0_hsteps!
        exact hJ4 0#32 mC ⟨Nat.zero_le _, sC.core.arena, har_len, fun _ _ => rfl,
          (fun _ hj => by cases hj), hmC⟩
      · rintro J4 k4 ml ⟨hk4, ar4, har4, hout4, hcp4, hml⟩ ih4
        c0_hsplit
        · have hk4_lt : k4.toNat < nsz2.toNat := ‹_›
          have hk1 : (k4 + 1#32).toNat = k4.toNat + 1 := by bv_omega
          have hcv_le2 := hmap2.cv_le
          have htk_bd : k4.toNat < tmp2.length := by have := hmap2.tmp_len; omega
          have htk_bd64 : (BitVec.setWidth 64 k4).toNat < sC.core.tmp.length := by
            rw [hsC_tmp, bv_c0_zext32_64]; exact htk_bd
          have har_bd : cr.toNat + 3 + k4.toNat < ar4.length := by rw [har4]; omega
          have hidx_4_c0 : (BitVec.setWidth 64 cr + (3 : BitVec 64) +
              BitVec.setWidth 64 k4).toNat = cr.toNat + 3 + k4.toNat := by
            simp only [bv_c0, bv_c0_zext32_64, show ((3 : BitVec 64)).toNat = 3 from rfl]
            exact Nat.mod_eq_of_lt (by omega)
          c0_hsteps_nogrp
          have htmp_eq : sC.core.tmp[(BitVec.setWidth 64 k4).toNat]'htk_bd64 =
              tmp2[k4.toNat]'htk_bd := by
            simp only [hsC_tmp]; exact m6_getElem_congr (bv_c0_zext32_64 k4) _ htk_bd
          have hm4' : (FullMem c { sC with core := { sC.core with
              arena := ar4.set (cr.toNat + 3 + k4.toNat) (tmp2[k4.toNat]'htk_bd) } } ⋆ R) m := by
            rw [← hidx_4_c0, ← htmp_eq]; exact hm
          refine ih4 (k4 + 1#32) _ (by rw [hk1]; omega) ⟨by omega,
            ar4.set (cr.toNat + 3 + k4.toNat) (tmp2[k4.toNat]'htk_bd), by simp [har4],
            fun i hi => by
              rw [List.getElem?_set_ne (by omega)]
              exact hout4 i
                (by rcases hi with h | h; exact Or.inl h; exact Or.inr (by rw [hk1] at h; omega)),
            fun j hj => by
              by_cases hjk : j = k4.toNat
              · subst hjk; rw [List.getElem?_set_self har_bd, List.getElem?_eq_getElem htk_bd]
              · rw [List.getElem?_set_ne (by omega)]; exact hcp4 j (by omega),
            hm4'⟩
        · have hk_eq : k4.toNat = nsz2.toNat := by
            have hle : ¬ k4.toNat < nsz2.toNat := ‹_›; omega
          rw [hk_eq] at hout4 hcp4
          let s4 : FullState := { sC with core := { sC.core with arena := ar4 } }
          have hhent4 := hhent htf
          c0_hsteps_nogrp
          refine wp_join_group (ts := []) (fun () m5 => ∃ ar5 : List (BitVec 32),
              let s5 : FullState := { sC with core := { sC.core with arena := ar5 } }
              FullDenseInvW c F0 F_cur s5 ∧ fullArenaClauseRefs s5 = fullArenaClauseRefs sC ∧
              (FullMem c s5 ⋆ R) m5) ?_ ?_
          · rintro _ ⟨⟩ m5 ⟨ar5, hinv5, hrefs5, hm5⟩
            have hnsz_lt_dim : nsz2.toNat < 2 ^ 31 := by omega
            have hcr5 : cr.toNat ∈ fullArenaClauseRefs
                { sC with core := { sC.core with arena := ar5 } } := by
              rw [hrefs5]; exact hcr_refC
            c0_hsteps_nogrp
            refine wp_join_group (ts := []) (fun () mRet => ∃ sR : FullState,
                S13ElsArOut c F0 F_cur s sR ∧ (FullMem c sR ⋆ R) mRet) ?_ ?_
            · rintro _ ⟨⟩ mRet ⟨sR, hoR, hmR⟩; c0_hsteps!; exact s13_els_ar_ret_bool hoR hmR hQ
            · intro JW hJW
              c0_hsplit
              · c0_hsteps!
                exact hJW () m5 ⟨_, ⟨hinv5, hoC.cv, hoC.fuel, hoC.repr, hoC.tmk, hoC.trh,
                  hoC.scr, hoC.ws1, hoC.ws2, hoC.gu⟩, hm5⟩
              · refine s13_els_ar_push_watched hWatch rfl rfl rfl rfl rfl hinv5 hoC.cv hoC.fuel
                  hoC.repr hoC.tmk hoC.trh hoC.scr hoC.ws1 hoC.ws2 hoC.gu
                  h3n hnsz_lt_dim hcr_lt_dim hcr_ne hcr5 hm5 fun ok s' m' ho' hm' => ?_
                c0_hsplit
                · c0_hsteps!; exact hJW () m' ⟨s', ho', hm'⟩
                · c0_hsteps!
                  exact hJW () _ ⟨{ s' with core := { s'.core with oom := 1#64 } },
                    ⟨s13_denseInvW_set_oom ho'.dinv, ho'.cv, ho'.fuel, ho'.repr, ho'.tmk, ho'.trh,
                     ho'.scr, ho'.ws1, ho'.ws2, ho'.gu⟩, by assumption⟩
          · intro J5 hJ5; c0_hsplit
            · have hlt_sz : nsz2.toNat < sz32.toNat := ‹_›
              have hcr_bd2 : cr.toNat + 2 < ar4.length := by rw [har4]; omega
              have hcr_bd1 : cr.toNat + 1 < ar4.length := by rw [har4]; omega
              c0_hsteps_nogrp
              refine wp_join_group (ts := []) (fun () m6 => ∃ ar5 : List (BitVec 32),
                  let s5 : FullState := { sC with core := { sC.core with arena := ar5 } }
                  FullDenseInvW c F0 F_cur s5 ∧
                  fullArenaClauseRefs s5 = fullArenaClauseRefs sC ∧ (FullMem c s5 ⋆ R) m6) ?_ ?_
              · rintro _ ⟨⟩ m6 ⟨ar5, hinv5, hrefs5, hm6⟩
                c0_hsteps!; exact hJ5 () m6 ⟨ar5, hinv5, hrefs5, hm6⟩
              · intro J6 hJ6
                obtain ⟨hs0, hs1⟩ := s13_els_ar_shrink_helpers hinvC hcr_refC hng_cr hcr_bd
                  har4 hcr_bd2 hcr_bd1 hsC_ar hoC.cv hsz_def h3n hlt_sz hout4 hcp4 hmap2 hhent4
                have hhd_sC' : s.core.arena[cr.toNat]'hcr_bd = fullArenaHdr sC cr.toNat := by
                  unfold fullArenaHdr fullArenaHdrCore; rw [hsC_ar]
                  change s.core.arena[cr.toNat]'hcr_bd = s.core.arena[cr.toNat]?.getD 0#32
                  rw [List.getElem?_eq_getElem hcr_bd, Option.getD_some]
                have hcr3_bv : (BitVec.setWidth 64 cr + (3 : BitVec 64) +
                    BitVec.setWidth 64 sz32 - (1 : BitVec 64)).toNat =
                    cr.toNat + 3 + sz32.toNat - 1 := by
                  bv_omega
                have hcr3_lt_ar : (BitVec.setWidth 64 cr + (3 : BitVec 64) +
                    BitVec.setWidth 64 sz32 - (1 : BitVec 64)).toNat < ar4.length := by
                  rw [hcr3_bv, har4]; omega
                c0_hsplit
                · have hhd0 : (s.core.arena[cr.toNat]'hcr_bd &&& 0x00800000#32) = 0#32 := ‹_›
                  obtain ⟨hinv5, hrefs5⟩ := hs0 hhd0
                  c0_hsteps_nogrp
                  refine hJ6 () _ ⟨_, hinv5, hrefs5, ?_⟩
                  dsimp only; rw [← hhd_sC', ← hcr2_eq, ← hcr1_eq, ← hcr3_bv]; exact (by assumption)
                · have hhd1 : (s.core.arena[cr.toNat]'hcr_bd &&& 0x00800000#32) ≠ 0#32 := ‹_›
                  obtain ⟨hinv5, hrefs5⟩ := hs1 hhd1
                  c0_hsteps!
                  refine hJ6 () _ ⟨_, hinv5, hrefs5, ?_⟩
                  dsimp only; rw [← hcr2_eq, ← hcr1_eq]; exact (by assumption)
            · have hnsz_eq : nsz2.toNat = sz32.toNat := by
                have hle : ¬ nsz2.toNat < sz32.toNat := ‹_›; omega
              have hcr_bd2 : cr.toNat + 2 < ar4.length := by rw [har4]; omega
              obtain ⟨hinv4, hrefs4⟩ := s13_els_ar_same_ok hinvC hcr_refC hng_cr har4 hcr_bd2
                hsC_ar hoC.cv hsz_def hnsz_eq hout4 hcp4 hmap2 hhent4
              c0_hsteps!; exact hJ5 () ml ⟨ar4, hinv4, hrefs4, hml⟩

private def s13ElsArLoop2Expr (h : Val i64) (cr rl : Val i32)
    (pArena pRepr pLitMark pTmp : Val i64) (nlits : Val i64) (hdr sz32 : Val i32)
    (has_rl : Val .bool) : Expr Val Cont [.bool] :=
  Expr.group (sig := [[i32, .bool, i32]]) (fun _Js3 =>
    Blocks.cons (fun (p_30 : Tup Val [i32, .bool, i32]) =>
    let taut2 := p_30.2.1; let nsz2 := p_30.2.2.1;
    Expr.group (sig := [[i32]]) (fun Js => Blocks.cons (fun (k3, ()) =>
      Expr.let_ (Op.mk (.cmp .ult i32 .bool rfl) (Arg.var k3, Arg.var nsz2, ())) (fun (b3, ()) =>
      Expr.jnz (Arg.var b3)
        (Expr.let_ (Op.mk (.zext 32 64) (Arg.var k3, ())) (fun (k3_64, ()) =>
        Expr.let_ (Op.mk (.mul i64) (Arg.var k3_64, Arg.imm 4, ())) (fun (o3, ()) =>
        Expr.let_ (Op.mk (.add i64) (Arg.var pTmp, Arg.var o3, ())) (fun (a3, ()) =>
        Expr.load i32 (Arg.var a3) (fun tl =>
        Expr.let_ (Op.mk (.zext 32 64) (Arg.var tl, ())) (fun (tl_64, ()) =>
        Expr.let_ (Op.mk (.add i64) (Arg.var pLitMark, Arg.var tl_64, ())) (fun (alm, ()) =>
        Expr.let_ (Op.mk (.trunc 32 8) (Arg.imm 0, ())) (fun (z8, ()) =>
        Expr.store (Arg.var z8) (Arg.var alm)
          (Expr.let_ (Op.mk (.add i32) (Arg.var k3, Arg.imm 1, ())) (fun (k3n, ()) =>
          Expr.jump Js.fst (Arg.var k3n, ())))))))))))
        (s13ElsArPostL3Expr h cr rl pArena pLitMark pTmp hdr sz32 taut2 nsz2 has_rl))) Blocks.nil)
    (fun Js => Expr.jump Js.fst (Arg.imm 0, ()))) Blocks.nil)
  (fun Js =>
    Expr.group (sig := [[i32, i32]]) (fun J2 => Blocks.cons (fun (p_30 : Tup Val [i32, i32]) =>
      let k2 := p_30.1; let nszL := p_30.2.1;
      Expr.let_ (Op.mk (.cmp .ult i32 .bool rfl) (Arg.var k2, Arg.var sz32, ())) (fun (b2, ()) =>
      Expr.jnz (Arg.var b2)
        (Expr.let_ (Op.mk (.zext 32 64) (Arg.var cr, ())) (fun (cr64, ()) =>
        Expr.let_ (Op.mk (.add i64) (Arg.var cr64, Arg.imm 3, ())) (fun (cr3, ()) =>
        Expr.let_ (Op.mk (.zext 32 64) (Arg.var k2, ())) (fun (k2_64, ()) =>
        Expr.let_ (Op.mk (.add i64) (Arg.var cr3, Arg.var k2_64, ())) (fun (cr3k, ()) =>
        Expr.let_ (Op.mk (.mul i64) (Arg.var cr3k, Arg.imm 4, ())) (fun (oar, ()) =>
        Expr.let_ (Op.mk (.add i64) (Arg.var pArena, Arg.var oar, ())) (fun (aar, ()) =>
        Expr.load i32 (Arg.var aar) (fun x =>
        Expr.group (sig := [[i32]]) (fun _J3 => Blocks.cons (fun (rx, ()) =>
          Expr.group (sig := [[.bool, i32]]) (fun _J4 =>
            Blocks.cons (fun (st4 : Tup Val [.bool, i32]) =>
            Expr.let_ (Op.mk (.add i32) (Arg.var k2, Arg.imm 1, ())) (fun (k2n, ()) =>
            Expr.jump J2.fst (Arg.var k2n, Arg.var st4.2.1, ()))) Blocks.nil)
          (fun J4 =>
            Expr.let_ (Op.mk (.zext 32 64) (Arg.var rx, ())) (fun (rx64, ()) =>
            Expr.let_ (Op.mk (.cmp .ult i64 .bool rfl) (Arg.var rx64, Arg.var nlits, ()))
              (fun (brx, ()) =>
            Expr.jnz (Arg.var brx)
              (Expr.let_ (Op.mk (.xor i32) (Arg.var rx, Arg.imm 1, ())) (fun (rx1, ()) =>
              Expr.let_ (Op.mk (.zext 32 64) (Arg.var rx1, ())) (fun (rx1_64, ()) =>
              Expr.let_ (Op.mk (.add i64) (Arg.var pLitMark, Arg.var rx1_64, ())) (fun (al1, ()) =>
              Expr.load i8 (Arg.var al1) (fun v1 =>
              Expr.let_ (Op.mk (.trunc 32 8) (Arg.imm 0, ())) (fun (z8, ()) =>
              Expr.let_ (Op.mk (.zext 8 32) (Arg.var v1, ())) (fun (v1_32, ()) =>
              Expr.let_ (Op.mk (.zext 8 32) (Arg.var z8, ())) (fun (z32, ()) =>
              Expr.let_ (Op.mk (.cmp .ne i32 .bool rfl) (Arg.var v1_32, Arg.var z32, ()))
                (fun (b_taut, ()) =>
              Expr.jnz (Arg.var b_taut)
                (Expr.jump Js.fst (Arg.var k2, Arg.imm true, Arg.var nszL, ()))
                (Expr.group (sig := [[i32]]) (fun _J5 => Blocks.cons (fun (nsz', ()) =>
                  Expr.jump J4.fst (Arg.imm false, Arg.var nsz', ())) Blocks.nil)
                (fun J5 =>
                  Expr.let_ (Op.mk (.zext 32 64) (Arg.var rx, ())) (fun (rx64b, ()) =>
                  Expr.let_ (Op.mk (.add i64) (Arg.var pLitMark, Arg.var rx64b, ()))
                      (fun (al0, ()) =>
                  Expr.load i8 (Arg.var al0) (fun v0 =>
                  Expr.let_ (Op.mk (.trunc 32 8) (Arg.imm 0, ())) (fun (z8b, ()) =>
                  Expr.let_ (Op.mk (.zext 8 32) (Arg.var v0, ())) (fun (v0_32, ()) =>
                  Expr.let_ (Op.mk (.zext 8 32) (Arg.var z8b, ())) (fun (z32b, ()) =>
                  Expr.let_ (Op.mk (.cmp .eq i32 .bool rfl) (Arg.var v0_32, Arg.var z32b, ()))
                    (fun (b_new, ()) =>
                  Expr.jnz (Arg.var b_new)
                    (Expr.let_ (Op.mk (.zext 32 64) (Arg.var nszL, ())) (fun (nsz64, ()) =>
                    Expr.let_ (Op.mk (.add i64) (Arg.var h, Arg.imm 768, ())) (fun (pmv, ()) =>
                    Expr.load i64 (Arg.var pmv) (fun mv =>
                    Expr.let_ (Op.mk (.cmp .ult i64 .bool rfl) (Arg.var nsz64, Arg.var mv, ()))
                      (fun (bmv, ()) =>
                    Expr.jnz (Arg.var bmv)
                      (Expr.let_ (Op.mk (.zext 32 64) (Arg.var rx, ())) (fun (rx64c, ()) =>
                      Expr.let_ (Op.mk (.add i64) (Arg.var pLitMark, Arg.var rx64c, ()))
                          (fun (al0w, ()) =>
                      Expr.let_ (Op.mk (.trunc 32 8) (Arg.imm 1, ())) (fun (o8, ()) =>
                      Expr.store (Arg.var o8) (Arg.var al0w)
                        (Expr.let_ (Op.mk (.zext 32 64) (Arg.var nszL, ())) (fun (nsz64b, ()) =>
                        Expr.let_ (Op.mk (.mul i64) (Arg.var nsz64b, Arg.imm 4, ()))
                            (fun (ont, ()) =>
                        Expr.let_ (Op.mk (.add i64) (Arg.var pTmp, Arg.var ont, ()))
                            (fun (ant, ()) =>
                        Expr.store (Arg.var rx) (Arg.var ant)
                          (Expr.let_ (Op.mk (.add i32) (Arg.var nszL, Arg.imm 1, ()))
                              (fun (nszn, ()) =>
                          Expr.jump J5.fst (Arg.var nszn, ())))))))))))
                      (Expr.jump J5.fst (Arg.var nszL, ())))))))
                    (Expr.jump J5.fst (Arg.var nszL, ()))))))))))))))))))))
              (Expr.jump J4.fst (Arg.imm false, Arg.var nszL, ())))))) Blocks.nil)
        (fun J3 =>
          Expr.let_ (Op.mk (.zext 32 64) (Arg.var x, ())) (fun (x64, ()) =>
          Expr.let_ (Op.mk (.cmp .ult i64 .bool rfl) (Arg.var x64, Arg.var nlits, ()))
            (fun (bx, ()) =>
          Expr.jnz (Arg.var bx)
            (Expr.call (as := [i64, i32]) (bs := [i32]) "full_cong_find"
              (Arg.var pRepr, Arg.var x, ()) (fun (frx, ()) =>
            Expr.jump J3.fst (Arg.var frx, ())))
            (Expr.jump J3.fst (Arg.var x, ())))))))))))))
        (Expr.jump Js.fst (Arg.var k2, Arg.imm false, Arg.var nszL, ())))) Blocks.nil)
    (fun J2 => Expr.jump J2.fst (Arg.imm 0, Arg.imm 0, ())))

private theorem s13_els_ar_loop2_wp {Γ : Env} {Q : Post [.bool]} {X : XPost}
    (hFind : ∀ a m Q X, fullCongFindSpec a m Q X →
      Γ "full_cong_find" [i64, i32] [i32] a m Q X)
    (hWatch : M6EnvSpec Γ "full_watch_push" Full.fullWatchPushSpec)
    (hAddUnit : M6EnvSpec Γ "full_add_unit" Full.fullAddUnitSpec)
    (hAddBin : M6EnvSpec Γ "full_add_bin" Full.fullAddBinSpec)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    {cr rl sz32 : BitVec 32} {nlits_v : Val i64} {hdr_v : Val i32}
    {has_rl : Bool} {R : Mem 64 → Prop} {m : Mem 64}
    (hinv : FullDenseInvW c F0 F_cur s)
    (hrepr : FullCongReprInv F_cur (2 * s.core.cur_vars) s.core.repr)
    (hcr_ref : cr.toNat ∈ fullArenaClauseRefs s)
    (hng_cr : fullArenaClauseGarb s cr.toNat = false)
    (hcr_bd : cr.toNat < s.core.arena.length) (hcr2_bd : cr.toNat + 2 < s.core.arena.length)
    (hnlits_v : nlits_v = BitVec.ofNat 64 s.core.cur_vars <<< 1#64)
    (hhdr_v : hdr_v = s.core.arena[cr.toNat]'hcr_bd)
    (hsz_def : sz32.toNat = fullArenaClauseSize s cr.toNat)
    (hsz3 : 3 ≤ sz32.toNat)
    (hsz_ar_bd : cr.toNat + 3 + sz32.toNat ≤ s.core.arena.length)
    (hsz_lt_dim : sz32.toNat < 2 ^ 31)
    (hcr_lt_dim : cr.toNat < 0x80000000) (hcr_ne : cr ≠ 0xFFFFFFFF#32)
    (hlits_lt : ∀ i (hi : i < sz32.toNat),
      (s.core.arena[cr.toNat + 3 + i]'(Nat.lt_of_lt_of_le
        (Nat.add_lt_add_left hi _) hsz_ar_bd)).toNat < 2 * s.core.cur_vars)
    (hent_cr : (cnfOfClauses F_cur).EntailsClause (cnfClause (fullArenaClauseLits s cr.toNat)))
    (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ (ok : Bool) (s' : FullState) (m' : Mem 64),
      FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.fuel = s.core.fuel → FullCongReprInv F_cur (2 * s.core.cur_vars) s'.core.repr →
      s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
      s'.scratch.tarjan_reach = s.scratch.tarjan_reach →
      s'.scratch.scratch_buf = s.scratch.scratch_buf →
      s'.scratch.work_stk1 = s.scratch.work_stk1 →
      s'.scratch.work_stk2 = s.scratch.work_stk2 →
      s'.scratch.glue_used = s.scratch.glue_used →
      (ok = false → F0.Unsat ∧ s'.core.inconsistent ≠ 0#64) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m') :
    wp Γ Q X
      (s13ElsArLoop2Expr c.hdr cr rl c.pArena c.pRepr c.pLitMark c.pTmp
        nlits_v hdr_v sz32 has_rl) m := by
  subst hnlits_v; subst hhdr_v
  unfold s13ElsArLoop2Expr
  have hcl := hinv.1.core_ok; have hmx := c.hmaxv; have har := c.harena
  unfold dimacsBound at hmx har
  have hcv_le := hcl.cur_vars_le; have hrp_len := hcl.repr_len
  have hcv_lt64 : s.core.cur_vars < 2 ^ 64 := by omega
  have hcv2_lt64 : 2 * s.core.cur_vars < 2 ^ 64 := by omega
  have hnl_eq : (BitVec.ofNat 64 s.core.cur_vars <<< 1#64).toNat = 2 * s.core.cur_vars := by
    simp only [bv_c0]
    rw [Nat.mod_eq_of_lt hcv_lt64, Nat.mod_eq_of_lt hcv2_lt64]
  have hsz_c : fullArenaClauseSizeCore s.core cr.toNat = sz32.toNat := hsz_def.symm
  have hmaxv_pos : 0 < c.max_vars := by
    have := hlits_lt 0 (by omega); omega
  refine wp_join_state (ts := [i32, .bool, i32])
    (proj := fun p : BitVec 32 × Bool × BitVec 32 => (p.1, p.2.1, p.2.2, ()))
    (fun (_k2, taut2, nsz2) m2 => ∃ (repr2 : List (BitVec 32)) (lm2 : List (BitVec 8))
        (tmp2 : List (BitVec 32)),
      repr2.length = 2 * c.max_vars ∧ FullCongReprInv F_cur (2 * s.core.cur_vars) repr2 ∧
      nsz2.toNat ≤ sz32.toNat ∧ S13ElsLitMap c s lm2 tmp2 nsz2.toNat ∧
      (taut2 = false → ∀ i < sz32.toNat,
        ∃ j < nsz2.toNat, LitEquiv (cnfOfClauses F_cur)
          (s.core.arena[cr.toNat + 3 + i]?.getD 0#32).toNat (tmp2[j]?.getD 0#32).toNat) ∧
      (FullMem c { s with core := { s.core with repr := repr2, lit_mark := lm2, tmp := tmp2 } }
        ⋆ R) m2) ?_ ?_
  · rintro _ ⟨_k2, taut2, nsz2⟩ m2 ⟨repr2, lm2, tmp2, hrp2, hrep2, hnsz_sz, hmap2, hcov2, hm2⟩
    c0_hsteps_nogrp
    refine wp_while_state (ts := [i32]) (proj := fun k : BitVec 32 => (k, ()))
      (μ := fun k => nsz2.toNat - k.toNat)
      (Inv := fun k ml => k.toNat ≤ nsz2.toNat ∧ ∃ lmL : List (BitVec 8),
        lmL.length = 2 * c.max_vars ∧
        (∀ l < 2 * c.max_vars, lmL[l]?.getD 0#8 ≠ 0#8 →
          ∃ j, k.toNat ≤ j ∧ j < nsz2.toNat ∧ (tmp2[j]?.getD 0#32).toNat = l) ∧
        (FullMem c { s with core := { s.core with repr := repr2, lit_mark := lmL, tmp := tmp2 } }
          ⋆ R) ml) ?_ ?_
    · intro J3 hJ3; c0_hsteps!
      exact hJ3 0#32 m2 ⟨Nat.zero_le _, lm2, hmap2.lm_len, fun l hl hnz => by
        rw [hmap2.map l hl] at hnz
        by_cases hex : ∃ j < nsz2.toNat, (tmp2[j]?.getD 0#32).toNat = l
        · exact ⟨hex.choose, Nat.zero_le _, hex.choose_spec.1, hex.choose_spec.2⟩
        · rw [decide_eq_false hex] at hnz; exact absurd rfl hnz, hm2⟩
    · rintro J3 k3 ml ⟨hk3, lm3, hlm3, hmap3, hml⟩ ih3
      c0_hsplit
      · have hk_lt : k3.toNat < nsz2.toNat := ‹_›
        have hk1 : (k3 + 1#32).toNat = k3.toNat + 1 := by bv_omega
        have hnsz_le := hmap2.nsz_le
        have htk_lt : (tmp2[k3.toNat]'(by have := hmap2.tmp_len; omega)).toNat <
            2 * s.core.cur_vars := by
          have := hmap2.tmp_lt k3.toNat hk_lt
          rwa [List.getElem?_eq_getElem (by have := hmap2.tmp_len; omega),
            Option.getD_some] at this
        have htk_lm : (tmp2[k3.toNat]'(by have := hmap2.tmp_len; omega)).toNat < lm3.length := by
          rw [hlm3]; omega
        have htk_bd64 : (BitVec.setWidth 64 k3).toNat < tmp2.length := by
          rw [bv_c0_zext32_64]; have htl := hmap2.tmp_len; omega
        have htk_lm64 : (BitVec.setWidth 64
            (tmp2[(BitVec.setWidth 64 k3).toNat]'htk_bd64)).toNat < lm3.length := by
          rw [bv_c0_zext32_64, m6_getElem_congr (bv_c0_zext32_64 k3) htk_bd64
            (by have htl := hmap2.tmp_len; omega)]
          exact htk_lm
        c0_hsteps_nogrp
        have hidx_tk : (BitVec.setWidth 64
            (tmp2[(BitVec.setWidth 64 k3).toNat]'htk_bd64)).toNat =
            (tmp2[k3.toNat]'(by have htl := hmap2.tmp_len; omega)).toNat := by
          rw [bv_c0_zext32_64, m6_getElem_congr (bv_c0_zext32_64 k3) htk_bd64
            (by have htl := hmap2.tmp_len; omega)]
        have hm3_nxt : (FullMem c
            { s with core := { s.core with
                repr := repr2,
                lit_mark :=
                  lm3.set (tmp2[k3.toNat]'(by have htl := hmap2.tmp_len; omega)).toNat 0#8,
                tmp := tmp2 } } ⋆ R) m := by
          rw [← hidx_tk]; exact hm
        have hcv2 := hmap2.cv_le
        exact ih3 (k3 + 1#32) _ (by rw [hk1]; omega) ⟨by omega,
          lm3.set (tmp2[k3.toNat]'(by have := hmap2.tmp_len; omega)).toNat 0#8,
          by simp [hlm3],
          by
            rw [hk1]
            exact s13_els_loop3_step hk_lt (mcv2 := 2 * c.max_vars)
              (by rw [hmap2.tmp_len]; omega) (by omega) hmap3,
          hm3_nxt⟩
      · have hk_eq : k3.toNat = nsz2.toNat := by
          have hle : ¬ k3.toNat < nsz2.toNat := ‹_›; omega
        let sC : FullState :=
          { s with core := { s.core with repr := repr2, lit_mark := lm3, tmp := tmp2 } }
        have hlm_zero : ∀ l < 2 * c.max_vars, lm3[l]?.getD 0#8 = 0#8 := fun l hl => by
          apply Classical.byContradiction; intro hnz
          obtain ⟨j, hkj, hj, _⟩ := hmap3 l hl hnz
          omega
        have hinvC0 := s13_denseInvW_set_lm_clear hinv hlm3 hmap2.tmp_len hlm_zero
        have hinvC : FullDenseInvW c F0 F_cur sC :=
          ⟨⟨{ hinvC0.1.core_ok with repr_len := by simp [sC, hrp2] }, hinvC0.1.scratch_ok⟩,
           { hinvC0.2.1 with
               arena := { hinvC0.2.1.arena with len_ok := hinvC0.2.1.arena.len_ok },
               watches := hinvC0.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) },
           hinvC0.2.2.1, hinvC0.2.2.2.1, hinvC0.2.2.2.2.1, hinvC0.2.2.2.2.2.1,
           hinvC0.2.2.2.2.2.2⟩
        have hoC : S13ElsArOut c F0 F_cur s sC :=
          ⟨hinvC, rfl, rfl, hrep2, rfl, rfl, rfl, rfl, rfl, rfl⟩
        have hhent : taut2 = false →
            (cnfOfClauses F_cur).EntailsClause
              (cnfClause ((tmp2.take nsz2.toNat).map BitVec.toNat)) := by
          intro htf
          refine s13_entails_clause_subst (cs := fullArenaClauseLits s cr.toNat) ?_ hent_cr
          intro lit hl
          unfold fullArenaClauseLits at hl
          rw [mem_fullArenaClauseLitsCore_iff (by rw [hsz_c]; exact hsz_ar_bd)] at hl
          obtain ⟨i, hi, hig⟩ := hl
          have hi' : i < sz32.toNat := by rwa [hsz_c] at hi
          obtain ⟨j, hj, heqv⟩ := hcov2 htf i hi'
          have htmp2_l := hmap2.tmp_len; have hnsz2_l := hmap2.nsz_le
          refine ⟨(tmp2[j]?.getD 0#32).toNat, ?_, ?_⟩
          · rw [List.mem_map]
            refine ⟨tmp2[j]'(by omega), ?_, ?_⟩
            · rw [List.mem_iff_getElem]
              exact ⟨j, by simp only [List.length_take]; omega, by rw [List.getElem_take]⟩
            · rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
          · rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at heqv
            rw [← hig]; exact heqv
        dsimp only
        exact s13_els_ar_post_l3_wp hWatch hAddUnit hAddBin hinvC hoC rfl rfl hcr_ref hcr_ref
          hng_cr hcr_bd hcr2_bd hsz_def hsz_ar_bd hsz_lt_dim hcr_lt_dim hcr_ne hnsz_sz hmap2 hhent
          hml hQ
  · intro J2 hJ2
    refine wp_while_state (ts := [i32, i32])
      (proj := fun p : BitVec 32 × BitVec 32 => (p.1, p.2, ()))
      (μ := fun p => sz32.toNat - p.1.toNat)
      (Inv := fun p ml => p.1.toNat ≤ sz32.toNat ∧ p.2.toNat ≤ p.1.toNat ∧
        ∃ (reprL : List (BitVec 32)) (lmL : List (BitVec 8)) (tmpL : List (BitVec 32)),
          reprL.length = 2 * c.max_vars ∧ FullCongReprInv F_cur (2 * s.core.cur_vars) reprL ∧
          S13ElsLitMap c s lmL tmpL p.2.toNat ∧
          (∀ i < p.1.toNat, ∃ j < p.2.toNat, LitEquiv (cnfOfClauses F_cur)
            (s.core.arena[cr.toNat + 3 + i]?.getD 0#32).toNat (tmpL[j]?.getD 0#32).toNat) ∧
          (FullMem c
            { s with core :=
              { s.core with repr := reprL, lit_mark := lmL, tmp := tmpL } } ⋆ R) ml) ?_ ?_
    · intro L2 hL2; c0_hsteps!
      exact hL2 (0#32, 0#32) m ⟨Nat.zero_le _, Nat.zero_le _, s.core.repr, s.core.lit_mark,
        s.core.tmp, hrp_len, hrepr, s13_elsLitMap_init hinv, (fun _ hi => by cases hi), hm⟩
    · rintro L2 ⟨kL, nszL⟩ ml ⟨hk_le, hnk, reprL, lmL, tmpL, hrpL, hrepL, hmapL, hcovL, hml⟩ ih2
      dsimp only at *
      c0_hsplit
      · have hk_lt : kL.toNat < sz32.toNat := ‹_›
        have hk1 : (kL + 1#32).toNat = kL.toNat + 1 := by bv_omega
        have hnszL := hmapL.nsz_le; have hlmL := hmapL.lm_len; have htmpL := hmapL.tmp_len
        have hidx_k_c0 : (BitVec.setWidth 64 cr + (3 : BitVec 64) +
            BitVec.setWidth 64 kL).toNat = cr.toNat + 3 + kL.toNat := by
          simp only [bv_c0, bv_c0_zext32_64, show ((3 : BitVec 64)).toNat = 3 from rfl]
          exact Nat.mod_eq_of_lt (by omega)
        have hidx_ar : (BitVec.setWidth 64 cr + (3 : BitVec 64) +
            BitVec.setWidth 64 kL).toNat < s.core.arena.length := by rw [hidx_k_c0]; omega
        have hx_lt : (s.core.arena[(BitVec.setWidth 64 cr + (3 : BitVec 64) +
            BitVec.setWidth 64 kL).toNat]'hidx_ar).toNat < 2 * s.core.cur_vars := by
          rw [m6_getElem_congr hidx_k_c0 hidx_ar (by omega)]; exact hlits_lt kL.toNat hk_lt
        let x0 := s.core.arena[(BitVec.setWidth 64 cr + (3 : BitVec 64) +
          BitVec.setWidth 64 kL).toNat]'hidx_ar
        have hx0_eq : x0.toNat = (s.core.arena[cr.toNat + 3 + kL.toNat]'(by omega)).toNat :=
          congrArg BitVec.toNat (m6_getElem_congr hidx_k_c0 hidx_ar (by omega))
        c0_hsteps_nogrp
        refine wp_join_state (ts := [i32]) (proj := fun rx : BitVec 32 => (rx, ()))
          (fun rx ml' => ∃ repr', repr'.length = 2 * c.max_vars ∧
            FullCongReprInv F_cur (2 * s.core.cur_vars) repr' ∧ rx.toNat < 2 * s.core.cur_vars ∧
            LitEquiv (cnfOfClauses F_cur) x0.toNat rx.toNat ∧
            (FullMem c
              { s with core :=
                { s.core with repr := repr', lit_mark := lmL, tmp := tmpL } } ⋆ R) ml') ?_ ?_
        · rintro _ rx ml1 ⟨repr1, hrp1, hrep1, hrx_lt, heqv_rx, hm1⟩
          have hrx_xor : (rx ^^^ 1#32).toNat < 2 * s.core.cur_vars := by
            rw [m6_els_bv32_xor1_toNat]
            rcases nat_xor1_cases rx.toNat with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
          c0_hsteps_nogrp
          refine wp_join_state (ts := [.bool, i32])
            (proj := fun p : Bool × BitVec 32 => (p.1, p.2, ()))
            (fun (_tb, nsz') ml' => nsz'.toNat ≤ kL.toNat + 1 ∧ ∃ lm' tmp',
              S13ElsLitMap c s lm' tmp' nsz'.toNat ∧
              (∀ i < kL.toNat + 1, ∃ j < nsz'.toNat, LitEquiv (cnfOfClauses F_cur)
                (s.core.arena[cr.toNat + 3 + i]?.getD 0#32).toNat (tmp'[j]?.getD 0#32).toNat) ∧
              let s_nxt : FullState :=
                { s with core := { s.core with repr := repr1, lit_mark := lm', tmp := tmp' } }
              (FullMem c s_nxt ⋆ R) ml') ?_ ?_
          · rintro _ ⟨_tb, nsz'⟩ ml' ⟨hnk', lm', tmp', hmap', hcov', hm'⟩
            c0_hsteps!
            exact @ih2 (kL + 1#32, nsz') ml' (by dsimp only; rw [hk1]; omega)
              ⟨by dsimp only; rw [hk1]; omega, by dsimp only; rw [hk1]; exact hnk',
               repr1, lm', tmp', hrp1, hrep1, hmap', (by simpa only [hk1] using hcov'), hm'⟩
          · intro J4 hJ4
            c0_hsplit; rotate_left
            · exfalso; simp only [bv_c0] at *; omega
            c0_hsplit
            · c0_hsteps!
              exact hJ2 (kL, true, nszL) ml1 ⟨repr1, lmL, tmpL, hrp1, hrep1, Nat.le_trans hnk hk_le,
                hmapL, (fun h => Bool.noConfusion h), hm1⟩
            · have h1_zero : lmL[(rx ^^^ 1#32).toNat]?.getD 0#8 = 0#8 := by
                have hlm_bd1 : rx.toNat ^^^ 1 < lmL.length := by
                  rw [← m6_els_bv32_xor1_toNat, hlmL]; omega
                rw [← m6_els_bv32_xor1_toNat] at hlm_bd1
                rw [List.getElem?_eq_getElem hlm_bd1, Option.getD_some]
                have h_se : BitVec.setWidth 32
                    (lmL[rx.toNat ^^^ 1]'(by rwa [← m6_els_bv32_xor1_toNat])) = 0#32 := by
                  simpa only [m6_els_bv32_xor1_toNat] using ‹_›
                have h_eq : lmL[(rx ^^^ 1#32).toNat]'hlm_bd1 =
                    lmL[rx.toNat ^^^ 1]'(by rwa [← m6_els_bv32_xor1_toNat]) :=
                  m6_getElem_congr (m6_els_bv32_xor1_toNat rx) hlm_bd1 _
                rw [h_eq]; exact (s13_bv8_zext32_eq0_iff _).mp h_se
              refine wp_join_state (ts := [i32]) (proj := fun n : BitVec 32 => (n, ()))
                (fun nsz' ml' => nsz'.toNat ≤ kL.toNat + 1 ∧ ∃ lm' tmp',
                  S13ElsLitMap c s lm' tmp' nsz'.toNat ∧
                  (∀ i < kL.toNat + 1, ∃ j < nsz'.toNat, LitEquiv (cnfOfClauses F_cur)
                    (s.core.arena[cr.toNat + 3 + i]?.getD 0#32).toNat
                    (tmp'[j]?.getD 0#32).toNat) ∧
                  let s_nxt2 : FullState :=
                    { s with core := { s.core with repr := repr1, lit_mark := lm', tmp := tmp' } }
                  (FullMem c s_nxt2 ⋆ R) ml') ?_ ?_
              · rintro _ nsz' ml' hst; c0_hsteps!; exact hJ4 (false, nsz') ml' hst
              · intro J5 hJ5; c0_hsplit
                · have h0_zero : lmL[rx.toNat]?.getD 0#8 = 0#8 := by
                    rw [List.getElem?_eq_getElem (by rw [hlmL]; omega), Option.getD_some]
                    exact (s13_bv8_zext32_eq0_iff _).mp ‹_›
                  obtain ⟨hnsz_mx, hmap'⟩ := s13_elsLitMap_push hmapL hrx_lt h0_zero h1_zero
                  have hnsz_lt_tl : (BitVec.setWidth 64 nszL).toNat < tmpL.length := by
                    rw [htmpL, bv_c0_zext32_64]; omega
                  c0_hsplit; rotate_left
                  · exfalso; rw [bv_c0_zext32_64] at *; omega
                  have hnsz1 : (nszL + 1#32).toNat = nszL.toNat + 1 := by bv_omega
                  c0_hsteps!
                  refine hJ5 (nszL + 1#32) _ ⟨by rw [hnsz1]; omega, _, _,
                    by rw [hnsz1]; exact hmap', fun i hi => ?_, by assumption⟩
                  by_cases hik : i = kL.toNat
                  · subst hik; refine ⟨nszL.toNat, by rw [hnsz1]; omega, ?_⟩
                    rw [List.getElem?_set_self (by rw [htmpL]; omega), Option.getD_some,
                      List.getElem?_eq_getElem (by omega : cr.toNat + 3 + kL.toNat <
                        s.core.arena.length), Option.getD_some, ← hx0_eq]
                    exact heqv_rx
                  · obtain ⟨j, hj, hje⟩ := hcovL i (by omega)
                    refine ⟨j, by rw [hnsz1]; omega, ?_⟩
                    rw [List.getElem?_set_ne (by omega)]; exact hje
                · have h0_nz : lmL[rx.toNat]?.getD 0#8 ≠ 0#8 := by
                    rw [List.getElem?_eq_getElem (by rw [hlmL]; omega), Option.getD_some]
                    intro h; rw [h] at hc; exact hc rfl
                  have hrx_cov : ∃ j < nszL.toNat, (tmpL[j]?.getD 0#32).toNat = rx.toNat := by
                    have hml' := hmapL.map rx.toNat (by omega)
                    by_cases hex : ∃ j < nszL.toNat, (tmpL[j]?.getD 0#32).toNat = rx.toNat
                    · exact hex
                    · exfalso; rw [decide_eq_false hex] at hml'; exact h0_nz hml'
                  c0_hsteps!
                  refine hJ5 nszL ml1 ⟨by omega, lmL, tmpL, hmapL, fun i hi => ?_, hm1⟩
                  by_cases hik : i = kL.toNat
                  · subst hik; obtain ⟨j, hj, hjr⟩ := hrx_cov
                    refine ⟨j, hj, ?_⟩
                    rw [List.getElem?_eq_getElem (by omega), Option.getD_some, hjr, ← hx0_eq]
                    exact heqv_rx
                  · exact hcovL i (by omega)
        · intro J3 hJ3; c0_hsplit
          · let s_find : FullState :=
              { s with core := { s.core with repr := reprL, lit_mark := lmL, tmp := tmpL } }
            refine s13_els_ar_call_find hFind (F_cur := F_cur) (s := s_find)
              hrepL hx_lt hml fun rx repr' m' hlen' hrep' hrx_lt heqv' hm' => ?_
            c0_hsteps!
            exact hJ3 rx m' ⟨repr', hlen'.trans hrpL, hrep', hrx_lt, heqv', hm'⟩
          · exfalso; simp only [bv_c0] at *; omega
      · have hk_eq : kL.toNat = sz32.toNat := by
          have hle : ¬ kL.toNat < sz32.toNat := ‹_›; omega
        c0_hsteps!
        refine hJ2 (kL, false, nszL) ml ⟨reprL, lmL, tmpL, hrpL, hrepL, by dsimp only; omega, hmapL,
          fun _ i hi => hcovL i (by omega), hml⟩

/-- Step-13 `full_m6_els_ar` (`FullCongReprInv`, `full_cong_find`, `has_rl` guard). -/
theorem full_m6_els_ar_s13_wp (Γ : Env)
    (hFind : ∀ a m Q X, fullCongFindSpec a m Q X →
      Γ "full_cong_find" [i64, i32] [i32] a m Q X)
    (hWatch : M6EnvSpec Γ "full_watch_push" Full.fullWatchPushSpec)
    (hAddUnit : M6EnvSpec Γ "full_add_unit" Full.fullAddUnitSpec)
    (hAddBin : M6EnvSpec Γ "full_add_bin" Full.fullAddBinSpec) :
    ∀ args m Q X, step13ElsArSpec args m Q X →
      Func.wp Γ full_m6_els_ar_body args m Q X := by
  rintro ⟨h, cr, rl, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, s, R, rfl, hinv, hcr_ref, hrl_lt, hrepr_inv, hm, hQ⟩
  have hcl := hinv.1.core_ok; have hw := hinv.2.1
  have hmx := c.hmaxv; have har := c.harena; have hwc := c.hwcap
  unfold dimacsBound at hmx har hwc
  have hcv_le := hcl.cur_vars_le; have hal_le := hcl.arena_len_le
  have har_len := hcl.arena_len_arr; have hrp_len := hcl.repr_len
  have hwf_cr := hw.arena.refs_wf cr.toNat hcr_ref
  have hcr_bd : cr.toNat < s.core.arena.length := by
    have := hwf_cr.2.2.1; have := hwf_cr.2.2.2.1; omega
  have hcr2_bd : cr.toNat + 2 < s.core.arena.length := by
    have := hwf_cr.2.2.1; have := hwf_cr.2.2.2.1; omega
  have hcr2_mod : (cr.toNat + 2) % 2 ^ 64 = cr.toNat + 2 := Nat.mod_eq_of_lt (by omega)
  have hsz_core : fullArenaClauseSizeCore s.core cr.toNat =
      (s.core.arena[cr.toNat + 2]'hcr2_bd).toNat := by
    unfold fullArenaClauseSizeCore; rw [List.getElem?_eq_getElem hcr2_bd, Option.getD_some]
  have hsz_core_3 : 3 ≤ (s.core.arena[cr.toNat + 2]'hcr2_bd).toNat := by
    simpa [hsz_core] using hwf_cr.2.1
  have hsz_core_bd : cr.toNat + 3 + (s.core.arena[cr.toNat + 2]'hcr2_bd).toNat ≤
      s.core.arena_len := by
    have := hwf_cr.2.2.1; have := hwf_cr.2.2.2.1; omega
  have hsz32_mod : s.core.arena[(cr.toNat + 2) % 2 ^ 64]'(by
      rw [hcr2_mod]; exact hcr2_bd) = s.core.arena[cr.toNat + 2]'hcr2_bd :=
    m6_getElem_congr hcr2_mod (by rw [hcr2_mod]; exact hcr2_bd) hcr2_bd
  have hcr2_eq_c0 : (BitVec.setWidth 64 cr + (2 : BitVec 64)).toNat = cr.toNat + 2 := by bv_omega
  have hcr_eq_c0 : (BitVec.setWidth 64 cr).toNat = cr.toNat := by bv_omega
  have hsz32_c0 : s.core.arena[(BitVec.setWidth 64 cr + (2 : BitVec 64)).toNat]'(by
      rw [hcr2_eq_c0]; exact hcr2_bd) = s.core.arena[cr.toNat + 2]'hcr2_bd :=
    m6_getElem_congr hcr2_eq_c0 (by rw [hcr2_eq_c0]; exact hcr2_bd) hcr2_bd
  have hhdr_c0 : s.core.arena[(BitVec.setWidth 64 cr).toNat]'(by
      rw [hcr_eq_c0]; exact hcr_bd) = s.core.arena[cr.toNat]'hcr_bd :=
    m6_getElem_congr hcr_eq_c0 (by rw [hcr_eq_c0]; exact hcr_bd) hcr_bd
  unfold Func.wp full_m6_els_ar_body
  c0_hsplit
  · exfalso; bv_omega
  c0_hsplit
  · c0_hsteps!; exact s13_els_ar_ret_bool (s13_elsArOut_init hinv hrepr_inv) hm hQ
  c0_hsplit
  · exfalso
    have h2 : (s.core.arena[(cr.toNat + 2) % 2 ^ 64]'(by
        rw [hcr2_mod]; exact hcr2_bd)).toNat < 3 := ‹_›
    rw [congrArg BitVec.toNat hsz32_mod] at h2; omega
  c0_hsplit
  · exfalso
    have hlt : s.core.arena_len % 2 ^ 64 < (cr.toNat + 3 + (s.core.arena[(cr.toNat + 2) % 2 ^ 64]'
        (by rw [hcr2_mod]; exact hcr2_bd)).toNat) % 2 ^ 64 := ‹_›
    rw [congrArg BitVec.toNat hsz32_mod, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)] at hlt; omega
  have hng_cr : fullArenaClauseGarb s cr.toNat = false := by
    unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore
    rw [List.getElem?_eq_getElem hcr_bd, Option.getD_some]
    simpa [BitVec.toNat_and, show (0x00080000#32).toNat = 0x80000 from rfl] using
      (by assumption : (s.core.arena[cr.toNat]'hcr_bd &&& 0x00080000#32) = 0#32)
  let sz32 := s.core.arena[cr.toNat + 2]'hcr2_bd
  have hsz_c : fullArenaClauseSizeCore s.core cr.toNat = sz32.toNat := hsz_core
  have hsz_def : sz32.toNat = fullArenaClauseSize s cr.toNat := hsz_core.symm
  have hsz3 : 3 ≤ sz32.toNat := hsz_core_3
  have hsz_bd : cr.toNat + 3 + sz32.toNat ≤ s.core.arena_len := hsz_core_bd
  have hsz_ar_bd : cr.toNat + 3 + sz32.toNat ≤ s.core.arena.length := by omega
  have hsz_lt_dim : sz32.toNat < 2 ^ 31 := by omega
  have hcr_lt_dim : cr.toNat < 0x80000000 := by omega
  have hcr_ne : cr ≠ 0xFFFFFFFF#32 := fun h' => by
    rw [h'] at hcr_lt_dim; revert hcr_lt_dim; decide
  have hlits_lt_k : ∀ i (hi : i < sz32.toNat),
      (s.core.arena[cr.toNat + 3 + i]'(by omega)).toNat < 2 * s.core.cur_vars := by
    intro i hi
    have hmem : (s.core.arena[cr.toNat + 3 + i]'(by omega)).toNat ∈
        fullArenaClauseLits s cr.toNat := by
      unfold fullArenaClauseLits
      rw [mem_fullArenaClauseLitsCore_iff (by rw [hsz_c]; exact hsz_ar_bd)]
      exact ⟨i, by rw [hsz_c]; exact hi, rfl⟩
    exact hw.arena.lits_lt cr.toNat hcr_ref hng_cr _ hmem
  have hent_cr : (cnfOfClauses F_cur).EntailsClause (cnfClause (fullArenaClauseLits s cr.toNat)) :=
    hw.arena.entails cr.toNat hcr_ref hng_cr
  c0_hsteps_nogrp
  refine wp_join_state (ts := [.bool, i32])
    (proj := fun p : Bool × BitVec 32 => (p.1, p.2, ()))
    (fun (_chg, _k) m1 => ∃ s1 : FullState,
      s1 = { s with core := { s.core with repr := s1.core.repr } } ∧
      s1.core.repr.length = 2 * c.max_vars ∧ FullDenseInvW c F0 F_cur s1 ∧
      FullCongReprInv F_cur (2 * s.core.cur_vars) s1.core.repr ∧
      (FullMem c s1 ⋆ R) m1) ?_ ?_
  · rintro _ ⟨chg1, _k1⟩ m1 ⟨s1, hs1_eq, hrp1, hinv1, hrep1, hm1⟩
    have hs1_ar : s1.core.arena = s.core.arena := by rw [hs1_eq]
    have hs1_cv : s1.core.cur_vars = s.core.cur_vars := by rw [hs1_eq]
    have hs1_fl : s1.core.fuel = s.core.fuel := by rw [hs1_eq]
    have hs1_sc : s1.scratch = s.scratch := by rw [hs1_eq]
    have hs1_refs : fullArenaClauseRefs s1 = fullArenaClauseRefs s := by
      unfold fullArenaClauseRefs fullArenaClauseRefsCore
      have hs1_al : s1.core.arena_len = s.core.arena_len := by rw [hs1_eq]
      rw [hs1_ar, hs1_al]
    have hs1_ng : fullArenaClauseGarb s1 cr.toNat = false := by
      unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore; rw [hs1_ar]; exact hng_cr
    have hs1_sz : sz32.toNat = fullArenaClauseSize s1 cr.toNat := by
      unfold fullArenaClauseSize fullArenaClauseSizeCore; rw [hs1_ar]; exact hsz_def
    have hs1_ent : (cnfOfClauses F_cur).EntailsClause
        (cnfClause (fullArenaClauseLits s1 cr.toNat)) := by
      unfold fullArenaClauseLits fullArenaClauseLitsCore fullArenaClauseSizeCore
      rw [hs1_ar]; exact hent_cr
    have hs1_lits : ∀ i (hi : i < sz32.toNat),
        (s1.core.arena[cr.toNat + 3 + i]'(by
          rw [hs1_ar]; exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hi (cr.toNat + 3))
            hsz_ar_bd)).toNat < 2 * s1.core.cur_vars := fun i hi => by
      rw [hs1_cv]; simpa only [hs1_ar] using hlits_lt_k i hi
    c0_hsplit
    · c0_hsteps_nogrp
      refine wp_join_state (ts := [.bool, i32])
        (proj := fun p : Bool × BitVec 32 => (p.1, p.2, ()))
        (fun (_hrl, _hk) m_hrl => (FullMem c s1 ⋆ R) m_hrl) ?_ ?_
      · rintro _ ⟨has_rl, _hk⟩ m_hrl hm_hrl
        simp only [Blocks.get, hsz32_c0, hhdr_c0]
        have hrp1' : FullCongReprInv F_cur (2 * s1.core.cur_vars) s1.core.repr := by
          rw [hs1_cv]; exact hrep1
        refine s13_els_ar_loop2_wp (Γ := Γ) (Q := Q) (X := X) (s := s1)
          (nlits_v := BitVec.ofNat 64 s.core.cur_vars <<< 1#64)
          (hdr_v := s.core.arena[cr.toNat]'hcr_bd) hFind hWatch hAddUnit hAddBin
          hinv1 hrp1' (hs1_refs ▸ hcr_ref)
          hs1_ng (by rw [hs1_ar]; exact hcr_bd) (by rw [hs1_ar]; exact hcr2_bd)
          (by rw [hs1_cv]) (by simp only [hs1_ar])
          hs1_sz hsz3 (by rw [hs1_ar]; exact hsz_ar_bd) hsz_lt_dim hcr_lt_dim hcr_ne
          hs1_lits hs1_ent hm_hrl
          fun ok s' m' hinv' hcv' hfl' hrep' htmk' htrh' hscr' hws1' hws2' hgu' huns' hm' => ?_
        exact hQ ok s' m' hinv' (hcv'.trans hs1_cv) (hfl'.trans hs1_fl) (hs1_cv ▸ hrep')
          (htmk'.trans (by rw [hs1_sc])) (htrh'.trans (by rw [hs1_sc]))
          (hscr'.trans (by rw [hs1_sc])) (hws1'.trans (by rw [hs1_sc]))
          (hws2'.trans (by rw [hs1_sc])) (hgu'.trans (by rw [hs1_sc])) huns' hm'
      · intro Jhrl hJhrl
        refine wp_while_state (ts := [i32]) (proj := fun hk : BitVec 32 => (hk, ()))
          (μ := fun hk => sz32.toNat - hk.toNat)
          (Inv := fun hk ml => hk.toNat ≤ sz32.toNat ∧ (FullMem c s1 ⋆ R) ml) ?_ ?_
        · intro Lh hLh; c0_hsteps!; exact hLh 0#32 _ ⟨Nat.zero_le _, by assumption⟩
        · rintro Lh hk ml ⟨hkle, hml_mem⟩ ihh
          c0_hsplit
          · have hklt : hk.toNat < sz32.toNat := by
              dsimp only [sz32]; rw [← congrArg BitVec.toNat hsz32_mod]; exact hc
            have hk1 : (hk + 1#32).toNat = hk.toNat + 1 := by bv_omega
            have hidx_h : (BitVec.setWidth 64 cr + (3 : BitVec 64) +
                BitVec.setWidth 64 hk).toNat = cr.toNat + 3 + hk.toNat := by
              simp only [bv_c0, bv_c0_zext32_64, show ((3 : BitVec 64)).toNat = 3 from rfl]
              exact Nat.mod_eq_of_lt (by omega)
            have har_hk : (BitVec.setWidth 64 cr + (3 : BitVec 64) +
                BitVec.setWidth 64 hk).toNat < s1.core.arena.length := by
              rw [hs1_ar, hidx_h]; omega
            c0_hsteps_nogrp; c0_hsplit
            · c0_hsteps!; exact hJhrl (true, hk) ml hml_mem
            · c0_hsteps!; exact ihh (hk + 1#32) ml (by omega) ⟨by omega, hml_mem⟩
          · c0_hsteps!; exact hJhrl (false, hk) ml hml_mem
    · c0_hsteps_nogrp
      refine wp_join_group (ts := []) (fun () mRet => ∃ sR : FullState,
          S13ElsArOut c F0 F_cur s sR ∧ (FullMem c sR ⋆ R) mRet) ?_ ?_
      · rintro _ ⟨⟩ mRet ⟨sR, hoR, hmR⟩; c0_hsteps!; exact s13_els_ar_ret_bool hoR hmR hQ
      · intro JW hJW
        have hcr2_c0 : (BitVec.setWidth 64 cr + 2).toNat = cr.toNat + 2 := by
          simp only [bv_c0, bv_c0_zext32_64, show (2 : BitVec 64).toNat = 2 from rfl]
          exact Nat.mod_eq_of_lt (by omega)
        refine s13_els_ar_push_watched hWatch rfl rfl (by
            dsimp only [Arg.val]; rw [m6_getElem_congr hcr2_c0 _ hcr2_bd]; rfl)
          rfl rfl hinv1 hs1_cv hs1_fl hrep1 (by rw [hs1_sc]) (by rw [hs1_sc]) (by rw [hs1_sc])
          (by rw [hs1_sc]) (by rw [hs1_sc]) (by rw [hs1_sc]) hsz3 hsz_lt_dim hcr_lt_dim hcr_ne
          (hs1_refs ▸ hcr_ref) hm1 fun ok s' m' ho' hm' => ?_
        c0_hsplit
        · c0_hsteps!; exact hJW () m' ⟨s', ho', hm'⟩
        · c0_hsteps!
          exact hJW () _ ⟨{ s' with core := { s'.core with oom := 1#64 } },
            ⟨s13_denseInvW_set_oom ho'.dinv, ho'.cv, ho'.fuel, ho'.repr, ho'.tmk, ho'.trh,
             ho'.scr, ho'.ws1, ho'.ws2, ho'.gu⟩, by assumption⟩
  · intro J1 hJ1
    refine wp_while_state (ts := [i32]) (proj := fun k : BitVec 32 => (k, ()))
      (μ := fun k => sz32.toNat - k.toNat)
      (Inv := fun k ml => k.toNat ≤ sz32.toNat ∧ ∃ sL : FullState,
        sL = { s with core := { s.core with repr := sL.core.repr } } ∧
        sL.core.repr.length = 2 * c.max_vars ∧ FullDenseInvW c F0 F_cur sL ∧
        FullCongReprInv F_cur (2 * s.core.cur_vars) sL.core.repr ∧ (FullMem c sL ⋆ R) ml) ?_ ?_
    · intro L1 hL1; c0_hsteps!
      exact hL1 0#32 m ⟨Nat.zero_le _, s, rfl, hrp_len, hinv, hrepr_inv, hm⟩
    · rintro L1 kL ml ⟨hk_le, sL, hsL_eq, hrpL, hinvL, hrepL, hmL⟩ ih1
      have hsL_ar : sL.core.arena = s.core.arena := by rw [hsL_eq]
      c0_hsplit
      · have hk_lt : kL.toNat < sz32.toNat := by
          dsimp only [sz32]; rw [← congrArg BitVec.toNat hsz32_mod]; exact hc
        have hk1 : (kL + 1#32).toNat = kL.toNat + 1 := by bv_omega
        have hidx_k_c0 : (BitVec.setWidth 64 cr + (3 : BitVec 64) +
            BitVec.setWidth 64 kL).toNat = cr.toNat + 3 + kL.toNat := by
          simp only [bv_c0, bv_c0_zext32_64, show ((3 : BitVec 64)).toNat = 3 from rfl]
          exact Nat.mod_eq_of_lt (by omega)
        have har_k : (BitVec.setWidth 64 cr + (3 : BitVec 64) +
            BitVec.setWidth 64 kL).toNat < sL.core.arena.length := by
          rw [hsL_ar, hidx_k_c0]; omega
        have hl_lt : (sL.core.arena[(BitVec.setWidth 64 cr + (3 : BitVec 64) +
            BitVec.setWidth 64 kL).toNat]'har_k).toNat < 2 * sL.core.cur_vars := by
          have har_k_s : (BitVec.setWidth 64 cr + (3 : BitVec 64) +
              BitVec.setWidth 64 kL).toNat < s.core.arena.length := by rw [← hsL_ar]; exact har_k
          have har_k2_s : cr.toNat + 3 + kL.toNat < s.core.arena.length := by omega
          simp only [hsL_ar]
          rw [m6_getElem_congr hidx_k_c0 har_k_s har_k2_s]
          rw [show sL.core.cur_vars = s.core.cur_vars from by rw [hsL_eq]]
          exact hlits_lt_k kL.toNat hk_lt
        c0_hsteps_nogrp
        refine wp_join_group (ts := []) (fun () ml' => ∃ sL' : FullState,
          sL' = { s with core := { s.core with repr := sL'.core.repr } } ∧
          sL'.core.repr.length = 2 * c.max_vars ∧ FullDenseInvW c F0 F_cur sL' ∧
          FullCongReprInv F_cur (2 * s.core.cur_vars) sL'.core.repr ∧ (FullMem c sL' ⋆ R) ml') ?_ ?_
        · rintro _ ⟨⟩ ml' ⟨sL', hsL', hrpL', hinvL', hrepL', hmL'⟩
          c0_hsteps!
          exact ih1 (kL + 1#32) ml' (by omega)
            ⟨by omega, sL', hsL', hrpL', hinvL', hrepL', hmL'⟩
        · intro J2 hJ2; c0_hsplit
          · have hrepL_cv : FullCongReprInv F_cur (2 * sL.core.cur_vars) sL.core.repr := by
              rw [show sL.core.cur_vars = s.core.cur_vars from by rw [hsL_eq]]; exact hrepL
            refine s13_els_ar_call_find hFind hrepL_cv hl_lt hmL
              fun fr repr' m' hlen' hrep' _ _ hm' => ?_
            let sN : FullState := { sL with core := { sL.core with repr := repr' } }
            have hsN_eq : sN = { s with core := { s.core with repr := sN.core.repr } } := by
              dsimp only [sN]; rw [hsL_eq]
            have hrpN : sN.core.repr.length = 2 * c.max_vars := hlen'.trans hrpL
            have hinvN : FullDenseInvW c F0 F_cur sN :=
              ⟨⟨{ hinvL.1.core_ok with repr_len := by simp [sN, hrpN] }, hinvL.1.scratch_ok⟩,
               { hinvL.2.1 with
                   arena := { hinvL.2.1.arena with len_ok := hinvL.2.1.arena.len_ok },
                   watches := hinvL.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) },
               hinvL.2.2.1, hinvL.2.2.2.1, hinvL.2.2.2.2.1, hinvL.2.2.2.2.2.1, hinvL.2.2.2.2.2.2⟩
            have hrepN : FullCongReprInv F_cur (2 * s.core.cur_vars) sN.core.repr := by
              simpa [sN, show sL.core.cur_vars = s.core.cur_vars from by rw [hsL_eq]] using hrep'
            c0_hsplit
            · c0_hsteps!; exact hJ1 (true, kL) m' ⟨sN, hsN_eq, hrpN, hinvN, hrepN, hm'⟩
            · c0_hsteps!; exact hJ2 () m' ⟨sN, hsN_eq, hrpN, hinvN, hrepN, hm'⟩
          · exfalso
            have hcvL_eq : sL.core.cur_vars = s.core.cur_vars := by rw [hsL_eq]
            have hcv2_lt64 : 2 * s.core.cur_vars < 2 ^ 64 := by omega
            simp only [bv_c0, bv_c0_zext32_64] at *; omega
      · c0_hsteps!; exact hJ1 (false, kL) ml ⟨sL, hsL_eq, hrpL, hinvL, hrepL, hmL⟩

end LeanQbe.T.Examples.Kissat.FullFidelityStep13S1
