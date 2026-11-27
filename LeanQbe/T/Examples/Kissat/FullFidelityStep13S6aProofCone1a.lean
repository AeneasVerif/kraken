/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S6aProofCone0
public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S6aProofCone1b

import LeanQbe.T.Examples.Kissat.FullFidelitySweepProofCone0
import LeanQbe.T.Examples.Kissat.FullM8SweepV2ConeProof
import LeanQbe.T.Examples.Kissat.FullM6SweepProofConeLemmas
import LeanQbe.T.Logic.ControlComb
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ProofKit

/-!
# Kissat Fidelity Step 13 Shard `S6a` — `fid11_sweep_cone` Binary Helpers (`Cone1a`)

Split out from `Cone1` to keep all `Cone*` modules well under `1,500` LOC:
1. `binAddExpr` (`@[expose]` verbatim AST slice matching `fid11_sweep_cone`) and
   `step13_cone_bin_add_wp`.
2. `binUnitCallExpr` and `step13_cone_bin_unit_call_wp`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep13S6a

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullArenaTactics
open LeanQbe.T.Examples.Kissat.FullM4Sweep
open LeanQbe.T.Examples.Kissat.FullM6Sweep
open LeanQbe.T.Examples.Kissat.FullM6Sweep.M6SweepTactics
open LeanQbe.T.Examples.Kissat.FullM6Sweep.K6MemATactics
open LeanQbe.T.Examples.Kissat.FullFidelitySweep

@[expose] public section

def binAddExpr (J25 J26 : Cont [i32, i32, .bool, i64])
    (pHdr pWs1 pTmk pTmp pKptr : Val i64) (mv vlim nv_w nc_w : Val i32)
    (done_w : Val .bool) (p_next : Val i64) (pol qi0 ot ov layer_start : Val i32) :
    Expr Val Cont [i64] :=
  .group (sig := [[]]) (fun J32 => .cons
    (fun _ =>
      .group (sig := [[i32, Ty.bool]]) (fun J33 => .cons
        (fun p142 =>
          .let_ (Op.mk (OpCode.sext 32 64) ((.imm 0), ())) fun v143 =>
          .let_ (Op.mk (OpCode.mul i64) ((.var v143.1), (.imm 4), ())) fun v144 =>
          .let_ (Op.mk (OpCode.add i64) ((.var pTmp), (.var v144.1), ())) fun v145 =>
          .let_ (Op.mk (OpCode.shl i32) ((.var qi0), (.imm 1), ())) fun v146 =>
          .let_ (Op.mk (OpCode.or i32) ((.var v146.1), (.var pol), ())) fun v147 =>
          .store (t := i32) (.var v147.1) (.var v145.1) <|
          .let_ (Op.mk (OpCode.sext 32 64) ((.imm 1), ())) fun v148 =>
          .let_ (Op.mk (OpCode.mul i64) ((.var v148.1), (.imm 4), ())) fun v149 =>
          .let_ (Op.mk (OpCode.add i64) ((.var pTmp), (.var v149.1), ())) fun v150 =>
          .let_ (Op.mk (OpCode.zext 32 64) ((.var ov), ())) fun v151 =>
          .let_ (Op.mk (OpCode.mul i64) ((.var v151.1), (.imm 4), ())) fun v152 =>
          .let_ (Op.mk (OpCode.add i64) ((.var pTmk), (.var v152.1), ())) fun v153 =>
          .load i32 (.var v153.1) fun ld154 =>
          .let_ (Op.mk (OpCode.sub i32) ((.var ld154), (.imm 1), ())) fun v155 =>
          .let_ (Op.mk (OpCode.shl i32) ((.var v155.1), (.imm 1), ())) fun v156 =>
          .let_ (Op.mk (OpCode.and i32) ((.var ot), (.imm 1), ())) fun v157 =>
          .let_ (Op.mk (OpCode.or i32) ((.var v156.1), (.var v157.1), ())) fun v158 =>
          .store (t := i32) (.var v158.1) (.var v150.1) <|
          .group (sig := [[i32, i32, Ty.bool]]) (fun J34 => .cons
            (fun p160 =>
              .jump J26 ((.var p160.1), (.var p160.2.1), (.var p160.2.2.1), (.var p_next), ())
            )
            .nil) (fun J34 =>
            .call (as := [i64, i64, i32]) (bs := [.bool]) "full_k6_add_clause"
                ((.var pHdr), (.var pTmp), (.imm 2), ()) fun c160 =>
            .jnz (.var c160.1) (
              .let_ (Op.mk (OpCode.add i32) ((.var nc_w), (.imm 1), ())) fun v161 =>
              .group (sig := [[Ty.bool]]) (fun J36 => .cons (fun p162 =>
                  .jump J34.1 ((.var p142.1), (.var v161.1), (.var p162.1), ())
                ) .nil) (fun J36 =>
                .let_ (Op.mk (OpCode.zext 32 64) ((.imm 6), ())) fun v162 =>
                .let_ (Op.mk (OpCode.mul i64) ((.var v162.1), (.imm 4), ())) fun v163 =>
                .let_ (Op.mk (OpCode.add i64) ((.var pKptr), (.var v163.1), ())) fun v164 =>
                .load i32 (.var v164.1) fun ld165 =>
                .let_ (Op.mk (.cmp CmpOp.ne i32) ((.var ld165), (.imm 0), ())) fun v166 =>
                .jnz (.var v166.1) (
                  .jump J36.1 ((.imm true), ())
                ) (
                  .let_ (Op.mk (.cmp CmpOp.uge i32) ((.var p142.1), (.var vlim), ())) fun v167 =>
                  .jnz (.var v167.1) (
                    .jump J36.1 ((.imm true), ())
                  ) (
                    .jump J36.1 ((.var p142.2.1), ())
                  )
                )
              )
            ) (
              .group (sig := [[i32]]) (fun J35 => .cons
                (fun p162 =>
                  .let_ (Op.mk (.cmp CmpOp.ugt i32) ((.var p162.1), (.var nv_w), ())) fun v163 =>
                  .jnz (.var v163.1) (
                    .let_ (Op.mk (OpCode.sub i32) ((.var p162.1), (.imm 1), ())) fun v164 =>
                    .let_ (Op.mk (OpCode.zext 32 64) ((.var v164.1), ())) fun v165 =>
                    .let_ (Op.mk (OpCode.mul i64) ((.var v165.1), (.imm 4), ())) fun v166 =>
                    .let_ (Op.mk (OpCode.add i64) ((.var pWs1), (.var v166.1), ())) fun v167 =>
                    .load i32 (.var v167.1) fun ld168 =>
                    .let_ (Op.mk (OpCode.zext 32 64) ((.var ld168), ())) fun v169 =>
                    .let_ (Op.mk (OpCode.mul i64) ((.var v169.1), (.imm 4), ())) fun v170 =>
                    .let_ (Op.mk (OpCode.add i64) ((.var pTmk), (.var v170.1), ())) fun v171 =>
                    .store (t := i32) (.imm 0) (.var v171.1) <|
                    .jump J35.1 ((.var v164.1), ())
                  ) (
                    .jump J34.1 ((.var p162.1), (.var nc_w), (.imm true), ())
                  )
                )
                .nil) (fun J35 =>
                .jump J35.1 ((.var p142.1), ())
              )
            )
          )
        )
        .nil) (fun J33 =>
        .let_ (Op.mk (OpCode.zext 32 64) ((.var ov), ())) fun v142 =>
        .let_ (Op.mk (OpCode.mul i64) ((.var v142.1), (.imm 4), ())) fun v143 =>
        .let_ (Op.mk (OpCode.add i64) ((.var pTmk), (.var v143.1), ())) fun v144 =>
        .load i32 (.var v144.1) fun ld145 =>
        .let_ (Op.mk (.cmp CmpOp.eq i32) ((.var ld145), (.imm 0), ())) fun v146 =>
        .jnz (.var v146.1) (
          .let_ (Op.mk (.cmp CmpOp.uge i32) ((.var nv_w), (.var mv), ())) fun v147 =>
          .jnz (.var v147.1) (
            .jump J25 ((.var nv_w), (.var nc_w), (.imm true), (.var p_next), ())
          ) (
            .let_ (Op.mk (OpCode.zext 32 64) ((.var nv_w), ())) fun v148 =>
            .let_ (Op.mk (OpCode.mul i64) ((.var v148.1), (.imm 4), ())) fun v149 =>
            .let_ (Op.mk (OpCode.add i64) ((.var pWs1), (.var v149.1), ())) fun v150 =>
            .store (t := i32) (.var ov) (.var v150.1) <|
            .let_ (Op.mk (OpCode.add i32) ((.var nv_w), (.imm 1), ())) fun v151 =>
            .let_ (Op.mk (OpCode.zext 32 64) ((.var ov), ())) fun v152 =>
            .let_ (Op.mk (OpCode.mul i64) ((.var v152.1), (.imm 4), ())) fun v153 =>
            .let_ (Op.mk (OpCode.add i64) ((.var pTmk), (.var v153.1), ())) fun v154 =>
            .store (t := i32) (.var v151.1) (.var v154.1) <|
            .jump J33.1 ((.var v151.1), (.var done_w), ())
          )
        ) (
          .jump J33.1 ((.var nv_w), (.var done_w), ())
        )
      )
    )
    .nil) (fun J32 =>
    .let_ (Op.mk (OpCode.zext 32 64) ((.var ov), ())) fun v140 =>
    .let_ (Op.mk (OpCode.mul i64) ((.var v140.1), (.imm 4), ())) fun v141 =>
    .let_ (Op.mk (OpCode.add i64) ((.var pTmk), (.var v141.1), ())) fun v142 =>
    .load i32 (.var v142.1) fun ld143 =>
    .let_ (Op.mk (.cmp CmpOp.ne i32) ((.var ld143), (.imm 0), ())) fun v144 =>
    .jnz (.var v144.1) (
      .let_ (Op.mk (OpCode.zext 32 64) ((.var ov), ())) fun v145 =>
      .let_ (Op.mk (OpCode.mul i64) ((.var v145.1), (.imm 4), ())) fun v146 =>
      .let_ (Op.mk (OpCode.add i64) ((.var pTmk), (.var v146.1), ())) fun v147 =>
      .load i32 (.var v147.1) fun ld148 =>
      .let_ (Op.mk (OpCode.sub i32) ((.var ld148), (.imm 1), ())) fun v149 =>
      .let_ (Op.mk (.cmp CmpOp.ult i32) ((.var v149.1), (.var layer_start), ())) fun v150 =>
      .jnz (.var v150.1) (
        .jump J26 ((.var nv_w), (.var nc_w), (.var done_w), (.var p_next), ())
      ) (
        .jump J32.1 (())
      )
    ) (
      .jump J32.1 (())
    )
  )

def binUnitCallExpr (onDone : Val i32 → Val .bool → Expr Val Cont [i64])
    (pHdr pTmp pKptr : Val i64) (nc : Val i32) (done : Val .bool) (qi0 pol : Val i32) :
    Expr Val Cont [i64] :=
  .let_ (Op.mk (OpCode.sext 32 64) ((.imm 0), ())) fun v0 =>
  .let_ (Op.mk (OpCode.mul i64) ((.var v0.1), (.imm 4), ())) fun v1 =>
  .let_ (Op.mk (OpCode.add i64) ((.var pTmp), (.var v1.1), ())) fun v2 =>
  .let_ (Op.mk (OpCode.shl i32) ((.var qi0), (.imm 1), ())) fun v3 =>
  .let_ (Op.mk (OpCode.or i32) ((.var v3.1), (.var pol), ())) fun v4 =>
  .store (t := i32) (.var v4.1) (.var v2.1) <|
  .group (sig := [[i32, Ty.bool]]) (fun J => .cons
    (fun p => onDone p.1 p.2.1) .nil) (fun J =>
    .call (as := [i64, i64, i32]) (bs := [.bool]) "full_k6_add_clause"
        ((.var pHdr), (.var pTmp), (.imm 1), ()) fun c0 =>
    .jnz (.var c0.1) (
      .let_ (Op.mk (OpCode.add i32) ((.var nc), (.imm 1), ())) fun v5 =>
      .group (sig := [[Ty.bool]]) (fun Jin => .cons
        (fun q => .jump J.1 ((.var v5.1), (.var q.1), ())) .nil) (fun Jin =>
        .let_ (Op.mk (OpCode.zext 32 64) ((.imm 6), ())) fun v6 =>
        .let_ (Op.mk (OpCode.mul i64) ((.var v6.1), (.imm 4), ())) fun v7 =>
        .let_ (Op.mk (OpCode.add i64) ((.var pKptr), (.var v7.1), ())) fun v8 =>
        .load i32 (.var v8.1) fun ld =>
        .let_ (Op.mk (.cmp CmpOp.ne i32) ((.var ld), (.imm 0), ())) fun v9 =>
        .jnz (.var v9.1) (.jump Jin.1 ((.imm true), ())) (.jump Jin.1 ((.var done), ()))
      )
    ) (.jump J.1 ((.var nc), (.imm true), ()))
  )

end

public section

private theorem s13_cur_vars_eq {s st : FullState}
    (hag : AgreesExcept step13ConeMask s st) : st.core.cur_vars = s.core.cur_vars :=
  congrArg (fun t => t.core.cur_vars) hag

theorem step13_cone_bin_add_wp
    {Γ : Env} {Q : Post [i64]} {X : XPost} {R : Mem 64 → Prop}
    {c : FullCfg} {F0 : Std.Sat.CNF Nat} {F_cur : List (List Nat)} {L : K6Layout} {mvC : BitVec 32}
    {s st_w : FullState}
    {vlim nv_w nc_w : BitVec 32} {done_w : Bool} {p_next : BitVec 64}
    {pol cv qi_l qi0 lit ot ov layer_start : BitVec 32} {m : Mem 64}
    (hAddCl : M6EnvSpec Γ "full_k6_add_clause" step13K6AddClauseSpec)
    (J25 J26 : Cont [i32, i32, .bool, i64])
    (pHdr pWs1 pTmk pTmp pKptr : Val i64)
    (hpHdr : pHdr = c.hdr) (hpWs1 : pWs1 = c.pWorkStk1) (hpTmk : pTmk = c.pTarjanMark)
    (hpTmp : pTmp = c.pTmp) (hpKptr : pKptr = L.kPtr c.pScratchBuf)
    (_hw : FullWitnessInv c F0 F_cur s.core) (hlen_s : FullState.LengthsOk c s)
    (hLscr : L.scrLen = c.scratch_cap) (hLmv : L.maxV = k6MaxV c.scratch_cap)
    (hb_w : Step13ConeBase F_cur L mvC c s cv qi_l nv_w.toNat nc_w.toNat st_w)
    (hnv_w : nv_w.toNat ≤ mvC.toNat) (hnc_lt : nc_w.toNat < L.maxOrig)
    (hqi_lt : qi_l.toNat < nv_w.toNat) (hpol : pol.toNat < 2)
    (hqi0 : qi0 = BitVec.ofNat 32 qi_l.toNat) (hlit_eq : 2 * cv.toNat + pol.toNat = lit.toNat)
    (hot_lt : ot.toNat < 2 * s.core.cur_vars) (hov_eq : ov = ot >>> 1#32) (hov_ne_cv : ov ≠ cv)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause [lit.toNat, ot.toNat]))
    (hm : (FullMem c st_w ⋆ R) m)
    (hJ25 : ∀ (nv' nc' : BitVec 32) (done' : Bool) (st' : FullState) (m' : Mem 64),
      Step13ConeBase F_cur L mvC c s cv qi_l nv'.toNat nc'.toNat st' →
      nv_w.toNat ≤ nv'.toNat → nv'.toNat ≤ mvC.toNat → nc'.toNat ≤ L.maxOrig →
      qi_l.toNat < nv'.toNat → (FullMem c st' ⋆ R) m' →
      J25 (nv', nc', done', p_next, ()) m')
    (hJ26 : ∀ (nv' nc' : BitVec 32) (done' : Bool) (st' : FullState) (m' : Mem 64),
      Step13ConeBase F_cur L mvC c s cv qi_l nv'.toNat nc'.toNat st' →
      nv_w.toNat ≤ nv'.toNat → nv'.toNat ≤ mvC.toNat → nc'.toNat ≤ L.maxOrig →
      qi_l.toNat < nv'.toNat → (FullMem c st' ⋆ R) m' →
      J26 (nv', nc', done', p_next, ()) m') :
    wp Γ Q X (binAddExpr J25 J26 pHdr pWs1 pTmk pTmp pKptr mvC vlim nv_w nc_w done_w
        p_next pol qi0 ot ov layer_start) m := by
  subst hpHdr hpWs1 hpTmk hpTmp hpKptr
  let ws0 := st_w.scratch.work_stk1; let scr0 := st_w.scratch.scratch_buf
  have hcv_eq := s13_cur_vars_eq hb_w.hag
  have hov_lt : ov.toNat < s.core.cur_vars := by
    rw [hov_eq]; simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; omega
  have hov_div : ov.toNat = ot.toNat / 2 := by
    rw [hov_eq]; simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have htmk_w_len : ov.toNat < st_w.scratch.tarjan_mark.length := by
    have := hb_w.hlen.scratch_ok.tarjan_mark_len; have := hlen_s.core_ok.cur_vars_le; omega
  have hta_w := s13_tmk_ov_at st_w ov htmk_w_len
  refine wp_join_state (fun (_ : Unit) => ()) (fun _ m2 => m2 = m) ?_ ?_
  · intro J32 () m2 hm2; dsimp [Blocks.get, Member.here]
    let γ := BitVec 32 × Bool × FullState
    let Inv33 : γ → Mem 64 → Prop := fun ⟨nv_a, done_a, st_a⟩ m_a =>
      done_a = done_w ∧ nv_w.toNat ≤ nv_a.toNat ∧ nv_a.toNat ≤ mvC.toNat ∧
      Step13ConeSavedBase F_cur L mvC c s cv qi_l nv_w ws0 scr0 nv_a.toNat nc_w.toNat st_a ∧
      (∃ iov, iov < nv_a.toNat ∧ (st_a.scratch.work_stk1[iov]?.getD 0#32).toNat = ov.toNat ∧
        st_a.scratch.tarjan_mark[ov.toNat]?.getD 0#32 = BitVec.ofNat 32 (iov + 1)) ∧
      (FullMem c st_a ⋆ R) m_a
    refine wp_join_state (fun p => (p.1, p.2.1, ())) Inv33 ?_ ?_
    · intro J33 ⟨nv_a, done_a, st_a⟩ m_a
        ⟨_, hnv_wa, hnv_am, hsb_a, ⟨iov, hiov_lt, hiov_ws, hiov_tmk⟩, hm_a⟩
      dsimp [Blocks.get, Member.here]
      have hs0 : (BitVec.signExtend 64 0#32).toNat = 0 := by decide
      have hs1 : (BitVec.signExtend 64 1#32).toNat = 1 := by decide
      have h2_nv : 2 ≤ nv_a.toNat := by
        rcases Nat.lt_or_ge nv_a.toNat 2 with hlt | hge
        · have hw0 := hsb_a.hwk; rw [show qi_l.toNat = iov by omega, hiov_ws] at hw0
          exact False.elim (hov_ne_cv (BitVec.eq_of_toNat_eq hw0))
        · exact hge
      have htmp_ge2 : 2 ≤ st_a.core.tmp.length := by
        have := hsb_a.hlen.core_ok.tmp_len_arr; have := hsb_a.hcone.nv_le_cv
        have := s13_cur_vars_eq hsb_a.hag; have := hlen_s.core_ok.cur_vars_le; omega
      have htmp0_idx : (BitVec.signExtend 64 0#32).toNat < st_a.core.tmp.length := by
        rw [hs0]; omega
      have htmp1_idx : (BitVec.signExtend 64 1#32).toNat <
          (st_a.core.tmp.set (BitVec.signExtend 64 0#32).toNat
            ((qi0 <<< 1#32) ||| pol)).length := by rw [List.length_set, hs1]; omega
      have htmk_a_len : ov.toNat < st_a.scratch.tarjan_mark.length := by
        have := hsb_a.hlen.scratch_ok.tarjan_mark_len; have := hlen_s.core_ok.cur_vars_le; omega
      have hta_a := s13_tmk_ov_at st_a ov htmk_a_len
      have htmk_a_idx : (BitVec.setWidth 64 ov).toNat < st_a.scratch.tarjan_mark.length := by
        rw [hta_a.1]; exact htmk_a_len
      have hnv_31 : nv_a.toNat < 2 ^ 31 := by have := L.hmaxV; have := hsb_a.hcone.mvC_leMax; omega
      have hqi_nv_a : qi_l.toNat < nv_a.toNat := by omega
      have hqi0_lt32 : qi_l.toNat < 2 ^ 32 := by omega
      have ⟨hl0_lt, hl1_lt, hl0_lift, hl1_lift⟩ := m6_cone_bin_lits_ok (cv := cv) (qi := qi0)
        (pol := pol) (lit := lit) (ot := ot) (ov := ov) (nv := nv_a) (iov := iov)
        (by rw [hqi0, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hqi0_lt32]; exact hqi_nv_a)
        hnv_31 hpol hlit_eq.symm hov_div hiov_lt
        (by rw [hqi0, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hqi0_lt32]; exact hsb_a.htmk)
        (by rw [hqi0, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hqi0_lt32]; exact hsb_a.hwk)
        hiov_tmk hiov_ws
      have hl0_eq : (st_a.scratch.tarjan_mark[cv.toNat]?.getD 0#32 - 1#32) <<< 1#32 ||| pol =
          (qi0 <<< 1#32) ||| pol := by
        rw [show st_a.scratch.tarjan_mark[cv.toNat]?.getD 0#32 - 1#32 = qi0 by
          rw [hsb_a.htmk, hqi0]; exact bv32_ofNat_sub1 (by omega)]
      have hl0_lt' : ((qi0 <<< 1#32) ||| pol).toNat < 2 * nv_a.toNat := by
        rw [← hl0_eq]; exact hl0_lt
      have hl0_lift' : m6ConeLift st_a.scratch.work_stk1 ((qi0 <<< 1#32) ||| pol).toNat =
          lit.toNat := by rw [← hl0_eq]; exact hl0_lift
      have ⟨hlen_ab, htmp_lt2, hent_ab⟩ := m6_cone_bin_tmp_prep (c := c) (F_cur := F_cur)
        hsb_a.hlen (by omega : 1 < st_a.core.tmp.length) hl0_lt' hl1_lt hl0_lift' hl1_lift hent
      let l0_v := (qi0 <<< 1#32) ||| pol
      let st_a0 : FullState :=
        { core := { st_a.core with tmp := st_a.core.tmp.set 0 l0_v }, scratch := st_a.scratch }
      let l1_v := (st_a.scratch.tarjan_mark[ov.toNat]?.getD 0#32 - 1#32) <<< 1#32 ||| (ot &&& 1#32)
      let st_ab : FullState :=
        { core := { st_a.core with tmp := (st_a.core.tmp.set 0 l0_v).set 1 l1_v }
          scratch := st_a.scratch }
      c0_hstraight; refine head_wp_store rfl rfl (c0_store_full_tmp l0_v htmp0_idx hm_a) ?_
      intro m_t0 hm_t0
      have hm_t0' : (FullMem c st_a0 ⋆ R) m_t0 := by simpa [st_a0, l0_v, hs0] using hm_t0
      c0_hstraight
      refine head_wp_load rfl (c0_load_full_tarjan_mark (s := st_a0) htmk_a_idx hm_t0') ?_
      have hl1_eq : (st_a0.scratch.tarjan_mark[(BitVec.setWidth 64 ov).toNat] - 1#32) <<< 1#32 |||
          (ot &&& 1#32) = l1_v := by dsimp [l1_v, st_a0]; rw [hta_a.2]
      have htmp1_64 : (1#64 : BitVec 64).toNat < st_a0.core.tmp.length := by
        dsimp [st_a0]; rw [List.length_set]; omega
      c0_hstraight; dsimp only [Arg.val, Prod.fst]
      refine head_wp_store (by dsimp only [Arg.val]; exact hl1_eq) rfl
        (c0_store_full_tmp l1_v htmp1_64 hm_t0') ?_
      intro m_t1 hm_t1; c0_hstraight
      have hm_ab : (FullMem c st_ab ⋆ R) m_t1 := by
        dsimp [st_ab, st_a0, l0_v, l1_v]
        rw [← hs0, ← show (1#64 : BitVec 64).toNat = 1 from rfl]; exact hm_t1
      have hcone_ab : FidConeInv F_cur L mvC st_ab nv_a.toNat nc_w.toNat := by
        simpa [st_ab] using fidConeInv_tmp_irrel
          (tmp' := (st_a.core.tmp.set 0 l0_v).set 1 l1_v) hsb_a.hcone
      have hgu_ab : S13GuOk L s st_ab := s13GuOk_with_core_tmp hsb_a.hgu
      have hag_ab : AgreesExcept step13ConeMask s st_ab := by
        simpa [st_ab] using s13_upd_tmp ((st_a.core.tmp.set 0 l0_v).set 1 l1_v) hsb_a.hag
      have h2lt28 : (2#32 : BitVec 32).toNat < 2 ^ 28 := by decide
      have h2_tmp : (2#32 : BitVec 32).toNat ≤ st_ab.core.tmp.length := by
        dsimp [st_ab]; rw [List.length_set, List.length_set]; exact htmp_ge2
      refine wp_join_state
        (fun (p : BitVec 32 × BitVec 32 × Bool × FullState) => (p.1, p.2.1, p.2.2.1, ()))
        (fun ⟨nv_r, nc_r, done_r, st_r⟩ m_r =>
          Step13ConeBase F_cur L mvC c s cv qi_l nv_r.toNat nc_r.toNat st_r ∧
          nv_w.toNat ≤ nv_r.toNat ∧ nv_r.toNat ≤ mvC.toNat ∧ nc_r.toNat ≤ L.maxOrig ∧
          qi_l.toNat < nv_r.toNat ∧ (FullMem c st_r ⋆ R) m_r) ?_ ?_
      · intro J34 ⟨nv_r, nc_r, done_r, st_r⟩ m_r ⟨hb_r, hnv_wr, hnv_r, hnc_r, hqi_r, hm_r⟩
        dsimp [Blocks.get, Member.here]; try rw [wp_jump]
        exact hJ26 nv_r nc_r done_r st_r m_r hb_r hnv_wr hnv_r hnc_r hqi_r hm_r
      · intro J34 hJ34
        refine step13_cone_call_add_clause hAddCl rfl rfl rfl hLscr hLmv
          hlen_ab hag_ab hgu_ab hcone_ab hnc_lt h2lt28 h2_tmp htmp_lt2 hent_ab hm_ab ?_
        intro ok st' m'' hlen' hag' hgu' hcone' hscr_eq htmk_eq hws_eq hm''
        dsimp only; rw [wp_jnz]; refine ⟨fun hc => ?_, fun hc => ?_⟩
        · subst hc; c0_hstraight
          have hnc1 : (nc_w + 1#32).toNat = nc_w.toNat + 1 := by
            have := L.hmaxV; have := nc_w.isLt; simp only [K6Layout.maxOrig] at hnc_lt
            simp [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega : nc_w.toNat + 1 < 2 ^ 32)]
          have hkptr := (fid_cone_load_kptr_hdr hcone' hm'').1
          refine wp_join_state (fun (p : Bool) => (p, ())) (fun _ m3 => m3 = m'') ?_ ?_
          · intro J36 done' m3 hm3
            dsimp [Blocks.get, Member.here]; (try dsimp only); (try rw [wp_jump])
            exact hJ34 (nv_a, nc_w + 1#32, done', st') m3
              ⟨⟨hlen', hag', hgu', hcone', by rw [htmk_eq]; exact hsb_a.htmk,
                by rw [hws_eq]; exact hsb_a.hwk⟩, hnv_wa, hnv_am, by omega, hqi_nv_a,
                hm3 ▸ hm''⟩
          · intro J36 hJ36
            c0_hstraight; refine head_wp_load rfl hkptr ?_
            c0_hstraight; (try clear hc); m6_split
            · try dsimp only; try rw [wp_jump]; exact hJ36 true m'' rfl
            · c0_hstraight; (try clear hc); m6_split
              · try dsimp only; try rw [wp_jump]; exact hJ36 true m'' rfl
              · try dsimp only; try rw [wp_jump]; exact hJ36 done_a m'' rfl
        · subst hc
          have hsb' : Step13ConeSavedBase F_cur L mvC c s cv qi_l nv_w ws0 scr0
              nv_a.toNat nc_w.toNat st' :=
            ⟨⟨hlen', hag', hgu', hcone', by rw [htmk_eq]; exact hsb_a.htmk,
              by rw [hws_eq]; exact hsb_a.hwk⟩, hnv_wa,
              by rw [hscr_eq rfl, hsb_a.hscr], fun j hj => by rw [hws_eq]; exact hsb_a.hws j hj⟩
          refine step13_cone_rollback_loop_wp c.pWorkStk1 c.pTarjanMark rfl rfl
            (fun p => .jump J34 ((.var p), (.var nc_w), (.imm true), ()))
            hsb' hb_w.hcone.nv_ge1 hqi_lt hb_w.hcone.k6_bdd hb_w.hcone.k6_trl_bdd hm'' ?_
          intro st_r m_r hbase_r _ _ hm_r; try dsimp only; try rw [wp_jump]
          exact hJ34 (nv_w, nc_w, true, st_r) m_r
            ⟨hbase_r, Nat.le_refl _, hnv_w, by omega, hqi_lt, hm_r⟩
    · intro J33 hJ33
      have hm_w : (FullMem c st_w ⋆ R) m2 := by rw [hm2]; exact hm
      c0_hstraight
      refine head_wp_load rfl (c0_load_full_tarjan_mark (by rw [hta_w.1]; exact htmk_w_len) hm_w) ?_
      c0_hstraight; (try clear hc); m6_split
      · try intro hc
        have htmk0 : st_w.scratch.tarjan_mark[ov.toNat]?.getD 0#32 = 0#32 := by
          rw [hta_w.2]; exact hc
        c0_hstraight; (try clear hc); m6_split
        · (try intro hc); (try rw [wp_jump])
          exact hJ25 nv_w nc_w true st_w m2 hb_w (Nat.le_refl _) hnv_w (by omega) hqi_lt hm_w
        · try intro hc
          have hsb0 : Step13ConeSavedBase F_cur L mvC c s cv qi_l nv_w ws0 scr0
              nv_w.toNat nc_w.toNat st_w := ⟨hb_w, Nat.le_refl _, rfl, fun _ _ => rfl⟩
          have ⟨_, hnv1, _, _, hsu', _⟩ :=
            step13_cone_push_var_step_ok hsb0 (by omega) hov_lt htmk0 hqi_lt
          have hws_idx : (BitVec.setWidth 64 nv_w).toNat < st_w.scratch.work_stk1.length := by
            have := hb_w.hlen.scratch_ok.work_stk1_len; have := hb_w.hcone.mvC_leMax
            have := hb_w.hcone.nv_le_cv; have := hlen_s.core_ok.cur_vars_le; simp; omega
          c0_hstraight; refine head_wp_store rfl rfl (c0_store_full_work_stk1 ov hws_idx hm_w) ?_
          intro _ hm_ws; c0_hstraight; refine head_wp_store rfl rfl
            (c0_store_full_tarjan_mark (nv_w + 1#32) (by rw [hta_w.1]; exact htmk_w_len) hm_ws) ?_
          intro m_t hm_t; c0_hstraight; try dsimp only; try rw [wp_jump]
          have h1 : (BitVec.setWidth 64 nv_w).toNat = nv_w.toNat := by simp
          have hlen_w : nv_w.toNat < st_w.scratch.work_stk1.length := by simpa [h1] using hws_idx
          have hbv : nv_w + 1#32 = BitVec.ofNat 32 (nv_w.toNat + 1) := by
            apply BitVec.eq_of_toNat_eq; rw [hnv1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
          let st_push : FullState :=
            { core := st_w.core
              scratch :=
                { st_w.scratch with
                  work_stk1 := st_w.scratch.work_stk1.set nv_w.toNat ov
                  tarjan_mark := st_w.scratch.tarjan_mark.set ov.toNat (nv_w + 1#32) } }
          have hm_t' : (FullMem c st_push ⋆ R) m_t := by simpa [st_push, h1, hta_w.1] using hm_t
          exact hJ33 (nv_w + 1#32, done_w, st_push) m_t ⟨rfl, by rw [hnv1]; omega,
            by rw [hnv1]; omega, hsu', ⟨nv_w.toNat, by rw [hnv1]; omega,
              by dsimp [st_push]; rw [List.getElem?_set_self hlen_w, Option.getD_some],
              by dsimp [st_push]; rw [List.getElem?_set_self htmk_w_len, Option.getD_some, hbv]⟩,
            hm_t'⟩
      · try intro hc
        have htm_ne0 : st_w.scratch.tarjan_mark[ov.toNat]?.getD 0#32 ≠ 0#32 := by
          rw [List.getElem?_eq_getElem htmk_w_len, Option.getD_some]; exact hc
        rcases hb_w.hcone.rev ov.toNat (by rw [hcv_eq]; exact hov_lt) with
          h0 | ⟨iov, hiov_lt, hiov_ws, hiov_tmk⟩
        · exact False.elim (htm_ne0 h0)
        · try dsimp only; try rw [wp_jump]
          exact hJ33 (nv_w, done_w, st_w) m2 ⟨rfl, Nat.le_refl _, hnv_w,
            ⟨hb_w, Nat.le_refl _, rfl, fun _ _ => rfl⟩, ⟨iov, hiov_lt, hiov_ws, hiov_tmk⟩, hm_w⟩
  · intro J32 hJ32; c0_hstep; c0_hstep; c0_hstep
    refine head_wp_load (a := .var _) rfl
      (c0_load_full_tarjan_mark (by rw [hta_w.1]; exact htmk_w_len) hm) ?_
    c0_hstraight; (try clear hc); m6_split
    · c0_hstep; c0_hstep; c0_hstep
      refine head_wp_load rfl (c0_load_full_tarjan_mark (by rw [hta_w.1]; exact htmk_w_len) hm) ?_
      c0_hstraight; (try clear hc); m6_split
      · (try rw [wp_jump])
        exact hJ26 nv_w nc_w done_w st_w m hb_w (Nat.le_refl _) hnv_w (by omega) hqi_lt hm
      · (try rw [wp_jump]); exact hJ32 () m rfl
    · (try rw [wp_jump]); exact hJ32 () m rfl

theorem step13_cone_bin_unit_call_wp
    {Γ : Env} {Q : Post [i64]} {X : XPost} {R : Mem 64 → Prop}
    {c : FullCfg} {F_cur : List (List Nat)} {L : K6Layout} {mvC : BitVec 32}
    {s st_pre : FullState}
    {nv nc qi_l cv qi0 pol lit : BitVec 32} {done : Bool} {m : Mem 64}
    (hAddCl : M6EnvSpec Γ "full_k6_add_clause" step13K6AddClauseSpec)
    (onDone : Val i32 → Val .bool → Expr Val Cont [i64]) (pHdr pTmp pKptr : Val i64)
    (hpHdr : pHdr = c.hdr) (hpTmp : pTmp = c.pTmp) (hpKptr : pKptr = L.kPtr c.pScratchBuf)
    (hLscr : L.scrLen = c.scratch_cap) (hLmv : L.maxV = k6MaxV c.scratch_cap)
    (hlen_s : FullState.LengthsOk c s)
    (hb_pre : Step13ConeBase F_cur L mvC c s cv qi_l nv.toNat nc.toNat st_pre)
    (hnc_lt : nc.toNat < L.maxOrig) (hqi_lt : qi_l.toNat < nv.toNat)
    (hqi0 : qi0 = BitVec.ofNat 32 qi_l.toNat) (hpol : pol.toNat < 2)
    (hlit : 2 * (st_pre.scratch.work_stk1[qi0.toNat]?.getD 0#32).toNat + pol.toNat = lit.toNat)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause [lit.toNat]))
    (hm : (FullMem c st_pre ⋆ R) m)
    (hDone : ∀ (nc' : BitVec 32) (done' : Bool) (st' : FullState) (m' : Mem 64),
      Step13ConeBase F_cur L mvC c s cv qi_l nv.toNat nc'.toNat st' →
      nc'.toNat ≤ L.maxOrig → (FullMem c st' ⋆ R) m' →
      wp Γ Q X (onDone nc' done') m') :
    wp Γ Q X (binUnitCallExpr onDone pHdr pTmp pKptr nc done qi0 pol) m := by
  subst hpHdr hpTmp hpKptr; dsimp [binUnitCallExpr]; let u := (qi0 <<< 1#32) ||| pol
  have hnv_31 : nv.toNat < 2 ^ 31 := by
    have := hb_pre.hcone.mvC_leMax; have := L.hmaxV; have := hb_pre.hcone.nv_le_mvC; omega
  have hqi0_nat : qi0.toNat = qi_l.toNat := by
    rw [hqi0, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : qi_l.toNat < 2 ^ 32)]
  have hqi0_lt : qi0.toNat < nv.toNat := by rw [hqi0_nat]; exact hqi_lt
  have hu_eq : u.toNat = 2 * qi0.toNat + pol.toNat := by
    dsimp [u]; simp only [BitVec.toNat_shiftLeft]
    rw [Nat.mod_eq_of_lt (by rw [Nat.shiftLeft_eq]; omega : qi0.toNat <<< 1 < 2 ^ 32),
      ← Nat.shiftLeft_add_eq_or_of_lt (by omega : pol.toNat < 2 ^ 1), Nat.shiftLeft_eq]; omega
  have h0_tmp : 0 < st_pre.core.tmp.length := by
    have := hb_pre.hlen.core_ok.tmp_len_arr; have := hb_pre.hcone.nv_le_cv
    have := s13_cur_vars_eq hb_pre.hag; have := hlen_s.core_ok.cur_vars_le
    have := hb_pre.hcone.nv_ge1; omega
  have ⟨hlen_u, htmp_lt1, hent_u⟩ := m6_cone_unit_tmp_prep hb_pre.hlen h0_tmp hqi0_lt hnv_31 hpol
    (by omega) hu_eq hlit hent
  let st_u : FullState :=
    { core := { st_pre.core with tmp := st_pre.core.tmp.set 0 u }, scratch := st_pre.scratch }
  have hs0 : (BitVec.signExtend 64 0#32).toNat = 0 := by decide
  have hidx0 : (BitVec.signExtend 64 0#32).toNat < st_pre.core.tmp.length := by
    rw [hs0]; exact h0_tmp
  c0_hstraight
  refine head_wp_store rfl rfl (c0_store_full_tmp u hidx0 hm) fun m_u hm_u => ?_
  have hm_u' : (FullMem c st_u ⋆ R) m_u := by simpa [st_u, u, hs0] using hm_u
  have hcone_u : FidConeInv F_cur L mvC st_u nv.toNat nc.toNat := by
    simpa [st_u] using fidConeInv_tmp_irrel (tmp' := st_pre.core.tmp.set 0 u) hb_pre.hcone
  have hgu_u : S13GuOk L s st_u := s13GuOk_with_core_tmp hb_pre.hgu
  have hag_u : AgreesExcept step13ConeMask s st_u := by
    simpa [st_u] using s13_upd_tmp (st_pre.core.tmp.set 0 u) hb_pre.hag
  refine wp_join_state (α := BitVec 32 × Bool × FullState) (fun p => (p.1, p.2.1, ()))
    (fun ⟨nc', done', st'⟩ m' => Step13ConeBase F_cur L mvC c s cv qi_l nv.toNat nc'.toNat st' ∧
      nc'.toNat ≤ L.maxOrig ∧ (FullMem c st' ⋆ R) m') ?_ ?_
  · intro J ⟨nc', done', st'⟩ m' ⟨hb', hnc', hm'⟩
    dsimp [Blocks.get, Member.here]; exact hDone nc' done' st' m' hb' hnc' hm'
  · intro J hJ
    have h1_lt28 : (1#32 : BitVec 32).toNat < 2 ^ 28 := by decide
    have h1_tmp : (1#32 : BitVec 32).toNat ≤ st_u.core.tmp.length := by
      have := hlen_u.core_ok.tmp_len_arr; have := hlen_s.core_ok.cur_vars_le
      dsimp [st_u]; rw [List.length_set]; omega
    refine step13_cone_call_add_clause hAddCl rfl rfl rfl hLscr hLmv
      hlen_u hag_u hgu_u hcone_u hnc_lt h1_lt28 h1_tmp htmp_lt1 hent_u hm_u' ?_
    intro ok st' m'' hlen' hag' hgu' hcone' _ htmk_eq hws_eq hm''
    dsimp only; rw [wp_jnz]; refine ⟨fun hc => ?_, fun hc => ?_⟩
    · subst hc; have hnc1_le : (nc + 1#32).toNat ≤ L.maxOrig := by
        have := L.hmaxV; have := nc.isLt; simp only [K6Layout.maxOrig] at hnc_lt ⊢
        rw [BitVec.toNat_add, show (1#32 : BitVec 32).toNat = 1 from rfl,
          Nat.mod_eq_of_lt (by omega : nc.toNat + 1 < 2 ^ 32)]; omega
      c0_hstraight; refine wp_join_state (fun p => (p, ())) (fun _ m3 => m3 = m'') ?_ ?_
      · intro Jin done' m3 hm3
        dsimp [Blocks.get, Member.here]; (try dsimp only); (try rw [wp_jump])
        exact hJ (nc + 1#32, done', st') m3 ⟨⟨hlen', hag', hgu', hcone',
          by rw [htmk_eq]; exact hb_pre.htmk, by rw [hws_eq]; exact hb_pre.hwk⟩,
          hnc1_le, by rw [hm3]; exact hm''⟩
      · intro Jin hJin
        c0_hstraight; refine head_wp_load rfl (fid_cone_load_kptr_hdr hcone' hm'').1 ?_
        c0_hstraight; (try clear hc); m6_split
        · (try dsimp only); (try rw [wp_jump]); exact hJin true m'' rfl
        · (try dsimp only); (try rw [wp_jump]); exact hJin done m'' rfl
    · subst hc; (try dsimp only); (try rw [wp_jump])
      exact hJ (nc, true, st') m'' ⟨⟨hlen', hag', hgu', hcone', by rw [htmk_eq]; exact hb_pre.htmk,
        by rw [hws_eq]; exact hb_pre.hwk⟩, by omega, hm''⟩

end
end LeanQbe.T.Examples.Kissat.FullFidelityStep13S6a
