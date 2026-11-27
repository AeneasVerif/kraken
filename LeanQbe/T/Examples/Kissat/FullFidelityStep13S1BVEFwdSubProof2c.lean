/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S1BVEFwdSubProof2b
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Examples.Kissat.FullFidelityBveTactics
import LeanQbe.T.Examples.Kissat.FullM6SweepProofDenseProp
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Fidelity Step 13 Shard S1-B Proofs — Part 2c (`full_bve_certify_unit_fid`)

Parametric `(Γ : Env)` `Func.wp` proof (`public section`, `0` `@[expose]`, `0` `import all`,
`<= 100` cols, `< 1,400` LOC, every theorem `<= 420` lines) for Step-13 `full_bve_certify_unit_fid`
using `step13K6InitSpec`, `step13K6AddClauseSpec`, `k6SolveSpec`, and `fullAssignLvlSpec`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep13S1

open Std Std.Sat Std.ExtHashMap Kraken.Bedrock2.Test
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullDenseWatchHelpers
open LeanQbe.T.Examples.Kissat.FullFastBveBudgets
open LeanQbe.T.Examples.Kissat.FullM4Sweep
open LeanQbe.T.Examples.Kissat.FullM6Sweep
open LeanQbe.T.Examples.Kissat.FullM8CoreParity
open LeanQbe.T.Examples.Kissat.FullFidelityBve

open scoped FullArenaTactics CertMkTactics
open CertMkTactics

public section

private theorem cert_loop2_post_wp (Γ : Env) (Q : Post [.bool]) (X : XPost)
    (hSolve : ∀ a m Q X, k6SolveSpec a m Q X → Γ "full_k6_solve" [i64, i64] [i64] a m Q X)
    (hAssign : ∀ a m Q X, fullAssignLvlSpec a m Q X →
      Γ "full_assign_lvl" [i64, i32, i32, i32] [] a m Q X)
    (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
    (R : Mem 64 → Prop) (L : K6Layout) (P : (Nat → Bool) → Prop)
    (tmp3 exp tmk scr3 gu3 : List (BitVec 32)) (unit nv : BitVec 32) (ok2 : Bool)
    (m3 : Mem 64)
    (hP : P = certModelSet F_cur exp nv.toNat unit.toNat)
    (hinv : FullDenseInvW c F0 F_cur s)
    (htmp3_len : tmp3.length = c.max_vars) (hexp_len : exp.length = 2 * c.max_vars)
    (htmk_len : tmk.length = 2 * c.max_vars) (hscr3_len : scr3.length = c.scratch_cap)
    (hgu3_len : gu3.length = 64) (hmaxv_lt : c.max_vars < 2 ^ 32)
    (hnv_cv : nv.toNat ≤ s.core.cur_vars)
    (hLscr : L.scrLen = c.scratch_cap) (hLmax : L.maxV = k6MaxV c.scratch_cap)
    (hLbase : 4192 ≤ L.k6Base) (hunit : unit.toNat < 2 * s.core.cur_vars)
    (hok : certExportOk s.core.cur_vars nv.toNat tmk exp)
    (hpres3 : ∀ i < 4192, scr3[i]? = s.scratch.scratch_buf[i]?)
    (hk6_3 : ok2 = true → K6Inv L P (k6StateOfScratch L scr3) ∧
      K6TrailSynced (k6StateOfScratch L scr3) ∧ (k6StateOfScratch L scr3).lvl = 0#32 ∧
      (k6StateOfScratch L scr3).nv = nv ∧ k6AssumpLitsS L scr3 = [] ∧
      K6HwmClean L (gu3[33]?.getD 0#32) (k6StateOfScratch L scr3))
    (hm3 : (Full.FullMem c (certMkStateGu s tmp3 exp tmk scr3 gu3) ⋆ R) m3)
    (hQ : ∀ (res : Bool) (s' : FullState) (m' : Mem 64),
      FullDenseInvW c F0 F_cur s' → TmkZero s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.arena = s.core.arena → s'.core.arena_len = s.core.arena_len →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (∀ i < 4192, s'.scratch.scratch_buf[i]? = s.scratch.scratch_buf[i]?) →
      (Full.FullMem c s' ⋆ R) m' → Q (res, ()) m') :
    wp Γ Q X (certUndoTmkExpr c.pWsort c.pTarjanMark nv
      (certPostLoop2Expr c.hdr c.pVals unit ok2)) m3 := by
  let s_gu : FullState := { s with scratch := { s.scratch with glue_used := gu3 } }
  have hdw3 : FullDenseInvW c F0 F_cur (certMkState s_gu tmp3 exp tmk scr3) :=
    cert_fullDenseInvW_mk hinv htmp3_len hexp_len htmk_len hscr3_len hgu3_len
  refine cert_undo_tmk_wp Γ Q X c F0 F_cur s s_gu R tmp3 exp tmk scr3 nv m3
    (certPostLoop2Expr c.hdr c.pVals unit ok2) hinv hdw3 hnv_cv rfl hinv.1.core_ok.cur_vars_le
    hmaxv_lt htmp3_len hexp_len htmk_len hscr3_len hgu3_len hok hm3 ?_
  intro tmk' m4 htmk'_len htmk4 hinv4 hm4
  unfold certPostLoop2Expr; c0_hsteps
  · have hok2_t : ok2 = true := by c0_bound
    rcases hk6_3 hok2_t with ⟨hk6inv3, _, _, _, hna3, _⟩
    fid_call hSolve; dsimp only [Arg.val]
    refine ⟨c, certMkState s_gu tmp3 exp tmk' scr3, P, L, R, rfl, hinv4.1, hLscr, hLmax,
      hk6inv3, hm4, ?_⟩
    intro r fl' scr5 m5; dsimp only
    intro hlen5 hfl5 hpres5 _ _ _ _ has5 _ hr huns5 hm5
    let s5 := { certMkState s_gu tmp3 exp tmk' scr3 with
      core := { (certMkState s_gu tmp3 exp tmk' scr3).core with fuel := fl' }
      scratch := { (certMkState s_gu tmp3 exp tmk' scr3).scratch with scratch_buf := scr5 } }
    have hinv5 : FullDenseInvW c F0 F_cur s5 :=
      cert_fullDenseInvW_mk (cert_fullDenseInvW_fuel hinv4 fl')
        htmp3_len hexp_len htmk'_len hlen5.scratch_ok.scratch_buf_len hgu3_len
    have htmk5 : TmkZero s5 := htmk4
    have hpres_4192_5 : ∀ i < 4192, scr5[i]? = s.scratch.scratch_buf[i]? :=
      fun i hi => by rw [hpres5 i (by omega)]; exact hpres3 i hi
    c0_hsteps
    · exact hQ false s5 m5 hinv5 htmk5 rfl rfl rfl hfl5
        (fun i hi => by simp [s5, hpres_4192_5 i hi]) hm5
    · have hreq20 : r = 20#64 := by c0_bound
      have hna_nil : k6AssumpLitsS L scr5 = [] := by
        rw [has5, show (certMkState s_gu tmp3 exp tmk' scr3).scratch.scratch_buf = scr3 from rfl,
          hna3]
      have hP_unsat : ∀ β : Nat → Bool, ¬ P β := fun β hPβ => by
        have hns := huns5 hreq20 β hPβ; rw [hna_nil] at hns
        exact hns (by simp [unitsCnf, CNF.sat_empty])
      refine cert_finish_unit_wp Γ Q X hAssign c F0 F_cur s5 R unit m5 hinv5 htmk5 hunit
        (cert_modelSet_unsat_entails (hP ▸ hP_unsat)) hm5 ?_
      intro s6 m6 hinv6 htmk6 hcv6 har6 hal6 hfl6 hscr6 hm6
      exact hQ true s6 m6 hinv6 htmk6 hcv6 har6 hal6 (hfl6 ▸ hfl5)
        (fun i hi => by rw [hscr6]; exact hpres_4192_5 i hi) hm6
  · exact hQ false (certMkState s_gu tmp3 exp tmk' scr3) m4 hinv4 htmk4 rfl rfl rfl
      (Nat.le_refl _) (fun i hi => hpres3 i hi) hm4

private theorem cert_loop2_addCl_wp (Γ : Env) (Q : Post [.bool]) (X : XPost)
    (hAdd : M6EnvSpec Γ "full_k6_add_clause" step13K6AddClauseSpec)
    (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
    (R : Mem 64 → Prop) (L : K6Layout) (P : (Nat → Bool) → Prop)
    (tmp2 exp tmk scr' gu' : List (BitVec 32)) (nv : BitVec 32) (a_csz : Arg Val i32)
    (m2 : Mem 64)
    (hinv : FullDenseInvW c F0 F_cur s) (htmp2_len : tmp2.length = c.max_vars)
    (hexp_len : exp.length = 2 * c.max_vars) (htmk_len : tmk.length = 2 * c.max_vars)
    (hscr'_len : scr'.length = c.scratch_cap) (hgu'_len : gu'.length = 64)
    (hLscr : L.scrLen = c.scratch_cap) (hLmax : L.maxV = k6MaxV c.scratch_cap)
    (hLbase : 4192 ≤ L.k6Base) (hpres' : ∀ i < 4192, scr'[i]? = s.scratch.scratch_buf[i]?)
    (hk6inv' : K6Inv L P (k6StateOfScratch L scr')) (hts' : K6TrailSynced (k6StateOfScratch L scr'))
    (hlvl' : (k6StateOfScratch L scr').lvl = 0#32) (hknv' : (k6StateOfScratch L scr').nv = nv)
    (hna' : k6AssumpLitsS L scr' = [])
    (hhwm' : K6HwmClean L (gu'[33]?.getD 0#32) (k6StateOfScratch L scr'))
    (hcsz_le : a_csz.val.toNat ≤ tmp2.length) (hcsz_28 : a_csz.val.toNat < 2 ^ 28)
    (hlts : ∀ j < a_csz.val.toNat, (tmp2[j]?.getD 0#32).toNat < 2 * nv.toNat)
    (hsem : SemEntails P ((tmp2.take a_csz.val.toNat).map BitVec.toNat))
    (hm2 : (Full.FullMem c (certMkStateGu s tmp2 exp tmk scr' gu') ⋆ R) m2)
    (k_ret : Tup Val [.bool] → Expr Val Cont [.bool])
    (hk : ∀ ok_a scr_a gu_a m_a,
      certL2Inv c s R L P nv exp tmk ok_a tmp2 scr_a gu_a m_a →
      wp Γ Q X (k_ret (ok_a, ())) m_a) :
    wp Γ Q X
      (Expr.call (as := [i64, i64, i32]) (bs := [.bool]) "full_k6_add_clause"
        (Arg.var c.hdr, Arg.var c.pTmp, a_csz, ()) k_ret) m2 := by
  let s2 := certMkStateGu s tmp2 exp tmk scr' gu'
  have hm_foc := cert_focus_addCl_tmp hm2
  refine wp_call_of_spec _ _ (hAdd _ _ _ _ ?_)
  refine ⟨c, s2, P, L, scr', gu', tmp2, _, rfl, ?_, rfl, rfl, hLscr, hLmax, hk6inv', hts', hlvl',
    hcsz_le, hcsz_28, (fun j hj => by simpa [hknv'] using hlts j hj), hsem, hhwm', hm_foc, ?_⟩
  · exact (cert_fullDenseInvW_mk hinv htmp2_len hexp_len htmk_len hscr'_len hgu'_len).1
  · dsimp only
    intro ok_a scr_a gu_a m_a hlen_a hpres_a hgu_a hhwm_a hk6_a hts_a hlvl_a hnv_a _
      has_a _ _ _ hm_a
    have hm_unf := cert_unfocus_addCl_tmp hm_a
    have hpres_4192_a : ∀ i < 4192, scr_a[i]? = s.scratch.scratch_buf[i]? :=
      fun i hi => by rw [hpres_a i (by omega)]; exact hpres' i hi
    have hna_nil_a : k6AssumpLitsS L scr_a = [] := by rw [has_a, hna']
    exact hk ok_a scr_a gu_a m_a ⟨htmp2_len, hlen_a.scratch_ok.scratch_buf_len,
      hlen_a.scratch_ok.glue_used_len, hpres_4192_a,
      fun _ => ⟨hk6_a, hts_a, hlvl_a, by rw [hnv_a, hknv'], hna_nil_a, hhwm_a⟩, hm_unf⟩

private def certLoop2UnitExpr (Jm : Cont [.bool]) (B : Cont [i32, .bool])
    (pHdr pVals pTmk pTmp : BitVec 64) (ot idx2 nv : BitVec 32) (ok2 : Bool) :
    Expr Val Cont [.bool] :=
  Expr.group (fun (_ : Tup Cont [[.bool]]) => Blocks.cons (fun q =>
    Expr.jump Jm (Arg.var q.fst, ())) Blocks.nil) fun Js_u =>
  Expr.let_ ⟨OpCode.zext 32 64, (Arg.var ot, ())⟩ fun p_1 =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var pVals, Arg.var p_1.fst, ())⟩ fun p_2 =>
  Expr.load i8 (Arg.var p_2.fst) fun ld =>
  Expr.let_ ⟨OpCode.trunc 32 8, (Arg.imm 0, ())⟩ fun p_3 =>
  Expr.let_ ⟨OpCode.sext 8 32, (Arg.var ld, ())⟩ fun p_4 =>
  Expr.let_ ⟨OpCode.sext 8 32, (Arg.var p_3.fst, ())⟩ fun p_5 =>
  Expr.let_ ⟨OpCode.cmp CmpOp.eq i32 Ty.bool rfl, (Arg.var p_4.fst, Arg.var p_5.fst, ())⟩
    fun p_6 =>
  Expr.jnz (Arg.var p_6.fst)
    (Expr.let_ ⟨OpCode.lshr i32, (Arg.var ot, Arg.imm 1, ())⟩ fun p_7 =>
     Expr.let_ ⟨OpCode.zext 32 64, (Arg.var p_7.fst, ())⟩ fun p_8 =>
     Expr.let_ ⟨OpCode.mul i64, (Arg.var p_8.fst, Arg.imm 4, ())⟩ fun p_9 =>
     Expr.let_ ⟨OpCode.add i64, (Arg.var pTmk, Arg.var p_9.fst, ())⟩ fun p_10 =>
     Expr.load i32 (Arg.var p_10.fst) fun ld1 =>
     Expr.let_ ⟨OpCode.cmp CmpOp.eq i32 Ty.bool rfl, (Arg.var ld1, Arg.imm 0, ())⟩ fun p_11 =>
     Expr.jnz (Arg.var p_11.fst)
       (Expr.jump B (Arg.var idx2, Arg.imm false, ()))
       (Expr.let_ ⟨OpCode.cmp CmpOp.ugt i32 Ty.bool rfl, (Arg.var ld1, Arg.var nv, ())⟩
          fun p_12 =>
        Expr.jnz (Arg.var p_12.fst)
          (Expr.jump B (Arg.var idx2, Arg.imm false, ()))
          (Expr.let_ ⟨OpCode.sext 32 64, (Arg.imm 0, ())⟩ fun p_13 =>
           Expr.let_ ⟨OpCode.mul i64, (Arg.var p_13.fst, Arg.imm 4, ())⟩ fun p_14 =>
           Expr.let_ ⟨OpCode.add i64, (Arg.var pTmp, Arg.var p_14.fst, ())⟩ fun p_15 =>
           Expr.let_ ⟨OpCode.sub i32, (Arg.var ld1, Arg.imm 1, ())⟩ fun p_16 =>
           Expr.let_ ⟨OpCode.shl i32, (Arg.var p_16.fst, Arg.imm 1, ())⟩ fun p_17 =>
           Expr.let_ ⟨OpCode.and i32, (Arg.var ot, Arg.imm 1, ())⟩ fun p_18 =>
           Expr.let_ ⟨OpCode.or i32, (Arg.var p_17.fst, Arg.var p_18.fst, ())⟩ fun p_19 =>
           Expr.store (t := i32) (Arg.var p_19.fst) (Arg.var p_15.fst)
             (Expr.call (as := [i64, i64, i32]) (bs := [.bool]) "full_k6_add_clause"
               (Arg.var pHdr, Arg.var pTmp, Arg.imm 1, ()) fun p_20 =>
              Expr.jnz (Arg.var p_20.fst) (Expr.jump Js_u.fst (Arg.var ok2, ()))
                (Expr.jump B (Arg.var idx2, Arg.imm false, ()))))))
    (Expr.jump Js_u.fst (Arg.var ok2, ()))

private theorem cert_loop2_unit_wp (Γ : Env) (Q : Post [.bool]) (X : XPost)
    (hAdd : M6EnvSpec Γ "full_k6_add_clause" step13K6AddClauseSpec)
    (Jm : Cont [.bool]) (B : Cont [i32, .bool])
    (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
    (R : Mem 64 → Prop) (L : K6Layout) (P : (Nat → Bool) → Prop)
    (tmp' exp tmk scr' gu' : List (BitVec 32)) (ot unit idx2 nv : BitVec 32)
    (ok2 : Bool) (m' : Mem 64)
    (hP : P = certModelSet F_cur exp nv.toNat unit.toNat) (hnv_le : nv.toNat ≤ 8192)
    (hok2_t : ok2 = true) (hinv : FullDenseInvW c F0 F_cur s) (hmaxv_pos : 0 < c.max_vars)
    (htmp'_len : tmp'.length = c.max_vars) (hexp_len : exp.length = 2 * c.max_vars)
    (htmk_len : tmk.length = 2 * c.max_vars) (hscr'_len : scr'.length = c.scratch_cap)
    (hgu'_len : gu'.length = 64) (hLscr : L.scrLen = c.scratch_cap)
    (hLmax : L.maxV = k6MaxV c.scratch_cap) (hLbase : 4192 ≤ L.k6Base)
    (hpres' : ∀ i < 4192, scr'[i]? = s.scratch.scratch_buf[i]?)
    (hk6inv' : K6Inv L P (k6StateOfScratch L scr')) (hts' : K6TrailSynced (k6StateOfScratch L scr'))
    (hlvl' : (k6StateOfScratch L scr').lvl = 0#32) (hknv' : (k6StateOfScratch L scr').nv = nv)
    (hna' : k6AssumpLitsS L scr' = [])
    (hhwm' : K6HwmClean L (gu'[33]?.getD 0#32) (k6StateOfScratch L scr'))
    (hok : certExportOk s.core.cur_vars nv.toNat tmk exp)
    (hot_lt : ot.toNat < 2 * s.core.cur_vars)
    (hot_ent : (cnfOfClauses F_cur).EntailsClause (cnfClause [unit.toNat, ot.toNat]))
    (hm' : (Full.FullMem c (certMkStateGu s tmp' exp tmk scr' gu') ⋆ R) m')
    (hJm : ∀ bst : Bool × List (BitVec 32) × List (BitVec 32) × List (BitVec 32) × Mem 64,
      ∀ m_in : Mem 64,
      (match bst with
       | (ok_n, tmp_n, scr_n, gu_n, m_n) => m_in = m_n ∧
         certL2Inv c s R L P nv exp tmk ok_n tmp_n scr_n gu_n m_n) →
      Jm (bst.1, ()) m_in)
    (hFail : ∀ {tmp_f scr_f gu_f mf}, tmp_f.length = c.max_vars →
      scr_f.length = c.scratch_cap → gu_f.length = 64 →
      (∀ i < 4192, scr_f[i]? = s.scratch.scratch_buf[i]?) →
      (Full.FullMem c (certMkStateGu s tmp_f exp tmk scr_f gu_f) ⋆ R) mf →
      B (idx2, false, ()) mf) :
    wp Γ Q X (certLoop2UnitExpr Jm B c.hdr c.pVals c.pTarjanMark c.pTmp ot idx2 nv ok2) m' := by
  let s' := certMkStateGu s tmp' exp tmk scr' gu'
  have hcv_le := hinv.1.core_ok.cur_vars_le
  have hv_len : s'.core.vals.length = 2 * c.max_vars := hinv.1.core_ok.vals_len
  have hot_len : (BitVec.zeroExtend 64 ot).toNat < s'.core.vals.length := by
    rw [cert_zext64_toNat, hv_len]; omega
  unfold certLoop2UnitExpr; c0_hsteps
  { exact hFail htmp'_len hscr'_len hgu'_len hpres' hm' }
  { exact hFail htmp'_len hscr'_len hgu'_len hpres' hm' }
  { have hu_eq := cert_shr1_toNat ot
    have hu_lt_cv : (ot >>> 1#32).toNat < s.core.cur_vars := by rw [hu_eq]; omega
    have hu_lt_tmk : (BitVec.zeroExtend 64 (ot >>> 1#32)).toNat < tmk.length := by
      rw [cert_zext64_toNat, htmk_len]; omega
    have hloc_nz : tmk[ot.toNat / 2] ≠ 0#32 := by c0_bound
    have hloc_le : tmk[ot.toNat / 2].toNat ≤ nv.toNat := by
      have hc2 : ¬ nv.toNat < tmk[ot.toNat / 2].toNat := by
        simpa only [show (2 : Nat) ^ OfNat.ofNat 1 = 2 from rfl] using hc
      exact Nat.le_of_not_lt fun h => hc2 h
    have hget_loc := cert_getElemD (by omega : ot.toNat / 2 < tmk.length) 0#32
    have hok_u := hok.1 (ot.toNat / 2) (by omega) (by rwa [hget_loc])
    have hloc1 : 1 ≤ tmk[ot.toNat / 2].toNat := by rw [← hget_loc]; exact hok_u.1
    have h0_lt_tmp : (BitVec.zeroExtend 64 0#32).toNat < tmp'.length := by
      rw [cert_zext64_toNat, htmp'_len]; exact hmaxv_pos
    c0_hsteps
    let loc := tmk[(ot >>> 1#32).toNat]
    have hloc_eq : loc = tmk[ot.toNat / 2] :=
      cert_list_getElem_eq rfl hu_eq (by rw [hu_eq]; omega) (by omega)
    let lit0 := ((loc - 1#32) <<< 1#32) ||| (ot &&& 1#32)
    let tmp'' := tmp'.set (BitVec.zeroExtend 64 0#32).toNat lit0
    have htmp''_eq : tmp'' = tmp'.set 0 lit0 := by simp [tmp'']
    have htmp''_len : tmp''.length = c.max_vars := by simp [htmp''_eq, htmp'_len]
    have hlit0_toNat : lit0.toNat = 2 * (loc.toNat - 1) + ot.toNat % 2 :=
      cert_packed_lit_toNat loc ot (hloc_eq ▸ hloc1) (hloc_eq ▸ by omega)
    have hlit0_lt : lit0.toNat < 2 * nv.toNat := by rw [hlit0_toNat, hloc_eq]; omega
    have hm0 := hm
    have htm_ot : (certMkStateGu s tmp' exp tmk scr' gu').scratch.tarjan_mark[
        (BitVec.setWidth 64 (ot >>> OfNat.ofNat 1)).toNat] = loc :=
      cert_list_getElem_eq (certMkStateGu_tmk s tmp' exp tmk scr' gu')
        (cert_zext64_toNat _)
        (by rw [certMkStateGu_tmk, cert_zext64_toNat,
              show (ot >>> OfNat.ofNat 1) = ot >>> 1#32 from rfl, hu_eq]; omega)
        (by rw [show (ot >>> OfNat.ofNat 1) = ot >>> 1#32 from rfl, hu_eq]; omega)
    erw [htm_ot] at hm0
    have hm_foc := cert_focus_addCl_tmp hm0
    have h1n : (1 : BitVec 32).toNat = 1 := rfl
    fid_call hAdd; dsimp only [vals, Arg.val]
    refine ⟨c, certMkStateGu s tmp'' exp tmk scr' gu', P, L, scr', gu', tmp'', _, rfl, ?_,
      rfl, rfl, hLscr, hLmax, hk6inv', hts', hlvl', (by rw [h1n, htmp''_len]; exact hmaxv_pos),
      (by rw [h1n]; decide), ?_, ?_, hhwm', hm_foc, ?_⟩
    { exact (cert_fullDenseInvW_mk hinv htmp''_len hexp_len htmk_len hscr'_len hgu'_len).1 }
    { intro idx0 hidx0
      have hi0 : idx0 = 0 := by rw [h1n] at hidx0; omega
      subst hi0
      rw [htmp''_eq, List.getElem?_set_self (by rw [htmp'_len]; exact hmaxv_pos),
        Option.getD_some, hknv']
      exact hlit0_lt }
    { intro β hPβ
      rw [hP] at hPβ; rcases hPβ with ⟨α, hsat, hnu, hmap⟩
      rcases cert_entails_in_modelSet hot_ent hsat hnu with ⟨q, hqm, _, hqs⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hqm
      rcases hqm with rfl | rfl
      · exact absurd hqs hnu
      · have htake : List.take 1 tmp'' = [lit0] := by
          rw [htmp''_eq]; cases tmp' with
          | nil => rw [← htmp'_len] at hmaxv_pos; exact absurd hmaxv_pos (Nat.not_lt_zero _)
          | cons _ _ => rfl
        rw [h1n, htake]; simp only [List.map_cons, List.map_nil]
        have hexp_loc : (exp[loc.toNat - 1]?.getD 0#32).toNat = ot.toNat / 2 := by
          rw [← show tmk[ot.toNat / 2]?.getD 0#32 = loc from hloc_eq ▸ hget_loc]; exact hok_u.2.2
        exact cert_mapped_lit_sat (hloc_eq ▸ hloc1) (hloc_eq ▸ hloc_le) hexp_loc hmap
          (by rw [hlit0_toNat]; omega) (by rw [hlit0_toNat]; omega) hqs }
    { dsimp only
      intro ok_a scr_a gu_a m_a hlen_a hpres_a hgu_a hhwm_a hk6_a hts_a hlvl_a hnv_a _
        has_a _ _ _ hm_a
      have hm_unf := cert_unfocus_addCl_tmp hm_a
      have hpres_4192_a : ∀ i < 4192, scr_a[i]? = s.scratch.scratch_buf[i]? :=
        fun i hi => by rw [hpres_a i (by omega)]; exact hpres' i hi
      have hna_nil_a : k6AssumpLitsS L scr_a = [] := by rw [has_a, hna']
      c0_hsteps
      { have hok_a : ok_a = true := by c0_bound
        have hgoal := hJm (true, tmp'', scr_a, gu_a, m_a) m_a ⟨rfl, htmp''_len,
          hlen_a.scratch_ok.scratch_buf_len, hlen_a.scratch_ok.glue_used_len, hpres_4192_a,
          fun _ => ⟨hk6_a, hts_a, hlvl_a, by rw [hnv_a, hknv'], hna_nil_a, hhwm_a⟩, hm_unf⟩
        dsimp only at hgoal ⊢; rwa [hok2_t] }
      { exact hFail htmp''_len hlen_a.scratch_ok.scratch_buf_len hlen_a.scratch_ok.glue_used_len
          hpres_4192_a hm_unf } } }
  { have hgoal := hJm (true, tmp', scr', gu', m') m'
      ⟨rfl, htmp'_len, hscr'_len, hgu'_len, hpres',
       fun _ => ⟨hk6inv', hts', hlvl', hknv', hna', hhwm'⟩, hm'⟩
    dsimp only at hgoal ⊢; rwa [hok2_t] }

theorem full_bve_certify_unit_fid_s13_wp (Γ : Env)
    (hMaxV : ∀ a m Q X, FullM6Sweep.m6MaxVSpec a m Q X → Γ "full_m6_max_v" [i64] [i64] a m Q X)
    (hInit : M6EnvSpec Γ "full_k6_init" step13K6InitSpec)
    (hAdd : M6EnvSpec Γ "full_k6_add_clause" step13K6AddClauseSpec)
    (hSolve : ∀ a m Q X, FullM6Sweep.k6SolveSpec a m Q X →
      Γ "full_k6_solve" [i64, i64] [i64] a m Q X)
    (hAssign : ∀ a m Q X, Full.fullAssignLvlSpec a m Q X →
      Γ "full_assign_lvl" [i64, i32, i32, i32] [] a m Q X) :
    ∀ a m Q X, fidBveCertifyUnitSpec a m Q X →
      Func.wp Γ full_bve_certify_unit_fid_body a m Q X := by
  rintro ⟨h, _v, unit, side_off, side_cnt, side_mask, ⟨⟩⟩ m Q X hspec
  rcases fidBveCertifyUnitSpec_elim hspec with
    ⟨c, F0, F_cur, s, R, rfl, hinv, htmk, hcap, hunit, hcnt, hoff_cnt, hmask, hent, hm, hQ⟩
  unfold full_bve_certify_unit_fid_body Func.wp
  have hcur_pos : 0 < s.core.cur_vars := by omega
  have hmaxv_pos : 0 < c.max_vars := Nat.lt_of_lt_of_le hcur_pos hinv.1.core_ok.cur_vars_le
  have hmaxv_lt : c.max_vars < 2 ^ 32 := by
    have := c.hmaxv; unfold LeanQbe.T.Examples.LratBytes.dimacsBound at this; omega
  have hcap_lt : c.scratch_cap < 2 ^ 64 := by
    have := c.hscr; unfold LeanQbe.T.Examples.LratBytes.dimacsBound at this; omega
  have harena_lt : c.arena_cap < 2 * 2 ^ 28 := by
    have := c.harena; unfold LeanQbe.T.Examples.LratBytes.dimacsBound at this; exact this
  c0_hsteps; fid_call hMaxV; dsimp only [m6MaxVSpec]
  let mv_nat := k6MaxV c.scratch_cap; let mv_sw : BitVec 32 := BitVec.ofNat 32 mv_nat
  have hmv_le : mv_nat ≤ 8192 := by
    by_cases hlt : c.scratch_cap < k6MinScr
    · have : mv_nat = 0 := by simp [mv_nat, k6MaxV, hlt]
      omega
    · exact (k6MaxV_bounds (Nat.not_lt.mp hlt)).2.1
  have hmv64 : BitVec.setWidth 32 (BitVec.ofNat 64 (k6MaxV c.scratch_cap)) = mv_sw := by
    apply BitVec.eq_of_toNat_eq; simp [mv_sw, mv_nat, Nat.mod_eq_of_lt (by omega : mv_nat < 2 ^ 32)]
  have hmv_toNat : mv_sw.toNat = mv_nat := Nat.mod_eq_of_lt (by omega : mv_nat < 2 ^ 32)
  dsimp only [vals, Arg.val]
  rw [show (BitVec.ofNat 64 c.scratch_cap).toNat = c.scratch_cap from Nat.mod_eq_of_lt hcap_lt]
  c0_hsteps_nogrp; rw [hmv64]
  refine wp_join_state1 (fun x : BitVec 32 => x)
    (fun x m' => x.toNat = min c.max_vars 65535 ∧ m' = m)
    (fun J_mcsz max_csz m' ⟨hmcsz, hm_eq⟩ => ?_)
    (fun J_mcsz hJm => by
      c0_hsteps
      · have hlt65 : c.max_vars < 65535 := by c0_bound
        exact hJm (BitVec.truncate 32 (BitVec.ofNat 64 c.max_vars)) m
          ⟨by simp [Nat.mod_eq_of_lt hmaxv_lt]; omega, rfl⟩
      · have hge65 : 65535 ≤ c.max_vars := by c0_bound
        exact hJm 65535#32 m ⟨by simp; omega, rfl⟩)
  rw [hm_eq]; have hmcsz_pos : 0 < max_csz.toNat := by omega
  have hmcsz_le : max_csz.toNat ≤ c.max_vars := by omega
  have htmp0 := hinv.1.core_ok.tmp_len_arr; have hbuf0 := hinv.1.scratch_ok.scratch_buf_len
  have hgu0 := hinv.1.scratch_ok.glue_used_len
  c0_hsteps_nogrp
  refine wp_join_state
    (α := BitVec 32 × Bool × Bool × BitVec 32 × List (BitVec 32) × List (BitVec 32))
    (fun (nv, de, ab, idx, _, _) => (nv, de, ab, idx, ()))
    (fun (nv, de, _ab, _, tmk, exp) m' => certL1Inv c s R mv_nat nv tmk exp m' ∧
      (de = true → (cnfOfClauses F_cur).EntailsClause (cnfClause [unit.toNat]))) ?_ ?_
  · rintro B ⟨nv, de, _ab, idx, tmk, exp⟩ m1
      ⟨⟨hnv_mv, hnv_cv, htmk_len, hexp_len, hok, hm1⟩, hde_ent⟩
    let s1 := certMkState s s.core.tmp exp tmk s.scratch.scratch_buf
    have hinv1 := cert_fullDenseInvW_mk hinv htmp0 hexp_len htmk_len hbuf0 hgu0
    c0_hsteps_nogrp
    · have hde_t : de = true := by c0_bound
      refine cert_undo_tmk_wp Γ Q X c F0 F_cur s s R s.core.tmp exp tmk s.scratch.scratch_buf
        nv m1 (certFinishUnitExpr c.hdr c.pVals unit) hinv hinv1 hnv_cv rfl
        hinv.1.core_ok.cur_vars_le hmaxv_lt htmp0 hexp_len htmk_len hbuf0 hgu0 hok hm1 ?_
      intro tmk' m2 _ htmk2 hinv2 hm2
      refine cert_finish_unit_wp Γ Q X hAssign c F0 F_cur
        (certMkState s s.core.tmp exp tmk' s.scratch.scratch_buf) R unit m2 hinv2 htmk2 hunit
        (hde_ent hde_t) hm2 ?_
      intro s3 m3 hinv3 htmk3 hcv3 har3 hal3 hfl3 hscr3 hm3
      exact hQ true s3 m3 hinv3 htmk3 hcv3 har3 hal3 (hfl3 ▸ Nat.le_refl _)
        (fun i _ => by rw [hscr3]; rfl) hm3
    · c0_hsteps_nogrp
      refine wp_join0 (fun m' => m' = m1) (fun J_ab m_ab hm_eq => by
          rw [hm_eq]; c0_hsteps_nogrp
          refine cert_undo_tmk_wp Γ Q X c F0 F_cur s s R s.core.tmp exp tmk s.scratch.scratch_buf
            nv m1 (Expr.ret (Arg.imm false, ())) hinv hinv1 hnv_cv rfl hinv.1.core_ok.cur_vars_le
            hmaxv_lt htmp0 hexp_len htmk_len hbuf0 hgu0 hok hm1 ?_
          intro tmk' m' _ htmkF hinvF hm'; c0_hsteps
          exact hQ false (certMkState s s.core.tmp exp tmk' s.scratch.scratch_buf) m' hinvF htmkF
            rfl rfl rfl (Nat.le_refl _) (fun _ _ => rfl) hm')
        (fun J_ab hJab => by
          c0_hsplit; · exact hJab m1 rfl
          c0_hsplit; · exact hJab m1 rfl
          c0_hsplit; · exact hJab m1 rfl
          c0_hsplit; · exact hJab m1 rfl
          · have hnv_nz : nv ≠ 0#32 := by c0_bound
            have hbase_ge : 4192 ≤ 1280 + 2 * mv_nat := by
              have h1 : ¬ ((1280#32 + (mv_sw <<< 1)).ult 4192#32 = true) := by c0_bound
              have hshl : (mv_sw <<< 1).toNat = 2 * mv_nat := by
                have : (mv_sw <<< 1).toNat = (mv_nat * 2) % 2 ^ 32 := by
                  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, hmv_toNat]
                omega
              have hadd : (1280#32 + (mv_sw <<< 1)).toNat = 1280 + 2 * mv_nat := by
                simp [BitVec.toNat_add, hshl]; omega
              rw [show (1280#32 + (mv_sw <<< 1)).ult 4192#32 =
                decide ((1280#32 + (mv_sw <<< 1)).toNat < 4192) from rfl,
                hadd, decide_eq_true_eq] at h1; omega
            have hmv_nz : mv_nat ≠ 0 := by omega
            have hcap_k6 : k6MinScr ≤ c.scratch_cap := Classical.byContradiction fun hlt =>
              hmv_nz (by simp [mv_nat, k6MaxV, Nat.lt_of_not_le hlt])
            have h33_gu : (BitVec.zeroExtend 64 33#32).toNat < s1.scratch.glue_used.length := by
              rw [cert_zext64_toNat]; change 33 < s.scratch.glue_used.length; omega
            clear hm; c0_hsteps
            let gu1 := s.scratch.glue_used.set 33 0xFFFFFFFF#32
            let s1g := certMkStateGu s s.core.tmp exp tmk s.scratch.scratch_buf gu1
            have hgu1_len : gu1.length = 64 := by simp [gu1, hgu0]
            have hinv1g := cert_fullDenseInvW_mk hinv htmp0 hexp_len htmk_len hbuf0 hgu1_len
            have h33_set : (gu1[33]?.getD 0#32) = 0xFFFFFFFF#32 := by
              simp [gu1, List.getElem?_set_self (by omega : 33 < s.scratch.glue_used.length)]
            let L := k6LayoutOfCap c.scratch_cap hcap_k6 c.hscr
            have hLscr : L.scrLen = c.scratch_cap := k6LayoutOfCap_scrLen hcap_k6 c.hscr
            have hLmax : L.maxV = k6MaxV c.scratch_cap := rfl
            have hm1g : (FullMem c s1g ⋆ R) m := by
              simpa only [s1g, gu1, certMkStateGu, certMkState,
                show (BitVec.ofNat 64 33).toNat = 33 from rfl,
                show (4294967295 : BitVec 32) = 0xFFFFFFFF#32 from rfl] using hm
            c0_call hInit
            refine ⟨c, s1g, R, rfl, hinv1g.1, hm1g,
              fun hbad => by omega, fun _ _ => ⟨L, hLscr, hLmax,
                Or.inl (by simp [s1g, certMkStateGu, h33_set]), ?_⟩⟩
            dsimp only
            intro scr2 gu2 m2 hlen2 hpres2 hgu2 _ _ hhwm2 hk6inv2 hts2 hknv _ hlvl _ _ _ _ _ _ _ _
              hm2
            have hLbase : 4192 ≤ L.k6Base := by rw [K6Layout.k6Base]; exact hbase_ge
            have hpres_4192_2 : ∀ i < 4192, scr2[i]? = s.scratch.scratch_buf[i]? :=
              fun i hi => hpres2 i (by omega)
            let P := certModelSet F_cur exp nv.toNat unit.toNat
            have hna_empty2 : k6AssumpLitsS L scr2 = [] := by
              have : (k6StateOfScratch L scr2).nassump = 0#32 := by assumption
              simp [k6AssumpLitsS, k6AssumpLits, this]
            c0_hsteps_nogrp
            refine wp_while_break_state (brkTs := [i32, .bool]) (lpTs := [i32, .bool])
              (β := BitVec 32 × Bool × List (BitVec 32) × List (BitVec 32) × List (BitVec 32))
              (fun (idx2, ok, _, _, _) => (idx2, ok, ()))
              (fun (_idx2, ok2, tmp', scr', gu') m' =>
                certL2Inv c s R L P nv exp tmk ok2 tmp' scr' gu' m')
              (α := BitVec 32 × Bool × List (BitVec 32) × List (BitVec 32) × List (BitVec 32))
              (fun (idx2, ok2, _, _, _) => (idx2, ok2, ()))
              (fun (idx2, _, _, _, _) => side_cnt.toNat - idx2.toNat)
              (fun (idx2, ok2, tmp', scr', gu') m' => idx2.toNat ≤ side_cnt.toNat ∧
                certL2Inv c s R L P nv exp tmk ok2 tmp' scr' gu' m') ?_ ?_ ?_
            · rintro B ⟨idx2, ok2, tmp3, scr3, gu3⟩ m3
                ⟨htmp3_len, hscr3_len, hgu3_len, hpres3, hk6_3, hm3⟩
              c0_hsteps_nogrp
              exact cert_loop2_post_wp Γ Q X hSolve hAssign c F0 F_cur s R L P tmp3 exp tmk scr3 gu3
                unit nv ok2 m3 rfl hinv htmp3_len hexp_len htmk_len hscr3_len hgu3_len hmaxv_lt
                hnv_cv hLscr hLmax hLbase hunit hok hpres3 hk6_3 hm3 hQ
            · rintro B L2 ⟨idx2, ok2, tmp', scr', gu'⟩ m' hB hL2
                ⟨hidx_le, htmp'_len, hscr'_len, hgu'_len, hpres', hk6', hm'⟩
              have hFail : ∀ {tmp_f scr_f gu_f mf}, tmp_f.length = c.max_vars →
                  scr_f.length = c.scratch_cap → gu_f.length = 64 →
                  (∀ i < 4192, scr_f[i]? = s.scratch.scratch_buf[i]?) →
                  (Full.FullMem c (certMkStateGu s tmp_f exp tmk scr_f gu_f) ⋆ R) mf →
                  B (idx2, false, ()) mf := fun {tmp_f scr_f gu_f mf} h1 h2 h3 h4 hm_f =>
                hB (idx2, false, tmp_f, scr_f, gu_f) mf
                  ⟨h1, h2, h3, h4, fun h => absurd h (by decide), hm_f⟩
              let s' := certMkStateGu s tmp' exp tmk scr' gu'; c0_hsteps_nogrp
              · have hidx_lt : idx2.toNat < side_cnt.toNat := by c0_bound
                have hok2_t : ok2 = true := by c0_bound
                rcases hk6' hok2_t with ⟨hk6inv', hts', hlvl', hknv', hna', hhwm'⟩
                refine wp_join_state (ts := [.bool])
                    (α := Bool × List (BitVec 32) × List (BitVec 32) × List (BitVec 32) × Mem 64)
                    (fun (ok_n, _, _, _, _) => (ok_n, ()))
                    (fun (ok_n, tmp_n, scr_n, gu_n, m_n) m_in =>
                      m_in = m_n ∧ certL2Inv c s R L P nv exp tmk ok_n tmp_n scr_n gu_n m_n)
                    (fun J_ok (ok_n, tmp_n, scr_n, gu_n, m_n) m_in ⟨hm_eq, hrest⟩ => by
                      rw [hm_eq]; c0_hsteps
                      exact hL2 (idx2 + 1#32, ok_n, tmp_n, scr_n, gu_n) m_n
                        (by simp [BitVec.toNat_add]; omega)
                        ⟨by simp [BitVec.toNat_add]; omega, hrest⟩)
                    (fun J_ok hJok => by
                      have hmask_idx_lt :
                          (BitVec.zeroExtend 64 (side_mask + (idx2 >>> 5#32))).toNat <
                          scr'.length := by
                        have hshr := cert_shr5_toNat idx2
                        have hm_lt : side_mask.toNat ≤ 4066 := by
                          rcases hmask with rfl | rfl <;> decide
                        rw [cert_zext64_toNat, BitVec.toNat_add, hshr]; omega
                      c0_hsteps_nogrp
                      · have hw_idx_eq : (side_off + idx2).toNat = side_off.toNat + idx2.toNat := by
                          simp [BitVec.toNat_add]; omega
                        have hw_idx_lt :
                            (BitVec.zeroExtend 64 (side_off + idx2)).toNat < scr'.length := by
                          rw [cert_zext64_toNat, hw_idx_eq]; omega
                        have hw_eq : scr'[(side_off + idx2).toNat]?.getD 0#32 =
                            s.scratch.scratch_buf[side_off.toNat + idx2.toNat]?.getD 0#32 := by
                          rw [hw_idx_eq, hpres' (side_off.toNat + idx2.toNat) (by omega)]
                        have hwe :
                            FullBveEntryOkW F_cur s unit.toNat scr'[(side_off + idx2).toNat] := by
                          rw [← cert_getElemD (by rw [← cert_zext64_toNat]; exact hw_idx_lt) 0#32,
                            hw_eq]
                          exact hent idx2.toNat hidx_lt
                        c0_hsteps_nogrp
                        refine wp_join_state (ts := [.bool])
                          (α :=
                            Bool × List (BitVec 32) × List (BitVec 32) × List (BitVec 32) × Mem 64)
                          (fun (ok_n, _, _, _, _) => (ok_n, ()))
                          (fun (ok_n, tmp_n, scr_n, gu_n, m_n) m_in => m_in = m_n ∧
                            certL2Inv c s R L P nv exp tmk ok_n tmp_n scr_n gu_n m_n)
                          (fun J_m (ok_n, tmp_n, scr_n, gu_n, m_n) m_in ⟨hm_eq, hrest⟩ => by
                            rw [hm_eq]; c0_hsteps
                            exact hJok (ok_n, tmp_n, scr_n, gu_n, m_n) m_n ⟨rfl, hrest⟩)
                          (fun J_m hJm => by
                            c0_hsteps_nogrp
                            · dsimp only
                              have hbit : scr'[(side_off + idx2).toNat] &&& 2147483648#32 ≠
                                  0#32 := by c0_bound
                              dsimp only [FullBveEntryOkW] at hwe
                              rw [ite_eq_left hbit] at hwe; rcases hwe with ⟨hot_lt, hot_ent⟩
                              have hw_buf_z : (certMkStateGu s tmp' exp tmk scr'
                                  gu').scratch.scratch_buf[(BitVec.setWidth 64
                                    (side_off + idx2)).toNat] =
                                  scr'[(side_off + idx2).toNat] :=
                                cert_list_getElem_eq (certMkStateGu_buf ..) (cert_zext64_toNat _)
                                  (by rw [certMkStateGu_buf]; exact hw_idx_lt)
                                  (by rw [cert_zext64_toNat] at hw_idx_lt; exact hw_idx_lt)
                              erw [hw_buf_z]
                              let ot := scr'[(side_off + idx2).toNat] &&& 2147483647#32
                              exact cert_loop2_unit_wp Γ Q X hAdd J_m B c F0 F_cur s R L P
                                tmp' exp tmk scr' gu' ot unit idx2 nv ok2 m' rfl
                                (by omega) hok2_t hinv
                                hmaxv_pos htmp'_len hexp_len htmk_len hscr'_len hgu'_len hLscr
                                hLmax hLbase hpres' hk6inv' hts' hlvl' hknv' hna' hhwm' hok
                                hot_lt hot_ent hm' hJm hFail
                            · let w := scr'[(side_off + idx2).toNat]
                              have hnb : w &&& 2147483648#32 = 0#32 := by dsimp only [w]; c0_bound
                              dsimp only [FullBveEntryOkW] at hwe
                              have hnb' : scr'[(side_off + idx2).toNat] &&& 2147483648#32 = 0#32 :=
                                hnb
                              rw [ite_eq_right (fun h => absurd hnb' h)] at hwe
                              rcases hwe with ⟨hwref, hwgarb⟩
                              have href_wf := hinv.2.1.arena.refs_wf w.toNat hwref
                              have har_le := hinv.1.core_ok.arena_len_le
                              have har_arr := hinv.1.core_ok.arena_len_arr
                              have hw3 := href_wf.1; have hn1 := href_wf.2.2.1
                              have hn2 := href_wf.2.2.2.1
                              have hw_idx_eq :
                                  (BitVec.zeroExtend 64 w + 2#64).toNat = w.toNat + 2 := by
                                have h2 : w.toNat < 2 ^ 32 := w.isLt
                                rw [BitVec.toNat_add, cert_zext64_toNat,
                                  show (2#64 : BitVec 64).toNat = 2 from rfl,
                                  Nat.mod_eq_of_lt (by omega)]
                              have hw_len :
                                  (BitVec.zeroExtend 64 w + 2#64).toNat < s'.core.arena.length := by
                                rw [hw_idx_eq]; dsimp only [s']; rw [certMkStateGu_arena]; omega
                              c0_hsteps_nogrp
                              have hwa2 : w.toNat + 2 < s'.core.arena.length := by
                                dsimp only [s']; rw [certMkStateGu_arena]; omega
                              let lsz := s'.core.arena[w.toNat + 2]'hwa2
                              have hlsz_eq :
                                  lsz.toNat = fullArenaClauseSizeCore s.core w.toNat := by
                                have hwa_s : w.toNat + 2 < s.core.arena.length := by omega
                                have hlsz_s : lsz = s.core.arena[w.toNat + 2] :=
                                  cert_list_getElem_eq
                                    (by dsimp only [s']; exact certMkStateGu_arena ..)
                                    rfl hwa2 hwa_s
                                rw [hlsz_s]
                                simp [fullArenaClauseSizeCore, List.getElem?_eq_getElem hwa_s]
                              have hlsz_bound : w.toNat + 3 + lsz.toNat ≤ s.core.arena.length := by
                                rw [hlsz_eq]; omega
                              have hlsz_lt_29 : lsz.toNat < 2 ^ 29 := by omega
                              refine wp_join_state (ts := [.bool, .bool, i32, i32])
                                (α :=
                                  Bool × Bool × BitVec 32 × BitVec 32 × List (BitVec 32) × Mem 64)
                                (fun (ok2_l, sat2, csz2, k2, _, _) => (ok2_l, sat2, csz2, k2, ()))
                                (fun (ok2_l, sat2, csz2, _, tmp2, m_n) m2_in => m2_in = m_n ∧
                                  tmp2.length = c.max_vars ∧
                                  (ok2_l = true → sat2 = false → csz2.toNat ≤ max_csz.toNat ∧
                                    (∀ j < csz2.toNat, (tmp2[j]?.getD 0#32).toNat < 2 * nv.toNat) ∧
                                    SemEntails P
                                      (List.map BitVec.toNat (List.take csz2.toNat tmp2))) ∧
                                  (Full.FullMem c (certMkStateGu s tmp2 exp tmk scr' gu') ⋆ R) m_n)
                                (fun J_l (ok2_l, sat2, csz2, _, tmp2, m_n) m2_in
                                    ⟨hm2_eq, htmp2_len, hsem2, hm2_mem⟩ => by
                                  subst m2_in; c0_hsteps
                                  · have hok2_lt : ok2_l = true := by c0_bound
                                    have hgoal : J_m (true, ()) m_n :=
                                      hJm (true, tmp2, scr', gu', m_n) m_n
                                        ⟨rfl, htmp2_len, hscr'_len, hgu'_len, hpres',
                                         fun _ => ⟨hk6inv', hts', hlvl', hknv', hna', hhwm'⟩,
                                         hm2_mem⟩
                                    rwa [hok2_lt]
                                  · have hok2_lt : ok2_l = true := by c0_bound
                                    have hsat2_f : sat2 = false := by c0_bound
                                    have hmcsz_65535 : max_csz.toNat ≤ 65535 := by omega
                                    rcases hsem2 hok2_lt hsat2_f with ⟨hcsz_le, hlts, hsem⟩
                                    exact cert_loop2_addCl_wp Γ Q X hAdd c F0 F_cur s R L P tmp2
                                      exp tmk scr' gu' nv (Arg.var csz2) m_n hinv htmp2_len
                                      hexp_len htmk_len
                                      hscr'_len hgu'_len hLscr hLmax hLbase hpres' hk6inv' hts'
                                      hlvl' hknv' hna' hhwm' (by dsimp only [Arg.val]; omega)
                                      (by dsimp only [Arg.val]; omega) hlts hsem hm2_mem _
                                      (fun ok_a scr_a gu_a m_a hcl2 => by
                                        c0_hsplit
                                        · c0_hsteps
                                          have hok_a : ok_a = true := by c0_bound
                                          have hgoal := hJm (true, tmp2, scr_a, gu_a, m_a) m_a
                                            ⟨rfl, hok_a ▸ hcl2⟩
                                          dsimp only at hgoal ⊢; rwa [hok2_lt]
                                        · c0_hsteps
                                          exact hFail htmp2_len hcl2.2.1 hcl2.2.2.1 hcl2.2.2.2.1
                                            hcl2.2.2.2.2.2)
                                  · have hok2_lf : ok2_l = false := by
                                      cases ok2_l with
                                      | false => rfl
                                      | true => exact absurd hc (by decide)
                                    simpa [hok2_lf] using hFail htmp2_len hscr'_len hgu'_len hpres'
                                      hm2_mem)
                                (fun Js hB3 => by
                                  have hgoal_w :
                                      (certMkStateGu s tmp' exp tmk scr' gu').scratch.scratch_buf[
                                        (BitVec.setWidth 64 (side_off + idx2)).toNat] = w :=
                                    cert_list_getElem_eq (certMkStateGu_buf ..)
                                      (cert_zext64_toNat _)
                                      (by rw [certMkStateGu_buf]; exact hw_idx_lt) (by omega)
                                  have hgoal_lsz :
                                      (certMkStateGu s tmp' exp tmk scr' gu').core.arena[
                                        (BitVec.setWidth 64 ((certMkStateGu s tmp' exp tmk
                                          scr' gu').scratch.scratch_buf[(BitVec.setWidth 64
                                            (side_off + idx2)).toNat]) + 2).toNat] = lsz :=
                                    cert_list_getElem_eq (certMkStateGu_arena ..)
                                      (by erw [hgoal_w, hw_idx_eq])
                                      (by rw [certMkStateGu_arena]; erw [hgoal_w, hw_idx_eq]; omega)
                                      hwa2
                                  dsimp -zeta only; erw [hgoal_lsz, hgoal_w]
                                  exact cert_loop2_large_wp Γ Q X Js c F0 F_cur s R tmp' exp tmk
                                    scr' gu' w lsz unit nv max_csz ok2 P m' rfl hok2_t hinv
                                    htmp'_len hexp_len htmk_len hscr'_len hgu'_len hcur_pos
                                    hmaxv_pos hnv_mv hmv_le hnv_cv hmcsz_pos hmcsz_le (by omega) hok
                                    hwref hwgarb hlsz_eq hlsz_bound hlsz_lt_29 hm' hB3))
                      · have hgoal := hJok (true, tmp', scr', gu', m') m'
                          ⟨rfl, htmp'_len, hscr'_len, hgu'_len, hpres',
                           fun _ => ⟨hk6inv', hts', hlvl', hknv', hna', hhwm'⟩, hm'⟩
                        dsimp only at hgoal ⊢; rwa [hok2_t])
              · exact hB (idx2, ok2, tmp', scr', gu') m'
                  ⟨htmp'_len, hscr'_len, hgu'_len, hpres', hk6', hm'⟩
              · exact hB (idx2, ok2, tmp', scr', gu') m'
                  ⟨htmp'_len, hscr'_len, hgu'_len, hpres', hk6', hm'⟩
            · rintro B L2 hB hL2; c0_hsteps
              exact hL2 (0#32, true, s.core.tmp, scr2, gu2) m2
                ⟨Nat.zero_le _, htmp0, hlen2.scratch_ok.scratch_buf_len,
                 hlen2.scratch_ok.glue_used_len, hpres_4192_2,
                 fun _ => ⟨hk6inv2 P, hts2, hlvl, hknv, hna_empty2, hhwm2⟩, hm2⟩)
  · intro Js hB
    exact cert_loop1_wp Γ Q X Js c F0 F_cur s R unit side_off side_cnt side_mask mv_sw max_csz m
      hmv_toNat hinv htmk hcap hmaxv_lt hcnt hoff_cnt hmask hent hm hB

end

end LeanQbe.T.Examples.Kissat.FullFidelityStep13S1
