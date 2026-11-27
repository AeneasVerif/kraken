/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S6aLiftsSpec
public import LeanQbe.T.Examples.Kissat.FullFidelityTumbleSpec
import LeanQbe.T.Examples.Kissat.FullFidelityStep13S6aProof1c0
import LeanQbe.T.Examples.Kissat.FullDimacsBodyLemmas1
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Fidelity Step 13 Shard `S6a` — `full_ingest_cl_tum` Lift (`Proof1c`)

Proves the callee-parametric `(Γ : Env)` Step-13 lift `full_ingest_cl_step13_wp` certifying
`FullFidelityTumble.fullIngestClTumSpec` over `step13AddClauseSpec` (handling `flags'` in the
`keep = 2` branch) and unchanged `kissatNextLitSpec`, `fullActivateLitFidSpec`, `fullAssignLvlSpec`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep13S6a

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full LeanQbe.T.Examples.Kissat.FullFidelityTumble
open Kraken.Bedrock2.Test

public section

open scoped FullArenaTactics FullDimacsBodyTactics
open FullArenaTactics FullDimacsBodyTactics

private theorem s6a_ingest_mark_clr_step {c : FullCfg} {tlen k : Nat} {kv32 : BitVec 32}
    {tmp' : List (BitVec 32)} {mrk'' : List (BitVec 8)}
    (htmpl : tmp'.length = c.max_vars) (hmk''l : mrk''.length = c.max_vars)
    (hklt : k < tlen) (htmv : tlen ≤ c.max_vars)
    (hkv_eq : kv32 = tmp'[k]'(by rw [htmpl]; omega))
    (hclr : ∀ v < c.max_vars, (∀ j, k ≤ j → j < tlen → (tmp'[j]?.getD 0#32).toNat / 2 ≠ v) →
      mrk''[v]?.getD 0#8 = 0#8) :
    ∀ v < c.max_vars,
      (∀ j, k + 1 ≤ j → j < tlen → (tmp'[j]?.getD 0#32).toNat / 2 ≠ v) →
      (mrk''.set (kv32.toNat / 2) 0#8)[v]?.getD 0#8 = 0#8 := by
  intro v hv hmiss
  subst hkv_eq
  by_cases hveq : v = (tmp'[k]'(by rw [htmpl]; omega)).toNat / 2
  · rw [hveq, List.getElem?_set_self (by rw [hmk''l, ← hveq]; exact hv)]; rfl
  · rw [List.getElem?_set_ne (Ne.symm hveq)]
    exact hclr v hv fun j hj1 hj2 => if hj_eq : j = k then by
      subst j; rw [List.getElem?_eq_getElem (l := tmp') (by rw [htmpl]; omega), Option.getD_some]
      exact Ne.symm hveq
    else hmiss j (by omega) hj2

private theorem s6a_ingest_keep1_prep {c : FullCfg} {F1_rel : CNF Nat}
    {F_cur : List (List Nat)} {s st_a : FullState} {l0 : BitVec 32}
    (hcv : s.core.cur_vars = c.mv) (hc_mv : c.mv ≤ c.max_vars)
    (hinv4 : FullSparseInvW c F1_rel F_cur st_a) (hF1_ent : F1_rel.Entails (cnfOfClauses F_cur))
    (hs_cv : st_a.core.cur_vars = s.core.cur_vars)
    (hs_vals : st_a.core.vals = s.core.vals)
    (hs_te : st_a.core.trail_end = s.core.trail_end)
    (hl0_lt : l0.toNat < 2 * c.mv) (hl0_un : s.core.vals[l0.toNat]?.getD 0#8 = 0#8)
    (hl0_ent : F1_rel.EntailsClause (cnfClause [l0.toNat])) :
    let F_next := [l0.toNat] :: F_cur
    FullWitnessInv c F1_rel F_next st_a.core ∧
    ¬ (st_a.core.cur_vars ≤ l0.toNat / 2 ∨ c.max_vars ≤ st_a.core.trail_end ∨
      st_a.core.vals[l0.toNat]?.getD 0#8 ≠ 0#8) := by
  let F_next := [l0.toNat] :: F_cur
  have hw4_n : FullWitnessInv c F1_rel F_next st_a.core :=
    hinv4.2.1.replace_extSound
      (extUnsatSound_of_entails_tum (varsBounded_cons_tum (fun q hq => by
        simp only [List.mem_singleton] at hq; rw [hq, hs_cv, hcv]; exact hl0_lt)
        hinv4.2.1.ext_sound.1) (entails_cnfOfClauses_cons_tum hF1_ent hl0_ent))
      (cnfOfClauses_cons_entails_tum _ _)
  have hte_lt := hw4_n.trail_end_lt_of_unassigned (by rw [hs_cv, hcv]; exact hl0_lt)
    (by rw [hs_vals]; exact hl0_un)
  refine ⟨hw4_n, ?_⟩
  rw [hs_cv, hcv, hs_vals, hs_te]
  refine not_or.mpr ⟨by omega, not_or.mpr ⟨by omega, fun h => h hl0_un⟩⟩

private theorem s6a_ingest_unit_false_cont {c : FullCfg} {s : FullState}
    {fd' : List (BitVec 32)} {revLits : List Nat} {taut_v : Bool} {tlen : Nat}
    (hfd_mono : ∀ e < c.mv, s.core.frame_dec[e]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
      fd'[e]?.getD 0xFFFFFFFF#32 = s.core.frame_dec[e]?.getD 0xFFFFFFFF#32)
    (hunit_r : ∀ l, revLits = [l] → taut_v = false ∧ tlen = 1 ∧ True)
    (hu1 : ∀ l < 2 * c.mv, revLits = [l] →
      s.core.vals[tumbleLit (decide (c.mv < c.extend_cap)) fd' l]?.getD 0#8 = 0xFF#8 →
      tlen = 1 → False) :
    ∀ vext l, 2 * c.mv ≤ vext.length → l < 2 * c.mv →
      TumbleValsRel (decide (c.mv < c.extend_cap)) c.mv s.core.frame_dec vext s.core.vals →
      revLits = [l] → vext[l]?.getD 0#8 = 0xFF#8 → False := by
  intro vext l _ hl hvr hrev hvf
  have ⟨_, ht1, _⟩ := hunit_r l hrev
  have hsf := tumbleValsRel_vals_of_vext_ff hvr hfd_mono hl hvf
  exact hu1 l hl hrev hsf ht1

private theorem s6a_ingest_unit_zero_cont {c : FullCfg} {s : FullState}
    {fd' : List (BitVec 32)} {revLits : List Nat} {taut_v : Bool} {tlen : Nat}
    (hrev_cov : decide (c.mv < c.extend_cap) = true →
      ∀ l ∈ revLits, fd'[l / 2]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32)
    (hvals_lift : ∀ vext, TumbleValsRel (decide (c.mv < c.extend_cap)) c.mv s.core.frame_dec
        vext s.core.vals →
      TumbleUnusedZero (decide (c.mv < c.extend_cap)) c.mv s.scratch.extend_len s.core.vals →
      TumbleValsRel (decide (c.mv < c.extend_cap)) c.mv fd' vext s.core.vals)
    (hunit_r : ∀ l, revLits = [l] → taut_v = false ∧ tlen = 1 ∧ True)
    (hu0 : ∀ l < 2 * c.mv, revLits = [l] →
      s.core.vals[tumbleLit (decide (c.mv < c.extend_cap)) fd' l]?.getD 0#8 = 0#8 →
      tlen = 1 → False) :
    ∀ vext l, 2 * c.mv ≤ vext.length → l < 2 * c.mv →
      TumbleValsRel (decide (c.mv < c.extend_cap)) c.mv s.core.frame_dec vext s.core.vals →
      TumbleUnusedZero (decide (c.mv < c.extend_cap)) c.mv s.scratch.extend_len s.core.vals →
      revLits = [l] → vext[l]?.getD 0#8 = 0#8 → False := by
  intro vext l _ hl hvr hunz hr hv0
  have ⟨_, ht1, _⟩ := hunit_r l hr
  have h0 := tumbleValsRel_vals_of_vext_zero (hvals_lift vext hvr hunz) hl
    (fun ht => hrev_cov ht l (by rw [hr]; exact List.mem_cons_self)) hv0
  exact hu0 l hl hr h0 ht1

private theorem s6a_ingest_q_ret {c : FullCfg} {accCnf : CNF Nat} {s : FullState}
    {cnf_ptr : BitVec 64} {cnfBytes : List UInt8} {i0 idx elen : Nat}
    {R : Mem 64 → Prop} {Q : Post [i64]} {revLits : List Nat} {fd' : List (BitVec 32)}
    (hi0_lt : i0 < idx) (hidx : idx ≤ cnfBytes.length)
    (hti_r : TumbleInv (decide (c.mv < c.extend_cap)) c.mv elen fd')
    (htc_f : TumbleCovers (decide (c.mv < c.extend_cap)) fd'
      (shiftDownCnf (accCnf.add (CNF.Clause.ofLiterals
        (revLits.reverse.map kissatLitToDimacsLiteral)))))
    (hvb_f : CnfVarsLt c.mv (shiftDownCnf (accCnf.add (CNF.Clause.ofLiterals
      (revLits.reverse.map kissatLitToDimacsLiteral)))))
    (hQ : ∀ (r : BitVec 64) (s' : FullState) (j : Nat) (m' : Mem 64),
      (∀ lit ∈ (CNF.Clause.ofLiterals
        (revLits.reverse.map kissatLitToDimacsLiteral)).literals, 1 ≤ lit.1) →
      i0 < j → j ≤ cnfBytes.length → cnfBytes.drop j = cnfBytes.drop idx →
      s'.LengthsOk c → s'.core.cur_vars = c.mv → s'.core.d_cur = cnf_ptr + BitVec.ofNat 64 j →
      s'.core.cur_level = 0 → s'.core.fuel = s.core.fuel → s'.core.oom = s.core.oom →
      s'.core.probing = s.core.probing →
      TumbleInv (decide (c.mv < c.extend_cap)) c.mv s'.scratch.extend_len s'.core.frame_dec →
      TumbleCovers (decide (c.mv < c.extend_cap)) s'.core.frame_dec
        (shiftDownCnf (accCnf.add (CNF.Clause.ofLiterals
          (revLits.reverse.map kissatLitToDimacsLiteral)))) →
      CnfVarsLt c.mv (shiftDownCnf (accCnf.add (CNF.Clause.ofLiterals
        (revLits.reverse.map kissatLitToDimacsLiteral)))) →
      (r = 1#64 ∨ r = 2#64 ∨ r = 3#64) →
      (r = 1#64 → ∃ F_cur', FullSparseInvW c (CNF.relabel (tumblePi
        (decide (c.mv < c.extend_cap)) s'.core.frame_dec) (shiftDownCnf (accCnf.add
        (CNF.Clause.ofLiterals (revLits.reverse.map kissatLitToDimacsLiteral))))) F_cur' s' ∧
        (CNF.relabel (tumblePi (decide (c.mv < c.extend_cap)) s'.core.frame_dec)
          (shiftDownCnf (accCnf.add (CNF.Clause.ofLiterals
            (revLits.reverse.map kissatLitToDimacsLiteral))))).Entails (cnfOfClauses F_cur')) →
      (r = 2#64 → (shiftDownCnf (accCnf.add (CNF.Clause.ofLiterals
        (revLits.reverse.map kissatLitToDimacsLiteral)))).Unsat) →
      (∀ vext l, 2 * c.mv ≤ vext.length → l < 2 * c.mv →
        TumbleValsRel (decide (c.mv < c.extend_cap)) c.mv s.core.frame_dec vext s.core.vals →
        TumbleUnusedZero (decide (c.mv < c.extend_cap)) c.mv s.scratch.extend_len s.core.vals →
        CNF.Clause.ofLiterals (revLits.reverse.map kissatLitToDimacsLiteral) =
          CNF.Clause.ofLiterals [kissatLitToDimacsLiteral l] → vext[l]?.getD 0#8 = 0#8 →
        r = 1#64 ∧
        TumbleValsRel (decide (c.mv < c.extend_cap)) c.mv s'.core.frame_dec
          ((vext.set l 1#8).set (l ^^^ 1) 0xFF#8) s'.core.vals ∧
        TumbleUnusedZero (decide (c.mv < c.extend_cap)) c.mv s'.scratch.extend_len s'.core.vals ∧
        s'.core.trail_end = s.core.trail_end + 1 ∧ s'.core.propagated = s.core.propagated) →
      (∀ vext l, 2 * c.mv ≤ vext.length → l < 2 * c.mv →
        TumbleValsRel (decide (c.mv < c.extend_cap)) c.mv s.core.frame_dec vext s.core.vals →
        CNF.Clause.ofLiterals (revLits.reverse.map kissatLitToDimacsLiteral) =
          CNF.Clause.ofLiterals [kissatLitToDimacsLiteral l] → vext[l]?.getD 0#8 = 0xFF#8 →
        r = 2#64) →
      (bytes cnf_ptr cnfBytes ⋆ FullMem c s' ⋆ R) m' → Q (r, ()) m')
    (hcl_pos : ∀ lit ∈ (CNF.Clause.ofLiterals
      (revLits.reverse.map kissatLitToDimacsLiteral)).literals, 1 ≤ lit.1) :
    ∀ ⦃r_out : BitVec 64⦄ ⦃st_out : FullState⦄ ⦃m_out : Mem 64⦄,
    st_out.LengthsOk c → st_out.core.cur_vars = c.mv →
    st_out.core.d_cur = cnf_ptr + BitVec.ofNat 64 idx → st_out.core.cur_level = 0 →
    st_out.core.fuel = s.core.fuel → st_out.core.oom = s.core.oom →
    st_out.core.probing = s.core.probing → st_out.core.frame_dec = fd' →
    st_out.scratch.extend_len = elen →
    (r_out = 1#64 ∨ r_out = 2#64 ∨ r_out = 3#64) →
    (r_out = 1#64 → ∃ F_cur', FullSparseInvW c (CNF.relabel
        (tumblePi (decide (c.mv < c.extend_cap)) fd') (shiftDownCnf (accCnf.add
          (CNF.Clause.ofLiterals (revLits.reverse.map kissatLitToDimacsLiteral))))) F_cur' st_out ∧
      (CNF.relabel (tumblePi (decide (c.mv < c.extend_cap)) fd')
        (shiftDownCnf (accCnf.add (CNF.Clause.ofLiterals
          (revLits.reverse.map kissatLitToDimacsLiteral))))).Entails (cnfOfClauses F_cur')) →
    (r_out = 2#64 → (shiftDownCnf (accCnf.add (CNF.Clause.ofLiterals
      (revLits.reverse.map kissatLitToDimacsLiteral)))).Unsat) →
    (∀ vext l, 2 * c.mv ≤ vext.length → l < 2 * c.mv →
      TumbleValsRel (decide (c.mv < c.extend_cap)) c.mv s.core.frame_dec vext s.core.vals →
      TumbleUnusedZero (decide (c.mv < c.extend_cap)) c.mv s.scratch.extend_len s.core.vals →
      revLits = [l] → vext[l]?.getD 0#8 = 0#8 →
      r_out = 1#64 ∧
      TumbleValsRel (decide (c.mv < c.extend_cap)) c.mv fd'
        ((vext.set l 1#8).set (l ^^^ 1) 0xFF#8) st_out.core.vals ∧
      TumbleUnusedZero (decide (c.mv < c.extend_cap)) c.mv elen st_out.core.vals ∧
      st_out.core.trail_end = s.core.trail_end + 1 ∧ st_out.core.propagated = s.core.propagated) →
    (∀ vext l, 2 * c.mv ≤ vext.length → l < 2 * c.mv →
      TumbleValsRel (decide (c.mv < c.extend_cap)) c.mv s.core.frame_dec vext s.core.vals →
      revLits = [l] → vext[l]?.getD 0#8 = 0xFF#8 → r_out = 2#64) →
    (FullMem c st_out ⋆ (bytes cnf_ptr cnfBytes ⋆ R)) m_out →
    Q (r_out, ()) m_out :=
  fun ⦃r_out st_out m_out⦄ hlo hcv_o hd_o hcl_o hfu_o hoom_o hpr_o hfd_o hel_o hdom
      hi1 hi2 hu0_o hu1_o hm_o =>
  hQ r_out st_out idx m_out hcl_pos hi0_lt hidx rfl hlo hcv_o hd_o hcl_o hfu_o hoom_o hpr_o
    (by rw [hfd_o, hel_o]; exact hti_r) (by rw [hfd_o]; exact htc_f) hvb_f hdom
    (by rw [hfd_o]; exact hi1) hi2
    (fun vext l hvl hl hvr hunz hcleq hv0 => by
      rw [hfd_o, hel_o]; exact hu0_o vext l hvl hl hvr hunz (fullIngestTum_unit_rev hcleq) hv0)
    (fun vext l hvl hl hvr hcleq hvf =>
      hu1_o vext l hvl hl hvr (fullIngestTum_unit_rev hcleq) hvf) (sep_ac hm_o)

/-- Callee-parametric `(Γ : Env)` Step-13 lift of `full_ingest_cl_tum_body` over
`step13AddClauseSpec`. -/
theorem full_ingest_cl_step13_wp (Γ : Env)
    (hLit : ∀ args m Q X, kissatNextLitSpec args m Q X →
      Γ "kissat_next_lit" [i64, i64] [i64] args m Q X)
    (hAct : ∀ args m Q X, fullActivateLitFidSpec args m Q X →
      Γ "full_activate_lit_fid" [i64, i32] [] args m Q X)
    (hAssign : ∀ args m Q X, fullAssignLvlSpec args m Q X →
      Γ "full_assign_lvl" [i64, i32, i32, i32] [] args m Q X)
    (hAddCl : ∀ args m Q X, step13AddClauseSpec args m Q X →
      Γ "full_add_clause" [i64, i32, i32, .bool] [i64] args m Q X) :
    ∀ args m Q X, fullIngestClTumSpec args m Q X →
      Func.wp Γ full_ingest_cl_tum_body args m Q X := by
  rintro ⟨h, cend, ⟨⟩⟩ m Q X
    ⟨c, accCnf, F_cur, s, cnf_ptr, cnfBytes, i0, R, rfl, rfl, hfit, hi0,
      hcv, hdcur, hcl0, hti0, htc0, hvb0, hinv, hent_init, hm, hQ⟩
  let tum : Bool := decide (c.mv < c.extend_cap)
  have hmv := c.hmv; have hmaxv := c.hmaxv; have hext_bd := c.hext
  unfold dimacsBound at hmv hmaxv hext_bd
  have hlen := hinv.1; have hcok := hlen.core_ok; have hw0 := hinv.2.1
  have hc_mv : c.mv ≤ c.max_vars := by rw [← hcv]; exact hcok.cur_vars_le
  have hm_r : (FullMem c s ⋆ (bytes cnf_ptr cnfBytes ⋆ R)) m := sep_ac hm
  refine s6a_ingest_read_loop_wp Γ hLit hfit hi0 hcv hdcur hti0 htc0 hlen hinv.2.2.1.1
    hinv.2.2.2.2.1.2 hm_r ?_
  rintro B tlen_v taut_v err_v mb
    ⟨idx, tlen, elen, revLits, mrk', tmp', fd', dcur, dval, hmb, rfl, hri, herr_p, hok_p⟩
  obtain ⟨hi_le, hidx, htlen_le, hmkl, htmpl, hfdl, hel_ge, hel_le, hti_r, htc_r, hrel_eq,
    hfd_mono, hvals_lift, hrev_lt, hrev_cov, htmp_lt, htmp_nd,
    hmrk_zero, hmrk_pos, hcov, hsub_rev, hnil_taut, hunit_r⟩ := hri
  dsimp only [ingestGroupFn]
  p_lets
  refine wp_loop_group (ts := [i32])
    (fun r2 (kv, ()) m2 => ∃ k mrk'',
      (FullMem c (ingestTumStR s dcur dval mrk'' tmp' fd' elen) ⋆ (bytes cnf_ptr cnfBytes ⋆ R)) m2 ∧
      k ≤ tlen ∧ r2 = tlen - k ∧ kv = BitVec.ofNat 32 k ∧ mrk''.length = c.max_vars ∧
      (∀ v < c.max_vars, (∀ j, k ≤ j → j < tlen → (tmp'[j]?.getD 0#32).toNat / 2 ≠ v) →
        mrk''[v]?.getD 0#8 = 0#8)) ?_ ?_
  · rintro L2 r2 ⟨kv, ⟨⟩⟩ m2 ih2 ⟨k, mrk'', hm2, hkle, rfl, rfl, hmk''l, hclr⟩
    p_lets
    have hult_k := bv32_ult_eq (a := k) (b := tlen) (by omega) (by omega)
    refine wp_head_jnz_iff (b := decide (k < tlen)) (by simpa [Arg.val_var] using hult_k) ?_
    rw [decide_eq_true_eq, decide_eq_false_iff_not]
    refine ⟨fun hklt => ?_, fun hkge => ?_⟩
    · p_lets
      rw [bv32_zext64_eq, bv32_ofNat_toNat (by omega), bv64_mul4_nat]
      have htm_bd_k : k < (ingestTumStR s dcur dval mrk'' tmp' fd' elen).core.tmp.length := by
        dsimp [ingestTumStR]; rw [htmpl]; omega
      refine wp_load_of (load_full_tmp (i := k) htm_bd_k hm2) ?_; p_lets
      let kv32 := tmp'[k]'(by rw [htmpl]; omega)
      have hkv32_st : (ingestTumStR s dcur dval mrk'' tmp' fd' elen).core.tmp[k]'htm_bd_k = kv32 :=
        rfl
      rw [hkv32_st]
      have hkvar_lt : kv32.toNat / 2 < c.mv := by
        have := htmp_lt k hklt
        rw [List.getElem?_eq_getElem (by rw [htmpl]; omega), Option.getD_some] at this
        change kv32.toNat < 2 * c.mv at this; omega
      refine wp_join_group (ts := [])
        (fun () m_in => ∃ mrk''',
          (FullMem c (ingestTumStR s dcur dval mrk''' tmp' fd' elen) ⋆
            (bytes cnf_ptr cnfBytes ⋆ R)) m_in ∧
          mrk'''.length = c.max_vars ∧
          (∀ v < c.max_vars,
            (∀ j, k + 1 ≤ j → j < tlen → (tmp'[j]?.getD 0#32).toNat / 2 ≠ v) →
            mrk'''[v]?.getD 0#8 = 0#8))
        (fun _ ⟨⟩ m_in ⟨mrk''', hm_in, hmk'''l, hclr'''⟩ => by
          p_lets; rw [bv32_add1_nat (by omega)]
          exact ih2 (tlen - (k + 1)) _ m_in (by omega)
            ⟨k + 1, mrk''', hm_in, by omega, rfl, rfl, hmk'''l, hclr'''⟩)
        (fun Jk hJk => by
          p_lets; refine wp_load_of (load_full_mv hm2) ?_; p_lets
          rw [bv32_zext64_eq, bv32_lshr1]
          have hult_kv : (BitVec.ofNat 64 (kv32.toNat / 2)).ult (BitVec.ofNat 64 c.mv) = true := by
            rw [bv_ult_eq (by omega) (by omega)]; simp [hkvar_lt]
          refine wp_head_jnz_iff (b := true) (by simpa [Arg.val_var] using hult_kv) ?_
          refine ⟨fun _ => ?_, fun h => (by cases h)⟩
          p_lets; rw [bv32_zext64_eq, bv32_lshr1]
          have hmk_bd_kv : kv32.toNat / 2 <
              (ingestTumStR s dcur dval mrk'' tmp' fd' elen).core.mrk.length := by
            dsimp [ingestTumStR]; rw [hmk''l]; omega
          obtain ⟨okm, hmm⟩ := store_full_mrk (i := kv32.toNat / 2) 0#8 hmk_bd_kv hm2
          refine ⟨okm, ?_⟩; p_lets
          have hmm' : (FullMem c (ingestTumStR s dcur dval (mrk''.set (kv32.toNat / 2) 0#8)
              tmp' fd' elen) ⋆ (bytes cnf_ptr cnfBytes ⋆ R)) _ := hmm
          exact hJk () _ ⟨mrk''.set (kv32.toNat / 2) 0#8, hmm', by simp [hmk''l],
            s6a_ingest_mark_clr_step htmpl hmk''l hklt (by omega) rfl hclr⟩)
    · have hkeq : k = tlen := by omega
      subst k
      let st2 := ingestTumStR s dcur dval mrk'' tmp' fd' elen
      have hlen2 : st2.LengthsOk c :=
        ⟨{ hcok with mrk_len := hmk''l, tmp_len_arr := htmpl, frame_dec_len := hfdl },
         { hlen.scratch_ok with extend_stk_len := hlen.scratch_ok.extend_stk_len }⟩
      have hinv2 := ingestTum_st2_inv hinv hcl0 hrel_eq rfl hlen2
        (fun v hv => hclr v hv (fun j hj1 hj2 => by omega)) hel_le rfl hent_init
      p_lets; refine wp_head_jnz_iff (b := err_v) (by c0_val_eq) ?_
      refine ⟨fun herr => ?_, fun hnoerr => ?_⟩
      · have hnone := herr_p herr; rw [hnone] at hQ; p_lets
        exact hQ st2 m2 hlen2 rfl rfl rfl (sep_ac hm2)
      · obtain ⟨hi0_lt, hdcur_eq, hpc_some⟩ := hok_p hnoerr
        subst hdcur_eq
        let cl := CNF.Clause.ofLiterals (revLits.reverse.map kissatLitToDimacsLiteral)
        have hcl_pos : ∀ lit ∈ cl.literals, 1 ≤ lit.1 := fun lit hlit => by
          simp only [cl, CNF.Clause.literals_ofLiterals, List.mem_map] at hlit
          rcases hlit with ⟨l, _, rfl⟩; simp [kissatLitToDimacsLiteral]
        rw [hpc_some] at hQ
        let F1 := shiftDownCnf (accCnf.add cl)
        let F1_rel := CNF.relabel (tumblePi tum fd') F1
        have htc_f : TumbleCovers tum fd' F1 :=
          tumbleCovers_add_clause htc_r fun ht l hl => hrev_cov ht l (List.mem_reverse.mp hl)
        have hvb_f : CnfVarsLt c.mv F1 :=
          cnfVarsLt_add_clause hvb0 fun l hl => hrev_lt l (List.mem_reverse.mp hl)
        have hF1_ent : F1_rel.Entails (cnfOfClauses F_cur) := by
          have h1 := relabel_entails_add (tumblePi tum fd') accCnf cl
          rw [hrel_eq] at h1; exact CNF.entails_trans h1 hent_init
        have hinv2_F1 := ingestTum_st2_inv hinv hcl0 hrel_eq rfl hlen2
          (fun v hv => hclr v hv (fun j hj1 hj2 => by omega)) hel_le rfl hF1_ent
        have hq_ret := s6a_ingest_q_ret hi0_lt hidx hti_r htc_f hvb_f hQ hcl_pos
        refine wp_head_jnz_iff (b := taut_v) (by c0_val_eq) ?_
        refine ⟨fun htaut => ?_, fun hntaut => ?_⟩
        · p_lets
          exact hq_ret hlen2 hcv rfl hcl0 rfl rfl rfl rfl rfl (Or.inl rfl)
            (fun _ => ⟨F_cur, hinv2_F1, hF1_ent⟩) (fun h => by cases h)
            (fun _ l _ _ _ _ hr _ => by have := (hunit_r l hr).1; rw [htaut] at this; cases this)
            (fun _ l _ _ _ hr _ => by have := (hunit_r l hr).1; rw [htaut] at this; cases this)
            hm2
        · have hF1_cl : F1_rel.EntailsClause (cnfClause ((tmp'.take tlen).map BitVec.toNat)) :=
            ingestTum_keep_cl_entails (by omega) htmpl rfl (hcov hntaut)
          p_lets
          refine wp_loop_group (ts := [i32, i32])
            (fun r3 (kp_v, iv, ()) m3 => ∃ keep i tmp'',
              (FullMem c (ingestTumStR s (cnf_ptr + BitVec.ofNat 64 idx) dval mrk''
                  tmp'' fd' elen) ⋆ (bytes cnf_ptr cnfBytes ⋆ R)) m3 ∧
              r3 = tlen - i ∧ kp_v = BitVec.ofNat 32 keep ∧ iv = BitVec.ofNat 32 i ∧
              IngestTumPruneInv c s tmp' fd' revLits tlen keep i tmp'') ?_ ?_
          · rintro L3 r3 ⟨kp_v, iv, ⟨⟩⟩ m3 ih3 ⟨keep, i, tmp'', hm3, rfl, rfl, rfl, hpi⟩
            have ⟨hk_le, hi_le3, htmp'l, htail, hkeep_un, _, _, _, hu0, hu1⟩ := hpi
            p_lets
            refine wp_head_jnz_iff (b := decide (i < tlen))
              (by simp only [Arg.val_var]; exact bv32_ult_eq (by omega) (by omega)) ?_
            rw [decide_eq_true_eq, decide_eq_false_iff_not]
            refine ⟨fun hilt => ?_, fun hige => ?_⟩
            · p_lets
              rw [bv32_zext64_eq, bv32_ofNat_toNat (by omega), bv64_mul4_nat]
              have htm_bd_i : i < (ingestTumStR s (cnf_ptr + BitVec.ofNat 64 idx) dval mrk''
                  tmp'' fd' elen).core.tmp.length := by
                dsimp [ingestTumStR]; rw [htmp'l]; omega
              refine wp_load_of (load_full_tmp (i := i) htm_bd_i hm3) ?_; p_lets
              let li := tmp''[i]'(by rw [htmp'l]; omega)
              have hli_st : (ingestTumStR s (cnf_ptr + BitVec.ofNat 64 idx) dval mrk''
                  tmp'' fd' elen).core.tmp[i]'htm_bd_i = li := rfl
              rw [hli_st]
              have hli_eq : li = tmp'[i]'(by rw [htmpl]; omega) := by
                have h1 := htail i (Nat.le_refl _) hilt
                rw [List.getElem?_eq_getElem (by rw [htmp'l]; omega),
                  List.getElem?_eq_getElem (by rw [htmpl]; omega)] at h1; exact Option.some.inj h1
              have hli_lt : li.toNat < 2 * c.mv := by
                have := htmp_lt i hilt
                rwa [List.getElem?_eq_getElem (by rw [htmpl]; omega),
                  Option.getD_some, ← hli_eq] at this
              rw [bv32_zext64_eq]
              have hv_bd_li : li.toNat < (ingestTumStR s (cnf_ptr + BitVec.ofNat 64 idx) dval mrk''
                  tmp'' fd' elen).core.vals.length := by
                dsimp [ingestTumStR]; rw [hcok.vals_len]; omega
              refine wp_load_of (load_full_vals hv_bd_li hm3) ?_; p_lets
              let lv := s.core.vals[li.toNat]'(by rw [hcok.vals_len]; omega)
              have hlv_eq : (ingestTumStR s (cnf_ptr + BitVec.ofNat 64 idx) dval mrk''
                  tmp'' fd' elen).core.vals[li.toNat]'hv_bd_li = lv := rfl
              have hlv_dom : lv = 0#8 ∨ lv = 1#8 ∨ lv = 0xFF#8 := by
                have := hw0.vals_domain li.toNat (by rw [hcv]; exact hli_lt)
                rwa [List.getElem?_eq_getElem (by rw [hcok.vals_len]; omega),
                  Option.getD_some] at this
              have hlv_getD : s.core.vals[li.toNat]?.getD 0#8 = lv := by
                rw [List.getElem?_eq_getElem (l := s.core.vals) (by rw [hcok.vals_len]; omega),
                  Option.getD_some]
              have hsgt : (0#32).slt (lv.signExtend 32) = true ↔ lv = 1#8 := i8_vals_sgt0 hlv_dom
              rw [wp_jnz]; dsimp only [Arg.val_var]; rw [hlv_eq]
              refine ⟨fun hpos => ?_, fun hnpos => ?_⟩
              · have hlv1 : lv = 1#8 := hsgt.mp hpos
                let st3 := ingestTumStR s (cnf_ptr + BitVec.ofNat 64 idx) dval mrk''
                  tmp'' fd' elen
                have hlen3 : st3.LengthsOk c :=
                  ⟨{ hlen2.core_ok with tmp_len_arr := htmp'l }, hlen2.scratch_ok⟩
                have hinv3 := ingestTum_st3_inv hinv2 hF1_ent hlen3 rfl rfl
                have hli_abs : ∀ l, revLits = [l] →
                    s.core.vals[tumbleLit tum fd' l]?.getD 0#8 = 1#8 := fun l hrev => by
                  obtain ⟨_, _, htmp0⟩ := hunit_r l hrev
                  have hi0_eq : i = 0 := by omega
                  subst hi0_eq
                  have hl_eq : li.toNat = tumbleLit tum fd' l := by
                    rw [hli_eq]; rwa [List.getElem?_eq_getElem (by rw [htmpl]; omega),
                      Option.getD_some] at htmp0
                  rw [hl_eq] at hlv_getD; exact hlv_getD.trans hlv1
                p_lets
                exact hq_ret hlen3 hcv rfl hcl0 rfl rfl rfl rfl rfl (Or.inl rfl)
                  (fun _ => ⟨F_cur, hinv3, hF1_ent⟩) (fun h => by cases h)
                  (fun vext l _ hl hvr hunz hr hv0 => by
                    have h1 := hli_abs l hr
                    have h0 := tumbleValsRel_vals_of_vext_zero (hvals_lift vext hvr hunz) hl
                      (fun ht => hrev_cov ht l (by rw [hr]; exact List.mem_cons_self)) hv0
                    rw [h1] at h0; cases h0)
                  (fun vext l _ hl hvr hr hvf => by
                    have h1 := hli_abs l hr
                    have hf := tumbleValsRel_vals_of_vext_ff hvr hfd_mono hl hvf
                    rw [h1] at hf; cases hf) hm3
              · have hlv_ne1 : lv ≠ 1#8 := fun h => by rw [hsgt.mpr h] at hnpos; cases hnpos
                refine wp_join_group
                  (fun (kp', ()) m3' => ∃ keep' tmp''',
                    (FullMem c (ingestTumStR s (cnf_ptr + BitVec.ofNat 64 idx) dval mrk''
                        tmp''' fd' elen) ⋆ (bytes cnf_ptr cnfBytes ⋆ R)) m3' ∧
                    kp' = BitVec.ofNat 32 keep' ∧
                    IngestTumPruneInv c s tmp' fd' revLits tlen keep' (i + 1) tmp''')
                  (fun _ ⟨kp', ⟨⟩⟩ m3' ⟨keep', tmp''', hm3', hkp', hpi'⟩ => by
                    subst hkp'; p_lets; rw [bv32_add1_nat (by omega)]
                    exact ih3 (tlen - (i + 1)) _ m3' (by omega)
                      ⟨keep', i + 1, tmp''', hm3', rfl, rfl, rfl, hpi'⟩)
                  (fun Jp hJp => by
                    p_lets; refine wp_head_jnz_iff (b := decide (lv = 0#8)) (by
                      simp only [Arg.val_var]; exact i8_vals_beq0 hlv_dom) ?_
                    rw [decide_eq_true_eq, decide_eq_false_iff_not]
                    refine ⟨fun hlv0 => ?_, fun hlvne0 => ?_⟩
                    · p_lets
                      rw [bv32_zext64_eq, bv32_ofNat_toNat (n := keep) (by omega), bv64_mul4_nat]
                      have htm_bd_kp : keep < (ingestTumStR s (cnf_ptr + BitVec.ofNat 64 idx)
                          dval mrk'' tmp'' fd' elen).core.tmp.length := by
                        dsimp [ingestTumStR]; rw [htmp'l]; omega
                      obtain ⟨okt, hmt⟩ := store_full_tmp (i := keep) li htm_bd_kp hm3
                      refine ⟨okt, ?_⟩; p_lets; rw [bv32_add1_nat (by omega)]
                      exact hJp _ _ ⟨keep + 1, tmp''.set keep li, hmt, rfl,
                        ingestTumPruneInv_push hc_mv hilt htlen_le htmpl htmp_nd
                          hli_eq hli_lt (hlv_getD.trans hlv0) (fun l hr => (hunit_r l hr).2.2) hpi⟩
                    · have hlv_ff : lv = 0xFF#8 := by
                        rcases hlv_dom with h | h | h
                        · exact absurd h hlvne0
                        · exact absurd h hlv_ne1
                        · exact h
                      exact hJp _ m3 ⟨keep, tmp'', hm3, rfl,
                        ingestTumPruneInv_skip hc_mv hilt htlen_le htmpl hli_eq
                          (hlv_getD.trans hlv_ff) (fun l hr => (hunit_r l hr).2.2) hpi⟩)
            · have hieq : i = tlen := by omega
              subst i
              have hF1_keep := ingestTum_keep_entails hcv hw0 hcl0 htlen_le htmpl hc_mv htmp_lt
                hF1_ent hF1_cl hpi
              let st3 := ingestTumStR s (cnf_ptr + BitVec.ofNat 64 idx) dval mrk'' tmp'' fd' elen
              have hlen3 : st3.LengthsOk c :=
                ⟨{ hlen2.core_ok with tmp_len_arr := htmp'l }, hlen2.scratch_ok⟩
              have hinv3 := ingestTum_st3_inv hinv2 hF1_ent hlen3 rfl rfl
              p_lets
              refine wp_loop_group (ts := [i32])
                (fun r4 (av, ()) m4 => ∃ a fl_a un_a sc_a,
                  let st_a : FullState :=
                    { core := { st3.core with flags := fl_a, unassigned := un_a }
                      scratch := sc_a }
                  (FullMem c st_a ⋆ (bytes cnf_ptr cnfBytes ⋆ R)) m4 ∧
                  a ≤ keep ∧ r4 = keep - a ∧ av = BitVec.ofNat 32 a ∧
                  st_a.LengthsOk c ∧ Full.FullExtScratchPres st3 st_a) ?_ ?_
              · rintro L4 r4 ⟨av, ⟨⟩⟩ m4 ih4
                  ⟨a, fl_a, un_a, sc_a, hm4, hale, rfl, rfl, hlen_a, hpres_a⟩
                let st_a : FullState :=
                  { core := { st3.core with flags := fl_a, unassigned := un_a }
                    scratch := sc_a }
                p_lets
                refine wp_head_jnz_iff (b := decide (a < keep))
                  (by simp only [Arg.val_var]; exact bv32_ult_eq (by omega) (by omega)) ?_
                rw [decide_eq_true_eq, decide_eq_false_iff_not]
                refine ⟨fun halt => ?_, fun hage => ?_⟩
                · p_lets
                  rw [bv32_zext64_eq, bv32_ofNat_toNat (n := a) (by omega), bv64_mul4_nat]
                  have htm_bd_a : a < st_a.core.tmp.length := by
                    change a < tmp''.length; rw [htmp'l]; omega
                  refine wp_load_of (load_full_tmp (i := a) htm_bd_a hm4) ?_; p_lets
                  apply wp_call_of_spec; apply hAct
                  dsimp only [fullActivateLitFidSpec, vals_nil, vals_cons, Arg.val_var]
                  refine ⟨c, st_a, bytes cnf_ptr cnfBytes ⋆ R, rfl, hlen_a, hm4,
                    fun fl_b un_b sc_b m5 hlen_b hpres_b hm5 => ?_⟩
                  p_lets; rw [bv32_add1_nat (by omega)]
                  exact ih4 (keep - (a + 1)) _ m5 (by omega)
                    ⟨a + 1, fl_b, un_b, sc_b, hm5, by omega, rfl, rfl, hlen_b,
                      ⟨hpres_b.1.trans hpres_a.1, hpres_b.2.trans hpres_a.2⟩⟩
                · have hinv4 : FullSparseInvW c F1_rel F_cur st_a :=
                    fullSparseInvW_with_act hinv3 hlen_a hpres_a
                  have hel_a : st_a.scratch.extend_len = elen := hpres_a.2
                  let hunit0_q := fun (hne1 : keep ≠ 1) =>
                    s6a_ingest_unit_zero_cont hrev_cov hvals_lift
                      (fun l hr => ⟨(hunit_r l hr).1, (hunit_r l hr).2.1, trivial⟩)
                      (fun l hl hr h0 h1 => absurd (hu0 l hl hr h0 h1).1 hne1)
                  let hunit1_q := fun (hne0 : keep ≠ 0) =>
                    s6a_ingest_unit_false_cont hfd_mono
                      (fun l hr => ⟨(hunit_r l hr).1, (hunit_r l hr).2.1, trivial⟩)
                      (fun l hl hr hsf h1 => absurd (hu1 l hl hr hsf h1) hne0)
                  p_lets
                  have hkeep0 : (BitVec.ofNat 32 keep == 0#32) = decide (keep = 0) := by
                    rw [show (0#32 : BitVec 32) = BitVec.ofNat 32 0 from rfl,
                      bv32_beq_nat_eq (by decide), bv32_ofNat_toNat (n := keep) (by omega)]
                  refine wp_head_jnz_iff (b := decide (keep = 0))
                    (by simpa [Arg.val_var] using hkeep0) ?_
                  rw [decide_eq_true_eq, decide_eq_false_iff_not]
                  refine ⟨fun hk0 => ?_, fun _ => ?_⟩
                  · subst hk0; p_lets
                    have hunsat : F1.Unsat :=
                      cnf_unsat_of_relabel_tumble hti_r htc_f hvb_f
                        (unsat_of_entails_nil (by simpa using hF1_keep))
                    exact hq_ret hlen_a hcv rfl hcl0 rfl rfl rfl rfl hel_a (Or.inr (Or.inl rfl))
                      (fun h => by cases h) (fun _ => hunsat)
                      (fun vext l hvl hl hvr hunz hr hv0 =>
                        absurd (hunit0_q (by omega) vext l hvl hl hvr hunz hr hv0) False.elim)
                      (fun _ _ _ _ _ _ _ => rfl) hm4
                  · p_lets
                    have hkeep1 : (BitVec.ofNat 32 keep == 1#32) = decide (keep = 1) := by
                      rw [show (1#32 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
                        bv32_beq_nat_eq (by decide), bv32_ofNat_toNat (n := keep) (by omega)]
                    refine wp_head_jnz_iff (b := decide (keep = 1))
                      (by simpa [Arg.val_var] using hkeep1) ?_
                    rw [decide_eq_true_eq, decide_eq_false_iff_not]
                    refine ⟨fun hk1 => ?_, fun _ => ?_⟩
                    · subst hk1; p_lets
                      have htm_bd0 : 0 < st_a.core.tmp.length := by
                        change 0 < tmp''.length; rw [htmp'l]; omega
                      refine wp_load_of (load_full_tmp (i := 0) htm_bd0 hm4) ?_; p_lets
                      let l0 := tmp''[0]'(by rw [htmp'l]; omega)
                      have hl0_st : st_a.core.tmp[0]'htm_bd0 = l0 := rfl
                      rw [hl0_st]
                      have ⟨hl0_lt, hl0_un⟩ := hkeep_un 0 (by decide)
                      rw [List.getElem?_eq_getElem (i := 0) (by rw [htmp'l]; omega),
                        Option.getD_some] at hl0_lt hl0_un
                      have hl0_ent : F1_rel.EntailsClause (cnfClause [l0.toNat]) := by
                        have htk : tmp''.take 1 = [l0] := by
                          cases tmp'' with | nil => simp at htmp'l; omega | cons _ _ => rfl
                        simpa [htk] using hF1_keep
                      obtain ⟨_, hguard_f⟩ := s6a_ingest_keep1_prep hcv hc_mv hinv4 hF1_ent rfl
                        rfl rfl hl0_lt hl0_un hl0_ent
                      apply wp_call_of_spec; apply hAssign
                      dsimp only [fullAssignLvlSpec, vals_nil, vals_cons, Arg.val_var, Arg.val_imm]
                      refine ⟨c, st_a, bytes cnf_ptr cnfBytes ⋆ R, rfl, hlen_a, hm4, ?_⟩
                      rw [ite_eq_right hguard_f]
                      intro flags' unass' phases' m5 hfl' hph' hm5; p_lets
                      have h_alvl : ((0 : BitVec 32) = 0#32) = True := eq_true rfl
                      simp only [h_alvl, ↓reduceIte] at hm5
                      let sf : FullState := { st_a with
                        core := { st_a.core with
                          vals := (st_a.core.vals.set l0.toNat 1#8).set (l0.toNat ^^^ 1) 0xFF#8
                          flags := flags', lvl := st_a.core.lvl.set (l0.toNat / 2) 0#32
                          rsns := st_a.core.rsns.set (l0.toNat / 2) 0xFFFFFFFF#32
                          trl := st_a.core.trl.set st_a.core.trail_end l0
                          trail_pos := st_a.core.trail_pos.set (l0.toNat / 2)
                            (BitVec.ofNat 32 st_a.core.trail_end)
                          trail_end := st_a.core.trail_end + 1
                          unassigned := unass', unflushed := st_a.core.unflushed + 1#64 }
                        scratch := { st_a.scratch with phases := phases' } }
                      obtain ⟨hlen_sf, hinv_sf, hFn_ent, hu_tr⟩ := ingestTum_keep1_step
                        (st_a := st_a) hcv hcl0 hlen_a hinv4 hF1_ent htmp'l (by omega) rfl hl0_lt
                        hl0_un hl0_ent rfl hfl' hph' rfl hti_r hel_ge hrev_cov hvals_lift
                        (fun l hl hr h0 =>
                          let ⟨_, htmp0⟩ := hu0 l hl hr h0 (hunit_r l hr).2.1; ⟨rfl, htmp0⟩)
                      exact hq_ret hlen_sf hcv rfl hcl0 rfl rfl rfl rfl hel_a (Or.inl rfl)
                        (fun _ => ⟨[l0.toNat] :: F_cur, hinv_sf, hFn_ent⟩) (fun h => by cases h)
                        (fun vext l hvl hl hvr hunz hrev hv0 =>
                          ⟨rfl, (hu_tr vext l hvl hl hvr hunz hrev hv0).1,
                            (hu_tr vext l hvl hl hvr hunz hrev hv0).2, rfl, rfl⟩)
                        (fun vext l hvl hl hvr hrev hvf =>
                          absurd (hunit1_q (by omega) vext l hvl hl hvr hrev hvf) False.elim) hm5
                    · have hkp_ge2 : 2 ≤ keep := by omega
                      have hkp_le_mv : keep ≤ c.max_vars := Nat.le_trans hk_le (by omega)
                      let clLits := (tmp''.take keep).map BitVec.toNat
                      let F_next := clLits :: F_cur
                      obtain ⟨hFn_ent, hw4_n, hlits_bd, hcl_nd, hcl_ent, _⟩ :=
                        ingestTum_keep2_setup (st_a := st_a) hcv hc_mv hk_le htlen_le htmp'l
                          hkeep_un hpi.2.2.2.2.2.2.1 hF1_ent hF1_keep hinv4
                      apply wp_call_of_spec; apply hAddCl
                      dsimp only [step13AddClauseSpec, vals_nil, vals_cons, Arg.val_var,
                        Arg.val_imm]
                      refine ⟨c, F1_rel, F_next, st_a, bytes cnf_ptr cnfBytes ⋆ R, rfl, hlen_a,
                        hw4_n, hinv4.2.2.2.2.2,
                        by rw [bv32_ofNat_toNat (by omega)]; exact hkp_le_mv,
                        (fun _ => by
                          rw [bv32_ofNat_toNat (by omega)]
                          exact ⟨hlits_bd,
                            by simpa [Function.comp_def, st_a, st3, ingestTumStR] using hcl_nd,
                            hcl_ent⟩),
                        hm4, ?_⟩
                      simp only [bv32_ofNat_toNat (n := keep) (by omega),
                        show ¬ (keep < 2) by omega, ↓reduceIte]
                      let hret31 (sf : FullState) (m5 : Mem 64) (hlen5 : sf.LengthsOk c)
                          (hcv5 : sf.core.cur_vars = c.mv)
                          (hd5 : sf.core.d_cur = cnf_ptr + BitVec.ofNat 64 idx)
                          (hcl5 : sf.core.cur_level = 0) (hfu5 : sf.core.fuel = s.core.fuel)
                          (hoom5 : sf.core.oom = s.core.oom)
                          (hpr5 : sf.core.probing = s.core.probing)
                          (hfd5 : sf.core.frame_dec = fd') (hel5 : sf.scratch.extend_len = elen)
                          (hinv5 : FullSparseInvW c F1_rel F_next sf)
                          (hm5 : (FullMem c sf ⋆ (bytes cnf_ptr cnfBytes ⋆ R)) m5) :
                          Q (3#64, ()) m5 ∧ Q (1#64, ()) m5 :=
                        ⟨hq_ret hlen5 hcv5 hd5 hcl5 hfu5 hoom5 hpr5 hfd5 hel5
                          (Or.inr (Or.inr rfl)) (fun h => by cases h) (fun h => by cases h)
                          (fun vext l hvl hl hvr hunz hr hv0 =>
                            absurd (hunit0_q (by omega) vext l hvl hl hvr hunz hr hv0) False.elim)
                          (fun vext l hvl hl hvr hr hvf =>
                            absurd (hunit1_q (by omega) vext l hvl hl hvr hr hvf) False.elim) hm5,
                         hq_ret hlen5 hcv5 hd5 hcl5 hfu5 hoom5 hpr5 hfd5 hel5 (Or.inl rfl)
                          (fun _ => ⟨F_next, hinv5, hFn_ent⟩) (fun h => by cases h)
                          (fun vext l hvl hl hvr hunz hr hv0 =>
                            absurd (hunit0_q (by omega) vext l hvl hl hvr hunz hr hv0) False.elim)
                          (fun vext l hvl hl hvr hr hvf =>
                            absurd (hunit1_q (by omega) vext l hvl hl hvr hr hvf) False.elim) hm5⟩
                      by_cases hkp2 : keep = 2
                      · simp only [hkp2, ↓reduceIte]
                        intro cid flags' wvec' wstk' wlen' wu' nb' wsort' m5 _ hlen5 hw5 hm5
                        let sf : FullState := { st_a with
                          core := { st_a.core with
                            flags := flags', wvec := wvec', wstk := wstk',
                            wlen := wlen', wusable := wu', num_binary := nb' }
                          scratch := { st_a.scratch with wsort := wsort' } }
                        have hret := hret31 sf m5 hlen5 hcv rfl hcl0 rfl rfl rfl rfl hel_a
                          ⟨hlen5, hw5, hinv4.2.2.1, hinv4.2.2.2.1, hinv4.2.2.2.2.1,
                            hinv4.2.2.2.2.2⟩ hm5
                        p_lets; refine wp_head_jnz_iff (b := decide (cid = 0xFFFFFFFF#64))
                          (by simp only [Arg.val_var]; exact bv64_beq_eq) ?_
                        rw [decide_eq_true_eq, decide_eq_false_iff_not]
                        exact ⟨fun _ => by p_lets; exact hret.1, fun _ => by p_lets; exact hret.2⟩
                      · simp only [hkp2, ↓reduceIte]
                        intro cid arena' alen' wvec' wstk' wlen' wu' fred' ni' nr' wsort' m5
                          _ hlen5 hw5 hsub5 hnd5 _ hm5
                        let sf : FullState := { st_a with
                          core := { st_a.core with arena := arena', arena_len := alen',
                                                   wvec := wvec', wstk := wstk', wlen := wlen',
                                                   wusable := wu', first_reducible := fred',
                                                   num_irred := ni', num_redundant := nr' }
                          scratch := { st_a.scratch with wsort := wsort' } }
                        have hret := hret31 sf m5 hlen5 hcv rfl hcl0 rfl rfl rfl rfl hel_a
                          ⟨hlen5, hw5, hinv4.2.2.1, hnd5 hinv4.2.2.2.1,
                            ⟨hinv4.2.2.2.2.1.1.of_refs_subset rfl hsub5, hinv4.2.2.2.2.1.2⟩,
                            hinv4.2.2.2.2.2⟩ hm5
                        p_lets; refine wp_head_jnz_iff (b := decide (cid = 0xFFFFFFFF#64))
                          (by simp only [Arg.val_var]; exact bv64_beq_eq) ?_
                        rw [decide_eq_true_eq, decide_eq_false_iff_not]
                        exact ⟨fun _ => by p_lets; exact hret.1, fun _ => by p_lets; exact hret.2⟩
              · intro L4 hL4; p_lets
                exact hL4 keep _ m3
                  ⟨0, st3.core.flags, st3.core.unassigned, st3.scratch, hm3,
                    Nat.zero_le _, by simp, rfl, hlen3, ⟨rfl, rfl⟩⟩
          · intro L3 hL3; p_lets
            exact hL3 tlen _ m2
              ⟨0, 0, tmp', hm2, by simp, rfl, rfl,
                ⟨Nat.le_refl _, Nat.zero_le _, htmpl, fun _ _ _ => rfl,
                  fun _ h => by omega, fun _ h => by omega, fun _ _ h => by omega,
                  fun _ h => by omega, fun _ _ _ _ h => by omega, fun _ _ _ _ h => by omega⟩⟩
  · intro L2 hL2; p_lets
    exact hL2 tlen _ mb
      ⟨0, mrk', hmb, Nat.zero_le _, by simp, rfl, hmkl,
        fun v hv hmiss => hmrk_zero v hv (fun j hj => hmiss j (Nat.zero_le _) hj)⟩

end

end LeanQbe.T.Examples.Kissat.FullFidelityStep13S6a
