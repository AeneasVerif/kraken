module

public import LeanQbe.T.Examples.Kissat.PlainSearchLemmas
public import LeanQbe.T.Examples.Kissat.PlainMinLemmas
public import LeanQbe.T.Examples.Kissat.PlainHeurLemmas
public import LeanQbe.T.Examples.Kissat.PlainPropLemmas
public import LeanQbe.T.Examples.Kissat.PlainAnalyzeLemmas
public import LeanQbe.T.Examples.Kissat.PlainIngestLemmas
public import LeanQbe.T.Examples.Kissat.PlainReduceLemmas
import LeanQbe.T.Examples.Kissat.DimacsLemmas

/-!
# Kissat `D-Plain` Top-Level `kissat_solve_bytes` Verification & Non-Vacuity Helpers (`Stage 3`)

Proves:
1. `plain_solve_core_wp`: parametric `(Γ : Env)` `Func.wp` proof of `kissat_solve_bytes_body`
   against `plainSolveBytesCoreSpec` (general soundness `0 | 10 | 20`, read-only CNF input,
   restored workspace `region`, plus deterministic unit-clause `UnitUnsatTrace`/`UnitSatTrace`
   witness clauses).
2. `plain_solve_bytes_wp`: headline parametric soundness against `plainSolveBytesSpec`.
3. Concrete UNSAT (`20#64`) and SAT (`10#64`) non-vacuity specs and `wlen = 2048` payload bridges.
4. Closed 59-function `Env.ofTable` assembly (`plainEnv_sound`, `plainEnv_noExit`,
   `plainEnv_moduleOk`, `plain_solve_bytes_correct`, `plain_unsat_nonvacuous`,
   `plain_sat_nonvacuous`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Plain

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open Kraken.Bedrock2.Test

/-! ## 1. Pure DIMACS, bit-vector, and `PlainState` helpers -/

private theorem parseClauses_vars_pos {mv : Nat} :
    ∀ {n : Nat} {acc : CNF Nat} {bs : List UInt8} {cnf : CNF Nat},
      CnfVarsPos acc → parseClauses mv n acc bs = some cnf → CnfVarsPos cnf
  | 0, acc, bs, cnf, hacc, h => by
    unfold parseClauses at h
    cases hsw : skipWsComments bs with
    | nil => rw [hsw] at h; cases Option.some.inj h; exact hacc
    | cons _ _ => rw [hsw] at h; cases h
  | n + 1, acc, bs, cnf, hacc, h => by
    unfold parseClauses at h
    cases hpc : parseClause mv bs with
    | none => rw [hpc] at h; cases h
    | some p =>
      rcases p with ⟨cl, rest⟩
      rw [hpc] at h
      exact parseClauses_vars_pos
        (cnfVarsPos_add hacc (parseClauseAux_vars_pos (by simp) hpc)) h

private theorem parseDimacs_vars_pos {bs : List UInt8} {cnf : CNF Nat}
    (h : parseDimacs bs = some cnf) : CnfVarsPos cnf := by
  unfold parseDimacs at h
  cases hh : parseHeader bs with
  | none => rw [hh] at h; cases h
  | some p =>
    rcases p with ⟨mv, nc, rest⟩
    rw [hh] at h
    exact parseClauses_vars_pos (by intro _ hc; simp at hc) h

private theorem bv64_ugt_max_sub_false {p : BitVec 64} {n : Nat}
    (hfit : p.toNat + n < 2 ^ 64) :
    ((0xFFFFFFFFFFFFFFFF#64 - p).ult (BitVec.ofNat 64 n)) = false := by
  have hp := p.isLt
  have hmax : (0xFFFFFFFFFFFFFFFF#64 : BitVec 64).toNat = 2 ^ 64 - 1 := rfl
  have hsub : 0xFFFFFFFFFFFFFFFF#64 - p = BitVec.ofNat 64 (2 ^ 64 - 1 - p.toNat) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, hmax, bv64_ofNat_toNat (by omega)]
    omega
  rw [hsub, bv_ult_eq (by omega) (by omega)]
  simp only [decide_eq_false_iff_not]; omega

private theorem bv64_and7_eq_ofNat (p : BitVec 64) :
    p &&& 7 = BitVec.ofNat 64 (p.toNat % 8) := by
  apply BitVec.eq_of_toNat_eq
  have h := BitVec.toNat_and p 7
  have h7 : (7 : BitVec 64).toNat = 7 := rfl
  rw [h7, Nat.and_two_pow_sub_one_eq_mod p.toNat 3] at h
  rw [h, bv64_ofNat_toNat (by omega)]

/-! ## 2. Parametric `Func.wp` proofs for `kissat_solve_bytes` -/

theorem plain_solve_core_wp (Γ : Env)
    (hInit : ∀ args m Q X, plainInitStateSpec args m Q X →
      Γ "plain_init_state" [i64, i64, i64, i64, i64] [.bool] args m Q X)
    (hParse : ∀ args m Q X, plainParseBodySpec args m Q X →
      Γ "plain_parse_body" [i64, i64] [i64] args m Q X)
    (hProp : ∀ args m Q X, plainPropagateSpec args m Q X →
      Γ "plain_propagate" [i64] [i64] args m Q X)
    (hLucky : ∀ args m Q X, plainLuckySpec args m Q X →
      Γ "plain_lucky" [i64] [i64] args m Q X)
    (hAnalyze : ∀ args m Q X, plainAnalyzeSpec args m Q X →
      Γ "plain_analyze" [i64] [i64] args m Q X)
    (hSwitch : ∀ args m Q X, plainSwitchModeSpec args m Q X →
      Γ "plain_switch_mode" [i64] [] args m Q X)
    (hReduce : ∀ args m Q X, plainReduceSpec args m Q X →
      Γ "plain_reduce" [i64, .bool] [i64] args m Q X)
    (hRephase : ∀ args m Q X, plainRephaseSpec args m Q X →
      Γ "plain_rephase" [i64] [] args m Q X)
    (hRestart : ∀ args m Q X, plainRestartDueSpec args m Q X →
      Γ "plain_restart_due" [i64] [i64] args m Q X)
    (hBt : ∀ args m Q X, plainBacktrackSpec args m Q X →
      Γ "plain_backtrack" [i64, i64] [] args m Q X)
    (hDecide : ∀ args m Q X, plainDecideSpec args m Q X →
      Γ "plain_decide" [i64] [i64] args m Q X)
    (hCheck : ∀ args m Q X, kissatCheckModelExactSpec args m Q X →
      Γ "kissat_check_model" [i64, i64, i64, i64, i64] [i64] args m Q X) :
    ∀ args m Q X, plainSolveBytesCoreSpec args m Q X →
      Func.wp Γ kissat_solve_bytes_body args m Q X := by
  rintro ⟨cnf_ptr, cnf_len, work_ptr, work_len, fuel, ⟨⟩⟩ m Q X
    ⟨cnfBytes, wlen, R, rfl, rfl, hcfit, hwfit, hm, hQ⟩
  unfold Func.wp kissat_solve_bytes_body; wp_unfold
  -- 1. if (fuel == 0ULL) return 0ULL
  refine ⟨fun hf0 => ?_, fun hfne => ?_⟩
  · have hfz : fuel.toNat = 0 := by rw [hf0]; rfl
    exact hQ 0#64 m (Or.inl rfl) (fun h => by cases h) (fun h => by cases h)
      (fun _ _ _ hpos => by omega) (fun _ _ _ _ _ hlt => by omega) hm
  have hfpos : 0 < fuel.toNat :=
    Nat.pos_of_ne_zero fun h0 => hfne (BitVec.eq_of_toNat_eq (by simpa using h0))
  -- 2. overflow guards
  have hnot0 : ~~~(0 : BitVec 64) = 0xFFFFFFFFFFFFFFFF#64 := rfl
  rw [hnot0, bv64_ugt_max_sub_false hcfit]
  refine ⟨(fun h => by cases h), fun _ => ?_⟩
  rw [bv64_ugt_max_sub_false hwfit]
  refine ⟨(fun h => by cases h), fun _ => ?_⟩
  -- 3. 8-byte alignment pad
  let pNat : Nat := plainAlignPad work_ptr
  have hp_lt8 : pNat < 8 := plainAlignPad_lt8 work_ptr
  refine wp_join_group (fun (pad_v, ()) m2 => pad_v = BitVec.ofNat 64 pNat ∧ m2 = m)
    (fun _ ⟨pad_v, ⟨⟩⟩ m2 ⟨hpad_v, hm2⟩ => by
      subst hpad_v m2; wp_unfold
      rw [show (768 : BitVec 64) = BitVec.ofNat 64 768 from rfl, bv_add_ofNat,
        bv_ult_eq (by omega) (by omega)]
      simp only [decide_eq_true_eq, decide_eq_false_iff_not]
      -- 4. if (work_len < pad + sizeof(PlainHdr)) return 0
      refine ⟨fun hw_small => ?_, fun hw_ok => ?_⟩
      · exact hQ 0#64 m (Or.inl rfl) (fun h => by cases h) (fun h => by cases h)
          (fun mv nc _ _ hsz _ _ _ => by unfold plainFixedBytes at hsz; omega)
          (fun mv nc _ _ _ _ hsz _ _ _ _ => by unfold plainFixedBytes at hsz; omega) hm
      · let hdr_addr : BitVec 64 := work_ptr + BitVec.ofNat 64 pNat
        let availNat : Nat := wlen - pNat
        have hav_eq : BitVec.ofNat 64 wlen - BitVec.ofNat 64 pNat =
            BitVec.ofNat 64 availNat := plain_bv64_sub_pad (by omega) (by omega)
        rw [hav_eq]
        have hhdr_fit : hdr_addr.toNat + availNat < 2 ^ 64 := by
          rw [bv_add_ofNat_toNat (by omega)]; omega
        have hsplit : (bytes cnf_ptr cnfBytes ⋆
            region hdr_addr availNat ⋆ (region work_ptr pNat ⋆ R)) m := by
          have h1 : (region work_ptr wlen ⋆ (bytes cnf_ptr cnfBytes ⋆ R)) m := sep_ac hm
          rw [← region_merge_eq (a := work_ptr) (n1 := pNat) (n2 := availNat) (n := wlen)
            (by omega) (by omega)] at h1
          exact sep_ac h1
        have hmerge_reg : ∀ m',
            (bytes cnf_ptr cnfBytes ⋆ region hdr_addr availNat ⋆
              (region work_ptr pNat ⋆ R)) m' →
            (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m' := by
          intro m' hm'
          have h1 : ((region work_ptr pNat ⋆ region hdr_addr availNat) ⋆
              (bytes cnf_ptr cnfBytes ⋆ R)) m' := sep_ac hm'
          have h2 : (region work_ptr (pNat + availNat) ⋆
              (bytes cnf_ptr cnfBytes ⋆ R)) m' :=
            sep_mono (fun _ f => pad_region_merge (by omega) f) h1
          rw [show pNat + availNat = wlen by omega] at h2
          exact sep_ac h2
        have hmerge_arena : ∀ (c : PlainCfg) (st : PlainState) (m' : Mem 64),
            c.hdr = hdr_addr → c.avail = availNat → st.LengthsOk c →
            (bytes cnf_ptr cnfBytes ⋆ PlainMem c st ⋆ (region work_ptr pNat ⋆ R)) m' →
            (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m' := by
          intro c st m' hch hca hlen hm'
          apply hmerge_reg
          have h1 : (PlainMem c st ⋆
              (bytes cnf_ptr cnfBytes ⋆ region work_ptr pNat ⋆ R)) m' := sep_ac hm'
          have h2 : (region hdr_addr availNat ⋆
              (bytes cnf_ptr cnfBytes ⋆ region work_ptr pNat ⋆ R)) m' :=
            sep_mono (fun _ f => by
              rw [← hch, ← hca]; exact PlainArenaInv.to_region ⟨hlen, f⟩) h1
          exact sep_ac h2
        -- 5. plain_init_state
        apply wp_call_of_spec; apply hInit
        dsimp only [plainInitStateSpec, vals, Arg.val]
        refine ⟨cnfBytes, region work_ptr pNat ⋆ R, rfl, hcfit,
          by simpa [hdr_addr, bv64_ofNat_toNat (by omega : availNat < 2 ^ 64)] using hhdr_fit,
          by rw [bv64_ofNat_toNat (by omega)]; omega,
          by simpa [bv64_ofNat_toNat (by omega : availNat < 2 ^ 64)] using hsplit, ?_, ?_⟩
        · intro m' hm' hfail
          wp_unfold
          have hm'_r := hmerge_reg m'
            (by simpa [bv64_ofNat_toNat (by omega : availNat < 2 ^ 64)] using hm')
          refine hQ 0#64 m' (Or.inl rfl) (fun h => by cases h) (fun h => by cases h)
            (fun mv nc i0 _ hsz _ hhdr _ => by
              have hlt := hfail mv nc (cnfBytes.drop i0) hhdr
              rw [bv64_ofNat_toNat (by omega)] at hlt; omega)
            (fun mv nc i0 _ _ _ hsz _ hhdr _ _ _ => by
              have hlt := hfail mv nc (cnfBytes.drop i0) hhdr
              rw [bv64_ofNat_toNat (by omega)] at hlt; omega) hm'_r
        · intro c s0 j0 rest0 m0 hch hca0 hhdr0 hj0 hdrop0 hinv0 hdcur0
            hal0 _ hte0 hpr0 hcl0 hfu0 _ hprob0 _ _ hoom0 hvals0 hwvec0 _ _ hm0
          have hca : c.avail = availNat := by rw [hca0, bv64_ofNat_toNat (by omega)]
          have hmv_bd := c.hmv; unfold dimacsBound at hmv_bd
          wp_unfold; rw [← hch]
          -- 6. plain_parse_body
          apply wp_call_of_spec; apply hParse
          refine ⟨c, s0, cnf_ptr, cnfBytes, j0, region work_ptr pNat ⋆ R,
            rfl, rfl, hcfit, hj0, by rwa [hdrop0], hdcur0, hcl0, hte0, hpr0, hal0,
            hoom0, hprob0, hinv0, hm0, ?_⟩
          intro pst s1 m1 hlen1 hpst_dom hfu1 hoom1 _ _ hpst20 hpst1 hsat_tr huns_tr hm1
          wp_unfold
          refine ⟨fun hp0 => ?_, fun hpne0 => ?_⟩
          · refine hQ 0#64 m1 (Or.inl rfl) (fun h => by cases h) (fun h => by cases h)
              (fun mv nc i0 _ _ _ hhdr hut => by
                rw [hhdr0] at hhdr
                rcases Prod.mk.inj (Option.some.inj hhdr) with ⟨rfl, hnc_rest⟩
                rcases Prod.mk.inj hnc_rest with ⟨rfl, hrest_eq⟩
                have h20 := huns_tr (by rw [hvals0, hdrop0, hrest_eq]; exact hut)
                rw [hp0] at h20; cases h20)
              (fun mv nc i0 vals' te' _ _ _ hhdr hst _ _ => by
                rw [hhdr0] at hhdr
                rcases Prod.mk.inj (Option.some.inj hhdr) with ⟨rfl, hnc_rest⟩
                rcases Prod.mk.inj hnc_rest with ⟨rfl, hrest_eq⟩
                have h1 := (hsat_tr vals' te'
                  (by rw [hvals0, hdrop0, hrest_eq]; exact hst)).1
                rw [hp0] at h1; cases h1)
              (hmerge_arena c s1 m1 hch hca hlen1 hm1)
          refine ⟨fun hp20 => ?_, fun hpne20 => ?_⟩
          · refine hQ 20#64 m1 (Or.inr (Or.inr rfl)) (fun _ => hpst20 hp20)
              (fun h => by cases h) (fun _ _ _ _ _ _ _ _ => rfl)
              (fun mv nc i0 vals' te' _ _ _ hhdr hst _ _ => by
                rw [hhdr0] at hhdr
                rcases Prod.mk.inj (Option.some.inj hhdr) with ⟨rfl, hnc_rest⟩
                rcases Prod.mk.inj hnc_rest with ⟨rfl, hrest_eq⟩
                have h1 := (hsat_tr vals' te'
                  (by rw [hvals0, hdrop0, hrest_eq]; exact hst)).1
                rw [hp20] at h1; cases h1)
              (hmerge_arena c s1 m1 hch hca hlen1 hm1)
          have hpst_eq1 : pst = 1#64 := by
            rcases hpst_dom with h | h | h
            · exact absurd h hpne0
            · exact h
            · exact absurd h hpne20
          obtain ⟨cnf, hparse, hinv1, hcl1⟩ := hpst1 hpst_eq1
          have hcnf_pos : CnfVarsPos cnf := parseDimacs_vars_pos hparse
          have hnot_unsat_trace :
              ¬ UnitUnsatTrace c.mv (List.replicate (2 * c.mv) 0#8) (cnfBytes.drop j0) c.nc :=
            fun hut => by
              have h20 := huns_tr (by rwa [hvals0]); rw [hpst_eq1] at h20; cases h20
          -- 7. Initial plain_propagate(h)
          have hm1_a : (PlainMem c s1 ⋆
              (bytes cnf_ptr cnfBytes ⋆ region work_ptr pNat ⋆ R)) m1 := sep_ac hm1
          apply wp_call_of_spec; apply hProp
          refine ⟨c, shiftDownCnf cnf, s1,
            bytes cnf_ptr cnfBytes ⋆ region work_ptr pNat ⋆ R,
            rfl, hinv1.core, hm1_a, ?_⟩
          intro pr0 vals2 lvl2 rsns2 trl2 tp2 te2 prop2 unfl2 wvec2 arena2 wstk2 wlen2 wu2
            fuel2 ctype2 cref2 c0_2 c1_2 oom2 heur2 m2 s2 hcore2 _ _ _ _ _ _ hpr0_dom _ hpr0_1
            hpr0_empty _ hm2
          have hinv2 : PlainInv c (shiftDownCnf cnf) s2 := ⟨hcore2, hinv1.marks⟩
          have hm2_b : (bytes cnf_ptr cnfBytes ⋆ PlainMem c s2 ⋆
              (region work_ptr pNat ⋆ R)) m2 := sep_ac hm2
          have hsat_s2 : ∀ vals' te',
              te' < fuel.toNat →
              UnitSatTrace c.mv (List.replicate (2 * c.mv) 0#8) 0
                (cnfBytes.drop j0) c.nc vals' te' →
              (∀ v < c.mv, vals'[2 * v]?.getD 0#8 ≠ 0#8) →
              runKissatCheckModel cnfBytes (vals'.map UInt8.ofBitVec) c.mv = true →
              pr0 = 0#64 ∧ s2.vals = vals' ∧ s2.trail_end = te' ∧ s2.propagated = te' ∧
              c.mv ≤ te' ∧ 0 < s2.fuel.toNat := by
            intro vals' te' hte hst hnz _
            obtain ⟨_, hvs, htes, hprs, _, hwvs⟩ := hsat_tr vals' te' (by rwa [hvals0])
            have hws0 : ∀ l < 2 * c.mv, watchSize s1 l = 0 := by
              intro l hl
              unfold watchSize
              rw [hwvs, hwvec0, List.getElem?_replicate]
              simp [show 2 * l + 1 < 4 * c.mv by omega]
            have hres := hpr0_empty hoom1 hws0 (by rw [htes, hprs, hfu1, hfu0]; omega)
            have hmv_le : c.mv ≤ te' := by
              have hle := hcore2.mv_le_te (by
                intro v hv; dsimp only [s2]; rw [hres.2.1, hvs]; exact hnz v hv)
              dsimp only [s2] at hle; rwa [hres.2.2.1, htes] at hle
            refine ⟨hres.1, by dsimp [s2]; rw [hres.2.1, hvs],
              by dsimp [s2]; rw [hres.2.2.1, htes],
              by dsimp [s2]; rw [hres.2.2.2.1, htes],
              hmv_le, ?_⟩
            dsimp only [s2]
            have hfeq := hres.2.2.2.2.2.2
            rw [htes, hprs, hfu1, hfu0] at hfeq; omega
          wp_unfold
          refine ⟨fun hpr0_2 => ?_, fun _ => ?_⟩
          · refine hQ 0#64 m2 (Or.inl rfl) (fun h => by cases h) (fun h => by cases h)
              (fun mv nc i0 _ _ _ hhdr hut => by
                rw [hhdr0] at hhdr
                rcases Prod.mk.inj (Option.some.inj hhdr) with ⟨rfl, hnc_rest⟩
                rcases Prod.mk.inj hnc_rest with ⟨rfl, hrest_eq⟩
                exact absurd (by rwa [hdrop0, hrest_eq]) hnot_unsat_trace)
              (fun mv nc i0 vals' te' hte _ _ hhdr hst hnz hcm => by
                rw [hhdr0] at hhdr
                rcases Prod.mk.inj (Option.some.inj hhdr) with ⟨rfl, hnc_rest⟩
                rcases Prod.mk.inj hnc_rest with ⟨rfl, hrest_eq⟩
                have h0 := (hsat_s2 vals' te' hte (by rwa [hdrop0, hrest_eq]) hnz hcm).1
                rw [hpr0_2] at h0; cases h0)
              (hmerge_arena c s2 m2 hch hca hcore2.lengths hm2_b)
          refine ⟨fun hpr0_1eq => ?_, fun _ => ?_⟩
          · obtain ⟨_, _, hconfl⟩ := hpr0_1 hpr0_1eq
            have huns := shiftDownCnf_unsat hcnf_pos
              (level0_unsat_of_prop_conflict hcore2 hcl1 hconfl)
            refine hQ 20#64 m2 (Or.inr (Or.inr rfl)) (fun _ => ⟨cnf, hparse, huns⟩)
              (fun h => by cases h) (fun _ _ _ _ _ _ _ _ => rfl)
              (fun mv nc i0 vals' te' hte _ _ hhdr hst hnz hcm => by
                rw [hhdr0] at hhdr
                rcases Prod.mk.inj (Option.some.inj hhdr) with ⟨rfl, hnc_rest⟩
                rcases Prod.mk.inj hnc_rest with ⟨rfl, hrest_eq⟩
                have h0 := (hsat_s2 vals' te' hte (by rwa [hdrop0, hrest_eq]) hnz hcm).1
                rw [hpr0_1eq] at h0; cases h0)
              (hmerge_arena c s2 m2 hch hca hcore2.lengths hm2_b)
          -- Helper invariant for UnitSatTrace fast path into the main CDCL loop
          let SatFast (st : PlainState) : Prop :=
            ∀ vals' te',
              te' < fuel.toNat →
              UnitSatTrace c.mv (List.replicate (2 * c.mv) 0#8) 0
                (cnfBytes.drop j0) c.nc vals' te' →
              (∀ v < c.mv, vals'[2 * v]?.getD 0#8 ≠ 0#8) →
              runKissatCheckModel cnfBytes (vals'.map UInt8.ofBitVec) c.mv = true →
              st.vals = vals' ∧ st.trail_end = te' ∧ st.propagated = te' ∧
              c.mv ≤ te' ∧ 0 < st.fuel.toNat
          have hsf2 : SatFast s2 := fun vals' te' hte hst hnz hcm =>
            (hsat_s2 vals' te' hte hst hnz hcm).2
          -- 8. Optional plain_lucky(h) block before the main loop
          refine wp_join_group
            (fun () m_pre => ∃ s_pre : PlainState,
              PlainInv c (shiftDownCnf cnf) s_pre ∧ SatFast s_pre ∧
              (bytes cnf_ptr cnfBytes ⋆ PlainMem c s_pre ⋆
                (region work_ptr pNat ⋆ R)) m_pre)
            (fun _ ⟨⟩ m_pre ⟨s_pre, hinv_pre, hsf_pre, hm_pre⟩ => by
              -- 9. Main CDCL while (true) loop, variant = st.fuel.toNat
              wp_unfold
              refine wp_loop_break_group
                (fun (res_v, ()) mb =>
                  (res_v = 0#64 ∨ res_v = 10#64 ∨ res_v = 20#64) ∧
                  (res_v = 20#64 → cnf.Unsat) ∧
                  (res_v = 10#64 → ¬ cnf.Unsat ∧ ∃ α, cnf.Sat α) ∧
                  (∀ vals' te',
                    te' < fuel.toNat →
                    UnitSatTrace c.mv (List.replicate (2 * c.mv) 0#8) 0
                      (cnfBytes.drop j0) c.nc vals' te' →
                    (∀ v < c.mv, vals'[2 * v]?.getD 0#8 ≠ 0#8) →
                    runKissatCheckModel cnfBytes (vals'.map UInt8.ofBitVec) c.mv = true →
                    res_v = 10#64) ∧
                  (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) mb)
                (fun rem () ml => ∃ st : PlainState,
                  rem = st.fuel.toNat ∧
                  PlainInv c (shiftDownCnf cnf) st ∧
                  SatFast st ∧
                  (bytes cnf_ptr cnfBytes ⋆ PlainMem c st ⋆
                    (region work_ptr pNat ⋆ R)) ml) ?_ ?_ ?_
              · rintro _ ⟨res_v, ⟨⟩⟩ mb ⟨hdom, hu, hs, hsf, hmb⟩
                wp_unfold
                exact hQ res_v mb hdom
                  (fun h20 => ⟨cnf, hparse, hu h20⟩)
                  (fun h10 => ⟨cnf, hparse, hs h10⟩)
                  (fun mv nc i0 _ _ _ hhdr hut => by
                    rw [hhdr0] at hhdr
                    rcases Prod.mk.inj (Option.some.inj hhdr) with ⟨rfl, hnc_rest⟩
                    rcases Prod.mk.inj hnc_rest with ⟨rfl, hrest_eq⟩
                    exact absurd (by rwa [hdrop0, hrest_eq]) hnot_unsat_trace)
                  (fun mv nc i0 vals' te' hte _ _ hhdr hst hnz hcm => by
                    rw [hhdr0] at hhdr
                    rcases Prod.mk.inj (Option.some.inj hhdr) with ⟨rfl, hnc_rest⟩
                    rcases Prod.mk.inj hnc_rest with ⟨rfl, hrest_eq⟩
                    exact hsf vals' te' hte (by rwa [hdrop0, hrest_eq]) hnz hcm) hmb
              · rintro B L rem ⟨⟩ ml hB ih ⟨st, rfl, hst_inv, hsf, hml⟩
                wp_unfold
                have hml_a : (PlainMem c st ⋆
                    (bytes cnf_ptr cnfBytes ⋆ region work_ptr pNat ⋆ R)) ml := sep_ac hml
                -- pr = plain_propagate(h)
                apply wp_call_of_spec; apply hProp
                refine ⟨c, shiftDownCnf cnf, st,
                  bytes cnf_ptr cnfBytes ⋆ region work_ptr pNat ⋆ R,
                  rfl, hst_inv.core, hml_a, ?_⟩
                intro pr vals3 lvl3 rsns3 trl3 tp3 te3 prop3 unfl3 wvec3 arena3 wstk3 wlen3 wu3
                  fuel3 ctype3 cref3 c0_3 c1_3 oom3 heur3 m3 s3 hcore3 _ hfu3_le _ _ _ _ hpr_dom _
                  hpr1 _ hpr_noop hm3
                have hs3_inv : PlainInv c (shiftDownCnf cnf) s3 := ⟨hcore3, hst_inv.marks⟩
                have hm3_b : (bytes cnf_ptr cnfBytes ⋆ PlainMem c s3 ⋆
                    (region work_ptr pNat ⋆ R)) m3 := sep_ac hm3
                have hsf_s3 : ∀ vals' te',
                    te' < fuel.toNat →
                    UnitSatTrace c.mv (List.replicate (2 * c.mv) 0#8) 0
                      (cnfBytes.drop j0) c.nc vals' te' →
                    (∀ v < c.mv, vals'[2 * v]?.getD 0#8 ≠ 0#8) →
                    runKissatCheckModel cnfBytes (vals'.map UInt8.ofBitVec) c.mv = true →
                    pr = 0#64 ∧ s3 = st ∧ st.vals = vals' ∧ st.trail_end = te' ∧
                    c.mv ≤ te' ∧ 0 < st.fuel.toNat := by
                  intro vals' te' hte hst hnz hcm
                  obtain ⟨hvs, htes, hprs, hmv_le, hfpos_st⟩ := hsf vals' te' hte hst hnz hcm
                  obtain ⟨hpr0', heq⟩ := hpr_noop (by omega)
                  exact ⟨hpr0', heq, hvs, htes, hmv_le, hfpos_st⟩
                wp_unfold
                -- if (pr == 2ULL) { res = 0ULL; break; }
                refine ⟨fun hpr2 => ?_, fun _ => ?_⟩
                · exact hB (0#64, ()) m3 ⟨Or.inl rfl, (fun h => by cases h),
                    (fun h => by cases h),
                    (fun vals' te' hte hst hnz hcm => by
                      have h0 := (hsf_s3 vals' te' hte hst hnz hcm).1
                      rw [hpr2] at h0; cases h0),
                    hmerge_arena c s3 m3 hch hca hcore3.lengths hm3_b⟩
                -- if (pr == 1ULL) { ... } else { ... }
                refine wp_join_group
                  (fun (_res, ()) m_next => ∃ s_next : PlainState,
                    s_next.fuel.toNat < st.fuel.toNat ∧
                    PlainInv c (shiftDownCnf cnf) s_next ∧
                    SatFast s_next ∧
                    (bytes cnf_ptr cnfBytes ⋆ PlainMem c s_next ⋆
                      (region work_ptr pNat ⋆ R)) m_next)
                  (fun _ ⟨_res, ⟨⟩⟩ m_next ⟨s_next, hlt_next, hinv_next, hsf_next, hm_next⟩ => by
                    wp_unfold
                    exact ih s_next.fuel.toNat () m_next hlt_next
                      ⟨s_next, rfl, hinv_next, hsf_next, hm_next⟩)
                  (fun J2 hJ2 => by
                    wp_unfold
                    refine ⟨fun hpr1_eq => ?_, fun _ => ?_⟩
                    · obtain ⟨hfuel_lt, _, hconfl⟩ := hpr1 hpr1_eq
                      have hsf_false : ∀ vals' te',
                          te' < fuel.toNat →
                          UnitSatTrace c.mv (List.replicate (2 * c.mv) 0#8) 0
                            (cnfBytes.drop j0) c.nc vals' te' →
                          (∀ v < c.mv, vals'[2 * v]?.getD 0#8 ≠ 0#8) →
                          runKissatCheckModel cnfBytes (vals'.map UInt8.ofBitVec) c.mv = true →
                          False := fun vals' te' hte hst hnz hcm => by
                        have h0 := (hsf_s3 vals' te' hte hst hnz hcm).1
                        rw [hpr1_eq] at h0; cases h0
                      refine ⟨_, load_arena_cur_level hm3, ?_⟩
                      have hcl_lt : s3.cur_level < 2 ^ 64 := by
                        have := hcore3.cur_level_le; have := hcore3.lengths.trail_end_le; omega
                      have hcl0_iff :
                          BitVec.ofNat 64 s3.cur_level = (0 : BitVec 64) ↔ s3.cur_level = 0 := by
                        constructor
                        · intro h; have ht := congrArg BitVec.toNat h
                          simpa [bv64_ofNat_toNat hcl_lt] using ht
                        · intro h; rw [h]; rfl
                      rw [hcl0_iff]
                      refine ⟨fun hcl0 => ?_, fun _ => ?_⟩
                      · have huns := shiftDownCnf_unsat hcnf_pos
                          (level0_unsat_of_prop_conflict hcore3 hcl0 hconfl)
                        exact hB (20#64, ()) m3 ⟨Or.inr (Or.inr rfl), fun _ => huns,
                          (fun h => by cases h),
                          fun vals' te' hte hst hnz hcm =>
                            (hsf_false vals' te' hte hst hnz hcm).elim,
                          hmerge_arena c s3 m3 hch hca hcore3.lengths hm3_b⟩
                      · apply wp_call_of_spec; apply hAnalyze
                        refine ⟨c, shiftDownCnf cnf, s3,
                          bytes cnf_ptr cnfBytes ⋆ region work_ptr pNat ⋆ R,
                          rfl, hs3_inv, analyze_confl_of_prop hconfl, hm3, ?_⟩
                        intro ast vals4 lvl4 rsns4 trl4 tp4 te4 prop4 cl4 fuel4 tc4 tl4 mrk4 tmp4
                          wvec4 arena4 alen4 wstk4 wlen4 wu4 ag4 fred4 ni4 nr4 nb4 unfl4 ctype4
                          cref4 c0_4 c1_4 oom4 mstk4 mclr4 mcl4 mcf4 heur4 m4 s4 hlen4 hast_dom
                          hfu4_le _ hast20 hast1 hm4
                        have hm4_b : (bytes cnf_ptr cnfBytes ⋆ PlainMem c s4 ⋆
                            (region work_ptr pNat ⋆ R)) m4 := sep_ac hm4
                        wp_unfold
                        refine ⟨fun ha20 => ?_, fun _ => ?_⟩
                        · have huns := shiftDownCnf_unsat hcnf_pos (hast20 ha20)
                          exact hB (20#64, ()) m4 ⟨Or.inr (Or.inr rfl), fun _ => huns,
                            (fun h => by cases h),
                            fun vals' te' hte hst hnz hcm =>
                              (hsf_false vals' te' hte hst hnz hcm).elim,
                            hmerge_arena c s4 m4 hch hca hlen4 hm4_b⟩
                        · have habort : B (0#64, ()) m4 :=
                            hB (0#64, ()) m4 ⟨Or.inl rfl, (fun h => by cases h),
                              (fun h => by cases h),
                              fun vals' te' hte hst hnz hcm =>
                                (hsf_false vals' te' hte hst hnz hcm).elim,
                              hmerge_arena c s4 m4 hch hca hlen4 hm4_b⟩
                          refine ⟨fun _ => habort, fun heq1 => ?_⟩
                          refine ⟨_, load_arena_oom hm4, fun _ => habort, fun _ => ?_⟩
                          exact hJ2 _ m4 ⟨s4, by dsimp only [s4, s3] at hfu4_le ⊢; omega,
                            (hast1 heq1).1,
                            fun vals' te' hte hst hnz hcm =>
                              (hsf_false vals' te' hte hst hnz hcm).elim, hm4_b⟩
                    · -- pr == 0: check fuel, decrement, branch on trail_end < mv
                      refine ⟨_, load_arena_fuel hm3, ?_⟩
                      refine ⟨fun hf3_0 => ?_, fun hf3_ne => ?_⟩
                      · exact hB (0#64, ()) m3 ⟨Or.inl rfl, (fun h => by cases h),
                          (fun h => by cases h),
                          (fun vals' te' hte hst hnz hcm => by
                            obtain ⟨_, heq, _, _, _, hfpos_st⟩ := hsf_s3 vals' te' hte hst hnz hcm
                            have hfz3 : s3.fuel.toNat = 0 := by rw [hf3_0]; rfl
                            rw [heq] at hfz3; omega),
                          hmerge_arena c s3 m3 hch hca hcore3.lengths hm3_b⟩
                      · have hf3_pos : 0 < s3.fuel.toNat :=
                          Nat.pos_of_ne_zero fun h0 =>
                            hf3_ne (BitVec.eq_of_toNat_eq (by simpa using h0))
                        have hf3_sub : (s3.fuel - 1).toNat = s3.fuel.toNat - 1 := by
                          rw [BitVec.toNat_sub, show (1 : BitVec 64).toNat = 1 from rfl]; omega
                        refine ⟨_, load_arena_fuel hm3, ?_⟩
                        obtain ⟨okf, hmf⟩ := store_arena_fuel (s3.fuel - 1) hm3
                        refine ⟨okf, ?_⟩
                        let s3' : PlainState := { s3 with fuel := s3.fuel - 1 }
                        have hs3'_inv : PlainInv c (shiftDownCnf cnf) s3' :=
                          plainInv_with_fuel hs3_inv (s3.fuel - 1)
                        have hf3'_lt : s3'.fuel.toNat < st.fuel.toNat := by
                          dsimp only [s3']; rw [hf3_sub]
                          dsimp only [s3] at hf3_pos ⊢; omega
                        refine ⟨_, load_arena_trail_end hmf, _, load_arena_mv hmf, ?_⟩
                        have hte_le := hcore3.lengths.trail_end_le
                        dsimp only [s3']
                        rw [bv_ult_eq (by omega) (by omega)]
                        simp only [decide_eq_true_eq, decide_eq_false_iff_not]
                        refine ⟨fun hte_lt => ?_, fun hte_ge => ?_⟩
                        · -- trail_end < mv: contradicts SatFast
                          have hsf_false : ∀ vals' te',
                              te' < fuel.toNat →
                              UnitSatTrace c.mv (List.replicate (2 * c.mv) 0#8) 0
                                (cnfBytes.drop j0) c.nc vals' te' →
                              (∀ v < c.mv, vals'[2 * v]?.getD 0#8 ≠ 0#8) →
                              runKissatCheckModel cnfBytes (vals'.map UInt8.ofBitVec) c.mv = true →
                              False := fun vals' te' hte hst hnz hcm => by
                            obtain ⟨_, heq, _, htes, hmv_le, _⟩ := hsf_s3 vals' te' hte hst hnz hcm
                            rw [heq, htes] at hte_lt; omega
                          -- plain_switch_mode(h)
                          apply wp_call_of_spec; apply hSwitch
                          refine ⟨c, s3', bytes cnf_ptr cnfBytes ⋆ region work_ptr pNat ⋆ R,
                            rfl, hs3'_inv.core.lengths, hmf, ?_⟩
                          intro heur4 m4 hok4 hm4
                          let s4 : PlainState := { s3' with heur := heur4 }
                          have hs4_inv : PlainInv c (shiftDownCnf cnf) s4 :=
                            hs3'_inv.with_heur hok4
                          -- Outer `if_join` for `if (num_redundant > 0 && ...) ... else ...`
                          refine wp_join_group (fun xs m => J2 xs m)
                            (fun _ ⟨_, ⟨⟩⟩ _ h => by wp_unfold; exact h)
                            (fun Jred hJred =>
                              -- `sc_false` for `num_redundant > 0 && conflicts >= reduce_limit`
                              wp_join_group (fun () m4' => m4' = m4)
                                (fun _ () m4' hm4' => by
                                  subst m4'
                                  -- `if_join` for `else if (stable != 0 && ...)`
                                  refine wp_join_group (fun xs m => Jred xs m)
                                    (fun _ ⟨_, ⟨⟩⟩ _ h => by wp_unfold; exact h)
                                    (fun Jrep0 hJrep0 =>
                                      -- `sc_false` for `stable != 0 && conflicts > rephase_limit`
                                      wp_join_group (fun () m4'' => m4'' = m4)
                                        (fun _ () m4'' hm4'' => by
                                          subst m4''
                                          -- `if_join` for `else if (plain_restart_due(h) != 0)`
                                          refine wp_join_group (fun xs m => Jrep0 xs m)
                                            (fun _ ⟨_, ⟨⟩⟩ _ h => by wp_unfold; exact h)
                                            (fun Jrd hJrd => by
                                              apply wp_call_of_spec; apply hRestart
                                              refine ⟨c, s4,
                                                bytes cnf_ptr cnfBytes ⋆ region work_ptr pNat ⋆ R,
                                                rfl, hs4_inv.core.lengths, hm4, ?_⟩
                                              intro rdue heur5 m5 hok5 _ hm5
                                              let s5 : PlainState := { s4 with heur := heur5 }
                                              have hs5_inv : PlainInv c (shiftDownCnf cnf) s5 :=
                                                hs4_inv.with_heur hok5
                                              wp_unfold
                                              refine ⟨fun _ => ?_, fun _ => ?_⟩
                                              · refine ⟨_, load_arena_restarts hm5, ?_⟩
                                                obtain ⟨okr, hm5'⟩ :=
                                                  store_arena_restarts (heur5.restarts + 1#64) hm5
                                                refine ⟨okr, ?_⟩
                                                let s5' : PlainState :=
                                                  { s5 with
                                                    heur :=
                                                      { heur5 with
                                                        restarts := heur5.restarts + 1#64 } }
                                                have hs5'_inv :
                                                    PlainInv c (shiftDownCnf cnf) s5' :=
                                                  hs5_inv.with_heur { hok5 with }
                                                apply wp_call_of_spec; apply hBt
                                                refine ⟨c, s5',
                                                  bytes cnf_ptr cnfBytes ⋆
                                                    region work_ptr pNat ⋆ R,
                                                  rfl, hs5'_inv.core.lengths,
                                                  hs5'_inv.core.trail_lits_lt, hm5', ?_⟩
                                                intro vals6 lvl6 rsns6 te6 prop6 heur6 m6 s6 _ _ _
                                                  _ _ hcore_fn hm6
                                                have hcore6 :=
                                                  (hcore_fn _ hs5'_inv.core (Nat.zero_le _)).1
                                                exact hJrd _ m6 (hJrep0 _ m6 (hJred _ m6
                                                  (hJ2 _ m6 ⟨s6, hf3'_lt,
                                                    ⟨hcore6, hs5'_inv.marks⟩,
                                                    fun vals' te' hte hst hnz hcm =>
                                                      (hsf_false vals' te' hte hst hnz hcm).elim,
                                                    sep_ac hm6⟩)))
                                              · -- else: plain_decide(h)
                                                apply wp_call_of_spec; apply hDecide
                                                refine ⟨c, shiftDownCnf cnf, s5,
                                                  bytes cnf_ptr cnfBytes ⋆
                                                    region work_ptr pNat ⋆ R,
                                                  rfl, hs5_inv, hm5, ?_⟩
                                                intro dst vals6 lvl6 rsns6 trl6 tp6 te6 cl6 unfl6
                                                  heur6 m6 s6 hs6_inv _ _ _ _ hm6
                                                have hm6_b :
                                                    (bytes cnf_ptr cnfBytes ⋆ PlainMem c s6 ⋆
                                                      (region work_ptr pNat ⋆ R)) m6 := sep_ac hm6
                                                wp_unfold
                                                refine ⟨fun _ => ?_, fun _ => ?_⟩
                                                · -- dst == 0: kissat_check_model
                                                  refine ⟨_, load_arena_values hm6,
                                                    _, load_arena_mv hm6, ?_⟩
                                                  have hcm_mem :=
                                                    plainMem_to_checkModel hs6_inv.core.lengths
                                                      hm6_b
                                                  apply wp_call_of_spec; apply hCheck
                                                  refine ⟨BitVec.ofNat 64 c.mv,
                                                    BitVec.ofNat 64 c.nc, s6.d_cur, s6.d_val,
                                                    cnfBytes, s6.vals.map UInt8.ofBitVec, c.mv,
                                                    PlainCheckRest c s6 ⋆
                                                      (region work_ptr pNat ⋆ R),
                                                    rfl, rfl, hcfit, by omega,
                                                    by simp [hs6_inv.core.lengths.vals_len],
                                                    by simp [hs6_inv.core.lengths.vals_len]; omega,
                                                    by simpa [sep_assoc] using hcm_mem, ?_⟩
                                                  intro ok mv' nc' cur' val' m7 hok hm7
                                                  have hm7_reg :
                                                      (bytes cnf_ptr cnfBytes ⋆
                                                        region work_ptr wlen ⋆ R) m7 :=
                                                    hmerge_reg m7 (by
                                                      dsimp only [hdr_addr]; rw [← hch, ← hca]
                                                      exact checkModel_post_to_region
                                                        hs6_inv.core.lengths
                                                        (by simpa [sep_assoc] using hm7))
                                                  refine wp_join_group
                                                    (fun (res_v, ()) m8 =>
                                                      res_v =
                                                        (if ok = (1 : BitVec 64) then 10#64
                                                         else 0#64) ∧ m8 = m7)
                                                    (fun _ ⟨res_v, ⟨⟩⟩ m8 ⟨hrv, hm8⟩ => by
                                                      subst res_v m8; wp_unfold
                                                      cases hrun : runKissatCheckModel cnfBytes
                                                          (s6.vals.map UInt8.ofBitVec) c.mv with
                                                      | false =>
                                                        rw [hrun] at hok; simp at hok; subst hok
                                                        exact hB (0#64, ()) m7 ⟨Or.inl rfl,
                                                          (fun h => by cases h),
                                                          (fun h => by cases h),
                                                          fun vals' te' hte hst hnz hcm =>
                                                            (hsf_false vals' te' hte hst hnz
                                                              hcm).elim, hm7_reg⟩
                                                      | true =>
                                                        rw [hrun] at hok; simp at hok; subst hok
                                                        obtain ⟨cnf', _, hparse', _, hnu, hsat⟩ :=
                                                          runKissatCheckModel_sound hrun
                                                        rw [hparse] at hparse'
                                                        cases Option.some.inj hparse'
                                                        exact hB (10#64, ()) m7
                                                          ⟨Or.inr (Or.inl rfl),
                                                            (fun h => by cases h),
                                                            fun _ => ⟨hnu, hsat⟩,
                                                            fun _ _ _ _ _ _ => rfl, hm7_reg⟩)
                                                    (fun Jc hJc => by
                                                      wp_unfold
                                                      exact ⟨fun h1 => hJc (10#64, ()) m7
                                                          ⟨by simp only [h1, ↓reduceIte], rfl⟩,
                                                        fun hne => hJc (0#64, ()) m7
                                                          ⟨by simp only [hne, ↓reduceIte], rfl⟩⟩)
                                                · exact hJrd _ m6 (hJrep0 _ m6 (hJred _ m6
                                                    (hJ2 _ m6 ⟨s6, hf3'_lt, hs6_inv,
                                                      fun vals' te' hte hst hnz hcm =>
                                                        (hsf_false vals' te' hte hst hnz hcm).elim,
                                                      hm6_b⟩)))))
                                        (fun Jrep hJrep => by
                                          wp_unfold
                                          refine ⟨_, load_arena_stable hm4, ?_⟩
                                          refine ⟨fun _ => ?_, fun _ => hJrep () m4 rfl⟩
                                          refine ⟨_, load_arena_conflicts hm4,
                                            _, load_arena_rephase_limit hm4, ?_⟩
                                          refine ⟨fun _ => ?_, fun _ => hJrep () m4 rfl⟩
                                          -- plain_rephase(h)
                                          apply wp_call_of_spec; apply hRephase
                                          refine ⟨c, shiftDownCnf cnf, s4,
                                            bytes cnf_ptr cnfBytes ⋆ region work_ptr pNat ⋆ R,
                                            rfl, hs4_inv, hm4, ?_⟩
                                          intro vals5 lvl5 rsns5 te5 prop5 heur5 m5 s5 hs5_inv hm5
                                          exact hJrep0 _ m5 (hJred _ m5 (hJ2 _ m5
                                            ⟨s5, hf3'_lt, hs5_inv,
                                              fun vals' te' hte hst hnz hcm =>
                                                (hsf_false vals' te' hte hst hnz hcm).elim,
                                              sep_ac hm5⟩)))))
                                (fun JredE hJredE => by
                                  wp_unfold
                                  refine ⟨_, load_arena_num_redundant hm4, ?_⟩
                                  refine ⟨fun _ => ?_, fun _ => hJredE () m4 rfl⟩
                                  refine ⟨_, load_arena_conflicts hm4,
                                    _, load_arena_reduce_limit hm4, ?_⟩
                                  refine ⟨fun _ => ?_, fun _ => hJredE () m4 rfl⟩
                                  -- plain_reduce(h, false)
                                  apply wp_call_of_spec; apply hReduce
                                  refine ⟨c, shiftDownCnf cnf, s4,
                                    bytes cnf_ptr cnfBytes ⋆ region work_ptr pNat ⋆ R,
                                    rfl, hs4_inv.core, hm4, ?_⟩
                                  intro rr vals5 lvl5 rsns5 trl5 tp5 te5 prop5 cl5 fuel5 unfl5
                                    wvec5 wstk5 arena5 alen5 wlen5 wu5 ag5 fred5 ni5 nr5 nb5
                                    ctype5 cref5 c0_5 c1_5 oom5 heur5 m5 s5 hlen5 hrr_dom
                                    hfu5_le _ hrr20 hrr1 _ hm5
                                  have hm5_b : (bytes cnf_ptr cnfBytes ⋆ PlainMem c s5 ⋆
                                      (region work_ptr pNat ⋆ R)) m5 := sep_ac hm5
                                  wp_unfold
                                  refine ⟨fun h20 => ?_, fun _ => ?_⟩
                                  · have huns := shiftDownCnf_unsat hcnf_pos (hrr20 h20)
                                    exact hB (20#64, ()) m5 ⟨Or.inr (Or.inr rfl), fun _ => huns,
                                      (fun h => by cases h),
                                      fun vals' te' hte hst hnz hcm =>
                                        (hsf_false vals' te' hte hst hnz hcm).elim,
                                      hmerge_arena c s5 m5 hch hca hlen5 hm5_b⟩
                                  · refine ⟨fun _ => hB (0#64, ()) m5 ⟨Or.inl rfl,
                                      (fun h => by cases h), (fun h => by cases h),
                                      fun vals' te' hte hst hnz hcm =>
                                        (hsf_false vals' te' hte hst hnz hcm).elim,
                                      hmerge_arena c s5 m5 hch hca hlen5 hm5_b⟩, fun h1 => ?_⟩
                                    exact hJred _ m5 (hJ2 _ m5
                                      ⟨s5, by dsimp [s5, s4] at hfu5_le ⊢; omega,
                                        ⟨(hrr1 h1).1, hs4_inv.marks⟩,
                                        fun vals' te' hte hst hnz hcm =>
                                          (hsf_false vals' te' hte hst hnz hcm).elim, hm5_b⟩)))
                        · -- trail_end >= mv: kissat_check_model (UnitSatTrace lands here)
                          have hmf_b : (bytes cnf_ptr cnfBytes ⋆ PlainMem c s3' ⋆
                              (region work_ptr pNat ⋆ R)) _ := sep_ac hmf
                          refine ⟨_, load_arena_values hmf, _, load_arena_mv hmf, ?_⟩
                          have hcm_mem := plainMem_to_checkModel hs3'_inv.core.lengths hmf_b
                          apply wp_call_of_spec; apply hCheck
                          refine ⟨BitVec.ofNat 64 c.mv, BitVec.ofNat 64 c.nc, s3'.d_cur, s3'.d_val,
                            cnfBytes, s3'.vals.map UInt8.ofBitVec, c.mv,
                            PlainCheckRest c s3' ⋆ (region work_ptr pNat ⋆ R),
                            rfl, rfl, hcfit, by omega,
                            by simp [hs3'_inv.core.lengths.vals_len],
                            by simp [hs3'_inv.core.lengths.vals_len]; omega,
                            by simpa [sep_assoc] using hcm_mem, ?_⟩
                          intro ok mv' nc' cur' val' m7 hok hm7
                          have hm7_reg :
                              (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m7 :=
                            hmerge_reg m7 (by
                              dsimp only [hdr_addr]; rw [← hch, ← hca]
                              exact checkModel_post_to_region hs3'_inv.core.lengths
                                (by simpa [sep_assoc] using hm7))
                          refine wp_join_group
                            (fun (res_v, ()) m8 =>
                              res_v = (if ok = (1 : BitVec 64) then 10#64 else 0#64) ∧ m8 = m7)
                            (fun _ ⟨res_v, ⟨⟩⟩ m8 ⟨hrv, hm8⟩ => by
                              subst res_v m8; wp_unfold
                              cases hrun : runKissatCheckModel cnfBytes
                                  (s3'.vals.map UInt8.ofBitVec) c.mv with
                              | false =>
                                rw [hrun] at hok; simp at hok; subst hok
                                refine hB (0#64, ()) m7 ⟨Or.inl rfl, (fun h => by cases h),
                                  (fun h => by cases h), ?_, hm7_reg⟩
                                intro vals' te' hte hst hnz hcm
                                obtain ⟨_, heq, hvs, _, _, _⟩ := hsf_s3 vals' te' hte hst hnz hcm
                                have hvs3 : s3'.vals = vals' := by dsimp [s3']; rw [heq, hvs]
                                rw [hvs3, hcm] at hrun; cases hrun
                              | true =>
                                rw [hrun] at hok; simp at hok; subst hok
                                obtain ⟨cnf', _, hparse', _, hnu, hsat⟩ :=
                                  runKissatCheckModel_sound hrun
                                rw [hparse] at hparse'
                                cases Option.some.inj hparse'
                                exact hB (10#64, ()) m7 ⟨Or.inr (Or.inl rfl),
                                  (fun h => by cases h), fun _ => ⟨hnu, hsat⟩,
                                  fun _ _ _ _ _ _ => rfl, hm7_reg⟩)
                            (fun Jc hJc => by
                              wp_unfold
                              exact ⟨fun h1 => hJc (10#64, ()) m7
                                  ⟨by simp only [h1, ↓reduceIte], rfl⟩,
                                fun hne => hJc (0#64, ()) m7
                                  ⟨by simp only [hne, ↓reduceIte], rfl⟩⟩))
              · intro B L _ hL; wp_unfold
                exact hL s_pre.fuel.toNat () m_pre ⟨s_pre, rfl, hinv_pre, hsf_pre, hm_pre⟩)
            (fun Jpre hJpre => by
              wp_unfold
              -- `if (h->trail_end < h->d.mv && h->fuel > 0ULL)`
              refine ⟨_, load_arena_trail_end hm2, _, load_arena_mv hm2, ?_⟩
              have hte_le := hcore2.lengths.trail_end_le
              rw [bv_ult_eq (by omega) (by omega)]
              simp only [decide_eq_true_eq, decide_eq_false_iff_not]
              refine ⟨fun hte_lt => ?_, fun _ => hJpre () m2 ⟨s2, hinv2, hsf2, hm2_b⟩⟩
              refine ⟨_, load_arena_fuel hm2, ?_⟩
              refine ⟨fun _ => ?_, fun _ => hJpre () m2 ⟨s2, hinv2, hsf2, hm2_b⟩⟩
              have hsf_false : ∀ vals' te',
                  te' < fuel.toNat →
                  UnitSatTrace c.mv (List.replicate (2 * c.mv) 0#8) 0
                    (cnfBytes.drop j0) c.nc vals' te' →
                  (∀ v < c.mv, vals'[2 * v]?.getD 0#8 ≠ 0#8) →
                  runKissatCheckModel cnfBytes (vals'.map UInt8.ofBitVec) c.mv = true →
                  False := fun vals' te' hte hst hnz hcm => by
                obtain ⟨_, htes, _, hmv_le, _⟩ := hsf2 vals' te' hte hst hnz hcm
                omega
              apply wp_call_of_spec; apply hLucky
              refine ⟨c, shiftDownCnf cnf, s2,
                bytes cnf_ptr cnfBytes ⋆ region work_ptr pNat ⋆ R,
                rfl, hinv2, hm2, ?_⟩
              intro lr vals3 lvl3 rsns3 trl3 tp3 te3 prop3 cl3 tc3 tl3 mrk3 tmp3 wvec3
                arena3 alen3 wstk3 wlen3 wu3 ag3 fred3 ni3 nr3 nb3 unfl3 fuel3 ctype3 cref3
                c0_3 c1_3 oom3 mstk3 mclr3 mcl3 mcf3 heur3 m3 s3 hlen3 hlr_dom hlr20 hlr10
                hlr0 hm3
              have hm3_b : (bytes cnf_ptr cnfBytes ⋆ PlainMem c s3 ⋆
                  (region work_ptr pNat ⋆ R)) m3 := sep_ac hm3
              wp_unfold
              refine ⟨fun h20 => ?_, fun hne20 => ?_⟩
              · have huns := shiftDownCnf_unsat hcnf_pos (hlr20 h20)
                exact hQ 20#64 m3 (Or.inr (Or.inr rfl)) (fun _ => ⟨cnf, hparse, huns⟩)
                  (fun h => by cases h) (fun _ _ _ _ _ _ _ _ => rfl)
                  (fun mv nc i0 vals' te' hte _ _ hhdr hst hnz hcm => by
                    rw [hhdr0] at hhdr
                    rcases Prod.mk.inj (Option.some.inj hhdr) with ⟨rfl, hnc_rest⟩
                    rcases Prod.mk.inj hnc_rest with ⟨rfl, hrest_eq⟩
                    exact (hsf_false vals' te' hte (by rwa [hdrop0, hrest_eq]) hnz hcm).elim)
                  (hmerge_arena c s3 m3 hch hca hlen3 hm3_b)
              · have habort : Q (0#64, ()) m3 :=
                  hQ 0#64 m3 (Or.inl rfl) (fun h => by cases h) (fun h => by cases h)
                    (fun mv nc i0 _ _ _ hhdr hut => by
                      rw [hhdr0] at hhdr
                      rcases Prod.mk.inj (Option.some.inj hhdr) with ⟨rfl, hnc_rest⟩
                      rcases Prod.mk.inj hnc_rest with ⟨rfl, hrest_eq⟩
                      exact absurd (by rwa [hdrop0, hrest_eq]) hnot_unsat_trace)
                    (fun mv nc i0 vals' te' hte _ _ hhdr hst hnz hcm => by
                      rw [hhdr0] at hhdr
                      rcases Prod.mk.inj (Option.some.inj hhdr) with ⟨rfl, hnc_rest⟩
                      rcases Prod.mk.inj hnc_rest with ⟨rfl, hrest_eq⟩
                      exact (hsf_false vals' te' hte
                        (by rwa [hdrop0, hrest_eq]) hnz hcm).elim)
                    (hmerge_arena c s3 m3 hch hca hlen3 hm3_b)
                refine ⟨fun _ => habort, fun hne2 => ?_⟩
                refine ⟨_, load_arena_oom hm3, fun _ => habort, fun _ => ?_⟩
                refine ⟨fun h10 => ?_, fun hne10 => ?_⟩
                · have hs3_inv := hlr10 h10
                  refine ⟨_, load_arena_values hm3, _, load_arena_mv hm3, ?_⟩
                  have hcm_mem := plainMem_to_checkModel hs3_inv.core.lengths hm3_b
                  apply wp_call_of_spec; apply hCheck
                  refine ⟨BitVec.ofNat 64 c.mv, BitVec.ofNat 64 c.nc, s3.d_cur,
                    s3.d_val, cnfBytes, s3.vals.map UInt8.ofBitVec, c.mv,
                    PlainCheckRest c s3 ⋆ (region work_ptr pNat ⋆ R),
                    rfl, rfl, hcfit, by omega,
                    by simp [hs3_inv.core.lengths.vals_len],
                    by simp [hs3_inv.core.lengths.vals_len]; omega,
                    by simpa [sep_assoc] using hcm_mem, ?_⟩
                  intro ok mv' nc' cur' val' m4 hok hm4
                  have hm4_reg :
                      (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m4 :=
                    hmerge_reg m4 (by
                      dsimp only [hdr_addr]; rw [← hch, ← hca]
                      exact checkModel_post_to_region hs3_inv.core.lengths
                        (by simpa [sep_assoc] using hm4))
                  refine wp_join_group
                    (fun (res_v, ()) m5 =>
                      res_v = (if ok = (1 : BitVec 64) then 10#64 else 0#64) ∧ m5 = m4)
                    (fun _ ⟨res_v, ⟨⟩⟩ m5 ⟨hrv, hm5⟩ => by
                      subst res_v m5; wp_unfold
                      cases hrun : runKissatCheckModel cnfBytes
                          (s3.vals.map UInt8.ofBitVec) c.mv with
                      | false =>
                        rw [hrun] at hok; simp at hok; subst hok
                        exact hQ 0#64 m4 (Or.inl rfl) (fun h => by cases h)
                          (fun h => by cases h)
                          (fun mv nc i0 _ _ _ hhdr hut => by
                            rw [hhdr0] at hhdr
                            rcases Prod.mk.inj (Option.some.inj hhdr) with ⟨rfl, hnc_rest⟩
                            rcases Prod.mk.inj hnc_rest with ⟨rfl, hrest_eq⟩
                            exact absurd (by rwa [hdrop0, hrest_eq]) hnot_unsat_trace)
                          (fun mv nc i0 vals' te' hte _ _ hhdr hst hnz hcm => by
                            rw [hhdr0] at hhdr
                            rcases Prod.mk.inj (Option.some.inj hhdr) with ⟨rfl, hnc_rest⟩
                            rcases Prod.mk.inj hnc_rest with ⟨rfl, hrest_eq⟩
                            exact (hsf_false vals' te' hte
                              (by rwa [hdrop0, hrest_eq]) hnz hcm).elim) hm4_reg
                      | true =>
                        rw [hrun] at hok; simp at hok; subst hok
                        obtain ⟨cnf', _, hparse', _, hnu, hsat⟩ :=
                          runKissatCheckModel_sound hrun
                        rw [hparse] at hparse'
                        cases Option.some.inj hparse'
                        exact hQ 10#64 m4 (Or.inr (Or.inl rfl))
                          (fun h => by cases h)
                          (fun _ => ⟨cnf, hparse, hnu, hsat⟩)
                          (fun mv nc i0 _ _ _ hhdr hut => by
                            rw [hhdr0] at hhdr
                            rcases Prod.mk.inj (Option.some.inj hhdr) with ⟨rfl, hnc_rest⟩
                            rcases Prod.mk.inj hnc_rest with ⟨rfl, hrest_eq⟩
                            exact absurd (by rwa [hdrop0, hrest_eq]) hnot_unsat_trace)
                          (fun _ _ _ _ _ _ _ _ _ _ _ _ => rfl) hm4_reg)
                    (fun Jc hJc => by
                      wp_unfold
                      exact ⟨fun h1 => hJc (10#64, ()) m4 ⟨by simp only [h1, ↓reduceIte], rfl⟩,
                        fun hne => hJc (0#64, ()) m4 ⟨by simp only [hne, ↓reduceIte], rfl⟩⟩)
                · have hlr_eq0 : lr = 0#64 := by
                    rcases hlr_dom with h | h | h | h
                    · exact h
                    · exact absurd h hne2
                    · exact absurd h hne10
                    · exact absurd h hne20
                  exact hJpre () m3 ⟨s3, hlr0 hlr_eq0,
                    fun vals' te' hte hst hnz hcm =>
                      (hsf_false vals' te' hte hst hnz hcm).elim, hm3_b⟩))
    (fun Jp hJp => by
      wp_unfold
      rw [bv64_and7_eq_ofNat work_ptr]
      have hmod0 :
          BitVec.ofNat 64 (work_ptr.toNat % 8) = (0 : BitVec 64) ↔ work_ptr.toNat % 8 = 0 := by
        constructor
        · intro h; have ht := congrArg BitVec.toNat h
          rwa [bv64_ofNat_toNat (by omega)] at ht
        · intro h; rw [h]; rfl
      rw [hmod0]
      refine ⟨fun hm0 => hJp (0#64, ()) m ⟨by simp [pNat, plainAlignPad, hm0], rfl⟩,
        fun hmne => ?_⟩
      have hsub : (8 : BitVec 64) - BitVec.ofNat 64 (work_ptr.toNat % 8) =
          BitVec.ofNat 64 (8 - work_ptr.toNat % 8) :=
        bv_sub_ofNat (a := 8) (b := work_ptr.toNat % 8) (by omega) (by decide)
      exact hJp _ m ⟨by rw [hsub]; simp [pNat, plainAlignPad, hmne], rfl⟩)

theorem plain_solve_bytes_wp (Γ : Env)
    (hInit : ∀ args m Q X, plainInitStateSpec args m Q X →
      Γ "plain_init_state" [i64, i64, i64, i64, i64] [.bool] args m Q X)
    (hParse : ∀ args m Q X, plainParseBodySpec args m Q X →
      Γ "plain_parse_body" [i64, i64] [i64] args m Q X)
    (hProp : ∀ args m Q X, plainPropagateSpec args m Q X →
      Γ "plain_propagate" [i64] [i64] args m Q X)
    (hLucky : ∀ args m Q X, plainLuckySpec args m Q X →
      Γ "plain_lucky" [i64] [i64] args m Q X)
    (hAnalyze : ∀ args m Q X, plainAnalyzeSpec args m Q X →
      Γ "plain_analyze" [i64] [i64] args m Q X)
    (hSwitch : ∀ args m Q X, plainSwitchModeSpec args m Q X →
      Γ "plain_switch_mode" [i64] [] args m Q X)
    (hReduce : ∀ args m Q X, plainReduceSpec args m Q X →
      Γ "plain_reduce" [i64, .bool] [i64] args m Q X)
    (hRephase : ∀ args m Q X, plainRephaseSpec args m Q X →
      Γ "plain_rephase" [i64] [] args m Q X)
    (hRestart : ∀ args m Q X, plainRestartDueSpec args m Q X →
      Γ "plain_restart_due" [i64] [i64] args m Q X)
    (hBt : ∀ args m Q X, plainBacktrackSpec args m Q X →
      Γ "plain_backtrack" [i64, i64] [] args m Q X)
    (hDecide : ∀ args m Q X, plainDecideSpec args m Q X →
      Γ "plain_decide" [i64] [i64] args m Q X)
    (hCheck : ∀ args m Q X, kissatCheckModelExactSpec args m Q X →
      Γ "kissat_check_model" [i64, i64, i64, i64, i64] [i64] args m Q X) :
    ∀ args m Q X, plainSolveBytesSpec args m Q X →
      Func.wp Γ kissat_solve_bytes_body args m Q X :=
  fun args m Q X h =>
    plain_solve_core_wp Γ hInit hParse hProp hLucky hAnalyze hSwitch hReduce hRephase hRestart hBt
      hDecide hCheck args m Q X (plainSolveBytesCoreSpec_of_spec h)

/-! ## 3. Concrete UNSAT (`20#64`) and SAT (`10#64`) non-vacuity helpers (`wlen = 2048`) -/

/-- Concrete UNSAT DIMACS input (`p cnf 1 2\n1 0\n-1 0\n`, 19 bytes). -/
@[expose] def plainNvUnsatBytes : List UInt8 :=
  [112, 32, 99, 110, 102, 32, 49, 32, 50, 10, 49, 32, 48, 10, 45, 49, 32, 48, 10]

/-- Parsed `Std.Sat.CNF Nat` for `plainNvUnsatBytes`. -/
@[expose] def plainNvUnsatCnf : CNF Nat :=
  (CNF.empty.add (CNF.Clause.ofLiterals [(1, true)])).add (CNF.Clause.ofLiterals [(1, false)])

theorem parseDimacs_plainUnsat : parseDimacs plainNvUnsatBytes = some plainNvUnsatCnf :=
  rfl

/-- Concrete SAT DIMACS input (`p cnf 1 1\n1 0\n`, 14 bytes). -/
@[expose] def plainNvSatBytes : List UInt8 :=
  [112, 32, 99, 110, 102, 32, 49, 32, 49, 10, 49, 32, 48, 10]

/-- Parsed `Std.Sat.CNF Nat` for `plainNvSatBytes`. -/
@[expose] def plainNvSatCnf : CNF Nat :=
  CNF.empty.add (CNF.Clause.ofLiterals [(1, true)])

theorem parseDimacs_plainSat : parseDimacs plainNvSatBytes = some plainNvSatCnf :=
  rfl

private theorem plainNvUnsat_header :
    parseHeader plainNvUnsatBytes = some (1, 2, plainNvUnsatBytes.drop 9) := by
  decide

private theorem plainNvUnsat_trace :
    UnitUnsatTrace 1 (List.replicate 2 0#8) (plainNvUnsatBytes.drop 9) 2 := by
  have hcl1 : parseClause 1 (plainNvUnsatBytes.drop 9) =
      some (CNF.Clause.ofLiterals [kissatLitToDimacsLiteral 0], plainNvUnsatBytes.drop 13) := rfl
  have hcl2 : parseClause 1 (plainNvUnsatBytes.drop 13) =
      some (CNF.Clause.ofLiterals [kissatLitToDimacsLiteral 1], [10]) := rfl
  have hrest : ∃ cnf, parseClauses 1 0 CNF.empty [10] = some cnf := ⟨CNF.empty, rfl⟩
  exact UnitUnsatTrace.step (l := 0) (by decide) hcl1 (by decide)
    (UnitUnsatTrace.conflict (l := 1) (by decide) hcl2 (by decide) hrest)

private theorem plainNvSat_header :
    parseHeader plainNvSatBytes = some (1, 1, plainNvSatBytes.drop 9) := by
  decide

private theorem plainNvSat_trace :
    UnitSatTrace 1 (List.replicate 2 0#8) 0 (plainNvSatBytes.drop 9) 1 [1#8, 0xFF#8] 1 := by
  have hcl1 : parseClause 1 (plainNvSatBytes.drop 9) =
      some (CNF.Clause.ofLiterals [kissatLitToDimacsLiteral 0], [10]) := rfl
  have hdone : UnitSatTrace 1 [1#8, 0xFF#8] 1 [10] 0 [1#8, 0xFF#8] 1 :=
    UnitSatTrace.done (by decide)
  exact UnitSatTrace.step (l := 0) (by decide) hcl1 (by decide) (by simpa using hdone)

private theorem plainNvSat_checkModel :
    runKissatCheckModel plainNvSatBytes ([1#8, 0xFF#8].map UInt8.ofBitVec) 1 = true := by
  decide

/-- Concrete UNSAT witness contract (`plainNvUnsatBytes`, `work_len = 2048`, `fuel = 16`). -/
@[expose] def plainUnsatWitnessSpec : Spec [i64, i64, i64, i64, i64] [i64] :=
  fun (cnf_ptr, cnf_len, work_ptr, work_len, fuel, ()) m Q _ =>
    ∃ R : Mem 64 → Prop,
      cnf_len = BitVec.ofNat 64 plainNvUnsatBytes.length ∧
      work_len = 2048#64 ∧
      fuel = 16#64 ∧
      cnf_ptr.toNat + plainNvUnsatBytes.length < 2 ^ 64 ∧
      work_ptr.toNat + 2048 < 2 ^ 64 ∧
      (bytes cnf_ptr plainNvUnsatBytes ⋆ region work_ptr 2048 ⋆ R) m ∧
      ∀ m', plainNvUnsatCnf.Unsat →
        (bytes cnf_ptr plainNvUnsatBytes ⋆ region work_ptr 2048 ⋆ R) m' →
        Q (20#64, ()) m'

theorem plainCoreSpec_of_unsat
    {args : Tup Val [i64, i64, i64, i64, i64]} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (h : plainUnsatWitnessSpec args m Q X) :
    plainSolveBytesCoreSpec args m Q X := by
  obtain ⟨R, hcl, hwl, hfu, hcfit, hwfit, hm, hQ⟩ := h
  refine ⟨plainNvUnsatBytes, 2048, R, hcl, hwl, hcfit, hwfit, hm,
    fun r m' _ hu _ huns_w _ hm' => ?_⟩
  have hr20 : r = 20#64 :=
    huns_w 1 2 9 (by rw [hfu]; decide)
      (by unfold plainFixedBytes valsBytes markBytes u32VarBytes plainMinDepthOf; decide)
      (by decide) plainNvUnsat_header plainNvUnsat_trace
  subst hr20
  obtain ⟨cnf, hparse, huns⟩ := hu rfl
  rw [parseDimacs_plainUnsat] at hparse
  cases Option.some.inj hparse
  exact hQ m' huns hm'

/-- Concrete SAT witness contract (`plainNvSatBytes`, `work_len = 2048`, `fuel = 16`). -/
@[expose] def plainSatWitnessSpec : Spec [i64, i64, i64, i64, i64] [i64] :=
  fun (cnf_ptr, cnf_len, work_ptr, work_len, fuel, ()) m Q _ =>
    ∃ R : Mem 64 → Prop,
      cnf_len = BitVec.ofNat 64 plainNvSatBytes.length ∧
      work_len = 2048#64 ∧
      fuel = 16#64 ∧
      cnf_ptr.toNat + plainNvSatBytes.length < 2 ^ 64 ∧
      work_ptr.toNat + 2048 < 2 ^ 64 ∧
      (bytes cnf_ptr plainNvSatBytes ⋆ region work_ptr 2048 ⋆ R) m ∧
      ∀ m', ¬ plainNvSatCnf.Unsat → (∃ α, plainNvSatCnf.Sat α) →
        (bytes cnf_ptr plainNvSatBytes ⋆ region work_ptr 2048 ⋆ R) m' →
        Q (10#64, ()) m'

theorem plainCoreSpec_of_sat
    {args : Tup Val [i64, i64, i64, i64, i64]} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (h : plainSatWitnessSpec args m Q X) :
    plainSolveBytesCoreSpec args m Q X := by
  obtain ⟨R, hcl, hwl, hfu, hcfit, hwfit, hm, hQ⟩ := h
  refine ⟨plainNvSatBytes, 2048, R, hcl, hwl, hcfit, hwfit, hm,
    fun r m' _ _ hs _ hsat_w hm' => ?_⟩
  have hr10 : r = 10#64 :=
    hsat_w 1 1 9 [1#8, 0xFF#8] 1 (by rw [hfu]; decide)
      (by unfold plainFixedBytes valsBytes markBytes u32VarBytes plainMinDepthOf; decide)
      (by decide) plainNvSat_header plainNvSat_trace
      (fun v hv => by rw [show v = 0 by omega]; decide)
      plainNvSat_checkModel
  subst hr10
  obtain ⟨cnf, hparse, hnu, hsat⟩ := hs rfl
  rw [parseDimacs_plainSat] at hparse
  cases Option.some.inj hparse
  exact hQ m' hnu hsat hm'

abbrev plainNvCnfPtr : BitVec 64 := 0x1000#64
abbrev plainNvWorkPtr (cnfBytes : List UInt8) : BitVec 64 :=
  plainNvCnfPtr + BitVec.ofNat 64 cnfBytes.length

@[expose] def plainPayload (cnfBytes : List UInt8) : List UInt8 :=
  cnfBytes ++ List.replicate 2048 0

theorem plainPayload_length (cnfBytes : List UInt8) :
    (plainPayload cnfBytes).length = cnfBytes.length + 2048 := by
  simp only [plainPayload, List.length_append, List.length_replicate]

theorem plainPayload_sep (cnfBytes : List UInt8) (hcb : cnfBytes.length ≤ 4096) :
    (bytes plainNvCnfPtr cnfBytes ⋆ region (plainNvWorkPtr cnfBytes) 2048)
      ((plainPayload cnfBytes).At plainNvCnfPtr) := by
  have h2048 : (List.replicate 2048 (0 : UInt8)).length = 2048 := List.length_replicate
  have h1 := Mem.At_append_sep cnfBytes (List.replicate 2048 0) plainNvCnfPtr
    (by simp only [h2048]; omega)
  have h0 : (Eq ((cnfBytes ++ List.replicate 2048 0).At plainNvCnfPtr))
      ((plainPayload cnfBytes).At plainNvCnfPtr) := rfl
  rw [h1] at h0
  exact sep_mono_r (fun _ hfW => ⟨List.replicate 2048 0, h2048, hfW.symm⟩) h0

/-! ## 4. Closed 59-function `Env.ofTable` assembly, `ModuleOk`, and non-vacuity -/

private theorem plainFns_nodup : (plainFns.map Fn.name).Nodup := by
  have hchk := plain_acyclic
  simp only [plainModule, Module.checkAcyclic, Bool.and_eq_true] at hchk
  exact (List.nodup_append.mp (Module.namesNodup_of_checkNamesNodup hchk.1)).1

private theorem plainSpecTable_nodup (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    ((plainSpecTable mainSpec).map SpecEntry.name).Nodup := by
  have h : (plainSpecTable mainSpec).map SpecEntry.name = plainFns.map Fn.name := rfl
  rw [h]
  exact plainFns_nodup

private theorem mkPlainEnv_row {mainSpec : Spec [i64, i64, i64, i64, i64] [i64]}
    (e : SpecEntry)
    (he : e ∈ plainSpecTable mainSpec := by
      simp only [plainSpecTable, List.mem_cons, true_or, or_true])
    (hno : ∀ xs m Q X, e.spec xs m Q X → e.eff xs m Q X := by intro _ _ _ _ h; exact h) :
    ∀ xs m Q X, e.spec xs m Q X → mkPlainEnv mainSpec e.name e.as e.rs xs m Q X :=
  fun xs m Q X h => Env.ofTable_of_mem he (plainSpecTable_nodup mainSpec) (hno xs m Q X h)

private theorem allFns_of_forall {P : Fn → Prop} :
    ∀ {fs : List Fn}, (∀ f ∈ fs, P f) → AllFns P fs
  | [], _ => trivial
  | _ :: _, h =>
      ⟨h _ List.mem_cons_self, allFns_of_forall fun f hf => h f (List.mem_cons_of_mem _ hf)⟩

/-- Row-by-row `TableImpl` for all 59 functions in `plainFns` (`dimacs_fns ++ plain1_fns ++
plain2_fns`) against `plainSpecTable mainSpec` (zero N-way `rcases`). -/
theorem mkPlainEnv_tableImpl
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hweaken : ∀ args m Q X, mainSpec args m Q X → plainSolveBytesCoreSpec args m Q X) :
    TableImpl (mkPlainEnv mainSpec) plainFns (plainSpecTable mainSpec) := by
  let Γ := mkPlainEnv mainSpec
  let hWs := mkPlainEnv_row (mainSpec := mainSpec)
    ⟨"kissat_is_ws", [i64], [.bool], kissatIsWsSpec, true⟩
  let hDig := mkPlainEnv_row (mainSpec := mainSpec)
    ⟨"kissat_is_digit", [i64], [.bool], kissatIsDigitSpec, true⟩
  let hSwc := mkPlainEnv_row (mainSpec := mainSpec)
    ⟨"kissat_skip_ws_comments", [i64, i64], [i64], kissatSkipWsCommentsSpec, true⟩
  let hWs1 := mkPlainEnv_row (mainSpec := mainSpec)
    ⟨"kissat_skip_ws1", [i64, i64], [.bool], kissatSkipWs1Spec, true⟩
  let hNat := mkPlainEnv_row (mainSpec := mainSpec)
    ⟨"kissat_read_nat", [i64, i64], [.bool], kissatReadNatSpec, true⟩
  let hHdr := mkPlainEnv_row (mainSpec := mainSpec)
    ⟨"kissat_parse_header", [i64, i64, i64], [.bool], kissatParseHeaderSpec, true⟩
  let hLit := mkPlainEnv_row (mainSpec := mainSpec)
    ⟨"kissat_next_lit", [i64, i64], [i64], kissatNextLitSpec, true⟩
  let hCheck := mkPlainEnv_row (mainSpec := mainSpec)
    ⟨"kissat_check_model", [i64, i64, i64, i64, i64], [i64], kissatCheckModelExactSpec, true⟩
  let hIsqrt := mkPlainEnv_row (mainSpec := mainSpec)
    ⟨"plain_isqrt", [i64], [i64], plainIsqrtSpec, true⟩
  let hIlog := mkPlainEnv_row (mainSpec := mainSpec)
    ⟨"plain_ilog10", [i64], [i64], plainIlog10Spec, true⟩
  let hAN := mkPlainEnv_row (mainSpec := mainSpec)
    ⟨"plain_arena_next", [i64, i32], [i32], plainArenaNextSpec, true⟩
  let hAlloc := mkPlainEnv_row (mainSpec := mainSpec)
    ⟨"plain_alloc_cl", [i64, i32, i32, .bool], [i64], plainAllocClSpec, true⟩
  let hDefrag := mkPlainEnv_row (mainSpec := mainSpec)
    ⟨"plain_wstack_defrag", [i64], [], plainWstackDefragSpec, true⟩
  let hWP := mkPlainEnv_row (mainSpec := mainSpec)
    ⟨"plain_watch_push", [i64, i32, i32, i32, i32], [.bool], plainWatchPushSpec, true⟩
  let hHUp := mkPlainEnv_row (mainSpec := mainSpec)
    ⟨"plain_heap_up", [i64, i32], [], plainHeapUpSpec, true⟩
  let hHDown := mkPlainEnv_row (mainSpec := mainSpec)
    ⟨"plain_heap_down", [i64, i32], [], plainHeapDownSpec, true⟩
  let hHPush := mkPlainEnv_row (mainSpec := mainSpec)
    ⟨"plain_heap_push", [i64, i32], [], plainHeapPushSpec, true⟩
  let hHPop := mkPlainEnv_row (mainSpec := mainSpec)
    ⟨"plain_heap_pop", [i64], [i64], plainHeapPopSpec, true⟩
  let hRescale := mkPlainEnv_row (mainSpec := mainSpec)
    ⟨"plain_rescale", [i64], [], plainRescaleSpec, true⟩
  let hBump := mkPlainEnv_row (mainSpec := mainSpec)
    ⟨"plain_bump_var", [i64, i32], [], plainBumpVarSpec, true⟩
  let hDecay := mkPlainEnv_row (mainSpec := mainSpec)
    ⟨"plain_bump_decay", [i64], [], plainBumpDecaySpec, true⟩
  let hQmtf := mkPlainEnv_row (mainSpec := mainSpec)
    ⟨"plain_queue_mtf", [i64, i32], [], plainQueueMtfSpec, true⟩
  let hTickRel := mkPlainEnv_row (mainSpec := mainSpec)
    ⟨"plain_tick_rel", [i64], [], plainTickRelSpec, true⟩
  let hEma := mkPlainEnv_row (mainSpec := mainSpec)
    ⟨"plain_ema_update", [i64, i64], [], plainEmaUpdateSpec, true⟩
  let hAssign := mkPlainEnv_row (mainSpec := mainSpec)
    ⟨"plain_assign", [i64, i32, i32], [], plainAssignSpec, true⟩
  let hBt := mkPlainEnv_row (mainSpec := mainSpec)
    ⟨"plain_backtrack", [i64, i64], [], plainBacktrackSpec, true⟩
  let hAddCl := mkPlainEnv_row (mainSpec := mainSpec)
    ⟨"plain_add_clause", [i64, i32, i32, .bool], [i64], plainAddClauseSpec, true⟩
  let hZero := mkPlainEnv_row (mainSpec := mainSpec)
    ⟨"plain_zero_tables", [i64], [], plainZeroTablesSpec, true⟩
  let hInit := mkPlainEnv_row (mainSpec := mainSpec)
    ⟨"plain_init_state", [i64, i64, i64, i64, i64], [.bool], plainInitStateSpec, true⟩
  let hSkip := mkPlainEnv_row (mainSpec := mainSpec)
    ⟨"plain_skip_cl", [i64, i64], [.bool], plainSkipClSpec, true⟩
  let hIngest := mkPlainEnv_row (mainSpec := mainSpec)
    ⟨"plain_ingest_cl", [i64, i64], [i64], plainIngestClSpec, true⟩
  let hParse := mkPlainEnv_row (mainSpec := mainSpec)
    ⟨"plain_parse_body", [i64, i64], [i64], plainParseBodySpec, true⟩
  let hFind := mkPlainEnv_row (mainSpec := mainSpec)
    ⟨"plain_find_repl", [i64, i64], [i64], plainFindReplSpec, true⟩
  let hPropLit := mkPlainEnv_row (mainSpec := mainSpec)
    ⟨"plain_prop_lit", [i64, i32], [.bool], plainPropLitSpec, true⟩
  let hProp := mkPlainEnv_row (mainSpec := mainSpec)
    ⟨"plain_propagate", [i64], [i64], plainPropagateSpec, true⟩
  let hRecomp := mkPlainEnv_row (mainSpec := mainSpec)
    ⟨"plain_recompute_tiers", [i64], [], plainRecomputeTiersSpec, true⟩
  let hMarkRsn := mkPlainEnv_row (mainSpec := mainSpec)
    ⟨"plain_mark_reasons", [i64, .bool], [], plainMarkReasonsSpec, true⟩
  let hRedLess := mkPlainEnv_row (mainSpec := mainSpec)
    ⟨"plain_red_less", [i64, i32, i32], [.bool], plainRedLessSpec, true⟩
  let hSortReds := mkPlainEnv_row (mainSpec := mainSpec)
    ⟨"plain_sort_reds", [i64, i64], [], plainSortRedsSpec, true⟩
  let hLitRank := mkPlainEnv_row (mainSpec := mainSpec)
    ⟨"plain_lit_rank", [i64, i64, i32], [i64], plainLitRankSpec, true⟩
  let hSweep := mkPlainEnv_row (mainSpec := mainSpec)
    ⟨"plain_sweep", [i64], [i64], plainSweepSpec, true⟩
  let hRed := mkPlainEnv_row (mainSpec := mainSpec)
    ⟨"plain_reduce", [i64, .bool], [i64], plainReduceSpec, true⟩
  let hAnaLit := mkPlainEnv_row (mainSpec := mainSpec)
    ⟨"plain_analyze_lit", [i64, i32, i32], [.bool], plainAnalyzeLitSpec, true⟩
  let hAnaRsn := mkPlainEnv_row (mainSpec := mainSpec)
    ⟨"plain_analyze_rsn", [i64, i32, i32], [.bool], plainAnalyzeRsnSpec, true⟩
  let hClrMrks := mkPlainEnv_row (mainSpec := mainSpec)
    ⟨"plain_clear_marks", [i64, i64], [], plainClearMarksSpec, true⟩
  let hMinMark := mkPlainEnv_row (mainSpec := mainSpec)
    ⟨"plain_min_mark", [i64, i32, i8], [], plainMinMarkSpec, true⟩
  let hMinLit := mkPlainEnv_row (mainSpec := mainSpec)
    ⟨"plain_min_lit", [i64, i32], [.bool], plainMinLitSpec, true⟩
  let hTmpLess := mkPlainEnv_row (mainSpec := mainSpec)
    ⟨"plain_tmp_less", [i64, i64, i32, i32], [.bool], plainTmpLessSpec, true⟩
  let hSortTmp := mkPlainEnv_row (mainSpec := mainSpec)
    ⟨"plain_sort_tmp", [i64], [], plainSortTmpSpec, true⟩
  let hShrkBlk := mkPlainEnv_row (mainSpec := mainSpec)
    ⟨"plain_shrink_blk", [i64, i64, i64, i32, i64], [], plainShrinkBlkSpec, true⟩
  let hMinShrk := mkPlainEnv_row (mainSpec := mainSpec)
    ⟨"plain_min_shrink", [i64], [], plainMinShrinkSpec, true⟩
  let hAnalyze := mkPlainEnv_row (mainSpec := mainSpec)
    ⟨"plain_analyze", [i64], [i64], plainAnalyzeSpec, true⟩
  let hDecide := mkPlainEnv_row (mainSpec := mainSpec)
    ⟨"plain_decide", [i64], [i64], plainDecideSpec, true⟩
  let hRephase := mkPlainEnv_row (mainSpec := mainSpec)
    ⟨"plain_rephase", [i64], [], plainRephaseSpec, true⟩
  let hSwitch := mkPlainEnv_row (mainSpec := mainSpec)
    ⟨"plain_switch_mode", [i64], [], plainSwitchModeSpec, true⟩
  let hRestart := mkPlainEnv_row (mainSpec := mainSpec)
    ⟨"plain_restart_due", [i64], [i64], plainRestartDueSpec, true⟩
  let hLScan := mkPlainEnv_row (mainSpec := mainSpec)
    ⟨"plain_lucky_scan", [i64, .bool, .bool], [i64], plainLuckyScanSpec, true⟩
  let hLucky := mkPlainEnv_row (mainSpec := mainSpec)
    ⟨"plain_lucky", [i64], [i64], plainLuckySpec, true⟩
  exact
    ⟨ .of (kissat_is_ws_wp Γ), .of (kissat_is_digit_wp Γ)
    , .of (kissat_skip_ws_comments_wp Γ hWs), .of (kissat_skip_ws1_wp Γ hWs)
    , .of (kissat_read_nat_wp Γ hDig hWs), .of (kissat_parse_header_wp Γ hSwc hWs1 hNat)
    , .of (kissat_next_lit_wp Γ hSwc hNat), .of (kissat_check_model_exact_wp Γ hHdr hLit hSwc)
    , .of (plain_isqrt_wp Γ), .of (plain_ilog10_wp Γ), .of (plain_arena_next_wp Γ)
    , .of (plain_alloc_cl_wp Γ), .of (plain_wstack_defrag_wp Γ)
    , .of (plain_watch_push_wp Γ hDefrag), .of (plain_heap_up_wp Γ)
    , .of (plain_heap_down_wp Γ), .of (plain_heap_push_wp Γ hHUp)
    , .of (plain_heap_pop_wp Γ hHDown), .of (plain_rescale_wp Γ)
    , .of (plain_bump_var_wp Γ hHUp hRescale), .of (plain_bump_decay_wp Γ hRescale)
    , .of (plain_queue_mtf_wp Γ), .of (plain_tick_rel_wp Γ), .of (plain_ema_update_wp Γ)
    , .of (plain_assign_wp Γ), .of (plain_backtrack_wp Γ hHPush)
    , .of (plain_add_clause_wp Γ hAlloc hWP), .of (plain_zero_tables_wp Γ)
    , .of (plain_init_state_wp Γ hHdr hZero), .of (plain_skip_cl_wp Γ hLit)
    , .of (plain_ingest_cl_wp Γ hLit hAssign hAddCl)
    , .of (plain_parse_body_wp Γ hSkip hIngest hSwc), .of (plain_find_repl_wp Γ)
    , .of (plain_prop_lit_wp Γ hFind hWP hAssign), .of (plain_propagate_wp Γ hPropLit)
    , .of (plain_recompute_tiers_wp Γ), .of (plain_mark_reasons_wp Γ)
    , .of (plain_red_less_wp Γ), .of (plain_sort_reds_wp Γ hRedLess)
    , .of (plain_lit_rank_wp Γ)
    , .of (plain_sweep_wp Γ hAN hDefrag hWP hAssign hLitRank)
    , .of (plain_reduce_wp Γ hIsqrt hBt hProp hRecomp hMarkRsn hAN hSortReds hIlog hSweep)
    , .of (plain_analyze_lit_wp Γ), .of (plain_analyze_rsn_wp Γ hAnaLit)
    , .of (plain_clear_marks_wp Γ), .of (plain_min_mark_wp Γ)
    , .of (plain_min_lit_wp Γ hMinMark), .of (plain_tmp_less_wp Γ)
    , .of (plain_sort_tmp_wp Γ hTmpLess), .of (plain_shrink_blk_wp Γ hMinLit hMinMark)
    , .of (plain_min_shrink_wp Γ hSortTmp hMinMark hMinLit hShrkBlk)
    , .of (plain_analyze_wp Γ hAnaLit hAnaRsn hClrMrks hBump hQmtf hDecay hMinShrk hTickRel
        hEma hBt hAssign hDefrag hRed hAddCl)
    , .of (plain_decide_wp Γ hHPop hAssign), .of (plain_rephase_wp Γ hBt hIlog)
    , .of (plain_switch_mode_wp Γ hHDown hIlog), .of (plain_restart_due_wp Γ)
    , .of (plain_lucky_scan_wp Γ hBt hAssign hProp hAnalyze), .of (plain_lucky_wp Γ hAN hBt hAssign
        hProp hLScan)
    , .of (fun args m Q X h =>
        plain_solve_core_wp Γ hInit hParse hProp hLucky hAnalyze hSwitch hRed hRephase hRestart
          hBt hDecide hCheck args m Q X (hweaken args m Q X h))
    , trivial ⟩

theorem mkPlainEnv_sound
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hweaken : ∀ args m Q X, mainSpec args m Q X → plainSolveBytesCoreSpec args m Q X) :
    ∀ f ∈ plainFns, ∀ args m Q X,
      mkPlainEnv mainSpec f.name f.as f.rs args m Q X →
      Func.wp (mkPlainEnv mainSpec) f.body args m Q X :=
  Env.ofTable_sound plainFns_nodup (mkPlainEnv_tableImpl mainSpec hweaken)

theorem mkPlainEnv_noExit (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    ∀ f as bs xs m Q X X',
      mkPlainEnv mainSpec f as bs xs m Q X →
      mkPlainEnv mainSpec f as bs xs m Q X' :=
  Env.ofTable_noExit (plainSpecTable_noExit mainSpec)

theorem mkPlainEnv_moduleOk
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hweaken : ∀ args m Q X, mainSpec args m Q X → plainSolveBytesCoreSpec args m Q X) :
    ModuleOk (mkPlainEnv mainSpec) plainModule :=
  Env.ofTable_moduleOk plain_acyclic (allFns_of_forall plainFns_wf)
    (mkPlainEnv_tableImpl mainSpec hweaken)

theorem mkPlainEnv_solve_bytes (mainSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hno : ∀ xs m Q X, mainSpec xs m Q X → mainSpec xs m Q (fun _ _ _ _ => False)) :
    ∀ xs m Q X, mainSpec xs m Q X →
      mkPlainEnv mainSpec "kissat_solve_bytes" [i64, i64, i64, i64, i64] [i64] xs m Q X :=
  fun xs m Q X h =>
    Env.ofTable_of_mem
      (e := ⟨"kissat_solve_bytes", [i64, i64, i64, i64, i64], [i64], mainSpec, true⟩)
      (by simp [plainSpecTable]) (plainSpecTable_nodup mainSpec) (hno xs m Q X h)

/-- Headline: every function in `plainFns` satisfies its contract in `plainEnv`. -/
theorem plainEnv_sound :
    ∀ f ∈ plainFns, ∀ args m Q X,
      plainEnv f.name f.as f.rs args m Q X →
      Func.wp plainEnv f.body args m Q X :=
  mkPlainEnv_sound plainSolveBytesSpec (fun _ _ _ _ => plainSolveBytesCoreSpec_of_spec)

/-- Every row in `plainEnv` ignores exit continuations (`fnSpec_noExit_of_legalSigAll`). -/
theorem plainEnv_noExit :
    ∀ f as bs xs m Q X X',
      plainEnv f as bs xs m Q X → plainEnv f as bs xs m Q X' :=
  mkPlainEnv_noExit plainSolveBytesSpec

/-- Headline: full 59-function `ModuleOk` for `plainModule` under `plainEnv`. -/
theorem plainEnv_moduleOk : ModuleOk plainEnv plainModule :=
  mkPlainEnv_moduleOk plainSolveBytesSpec (fun _ _ _ _ => plainSolveBytesCoreSpec_of_spec)

/-- Headline source-level correctness of `kissat_solve_bytes` under `plainEnv`: returns
`r ∈ {0, 10, 20}`, keeps `[cnf_ptr, cnf_ptr + cnf_len)` read-only, restores
`region work_ptr work_len`, and certifies UNSAT (`20`) and SAT (`10`). -/
theorem plain_solve_bytes_correct
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8} {wlen : Nat}
    {R : Mem 64 → Prop} {m : Mem 64} {X : XPost}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp plainEnv kissat_solve_bytes_body
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ()) m
      (fun (r, ()) m' =>
        (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
        (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
        (r = 10#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ ¬ cnf.Unsat ∧ ∃ α, cnf.Sat α) ∧
        (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m') X :=
  plainEnv_sound kissat_solve_bytes (by simp [plainFns, plain2_fns]) _ m _ X
    (mkPlainEnv_solve_bytes plainSolveBytesSpec (fun _ _ _ _ h => h) _ m _ X
      ⟨cnfBytes, wlen, R, rfl, rfl, hcfit, hwfit, hm,
        fun _ _ hdom hu hs hm' => ⟨hdom, hu, hs, hm'⟩⟩)

/-- Closed 59-function environment for concrete UNSAT non-vacuity (`20#64`). -/
@[expose] def plainUnsatEnv : Env := mkPlainEnv plainUnsatWitnessSpec

theorem plainUnsatEnv_sound :
    ∀ f ∈ plainFns, ∀ args m Q X,
      plainUnsatEnv f.name f.as f.rs args m Q X → Func.wp plainUnsatEnv f.body args m Q X :=
  mkPlainEnv_sound plainUnsatWitnessSpec (fun _ _ _ _ => plainCoreSpec_of_unsat)

theorem plainUnsatEnv_noExit :
    ∀ f as bs xs m Q X X',
      plainUnsatEnv f as bs xs m Q X → plainUnsatEnv f as bs xs m Q X' :=
  mkPlainEnv_noExit plainUnsatWitnessSpec

theorem plainUnsatEnv_moduleOk : ModuleOk plainUnsatEnv plainModule :=
  mkPlainEnv_moduleOk plainUnsatWitnessSpec (fun _ _ _ _ => plainCoreSpec_of_unsat)

/-- Headline source-level UNSAT non-vacuity: `kissat_solve_bytes` returns `20#64` and proves
`plainNvUnsatCnf.Unsat` on `plainNvUnsatBytes` with `work_len = 2048` and `fuel = 16`. -/
theorem plain_unsat_nonvacuous :
    let m0 : Mem 64 := (plainPayload plainNvUnsatBytes).At plainNvCnfPtr
    Func.wp plainUnsatEnv kissat_solve_bytes_body
      (plainNvCnfPtr, BitVec.ofNat 64 plainNvUnsatBytes.length,
        plainNvWorkPtr plainNvUnsatBytes, 2048#64, 16#64, ()) m0
      (fun rs _ => rs = (20#64, ()) ∧ plainNvUnsatCnf.Unsat) (fun _ _ _ _ => False) := by
  apply plainUnsatEnv_sound kissat_solve_bytes (by simp [plainFns, plain2_fns])
  exact mkPlainEnv_solve_bytes plainUnsatWitnessSpec (fun _ _ _ _ h => h) _ _ _ _
    ⟨emp, rfl, rfl, rfl, by decide, by decide,
      by rw [sep_emp]; exact plainPayload_sep plainNvUnsatBytes (by decide),
      fun _ hu _ => ⟨rfl, hu⟩⟩

/-- Closed 59-function environment for concrete SAT non-vacuity (`10#64`). -/
@[expose] def plainSatEnv : Env := mkPlainEnv plainSatWitnessSpec

theorem plainSatEnv_sound :
    ∀ f ∈ plainFns, ∀ args m Q X,
      plainSatEnv f.name f.as f.rs args m Q X → Func.wp plainSatEnv f.body args m Q X :=
  mkPlainEnv_sound plainSatWitnessSpec (fun _ _ _ _ => plainCoreSpec_of_sat)

theorem plainSatEnv_noExit :
    ∀ f as bs xs m Q X X',
      plainSatEnv f as bs xs m Q X → plainSatEnv f as bs xs m Q X' :=
  mkPlainEnv_noExit plainSatWitnessSpec

theorem plainSatEnv_moduleOk : ModuleOk plainSatEnv plainModule :=
  mkPlainEnv_moduleOk plainSatWitnessSpec (fun _ _ _ _ => plainCoreSpec_of_sat)

/-- Headline source-level SAT non-vacuity: `kissat_solve_bytes` returns `10#64` and proves
`¬ plainNvSatCnf.Unsat ∧ ∃ α, plainNvSatCnf.Sat α` on `plainNvSatBytes`
(`work_len = 2048`, `fuel = 16`). -/
theorem plain_sat_nonvacuous :
    let m0 : Mem 64 := (plainPayload plainNvSatBytes).At plainNvCnfPtr
    Func.wp plainSatEnv kissat_solve_bytes_body
      (plainNvCnfPtr, BitVec.ofNat 64 plainNvSatBytes.length,
        plainNvWorkPtr plainNvSatBytes, 2048#64, 16#64, ()) m0
      (fun rs _ => rs = (10#64, ()) ∧ ¬ plainNvSatCnf.Unsat ∧ ∃ α, plainNvSatCnf.Sat α)
      (fun _ _ _ _ => False) := by
  apply plainSatEnv_sound kissat_solve_bytes (by simp [plainFns, plain2_fns])
  exact mkPlainEnv_solve_bytes plainSatWitnessSpec (fun _ _ _ _ h => h) _ _ _ _
    ⟨emp, rfl, rfl, rfl, by decide, by decide,
      by rw [sep_emp]; exact plainPayload_sep plainNvSatBytes (by decide),
      fun _ hnu hsat _ => ⟨rfl, hnu, hsat⟩⟩

end LeanQbe.T.Examples.Kissat.Plain
