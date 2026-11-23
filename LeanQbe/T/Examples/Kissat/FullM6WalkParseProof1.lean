module

public import LeanQbe.T.Examples.Kissat.FullM6WalkParse
public import LeanQbe.T.Examples.Kissat.FullSpec
import LeanQbe.T.Examples.Kissat.FullDimacsBodyLemmas
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat M6 Wave 2 (`RC-26b` + `RC-27`) `Func.wp` Proofs — Part 1 (`FullM6WalkParseProof1`)

Proves UNSAT-only parametric `Func.wp` contracts (`XPost := False`, `0` SAT proofs) for:
1. `full_rescale_m6_wp` against exact canonical `Full.fullRescaleSpec` (`>> 16ULL` EVSIDS rescale).
2. `full_parse_body_m6_wp` against exact canonical `Full.fullParseBodySpec` (eager parse-time
   level-0 unit BCP calling canonical `full_ingest_cl` + `full_propagate`, preserving `fuel` and
   `UnitUnsatTrace` determinism).
3. Pure/read-only ProbSAT walk helpers: `full_walk_cb_inv_m6_wp`, `full_walk_score_m6_wp`, and
   `full_walk_break_m6_wp`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM6WalkParse

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open Kraken.Bedrock2.Test

/-! ## 1. Specs for Pure / Read-Only ProbSAT Helpers -/

/-- Pure `full_walk_cb_inv_m6` contract (`Mem`-preserving). -/
def m6WalkCbInvSpec : Spec [i64, i64, i64] [i64] := fun (_tot, _ncl, _wc, ()) m Q _ =>
  ∀ r : BitVec 64, Q (r, ()) m

/-- Pure `full_walk_score_m6` contract (`Mem`-preserving, bounded by `2^30`). -/
def m6WalkScoreSpec : Spec [i64, i64] [i32] := fun (_inv, _brk, ()) m Q _ =>
  ∀ r : BitVec 32, r.toNat ≤ 2 ^ 30 → Q (r, ()) m

/-- Read-only `full_walk_break_m6` contract (`s' = s`, `Mem`-preserving). -/
def m6WalkBreakSpec : Spec [i64, i32, i64, i64, i64] [i64] :=
  SafetySlice.spec fullSafetySlice
    (fun c (h, _lit, ncl, max_cl, occ_cap, ()) _ =>
      h = c.hdr ∧ ncl.toNat ≤ max_cl.toNat ∧ 5 * max_cl.toNat + occ_cap.toNat ≤ c.scratch_cap)
    (fun _ _ _ s s' => s' = s)

/-! ## 2. `full_rescale_m6` (`Full.fullRescaleSpec`) -/

section RescaleProof

open scoped FullArenaTactics

private theorem m6_probePres_refl (s : FullState) : FullProbeScratchPres s s :=
  ⟨⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem m6_hlen_upd_score {c : FullCfg} {s : FullState}
    (hlen : s.LengthsOk c) (sc' : List (BitVec 64)) (hs : sc'.length = c.max_vars) :
    ({ core := s.core, scratch := { s.scratch with score := sc' } } : FullState).LengthsOk c :=
  hlen.with_scratch { hlen.scratch_ok with score_len := hs }

/-- Finer `>> 16ULL` EVSIDS rescale satisfies exact canonical `Full.fullRescaleSpec`. -/
theorem full_rescale_m6_wp (Γ : Env) :
    ∀ a m Q X, fullRescaleSpec a m Q X → Func.wp Γ full_rescale_m6_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  dsimp only [fullSafetySlice] at hm hlen hQ
  obtain hmx : c.max_vars < 2 * dimacsBound := c.hmaxv
  unfold dimacsBound at hmx
  obtain hcv_le := hlen.core_ok.cur_vars_le
  c0_hsteps_nogrp
  refine wp_loop_safety_slice_pure (fullSafetySlice c) s R
    (fun s1 (v, ()) => v.toNat ≤ s.core.cur_vars ∧ FullProbeScratchPres s s1)
    (fun (v, ()) => s.core.cur_vars - v.toNat)
    (fun J hLoop => ?_)
    (fun J s1 (v, ()) m1 hcore1 hlen1 ⟨hv1, hpres1⟩ hm1 hLoop1 => ?_)
  · c0_hsteps; exact hLoop s (0#64, ()) m hm rfl hlen ⟨by simp, m6_probePres_refl s⟩
  · rw [Blocks.get_here]; dsimp only [fullSafetySlice] at *
    have hceq1 : s1.core = s.core := hcore1
    obtain hsl1 := hlen1.scratch_ok.score_len
    c0_hsteps
    · have hcv64 : (BitVec.ofNat 64 s.core.cur_vars).toNat = s.core.cur_vars :=
        bv64_ofNat_toNat (by omega)
      have hv_lt : v.toNat < s.core.cur_vars := by
        have h1 : v.toNat < (BitVec.ofNat 64 s.core.cur_vars).toNat := by
          rw [hceq1] at *; c0_bound
        omega
      have hvp1 : (v + 1).toNat = v.toNat + 1 := by bv_omega
      have hv_sc : v.toNat < s1.scratch.score.length := by rw [hsl1]; omega
      c0_hsteps
      exact hLoop1 _ (v + 1, ()) m hm (by dsimp only; omega) rfl
        (m6_hlen_upd_score hlen1 _ (by simp [hsl1])) ⟨by dsimp only; omega, hpres1⟩
    · refine hQ () _ m ?_ ?_ ?_ hm
      · exact hcore1
      · exact hlen1.with_scratch { hlen1.scratch_ok with }
      · exact hpres1
    · refine hQ () _ m ?_ ?_ ?_ hm
      · exact hcore1
      · exact hlen1.with_scratch { hlen1.scratch_ok with }
      · exact hpres1

end RescaleProof

/-! ## 3. `full_parse_body_m6` (`Full.fullParseBodySpec`, Eager Parse-Time Unit BCP) -/

section ParseBodyM6Proof

open scoped FullArenaTactics FullDimacsBodyTactics
open FullDimacsBodyTactics

private theorem m6_mem_to_dimacs {c : FullCfg} {s : FullState} {cnf_ptr : BitVec 64}
    {cnfBytes : List UInt8} {R : Mem 64 → Prop} {m : Mem 64}
    (h : (bytes cnf_ptr cnfBytes ⋆ FullMem c s ⋆ R) m) :
    (bytes cnf_ptr cnfBytes ⋆
      dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
      (FullRest c s ⋆ R)) m :=
  sep_ac (focus_dimacs (sep_ac h : (FullMem c s ⋆ (bytes cnf_ptr cnfBytes ⋆ R)) m))

private theorem m6_dimacs_to_mem {c : FullCfg} {s : FullState} {cur' val' cnf_ptr : BitVec 64}
    {cnfBytes : List UInt8} {R : Mem 64 → Prop} {m : Mem 64}
    (h : (bytes cnf_ptr cnfBytes ⋆
      dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) cur' val' ⋆
      (FullRest c s ⋆ R)) m) :
    (bytes cnf_ptr cnfBytes ⋆
      FullMem c { s with core := { s.core with d_cur := cur', d_val := val' } } ⋆ R) m :=
  sep_ac (unfocus_dimacs (R := bytes cnf_ptr cnfBytes ⋆ R) (sep_ac h))

private theorem m6_unitUnsatTrace_congr_vals {mv : Nat} :
    ∀ {bs : List UInt8} {n : Nat} {v1 v2 : List (BitVec 8)},
      2 * mv ≤ v1.length → 2 * mv ≤ v2.length →
      (∀ k < 2 * mv, v1[k]?.getD 0#8 = v2[k]?.getD 0#8) →
      UnitUnsatTrace mv v1 bs n → UnitUnsatTrace mv v2 bs n := by
  intro bs n v1 v2 hlen1 hlen2 hcongr hut
  induction hut generalizing v2 with
  | @conflict vals bs l rest k hl hpc hvf hrest =>
    exact .conflict hl hpc (by rw [← hcongr l hl]; exact hvf) hrest
  | @step vals bs l rest k hl hpc hv0 _ ih =>
    have hln_lt : l ^^^ 1 < 2 * mv := litNeg_lt_two_mul hl
    refine .step hl hpc (by rw [← hcongr l hl]; exact hv0)
      (ih (by simp [hlen1]) (by simp [hlen2]) fun m hm => ?_)
    by_cases hm2 : m = l ^^^ 1
    · subst hm2
      rw [List.getElem?_set_self (by simp; omega), List.getElem?_set_self (by simp; omega)]
    · rw [List.getElem?_set_ne (Ne.symm hm2), List.getElem?_set_ne (Ne.symm hm2)]
      by_cases hm1 : m = l
      · subst hm1; rw [List.getElem?_set_self (by omega), List.getElem?_set_self (by omega)]
      · rw [List.getElem?_set_ne (Ne.symm hm1), List.getElem?_set_ne (Ne.symm hm1)]
        exact hcongr m hm

private theorem m6_init_sparseW {c : FullCfg} {s : FullState}
    (hinv0 : FullSparseInv c (shiftDownCnf CNF.empty) s)
    (hcv0 : s.core.cur_vars = c.mv) (hal0 : s.core.arena_len = 0)
    (hte0 : s.core.trail_end = 0) (hcl0 : s.core.cur_level = 0)
    (hinc0 : s.core.inconsistent = 0#64)
    (hvals0 : s.core.vals = List.replicate (2 * c.max_vars) 0#8)
    (hwvec0 : s.core.wvec = List.replicate (4 * c.max_vars) 0#32) :
    FullSparseInvW c (shiftDownCnf CNF.empty) [] s ∧
      (shiftDownCnf CNF.empty).Entails (cnfOfClauses []) := by
  obtain ⟨F_init, hw_init⟩ := hinv0.1.witness
  have hft0 : (s.core.frame_trail[0]?.getD 0#32).toNat = 0 := by
    have := hw_init.frame_trail_lt 0 (by omega); omega
  have hcmv : s.core.cur_vars ≤ c.max_vars := hinv0.1.lengths.core_ok.cur_vars_le
  have hext : ExtUnsatSound (shiftDownCnf CNF.empty) s.core.cur_vars [] :=
    ⟨(fun _ hc => nomatch hc), fun hu => by
      rw [CNF.unsat_iff_not_sat] at hu
      exact False.elim (hu (fun _ => false)
        ((cnf_sat_cnfOfClauses_iff (fun _ => false) []).mpr fun _ hc => by cases hc))⟩
  have hw0 : ∀ l < 2 * s.core.cur_vars,
      fullWatchOffCore s.core l = 0 ∧ fullWatchSizeCore s.core l = 0 := fun l hl => by
    unfold fullWatchOffCore fullWatchSizeCore; rw [hwvec0]
    simp [show 2 * l < 4 * c.max_vars by omega, show 2 * l + 1 < 4 * c.max_vars by omega]
  have hv0 : ∀ l < 2 * s.core.cur_vars, s.core.vals[l]?.getD 0#8 = 0#8 := fun l hl => by
    rw [hvals0]; simp [show l < 2 * c.max_vars by omega]
  have hw_empty := fullWitnessInv_empty (c := c) hext hinc0 hal0 hw0 hte0 hcl0 hft0 hv0
  refine ⟨⟨hinv0.1.lengths, hw_empty, hinv0.2.1, hinv0.2.2.1, hinv0.2.2.2.1, hinv0.2.2.2.2⟩, ?_⟩
  rw [CNF.entails_def]
  intro α _; exact (cnf_sat_cnfOfClauses_iff α []).mpr fun _ hc => by cases hc

private theorem m6_sparseInvW_of_perm {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s s' : FullState} (hsp : FullSparseInvW c F0 F_cur s)
    (hlen' : s'.LengthsOk c) (hw' : FullWitnessInv c F0 F_cur s'.core)
    (hperm : FullArenaPermEq s.core s'.core)
    (hmrk : s'.core.mrk = s.core.mrk) (hlm : s'.core.lit_mark = s.core.lit_mark)
    (hdm : s'.core.dense_mode = s.core.dense_mode)
    (hpres : FullExtScratchPres s s') : FullSparseInvW c F0 F_cur s' := by
  refine ⟨hlen', hw', ?_, ?_, ?_, hdm.trans hsp.2.2.2.2.2⟩
  · exact ⟨fun v hv => by rw [hmrk]; exact hsp.2.2.1.1 v hv,
      fun l hl => by rw [hlm]; exact hsp.2.2.1.2 l hl⟩
  · intro ref href hng
    have href0 : ref ∈ fullArenaClauseRefsCore s.core := hperm.2.1 ▸ href
    obtain ⟨_, hgb, hp⟩ := hperm.2.2 ref href0
    exact (hp.map (· / 2)).nodup_iff.mpr (hsp.2.2.2.1 ref href0 (hgb.symm.trans hng))
  · exact hsp.2.2.2.2.1.of_pres hpres fun ref href => by
      change ref ∈ fullArenaClauseRefsCore s'.core; rw [hperm.2.1]; exact href

private theorem m6_sparseInvW_with_fuel_ticks {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hsp : FullSparseInvW c F0 F_cur s) (fuel' ticks' : BitVec 64) :
    FullSparseInvW c F0 F_cur
      { core := { s.core with fuel := fuel' }
        scratch := { s.scratch with search_ticks := ticks' } } := by
  let s' : FullState :=
    { core := { s.core with fuel := fuel' }, scratch := { s.scratch with search_ticks := ticks' } }
  have hlen' : s'.LengthsOk c :=
    ⟨{ hsp.1.core_ok with cur_vars_le := hsp.1.core_ok.cur_vars_le }, { hsp.1.scratch_ok with }⟩
  have hw' : FullWitnessInv c F0 F_cur s'.core :=
    { hsp.2.1 with
      arena := { hsp.2.1.arena with len_ok := hsp.2.1.arena.len_ok }
      watches := hsp.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) }
  exact m6_sparseInvW_of_perm hsp hlen' hw' ⟨rfl, rfl, fun _ _ => ⟨rfl, rfl, .refl _⟩⟩
    rfl rfl rfl ⟨rfl, rfl⟩

private structure ParseBodyM6Inv (c : FullCfg) (s : FullState) (cnf_ptr : BitVec 64)
    (cnfBytes : List UInt8) (i0 i idx : Nat) (accCnf : CNF Nat)
    (unsat oom has_cl : Bool) (st : FullState) : Prop where
  i_le : i ≤ c.nc
  idx_le : idx ≤ cnfBytes.length
  cv_eq : st.core.cur_vars = c.mv
  d_cur_eq : st.core.d_cur = cnf_ptr + BitVec.ofNat 64 idx
  len_ok : st.LengthsOk c
  cl0 : st.core.cur_level = 0
  fuel_eq : st.core.fuel = s.core.fuel
  oom_eq : st.core.oom = 0#64
  prb_eq : st.core.probing = 0#64
  vars_pos : CnfVarsPos accCnf
  pc_eq : parseClauses c.mv (c.nc - i) accCnf (cnfBytes.drop idx) = parseDimacs cnfBytes
  uns_inv : unsat = true → (shiftDownCnf accCnf).Unsat
  ok_inv : unsat = false → oom = false →
    ∃ F_cur, FullSparseInvW c (shiftDownCnf accCnf) F_cur st ∧
      (shiftDownCnf accCnf).Entails (cnfOfClauses F_cur)
  uns_tr : UnitUnsatTrace c.mv (s.core.vals.take (2 * c.mv)) (cnfBytes.drop i0) c.nc →
    oom = false ∧
    ((unsat = false ∧ has_cl = false ∧
        UnitUnsatTrace c.mv st.core.vals (cnfBytes.drop idx) (c.nc - i)) ∨
     (unsat = true ∧ ∃ cnf, parseClauses c.mv (c.nc - i) CNF.empty (cnfBytes.drop idx) = some cnf))

private abbrev ParseBodyM6Post (c : FullCfg) (s : FullState) (cnf_ptr : BitVec 64)
    (cnfBytes : List UInt8) (i0 : Nat) (R : Mem 64 → Prop) (Q : Post [i64]) : Prop :=
  ∀ r st' m', st'.LengthsOk c → (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) →
    st'.core.fuel = s.core.fuel → st'.core.oom = 0#64 → st'.core.probing = 0#64 →
    (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) →
    (r = 1#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧
      FullSparseInv c (shiftDownCnf cnf) st' ∧ st'.core.cur_level = 0) →
    (UnitUnsatTrace c.mv (s.core.vals.take (2 * c.mv)) (cnfBytes.drop i0) c.nc → r = 20#64) →
    (bytes cnf_ptr cnfBytes ⋆ FullMem c st' ⋆ R) m' → Q (r, ()) m'

private theorem pb6_skip_step {c : FullCfg} {s st st' : FullState}
    {cnf_ptr : BitVec 64} {cnfBytes rest : List UInt8} {i0 i idx j : Nat} {accCnf : CNF Nat}
    {oom has_cl : Bool} {cl : CNF.Clause Nat}
    (hp : ParseBodyM6Inv c s cnf_ptr cnfBytes i0 i idx accCnf true oom has_cl st)
    (hi : i < c.nc) (hpc1 : parseClause c.mv (cnfBytes.drop idx) = some (cl, rest))
    (hcl_pos : ∀ lit ∈ cl.literals, 1 ≤ lit.1) (hj : j ≤ cnfBytes.length)
    (hdrop : cnfBytes.drop j = rest)
    (hst' : st' = { st with core := { st.core with d_cur := cnf_ptr + BitVec.ofNat 64 j,
                                                   d_val := 0#64 } }) :
    ParseBodyM6Inv c s cnf_ptr cnfBytes i0 (i + 1) j (accCnf.add cl) true oom has_cl st' := by
  have hsub : c.nc - i = (c.nc - (i + 1)) + 1 := by omega
  refine ⟨by omega, hj, by rw [hst']; exact hp.cv_eq, by rw [hst'],
    by rw [hst']; exact ⟨{ hp.len_ok.core_ok with vals_len := hp.len_ok.core_ok.vals_len },
      hp.len_ok.scratch_ok⟩,
    by rw [hst']; exact hp.cl0, by rw [hst']; exact hp.fuel_eq, by rw [hst']; exact hp.oom_eq,
    by rw [hst']; exact hp.prb_eq, cnfVarsPos_add hp.vars_pos hcl_pos,
    by rw [← hp.pc_eq, hsub, parseClauses, hpc1, ← hdrop]; rfl,
    (fun _ => by rw [shiftDownCnf_add]; exact cnf_unsat_add (hp.uns_inv rfl)),
    (fun hc => by cases hc),
    (fun hut => by
      obtain ⟨hoom, hdisj⟩ := hp.uns_tr hut; refine ⟨hoom, Or.inr ⟨rfl, ?_⟩⟩
      rcases hdisj with ⟨hf, _⟩ | ⟨_, cnf_r, hr⟩
      · cases hf
      · rw [hsub, parseClauses, hpc1, ← hdrop] at hr; exact parseClauses_some_of_acc hr)⟩

private theorem pb6_oom_exit {c : FullCfg} {s st : FullState}
    {cnf_ptr : BitVec 64} {cnfBytes : List UInt8} {i0 i idx : Nat} {accCnf : CNF Nat}
    {unsat_v has_cl_v : Bool} {R : Mem 64 → Prop} {ml : Mem 64} {Q : Post [i64]}
    (hp : ParseBodyM6Inv c s cnf_ptr cnfBytes i0 i idx accCnf unsat_v true has_cl_v st)
    (hml : (bytes cnf_ptr cnfBytes ⋆ FullMem c st ⋆ R) ml)
    (hQ : ParseBodyM6Post c s cnf_ptr cnfBytes i0 R Q) : Q (0#64, ()) ml :=
  hQ 0#64 st ml hp.len_ok (Or.inl rfl) hp.fuel_eq hp.oom_eq hp.prb_eq
    (fun h => by cases h) (fun h => by cases h)
    (fun hut => by cases (hp.uns_tr hut).1) hml

private theorem pb6_eof_ne {c : FullCfg} {s st : FullState}
    {cnf_ptr : BitVec 64} {cnfBytes : List UInt8} {i0 idx j : Nat} {accCnf : CNF Nat}
    {unsat_v oom_v has_cl_v : Bool} {R : Mem 64 → Prop} {m' : Mem 64} {Q : Post [i64]}
    (hp : ParseBodyM6Inv c s cnf_ptr cnfBytes i0 c.nc idx accCnf unsat_v oom_v has_cl_v st)
    (hj : j ≤ cnfBytes.length)
    (hsw : cnfBytes.drop j = skipWsComments (cnfBytes.drop idx))
    (hne : cnf_ptr + BitVec.ofNat 64 j ≠ cnf_ptr + BitVec.ofNat 64 cnfBytes.length)
    (hfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ FullMem c
      { st with core := { st.core with d_cur := cnf_ptr + BitVec.ofNat 64 j } } ⋆ R) m')
    (hQ : ParseBodyM6Post c s cnf_ptr cnfBytes i0 R Q) : Q (0#64, ()) m' := by
  have hj_lt : j < cnfBytes.length := by
    have hj_ne : j ≠ cnfBytes.length := fun heq =>
      hne ((cursor_eq_iff (base := cnf_ptr) (by omega) (by omega)).mpr heq)
    omega
  have hne_emp : (skipWsComments (cnfBytes.drop idx)).isEmpty = false := by
    rw [← hsw, List.drop_eq_getElem_cons hj_lt]; rfl
  exact hQ 0#64 { st with core := { st.core with d_cur := cnf_ptr + BitVec.ofNat 64 j } } m'
    ⟨{ hp.len_ok.core_ok with vals_len := hp.len_ok.core_ok.vals_len }, hp.len_ok.scratch_ok⟩
    (Or.inl rfl) hp.fuel_eq hp.oom_eq hp.prb_eq (fun h => by cases h) (fun h => by cases h)
    (fun hut => by
      rcases (hp.uns_tr hut).2 with ⟨_, _, htr⟩ | ⟨_, _, hr⟩
      · rw [Nat.sub_self] at htr; cases htr
      · rw [Nat.sub_self] at hr
        simp only [parseClauses, hne_emp, Bool.false_eq_true, ↓reduceIte] at hr; cases hr) hm

private theorem pb6_eof_done {c : FullCfg} {s st : FullState}
    {cnf_ptr : BitVec 64} {cnfBytes : List UInt8} {i0 idx j : Nat} {accCnf : CNF Nat}
    {unsat_v oom_v has_cl_v : Bool} {R : Mem 64 → Prop} {m' : Mem 64} {Q : Post [i64]}
    (hp : ParseBodyM6Inv c s cnf_ptr cnfBytes i0 c.nc idx accCnf unsat_v oom_v has_cl_v st)
    (hj : j ≤ cnfBytes.length)
    (hsw : cnfBytes.drop j = skipWsComments (cnfBytes.drop idx))
    (heq : cnf_ptr + BitVec.ofNat 64 j = cnf_ptr + BitVec.ofNat 64 cnfBytes.length)
    (hfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ FullMem c
      { st with core := { st.core with d_cur := cnf_ptr + BitVec.ofNat 64 j } } ⋆ R) m')
    (hQ : ParseBodyM6Post c s cnf_ptr cnfBytes i0 R Q)
    (hret : (unsat_v = true ∧ cnf_ptr = cnf_ptr) ∨ (unsat_v = false ∧ oom_v = false)) :
    Q (if unsat_v then 20#64 else 1#64, ()) m' := by
  have hj_len : j = cnfBytes.length := (cursor_eq_iff (by omega) (by omega)).mp heq
  have hemp : (skipWsComments (cnfBytes.drop idx)).isEmpty = true := by
    rw [← hsw, hj_len, List.drop_length]; rfl
  have hpc_eq := hp.pc_eq; simp only [Nat.sub_self, parseClauses] at hpc_eq
  have hpd_some : parseDimacs cnfBytes = some accCnf := by rw [← hpc_eq]; simp [hemp]
  let sf : FullState := { st with core := { st.core with d_cur := cnf_ptr + BitVec.ofNat 64 j } }
  have hlen_sf : sf.LengthsOk c :=
    ⟨{ hp.len_ok.core_ok with vals_len := hp.len_ok.core_ok.vals_len }, hp.len_ok.scratch_ok⟩
  rcases hret with ⟨hunt, _⟩ | ⟨huf, hnf⟩
  · subst hunt
    exact hQ 20#64 sf m' hlen_sf (Or.inr (Or.inr rfl)) hp.fuel_eq hp.oom_eq hp.prb_eq
      (fun _ => ⟨accCnf, hpd_some, shiftDownCnf_unsat hp.vars_pos (hp.uns_inv rfl)⟩)
      (fun h => by cases h) (fun _ => rfl) hm
  · subst huf hnf
    obtain ⟨F_cur, hinv_w, _⟩ := hp.ok_inv rfl rfl
    have hw_sf : FullWitnessInv c (shiftDownCnf accCnf) F_cur sf.core :=
      { hinv_w.2.1 with
        arena := { hinv_w.2.1.arena with len_ok := hinv_w.2.1.arena.len_ok }
        watches := hinv_w.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) }
    have hinv_sf : FullSparseInv c (shiftDownCnf accCnf) sf :=
      ⟨⟨hlen_sf, F_cur, hw_sf⟩,
        hinv_w.2.2.1, hinv_w.2.2.2.1, hinv_w.2.2.2.2.1, hinv_w.2.2.2.2.2⟩
    exact hQ 1#64 sf m' hlen_sf (Or.inr (Or.inl rfl)) hp.fuel_eq hp.oom_eq hp.prb_eq
      (fun h => by cases h) (fun _ => ⟨accCnf, hpd_some, hinv_sf, hp.cl0⟩)
      (fun hut => by rcases (hp.uns_tr hut).2 with ⟨_, _, htr⟩ | ⟨ht, _⟩
                     · rw [Nat.sub_self] at htr; cases htr
                     · cases ht) hm

/-- Eager parse-time unit BCP `full_parse_body_m6` satisfies exact canonical
`Full.fullParseBodySpec` parametrically in `Γ`. -/
theorem full_parse_body_m6_del_wp (Γ : Env)
    (hSkip : ∀ a m Q X, fullSkipClSpec a m Q X → Γ "full_skip_cl" [i64, i64] [.bool] a m Q X)
    (hIngest : ∀ a m Q X, fullIngestClSpec a m Q X →
      Γ "full_ingest_cl" [i64, i64] [i64] a m Q X)
    (hProp : ∀ a m Q X, fullPropagateDelSpec a m Q X → Γ "full_propagate" [i64] [i64] a m Q X)
    (hSwc : ∀ a m Q X, kissatSkipWsCommentsSpec a m Q X →
      Γ "kissat_skip_ws_comments" [i64, i64] [i64] a m Q X) :
    ∀ a m Q X, fullParseBodySpec a m Q X → Func.wp Γ full_parse_body_m6_body a m Q X := by
  rintro ⟨h, cend, ⟨⟩⟩ m Q X
    ⟨c, s, cnf_ptr, cnfBytes, i0, R, rfl, rfl, hfit, hi0, hhdr, hcv0, hdcur, hcl0, hte0, hpr0,
      hal0, hoom0, hprb0, hinc0, hvals0, hwvec0, hinv0, hm, hQ⟩
  have hnc_bd := c.hnc; have hmv_bd := c.hmv; have hmx_bd := c.hmaxv
  unfold dimacsBound at hnc_bd hmv_bd hmx_bd
  have hpd_init : parseClauses c.mv c.nc CNF.empty (cnfBytes.drop i0) = parseDimacs cnfBytes := by
    simp [parseDimacs, hhdr]
  obtain ⟨hinv_w0, hent_0⟩ :=
    m6_init_sparseW hinv0 hcv0 hal0 hte0 hcl0 hinc0 hvals0 hwvec0
  c0_hsteps_nogrp
  refine wp_loop_group
    (fun r (unsat_v, oom_v, has_cl_v, iv, ()) ml => ∃ i idx accCnf st,
      r = c.nc - i ∧ iv = BitVec.ofNat 64 i ∧
      ParseBodyM6Inv c s cnf_ptr cnfBytes i0 i idx accCnf unsat_v oom_v has_cl_v st ∧
      (bytes cnf_ptr cnfBytes ⋆ FullMem c st ⋆ R) ml) ?_ ?_
  · rintro L r ⟨unsat_v, oom_v, has_cl_v, iv, ⟨⟩⟩ ml ih ⟨i, idx, accCnf, st, rfl, rfl, hp, hml⟩
    have hile := hp.i_le; have hidx := hp.idx_le; have hcv_st := hp.cv_eq
    have hdcur_st := hp.d_cur_eq; have hlen_st := hp.len_ok; have hcl_st := hp.cl0
    have hfu_st := hp.fuel_eq; have hoom_st := hp.oom_eq; have hprb_st := hp.prb_eq
    c0_hsteps
    · have hilt : i < c.nc := by clear hm hml hQ; c0_bound
      have hunt : unsat_v = true := by assumption
      subst hunt; have hsub_eq : c.nc - i = (c.nc - (i + 1)) + 1 := by omega
      have hinc : BitVec.ofNat 64 i + 1 = BitVec.ofNat 64 (i + 1) := by
        apply BitVec.eq_of_toNat_eq; change (i % 2 ^ 64 + 1) % 2 ^ 64 = (i + 1) % 2 ^ 64; omega
      c0_call hSkip
      refine ⟨cnf_ptr, BitVec.ofNat 64 c.nc, st.core.d_val, c.mv, cnfBytes, idx,
        FullRest c st ⋆ R, rfl, hfit, by omega, hidx,
        by rw [← hdcur_st]; exact m6_mem_to_dimacs hml, ?_⟩
      cases hpc1 : parseClause c.mv (cnfBytes.drop idx) with
      | none =>
        intro cur' val' m' hm'; c0_hsteps
        exact hQ 0#64 { st with core := { st.core with d_cur := cur', d_val := val' } } m'
          ⟨{ hlen_st.core_ok with vals_len := hlen_st.core_ok.vals_len }, hlen_st.scratch_ok⟩
          (Or.inl rfl) hfu_st hoom_st hprb_st (fun h => by cases h) (fun h => by cases h)
          (fun hut => by rcases (hp.uns_tr hut).2 with ⟨hf, _⟩ | ⟨_, _, hr⟩
                         · cases hf
                         · rw [hsub_eq, parseClauses, hpc1] at hr; cases hr)
          (m6_dimacs_to_mem hm')
      | some p =>
        rcases p with ⟨cl, rest⟩; intro j m' hcl_pos _ hj hdrop hm'; c0_hsteps
        · exact ih (c.nc - (i + 1)) _ _ (by omega)
            ⟨i + 1, j, accCnf.add cl, _, rfl, hinc,
              pb6_skip_step hp hilt hpc1 hcl_pos hj hdrop rfl, m6_dimacs_to_mem hm'⟩
        · cases (by assumption : true = false)
    · have hoo : oom_v = true := by assumption
      subst hoo; exact pb6_oom_exit hp hml hQ
    · have hilt : i < c.nc := by clear hm hml hQ; c0_bound
      have huf : unsat_v = false := by assumption
      have hnf : oom_v = false := by assumption
      subst huf hnf; have hsub_eq : c.nc - i = (c.nc - (i + 1)) + 1 := by omega
      have hinc : BitVec.ofNat 64 i + 1 = BitVec.ofNat 64 (i + 1) := by
        apply BitVec.eq_of_toNat_eq; change (i % 2 ^ 64 + 1) % 2 ^ 64 = (i + 1) % 2 ^ 64; omega
      obtain ⟨F_cur, hinv_st, hent_st⟩ := hp.ok_inv rfl rfl
      c0_call hIngest
      refine ⟨c, accCnf, F_cur, st, cnf_ptr, cnfBytes, idx, R, rfl, rfl, hfit, hidx,
        hcv_st, hdcur_st, hcl_st, hinv_st, hent_st, hml, ?_⟩
      cases hpc1 : parseClause c.mv (cnfBytes.drop idx) with
      | none =>
        intro st' m' hlen' hfu' hoom' hprb' hm'; c0_hsteps
        exact hQ 0#64 st' m' hlen' (Or.inl rfl) (hfu'.trans hfu_st) (hoom'.trans hoom_st)
          (hprb'.trans hprb_st) (fun h => by cases h) (fun h => by cases h)
          (fun hut => by rcases (hp.uns_tr hut).2 with ⟨_, _, htr⟩ | ⟨ht, _⟩
                         · rw [hsub_eq] at htr; cases htr with
                           | conflict _ hpc_s _ _ => rw [hpc1] at hpc_s; cases hpc_s
                           | step _ hpc_s _ _ => rw [hpc1] at hpc_s; cases hpc_s
                         · cases ht) hm'
      | some p =>
        rcases p with ⟨cl, rest⟩
        intro r_in st' j m' hcl_pos _ hj hdrop hlen' hcv' hd' hcl' hfu' hoom' hprb' hr_dom
          hok_in huns_in hunit_ok hunit_fl hm'
        have hpc_next : parseClauses c.mv (c.nc - (i + 1)) (accCnf.add cl) (cnfBytes.drop j) =
            parseDimacs cnfBytes := by rw [← hp.pc_eq, hsub_eq, parseClauses, hpc1, ← hdrop]; rfl
        have hcmv_st : c.mv ≤ c.max_vars := hcv_st ▸ hlen_st.core_ok.cur_vars_le
        have hcmv_st' : c.mv ≤ c.max_vars := hcv' ▸ hlen'.core_ok.cur_vars_le
        rcases hr_dom with rfl | rfl | rfl
        · -- `r_in = 1#64`: update `has_cl`, then optionally run eager `full_propagate`
          obtain ⟨F_cur', hsp', hent'⟩ := hok_in rfl
          have hno_ut_te_eq : st'.core.trail_end = st.core.trail_end →
              ¬ UnitUnsatTrace c.mv (s.core.vals.take (2 * c.mv)) (cnfBytes.drop i0) c.nc := by
            intro hte_eq hut
            rcases (hp.uns_tr hut).2 with ⟨_, _, htr⟩ | ⟨ht, _⟩
            · rw [hsub_eq] at htr; cases htr with
              | conflict hl hpc_s hvf _ =>
                rw [hpc1] at hpc_s
                rcases Prod.mk.inj (Option.some.inj hpc_s) with ⟨hcl_eq, _⟩
                have hr2 := hunit_fl _ hl hcl_eq hvf; cases hr2
              | step hl hpc_s hv0 _ =>
                rw [hpc1] at hpc_s
                rcases Prod.mk.inj (Option.some.inj hpc_s) with ⟨hcl_eq, _⟩
                have hte_inc := (hunit_ok _ hl hcl_eq hv0).2.2.1; omega
            · cases ht
          have h_ut_step :
              UnitUnsatTrace c.mv (s.core.vals.take (2 * c.mv)) (cnfBytes.drop i0) c.nc →
              has_cl_v = false ∧ st'.core.trail_end ≠ st.core.trail_end ∧
              UnitUnsatTrace c.mv st'.core.vals (cnfBytes.drop j) (c.nc - (i + 1)) := by
            intro hut
            rcases (hp.uns_tr hut).2 with ⟨_, hhc0, htr⟩ | ⟨ht, _⟩
            · rw [hsub_eq] at htr; cases htr with
              | conflict hl hpc_s hvf _ =>
                rw [hpc1] at hpc_s
                rcases Prod.mk.inj (Option.some.inj hpc_s) with ⟨hcl_eq, _⟩
                have hr2 := hunit_fl _ hl hcl_eq hvf; cases hr2
              | step hl hpc_s hv0 htr_next =>
                rw [hpc1] at hpc_s
                rcases Prod.mk.inj (Option.some.inj hpc_s) with ⟨hcl_eq, hreq⟩
                obtain ⟨_, hvs, hte_inc, _⟩ := hunit_ok _ hl hcl_eq hv0
                refine ⟨hhc0, by omega, ?_⟩
                rw [hdrop, hreq]
                exact m6_unitUnsatTrace_congr_vals
                  (by simp [hlen_st.core_ok.vals_len]; omega)
                  (by rw [hlen'.core_ok.vals_len]; omega)
                  (fun k hk => (hvs k hk).symm) htr_next
            · cases ht
          c0_hsteps_nogrp
          apply wp_unroll_group; intro J1 hJ1; c0_hsteps_nogrp
          apply wp_unroll_group; intro J2 hJ2; c0_hsteps_nogrp
          -- Join after `if (h->trail_end == old_te) { has_cl = true; }`
          refine wp_join_group (ts := [.bool])
            (fun (hc_new, ()) mj => mj = m' ∧
              (UnitUnsatTrace c.mv (s.core.vals.take (2 * c.mv)) (cnfBytes.drop i0) c.nc →
                hc_new = false))
            (fun _ (hc_new, ()) mj ⟨hmj, hhc_ut⟩ => ?_)
            (fun Jhc hJhc => ?_)
          · subst mj
            c0_hsteps_nogrp
            -- Join after `if (has_cl && h->propagated < h->trail_end)`
            refine wp_join_group (ts := [.bool, .bool])
              (fun (uns_n, oom_n, ()) mp => ∃ st_p : FullState,
                ParseBodyM6Inv c s cnf_ptr cnfBytes i0 (i + 1) j (accCnf.add cl)
                  uns_n oom_n hc_new st_p ∧
                (bytes cnf_ptr cnfBytes ⋆ FullMem c st_p ⋆ R) mp)
              (fun _ (uns_n, oom_n, ()) mp ⟨st_p, hp_p, hmp⟩ => by
                c0_hsteps_nogrp
                exact ih (c.nc - (i + 1)) _ _ (by omega)
                  ⟨i + 1, j, accCnf.add cl, st_p, rfl, hinc, hp_p, hmp⟩)
              (fun Jp hJp => ?_)
            have hinv_noprop :
                ParseBodyM6Inv c s cnf_ptr cnfBytes i0 (i + 1) j (accCnf.add cl)
                  false false hc_new st' :=
              ⟨by omega, hj, hcv', hd', hlen', hcl', hfu'.trans hfu_st, hoom'.trans hoom_st,
                hprb'.trans hprb_st, cnfVarsPos_add hp.vars_pos hcl_pos, hpc_next,
                (fun h => by cases h), (fun _ _ => ⟨F_cur', hsp', hent'⟩),
                (fun hut => ⟨rfl, Or.inl ⟨rfl, hhc_ut hut, (h_ut_step hut).2.2⟩⟩)⟩
            c0_hsteps_nogrp
            · have hhc_true : hc_new = true := by assumption
              have hnot_ut :
                  ¬ UnitUnsatTrace c.mv (s.core.vals.take (2 * c.mv)) (cnfBytes.drop i0) c.nc :=
                fun hut => by have := hhc_ut hut; rw [hhc_true] at this; cases this
              c0_call hProp
              refine ⟨c, shiftDownCnf (accCnf.add cl), F_cur', st',
                bytes cnf_ptr cnfBytes ⋆ R, rfl, hsp'.1, hsp'.2.1, hsp'.2.2.2.2.2,
                sep_ac hm', ?_⟩
              intro pr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ delayed_pr m_pr s_pr
                hlen_pr hw_pr _ hperm_pr _ hpr_dom hpr0 hpr1 _ _ hm_pr
              have hm_pr' : (bytes cnf_ptr cnfBytes ⋆ FullMem c s_pr ⋆ R) m_pr := sep_ac hm_pr
              have hsp_pr : FullSparseInvW c (shiftDownCnf (accCnf.add cl)) F_cur' s_pr :=
                m6_sparseInvW_of_perm hsp' hlen_pr hw_pr hperm_pr rfl rfl rfl ⟨rfl, rfl⟩
              have hsp_rest : FullSparseInvW c (shiftDownCnf (accCnf.add cl)) F_cur'
                  { core := { s_pr.core with fuel := st'.core.fuel }
                    scratch := { s_pr.scratch with search_ticks := st'.scratch.search_ticks } } :=
                m6_sparseInvW_with_fuel_ticks hsp_pr st'.core.fuel st'.scratch.search_ticks
              rcases hpr_dom with rfl | rfl | rfl
              · have hoom_pr0 : s_pr.core.oom = 0#64 := (hpr0 rfl).2.1 (hoom'.trans hoom_st)
                c0_hsteps
                refine hJp (false, false, ()) _ ⟨_, ?_, sep_ac hm⟩
                exact ⟨by omega, hj, hcv', hd', hsp_rest.1, hcl', hfu'.trans hfu_st, hoom_pr0,
                  hprb'.trans hprb_st, cnfVarsPos_add hp.vars_pos hcl_pos, hpc_next,
                  (fun h => by cases h), (fun _ _ => ⟨F_cur', hsp_rest, hent'⟩),
                  (fun hut => False.elim (hnot_ut hut))⟩
              · have hoom_pr1 : s_pr.core.oom = 0#64 := (hpr1 rfl).2.1
                have huns_pr1 : (shiftDownCnf (accCnf.add cl)).Unsat :=
                  level0_unsat_of_conflict_okW (s := s_pr) hw_pr hcl' (hpr1 rfl).2.2
                c0_hsteps
                refine hJp (true, false, ()) _ ⟨_, ?_, sep_ac hm⟩
                exact ⟨by omega, hj, hcv', hd', hsp_rest.1, hcl', hfu'.trans hfu_st, hoom_pr1,
                  hprb'.trans hprb_st, cnfVarsPos_add hp.vars_pos hcl_pos, hpc_next,
                  (fun _ => huns_pr1), (fun h => by cases h),
                  (fun hut => False.elim (hnot_ut hut))⟩
              · c0_hsteps
                refine hJp (false, true, ()) _ ⟨_, ?_, sep_ac hm⟩
                exact ⟨by omega, hj, hcv', hd',
                  ⟨{ hsp_rest.1.core_ok with cur_vars_le := hsp_rest.1.core_ok.cur_vars_le },
                    hsp_rest.1.scratch_ok⟩,
                  hcl', hfu'.trans hfu_st, rfl, hprb'.trans hprb_st,
                  cnfVarsPos_add hp.vars_pos hcl_pos, hpc_next,
                  (fun h => by cases h), (fun _ h => by cases h),
                  (fun hut => False.elim (hnot_ut hut))⟩
            · exact hJp (false, false, ()) m' ⟨st', hinv_noprop, hm'⟩
            · exact hJp (false, false, ()) m' ⟨st', hinv_noprop, hm'⟩
          · -- Body of `if (h->trail_end == old_te)`
            c0_hsteps_nogrp
            · have hte_eq_bv : BitVec.ofNat 64 st'.core.trail_end =
                  BitVec.ofNat 64 st.core.trail_end := by assumption
              have hte_eq : st'.core.trail_end = st.core.trail_end := by
                have h1 := congrArg BitVec.toNat hte_eq_bv
                have hle1 := hlen'.core_ok.trail_end_le
                have hle0 := hlen_st.core_ok.trail_end_le
                rw [bv64_ofNat_toNat (by omega), bv64_ofNat_toNat (by omega)] at h1; exact h1
              exact hJhc (true, ()) m' ⟨rfl, fun hut => False.elim (hno_ut_te_eq hte_eq hut)⟩
            · exact hJhc (has_cl_v, ()) m' ⟨rfl, fun hut => (h_ut_step hut).1⟩
        · -- `r_in = 2#64`: `unsat_seen = true`
          c0_hsteps
          exact ih (c.nc - (i + 1)) _ _ (by omega)
            ⟨i + 1, j, accCnf.add cl, st', rfl, hinc,
              ⟨by omega, hj, hcv', hd', hlen', hcl', hfu'.trans hfu_st, hoom'.trans hoom_st,
                hprb'.trans hprb_st, cnfVarsPos_add hp.vars_pos hcl_pos, hpc_next,
                (fun _ => huns_in rfl), (fun h => by cases h),
                (fun hut => by
                  refine ⟨rfl, Or.inr ⟨rfl, ?_⟩⟩
                  rcases (hp.uns_tr hut).2 with ⟨_, _, htr⟩ | ⟨ht, _⟩
                  · rw [hsub_eq] at htr; cases htr with
                    | conflict _ hpc_s _ hrest =>
                      rw [hpc1] at hpc_s
                      rcases Prod.mk.inj (Option.some.inj hpc_s) with ⟨_, hreq⟩
                      rwa [hdrop, hreq]
                    | step hl hpc_s hv0 _ =>
                      rw [hpc1] at hpc_s
                      rcases Prod.mk.inj (Option.some.inj hpc_s) with ⟨hcl_eq, _⟩
                      exact absurd (hunit_ok _ hl hcl_eq hv0).1 (by decide)
                  · cases ht)⟩, hm'⟩
        · -- `r_in = 3#64`: `oom_seen = true`
          c0_hsteps
          exact ih (c.nc - (i + 1)) _ _ (by omega)
            ⟨i + 1, j, accCnf.add cl, st', rfl, hinc,
              ⟨by omega, hj, hcv', hd', hlen', hcl', hfu'.trans hfu_st, hoom'.trans hoom_st,
                hprb'.trans hprb_st, cnfVarsPos_add hp.vars_pos hcl_pos, hpc_next,
                (fun h => by cases h), (fun _ h => by cases h),
                (fun hut => by
                  rcases (hp.uns_tr hut).2 with ⟨_, _, htr⟩ | ⟨ht, _⟩
                  · rw [hsub_eq] at htr; cases htr with
                    | conflict hl hpc_s hvf _ =>
                      rw [hpc1] at hpc_s
                      rcases Prod.mk.inj (Option.some.inj hpc_s) with ⟨hcl_eq, _⟩
                      exact absurd (hunit_fl _ hl hcl_eq hvf) (by decide)
                    | step hl hpc_s hv0 _ =>
                      rw [hpc1] at hpc_s
                      rcases Prod.mk.inj (Option.some.inj hpc_s) with ⟨hcl_eq, _⟩
                      exact absurd (hunit_ok _ hl hcl_eq hv0).1 (by decide)
                  · cases ht)⟩, hm'⟩
    · have hoo : oom_v = true := by assumption
      subst hoo; exact pb6_oom_exit hp hml hQ
    · have hieq : i = c.nc := by clear hml hQ; c0_bound
      subst hieq; c0_call hSwc
      refine ⟨cnf_ptr, cnfBytes, idx, FullMem c st ⋆ R, hdcur_st, rfl, hfit, hidx,
        sep_ac hml, fun j _ hj hsw => ?_⟩
      c0_hsteps
      · exact pb6_eof_ne hp hj hsw (by assumption) hfit (sep_ac hm) hQ
      · have hunt : unsat_v = true := by assumption
        simpa [hunt] using pb6_eof_done hp hj hsw (by assumption) hfit (sep_ac hm) hQ
          (Or.inl ⟨hunt, rfl⟩)
      · have huf : unsat_v = false := by assumption
        have hnf : oom_v = false := by assumption
        simpa [huf] using pb6_eof_done hp hj hsw (by assumption) hfit (sep_ac hm) hQ
          (Or.inr ⟨huf, hnf⟩)
  · intro L hL; c0_hsteps
    have hcmv0 : c.mv ≤ c.max_vars := hcv0 ▸ hinv0.1.lengths.core_ok.cur_vars_le
    exact hL c.nc _ m ⟨0, i0, CNF.empty, s, by simp, rfl,
      ⟨Nat.zero_le _, hi0, hcv0, hdcur, hinv0.1.lengths, hcl0, rfl, hoom0, hprb0,
        cnfVarsPos_empty, by simpa using hpd_init, (fun hc => by cases hc),
        fun _ _ => ⟨[], hinv_w0, hent_0⟩,
        fun hut => ⟨rfl, Or.inl ⟨rfl, rfl, by
          rw [Nat.sub_zero]
          refine m6_unitUnsatTrace_congr_vals
            (by rw [List.length_take, hinv0.1.lengths.core_ok.vals_len]; omega)
            (by rw [hinv0.1.lengths.core_ok.vals_len]; omega) (fun k hk => ?_) hut
          rw [List.getElem?_take_of_lt hk]⟩⟩⟩, hm⟩

theorem full_parse_body_m6_wp (Γ : Env)
    (hSkip : ∀ a m Q X, fullSkipClSpec a m Q X → Γ "full_skip_cl" [i64, i64] [.bool] a m Q X)
    (hIngest : ∀ a m Q X, fullIngestClSpec a m Q X →
      Γ "full_ingest_cl" [i64, i64] [i64] a m Q X)
    (hProp : ∀ a m Q X, fullPropagateSpec a m Q X → Γ "full_propagate" [i64] [i64] a m Q X)
    (hSwc : ∀ a m Q X, kissatSkipWsCommentsSpec a m Q X →
      Γ "kissat_skip_ws_comments" [i64, i64] [i64] a m Q X) :
    ∀ a m Q X, fullParseBodySpec a m Q X → Func.wp Γ full_parse_body_m6_body a m Q X :=
  full_parse_body_m6_del_wp Γ hSkip hIngest
    (fun a m Q X h => hProp a m Q X (fullPropagateSpec_of_del h)) hSwc

end ParseBodyM6Proof

/-! ## 4. Pure / Read-Only ProbSAT Helpers (`cb_inv`, `score`, `break`) -/

section PureWalkProofs

open scoped FullArenaTactics

private theorem m6_cb_lin_ge {base lo coeff : BitVec 64} {avg : BitVec 64}
    (hb : 640 ≤ base.toNat) (hb_hi : base.toNat ≤ 2000) (hc_hi : coeff.toNat ≤ 1000)
    (hlo : lo.toNat ≤ avg.toNat) (hhi : avg.toNat ≤ lo.toNat + 256) :
    640 ≤ (base + (((avg - lo) * coeff) >>> (8 : Nat))).toNat := by
  have hsub : (avg - lo).toNat = avg.toNat - lo.toNat := by
    rw [BitVec.toNat_sub]; omega
  have hmul : ((avg - lo) * coeff).toNat = (avg.toNat - lo.toNat) * coeff.toNat := by
    have : (avg.toNat - lo.toNat) * coeff.toNat ≤ 256 * 1000 :=
      Nat.mul_le_mul (by omega) hc_hi
    rw [BitVec.toNat_mul, hsub, Nat.mod_eq_of_lt (by omega)]
  have hsh : (((avg - lo) * coeff) >>> (8 : Nat)).toNat ≤ 1000 := by
    have : (avg.toNat - lo.toNat) * coeff.toNat ≤ 256 * 1000 :=
      Nat.mul_le_mul (by omega) hc_hi
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, hmul]; omega
  rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]; omega

/-- Pure `full_walk_cb_inv_m6` satisfies `m6WalkCbInvSpec` (never divides by zero). -/
theorem full_walk_cb_inv_m6_wp (Γ : Env) :
    ∀ a m Q X, m6WalkCbInvSpec a m Q X → Func.wp Γ full_walk_cb_inv_m6_body a m Q X := by
  rintro ⟨tot, ncl, wc, ⟨⟩⟩ m Q X hQ
  c0_hsteps_nogrp
  · exact hQ _
  · exact hQ _
  · refine wp_join_group (ts := [i64]) (fun (_avg, ()) m1 => m1 = m)
      (fun _ ⟨avg, ⟨⟩⟩ m1 hm1 => ?_) (fun J hJ => ?_)
    · subst m1
      c0_hsteps_nogrp
      refine wp_join_group (ts := [i64])
        (fun (cb, ()) m2 => m2 = m ∧ 640 ≤ cb.toNat)
        (fun _ ⟨cb, ⟨⟩⟩ m2 ⟨hm2, hcb⟩ => ?_) (fun Jc hJc => ?_)
      · subst m2
        have hnz : cb ≠ 0#64 := fun h => by rw [h] at hcb; simp at hcb
        c0_hsteps; exact hQ _
      · c0_hsteps
        all_goals first
        | exact hJc (640#64, ()) m ⟨rfl, by decide⟩
        | exact hJc (1894#64, ()) m ⟨rfl, by decide⟩
        | exact hJc (_, ()) m ⟨rfl, m6_cb_lin_ge (by decide) (by decide) (by decide)
            (by c0_bound) (by c0_bound)⟩
    · c0_hsteps_nogrp
      · exact hJ (2048#64, ()) m rfl
      · have hncl_nz : ncl ≠ 0#64 := by assumption
        c0_hsteps; exact hJ (_, ()) m rfl

/-- Pure `full_walk_score_m6` satisfies `m6WalkScoreSpec` (`r ≤ 2^30`). -/
theorem full_walk_score_m6_wp (Γ : Env) :
    ∀ a m Q X, m6WalkScoreSpec a m Q X → Func.wp Γ full_walk_score_m6_body a m Q X := by
  rintro ⟨inv_q16, brk, ⟨⟩⟩ m Q X hQ
  c0_hsteps_nogrp
  refine wp_join_group (ts := [i64]) (fun (lim, ()) m1 => m1 = m ∧ lim.toNat ≤ 30)
    (fun _ ⟨lim, ⟨⟩⟩ m1 ⟨hm1, hlim⟩ => ?_) (fun Jl hJl => ?_)
  · subst m1
    c0_hsteps_nogrp
    refine wp_join_group (ts := [i64]) (fun (inv, ()) m2 => m2 = m ∧ inv.toNat ≤ 65536)
      (fun _ ⟨inv, ⟨⟩⟩ m2 ⟨hm2, hinv⟩ => ?_) (fun Ji hJi => ?_)
    · subst m2
      c0_hsteps_nogrp
      refine wp_loop_group (ts := [i64, i64])
        (fun rem (sc, i, ()) ml => ml = m ∧ i.toNat ≤ lim.toNat ∧ rem = lim.toNat - i.toNat ∧
          sc.toNat ≤ 2 ^ 30) ?_ ?_
      · rintro _ rem ⟨sc, i, ⟨⟩⟩ ml ih ⟨rfl, hile, rfl, hsc⟩
        have hmul_le : sc.toNat * inv.toNat ≤ 2 ^ 30 * 65536 := Nat.mul_le_mul hsc hinv
        have hsc' : ((sc * inv) >>> (16 : Nat)).toNat ≤ 2 ^ 30 := by
          have hmul : (sc * inv).toNat = sc.toNat * inv.toNat := by
            rw [BitVec.toNat_mul, Nat.mod_eq_of_lt (by omega : sc.toNat * inv.toNat < 2 ^ 64)]
          rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, hmul]; omega
        c0_hsteps_nogrp
        · exact hQ 1#32 (by decide)
        · have hilt : i.toNat < lim.toNat := by c0_bound
          have hi1 : (i + 1#64).toNat = i.toNat + 1 := by bv_omega
          exact ih (lim.toNat - (i + 1#64).toNat) (_, i + 1#64, ()) ml
            (by rw [hi1]; omega) ⟨rfl, by rw [hi1]; omega, rfl, hsc'⟩
        · c0_hsteps
          · exact hQ 1#32 (by decide)
          · exact hQ (sc.setWidth 32) (by
              rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]; exact hsc)
      · intro _ hL; c0_hsteps
        exact hL lim.toNat (1073741824#64, 0#64, ()) m ⟨rfl, by simp, by simp, by decide⟩
    · c0_hsteps
      · exact hJi (65536#64, ()) m ⟨rfl, by decide⟩
      · exact hJi (inv_q16, ()) m ⟨rfl, by c0_bound⟩
  · c0_hsteps
    · exact hJl (30#64, ()) m ⟨rfl, by decide⟩
    · exact hJl (brk, ()) m ⟨rfl, by c0_bound⟩

/-- Read-only CSR `full_walk_break_m6` satisfies `m6WalkBreakSpec`. -/
theorem full_walk_break_m6_wp (Γ : Env) :
    ∀ a m Q X, m6WalkBreakSpec a m Q X → Func.wp Γ full_walk_break_m6_body a m Q X := by
  rintro ⟨h, lit, ncl, max_cl, occ_cap, ⟨⟩⟩ m Q X ⟨c, s, R, ⟨rfl, hncl, hcap⟩, hlen, hm, hQ⟩
  dsimp only [fullSafetySlice] at hm hlen hQ
  obtain hmx : c.max_vars < 2 * dimacsBound := c.hmaxv
  obtain hsca : c.scratch_cap < dimacsBound := c.hscr
  unfold dimacsBound at hmx hsca
  obtain hcv_le := hlen.core_ok.cur_vars_le
  obtain hws1l := hlen.scratch_ok.work_stk1_len
  obtain hws2l := hlen.scratch_ok.work_stk2_len
  obtain hsbl := hlen.scratch_ok.scratch_buf_len
  have hsh_cv : ((BitVec.ofNat 64 s.core.cur_vars) <<< (1 : Nat)).toNat = 2 * s.core.cur_vars := by
    rw [BitVec.toNat_shiftLeft, bv64_ofNat_toNat (by omega), Nat.shiftLeft_eq]
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  have hsh_mc : (max_cl <<< (1 : Nat)).toNat = 2 * max_cl.toNat := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]; omega
  c0_hsteps_nogrp
  · exact hQ (0#64, ()) s m rfl hlen rfl hm
  · exact hQ (0#64, ()) s m rfl hlen rfl hm
  · exact hQ (0#64, ()) s m rfl hlen rfl hm
  · have hnlit_eq : ((lit ^^^ 1#32).setWidth 64).toNat = lit.toNat ^^^ 1 := by
      rw [zext_toNat _ (by decide), BitVec.toNat_xor]; rfl
    have hnlit_lt : lit.toNat ^^^ 1 < 2 * s.core.cur_vars := by
      have h1 : ¬2 * (s.core.cur_vars % 2 ^ 64) % 2 ^ 64 ≤ lit.toNat ^^^ 1 := by assumption
      rw [Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64),
        Nat.mod_eq_of_lt (by omega : 2 * s.core.cur_vars < 2 ^ 64)] at h1
      omega
    have hnlit_ws1 : lit.toNat ^^^ 1 < s.scratch.work_stk1.length := by rw [hws1l]; omega
    have hnlit_ws2 : lit.toNat ^^^ 1 < s.scratch.work_stk2.length := by rw [hws2l]; omega
    let off64 := (s.scratch.work_stk1[lit.toNat ^^^ 1]'hnlit_ws1).setWidth 64
    let len64 := (s.scratch.work_stk2[lit.toNat ^^^ 1]'hnlit_ws2).setWidth 64
    have hoff_eq : off64.toNat = (s.scratch.work_stk1[lit.toNat ^^^ 1]'hnlit_ws1).toNat :=
      zext_toNat _ (by decide)
    have hlen_eq : len64.toNat = (s.scratch.work_stk2[lit.toNat ^^^ 1]'hnlit_ws2).toNat :=
      zext_toNat _ (by decide)
    have hoff_le : off64.toNat ≤ occ_cap.toNat := by
      have h1 : ¬occ_cap.toNat < (s.scratch.work_stk1[lit.toNat ^^^ 1]'hnlit_ws1).toNat := by
        assumption
      omega
    have hlen_le : len64.toNat ≤ occ_cap.toNat - off64.toNat := by
      have h1 : ¬(2 ^ 64 - (s.scratch.work_stk1[lit.toNat ^^^ 1]'hnlit_ws1).toNat +
          occ_cap.toNat) % 2 ^ 64 < (s.scratch.work_stk2[lit.toNat ^^^ 1]'hnlit_ws2).toNat := by
        assumption
      have hsub : (2 ^ 64 - (s.scratch.work_stk1[lit.toNat ^^^ 1]'hnlit_ws1).toNat +
          occ_cap.toNat) % 2 ^ 64 = occ_cap.toNat - off64.toNat := by
        have : 2 ^ 64 - off64.toNat + occ_cap.toNat =
            2 ^ 64 + (occ_cap.toNat - off64.toNat) := by omega
        rw [← hoff_eq, this, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
      rw [hsub] at h1; omega
    refine wp_loop_group (ts := [i64, i64])
      (fun rem (_brk, k, ()) ml => ml = m ∧ k.toNat ≤ len64.toNat ∧
        rem = len64.toNat - k.toNat) ?_ ?_
    · rintro _ rem ⟨brk_v, k, ⟨⟩⟩ ml ih ⟨rfl, hkle, rfl⟩
      c0_hsteps_nogrp
      · have hklt : k.toNat < len64.toNat := by
          have : k.toNat < (s.scratch.work_stk2[lit.toNat ^^^ 1]'hnlit_ws2).toNat := by assumption
          omega
        have hocc_idx : ((max_cl * 5#64 + off64) + k).toNat =
            5 * max_cl.toNat + off64.toNat + k.toNat := by bv_omega
        have hocc_lt : ((max_cl * 5#64 + off64) + k).toNat < s.scratch.scratch_buf.length := by
          rw [hocc_idx, hsbl]; omega
        have hk1 : (k + 1#64).toNat = k.toNat + 1 := by bv_omega
        let ci32 := s.scratch.scratch_buf[((max_cl * 5#64 + off64) + k).toNat]'hocc_lt
        c0_hsteps
        · have hci_lt : ci32.toNat < ncl.toNat := by
            have hidx_eq : ((max_cl * 5#64 + off64) + k).toNat =
                (max_cl.toNat * (5 : BitVec 64).toNat +
                  (s.scratch.work_stk1[lit.toNat ^^^ 1]'hnlit_ws1).toNat + k.toNat) % 2 ^ 64 := by
              rw [hocc_idx, hoff_eq, show (5 : BitVec 64).toNat = 5 from rfl,
                Nat.mod_eq_of_lt (by omega)]; omega
            simpa only [ci32, hidx_eq] using hc
          have hsat_idx : ((max_cl <<< (1 : Nat)) + ci32.setWidth 64).toNat =
              2 * max_cl.toNat + ci32.toNat := by
            have hz : (ci32.setWidth 64).toNat = ci32.toNat := zext_toNat _ (by decide)
            rw [BitVec.toNat_add, hsh_mc, hz, Nat.mod_eq_of_lt (by omega)]
          have hsat_lt : ((max_cl <<< (1 : Nat)) + ci32.setWidth 64).toNat <
              s.scratch.scratch_buf.length := by rw [hsat_idx, hsbl]; omega
          c0_hsteps
          · exact ih (len64.toNat - (k + 1#64).toNat) (brk_v + 1#64, k + 1#64, ()) ml
              (by rw [hk1]; omega) ⟨rfl, by rw [hk1]; omega, rfl⟩
          · exact ih (len64.toNat - (k + 1#64).toNat) (brk_v, k + 1#64, ()) ml
              (by rw [hk1]; omega) ⟨rfl, by rw [hk1]; omega, rfl⟩
        · exact ih (len64.toNat - (k + 1#64).toNat) (brk_v, k + 1#64, ()) ml
            (by rw [hk1]; omega) ⟨rfl, by rw [hk1]; omega, rfl⟩
      · exact hQ (brk_v, ()) s ml rfl hlen rfl hm
    · intro _ hL; c0_hsteps; exact hL len64.toNat (0#64, 0#64, ()) m ⟨rfl, by simp, by simp⟩

end PureWalkProofs

end LeanQbe.T.Examples.Kissat.FullM6WalkParse
