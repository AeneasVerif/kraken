module

public import LeanQbe.T.Examples.Kissat.FullSpec
public import LeanQbe.T.Examples.Kissat.FullArena
public import LeanQbe.T.Examples.Kissat.DimacsLemmas
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat `D-Full` Top-Level Orchestrator Proofs (`Stage 4`, UNSAT-Only)

Proves parametric `(Γ : Env)` `Func.wp` theorems directly against canonical `FullSpec` contracts
for all `6` top orchestrators in `Full.lean` (`indices 160..165`, strictly UNSAT-only, zero SAT
model-reconstruction proofs):
1. `full_probe` (`full_probe_wp`)
2. `full_eliminate` (`full_eliminate_wp`)
3. `full_preprocess` (`full_preprocess_wp`)
4. `full_simplify` (`full_simplify_wp`)
5. `full_search` (`full_search_wp`)
6. `kissat_solve_bytes` (`kissat_solve_bytes_core_wp`, `kissat_solve_bytes_wp`)
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.Full

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open Kraken.Bedrock2.Test

/-! ## 1. Pure helpers for `FullSparseInv`, `FullDenseInv`, DIMACS positivity, and framing -/

private theorem fullSparseInv_with_scratch_keep {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullSparseInv c F0 s) {sc' : FullScratch} (hok : sc'.LengthsOk c)
    (hll : sc'.last_learned = s.scratch.last_learned)
    (hext : sc'.extend_len = s.scratch.extend_len) :
    FullSparseInv c F0 { s with scratch := sc' } :=
  h.of_safetySlice (h.lengths.with_scratch hok) rfl ⟨hll, hext⟩

private theorem fullDenseInv_with_flags {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullDenseInv c F0 s) {fl' : List (BitVec 32)} (hflen : fl'.length = c.max_vars) :
    FullDenseInv c F0 { s with core := { s.core with flags := fl' } } := by
  obtain ⟨F_cur, hw⟩ := h.1.witness
  have hlen' : ({ s with core := { s.core with flags := fl' } } : FullState).LengthsOk c :=
    ⟨{ h.lengths.core_ok with flags_len := hflen }, h.lengths.scratch_ok⟩
  exact ⟨⟨hlen', F_cur, { hw with
    arena := { hw.arena with len_ok := hw.arena.len_ok }
    watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) }⟩,
    h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

private theorem fullSparseInvW_of_perm {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
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

private theorem fullSparseInv_of_perm_core {c : FullCfg} {F0 : CNF Nat} {s s' : FullState}
    (hsp : FullSparseInv c F0 s) (hcore' : FullCoreInv c F0 s')
    (hperm : FullArenaPermEq s.core s'.core)
    (hmrk : s'.core.mrk = s.core.mrk) (hlm : s'.core.lit_mark = s.core.lit_mark)
    (hdm : s'.core.dense_mode = s.core.dense_mode)
    (hpres : FullExtScratchPres s s') : FullSparseInv c F0 s' := by
  refine ⟨hcore', ?_, ?_, ?_, hdm.trans hsp.2.2.2.2⟩
  · exact ⟨fun v hv => by rw [hmrk]; exact hsp.2.1.1 v hv,
      fun l hl => by rw [hlm]; exact hsp.2.1.2 l hl⟩
  · intro ref href hng
    have href0 : ref ∈ fullArenaClauseRefsCore s.core := hperm.2.1 ▸ href
    obtain ⟨_, hgb, hp⟩ := hperm.2.2 ref href0
    exact (hp.map (· / 2)).nodup_iff.mpr (hsp.2.2.1 ref href0 (hgb.symm.trans hng))
  · exact hsp.2.2.2.1.of_pres hpres fun ref href => by
      change ref ∈ fullArenaClauseRefsCore s'.core; rw [hperm.2.1]; exact href

private theorem fullSparseInv_of_same_arena {c : FullCfg} {F0 : CNF Nat} {s s' : FullState}
    (hsp : FullSparseInv c F0 s) (hcore' : FullCoreInv c F0 s')
    (hmrk : s'.core.mrk = s.core.mrk) (hlm : s'.core.lit_mark = s.core.lit_mark)
    (har : s'.core.arena = s.core.arena) (hal : s'.core.arena_len = s.core.arena_len)
    (hdm : s'.core.dense_mode = s.core.dense_mode)
    (hpres : FullExtScratchPres s s') : FullSparseInv c F0 s' := by
  refine ⟨hcore', ?_, ?_, ?_, hdm.trans hsp.2.2.2.2⟩
  · exact ⟨fun v hv => by rw [hmrk]; exact hsp.2.1.1 v hv,
      fun l hl => by rw [hlm]; exact hsp.2.1.2 l hl⟩
  · unfold FullArenaVarsNodup fullArenaClauseRefs fullArenaClauseRefsCore
      fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore
      fullArenaClauseLits fullArenaClauseLitsCore fullArenaClauseSizeCore
    rw [har, hal]; exact hsp.2.2.1
  · exact hsp.2.2.2.1.of_pres hpres fun ref href => by
      unfold fullArenaClauseRefs fullArenaClauseRefsCore at href ⊢; rwa [har, hal]

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
    rw [BitVec.toNat_sub, hmax, bv64_ofNat_toNat (by omega)]; omega
  rw [hsub, bv_ult_eq (by omega) (by omega)]
  simp only [decide_eq_false_iff_not]; omega

private theorem fullAlignPad_bv_eq (p : BitVec 64) :
    (8 - (p &&& 7)) &&& 7 = BitVec.ofNat 64 (fullAlignPad p) := by
  apply BitVec.eq_of_toNat_eq
  rw [show ((8 : BitVec 64) - (p &&& 7)) &&& 7 = (8#64 - (p &&& 7#64)) &&& 7#64 from rfl,
    fullAlignPad_eq, bv64_ofNat_toNat (by have := fullAlignPad_lt8 p; omega)]

private theorem full_merge_reg {cnf_ptr work_ptr : BitVec 64} {cnfBytes : List UInt8}
    {wlen : Nat} {R : Mem 64 → Prop} (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hw_ge : fullAlignPad work_ptr ≤ wlen) {m' : Mem 64}
    (hm' : (bytes cnf_ptr cnfBytes ⋆
      region (work_ptr + BitVec.ofNat 64 (fullAlignPad work_ptr))
        (wlen - fullAlignPad work_ptr) ⋆
      (region work_ptr (fullAlignPad work_ptr) ⋆ R)) m') :
    (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m' := by
  have h1 : ((region work_ptr (fullAlignPad work_ptr) ⋆
      region (work_ptr + BitVec.ofNat 64 (fullAlignPad work_ptr))
        (wlen - fullAlignPad work_ptr)) ⋆
      (bytes cnf_ptr cnfBytes ⋆ R)) m' := sep_ac hm'
  have h2 : (region work_ptr (fullAlignPad work_ptr + (wlen - fullAlignPad work_ptr)) ⋆
      (bytes cnf_ptr cnfBytes ⋆ R)) m' :=
    sep_mono (fun _ f => pad_region_merge (by omega) f) h1
  rw [show fullAlignPad work_ptr + (wlen - fullAlignPad work_ptr) = wlen by omega] at h2
  exact sep_ac h2

private theorem full_merge_arena {cnf_ptr work_ptr : BitVec 64} {cnfBytes : List UInt8}
    {wlen : Nat} {R : Mem 64 → Prop} {c : FullCfg} {st : FullState}
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64) (hw_ge : fullAlignPad work_ptr ≤ wlen)
    (hch : c.hdr = work_ptr + BitVec.ofNat 64 (fullAlignPad work_ptr))
    (hca : c.avail = wlen - fullAlignPad work_ptr) (hlen : st.LengthsOk c) {m' : Mem 64}
    (hm' : (bytes cnf_ptr cnfBytes ⋆ FullMem c st ⋆
      (region work_ptr (fullAlignPad work_ptr) ⋆ R)) m') :
    (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m' := by
  apply full_merge_reg hwfit hw_ge
  have h1 : (FullMem c st ⋆
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr (fullAlignPad work_ptr) ⋆ R)) m' := sep_ac hm'
  have h2 : (region (work_ptr + BitVec.ofNat 64 (fullAlignPad work_ptr))
      (wlen - fullAlignPad work_ptr) ⋆
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr (fullAlignPad work_ptr) ⋆ R)) m' :=
    sep_mono (fun _ f => by rw [← hch, ← hca]; exact FullArenaInv.to_region ⟨hlen, f⟩) h1
  exact sep_ac h2

/-- Lexicographic termination measure for `full_search`: either `fuel` strictly decreases (on any
propagation step) or `propagated = trail_end` flips to `propagated < trail_end` (on `decide`). -/
def searchVariant (st : FullState) : Nat :=
  2 * st.core.fuel.toNat + if st.core.propagated = st.core.trail_end then 1 else 0

/-! ## 2. `full_probe`, `full_eliminate`, `full_preprocess`, `full_simplify` -/

section TopOrchestrators

open scoped FullArenaTactics

local macro "fp_step" : tactic => `(tactic| (try (change wp _ _ _ _ _); c0_step))
local macro "fp_steps" : tactic => `(tactic| (try (change wp _ _ _ _ _); c0_steps))

/-- `Func.wp` proof for `full_probe` (`Full.lean:1054-1067`) against canonical `fullProbeSpec`. -/
theorem full_probe_wp (Γ : Env)
    (hIsqrt : ∀ a m Q X, fullIsqrtSpec a m Q X → Γ "full_isqrt" [i64] [i64] a m Q X)
    (hSubst : ∀ a m Q X, fullSubstituteSpec a m Q X → Γ "full_substitute" [i64] [i64] a m Q X)
    (hCong : ∀ a m Q X, fullCongruenceSpec a m Q X → Γ "full_congruence" [i64] [i64] a m Q X)
    (hSweep : ∀ a m Q X, fullSweepSatSpec a m Q X → Γ "full_sweep_sat" [i64] [i64] a m Q X)
    (hTrans : ∀ a m Q X, fullTransitiveSpec a m Q X → Γ "full_transitive" [i64] [i64] a m Q X)
    (hPRun : ∀ a m Q X, fullProbeRunSpec a m Q X →
      Γ "full_probe_run" [i64, i64] [i64] a m Q X)
    (hViv : ∀ a m Q X, fullVivifySpec a m Q X → Γ "full_vivify" [i64, i64] [i64] a m Q X) :
    ∀ args m Q X, fullProbeSpec args m Q X → Func.wp Γ full_probe_body args m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hinv, _, hm, hQ⟩
  unfold Func.wp full_probe_body; fp_steps
  c0_call hIsqrt
  intro r_sq _ _ _
  fp_steps
  let s0 : FullState :=
    { s with
      scratch := { s.scratch with
        probings := s.scratch.probings + 1#64
        probe_limit := s.scratch.conflicts + 500#64 * r_sq } }
  have hinv0 : FullSparseInv c F0 s0 :=
    fullSparseInv_with_scratch_keep hinv { hinv.lengths.scratch_ok with } rfl rfl
  have hfu0 : s0.core.fuel = s.core.fuel := rfl
  -- 1. full_substitute(h)
  c0_call hSubst; refine ⟨c, F0, s0, R, rfl, hinv0, hm, ?_⟩
  intro r1 s1 m1 hsp1 _ hfu1 _ hu1 hm1
  rw [hfu0] at hfu1; fp_steps
  · exact hQ 20#64 s1 m1 hsp1.lengths hfu1 (Or.inr rfl) (fun _ => hu1 hc) (fun h => by cases h) hm1
  -- 2. full_congruence(h)
  c0_call hCong; refine ⟨c, F0, s1, R, rfl, hsp1, hm1, ?_⟩
  intro r2 s2 m2 hfu2 hr2 hsp2 h20_2 hm2; fp_steps
  · obtain ⟨hu2, hlen2⟩ := h20_2 hc
    exact hQ 20#64 s2 m2 hlen2 (Nat.le_trans hfu2 hfu1) (Or.inr rfl) (fun _ => hu2)
      (fun h => by cases h) hm2
  have hinv2 : FullSparseInv c F0 s2 := hsp2 (hr2.resolve_right hc)
  -- 3. full_substitute(h)
  c0_call hSubst; refine ⟨c, F0, s2, R, rfl, hinv2, hm2, ?_⟩
  intro r3 s3 m3 hsp3 _ hfu3 _ hu3 hm3; fp_steps
  · exact hQ 20#64 s3 m3 hsp3.lengths (by omega) (Or.inr rfl) (fun _ => hu3 hc)
      (fun h => by cases h) hm3
  -- 4. full_sweep_sat(h)
  c0_call hSweep; refine ⟨c, F0, s3, R, rfl, hsp3, hm3, ?_⟩
  intro r4 s4 m4 hsp4 _ hfu4 _ hu4 hm4; fp_steps
  · exact hQ 20#64 s4 m4 hsp4.lengths (by omega) (Or.inr rfl) (fun _ => hu4 hc)
      (fun h => by cases h) hm4
  -- 5. full_transitive(h)
  c0_call hTrans; refine ⟨c, F0, s4, R, rfl, hsp4, hm4, ?_⟩
  intro r5 s5 m5 hsp5 _ _ hfu5 _ hu5 hm5; fp_steps
  · exact hQ 20#64 s5 m5 hsp5.lengths (by omega) (Or.inr rfl) (fun _ => hu5 hc)
      (fun h => by cases h) hm5
  -- 6. full_probe_run(h, 64ULL)
  c0_call hPRun; refine ⟨c, F0, s5, R, rfl, hsp5, hm5, ?_⟩
  intro r6 s6 m6 hsp6 _ _ hfu6 _ hu6 hm6; fp_steps
  · exact hQ 20#64 s6 m6 hsp6.lengths (by omega) (Or.inr rfl) (fun _ => hu6 hc)
      (fun h => by cases h) hm6
  -- 7. full_vivify(h, 1ULL)
  c0_call hViv; refine ⟨c, F0, s6, R, rfl, hsp6, hm6, ?_⟩
  intro r7 s7 m7 hsp7 _ _ hfu7 _ hu7 hm7; fp_steps
  · exact hQ 20#64 s7 m7 hsp7.lengths (by omega) (Or.inr rfl) (fun _ => hu7 hc)
      (fun h => by cases h) hm7
  -- 8. full_vivify(h, 2ULL)
  c0_call hViv; refine ⟨c, F0, s7, R, rfl, hsp7, hm7, ?_⟩
  intro r8 s8 m8 hsp8 _ _ hfu8 _ hu8 hm8; fp_steps
  · exact hQ 20#64 s8 m8 hsp8.lengths (by omega) (Or.inr rfl) (fun _ => hu8 hc)
      (fun h => by cases h) hm8
  -- 9. full_vivify(h, 0ULL)
  c0_call hViv; refine ⟨c, F0, s8, R, rfl, hsp8, hm8, ?_⟩
  intro r9 s9 m9 hsp9 hcl9 _ hfu9 _ hu9 hm9; fp_steps
  · exact hQ 20#64 s9 m9 hsp9.lengths (by omega) (Or.inr rfl) (fun _ => hu9 hc)
      (fun h => by cases h) hm9
  exact hQ 1#64 s9 m9 hsp9.lengths (by omega) (Or.inl rfl) (fun h => by cases h)
    (fun _ => ⟨hsp9, hcl9⟩) hm9

/-- `Func.wp` proof for `full_eliminate` (`Full.lean:1069-1089`) against canonical
`fullEliminateSpec`. -/
theorem full_eliminate_wp (Γ : Env)
    (hIsqrt : ∀ a m Q X, fullIsqrtSpec a m Q X → Γ "full_isqrt" [i64] [i64] a m Q X)
    (hEnter : ∀ a m Q X, fullEnterDenseSpec a m Q X → Γ "full_enter_dense" [i64] [.bool] a m Q X)
    (hFwd : ∀ a m Q X, fullForwardSubSpec a m Q X → Γ "full_forward_sub" [i64] [i64] a m Q X)
    (hBve : ∀ a m Q X, fullBveVarSpec a m Q X → Γ "full_bve_var" [i64, i32] [i64] a m Q X)
    (hFact : ∀ a m Q X, fullFactorSpec a m Q X → Γ "full_factor" [i64] [i64] a m Q X)
    (hReb : ∀ a m Q X, fullRebuildWatchesSpec a m Q X →
      Γ "full_rebuild_watches" [i64] [i64] a m Q X) :
    ∀ args m Q X, fullEliminateSpec args m Q X → Func.wp Γ full_eliminate_body args m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hinv, _, hm, hQ⟩
  unfold Func.wp full_eliminate_body; fp_steps
  c0_call hIsqrt
  intro r_sq _ _ _
  fp_steps
  let s0 : FullState :=
    { s with
      scratch := { s.scratch with
        eliminations := s.scratch.eliminations + 1#64
        elim_limit := s.scratch.conflicts + 1500#64 * r_sq } }
  have hinv0 : FullSparseInv c F0 s0 :=
    fullSparseInv_with_scratch_keep hinv { hinv.lengths.scratch_ok with } rfl rfl
  have hfu0 : s0.core.fuel = s.core.fuel := rfl
  c0_call hEnter; refine ⟨c, F0, s0, R, rfl, hinv0, hm, ?_⟩
  intro ok s1 m1 hcl1 hfu1 hok hfail hm1
  have hfu1_eq : s1.core.fuel = s.core.fuel := hfu1.trans hfu0
  fp_steps
  · c0_call hFwd; refine ⟨c, F0, s1, R, rfl, hok hc, hm1, ?_⟩
    intro r_fwd s2 m2 hden2 _ hfu2 _ hufwd hm2
    have hfu2_le : s2.core.fuel.toNat ≤ s.core.fuel.toNat := by
      rw [hfu2, hfu1_eq]; exact Nat.le_refl _
    fp_steps
    · c0_call hReb; refine ⟨c, F0, s2, R, rfl, hden2, hm2, ?_⟩
      intro _ s3 m3 hsp3 hcl3 hfu3 _ _ hm3; fp_steps
      exact hQ 20#64 s3 m3 hsp3 hcl3 (by omega) (Or.inr rfl) (fun _ => hufwd hc) hm3
    -- Post-loop join continuation `J` (unrolled by `fp_steps`)
    have hB : ∀ (v_bv res_v : BitVec 64) (sb : FullState) (mb : Mem 64),
        FullDenseInv c F0 sb → sb.core.fuel.toNat ≤ s.core.fuel.toNat →
        (res_v = 1#64 ∨ res_v = 20#64) → (res_v = 20#64 → F0.Unsat) →
        (FullMem c sb ⋆ R) mb → J (v_bv, res_v, ()) mb := by
      intro v_bv res_v sb mb hden_b hfu_b _ hres_u hmb
      apply hJ; c0_let_simp
      refine wp_join_group (ts := [])
        (fun () mf => ∃ sf : FullState,
          FullDenseInv c F0 sf ∧ sf.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c sf ⋆ R) mf)
        (fun _ ⟨⟩ mf ⟨sf, hden_f, hfu_f, hmf⟩ => by
          fp_steps
          c0_call hReb; refine ⟨c, F0, sf, R, rfl, hden_f, hmf, ?_⟩
          intro rr s_end m_end hsp_e hcl_e hfu_e _ hu_e hm_e
          fp_steps
          · exact hQ 20#64 s_end m_end hsp_e hcl_e (by omega) (Or.inr rfl) (fun _ => hres_u hc) hm_e
          · exact hQ 20#64 s_end m_end hsp_e hcl_e (by omega) (Or.inr rfl) (fun _ => hu_e hc) hm_e
          · exact hQ 20#64 s_end m_end hsp_e hcl_e (by omega) (Or.inr rfl)
              (fun _ => hsp_e.inconsistent_unsat hc) hm_e
          · exact hQ 1#64 s_end m_end hsp_e hcl_e (by omega) (Or.inl rfl)
              (fun h => by cases h) hm_e)
        (fun Jf hJf => by
          fp_steps
          · c0_call hFact; refine ⟨c, F0, sb, R, rfl, hden_b, hmb, ?_⟩
            intro _ sf mf hden_f _ hfu_f _ hmf; fp_steps
            exact hJf () mf ⟨sf, hden_f, by rw [hfu_f]; exact hfu_b, hmf⟩
          · exact hJf () mb ⟨sb, hden_b, hfu_b, hmb⟩)
    clear hJ
    -- BVE variable loop (`v < cv && h->oom == 0 && h->fuel > 0`)
    let cv : Nat := s2.core.cur_vars
    have hcv_le_max : cv ≤ c.max_vars := hden2.lengths.core_ok.cur_vars_le
    have hmax_lt32 : c.max_vars < 2 ^ 32 := fullInv_max_vars_lt32 c
    have hcv_lt64 : cv < 2 ^ 64 := by omega
    refine wp_loop_group (ts := [i64])
      (fun rem (v_bv, ()) ml => ∃ st : FullState,
        rem = cv - v_bv.toNat ∧ v_bv.toNat ≤ cv ∧ cv ≤ st.core.cur_vars ∧
        FullDenseInv c F0 st ∧ st.core.fuel.toNat ≤ s.core.fuel.toNat ∧
        (FullMem c st ⋆ R) ml) ?_ ?_
    · rintro L rem ⟨v_bv, ⟨⟩⟩ ml ih ⟨st, rfl, hv_le, hcv_le, hden_t, hfu_t, hml⟩
      fp_steps
      · have hv_lt_cv : v_bv.toNat < cv := by
          have : v_bv.toNat < s2.core.cur_vars % 2 ^ 64 := by assumption
          rw [Nat.mod_eq_of_lt hcv_lt64] at this; exact this
        have hv_lt_fl : v_bv.toNat < st.core.flags.length := by
          rw [hden_t.lengths.core_ok.flags_len]; omega
        have h2v_lt_vals : (v_bv <<< (1 : Nat)).toNat < st.core.vals.length := by
          rw [hden_t.lengths.core_ok.vals_len, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
          rw [Nat.mod_eq_of_lt (by omega)]; omega
        have hv1_lt64 : v_bv.toNat + 1 < 2 ^ 64 := by omega
        have hv_next_toNat : (v_bv + 1#64).toNat = v_bv.toNat + 1 := by bv_omega
        fp_steps
        · let st' : FullState :=
            { st with core :=
              { st.core with
                flags := st.core.flags.set v_bv.toNat
                  (st.core.flags[v_bv.toNat] &&& ~~~16#32) } }
          have hden_t' : FullDenseInv c F0 st' :=
            fullDenseInv_with_flags hden_t (by simp [hden_t.lengths.core_ok.flags_len])
          have hfu_t' : st'.core.fuel = st.core.fuel := rfl
          have hcv_t' : st'.core.cur_vars = st.core.cur_vars := rfl
          have hv32 : (v_bv.setWidth 32).toNat < st'.core.cur_vars := by
            have hlt32 : v_bv.toNat < 2 ^ 32 := by omega
            have : (v_bv.setWidth 32).toNat = v_bv.toNat := by bv_omega
            rw [hcv_t']; omega
          c0_call hBve; refine ⟨c, F0, st', R, rfl, hden_t', hv32, hm, ?_⟩
          intro br sb mb hden_b hcv_b hfu_b _ hub hmb
          rw [hfu_t'] at hfu_b; rw [hcv_t'] at hcv_b; fp_steps
          · exact hB v_bv 20#64 sb mb hden_b (by omega) (Or.inr rfl) (fun _ => hub hc) hmb
          · exact hB v_bv 1#64 sb mb hden_b (by omega) (Or.inl rfl) (fun h => by cases h) hmb
          · exact ih (cv - (v_bv + 1#64).toNat) (v_bv + 1#64, ()) mb
              (by rw [hv_next_toNat]; omega)
              ⟨sb, rfl, by rw [hv_next_toNat]; omega, Nat.le_trans hcv_le hcv_b,
                hden_b, by omega, hmb⟩
        · exact ih (cv - (v_bv + 1#64).toNat) (v_bv + 1#64, ()) ml
            (by rw [hv_next_toNat]; omega)
            ⟨st, rfl, by rw [hv_next_toNat]; omega, hcv_le, hden_t, hfu_t, hml⟩
        · exact ih (cv - (v_bv + 1#64).toNat) (v_bv + 1#64, ()) ml
            (by rw [hv_next_toNat]; omega)
            ⟨st, rfl, by rw [hv_next_toNat]; omega, hcv_le, hden_t, hfu_t, hml⟩
      · exact hB v_bv 1#64 st ml hden_t hfu_t (Or.inl rfl) (fun h => by cases h) hml
      · exact hB v_bv 1#64 st ml hden_t hfu_t (Or.inl rfl) (fun h => by cases h) hml
      · exact hB v_bv 1#64 st ml hden_t hfu_t (Or.inl rfl) (fun h => by cases h) hml
    · intro _ hL; fp_steps
      exact hL cv (0#64, ()) m2 ⟨s2, by simp, Nat.zero_le _, Nat.le_refl _,
        hden2, hfu2_le, hm2⟩
  · exact hQ 1#64 s1 m1 (hfail hc) hcl1 (by rw [hfu1_eq]; exact Nat.le_refl _)
      (Or.inl rfl) (fun h => by cases h) hm1

/-- `Func.wp` proof for `full_preprocess` (`Full.lean:1091-1102`) against canonical
`fullPreprocessSpec`. -/
theorem full_preprocess_wp (Γ : Env)
    (hProp : ∀ a m Q X, fullPropagateSpec a m Q X → Γ "full_propagate" [i64] [i64] a m Q X)
    (hProbe : ∀ a m Q X, fullProbeSpec a m Q X → Γ "full_probe" [i64] [i64] a m Q X)
    (hElim : ∀ a m Q X, fullEliminateSpec a m Q X → Γ "full_eliminate" [i64] [i64] a m Q X) :
    ∀ args m Q X, fullPreprocessSpec args m Q X → Func.wp Γ full_preprocess_body args m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hinv, hcl0, hm, hQ⟩
  obtain ⟨F_cur, hspW⟩ := hinv.exists_witness
  unfold Func.wp full_preprocess_body; fp_steps
  c0_call hProp; refine ⟨c, F0, F_cur, s, R, rfl, hspW.1, hspW.2.1, hspW.2.2.2.2.2, hm, ?_⟩
  intro pr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 s1
    hlen1 hw1 _ hperm1 hfu1 _ _ hpr1 _ _ hm1
  have hspW1 : FullSparseInvW c F0 F_cur s1 :=
    fullSparseInvW_of_perm hspW hlen1 hw1 hperm1 rfl rfl rfl ⟨rfl, rfl⟩
  have hcl1 : s1.core.cur_level = 0 := hcl0
  have hfu1' : s1.core.fuel.toNat ≤ s.core.fuel.toNat := hfu1
  fp_steps
  · exact hQ 20#64 s1 m1 hlen1 (Or.inr (Or.inr (Or.inr rfl))) hfu1
      (fun _ => level0_unsat_of_conflict_okW (s := s1) hw1 hcl1 (hpr1 hc).2.2)
      (fun h => by cases h) (fun h => by cases h) hm1
  · exact hQ 0#64 s1 m1 hlen1 (Or.inl rfl) hfu1 (fun h => by cases h) (fun h => by cases h)
      (fun h => by cases h) hm1
  · exact hQ 0#64 s1 m1 hlen1 (Or.inl rfl) hfu1 (fun h => by cases h) (fun h => by cases h)
      (fun h => by cases h) hm1
  · exact hQ 10#64 s1 m1 hlen1 (Or.inr (Or.inr (Or.inl rfl))) hfu1 (fun h => by cases h)
      (fun h => by cases h) (fun _ => hspW1.2.2.2.2.1.2) hm1
  c0_call hProbe; refine ⟨c, F0, s1, R, rfl, hspW1.toSparse, hcl1, hm1, ?_⟩
  intro rp s2 m2 hlen2 hfu2 hrp_dom hup2 hsp2 hm2; fp_steps
  · exact hQ 20#64 s2 m2 hlen2 (Or.inr (Or.inr (Or.inr rfl))) (by omega)
      (fun _ => hup2 hc) (fun h => by cases h) (fun h => by cases h) hm2
  · exact hQ 0#64 s2 m2 hlen2 (Or.inl rfl) (by omega) (fun h => by cases h)
      (fun h => by cases h) (fun h => by cases h) hm2
  · exact hQ 0#64 s2 m2 hlen2 (Or.inl rfl) (by omega) (fun h => by cases h)
      (fun h => by cases h) (fun h => by cases h) hm2
  obtain ⟨hinv2, hcl2⟩ := hsp2 (hrp_dom.resolve_right (by assumption))
  c0_call hElim; refine ⟨c, F0, s2, R, rfl, hinv2, hcl2, hm2, ?_⟩
  intro re s3 m3 hinv3 hcl3 hfu3 _ hue3 hm3; fp_steps
  · exact hQ 20#64 s3 m3 hinv3.lengths (Or.inr (Or.inr (Or.inr rfl))) (by omega)
      (fun _ => hue3 hc) (fun h => by cases h) (fun h => by cases h) hm3
  · exact hQ 20#64 s3 m3 hinv3.lengths (Or.inr (Or.inr (Or.inr rfl))) (by omega)
      (fun _ => hinv3.inconsistent_unsat hc) (fun h => by cases h) (fun h => by cases h) hm3
  · exact hQ 0#64 s3 m3 hinv3.lengths (Or.inl rfl) (by omega) (fun h => by cases h)
      (fun h => by cases h) (fun h => by cases h) hm3
  · exact hQ 10#64 s3 m3 hinv3.lengths (Or.inr (Or.inr (Or.inl rfl))) (by omega)
      (fun h => by cases h) (fun h => by cases h) (fun _ => hinv3.2.2.2.1.2) hm3
  · exact hQ 1#64 s3 m3 hinv3.lengths (Or.inr (Or.inl rfl)) (by omega) (fun h => by cases h)
      (fun _ => ⟨hinv3, hcl3⟩) (fun h => by cases h) hm3

/-- `Func.wp` proof for `full_simplify` (`Full.lean:1104-1113`) against canonical
`fullSimplifySpec`. -/
theorem full_simplify_wp (Γ : Env)
    (hBt : ∀ a m Q X, fullBacktrackSpec a m Q X → Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hRed : ∀ a m Q X, fullReduceSpec a m Q X → Γ "full_reduce" [i64, .bool] [i64] a m Q X)
    (hProbe : ∀ a m Q X, fullProbeSpec a m Q X → Γ "full_probe" [i64] [i64] a m Q X)
    (hElim : ∀ a m Q X, fullEliminateSpec a m Q X → Γ "full_eliminate" [i64] [i64] a m Q X) :
    ∀ args m Q X, fullSimplifySpec args m Q X → Func.wp Γ full_simplify_body args m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hinv, hm, hQ⟩
  unfold Func.wp full_simplify_body
  obtain ⟨F_cur0, hw0⟩ := hinv.1.witness
  have hcl_lt64 : s.core.cur_level < 2 ^ 64 := by
    have h1 := hw0.cur_level_le; have h2 := hinv.lengths.core_ok.trail_end_le
    have h3 := hinv.lengths.core_ok.cur_vars_le; have h4 := fullInv_max_vars_lt32 c; omega
  have htgt0 : (0#64 : BitVec 64).toNat < s.core.cur_level →
      (0#64 : BitVec 64).toNat < c.max_vars := by
    intro _; have h1 := hw0.cur_level_le; have h2 := hinv.lengths.core_ok.trail_end_le
    have h3 := hinv.lengths.core_ok.cur_vars_le; omega
  refine wp_join_group
    (fun () m0 => ∃ s0 : FullState,
      FullSparseInv c F0 s0 ∧ s0.core.cur_level = 0 ∧
      s0.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c s0 ⋆ R) m0)
    (fun _ ⟨⟩ m0 ⟨s0, hinv0, hcl0, hfu0, hm0⟩ => by
      obtain ⟨F_cur1, hspW0⟩ := hinv0.exists_witness
      fp_steps
      c0_call hRed; refine ⟨c, F0, F_cur1, s0, R, rfl, hspW0, hm0, ?_⟩
      intro rr s1 m1 hspW1 _ hcl1_le hfu1 _ _ _ _ hur1 _ _ hm1
      have hcl1 : s1.core.cur_level = 0 := by omega
      fp_steps
      · exact hQ 20#64 s1 m1 hspW1.1 (by omega) (Or.inr (Or.inr rfl))
          (fun _ => hur1 hc) (fun h => by cases h) hm1
      c0_call hProbe; refine ⟨c, F0, s1, R, rfl, hspW1.toSparse, hcl1, hm1, ?_⟩
      intro rp s2 m2 hlen2 hfu2 hrp_dom hup2 hsp2 hm2; fp_steps
      · exact hQ 20#64 s2 m2 hlen2 (by omega) (Or.inr (Or.inr rfl))
          (fun _ => hup2 hc) (fun h => by cases h) hm2
      · exact hQ 0#64 s2 m2 hlen2 (by omega) (Or.inl rfl)
          (fun h => by cases h) (fun h => by cases h) hm2
      · exact hQ 0#64 s2 m2 hlen2 (by omega) (Or.inl rfl)
          (fun h => by cases h) (fun h => by cases h) hm2
      obtain ⟨hinv2, hcl2⟩ := hsp2 (hrp_dom.resolve_right (by assumption))
      c0_call hElim; refine ⟨c, F0, s2, R, rfl, hinv2, hcl2, hm2, ?_⟩
      intro re s3 m3 hinv3 hcl3 hfu3 _ hue3 hm3; fp_steps
      · exact hQ 20#64 s3 m3 hinv3.lengths (by omega) (Or.inr (Or.inr rfl))
          (fun _ => hue3 hc) (fun h => by cases h) hm3
      · exact hQ 20#64 s3 m3 hinv3.lengths (by omega) (Or.inr (Or.inr rfl))
          (fun _ => hinv3.inconsistent_unsat hc) (fun h => by cases h) hm3
      · exact hQ 0#64 s3 m3 hinv3.lengths (by omega) (Or.inl rfl)
          (fun h => by cases h) (fun h => by cases h) hm3
      · exact hQ 1#64 s3 m3 hinv3.lengths (by omega) (Or.inr (Or.inl rfl))
          (fun h => by cases h) (fun _ => ⟨hinv3, hcl3⟩) hm3)
    (fun J0 hJ0 => by
      fp_steps
      · c0_call hBt
        refine ⟨c, s, R, rfl, hinv.lengths, hcl_lt64, htgt0, hw0.trail_lits_lt, hm, ?_⟩
        intro _ _ _ _ _ _ _ _ _ _ m0 s0 hlen0 _ _ hcl0' hps0 _ _ _ hw0' _ hm0
        have hinv0 : FullSparseInv c F0 s0 :=
          fullSparseInv_of_same_arena hinv ⟨hlen0, F_cur0, hw0' F0 F_cur0 hw0 (Nat.zero_le _)⟩
            rfl rfl rfl rfl rfl hps0.1
        have hcl0 : s0.core.cur_level = 0 := by dsimp only [s0]; rw [hcl0']; simp
        fp_steps
        exact hJ0 () m0 ⟨s0, hinv0, hcl0, Nat.le_refl _, hm0⟩
      · have hcl0 : s.core.cur_level = 0 := by c0_bound
        exact hJ0 () m ⟨s, hinv, hcl0, Nat.le_refl _, hm⟩)

/-! ## 3. `full_search` (`Full.lean:1115-1144`) -/

/-- `Func.wp` proof for `full_search` (`Full.lean:1115-1144`) against canonical
`fullSearchSpec`. -/
theorem full_search_wp (Γ : Env)
    (hLucky : ∀ a m Q X, fullLuckySpec a m Q X → Γ "full_lucky" [i64] [i64] a m Q X)
    (hWarm : ∀ a m Q X, fullWarmupSpec a m Q X → Γ "full_warmup" [i64] [] a m Q X)
    (hProp : ∀ a m Q X, fullPropagateSpec a m Q X → Γ "full_propagate" [i64] [i64] a m Q X)
    (hAna : ∀ a m Q X, fullAnalyzeSpec a m Q X → Γ "full_analyze" [i64] [i64] a m Q X)
    (hSw : ∀ a m Q X, fullSwitchModeSpec a m Q X → Γ "full_switch_mode" [i64] [] a m Q X)
    (hReph : ∀ a m Q X, fullRephaseSpec a m Q X → Γ "full_rephase" [i64] [] a m Q X)
    (hRed : ∀ a m Q X, fullReduceSpec a m Q X → Γ "full_reduce" [i64, .bool] [i64] a m Q X)
    (hSimp : ∀ a m Q X, fullSimplifySpec a m Q X → Γ "full_simplify" [i64] [i64] a m Q X)
    (hRdue : ∀ a m Q X, fullRestartDueSpec a m Q X → Γ "full_restart_due" [i64] [i64] a m Q X)
    (hRst : ∀ a m Q X, fullRestartSpec a m Q X → Γ "full_restart" [i64] [] a m Q X)
    (hDec : ∀ a m Q X, fullDecideSpec a m Q X → Γ "full_decide" [i64] [i64] a m Q X) :
    ∀ args m Q X, fullSearchSpec args m Q X → Func.wp Γ full_search_body args m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hinv, hcl0, hm, hQ⟩
  unfold Func.wp full_search_body; fp_steps
  c0_call hLucky; refine ⟨c, F0, s, R, rfl, hinv, hcl0, hm, ?_⟩
  intro lk s1 m1 hlen1 hlk_dom _ _ hulk hsp1 hext1 hm1; fp_steps
  · rw [hc]; exact hQ 20#64 s1 m1 hlen1 (Or.inr (Or.inr rfl)) (fun _ => hulk hc)
      (fun h => by cases h) hm1
  · rw [hc]; exact hQ 10#64 s1 m1 hlen1 (Or.inr (Or.inl rfl)) (fun h => by cases h)
      (fun _ => hext1 hc) hm1
  have hlk02 : lk = 0#64 ∨ lk = 2#64 := by
    rcases hlk_dom with h0 | h2 | h10 | h20
    · exact Or.inl h0
    · exact Or.inr h2
    · exact absurd h10 hc
    · exact absurd h20 (by assumption)
  have hinv1 : FullSparseInv c F0 s1 := (hsp1 hlk02).1
  c0_call hWarm; refine ⟨c, F0, s1, R, rfl, hinv1.1, hinv1.2.2.2.2, hm1, ?_⟩
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m2 s2
    hcore2 hperm2 _ hpres2 _ hm2
  have hinv2 : FullSparseInv c F0 s2 :=
    fullSparseInv_of_perm_core hinv1 hcore2 hperm2 rfl rfl rfl hpres2
  fp_steps
  -- Main CDCL `while (true)` loop with variant `searchVariant st`
  refine wp_loop_group (ts := [])
    (fun rem () ml => ∃ st : FullState,
      rem = searchVariant st ∧ FullSparseInv c F0 st ∧ (FullMem c st ⋆ R) ml) ?_ ?_
  · rintro L rem ⟨⟩ ml ih ⟨st, rfl, hst, hml⟩
    fp_steps
    · exact hQ 0#64 st ml hst.lengths (Or.inl rfl) (fun h => by cases h) (fun h => by cases h) hml
    · exact hQ 0#64 st ml hst.lengths (Or.inl rfl) (fun h => by cases h) (fun h => by cases h) hml
    rotate_left 1
    · cases hc
    obtain ⟨F_cur, hspW⟩ := hst.exists_witness
    c0_call hProp; refine ⟨c, F0, F_cur, st, R, rfl, hspW.1, hspW.2.1, hspW.2.2.2.2.2, hml, ?_⟩
    intro pr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3 s3
      hlen3 hw3 _ hperm3 hfu3 hpr_dom hpr0 hpr1 _ _ hm3
    have hspW3 : FullSparseInvW c F0 F_cur s3 :=
      fullSparseInvW_of_perm hspW hlen3 hw3 hperm3 rfl rfl rfl ⟨rfl, rfl⟩
    fp_steps
    · exact hQ 0#64 s3 m3 hlen3 (Or.inl rfl) (fun h => by cases h) (fun h => by cases h) hm3
    · -- Conflict branch (`pr == 1ULL`)
      obtain ⟨hfu3_lt, _, hconf3⟩ := hpr1 hc
      c0_call hAna; refine ⟨c, F0, F_cur, s3, R, rfl, hspW3, hconf3, hm3, ?_⟩
      intro ast s4 m4 hlen4 _ _ hfu4 _ hua4 _ hsp4 hm4; fp_steps
      · exact hQ 20#64 s4 m4 hlen4 (Or.inr (Or.inr rfl)) (fun _ => hua4 hc)
          (fun h => by cases h) hm4
      · exact hQ 0#64 s4 m4 hlen4 (Or.inl rfl) (fun h => by cases h)
          (fun h => by cases h) hm4
      have hinv4 : FullSparseInv c F0 s4 := (hsp4 hc).1.toSparse
      c0_call hSw; refine ⟨c, s4, R, rfl, hinv4.lengths, hm4, ?_⟩
      intro ⟨⟩ s5 m5 hcore5 hlen5 hpres5 hm5
      dsimp only [fullSafetySlice, SafetySlice.ofMask] at hm5
      have hinv5 : FullSparseInv c F0 s5 := hinv4.of_safetySlice hlen5 hcore5 hpres5.1
      have hfu5 : s5.core.fuel.toNat < st.core.fuel.toNat := by
        have heq : s5.core = s4.core := fullCoreState_agrees_with_scratch hcore5
        rw [heq]; change s4.core.fuel.toNat < st.core.fuel.toNat; dsimp only [s3] at hfu4; omega
      -- Optional `full_rephase`
      refine wp_join_group (ts := [])
        (fun () m6 => ∃ s6 : FullState,
          FullSparseInv c F0 s6 ∧ s6.core.fuel.toNat < st.core.fuel.toNat ∧
          (FullMem c s6 ⋆ R) m6)
        (fun _ ⟨⟩ m6 ⟨s6, hinv6, hfu6, hm6⟩ => by
          c0_let_simp
          -- Optional `full_reduce(h, false)`
          refine wp_join_group (ts := [])
            (fun () m7 => ∃ s7 : FullState,
              FullSparseInv c F0 s7 ∧ s7.core.fuel.toNat < st.core.fuel.toNat ∧
              (FullMem c s7 ⋆ R) m7)
            (fun _ ⟨⟩ m7 ⟨s7, hinv7, hfu7, hm7⟩ => by
              c0_let_simp
              -- Optional `full_simplify` else optional `full_restart`
              refine wp_join_group (ts := [])
                (fun () m8 => ∃ s8 : FullState,
                  FullSparseInv c F0 s8 ∧ s8.core.fuel.toNat < st.core.fuel.toNat ∧
                  (FullMem c s8 ⋆ R) m8)
                (fun _ ⟨⟩ m8 ⟨s8, hinv8, hfu8, hm8⟩ => by
                  fp_steps
                  have hv_lt : searchVariant s8 < searchVariant st := by
                    unfold searchVariant; split <;> split <;> omega
                  exact ih (searchVariant s8) () m8 hv_lt ⟨s8, rfl, hinv8, hm8⟩)
                (fun J_sr hJ_sr => by
                  c0_let_simp
                  refine wp_join_group (ts := [])
                    (fun () ms => ms = m7)
                    (fun _ ⟨⟩ ms hms => by
                      subst hms; fp_steps
                      c0_call hSimp; refine ⟨c, F0, s7, R, rfl, hinv7, hm7, ?_⟩
                      intro sr s8 m8 hlen8 hfu8 _ hus8 hsp8 hm8; fp_steps
                      · exact hQ 20#64 s8 m8 hlen8 (Or.inr (Or.inr rfl)) (fun _ => hus8 hc)
                          (fun h => by cases h) hm8
                      · exact hQ 0#64 s8 m8 hlen8 (Or.inl rfl) (fun h => by cases h)
                          (fun h => by cases h) hm8
                      exact hJ_sr () m8 ⟨s8, (hsp8 hc).1, by omega, hm8⟩)
                    (fun J_simp hJ_simp => by
                      fp_steps
                      · exact hJ_simp () m7 rfl
                      · exact hJ_simp () m7 rfl
                      · c0_call hRdue; refine ⟨c, s7, R, rfl, hinv7.lengths, hm7, ?_⟩
                        intro ⟨rd, ⟨⟩⟩ s7' m7' hcore7' hlen7' ⟨_, hpres7'⟩ hm7'
                        dsimp only [fullSafetySlice, SafetySlice.ofMask] at hm7'
                        have hinv7' : FullSparseInv c F0 s7' :=
                          hinv7.of_safetySlice hlen7' hcore7' hpres7'
                        have hfu7' : s7'.core.fuel.toNat < st.core.fuel.toNat := by
                          have heq : s7'.core = s7.core :=
                            fullCoreState_agrees_with_scratch hcore7'
                          rw [heq]; exact hfu7
                        fp_steps
                        · c0_call hRst; refine ⟨c, F0, s7', R, rfl, hinv7'.1, hm7', ?_⟩
                          intro _ _ _ _ _ _ _ _ _ _ m8 s8 hcore8 _ hpres8 hm8
                          have hinv8 : FullSparseInv c F0 s8 :=
                            fullSparseInv_of_same_arena hinv7' hcore8 rfl rfl rfl rfl rfl hpres8
                          fp_steps
                          exact hJ () m8 (by fp_steps; exact hJ_sr () m8 ⟨s8, hinv8, hfu7', hm8⟩)
                        · exact hJ_sr () m7' ⟨s7', hinv7', hfu7', hm7'⟩)))
            (fun J_rd hJ_rd => by
              fp_steps
              · obtain ⟨Fc6, hspW6⟩ := hinv6.exists_witness
                c0_call hRed; refine ⟨c, F0, Fc6, s6, R, rfl, hspW6, hm6, ?_⟩
                intro rr s7 m7 hspW7 _ _ hfu7 _ _ _ _ hur7 _ _ hm7; fp_steps
                · exact hQ 20#64 s7 m7 hspW7.1 (Or.inr (Or.inr rfl)) (fun _ => hur7 hc)
                    (fun h => by cases h) hm7
                · exact hQ 0#64 s7 m7 hspW7.1 (Or.inl rfl) (fun h => by cases h)
                    (fun h => by cases h) hm7
                exact hJ_rd () m7 ⟨s7, hspW7.toSparse, by omega, hm7⟩
              · exact hJ_rd () m6 ⟨s6, hinv6, hfu6, hm6⟩))
        (fun J_rp hJ_rp => by
          fp_steps
          · c0_call hReph; refine ⟨c, F0, s5, R, rfl, hinv5.1, hm5, ?_⟩
            intro _ _ _ _ _ _ _ _ _ _ m6 s6 hcore6 hfu6 hpres6 hm6
            have hinv6 : FullSparseInv c F0 s6 :=
              fullSparseInv_of_same_arena hinv5 hcore6 rfl rfl rfl rfl rfl hpres6
            fp_steps
            exact hJ_rp () m6 ⟨s6, hinv6, by dsimp only [s6]; omega, hm6⟩
          · exact hJ_rp () m5 ⟨s5, hinv5, hfu5, hm5⟩)
    · -- Non-conflict branch (`pr == 0ULL`), `unassigned == 0ULL`
      exact hQ 10#64 s3 m3 hlen3 (Or.inr (Or.inl rfl)) (fun h => by cases h)
        (fun _ => hspW3.2.2.2.2.1.2) hm3
    · -- Non-conflict branch (`pr == 0ULL`), `unassigned ≠ 0ULL`
      have hpr_eq0 : pr = 0#64 := by
        rcases hpr_dom with h0 | h1 | h2
        · exact h0
        · exact absurd h1 (by assumption)
        · exact absurd h2 (by assumption)
      obtain ⟨hprop3, _, hfu3_lt_if⟩ := hpr0 hpr_eq0
      have hinv3 : FullSparseInv c F0 s3 := hspW3.toSparse
      c0_call hDec; refine ⟨c, F0, s3, R, rfl, hinv3.1, hm3, ?_⟩
      intro dr _ _ _ _ _ _ _ _ _ _ _ _ _ m4 s4 hcore4 hpres4 hdr_dom _ hd1 hm4
      have hinv4 : FullSparseInv c F0 s4 :=
        fullSparseInv_of_same_arena hinv3 hcore4 rfl rfl rfl rfl rfl hpres4
      fp_steps
      · exact hQ 10#64 s4 m4 hinv4.lengths (Or.inr (Or.inl rfl)) (fun h => by cases h)
          (fun _ => hinv4.2.2.2.1.2) hm4
      · exact hQ 0#64 s4 m4 hinv4.lengths (Or.inl rfl) (fun h => by cases h)
          (fun h => by cases h) hm4
      · have hdr1 : dr = 1#64 := hdr_dom.resolve_left hc
        have hte4 : s4.core.trail_end = s3.core.trail_end + 1 := (hd1 hdr1).2
        have hv_lt : searchVariant s4 < searchVariant st := by
          have hfu3' : s3.core.fuel.toNat ≤ st.core.fuel.toNat := hfu3
          have hprop3' : s3.core.propagated = s3.core.trail_end := hprop3
          have hne4 : s4.core.propagated ≠ s4.core.trail_end := by
            change s3.core.propagated ≠ s4.core.trail_end; omega
          have hle_st := hst.lengths.core_ok.propagated_le
          have hfu4 : s4.core.fuel = s3.core.fuel := rfl
          unfold searchVariant
          simp only [hne4, ↓reduceIte, Nat.add_zero, hfu4]
          by_cases heq_st : st.core.propagated = st.core.trail_end
          · simp only [heq_st, ↓reduceIte]; omega
          · simp only [heq_st, ↓reduceIte, Nat.add_zero]
            have hlt_f : s3.core.fuel.toNat < st.core.fuel.toNat := hfu3_lt_if (by omega)
            omega
        exact ih (searchVariant s4) () m4 hv_lt ⟨s4, rfl, hinv4, hm4⟩
  · intro _ hL; fp_steps
    exact hL (searchVariant s2) () m2 ⟨s2, rfl, hinv2, hm2⟩

/-! ## 4. `kissat_solve_bytes_core_wp` and `kissat_solve_bytes_wp` (`Full.lean:1146-1167`) -/

/-- Post-search `r == 10ULL` gate: `full_extend` (via `fullExtendSlice`) + `kissat_check_model`
(via `fullMem_to_checkModel` / `checkModel_post_to_region`), restoring `(bytes ⋆ region ⋆ R) m'`. -/
private theorem solve_bytes_extend_check {Γ : Env} {Q : Post [i64]} {X : XPost}
    {c : FullCfg} {s3 : FullState} {cnf_ptr work_ptr hdr_ptr : BitVec 64} {cnfBytes : List UInt8}
    {wlen : Nat} {R : Mem 64 → Prop} {m3 : Mem 64}
    (hExt : ∀ a m Q X, fullExtendSpec a m Q X → Γ "full_extend" [i64] [] a m Q X)
    (hCheck : ∀ a m Q X, kissatCheckModelExactSpec a m Q X →
      Γ "kissat_check_model" [i64, i64, i64, i64, i64] [i64] a m Q X)
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64) (hw_ge : fullAlignPad work_ptr ≤ wlen)
    (hch_ptr : c.hdr = hdr_ptr)
    (hch : c.hdr = work_ptr + BitVec.ofNat 64 (fullAlignPad work_ptr))
    (hca : c.avail = wlen - fullAlignPad work_ptr)
    (hlen3 : s3.LengthsOk c) (hext3 : s3.scratch.extend_len ≤ c.extend_cap)
    (hm3 : (bytes cnf_ptr cnfBytes ⋆ FullMem c s3 ⋆
      (region work_ptr (fullAlignPad work_ptr) ⋆ R)) m3)
    (hRet : ∀ r m', (r = 0#64 ∨ r = 10#64) →
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m' → Q (r, ()) m') :
    let cnf_end := cnf_ptr + BitVec.ofNat 64 cnfBytes.length
    wp Γ Q X (Expr.call (as := [i64]) (bs := []) "full_extend" (Arg.var hdr_ptr, ()) fun _ =>
      Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                  args := (Arg.var hdr_ptr, Arg.imm 64, ()) }
      fun p1 => Expr.load i64 (Arg.var p1.fst) fun ld_v =>
      Expr.load i64 (Arg.var hdr_ptr) fun ld_mv =>
      Expr.call (as := [i64, i64, i64, i64, i64]) (bs := [i64]) "kissat_check_model"
        (Arg.var cnf_ptr, Arg.var cnf_end, Arg.var hdr_ptr, Arg.var ld_v, Arg.var ld_mv, ())
      fun p2 => Expr.group (sig := [[i64]])
        (fun _ => Blocks.cons (fun p3 => Expr.ret (Arg.var p3.fst, ())) Blocks.nil)
        fun Jr => Expr.let_
          { sig := [i64, i64], code := OpCode.cmp CmpOp.eq i64 Ty.bool rfl,
            args := (Arg.var p2.fst, Arg.imm 1, ()) }
          fun p3 => Expr.jnz (Arg.var p3.fst)
            (Expr.jump Jr.fst (Arg.imm 10, ())) (Expr.jump Jr.fst (Arg.imm 0, ()))) m3 := by
  dsimp only
  rw [← hch_ptr]
  c0_call hExt
  refine ⟨c, s3, bytes cnf_ptr cnfBytes ⋆ region work_ptr (fullAlignPad work_ptr) ⋆ R,
    ⟨rfl, hext3⟩, hlen3,
    by dsimp only [fullExtendSlice, SafetySlice.ofMask]; exact sep_ac hm3, ?_⟩
  intro ⟨⟩ s4 m4 _ hlen4 _ hm4
  dsimp only [fullExtendSlice, SafetySlice.ofMask] at hm4
  fp_steps
  have hm4_b : (bytes cnf_ptr cnfBytes ⋆ FullMem c s4 ⋆
      (region work_ptr (fullAlignPad work_ptr) ⋆ R)) m4 := sep_ac hm4
  have hmv_bd := c.hmv; have hmx_bd := c.hmaxv; have hbva := c.hbva
  unfold dimacsBound at hmv_bd hmx_bd
  have hcm_mem := fullMem_to_checkModel hlen4 hm4_b
  c0_call hCheck
  refine ⟨BitVec.ofNat 64 c.mv, BitVec.ofNat 64 c.nc, s4.core.d_cur, s4.core.d_val,
    cnfBytes, s4.core.vals.map UInt8.ofBitVec, c.mv,
    FullCheckRest c s4 ⋆ (region work_ptr (fullAlignPad work_ptr) ⋆ R),
    rfl, rfl, hcfit, by omega,
    by simp [hlen4.core_ok.vals_len]; omega,
    by simp [hlen4.core_ok.vals_len]; omega,
    by simpa [sep_assoc] using hcm_mem, ?_⟩
  intro ok mv' nc' cur' val' m5 _ hm5
  have hm5_reg : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m5 :=
    full_merge_reg hwfit hw_ge (by
      rw [← hch, ← hca]
      exact checkModel_post_to_region hlen4 (by simpa [sep_assoc] using hm5))
  refine wp_join_group (ts := [i64])
    (fun (res_v, ()) m6 => (res_v = 0#64 ∨ res_v = 10#64) ∧ m6 = m5)
    (fun _ ⟨res_v, ⟨⟩⟩ m6 ⟨hres_v, hm6⟩ => by
      rw [hm6]; fp_steps; exact hRet res_v m5 hres_v hm5_reg)
    (fun Jr hJr => by
      fp_steps
      · exact hJr (10#64, ()) m5 ⟨Or.inr rfl, rfl⟩
      · exact hJr (0#64, ()) m5 ⟨Or.inl rfl, rfl⟩)

/-- `Func.wp` proof for `D-Full` `kissat_solve_bytes` (`Full.lean:1146-1167`) against canonical
`fullSolveBytesCoreSpec` (UNSAT-only soundness + `UnitUnsatTrace` non-vacuity). -/
theorem kissat_solve_bytes_core_wp (Γ : Env)
    (hInit : ∀ a m Q X, fullInitStateSpec a m Q X →
      Γ "full_init_state" [i64, i64, i64, i64, i64] [.bool] a m Q X)
    (hParse : ∀ a m Q X, fullParseBodySpec a m Q X →
      Γ "full_parse_body" [i64, i64] [i64] a m Q X)
    (hPre : ∀ a m Q X, fullPreprocessSpec a m Q X → Γ "full_preprocess" [i64] [i64] a m Q X)
    (hSearch : ∀ a m Q X, fullSearchSpec a m Q X → Γ "full_search" [i64] [i64] a m Q X)
    (hExt : ∀ a m Q X, fullExtendSpec a m Q X → Γ "full_extend" [i64] [] a m Q X)
    (hCheck : ∀ a m Q X, kissatCheckModelExactSpec a m Q X →
      Γ "kissat_check_model" [i64, i64, i64, i64, i64] [i64] a m Q X) :
    ∀ args m Q X, fullSolveBytesCoreSpec args m Q X →
      Func.wp Γ kissat_solve_bytes_body args m Q X := by
  rintro ⟨cnf_ptr, cnf_len, work_ptr, work_len, fuel, ⟨⟩⟩ m Q X
    ⟨cnfBytes, wlen, R, rfl, rfl, hcfit, hwfit, hm, hQ⟩
  unfold Func.wp kissat_solve_bytes_body; wp_unfold
  refine ⟨fun hf0 => ?_, fun _ => ?_⟩
  · exact hQ 0#64 m (Or.inl rfl) (fun h => by cases h)
      (fun _ _ _ _ _ hf => by rw [hf0] at hf; simp at hf) hm
  refine ⟨fun hcp0 => ?_, fun _ => ?_⟩
  · exact hQ 0#64 m (Or.inl rfl) (fun h => by cases h)
      (fun _ _ _ hcp => absurd hcp0 hcp) hm
  refine ⟨fun hwp0 => ?_, fun _ => ?_⟩
  · exact hQ 0#64 m (Or.inl rfl) (fun h => by cases h)
      (fun _ _ _ _ hwp => absurd hwp0 hwp) hm
  have hnot0 : ~~~(0 : BitVec 64) = 0xFFFFFFFFFFFFFFFF#64 := rfl
  rw [hnot0, bv64_ugt_max_sub_false hcfit]
  refine ⟨(fun h => by cases h), fun _ => ?_⟩
  rw [bv64_ugt_max_sub_false hwfit]
  refine ⟨(fun h => by cases h), fun _ => ?_⟩
  let pNat : Nat := fullAlignPad work_ptr
  have hp_lt8 : pNat < 8 := fullAlignPad_lt8 work_ptr
  have hpad_ult : (BitVec.ofNat 64 wlen).ult (((8 - (work_ptr &&& 7)) &&& 7) + 1152) =
      decide (wlen < pNat + 1152) := by
    rw [fullAlignPad_bv_eq work_ptr, show (1152 : BitVec 64) = BitVec.ofNat 64 1152 from rfl,
      bv_add_ofNat, bv_ult_eq (by omega) (by omega)]
  rw [hpad_ult]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  refine ⟨fun hw_small => ?_, fun hw_ge_not => ?_⟩
  · exact hQ 0#64 m (Or.inl rfl) (fun h => by cases h)
      (fun mv nc _ _ _ _ hsz _ _ _ => by unfold fullFixedBytes at hsz; omega) hm
  have hw_ok : pNat + 1152 ≤ wlen := by omega
  let hdr_addr : BitVec 64 := work_ptr + BitVec.ofNat 64 pNat
  let availNat : Nat := wlen - pNat
  have hpad_bv : (8 - (work_ptr &&& 7)) &&& 7 = BitVec.ofNat 64 pNat := fullAlignPad_bv_eq work_ptr
  have hhdr_bv : work_ptr + ((8 - (work_ptr &&& 7)) &&& 7) = hdr_addr := by rw [hpad_bv]
  have hav_bv :
      BitVec.ofNat 64 wlen - ((8 - (work_ptr &&& 7)) &&& 7) = BitVec.ofNat 64 availNat := by
    rw [hpad_bv]; exact bv_sub_ofNat (by omega) (by omega)
  have hav_toNat : (BitVec.ofNat 64 wlen - ((8 - (work_ptr &&& 7)) &&& 7)).toNat = availNat := by
    rw [hav_bv, bv64_ofNat_toNat (by omega)]
  have hhdr_fit : hdr_addr.toNat + availNat < 2 ^ 64 := by
    rw [bv_add_ofNat_toNat (by omega)]; omega
  have hsplit : (bytes cnf_ptr cnfBytes ⋆
      region hdr_addr availNat ⋆ (region work_ptr pNat ⋆ R)) m := by
    have h1 : (region work_ptr wlen ⋆ (bytes cnf_ptr cnfBytes ⋆ R)) m := sep_ac hm
    have h2 : ((region work_ptr pNat ⋆ region hdr_addr availNat) ⋆
        (bytes cnf_ptr cnfBytes ⋆ R)) m :=
      sep_mono (fun _ f => region_work_to_hdr (by omega) (by omega) f) h1
    exact sep_ac h2
  c0_call hInit
  refine ⟨cnfBytes, region work_ptr pNat ⋆ R, rfl, hcfit,
    by rw [hhdr_bv, hav_toNat]; exact hhdr_fit,
    by rw [hav_toNat]; omega,
    by rw [hhdr_bv, hav_toNat]; exact hsplit, ?_, ?_⟩
  · intro m' hm' hfail; wp_unfold
    have hm'_r : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m' :=
      full_merge_reg hwfit (by omega) (by rw [hhdr_bv, hav_toNat] at hm'; exact hm')
    exact hQ 0#64 m' (Or.inl rfl) (fun h => by cases h)
      (fun mv nc i0 _ _ _ hsz _ hhdr _ => by
        have hlt := hfail mv nc (cnfBytes.drop i0) hhdr
        rw [hav_toNat] at hlt; omega) hm'_r
  · intro c s0 j0 rest0 m0 hch_ptr hca0 hhdr0 hj0 hdrop0 hinv0 hcv0 hdcur0
      hal0 _ hte0 hpr0 hcl0 _ _ hprob0 _ _ hoom0 hinc0 hvals0 hwvec0 _ _ _ hm0
    have hch : c.hdr = hdr_addr := hch_ptr.trans hhdr_bv
    have hca : c.avail = availNat := hca0.trans hav_toNat
    have hvals_take : s0.core.vals.take (2 * c.mv) = List.replicate (2 * c.mv) 0#8 := by
      have hbva := c.hbva
      rw [hvals0, List.take_replicate, Nat.min_eq_left (by omega)]
    fp_step
    rotate_left 1
    · cases hc
    c0_call hParse
    refine ⟨c, s0, cnf_ptr, cnfBytes, j0, region work_ptr pNat ⋆ R,
      hch_ptr.symm, rfl, hcfit, hj0, by rwa [hdrop0], hcv0, hdcur0, hcl0, hte0, hpr0, hal0,
      hoom0, hprob0, hinc0, hvals0, hwvec0, hinv0, hm0, ?_⟩
    intro pb s1 m1 hlen1 hpb_dom _ _ _ hpb20 hpb1 huns_tr hm1; fp_steps
    · -- `pb ≠ 1#64`: `pb = 0#64` or `pb = 20#64`
      rcases hpb_dom with rfl | h1 | rfl
      · refine hQ 0#64 m1 (Or.inl rfl) (fun h => by cases h) ?_
          (full_merge_arena hwfit (by omega) hch hca hlen1 hm1)
        intro mv nc i0 _ _ _ _ _ hhdr hut
        rw [hhdr0, Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq] at hhdr
        rcases hhdr with ⟨rfl, rfl, hre⟩
        have h20 := huns_tr (by rw [hvals_take, hdrop0, hre]; exact hut)
        cases h20
      · exact absurd h1 hc
      · exact hQ 20#64 m1 (Or.inr (Or.inr rfl)) (fun _ => hpb20 rfl)
          (fun _ _ _ _ _ _ _ _ _ _ => rfl)
          (full_merge_arena hwfit (by omega) hch hca hlen1 hm1)
    · -- `pb == 1#64`: `cnf` parsed, `UnitUnsatTrace` ruled out
      obtain ⟨cnf, hparse, hinv1, hcl1⟩ := hpb1 hc
      have hcnf_pos : CnfVarsPos cnf := parseDimacs_vars_pos hparse
      have hnot_ut : ∀ mv nc i0, cnf_ptr ≠ 0#64 → work_ptr ≠ 0#64 → 0 < fuel.toNat →
          fullFixedBytes mv + nc * 40 + 136 + 8 ≤ wlen → i0 ≤ cnfBytes.length →
          parseHeader cnfBytes = some (mv, nc, cnfBytes.drop i0) →
          UnitUnsatTrace mv (List.replicate (2 * mv) 0#8) (cnfBytes.drop i0) nc → False := by
        intro mv nc i0 _ _ _ _ _ hhdr hut
        rw [hhdr0, Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq] at hhdr
        rcases hhdr with ⟨rfl, rfl, hre⟩
        have h20 := huns_tr (by rw [hvals_take, hdrop0, hre]; exact hut)
        rw [hc] at h20; cases h20
      c0_call hPre; refine ⟨c, shiftDownCnf cnf, s1,
        bytes cnf_ptr cnfBytes ⋆ region work_ptr pNat ⋆ R,
        hch_ptr.symm, hinv1, hcl1, sep_ac hm1, ?_⟩
      intro pp s2 m2 hlen2 hpp_dom _ hpp20 hpp1 hpp10 hm2
      fp_step
      · fp_steps
        exact hQ 20#64 m2 (Or.inr (Or.inr rfl))
          (fun _ => ⟨cnf, hparse, shiftDownCnf_unsat hcnf_pos (hpp20 hc)⟩)
          (fun _ _ _ _ _ _ _ _ _ _ => rfl)
          (full_merge_arena hwfit (by omega) hch hca hlen2 (sep_ac hm2))
      -- `r = (pp == 10) ? 10 : ((pp == 0) ? 0 : full_search(h))`
      refine wp_join_group (ts := [i64])
        (fun (rv, ()) mr => ∃ sr : FullState,
          sr.LengthsOk c ∧ (rv = 0#64 ∨ rv = 10#64 ∨ rv = 20#64) ∧
          (rv = 20#64 → cnf.Unsat) ∧
          (rv = 10#64 → sr.scratch.extend_len ≤ c.extend_cap) ∧
          (bytes cnf_ptr cnfBytes ⋆ FullMem c sr ⋆ (region work_ptr pNat ⋆ R)) mr)
        (fun _ ⟨rv, ⟨⟩⟩ mr ⟨sr, hlen_r, hrv_dom, hrv_u, hrv_ext, hmr⟩ => by
          fp_steps
          · exact solve_bytes_extend_check hExt hCheck hcfit hwfit (by omega) hch_ptr hch hca
              hlen_r (hrv_ext hc) hmr fun res m_end hres hm_end =>
                hQ res m_end (hres.elim Or.inl fun h => Or.inr (Or.inl h))
                  (fun h20 => by rcases hres with rfl | rfl <;> cases h20)
                  (fun mv nc i0 h1 h2 h3 h4 h5 h6 h7 =>
                    (hnot_ut mv nc i0 h1 h2 h3 h4 h5 h6 h7).elim)
                  hm_end
          · exact hQ rv mr hrv_dom (fun h20 => ⟨cnf, hparse, hrv_u h20⟩)
              (fun mv nc i0 h1 h2 h3 h4 h5 h6 h7 => (hnot_ut mv nc i0 h1 h2 h3 h4 h5 h6 h7).elim)
              (full_merge_arena hwfit (by omega) hch hca hlen_r hmr))
        (fun J_r hJ_r => by
          fp_step; fp_step
          · fp_steps; exact hJ_r (10#64, ()) m2 ⟨s2, hlen2, Or.inr (Or.inl rfl),
              (fun h => by cases h), (fun _ => hpp10 hc), sep_ac hm2⟩
          · refine wp_join_group (ts := [i64])
              (fun (rv, ()) mr => ∃ sr : FullState,
                sr.LengthsOk c ∧ (rv = 0#64 ∨ rv = 10#64 ∨ rv = 20#64) ∧
                (rv = 20#64 → cnf.Unsat) ∧
                (rv = 10#64 → sr.scratch.extend_len ≤ c.extend_cap) ∧
                (bytes cnf_ptr cnfBytes ⋆ FullMem c sr ⋆ (region work_ptr pNat ⋆ R)) mr)
              (fun _ ⟨rv, ⟨⟩⟩ mr hmr => by fp_steps; exact hJ_r (rv, ()) mr hmr)
              (fun J_r2 hJ_r2 => by
                fp_steps
                · exact hJ_r2 (0#64, ()) m2 ⟨s2, hlen2, Or.inl rfl, (fun h => by cases h),
                    (fun h => by cases h), sep_ac hm2⟩
                · have hpp_eq1 : pp = 1#64 := by
                    rcases hpp_dom with h0 | h1 | h10 | h20
                    · exact absurd h0 hc
                    · exact h1
                    · exact absurd h10 (by assumption)
                    · exact absurd h20 (by assumption)
                  obtain ⟨hinv2, hcl2⟩ := hpp1 hpp_eq1
                  c0_call hSearch
                  refine ⟨c, shiftDownCnf cnf, s2,
                    bytes cnf_ptr cnfBytes ⋆ region work_ptr pNat ⋆ R,
                    hch_ptr.symm, hinv2, hcl2, hm2, ?_⟩
                  intro r3 s3 m3 hlen3 hr3_dom hu3 hext3 hm3; fp_steps
                  exact hJ_r2 (r3, ()) m3 ⟨s3, hlen3, hr3_dom,
                    fun h20 => shiftDownCnf_unsat hcnf_pos (hu3 h20), hext3, sep_ac hm3⟩))

/-- `Func.wp` proof for `D-Full` `kissat_solve_bytes` (`Full.lean:1146-1167`) against canonical
`fullSolveBytesSpec` (headline UNSAT-only soundness). -/
theorem kissat_solve_bytes_wp (Γ : Env)
    (hInit : ∀ a m Q X, fullInitStateSpec a m Q X →
      Γ "full_init_state" [i64, i64, i64, i64, i64] [.bool] a m Q X)
    (hParse : ∀ a m Q X, fullParseBodySpec a m Q X →
      Γ "full_parse_body" [i64, i64] [i64] a m Q X)
    (hPre : ∀ a m Q X, fullPreprocessSpec a m Q X → Γ "full_preprocess" [i64] [i64] a m Q X)
    (hSearch : ∀ a m Q X, fullSearchSpec a m Q X → Γ "full_search" [i64] [i64] a m Q X)
    (hExt : ∀ a m Q X, fullExtendSpec a m Q X → Γ "full_extend" [i64] [] a m Q X)
    (hCheck : ∀ a m Q X, kissatCheckModelExactSpec a m Q X →
      Γ "kissat_check_model" [i64, i64, i64, i64, i64] [i64] a m Q X) :
    ∀ args m Q X, fullSolveBytesSpec args m Q X →
      Func.wp Γ kissat_solve_bytes_body args m Q X :=
  fun args m Q X h =>
    kissat_solve_bytes_core_wp Γ hInit hParse hPre hSearch hExt hCheck args m Q X
      (fullSolveBytesCoreSpec_of_spec h)

end TopOrchestrators

end LeanQbe.T.Examples.Kissat.Full
