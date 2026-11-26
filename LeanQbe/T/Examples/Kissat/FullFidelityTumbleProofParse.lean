/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityTumbleSpec
import LeanQbe.T.Examples.Kissat.FullDimacsBodyLemmas
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Fidelity Step 11 PR 2 Tumble Parse & Finish Proofs (`FullFidelityTumbleProofParse`)

Proves:
1. `full_tumble_finish_fid_wp` against `fullTumbleFinishFidSpec` (writes bottom `EXT_PERM_FLAG`
   block to `extend_stk`, resets `frame_dec[0..mv-1] = 0xFFFFFFFFu`, sets `extend_len = mv + 1`).
2. `full_parse_body_tum_del_wp` & `full_parse_body_tum_wp` against **exact unchanged canonical
   `Full.fullParseBodySpec`**, lifting relabeled `FullWitnessInv` back to `shiftDownCnf accCnf`
   via `fullWitnessInv_relabel_back` before `full_tumble_finish_fid` resets `frame_dec`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityTumble

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open Kraken.Bedrock2.Test

/-! ## 1. `full_tumble_finish_fid` (`fullTumbleFinishFidSpec`) -/

section TumbleFinishProof

open scoped FullArenaTactics

/-- `full_tumble_finish_fid` writes the bottom `EXT_PERM_FLAG` block and resets `frame_dec`. -/
theorem full_tumble_finish_fid_wp (Γ : Env) :
    ∀ a m Q X, fullTumbleFinishFidSpec a m Q X →
      Func.wp Γ full_tumble_finish_fid_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hcl0, hm, hQ⟩
  have hmv_bd := c.hmv; have hmx_bd := c.hmaxv; have hext_bd := c.hext
  unfold dimacsBound at hmv_bd hmx_bd hext_bd
  have hcmv : c.mv ≤ c.max_vars := by have := c.hbva; omega
  unfold Func.wp full_tumble_finish_fid_body
  c0_hsteps_nogrp
  · -- `extend_cap ≤ mv`: no-op
    have hle : c.extend_cap ≤ c.mv := by
      have h1 : c.extend_cap % 2 ^ 64 ≤ c.mv % 2 ^ 64 := by assumption
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h1; exact h1
    exact hQ s.core.frame_dec s.scratch.extend_stk s.scratch.extend_len m hlen
      (fun h => by omega) (fun _ => rfl) hm
  · -- `mv < extend_cap`
    have hlt : c.mv < c.extend_cap := by
      have h1 : ¬ c.extend_cap % 2 ^ 64 ≤ c.mv % 2 ^ 64 := by assumption
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h1; omega
    refine wp_while_state
      (fun (p : BitVec 64 × List (BitVec 32) × List (BitVec 32)) => (p.1, ()))
      (fun p => c.mv - p.1.toNat)
      (fun p ml =>
        p.1.toNat ≤ c.mv ∧ p.2.1.length = c.max_vars + 1 ∧ p.2.2.length = c.extend_cap ∧
        (FullMem c { core := { s.core with frame_dec := p.2.1 }
                     scratch := { s.scratch with extend_stk := p.2.2 } } ⋆ R) ml)
      (fun J hJ => by
        c0_hsteps
        exact hJ (0#64, s.core.frame_dec, s.scratch.extend_stk) m
          ⟨Nat.zero_le _, hlen.core_ok.frame_dec_len, hlen.scratch_ok.extend_stk_len, hm⟩)
      (fun J ⟨e, fd', ext'⟩ ml ⟨hele, hfdl, hextl, hml⟩ ih => ?_)
    dsimp only at hele hfdl hextl hml ih ⊢
    c0_hsteps_nogrp
    · have he_lt : e.toNat < c.mv := by
        have h1 : e.toNat < c.mv % 2 ^ 64 := by assumption
        rw [Nat.mod_eq_of_lt (by omega)] at h1; exact h1
      have he1 : (e + 1#64).toNat = e.toNat + 1 := by simp only [bv_c0]; omega
      have he_fd : e.toNat < fd'.length := by rw [hfdl]; omega
      have he1_ext : (e + 1#64).toNat < ext'.length := by rw [hextl, he1]; omega
      c0_hsteps_nogrp
      refine wp_join_group (ts := [i32])
        (fun _ m1 =>
          (FullMem c { core := { s.core with frame_dec := fd' }
                       scratch := { s.scratch with extend_stk := ext' } } ⋆ R) m1)
        (fun _ ⟨v_out, ⟨⟩⟩ m1 hm1 => by
          c0_hsteps
          exact ih (e + 1#64, fd'.set e.toNat 0xFFFFFFFF#32, ext'.set (e + 1#64).toNat v_out) m
            (by dsimp only; rw [he1]; omega)
            ⟨by rw [he1]; omega, by simp [hfdl], by simp [hextl], hm⟩)
        (fun Jv hJv => by
          c0_hsteps_nogrp
          · exact hJv (2147483647#32, ()) ml hml
          · exact hJv (fd'[e.toNat]'he_fd, ()) ml hml)
    · have h0_ext : (BitVec.ofNat 64 0).toNat < ext'.length := by
        rw [hextl]; simp only [BitVec.toNat_ofNat]; omega
      c0_hsteps
      refine hQ fd' _ _ m ?_ ?_ (fun h => absurd hlt h) hm
      · exact ⟨{ hlen.core_ok with frame_dec_len := hfdl },
          { hlen.scratch_ok with extend_stk_len := by simp [hextl] }⟩
      · intro _
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
          show BitVec.toNat (1 : BitVec 64) = 1 from rfl]
        omega

end TumbleFinishProof

/-! ## 2. `full_parse_body_tum` (`Full.fullParseBodySpec`, Unchanged Canonical Spec) -/

section ParseBodyTumProof

open scoped FullArenaTactics FullDimacsBodyTactics
open FullDimacsBodyTactics

private theorem tum_mem_to_dimacs {c : FullCfg} {s : FullState} {cnf_ptr : BitVec 64}
    {cnfBytes : List UInt8} {R : Mem 64 → Prop} {m : Mem 64}
    (h : (bytes cnf_ptr cnfBytes ⋆ FullMem c s ⋆ R) m) :
    (bytes cnf_ptr cnfBytes ⋆
      dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
      (FullRest c s ⋆ R)) m :=
  sep_ac (focus_dimacs (sep_ac h : (FullMem c s ⋆ (bytes cnf_ptr cnfBytes ⋆ R)) m))

private theorem tum_dimacs_to_mem {c : FullCfg} {s : FullState} {cur' val' cnf_ptr : BitVec 64}
    {cnfBytes : List UInt8} {R : Mem 64 → Prop} {m : Mem 64}
    (h : (bytes cnf_ptr cnfBytes ⋆
      dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) cur' val' ⋆
      (FullRest c s ⋆ R)) m) :
    (bytes cnf_ptr cnfBytes ⋆
      FullMem c { s with core := { s.core with d_cur := cur', d_val := val' } } ⋆ R) m :=
  sep_ac (unfocus_dimacs (R := bytes cnf_ptr cnfBytes ⋆ R) (sep_ac h))

private theorem tum_relabel_empty (f : Nat → Nat) :
    CNF.relabel f (shiftDownCnf CNF.empty) = shiftDownCnf CNF.empty := by
  simp [CNF.relabel, shiftDownCnf, CNF.empty]

private theorem tum_init_sparseW {c : FullCfg} {s : FullState}
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

private theorem tum_sparseInvW_of_perm {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
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

private theorem tum_sparseInvW_with_fuel_ticks {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hsp : FullSparseInvW c F0 F_cur s)
    (fuel' ticks' : BitVec 64) :
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
  exact tum_sparseInvW_of_perm hsp hlen' hw' ⟨rfl, rfl, fun _ _ => ⟨rfl, rfl, .refl _⟩⟩
    rfl rfl rfl ⟨rfl, rfl⟩

private structure ParseBodyTumInv (c : FullCfg) (s : FullState) (cnf_ptr : BitVec 64)
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
    let tum := decide (c.mv < c.extend_cap)
    TumbleInv tum c.mv st.scratch.extend_len st.core.frame_dec ∧
    TumbleCovers tum st.core.frame_dec (shiftDownCnf accCnf) ∧
    CnfVarsLt c.mv (shiftDownCnf accCnf) ∧
    ∃ F_cur,
      FullSparseInvW c
        (CNF.relabel (tumblePi tum st.core.frame_dec) (shiftDownCnf accCnf)) F_cur st ∧
      (CNF.relabel (tumblePi tum st.core.frame_dec) (shiftDownCnf accCnf)).Entails
        (cnfOfClauses F_cur)
  uns_tr : UnitUnsatTrace c.mv (s.core.vals.take (2 * c.mv)) (cnfBytes.drop i0) c.nc →
    oom = false ∧
    ((unsat = false ∧ has_cl = false ∧
        ∃ vext : List (BitVec 8), 2 * c.mv ≤ vext.length ∧
          TumbleValsRel (decide (c.mv < c.extend_cap)) c.mv st.core.frame_dec vext st.core.vals ∧
          TumbleUnusedZero (decide (c.mv < c.extend_cap)) c.mv
            st.scratch.extend_len st.core.vals ∧
          UnitUnsatTrace c.mv vext (cnfBytes.drop idx) (c.nc - i)) ∨
     (unsat = true ∧ ∃ cnf,
        parseClauses c.mv (c.nc - i) CNF.empty (cnfBytes.drop idx) = some cnf))

private abbrev ParseBodyTumPost (c : FullCfg) (s : FullState) (cnf_ptr : BitVec 64)
    (cnfBytes : List UInt8) (i0 : Nat) (R : Mem 64 → Prop) (Q : Post [i64]) : Prop :=
  ∀ r st' m', st'.LengthsOk c → (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) →
    st'.core.fuel = s.core.fuel → st'.core.oom = 0#64 → st'.core.probing = 0#64 →
    (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) →
    (r = 1#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧
      FullSparseInv c (shiftDownCnf cnf) st' ∧ st'.core.cur_level = 0) →
    (UnitUnsatTrace c.mv (s.core.vals.take (2 * c.mv)) (cnfBytes.drop i0) c.nc → r = 20#64) →
    (bytes cnf_ptr cnfBytes ⋆ FullMem c st' ⋆ R) m' → Q (r, ()) m'

private theorem pb_tum_skip_step {c : FullCfg} {s st st' : FullState}
    {cnf_ptr : BitVec 64} {cnfBytes rest : List UInt8} {i0 i idx j : Nat} {accCnf : CNF Nat}
    {oom has_cl : Bool} {cl : CNF.Clause Nat}
    (hp : ParseBodyTumInv c s cnf_ptr cnfBytes i0 i idx accCnf true oom has_cl st)
    (hi : i < c.nc) (hpc1 : parseClause c.mv (cnfBytes.drop idx) = some (cl, rest))
    (hcl_pos : ∀ lit ∈ cl.literals, 1 ≤ lit.1) (hj : j ≤ cnfBytes.length)
    (hdrop : cnfBytes.drop j = rest)
    (hst' : st' = { st with core := { st.core with d_cur := cnf_ptr + BitVec.ofNat 64 j,
                                                   d_val := 0#64 } }) :
    ParseBodyTumInv c s cnf_ptr cnfBytes i0 (i + 1) j (accCnf.add cl) true oom has_cl st' := by
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

private theorem pb_tum_oom_exit {c : FullCfg} {s st : FullState}
    {cnf_ptr : BitVec 64} {cnfBytes : List UInt8} {i0 i idx : Nat} {accCnf : CNF Nat}
    {unsat_v has_cl_v : Bool} {R : Mem 64 → Prop} {ml : Mem 64} {Q : Post [i64]}
    (hp : ParseBodyTumInv c s cnf_ptr cnfBytes i0 i idx accCnf unsat_v true has_cl_v st)
    (hml : (bytes cnf_ptr cnfBytes ⋆ FullMem c st ⋆ R) ml)
    (hQ : ParseBodyTumPost c s cnf_ptr cnfBytes i0 R Q) : Q (0#64, ()) ml :=
  hQ 0#64 st ml hp.len_ok (Or.inl rfl) hp.fuel_eq hp.oom_eq hp.prb_eq
    (fun h => by cases h) (fun h => by cases h)
    (fun hut => by cases (hp.uns_tr hut).1) hml

private theorem pb_tum_eof_ne {c : FullCfg} {s st : FullState}
    {cnf_ptr : BitVec 64} {cnfBytes : List UInt8} {i0 idx j : Nat} {accCnf : CNF Nat}
    {unsat_v oom_v has_cl_v : Bool} {R : Mem 64 → Prop} {m' : Mem 64} {Q : Post [i64]}
    (hp : ParseBodyTumInv c s cnf_ptr cnfBytes i0 c.nc idx accCnf unsat_v oom_v has_cl_v st)
    (hj : j ≤ cnfBytes.length)
    (hsw : cnfBytes.drop j = skipWsComments (cnfBytes.drop idx))
    (hne : cnf_ptr + BitVec.ofNat 64 j ≠ cnf_ptr + BitVec.ofNat 64 cnfBytes.length)
    (hfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ FullMem c
      { st with core := { st.core with d_cur := cnf_ptr + BitVec.ofNat 64 j } } ⋆ R) m')
    (hQ : ParseBodyTumPost c s cnf_ptr cnfBytes i0 R Q) : Q (0#64, ()) m' := by
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
      rcases (hp.uns_tr hut).2 with ⟨_, _, _, _, _, _, htr⟩ | ⟨_, _, hr⟩
      · rw [Nat.sub_self] at htr; cases htr
      · rw [Nat.sub_self] at hr
        simp only [parseClauses, hne_emp, Bool.false_eq_true, ↓reduceIte] at hr; cases hr) hm

private theorem pb_tum_eof_finish {c : FullCfg} {s st : FullState}
    {cnf_ptr : BitVec 64} {cnfBytes : List UInt8} {i0 idx j : Nat} {accCnf : CNF Nat}
    {unsat_v oom_v has_cl_v : Bool} {R : Mem 64 → Prop} {m' : Mem 64} {Q : Post [i64]}
    {fdec' ext' : List (BitVec 32)} {elen' : Nat}
    (hp : ParseBodyTumInv c s cnf_ptr cnfBytes i0 c.nc idx accCnf unsat_v oom_v has_cl_v st)
    (hj : j ≤ cnfBytes.length)
    (hsw : cnfBytes.drop j = skipWsComments (cnfBytes.drop idx))
    (heq : cnf_ptr + BitVec.ofNat 64 j = cnf_ptr + BitVec.ofNat 64 cnfBytes.length)
    (hfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hret : (unsat_v = true ∧ cnf_ptr = cnf_ptr) ∨ (unsat_v = false ∧ oom_v = false))
    (hlen_fin : ({ core := { st.core with d_cur := cnf_ptr + BitVec.ofNat 64 j,
                                          frame_dec := fdec' }
                   scratch := { st.scratch with extend_stk := ext',
                                                extend_len := elen' } } : FullState).LengthsOk c)
    (helen_lt : c.mv < c.extend_cap → elen' = c.mv + 1)
    (helen_noop : ¬ c.mv < c.extend_cap →
      ({ core := { st.core with d_cur := cnf_ptr + BitVec.ofNat 64 j, frame_dec := fdec' }
         scratch := { st.scratch with extend_stk := ext', extend_len := elen' } } : FullState) =
      { st with core := { st.core with d_cur := cnf_ptr + BitVec.ofNat 64 j } })
    (hm : (bytes cnf_ptr cnfBytes ⋆ FullMem c
      { core := { st.core with d_cur := cnf_ptr + BitVec.ofNat 64 j, frame_dec := fdec' }
        scratch := { st.scratch with extend_stk := ext', extend_len := elen' } } ⋆ R) m')
    (hQ : ParseBodyTumPost c s cnf_ptr cnfBytes i0 R Q) :
    Q (if unsat_v then 20#64 else 1#64, ()) m' := by
  have hj_len : j = cnfBytes.length := (cursor_eq_iff (by omega) (by omega)).mp heq
  have hemp : (skipWsComments (cnfBytes.drop idx)).isEmpty = true := by
    rw [← hsw, hj_len, List.drop_length]; rfl
  have hpc_eq := hp.pc_eq; simp only [Nat.sub_self, parseClauses] at hpc_eq
  have hpd_some : parseDimacs cnfBytes = some accCnf := by rw [← hpc_eq]; simp [hemp]
  let sf : FullState :=
    { core := { st.core with d_cur := cnf_ptr + BitVec.ofNat 64 j, frame_dec := fdec' }
      scratch := { st.scratch with extend_stk := ext', extend_len := elen' } }
  rcases hret with ⟨hunt, _⟩ | ⟨huf, hnf⟩
  · subst hunt
    exact hQ 20#64 sf m' hlen_fin (Or.inr (Or.inr rfl)) hp.fuel_eq hp.oom_eq hp.prb_eq
      (fun _ => ⟨accCnf, hpd_some, shiftDownCnf_unsat hp.vars_pos (hp.uns_inv rfl)⟩)
      (fun h => by cases h) (fun _ => rfl) hm
  · subst huf hnf
    obtain ⟨htum, hcov, hvb, F_cur, hinv_w, _⟩ := hp.ok_inv rfl rfl
    let sd : FullState := { st with core := { st.core with d_cur := cnf_ptr + BitVec.ofNat 64 j } }
    have hlen_sd : sd.LengthsOk c :=
      ⟨{ hp.len_ok.core_ok with vals_len := hp.len_ok.core_ok.vals_len }, hp.len_ok.scratch_ok⟩
    have hw_sd_rel : FullWitnessInv c
        (CNF.relabel (tumblePi (decide (c.mv < c.extend_cap)) sd.core.frame_dec)
          (shiftDownCnf accCnf)) F_cur sd.core :=
      { hinv_w.2.1 with
        arena := { hinv_w.2.1.arena with len_ok := hinv_w.2.1.arena.len_ok }
        watches := hinv_w.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) }
    have hw_sd_orig : FullWitnessInv c (shiftDownCnf accCnf) F_cur sd.core :=
      fullWitnessInv_relabel_back hp.cv_eq htum hcov hvb hw_sd_rel
    have hinv_sd : FullSparseInvW c (shiftDownCnf accCnf) F_cur sd :=
      ⟨hlen_sd, hw_sd_orig, hinv_w.2.2.1, hinv_w.2.2.2.1, hinv_w.2.2.2.2.1, hinv_w.2.2.2.2.2⟩
    have helen_le : elen' ≤ c.extend_cap := by
      by_cases hlt : c.mv < c.extend_cap
      · rw [helen_lt hlt]; omega
      · have hseq := helen_noop hlt
        have hel_eq : elen' = st.scratch.extend_len := congrArg (fun x => x.scratch.extend_len) hseq
        rw [hel_eq]; exact hinv_w.2.2.2.2.1.2
    have hinv_sf_w : FullSparseInvW c (shiftDownCnf accCnf) F_cur sf :=
      fullSparseInvW_with_fd_ext hinv_sd hp.cl0 hlen_fin.core_ok.frame_dec_len
        hlen_fin.scratch_ok.extend_stk_len helen_le
    exact hQ 1#64 sf m' hlen_fin (Or.inr (Or.inl rfl)) hp.fuel_eq hp.oom_eq hp.prb_eq
      (fun h => by cases h) (fun _ => ⟨accCnf, hpd_some, hinv_sf_w.toSparse, hp.cl0⟩)
      (fun hut => by rcases (hp.uns_tr hut).2 with ⟨_, _, _, _, _, _, htr⟩ | ⟨ht, _⟩
                     · rw [Nat.sub_self] at htr; cases htr
                     · cases ht) hm

/-- Tumble + lazy-activation `full_parse_body_tum` satisfies **exact unchanged canonical
`Full.fullParseBodySpec`** (parameterized by `fullPropagateDelSpec`). -/
theorem full_parse_body_tum_del_wp (Γ : Env)
    (hSkip : ∀ a m Q X, fullSkipClSpec a m Q X → Γ "full_skip_cl" [i64, i64] [.bool] a m Q X)
    (hIngest : ∀ a m Q X, fullIngestClTumSpec a m Q X →
      Γ "full_ingest_cl" [i64, i64] [i64] a m Q X)
    (hProp : ∀ a m Q X, fullPropagateDelSpec a m Q X → Γ "full_propagate" [i64] [i64] a m Q X)
    (hSwc : ∀ a m Q X, kissatSkipWsCommentsSpec a m Q X →
      Γ "kissat_skip_ws_comments" [i64, i64] [i64] a m Q X)
    (hFinish : ∀ a m Q X, fullTumbleFinishFidSpec a m Q X →
      Γ "full_tumble_finish_fid" [i64] [] a m Q X) :
    ∀ a m Q X, fullParseBodySpec a m Q X → Func.wp Γ full_parse_body_tum_body a m Q X := by
  rintro ⟨h, cend, ⟨⟩⟩ m Q X
    ⟨c, s, cnf_ptr, cnfBytes, i0, R, rfl, rfl, hfit, hi0, hhdr, hcv0, hdcur, hcl0, hte0, hpr0,
      hal0, hoom0, hprb0, hinc0, hvals0, hwvec0, hinv0, hm, hQ⟩
  have hnc_bd := c.hnc; have hmv_bd := c.hmv; have hmx_bd := c.hmaxv; have hext_bd := c.hext
  unfold dimacsBound at hnc_bd hmv_bd hmx_bd hext_bd
  have hcmv0 : c.mv ≤ c.max_vars := hcv0 ▸ hinv0.1.lengths.core_ok.cur_vars_le
  have hpd_init : parseClauses c.mv c.nc CNF.empty (cnfBytes.drop i0) = parseDimacs cnfBytes := by
    simp [parseDimacs, hhdr]
  obtain ⟨hinv_w0, hent_0⟩ :=
    tum_init_sparseW hinv0 hcv0 hal0 hte0 hcl0 hinc0 hvals0 hwvec0
  have hgu31 : 31 < s.scratch.glue_used.length := by
    rw [hinv0.1.lengths.scratch_ok.glue_used_len]; decide
  unfold Func.wp full_parse_body_tum_body
  c0_hsteps_nogrp
  let s_gu : FullState :=
    { s with scratch := { s.scratch with glue_used := s.scratch.glue_used.set 31 0#32 } }
  have hinv_gu : FullSparseInvW c (shiftDownCnf CNF.empty) [] s_gu :=
    fullSparseInvW_with_gu hinv_w0 (by simp [hinv0.1.lengths.scratch_ok.glue_used_len])
  -- Join after `if (h->extend_cap > h->d.mv) { fd[0..mv-1] = 0xFFFFFFFF; extend_len = 0; }`
  refine wp_join_state0 (α := FullState)
    (fun s_init m_init =>
      (bytes cnf_ptr cnfBytes ⋆ FullMem c s_init ⋆ R) m_init ∧
      ParseBodyTumInv c s cnf_ptr cnfBytes i0 0 i0 CNF.empty false false false s_init)
    (fun _ s_init m_init ⟨hm_init, hp_init⟩ => ?_)
    (fun Jinit hJinit => ?_)
  · -- Main parse loop: `while (i < h->d.nc)`
    c0_hsteps_nogrp
    refine wp_loop_group
      (fun r (unsat_v, oom_v, has_cl_v, iv, ()) ml => ∃ i idx accCnf st,
        r = c.nc - i ∧ iv = BitVec.ofNat 64 i ∧
        ParseBodyTumInv c s cnf_ptr cnfBytes i0 i idx accCnf unsat_v oom_v has_cl_v st ∧
        (bytes cnf_ptr cnfBytes ⋆ FullMem c st ⋆ R) ml) ?_ ?_
    · rintro L r ⟨unsat_v, oom_v, has_cl_v, iv, ⟨⟩⟩ ml ih ⟨i, idx, accCnf, st, rfl, rfl, hp, hml⟩
      have hile := hp.i_le; have hidx := hp.idx_le; have hcv_st := hp.cv_eq
      have hdcur_st := hp.d_cur_eq; have hlen_st := hp.len_ok; have hcl_st := hp.cl0
      have hfu_st := hp.fuel_eq; have hoom_st := hp.oom_eq; have hprb_st := hp.prb_eq
      c0_hsteps
      · have hilt : i < c.nc := by clear hm hm_init hml hQ; c0_bound
        have hunt : unsat_v = true := by assumption
        subst hunt; have hsub_eq : c.nc - i = (c.nc - (i + 1)) + 1 := by omega
        have hinc : BitVec.ofNat 64 i + 1 = BitVec.ofNat 64 (i + 1) := by
          apply BitVec.eq_of_toNat_eq
          change (i % 2 ^ 64 + 1) % 2 ^ 64 = (i + 1) % 2 ^ 64; omega
        c0_call hSkip
        refine ⟨cnf_ptr, BitVec.ofNat 64 c.nc, st.core.d_val, c.mv, cnfBytes, idx,
          FullRest c st ⋆ R, rfl, hfit, by omega, hidx,
          by rw [← hdcur_st]; exact tum_mem_to_dimacs hml, ?_⟩
        cases hpc1 : parseClause c.mv (cnfBytes.drop idx) with
        | none =>
          intro cur' val' m' hm'; c0_hsteps
          exact hQ 0#64 { st with core := { st.core with d_cur := cur', d_val := val' } } m'
            ⟨{ hlen_st.core_ok with vals_len := hlen_st.core_ok.vals_len }, hlen_st.scratch_ok⟩
            (Or.inl rfl) hfu_st hoom_st hprb_st (fun h => by cases h) (fun h => by cases h)
            (fun hut => by rcases (hp.uns_tr hut).2 with ⟨hf, _⟩ | ⟨_, _, hr⟩
                           · cases hf
                           · rw [hsub_eq, parseClauses, hpc1] at hr; cases hr)
            (tum_dimacs_to_mem hm')
        | some p =>
          rcases p with ⟨cl, rest⟩; intro j m' hcl_pos _ hj hdrop hm'; c0_hsteps
          · exact ih (c.nc - (i + 1)) _ _ (by omega)
              ⟨i + 1, j, accCnf.add cl, _, rfl, hinc,
                pb_tum_skip_step hp hilt hpc1 hcl_pos hj hdrop rfl, tum_dimacs_to_mem hm'⟩
          · cases (by assumption : true = false)
      · have hoo : oom_v = true := by assumption
        subst hoo; exact pb_tum_oom_exit hp hml hQ
      · have hilt : i < c.nc := by clear hm hm_init hml hQ; c0_bound
        have huf : unsat_v = false := by assumption
        have hnf : oom_v = false := by assumption
        subst huf hnf; have hsub_eq : c.nc - i = (c.nc - (i + 1)) + 1 := by omega
        have hinc : BitVec.ofNat 64 i + 1 = BitVec.ofNat 64 (i + 1) := by
          apply BitVec.eq_of_toNat_eq
          change (i % 2 ^ 64 + 1) % 2 ^ 64 = (i + 1) % 2 ^ 64; omega
        obtain ⟨htum_st, hcov_st, hvb_st, F_cur, hinv_st, hent_st⟩ := hp.ok_inv rfl rfl
        c0_call hIngest
        refine ⟨c, accCnf, F_cur, st, cnf_ptr, cnfBytes, idx, R, rfl, rfl, hfit, hidx,
          hcv_st, hdcur_st, hcl_st, htum_st, hcov_st, hvb_st, hinv_st, hent_st, hml, ?_⟩
        cases hpc1 : parseClause c.mv (cnfBytes.drop idx) with
        | none =>
          intro st' m' hlen' hfu' hoom' hprb' hm'; c0_hsteps
          exact hQ 0#64 st' m' hlen' (Or.inl rfl) (hfu'.trans hfu_st) (hoom'.trans hoom_st)
            (hprb'.trans hprb_st) (fun h => by cases h) (fun h => by cases h)
            (fun hut => by rcases (hp.uns_tr hut).2 with ⟨_, _, _, _, _, _, htr⟩ | ⟨ht, _⟩
                           · rw [hsub_eq] at htr; cases htr with
                             | conflict _ hpc_s _ _ => rw [hpc1] at hpc_s; cases hpc_s
                             | step _ hpc_s _ _ => rw [hpc1] at hpc_s; cases hpc_s
                           · cases ht) hm'
        | some p =>
          rcases p with ⟨cl, rest⟩
          intro r_in st' j m' hcl_pos _ hj hdrop hlen' hcv' hd' hcl' hfu' hoom' hprb'
            htum' hcov' hvb' hr_dom hok_in huns_in hunit_ok hunit_fl hm'
          have hpc_next : parseClauses c.mv (c.nc - (i + 1)) (accCnf.add cl) (cnfBytes.drop j) =
              parseDimacs cnfBytes := by rw [← hp.pc_eq, hsub_eq, parseClauses, hpc1, ← hdrop]; rfl
          rcases hr_dom with rfl | rfl | rfl
          · -- `r_in = 1#64`: update `has_cl`, then optionally run eager `full_propagate`
            obtain ⟨F_cur', hsp', hent'⟩ := hok_in rfl
            have hno_ut_te_eq : st'.core.trail_end = st.core.trail_end →
                ¬ UnitUnsatTrace c.mv (s.core.vals.take (2 * c.mv)) (cnfBytes.drop i0) c.nc := by
              intro hte_eq hut
              rcases (hp.uns_tr hut).2 with ⟨_, _, vext, hvl, hrel, hunz, htr⟩ | ⟨ht, _⟩
              · rw [hsub_eq] at htr; cases htr with
                | conflict hl hpc_s hvf _ =>
                  rw [hpc1] at hpc_s
                  rcases Prod.mk.inj (Option.some.inj hpc_s) with ⟨hcl_eq, _⟩
                  have hr2 := hunit_fl vext _ hvl hl hrel hcl_eq hvf; cases hr2
                | step hl hpc_s hv0 _ =>
                  rw [hpc1] at hpc_s
                  rcases Prod.mk.inj (Option.some.inj hpc_s) with ⟨hcl_eq, _⟩
                  have hte_inc := (hunit_ok vext _ hvl hl hrel hunz hcl_eq hv0).2.2.2.1; omega
              · cases ht
            have h_ut_step :
                UnitUnsatTrace c.mv (s.core.vals.take (2 * c.mv)) (cnfBytes.drop i0) c.nc →
                has_cl_v = false ∧ st'.core.trail_end ≠ st.core.trail_end ∧
                ∃ vext' : List (BitVec 8), 2 * c.mv ≤ vext'.length ∧
                  TumbleValsRel (decide (c.mv < c.extend_cap)) c.mv
                    st'.core.frame_dec vext' st'.core.vals ∧
                  TumbleUnusedZero (decide (c.mv < c.extend_cap)) c.mv
                    st'.scratch.extend_len st'.core.vals ∧
                  UnitUnsatTrace c.mv vext' (cnfBytes.drop j) (c.nc - (i + 1)) := by
              intro hut
              rcases (hp.uns_tr hut).2 with ⟨_, hhc0, vext, hvl, hrel, hunz, htr⟩ | ⟨ht, _⟩
              · rw [hsub_eq] at htr; cases htr with
                | conflict hl hpc_s hvf _ =>
                  rw [hpc1] at hpc_s
                  rcases Prod.mk.inj (Option.some.inj hpc_s) with ⟨hcl_eq, _⟩
                  have hr2 := hunit_fl vext _ hvl hl hrel hcl_eq hvf; cases hr2
                | step hl hpc_s hv0 htr_next =>
                  rw [hpc1] at hpc_s
                  rcases Prod.mk.inj (Option.some.inj hpc_s) with ⟨hcl_eq, hreq⟩
                  obtain ⟨_, hrel', hunz', hte_inc, _⟩ :=
                    hunit_ok vext _ hvl hl hrel hunz hcl_eq hv0
                  refine ⟨hhc0, by omega, (vext.set _ 1#8).set (_ ^^^ 1) 0xFF#8,
                    by simp; omega, hrel', hunz', ?_⟩
                  rw [hdrop, hreq]; exact htr_next
              · cases ht
            c0_hsteps_nogrp
            apply wp_unroll_group; intro J1 hJ1; c0_hsteps_nogrp
            apply wp_unroll_group; intro J2 hJ2; c0_hsteps_nogrp
            refine wp_join_group (ts := [.bool])
              (fun (hc_new, ()) mj => mj = m' ∧
                (UnitUnsatTrace c.mv (s.core.vals.take (2 * c.mv)) (cnfBytes.drop i0) c.nc →
                  hc_new = false))
              (fun _ (hc_new, ()) mj ⟨hmj, hhc_ut⟩ => ?_)
              (fun Jhc hJhc => ?_)
            · subst mj
              c0_hsteps_nogrp
              refine wp_join_group (ts := [.bool, .bool])
                (fun (uns_n, oom_n, ()) mp => ∃ st_p : FullState,
                  ParseBodyTumInv c s cnf_ptr cnfBytes i0 (i + 1) j (accCnf.add cl)
                    uns_n oom_n hc_new st_p ∧
                  (bytes cnf_ptr cnfBytes ⋆ FullMem c st_p ⋆ R) mp)
                (fun _ (uns_n, oom_n, ()) mp ⟨st_p, hp_p, hmp⟩ => by
                  c0_hsteps_nogrp
                  exact ih (c.nc - (i + 1)) _ _ (by omega)
                    ⟨i + 1, j, accCnf.add cl, st_p, rfl, hinc, hp_p, hmp⟩)
                (fun Jp hJp => ?_)
              have hinv_noprop :
                  ParseBodyTumInv c s cnf_ptr cnfBytes i0 (i + 1) j (accCnf.add cl)
                    false false hc_new st' :=
                ⟨by omega, hj, hcv', hd', hlen', hcl', hfu'.trans hfu_st, hoom'.trans hoom_st,
                  hprb'.trans hprb_st, cnfVarsPos_add hp.vars_pos hcl_pos, hpc_next,
                  (fun h => by cases h),
                  (fun _ _ => ⟨htum', hcov', hvb', F_cur', hsp', hent'⟩),
                  (fun hut => ⟨rfl, Or.inl ⟨rfl, hhc_ut hut, (h_ut_step hut).2.2⟩⟩)⟩
              c0_hsteps_nogrp
              · have hhc_true : hc_new = true := by assumption
                have hnot_ut :
                    ¬ UnitUnsatTrace c.mv (s.core.vals.take (2 * c.mv)) (cnfBytes.drop i0) c.nc :=
                  fun hut => by have := hhc_ut hut; rw [hhc_true] at this; cases this
                let F1_rel := CNF.relabel
                  (tumblePi (decide (c.mv < c.extend_cap)) st'.core.frame_dec)
                  (shiftDownCnf (accCnf.add cl))
                c0_call hProp
                refine ⟨c, F1_rel, F_cur', st',
                  bytes cnf_ptr cnfBytes ⋆ R, rfl, hsp'.1, hsp'.2.1, hsp'.2.2.2.2.2,
                  sep_ac hm', ?_⟩
                intro pr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ delayed_pr m_pr s_pr
                  hlen_pr hw_pr _ hperm_pr _ hpr_dom hpr0 hpr1 _ _ hm_pr
                have hsp_pr : FullSparseInvW c F1_rel F_cur' s_pr :=
                  tum_sparseInvW_of_perm hsp' hlen_pr hw_pr hperm_pr rfl rfl rfl ⟨rfl, rfl⟩
                have hsp_rest : FullSparseInvW c F1_rel F_cur'
                    { core := { s_pr.core with fuel := st'.core.fuel }
                      scratch := { s_pr.scratch with search_ticks := st'.scratch.search_ticks } } :=
                  tum_sparseInvW_with_fuel_ticks hsp_pr st'.core.fuel st'.scratch.search_ticks
                rcases hpr_dom with rfl | rfl | rfl
                · have hoom_pr0 : s_pr.core.oom = 0#64 := (hpr0 rfl).2.1 (hoom'.trans hoom_st)
                  c0_hsteps
                  refine hJp (false, false, ()) _ ⟨_, ?_, sep_ac hm⟩
                  exact ⟨by omega, hj, hcv', hd', hsp_rest.1, hcl', hfu'.trans hfu_st, hoom_pr0,
                    hprb'.trans hprb_st, cnfVarsPos_add hp.vars_pos hcl_pos, hpc_next,
                    (fun h => by cases h),
                    (fun _ _ => ⟨htum', hcov', hvb', F_cur', hsp_rest, hent'⟩),
                    (fun hut => False.elim (hnot_ut hut))⟩
                · have hoom_pr1 : s_pr.core.oom = 0#64 := (hpr1 rfl).2.1
                  have huns_rel : F1_rel.Unsat :=
                    level0_unsat_of_conflict_okW (s := s_pr) hw_pr hcl' (hpr1 rfl).2.2
                  have huns_pr1 : (shiftDownCnf (accCnf.add cl)).Unsat :=
                    cnf_unsat_of_relabel_tumble htum' hcov' hvb' huns_rel
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
                    rcases (hp.uns_tr hut).2 with ⟨_, _, vext, hvl, hrel, hunz, htr⟩ | ⟨ht, _⟩
                    · rw [hsub_eq] at htr; cases htr with
                      | conflict _ hpc_s _ hrest =>
                        rw [hpc1] at hpc_s
                        rcases Prod.mk.inj (Option.some.inj hpc_s) with ⟨_, hreq⟩
                        rwa [hdrop, hreq]
                      | step hl hpc_s hv0 _ =>
                        rw [hpc1] at hpc_s
                        rcases Prod.mk.inj (Option.some.inj hpc_s) with ⟨hcl_eq, _⟩
                        exact absurd (hunit_ok vext _ hvl hl hrel hunz hcl_eq hv0).1 (by decide)
                    · cases ht)⟩, hm'⟩
          · -- `r_in = 3#64`: `oom_seen = true`
            c0_hsteps
            exact ih (c.nc - (i + 1)) _ _ (by omega)
              ⟨i + 1, j, accCnf.add cl, st', rfl, hinc,
                ⟨by omega, hj, hcv', hd', hlen', hcl', hfu'.trans hfu_st, hoom'.trans hoom_st,
                  hprb'.trans hprb_st, cnfVarsPos_add hp.vars_pos hcl_pos, hpc_next,
                  (fun h => by cases h), (fun _ h => by cases h),
                  (fun hut => by
                    rcases (hp.uns_tr hut).2 with ⟨_, _, vext, hvl, hrel, hunz, htr⟩ | ⟨ht, _⟩
                    · rw [hsub_eq] at htr; cases htr with
                      | conflict hl hpc_s hvf _ =>
                        rw [hpc1] at hpc_s
                        rcases Prod.mk.inj (Option.some.inj hpc_s) with ⟨hcl_eq, _⟩
                        exact absurd (hunit_fl vext _ hvl hl hrel hcl_eq hvf) (by decide)
                      | step hl hpc_s hv0 _ =>
                        rw [hpc1] at hpc_s
                        rcases Prod.mk.inj (Option.some.inj hpc_s) with ⟨hcl_eq, _⟩
                        exact absurd (hunit_ok vext _ hvl hl hrel hunz hcl_eq hv0).1 (by decide)
                    · cases ht)⟩, hm'⟩
      · have hoo : oom_v = true := by assumption
        subst hoo; exact pb_tum_oom_exit hp hml hQ
      · have hieq : i = c.nc := by clear hml hQ; c0_bound
        subst hieq; c0_call hSwc
        refine ⟨cnf_ptr, cnfBytes, idx, FullMem c st ⋆ R, hdcur_st, rfl, hfit, hidx,
          sep_ac hml, fun j _ hj hsw => ?_⟩
        c0_hsteps_nogrp
        · exact pb_tum_eof_ne hp hj hsw (by assumption) hfit (sep_ac hm) hQ
        · have heof : cnf_ptr + BitVec.ofNat 64 j = cnf_ptr + BitVec.ofNat 64 cnfBytes.length := by
            assumption
          let sd : FullState :=
            { st with core := { st.core with d_cur := cnf_ptr + BitVec.ofNat 64 j } }
          have hlen_sd : sd.LengthsOk c :=
            ⟨{ hlen_st.core_ok with vals_len := hlen_st.core_ok.vals_len }, hlen_st.scratch_ok⟩
          c0_call hFinish
          refine ⟨c, sd, bytes cnf_ptr cnfBytes ⋆ R, rfl, hlen_sd, hcl_st, sep_ac hm,
            fun fdec' ext' elen' m_fin hlen_fin hel_lt hel_noop hm_fin => ?_⟩
          c0_hsteps
          · have hunt : unsat_v = true := by assumption
            simpa [hunt] using pb_tum_eof_finish hp hj hsw heof hfit (Or.inl ⟨hunt, rfl⟩)
              hlen_fin hel_lt hel_noop (sep_ac hm_fin) hQ
          · have huf : unsat_v = false := by assumption
            have hnf : oom_v = false := by assumption
            simpa [huf] using pb_tum_eof_finish hp hj hsw heof hfit (Or.inr ⟨huf, hnf⟩)
              hlen_fin hel_lt hel_noop (sep_ac hm_fin) hQ
    · intro L hL; c0_hsteps
      exact hL c.nc _ m_init ⟨0, i0, CNF.empty, s_init, by simp, rfl, hp_init, hm_init⟩
  · -- Entry of `Jinit`: `if (h->extend_cap > h->d.mv)`
    c0_hsteps_nogrp
    · -- `c.mv < c.extend_cap`: initialize `fd[0..mv-1] = 0xFFFFFFFFu`, `extend_len = 0`
      have hlt_ec : c.mv < c.extend_cap := by
        have h1 : c.mv < c.extend_cap % 2 ^ 64 := by assumption
        rw [Nat.mod_eq_of_lt (by omega)] at h1; exact h1
      have htum_t : decide (c.mv < c.extend_cap) = true := decide_eq_true hlt_ec
      refine wp_while_state
        (fun (p : BitVec 64 × List (BitVec 32)) => (p.1, ()))
        (fun p => c.mv - p.1.toNat)
        (fun p ml =>
          p.1.toNat ≤ c.mv ∧ p.2.length = c.max_vars + 1 ∧
          (∀ k < p.1.toNat, p.2[k]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32) ∧
          (bytes cnf_ptr cnfBytes ⋆
            FullMem c { s_gu with core := { s_gu.core with frame_dec := p.2 } } ⋆ R) ml)
        (fun Jf hJf => by
          c0_hsteps
          exact hJf (0#64, s_gu.core.frame_dec) m
            ⟨Nat.zero_le _, hinv_gu.1.core_ok.frame_dec_len, (fun _ h => by cases h), sep_ac hm⟩)
        (fun Jf ⟨e, fd'⟩ ml ⟨hele, hfdl, hff, hml⟩ ihf => ?_)
      dsimp only at hele hfdl hff hml ihf ⊢
      c0_hsteps_nogrp
      · have he_lt : e.toNat < c.mv := by assumption
        have he1 : (e + 1#64).toNat = e.toNat + 1 := by simp only [bv_c0]; omega
        have he_fd : e.toNat < fd'.length := by rw [hfdl]; omega
        c0_hsteps
        refine ihf (e + 1#64, fd'.set e.toNat 0xFFFFFFFF#32) m
          (by dsimp only; rw [he1]; omega)
          ⟨by rw [he1]; omega, by simp [hfdl], fun k hk => ?_, sep_ac hm⟩
        rw [he1] at hk
        by_cases hke : k = e.toNat
        · subst hke; rw [List.getElem?_set_self he_fd]; rfl
        · rw [List.getElem?_set_ne (Ne.symm hke)]; exact hff k (by omega)
      · have he_eq : e.toNat = c.mv := by
          have h1 : ¬ e.toNat < c.mv := by assumption
          omega
        rw [he_eq] at hff
        c0_hsteps
        let s1 : FullState :=
          { core := { s_gu.core with frame_dec := fd' }
            scratch := { s_gu.scratch with extend_len := 0 } }
        have hsp1 : FullSparseInvW c (shiftDownCnf CNF.empty) [] s1 :=
          fullSparseInvW_with_fd_ext hinv_gu hcl0 hfdl hinv_gu.1.scratch_ok.extend_stk_len
            (Nat.zero_le _)
        have hv_take : s.core.vals.take (2 * c.mv) = List.replicate (2 * c.mv) 0#8 := by
          rw [hvals0, List.take_replicate, Nat.min_eq_left (by omega)]
        exact hJinit s1 m
          ⟨sep_ac hm,
           ⟨Nat.zero_le _, hi0, hcv0, hdcur, hsp1.1, hcl0, rfl, hoom0, hprb0,
            cnfVarsPos_empty, by simpa using hpd_init, (fun h => by cases h),
            (fun _ _ => ⟨fun _ => tumbleMapInv_init hff, tumbleCovers_empty _ _, cnfVarsLt_empty _,
              [], by rw [tum_relabel_empty]; exact hsp1, by rw [tum_relabel_empty]; exact hent_0⟩),
            (fun hut => ⟨rfl, Or.inl ⟨rfl, rfl, s.core.vals.take (2 * c.mv),
              by rw [hv_take, List.length_replicate]; exact Nat.le_refl _,
              by rw [hv_take]; change TumbleValsRel _ _ _ _ s.core.vals; rw [hvals0]
                 exact tumbleValsRel_init,
              by change TumbleUnusedZero _ _ 0 s.core.vals; rw [hvals0]
                 exact tumbleUnusedZero_init hcmv0,
              by rwa [Nat.sub_zero]⟩⟩)⟩⟩
    · -- `¬ (c.mv < c.extend_cap)`: `tum = false`, keep `s_gu`
      have hge_ec : ¬ c.mv < c.extend_cap := by
        have h1 : ¬ c.mv < c.extend_cap % 2 ^ 64 := by assumption
        rw [Nat.mod_eq_of_lt (by omega)] at h1; exact h1
      have htum_f : decide (c.mv < c.extend_cap) = false := decide_eq_false hge_ec
      have hv_take : s.core.vals.take (2 * c.mv) = List.replicate (2 * c.mv) 0#8 := by
        rw [hvals0, List.take_replicate, Nat.min_eq_left (by omega)]
      exact hJinit s_gu m
        ⟨sep_ac hm,
         ⟨Nat.zero_le _, hi0, hcv0, hdcur, hinv_gu.1, hcl0, rfl, hoom0, hprb0,
          cnfVarsPos_empty, by simpa using hpd_init, (fun h => by cases h),
          (fun _ _ => ⟨(fun ht => by rw [htum_f] at ht; cases ht),
            tumbleCovers_empty _ _, cnfVarsLt_empty _,
            [], by rw [tum_relabel_empty]; exact hinv_gu,
            by rw [tum_relabel_empty]; exact hent_0⟩),
          (fun hut => ⟨rfl, Or.inl ⟨rfl, rfl, s.core.vals.take (2 * c.mv),
            by rw [hv_take, List.length_replicate]; exact Nat.le_refl _,
            by rw [hv_take]; change TumbleValsRel _ _ _ _ s.core.vals; rw [hvals0]
               exact tumbleValsRel_init,
            (fun ht => by rw [htum_f] at ht; cases ht),
            by rwa [Nat.sub_zero]⟩⟩)⟩⟩

/-- Canonical `fullPropagateSpec` wrapper for `full_parse_body_tum_del_wp`. -/
theorem full_parse_body_tum_wp (Γ : Env)
    (hSkip : ∀ a m Q X, fullSkipClSpec a m Q X → Γ "full_skip_cl" [i64, i64] [.bool] a m Q X)
    (hIngest : ∀ a m Q X, fullIngestClTumSpec a m Q X →
      Γ "full_ingest_cl" [i64, i64] [i64] a m Q X)
    (hProp : ∀ a m Q X, fullPropagateSpec a m Q X → Γ "full_propagate" [i64] [i64] a m Q X)
    (hSwc : ∀ a m Q X, kissatSkipWsCommentsSpec a m Q X →
      Γ "kissat_skip_ws_comments" [i64, i64] [i64] a m Q X)
    (hFinish : ∀ a m Q X, fullTumbleFinishFidSpec a m Q X →
      Γ "full_tumble_finish_fid" [i64] [] a m Q X) :
    ∀ a m Q X, fullParseBodySpec a m Q X → Func.wp Γ full_parse_body_tum_body a m Q X :=
  full_parse_body_tum_del_wp Γ hSkip hIngest
    (fun a m Q X h => hProp a m Q X (fullPropagateSpec_of_del h)) hSwc hFinish

end ParseBodyTumProof

end LeanQbe.T.Examples.Kissat.FullFidelityTumble

end
