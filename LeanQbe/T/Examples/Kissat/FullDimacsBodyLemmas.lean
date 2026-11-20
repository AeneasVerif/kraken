module

public import LeanQbe.T.Examples.Kissat.FullDimacsBodyLemmas2

/-!
# Soundness Proofs for Kissat `D-Full` DIMACS Body Parser (`Stage 4`, Part 3)

Proves `full_parse_body_wp` (`Full1.full_parse_body`), UNSAT-only soundness + deterministic
level-0 `UnitUnsatTrace` non-vacuity.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.Full

open Std Std.Sat Std.ExtHashMap LeanQbe.T.C0Step
open LeanQbe.T LeanQbe.T.ProofUtil LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open Kraken.Bedrock2.Test

section ParseBodyProof

open scoped FullArenaTactics FullDimacsBodyTactics
open FullDimacsBodyTactics FullDimacsBodySpecs

private theorem full_mem_to_dimacs {c : FullCfg} {s : FullState} {cnf_ptr : BitVec 64}
    {cnfBytes : List UInt8} {R : Mem 64 → Prop} {m : Mem 64}
    (h : (bytes cnf_ptr cnfBytes ⋆ FullMem c s ⋆ R) m) :
    (bytes cnf_ptr cnfBytes ⋆
      dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
      (FullRest c s ⋆ R)) m := by
  have h1 := focus_dimacs (sep_ac h : (FullMem c s ⋆ (bytes cnf_ptr cnfBytes ⋆ R)) m)
  exact sep_ac h1

private theorem full_dimacs_to_mem {c : FullCfg} {s : FullState} {cur' val' cnf_ptr : BitVec 64}
    {cnfBytes : List UInt8} {R : Mem 64 → Prop} {m : Mem 64}
    (h : (bytes cnf_ptr cnfBytes ⋆
      dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) cur' val' ⋆
      (FullRest c s ⋆ R)) m) :
    (bytes cnf_ptr cnfBytes ⋆
      FullMem c { s with core := { s.core with d_cur := cur', d_val := val' } } ⋆ R) m :=
  sep_ac (unfocus_dimacs (R := bytes cnf_ptr cnfBytes ⋆ R) (sep_ac h))

private theorem unitUnsatTrace_congr_vals {mv : Nat} :
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

private theorem full_init_sparseW {c : FullCfg} {s : FullState}
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

private structure ParseBodyInv (c : FullCfg) (s : FullState) (cnf_ptr : BitVec 64)
    (cnfBytes : List UInt8) (i0 i idx : Nat) (accCnf : CNF Nat) (unsat oom : Bool)
    (st : FullState) : Prop where
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
    ((unsat = false ∧ UnitUnsatTrace c.mv st.core.vals (cnfBytes.drop idx) (c.nc - i)) ∨
     (unsat = true ∧ ∃ cnf, parseClauses c.mv (c.nc - i) CNF.empty (cnfBytes.drop idx) = some cnf))

private theorem parse_body_skip_step {c : FullCfg} {s st st' : FullState}
    {cnf_ptr : BitVec 64} {cnfBytes rest : List UInt8} {i0 i idx j : Nat} {accCnf : CNF Nat}
    {oom : Bool} {cl : CNF.Clause Nat}
    (hp : ParseBodyInv c s cnf_ptr cnfBytes i0 i idx accCnf true oom st)
    (hi : i < c.nc) (hpc1 : parseClause c.mv (cnfBytes.drop idx) = some (cl, rest))
    (hcl_pos : ∀ lit ∈ cl.literals, 1 ≤ lit.1) (hj : j ≤ cnfBytes.length)
    (hdrop : cnfBytes.drop j = rest)
    (hst' : st' = { st with core := { st.core with d_cur := cnf_ptr + BitVec.ofNat 64 j,
                                                   d_val := 0#64 } }) :
    ParseBodyInv c s cnf_ptr cnfBytes i0 (i + 1) j (accCnf.add cl) true oom st' := by
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

private theorem parse_body_ingest_step {c : FullCfg} {s st st' : FullState}
    {cnf_ptr : BitVec 64} {cnfBytes rest : List UInt8} {i0 i idx j : Nat} {accCnf : CNF Nat}
    {r_in : BitVec 64} {cl : CNF.Clause Nat}
    (hp : ParseBodyInv c s cnf_ptr cnfBytes i0 i idx accCnf false false st)
    (hi : i < c.nc) (hpc1 : parseClause c.mv (cnfBytes.drop idx) = some (cl, rest))
    (hcl_pos : ∀ lit ∈ cl.literals, 1 ≤ lit.1) (hj : j ≤ cnfBytes.length)
    (hdrop : cnfBytes.drop j = rest) (hlen' : st'.LengthsOk c) (hcv' : st'.core.cur_vars = c.mv)
    (hd' : st'.core.d_cur = cnf_ptr + BitVec.ofNat 64 j) (hcl' : st'.core.cur_level = 0)
    (hfu' : st'.core.fuel = st.core.fuel) (hoom' : st'.core.oom = st.core.oom)
    (hprb' : st'.core.probing = st.core.probing)
    (hr_dom : r_in = 1#64 ∨ r_in = 2#64 ∨ r_in = 3#64)
    (hok_in : r_in = 1#64 → ∃ F_cur', FullSparseInvW c (shiftDownCnf (accCnf.add cl)) F_cur' st' ∧
      (shiftDownCnf (accCnf.add cl)).Entails (cnfOfClauses F_cur'))
    (huns_in : r_in = 2#64 → (shiftDownCnf (accCnf.add cl)).Unsat)
    (hunit_ok : ∀ l < 2 * c.mv, cl = CNF.Clause.ofLiterals [kissatLitToDimacsLiteral l] →
      st.core.vals[l]?.getD 0#8 = 0#8 → r_in = 1#64 ∧
      (∀ k < 2 * c.mv, st'.core.vals[k]?.getD 0#8 =
        ((st.core.vals.set l 1#8).set (l ^^^ 1) 0xFF#8)[k]?.getD 0#8) ∧
      st'.core.trail_end = st.core.trail_end + 1 ∧ st'.core.propagated = st.core.propagated)
    (hunit_fl : ∀ l < 2 * c.mv, cl = CNF.Clause.ofLiterals [kissatLitToDimacsLiteral l] →
      st.core.vals[l]?.getD 0#8 = 0xFF#8 → r_in = 2#64) :
    ParseBodyInv c s cnf_ptr cnfBytes i0 (i + 1) j (accCnf.add cl)
      (decide (r_in = 2#64)) (decide (r_in = 3#64)) st' := by
  have hsub : c.nc - i = (c.nc - (i + 1)) + 1 := by omega
  have hpc_next : parseClauses c.mv (c.nc - (i + 1)) (accCnf.add cl) (cnfBytes.drop j) =
      parseDimacs cnfBytes := by rw [← hp.pc_eq, hsub, parseClauses, hpc1, ← hdrop]; rfl
  have hcmv_st : c.mv ≤ c.max_vars := hp.cv_eq ▸ hp.len_ok.core_ok.cur_vars_le
  have hcmv_st' : c.mv ≤ c.max_vars := hcv' ▸ hlen'.core_ok.cur_vars_le
  rcases hr_dom with rfl | rfl | rfl <;>
    refine ⟨by omega, hj, hcv', hd', hlen', hcl', hfu'.trans hp.fuel_eq, hoom'.trans hp.oom_eq,
      hprb'.trans hp.prb_eq, cnfVarsPos_add hp.vars_pos hcl_pos, hpc_next, ?_, ?_, ?_⟩
  · exact fun hc => by cases hc
  · exact fun _ _ => hok_in rfl
  · intro hut; refine ⟨rfl, Or.inl ⟨rfl, ?_⟩⟩
    rcases (hp.uns_tr hut).2 with ⟨_, htr⟩ | ⟨ht, _⟩
    · rw [hsub] at htr; cases htr with
      | conflict hl hpc_s hvf _ =>
        rw [hpc1] at hpc_s; rcases Prod.mk.inj (Option.some.inj hpc_s) with ⟨hcl_eq, _⟩
        have hr2 := hunit_fl _ hl hcl_eq hvf; cases hr2
      | step hl hpc_s hv0 htr_next =>
        rw [hpc1] at hpc_s; rcases Prod.mk.inj (Option.some.inj hpc_s) with ⟨hcl_eq, hreq⟩
        obtain ⟨_, hvs, _, _⟩ := hunit_ok _ hl hcl_eq hv0
        rw [hdrop, hreq]
        exact unitUnsatTrace_congr_vals
          (by simp [hp.len_ok.core_ok.vals_len]; omega)
          (by rw [hlen'.core_ok.vals_len]; omega)
          (fun k hk => (hvs k hk).symm) htr_next
    · cases ht
  · exact fun _ => huns_in rfl
  · exact fun hc => by cases hc
  · intro hut; refine ⟨rfl, Or.inr ⟨rfl, ?_⟩⟩
    rcases (hp.uns_tr hut).2 with ⟨_, htr⟩ | ⟨ht, _⟩
    · rw [hsub] at htr; cases htr with
      | conflict _ hpc_s _ hrest =>
        rw [hpc1] at hpc_s; rcases Prod.mk.inj (Option.some.inj hpc_s) with ⟨_, hreq⟩
        rwa [hdrop, hreq]
      | step hl hpc_s hv0 _ =>
        rw [hpc1] at hpc_s; rcases Prod.mk.inj (Option.some.inj hpc_s) with ⟨hcl_eq, _⟩
        exact absurd (hunit_ok _ hl hcl_eq hv0).1 (by decide)
    · cases ht
  · exact fun hc => by cases hc
  · exact fun _ hc => by cases hc
  · intro hut; rcases (hp.uns_tr hut).2 with ⟨_, htr⟩ | ⟨ht, _⟩
    · rw [hsub] at htr; cases htr with
      | conflict hl hpc_s hvf _ =>
        rw [hpc1] at hpc_s; rcases Prod.mk.inj (Option.some.inj hpc_s) with ⟨hcl_eq, _⟩
        exact absurd (hunit_fl _ hl hcl_eq hvf) (by decide)
      | step hl hpc_s hv0 _ =>
        rw [hpc1] at hpc_s; rcases Prod.mk.inj (Option.some.inj hpc_s) with ⟨hcl_eq, _⟩
        exact absurd (hunit_ok _ hl hcl_eq hv0).1 (by decide)
    · cases ht

private abbrev FullParseBodyPost (c : FullCfg) (s : FullState) (cnf_ptr : BitVec 64)
    (cnfBytes : List UInt8) (i0 : Nat) (R : Mem 64 → Prop) (Q : Post [i64]) : Prop :=
  ∀ r st' m', st'.LengthsOk c → (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) →
    st'.core.fuel = s.core.fuel → st'.core.oom = 0#64 → st'.core.probing = 0#64 →
    (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) →
    (r = 1#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧
      FullSparseInv c (shiftDownCnf cnf) st' ∧ st'.core.cur_level = 0) →
    (UnitUnsatTrace c.mv (s.core.vals.take (2 * c.mv)) (cnfBytes.drop i0) c.nc → r = 20#64) →
    (bytes cnf_ptr cnfBytes ⋆ FullMem c st' ⋆ R) m' → Q (r, ()) m'

private theorem parse_body_oom_exit {c : FullCfg} {s st : FullState}
    {cnf_ptr : BitVec 64} {cnfBytes : List UInt8} {i0 i idx : Nat} {accCnf : CNF Nat}
    {unsat_v : Bool} {R : Mem 64 → Prop} {ml : Mem 64} {Q : Post [i64]}
    (hp : ParseBodyInv c s cnf_ptr cnfBytes i0 i idx accCnf unsat_v true st)
    (hml : (bytes cnf_ptr cnfBytes ⋆ FullMem c st ⋆ R) ml)
    (hQ : FullParseBodyPost c s cnf_ptr cnfBytes i0 R Q) : Q (0#64, ()) ml :=
  hQ 0#64 st ml hp.len_ok (Or.inl rfl) hp.fuel_eq hp.oom_eq hp.prb_eq
    (fun h => by cases h) (fun h => by cases h)
    (fun hut => by cases (hp.uns_tr hut).1) hml

private theorem parse_body_eof_ne {c : FullCfg} {s st : FullState}
    {cnf_ptr : BitVec 64} {cnfBytes : List UInt8} {i0 idx j : Nat} {accCnf : CNF Nat}
    {unsat_v oom_v : Bool} {R : Mem 64 → Prop} {m' : Mem 64} {Q : Post [i64]}
    (hp : ParseBodyInv c s cnf_ptr cnfBytes i0 c.nc idx accCnf unsat_v oom_v st)
    (_hidx : idx ≤ cnfBytes.length) (hj : j ≤ cnfBytes.length)
    (hsw : cnfBytes.drop j = skipWsComments (cnfBytes.drop idx))
    (hne : cnf_ptr + BitVec.ofNat 64 j ≠ cnf_ptr + BitVec.ofNat 64 cnfBytes.length)
    (hfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ FullMem c
      { st with core := { st.core with d_cur := cnf_ptr + BitVec.ofNat 64 j } } ⋆ R) m')
    (hQ : FullParseBodyPost c s cnf_ptr cnfBytes i0 R Q) : Q (0#64, ()) m' := by
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
      rcases (hp.uns_tr hut).2 with ⟨_, htr⟩ | ⟨_, _, hr⟩
      · rw [Nat.sub_self] at htr; cases htr
      · rw [Nat.sub_self] at hr
        simp only [parseClauses, hne_emp, Bool.false_eq_true, ↓reduceIte] at hr; cases hr) hm

private theorem parse_body_eof_done {c : FullCfg} {s st : FullState}
    {cnf_ptr : BitVec 64} {cnfBytes : List UInt8} {i0 idx j : Nat} {accCnf : CNF Nat}
    {unsat_v oom_v : Bool} {R : Mem 64 → Prop} {m' : Mem 64} {Q : Post [i64]}
    (hp : ParseBodyInv c s cnf_ptr cnfBytes i0 c.nc idx accCnf unsat_v oom_v st)
    (_hidx : idx ≤ cnfBytes.length) (hj : j ≤ cnfBytes.length)
    (hsw : cnfBytes.drop j = skipWsComments (cnfBytes.drop idx))
    (heq : cnf_ptr + BitVec.ofNat 64 j = cnf_ptr + BitVec.ofNat 64 cnfBytes.length)
    (hfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ FullMem c
      { st with core := { st.core with d_cur := cnf_ptr + BitVec.ofNat 64 j } } ⋆ R) m')
    (hQ : FullParseBodyPost c s cnf_ptr cnfBytes i0 R Q)
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
    have hinv_sf : FullSparseInv c (shiftDownCnf accCnf) sf :=
      (hinv_w.with_d (cnf_ptr + BitVec.ofNat 64 j) st.core.d_val).toSparse
    exact hQ 1#64 sf m' hlen_sf (Or.inr (Or.inl rfl)) hp.fuel_eq hp.oom_eq hp.prb_eq
      (fun h => by cases h) (fun _ => ⟨accCnf, hpd_some, hinv_sf, hp.cl0⟩)
      (fun hut => by rcases (hp.uns_tr hut).2 with ⟨_, htr⟩ | ⟨ht, _⟩
                     · rw [Nat.sub_self] at htr; cases htr
                     · cases ht) hm

/-! ## `full_parse_body` proof -/

theorem full_parse_body_wp (Γ : Env)
    (hSkip : ∀ a m Q X, fullSkipClSpec a m Q X → Γ "full_skip_cl" [i64, i64] [.bool] a m Q X)
    (hIngest : ∀ a m Q X, fullIngestClSpec a m Q X →
      Γ "full_ingest_cl" [i64, i64] [i64] a m Q X)
    (hSwc : ∀ a m Q X, kissatSkipWsCommentsSpec a m Q X →
      Γ "kissat_skip_ws_comments" [i64, i64] [i64] a m Q X) :
    ∀ a m Q X, fullParseBodySpec a m Q X → Func.wp Γ full_parse_body_body a m Q X := by
  rintro ⟨h, cend, ⟨⟩⟩ m Q X
    ⟨c, s, cnf_ptr, cnfBytes, i0, R, rfl, rfl, hfit, hi0, hhdr, hcv0, hdcur, hcl0, hte0, hpr0,
      hal0, hoom0, hprb0, hinc0, hvals0, hwvec0, hinv0, hm, hQ⟩
  have hnc_bd := c.hnc; have hmv_bd := c.hmv; unfold dimacsBound at hnc_bd hmv_bd
  have hpd_init : parseClauses c.mv c.nc CNF.empty (cnfBytes.drop i0) = parseDimacs cnfBytes := by
    simp [parseDimacs, hhdr]
  obtain ⟨hinv_w0, hent_0⟩ :=
    full_init_sparseW hinv0 hcv0 hal0 hte0 hcl0 hinc0 hvals0 hwvec0
  pi_steps
  refine wp_loop_group (fun r (unsat_v, oom_v, iv, ()) ml => ∃ i idx accCnf st,
      r = c.nc - i ∧ iv = BitVec.ofNat 64 i ∧
      ParseBodyInv c s cnf_ptr cnfBytes i0 i idx accCnf unsat_v oom_v st ∧
      (bytes cnf_ptr cnfBytes ⋆ FullMem c st ⋆ R) ml) ?_ ?_
  · rintro L r ⟨unsat_v, oom_v, iv, ⟨⟩⟩ ml ih ⟨i, idx, accCnf, st, rfl, rfl, hp, hml⟩
    have hile := hp.i_le; have hidx := hp.idx_le; have hcv_st := hp.cv_eq
    have hdcur_st := hp.d_cur_eq; have hlen_st := hp.len_ok; have hcl_st := hp.cl0
    have hfu_st := hp.fuel_eq; have hoom_st := hp.oom_eq; have hprb_st := hp.prb_eq
    pi_steps
    · have hilt : i < c.nc := by clear hm hml hQ; c0_bound
      have hunt : unsat_v = true := by assumption
      subst hunt; have hsub_eq : c.nc - i = (c.nc - (i + 1)) + 1 := by omega
      have hinc : BitVec.ofNat 64 i + 1 = BitVec.ofNat 64 (i + 1) := by
        apply BitVec.eq_of_toNat_eq; change (i % 2 ^ 64 + 1) % 2 ^ 64 = (i + 1) % 2 ^ 64; omega
      c0_call hSkip
      refine ⟨cnf_ptr, BitVec.ofNat 64 c.nc, st.core.d_val, c.mv, cnfBytes, idx,
        FullRest c st ⋆ R, rfl, hfit, by omega, hidx,
        by rw [← hdcur_st]; exact full_mem_to_dimacs hml, ?_⟩
      cases hpc1 : parseClause c.mv (cnfBytes.drop idx) with
      | none =>
        intro cur' val' m' hm'; pi_steps
        exact hQ 0#64 { st with core := { st.core with d_cur := cur', d_val := val' } } m'
          ⟨{ hlen_st.core_ok with vals_len := hlen_st.core_ok.vals_len }, hlen_st.scratch_ok⟩
          (Or.inl rfl) hfu_st hoom_st hprb_st (fun h => by cases h) (fun h => by cases h)
          (fun hut => by rcases (hp.uns_tr hut).2 with ⟨hf, _⟩ | ⟨_, _, hr⟩
                         · cases hf
                         · rw [hsub_eq, parseClauses, hpc1] at hr; cases hr)
          (full_dimacs_to_mem hm')
      | some p =>
        rcases p with ⟨cl, rest⟩; intro j m' hcl_pos _ hj hdrop hm'; pi_steps
        · exact ih (c.nc - (i + 1)) _ _ (by omega)
            ⟨i + 1, j, accCnf.add cl, _, rfl, hinc,
              parse_body_skip_step hp hilt hpc1 hcl_pos hj hdrop rfl, full_dimacs_to_mem hm'⟩
        · cases (by assumption : true = false)
    · have hoo : oom_v = true := by assumption
      subst hoo; exact parse_body_oom_exit hp hml hQ
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
        intro st' m' hlen' hfu' hoom' hprb' hm'; pi_steps
        · exact hQ 0#64 st' m' hlen' (Or.inl rfl) (hfu'.trans hfu_st) (hoom'.trans hoom_st)
            (hprb'.trans hprb_st) (fun h => by cases h) (fun h => by cases h)
            (fun hut => by rcases (hp.uns_tr hut).2 with ⟨_, htr⟩ | ⟨ht, _⟩
                           · rw [hsub_eq] at htr; cases htr with
                             | conflict _ hpc_s _ _ => rw [hpc1] at hpc_s; cases hpc_s
                             | step _ hpc_s _ _ => rw [hpc1] at hpc_s; cases hpc_s
                           · cases ht) hm'
        · exact absurd rfl (by assumption : ¬(0#64 : BitVec 64) = 0)
      | some p =>
        rcases p with ⟨cl, rest⟩
        intro r_in st' j m' hcl_pos _ hj hdrop hlen' hcv' hd' hcl' hfu' hoom' hprb' hr_dom
          hok_in huns_in hunit_ok hunit_fl hm'
        rcases hr_dom with rfl | rfl | rfl <;> pi_steps <;>
          first
          | (exact absurd rfl (by assumption : ¬(2#64 : BitVec 64) = 2))
          | (exact absurd rfl (by assumption : ¬(3#64 : BitVec 64) = 3))
          | exact ih (c.nc - (i + 1)) _ _ (by omega)
              ⟨i + 1, j, accCnf.add cl, st', rfl, hinc, by
                simpa using parse_body_ingest_step hp hilt hpc1 hcl_pos hj hdrop hlen' hcv'
                  hd' hcl' hfu' hoom' hprb' (by simp) hok_in huns_in hunit_ok hunit_fl, hm'⟩
    · have hoo : oom_v = true := by assumption
      subst hoo; exact parse_body_oom_exit hp hml hQ
    · have hieq : i = c.nc := by clear hml hQ; c0_bound
      subst hieq; c0_call hSwc
      refine ⟨cnf_ptr, cnfBytes, idx, FullMem c st ⋆ R, hdcur_st, rfl, hfit, hidx,
        sep_ac hml, fun j _ hj hsw => ?_⟩
      pi_steps
      · exact parse_body_eof_ne hp hidx hj hsw (by assumption) hfit (sep_ac hm) hQ
      · have hunt : unsat_v = true := by assumption
        simpa [hunt] using parse_body_eof_done hp hidx hj hsw (by assumption) hfit (sep_ac hm) hQ
          (Or.inl ⟨hunt, rfl⟩)
      · have huf : unsat_v = false := by assumption
        have hnf : oom_v = false := by assumption
        simpa [huf] using parse_body_eof_done hp hidx hj hsw (by assumption) hfit (sep_ac hm) hQ
          (Or.inr ⟨huf, hnf⟩)
  · intro L hL; pi_steps
    have hcmv0 : c.mv ≤ c.max_vars := hcv0 ▸ hinv0.1.lengths.core_ok.cur_vars_le
    exact hL c.nc _ m ⟨0, i0, CNF.empty, s, by simp, rfl,
      ⟨Nat.zero_le _, hi0, hcv0, hdcur, hinv0.1.lengths, hcl0, rfl, hoom0, hprb0,
        cnfVarsPos_empty, by simpa using hpd_init, (fun hc => by cases hc),
        fun _ _ => ⟨[], hinv_w0, hent_0⟩,
        fun hut => ⟨rfl, Or.inl ⟨rfl, by
          rw [Nat.sub_zero]
          refine unitUnsatTrace_congr_vals
            (by rw [List.length_take, hinv0.1.lengths.core_ok.vals_len]; omega)
            (by rw [hinv0.1.lengths.core_ok.vals_len]; omega) (fun k hk => ?_) hut
          rw [List.getElem?_take_of_lt hk]⟩⟩⟩, hm⟩

end ParseBodyProof

end LeanQbe.T.Examples.Kissat.Full
