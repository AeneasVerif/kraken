/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Sweep.LemmasCommon

/-!
# Top-Level Driver WP Proofs Part 1 (`Kissat.Proof.Sweep.WpDriver1`)

Flat `CanonicalEnv` `Func.wp` proof for `1/5` driver functions in `Src.Sweep`:
- `full_m6_sweep_classes_wp` (`fullM6SweepClassesSpec`)

Zero legacy `Full*` imports; zero expose attributes on theorems, lemmas, or sections.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Sweep

open Std Std.Sat Std.ExtHashMap Kraken.Bedrock2.Test
open LeanQbe.T LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src
open LeanQbe.T.Examples.Kissat.Src.Sweep
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Kitten
open LeanQbe.T.Examples.Kissat.Proof.Kitten.Spec
open LeanQbe.T.Examples.Kissat.Proof.Sweep.Spec

open FullArenaTactics K6MemATactics K6PtrTactics M6SweepTactics
open scoped FullArenaTactics M6SweepTactics

/-! ## 1. Assumption Memory, `K6Inv`/`K6TailEq`, & Partition Helpers -/

namespace M6ClsMem
@[scoped c0_store] theorem store_k6_assump0_ofnat {L : K6Layout} {kPtr : BitVec 64}
    {ks : K6State} {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32)
    (hm : (K6MemA L kPtr ks ⋆ R) m) :
    storeOk m i32 ((kPtr + BitVec.ofNat 64 (4 * L.oAssump)) + BitVec.ofNat 64 0 * 4) ∧
      (K6MemA L kPtr (ks.putArr .assump 0 v) ⋆ R)
        (storeMem m i32 ((kPtr + BitVec.ofNat 64 (4 * L.oAssump)) + BitVec.ofNat 64 0 * 4) v) := by
  simpa using store_k6_assump0 v hm
@[scoped c0_store] theorem store_k6_assump1_ofnat {L : K6Layout} {kPtr : BitVec 64}
    {ks : K6State} {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32)
    (hm : (K6MemA L kPtr ks ⋆ R) m) :
    storeOk m i32 ((kPtr + BitVec.ofNat 64 (4 * L.oAssump)) + BitVec.ofNat 64 1 * 4) ∧
      (K6MemA L kPtr (ks.putArr .assump 1 v) ⋆ R)
        (storeMem m i32 ((kPtr + BitVec.ofNat 64 (4 * L.oAssump)) + BitVec.ofNat 64 1 * 4) v) := by
  have hi : (1#32).toNat < szV L := by unfold szV; have := L.hmaxV; bv_omega
  simpa using store_k6_assump v (i := 1#32) hi hm
@[scoped c0_store] theorem store_k6_assump1_4 {L : K6Layout} {kPtr : BitVec 64}
    {ks : K6State} {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32)
    (hm : (K6MemA L kPtr ks ⋆ R) m) :
    storeOk m i32 ((kPtr + BitVec.ofNat 64 (4 * L.oAssump)) + 4) ∧
      (K6MemA L kPtr (ks.putArr .assump 1 v) ⋆ R)
        (storeMem m i32 ((kPtr + BitVec.ofNat 64 (4 * L.oAssump)) + 4) v) := by
  simpa using store_k6_assump1_ofnat v hm
@[scoped c0_store] theorem store_k6_assump0_dyn {L : K6Layout} {kPtr : BitVec 64} {ks : K6State}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32) (hm : (K6MemA L kPtr ks ⋆ R) m) :
    storeOk m i32 ((kPtr + BitVec.setWidth 64 ((32 : BitVec 32) + (9 : BitVec 32) * L.mv32) * 4) +
        BitVec.ofNat 64 0 * 4) ∧
      (K6MemA L kPtr (ks.putArr .assump 0 v) ⋆ R) (storeMem m i32
        ((kPtr + BitVec.setWidth 64 ((32 : BitVec 32) + (9 : BitVec 32) * L.mv32) * 4) +
          BitVec.ofNat 64 0 * 4) v) := by
  rw [k6_ptr_assump L kPtr]; exact store_k6_assump0_ofnat v hm
@[scoped c0_store] theorem store_k6_assump1_dyn {L : K6Layout} {kPtr : BitVec 64} {ks : K6State}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32) (hm : (K6MemA L kPtr ks ⋆ R) m) :
    storeOk m i32 ((kPtr + BitVec.setWidth 64 ((32 : BitVec 32) + (9 : BitVec 32) * L.mv32) * 4) +
        BitVec.ofNat 64 1 * 4) ∧
      (K6MemA L kPtr (ks.putArr .assump 1 v) ⋆ R) (storeMem m i32
        ((kPtr + BitVec.setWidth 64 ((32 : BitVec 32) + (9 : BitVec 32) * L.mv32) * 4) +
          BitVec.ofNat 64 1 * 4) v) := by
  rw [k6_ptr_assump L kPtr]; exact store_k6_assump1_ofnat v hm
@[scoped c0_load] theorem load_m6_full_kvals_dyn_bv {c : FullCfg} {L : K6Layout} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {idx : BitVec 32}
    (hL : L.scrLen = c.scratch_cap) (hscr : s.scratch.scratch_buf.length = c.scratch_cap)
    (hi : idx.toNat < 2 * L.maxV) (hm : (FullMem c s ⋆ R) m) :
    loadVal m i32
        ((L.kPtr c.pScratchBuf + BitVec.setWidth 64 (32#32 + 10#32 * L.mv32) * 4) +
          idx.setWidth 64 * 4) =
      some (s.scratch.scratch_buf[L.k6Base + L.oVals + idx.toNat]'(by
        have := L.hmaxV; have := L.hacap
        rw [hscr, ← hL]; unfold K6Layout.scrLen K6Layout.k6Fixed K6Layout.oVals; omega)) :=
  FullK6DynMem.load_m6_full_kvals_dyn hL hscr hi hm
end M6ClsMem

private theorem m6_scrCap_lt64 (c : FullCfg) : c.scratch_cap < 2 ^ 64 := by
  have := c.hscr; unfold dimacsBound at this; omega
private theorem m6_mv32_eq {c : FullCfg} {L : K6Layout} (hLmv : L.maxV = k6MaxV c.scratch_cap) :
    (BitVec.ofNat 64 (k6MaxV c.scratch_cap)).setWidth 32 = L.mv32 := by
  have hm := L.hmaxV; apply BitVec.eq_of_toNat_eq
  simp only [k6_mv32_toNat, BitVec.toNat_setWidth, BitVec.toNat_ofNat]; rw [← hLmv]; omega
private theorem m6_ptr_phtMerged (L : K6Layout) (pScr : BitVec 64) :
    pScr + BitVec.setWidth 64 ((1280 : BitVec 32) + L.mv32) * 4 =
      pScr + BitVec.ofNat 64 (4 * L.phtMerged) := by
  have := L.hmaxV; congr 1; apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_add, k6_mv32_toNat,
    BitVec.toNat_ofNat]
  rw [show (1280 : BitVec 32).toNat = 1280 from rfl, show (4 : BitVec 64).toNat = 4 from rfl]
  unfold K6Layout.phtMerged
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
private theorem bv32_sub1_of_pos {x : BitVec 32} (hx : 0 < x.toNat) :
    (x - 1#32).toNat = x.toNat - 1 := by bv_omega

private theorem m6_hwm_step {L : K6Layout} {gu : List (BitVec 32)} {nv : BitVec 32}
    {ks ks' : K6State}
    (hhw_le : gu[33]? = some 0xFFFFFFFF#32 ∨ nv.toNat ≤ (gu[33]?.getD 0#32).toNat)
    (hnv : ks.nv = nv) (hhwm : K6HwmClean L (gu[33]?.getD 0#32) ks)
    (ht : K6TailEq L ks ks') : K6HwmClean L (gu[33]?.getD 0#32) ks' :=
  k6HwmClean_of_tailEq (hnv ▸ hhw_le) rfl hhwm ht

private theorem k6Inv_set_assump2 {L : K6Layout} {P : (Nat → Bool) → Prop} {ks : K6State}
    {a0 a1 : BitVec 32} (ha0 : a0.toNat < 2 * ks.nv.toNat) (ha1 : a1.toNat < 2 * ks.nv.toNat)
    (hinv : K6Inv L P ks) :
    let ks' := ((ks.putHdr .nassump 2#32).putArr .assump 0 a0).putArr .assump 1 a1
    K6Inv L P ks' ∧ ks'.nv = ks.nv ∧ K6TailEq L ks ks' ∧
    k6AssumpLits ks' = [a0.toNat, a1.toNat] ∧ ks'.neq = ks.neq := by
  intro ks'
  have hmL := L.hmaxV; have hcl := hinv.clauses
  have ha1_lt : 1 < ks.assump.length := by rw [hinv.shapes.assump_len]; omega
  refine ⟨⟨((hinv.shapes.putHdr .nassump 2#32).putArr .assump 0 a0).putArr .assump 1 a1,
    { acap_eq := hcl.acap_eq, max_v_eq := hcl.max_v_eq, max_orig_eq := hcl.max_orig_eq,
      max_cl_eq := hcl.max_cl_eq, nv_le := hcl.nv_le, nc_le := hcl.nc_le, alen_le := hcl.alen_le,
      nassump_le := by dsimp only [ks', K6State.putArr, K6State.putHdr]; simp; omega
      nkl_le := hcl.nkl_le, nana_le := hcl.nana_le, cl_wf := hcl.cl_wf, cl_mono := hcl.cl_mono,
      incons_ok := hcl.incons_ok, flags_clean := hcl.flags_clean,
      assump_ok := fun i hi => by
        dsimp only [ks', K6State.putArr, K6State.putHdr] at hi ⊢
        have h2 : i < 2 := by simp at hi; exact hi
        rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
        · rw [List.getElem?_set_ne (by decide), List.getElem?_set_self (by omega), Option.getD_some]
          exact ha0
        · rw [List.getElem?_set_self (by simp; exact ha1_lt), Option.getD_some]; exact ha1 },
    hinv.watches, k6BaseAssignOk_cast hinv.assign rfl rfl rfl rfl rfl rfl rfl rfl rfl,
    hinv.reasons⟩, rfl, ⟨rfl, fun _ _ _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩, ?_, rfl⟩
  unfold k6AssumpLits; dsimp only [ks', K6State.putArr, K6State.putHdr]
  cases h : ks.assump with
  | nil => simp [h] at ha1_lt
  | cons x0 tl0 =>
    cases tl0 with | nil => simp [h] at ha1_lt | cons x1 tl1 => simp [List.set, List.take]

private theorem k6Inv_set_neq {L : K6Layout} {P : (Nat → Bool) → Prop} {ks : K6State}
    (v : BitVec 32) (hinv : K6Inv L P ks) : K6Inv L P (ks.putHdr .neq v) :=
  ⟨hinv.shapes.putHdr .neq v,
   k6ClausesOk_cast hinv.clauses,
   hinv.watches,
   k6BaseAssignOk_cast hinv.assign (by k6_field) (by k6_field) (by k6_field) (by k6_field)
     (by k6_field) (by k6_field) (by k6_field) (by k6_field) (by k6_field), hinv.reasons⟩
private theorem m6_partOk_drop_head {nv ncls : Nat} {scr heads : List (BitVec 32)}
    (hp : M6PartitionOk nv ncls scr heads) : M6PartitionOk nv (ncls - 1) scr heads :=
  ⟨Nat.le_trans (Nat.sub_le _ _) hp.1, hp.2.1, fun ci hci => hp.2.2 ci (by omega)⟩

private theorem m6_partOk_unlink {nv ncls : Nat} {scr heads : List (BitVec 32)}
    {a c : BitVec 32} (hnv_lt : nv ≤ 2 ^ 31) (ha : a.toNat < nv)
    (hc_eq : c = scr[k6PhtNext + a.toNat]?.getD 0xFFFFFFFF#32)
    (hc : c.toNat < nv) (hbd_a : k6PhtNext + a.toNat < scr.length)
    (hbd : k6PhtNext + c.toNat < scr.length)
    (hp : M6PartitionOk nv ncls scr heads) :
    let v := scr[k6PhtNext + c.toNat]'hbd
    let scr' := scr.set (k6PhtNext + a.toNat) v
    M6PartitionOk nv ncls scr' heads ∧ M6PartitionOk nv (ncls - 1) scr' heads := by
  intro v scr'
  have hc_lt_a : c.toNat < a.toNat := by
    have ha' := hp.2.1 a.toNat ha; rw [← hc_eq] at ha'
    rcases ha' with rfl | hlt
    · exfalso; exact absurd hc (by rw [show (0xFFFFFFFF#32).toNat = 4294967295 from rfl]; omega)
    · exact hlt
  have hv_ok : v = 0xFFFFFFFF#32 ∨ v.toNat < a.toNat := by
    have hc' := hp.2.1 c.toNat hc
    dsimp only [v]; rw [List.getElem?_eq_getElem hbd, Option.getD_some] at hc'
    exact hc'.elim Or.inl fun hlt => Or.inr (Nat.lt_trans hlt hc_lt_a)
  have hp' : M6PartitionOk nv ncls scr' heads := by
    refine ⟨hp.1, fun i hi => ?_, hp.2.2⟩
    by_cases hia : i = a.toNat
    · subst hia; dsimp only [scr']; rw [List.getElem?_set_self hbd_a, Option.getD_some]; exact hv_ok
    · dsimp only [scr']; rw [List.getElem?_set_ne (by omega)]; exact hp.2.1 i hi
  exact ⟨hp', m6_partOk_drop_head hp'⟩

private theorem m6_coneModelSet_unsat_bin {F_cur : List (List Nat)} {ws1 : List (BitVec 32)}
    {nv a0 a1 : Nat} (_ha0 : a0 < 2 * nv) (_ha1 : a1 < 2 * nv)
    (h : ∀ β, ConeModelSet F_cur ws1 nv β → ¬ (unitsCnf [a0, a1]).Sat β) :
    SemEntails (ConeModelSet F_cur ws1 nv) [a0 ^^^ 1, a1 ^^^ 1] ∧
    (cnfOfClauses F_cur).EntailsClause (cnfClause
      [m6ConeLift ws1 (a0 ^^^ 1), m6ConeLift ws1 (a1 ^^^ 1)]) := by
  have hsem : SemEntails (ConeModelSet F_cur ws1 nv) [a0 ^^^ 1, a1 ^^^ 1] := fun β hβ =>
    Classical.byContradiction fun hnot => by
      have h0 : (cnfClause [a0]).Sat β := Classical.byContradiction fun hn0 =>
        hnot ((clause_sat_cnfClause_iff β [a0 ^^^ 1, a1 ^^^ 1]).mpr ⟨a0 ^^^ 1,
          List.mem_cons_self .., (sat_cnfClause_singleton β (a0 ^^^ 1)).mp
            ((sat_cnfClause_litNeg_iff β a0).mpr hn0)⟩)
      have h1 : (cnfClause [a1]).Sat β := Classical.byContradiction fun hn1 =>
        hnot ((clause_sat_cnfClause_iff β [a0 ^^^ 1, a1 ^^^ 1]).mpr ⟨a1 ^^^ 1,
          List.mem_cons_of_mem _ (List.mem_cons_self ..),
          (sat_cnfClause_singleton β (a1 ^^^ 1)).mp ((sat_cnfClause_litNeg_iff β a1).mpr hn1)⟩)
      exact h β hβ ((sat_unitsCnf_iff β [a0, a1]).mpr fun l hl => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
        rcases hl with rfl | rfl <;> assumption)
  refine ⟨hsem, ?_⟩
  rw [CNF.entails_clause_def]; intro α hα
  have hsat := hsem (fun i => α (ws1[i]?.getD 0#32).toNat) ⟨α, hα, fun _ _ => rfl⟩
  obtain ⟨x, hx, hxs⟩ := (clause_sat_cnfClause_iff _ _).mp hsat
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · exact (clause_sat_cnfClause_iff _ _).mpr ⟨m6ConeLift ws1 (a0 ^^^ 1), List.mem_cons_self ..,
      (sat_cnfClause_singleton α _).mp ((coneLift_sat_iff (α := α) (cone_v := ws1)
        (l := a0 ^^^ 1)).mp ((sat_cnfClause_singleton _ _).mpr hxs))⟩
  · exact (clause_sat_cnfClause_iff _ _).mpr ⟨m6ConeLift ws1 (a1 ^^^ 1),
      List.mem_cons_of_mem _ (List.mem_cons_self ..),
      (sat_cnfClause_singleton α _).mp ((coneLift_sat_iff (α := α) (cone_v := ws1)
        (l := a1 ^^^ 1)).mp ((sat_cnfClause_singleton _ _).mpr hxs))⟩

private theorem m6_bin_lits_align {ws1 : List (BitVec 32)} {a c gv_a gv_c pol : BitVec 32}
    (ha : a.toNat < 2 ^ 31) (hc : c.toNat < 2 ^ 31)
    (hgva : gv_a.toNat < 2 ^ 31) (hgvc : gv_c.toNat < 2 ^ 31)
    (hwsa : (ws1[a.toNat]?.getD 0#32).toNat = gv_a.toNat)
    (hwsc : (ws1[c.toNat]?.getD 0#32).toNat = gv_c.toNat)
    (hpol : pol = 0#32 ∨ pol = 1#32) :
    let la := gv_a <<< (1 : Nat); let lc := (gv_c <<< (1 : Nat)) ||| pol
    let a0_1 := a <<< (1 : Nat); let a1_1 := (c <<< (1 : Nat)) ||| (1#32 ^^^ pol)
    let a0_2 := (a <<< (1 : Nat)) ||| 1#32; let a1_2 := (c <<< (1 : Nat)) ||| pol
    a0_1.toNat = 2 * a.toNat ∧ a1_1.toNat = 2 * c.toNat + (1#32 ^^^ pol).toNat ∧
    a0_2.toNat = 2 * a.toNat + 1 ∧ a1_2.toNat = 2 * c.toNat + pol.toNat ∧
    la.toNat = 2 * gv_a.toNat ∧ lc.toNat = 2 * gv_c.toNat + pol.toNat ∧
    ((a <<< (1 : Nat)) ^^^ 1#32).toNat = a0_1.toNat ^^^ 1 ∧
    ((c <<< (1 : Nat)) ||| pol).toNat = a1_1.toNat ^^^ 1 ∧
    (a <<< (1 : Nat)).toNat = a0_2.toNat ^^^ 1 ∧
    (((c <<< (1 : Nat)) ||| pol) ^^^ 1#32).toNat = a1_2.toNat ^^^ 1 ∧
    (la ^^^ 1#32).toNat = m6ConeLift ws1 (a0_1.toNat ^^^ 1) ∧
    lc.toNat = m6ConeLift ws1 (a1_1.toNat ^^^ 1) ∧
    la.toNat = m6ConeLift ws1 (a0_2.toNat ^^^ 1) ∧
    (lc ^^^ 1#32).toNat = m6ConeLift ws1 (a1_2.toNat ^^^ 1) := by
  intro la lc a0_1 a1_1 a0_2 a1_2
  have hp_lt : pol.toNat < 2 := by rcases hpol with rfl | rfl <;> decide
  have hxp_lt : (1#32 ^^^ pol).toNat < 2 := by rcases hpol with rfl | rfl <;> decide
  have ha01 : a0_1.toNat = 2 * a.toNat := m6_bv32_shl1_lt ha
  have ha11 : a1_1.toNat = 2 * c.toNat + (1#32 ^^^ pol).toNat :=
    m6_bv32_shl1_or_pol c (1#32 ^^^ pol) hc hxp_lt
  have ha02 : a0_2.toNat = 2 * a.toNat + 1 := m6_bv32_shl1_or_pol a 1#32 ha (by decide)
  have ha12 : a1_2.toNat = 2 * c.toNat + pol.toNat := m6_bv32_shl1_or_pol c pol hc hp_lt
  have hla : la.toNat = 2 * gv_a.toNat := m6_bv32_shl1_lt hgva
  have hlc : lc.toNat = 2 * gv_c.toNat + pol.toNat := m6_bv32_shl1_or_pol gv_c pol hgvc hp_lt
  refine ⟨ha01, ha11, ha02, ha12, hla, hlc, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [BitVec.toNat_xor, show (1#32).toNat = 1 from rfl]
  · rw [ha12, ha11]; rcases hpol with rfl | rfl
    · simpa [show (0#32).toNat = 0 from rfl, show (1#32 ^^^ 0#32).toNat = 1 from rfl] using
        (m6_nat_xor1_odd c.toNat).symm
    · simpa [show (1#32).toNat = 1 from rfl, show (1#32 ^^^ 1#32).toNat = 0 from rfl] using
        (m6_nat_xor1_even c.toNat).symm
  · rw [ha01, ha02]; exact (m6_nat_xor1_odd a.toNat).symm
  · rw [BitVec.toNat_xor, show (1#32).toNat = 1 from rfl]
  · rw [BitVec.toNat_xor, show (1#32).toNat = 1 from rfl, hla, ha01,
      m6_nat_xor1_even gv_a.toNat, m6_nat_xor1_even a.toNat]
    simpa [show (2 * gv_a.toNat + 1) % 2 = 1 by omega] using
      (coneLift_of_tmk_pair (cone_v := ws1) (idx := a.toNat) (v := gv_a.toNat)
        (l := 2 * gv_a.toNat + 1) hwsa (by omega)).symm
  · rw [hlc, ha11]; rcases hpol with rfl | rfl
    · rw [show (0#32).toNat = 0 from rfl, show (1#32 ^^^ 0#32).toNat = 1 from rfl,
        m6_nat_xor1_odd c.toNat]
      simpa [show (2 * gv_c.toNat) % 2 = 0 by omega] using
        (coneLift_of_tmk_pair (cone_v := ws1) (idx := c.toNat) (v := gv_c.toNat)
          (l := 2 * gv_c.toNat) hwsc (by omega)).symm
    · rw [show (1#32).toNat = 1 from rfl, show (1#32 ^^^ 1#32).toNat = 0 from rfl,
        show 2 * c.toNat + 0 = 2 * c.toNat by omega, m6_nat_xor1_even c.toNat]
      simpa [show (2 * gv_c.toNat + 1) % 2 = 1 by omega] using
        (coneLift_of_tmk_pair (cone_v := ws1) (idx := c.toNat) (v := gv_c.toNat)
          (l := 2 * gv_c.toNat + 1) hwsc (by omega)).symm
  · rw [hla, ha02, m6_nat_xor1_odd a.toNat]
    simpa [show (2 * gv_a.toNat) % 2 = 0 by omega] using
      (coneLift_of_tmk_pair (cone_v := ws1) (idx := a.toNat) (v := gv_a.toNat)
        (l := 2 * gv_a.toNat) hwsa (by omega)).symm
  · rw [BitVec.toNat_xor, show (1#32).toNat = 1 from rfl, hlc, ha12]
    rcases hpol with rfl | rfl
    · rw [show (0#32).toNat = 0 from rfl, show 2 * c.toNat + 0 = 2 * c.toNat by omega,
        show 2 * gv_c.toNat + 0 = 2 * gv_c.toNat by omega, m6_nat_xor1_even gv_c.toNat,
        m6_nat_xor1_even c.toNat]
      simpa [show (2 * gv_c.toNat + 1) % 2 = 1 by omega] using
        (coneLift_of_tmk_pair (cone_v := ws1) (idx := c.toNat) (v := gv_c.toNat)
          (l := 2 * gv_c.toNat + 1) hwsc (by omega)).symm
    · rw [show (1#32).toNat = 1 from rfl, m6_nat_xor1_odd gv_c.toNat, m6_nat_xor1_odd c.toNat]
      simpa [show (2 * gv_c.toNat) % 2 = 0 by omega] using
        (coneLift_of_tmk_pair (cone_v := ws1) (idx := c.toNat) (v := gv_c.toNat)
          (l := 2 * gv_c.toNat) hwsc (by omega)).symm

private structure M6ClassData (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s0 : FullState) (L : K6Layout) (nv ncls neq rbit : BitVec 32)
    (R : Mem 64 → Prop) (m : Mem 64) where
  rbit_le : rbit.toNat ≤ 64
  ncls_le : ncls.toNat ≤ c.max_vars
  neq_le : neq.toNat ≤ s0.core.cur_vars
  st : FullState
  inv : FullDenseInvW c F0 F_cur st
  cv : st.core.cur_vars = s0.core.cur_vars
  fuel : st.core.fuel.toNat ≤ s0.core.fuel.toNat
  repr : st.core.repr = s0.core.repr
  ws : st.scratch.work_stk1 = s0.scratch.work_stk1
  tmk : st.scratch.tarjan_mark = s0.scratch.tarjan_mark
  trh : st.scratch.tarjan_reach = s0.scratch.tarjan_reach
  gu : st.scratch.glue_used = s0.scratch.glue_used
  k6 : K6Inv L (ConeModelSet F_cur s0.scratch.work_stk1 nv.toNat)
    (k6StateOfScratch L st.scratch.scratch_buf)
  nv_eq : (k6StateOfScratch L st.scratch.scratch_buf).nv = nv
  neq_eq : (k6StateOfScratch L st.scratch.scratch_buf).neq = neq
  hwm : K6HwmClean L (s0.scratch.glue_used[33]?.getD 0#32)
    (k6StateOfScratch L st.scratch.scratch_buf)
  hw_le : s0.scratch.glue_used[33]? = some 0xFFFFFFFF#32 ∨
    nv.toNat ≤ (s0.scratch.glue_used[33]?.getD 0#32).toNat
  part : M6PartitionOk nv.toNat ncls.toNat st.scratch.scratch_buf st.scratch.shrink_stk
  eqb : M6EqBufOk F_cur st neq.toNat
  mem : (FullMem c st ⋆ R) m

private def clsRefineExpr {rs : List Ty} (h : Val i64) (nv nclsL neq rbit steps1 : Val i32)
    (jLoop : Cont [i32, i32, i32, i32]) : Expr Val Cont rs :=
  Expr.group (sig := [[i32]])
    (fun _ => Blocks.cons (fun (p_r : Tup Val [i32]) =>
      Expr.call "full_m6_refine_partition" (as := [i64, i32, i32]) (bs := [i32])
        (Arg.var h, Arg.var nv, Arg.var nclsL, ()) fun (p_n : Tup Val [i32]) =>
        Expr.jump jLoop (Arg.var p_r.fst, Arg.var p_n.fst, Arg.var neq, Arg.var steps1, ()))
      Blocks.nil)
    (fun Js =>
      Expr.let_ (Op.mk (OpCode.cmp CmpOp.ult i32) (Arg.var rbit, Arg.imm 64, ())) fun p_c =>
      Expr.jnz (Arg.var p_c.fst)
        (Expr.call "full_m6_sweep_refine_sig" (as := [i64, i32, i32]) (bs := [])
          (Arg.var h, Arg.var nv, Arg.var rbit, ()) fun _ =>
          Expr.let_ (Op.mk (OpCode.add i32) (Arg.var rbit, Arg.imm 1, ())) fun p_1 =>
            Expr.jump Js.fst (Arg.var p_1.fst, ()))
        (Expr.jump Js.fst (Arg.var rbit, ())))

private def clsUnlinkExpr {rs : List Ty} (pnPtr : Val i64) (a cNode nv nclsL : Val i32)
    (onDone : Val i32 → Expr Val Cont rs) : Expr Val Cont rs :=
  Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var a, ())) fun p0 =>
  Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p0.fst, Arg.imm 4, ())) fun p1 =>
  Expr.let_ (Op.mk (OpCode.add i64) (Arg.var pnPtr, Arg.var p1.fst, ())) fun p2 =>
  Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var cNode, ())) fun p3 =>
  Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p3.fst, Arg.imm 4, ())) fun p4 =>
  Expr.let_ (Op.mk (OpCode.add i64) (Arg.var pnPtr, Arg.var p4.fst, ())) fun p5 =>
  Expr.load i32 (Arg.var p5.fst) fun ld =>
  Expr.store (t := i32) (Arg.var ld) (Arg.var p2.fst)
    (Expr.group (sig := [[i32]])
      (fun _ => Blocks.cons (fun (pn : Tup Val [i32]) => onDone pn.fst) Blocks.nil)
      (fun Js =>
        Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var a, ())) fun q0 =>
        Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var q0.fst, Arg.imm 4, ())) fun q1 =>
        Expr.let_ (Op.mk (OpCode.add i64) (Arg.var pnPtr, Arg.var q1.fst, ())) fun q2 =>
        Expr.load i32 (Arg.var q2.fst) fun ld2 =>
        Expr.let_ (Op.mk (OpCode.cmp CmpOp.uge i32) (Arg.var ld2, Arg.var nv, ())) fun qc =>
        Expr.jnz (Arg.var qc.fst)
          (Expr.let_ (Op.mk (OpCode.sub i32) (Arg.var nclsL, Arg.imm 1, ())) fun qn =>
            Expr.jump Js.fst (Arg.var qn.fst, ()))
          (Expr.jump Js.fst (Arg.var nclsL, ()))))

private def clsAddLiveExpr (h kPtr : Val i64) (l0 l1 : Val i32) (cont : Expr Val Cont [i64]) :
    Expr Val Cont [i64] :=
  Expr.call "full_k512_add_live_m6" (as := [i64, i32, i32]) (bs := [])
    (Arg.var h, Arg.var l0, Arg.var l1, ()) fun _ =>
  Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.imm 6, ())) fun p0 =>
  Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p0.fst, Arg.imm 4, ())) fun p1 =>
  Expr.let_ (Op.mk (OpCode.add i64) (Arg.var kPtr, Arg.var p1.fst, ())) fun p2 =>
  Expr.load i32 (Arg.var p2.fst) fun ld =>
  Expr.let_ (Op.mk (OpCode.cmp CmpOp.ne i32) (Arg.var ld, Arg.imm 0, ())) fun pc =>
  Expr.jnz (Arg.var pc.fst)
    (Expr.let_ (Op.mk (OpCode.add i64) (Arg.var h, Arg.imm 1024, ())) fun ph =>
     Expr.store (t := i64) (Arg.imm 1) (Arg.var ph.fst) (Expr.ret (Arg.imm 20, ())))
    cont

private def clsEqPushExpr {rs : List Ty} (h kPtr eqbPtr : Val i64)
    (rbit nclsM neq steps1 gv_a gv_c pol : Val i32) (jLoop : Cont [i32, i32, i32, i32]) :
    Expr Val Cont rs :=
  Expr.group (sig := [[i32]])
    (fun _ => Blocks.cons (fun (p_neq : Tup Val [i32]) =>
      Expr.call "full_m6_sweep_rearm" (as := [i64, i32]) (bs := []) (Arg.var h, Arg.var gv_a, ())
        fun _ =>
      Expr.call "full_m6_sweep_rearm" (as := [i64, i32]) (bs := []) (Arg.var h, Arg.var gv_c, ())
        fun _ =>
      Expr.let_ (Op.mk (OpCode.add i64) (Arg.var h, Arg.imm 1080, ())) fun p0 =>
      Expr.load i64 (Arg.var p0.fst) fun ld =>
      Expr.let_ (Op.mk (OpCode.add i64) (Arg.var ld, Arg.imm 1, ())) fun p1 =>
      Expr.let_ (Op.mk (OpCode.add i64) (Arg.var h, Arg.imm 1080, ())) fun p2 =>
      Expr.store (t := i64) (Arg.var p1.fst) (Arg.var p2.fst)
        (Expr.jump jLoop (Arg.var rbit, Arg.var nclsM, Arg.var p_neq.fst, Arg.var steps1, ())))
      Blocks.nil)
    (fun Js =>
      Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var neq, ())) fun p0 =>
      Expr.let_ (Op.mk (OpCode.add i64) (Arg.var h, Arg.imm 776, ())) fun p1 =>
      Expr.load i64 (Arg.var p1.fst) fun ld =>
      Expr.let_ (Op.mk (OpCode.cmp CmpOp.ult i64) (Arg.var p0.fst, Arg.var ld, ())) fun p2 =>
      Expr.jnz (Arg.var p2.fst)
        (Expr.let_ (Op.mk (OpCode.shl i32) (Arg.var neq, Arg.imm 1, ())) fun q0 =>
         Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var q0.fst, ())) fun q1 =>
         Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var q1.fst, Arg.imm 4, ())) fun q2 =>
         Expr.let_ (Op.mk (OpCode.add i64) (Arg.var eqbPtr, Arg.var q2.fst, ())) fun q3 =>
         Expr.let_ (Op.mk (OpCode.shl i32) (Arg.var gv_a, Arg.imm 1, ())) fun q4 =>
         Expr.store (t := i32) (Arg.var q4.fst) (Arg.var q3.fst)
         (Expr.let_ (Op.mk (OpCode.shl i32) (Arg.var neq, Arg.imm 1, ())) fun q5 =>
          Expr.let_ (Op.mk (OpCode.add i32) (Arg.var q5.fst, Arg.imm 1, ())) fun q6 =>
          Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var q6.fst, ())) fun q7 =>
          Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var q7.fst, Arg.imm 4, ())) fun q8 =>
          Expr.let_ (Op.mk (OpCode.add i64) (Arg.var eqbPtr, Arg.var q8.fst, ())) fun q9 =>
          Expr.let_ (Op.mk (OpCode.shl i32) (Arg.var gv_c, Arg.imm 1, ())) fun q10 =>
          Expr.let_ (Op.mk (OpCode.or i32) (Arg.var q10.fst, Arg.var pol, ())) fun q11 =>
          Expr.store (t := i32) (Arg.var q11.fst) (Arg.var q9.fst)
          (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var neq, Arg.imm 1, ())) fun q12 =>
           Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.imm 24, ())) fun q13 =>
           Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var q13.fst, Arg.imm 4, ())) fun q14 =>
           Expr.let_ (Op.mk (OpCode.add i64) (Arg.var kPtr, Arg.var q14.fst, ())) fun q15 =>
           Expr.store (t := i32) (Arg.var q12.fst) (Arg.var q15.fst)
             (Expr.jump Js.fst (Arg.var q12.fst, ())))))
        (Expr.jump Js.fst (Arg.var neq, ())))

private def clsMergeBodyExpr (h kPtr flPtr : Val i64) (a cNode gv_c pol : Val i32)
    (eqExpr : Expr Val Cont [i64]) : Expr Val Cont [i64] :=
  Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var gv_c, ())) fun pf0 =>
  Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var pf0.fst, Arg.imm 4, ())) fun pf1 =>
  Expr.let_ (Op.mk (OpCode.add i64) (Arg.var flPtr, Arg.var pf1.fst, ())) fun pf2 =>
  Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var gv_c, ())) fun pf3 =>
  Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var pf3.fst, Arg.imm 4, ())) fun pf4 =>
  Expr.let_ (Op.mk (OpCode.add i64) (Arg.var flPtr, Arg.var pf4.fst, ())) fun pf5 =>
  Expr.load i32 (Arg.var pf5.fst) fun ld =>
  Expr.let_ (Op.mk (OpCode.not i32) (Arg.imm 1024, ())) fun pf6 =>
  Expr.let_ (Op.mk (OpCode.and i32) (Arg.var ld, Arg.var pf6.fst, ())) fun pf7 =>
  Expr.store (t := i32) (Arg.var pf7.fst) (Arg.var pf2.fst)
    (Expr.let_ (Op.mk (OpCode.shl i32) (Arg.var a, Arg.imm 1, ())) fun l0 =>
     Expr.let_ (Op.mk (OpCode.xor i32) (Arg.var l0.fst, Arg.imm 1, ())) fun l1 =>
     Expr.let_ (Op.mk (OpCode.shl i32) (Arg.var cNode, Arg.imm 1, ())) fun l2 =>
     Expr.let_ (Op.mk (OpCode.or i32) (Arg.var l2.fst, Arg.var pol, ())) fun l3 =>
     clsAddLiveExpr h kPtr l1.fst l3.fst
       (Expr.let_ (Op.mk (OpCode.shl i32) (Arg.var a, Arg.imm 1, ())) fun m0 =>
        Expr.let_ (Op.mk (OpCode.shl i32) (Arg.var cNode, Arg.imm 1, ())) fun m1 =>
        Expr.let_ (Op.mk (OpCode.or i32) (Arg.var m1.fst, Arg.var pol, ())) fun m2 =>
        Expr.let_ (Op.mk (OpCode.xor i32) (Arg.var m2.fst, Arg.imm 1, ())) fun m3 =>
        clsAddLiveExpr h kPtr m0.fst m3.fst eqExpr))

private theorem m6_class_refine_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    {L : K6Layout} {nv nclsL neq rbit steps1 : Val i32} {R : Mem 64 → Prop} {mFl : Mem 64}
    {h : Val i64} {jLoop : Cont [i32, i32, i32, i32]}
    (hRef : Γ.Has "full_m6_sweep_refine_sig" fullM6SweepRefineSigSpec)
    (hRefP : Γ.Has "full_m6_refine_partition" fullM6RefinePartitionSpec)
    (h_hdr : h = c.hdr) (hL_len : L.scrLen = c.scratch_cap)
    (hL_mv : L.maxV = k6MaxV c.scratch_cap) (hcap : k6MinScr ≤ c.scratch_cap)
    (hnv_L : nv.toNat ≤ L.maxV) (hnv_mx : nv.toNat ≤ c.max_vars)
    (hnv_2mx : nv.toNat ≤ 2 * c.max_vars)
    (hws_lt : ∀ i < nv.toNat, (s.scratch.work_stk1[i]?.getD 0#32).toNat < s.core.cur_vars)
    (hcongr : ∀ {scrA scrB : List (BitVec 32)},
      (∀ i < c.scratch_cap, L.phtMerged ≤ i → scrB[i]? = scrA[i]?) →
      scrA.length = c.scratch_cap → scrB.length = c.scratch_cap →
      k6StateOfScratch L scrB = k6StateOfScratch L scrA)
    (dFl : M6ClassData c F0 F_cur s L nv nclsL neq rbit R mFl)
    (hJump : ∀ (rbitR new_n : BitVec 32) mP,
      M6ClassData c F0 F_cur s L nv new_n neq rbitR R mP →
      wp Γ Q X (Expr.jump jLoop (Arg.var rbitR, Arg.var new_n, Arg.var neq, Arg.var steps1, ()))
        mP) :
    wp Γ Q X (clsRefineExpr h nv nclsL neq rbit steps1 jLoop) mFl := by
  subst h_hdr; unfold clsRefineExpr
  refine wp_join_group (ts := [i32])
    (fun (rbitR, ()) mR => ∃ _ : M6ClassData c F0 F_cur s L nv nclsL neq rbitR R mR, True)
    (fun _ (rbitR, ()) mR ⟨dR, _⟩ => by
      m6_call hRefP
      refine ⟨c, dR.st, L, R, rfl, dR.inv.1, hL_len, hL_mv, hnv_L, hnv_mx, dR.ncls_le,
        fun j hj => by rw [dR.ws, dR.cv]; exact hws_lt j hj, dR.part, dR.mem, ?_⟩
      intro new_n scrP sstkP wsoP mP _ _ hscrP hsstP hwsoP hpreP hnnP hpartP hmP
      have hofP := hcongr (fun i hi hdom => hpreP i hi (Or.inr hdom))
        dR.inv.1.scratch_ok.scratch_buf_len hscrP
      let sP : FullState :=
        { dR.st with scratch :=
          { dR.st.scratch with scratch_buf := scrP, shrink_stk := sstkP, wsort := wsoP } }
      have hinvP := m6_fullDenseInvW_with_cls_scratch dR.inv hscrP hsstP
        dR.inv.1.core_ok.min_clr_len_arr hwsoP
      m6_steps
      exact hJump rbitR new_n mP
        ⟨dR.rbit_le, hnnP, dR.neq_le, sP, hinvP, dR.cv, dR.fuel, dR.repr, dR.ws, dR.tmk, dR.trh,
         dR.gu, hofP ▸ dR.k6, hofP ▸ dR.nv_eq, hofP ▸ dR.neq_eq, hofP ▸ dR.hwm, dR.hw_le,
         hpartP, m6EqBufOk_mono dR.eqb rfl rfl, hmP⟩)
    (fun _ hJrb => by
      m6_split; rotate_left; · m6_steps; exact hJrb (rbit, ()) mFl ⟨dFl, trivial⟩
      have hrb_lt : rbit.toNat < 64 := hc
      have hrb1 : (rbit + 1#32).toNat = rbit.toNat + 1 := m6_bv32_add1 (by omega)
      m6_call hRef
      refine ⟨c, dFl.st, R, rfl, dFl.inv.1, hcap, by rw [← hL_mv]; exact hnv_L, hnv_2mx,
        fun j hj => by rw [dFl.ws, dFl.cv]; exact hws_lt j hj, dFl.mem,
        fun sigR mR hsigR hmR => ?_⟩
      let sR := { dFl.st with scratch := { dFl.st.scratch with sim_sig := sigR } }
      m6_steps
      exact hJrb (rbit + 1#32, ()) mR
        ⟨⟨by omega, dFl.ncls_le, dFl.neq_le, sR, m6_fullDenseInvW_with_sig dFl.inv hsigR,
          dFl.cv, dFl.fuel, dFl.repr, dFl.ws, dFl.tmk, dFl.trh, dFl.gu, dFl.k6, dFl.nv_eq,
          dFl.neq_eq, dFl.hwm, dFl.hw_le, dFl.part, m6EqBufOk_mono dFl.eqb rfl rfl, hmR⟩,
         trivial⟩)

private theorem m6_class_unlink_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    {L : K6Layout} {nv nclsL neq rbit a cNode steps1 : Val i32} {phtNextPtr : Val i64}
    {R : Mem 64 → Prop} {mU : Mem 64} {jLoop : Cont [i32, i32, i32, i32]}
    (hL_len : L.scrLen = c.scratch_cap) (hnv_L : nv.toNat ≤ L.maxV)
    (hncls_pos : 0 < nclsL.toNat) (ha_lt : a.toNat < nv.toNat) (hc_lt : cNode.toNat < nv.toNat)
    (dU : M6ClassData c F0 F_cur s L nv nclsL neq rbit R mU)
    (hc_eq : cNode = dU.st.scratch.scratch_buf[k6PhtNext + a.toNat]?.getD 0xFFFFFFFF#32)
    (hpht : phtNextPtr = c.pScratchBuf + BitVec.ofNat 64 (4 * k6PhtNext))
    (hJump : ∀ (ncls' : Val i32) m',
      M6ClassData c F0 F_cur s L nv ncls' neq rbit R m' →
      wp Γ Q X (Expr.jump jLoop (Arg.var rbit, Arg.var ncls', Arg.var neq, Arg.var steps1, ()))
        m') :
    wp Γ Q X
      (clsUnlinkExpr phtNextPtr a cNode nv nclsL fun pn =>
        Expr.jump jLoop (Arg.var rbit, Arg.var pn, Arg.var neq, Arg.var steps1, ())) mU := by
  subst hpht; unfold clsUnlinkExpr
  have hmL := L.hmaxV; have haL := L.hacap
  have hscrU_len := dU.inv.1.scratch_ok.scratch_buf_len
  have ha_mv : a.toNat < L.maxV := Nat.lt_of_lt_of_le ha_lt hnv_L
  have hc_mv : cNode.toNat < L.maxV := Nat.lt_of_lt_of_le hc_lt hnv_L
  have hpht_cap : k6PhtNext + L.maxV < c.scratch_cap := by
    unfold k6PhtNext; unfold K6Layout.scrLen K6Layout.k6Base K6Layout.k6Fixed at hL_len; omega
  have hpht_k6b : k6PhtNext + L.maxV < L.k6Base := by unfold k6PhtNext K6Layout.k6Base; omega
  have hc_bd : k6PhtNext + cNode.toNat < dU.st.scratch.scratch_buf.length := by
    rw [hscrU_len]; exact Nat.lt_trans (Nat.add_lt_add_left hc_mv _) hpht_cap
  have ha_bd : k6PhtNext + a.toNat < dU.st.scratch.scratch_buf.length := by
    rw [hscrU_len]; exact Nat.lt_trans (Nat.add_lt_add_left ha_mv _) hpht_cap
  let nxtU := dU.st.scratch.scratch_buf[k6PhtNext + cNode.toNat]'hc_bd
  let scrU := dU.st.scratch.scratch_buf.set (k6PhtNext + a.toNat) nxtU
  have hofU : k6StateOfScratch L scrU = k6StateOfScratch L dU.st.scratch.scratch_buf :=
    m6_k6Inv_of_prefix_set (Nat.lt_trans (Nat.add_lt_add_left ha_mv _) hpht_k6b)
  have hslU : scrU.length = c.scratch_cap := List.length_set.trans hscrU_len
  let sU : FullState := { dU.st with scratch := { dU.st.scratch with scratch_buf := scrU } }
  have hinvU := m6_fullDenseInvW_with_scratch dU.inv hslU (fuel' := dU.st.core.fuel)
  have heqbU := m6EqBufOk_mono dU.eqb rfl rfl
  have hunk := m6_partOk_unlink (Nat.le_trans hnv_L (by omega)) ha_lt hc_eq hc_lt ha_bd hc_bd
    dU.part
  have hmD := dU.mem
  change wp _ _ _ _ _
  open scoped M6PhtMem in
    (c0_hsteps_nogrp; try dsimp only [Prod.fst]
     m6_to_group; refine wp_unroll_group fun _ _ => ?_
     c0_hsteps_nogrp; try dsimp only [Prod.fst]
     m6_split
     · have hn1 : (nclsL - 1#32).toNat ≤ c.max_vars := by
         rw [bv32_sub1_of_pos hncls_pos]; exact Nat.le_trans (Nat.sub_le _ _) dU.ncls_le
       m6_steps
       exact hJump (nclsL - 1#32) _
         ⟨dU.rbit_le, hn1, dU.neq_le, sU, hinvU, dU.cv, dU.fuel, dU.repr, dU.ws, dU.tmk, dU.trh,
          dU.gu, hofU ▸ dU.k6, hofU ▸ dU.nv_eq, hofU ▸ dU.neq_eq, hofU ▸ dU.hwm, dU.hw_le,
          (by rw [bv32_sub1_of_pos hncls_pos]; exact hunk.2), heqbU,
          by dsimp only [sU, scrU, nxtU]; assumption⟩
     · m6_steps
       exact hJump nclsL _
         ⟨dU.rbit_le, dU.ncls_le, dU.neq_le, sU, hinvU, dU.cv, dU.fuel, dU.repr, dU.ws, dU.tmk,
          dU.trh, dU.gu, hofU ▸ dU.k6, hofU ▸ dU.nv_eq, hofU ▸ dU.neq_eq, hofU ▸ dU.hwm,
          dU.hw_le, hunk.1, heqbU, by dsimp only [sU, scrU, nxtU]; assumption⟩)

private theorem m6_class_solve2_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    {L : K6Layout} {nv nclsL neq rbit : Val i32} {R : Mem 64 → Prop} {mIn mKa : Mem 64}
    {h rem : Val i64} {a0 a1 : BitVec 32} {k : Tup Val [i64] → Expr Val Cont rs}
    (hSolve : Γ.Has "full_m6_sweep_solve" fullM6SweepSolveSpec)
    (h_hdr : h = c.hdr) (hL_len : L.scrLen = c.scratch_cap)
    (hL_mv : L.maxV = k6MaxV c.scratch_cap) (hpht_k6b : k6PhtNext + L.maxV < L.k6Base)
    (hnv_L : nv.toNat ≤ L.maxV)
    (dIn : M6ClassData c F0 F_cur s L nv nclsL neq rbit R mIn)
    (ha0 : a0.toNat < 2 * nv.toNat) (ha1 : a1.toNat < 2 * nv.toNat)
    (hm_ka : (K6MemA L (L.kPtr c.pScratchBuf)
      ((((k6StateOfScratch L dIn.st.scratch.scratch_buf).putHdr .nassump 2#32).putArr
        .assump 0 a0).putArr .assump 1 a1) ⋆ (FullK6Frame c L dIn.st ⋆ R)) mKa)
    (hk : ∀ (dOut : Val i64) mOut (dS : M6ClassData c F0 F_cur s L nv nclsL neq rbit R mOut),
      (∀ i < L.k6Base, dS.st.scratch.scratch_buf[i]? = dIn.st.scratch.scratch_buf[i]?) →
      (dOut = 20#64 → ∀ β, ConeModelSet F_cur s.scratch.work_stk1 nv.toNat β →
        ¬ (unitsCnf [a0.toNat, a1.toNat]).Sat β) →
      wp Γ Q X (k (dOut, ())) mOut) :
    wp Γ Q X
      (Expr.call "full_m6_sweep_solve" (as := [i64, i32, i64]) (bs := [i64])
        (Arg.var h, Arg.var nv, Arg.var rem, ()) k) mKa := by
  subst h_hdr
  have hscr_in := dIn.inv.1.scratch_ok.scratch_buf_len
  obtain ⟨hK1, hnv1_s, htl1, hass1, _⟩ := k6Inv_set_assump2
    (by rw [dIn.nv_eq]; exact ha0) (by rw [dIn.nv_eq]; exact ha1) dIn.k6
  obtain ⟨hscr1_len, hpre1, hof1, hm1⟩ :=
    m6_join_k6_ofSlab (s := dIn.st) hL_len hscr_in hK1.shapes hm_ka
  let ks1 := (((k6StateOfScratch L dIn.st.scratch.scratch_buf).putHdr .nassump 2#32).putArr
    .assump 0 a0).putArr .assump 1 a1
  let scr1 := dIn.st.scratch.scratch_buf.take L.k6Base ++ ks1.toSlab
  let s1 : FullState := { dIn.st with scratch := { dIn.st.scratch with scratch_buf := scr1 } }
  have hlen1 : s1.LengthsOk c :=
    ⟨dIn.inv.1.core_ok, { dIn.inv.1.scratch_ok with scratch_buf_len := hscr1_len }⟩
  have hnv1' : (k6StateOfScratch L scr1).nv = nv := by rw [hof1]; exact hnv1_s.trans dIn.nv_eq
  have hhwm1 : K6HwmClean L (s.scratch.glue_used[33]?.getD 0#32) (k6StateOfScratch L scr1) :=
    hof1.symm ▸ m6_hwm_step dIn.hw_le dIn.nv_eq dIn.hwm htl1
  have hass1' : k6AssumpLitsS L scr1 = [a0.toNat, a1.toNat] := by
    unfold k6AssumpLitsS; rw [hof1]; exact hass1
  m6_call hSolve
  refine ⟨c, s1, ConeModelSet F_cur s.scratch.work_stk1 nv.toNat, L, R, rfl, hlen1, hL_len, hL_mv,
    hof1 ▸ hK1, hnv1', hm1, fun dOut fuelS scrS mOut hlenS hfuelS hpreS hKS _
      hnvS htlS _ hassS hnqS _ hunsS hmOut => ?_⟩
  let sS : FullState :=
    { s1 with core := { s1.core with fuel := fuelS }
              scratch := { s1.scratch with scratch_buf := scrS } }
  have hscrS_len := hlenS.scratch_ok.scratch_buf_len
  have hinvS := m6_fullDenseInvW_with_scratch dIn.inv hscrS_len (fuel' := fuelS)
  have hnqS' : (k6StateOfScratch L scrS).neq = neq := by rw [hnqS, hof1]; exact dIn.neq_eq
  have hpre_comb : ∀ i < L.k6Base, scrS[i]? = dIn.st.scratch.scratch_buf[i]? := fun i hi => by
    rw [hpreS i hi, hpre1 i hi]
  have hpartS : M6PartitionOk nv.toNat nclsL.toNat scrS dIn.st.scratch.shrink_stk :=
    ⟨dIn.part.1, fun i hi => by
      have hiL : k6PhtNext + i < L.k6Base :=
        Nat.lt_trans (Nat.add_lt_add_left (Nat.lt_of_lt_of_le hi hnv_L) _) hpht_k6b
      rw [hpre_comb (k6PhtNext + i) hiL]; exact dIn.part.2.1 i hi, dIn.part.2.2⟩
  let dS : M6ClassData c F0 F_cur s L nv nclsL neq rbit R mOut :=
    ⟨dIn.rbit_le, dIn.ncls_le, dIn.neq_le, sS, hinvS, dIn.cv, Nat.le_trans hfuelS dIn.fuel,
     dIn.repr, dIn.ws, dIn.tmk, dIn.trh, dIn.gu, hKS, hnvS, hnqS',
     m6_hwm_step dIn.hw_le hnv1' hhwm1 htlS, dIn.hw_le, hpartS,
     m6EqBufOk_mono dIn.eqb rfl rfl, hmOut⟩
  refine hk dOut mOut dS hpre_comb fun hdOut β hβ => ?_
  have := hunsS hdOut β hβ; rwa [hassS, hass1'] at this

private theorem m6_partOk_merge_unlink {L : K6Layout} {scr heads : List (BitVec 32)}
    {nv nclsL : Nat} {a cNode : BitVec 32}
    (hL_len : L.scrLen = scr.length) (hnv_L : nv ≤ L.maxV) (hnv_lt : nv ≤ 2 ^ 31)
    (ha_lt : a.toNat < nv) (hc_lt : cNode.toNat < nv)
    (hc_eq : cNode = scr[k6PhtNext + a.toNat]?.getD 0xFFFFFFFF#32)
    (hpart : M6PartitionOk nv nclsL scr heads) :
    let scrM0 := scr.set (L.phtMerged + cNode.toNat) 1#32
    let nxtC2 := scrM0[k6PhtNext + cNode.toNat]'(by
      have hmL := L.hmaxV; have haL := L.hacap
      rw [List.length_set, ← hL_len]
      unfold k6PhtNext K6Layout.scrLen K6Layout.k6Base K6Layout.k6Fixed; omega)
    let scrM := scrM0.set (k6PhtNext + a.toNat) nxtC2
    scrM.length = L.scrLen ∧ k6StateOfScratch L scrM = k6StateOfScratch L scr ∧
    M6PartitionOk nv nclsL scrM heads ∧ M6PartitionOk nv (nclsL - 1) scrM heads := by
  intro scrM0 nxtC2 scrM
  have hmL := L.hmaxV; have haL := L.hacap; have hscr_L : scr.length = L.scrLen := hL_len.symm
  have hofM : k6StateOfScratch L scrM = k6StateOfScratch L scr := by
    dsimp only [scrM, scrM0]
    rw [m6_k6Inv_of_prefix_set (by unfold k6PhtNext K6Layout.k6Base; omega),
      m6_k6Inv_of_prefix_set (by unfold K6Layout.phtMerged K6Layout.k6Base; omega)]
  have hp_m0 : M6PartitionOk nv nclsL scrM0 heads :=
    ⟨hpart.1, fun i hi => by
      dsimp only [scrM0]
      rw [List.getElem?_set_ne (by unfold k6PhtNext K6Layout.phtMerged; omega)]
      exact hpart.2.1 i hi, hpart.2.2⟩
  have hc_eq_M0 : cNode = scrM0[k6PhtNext + a.toNat]?.getD 0xFFFFFFFF#32 := by
    dsimp only [scrM0]
    rw [List.getElem?_set_ne (by unfold k6PhtNext K6Layout.phtMerged; omega), hc_eq]
  have hunkM := m6_partOk_unlink hnv_lt ha_lt hc_eq_M0 hc_lt
    (by dsimp only [scrM0]; rw [List.length_set, hscr_L]
        unfold k6PhtNext K6Layout.scrLen K6Layout.k6Base K6Layout.k6Fixed; omega)
    (by dsimp only [scrM0]; rw [List.length_set, hscr_L]
        unfold k6PhtNext K6Layout.scrLen K6Layout.k6Base K6Layout.k6Fixed; omega) hp_m0
  exact ⟨by dsimp only [scrM, scrM0]; rw [List.length_set, List.length_set, hscr_L],
    hofM, hunkM.1, hunkM.2⟩

private abbrev M6ClsQ20 (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
    (L : K6Layout) (R : Mem 64 → Prop) (Q : Post [i64]) : Prop :=
  ∀ (s' : FullState) m',
    FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
    s'.core.fuel.toNat ≤ s.core.fuel.toNat → s'.core.repr = s.core.repr →
    s'.scratch.work_stk1 = s.scratch.work_stk1 →
    s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
    s'.scratch.tarjan_reach = s.scratch.tarjan_reach →
    s'.scratch.glue_used = s.scratch.glue_used →
    K6HwmClean L (s'.scratch.glue_used[33]?.getD 0#32)
      (k6StateOfScratch L s'.scratch.scratch_buf) →
    F0.Unsat → (FullMem c s' ⋆ R) m' → Q (20#64, ()) m'

private theorem m6_class_add_live_wp {Γ : Env} {Q : Post [i64]} {X : XPost}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    {L : K6Layout} {nv nclsL neq rbit l0 l1 : Val i32} {h kPtr : Val i64}
    {R : Mem 64 → Prop} {mIn : Mem 64} {cont : Expr Val Cont [i64]}
    (hLive : Γ.Has "full_k512_add_live_m6" step13K6AddLiveSpec)
    (hQ_20 : M6ClsQ20 c F0 F_cur s L R Q)
    (h_hdr : h = c.hdr) (hkptr : kPtr = L.kPtr c.pScratchBuf)
    (hL_len : L.scrLen = c.scratch_cap) (hL_mv : L.maxV = k6MaxV c.scratch_cap)
    (hpht_k6b : k6PhtNext + L.maxV < L.k6Base) (hnv_L : nv.toNat ≤ L.maxV)
    (dIn : M6ClassData c F0 F_cur s L nv nclsL neq rbit R mIn)
    (hl0 : l0.toNat < 2 * nv.toNat) (hl1 : l1.toNat < 2 * nv.toNat)
    (hsem : SemEntails (ConeModelSet F_cur s.scratch.work_stk1 nv.toNat) [l0.toNat, l1.toNat])
    (hcont : ∀ mL, M6ClassData c F0 F_cur s L nv nclsL neq rbit R mL → wp Γ Q X cont mL) :
    wp Γ Q X (clsAddLiveExpr h kPtr l0 l1 cont) mIn := by
  subst h_hdr hkptr; unfold clsAddLiveExpr
  have hmL := L.hmaxV; have haL := L.hacap
  m6_call hLive
  refine ⟨c, dIn.st, ConeModelSet F_cur s.scratch.work_stk1 nv.toNat, L, R, rfl, dIn.inv.1,
    hL_len, hL_mv, dIn.k6, by rw [dIn.nv_eq]; exact hl0,
    fun hff => by
      have := congrArg BitVec.toNat hff; dsimp only [Arg.val] at this
      rw [show (0xFFFFFFFF#32).toNat = 4294967295 from rfl] at this; omega,
    fun _ => ⟨by rw [dIn.nv_eq]; exact hl1, hsem⟩, dIn.mem,
    fun scrL mL hlenL hpreL hKL _ hnvL htlL _ _ hnqL hmL => ?_⟩
  let sL : FullState := { dIn.st with scratch := { dIn.st.scratch with scratch_buf := scrL } }
  have hscrL := hlenL.scratch_ok.scratch_buf_len
  have hinvL := m6_fullDenseInvW_with_scratch dIn.inv hscrL (fuel' := dIn.st.core.fuel)
  have hhwmL := m6_hwm_step dIn.hw_le dIn.nv_eq dIn.hwm htlL
  have hpartL : M6PartitionOk nv.toNat nclsL.toNat scrL dIn.st.scratch.shrink_stk :=
    ⟨dIn.part.1, fun i hi => by
      have hiL : k6PhtNext + i < L.k6Base :=
        Nat.lt_trans (Nat.add_lt_add_left (Nat.lt_of_lt_of_le hi hnv_L) _) hpht_k6b
      rw [hpreL (k6PhtNext + i) hiL]; exact dIn.part.2.1 i hi, dIn.part.2.2⟩
  let dOut : M6ClassData c F0 F_cur s L nv nclsL neq rbit R mL :=
    ⟨dIn.rbit_le, dIn.ncls_le, dIn.neq_le, sL, hinvL, dIn.cv, dIn.fuel, dIn.repr, dIn.ws, dIn.tmk,
     dIn.trh, dIn.gu, hKL, hnvL.trans dIn.nv_eq, hnqL.trans dIn.neq_eq, hhwmL, dIn.hw_le,
     hpartL, m6EqBufOk_mono dIn.eqb rfl rfl, hmL⟩
  change wp _ _ _ _ _; c0_hsteps_nogrp; try dsimp only [Prod.fst]
  open scoped FullK6DynMem in m6_split
  · have hk_inc : (k6StateOfScratch L scrL).incons ≠ 0#32 := by
      rw [m6_k6StateOfScratch_incons (by
        rw [hscrL, ← hL_len]; unfold K6Layout.scrLen K6Layout.k6Fixed; omega)]
      exact ‹_›
    have huns_cur := m6_coneModelSet_unsat_of_empty (hKL.clauses.incons_ok hk_inc)
    m6_steps
    exact hQ_20 _ _ (m6_fullDenseInvW_set_inconsistent hinvL huns_cur) dIn.cv dIn.fuel dIn.repr
      dIn.ws dIn.tmk dIn.trh dIn.gu (dIn.gu.symm ▸ hhwmL)
      (hinvL.2.1.ext_sound.2 huns_cur) (by assumption)
  · exact hcont mL dOut

private theorem m6_class_eq_push_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    {L : K6Layout} {nv nclsM neq rbit steps1 gv_a gv_c pol : Val i32}
    {h kPtr eqbPtr : Val i64} {R : Mem 64 → Prop} {mL2 : Mem 64}
    {jLoop : Cont [i32, i32, i32, i32]}
    (hRearm : Γ.Has "full_m6_sweep_rearm" fullM6SweepRearmSpec)
    (h_hdr : h = c.hdr) (hkptr : kPtr = L.kPtr c.pScratchBuf) (heqb_p : eqbPtr = c.pWorkStk2)
    (hL_len : L.scrLen = c.scratch_cap) (hpht_k6b : k6PhtNext + L.maxV < L.k6Base)
    (hnv_L : nv.toNat ≤ L.maxV) (hncM : nclsM.toNat ≤ c.max_vars)
    (hgva_lt : gv_a.toNat < s.core.cur_vars) (hgvc_lt : gv_c.toNat < s.core.cur_vars)
    (hpol : pol = 0#32 ∨ pol = 1#32)
    (hla_eq : (gv_a <<< (1 : Nat)).toNat = 2 * gv_a.toNat)
    (hlc_eq : ((gv_c <<< (1 : Nat)) ||| pol).toNat = 2 * gv_c.toNat + pol.toNat)
    (heq_f : LitEquiv (cnfOfClauses F_cur)
      (gv_a <<< (1 : Nat)).toNat ((gv_c <<< (1 : Nat)) ||| pol).toNat)
    (dL2 : M6ClassData c F0 F_cur s L nv nclsM neq rbit R mL2)
    (hJump : ∀ (neq' : Val i32) mF,
      M6ClassData c F0 F_cur s L nv nclsM neq' rbit R mF →
      wp Γ Q X (Expr.jump jLoop (Arg.var rbit, Arg.var nclsM, Arg.var neq', Arg.var steps1, ()))
        mF) :
    wp Γ Q X (clsEqPushExpr h kPtr eqbPtr rbit nclsM neq steps1 gv_a gv_c pol jLoop) mL2 := by
  subst h_hdr hkptr heqb_p; unfold clsEqPushExpr
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hlenL2 := dL2.inv.1
  have hcv_le : s.core.cur_vars ≤ c.max_vars := dL2.cv ▸ hlenL2.core_ok.cur_vars_le
  have hpol_lt : pol.toNat < 2 := by rcases hpol with rfl | rfl <;> decide
  have hmL2 := dL2.mem
  refine wp_join_group (ts := [i32])
    (fun (neq', ()) mEq => ∃ _ : M6ClassData c F0 F_cur s L nv nclsM neq' rbit R mEq, True)
    (fun _ (neq', ()) mEq ⟨dEq, _⟩ => by
      m6_call hRearm
      refine ⟨c, F0, F_cur, dEq.st, R, rfl, dEq.inv, dEq.mem, fun flR1 mR1 _ hinvR1 hmR1 => ?_⟩
      let sR1 := { dEq.st with core := { dEq.st.core with flags := flR1 } }
      m6_call hRearm
      refine ⟨c, F0, F_cur, sR1, R, rfl, hinvR1, hmR1, fun flR2 mR2 _ hinvR2 hmR2 => ?_⟩
      let sR2 := { sR1 with core := { sR1.core with flags := flR2 } }
      m6_steps
      let sFin := { sR2 with scratch := { sR2.scratch with
        sweep_cnt := sR2.scratch.sweep_cnt + 1#64 } }
      exact hJump neq' _
        ⟨dEq.rbit_le, dEq.ncls_le, dEq.neq_le, sFin,
         m6_fullDenseInvW_set_sweep_cnt hinvR2 (sR2.scratch.sweep_cnt + 1#64),
         dEq.cv, dEq.fuel, dEq.repr, dEq.ws, dEq.tmk, dEq.trh, dEq.gu, dEq.k6, dEq.nv_eq,
         dEq.neq_eq, dEq.hwm, dEq.hw_le, dEq.part, dEq.eqb, by assumption⟩)
    (fun _ hJeq => by
      m6_split; rotate_left; · m6_steps; exact hJeq (neq, ()) mL2 ⟨dL2, trivial⟩
      have hnq_lt : neq.toNat < s.core.cur_vars := by
        have h1 : neq.toNat < (dL2.st.core.cur_vars % 2 ^ 64) := hc; rw [dL2.cv] at h1; omega
      have hnq1 : (neq + 1#32).toNat = neq.toNat + 1 := m6_bv32_add1 (by omega)
      have h2nq0 : ((neq <<< (1 : Nat)).setWidth 64).toNat = 2 * neq.toNat := by
        rw [bv_c0_zext32_64]; exact m6_bv32_shl1_lt (by omega)
      have h2nq1 : (((neq <<< (1 : Nat)) + 1#32).setWidth 64).toNat = 2 * neq.toNat + 1 := by
        rw [bv_c0_zext32_64]; have hs := m6_bv32_shl1_lt (v := neq) (by omega); bv_omega
      have hws2_0 : ((neq <<< (1 : Nat)).setWidth 64).toNat < dL2.st.scratch.work_stk2.length := by
        rw [hlenL2.scratch_ok.work_stk2_len, h2nq0]; omega
      have hws2_1 : (((neq <<< (1 : Nat)) + 1#32).setWidth 64).toNat <
          (dL2.st.scratch.work_stk2.set ((neq <<< (1 : Nat)).setWidth 64).toNat
            (gv_a <<< (1 : Nat))).length := by
        rw [List.length_set, hlenL2.scratch_ok.work_stk2_len, h2nq1]; omega
      have hK_eq_fin := k6Inv_set_neq (neq + 1#32) dL2.k6
      have hscrL2_len := hlenL2.scratch_ok.scratch_buf_len
      let la := gv_a <<< (1 : Nat); let lc := (gv_c <<< (1 : Nat)) ||| pol
      let ws2' := (dL2.st.scratch.work_stk2.set (2 * neq.toNat) la).set (2 * neq.toNat + 1) lc
      have hws2'_len : ws2'.length = 2 * c.max_vars := by
        dsimp only [ws2']; rw [List.length_set, List.length_set, hlenL2.scratch_ok.work_stk2_len]
      let sEq0 : FullState := { dL2.st with scratch := { dL2.st.scratch with work_stk2 := ws2' } }
      have heqbEq0 : M6EqBufOk F_cur sEq0 (neq + 1#32).toNat := by
        rw [hnq1]
        exact m6_eqBufOk_push (m6EqBufOk_mono dL2.eqb rfl rfl) (dL2.cv ▸ hnq_lt)
          (dL2.cv ▸ by rw [hla_eq]; omega) (dL2.cv ▸ by rw [hlc_eq]; omega) heq_f
          (by rw [hlenL2.scratch_ok.work_stk2_len]; omega)
      change wp _ _ _ _ _; c0_hsteps
      have hmEq0 : (FullMem c sEq0 ⋆ R) m := by
        have hs_eq : ({ dL2.st with scratch := { dL2.st.scratch with work_stk2 :=
            ((dL2.st.scratch.work_stk2.set ((neq <<< (1 : Nat)).setWidth 64).toNat la) |>.set
              (((neq <<< (1 : Nat)) + 1#32).setWidth 64).toNat lc) } } : FullState) = sEq0 := by
          simp only [sEq0, ws2', h2nq0, h2nq1]
        rw [← hs_eq]; exact hm
      obtain ⟨RfrE, hRfrE⟩ : ∃ RfrE : Mem 64 → Prop, RfrE = (FullK6Frame c L sEq0 ⋆ R) := ⟨_, rfl⟩
      have hm_kaE : (K6MemA L (L.kPtr c.pScratchBuf)
          (k6StateOfScratch L dL2.st.scratch.scratch_buf) ⋆ RfrE) m := by
        rw [fullMem_eq_k6Frame (s := sEq0) (hscrL2_len.trans hL_len.symm)] at hmEq0
        rw [hRfrE]; exact k6Mem_to_amem dL2.k6.shapes (sep_ac hmEq0)
      change wp _ _ _ _ _
      open scoped K6MemATactics K6PtrTactics in c0_hsteps!
      rw [hRfrE] at hm
      let ksEqFin := (k6StateOfScratch L dL2.st.scratch.scratch_buf).putHdr .neq (neq + 1#32)
      let scrEqFin := dL2.st.scratch.scratch_buf.take L.k6Base ++ ksEqFin.toSlab
      let sEqFin : FullState :=
        { sEq0 with scratch := { sEq0.scratch with scratch_buf := scrEqFin } }
      obtain ⟨hscrEqFin_len, hpreEqFin, hofEqFin, hmEqFin⟩ :=
        m6_join_k6_ofSlab (s := sEq0) hL_len hscrL2_len hK_eq_fin.shapes hm
      have hpartEqFin : M6PartitionOk nv.toNat nclsM.toNat scrEqFin sEq0.scratch.shrink_stk :=
        ⟨dL2.part.1, fun i hi => by
          have hiL : k6PhtNext + i < L.k6Base :=
            Nat.lt_trans (Nat.add_lt_add_left (Nat.lt_of_lt_of_le hi hnv_L) _) hpht_k6b
          rw [hpreEqFin (k6PhtNext + i) hiL]; exact dL2.part.2.1 i hi, dL2.part.2.2⟩
      try dsimp only [Prod.fst]
      exact hJeq (neq + 1#32, ()) _
        ⟨⟨dL2.rbit_le, hncM, by omega, sEqFin,
          m6_fullDenseInvW_with_scratch (m6_fullDenseInvW_with_ws2 dL2.inv hws2'_len)
            hscrEqFin_len (fuel' := sEq0.core.fuel),
          dL2.cv, dL2.fuel, dL2.repr, dL2.ws, dL2.tmk, dL2.trh, dL2.gu, hofEqFin ▸ hK_eq_fin,
          by rw [hofEqFin]; exact dL2.nv_eq, by rw [hofEqFin]; rfl,
          hofEqFin.symm ▸ m6_hwm_step dL2.hw_le dL2.nv_eq dL2.hwm
            (k6TailEq_of_putHdr_ne_nv (by decide) _),
          dL2.hw_le, hpartEqFin, heqbEq0, hmEqFin⟩, trivial⟩)

private theorem m6_class_flip2_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    {L : K6Layout} {nv nclsL neq rbit fa fc : Val i32} {h : Val i64}
    {R : Mem 64 → Prop} {mIn : Mem 64} {jFl : Cont []} {cont : Expr Val Cont rs}
    (hFlip : Γ.Has "full_k6_flip" step13K6FlipSpec)
    (h_hdr : h = c.hdr) (hL_len : L.scrLen = c.scratch_cap)
    (hL_mv : L.maxV = k6MaxV c.scratch_cap) (hpht_k6b : k6PhtNext + L.maxV < L.k6Base)
    (hnv_L : nv.toNat ≤ L.maxV) (hfa_lt : fa.toNat < 2 * nv.toNat)
    (hfc_lt : fc.toNat < 2 * nv.toNat)
    (dIn : M6ClassData c F0 F_cur s L nv nclsL neq rbit R mIn)
    (hJumpFl : ∀ mFl, M6ClassData c F0 F_cur s L nv nclsL neq rbit R mFl →
      wp Γ Q X (Expr.jump jFl ()) mFl)
    (hCont : ∀ mFc (dFc : M6ClassData c F0 F_cur s L nv nclsL neq rbit R mFc),
      (∀ i < L.k6Base, dFc.st.scratch.scratch_buf[i]? = dIn.st.scratch.scratch_buf[i]?) →
      wp Γ Q X cont mFc) :
    wp Γ Q X
      (Expr.call "full_k6_flip" (as := [i64, i32]) (bs := [.bool]) (Arg.var h, Arg.var fa, ())
        fun p0 => Expr.jnz (Arg.var p0.fst) (Expr.jump jFl ())
          (Expr.call "full_k6_flip" (as := [i64, i32]) (bs := [.bool])
            (Arg.var h, Arg.var fc, ()) fun p1 => Expr.jnz (Arg.var p1.fst)
              (Expr.jump jFl ()) cont)) mIn := by
  subst h_hdr
  let P := ConeModelSet F_cur s.scratch.work_stk1 nv.toNat
  have h_idx_k6b : ∀ x < nv.toNat, k6PhtNext + x < L.k6Base := fun x hx =>
    Nat.lt_trans (Nat.add_lt_add_left (Nat.lt_of_lt_of_le hx hnv_L) _) hpht_k6b
  m6_call hFlip
  refine ⟨c, dIn.st, P, L, R, rfl, dIn.inv.1, hL_len, hL_mv, dIn.k6,
    by rw [dIn.nv_eq]; exact hfa_lt, dIn.mem,
    fun okFa scrFa mFa hlenFa hpreFa hKFa hnvFa htlFa _ _ hnqFa hmFa => ?_⟩
  let dFa : M6ClassData c F0 F_cur s L nv nclsL neq rbit R mFa :=
    ⟨dIn.rbit_le, dIn.ncls_le, dIn.neq_le,
     { dIn.st with scratch := { dIn.st.scratch with scratch_buf := scrFa } },
     m6_fullDenseInvW_with_scratch dIn.inv hlenFa.scratch_ok.scratch_buf_len
       (fuel' := dIn.st.core.fuel),
     dIn.cv, dIn.fuel, dIn.repr, dIn.ws, dIn.tmk, dIn.trh, dIn.gu, hKFa,
     hnvFa.trans dIn.nv_eq, hnqFa.trans dIn.neq_eq, m6_hwm_step dIn.hw_le dIn.nv_eq dIn.hwm htlFa,
     dIn.hw_le, ⟨dIn.part.1, fun i hi => by
       rw [hpreFa (k6PhtNext + i) (h_idx_k6b i hi)]; exact dIn.part.2.1 i hi, dIn.part.2.2⟩,
     m6EqBufOk_mono dIn.eqb rfl rfl, hmFa⟩
  m6_split; · m6_steps; exact hJumpFl mFa dFa
  m6_call hFlip
  refine ⟨c, dFa.st, P, L, R, rfl, dFa.inv.1, hL_len, hL_mv, dFa.k6,
    by rw [dFa.nv_eq]; exact hfc_lt, dFa.mem,
    fun okFc scrFc mFc hlenFc hpreFc hKFc hnvFc htlFc _ _ hnqFc hmFc => ?_⟩
  let dFc : M6ClassData c F0 F_cur s L nv nclsL neq rbit R mFc :=
    ⟨dFa.rbit_le, dFa.ncls_le, dFa.neq_le,
     { dFa.st with scratch := { dFa.st.scratch with scratch_buf := scrFc } },
     m6_fullDenseInvW_with_scratch dFa.inv hlenFc.scratch_ok.scratch_buf_len
       (fuel' := dFa.st.core.fuel),
     dFa.cv, dFa.fuel, dFa.repr, dFa.ws, dFa.tmk, dFa.trh, dFa.gu, hKFc,
     hnvFc.trans dFa.nv_eq, hnqFc.trans dFa.neq_eq, m6_hwm_step dFa.hw_le dFa.nv_eq dFa.hwm htlFc,
     dFa.hw_le, ⟨dFa.part.1, fun i hi => by
       rw [hpreFc (k6PhtNext + i) (h_idx_k6b i hi)]; exact dFa.part.2.1 i hi, dFa.part.2.2⟩,
     m6EqBufOk_mono dFa.eqb rfl rfl, hmFc⟩
  m6_split; · m6_steps; exact hJumpFl mFc dFc
  exact hCont mFc dFc fun i hi => by rw [hpreFc i hi, hpreFa i hi]

private theorem m6_class_merge_body_wp {Γ : Env} {Q : Post [i64]} {X : XPost}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    {L : K6Layout} {nv nclsM neq rbit a cNode gv_c pol : Val i32}
    {h kPtr flPtr : Val i64} {R : Mem 64 → Prop} {mM : Mem 64} {eqExpr : Expr Val Cont [i64]}
    (hLive : Γ.Has "full_k512_add_live_m6" step13K6AddLiveSpec)
    (hQ_20 : M6ClsQ20 c F0 F_cur s L R Q)
    (h_hdr : h = c.hdr) (hkptr : kPtr = L.kPtr c.pScratchBuf) (hflp : flPtr = c.pFlags)
    (hL_len : L.scrLen = c.scratch_cap) (hL_mv : L.maxV = k6MaxV c.scratch_cap)
    (hpht_k6b : k6PhtNext + L.maxV < L.k6Base) (hnv_L : nv.toNat ≤ L.maxV)
    (hgvc_lt : gv_c.toNat < s.core.cur_vars)
    (ha_lt : a.toNat < nv.toNat) (hc_lt : cNode.toNat < nv.toNat)
    (hpol : pol = 0#32 ∨ pol = 1#32)
    (ha01 : (a <<< (1 : Nat)).toNat = 2 * a.toNat)
    (ha12 : ((cNode <<< (1 : Nat)) ||| pol).toNat = 2 * cNode.toNat + pol.toNat)
    (hll1_0 : ((a <<< (1 : Nat)) ^^^ 1#32).toNat = (a <<< (1 : Nat)).toNat ^^^ 1)
    (hll2_1 : (((cNode <<< (1 : Nat)) ||| pol) ^^^ 1#32).toNat =
      ((cNode <<< (1 : Nat)) ||| pol).toNat ^^^ 1)
    (hsem1 : SemEntails (ConeModelSet F_cur s.scratch.work_stk1 nv.toNat)
      [((a <<< (1 : Nat)) ^^^ 1#32).toNat, ((cNode <<< (1 : Nat)) ||| pol).toNat])
    (hsem2 : SemEntails (ConeModelSet F_cur s.scratch.work_stk1 nv.toNat)
      [(a <<< (1 : Nat)).toNat, (((cNode <<< (1 : Nat)) ||| pol) ^^^ 1#32).toNat])
    (dM : M6ClassData c F0 F_cur s L nv nclsM neq rbit R mM)
    (hEq : ∀ mL2, M6ClassData c F0 F_cur s L nv nclsM neq rbit R mL2 → wp Γ Q X eqExpr mL2) :
    wp Γ Q X (clsMergeBodyExpr h kPtr flPtr a cNode gv_c pol eqExpr) mM := by
  subst h_hdr hkptr hflp; unfold clsMergeBodyExpr
  have hpol_lt : pol.toNat < 2 := by rcases hpol with rfl | rfl <;> decide
  have hgvc_fl : (gv_c.setWidth 64).toNat < dM.st.core.flags.length := by
    rw [dM.inv.1.core_ok.flags_len, bv_c0_zext32_64]
    have := dM.inv.1.core_ok.cur_vars_le; rw [dM.cv] at this; omega
  let flC := dM.st.core.flags.set (gv_c.setWidth 64).toNat
    ((dM.st.core.flags[(gv_c.setWidth 64).toNat]'hgvc_fl) &&& ~~~1024#32)
  let sC : FullState := { dM.st with core := { dM.st.core with flags := flC } }
  have hinvC := m6_fullDenseInvW_with_flags dM.inv (flags' := flC)
    (List.length_set.trans dM.inv.1.core_ok.flags_len)
  have hmM := dM.mem
  m6_steps
  let dC : M6ClassData c F0 F_cur s L nv nclsM neq rbit R _ :=
    ⟨dM.rbit_le, dM.ncls_le, dM.neq_le, sC, hinvC, dM.cv, dM.fuel, dM.repr, dM.ws, dM.tmk, dM.trh,
     dM.gu, dM.k6, dM.nv_eq, dM.neq_eq, dM.hwm, dM.hw_le, dM.part,
     m6EqBufOk_mono dM.eqb rfl rfl, by dsimp only [sC, flC]; assumption⟩
  refine m6_class_add_live_wp hLive hQ_20 rfl rfl hL_len hL_mv hpht_k6b hnv_L dC
    (by change ((a <<< (1 : Nat)) ^^^ 1#32).toNat < 2 * nv.toNat
        rw [hll1_0, ha01, m6_nat_xor1_cases]; split <;> omega)
    (by change ((cNode <<< (1 : Nat)) ||| pol).toNat < 2 * nv.toNat; rw [ha12]; omega) hsem1
    fun mL1 dL1 => ?_
  exact m6_class_add_live_wp hLive hQ_20 rfl rfl hL_len hL_mv hpht_k6b hnv_L dL1
    (by change (a <<< (1 : Nat)).toNat < 2 * nv.toNat; rw [ha01]; omega)
    (by change (((cNode <<< (1 : Nat)) ||| pol) ^^^ 1#32).toNat < 2 * nv.toNat
        rw [hll2_1, ha12, m6_nat_xor1_cases]; split <;> omega) hsem2 hEq

private theorem m6_class_d2_wp {Γ : Env} {Q : Post [i64]} {X : XPost}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    {L : K6Layout} {nv nclsL neq rbit steps1 a cNode gv_a gv_c pol : Val i32}
    {h kPtr assPtr flPtr pmPtr pnPtr eqbPtr tick_lim : Val i64}
    {R : Mem 64 → Prop} {mS1 : Mem 64} {jLoop : Cont [i32, i32, i32, i32]}
    (hRef : Γ.Has "full_m6_sweep_refine_sig" fullM6SweepRefineSigSpec)
    (hRefP : Γ.Has "full_m6_refine_partition" fullM6RefinePartitionSpec)
    (hSolve : Γ.Has "full_m6_sweep_solve" fullM6SweepSolveSpec)
    (hLive : Γ.Has "full_k512_add_live_m6" step13K6AddLiveSpec)
    (hRearm : Γ.Has "full_m6_sweep_rearm" fullM6SweepRearmSpec)
    (hQ_20 : M6ClsQ20 c F0 F_cur s L R Q)
    (h_hdr : h = c.hdr) (hkptr : kPtr = L.kPtr c.pScratchBuf)
    (hassp : assPtr = L.kPtr c.pScratchBuf + BitVec.ofNat 64 (4 * L.oAssump))
    (hflp : flPtr = c.pFlags)
    (hpmp : pmPtr = c.pScratchBuf + BitVec.ofNat 64 (4 * L.phtMerged))
    (hpnp : pnPtr = c.pScratchBuf + BitVec.ofNat 64 (4 * k6PhtNext))
    (heqb_p : eqbPtr = c.pWorkStk2)
    (hL_len : L.scrLen = c.scratch_cap) (hL_mv : L.maxV = k6MaxV c.scratch_cap)
    (hcap : k6MinScr ≤ c.scratch_cap)
    (hpht_k6b : k6PhtNext + L.maxV < L.k6Base) (hnv_L : nv.toNat ≤ L.maxV)
    (hnv_mx : nv.toNat ≤ c.max_vars) (hnv_2mx : nv.toNat ≤ 2 * c.max_vars)
    (hws_lt : ∀ i < nv.toNat, (s.scratch.work_stk1[i]?.getD 0#32).toNat < s.core.cur_vars)
    (hcongr : ∀ {scrA scrB : List (BitVec 32)},
      (∀ i < c.scratch_cap, L.phtMerged ≤ i → scrB[i]? = scrA[i]?) →
      scrA.length = c.scratch_cap → scrB.length = c.scratch_cap →
      k6StateOfScratch L scrB = k6StateOfScratch L scrA)
    (hncls_pos : 0 < nclsL.toNat) (ha_lt : a.toNat < nv.toNat) (hc_lt : cNode.toNat < nv.toNat)
    (hgva_lt : gv_a.toNat < s.core.cur_vars) (hgvc_lt : gv_c.toNat < s.core.cur_vars)
    (hpol : pol = 0#32 ∨ pol = 1#32)
    (ha01 : (a <<< (1 : Nat)).toNat = 2 * a.toNat)
    (ha02 : ((a <<< (1 : Nat)) ||| 1#32).toNat = 2 * a.toNat + 1)
    (ha12 : ((cNode <<< (1 : Nat)) ||| pol).toNat = 2 * cNode.toNat + pol.toNat)
    (hla_eq : (gv_a <<< (1 : Nat)).toNat = 2 * gv_a.toNat)
    (hlc_eq : ((gv_c <<< (1 : Nat)) ||| pol).toNat = 2 * gv_c.toNat + pol.toNat)
    (hll1_0 : ((a <<< (1 : Nat)) ^^^ 1#32).toNat = (a <<< (1 : Nat)).toNat ^^^ 1)
    (hll1_1 : ((cNode <<< (1 : Nat)) ||| pol).toNat =
      ((cNode <<< (1 : Nat)) ||| (1#32 ^^^ pol)).toNat ^^^ 1)
    (hll2_0 : (a <<< (1 : Nat)).toNat = ((a <<< (1 : Nat)) ||| 1#32).toNat ^^^ 1)
    (hll2_1 : (((cNode <<< (1 : Nat)) ||| pol) ^^^ 1#32).toNat =
      ((cNode <<< (1 : Nat)) ||| pol).toNat ^^^ 1)
    (hgl1_0 : ((gv_a <<< (1 : Nat)) ^^^ 1#32).toNat =
      m6ConeLift s.scratch.work_stk1 ((a <<< (1 : Nat)).toNat ^^^ 1))
    (hgl1_1 : ((gv_c <<< (1 : Nat)) ||| pol).toNat =
      m6ConeLift s.scratch.work_stk1 (((cNode <<< (1 : Nat)) ||| (1#32 ^^^ pol)).toNat ^^^ 1))
    (hgl2_0 : (gv_a <<< (1 : Nat)).toNat =
      m6ConeLift s.scratch.work_stk1 (((a <<< (1 : Nat)) ||| 1#32).toNat ^^^ 1))
    (hgl2_1 : (((gv_c <<< (1 : Nat)) ||| pol) ^^^ 1#32).toNat =
      m6ConeLift s.scratch.work_stk1 (((cNode <<< (1 : Nat)) ||| pol).toNat ^^^ 1))
    (hsem1 : SemEntails (ConeModelSet F_cur s.scratch.work_stk1 nv.toNat)
      [(a <<< (1 : Nat)).toNat ^^^ 1, ((cNode <<< (1 : Nat)) ||| (1#32 ^^^ pol)).toNat ^^^ 1])
    (hent1 : (cnfOfClauses F_cur).EntailsClause
      (cnfClause [m6ConeLift s.scratch.work_stk1 ((a <<< (1 : Nat)).toNat ^^^ 1),
        m6ConeLift s.scratch.work_stk1 (((cNode <<< (1 : Nat)) ||| (1#32 ^^^ pol)).toNat ^^^ 1)]))
    (dS1 : M6ClassData c F0 F_cur s L nv nclsL neq rbit R mS1)
    (hc_get : cNode = dS1.st.scratch.scratch_buf[k6PhtNext + a.toNat]?.getD 0xFFFFFFFF#32)
    (hJ : ∀ (rbit' ncls' neq' : Val i32) m',
      M6ClassData c F0 F_cur s L nv ncls' neq' rbit' R m' →
      wp Γ Q X (Expr.jump jLoop (Arg.var rbit', Arg.var ncls', Arg.var neq',
        Arg.var steps1, ())) m') :
    wp Γ Q X
      (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.imm 11, ())) fun p0 =>
       Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p0.fst, Arg.imm 4, ())) fun p1 =>
       Expr.let_ (Op.mk (OpCode.add i64) (Arg.var kPtr, Arg.var p1.fst, ())) fun p2 =>
       Expr.load i32 (Arg.var p2.fst) fun ld =>
       Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var ld, ())) fun p3 =>
       Expr.let_ (Op.mk (OpCode.sub i64) (Arg.var tick_lim, Arg.var p3.fst, ())) fun prem =>
       Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.imm 15, ())) fun p4 =>
       Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p4.fst, Arg.imm 4, ())) fun p5 =>
       Expr.let_ (Op.mk (OpCode.add i64) (Arg.var kPtr, Arg.var p5.fst, ())) fun p6 =>
       Expr.store (t := i32) (Arg.imm 2) (Arg.var p6.fst)
       (Expr.let_ (Op.mk (OpCode.sext 32 64) (Arg.imm 0, ())) fun q0 =>
        Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var q0.fst, Arg.imm 4, ())) fun q1 =>
        Expr.let_ (Op.mk (OpCode.add i64) (Arg.var assPtr, Arg.var q1.fst, ())) fun q2 =>
        Expr.let_ (Op.mk (OpCode.shl i32) (Arg.var a, Arg.imm 1, ())) fun q3 =>
        Expr.let_ (Op.mk (OpCode.or i32) (Arg.var q3.fst, Arg.imm 1, ())) fun q4 =>
        Expr.store (t := i32) (Arg.var q4.fst) (Arg.var q2.fst)
        (Expr.let_ (Op.mk (OpCode.sext 32 64) (Arg.imm 1, ())) fun r0 =>
         Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var r0.fst, Arg.imm 4, ())) fun r1 =>
         Expr.let_ (Op.mk (OpCode.add i64) (Arg.var assPtr, Arg.var r1.fst, ())) fun r2 =>
         Expr.let_ (Op.mk (OpCode.shl i32) (Arg.var cNode, Arg.imm 1, ())) fun r3 =>
         Expr.let_ (Op.mk (OpCode.or i32) (Arg.var r3.fst, Arg.var pol, ())) fun r4 =>
         Expr.store (t := i32) (Arg.var r4.fst) (Arg.var r2.fst)
         (Expr.call "full_m6_sweep_solve" (as := [i64, i32, i64]) (bs := [i64])
          (Arg.var h, Arg.var nv, Arg.var prem.fst, ()) fun pd2 =>
          Expr.let_ (Op.mk (OpCode.cmp CmpOp.eq i64) (Arg.var pd2.fst, Arg.imm 10, ())) fun c10 =>
          Expr.jnz (Arg.var c10.fst) (clsRefineExpr h nv nclsL neq rbit steps1 jLoop)
           (Expr.let_ (Op.mk (OpCode.cmp CmpOp.ne i64) (Arg.var pd2.fst, Arg.imm 20, ())) fun c20 =>
            Expr.jnz (Arg.var c20.fst)
             (clsUnlinkExpr pnPtr a cNode nv nclsL fun pn =>
               Expr.jump jLoop (Arg.var rbit, Arg.var pn, Arg.var neq, Arg.var steps1, ()))
             (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var cNode, ())) fun u0 =>
              Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var u0.fst, Arg.imm 4, ())) fun u1 =>
              Expr.let_ (Op.mk (OpCode.add i64) (Arg.var pmPtr, Arg.var u1.fst, ())) fun u2 =>
              Expr.store (t := i32) (Arg.imm 1) (Arg.var u2.fst)
              (clsUnlinkExpr pnPtr a cNode nv nclsL fun p_nc =>
                clsMergeBodyExpr h kPtr flPtr a cNode gv_c pol
                  (clsEqPushExpr h kPtr eqbPtr rbit p_nc neq steps1 gv_a gv_c pol jLoop))))))))
      mS1 := by
  subst h_hdr hkptr hassp hflp hpmp hpnp heqb_p
  have hmL := L.hmaxV; have haL := L.hacap
  have hpol_lt : pol.toNat < 2 := by rcases hpol with rfl | rfl <;> decide
  have hscrS1_len := dS1.inv.1.scratch_ok.scratch_buf_len
  have h_idx_cap : ∀ x < nv.toNat, k6PhtNext + x < c.scratch_cap := fun x hx => by
    unfold K6Layout.k6Base at hpht_k6b
    unfold K6Layout.scrLen K6Layout.k6Fixed at hL_len; unfold k6PhtNext at hpht_k6b ⊢; omega
  have h_idx_k6b : ∀ x < nv.toNat, k6PhtNext + x < L.k6Base := fun x hx =>
    Nat.lt_trans (Nat.add_lt_add_left (Nat.lt_of_lt_of_le hx hnv_L) _) hpht_k6b
  obtain ⟨Rfr2, hRfr2⟩ : ∃ Rfr2 : Mem 64 → Prop, Rfr2 = (FullK6Frame c L dS1.st ⋆ R) := ⟨_, rfl⟩
  have hm_ka2 : (K6MemA L (L.kPtr c.pScratchBuf)
      (k6StateOfScratch L dS1.st.scratch.scratch_buf) ⋆ Rfr2) mS1 := by
    have hmF' := dS1.mem
    rw [fullMem_eq_k6Frame (hscrS1_len.trans hL_len.symm)] at hmF'; rw [hRfr2]
    exact k6Mem_to_amem dS1.k6.shapes (sep_ac hmF')
  change wp _ _ _ _ _; c0_hsteps; try dsimp only [Prod.fst]
  open scoped K6MemATactics K6PtrTactics FullK6DynMem M6ClsMem in c0_hsteps!
  rw [hRfr2] at hm
  refine m6_class_solve2_wp hSolve rfl hL_len hL_mv hpht_k6b hnv_L dS1
    (by change ((a <<< (1 : Nat)) ||| 1#32).toNat < 2 * nv.toNat; rw [ha02]; omega)
    (by change ((cNode <<< (1 : Nat)) ||| pol).toNat < 2 * nv.toNat; rw [ha12]; omega)
    hm fun d2 mS2 dS2 hpreS2 hunsS2 => ?_
  have hc_get_S2 : cNode = dS2.st.scratch.scratch_buf[k6PhtNext + a.toNat]?.getD 0xFFFFFFFF#32 := by
    rw [hpreS2 _ (h_idx_k6b _ ha_lt)]; exact hc_get
  m6_split
  · m6_to_group
    exact m6_class_refine_wp hRef hRefP rfl hL_len hL_mv hcap hnv_L hnv_mx hnv_2mx hws_lt
      (@hcongr) dS2 fun rbitR new_n mP hdP => by m6_steps; exact hJ rbitR new_n neq mP hdP
  m6_split; rotate_left
  · obtain ⟨hsem2, hent2⟩ := m6_coneModelSet_unsat_bin
      (by change ((a <<< (1 : Nat)) ||| 1#32).toNat < 2 * nv.toNat; rw [ha02]; omega)
      (by change ((cNode <<< (1 : Nat)) ||| pol).toNat < 2 * nv.toNat; rw [ha12]; omega)
      (hunsS2 (by bv_omega))
    have hscrS2_len := dS2.inv.1.scratch_ok.scratch_buf_len
    have hsl_S2 : dS2.st.scratch.scratch_buf.length = L.scrLen := hscrS2_len.trans hL_len.symm
    obtain ⟨hslM, hofM, hpkM1, hpkM2⟩ := m6_partOk_merge_unlink hsl_S2.symm hnv_L (by omega)
      ha_lt hc_lt hc_get_S2 dS2.part
    let scrM0 := dS2.st.scratch.scratch_buf.set (L.phtMerged + cNode.toNat) 1#32
    let nxtC2 := scrM0[k6PhtNext + cNode.toNat]'(by
      dsimp only [scrM0]; rw [List.length_set, hscrS2_len]; exact h_idx_cap cNode.toNat hc_lt)
    let scrM := scrM0.set (k6PhtNext + a.toNat) nxtC2
    let sM : FullState := { dS2.st with scratch := { dS2.st.scratch with scratch_buf := scrM } }
    have hinvM := m6_fullDenseInvW_with_scratch dS2.inv (hslM.trans hL_len)
      (fuel' := dS2.st.core.fuel)
    have hmS2 := dS2.mem
    unfold clsUnlinkExpr; change wp _ _ _ _ _
    open scoped M6PhtMem in (c0_hsteps_nogrp; try dsimp only [Prod.fst])
    open scoped M6PhtMem in m6_to_group
    refine wp_join_group (ts := [i32])
      (fun (nclsM, ()) mM => nclsM.toNat ≤ c.max_vars ∧
        ∃ _ : M6ClassData c F0 F_cur s L nv nclsM neq rbit R mM, True)
      (fun _ (nclsM, ()) mM ⟨hncM, dM, _⟩ => by
        refine m6_class_merge_body_wp hLive hQ_20 rfl rfl rfl hL_len hL_mv hpht_k6b hnv_L (by omega)
          ha_lt hc_lt hpol ha01 ha12 hll1_0 hll2_1 (by rw [hll1_0, hll1_1]; exact hsem1)
          (by rw [hll2_0, hll2_1]; exact hsem2) dM fun mL2 dL2 => ?_
        have heq_f : LitEquiv (cnfOfClauses F_cur)
            (gv_a <<< (1 : Nat)).toNat ((gv_c <<< (1 : Nat)) ||| pol).toNat := by
          have he1 : (cnfOfClauses F_cur).EntailsClause
              (cnfClause [(gv_a <<< (1 : Nat)).toNat ^^^ 1,
                ((gv_c <<< (1 : Nat)) ||| pol).toNat]) := by
            rw [show (gv_a <<< (1 : Nat)).toNat ^^^ 1 = ((gv_a <<< (1 : Nat)) ^^^ 1#32).toNat
              by simp, hgl1_0, hgl1_1]; exact hent1
          have he2 : (cnfOfClauses F_cur).EntailsClause
              (cnfClause [(gv_a <<< (1 : Nat)).toNat,
                ((gv_c <<< (1 : Nat)) ||| pol).toNat ^^^ 1]) := by
            rw [show ((gv_c <<< (1 : Nat)) ||| pol).toNat ^^^ 1 =
              (((gv_c <<< (1 : Nat)) ||| pol) ^^^ 1#32).toNat by simp, hgl2_0, hgl2_1]; exact hent2
          refine ⟨he1, ?_⟩
          rw [CNF.entails_clause_def] at he2 ⊢; intro β hβ
          have h2 := (clauseEvalVal_iff β _).mpr (he2 β hβ); rw [← clauseEvalVal_iff]
          simp only [clauseEvalVal, List.any_cons, List.any_nil, Bool.or_false,
            show ((gv_c <<< (1 : Nat)) ||| pol).toNat ^^^ 1 =
              litNeg ((gv_c <<< (1 : Nat)) ||| pol).toNat from rfl] at h2 ⊢
          simpa [Bool.or_comm] using h2
        exact m6_class_eq_push_wp hRearm rfl rfl rfl hL_len hpht_k6b hnv_L hncM hgva_lt hgvc_lt
          hpol hla_eq hlc_eq heq_f dL2 fun neq' mF hdF => hJ rbit nclsM neq' mF hdF)
      (fun _ hJnc => by
        open scoped M6PhtMem in (c0_hsteps_nogrp; try dsimp only [Prod.fst]; m6_split)
        · have hn1 : (nclsL - 1#32).toNat ≤ c.max_vars := by
            rw [bv32_sub1_of_pos hncls_pos]; exact Nat.le_trans (Nat.sub_le _ _) dS2.ncls_le
          m6_steps
          exact hJnc (nclsL - 1#32, ()) _ ⟨hn1, ⟨dS2.rbit_le, hn1, dS2.neq_le, sM, hinvM, dS2.cv,
            dS2.fuel, dS2.repr, dS2.ws, dS2.tmk, dS2.trh, dS2.gu, hofM ▸ dS2.k6, hofM ▸ dS2.nv_eq,
            hofM ▸ dS2.neq_eq, hofM ▸ dS2.hwm, dS2.hw_le,
            (by rw [bv32_sub1_of_pos hncls_pos]; exact hpkM2), m6EqBufOk_mono dS2.eqb rfl rfl,
            by dsimp only [sM, scrM, scrM0, nxtC2]; assumption⟩, trivial⟩
        · m6_steps
          exact hJnc (nclsL, ()) _ ⟨dS2.ncls_le, ⟨dS2.rbit_le, dS2.ncls_le, dS2.neq_le, sM, hinvM,
            dS2.cv, dS2.fuel, dS2.repr, dS2.ws, dS2.tmk, dS2.trh, dS2.gu, hofM ▸ dS2.k6,
            hofM ▸ dS2.nv_eq, hofM ▸ dS2.neq_eq, hofM ▸ dS2.hwm, dS2.hw_le, hpkM1,
            m6EqBufOk_mono dS2.eqb rfl rfl, by dsimp only [sM, scrM, scrM0, nxtC2]; assumption⟩,
            trivial⟩)
  · exact m6_class_unlink_wp hL_len hnv_L hncls_pos ha_lt hc_lt dS2 hc_get_S2 rfl
      fun ncls' m' hd' => by m6_steps; exact hJ rbit ncls' neq m' hd'

/-! ## 3. Main Theorem (`full_m6_sweep_classes_wp`) -/

theorem full_m6_sweep_classes_wp (Γ : Env)
    (hMaxV : Γ.Has "full_m6_max_v" m6MaxVSpec)
    (hBuild : Γ.Has "full_m6_sweep_build_pht" fullM6SweepBuildPhtSpec)
    (hExt : Γ.Has "full_m6_extract_pht" fullM6ExtractPhtSpec)
    (hFlip : Γ.Has "full_k6_flip" step13K6FlipSpec)
    (hRef : Γ.Has "full_m6_sweep_refine_sig" fullM6SweepRefineSigSpec)
    (hRefP : Γ.Has "full_m6_refine_partition" fullM6RefinePartitionSpec)
    (hSolve : Γ.Has "full_m6_sweep_solve" fullM6SweepSolveSpec)
    (hLive : Γ.Has "full_k512_add_live_m6" step13K6AddLiveSpec)
    (hRearm : Γ.Has "full_m6_sweep_rearm" fullM6SweepRearmSpec) :
    ∀ args m Q X, fullM6SweepClassesSpec args m Q X →
      Func.wp Γ full_m6_sweep_classes_body args m Q X := by
  rintro ⟨h, nv, rbit_in, tick_lim, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, s, R, rfl, hinv, hcone, hrb_in, ⟨L, hL_len, hL_mv, hhwm0, hhw_le0⟩, hm, hQ⟩
  have hlen := hinv.1; have hcv_le := hlen.core_ok.cur_vars_le
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hscr_len := hlen.scratch_ok.scratch_buf_len
  obtain ⟨hK0, hnv_bv0, _⟩ :=
    m6SweepConeOk_to_k6Inv (hL_len.trans hscr_len.symm) (hscr_len.symm ▸ hL_mv) hcone
  have hnv_bv : (k6StateOfScratch L s.scratch.scratch_buf).nv = nv :=
    hnv_bv0.trans (BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt nv.isLt]))
  have hhw_le : s.scratch.glue_used[33]? = some 0xFFFFFFFF#32 ∨
      nv.toNat ≤ (s.scratch.glue_used[33]?.getD 0#32).toNat := by rwa [hnv_bv] at hhw_le0
  have hcap : k6MinScr ≤ c.scratch_cap := hscr_len ▸ hcone.2.2.2.2.2.1
  have hnv_cv : nv.toNat ≤ s.core.cur_vars := hcone.2.2.1
  have hws_lt := hcone.2.2.2.1; have hnv_mx : nv.toNat ≤ c.max_vars := Nat.le_trans hnv_cv hcv_le
  have hnv_2mx : nv.toNat ≤ 2 * c.max_vars := by omega
  let ws1 := s.scratch.work_stk1; let P := ConeModelSet F_cur ws1 nv.toNat
  have hmL := L.hmaxV; have haL := L.hacap
  have hnv_L : nv.toNat ≤ L.maxV := by rw [hL_mv, ← hscr_len]; exact hcone.2.1
  have hmv_eq := m6_mv32_eq (c := c) hL_mv; have hkptr_c0 := m6_k6Ptr_eq (c := c) hL_mv (by omega)
  have hpm_c0 := m6_ptr_phtMerged L c.pScratchBuf
  have hpn_c0' : c.pScratchBuf + BitVec.setWidth 64 (1280 : BitVec 32) * 4 =
      c.pScratchBuf + BitVec.ofNat 64 (4 * k6PhtNext) := rfl
  have hass_c0 := k6_ptr_assump L (L.kPtr c.pScratchBuf)
  have hkvals_c0 := k6_ptr_vals L (L.kPtr c.pScratchBuf)
  have hpht_k6b : k6PhtNext + L.maxV < L.k6Base := by unfold k6PhtNext K6Layout.k6Base; omega
  have h_idx_cap : ∀ x < nv.toNat, k6PhtNext + x < c.scratch_cap := fun x hx => by
    unfold k6PhtNext; unfold K6Layout.scrLen K6Layout.k6Base K6Layout.k6Fixed at hL_len; omega
  have h_idx_k6b : ∀ x < nv.toNat, k6PhtNext + x < L.k6Base := fun x hx =>
    Nat.lt_trans (Nat.add_lt_add_left (Nat.lt_of_lt_of_le hx hnv_L) _) hpht_k6b
  have hcongr_k6 : ∀ {scrA scrB : List (BitVec 32)},
      (∀ i < c.scratch_cap, L.phtMerged ≤ i → scrB[i]? = scrA[i]?) →
      scrA.length = c.scratch_cap → scrB.length = c.scratch_cap →
      k6StateOfScratch L scrB = k6StateOfScratch L scrA := fun {scrA scrB} heq hA hB => by
    have hdrop : scrB.drop L.k6Base = scrA.drop L.k6Base := List.ext_getElem
      (by simp [hA, hB]) fun j h1 h2 => by
        simp only [List.getElem_drop]
        have hj : L.k6Base + j < c.scratch_cap := by simp [hB] at h1; omega
        have hq := heq (L.k6Base + j) hj (by unfold K6Layout.phtMerged K6Layout.k6Base; omega)
        rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at hq
        exact Option.some.inj hq
    unfold k6StateOfScratch; rw [hdrop]
  have hQ_20 : M6ClsQ20 c F0 F_cur s L R Q :=
    fun s' m' hi hc' hf hr hw ht htr hg hh hu hm' =>
      hQ 20#64 s' m' hi hc' hf hr hw ht htr hg ⟨L, hL_len, hL_mv, hh⟩
        (Or.inr rfl) (fun _ => hu) (fun h => by cases h) hm'
  clear hcone hnv_bv0 hhw_le0
  unfold Func.wp
  run_tac do
    let g ← Lean.Elab.Tactic.getMainGoal
    let ty := (← Lean.instantiateMVars (← g.getType)).consumeMData.headBeta
    let e' ← Lean.Meta.whnf (ty.getArg! 4)
    let ty' := Lean.mkAppN ty.getAppFn (ty.getAppArgs.set! 4 e')
    Lean.Elab.Tactic.replaceMainGoal [← g.change ty' (checkDefEq := false)]
  m6_steps
  refine m6_call_max_v hMaxV (m6_scrCap_lt64 c) ?_
  m6_split
  · exfalso; have h0 := congrArg BitVec.toNat hc
    rw [hmv_eq, k6_mv32_toNat] at h0; simp at h0; omega
  m6_split
  · exfalso; rw [← hL_mv, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hc; omega
  obtain ⟨Rfr0, hRfr0⟩ : ∃ Rfr0 : Mem 64 → Prop, Rfr0 = (FullK6Frame c L s ⋆ R) := ⟨_, rfl⟩
  have hm_ka0 : (K6MemA L (L.kPtr c.pScratchBuf)
      (k6StateOfScratch L s.scratch.scratch_buf) ⋆ Rfr0) m := by
    rw [fullMem_eq_k6Frame (hscr_len.trans hL_len.symm)] at hm; rw [hRfr0]
    exact k6Mem_to_amem hK0.shapes (sep_ac hm)
  change wp _ _ _ _ _; c0_hsteps; try dsimp only [Prod.fst]; try rw [hkptr_c0]; try rw [hmv_eq]
  open scoped K6MemATactics K6PtrTactics in (c0_hstep; c0_hsteps_nogrp)
  have hKnq0 := k6Inv_set_neq 0#32 hK0
  rw [hRfr0, show (0 : BitVec 32) = 0#32 from rfl] at hm
  let ksNq0 := (k6StateOfScratch L s.scratch.scratch_buf).putHdr .neq 0#32
  let scrNq0 := s.scratch.scratch_buf.take L.k6Base ++ ksNq0.toSlab
  let sNq0 : FullState := { s with scratch := { s.scratch with scratch_buf := scrNq0 } }
  obtain ⟨hscrNq0_len, _, hofNq0, hmNq0⟩ :=
    m6_join_k6_ofSlab (s := s) hL_len hscr_len hKnq0.shapes hm
  have hlenNq0 : sNq0.LengthsOk c :=
    ⟨hlen.core_ok, { hlen.scratch_ok with scratch_buf_len := hscrNq0_len }⟩
  have hhwmNq0 : K6HwmClean L (s.scratch.glue_used[33]?.getD 0#32) ksNq0 :=
    m6_hwm_step hhw_le hnv_bv hhwm0 (k6TailEq_of_putHdr_ne_nv (by decide) _)
  m6_to_group
  refine wp_join_group (ts := [i64]) (fun (_smask0, ()) ms => ms = m)
    (fun _ (smask0, ()) ms hms => by
      subst ms; m6_call hBuild
      refine ⟨c, sNq0, L, R, rfl, hlenNq0, hL_len, hL_mv, hnv_L, hnv_2mx, hws_lt, hmNq0,
        fun scrB mB hscrB_len hpreB hphtB hmB => ?_⟩
      let sB : FullState := { sNq0 with scratch := { sNq0.scratch with scratch_buf := scrB } }
      have hlenB : sB.LengthsOk c :=
        ⟨hlenNq0.core_ok, { hlenNq0.scratch_ok with scratch_buf_len := hscrB_len }⟩
      have hofB : k6StateOfScratch L scrB = ksNq0 := by
        dsimp only [ksNq0]; rw [← hofNq0]
        exact hcongr_k6 (fun i hi hdom => hpreB i hi (Or.inr hdom)) hscrNq0_len hscrB_len
      m6_call hExt
      refine ⟨c, sB, L, R, rfl, hlenB, hL_len, hL_mv, hnv_L, hnv_mx, hws_lt, hphtB, hmB,
        fun ncls scrE sstkE mclrE mE hscrE_len hsstE_len hmcE_len hpreE hnclsE hpartE hmE => ?_⟩
      let sE : FullState :=
        { sB with core := { sB.core with min_clr := mclrE }
                  scratch := { sB.scratch with scratch_buf := scrE, shrink_stk := sstkE } }
      have hofE : k6StateOfScratch L scrE = ksNq0 := by
        rw [← hofB]
        exact hcongr_k6 (fun i hi hdom => hpreE i hi (Or.inr hdom)) hscrB_len hscrE_len
      obtain ⟨initD, _⟩ : ∃ _ : M6ClassData c F0 F_cur s L nv ncls 0#32 rbit_in R mE, True :=
        ⟨⟨hrb_in, hnclsE, Nat.zero_le _, sE,
          m6_fullDenseInvW_with_cls_scratch hinv hscrE_len hsstE_len hmcE_len
            hlen.scratch_ok.wsort_len,
          rfl, le_refl _, rfl, rfl, rfl, rfl, rfl, hofE ▸ hKnq0, hofE.symm ▸ hnv_bv,
          by rw [hofE]; rfl, hofE ▸ hhwmNq0, hhw_le, hpartE,
          ⟨Nat.zero_le _, fun _ h => by cases h⟩, hmE⟩, trivial⟩
      clear hpartE hofE hpreE hnclsE hmE hmcE_len hsstE_len hscrE_len sE scrE sstkE mclrE
        hmB hphtB hofB hpreB hlenB hscrB_len sB scrB
        hhwmNq0 hmNq0 hofNq0 hlenNq0 hscrNq0_len sNq0 scrNq0 ksNq0 hm
      let steps0 : BitVec 32 := (nv <<< (2 : Nat)) + 64#32
      m6_to_group
      refine wp_loop_inv (ts := [i32, i32, i32, i32])
        (fun (rbit, nclsL, neq, steps, ()) ml =>
          ∃ _ : M6ClassData c F0 F_cur s L nv nclsL neq rbit R ml, True)
        (fun (_, _, _, steps, ()) _ => steps.toNat)
        (fun _ hJ => by m6_steps; exact hJ (rbit_in, ncls, 0#32, steps0, ()) mE ⟨initD, trivial⟩)
        (fun _ (rbit, nclsL, neq, steps, ()) ml ⟨D, _⟩ hJ => by
          clear initD; m6_to_group
          refine wp_join_group (ts := []) (fun () m_ex => m_ex = ml)
            (fun _ () m_ex hm_ex => by
              have hm_ex_mem : (FullMem c D.st ⋆ R) m_ex := hm_ex ▸ D.mem
              m6_to_group; refine wp_unroll_group fun _ _ => ?_
              m6_split
              · have huns := D.inv.2.1.ext_sound.2 (D.inv.2.1.inconsistent_sound (by bv_omega))
                m6_steps
                exact hQ_20 D.st m_ex D.inv D.cv D.fuel D.repr D.ws D.tmk D.trh D.gu
                  (D.gu.symm ▸ D.hwm) huns hm_ex_mem
              · m6_steps
                exact hQ 1#64 D.st m_ex D.inv D.cv D.fuel D.repr D.ws D.tmk D.trh D.gu
                  ⟨L, hL_len, hL_mv, D.gu.symm ▸ D.hwm⟩ (Or.inl rfl) (fun h => by cases h)
                  (fun _ => ⟨L, hL_len, hL_mv, D.neq_eq.symm ▸ D.eqb⟩) hm_ex_mem)
            (fun _ hJex => by
              have hml := D.mem; have hlenD := D.inv.1
              have hscrD_len := hlenD.scratch_ok.scratch_buf_len
              m6_split; rotate_left; · m6_steps; exact hJex () ml rfl
              m6_split; rotate_left; · m6_steps; exact hJex () ml rfl
              m6_split; rotate_left; · m6_steps; exact hJex () ml rfl
              m6_split; rotate_left; · m6_steps; exact hJex () ml rfl
              m6_split; rotate_left; · m6_steps; exact hJex () ml rfl
              change wp _ _ _ _ _
              c0_hsteps_nogrp; try dsimp only [Prod.fst]; try rw [hkptr_c0]; try rw [hmv_eq]
              open scoped FullK6DynMem in m6_split; rotate_left; · m6_steps; exact hJex () ml rfl
              have hncls_pos : 0 < nclsL.toNat := ‹_›
              have hsteps_pos : 0 < steps.toNat := ‹_›
              have hsteps1 : (steps - 1#32).toNat = steps.toNat - 1 := bv32_sub1_of_pos hsteps_pos
              have ha_idx : ((nclsL - 1#32).setWidth 64).toNat <
                  D.st.scratch.shrink_stk.length := by
                rw [hlenD.scratch_ok.shrink_stk_len, bv_c0_zext32_64, bv32_sub1_of_pos hncls_pos]
                have := D.ncls_le; omega
              let a := D.st.scratch.shrink_stk[((nclsL - 1#32).setWidth 64).toNat]'ha_idx
              have ha_lt : a.toNat < nv.toNat := by
                have hp := D.part.2.2 (nclsL.toNat - 1) (by omega)
                have hlen_ss := hlenD.scratch_ok.shrink_stk_len; have hn_le := D.ncls_le
                rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at hp
                dsimp only [a]
                rwa [m6_list_getElem_congr (by rw [bv_c0_zext32_64, bv32_sub1_of_pos hncls_pos])
                  ha_idx (by omega)]
              let cNode := D.st.scratch.scratch_buf[k6PhtNext + a.toNat]'(by
                rw [hscrD_len]; exact h_idx_cap a.toNat ha_lt)
              have hc_get : cNode = D.st.scratch.scratch_buf[k6PhtNext + a.toNat]?.getD
                  0xFFFFFFFF#32 := by
                dsimp only [cNode]
                rw [List.getElem?_eq_getElem (by rw [hscrD_len]; exact h_idx_cap a.toNat ha_lt),
                  Option.getD_some]
              have ha_mv : a.toNat < L.maxV := Nat.lt_of_lt_of_le ha_lt hnv_L
              change wp _ _ _ _ _; c0_hsteps_nogrp; try dsimp only [Prod.fst]
              try rw [hmv_eq]; try rw [hpm_c0]; try rw [hpn_c0]; try rw [hpn_c0']
              open scoped M6PhtMem in m6_split
              · m6_steps
                exact hJ (rbit, nclsL - 1#32, neq, steps - 1#32, ()) ml
                  (by dsimp only; rw [hsteps1]; omega)
                  ⟨⟨D.rbit_le,
                    (by rw [bv32_sub1_of_pos hncls_pos]
                        exact Nat.le_trans (Nat.sub_le _ _) D.ncls_le),
                    D.neq_le, D.st, D.inv, D.cv, D.fuel, D.repr, D.ws, D.tmk, D.trh, D.gu, D.k6,
                    D.nv_eq, D.neq_eq, D.hwm, D.hw_le,
                    (by rw [bv32_sub1_of_pos hncls_pos]; exact m6_partOk_drop_head D.part),
                    D.eqb, D.mem⟩, trivial⟩
              · have hc_lt : cNode.toNat < nv.toNat := by
                  have : ¬ nv.toNat ≤ cNode.toNat := ‹_›; omega
                have hc_mv : cNode.toNat < L.maxV := Nat.lt_of_lt_of_le hc_lt hnv_L
                have ha_ws : (a.setWidth 64).toNat < D.st.scratch.work_stk1.length := by
                  rw [hlenD.scratch_ok.work_stk1_len, bv_c0_zext32_64]; omega
                have hc_ws : (cNode.setWidth 64).toNat < D.st.scratch.work_stk1.length := by
                  rw [hlenD.scratch_ok.work_stk1_len, bv_c0_zext32_64]; omega
                let gv_a := D.st.scratch.work_stk1[(a.setWidth 64).toNat]'ha_ws
                let gv_c := D.st.scratch.work_stk1[(cNode.setWidth 64).toNat]'hc_ws
                have hgva_ws : (ws1[a.toNat]?.getD 0#32).toNat = gv_a.toNat := by
                  have h_wlen := hlenD.scratch_ok.work_stk1_len; dsimp only [gv_a, ws1]
                  rw [← D.ws, List.getElem?_eq_getElem (by rw [h_wlen]; omega), Option.getD_some]
                  exact congrArg BitVec.toNat (m6_list_getElem_congr (bv_c0_zext32_64 a)
                    (by rw [h_wlen]; omega) (by rw [h_wlen]; omega)).symm
                have hgvc_ws : (ws1[cNode.toNat]?.getD 0#32).toNat = gv_c.toNat := by
                  have h_wlen := hlenD.scratch_ok.work_stk1_len; dsimp only [gv_c, ws1]
                  rw [← D.ws, List.getElem?_eq_getElem (by rw [h_wlen]; omega), Option.getD_some]
                  exact congrArg BitVec.toNat (m6_list_getElem_congr (bv_c0_zext32_64 cNode)
                    (by rw [h_wlen]; omega) (by rw [h_wlen]; omega)).symm
                have hgva_lt : gv_a.toNat < s.core.cur_vars := by
                  rw [← hgva_ws]; exact hws_lt a.toNat ha_lt
                have hgvc_lt : gv_c.toNat < s.core.cur_vars := by
                  rw [← hgvc_ws]; exact hws_lt cNode.toNat hc_lt
                have ha_fl : (gv_a.setWidth 64).toNat < D.st.core.flags.length := by
                  rw [hlenD.core_ok.flags_len, bv_c0_zext32_64]; omega
                have hc_fl : (gv_c.setWidth 64).toNat < D.st.core.flags.length := by
                  rw [hlenD.core_ok.flags_len, bv_c0_zext32_64]; omega
                change wp _ _ _ _ _; c0_hsteps_nogrp; try dsimp only [Prod.fst]
                try rw [hmv_eq]; try rw [hpm_c0]; try rw [hpn_c0]; try rw [hpn_c0']
                open scoped M6PhtMem in m6_to_group
                refine wp_join_group (ts := []) (fun () mU => mU = ml)
                  (fun _ () mU hmU => by
                    subst mU
                    exact m6_class_unlink_wp hL_len hnv_L hncls_pos ha_lt hc_lt D hc_get rfl
                      fun ncls' m' hd' => by
                        m6_steps
                        exact hJ (rbit, ncls', neq, steps - 1#32, ()) m'
                          (by dsimp only; rw [hsteps1]; omega) ⟨hd', trivial⟩)
                  (fun _ hJ_un => by
                    open scoped M6PhtMem in m6_split; · m6_steps; exact hJ_un () ml rfl
                    open scoped M6PhtMem in m6_split; · m6_steps; exact hJ_un () ml rfl
                    m6_split; · m6_steps; exact hJ_un () ml rfl
                    m6_split; · m6_steps; exact hJ_un () ml rfl
                    have ha_mc : (a.setWidth 64).toNat < D.st.core.min_clr.length := by
                      rw [hlenD.core_ok.min_clr_len_arr, bv_c0_zext32_64]; omega
                    have hc_mc : (cNode.setWidth 64).toNat < D.st.core.min_clr.length := by
                      rw [hlenD.core_ok.min_clr_len_arr, bv_c0_zext32_64]; omega
                    let pol : BitVec 32 :=
                      (D.st.core.min_clr[(a.setWidth 64).toNat]'ha_mc &&& 1#32) ^^^
                      (D.st.core.min_clr[(cNode.setWidth 64).toNat]'hc_mc &&& 1#32)
                    have hpol : pol = 0#32 ∨ pol = 1#32 := m6_pol_01 _ _
                    obtain ⟨hpol_lt0, hpol_lt1⟩ : pol.toNat < 2 ∧ (1#32 ^^^ pol).toNat < 2 := by
                      rcases hpol with hp | hp <;> rw [hp] <;> decide
                    obtain ⟨ha01, ha11, ha02, ha12, hla_eq, hlc_eq, hll1_0, hll1_1, hll2_0, hll2_1,
                      hgl1_0, hgl1_1, hgl2_0, hgl2_1⟩ :=
                      m6_bin_lits_align (by omega) (by omega) (by omega) (by omega) hgva_ws hgvc_ws
                        hpol
                    have ha2_lt : (a <<< (1 : Nat)).toNat < 2 * L.maxV := by
                      rw [m6_bv32_shl1_lt (by omega)]; omega
                    have hc2_lt : (cNode <<< (1 : Nat)).toNat < 2 * L.maxV := by
                      rw [m6_bv32_shl1_lt (by omega)]; omega
                    m6_to_group
                    refine wp_join_group (ts := [i32])
                      (fun (fa, ()) mfa => mfa = ml ∧ fa.toNat < 2 * nv.toNat)
                      (fun _ (fa, ()) mfa ⟨hmfa, hfa_lt⟩ => by
                        subst mfa; m6_to_group
                        refine wp_join_group (ts := [i32])
                          (fun (fc, ()) mfc => mfc = ml ∧ fc.toNat < 2 * nv.toNat)
                          (fun _ (fc, ()) mfc ⟨hmfc, hfc_lt⟩ => by
                            subst mfc; m6_to_group
                            refine wp_join_group (ts := [])
                              (fun () mFl =>
                                ∃ _ : M6ClassData c F0 F_cur s L nv nclsL neq rbit R mFl, True)
                              (fun _ () mFl ⟨dFl, _⟩ => by
                                m6_to_group
                                exact m6_class_refine_wp hRef hRefP rfl hL_len hL_mv hcap hnv_L
                                  hnv_mx hnv_2mx hws_lt (@hcongr_k6) dFl fun rbitR new_n mP hdP =>
                                  by m6_steps
                                     exact hJ (rbitR, new_n, neq, steps - 1#32, ()) mP
                                       (by dsimp only; rw [hsteps1]; omega) ⟨hdP, trivial⟩)
                              (fun _ hJfl =>
                                m6_class_flip2_wp hFlip rfl hL_len hL_mv hpht_k6b hnv_L hfa_lt
                                  hfc_lt D (fun mFl dFl => by m6_steps; exact hJfl () mFl ⟨dFl,
                                    trivial⟩)
                                  fun mFc dFc hdFc_pre => by
                                  have hscrFc := dFc.inv.1.scratch_ok.scratch_buf_len
                                  obtain ⟨Rfr1, hRfr1⟩ :
                                      ∃ Rfr1 : Mem 64 → Prop, Rfr1 = (FullK6Frame c L dFc.st ⋆ R) :=
                                    ⟨_, rfl⟩
                                  have hm_ka1 : (K6MemA L (L.kPtr c.pScratchBuf)
                                      (k6StateOfScratch L dFc.st.scratch.scratch_buf) ⋆ Rfr1) mFc :=
                                    by have hmF' := dFc.mem
                                       rw [fullMem_eq_k6Frame (hscrFc.trans hL_len.symm)] at hmF'
                                       rw [hRfr1]; exact k6Mem_to_amem dFc.k6.shapes (sep_ac hmF')
                                  change wp _ _ _ _ _; c0_hsteps; try dsimp only [Prod.fst]
                                  try rw [hkptr_c0]; try rw [hmv_eq]; try rw [hass_c0]
                                  open scoped K6MemATactics K6PtrTactics FullK6DynMem M6ClsMem
                                    in c0_hsteps!
                                  rw [hRfr1] at hm
                                  refine m6_class_solve2_wp hSolve rfl hL_len hL_mv hpht_k6b hnv_L
                                    dFc (by change (a <<< (1 : Nat)).toNat < 2 * nv.toNat
                                            rw [ha01]; omega)
                                    (by change ((cNode <<< (1 : Nat)) ||| (1#32 ^^^ pol)).toNat <
                                          2 * nv.toNat; rw [ha11]; omega)
                                    hm fun d1 mS1 dS1 hpreS1 hunsS1 => ?_
                                  have hc_get_S1 : cNode = dS1.st.scratch.scratch_buf[k6PhtNext +
                                      a.toNat]?.getD 0xFFFFFFFF#32 := by
                                    rw [hpreS1 _ (h_idx_k6b _ ha_lt),
                                      hdFc_pre _ (h_idx_k6b _ ha_lt), ← hc_get]
                                  m6_split
                                  · m6_to_group
                                    exact m6_class_refine_wp hRef hRefP rfl hL_len hL_mv hcap hnv_L
                                      hnv_mx hnv_2mx hws_lt (@hcongr_k6) dS1
                                      fun rbitR new_n mP hdP => by
                                        m6_steps
                                        exact hJ (rbitR, new_n, neq, steps - 1#32, ()) mP
                                          (by dsimp only; rw [hsteps1]; omega) ⟨hdP, trivial⟩
                                  m6_to_group
                                  refine wp_join_group (ts := []) (fun () mU1 => mU1 = mS1)
                                    (fun _ () mU1 hmU1 => by
                                      subst mU1
                                      exact m6_class_unlink_wp hL_len hnv_L hncls_pos ha_lt hc_lt
                                        dS1 hc_get_S1 rfl fun ncls' m' hd' => by
                                          m6_steps
                                          exact hJ (rbit, ncls', neq, steps - 1#32, ()) m'
                                            (by dsimp only; rw [hsteps1]; omega) ⟨hd', trivial⟩)
                                    (fun _ hJu1 => by
                                      m6_split; · m6_steps; exact hJu1 () mS1 rfl
                                      have hscrS1_len := dS1.inv.1.scratch_ok.scratch_buf_len
                                      have hmS1 := dS1.mem
                                      change wp _ _ _ _ _; c0_hsteps_nogrp
                                      try dsimp only [Prod.fst]
                                      try rw [hkptr_c0]; try rw [hmv_eq]
                                      open scoped FullK6DynMem in m6_split
                                      · m6_steps; exact hJu1 () mS1 rfl
                                      obtain ⟨hsem1, hent1⟩ := m6_coneModelSet_unsat_bin
                                        (by change (a <<< (1 : Nat)).toNat < 2 * nv.toNat
                                            rw [ha01]; omega)
                                        (by change ((cNode <<< (1 : Nat)) |||
                                              (1#32 ^^^ pol)).toNat < 2 * nv.toNat
                                            rw [ha11]; omega)
                                        (hunsS1 (by bv_omega))
                                      exact m6_class_d2_wp hRef hRefP hSolve hLive hRearm hQ_20 rfl
                                        rfl hass_c0 rfl hpm_c0 hpn_c0' rfl hL_len hL_mv hcap
                                        hpht_k6b hnv_L hnv_mx hnv_2mx hws_lt (@hcongr_k6) hncls_pos
                                        ha_lt hc_lt hgva_lt hgvc_lt hpol ha01 ha02 ha12 hla_eq
                                        hlc_eq hll1_0 hll1_1 hll2_0 hll2_1 hgl1_0 hgl1_1 hgl2_0
                                        hgl2_1 hsem1 hent1 dS1 hc_get_S1
                                        fun rbit' ncls' neq' m' hd' =>
                                          hJ (rbit', ncls', neq', steps - 1#32, ()) m'
                                            (by dsimp only; rw [hsteps1]; omega) ⟨hd', trivial⟩)))
                          (fun _ hJfc => by
                            dsimp only [cNode] at hc2_lt; change wp _ _ _ _ _
                            c0_hsteps_nogrp; try dsimp only [Prod.fst]
                            try rw [hkptr_c0]; try rw [hmv_eq]; try rw [hkvals_c0]
                            open scoped FullK6DynMem M6ClsMem in m6_split
                            · m6_steps; exact hJfc (cNode <<< (1 : Nat), ()) ml ⟨rfl, by
                                rw [m6_bv32_shl1_lt (by omega)]; omega⟩
                            · m6_steps
                              have hcc1 := m6_bv32_shl1_or_pol cNode 1#32 (by omega) (by decide)
                              rw [show (1#32 : BitVec 32).toNat = 1 from rfl] at hcc1
                              exact hJfc ((cNode <<< (1 : Nat)) ||| 1#32, ()) ml ⟨rfl, by omega⟩))
                      (fun _ hJfa => by
                        dsimp only [a] at ha2_lt; change wp _ _ _ _ _
                        c0_hsteps_nogrp; try dsimp only [Prod.fst]
                        try rw [hkptr_c0]; try rw [hmv_eq]; try rw [hkvals_c0]
                        open scoped FullK6DynMem M6ClsMem in m6_split
                        · m6_steps; exact hJfa (a <<< (1 : Nat), ()) ml ⟨rfl, by
                            rw [m6_bv32_shl1_lt (by omega)]; omega⟩
                        · m6_steps
                          have haa1 := m6_bv32_shl1_or_pol a 1#32 (by omega) (by decide)
                          rw [show (1#32 : BitVec 32).toNat = 1 from rfl] at haa1
                          exact hJfa ((a <<< (1 : Nat)) ||| 1#32, ()) ml ⟨rfl, by omega⟩)))))
    (fun _ hJsm => by
      m6_split
      · m6_steps; exact hJsm _ _ rfl
      · m6_steps; exact hJsm _ _ rfl)

end LeanQbe.T.Examples.Kissat.Proof.Sweep

end
