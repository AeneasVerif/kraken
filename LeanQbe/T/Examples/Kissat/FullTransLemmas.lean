module
public import LeanQbe.T.Examples.Kissat.FullTransLemmas1
import all Kraken.Mem
import all Kraken.Separation
/-! # Kissat `D-Full` Transitive Reduction Proofs (`Stage 4`, Part 2) -/
set_option autoImplicit false
@[expose] public section
namespace LeanQbe.T.Examples.Kissat.Full
open Std Std.Sat Std.ExtHashMap LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat Kraken.Bedrock2.Test
open FullTransHelpers
open scoped FullArenaTactics FullTransTactics
namespace FullTransHelpers
/-! ## 1. BFS & unroll invariants for `full_trans_lit` -/
section TransBfsInvariants
private theorem sat_pair_elim {α : Nat → Bool} {a b : Nat} (h : (cnfClause [a, b]).Sat α) :
    (cnfClause [a]).Sat α ∨ (cnfClause [b]).Sat α := by
  obtain ⟨l, hl, hs⟩ := (clause_sat_cnfClause_iff α [a, b]).mp h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with hl | hl <;> rw [hl] at hs <;>
    first | exact Or.inl ((sat_cnfClause_singleton α a).mpr hs)
          | exact Or.inr ((sat_cnfClause_singleton α b).mpr hs)
theorem entails_pair_taut {f : CNF Nat} (a : Nat) : f.EntailsClause (cnfClause [a, a ^^^ 1]) := by
  rw [CNF.entails_clause_def]; intro α _; rw [clause_sat_cnfClause_iff]
  by_cases ha : (cnfClause [a]).Sat α
  · exact ⟨a, by simp, (sat_cnfClause_singleton α a).mp ha⟩
  · exact ⟨a ^^^ 1, by simp,
      (sat_cnfClause_singleton α _).mp ((sat_cnfClause_litNeg_iff α a).mpr ha)⟩
theorem entails_pair_trans {f : CNF Nat} {a b c : Nat}
    (h1 : f.EntailsClause (cnfClause [a, b])) (h2 : f.EntailsClause (cnfClause [b ^^^ 1, c])) :
    f.EntailsClause (cnfClause [a, c]) := by
  rw [CNF.entails_clause_def] at h1 h2 ⊢; intro α hα; rw [clause_sat_cnfClause_iff]
  exact (sat_pair_elim (h1 α hα)).elim
    (fun ha => ⟨a, by simp, (sat_cnfClause_singleton α a).mp ha⟩) fun hb =>
    (sat_pair_elim (h2 α hα)).elim (fun hnb => absurd hb ((sat_cnfClause_litNeg_iff α b).mp hnb))
      fun hc => ⟨c, by simp, (sat_cnfClause_singleton α c).mp hc⟩
theorem entails_unit_resolve_pair {f : CNF Nat} {a b : Nat}
    (h1 : f.EntailsClause (cnfClause [a, b])) (h2 : f.EntailsClause (cnfClause [b ^^^ 1])) :
    f.EntailsClause (cnfClause [a]) := by
  rw [CNF.entails_clause_def] at h1 h2 ⊢; intro α hα
  exact (sat_pair_elim (h1 α hα)).elim id fun hb =>
    absurd hb ((sat_cnfClause_litNeg_iff α b).mp (h2 α hα))
theorem entails_pair_collapse {f : CNF Nat} {a b : Nat} (h1 : f.EntailsClause (cnfClause [a, b]))
    (h2 : f.EntailsClause (cnfClause [a, b ^^^ 1])) : f.EntailsClause (cnfClause [a]) := by
  rw [CNF.entails_clause_def] at h1 h2 ⊢; intro α hα; exact (sat_pair_elim (h1 α hα)).elim id
    fun hb => (sat_pair_elim (h2 α hα)).elim id fun hnb =>
      absurd hb ((sat_cnfClause_litNeg_iff α b).mp hnb)
private theorem getD_set2_ne {α : Type} {xs : List α} {a b i : Nat} {x y d : α}
    (ha : i ≠ a) (hb : i ≠ b) : ((xs.set a x).set b y)[i]?.getD d = xs[i]?.getD d := by
  rw [List.getElem?_set_ne hb.symm, List.getElem?_set_ne ha.symm]
private theorem var_ne_xor_pair {x y : Nat} (h : x / 2 ≠ y / 2) :
    x ≠ y ∧ x ≠ y ^^^ 1 ∧ x ^^^ 1 ≠ y ∧ x ^^^ 1 ≠ y ^^^ 1 :=
  ⟨fun e => h (by rw [e]), fun e => h (by rw [e, fullInv_var_xor1]),
   fun e => h (by rw [← e, fullInv_var_xor1]),
   fun e => h (by have := congrArg (· / 2) e; simpa only [fullInv_var_xor1] using this)⟩
/-- Unroll/BFS invariant for `full_trans_lit`. -/
structure TransUnrollInv (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s0 st_pre : FullState) (src saved : Nat) (st : FullState) : Prop where
  len_ok : st.LengthsOk c
  same_core : st.core = { st_pre.core with
    vals := st.core.vals, trl := st.core.trl, trail_end := st.core.trail_end }
  same_scratch : st.scratch = st_pre.scratch
  saved_eq : saved = st_pre.core.trail_end
  saved_le_te : saved ≤ st.core.trail_end
  trl_pres : ∀ i < saved, st.core.trl[i]? = st_pre.core.trl[i]?
  vals_pres : ∀ l < 2 * st_pre.core.cur_vars,
    st_pre.core.vals[l]?.getD 0#8 ≠ 0#8 → st.core.vals[l]?.getD 0#8 = st_pre.core.vals[l]?.getD 0#8
  vals_hi_pres : ∀ l, 2 * st_pre.core.cur_vars ≤ l → st.core.vals[l]? = st_pre.core.vals[l]?
  bfs_trl_inv : ∀ i, saved ≤ i → i < st.core.trail_end →
    ∃ l : BitVec 32, st.core.trl[i]? = some l ∧ l.toNat < 2 * st_pre.core.cur_vars ∧
      st_pre.core.vals[l.toNat]?.getD 0#8 = 0#8 ∧ st.core.vals[l.toNat]?.getD 0#8 = 1#8 ∧
      st.core.vals[l.toNat ^^^ 1]?.getD 0#8 = 0xFF#8 ∧
      (cnfOfClauses F_cur).EntailsClause (cnfClause [src, l.toNat])
  bfs_vars_nodup : ∀ i j, saved ≤ i → i < j → j < st.core.trail_end →
    (st.core.trl[i]?.getD 0#32).toNat / 2 ≠ (st.core.trl[j]?.getD 0#32).toNat / 2
  vals_only_trl : ∀ l < 2 * st_pre.core.cur_vars,
    st_pre.core.vals[l]?.getD 0#8 = 0#8 → st.core.vals[l]?.getD 0#8 ≠ 0#8 →
    ∃ i, saved ≤ i ∧ i < st.core.trail_end ∧
      ((st.core.trl[i]?.getD 0#32).toNat = l ∨ (st.core.trl[i]?.getD 0#32).toNat ^^^ 1 = l)
theorem TransUnrollInv.vals_domain {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 st_pre st : FullState} {src saved l : Nat} (hw0 : FullWitnessInv c F0 F_cur s0.core)
    (hpre_vals : st_pre.core.vals = s0.core.vals)
    (hpre_cv : st_pre.core.cur_vars = s0.core.cur_vars)
    (h : TransUnrollInv c F0 F_cur s0 st_pre src saved st) (hl : l < 2 * st_pre.core.cur_vars) :
    st.core.vals[l]?.getD 0#8 = 0#8 ∨ st.core.vals[l]?.getD 0#8 = 1#8 ∨
    st.core.vals[l]?.getD 0#8 = 0xFF#8 := by
  by_cases h0 : st_pre.core.vals[l]?.getD 0#8 = 0#8
  · by_cases hcur : st.core.vals[l]?.getD 0#8 = 0#8; · exact Or.inl hcur
    obtain ⟨i, hi1, hi2, he⟩ := h.vals_only_trl l hl h0 hcur
    obtain ⟨lit, hget, _, _, hv1, hvff, _⟩ := h.bfs_trl_inv i hi1 hi2
    rw [show (st.core.trl[i]?.getD 0#32).toNat = lit.toNat by simp [hget]] at he
    rcases he with rfl | rfl <;> first | exact Or.inr (Or.inl hv1) | exact Or.inr (Or.inr hvff)
  · rw [h.vals_pres l hl h0, hpre_vals]; exact hw0.vals_domain l (hpre_cv ▸ hl)
theorem TransUnrollInv.trail_end_lt_of_unassigned {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s0 st_pre st : FullState} {src saved ot : Nat}
    (hw0 : FullWitnessInv c F0 F_cur s0.core) (hpre_vals : st_pre.core.vals = s0.core.vals)
    (hpre_te : st_pre.core.trail_end = s0.core.trail_end)
    (hpre_trl : ∀ i < s0.core.trail_end, st_pre.core.trl[i]? = s0.core.trl[i]?)
    (hpre_cv : st_pre.core.cur_vars = s0.core.cur_vars)
    (h : TransUnrollInv c F0 F_cur s0 st_pre src saved st) (hot : ot < 2 * st_pre.core.cur_vars)
    (hzero : st.core.vals[ot]?.getD 0#8 = 0#8) : st.core.trail_end < st_pre.core.cur_vars := by
  have hs_te := h.saved_eq.trans hpre_te
  have htr : ∀ i < saved, (st.core.trl[i]?.getD 0#32).toNat = (s0.core.trl[i]?.getD 0#32).toNat :=
    fun i hi => by rw [h.trl_pres i hi, hpre_trl i (hs_te ▸ hi)]
  have hcross : ∀ a b, a < saved → saved ≤ b → b < st.core.trail_end →
      (st.core.trl[a]?.getD 0#32).toNat / 2 ≠ (st.core.trl[b]?.getD 0#32).toNat / 2 := by
    intro a b ha hb1 hb2 hij; obtain ⟨lit, hget, hlt, hpre0, _, _, _⟩ := h.bfs_trl_inv b hb1 hb2
    rw [htr a ha, show (st.core.trl[b]?.getD 0#32).toNat = lit.toNat by simp [hget]] at hij
    rcases (litVar_eq_iff _ _).mp hij.symm with heq | heq
    · have ht := (hw0.vals_true_iff _ (hpre_cv ▸ hlt)).mpr ⟨a, hs_te ▸ ha, heq.symm⟩
      rw [← hpre_vals, hpre0] at ht; cases ht
    · have hf := (hw0.vals_false_iff _ (hpre_cv ▸ hlt)).mpr
        ⟨a, hs_te ▸ ha, by rw [heq]; exact (litNeg_litNeg _).symm⟩
      rw [← hpre_vals, hpre0] at hf; cases hf
  refine inj_lt_of_missing (fun i => (st.core.trl[i]?.getD 0#32).toNat / 2) ?_ ?_
    (by omega : ot / 2 < st_pre.core.cur_vars) ?_
  · intro i j hi hj hij; by_cases his : i < saved <;> by_cases hjs : j < saved
    · rw [htr i his, htr j hjs] at hij
      exact hw0.trail_vars_nodup i j (hs_te ▸ his) (hs_te ▸ hjs) hij
    · exact False.elim (hcross i j his (by omega) hj hij)
    · exact False.elim (hcross j i hjs (by omega) hi hij.symm)
    · rcases Nat.lt_trichotomy i j with hlt | rfl | hgt
      · exact False.elim (h.bfs_vars_nodup i j (by omega) hlt hj hij)
      · rfl
      · exact False.elim (h.bfs_vars_nodup j i (by omega) hgt hi hij.symm)
  · intro i hi; by_cases his : i < saved
    · rw [htr i his, hpre_cv]; have := hw0.trail_lits_lt i (hs_te ▸ his); omega
    · obtain ⟨_, hget, _, _⟩ := h.bfs_trl_inv i (by omega) hi; simp [hget]; omega
  · intro i hi hij; by_cases his : i < saved
    · have hpre_nz : st_pre.core.vals[ot]?.getD 0#8 ≠ 0#8 := by
        rw [hpre_vals]; intro hz; rw [htr i his] at hij
        exact (hw0.vals_zero_iff (hpre_cv ▸ hot)).mp hz i (hs_te ▸ his) hij
      rw [h.vals_pres ot hot hpre_nz] at hzero; exact hpre_nz hzero
    · obtain ⟨lit, hget, _, _, hv1, hvff, _⟩ := h.bfs_trl_inv i (by omega) hi
      simp [hget] at hij; rcases (litVar_eq_iff _ _).mp hij with heq | heq
      · rw [heq, hzero] at hv1; cases hv1
      · change lit.toNat = ot ^^^ 1 at heq; rw [show lit.toNat ^^^ 1 = ot by
          rw [heq]; exact litNeg_litNeg ot, hzero] at hvff; cases hvff
private theorem pre_xor_zero {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 st_pre : FullState} {l : Nat} (hw0 : FullWitnessInv c F0 F_cur s0.core)
    (hpv : st_pre.core.vals = s0.core.vals) (hpcv : st_pre.core.cur_vars = s0.core.cur_vars)
    (hl : l < 2 * st_pre.core.cur_vars) (h0 : st_pre.core.vals[l]?.getD 0#8 = 0#8) :
    st_pre.core.vals[l ^^^ 1]?.getD 0#8 = 0#8 := by
  rw [hpv]; refine (hw0.vals_zero_iff (hpcv ▸ litNeg_lt_two_mul hl)).mpr fun i hi => ?_
  rw [fullInv_var_xor1]; exact (hw0.vals_zero_iff (hpcv ▸ hl)).mp (hpv ▸ h0) i hi
private theorem ft_bv32_ofNat_eq {c : FullCfg} {n : Nat} (hn : n < 2 * c.max_vars) :
    (BitVec.ofNat 32 n).toNat = n := by
  have := c.hmaxv; unfold dimacsBound at *; simp [Nat.mod_eq_of_lt (by omega : n < 2 ^ 32)]
theorem TransUnrollInv.init {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 st_pre : FullState} {src : Nat} (hw0 : FullWitnessInv c F0 F_cur s0.core)
    (hlen : st_pre.LengthsOk c) (hpre_vals : st_pre.core.vals = s0.core.vals)
    (hpre_te : st_pre.core.trail_end = s0.core.trail_end)
    (hpre_cv : st_pre.core.cur_vars = s0.core.cur_vars)
    (hsrc_lt : src < 2 * st_pre.core.cur_vars) (hsrc0 : st_pre.core.vals[src]?.getD 0#8 = 0#8) :
    let saved := st_pre.core.trail_end; let not_src := src ^^^ 1
    let vals2 := (st_pre.core.vals.set not_src 1#8).set src 0xFF#8
    let trl1 := st_pre.core.trl.set saved (BitVec.ofNat 32 not_src)
    let st' := { st_pre with core :=
      { st_pre.core with vals := vals2, trl := trl1, trail_end := saved + 1 } }
    saved < st_pre.core.cur_vars ∧
    TransUnrollInv c F0 F_cur s0 st_pre src saved st' ∧ saved < st'.core.trail_end := by
  intro saved not_src vals2 trl1 st'; have hte_lt : saved < st_pre.core.cur_vars := by
    rw [show saved = st_pre.core.trail_end from rfl, hpre_te, hpre_cv]
    exact hw0.trail_end_lt_of_unassigned (hpre_cv ▸ hsrc_lt) (hpre_vals ▸ hsrc0)
  have hnot_lt := litNeg_lt_two_mul hsrc_lt; have hnot_ne : not_src ≠ src := litNeg_ne_self src
  have hnot0 := pre_xor_zero hw0 hpre_vals hpre_cv hsrc_lt hsrc0
  have hmx := hlen.core_ok.cur_vars_le
  have hbv_not : (BitVec.ofNat 32 not_src).toNat = not_src := ft_bv32_ofNat_eq (c := c) (by omega)
  have hv_len := hlen.core_ok.vals_len; have htrl_len := hlen.core_ok.trl_len; refine ⟨hte_lt, {
    len_ok := ⟨{ hlen.core_ok with
      vals_len := by simp [st', vals2, hv_len], trl_len := by simp [st', trl1, htrl_len]
      trail_end_le := by simp [st']; omega
      propagated_le := by simp [st']; have := hlen.core_ok.propagated_le; omega }, hlen.scratch_ok⟩
    same_core := rfl, same_scratch := rfl, saved_eq := rfl, saved_le_te := by simp [st']
    trl_pres := fun i hi => List.getElem?_set_ne (by omega)
    vals_pres := fun l hl hnz => getD_set2_ne (fun e => hnz (e ▸ hnot0)) (fun e => hnz (e ▸ hsrc0))
    vals_hi_pres := fun l hl =>
      (List.getElem?_set_ne (by omega)).trans (List.getElem?_set_ne (by omega))
    bfs_trl_inv := fun i hi1 hi2 => by
      have hi : i = saved := by simp [st'] at hi2; omega
      subst hi; refine ⟨BitVec.ofNat 32 not_src, List.getElem?_set_self (by rw [htrl_len]; omega),
        hbv_not.symm ▸ hnot_lt, hbv_not.symm ▸ hnot0, ?_, ?_,
        hbv_not.symm ▸ entails_pair_taut src⟩
      · rw [hbv_not, List.getElem?_set_ne hnot_ne.symm,
          List.getElem?_set_self (by rw [hv_len]; omega)]; rfl
      · rw [hbv_not]; change vals2[(src ^^^ 1) ^^^ 1]?.getD 0#8 = 0xFF#8
        rw [show (src ^^^ 1) ^^^ 1 = src from litNeg_litNeg src,
          List.getElem?_set_self (by rw [List.length_set, hv_len]; omega)]; rfl
    bfs_vars_nodup := fun i j hi1 hij hj2 => by simp [st'] at hj2; omega
    vals_only_trl := fun l hl hpre0 hcur => by
      have hmem : l = not_src ∨ l = src := Classical.byContradiction fun hc => by
        simp only [not_or] at hc; rw [show st'.core.vals[l]?.getD 0#8 =
          st_pre.core.vals[l]?.getD 0#8 from getD_set2_ne hc.1 hc.2, hpre0] at hcur
        exact hcur rfl
      have hg : (st'.core.trl[saved]?.getD 0#32).toNat = not_src := by
        change (trl1[saved]?.getD 0#32).toNat = not_src
        rw [List.getElem?_set_self (by rw [htrl_len]; omega)]; simp [hbv_not]
      refine ⟨saved, Nat.le_refl _, by simp [st'], ?_⟩; rw [hg]
      exact hmem.elim (fun h => Or.inl h.symm)
        fun h => Or.inr (by rw [h]; exact litNeg_litNeg src) }, by simp [st']⟩
theorem TransUnrollInv.push {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 st_pre st : FullState} {src saved ot : Nat} (hw0 : FullWitnessInv c F0 F_cur s0.core)
    (hpre_vals : st_pre.core.vals = s0.core.vals)
    (hpre_te : st_pre.core.trail_end = s0.core.trail_end)
    (hpre_trl : ∀ i < s0.core.trail_end, st_pre.core.trl[i]? = s0.core.trl[i]?)
    (hpre_cv : st_pre.core.cur_vars = s0.core.cur_vars)
    (h : TransUnrollInv c F0 F_cur s0 st_pre src saved st) (hot : ot < 2 * st_pre.core.cur_vars)
    (hzero : st.core.vals[ot]?.getD 0#8 = 0#8)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause [src, ot])) :
    let te := st.core.trail_end; let vals2 := (st.core.vals.set ot 1#8).set (ot ^^^ 1) 0xFF#8
    let trl1 := st.core.trl.set te (BitVec.ofNat 32 ot); let st' := { st with core :=
      { st.core with vals := vals2, trl := trl1, trail_end := te + 1 } }
    te < st_pre.core.cur_vars ∧ TransUnrollInv c F0 F_cur s0 st_pre src saved st' := by
  intro te vals2 trl1 st'
  have hte_lt := h.trail_end_lt_of_unassigned hw0 hpre_vals hpre_te hpre_trl hpre_cv hot hzero
  have hnot_lt : ot ^^^ 1 < 2 * st_pre.core.cur_vars := litNeg_lt_two_mul hot
  have hnot_ne : ot ≠ ot ^^^ 1 := (litNeg_ne_self ot).symm
  have hpre_ot0 : st_pre.core.vals[ot]?.getD 0#8 = 0#8 := Classical.byContradiction fun hnz => by
    rw [h.vals_pres ot hot hnz] at hzero; exact hnz hzero
  have hpre_not0 := pre_xor_zero hw0 hpre_vals hpre_cv hot hpre_ot0
  have hcv_eq : st.core.cur_vars = st_pre.core.cur_vars := by rw [h.same_core]
  have hmx : st_pre.core.cur_vars ≤ c.max_vars := hcv_eq ▸ h.len_ok.core_ok.cur_vars_le
  have hbv_ot : (BitVec.ofNat 32 ot).toNat = ot := ft_bv32_ofNat_eq (c := c) (by omega)
  have hv_len := h.len_ok.core_ok.vals_len; have htrl_len := h.len_ok.core_ok.trl_len
  have hmiss : ∀ i, saved ≤ i → i < te → (st.core.trl[i]?.getD 0#32).toNat / 2 ≠ ot / 2 := by
    intro i hi1 hi2 heq; obtain ⟨lit, hget, _, _, hv1, hvff, _⟩ := h.bfs_trl_inv i hi1 hi2
    simp [hget] at heq; rcases (litVar_eq_iff _ _).mp heq with hl | hl
    · rw [hl, hzero] at hv1; cases hv1
    · change lit.toNat = ot ^^^ 1 at hl
      rw [show lit.toNat ^^^ 1 = ot by rw [hl]; exact litNeg_litNeg ot, hzero] at hvff; cases hvff
  refine ⟨hte_lt, {
    len_ok := ⟨{ h.len_ok.core_ok with
      vals_len := by simp [st', vals2, hv_len], trl_len := by simp [st', trl1, htrl_len]
      trail_end_le := by simp [st']; omega
      propagated_le := by simp [st']; have := h.len_ok.core_ok.propagated_le; omega },
      h.len_ok.scratch_ok⟩
    same_core := by dsimp only [st']; rw [h.same_core], same_scratch := h.same_scratch
    saved_eq := h.saved_eq, saved_le_te := by simp [st']; have := h.saved_le_te; omega
    trl_pres := fun i hi =>
      (List.getElem?_set_ne (by have := h.saved_le_te; omega)).trans (h.trl_pres i hi)
    vals_pres := fun l hl hnz => by
      rw [show st'.core.vals[l]?.getD 0#8 = st.core.vals[l]?.getD 0#8 from getD_set2_ne
        (fun e => hnz (e ▸ hpre_ot0)) (fun e => hnz (e ▸ hpre_not0))]; exact h.vals_pres l hl hnz
    vals_hi_pres := fun l hl => ((List.getElem?_set_ne (by omega)).trans
      (List.getElem?_set_ne (by omega))).trans (h.vals_hi_pres l hl)
    bfs_trl_inv := fun i hi1 hi2 => by
      by_cases hit : i = te
      · subst hit
        have hv1 : vals2[ot]?.getD 0#8 = 1#8 := by
          rw [List.getElem?_set_ne hnot_ne.symm, List.getElem?_set_self (by rw [hv_len]; omega)]
          rfl
        have hvff : vals2[ot ^^^ 1]?.getD 0#8 = 0xFF#8 := by
          rw [List.getElem?_set_self (by rw [List.length_set, hv_len]; omega)]; rfl
        refine ⟨BitVec.ofNat 32 ot, List.getElem?_set_self (by rw [htrl_len]; omega),
          hbv_ot.symm ▸ hot, hbv_ot.symm ▸ hpre_ot0, hbv_ot.symm ▸ hv1, hbv_ot.symm ▸ hvff,
          hbv_ot.symm ▸ hent⟩
      · have hi2' : i < te := by simp [st'] at hi2; omega
        obtain ⟨lit, hget, hlt, hp0, hv1, hvff, he⟩ := h.bfs_trl_inv i hi1 hi2'
        obtain ⟨hne1, hne2, hne3, hne4⟩ := var_ne_xor_pair (by simpa [hget] using hmiss i hi1 hi2')
        exact ⟨lit, (List.getElem?_set_ne (Ne.symm hit)).trans hget, hlt, hp0,
          by change vals2[lit.toNat]?.getD 0#8 = 1#8; rwa [getD_set2_ne hne1 hne2],
          by change vals2[lit.toNat ^^^ 1]?.getD 0#8 = 0xFF#8; rwa [getD_set2_ne hne3 hne4], he⟩
    bfs_vars_nodup := fun i j hi1 hij hj2 => by
      have hj' : j ≤ te := by simp [st'] at hj2; omega
      have hg1 : (st'.core.trl[i]?.getD 0#32).toNat = (st.core.trl[i]?.getD 0#32).toNat := by
        change (trl1[i]?.getD 0#32).toNat = _; rw [List.getElem?_set_ne (by omega)]
      by_cases hje : j = te
      · subst hje; have hg2 : (st'.core.trl[te]?.getD 0#32).toNat = ot := by
          change (trl1[te]?.getD 0#32).toNat = ot
          rw [List.getElem?_set_self (by rw [htrl_len]; omega)]; exact hbv_ot
        rw [hg1, hg2]; exact hmiss i hi1 hij
      · have hg2 : (st'.core.trl[j]?.getD 0#32).toNat = (st.core.trl[j]?.getD 0#32).toNat := by
          change (trl1[j]?.getD 0#32).toNat = _; rw [List.getElem?_set_ne (Ne.symm hje)]
        rw [hg1, hg2]; exact h.bfs_vars_nodup i j hi1 hij (by omega)
    vals_only_trl := fun l hl hpre0 hcur => by
      by_cases hmem : l = ot ∨ l = ot ^^^ 1
      · have hg : (st'.core.trl[te]?.getD 0#32).toNat = ot := by
          change (trl1[te]?.getD 0#32).toNat = ot
          rw [List.getElem?_set_self (by rw [htrl_len]; omega)]; exact hbv_ot
        exact ⟨te, h.saved_le_te, by simp [st'], by rw [hg]; exact Or.imp Eq.symm Eq.symm hmem⟩
      · simp only [not_or] at hmem; rw [show st'.core.vals[l]?.getD 0#8 =
          st.core.vals[l]?.getD 0#8 from getD_set2_ne hmem.1 hmem.2] at hcur
        obtain ⟨i, hi1, hi2, hw⟩ := h.vals_only_trl l hl hpre0 hcur
        have hg : (st'.core.trl[i]?.getD 0#32).toNat = (st.core.trl[i]?.getD 0#32).toNat := by
          change (trl1[i]?.getD 0#32).toNat = _; rw [List.getElem?_set_ne (by omega)]
        exact ⟨i, hi1, by simp [st']; omega, by rwa [hg]⟩ }⟩
theorem TransUnrollInv.entails_src_of_falsified {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s0 st_pre st : FullState} {src saved ot : Nat}
    (hw0 : FullWitnessInv c F0 F_cur s0.core) (hpre_vals : st_pre.core.vals = s0.core.vals)
    (hpre_cv : st_pre.core.cur_vars = s0.core.cur_vars) (hcl0 : s0.core.cur_level = 0)
    (h : TransUnrollInv c F0 F_cur s0 st_pre src saved st) (hot : ot < 2 * st_pre.core.cur_vars)
    (hfals : st.core.vals[ot]?.getD 0#8 = 0xFF#8)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause [src, ot])) :
    (cnfOfClauses F_cur).EntailsClause (cnfClause [src]) := by
  by_cases hp0 : st_pre.core.vals[ot]?.getD 0#8 = 0#8
  · obtain ⟨i, hi1, hi2, hmem⟩ := h.vals_only_trl ot hot hp0 (by rw [hfals]; decide)
    obtain ⟨lit, hget, _, _, hv1, _, hent_lit⟩ := h.bfs_trl_inv i hi1 hi2
    simp [hget] at hmem; rcases hmem with rfl | hneg
    · rw [hfals] at hv1; cases hv1
    · rw [show lit.toNat = ot ^^^ 1 by rw [← hneg]; exact (litNeg_litNeg _).symm] at hent_lit
      exact entails_pair_collapse hent hent_lit
  · have hpre_ff : s0.core.vals[ot]?.getD 0#8 = 0xFF#8 := by
      rw [← hpre_vals, ← h.vals_pres ot hot hp0, hfals]
    obtain ⟨i, hi, heq⟩ := (hw0.vals_false_iff ot (hpre_cv ▸ hot)).mp hpre_ff
    have hs := hw0.level0_sound i hi (by have := hw0.lvl_le i hi; omega); rw [heq] at hs
    exact entails_unit_resolve_pair hent hs
theorem TransUnrollInv.unroll_step {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 st_pre st : FullState} {src saved : Nat} (hw0 : FullWitnessInv c F0 F_cur s0.core)
    (hpre_vals : st_pre.core.vals = s0.core.vals)
    (hpre_cv : st_pre.core.cur_vars = s0.core.cur_vars)
    (hlen_pre : st_pre.LengthsOk c) (h : TransUnrollInv c F0 F_cur s0 st_pre src saved st)
    (hgt : saved < st.core.trail_end) :
    let te' := st.core.trail_end - 1
    ∃ ul : BitVec 32, st.core.trl[te']? = some ul ∧ ul.toNat < 2 * st_pre.core.cur_vars ∧
      let vals2 := (st.core.vals.set ul.toNat 0#8).set (ul.toNat ^^^ 1) 0#8
      let st' := { st with core := { st.core with vals := vals2, trail_end := te' } }
      TransUnrollInv c F0 F_cur s0 st_pre src saved st' := by
  intro te'; obtain ⟨ul, hget, hult, hp0, _, _, _⟩ := h.bfs_trl_inv te' (by omega) (by omega)
  refine ⟨ul, hget, hult, ?_⟩; intro vals2 st'; have hnot_lt := litNeg_lt_two_mul hult
  have hpre_not0 := pre_xor_zero hw0 hpre_vals hpre_cv hult hp0
  have hv_len := h.len_ok.core_ok.vals_len; have hmx := hlen_pre.core_ok.cur_vars_le
  have hmiss : ∀ i, saved ≤ i → i < te' →
      (st.core.trl[i]?.getD 0#32).toNat / 2 ≠ ul.toNat / 2 := fun i hi1 hi2 heq => by
    have hnd := h.bfs_vars_nodup i te' hi1 hi2 (by omega); simp [hget] at hnd; exact hnd heq
  exact {
    len_ok := ⟨{ h.len_ok.core_ok with
      vals_len := by simp [st', vals2, hv_len]
      trail_end_le := by simp [st']; have := h.len_ok.core_ok.trail_end_le; omega
      propagated_le := by
        simp only [st'] at *; rw [h.same_core]; dsimp only
        have : st_pre.core.propagated ≤ saved := h.saved_eq ▸ hlen_pre.core_ok.propagated_le
        omega }, h.len_ok.scratch_ok⟩
    same_core := by dsimp only [st']; rw [h.same_core]
    same_scratch := h.same_scratch, saved_eq := h.saved_eq, saved_le_te := by simp [st']; omega
    trl_pres := h.trl_pres, vals_pres := fun l hl hnz => by
      rw [show st'.core.vals[l]?.getD 0#8 = st.core.vals[l]?.getD 0#8 from
        getD_set2_ne (fun he => hnz (he ▸ hp0)) (fun he => hnz (he ▸ hpre_not0))]
      exact h.vals_pres l hl hnz
    vals_hi_pres := fun l hl =>
      ((List.getElem?_set_ne (by omega)).trans (List.getElem?_set_ne (by omega))).trans
        (h.vals_hi_pres l hl)
    bfs_trl_inv := fun i hi1 hi2 => by
      have hi2' : i < te' := by simp [st'] at hi2; exact hi2
      obtain ⟨lit, hgl, hll, hpl, hv1, hvff, he⟩ := h.bfs_trl_inv i hi1 (by omega)
      have hlit : (st.core.trl[i]?.getD 0#32).toNat = lit.toNat := by simp [hgl]
      obtain ⟨hne1, hne2, hne3, hne4⟩ := var_ne_xor_pair (hlit ▸ hmiss i hi1 hi2')
      exact ⟨lit, hgl, hll, hpl,
        by change vals2[lit.toNat]?.getD 0#8 = 1#8; rwa [getD_set2_ne hne1 hne2],
        by change vals2[lit.toNat ^^^ 1]?.getD 0#8 = 0xFF#8; rwa [getD_set2_ne hne3 hne4], he⟩
    bfs_vars_nodup := fun i j hi1 hij hj2 =>
      h.bfs_vars_nodup i j hi1 hij (by simp [st'] at hj2; omega)
    vals_only_trl := fun l hl hpre0 hcur => by
      have hne_ul : ul.toNat ≠ ul.toNat ^^^ 1 := (litNeg_ne_self ul.toNat).symm
      have hmem : l ≠ ul.toNat ∧ l ≠ ul.toNat ^^^ 1 := by
        constructor <;> rintro rfl
        · exact hcur (by rw [List.getElem?_set_ne hne_ul.symm,
            List.getElem?_set_self (by rw [hv_len]; omega)]; rfl)
        · exact hcur (by rw [List.getElem?_set_self (by rw [List.length_set, hv_len]; omega)]; rfl)
      rw [show st'.core.vals[l]?.getD 0#8 = st.core.vals[l]?.getD 0#8 from
        getD_set2_ne hmem.1 hmem.2] at hcur
      obtain ⟨i, hi1, hi2, hw⟩ := h.vals_only_trl l hl hpre0 hcur; have hne : i ≠ te' := by
        rintro rfl; simp [hget] at hw
        exact hw.elim (fun e => hmem.1 e.symm) (fun e => hmem.2 e.symm)
      exact ⟨i, hi1, by simp [st']; omega, hw⟩ }
theorem TransUnrollInv.done {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 st_pre st : FullState} {src off p end_v reduced saved : Nat}
    (ho : TransOuterInv c F0 F_cur s0 src off p end_v reduced st_pre)
    (h : TransUnrollInv c F0 F_cur s0 st_pre src saved st) (hte : st.core.trail_end = saved) :
    TransOuterInv c F0 F_cur s0 src off p end_v reduced st := by
  have hvals_eq : st.core.vals = st_pre.core.vals := List.ext_getElem? fun l => by
    by_cases hl : l < 2 * st_pre.core.cur_vars
    · have hl1 : l < st.core.vals.length := by
        rw [h.len_ok.core_ok.vals_len]; have := ho.base.len_ok.core_ok.cur_vars_le; omega
      have hl2 : l < st_pre.core.vals.length := by
        rw [ho.base.len_ok.core_ok.vals_len]; have := ho.base.len_ok.core_ok.cur_vars_le; omega
      have hgd : st.core.vals[l]?.getD 0#8 = st_pre.core.vals[l]?.getD 0#8 := by
        by_cases h0 : st_pre.core.vals[l]?.getD 0#8 = 0#8
        · rw [h0]; exact Classical.byContradiction fun hnz => by
            obtain ⟨i, _, _, _⟩ := h.vals_only_trl l hl h0 hnz; omega
        · exact h.vals_pres l hl h0
      rw [List.getElem?_eq_getElem hl1, List.getElem?_eq_getElem hl2] at hgd ⊢
      exact congrArg some hgd
    · exact h.vals_hi_pres l (by omega)
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17⟩ :=
    ho.base.core_pres
  have hc_eq : st.core = { st_pre.core with trl := st.core.trl } := by
    rw [h.same_core, hvals_eq, hte, h.saved_eq]
  have hrefs : ∀ r ∈ fullArenaClauseRefsCore st_pre.core, r ∈ fullArenaClauseRefsCore st.core :=
    fun r hr => by unfold fullArenaClauseRefsCore at hr ⊢; rwa [hc_eq]
  exact {
    base := {
      len_ok := h.len_ok, scratch_pres := by rw [h.same_scratch]; exact ho.base.scratch_pres
      core_pres := by
        rw [hc_eq]; exact ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15,
          fun i hi => by rw [← hc_eq, h.trl_pres i (h.saved_eq ▸ c15 ▸ hi)]; exact c16 i hi, c17⟩
      off_le_end := ho.base.off_le_end, src_off := by rw [hc_eq]; exact ho.base.src_off
      src_sz := by rw [hc_eq]; exact ho.base.src_sz
      end_le_wlen := by rw [hc_eq]; exact ho.base.end_le_wlen, off_pos := ho.base.off_pos
      other_bounds := fun l hl hls => by rw [hc_eq] at hl ⊢; exact ho.base.other_bounds l hl hls
      other_pos_off := fun l hl hls p => by
        rw [hc_eq] at hl p ⊢; exact ho.base.other_pos_off l hl hls p
      disjoint_all := fun a b ha hb ne pa pb => by
        rw [hc_eq] at ha hb pa pb ⊢; exact ho.base.disjoint_all a b ha hb ne pa pb
      other_no_sent := fun l hl hls i hi => by
        rw [hc_eq] at hl hi ⊢; exact ho.base.other_no_sent l hl hls i hi
      other_slices := fun l hl hls => by
        rw [hc_eq] at hl ⊢; exact WatchSliceOk.relocate_same (k := st_pre.core) (Nat.le_refl _)
          (fun _ h => h) (fun _ _ => rfl) (ho.base.other_slices l hl hls) }
    off_le_p := ho.off_le_p, p_le_end := ho.p_le_end, red_le := ho.red_le
    src_pref := TombWatchSliceOk.mono (k := st_pre.core) (k' := st.core)
      (by rw [hc_eq]; exact Nat.le_refl _) hrefs (fun _ _ _ => by rw [hc_eq]) ho.src_pref
    src_rem := WatchSliceOk.relocate_same (k := st_pre.core) (k' := st.core)
      (by rw [hc_eq]; exact Nat.le_refl _) hrefs (fun _ _ => by rw [hc_eq]) ho.src_rem }
end TransBfsInvariants
/-! ## 2. Local `trans_lit` and `transitive` wrappers -/
section TransitiveWrappers
theorem TransUnrollInv.watch_slice {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 st_pre st : FullState} {src off p end_v reduced saved nl : Nat}
    (ho : TransOuterInv c F0 F_cur s0 src off p end_v reduced st_pre)
    (hu : TransUnrollInv c F0 F_cur s0 st_pre src saved st) (hnl : nl < 2 * st.core.cur_vars) :
    fullWatchOffCore st.core nl + fullWatchSizeCore st.core nl ≤ st.core.wlen ∧ ∃ nt,
      TombWatchSliceOk F_cur st.core nl
        (fullWatchOffCore st.core nl) (fullWatchSizeCore st.core nl) nt := by
  have hsc := hu.same_core; have hcv : st.core.cur_vars = st_pre.core.cur_vars := by rw [hsc]
  have hws : st.core.wstk = st_pre.core.wstk := by rw [hsc]
  have hrefs : ∀ r ∈ fullArenaClauseRefsCore st_pre.core, r ∈ fullArenaClauseRefsCore st.core :=
    fun r hr => by unfold fullArenaClauseRefsCore at hr ⊢; rwa [hsc]
  rw [show fullWatchOffCore st.core nl = fullWatchOffCore st_pre.core nl by
      unfold fullWatchOffCore; rw [hsc], show fullWatchSizeCore st.core nl =
      fullWatchSizeCore st_pre.core nl by unfold fullWatchSizeCore; rw [hsc],
    show st.core.wlen = st_pre.core.wlen by rw [hsc]]
  by_cases hns : nl = src
  · subst hns; rw [ho.base.src_off, ho.base.src_sz]; exact ⟨by
      have := ho.base.off_le_end; have := ho.base.end_le_wlen; omega, reduced,
      TombWatchSliceOk.mono (by omega) hrefs (fun _ _ _ => by rw [hws]) ho.src_full_tomb⟩
  · exact ⟨ho.base.other_bounds nl (hcv ▸ hnl) hns, 0, TombWatchSliceOk.of_watchSlice
      (WatchSliceOk.relocate_same (p' := fullWatchOffCore st_pre.core nl) (by omega) hrefs
        (fun _ _ => by rw [hws]) (ho.base.other_slices nl (hcv ▸ hnl) hns))⟩
private theorem TombWatchSliceOk.step_non_large {F_cur : List (List Nat)} {k : FullCoreState}
    {nl q lend nt : Nat} {qw : BitVec 32} (hq : q < lend) (hg : k.wstk[q]? = some qw)
    (hfl : (qw &&& 0x80000000#32) ≠ 0#32) (ht : TombWatchSliceOk F_cur k nl q (lend - q) nt) :
    ∃ nt2, TombWatchSliceOk F_cur k nl (q + 1) (lend - (q + 1)) nt2 := by
  have hs := ht.inv_step (by omega) hg; simp only [hfl, ↓reduceIte] at hs
  by_cases hq_t : qw = 0xFFFFFFFF#32 <;> simp only [hq_t, ↓reduceIte] at hs
  · exact ⟨nt - 1, by have hs2 := hs.2; rwa [show lend - q - 1 = lend - (q + 1) by omega] at hs2⟩
  · exact ⟨nt, by have hs3 := hs.2.2; rwa [show lend - q - 1 = lend - (q + 1) by omega] at hs3⟩
private theorem trans_vals_ff_of_domain {v : BitVec 8} {z : BitVec 32}
    (hdom : v = 0#8 ∨ v = 1#8 ∨ v = 0xFF#8) (hz : z = 0#32)
    (hslt : (v.signExtend 32).slt z = true) : v = 0xFF#8 := by
  subst hz; rcases hdom with rfl | rfl | rfl <;> first | rfl | exact absurd hslt (by decide)
private theorem trans_vals_zero_of_domain {v : BitVec 8} {z : BitVec 32}
    (hdom : v = 0#8 ∨ v = 1#8 ∨ v = 0xFF#8) (hz : z = 0#32) (heq : v.signExtend 32 = z) :
    v = 0#8 := by
  subst hz; rcases hdom with rfl | rfl | rfl <;> first | rfl | exact absurd heq (by decide)
private theorem TransOuterInv.of_reduced0_full {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s0 : FullState} {src off p end_v : Nat} {st : FullState}
    (hsp0 : FullSparseInv c F0 s0) (hw0 : FullWitnessInv c F0 F_cur s0.core)
    (h : TransOuterInv c F0 F_cur s0 src off p end_v 0 st) :
    FullSparseInv c F0 st ∧ FullWitnessInv c F0 F_cur st.core :=
  have hcl : WatchSliceOk F_cur st.core src
      (fullWatchOffCore st.core src) (fullWatchSizeCore st.core src) := by
    rw [h.base.src_off, h.base.src_sz]; exact h.src_full_tomb.to_watchSlice
  ⟨h.base.toSparse hsp0 hw0 hcl, h.base.toWitness_of_src_clean hw0 hcl⟩
private theorem TransOuterInv.del_side_and_tomb {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s0 : FullState} {src off p end_v reduced dst : Nat}
    {st_r st' : FullState} {w0 : BitVec 32} {wvec' wstk' : List (BitVec 32)} {wu' tc' : BitVec 64}
    (hto : TransOuterInv c F0 F_cur s0 src off p end_v reduced st_r) (hp_lt : p < end_v)
    (hp_wc : p < c.wcap) (hs_lt : src < 2 * st_r.core.cur_vars)
    (hd_lt : dst < 2 * st_r.core.cur_vars) (hd_ne : dst ≠ src) (hget : st_r.core.wstk[p]? = some w0)
    (hfl : (w0 &&& 0x80000000#32) ≠ 0#32) (hst' : st' = { st_r with
      core := { st_r.core with wvec := wvec', wstk := wstk', wusable := wu' } })
    (hl' : st'.LengthsOk c) (hws : fullWatchOff st' dst = fullWatchOff st_r dst ∧
      fullWatchSize st' dst ≤ fullWatchSize st_r dst)
    (hows : ∀ l < 2 * st_r.core.cur_vars, l ≠ dst →
      fullWatchOff st' l = fullWatchOff st_r l ∧ fullWatchSize st' l = fullWatchSize st_r l)
    (hout : ∀ i < c.wcap, (i < fullWatchOff st_r dst ∨
      fullWatchOff st_r dst + fullWatchSize st_r dst ≤ i) → wstk'[i]? = st_r.core.wstk[i]?)
    (hsl : WatchSliceOk F_cur st_r.core dst (fullWatchOff st_r dst) (fullWatchSize st_r dst) →
      WatchSliceOk F_cur st'.core dst (fullWatchOff st' dst) (fullWatchSize st' dst)) :
    TransOuterInv c F0 F_cur s0 src off (p + 1) end_v (reduced + 1) { st' with
      core := { st'.core with wstk := wstk'.set p 0xFFFFFFFF#32 },
      scratch := { st_r.scratch with trans_cnt := tc' } } := by
  subst hst'
  have hp_out : p < fullWatchOff st_r dst ∨ fullWatchOff st_r dst + fullWatchSize st_r dst ≤ p := by
    by_cases hdz : fullWatchSize st_r dst = 0; · dsimp only [fullWatchSize] at hdz ⊢; omega
    rcases hto.base.disjoint_all src dst hs_lt hd_lt hd_ne.symm
        (by rw [hto.base.src_sz]; have := hto.off_le_p; omega) (Nat.pos_of_ne_zero hdz) with
      h1 | h2
    · left; have := hto.base.src_off; have := hto.base.src_sz; dsimp only [fullWatchOff]; omega
    · right; have := hto.off_le_p; have := hto.base.src_off
      dsimp only [fullWatchOff, fullWatchSize]; omega
  exact (hto.of_delete_bin_side hs_lt hd_lt hd_ne rfl hl' hws hows hout hsl).mark_tomb
    hp_lt hs_lt ((hout p hp_wc hp_out).trans hget) hfl
private theorem ft_bnds {c : FullCfg} {k : FullCoreState} (hl : k.LengthsOk c) :
    2 * k.cur_vars + 1 < 2 ^ 30 ∧ k.wlen ≤ c.wcap ∧ k.wlen < 2 ^ 64 ∧ k.trail_end < 2 ^ 64 := by
  have := hl.cur_vars_le; have := hl.wlen_le; have := hl.trail_end_le
  have := c.hmaxv; have := c.hwcap; unfold dimacsBound at *; omega
private theorem ft_wstk_lt {c : FullCfg} {k : FullCoreState} {p end_v : Nat}
    (hl : FullCoreState.LengthsOk c k) (hp : p < end_v) (he : end_v ≤ k.wlen) :
    p < k.wstk.length := by rw [hl.wstk_len_arr]; have := hl.wlen_le; omega
private theorem ft_vals_lt {c : FullCfg} {k : FullCoreState} {l : Nat}
    (hl : FullCoreState.LengthsOk c k) (h : l < 2 * k.cur_vars) :
    l < k.vals.length := by rw [hl.vals_len]; have := hl.cur_vars_le; omega
private theorem ft_getElem_toNat {xs : List (BitVec 32)} {i : Nat} (hi : i < xs.length) :
    (xs[i]'hi).toNat = (xs[i]?.getD 0#32).toNat := by simp [List.getElem?_eq_getElem hi]
private theorem ft_bv32_ofNat_toNat (x : BitVec 32) : BitVec.ofNat 32 x.toNat = x := by simp
private theorem ft_bv64_sub_sz (a b r : BitVec 64) {bn rn : Nat}
    (hb : b.toNat = bn) (hr : r.toNat = rn) (h : rn ≤ bn) (hbn : bn < 2 ^ 32) :
    BitVec.setWidth 32 (a + b - a - r) = BitVec.ofNat 32 (bn - rn) := by
  apply BitVec.eq_of_toNat_eq; have : (a + b - a - r).toNat = bn - rn := by bv_omega
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, this, Nat.mod_eq_of_lt (by omega)]
private theorem ft_bv64_sub1' {n : Nat} (hn1 : 0 < n) (hn2 : n < 2 ^ 64) :
    (BitVec.ofNat 64 n - 1#64).toNat = n - 1 := by bv_omega
private theorem ft_bv64_lt_eq {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a < BitVec.ofNat 64 b) ↔ a < b := by bv_omega
private theorem ft_compact_done_eq {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 : FullState} {src off end_v reduced : Nat} {wu' nb_bv : BitVec 64} {idx : Nat}
    {new_sz : BitVec 32} {st : FullState} (hsp0 : FullSparseInv c F0 s0)
    (hw0 : FullWitnessInv c F0 F_cur s0.core) (hb : TransOuterBase c F0 F_cur s0 src off end_v st)
    (hsrc_lt : src < 2 * st.core.cur_vars) (hred : reduced ≤ end_v - off)
    (hsl : WatchSliceOk F_cur st.core src off (end_v - off - reduced)) (hidx : idx = 2 * src + 1)
    (hsz : new_sz = BitVec.ofNat 32 (end_v - off - reduced)) :
    let st' := { st with core :=
      { st.core with wvec := st.core.wvec.set idx new_sz, wusable := wu', num_binary := nb_bv } }
    FullSparseInv c F0 st' ∧ FullWitnessInv c F0 F_cur st'.core := by
  subst hidx; subst hsz; have hnb : ((nb_bv.toNat : Nat) : BitVec 64) = nb_bv := by simp
  simpa only [hnb] using
    hb.of_compact_done_full hsp0 hw0 hsrc_lt hred hsl (wu' := wu') (nb' := nb_bv.toNat)
private theorem ft_unroll_c0_aux {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 st_pre st_r : FullState} {src saved : Nat} (hw0 : FullWitnessInv c F0 F_cur s0.core)
    (hpre_vals : st_pre.core.vals = s0.core.vals)
    (hpre_cv : st_pre.core.cur_vars = s0.core.cur_vars)
    (hlen_pre : st_pre.LengthsOk c) (hu_r : TransUnrollInv c F0 F_cur s0 st_pre src saved st_r)
    (hte_gt : saved < st_r.core.trail_end) (hte_r_lt : st_r.core.trail_end < 2 ^ 64) :
    let idx := (BitVec.ofNat 64 (BitVec.ofNat 64 st_r.core.trail_end - 1#64).toNat).toNat
    ∃ hidx : idx < st_r.core.trl.length, let ul := st_r.core.trl[idx]'hidx
      (BitVec.setWidth 64 ul).toNat < st_r.core.vals.length ∧
      (BitVec.setWidth 64 (ul ^^^ 1#32)).toNat < st_r.core.vals.length ∧
      (BitVec.ofNat 64 st_r.core.trail_end - 1#64).toNat = st_r.core.trail_end - 1 ∧
      TransUnrollInv c F0 F_cur s0 st_pre src saved { st_r with core := { st_r.core with
        vals := (st_r.core.vals.set (BitVec.setWidth 64 ul).toNat 0#8).set
          (BitVec.setWidth 64 (ul ^^^ 1#32)).toNat 0#8,
        trail_end := (BitVec.ofNat 64 st_r.core.trail_end - 1#64).toNat } } := by
  have hlen_r := hu_r.len_ok
  obtain ⟨ul, hul_get, hul_lt, hu_r'⟩ := hu_r.unroll_step hw0 hpre_vals hpre_cv hlen_pre hte_gt
  have hcv_r : st_pre.core.cur_vars ≤ c.max_vars := by
    have := hlen_r.core_ok.cur_vars_le; rw [hu_r.same_core] at this; exact this
  have hte1_bv := ft_bv64_sub1' (n := st_r.core.trail_end) (by omega) hte_r_lt
  have hul_vlen := ft_vals_lt (l := ul.toNat) hlen_r.core_ok (by rw [hu_r.same_core]; exact hul_lt)
  have huln_vlen := ft_vals_lt (l := (ul ^^^ 1#32).toNat) hlen_r.core_ok
    (by rw [ft_bv32_xor1, hu_r.same_core]; exact litNeg_lt_two_mul hul_lt)
  have hte1_len : (BitVec.ofNat 64 st_r.core.trail_end - 1#64).toNat < st_r.core.trl.length := by
    rw [hte1_bv, hlen_r.core_ok.trl_len]
    have := hlen_r.core_ok.trail_end_le; have := hlen_r.core_ok.cur_vars_le; omega
  have hte1_bv_len : (BitVec.ofNat 64 (BitVec.ofNat 64 st_r.core.trail_end - 1#64).toNat).toNat <
      st_r.core.trl.length := by simpa using hte1_len
  have hul_ge2 : st_r.core.trl[(BitVec.ofNat 64
      (BitVec.ofNat 64 st_r.core.trail_end - 1#64).toNat).toNat]'hte1_bv_len = ul := by
    simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (BitVec.isLt _)] using
      Option.some.inj ((List.getElem?_eq_getElem hte1_len).symm.trans (by rw [hte1_bv, hul_get]))
  exact ⟨hte1_bv_len, by rw [hul_ge2, ft_bv32_setWidth64]; exact hul_vlen,
    by rw [hul_ge2, ft_bv32_setWidth64]; exact huln_vlen, hte1_bv,
    by rw [hul_ge2, ft_bv32_setWidth64, ft_bv32_setWidth64, hte1_bv, ft_bv32_xor1]; exact hu_r'⟩
end TransitiveWrappers
end FullTransHelpers
/-! ## 3. Main `Func.wp` proofs (`full_trans_lit` and `full_transitive`) -/
section MainWpProofs
theorem full_trans_lit_wp (Γ : Env)
    (h_del_bin : ∀ args m Q X,
      fullDeleteBinSideSpec args m Q X → Γ "full_delete_bin_side" [i64, i32, i32] [] args m Q X)
    (h_add_unit : ∀ args m Q X,
      fullAddUnitSpec args m Q X → Γ "full_add_unit" [i64, i32] [.bool] args m Q X) :
    ∀ args m Q X, fullTransLitSpec args m Q X → Func.wp Γ full_trans_lit_body args m Q X := by
  rintro ⟨h, src, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hsp, hcl0, hsrc_lt, hm, hQ⟩
  unfold full_trans_lit_body; ft_unmdata
  obtain ⟨F_cur, hw0⟩ := hsp.1.witness; have hlen0 := hsp.1.lengths
  have hsrc_vlen := ft_vals_lt hlen0.core_ok hsrc_lt
  ft_split; · ft_steps; exact hQ true s m hsp hcl0 rfl rfl (fun hf => absurd hf (by decide)) hm
  have hsrc0 : s.core.vals[src.toNat]?.getD 0#8 = 0#8 := trans_vals_zero_of_domain (z := 0#32)
    (hw0.vals_domain src.toNat hsrc_lt) rfl (by simpa [List.getElem?_eq_getElem hsrc_vlen] using
      ‹BitVec.signExtend 32 s.core.vals[BitVec.toNat src] = 0#32›)
  have hcv_lt : 2 * s.core.cur_vars < 2 ^ 32 := by have := (ft_bnds hlen0.core_ok).1; omega
  have hsrc64 : (src.setWidth 64 <<< (1 : Nat)).toNat = 2 * src.toNat := by
    rw [ft_bv64_shl1 (by rw [ft_bv32_setWidth64]; omega), ft_bv32_setWidth64]
  have hsrc64_1 : ((src.setWidth 64 <<< (1 : Nat)) + 1#64).toNat = 2 * src.toNat + 1 := by
    rw [ft_bv64_add1 (by rw [hsrc64]; omega), hsrc64]
  let off := fullWatchOff s src.toNat; let sz := fullWatchSize s src.toNat; let end_v := off + sz
  have hws_b : end_v ≤ s.core.wlen := by
    have hwm := hw0.watches; unfold ModeWatchesInv at hwm
    simp only [hsp.2.2.2.2, ↓reduceIte] at hwm; exact hwm.layout.bounds src.toNat hsrc_lt
  have hwv_b : 2 * src.toNat + 1 < s.core.wvec.length := by
    rw [hlen0.core_ok.wvec_len]; have := hlen0.core_ok.cur_vars_le; omega
  have hwc_lt : c.wcap < 2 ^ 64 := by have := c.hwcap; unfold dimacsBound at *; omega
  have hoff_lt : off < 2 ^ 32 := BitVec.isLt _; have hsz_lt : sz < 2 ^ 32 := BitVec.isLt _
  ft_split; · ft_steps; exact hQ true s m hsp hcl0 rfl rfl (fun hf => absurd hf (by decide)) hm
  have hmod1 : (2 * src.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 = 2 * src.toNat + 1 := by
    rw [show BitVec.toNat (1 : BitVec 64) = 1 from rfl, Nat.mod_eq_of_lt (by omega)]
  have hsz_pos : 0 < sz := by
    have hc0 : ¬BitVec.setWidth 64 (s.core.wvec[(2 * src.toNat + BitVec.toNat (1 : BitVec 64)) %
        2 ^ 64]'(by rw [hmod1]; exact hwv_b)) = 0 := ‹_›
    have hsz_eq : (s.core.wvec[(2 * src.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'
        (by rw [hmod1]; exact hwv_b)).toNat = sz := by
      simp only [hmod1]; exact ft_getElem_toNat hwv_b
    exact Nat.pos_of_ne_zero fun hz =>
      hc0 (BitVec.eq_of_toNat_eq (by rw [ft_bv32_setWidth64, hsz_eq, hz]; rfl))
  have hend_lt : end_v < 2 ^ 64 := by have := (ft_bnds hlen0.core_ok).2.1; omega
  ft_to_group; have hw0_b2 : 2 * src.toNat < s.core.wvec.length := by omega
  have hmod0 : 2 * src.toNat % 2 ^ 64 = 2 * src.toNat := Nat.mod_eq_of_lt (by omega)
  have h_end_c0 : ((s.core.wvec[2 * src.toNat % 2 ^ 64]'(by rw [hmod0]; exact hw0_b2)).toNat +
      (s.core.wvec[(2 * src.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'
        (by rw [hmod1]; exact hwv_b)).toNat) % 2 ^ 64 = end_v := by
    simp only [hmod0, hmod1, ft_getElem_toNat hw0_b2, ft_getElem_toNat hwv_b]
    exact Nat.mod_eq_of_lt hend_lt
  have hof64 : (BitVec.ofNat 64 off).toNat = off := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hw0_b : (BitVec.setWidth 64 src <<< (1 : Nat)).toNat < s.core.wvec.length := by
    rw [hsrc64]; exact hw0_b2
  have h_off_arg : BitVec.setWidth 64 (s.core.wvec[(BitVec.setWidth 64 src <<< (1 : Nat)).toNat]'
      hw0_b) = BitVec.ofNat 64 off := BitVec.eq_of_toNat_eq (by
    rw [ft_bv32_setWidth64, hof64]; simp only [hsrc64]; exact ft_getElem_toNat hw0_b2)
  refine wp_loop_group (ts := [Ty.bool, i64, i64])
    (Inv := fun n xs m' => let failed := xs.1; let reduced := xs.2.1; let p := xs.2.2.1
      ∃ st : FullState, off ≤ p.toNat ∧ p.toNat ≤ end_v ∧ n = end_v - p.toNat ∧
        reduced.toNat ≤ p.toNat - off ∧
        TransOuterInv c F0 F_cur s src.toNat off p.toNat end_v reduced.toNat st ∧
        (failed = true → (cnfOfClauses F_cur).EntailsClause (cnfClause [src.toNat])) ∧
        st.core.cur_vars = s.core.cur_vars ∧ st.core.fuel = s.core.fuel ∧
        (FullMem c st ⋆ R) m') ?_ ?_
  rotate_left
  · intro L hL; ft_steps; rw [h_off_arg]
    have hto0 := TransOuterInv.init hlen0 hw0 hsp.2.2.2.2 hcl0 hsrc_lt hsz_pos
    exact hL (end_v - off) (false, 0#64, BitVec.ofNat 64 off, ()) m ⟨s,
      (by dsimp only; rw [hof64]; exact Nat.le_refl _),
      (by dsimp only; rw [hof64]; exact Nat.le_add_right off sz), (by dsimp only; rw [hof64]),
      (by dsimp only; simp), (by dsimp only; rw [hof64]; exact hto0),
      (by dsimp only; intro h; cases h), rfl, rfl, hm⟩
  rintro L n ⟨failed, reduced, p, ⟨⟩⟩ m1 hL
    ⟨st, hp_lo, hp_hi, hneq, hred_le, hto, hfail_ent, hcv_st, hfuel_st, hm1⟩
  dsimp only at hp_lo hp_hi hneq hred_le hto hfail_ent; have hlen_st := hto.base.len_ok
  refine wp_join_group (P := fun _ m2 => ∃ st2 : FullState,
      TransOuterInv c F0 F_cur s src.toNat off p.toNat end_v reduced.toNat st2 ∧
      (failed = true → (cnfOfClauses F_cur).EntailsClause (cnfClause [src.toNat])) ∧
      st2.core.cur_vars = s.core.cur_vars ∧ st2.core.fuel = s.core.fuel ∧
      (FullMem c st2 ⋆ R) m2) ?_ ?_
  · intro J4 ⟨⟩ m2 ⟨st2, hto2, hfail2, hcv2, hfuel2, hm2⟩; have hlen2 := hto2.base.len_ok
    refine wp_join_group (P := fun _ m3 => ∃ stf : FullState, FullSparseInv c F0 stf ∧
        FullWitnessInv c F0 F_cur stf.core ∧ stf.core.cur_level = 0 ∧
        stf.core.cur_vars = s.core.cur_vars ∧ stf.core.fuel = s.core.fuel ∧
        (failed = true → (cnfOfClauses F_cur).EntailsClause (cnfClause [src.toNat])) ∧
        (FullMem c stf ⋆ R) m3) ?_ ?_
    · rintro J6 ⟨_, ⟨⟩⟩ m3 ⟨stf, hspf, hwf, hclf, hcvf, hfuelf, hfailf, hm3⟩
      have hlenf := hspf.1.lengths; ft_split; rotate_left
      · ft_steps; exact hQ true stf m3 hspf hclf hcvf hfuelf (fun h => absurd h (by decide)) hm3
      ft_to_group; ft_call h_add_unit
      obtain ⟨hsp_tc, hw_tc⟩ := fullSparseInv_with_trans_cnt hspf hwf (stf.scratch.trans_cnt + 1#64)
      refine ⟨c, F0, F_cur, _, R, rfl, hsp_tc.1.lengths, hw_tc, fun _ => hfailf ‹_›, ‹_›,
        fun ok vals' flags' lvl' rsns' trl' tp' te' prop' cl' unass' unfl' inc'
          phases' ta' ba' pt' pb' hp' ps' hl' qsi' qss' m4 hlen4 hw4 hcl4 huns4 _ hm4 => ?_⟩
      let st_au : FullState := { stf with
        core := { stf.core with
          vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl', trail_pos := tp',
          trail_end := te', propagated := prop', cur_level := cl', unassigned := unass',
          unflushed := unfl', inconsistent := inc' },
        scratch := { stf.scratch with
          trans_cnt := stf.scratch.trans_cnt + 1#64, phases := phases', target_assigned := ta',
          best_assigned := ba', phases_target := pt', phases_best := pb', heap := hp', pos := ps',
          heap_len := hl', q_search_idx := qsi', q_search_stamp := qss' } }
      exact hQ ok st_au m4 (fullAddUnit_sparse hsp_tc rfl hlen4 hw4) hcl4 hcvf hfuelf
        (fun hok => (huns4 (by dsimp only [Arg.val_var] at *; omega) hok).1) hm4
    intro J6 hJ6; ft_split; rotate_left
    · have hred0 : reduced.toNat = 0 := by bv_omega
      ft_steps; rw [hred0] at hto2; obtain ⟨hsp2, hw2⟩ := hto2.of_reduced0_full hsp hw0
      exact hJ6 (p, ()) m2 ⟨st2, hsp2, hw2, hto2.base.core_pres.2.1, hcv2, hfuel2, hfail2, hm2⟩
    ft_to_group; have hred_pos : 0 < reduced.toNat := by bv_omega
    refine wp_loop_group (ts := [i64, i64])
      (Inv := fun nc xs m3 => let pc := xs.1; let qc := xs.2.1
        ∃ stc : FullState, off ≤ qc.toNat ∧ qc.toNat ≤ pc.toNat ∧ pc.toNat ≤ end_v ∧
          nc = end_v - pc.toNat ∧
          TransCompactInv c F0 F_cur s src.toNat off qc.toNat pc.toNat end_v reduced.toNat stc ∧
          stc.core.cur_vars = s.core.cur_vars ∧ stc.core.fuel = s.core.fuel ∧
          (FullMem c stc ⋆ R) m3) ?_ ?_
    · rintro L8 nc ⟨pc, qc, ⟨⟩⟩ m3 hL8 ⟨stc, hql, hqp, hpe, hcneq, hci, hcvc, hfuelc, hm3⟩
      dsimp only at hql hqp hpe hcneq hci; have hlenc := hci.base.len_ok; ft_split
      · have hpc_lt : pc.toNat < end_v := by have := h_end_c0; omega
        have hpc_len := ft_wstk_lt hlenc.core_ok hpc_lt hci.base.end_le_wlen
        have hpc1 : (pc + 1#64).toNat = pc.toNat + 1 := ft_bv64_add1 (by omega); ft_split
        · have ht_pc : stc.core.wstk[pc.toNat]? = some 0xFFFFFFFF#32 := by
            rw [List.getElem?_eq_getElem hpc_len]; exact congrArg some ‹_›
          ft_steps; refine hL8 (end_v - (pc.toNat + 1)) (pc + 1#64, qc, ()) m3 (by omega)
            ⟨stc, hql, by dsimp only; rw [hpc1]; omega, by dsimp only; rw [hpc1]; omega,
              by dsimp only; rw [hpc1],
              by dsimp only; rw [hpc1]; exact hci.step_tomb hpc_lt ht_pc rfl, hcvc, hfuelc, hm3⟩
        have hsrc_c : src.toNat < 2 * stc.core.cur_vars := by rw [hcvc]; exact hsrc_lt
        ft_split
        · have hne_c : stc.core.wstk[pc.toNat] ≠ 0xFFFFFFFF#32 := ‹_›
          have hfl_c : (stc.core.wstk[pc.toNat] &&& 0x80000000#32) ≠ 0#32 := ‹_›
          have hqc1 : (qc + 1#64).toNat = qc.toNat + 1 := ft_bv64_add1 (by omega)
          have hci_b := hci.step_bin hpc_lt hsrc_c (List.getElem?_eq_getElem hpc_len) hne_c hfl_c
          rw [← hpc1, ← hqc1] at hci_b; ft_steps
          exact hL8 (end_v - (pc.toNat + 1)) (pc + 1#64, qc + 1#64, ()) _ (by omega)
            ⟨_, by dsimp only; rw [hqc1]; omega, by dsimp only; rw [hpc1, hqc1]; omega,
              by dsimp only; rw [hpc1]; omega, by dsimp only; rw [hpc1],
              hci_b, hcvc, hfuelc, by assumption⟩
        have hfl0 : (stc.core.wstk[pc.toNat] &&& 0x80000000#32) = 0#32 := ‹_›
        obtain ⟨hp1_lt, w1, hw1_get, hci_l⟩ :=
          hci.step_large hpc_lt hsrc_c (List.getElem?_eq_getElem hpc_len) hfl0
        ft_split; rotate_left
        · exact False.elim (‹¬((pc + 1#64).toNat < _)› (by rw [hpc1, h_end_c0]; exact hp1_lt))
        have hpc2 := ft_bv64_add2 (by omega : pc.toNat + 2 < 2 ^ 64)
        have hqc2 := ft_bv64_add2 (by omega : qc.toNat + 2 < 2 ^ 64)
        have hqc1 := ft_bv64_add1 (by omega : qc.toNat + 1 < 2 ^ 64)
        have hpc1_len := ft_wstk_lt (p := (pc + 1#64).toNat) hlenc.core_ok
          (by rw [hpc1]; exact hp1_lt) hci.base.end_le_wlen
        have hqc1_len := ft_wstk_lt (p := (qc + 1#64).toNat) hlenc.core_ok
          (by rw [hqc1]; exact Nat.lt_of_lt_of_le (by omega) hp1_lt) hci.base.end_le_wlen
        ft_steps
        have hw1_hm : (stc.core.wstk.set qc.toNat stc.core.wstk[pc.toNat])[(pc + 1#64).toNat]'(
            by rw [List.length_set]; exact hpc1_len) = w1 := by
          rw [List.getElem_set_ne (by omega : qc.toNat ≠ (pc + 1#64).toNat)]
          exact Option.some.inj
            ((List.getElem?_eq_getElem hpc1_len).symm.trans (by rw [hpc1, hw1_get]))
        rw [← hpc2, ← hqc2, ← hqc1, ← hw1_hm] at hci_l
        exact hL8 (end_v - (pc.toNat + 2)) (pc + 2#64, qc + 2#64, ()) _ (by omega)
          ⟨_, by dsimp only; rw [hqc2]; omega, by dsimp only; rw [hpc2, hqc2]; omega,
            by dsimp only; rw [hpc2]; omega, by dsimp only; rw [hpc2], hci_l, hcvc, hfuelc,
            by assumption⟩
      have hpc_end : pc.toNat = end_v := by have := h_end_c0; omega
      rw [hpc_end] at hci; obtain ⟨hq_eq, hq_lo, hq_hi, hsl⟩ := hci.at_end; ft_to_group
      refine wp_loop_group (ts := [i64])
        (Inv := fun nq xs m4 => let qf := xs.1
          ∃ stq : FullState, off ≤ end_v - reduced.toNat ∧ end_v - reduced.toNat ≤ qf.toNat ∧
            qf.toNat ≤ end_v ∧ nq = end_v - qf.toNat ∧
            TransOuterBase c F0 F_cur s src.toNat off end_v stq ∧
            WatchSliceOk F_cur stq.core src.toNat off (end_v - off - reduced.toNat) ∧
            stq.core.cur_vars = s.core.cur_vars ∧ stq.core.fuel = s.core.fuel ∧
            (FullMem c stq ⋆ R) m4) ?_ ?_
      rotate_left
      · intro L11 hL11; ft_steps; exact hL11 (end_v - qc.toNat) (qc, ()) m3 ⟨stc, hq_lo,
          by dsimp only; rw [hq_eq]; exact Nat.le_refl _,
          by dsimp only; rw [hq_eq]; exact hq_hi, rfl, hci.base, hsl, hcvc, hfuelc, hm3⟩
      rintro L11 nq ⟨qf, ⟨⟩⟩ m4 hL11 ⟨stq, hqo, hql2, hqh, hqneq, hbq, hslq, hcvq, hfuelq, hm4⟩
      dsimp only at hqo hql2 hqh hqneq hbq hslq; have hlenq := hbq.len_ok
      have hsrc_q : src.toNat < 2 * stq.core.cur_vars := by rw [hcvq]; exact hsrc_lt
      ft_split
      · have hq_lt : qf.toNat < end_v := by have := h_end_c0; omega
        have hqf_len := ft_wstk_lt hlenq.core_ok hq_lt hbq.end_le_wlen
        ft_steps; have hq1 : (qf + 1#64).toNat = qf.toNat + 1 := ft_bv64_add1 (by omega)
        obtain ⟨hbq', hslq'⟩ := hbq.sentinel_fill_step hsrc_q ⟨hqo, hql2, hq_lt⟩
          (by rwa [show (end_v - reduced.toNat) - off = end_v - off - reduced.toNat by omega])
        exact hL11 (end_v - (qf.toNat + 1)) (qf + 1#64, ()) _ (by omega) ⟨_, hqo,
          by dsimp only; rw [hq1]; omega, by dsimp only; rw [hq1]; omega, by dsimp only; rw [hq1],
          hbq', by simpa only [(show end_v - reduced.toNat - off =
            end_v - off - reduced.toNat by omega)] using hslq', hcvq, hfuelq, by assumption⟩
      have hred_off : reduced.toNat ≤ end_v - off := by omega
      have hw1_b : (BitVec.setWidth 64 src <<< (1 : Nat) + 1#64).toNat < s.core.wvec.length := by
        rw [hsrc64_1]; exact hwv_b
      have hq_wv1 : (BitVec.setWidth 64 src <<< 1 + 1#64).toNat < stq.core.wvec.length := by
        rw [hsrc64_1, hlenq.core_ok.wvec_len, ← hlen0.core_ok.wvec_len]; exact hwv_b
      have hclq : stq.core.cur_level = 0 := hbq.core_pres.2.1; have h_wsz_bv : BitVec.setWidth 32
          (BitVec.setWidth 64 (s.core.wvec[(BitVec.setWidth 64 src <<< (1 : Nat)).toNat]'hw0_b) +
            BitVec.setWidth 64 (s.core.wvec[(BitVec.setWidth 64 src <<< (1 : Nat) + 1#64).toNat]'
              hw1_b) - BitVec.setWidth 64
              (s.core.wvec[(BitVec.setWidth 64 src <<< (1 : Nat)).toNat]'hw0_b) - reduced) =
          BitVec.ofNat 32 (end_v - off - reduced.toNat) := by
        have hb : (BitVec.setWidth 64 (s.core.wvec[(BitVec.setWidth 64 src <<< (1 : Nat) +
            1#64).toNat]'hw1_b)).toNat = sz := by
          rw [ft_bv32_setWidth64]; simp only [hsrc64_1]; exact ft_getElem_toNat hwv_b
        rw [show end_v - off = sz from Nat.add_sub_cancel_left off sz]
        exact ft_bv64_sub_sz _ _ reduced hb rfl (by omega) (by omega)
      ft_split
      · ft_steps; obtain ⟨hsp_d, hw_d⟩ := ft_compact_done_eq hsp hw0 hbq hsrc_q hred_off hslq
          (wu' := stq.core.wusable + reduced) (nb_bv := stq.core.num_binary - reduced) hsrc64_1
          h_wsz_bv
        exact hJ6 (pc, ()) _ ⟨_, hsp_d, hw_d, hclq, hcvq, hfuelq, hfail2, by assumption⟩
      ft_steps; obtain ⟨hsp_d, hw_d⟩ := ft_compact_done_eq hsp hw0 hbq hsrc_q hred_off hslq
        (wu' := stq.core.wusable + reduced) (nb_bv := stq.core.num_binary) hsrc64_1 h_wsz_bv
      exact hJ6 (pc, ()) _ ⟨_, hsp_d, hw_d, hclq, hcvq, hfuelq, hfail2, by assumption⟩
    intro L8 hL8; ft_steps; rw [h_off_arg]
    exact hL8 (end_v - off) (BitVec.ofNat 64 off, BitVec.ofNat 64 off, ()) m2 ⟨st2,
      (by dsimp only; rw [hof64]; exact Nat.le_refl _),
      (by dsimp only; rw [hof64]; exact Nat.le_refl _),
      by dsimp only; rw [hof64]; exact hto2.base.off_le_end, by dsimp only; rw [hof64],
      by dsimp only; rw [hof64]; exact TransCompactInv.init hto2, hcv2, hfuel2, hm2⟩
  intro J4 hJ4; have hst_cv_lt : st.core.cur_vars < 2 ^ 32 := by rw [hcv_st]; omega
  ft_split; rotate_left; · ft_steps; exact hJ4 () m1 ⟨st, hto, hfail_ent, hcv_st, hfuel_st, hm1⟩
  have hp_lt : p.toNat < end_v := by have := h_end_c0; omega
  ft_split; · ft_steps; exact hJ4 () m1 ⟨st, hto, hfail_ent, hcv_st, hfuel_st, hm1⟩
  have hfail_f : failed = false := by revert ‹_›; cases failed <;> simp
  ft_split; rotate_left; · ft_steps; exact hJ4 () m1 ⟨st, hto, hfail_ent, hcv_st, hfuel_st, hm1⟩
  have hp_len := ft_wstk_lt hlen_st.core_ok hp_lt hto.base.end_le_wlen
  ft_split
  · have hfl0 : (st.core.wstk[p.toNat] &&& 0x80000000#32) = 0#32 := ‹_›
    obtain ⟨hp2, hto2⟩ := hto.skip_large hp_lt (List.getElem?_eq_getElem hp_len) hfl0
    ft_steps; have hp2_bv : (p + 2#64).toNat = p.toNat + 2 := ft_bv64_add2 (by omega)
    exact hL (end_v - (p.toNat + 2)) (failed, reduced, p + 2#64, ()) m1 (by omega) ⟨st,
      by dsimp only; rw [hp2_bv]; omega, by dsimp only; rw [hp2_bv]; omega,
      by dsimp only; rw [hp2_bv], by dsimp only; rw [hp2_bv]; omega,
      by dsimp only; rw [hp2_bv]; exact hto2, hfail_ent, hcv_st, hfuel_st, hm1⟩
  have hfl_nz : (st.core.wstk[p.toNat] &&& 0x80000000#32) ≠ 0#32 := ‹_›
  obtain ⟨hw0_ne, hdst_lt_st, hdst_ent, hto_skip⟩ :=
    hto.skip_bin hp_lt (List.getElem?_eq_getElem hp_len) hfl_nz
  let w0 := st.core.wstk[p.toNat]; let dst := w0 &&& 0x7FFFFFFF#32
  have hdst_lt0 : dst.toNat < 2 * s.core.cur_vars := by rw [← hcv_st]; exact hdst_lt_st
  refine wp_join_group (P := fun _ m2 => ∃ st_s : FullState,
      TransOuterInv c F0 F_cur s src.toNat off (p.toNat + 1) end_v reduced.toNat st_s ∧
      (failed = true → (cnfOfClauses F_cur).EntailsClause (cnfClause [src.toNat])) ∧
      st_s.core.cur_vars = s.core.cur_vars ∧ st_s.core.fuel = s.core.fuel ∧
      (FullMem c st_s ⋆ R) m2) ?_ ?_
  · rintro J9 ⟨⟩ m2 ⟨st_s, hto_s, hfail_s, hcv_s, hfuel_s, hm2⟩; ft_steps
    have hp1_bv : (p + 1#64).toNat = p.toNat + 1 := ft_bv64_add1 (by omega)
    exact hL (end_v - (p.toNat + 1)) (failed, reduced, p + 1#64, ()) m2 (by omega) ⟨st_s,
      by dsimp only; rw [hp1_bv]; omega, by dsimp only; rw [hp1_bv]; omega,
      by dsimp only; rw [hp1_bv], by dsimp only; rw [hp1_bv]; omega,
      by dsimp only; rw [hp1_bv]; exact hto_s, hfail_s, hcv_s, hfuel_s, hm2⟩
  intro J9 hJ9
  ft_split; · ft_steps; exact hJ9 () m1 ⟨st, hto_skip, hfail_ent, hcv_st, hfuel_st, hm1⟩
  ft_split; · ft_steps; exact hJ9 () m1 ⟨st, hto_skip, hfail_ent, hcv_st, hfuel_st, hm1⟩
  have hdst_ne : dst.toNat ≠ src.toNat := fun heq => absurd (BitVec.eq_of_toNat_eq heq) ‹¬_›
  have hdst_vlen := ft_vals_lt hlen_st.core_ok hdst_lt_st
  ft_split; · ft_steps; exact hJ9 () m1 ⟨st, hto_skip, hfail_ent, hcv_st, hfuel_st, hm1⟩
  have hdst0 : st.core.vals[dst.toNat]?.getD 0#8 = 0#8 := by
    have hv := hw0.vals_domain dst.toNat hdst_lt0
    rw [← hto.base.core_pres.2.2.2.2.2.2.2.2.2.2.1] at hv
    exact trans_vals_zero_of_domain (z := 0#32) hv rfl (by
      rw [List.getElem?_eq_getElem hdst_vlen]
      exact ‹BitVec.signExtend 32 st.core.vals[dst.toNat] = 0#32›)
  let not_src := src ^^^ 1#32; have hnot_eq : not_src.toNat = src.toNat ^^^ 1 := ft_bv32_xor1 src
  have hnot_lt : not_src.toNat < 2 * st.core.cur_vars := by
    rw [hnot_eq, hcv_st]; exact litNeg_lt_two_mul hsrc_lt
  have hnot_vlen := ft_vals_lt hlen_st.core_ok hnot_lt
  let st_pre : FullState :=
    { st with scratch := { st.scratch with ant_sz := st.scratch.ant_sz - 1 } }
  have hto_pre : TransOuterInv c F0 F_cur s src.toNat off p.toNat end_v reduced.toNat st_pre :=
    hto.with_scratch { hlen_st.scratch_ok with walk_vals_len := hlen_st.scratch_ok.walk_vals_len }
      rfl rfl
  have hpre_vals := hto_pre.base.core_pres.2.2.2.2.2.2.2.2.2.2.1
  have hpre_te := hto_pre.base.core_pres.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hpre_trl := hto_pre.base.core_pres.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hpre_cv : st_pre.core.cur_vars = s.core.cur_vars := hcv_st
  let saved := st_pre.core.trail_end
  obtain ⟨hsaved_lt, hu1, hte1⟩ := TransUnrollInv.init (st_pre := st_pre) hw0
    ⟨hlen_st.core_ok, { hlen_st.scratch_ok with walk_vals_len := hlen_st.scratch_ok.walk_vals_len }⟩
    hpre_vals hpre_te hpre_cv (by rw [hcv_st]; exact hsrc_lt) (by rw [hpre_vals]; exact hsrc0)
  have hte_len : saved < st_pre.core.trl.length := by
    rw [hlen_st.core_ok.trl_len]; exact Nat.lt_of_lt_of_le hsaved_lt hlen_st.core_ok.cur_vars_le
  have hbv_not : BitVec.ofNat 32 (src.toNat ^^^ 1) = not_src := BitVec.eq_of_toNat_eq
    (by rw [hnot_eq, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega))
  have hsrc64_vlen : (BitVec.setWidth 64 src).toNat < st.core.vals.length := by
    rw [ft_bv32_setWidth64, hlen_st.core_ok.vals_len, ← hlen0.core_ok.vals_len]; exact hsrc_vlen
  have hsav_lt := (ft_bnds hlen_st.core_ok).2.2.2
  have hte64_len : (BitVec.ofNat 64 st.core.trail_end).toNat < st.core.trl.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsav_lt]; exact hte_len
  ft_to_group; refine wp_loop_group (ts := [Ty.bool, i64, Ty.bool])
    (Inv := fun nb xs m2 => let fb := xs.1; let prop := xs.2.1; let tb := xs.2.2.1
      ∃ st_b : FullState, saved ≤ prop.toNat ∧ prop.toNat ≤ st_b.core.trail_end ∧
        nb = st_pre.core.cur_vars - prop.toNat ∧
        TransUnrollInv c F0 F_cur s st_pre src.toNat saved st_b ∧ ¬(fb = true ∧ tb = true) ∧
        (fb = true → (cnfOfClauses F_cur).EntailsClause (cnfClause [src.toNat])) ∧
        (tb = true → (cnfOfClauses F_cur).EntailsClause (cnfClause [src.toNat, dst.toNat])) ∧
        (FullMem c st_b ⋆ R) m2) ?_ ?_
  rotate_left
  · intro L13 hL13
    have hs_eq : (BitVec.ofNat 64 saved).toNat = saved := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsav_lt]
    have hnot_sw : (BitVec.setWidth 64 (BitVec.ofNat 32 (src.toNat ^^^ 1))).toNat =
        src.toNat ^^^ 1 := by
      rw [ft_bv32_setWidth64, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have h1_sw : BitVec.setWidth 8 (1 : BitVec 32) = 1#8 := rfl
    have hsrc_sw : (BitVec.setWidth 64 src).toNat = src.toNat := ft_bv32_setWidth64 src
    have hff_sw : (BitVec.setWidth 8 (-1 : BitVec 32)) = 0xFF#8 := by decide
    have hte_p1 : (BitVec.ofNat 64 st.core.trail_end + 1).toNat = st_pre.core.trail_end + 1 := by
      have hte_lt64 : (BitVec.ofNat 64 st.core.trail_end).toNat + 1 < 2 ^ 64 := by
        change (BitVec.ofNat 64 saved).toNat + 1 < 2 ^ 64; rw [hs_eq]
        have := (ft_bnds hlen_st.core_ok).2.2.2; dsimp only [saved, st_pre] at *; omega
      rw [show (1 : BitVec 64) = 1#64 from rfl, ft_bv64_add1 hte_lt64]
      exact congrArg (· + 1) hs_eq
    ft_steps; refine hL13 (st_pre.core.cur_vars - saved) (failed, BitVec.ofNat 64 saved, false, ())
      _ ⟨_, by dsimp only; rw [hs_eq]; exact Nat.le_refl _, ?_, by dsimp only; rw [hs_eq], ?_,
        by dsimp only; simp [hfail_f], fun hf => by dsimp only at hf; simp [hfail_f] at hf,
        fun ht => False.elim (Bool.noConfusion ht), by assumption⟩
    · rw [hs_eq, hte_p1]; exact Nat.le_of_lt hte1
    · dsimp only [not_src] at hbv_not
      rw [show (1#32 : BitVec 32) = 1 from rfl] at hbv_not
      simpa only [saved, st_pre, hnot_sw, h1_sw, hsrc_sw, hff_sw, ← hbv_not, hte_p1,
        show (BitVec.ofNat 64 st.core.trail_end).toNat = saved from hs_eq] using hu1
  rintro L13 nb ⟨fb, prop, tb, ⟨⟩⟩ m2 hL13 ⟨st_b, hsp_le, hpt_le, hbneq, hu_b, hntf, hfb, htb, hm2⟩
  dsimp only at hsp_le hpt_le hbneq hntf hfb htb; have hlen_b := hu_b.len_ok
  refine wp_join_group (P := fun _ m3 => ∃ st_u : FullState,
      TransUnrollInv c F0 F_cur s st_pre src.toNat saved st_u ∧ ¬(fb = true ∧ tb = true) ∧
      (fb = true → (cnfOfClauses F_cur).EntailsClause (cnfClause [src.toNat])) ∧
      (tb = true → (cnfOfClauses F_cur).EntailsClause (cnfClause [src.toNat, dst.toNat])) ∧
      (FullMem c st_u ⋆ R) m3) ?_ ?_
  · rintro J15 ⟨⟩ m3 ⟨st_u, hu_u, hntf_u, hfb_u, htb_u, hm3⟩; ft_to_group
    refine wp_loop_group (ts := []) (Inv := fun nu _ m4 => ∃ st_r : FullState,
        nu = st_r.core.trail_end - saved ∧
        TransUnrollInv c F0 F_cur s st_pre src.toNat saved st_r ∧ (FullMem c st_r ⋆ R) m4) ?_ ?_
    rotate_left
    · intro L17 hL17; exact hL17 (st_u.core.trail_end - saved) () m3 ⟨st_u, rfl, hu_u, hm3⟩
    rintro L17 nu ⟨⟩ m4 hL17 ⟨st_r, huneq, hu_r, hm4⟩; have hlen_r := hu_r.len_ok
    have hte_r_lt : st_r.core.trail_end < 2 ^ 64 := (ft_bnds hlen_r.core_ok).2.2.2; ft_split
    · have hte_gt : saved < st_r.core.trail_end :=
        (ft_bv64_lt_eq hsav_lt hte_r_lt).mp (by simpa [BitVec.ult] using ‹_›)
      obtain ⟨hte1_bv_len, hul_sw_bv, huln_sw_bv, hte1_bv, hu_r''⟩ :=
        ft_unroll_c0_aux hw0 hpre_vals hpre_cv hto_pre.base.len_ok hu_r hte_gt hte_r_lt
      have huln_sw_set : (BitVec.setWidth 64 (st_r.core.trl[(BitVec.ofNat 64
          (BitVec.ofNat 64 st_r.core.trail_end - 1#64).toNat).toNat]'hte1_bv_len ^^^ 1#32)).toNat <
          (st_r.core.vals.set (BitVec.setWidth 64 (st_r.core.trl[(BitVec.ofNat 64 (BitVec.ofNat 64
            st_r.core.trail_end - 1#64).toNat).toNat]'hte1_bv_len)).toNat 0#8).length := by
        rw [List.length_set]; exact huln_sw_bv
      ft_steps; exact hL17 (st_r.core.trail_end - 1 - saved) () _ (by omega)
        ⟨_, by dsimp only; rw [hte1_bv], hu_r'', by assumption⟩
    have hte_eq : st_r.core.trail_end = saved := by
      have hng : ¬(saved < st_r.core.trail_end) := fun hlt => ‹¬(_ < _)› (by
        rwa [Nat.mod_eq_of_lt hsav_lt, Nat.mod_eq_of_lt hte_r_lt])
      have := hu_r.saved_le_te; omega
    have hto_done := hu_r.done hto_pre hte_eq; have hlen_d := hto_done.base.len_ok
    have hp1_bv : (p + 1#64).toNat = p.toNat + 1 := ft_bv64_add1 (by omega); ft_to_group
    refine wp_join_group (P := fun xs m5 => let red' := xs.1; ∃ st_d : FullState,
        red'.toNat ≤ p.toNat + 1 - off ∧
        TransOuterInv c F0 F_cur s src.toNat off (p.toNat + 1) end_v red'.toNat st_d ∧
        st_d.core.cur_vars = s.core.cur_vars ∧ st_d.core.fuel = s.core.fuel ∧
        (FullMem c st_d ⋆ R) m5) ?_ ?_
    · rintro J20 ⟨red', ⟨⟩⟩ m5 ⟨st_d, hrl_d, hto_d, hcv_d, hfuel_d, hm5⟩; ft_steps
      exact hL (end_v - (p.toNat + 1)) (fb, red', p + 1#64, ()) m5 (by omega) ⟨st_d,
        (by dsimp only; rw [hp1_bv]; omega), (by dsimp only; rw [hp1_bv]; omega),
        (by dsimp only; rw [hp1_bv]), (by dsimp only; rw [hp1_bv]; exact hrl_d),
        (by dsimp only; rw [hp1_bv]; exact hto_d), fun hf => hfb_u hf, hcv_d, hfuel_d, hm5⟩
    intro J20 hJ20; have hget_r : st_r.core.wstk[p.toNat]? = some w0 := by
      rw [hu_r.same_core, List.getElem?_eq_getElem hp_len]
    ft_split; rotate_left
    · obtain ⟨_, _, _, hto_nxt⟩ := hto_done.skip_bin hp_lt hget_r hfl_nz; ft_steps
      exact hJ20 (reduced, ()) m4 ⟨st_r, by dsimp only; omega, hto_nxt,
        by rw [hu_r.same_core, hcv_st], by rw [hu_r.same_core, hfuel_st], hm4⟩
    ft_to_group; rw [show (Arg.var (lift2 (fun {n} x1 x2 => x1 &&& x2) (fun x1 x2 => x1 && x2) i32
      st.core.wstk[p.toNat] (2147483647 : BitVec 32))) = Arg.var dst from rfl]; ft_call h_del_bin
    have hdst_lt_d : dst.toNat < 2 * st_r.core.cur_vars := by
      rw [hu_r.same_core, hcv_st]; exact hdst_lt0
    have hsrc_lt_d : src.toNat < 2 * st_r.core.cur_vars := by
      rw [hu_r.same_core, hcv_st]; exact hsrc_lt
    refine ⟨c, st_r, R, rfl, hlen_r,
      fun _ => hto_done.base.other_bounds dst.toNat hdst_lt_d hdst_ne, hm4,
      fun wvec' wstk' wu' m5 hlen5 hdst_ws hother_ws hwstk_out hdst_sl _ _ _ hm5 => ?_⟩
    have hp_wc : p.toNat < c.wcap := by
      have := hto_done.base.end_le_wlen; have := hlen_r.core_ok.wlen_le; omega
    have hred1 : (reduced + 1#64).toNat = reduced.toNat + 1 :=
      ft_bv64_add1 (by have := hto_done.base.end_le_wlen; have := hlen_r.core_ok.wlen_le; omega)
    have hto_mk := hto_done.del_side_and_tomb hp_lt hp_wc hsrc_lt_d hdst_lt_d hdst_ne hget_r hfl_nz
      rfl hlen5 (by simpa only [Arg.val_var] using hdst_ws hdst_lt_d) hother_ws
      (fun idx hidx ho => hwstk_out idx hidx (fun _ => by simpa only [Arg.val_var] using ho))
      (by simpa only [Arg.val_var] using hdst_sl F_cur) (tc' := st_r.scratch.trans_cnt + 1#64)
    have hp_l5 : p.toNat < wstk'.length := by rw [hlen5.core_ok.wstk_len_arr]; omega
    ft_steps; exact hJ20 (reduced + 1#64, ()) _ ⟨_, by rw [hred1]; omega,
      by rw [hred1]; exact hto_mk, by dsimp only; rw [hu_r.same_core, hcv_st],
      by dsimp only; rw [hu_r.same_core, hfuel_st], by assumption⟩
  intro J15 hJ15; ft_split; · ft_steps; exact hJ15 () m2 ⟨st_b, hu_b, hntf, hfb, htb, hm2⟩
  ft_split; · ft_steps; exact hJ15 () m2 ⟨st_b, hu_b, hntf, hfb, htb, hm2⟩
  ft_split; rotate_left; · ft_steps; exact hJ15 () m2 ⟨st_b, hu_b, hntf, hfb, htb, hm2⟩
  have hte_b_lt := (ft_bnds hlen_b.core_ok).2.2.2; have hcv_b_le := hlen_b.core_ok.cur_vars_le
  have hpt_lt : prop.toNat < st_b.core.trail_end := by
    have h1 : prop.toNat < st_b.core.trail_end % 2 ^ 64 := ‹_›
    rwa [Nat.mod_eq_of_lt hte_b_lt] at h1
  have hprop_tlen : prop.toNat < st_b.core.trl.length := by
    rw [hlen_b.core_ok.trl_len]; have := hlen_b.core_ok.trail_end_le; omega
  have hprop1 := ft_bv64_add1 (by omega : prop.toNat + 1 < 2 ^ 64)
  obtain ⟨lit, hlit_get, hlit_lt, _, _, _, hent_lit⟩ := hu_b.bfs_trl_inv prop.toNat hsp_le hpt_lt
  let nl := lit ^^^ 1#32; have hnl_eq := ft_bv32_xor1 lit
  have hnl_lt : nl.toNat < 2 * st_b.core.cur_vars := by
    rw [hnl_eq, hu_b.same_core]; exact litNeg_lt_two_mul hlit_lt
  have hlit_ge : st_b.core.trl[prop.toNat]'hprop_tlen = lit :=
    Option.some.inj ((List.getElem?_eq_getElem hprop_tlen).symm.trans hlit_get)
  have hnl_shl : (BitVec.setWidth 64 (lit ^^^ 1#32) <<< 1).toNat = 2 * nl.toNat := by
    rw [ft_bv64_shl1 (by rw [ft_bv32_setWidth64]; omega), ft_bv32_setWidth64]
  have hnl_wv0 : (BitVec.setWidth 64
      (st_b.core.trl[prop.toNat]'hprop_tlen ^^^ 1#32) <<< 1).toNat < st_b.core.wvec.length := by
    rw [hlit_ge, hnl_shl, hlen_b.core_ok.wvec_len]; omega
  have hnl_wv1 : ((BitVec.setWidth 64 (st_b.core.trl[prop.toNat]'hprop_tlen ^^^ 1#32) <<< 1) +
      1#64).toNat < st_b.core.wvec.length := by
    rw [hlit_ge, ft_bv64_add1 (by rw [hnl_shl]; omega), hnl_shl, hlen_b.core_ok.wvec_len]; omega
  obtain ⟨hnl_bnd, nt0, htomb0⟩ := hu_b.watch_slice hto_pre hnl_lt; ft_to_group
  refine wp_join_group (P := fun xs m3 => let f2 := xs.1; let t2 := xs.2.1; ∃ st_w : FullState,
      TransUnrollInv c F0 F_cur s st_pre src.toNat saved st_w ∧
      st_b.core.trail_end ≤ st_w.core.trail_end ∧ ¬(f2 = true ∧ t2 = true) ∧
      (f2 = true → (cnfOfClauses F_cur).EntailsClause (cnfClause [src.toNat])) ∧
      (t2 = true → (cnfOfClauses F_cur).EntailsClause (cnfClause [src.toNat, dst.toNat])) ∧
      (FullMem c st_w ⋆ R) m3) ?_ ?_
  · rintro J19 ⟨f2, t2, _q, ⟨⟩⟩ m3 ⟨st_w, hu_w, hte_w, hntf2, hf2, ht2, hm3⟩
    have hpt_pre : prop.toNat < st_pre.core.cur_vars := by
      have := hlen_b.core_ok.trail_end_le; rw [hu_b.same_core] at this
      exact Nat.lt_of_lt_of_le hpt_lt this
    ft_steps; refine hL13 (st_pre.core.cur_vars - (prop.toNat + 1)) (f2, prop + 1#64, t2, ()) m3
      (by rw [hbneq]; omega) ⟨st_w, by rw [hprop1]; omega, by rw [hprop1]; omega,
        by rw [hprop1], hu_w, hntf2, hf2, ht2, hm3⟩
  intro J19 hJ19; let loff := fullWatchOffCore st_b.core nl.toNat
  let lsz := fullWatchSizeCore st_b.core nl.toNat; let lend := loff + lsz; ft_to_group
  refine wp_loop_group (ts := [i64]) (Inv := fun nq xs m3 => let q := xs.1
      ∃ st_q : FullState, ∃ nt : Nat, loff ≤ q.toNat ∧ q.toNat ≤ lend ∧
        nq = lend - q.toNat ∧ st_b.core.trail_end ≤ st_q.core.trail_end ∧
        TombWatchSliceOk F_cur st_q.core nl.toNat q.toNat (lend - q.toNat) nt ∧
        TransUnrollInv c F0 F_cur s st_pre src.toNat saved st_q ∧ (FullMem c st_q ⋆ R) m3) ?_ ?_
  rotate_left
  · intro L20 hL20
    have hloff_lt : loff < 2 ^ 64 := by
      have := hnl_bnd; have := (ft_bnds hlen_b.core_ok).2.2.1; omega
    have hlo_eq : (BitVec.ofNat 64 loff).toNat = loff := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hloff_lt]
    have hlo_arg : BitVec.setWidth 64 (st_b.core.wvec[(BitVec.setWidth 64
        (st_b.core.trl[prop.toNat]'hprop_tlen ^^^ (1 : BitVec 32)) <<<
          (1 : Nat)).toNat]'hnl_wv0) = BitVec.ofNat 64 loff := by
      apply BitVec.eq_of_toNat_eq; rw [ft_bv32_setWidth64, hlo_eq]
      have hidx2 : (BitVec.setWidth 64 (st_b.core.trl[prop.toNat]'hprop_tlen ^^^
          (1 : BitVec 32)) <<< (1 : Nat)).toNat = 2 * nl.toNat := by simpa [hlit_ge] using hnl_shl
      have hnl0 : 2 * nl.toNat < st_b.core.wvec.length := by rw [← hidx2]; exact hnl_wv0
      simp only [hidx2]; exact ft_getElem_toNat hnl0
    ft_steps; rw [hlo_arg]; exact hL20 (lend - loff) (BitVec.ofNat 64 loff, ()) m2
      ⟨st_b, nt0, by rw [hlo_eq]; exact Nat.le_refl _, by rw [hlo_eq]; omega, by rw [hlo_eq],
        Nat.le_refl _, by rw [hlo_eq]; simpa [lend, loff, lsz] using htomb0, hu_b, hm2⟩
  rintro L20 nq ⟨q, ⟨⟩⟩ m3 hL20 ⟨st_q, nt, hql, hqh, hqneq, hte_q, htm_q, hu_q, hm3⟩
  dsimp only at hql hqh hqneq htm_q; have hlen_q := hu_q.len_ok; ft_split; rotate_left
  · ft_steps; exact hJ19 (fb, tb, q, ()) m3 ⟨st_q, hu_q, hte_q, hntf, hfb, htb, hm3⟩
  have hq_lt : q.toNat < lend := by
    have hnl0_lt : 2 * nl.toNat < st_b.core.wvec.length := by rw [hlen_b.core_ok.wvec_len]; omega
    have hnl1_lt : 2 * nl.toNat + 1 < st_b.core.wvec.length := by
      rw [hlen_b.core_ok.wvec_len]; omega
    have hlo_w := ft_getElem_toNat hnl0_lt; have hls_w := ft_getElem_toNat hnl1_lt
    have hq_c0 := ‹q.toNat < _›
    have hidx_eq : (st_b.core.trl[prop.toNat]'hprop_tlen).toNat ^^^ 1 = nl.toNat := by
      rw [hlit_ge, hnl_eq]
    have h2nl_lt : 2 * nl.toNat + 1 < 2 ^ 64 := by have := (ft_bnds hlen_b.core_ok).1; omega
    have hmod0 : 2 * nl.toNat % 2 ^ 64 = 2 * nl.toNat := Nat.mod_eq_of_lt (by omega)
    have hmod1 : (2 * nl.toNat + (1 : BitVec 64).toNat) % 2 ^ 64 = 2 * nl.toNat + 1 := by
      rw [show (1 : BitVec 64).toNat = 1 from rfl, Nat.mod_eq_of_lt h2nl_lt]
    simp only [hidx_eq, hmod0, hmod1, hlo_w, hls_w] at hq_c0
    have := hnl_bnd; have := (ft_bnds hlen_b.core_ok).2.2.1
    change q.toNat < (loff + lsz) % 2 ^ 64 at hq_c0; rwa [Nat.mod_eq_of_lt (by omega)] at hq_c0
  have hq_len : q.toNat < st_q.core.wstk.length := by
    rw [hlen_q.core_ok.wstk_len_arr]; have := hnl_bnd; have := hlen_b.core_ok.wlen_le; omega
  have hstep := htm_q.inv_step (by omega) (List.getElem?_eq_getElem hq_len); ft_split
  · have hfl0 : (st_q.core.wstk[q.toNat] &&& 0x80000000#32) = 0#32 := ‹_›
    simp only [hfl0, ↓reduceIte] at hstep; obtain ⟨hle2, _, _, _, _, htm'⟩ := hstep; ft_steps
    have hq2 : (q + 2#64).toNat = q.toNat + 2 :=
      ft_bv64_add2 (by have := hnl_bnd; have := (ft_bnds hlen_b.core_ok).2.2.1; omega)
    exact hL20 (lend - (q.toNat + 2)) (q + 2#64, ()) m3 (by omega) ⟨st_q, nt, by rw [hq2]; omega,
      by rw [hq2]; omega, by rw [hq2], hte_q,
      by rw [hq2]; rwa [show lend - q.toNat - 2 = lend - (q.toNat + 2) by omega] at htm', hu_q, hm3⟩
  have hfl_nz : (st_q.core.wstk[q.toNat] &&& 0x80000000#32) ≠ 0#32 := ‹_›
  have hq1 : (q + 1#64).toNat = q.toNat + 1 :=
    ft_bv64_add1 (by have := hnl_bnd; have := (ft_bnds hlen_b.core_ok).2.2.1; omega)
  refine wp_join_group (P := fun _ m4 => m4 = m3) ?_ ?_
  rotate_left
  · intro J24 hJ24; ft_split
    · ft_split
      · obtain ⟨nt2, htm2⟩ := htm_q.step_non_large hq_lt (List.getElem?_eq_getElem hq_len) hfl_nz
        ft_steps; exact hL20 (lend - (q.toNat + 1)) (q + 1#64, ()) m3 (by omega)
          ⟨st_q, nt2, by rw [hq1]; omega, by rw [hq1]; omega, by rw [hq1], hte_q,
            by rw [hq1]; exact htm2, hu_q, hm3⟩
      · ft_steps; exact hJ24 () m3 rfl
    · ft_steps; exact hJ24 () m3 rfl
  rintro J24 ⟨⟩ m4 rfl; simp only [hfl_nz, ↓reduceIte] at hstep
  let ot := st_q.core.wstk[q.toNat] &&& 0x7FFFFFFF#32
  have hot64 : (ot.setWidth 64).toNat = ot.toNat := ft_bv32_setWidth64 ot
  have hnlits_lt : (st_q.core.cur_vars <<< 1) = 2 * st_q.core.cur_vars := by omega
  ft_split
  · have hdst_eq : st_q.core.wstk[q.toNat] &&& 0x7FFFFFFF#32 = dst := ‹_›
    have hne_tomb : st_q.core.wstk[q.toNat] ≠ 0xFFFFFFFF#32 := fun ht => by
      have hdst_nat := congrArg BitVec.toNat hdst_eq; rw [ht] at hdst_nat
      have := (ft_bnds hlen0.core_ok).1
      have hmsk : (0xFFFFFFFF#32 &&& 0x7FFFFFFF#32).toNat = 2147483647 := by decide
      omega
    simp only [hne_tomb, ↓reduceIte] at hstep; obtain ⟨hot_lt, hent_nl, _⟩ := hstep
    have hent_ot := entails_pair_trans hent_lit (by rwa [← hnl_eq])
    rw [congrArg BitVec.toNat hdst_eq] at hent_ot; ft_steps
    exact hJ19 (fb, true, q, ()) m4 ⟨st_q, hu_q, hte_q, by simp [‹fb = false›],
      fun hf => absurd hf (by simp [‹fb = false›]), fun _ => hent_ot, hm3⟩
  refine wp_join_group (P := fun _ m5 => ∃ st_q2 : FullState, ∃ nt2 : Nat,
      st_b.core.trail_end ≤ st_q2.core.trail_end ∧
      TombWatchSliceOk F_cur st_q2.core nl.toNat (q.toNat + 1) (lend - (q.toNat + 1)) nt2 ∧
      TransUnrollInv c F0 F_cur s st_pre src.toNat saved st_q2 ∧ (FullMem c st_q2 ⋆ R) m5) ?_ ?_
  · rintro J27 ⟨_, ⟨⟩⟩ m5 ⟨st_q2, nt2, hte_q2, htm_q2, hu_q2, hm5⟩; ft_steps
    exact hL20 (lend - (q.toNat + 1)) (q + 1#64, ()) m5 (by omega)
      ⟨st_q2, nt2, by rw [hq1]; omega, by rw [hq1]; omega, by rw [hq1], hte_q2,
        by rw [hq1]; exact htm_q2, hu_q2, hm5⟩
  intro J27 hJ27; ft_split; rotate_left
  · have htomb_q : st_q.core.wstk[q.toNat] = 0xFFFFFFFF#32 := Classical.byContradiction fun hne =>
        by
      simp only [hne, ↓reduceIte] at hstep
      have hlt_w : ¬((st_q.core.wstk[q.toNat] &&& (2147483647 : BitVec 32)).toNat <
          2 * (s.core.cur_vars % 2 ^ 64) % 2 ^ 64) := ‹_›
      have hcv_qs : st_q.core.cur_vars = s.core.cur_vars := by rw [hu_q.same_core, hcv_st]
      have hlt2 := (ft_bnds hlen0.core_ok).1; rw [Nat.mod_eq_of_lt (by omega :
        s.core.cur_vars < 2 ^ 64), Nat.mod_eq_of_lt (by omega : 2 * s.core.cur_vars < 2 ^ 64),
        ← hcv_qs] at hlt_w
      exact hlt_w hstep.1
    simp only [htomb_q, ↓reduceIte] at hstep; obtain ⟨_, hstep_t⟩ := hstep; ft_steps
    exact hJ27 (fb, ()) m4 ⟨st_q, nt - 1, hte_q,
      by rwa [show lend - q.toNat - 1 = lend - (q.toNat + 1) by omega] at hstep_t, hu_q, hm3⟩
  have hne_tomb : st_q.core.wstk[q.toNat] ≠ 0xFFFFFFFF#32 := fun ht => by
    have hlt_w : (st_q.core.wstk[q.toNat] &&& (2147483647 : BitVec 32)).toNat <
        2 * (s.core.cur_vars % 2 ^ 64) % 2 ^ 64 := ‹_›
    rw [ht] at hlt_w; have hmsk : (0xFFFFFFFF#32 &&& (2147483647 : BitVec 32)).toNat = 2147483647 :=
      by decide
    have := (ft_bnds hlen0.core_ok).1; omega
  simp only [hne_tomb, ↓reduceIte] at hstep; obtain ⟨hot_lt, hent_nl, htail⟩ := hstep
  have hent_ot := entails_pair_trans hent_lit (by rwa [← hnl_eq])
  have hot_vlen := ft_vals_lt hlen_q.core_ok hot_lt
  have hot_st : ot.toNat < 2 * st_pre.core.cur_vars := by
    have hcv_q_pre : st_q.core.cur_vars = st_pre.core.cur_vars := by rw [hu_q.same_core]
    rw [← hcv_q_pre]; exact hot_lt
  have hdom_ot := hu_q.vals_domain hw0 hpre_vals hpre_cv hot_st; ft_split
  · rename_i hslt_c0
    change (BitVec.signExtend 32 st_q.core.vals[ot.toNat]).slt 0#32 = true at hslt_c0
    have hval_ff := trans_vals_ff_of_domain (z := 0#32) hdom_ot rfl
      (by rw [List.getElem?_eq_getElem hot_vlen]; exact hslt_c0)
    have hent_src := hu_q.entails_src_of_falsified hw0 hpre_vals hpre_cv hcl0 hot_st hval_ff hent_ot
    ft_steps; exact hJ19 (true, tb, q, ()) m4 ⟨st_q, hu_q, hte_q, by simp [‹tb = false›],
      fun _ => hent_src, fun ht => absurd ht (by simp [‹tb = false›]), hm3⟩
  refine wp_join_group (P := fun _ m5 => ∃ st_q2 : FullState, ∃ nt2 : Nat,
      st_b.core.trail_end ≤ st_q2.core.trail_end ∧
      TombWatchSliceOk F_cur st_q2.core nl.toNat (q.toNat + 1) (lend - (q.toNat + 1)) nt2 ∧
      TransUnrollInv c F0 F_cur s st_pre src.toNat saved st_q2 ∧ (FullMem c st_q2 ⋆ R) m5) ?_ ?_
  · rintro J30 ⟨⟩ m5 ⟨st_q2, nt2, hte2, htm2, hu2, hm5⟩; ft_steps
    exact hJ27 (fb, ()) m5 ⟨st_q2, nt2, hte2, htm2, hu2, hm5⟩
  intro J30 hJ30
  have htail' : TombWatchSliceOk F_cur st_q.core nl.toNat (q.toNat + 1) (lend - (q.toNat + 1)) nt :=
    by rwa [show lend - q.toNat - 1 = lend - (q.toNat + 1) by omega] at htail
  ft_split; rotate_left; · ft_steps; exact hJ30 () m4 ⟨st_q, nt, hte_q, htail', hu_q, hm3⟩
  ft_split; rotate_left; · ft_steps; exact hJ30 () m4 ⟨st_q, nt, hte_q, htail', hu_q, hm3⟩
  rename_i hval0 _
  change BitVec.signExtend 32 st_q.core.vals[ot.toNat] = 0#32 at hval0
  have hot0 := trans_vals_zero_of_domain (z := 0#32) hdom_ot rfl
    (by rw [List.getElem?_eq_getElem hot_vlen]; exact hval0)
  obtain ⟨hte_q_lt, hu_q'⟩ := hu_q.push hw0 hpre_vals hpre_te hpre_trl hpre_cv hot_st hot0 hent_ot
  have hbv_ot : BitVec.ofNat 32 ot.toNat = ot := ft_bv32_ofNat_toNat ot
  have hotn_vlen : (BitVec.setWidth 64 (ot ^^^ 1#32)).toNat < (st_q.core.vals.set
      (BitVec.setWidth 64 ot).toNat (BitVec.setWidth 8 (1 : BitVec 32))).length := by
    rw [List.length_set, ft_bv32_setWidth64, ft_bv32_xor1, hlen_q.core_ok.vals_len]
    have := litNeg_lt_two_mul hot_lt; have := hlen_q.core_ok.cur_vars_le; dsimp only [ot]; omega
  have hteq_lt : st_q.core.trail_end < 2 ^ 64 := (ft_bnds hlen_q.core_ok).2.2.2
  have hte_bv : (BitVec.ofNat 64 st_q.core.trail_end).toNat = st_q.core.trail_end := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hteq_lt]
  have hteq_tlen : (BitVec.ofNat 64 st_q.core.trail_end).toNat < st_q.core.trl.length := by
    rw [hte_bv, hlen_q.core_ok.trl_len]; have := hlen_q.core_ok.cur_vars_le; omega
  have hteq1 : (BitVec.ofNat 64 st_q.core.trail_end + 1#64).toNat = st_q.core.trail_end + 1 := by
    rw [ft_bv64_add1 (by omega), hte_bv]
  ft_steps
  let st_q2 : FullState := { st_q with core := { st_q.core with
      vals := (st_q.core.vals.set ot.toNat 1#8).set (ot.toNat ^^^ 1) 0xFF#8,
      trl := st_q.core.trl.set st_q.core.trail_end ot, trail_end := st_q.core.trail_end + 1 } }
  have hm_q2 : (FullMem c { st_q with core := { st_q.core with
      vals := (st_q.core.vals.set (BitVec.setWidth 64 ot).toNat 1#8).set
        (BitVec.setWidth 64 (ot ^^^ 1#32)).toNat 0xFF#8,
      trl := st_q.core.trl.set (BitVec.ofNat 64 st_q.core.trail_end).toNat ot,
      trail_end := (BitVec.ofNat 64 st_q.core.trail_end + 1#64).toNat } } ⋆ R) _ := ‹_›
  simp only [ft_bv32_setWidth64, ft_bv32_xor1, hte_bv, hteq1] at hm_q2
  exact hJ30 () _ ⟨st_q2, nt, Nat.le_trans hte_q (Nat.le_succ _),
    TombWatchSliceOk.mono (k := st_q.core) (k' := st_q2.core) (Nat.le_refl _) (fun _ hr => hr)
      (fun _ _ _ => rfl) htail',
    by simpa only [hbv_ot] using hu_q', hm_q2⟩
theorem full_transitive_wp (Γ : Env)
    (h_backtrack : ∀ args m Q X,
      fullBacktrackSpec args m Q X → Γ "full_backtrack" [i64, i64] [] args m Q X)
    (h_trans_lit : ∀ args m Q X,
      fullTransLitSpec args m Q X → Γ "full_trans_lit" [i64, i32] [.bool] args m Q X)
    (h_propagate : ∀ args m Q X,
      fullPropagateSpec args m Q X → Γ "full_propagate" [i64] [i64] args m Q X)
    (h_defrag : ∀ args m Q X,
      fullWstackDefragSpec args m Q X → Γ "full_wstack_defrag" [i64] [] args m Q X) :
    ∀ args m Q X, fullTransitiveSpec args m Q X → Func.wp Γ full_transitive_body args m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hsp, hm, hQ⟩; unfold full_transitive_body; ft_unmdata
  refine wp_join_group (P := fun _ m' => ∃ s1 : FullState, FullSparseInv c F0 s1 ∧
      s1.core.cur_level = 0 ∧ s1.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c s1 ⋆ R) m') ?_ ?_
  · rintro J ⟨⟩ m1 ⟨s1, hsp1, hcl1, hfuel1, hm1⟩; have hlen1 := hsp1.1.lengths; ft_to_group
    refine wp_loop_break_group (brkTs := [i64, i64]) (lpTs := [i64])
      (BrkPost := fun xs m' => let res := xs.2.1; ∃ sb : FullState, FullSparseInv c F0 sb ∧
        sb.core.cur_level = 0 ∧ sb.core.fuel.toNat ≤ s.core.fuel.toNat ∧
        (res = 1#64 ∨ res = 20#64) ∧ (res = 20#64 → F0.Unsat) ∧ (FullMem c sb ⋆ R) m')
      (Inv := fun n xs m' => let v := xs.1; ∃ sl : FullState, v.toNat ≤ s1.core.cur_vars ∧
        n = s1.core.cur_vars - v.toNat ∧ FullSparseInv c F0 sl ∧ sl.core.cur_level = 0 ∧
        sl.core.cur_vars = s1.core.cur_vars ∧ sl.core.fuel.toNat ≤ s.core.fuel.toNat ∧
        (FullMem c sl ⋆ R) m') ?_ ?_ ?_
    · rintro B ⟨_v, res, ⟨⟩⟩ m2 ⟨sb, hspb, hclb, hfuelb, hresb, hunsatb, hm2⟩
      refine wp_join_group (P := fun _ m3 => ∃ sd : FullState, FullSparseInv c F0 sd ∧
          sd.core.cur_level = 0 ∧ sd.core.fuel.toNat ≤ s.core.fuel.toNat ∧
          (FullMem c sd ⋆ R) m3) ?_ ?_
      · rintro Jd ⟨⟩ m3 ⟨sd, hspd, hcld, hfueld, hm3⟩; have hlend := hspd.1.lengths; ft_steps
        exact hQ res _ _ (fullSparseInv_with_probing hspd 0#64) hcld rfl hfueld hresb hunsatb
          (by assumption)
      · intro Jd hJd; have hlenb := hspb.1.lengths; ft_split
        · ft_call h_defrag; obtain ⟨F_cb, hwb⟩ := hspb.1.witness
          have hm := hwb.watches; simp only [ModeWatchesInv, hspb.2.2.2.2, ↓reduceIte] at hm
          refine ⟨c, sb, R, rfl, hlenb, hm.layout, hm2, fun _ _ _ _ m3 hlen3 hlay3 _ hpres hm3 =>
            hJd () m3 ⟨_, fullWstackDefrag_sparse hspb rfl hlen3 hlay3 hpres, hclb, hfuelb, hm3⟩⟩
        · ft_steps; exact hJd () m2 ⟨sb, hspb, hclb, hfuelb, hm2⟩
    · rintro B L n ⟨v, ⟨⟩⟩ m2 hB hL ⟨sl, hvle, hneq, hspl, hcll, hcvl, hfuell, hm2⟩
      have hlenl := hspl.1.lengths
      have hcv_lt : s1.core.cur_vars < 2 ^ 64 := by have := (ft_bnds hlen1.core_ok).1; omega
      have hB1 : B (v, 1#64, ()) m2 := hB (v, 1#64, ()) m2 ⟨sl, hspl, hcll, hfuell, Or.inl rfl,
        fun h => absurd (show (1#64 : BitVec 64) = 20#64 from h) (by decide), hm2⟩
      ft_split; rotate_left; · ft_steps; exact hB1
      have hv_lt : v.toNat < s1.core.cur_vars := by
        have hlt : v.toNat < (BitVec.ofNat 64 s1.core.cur_vars).toNat := by
          simpa [BitVec.ult] using ‹_›
        rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcv_lt] at hlt
      ft_split; rotate_left; · ft_steps; exact hB1
      ft_split; rotate_left; · ft_steps; exact hB1
      refine wp_join_group (P := fun xs m3 => xs.1 = 1#64 ∧ ∃ sn : FullState,
          FullSparseInv c F0 sn ∧ sn.core.cur_level = 0 ∧ sn.core.cur_vars = s1.core.cur_vars ∧
          sn.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c sn ⋆ R) m3) ?_ ?_
      · rintro J2 ⟨_, ⟨⟩⟩ m3 ⟨rfl, sn, hspn, hcln, hcvn, hfueln, hm3⟩; ft_steps
        have hv1 : (v + 1#64).toNat = v.toNat + 1 := ft_bv64_add1 (by omega)
        dsimp only at hvle hneq; exact hL (s1.core.cur_vars - (v.toNat + 1)) (v + 1#64, ()) m3
          (by omega) ⟨sn, by dsimp only; rw [hv1]; omega, by dsimp only; rw [hv1], hspn, hcln,
            hcvn, hfueln, hm3⟩
      · intro J2 hJ2
        have hv_fl : v.toNat < sl.core.flags.length := by
          rw [hlenl.core_ok.flags_len]; have := hlenl.core_ok.cur_vars_le; omega
        ft_split; rotate_left
        · ft_steps; exact hJ2 (1#64, ()) m2 ⟨rfl, sl, hspl, hcll, hcvl, hfuell, hm2⟩
        ft_to_group; have hsp_cl : FullSparseInv c F0 { sl with core := { sl.core with
            flags := sl.core.flags.set v.toNat (sl.core.flags[v.toNat] &&& ~~~512#32) } } :=
          fullSparseInv_clear_fl_trans hspl
        have hv32 : 2 * v.toNat + 1 < 2 ^ 32 := by have := (ft_bnds hlenl.core_ok).1; omega
        have hlit0 : ((v <<< (1 : Nat)).setWidth 32).toNat < 2 * ({ sl.core with
            flags := sl.core.flags.set v.toNat (sl.core.flags[v.toNat] &&& ~~~512#32) } :
            FullCoreState).cur_vars := by rw [ft_bv64_shl1_setWidth32 (by omega)]; dsimp only; omega
        ft_call h_trans_lit; refine ⟨c, F0, _, R, rfl, hsp_cl, hcll, hlit0, (by assumption),
          fun ok s_t0 m3 hspt0 hclt0 hcvt0 hfuelt0 huns0 hm3 => ?_⟩
        have hcv_t0 : s_t0.core.cur_vars = s1.core.cur_vars := hcvt0.trans hcvl
        ft_split; rotate_left; · ft_steps; exact hB (v, 20#64, ()) m3 ⟨s_t0, hspt0, hclt0,
          by rw [hfuelt0]; exact hfuell, Or.inr rfl, fun _ => huns0 (by cases ok <;> simp_all), hm3⟩
        obtain ⟨F_ct0, hwt0⟩ := hspt0.1.witness; ft_call h_propagate
        refine ⟨c, F0, F_ct0, s_t0, R, rfl, hspt0.1.lengths, hwt0, hspt0.2.2.2.2, hm3,
          fun r_p0 vals' flags' lvl' rsns' trl' tp' te' prop' unass' unfl' wvec' arena' wstk'
            wlen' wu' fuel' ctype' cref' c0' c1' oom' ticks' wsort' phases' m4 hlen4 hw4 _ hperm4
            hfu4 _ _ hr1 _ _ hm4 => ?_⟩
        have hsp_p0 := fullPropagate_sparse hspt0 rfl hlen4 hw4 hperm4; ft_split
        · ft_steps; exact hB (v, 20#64, ()) m4 ⟨_, hsp_p0, hclt0,
            Nat.le_trans (Nat.le_trans hfu4 (by rw [hfuelt0]; exact Nat.le_refl _)) hfuell,
            Or.inr rfl, fun _ => level0_unsat_of_conflict_okW hw4 hclt0 (hr1 ‹_›).2.2, hm4⟩
        · let st_p0 : FullState := { s_t0 with
            scratch := { s_t0.scratch with
              search_ticks := ticks', wsort := wsort', phases := phases' },
            core := { s_t0.core with
              vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
              trail_pos := tp', trail_end := te', propagated := prop', unassigned := unass',
              unflushed := unfl', wvec := wvec', arena := arena', wstk := wstk', wlen := wlen',
              wusable := wu', fuel := fuel', confl_type := ctype', confl_ref := cref',
              confl_lit0 := c0', confl_lit1 := c1', oom := oom' } }
          have hlit1 : (((v <<< (1 : Nat)) ||| 1#64).setWidth 32).toNat <
              2 * st_p0.core.cur_vars := by rw [ft_bv64_shl1_or1_setWidth32 hv32, hcv_t0]; omega
          ft_to_group; ft_call h_trans_lit; refine ⟨c, F0, st_p0, R, rfl, hsp_p0, hclt0, hlit1,
            hm4, fun ok2 s_t1 m5 hspt1 hclt1 hcvt1 hfuelt1 huns1 hm5 => ?_⟩
          have hcv_t1 : s_t1.core.cur_vars = s1.core.cur_vars := hcvt1.trans hcv_t0
          ft_split; rotate_left; · ft_steps; exact hB (v, 20#64, ()) m5 ⟨s_t1, hspt1, hclt1,
            by rw [hfuelt1]; exact Nat.le_trans hfu4 (by rw [hfuelt0]; exact hfuell),
            Or.inr rfl, fun _ => huns1 (by cases ok2 <;> simp_all), hm5⟩
          obtain ⟨F_ct1, hwt1⟩ := hspt1.1.witness; ft_call h_propagate
          refine ⟨c, F0, F_ct1, s_t1, R, rfl, hspt1.1.lengths, hwt1, hspt1.2.2.2.2, hm5,
            fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ fuel2 _ _ _ _ _ _ _ _ m6 hlen6 hw6 _ hperm6
              hfu6 _ _ hr1_2 _ _ hm6 => ?_⟩
          have hsp_p1 := fullPropagate_sparse hspt1 rfl hlen6 hw6 hperm6
          have hfuel_p1 : fuel2.toNat ≤ s.core.fuel.toNat := Nat.le_trans hfu6
            (by rw [hfuelt1]; exact Nat.le_trans hfu4 (by rw [hfuelt0]; exact hfuell))
          ft_split
          · ft_steps; exact hB (v, 20#64, ()) m6 ⟨_, hsp_p1, hclt1, hfuel_p1, Or.inr rfl,
              fun _ => level0_unsat_of_conflict_okW hw6 hclt1 (hr1_2 ‹_›).2.2, hm6⟩
          · ft_steps; exact hJ2 (1#64, ()) m6 ⟨rfl, _, hsp_p1, hclt1, hcv_t1, hfuel_p1, hm6⟩
    · intro B L hB hL; ft_steps; exact hL s1.core.cur_vars (0#64, ()) _ ⟨_, Nat.zero_le _, rfl,
        fullSparseInv_with_ant_sz (fullSparseInv_with_probing hsp1 1#64) 100000#64,
        hcl1, rfl, hfuel1, by assumption⟩
  · intro J hJ; have hlen := hsp.1.lengths; obtain ⟨F_cur, hw⟩ := hsp.1.witness
    have hcl_lt : s.core.cur_level < 2 ^ 64 := by
      have := hw.cur_level_le; have := (ft_bnds hlen.core_ok).2.2.2; omega
    ft_split
    · ft_call h_backtrack
      have htl0 : ((Arg.imm 0).val : Val i64).toNat = 0 := by decide
      refine ⟨c, s, R, rfl, hlen, hcl_lt, (fun hpos => by
          have := hlen.core_ok.cur_vars_le; have := hw.cur_level_le
          have := hlen.core_ok.trail_end_le; rw [htl0] at hpos ⊢; omega), hw.trail_lits_lt, hm,
        fun _ _ _ _ _ _ _ _ _ _ _ hlen1 _ _ hcl1 hpr1 _ _ _ hw1 _ hm1 => hJ () _ ⟨_,
          fullBacktrack_sparse hsp rfl hlen1 hpr1 hw1, by simp [hcl1], Nat.le_refl _, hm1⟩⟩
    · ft_steps
      have hcl0' : s.core.cur_level = 0 := by
        simpa [Nat.mod_eq_of_lt hcl_lt] using
          congrArg BitVec.toNat (‹BitVec.ofNat 64 s.core.cur_level = 0#64›)
      exact hJ () m ⟨s, hsp, hcl0', Nat.le_refl _, hm⟩
end MainWpProofs
end LeanQbe.T.Examples.Kissat.Full
