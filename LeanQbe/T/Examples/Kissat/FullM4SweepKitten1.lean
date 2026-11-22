module

public import LeanQbe.T.Examples.Kissat.FullM4SweepSpec

/-!
# Kissat `D-Full` M4b — 512-Var `kitten` Core Preservation & `7/12` `Func.wp` Proofs (`Part 1`)

1. Pure bitvector, list, semantic model-set (`SemEntails`), trail-entailment, and refutation
   lemmas (`k5_trail_entails`, `k5_conflict_unsat_lvl0`, `k5_conflict_unsat_assumps`,
   `k5_falsified_assump_unsat`).
2. Structural preservation for `K512Inv`: `k5WatchStep`, `k5AssignStep`, queue updates,
   `K5BtLoopInv`, `init`, `add_clause`, and `add_live`.
3. Parametric `(Γ : Env)` `Func.wp` proofs for `7/24` functions:
   - `full_k512_watch_wp`, `full_k512_assign_wp`, `full_k512_mtf_wp`, `full_k512_backtrack_wp`,
     `full_k512_init_wp`, `full_k512_add_clause_wp`, `full_k512_add_live_wp`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM4Sweep

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0HeadStep
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open Kraken.Bedrock2.Test

open scoped K512MemATactics

/-! ## 1. Pure Bitvector, List, & `SemEntails` Helpers -/

theorem k5_bv32_one : (1 : BitVec 32) = 1#32 := rfl

theorem k5_shl1_toNat (x : BitVec 32) :
    (x <<< (1 : Nat)).toNat = 2 * x.toNat % 2 ^ 32 := by
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm]

theorem k5_nat_xor1_cases (l : Nat) :
    (l = 2 * (l / 2) ∧ (l ^^^ 1) = 2 * (l / 2) + 1) ∨
    (l = 2 * (l / 2) + 1 ∧ (l ^^^ 1) = 2 * (l / 2)) := by
  have h := litNeg_eq l
  unfold litNeg at h
  rcases Nat.mod_two_eq_zero_or_one l with hm | hm
  · left; simp [hm] at h; omega
  · right; simp [hm] at h; omega

theorem k5_nat_xor1_xor1 (l : Nat) : (l ^^^ 1) ^^^ 1 = l := by
  rcases k5_nat_xor1_cases l with ⟨_, _⟩ | ⟨_, _⟩ <;>
    rcases k5_nat_xor1_cases (l ^^^ 1) with ⟨_, _⟩ | ⟨_, _⟩ <;> omega

theorem k5_litNeg_eq_xor1 (l : Nat) : l ^^^ 1 = litNeg l := rfl

theorem k5_slab_drop_exact {α : Type _} (p s : List α) {k : Nat} (hk : p.length = k) :
    (p ++ s).drop k = s := by
  rw [List.drop_append_of_le_length (by omega), ← hk, List.drop_length, List.nil_append]

theorem k5_fullState_lengthsOk_scratch {c : FullCfg} {s : FullState} {scr' : List (BitVec 32)}
    (hlen : s.LengthsOk c) (hscr : scr'.length = c.scratch_cap) :
    ({ s with scratch := { s.scratch with scratch_buf := scr' } } : FullState).LengthsOk c :=
  ⟨hlen.core_ok, { hlen.scratch_ok with scratch_buf_len := hscr }⟩

theorem k5_list_nodup_getElem_inj {α : Type} {xs : List α} (hnd : xs.Nodup)
    {i j : Nat} (hi : i < xs.length) (hj : j < xs.length) (hij : xs[i] = xs[j]) : i = j := by
  induction xs generalizing i j with
  | nil => simp at hi
  | cons x tl ih =>
    rcases List.nodup_cons.mp hnd with ⟨hnot, hnd_tl⟩
    cases i <;> cases j
    · rfl
    · exfalso; simp only [List.getElem_cons_zero, List.getElem_cons_succ] at hij
      exact hnot (hij ▸ List.getElem_mem (by simp at hj; omega))
    · exfalso; simp only [List.getElem_cons_zero, List.getElem_cons_succ] at hij
      exact hnot (hij ▸ List.getElem_mem (by simp at hi; omega))
    · simp only [List.getElem_cons_succ] at hij
      exact congrArg Nat.succ (ih hnd_tl (by simp at hi; omega) (by simp at hj; omega) hij)

theorem k5_nodup_subset_length {n : Nat} :
    ∀ {xs : List Nat}, xs.Nodup → (∀ x ∈ xs, x < n) → xs.length ≤ n := by
  induction n with
  | zero =>
    intro xs _ hlt; cases xs with
    | nil => simp
    | cons x _ => exact absurd (hlt x List.mem_cons_self) (by omega)
  | succ k ih =>
    intro xs hnd hlt
    by_cases hmem : k ∈ xs
    · have hnd' := hnd.erase k
      have hlt' : ∀ x ∈ xs.erase k, x < k := fun x hx => by
        have hne : x ≠ k := fun h => by subst h; exact List.Nodup.not_mem_erase hnd hx
        have := hlt x (List.mem_of_mem_erase hx); omega
      have hle := ih hnd' hlt'
      have hlen := List.length_erase_of_mem hmem
      omega
    · have hle := ih hnd (fun x hx => by
        have := hlt x hx; have : x ≠ k := fun h => hmem (h ▸ hx); omega)
      omega

theorem k5_nodup_mem_of_length_ge {n : Nat} {xs : List Nat} (hnd : xs.Nodup)
    (hlt : ∀ x ∈ xs, x < n) (hlen : n ≤ xs.length) {v : Nat} (hv : v < n) : v ∈ xs := by
  by_cases hmem : v ∈ xs
  · exact hmem
  · exfalso
    have hle := k5_nodup_subset_length (List.nodup_cons.mpr ⟨hmem, hnd⟩) fun x hx => by
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact hv
      · exact hlt x hx'
    simp at hle; omega

private theorem k5_count_set_eq {α : Type} [BEq α] [LawfulBEq α] (xs : List α) {i : Nat}
    (hi : i < xs.length) (v a : α) :
    (xs.set i v).count a + (if xs[i] == a then 1 else 0) =
      xs.count a + (if v == a then 1 else 0) := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x tl ih =>
    cases i with
    | zero => simp [List.count_cons]; omega
    | succ i' =>
      simp only [List.set_cons_succ, List.count_cons, List.getElem_cons_succ]
      have := ih (i := i') (by simp at hi; omega); omega

theorem k5_list_swap_perm {α : Type} [BEq α] [LawfulBEq α] (xs : List α) {i j : Nat}
    (hi : i < xs.length) (hj : j < xs.length) :
    ((xs.set i xs[j]).set j xs[i]).Perm xs := by
  rw [List.perm_iff_count]; intro a
  have h1 := k5_count_set_eq xs hi xs[j] a
  have h2 := k5_count_set_eq (xs.set i xs[j]) (i := j) (by simp [hj]) xs[i] a
  by_cases hij : i = j
  · subst hij; simp only [List.getElem_set_self] at h2; omega
  · simp only [List.getElem_set_ne hij] at h2; omega

theorem k5_drop_take_set_swap {α : Type} [BEq α] [LawfulBEq α] (xs : List α) {off sz p q : Nat}
    (hp : p < sz) (hq : q < sz) (hbd : off + sz ≤ xs.length) :
    (((xs.set (off + p) (xs[off + q]'(by omega))).set (off + q)
        (xs[off + p]'(by omega))).drop off |>.take sz).Perm ((xs.drop off).take sz) := by
  have hlen : ((xs.drop off).take sz).length = sz := by simp; omega
  have h1 : (((xs.set (off + p) (xs[off + q]'(by omega))).set (off + q)
      (xs[off + p]'(by omega))).drop off).take sz =
      (((xs.drop off).take sz).set p (((xs.drop off).take sz)[q]'(by omega))).set q
        (((xs.drop off).take sz)[p]'(by omega)) := by
    apply List.ext_getElem?; intro k
    by_cases hk : k < sz
    · have hk1 : k < (((xs.set (off + p) xs[off + q]).set (off + q) xs[off + p]).drop off
          |>.take sz).length := by simp; omega
      have hk2 : k < ((((xs.drop off).take sz).set p ((xs.drop off).take sz)[q]).set q
          ((xs.drop off).take sz)[p]).length := by simp [hlen]; exact hk
      rw [List.getElem?_eq_getElem hk1, List.getElem?_eq_getElem hk2]
      simp only [List.getElem_take, List.getElem_drop, Option.some.injEq]
      by_cases hkq : k = q
      · subst hkq
        rw [List.getElem_set_self (by simp; omega), List.getElem_set_self (by simp [hlen, hq])]
      · rw [List.getElem_set_ne (by omega), List.getElem_set_ne (Ne.symm hkq)]
        by_cases hkp : k = p
        · subst hkp
          rw [List.getElem_set_self (by simp; omega), List.getElem_set_self (by simp [hlen, hp])]
        · rw [List.getElem_set_ne (by omega), List.getElem_set_ne (Ne.symm hkp)]
          simp [List.getElem_take, List.getElem_drop]
    · have hk1 : (((xs.set (off + p) xs[off + q]).set (off + q) xs[off + p]).drop off
          |>.take sz).length ≤ k := by simp; omega
      have hk2 : ((((xs.drop off).take sz).set p ((xs.drop off).take sz)[q]).set q
          ((xs.drop off).take sz)[p]).length ≤ k := by simp [hlen]; omega
      rw [List.getElem?_eq_none hk1, List.getElem?_eq_none hk2]
  rw [h1]; exact k5_list_swap_perm ((xs.drop off).take sz) (by omega) (by omega)

theorem k5_drop_take_set_out {α : Type} (xs : List α) {off sz idx : Nat} (v : α)
    (hout : idx < off ∨ off + sz ≤ idx) :
    ((xs.set idx v).drop off).take sz = (xs.drop off).take sz := by
  apply List.ext_getElem
  · simp [List.length_take, List.length_drop, List.length_set]
  · intro k hk1 _
    have : k < sz ∧ off + k < xs.length := by simp at hk1; omega
    simp only [List.getElem_take, List.getElem_drop]
    rw [List.getElem_set_ne (by omega)]

theorem k5_list_flatten_set_perm {α : Type} (xs : List (List α)) {i : Nat} (hi : i < xs.length)
    (a : α) : (xs.set i (a :: xs[i])).flatten.Perm (a :: xs.flatten) := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x tl ih =>
    cases i with
    | zero => simp
    | succ i' =>
      simp only [List.set_cons_succ, List.flatten_cons, List.getElem_cons_succ]
      exact (List.Perm.append_left x (ih (by simp at hi; omega))).trans List.perm_middle

theorem SemEntails.mono {P P' : (Nat → Bool) → Prop} {cl : List Nat}
    (himp : ∀ β, P' β → P β) (h : SemEntails P cl) : SemEntails P' cl :=
  fun β hβ => h β (himp β hβ)

theorem SemEntails.subset {P : (Nat → Bool) → Prop} {c1 c2 : List Nat}
    (hsub : ∀ l ∈ c1, l ∈ c2) (h : SemEntails P c1) : SemEntails P c2 := fun β hβ => by
  obtain ⟨l, hl, hs⟩ := (clause_sat_cnfClause_iff β c1).mp (h β hβ)
  exact (clause_sat_cnfClause_iff β c2).mpr ⟨l, hsub l hl, hs⟩

theorem SemEntails.perm {P : (Nat → Bool) → Prop} {c1 c2 : List Nat}
    (hp : c1.Perm c2) (h : SemEntails P c1) : SemEntails P c2 :=
  h.subset fun _ hl => hp.mem_iff.mp hl

theorem SemEntails.unsat_of_nil {P : (Nat → Bool) → Prop} (h : SemEntails P []) :
    ∀ β, ¬ P β := fun β hβ => by
  obtain ⟨_, hm, _⟩ := (clause_sat_cnfClause_iff β []).mp (h β hβ); cases hm

theorem SemEntails.unit_of_falsified {P : (Nat → Bool) → Prop} {c : List Nat} {u : Nat}
    (hc : SemEntails P c)
    (hoth : ∀ x ∈ c, x ≠ u → SemEntails P [x ^^^ 1]) : SemEntails P [u] := fun β hβ => by
  obtain ⟨x, hx, hxs⟩ := (clause_sat_cnfClause_iff β c).mp (hc β hβ)
  by_cases hxu : x = u
  · rw [hxu] at hxs; exact (sat_cnfClause_singleton β u).mpr hxs
  · have hneg := hoth x hx hxu β hβ
    exact absurd ((sat_cnfClause_singleton β x).mpr hxs)
      ((sat_cnfClause_litNeg_iff β x).mp hneg)

theorem SemEntails.unsat_of_falsified {P : (Nat → Bool) → Prop} {c : List Nat}
    (hc : SemEntails P c) (hfals : ∀ x ∈ c, SemEntails P [x ^^^ 1]) : ∀ β, ¬ P β := fun β hβ => by
  obtain ⟨x, hx, hxs⟩ := (clause_sat_cnfClause_iff β c).mp (hc β hβ)
  exact (sat_cnfClause_litNeg_iff β x).mp (hfals x hx β hβ) ((sat_cnfClause_singleton β x).mpr hxs)

theorem SemEntails.resolve {P : (Nat → Bool) → Prop} {p : Nat} {c1 c2 res : List Nat}
    (h1 : SemEntails P c1) (h2 : SemEntails P c2)
    (hr1 : ∀ l ∈ c1, l ≠ p → l ∈ res) (hr2 : ∀ l ∈ c2, l ≠ p ^^^ 1 → l ∈ res) :
    SemEntails P res := fun β hβ => by
  obtain ⟨l1, hm1, hs1⟩ := (clause_sat_cnfClause_iff β c1).mp (h1 β hβ)
  by_cases h1p : l1 = p
  · subst h1p
    obtain ⟨l2, hm2, hs2⟩ := (clause_sat_cnfClause_iff β c2).mp (h2 β hβ)
    by_cases h2p : l2 = l1 ^^^ 1
    · rw [h2p] at hs2
      exact absurd ((sat_cnfClause_singleton β l1).mpr hs1)
        ((sat_cnfClause_litNeg_iff β l1).mp ((sat_cnfClause_singleton β (litNeg l1)).mpr hs2))
    · exact (clause_sat_cnfClause_iff β res).mpr ⟨l2, hr2 l2 hm2 h2p, hs2⟩
  · exact (clause_sat_cnfClause_iff β res).mpr ⟨l1, hr1 l1 hm1 h1p, hs1⟩

theorem K512Inv.mono_P {acap : Nat} {P P' : (Nat → Bool) → Prop} {ks : K512State}
    (himp : ∀ β, P' β → P β) (h : K512Inv acap P ks) : K512Inv acap P' ks :=
  { shapes := h.shapes
    clauses := { h.clauses with
      cl_wf := fun cid hc => let w := h.clauses.cl_wf cid hc
        ⟨w.1, w.2.1, w.2.2.1, w.2.2.2.mono himp⟩
      incons_ok := fun hi β hβ => h.clauses.incons_ok hi β (himp β hβ) }
    watches := h.watches
    assign := { h.assign with
      lvl0_ok := fun i hi hl0 => let w := h.assign.lvl0_ok i hi hl0
        ⟨w.1, w.2.1, w.2.2.mono himp⟩ }
    reasons := h.reasons }

theorem K512ScratchInv.mono_P {P P' : (Nat → Bool) → Prop} {scr : List (BitVec 32)}
    (himp : ∀ β, P' β → P β) (h : K512ScratchInv P scr) : K512ScratchInv P' scr :=
  ⟨h.1, h.2.1, h.2.2.mono_P himp⟩

/-! ## 2. Trail, Clause-Literal, & Refutation Helpers -/

theorem k5_mem_clauseLits_iff {ks : K512State} {cid : Nat}
    (hbd : k5ClauseOff ks cid + k5ClauseSize ks cid ≤ ks.arena.length) {l : Nat} :
    l ∈ k5ClauseLits ks cid ↔
      ∃ n < k5ClauseSize ks cid, (ks.arena[k5ClauseOff ks cid + n]?.getD 0#32).toNat = l := by
  unfold k5ClauseLits; rw [List.mem_map]; constructor
  · rintro ⟨b, hb, rfl⟩; rw [List.mem_iff_getElem] at hb; obtain ⟨n, hn, rfl⟩ := hb
    have hns : n < k5ClauseSize ks cid := by simp [List.length_take] at hn; omega
    have hlt : k5ClauseOff ks cid + n < ks.arena.length := by omega
    exact ⟨n, hns, by simp [List.getElem_take, List.getElem_drop, List.getElem?_eq_getElem hlt]⟩
  · rintro ⟨n, hn, rfl⟩
    have hlt : k5ClauseOff ks cid + n < ks.arena.length := by omega
    refine ⟨ks.arena[k5ClauseOff ks cid + n]'hlt, ?_, by simp [List.getElem?_eq_getElem hlt]⟩
    rw [List.mem_iff_getElem]
    exact ⟨n, by simp [List.length_take, List.length_drop]; omega,
      by simp [List.getElem_take, List.getElem_drop]⟩

theorem k5_mem_trailLits_of_lt {ks : K512State} {i : Nat}
    (hi : i < ks.trl_end.toNat) (hle : ks.trl_end.toNat ≤ ks.trl.length) :
    (ks.trl[i]?.getD 0#32).toNat ∈ k5TrailLits ks := by
  unfold k5TrailLits; rw [List.mem_map]
  refine ⟨ks.trl[i]'(by omega), ?_,
    by simp [List.getElem?_eq_getElem (by omega : i < ks.trl.length)]⟩
  rw [List.mem_iff_getElem]; exact ⟨i, by simp [List.length_take]; omega, by simp⟩

theorem k5_mem_trailDecisions_iff {ks : K512State} {d : Nat}
    (hle : ks.trl_end.toNat ≤ ks.trl.length) :
    d ∈ k5TrailDecisions ks ↔
      ∃ i < ks.trl_end.toNat, (ks.trl[i]?.getD 0#32).toNat = d ∧
        0 < (ks.lvlArr[d / 2]?.getD 0#32).toNat ∧ ks.rsn[d / 2]?.getD 0#32 = 0xFFFFFFFF#32 := by
  unfold k5TrailDecisions; rw [List.mem_filterMap]; constructor
  · rintro ⟨l, hl, hif⟩; obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hl
    have hlt : i < ks.trl_end.toNat := by simp at hi; omega
    simp only [List.getElem_take] at hif
    have h1 : i < ks.trl.length := by omega
    split at hif
    · rename_i hc; simp only [Option.some.injEq] at hif
      refine ⟨i, hlt, ?_, hif ▸ hc.1, hif ▸ hc.2⟩
      rw [List.getElem?_eq_getElem h1, Option.getD_some]; exact hif
    · simp at hif
  · rintro ⟨i, hi, hteq, hpos, hrs⟩
    have h1 : i < ks.trl.length := by omega
    refine ⟨ks.trl[i], ?_, ?_⟩
    · rw [List.mem_iff_getElem]; exact ⟨i, by simp [List.length_take]; omega, by simp⟩
    · rw [List.getElem?_eq_getElem h1, Option.getD_some] at hteq
      rw [hteq]; simp [hpos, hrs]

theorem k5_trl_nodup_var_ne {acap : Nat} {P : (Nat → Bool) → Prop} {ks : K512State}
    (hsh : ks.ShapesOk acap) (hnv : ks.nv.toNat ≤ k5MaxV) (hba : K512BaseAssignOk P ks)
    {i j : Nat} (hi : i < ks.trl_end.toNat) (hj : j < ks.trl_end.toNat) (hne : i ≠ j) :
    (ks.trl[i]?.getD 0#32).toNat / 2 ≠ (ks.trl[j]?.getD 0#32).toNat / 2 := by
  have hlen : ks.trl_end.toNat ≤ ks.trl.length := by
    rw [hsh.trl_len]; have := hba.trl_end_le; unfold k5MaxV at hnv; omega
  have hnd := hba.trl_nodup; unfold k5TrailLits at hnd; rw [List.map_map] at hnd
  have hm_len : (List.map ((fun x => x / 2) ∘ BitVec.toNat)
      (ks.trl.take ks.trl_end.toNat)).length = ks.trl_end.toNat := by simp [List.length_take]; omega
  intro heq
  exact hne (k5_list_nodup_getElem_inj hnd (by omega) (by omega) (by
    simp only [List.getElem_map, List.getElem_take, Function.comp_def]
    rw [List.getElem?_eq_getElem (by omega : i < ks.trl.length),
      List.getElem?_eq_getElem (by omega : j < ks.trl.length), Option.getD_some,
      Option.getD_some] at heq
    exact heq))

theorem k5_trl_end_lt_of_unassigned {acap : Nat} {P : (Nat → Bool) → Prop} {ks : K512State}
    (hsh : ks.ShapesOk acap) (hnv : ks.nv.toNat ≤ k5MaxV) (hba : K512BaseAssignOk P ks)
    {l : Nat} (hl : l < 2 * ks.nv.toNat) (h0 : ks.vals[l]?.getD 0#32 = 0#32) :
    ks.trl_end.toNat < ks.nv.toNat := by
  have hle := hba.trl_end_le
  by_cases hlt : ks.trl_end.toNat < ks.nv.toNat
  · exact hlt
  · exfalso
    have htrl_len : ks.trl_end.toNat ≤ ks.trl.length := by
      rw [hsh.trl_len]; unfold k5MaxV at hnv; omega
    let vs := (k5TrailLits ks).map (· / 2)
    have hv_mem := k5_nodup_mem_of_length_ge (n := ks.nv.toNat) hba.trl_nodup (fun x hx => by
      rw [List.mem_map] at hx; obtain ⟨t, ht, rfl⟩ := hx; have := hba.trl_lt t ht; omega)
      (by simp [k5TrailLits, List.length_take]; omega) (v := l / 2) (by omega)
    rw [List.mem_map] at hv_mem; obtain ⟨t, ht, htv⟩ := hv_mem
    unfold k5TrailLits at ht; rw [List.mem_map] at ht; obtain ⟨bv, hbv, rfl⟩ := ht
    obtain ⟨i, hi, heq_bv⟩ := List.getElem_of_mem hbv
    have hi_te : i < ks.trl_end.toNat := by simp [List.length_take] at hi; omega
    simp only [List.getElem_take] at heq_bv
    have hnz := (hba.vals_nz_iff_trl l hl).mpr ⟨i, hi_te, by
      rw [List.getElem?_eq_getElem (by omega : i < ks.trl.length), Option.getD_some, heq_bv]
      exact htv⟩
    exact hnz h0

theorem k5_vals_xor1_zero {acap : Nat} {P : (Nat → Bool) → Prop} {ks : K512State}
    (hinv : K512Inv acap P ks) {l : Nat} (hl : l < 2 * ks.nv.toNat)
    (hz : ks.vals[l]?.getD 0#32 = 0#32) : ks.vals[l ^^^ 1]?.getD 0#32 = 0#32 := by
  have hnl : l ^^^ 1 < 2 * ks.nv.toNat := by
    rcases k5_nat_xor1_cases l with ⟨_, _⟩ | ⟨_, _⟩ <;> omega
  rcases hinv.assign.vals_dom (l ^^^ 1) hnl with h0 | h1 | h2
  · exact h0
  · exfalso; have hneg := (hinv.assign.vals_neg_iff (l ^^^ 1) hnl).mp h1
    rw [k5_nat_xor1_xor1, hz] at hneg; cases hneg
  · exfalso; have hneg := (hinv.assign.vals_neg_iff l hl).mpr h2; rw [hz] at hneg; cases hneg

theorem k5_falsified_to_trail {acap : Nat} {P : (Nat → Bool) → Prop} {ks : K512State}
    (_hsh : ks.ShapesOk acap) (_hnv : ks.nv.toNat ≤ k5MaxV) (hba : K512BaseAssignOk P ks)
    (hsync : K512TrailSynced ks) {l : Nat} (hl : l < 2 * ks.nv.toNat)
    (hfals : ks.vals[l]? = some 2#32) :
    ∃ i < ks.trl_end.toNat, (ks.trl[i]?.getD 0#32).toNat = l ^^^ 1 := by
  obtain ⟨i, hi, hveq⟩ := (hba.vals_nz_iff_trl l hl).mp (by simp [hfals])
  have hs := hsync i hi
  let tl := (ks.trl[i]?.getD 0#32).toNat
  change ks.vals[tl]? = some 1#32 ∧ ks.vals[tl ^^^ 1]? = some 2#32 at hs
  rcases (litVar_eq_iff tl l).mp (by simpa [litVar] using hveq) with heq | heq
  · rw [heq, hfals] at hs; cases hs.1
  · exact ⟨i, hi, heq⟩

theorem k5_falsified_lvl0_entails {acap : Nat} {P : (Nat → Bool) → Prop} {ks : K512State}
    (hinv : K512Inv acap P ks) (hlvl0 : ks.lvl = 0#32) {l : Nat} (hl : l < 2 * ks.nv.toNat)
    (hfals : ks.vals[l]? = some 2#32) :
    (∃ i < ks.trl_end.toNat, (ks.trl[i]?.getD 0#32).toNat = l ^^^ 1) ∧
    SemEntails P [l ^^^ 1] := by
  obtain ⟨i, hi, hveq⟩ := (hinv.assign.vals_nz_iff_trl l hl).mp (by simp [hfals])
  have htrl_len : ks.trl_end.toNat ≤ ks.trl.length := by
    rw [hinv.shapes.trl_len]; have := hinv.assign.trl_end_le; have := hinv.clauses.nv_le
    unfold k5MaxV at *; omega
  let tl := (ks.trl[i]?.getD 0#32).toNat
  have htl_lt : tl < 2 * ks.nv.toNat := hinv.assign.trl_lt tl (k5_mem_trailLits_of_lt hi htrl_len)
  have hl0 : ks.lvlArr[tl / 2]?.getD 0#32 = 0#32 := by
    have hle := hinv.assign.trl_lvl_le (tl / 2) (by omega)
    rw [hlvl0] at hle; exact BitVec.eq_of_toNat_eq (Nat.eq_zero_of_le_zero hle)
  have hok := hinv.assign.lvl0_ok i hi hl0
  change ks.vals[tl]? = some 1#32 ∧ ks.vals[tl ^^^ 1]? = some 2#32 ∧ SemEntails P [tl] at hok
  rcases (litVar_eq_iff tl l).mp (by simpa [litVar] using hveq) with heq | heq
  · rw [heq, hfals] at hok; cases hok.1
  · rw [← k5_litNeg_eq_xor1] at heq
    exact ⟨⟨i, hi, heq⟩, heq ▸ hok.2.2⟩

theorem k5_conflict_unsat_lvl0 {acap : Nat} {P : (Nat → Bool) → Prop} {ks : K512State}
    (hinv : K512Inv acap P ks) (hlvl0 : ks.lvl = 0#32) {cid : Nat} (hcid : cid < ks.nc.toNat)
    (hfals : ∀ l ∈ k5ClauseLits ks cid, ks.vals[l]? = some 2#32) : ∀ β, ¬ P β :=
  SemEntails.unsat_of_falsified (hinv.clauses.cl_wf cid hcid).2.2.2 fun l hl =>
    (k5_falsified_lvl0_entails hinv hlvl0 ((hinv.clauses.cl_wf cid hcid).2.2.1 l hl)
      (hfals l hl)).2

/-- Under `P` plus assumption units, every trail literal `trl[i]` holds whenever all positive-level
decisions are assumptions. -/
theorem k5_trail_entails_assumps {acap : Nat} {P : (Nat → Bool) → Prop} {ks : K512State}
    (hinv : K512Inv acap P ks)
    (hdec : ∀ d ∈ k5TrailDecisions ks, d ∈ k5AssumpLits ks)
    {β : Nat → Bool} (hP : P β) (hA : (unitsCnf (k5AssumpLits ks)).Sat β) :
    ∀ i < ks.trl_end.toNat, (cnfClause [(ks.trl[i]?.getD 0#32).toNat]).Sat β := by
  have htrl_len : ks.trl_end.toNat ≤ ks.trl.length := by
    rw [hinv.shapes.trl_len]; have := hinv.assign.trl_end_le; have := hinv.clauses.nv_le
    unfold k5MaxV at *; omega
  intro i
  induction i using Nat.strongRecOn with
  | _ i ih =>
    intro hi
    let l := (ks.trl[i]?.getD 0#32).toNat
    rcases hinv.reasons i hi with hrsn | ⟨hr_lt, hl_mem, hoth⟩
    · by_cases hl0 : ks.lvlArr[l / 2]?.getD 0#32 = 0#32
      · exact (hinv.assign.lvl0_ok i hi hl0).2.2 β hP
      · have hpos : 0 < (ks.lvlArr[l / 2]?.getD 0#32).toNat :=
          Nat.pos_of_ne_zero fun hz => hl0 (BitVec.eq_of_toNat_eq hz)
        have hd_mem : l ∈ k5TrailDecisions ks :=
          (k5_mem_trailDecisions_iff htrl_len).mpr ⟨i, hi, rfl, hpos, hrsn⟩
        exact (sat_unitsCnf_iff β (k5AssumpLits ks)).mp hA l (hdec l hd_mem)
    · have hce := (hinv.clauses.cl_wf _ hr_lt).2.2.2 β hP
      obtain ⟨x, hx_mem, hxs⟩ := (clause_sat_cnfClause_iff β _).mp hce
      by_cases hxl : x = l
      · rw [hxl] at hxs; exact (sat_cnfClause_singleton β l).mpr hxs
      · obtain ⟨j, hj_lt, hj_eq⟩ := hoth x hx_mem hxl
        have hjs := ih j hj_lt (Nat.lt_trans hj_lt hi)
        rw [hj_eq] at hjs
        exact absurd ((sat_cnfClause_singleton β x).mpr hxs) ((sat_cnfClause_litNeg_iff β x).mp hjs)

theorem k5_conflict_unsat_assumps {acap : Nat} {P : (Nat → Bool) → Prop} {ks : K512State}
    (hinv : K512Inv acap P ks) (hsync : K512TrailSynced ks)
    (hdec : ∀ d ∈ k5TrailDecisions ks, d ∈ k5AssumpLits ks)
    {cid : Nat} (hcid : cid < ks.nc.toNat)
    (hfals : ∀ l ∈ k5ClauseLits ks cid, ks.vals[l]? = some 2#32) :
    ∀ β, P β → ¬ (unitsCnf (k5AssumpLits ks)).Sat β := fun β hP hA => by
  obtain ⟨l, hl_mem, hls⟩ := (clause_sat_cnfClause_iff β _).mp
    ((hinv.clauses.cl_wf cid hcid).2.2.2 β hP)
  have hl_lt := (hinv.clauses.cl_wf cid hcid).2.2.1 l hl_mem
  obtain ⟨i, hi, hieq⟩ :=
    k5_falsified_to_trail hinv.shapes hinv.clauses.nv_le hinv.assign hsync hl_lt (hfals l hl_mem)
  have hts := k5_trail_entails_assumps hinv hdec hP hA i hi
  rw [hieq] at hts
  exact (sat_cnfClause_litNeg_iff β l).mp hts ((sat_cnfClause_singleton β l).mpr hls)

theorem k5_falsified_assump_unsat {acap : Nat} {P : (Nat → Bool) → Prop} {ks : K512State}
    (hinv : K512Inv acap P ks) (hsync : K512TrailSynced ks)
    (hdec : ∀ d ∈ k5TrailDecisions ks, d ∈ k5AssumpLits ks)
    {i : Nat} (hi : i < ks.nassump.toNat)
    (hfals : ks.vals[(ks.assump[i]?.getD 0#32).toNat]? = some 2#32) :
    ∀ β, P β → ¬ (unitsCnf (k5AssumpLits ks)).Sat β := fun β hP hA => by
  let a := (ks.assump[i]?.getD 0#32).toNat
  have ha_lt := hinv.clauses.assump_ok i hi
  have ha_mem : a ∈ k5AssumpLits ks := by
    unfold k5AssumpLits; rw [List.mem_map]
    have hlen : ks.nassump.toNat ≤ ks.assump.length := by
      rw [hinv.shapes.assump_len]; exact hinv.clauses.nassump_le
    refine ⟨ks.assump[i]?.getD 0#32, ?_, rfl⟩
    rw [List.mem_iff_getElem]
    exact ⟨i, by simp [List.length_take]; omega,
      by simp [List.getElem?_eq_getElem (by omega : i < ks.assump.length)]⟩
  have hsa := (sat_unitsCnf_iff β (k5AssumpLits ks)).mp hA a ha_mem
  obtain ⟨j, hj, hjeq⟩ :=
    k5_falsified_to_trail hinv.shapes hinv.clauses.nv_le hinv.assign hsync ha_lt hfals
  have hts := k5_trail_entails_assumps hinv hdec hP hA j hj
  rw [hjeq] at hts
  exact (sat_cnfClause_litNeg_iff β a).mp hts hsa

/-! ## 3. Watch-Chain & Structural Preservation Lemmas -/

theorem K5WChain.congr {wn1 wn2 : List (BitVec 32)} {hd : BitVec 32} {ws : List Nat}
    (hc : K5WChain wn1 hd ws) (hcongr : ∀ w ∈ ws, wn1[w]? = wn2[w]?) : K5WChain wn2 hd ws := by
  induction hc with
  | nil => exact K5WChain.nil
  | @cons w ws hw _ ih =>
    have hw2 : w < wn2.length := by
      have heq := hcongr w List.mem_cons_self
      rw [List.getElem?_eq_getElem hw] at heq
      exact (List.getElem?_eq_some_iff.mp heq.symm).1
    have hnxt : wn1[w]'hw = wn2[w]'hw2 := by
      have heq := hcongr w List.mem_cons_self
      rw [List.getElem?_eq_getElem hw, List.getElem?_eq_getElem hw2] at heq
      exact Option.some.inj heq
    have ih' := ih fun x hx => hcongr x (List.mem_cons_of_mem _ hx)
    rw [hnxt] at ih'; exact K5WChain.cons hw2 ih'

theorem K5WChain.lt_length {wn : List (BitVec 32)} {hd : BitVec 32} {ws : List Nat}
    (hc : K5WChain wn hd ws) : ∀ w ∈ ws, w < wn.length := by
  induction hc with
  | nil => intro _ hm; nomatch hm
  | @cons w ws hw _ ih =>
    intro x hx; rcases List.mem_cons.mp hx with rfl | hmem
    · exact hw
    · exact ih x hmem

theorem K5WChain_cases {wn : List (BitVec 32)} {hd : BitVec 32} {ws : List Nat}
    (hc : K5WChain wn hd ws) :
    (hd = 0xFFFFFFFF#32 ∧ ws = []) ∨
    (∃ w ws', ∃ (hw : w < wn.length),
      hd = BitVec.ofNat 32 w ∧ ws = w :: ws' ∧ K5WChain wn (wn[w]'hw) ws') := by
  cases hc with
  | nil => exact Or.inl ⟨rfl, rfl⟩
  | @cons w ws' hw ht => exact Or.inr ⟨w, ws', hw, rfl, rfl, ht⟩

theorem K5WChain.unique {wn : List (BitVec 32)} {hd : BitVec 32} {ws1 ws2 : List Nat}
    (hwn : wn.length < 2 ^ 32) (h1 : K5WChain wn hd ws1) (h2 : K5WChain wn hd ws2) :
    ws1 = ws2 := by
  induction h1 generalizing ws2 with
  | nil =>
    rcases K5WChain_cases h2 with ⟨_, rfl⟩ | ⟨w, _, hw, h2eq, _, _⟩
    · rfl
    · exfalso; have h2 := congrArg BitVec.toNat h2eq
      simp [Nat.mod_eq_of_lt (Nat.lt_trans hw hwn)] at h2; omega
  | @cons w1 ws1' hw1 _ ih =>
    rcases K5WChain_cases h2 with ⟨h2eq, _⟩ | ⟨w2, ws2', hw2, h2eq, rfl, ht2⟩
    · exfalso; have h2 := congrArg BitVec.toNat h2eq
      simp [Nat.mod_eq_of_lt (Nat.lt_trans hw1 hwn)] at h2; omega
    · have h12 : w1 = w2 := by
        have ht := congrArg BitVec.toNat h2eq
        rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (Nat.lt_trans hw1 hwn), Nat.mod_eq_of_lt (Nat.lt_trans hw2 hwn)] at ht
      subst h12; exact congrArg (w1 :: ·) (ih ht2)

theorem K5WChain_getElem_of_eq {wn : List (BitVec 32)} {hd : BitVec 32} {ws : List Nat}
    (hc : K5WChain wn hd ws) (hne : hd ≠ 0xFFFFFFFF#32) :
    ∃ w ws', ∃ (hw : w < wn.length), ws = w :: ws' ∧ hd = BitVec.ofNat 32 w ∧
      K5WChain wn (wn[w]'hw) ws' := by
  rcases K5WChain_cases hc with ⟨heq, _⟩ | ⟨w, ws', hw, rfl, rfl, htail⟩
  · exact absurd heq hne
  · exact ⟨w, ws', hw, rfl, rfl, htail⟩

theorem K5WChain_nil_iff {wn : List (BitVec 32)} {hd : BitVec 32} {ws : List Nat}
    (hwn : wn.length < 2 ^ 32) (hc : K5WChain wn hd ws) : hd = 0xFFFFFFFF#32 → ws = [] := by
  intro heq
  rcases K5WChain_cases hc with ⟨_, rfl⟩ | ⟨w, _, hw, h2eq, _, _⟩
  · rfl
  · exfalso
    have h2 : (BitVec.ofNat 32 w).toNat = (0xFFFFFFFF#32 : BitVec 32).toNat :=
      congrArg BitVec.toNat (h2eq.symm.trans heq)
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans hw hwn),
      show (0xFFFFFFFF#32 : BitVec 32).toNat = 2 ^ 32 - 1 by decide] at h2; omega

theorem k5WatchStep0_preserves_shapes {acap : Nat} {ks : K512State} (h : ks.ShapesOk acap)
    (w l vo : BitVec 32) : (k5WatchStep0 ks w l vo).ShapesOk acap :=
  { h with whead_len := by simp [k5WatchStep0, h.whead_len]
           wnext_len := by simp [k5WatchStep0, h.wnext_len]
           wblit_len := by simp [k5WatchStep0, h.wblit_len] }

theorem k5WatchStep_preserves_shapes {acap : Nat} {ks : K512State} (h : ks.ShapesOk acap)
    (cid l0 l1 : BitVec 32) : (k5WatchStep ks cid l0 l1).ShapesOk acap :=
  k5WatchStep0_preserves_shapes (k5WatchStep0_preserves_shapes h _ _ _) _ _ _

theorem k5WatchStep0_preserves_watches_with {acap : Nat} {ks : K512State} (hsh : ks.ShapesOk acap)
    {chains : List (List Nat)} (hlen : chains.length = 2 * ks.nv.toNat) (hnd : chains.flatten.Nodup)
    (hwc : ∀ x < 2 * ks.nv.toNat,
      K5WChain ks.wnext (ks.whead[x]?.getD 0xFFFFFFFF#32) (chains[x]?.getD []))
    (hbnd : ∀ x < 2 * ks.nv.toNat, ∀ u ∈ chains[x]?.getD [],
      u < 2 * ks.nc.toNat ∧ 2 ≤ k5ClauseSize ks (u / 2) ∧
      (ks.arena[k5ClauseOff ks (u / 2) + (u % 2)]?.getD 0#32).toNat = x ∧
      (ks.wblit[u]?.getD 0#32).toNat < 2 * ks.nv.toNat)
    {w l vo : BitVec 32} (hw_nc : w.toNat < 2 * ks.nc.toNat) (hw_max : ks.nc.toNat ≤ k5MaxCl)
    (hnv : ks.nv.toNat ≤ k5MaxV) (hl : l.toNat < 2 * ks.nv.toNat) (hvo : vo.toNat < 2 * ks.nv.toNat)
    (hsz : 2 ≤ k5ClauseSize ks (w.toNat / 2))
    (hlit : (ks.arena[k5ClauseOff ks (w.toNat / 2) + (w.toNat % 2)]?.getD 0#32).toNat = l.toNat)
    (hfresh : w.toNat ∉ chains.flatten) :
    let ks' := k5WatchStep0 ks w l vo
    let chains' := chains.set l.toNat (w.toNat :: chains[l.toNat]'(by omega))
    chains'.length = 2 * ks'.nv.toNat ∧ chains'.flatten.Nodup ∧
    (∀ x < 2 * ks'.nv.toNat,
      K5WChain ks'.wnext (ks'.whead[x]?.getD 0xFFFFFFFF#32) (chains'[x]?.getD [])) ∧
    (∀ x < 2 * ks'.nv.toNat, ∀ u ∈ chains'[x]?.getD [],
      u < 2 * ks'.nc.toNat ∧ 2 ≤ k5ClauseSize ks' (u / 2) ∧
      (ks'.arena[k5ClauseOff ks' (u / 2) + (u % 2)]?.getD 0#32).toNat = x ∧
      (ks'.wblit[u]?.getD 0#32).toNat < 2 * ks'.nv.toNat) ∧
    (∀ u, u ∈ chains'.flatten ↔ u = w.toNat ∨ u ∈ chains.flatten) := by
  intro ks' chains'
  have hl_ch : l.toNat < chains.length := by omega
  have hwi_len : w.toNat < ks.wnext.length := by rw [hsh.wnext_len]; unfold k5MaxCl at hw_max; omega
  have hwbi_len : w.toNat < ks.wblit.length := by
    rw [hsh.wblit_len]; unfold k5MaxCl at hw_max; omega
  have hwh_len : l.toNat < ks.whead.length := by rw [hsh.whead_len]; unfold k5MaxV at hnv; omega
  have hnd' : chains'.flatten.Nodup :=
    (k5_list_flatten_set_perm chains hl_ch w.toNat).nodup_iff.mpr (List.nodup_cons.mpr ⟨hfresh,
      hnd⟩)
  have hperm : ∀ u, u ∈ chains'.flatten ↔ u = w.toNat ∨ u ∈ chains.flatten := fun u => by
    rw [(k5_list_flatten_set_perm chains hl_ch w.toNat).mem_iff, List.mem_cons]
  refine ⟨by simp [chains', ks', k5WatchStep0, hlen], hnd', ?_, ?_, hperm⟩
  · intro x hx
    change x < 2 * ks.nv.toNat at hx
    have hx_ch : x < chains.length := by omega
    have hch_old := hwc x hx; rw [List.getElem?_eq_getElem hx_ch, Option.getD_some] at hch_old
    have hcl_x : x < chains'.length := by simp [chains', hx_ch]
    by_cases hxl : x = l.toNat
    · subst hxl; rw [List.getElem?_eq_getElem hcl_x, Option.getD_some]
      simp only [chains', List.getElem_set_self]
      have hwh' : ks'.whead[l.toNat]?.getD 0xFFFFFFFF#32 = w := by
        simp [ks', k5WatchStep0, List.getElem?_set_self hwh_len]
      rw [hwh']
      have hw_lt' : w.toNat < ks'.wnext.length := by simp [ks', k5WatchStep0, hwi_len]
      have hget : ks'.wnext[w.toNat]'hw_lt' = ks.whead[l.toNat]?.getD 0xFFFFFFFF#32 := by
        simp [ks', k5WatchStep0, List.getElem?_eq_getElem hwh_len]
      have htail : K5WChain ks'.wnext (ks'.wnext[w.toNat]'hw_lt') chains[l.toNat] := by
        rw [hget]; refine hch_old.congr fun u hu => ?_
        have hune : u ≠ w.toNat := fun heq => hfresh (by
          rw [← heq]; exact List.mem_flatten.mpr ⟨chains[l.toNat], List.getElem_mem hx_ch, hu⟩)
        exact (List.getElem?_set_ne hune.symm).symm
      simpa [BitVec.ofNat_toNat] using K5WChain.cons hw_lt' htail
    · rw [List.getElem?_eq_getElem hcl_x, Option.getD_some]
      simp only [chains', List.getElem_set_ne (Ne.symm hxl)]
      have hwh' : ks'.whead[x]?.getD 0xFFFFFFFF#32 = ks.whead[x]?.getD 0xFFFFFFFF#32 := by
        simp [ks', k5WatchStep0, List.getElem?_set_ne (Ne.symm hxl)]
      rw [hwh']; refine hch_old.congr fun u hu => ?_
      have hune : u ≠ w.toNat := fun heq => hfresh (by
        rw [← heq]; exact List.mem_flatten.mpr ⟨chains[x], List.getElem_mem hx_ch, hu⟩)
      exact (List.getElem?_set_ne hune.symm).symm
  · intro x hx u hu
    change x < 2 * ks.nv.toNat at hx
    have hx_ch : x < chains.length := by omega
    have hcl_x : x < chains'.length := by simp [chains', hx_ch]
    rw [List.getElem?_eq_getElem hcl_x, Option.getD_some] at hu
    by_cases hxl : x = l.toNat
    · subst hxl; simp only [chains', List.getElem_set_self] at hu
      rcases List.mem_cons.mp hu with rfl | hu_old
      · exact ⟨hw_nc, hsz, hlit, by simp [ks', k5WatchStep0, List.getElem?_set_self hwbi_len, hvo]⟩
      · obtain ⟨h1, h2, h3, h4⟩ := hbnd l.toNat hx u
          (by simpa [List.getElem?_eq_getElem hx_ch] using hu_old)
        have hune : u ≠ w.toNat := fun heq => hfresh (by
          rw [← heq]; exact List.mem_flatten.mpr ⟨chains[l.toNat], List.getElem_mem hx_ch, hu_old⟩)
        exact ⟨h1, h2, h3, by
          rw [show ks'.wblit[u]? = ks.wblit[u]? from List.getElem?_set_ne hune.symm]; exact h4⟩
    · simp only [chains', List.getElem_set_ne (Ne.symm hxl)] at hu
      obtain ⟨h1, h2, h3, h4⟩ := hbnd x hx u (by simpa [List.getElem?_eq_getElem hx_ch] using hu)
      have hune : u ≠ w.toNat := fun heq => hfresh (by
        rw [← heq]; exact List.mem_flatten.mpr ⟨chains[x], List.getElem_mem hx_ch, hu⟩)
      exact ⟨h1, h2, h3, by
        rw [show ks'.wblit[u]? = ks.wblit[u]? from List.getElem?_set_ne hune.symm]; exact h4⟩

theorem k5WatchStep_preserves_watches {acap : Nat} {ks : K512State} (hsh : ks.ShapesOk acap)
    (hw : K512WatchesOk ks) {cid l0 l1 : BitVec 32} (hc_lt : cid.toNat < ks.nc.toNat)
    (hc_max : ks.nc.toNat ≤ k5MaxCl) (hnv : ks.nv.toNat ≤ k5MaxV)
    (hl0 : l0.toNat < 2 * ks.nv.toNat) (hl1 : l1.toNat < 2 * ks.nv.toNat)
    (hsz : 2 ≤ k5ClauseSize ks cid.toNat)
    (hlit0 : (ks.arena[k5ClauseOff ks cid.toNat]?.getD 0#32).toNat = l0.toNat)
    (hlit1 : (ks.arena[k5ClauseOff ks cid.toNat + 1]?.getD 0#32).toNat = l1.toNat)
    (hfwd : ∀ chains : List (List Nat), chains.length = 2 * ks.nv.toNat → chains.flatten.Nodup →
      (∀ x < 2 * ks.nv.toNat,
        K5WChain ks.wnext (ks.whead[x]?.getD 0xFFFFFFFF#32) (chains[x]?.getD [])) →
      2 * cid.toNat ∉ chains.flatten ∧ 2 * cid.toNat + 1 ∉ chains.flatten) :
    K512WatchesOk (k5WatchStep ks cid l0 l1) := by
  obtain ⟨chains, hlen, hnd, hwc, hbnd⟩ := hw
  obtain ⟨hf0, hf1⟩ := hfwd chains hlen hnd hwc
  have hw0 := k5_bv32_cid_w0 hc_lt (by unfold k5MaxCl at hc_max; omega)
  have hw1 := k5_bv32_cid_w1 hc_lt (by unfold k5MaxCl at hc_max; omega)
  let w0 := cid <<< 1; let w1 := w0 ||| 1#32
  have hw0_tn : w0.toNat = 2 * cid.toNat := hw0.1
  have hw1_tn : w1.toNat = 2 * cid.toNat + 1 := hw1.1
  have hstep0 := k5WatchStep0_preserves_watches_with hsh hlen hnd hwc hbnd
    (w := w0) (l := l0) (vo := l1) (by omega) hc_max hnv hl0 hl1
    (by rw [hw0_tn, show 2 * cid.toNat / 2 = cid.toNat by omega]; exact hsz)
    (by rw [hw0_tn, show 2 * cid.toNat / 2 = cid.toNat by omega,
      show 2 * cid.toNat % 2 = 0 by omega]; exact hlit0)
    (by rw [hw0_tn]; exact hf0)
  have hsh0 := k5WatchStep0_preserves_shapes hsh w0 l0 l1
  have h1 := k5WatchStep0_preserves_watches_with hsh0 hstep0.1 hstep0.2.1 hstep0.2.2.1
    hstep0.2.2.2.1 (w := w1) (l := l1) (vo := l0)
    (by change w1.toNat < 2 * ks.nc.toNat; omega)
    hc_max hnv hl1 hl0
    (by dsimp only [k5WatchStep0, k5ClauseSize]
        rw [hw1_tn, show (2 * cid.toNat + 1) / 2 = cid.toNat by omega]; exact hsz)
    (by dsimp only [k5WatchStep0, k5ClauseOff]
        rw [hw1_tn, show (2 * cid.toNat + 1) / 2 = cid.toNat by omega,
          show (2 * cid.toNat + 1) % 2 = 1 by omega]; exact hlit1)
    (fun hm => by rcases (hstep0.2.2.2.2 w1.toNat).mp hm with heq | hmem
                  · omega
                  · exact hf1 (by rwa [← hw1_tn]))
  exact ⟨_, h1.1, h1.2.1, h1.2.2.1, h1.2.2.2.1⟩

theorem k5AssignStep_preserves_shapes {acap : Nat} {ks : K512State} (h : ks.ShapesOk acap)
    (lit rsn : BitVec 32) : (k5AssignStep ks lit rsn).ShapesOk acap :=
  { h with lvlArr_len := by simp [k5AssignStep, h.lvlArr_len]
           rsn_len := by simp [k5AssignStep, h.rsn_len]
           trl_len := by simp [k5AssignStep, h.trl_len]
           flags_len := by simp [k5AssignStep, h.flags_len]
           vals_len := by simp [k5AssignStep, h.vals_len] }

private theorem k5_flags_bit1_preserved (fl : BitVec 32) (b : Bool) :
    ((if b then fl ||| 1#32 else fl &&& ~~~1#32) &&& 2#32) = (fl &&& 2#32) := by
  cases b <;> ext i hi
  · simp only [Bool.false_eq_true, ↓reduceIte, BitVec.getElem_and, BitVec.getElem_not]
    have h1 : (1#32 : BitVec 32)[i] = false ∨ (2#32 : BitVec 32)[i] = false := by
      revert i hi; decide
    rcases h1 with h | h <;> simp [h]
  · simp only [↓reduceIte, BitVec.getElem_and, BitVec.getElem_or]
    have h1 : (1#32 : BitVec 32)[i] = false ∨ (2#32 : BitVec 32)[i] = false := by
      revert i hi; decide
    rcases h1 with h | h <;> simp [h]

theorem k5AssignStep_preserves_inv {acap : Nat} {P : (Nat → Bool) → Prop} {ks : K512State}
    (hinv : K512Inv acap P ks) (hsync : K512TrailSynced ks)
    {lit rsn : BitVec 32} (hlit : lit.toNat < 2 * ks.nv.toNat)
    (hun : ks.vals[lit.toNat]? = some 0#32)
    (hlvl0 : ks.lvl = 0#32 → SemEntails P [lit.toNat])
    (hdec : 0 < ks.lvl.toNat → rsn = 0xFFFFFFFF#32 →
      ∀ i < ks.trl_end.toNat, ks.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32 ≠ ks.lvl)
    (hrsn_ok : rsn = 0xFFFFFFFF#32 ∨
      (rsn.toNat < ks.nc.toNat ∧ lit.toNat ∈ k5ClauseLits ks rsn.toNat ∧
       ∀ x ∈ k5ClauseLits ks rsn.toNat, x ≠ lit.toNat →
         ∃ j < ks.trl_end.toNat, (ks.trl[j]?.getD 0#32).toNat = x ^^^ 1)) :
    K512Inv acap P (k5AssignStep ks lit rsn) ∧ K512TrailSynced (k5AssignStep ks lit rsn) := by
  let ks' := k5AssignStep ks lit rsn
  have hsh' := k5AssignStep_preserves_shapes hinv.shapes lit rsn
  have hnv := hinv.clauses.nv_le
  have hte_lt := k5_trl_end_lt_of_unassigned hinv.shapes hnv hinv.assign hlit (by simp [hun])
  have hun_pos : 0 < ks.unass.toNat := by have := hinv.assign.unass_eq; omega
  have e_te : ks'.trl_end.toNat = ks.trl_end.toNat + 1 := by
    dsimp only [ks', k5AssignStep]; unfold k5MaxV at hnv; bv_omega
  have e_un : ks'.unass.toNat = ks.unass.toNat - 1 := by
    dsimp only [ks', k5AssignStep]; simp only [hun_pos, ite_true]; bv_omega
  have hnl_eq : (lit ^^^ 1#32).toNat = lit.toNat ^^^ 1 := by simp
  have hv_eq : (lit >>> 1).toNat = lit.toNat / 2 := (k5_bv32_div2_lt hlit).1
  have hlit_1024 : lit.toNat < 1024 := by unfold k5MaxV at hnv; omega
  have hnl_1024 : lit.toNat ^^^ 1 < 1024 := by
    rcases k5_nat_xor1_cases lit.toNat with ⟨_, _⟩ | ⟨_, _⟩ <;> unfold k5MaxV at hnv <;> omega
  have hv_512 : lit.toNat / 2 < 512 := by unfold k5MaxV at hnv; omega
  have hte_512 : ks.trl_end.toNat < 512 := by unfold k5MaxV at hnv; omega
  have hne_nl : lit.toNat ≠ lit.toNat ^^^ 1 := by
    rcases k5_nat_xor1_cases lit.toNat with ⟨_, _⟩ | ⟨_, _⟩ <;> omega
  have hnot_trl : ∀ i < ks.trl_end.toNat, (ks.trl[i]?.getD 0#32).toNat / 2 ≠ lit.toNat / 2 := by
    intro i hi heq; have hnz := (hinv.assign.vals_nz_iff_trl lit.toNat hlit).mpr ⟨i, hi, heq⟩
    simp [hun] at hnz
  have hvals_lit : ks'.vals[lit.toNat]? = some 1#32 := by
    dsimp only [ks', k5AssignStep]
    rw [hnl_eq, List.getElem?_set_ne hne_nl.symm,
      List.getElem?_set_self (by rw [hinv.shapes.vals_len]; omega)]
  have hvals_nl : ks'.vals[lit.toNat ^^^ 1]? = some 2#32 := by
    dsimp only [ks', k5AssignStep]
    rw [hnl_eq, List.getElem?_set_self (by simp [hinv.shapes.vals_len]; omega)]
  have hvals_other : ∀ x, x / 2 ≠ lit.toNat / 2 → ks'.vals[x]? = ks.vals[x]? := fun x hne => by
    have hx1 : lit.toNat ≠ x := by
      rcases k5_nat_xor1_cases x with ⟨_, _⟩ | ⟨_, _⟩ <;>
        rcases k5_nat_xor1_cases lit.toNat with ⟨_, _⟩ | ⟨_, _⟩ <;> omega
    have hx2 : lit.toNat ^^^ 1 ≠ x := by
      rcases k5_nat_xor1_cases x with ⟨_, _⟩ | ⟨_, _⟩ <;>
        rcases k5_nat_xor1_cases lit.toNat with ⟨_, _⟩ | ⟨_, _⟩ <;> omega
    dsimp only [ks', k5AssignStep]; rw [hnl_eq, List.getElem?_set_ne hx2, List.getElem?_set_ne hx1]
  have htrl_lt_idx : ∀ i < ks.trl_end.toNat, ks'.trl[i]? = ks.trl[i]? := fun i hi => by
    dsimp only [ks', k5AssignStep]; exact List.getElem?_set_ne (by omega)
  have htrl_end_idx : ks'.trl[ks.trl_end.toNat]? = some lit := by
    dsimp only [ks', k5AssignStep]
    exact List.getElem?_set_self (by rw [hinv.shapes.trl_len]; omega)
  have hlvl_other : ∀ v, v ≠ lit.toNat / 2 → ks'.lvlArr[v]? = ks.lvlArr[v]? := fun v hne => by
    dsimp only [ks', k5AssignStep]; rw [hv_eq]; exact List.getElem?_set_ne hne.symm
  have hlvl_v : ks'.lvlArr[lit.toNat / 2]? = some ks.lvl := by
    dsimp only [ks', k5AssignStep]; rw [hv_eq]
    exact List.getElem?_set_self (by rw [hinv.shapes.lvlArr_len]; omega)
  have hrsn_other : ∀ v, v ≠ lit.toNat / 2 → ks'.rsn[v]? = ks.rsn[v]? := fun v hne => by
    dsimp only [ks', k5AssignStep]; rw [hv_eq]; exact List.getElem?_set_ne hne.symm
  have hrsn_v : ks'.rsn[lit.toNat / 2]? = some rsn := by
    dsimp only [ks', k5AssignStep]; rw [hv_eq]
    exact List.getElem?_set_self (by rw [hinv.shapes.rsn_len]; omega)
  have hcl' : K512ClausesOk acap P ks' :=
    { hinv.clauses with
      flags_clean := fun v hv => by
        by_cases hvv : v = lit.toNat / 2
        · subst hvv
          have hfl : ks'.flags[lit.toNat / 2]?.getD 0#32 =
              if (lit &&& 1#32) ≠ 0#32 then ks.flags[lit.toNat / 2]?.getD 0#32 ||| 1#32
              else ks.flags[lit.toNat / 2]?.getD 0#32 &&& ~~~1#32 := by
            dsimp only [ks', k5AssignStep]
            rw [hv_eq, List.getElem?_set_self (by rw [hinv.shapes.flags_len]; omega),
              Option.getD_some]
          rw [hfl]
          by_cases hc : (lit &&& 1#32) ≠ 0#32
          · simpa [hc] using (k5_flags_bit1_preserved
            (ks.flags[lit.toNat / 2]?.getD 0#32) true).trans
              (hinv.clauses.flags_clean (lit.toNat / 2) hv)
          · simpa [hc] using (k5_flags_bit1_preserved
            (ks.flags[lit.toNat / 2]?.getD 0#32) false).trans
              (hinv.clauses.flags_clean (lit.toNat / 2) hv)
        · have hf : ks'.flags[v]? = ks.flags[v]? := by
            dsimp only [ks', k5AssignStep]; rw [hv_eq]; exact List.getElem?_set_ne (Ne.symm hvv)
          rw [hf]; exact hinv.clauses.flags_clean v hv }
  have hsync' : K512TrailSynced ks' := fun i hi => by
    rw [e_te] at hi
    by_cases hie : i = ks.trl_end.toNat
    · subst hie
      change ks'.vals[(ks'.trl[ks.trl_end.toNat]?.getD 0#32).toNat]? = some 1#32 ∧
        ks'.vals[(ks'.trl[ks.trl_end.toNat]?.getD 0#32).toNat ^^^ 1]? = some 2#32
      rw [htrl_end_idx, Option.getD_some]; exact ⟨hvals_lit, hvals_nl⟩
    · have hi' : i < ks.trl_end.toNat := by omega
      let l := (ks.trl[i]?.getD 0#32).toNat
      have hne_v := hnot_trl i hi'
      have hne_vx : (l ^^^ 1) / 2 ≠ lit.toNat / 2 := by
        rcases k5_nat_xor1_cases l with ⟨_, _⟩ | ⟨_, _⟩ <;> omega
      change ks'.vals[(ks'.trl[i]?.getD 0#32).toNat]? = some 1#32 ∧
        ks'.vals[(ks'.trl[i]?.getD 0#32).toNat ^^^ 1]? = some 2#32
      rw [htrl_lt_idx i hi']; change ks'.vals[l]? = some 1#32 ∧ ks'.vals[l ^^^ 1]? = some 2#32
      rw [hvals_other l hne_v, hvals_other (l ^^^ 1) hne_vx]; exact hsync i hi'
  have htrl_take : ks'.trl.take ks'.trl_end.toNat = ks.trl.take ks.trl_end.toNat ++ [lit] := by
    apply List.ext_getElem
    · have hlt' : ks'.trl.length = 512 := hsh'.trl_len
      simp [List.length_take, e_te, hlt', hinv.shapes.trl_len]; unfold k5MaxV at hnv; omega
    · intro i hi1 hi2
      have h1 : i < ks.trl_end.toNat + 1 := by simp [List.length_take, e_te] at hi1; omega
      simp only [List.getElem_take]
      by_cases hie : i = ks.trl_end.toNat
      · subst hie
        have hgl : ks'.trl[ks.trl_end.toNat]'(by rw [hsh'.trl_len]; omega) = lit := by
          have := htrl_end_idx; rw [List.getElem?_eq_getElem (by rw [hsh'.trl_len]; omega)] at this
          exact Option.some.inj this
        rw [hgl, List.getElem_append_right (by
          simp [List.length_take, hinv.shapes.trl_len]; unfold k5MaxV at hnv; omega)]
        simp [List.length_take, hinv.shapes.trl_len,
          show min ks.trl_end.toNat 512 = ks.trl_end.toNat by omega]
      · have hi' : i < ks.trl_end.toNat := by omega
        have hgl : ks'.trl[i]'(by rw [hsh'.trl_len]; omega) =
            ks.trl[i]'(by rw [hinv.shapes.trl_len]; omega) := by
          have := htrl_lt_idx i hi'
          rw [List.getElem?_eq_getElem (by rw [hsh'.trl_len]; omega),
            List.getElem?_eq_getElem (by rw [hinv.shapes.trl_len]; omega)] at this
          exact Option.some.inj this
        rw [hgl, List.getElem_append_left (by simp [List.length_take, hinv.shapes.trl_len]; omega),
          List.getElem_take]
  have hba' : K512BaseAssignOk P ks' := by
    refine ⟨by rw [e_te]; change ks.trl_end.toNat + 1 ≤ ks.nv.toNat; omega,
      by rw [e_te]; change ks.prop.toNat ≤ ks.trl_end.toNat + 1; have := hinv.assign.prop_le; omega,
      by rw [e_un, e_te]; change (ks.unass.toNat - 1) + (ks.trl_end.toNat + 1) = ks.nv.toNat
         have := hinv.assign.unass_eq; omega,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro l hl; by_cases hv : l / 2 = lit.toNat / 2
      · rcases k5_nat_xor1_cases l with ⟨_, _⟩ | ⟨_, _⟩ <;>
          rcases k5_nat_xor1_cases lit.toNat with ⟨_, _⟩ | ⟨_, _⟩
        · rw [show l = lit.toNat by omega, hvals_lit]; exact Or.inr (Or.inl rfl)
        · rw [show l = lit.toNat ^^^ 1 by omega, hvals_nl]; exact Or.inr (Or.inr rfl)
        · rw [show l = lit.toNat ^^^ 1 by omega, hvals_nl]; exact Or.inr (Or.inr rfl)
        · rw [show l = lit.toNat by omega, hvals_lit]; exact Or.inr (Or.inl rfl)
      · rw [hvals_other l hv]; exact hinv.assign.vals_dom l hl
    · intro l hl; by_cases hv : l / 2 = lit.toNat / 2
      · rcases k5_nat_xor1_cases l with ⟨_, _⟩ | ⟨_, _⟩ <;>
          rcases k5_nat_xor1_cases lit.toNat with ⟨_, _⟩ | ⟨_, _⟩
        · rw [show l = lit.toNat by omega, hvals_lit, hvals_nl]; simp
        · rw [show l = lit.toNat ^^^ 1 by omega, k5_nat_xor1_xor1, hvals_nl, hvals_lit]; simp
        · rw [show l = lit.toNat ^^^ 1 by omega, k5_nat_xor1_xor1, hvals_nl, hvals_lit]; simp
        · rw [show l = lit.toNat by omega, hvals_lit, hvals_nl]; simp
      · have hvx : (l ^^^ 1) / 2 ≠ lit.toNat / 2 := by
          rcases k5_nat_xor1_cases l with ⟨_, _⟩ | ⟨_, _⟩ <;> omega
        rw [hvals_other l hv, hvals_other (l ^^^ 1) hvx]; exact hinv.assign.vals_neg_iff l hl
    · intro l hl; constructor
      · intro hnz; by_cases hv : l / 2 = lit.toNat / 2
        · exact ⟨ks.trl_end.toNat, by rw [e_te]; omega,
            by rw [htrl_end_idx, Option.getD_some]; exact hv.symm⟩
        · rw [hvals_other l hv] at hnz
          obtain ⟨i, hi, hiv⟩ := (hinv.assign.vals_nz_iff_trl l hl).mp hnz
          exact ⟨i, by rw [e_te]; omega, by rw [htrl_lt_idx i hi]; exact hiv⟩
      · rintro ⟨i, hi, hiv⟩; rw [e_te] at hi
        by_cases hie : i = ks.trl_end.toNat
        · subst hie; rw [htrl_end_idx, Option.getD_some] at hiv
          rcases k5_nat_xor1_cases l with ⟨_, _⟩ | ⟨_, _⟩ <;>
            rcases k5_nat_xor1_cases lit.toNat with ⟨_, _⟩ | ⟨_, _⟩
          · rw [show l = lit.toNat by omega, hvals_lit]; decide
          · rw [show l = lit.toNat ^^^ 1 by omega, hvals_nl]; decide
          · rw [show l = lit.toNat ^^^ 1 by omega, hvals_nl]; decide
          · rw [show l = lit.toNat by omega, hvals_lit]; decide
        · have hi' : i < ks.trl_end.toNat := by omega
          rw [htrl_lt_idx i hi'] at hiv
          have hv : l / 2 ≠ lit.toNat / 2 := by rw [← hiv]; exact hnot_trl i hi'
          rw [hvals_other l hv]; exact (hinv.assign.vals_nz_iff_trl l hl).mpr ⟨i, hi', hiv⟩
    · unfold k5TrailLits; rw [htrl_take, List.map_append, List.map_append, List.nodup_append]
      refine ⟨hinv.assign.trl_nodup, by simp, fun x hx y hy heq => ?_⟩
      simp only [List.map_cons, List.map_nil, List.mem_singleton] at hy; subst hy; subst heq
      rw [List.mem_map] at hx; obtain ⟨l0, hl0, hlv⟩ := hx
      rw [List.mem_map] at hl0; obtain ⟨b, hb, rfl⟩ := hl0
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
      have hi' : i < ks.trl_end.toNat := by simp [List.length_take] at hi; omega
      simp only [List.getElem_take] at hlv
      exact hnot_trl i hi'
        (by rw [List.getElem?_eq_getElem (by rw [hinv.shapes.trl_len]; omega), Option.getD_some]
            exact hlv)
    · intro l hl; unfold k5TrailLits at hl; rw [htrl_take, List.map_append, List.mem_append] at hl
      rcases hl with hl | hl
      · exact hinv.assign.trl_lt l hl
      · simp at hl; subst hl; exact hlit
    · intro v hv; by_cases hvv : v = lit.toNat / 2
      · subst hvv; rw [hlvl_v, Option.getD_some]; exact Nat.le_refl _
      · rw [hlvl_other v hvv]; exact hinv.assign.trl_lvl_le v hv
    · intro v hv hz
      have hne : v ≠ lit.toNat / 2 := fun h => by
        subst h; rcases k5_nat_xor1_cases lit.toNat with ⟨he, _⟩ | ⟨_, hx⟩
        · rw [← he, hvals_lit] at hz; cases hz
        · rw [← hx, hvals_nl] at hz; cases hz
      rw [hvals_other (2 * v) (by omega)] at hz
      rw [hlvl_other v hne, hrsn_other v hne]; exact hinv.assign.unass_lvl_zero v hv hz
    · intro i j hij hj; rw [e_te] at hj
      by_cases hje : j = ks.trl_end.toNat
      · subst hje; rw [htrl_end_idx, Option.getD_some, hlvl_v, Option.getD_some]
        by_cases hie : i = ks.trl_end.toNat
        · subst hie; rw [htrl_end_idx, Option.getD_some, hlvl_v, Option.getD_some]
          exact Nat.le_refl _
        · have hi' : i < ks.trl_end.toNat := by omega
          rw [htrl_lt_idx i hi', hlvl_other _ (hnot_trl i hi')]
          have hli := hinv.assign.trl_lt _
            (k5_mem_trailLits_of_lt hi' (by rw [hinv.shapes.trl_len]; omega))
          exact hinv.assign.trl_lvl_le _ (by omega)
      · have hj' : j < ks.trl_end.toNat := by omega
        have hi' : i < ks.trl_end.toNat := by omega
        rw [htrl_lt_idx i hi', htrl_lt_idx j hj', hlvl_other _ (hnot_trl i hi'),
          hlvl_other _ (hnot_trl j hj')]
        exact hinv.assign.trl_lvl_mono i j hij hj'
    · intro i j hji hi hpos hlvl_eq; rw [e_te] at hi
      by_cases hie : i = ks.trl_end.toNat
      · subst hie
        have hj' : j < ks.trl_end.toNat := by omega
        rw [htrl_end_idx, Option.getD_some, hlvl_v, Option.getD_some] at hpos hlvl_eq
        rw [htrl_lt_idx j hj', hlvl_other _ (hnot_trl j hj')] at hlvl_eq
        rw [htrl_end_idx, Option.getD_some, hrsn_v, Option.getD_some]
        intro hrs_eq; exact hdec hpos hrs_eq j hj' hlvl_eq
      · have hi' : i < ks.trl_end.toNat := by omega
        have hj' : j < ks.trl_end.toNat := by omega
        rw [htrl_lt_idx i hi', hlvl_other _ (hnot_trl i hi')] at hpos hlvl_eq
        rw [htrl_lt_idx j hj', hlvl_other _ (hnot_trl j hj')] at hlvl_eq
        rw [htrl_lt_idx i hi', hrsn_other _ (hnot_trl i hi')]
        exact hinv.assign.dec_earliest i j hji hi' hpos hlvl_eq
    · intro i hi; dsimp only; intro hl0; rw [e_te] at hi
      by_cases hie : i = ks.trl_end.toNat
      · subst hie
        rw [htrl_end_idx, Option.getD_some, hlvl_v, Option.getD_some] at hl0
        rw [htrl_end_idx, Option.getD_some]; exact ⟨hvals_lit, hvals_nl, hlvl0 hl0⟩
      · have hi' : i < ks.trl_end.toNat := by omega
        let l := (ks.trl[i]?.getD 0#32).toNat
        have hne_v := hnot_trl i hi'
        have hne_vx : (l ^^^ 1) / 2 ≠ lit.toNat / 2 := by
          rcases k5_nat_xor1_cases l with ⟨_, _⟩ | ⟨_, _⟩ <;> omega
        rw [htrl_lt_idx i hi'] at hl0 ⊢
        change ks'.lvlArr[l / 2]?.getD 0#32 = 0#32 at hl0
        rw [hlvl_other (l / 2) hne_v] at hl0
        change ks'.vals[l]? = some 1#32 ∧ ks'.vals[l ^^^ 1]? = some 2#32 ∧ SemEntails P [l]
        rw [hvals_other l hne_v, hvals_other (l ^^^ 1) hne_vx]; exact hinv.assign.lvl0_ok i hi' hl0
  have hre' : K512ReasonOk ks' := fun i hi => by
    rw [e_te] at hi
    by_cases hie : i = ks.trl_end.toNat
    · subst hie
      change let l := (ks'.trl[ks.trl_end.toNat]?.getD 0#32).toNat
             let r := ks'.rsn[l / 2]?.getD 0#32; _
      rw [htrl_end_idx, Option.getD_some, hrsn_v, Option.getD_some]
      rcases hrsn_ok with rfl | ⟨hr_lt, hmem, hoth⟩
      · exact Or.inl rfl
      · right; refine ⟨hr_lt, hmem, fun x hx hne => ?_⟩
        obtain ⟨j, hj, hje⟩ := hoth x hx hne
        exact ⟨j, hj, by rw [htrl_lt_idx j hj]; exact hje⟩
    · have hi' : i < ks.trl_end.toNat := by omega
      change let l := (ks'.trl[i]?.getD 0#32).toNat; let r := ks'.rsn[l / 2]?.getD 0#32; _
      rw [htrl_lt_idx i hi', hrsn_other _ (hnot_trl i hi')]
      rcases hinv.reasons i hi' with hnone | ⟨hr_lt, hmem, hoth⟩
      · exact Or.inl hnone
      · right; refine ⟨hr_lt, hmem, fun x hx hne => ?_⟩
        obtain ⟨j, hj, hje⟩ := hoth x hx hne
        exact ⟨j, hj, by rw [htrl_lt_idx j (Nat.lt_trans hj hi')]; exact hje⟩
  exact ⟨⟨hsh', hcl', hinv.watches, hba', hre'⟩, hsync'⟩

theorem k5SetQueue_preserves_inv {acap : Nat} {P : (Nat → Bool) → Prop} {ks : K512State}
    (hinv : K512Inv acap P ks) {qf ql qs qst : BitVec 32} {qp qn qsa : List (BitVec 32)}
    (hp : qp.length = 512) (hn : qn.length = 512) (hs : qsa.length = 512) :
    K512Inv acap P { ks with qfirst := qf, qlast := ql, qsearch := qs, qstamp := qst,
                             qprev := qp, qnext := qn, qstampArr := qsa } :=
  ⟨{ hinv.shapes with qprev_len := hp, qnext_len := hn, qstampArr_len := hs },
   ⟨hinv.clauses.acap_ge, hinv.clauses.acap_lt, hinv.clauses.acap_eq, hinv.clauses.nv_le,
    hinv.clauses.nc_le, hinv.clauses.alen_le, hinv.clauses.nassump_le, hinv.clauses.nkl_le,
    hinv.clauses.nana_le, hinv.clauses.cl_wf, hinv.clauses.cl_mono, hinv.clauses.incons_ok,
    hinv.clauses.assump_ok, hinv.clauses.flags_clean⟩,
   hinv.watches,
   ⟨hinv.assign.trl_end_le, hinv.assign.prop_le, hinv.assign.unass_eq, hinv.assign.vals_dom,
    hinv.assign.vals_neg_iff, hinv.assign.vals_nz_iff_trl, hinv.assign.trl_nodup,
    hinv.assign.trl_lt, hinv.assign.trl_lvl_le, hinv.assign.unass_lvl_zero,
    hinv.assign.trl_lvl_mono, hinv.assign.dec_earliest, hinv.assign.lvl0_ok⟩,
   hinv.reasons⟩

theorem k5BumpPropTicks_preserves_inv {acap : Nat} {P : (Nat → Bool) → Prop} {ks : K512State}
    (hinv : K512Inv acap P ks) (hsync : K512TrailSynced ks) {pr' tk' : BitVec 32}
    (hpr : pr'.toNat ≤ ks.trl_end.toNat) :
    let ks' := (ks.putHdr .prop pr').putHdr .ticks tk'
    K512Inv acap P ks' ∧ K512TrailSynced ks' := by
  intro ks'
  refine ⟨⟨(hinv.shapes.putHdr .prop pr').putHdr .ticks tk',
    ⟨hinv.clauses.acap_ge, hinv.clauses.acap_lt, hinv.clauses.acap_eq, hinv.clauses.nv_le,
     hinv.clauses.nc_le, hinv.clauses.alen_le, hinv.clauses.nassump_le, hinv.clauses.nkl_le,
     hinv.clauses.nana_le, hinv.clauses.cl_wf, hinv.clauses.cl_mono, hinv.clauses.incons_ok,
     hinv.clauses.assump_ok, hinv.clauses.flags_clean⟩,
    hinv.watches,
    ⟨hinv.assign.trl_end_le, hpr, hinv.assign.unass_eq, hinv.assign.vals_dom,
     hinv.assign.vals_neg_iff, hinv.assign.vals_nz_iff_trl, hinv.assign.trl_nodup,
     hinv.assign.trl_lt, hinv.assign.trl_lvl_le, hinv.assign.unass_lvl_zero,
     hinv.assign.trl_lvl_mono, hinv.assign.dec_earliest, hinv.assign.lvl0_ok⟩,
    hinv.reasons⟩, hsync⟩

theorem k5SetIncons_preserves_inv {acap : Nat} {P : (Nat → Bool) → Prop} {ks : K512State}
    (hinv : K512Inv acap P ks) (hunsat : ∀ β, ¬ P β) :
    K512Inv acap P (ks.putHdr .incons 1#32) :=
  ⟨hinv.shapes.putHdr .incons 1#32,
   ⟨hinv.clauses.acap_ge, hinv.clauses.acap_lt, hinv.clauses.acap_eq, hinv.clauses.nv_le,
    hinv.clauses.nc_le, hinv.clauses.alen_le, hinv.clauses.nassump_le, hinv.clauses.nkl_le,
    hinv.clauses.nana_le, hinv.clauses.cl_wf, hinv.clauses.cl_mono, fun _ => hunsat,
    hinv.clauses.assump_ok, hinv.clauses.flags_clean⟩,
   hinv.watches,
   ⟨hinv.assign.trl_end_le, hinv.assign.prop_le, hinv.assign.unass_eq, hinv.assign.vals_dom,
    hinv.assign.vals_neg_iff, hinv.assign.vals_nz_iff_trl, hinv.assign.trl_nodup,
    hinv.assign.trl_lt, hinv.assign.trl_lvl_le, hinv.assign.unass_lvl_zero,
    hinv.assign.trl_lvl_mono, hinv.assign.dec_earliest, hinv.assign.lvl0_ok⟩,
   hinv.reasons⟩

/-! ### Backtrack Loop Invariant & Finish Lemmas -/

structure K5BtLoopInv (acap : Nat) (ks : K512State) (target_lvl te : BitVec 32)
    (st : K512State) : Prop where
  sh : st.ShapesOk acap
  te_le : te.toNat ≤ ks.trl_end.toNat
  unass_eq : st.unass.toNat + te.toNat = ks.nv.toNat
  nv_eq : st.nv = ks.nv
  nc_eq : st.nc = ks.nc
  lvl_eq : st.lvl = ks.lvl
  prop_eq : st.prop = ks.prop
  te_hdr : st.trl_end = ks.trl_end
  inc_eq : st.incons = ks.incons
  alen_eq : st.alen = ks.alen
  acap_eq : st.acap = ks.acap
  na_eq : st.nassump = ks.nassump
  nk_eq : st.nkl = ks.nkl
  nan_eq : st.nana = ks.nana
  st_eq : st.status = ks.status
  ph_eq : st.phase = ks.phase
  ht_eq : st.hdrTail = ks.hdrTail
  qs_eq : st.qstampArr = ks.qstampArr
  trl_eq : st.trl = ks.trl
  fl_eq : st.flags = ks.flags
  ass_eq : st.assump = ks.assump
  ana_eq : st.ana = ks.ana
  kl_eq : st.kl = ks.kl
  wh_eq : st.whead = ks.whead
  wn_eq : st.wnext = ks.wnext
  wb_eq : st.wblit = ks.wblit
  co_eq : st.clOff = ks.clOff
  cs_eq : st.clSz = ks.clSz
  ar_eq : st.arena = ks.arena
  kept_var : ∀ v < ks.nv.toNat,
    (∃ i < te.toNat, (ks.trl[i]?.getD 0#32).toNat / 2 = v) →
    st.lvlArr[v]? = ks.lvlArr[v]? ∧ st.rsn[v]? = ks.rsn[v]? ∧
    st.vals[2 * v]? = ks.vals[2 * v]? ∧ st.vals[2 * v + 1]? = ks.vals[2 * v + 1]?
  cleared_var : ∀ v < ks.nv.toNat,
    (¬ ∃ i < te.toNat, (ks.trl[i]?.getD 0#32).toNat / 2 = v) →
    st.lvlArr[v]? = some 0#32 ∧ st.rsn[v]? = some 0xFFFFFFFF#32 ∧
    st.vals[2 * v]? = some 0#32 ∧ st.vals[2 * v + 1]? = some 0#32
  popped_gt : ∀ i, te.toNat ≤ i → i < ks.trl_end.toNat →
    target_lvl.toNat < (ks.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat

theorem k5BtLoopInv_init {acap : Nat} {P : (Nat → Bool) → Prop} {ks : K512State}
    {target_lvl : BitVec 32} (hinv : K512Inv acap P ks) :
    K5BtLoopInv acap ks target_lvl ks.trl_end ks := by
  refine ⟨hinv.shapes, Nat.le_refl _, hinv.assign.unass_eq, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, fun _ _ _ => ⟨rfl, rfl, rfl, rfl⟩, ?_, fun i h1 h2 => by omega⟩
  intro v hv hnone
  have h0 : ks.vals[2 * v]?.getD 0#32 = 0#32 := by
    by_cases hnz : ks.vals[2 * v]?.getD 0#32 = 0#32
    · exact hnz
    · exfalso; obtain ⟨i, hi, hiv⟩ := (hinv.assign.vals_nz_iff_trl (2 * v) (by omega)).mp hnz
      exact hnone ⟨i, hi, by omega⟩
  have h1 : ks.vals[2 * v + 1]?.getD 0#32 = 0#32 := by
    by_cases hnz : ks.vals[2 * v + 1]?.getD 0#32 = 0#32
    · exact hnz
    · exfalso; obtain ⟨i, hi, hiv⟩ := (hinv.assign.vals_nz_iff_trl (2 * v + 1) (by omega)).mp hnz
      exact hnone ⟨i, hi, by omega⟩
  have hun := hinv.assign.unass_lvl_zero v hv h0
  have hnv := hinv.clauses.nv_le; unfold k5MaxV at hnv
  have hlv : v < ks.lvlArr.length := by rw [hinv.shapes.lvlArr_len]; omega
  have hrs : v < ks.rsn.length := by rw [hinv.shapes.rsn_len]; omega
  have hv0 : 2 * v < ks.vals.length := by rw [hinv.shapes.vals_len]; omega
  have hv1 : 2 * v + 1 < ks.vals.length := by rw [hinv.shapes.vals_len]; omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [List.getElem?_eq_getElem hlv] at hun ⊢; exact congrArg some hun.1
  · rw [List.getElem?_eq_getElem hrs] at hun ⊢; exact congrArg some hun.2
  · rw [List.getElem?_eq_getElem hv0] at h0 ⊢; exact congrArg some h0
  · rw [List.getElem?_eq_getElem hv1] at h1 ⊢; exact congrArg some h1

theorem k5BtLoopInv_step {acap : Nat} {P : (Nat → Bool) → Prop} {ks : K512State}
    {target_lvl te : BitVec 32} {st : K512State} (hinv : K512Inv acap P ks)
    (hbt : K5BtLoopInv acap ks target_lvl te st) (hpos : 0 < te.toNat)
    (hpop : target_lvl.toNat <
      (st.lvlArr[(ks.trl[te.toNat - 1]?.getD 0#32).toNat / 2]?.getD 0#32).toNat) :
    let lit := ks.trl[te.toNat - 1]'(by
      rw [hinv.shapes.trl_len]; have := hinv.assign.trl_end_le; have := hinv.clauses.nv_le
      have := hbt.te_le; unfold k5MaxV at *; omega)
    let v := lit.toNat / 2
    let st' := (((((st.putArr .vals lit.toNat 0#32).putArr .vals (lit ^^^ 1#32).toNat 0#32).putArr
      .lvlArr v 0#32).putArr .rsn v 0xFFFFFFFF#32).putHdr .unass (st.unass + 1#32))
    K5BtLoopInv acap ks target_lvl (te - 1#32) st' ∧
    (∀ qs, K5BtLoopInv acap ks target_lvl (te - 1#32) (st'.putHdr .qsearch qs)) := by
  intro lit v st'
  have hnv := hinv.clauses.nv_le; have hte := hbt.te_le
  have hte1_lt : te.toNat - 1 < ks.trl_end.toNat := by omega
  have htrl_len : ks.trl_end.toNat ≤ ks.trl.length := by
    rw [hinv.shapes.trl_len]; have := hinv.assign.trl_end_le; unfold k5MaxV at hnv; omega
  have hlit_lt : lit.toNat < 2 * ks.nv.toNat := by
    have hm := k5_mem_trailLits_of_lt hte1_lt htrl_len
    rw [List.getElem?_eq_getElem (by omega : te.toNat - 1 < ks.trl.length), Option.getD_some] at hm
    exact hinv.assign.trl_lt lit.toNat hm
  have hv_lt : v < ks.nv.toNat := by omega
  have hnl_eq : (lit ^^^ 1#32).toNat = lit.toNat ^^^ 1 := by simp
  have hsh' : st'.ShapesOk acap :=
    ((((hbt.sh.putArr .vals _ _).putArr .vals _ _).putArr .lvlArr _ _).putArr
      .rsn _ _).putHdr .unass _
  have hun_lt : st.unass.toNat + 1 < 2 ^ 32 := by have := hbt.unass_eq; unfold k5MaxV at hnv; omega
  have hmk : ∀ qOpt : Option (BitVec 32),
      K5BtLoopInv acap ks target_lvl (te - 1#32)
        (match qOpt with | none => st' | some qs => st'.putHdr .qsearch qs) := by
    intro qOpt
    let finSt := match qOpt with | none => st' | some qs => st'.putHdr .qsearch qs
    have hshF : finSt.ShapesOk acap := by
      cases qOpt with | none => exact hsh' | some qs => exact hsh'.putHdr .qsearch qs
    have hte_sub : (te - 1#32).toNat = te.toNat - 1 := by bv_omega
    have hunF : finSt.unass.toNat + (te - 1#32).toNat = ks.nv.toNat := by
      have hun_st : finSt.unass = st.unass + 1#32 := by
        cases qOpt <;> dsimp only [finSt, st'] <;> k5_field
      rw [hun_st, hte_sub, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      have := hbt.unass_eq; omega
    have hlvl_st : finSt.lvlArr = st.lvlArr.set v 0#32 := by
      cases qOpt <;> dsimp only [finSt, st'] <;> k5_field
    have hrsn_st : finSt.rsn = st.rsn.set v 0xFFFFFFFF#32 := by
      cases qOpt <;> dsimp only [finSt, st'] <;> k5_field
    have hvals_st : finSt.vals = (st.vals.set lit.toNat 0#32).set (lit.toNat ^^^ 1) 0#32 := by
      cases qOpt <;> dsimp only [finSt, st'] <;> k5_field <;> rw [hnl_eq]
    have hl_xor := k5_nat_xor1_cases lit.toNat
    refine ⟨hshF, by rw [hte_sub]; omega, hunF,
      by cases qOpt <;> dsimp only [finSt, st'] <;> k5_field <;> exact hbt.nv_eq,
      by cases qOpt <;> dsimp only [finSt, st'] <;> k5_field <;> exact hbt.nc_eq,
      by cases qOpt <;> dsimp only [finSt, st'] <;> k5_field <;> exact hbt.lvl_eq,
      by cases qOpt <;> dsimp only [finSt, st'] <;> k5_field <;> exact hbt.prop_eq,
      by cases qOpt <;> dsimp only [finSt, st'] <;> k5_field <;> exact hbt.te_hdr,
      by cases qOpt <;> dsimp only [finSt, st'] <;> k5_field <;> exact hbt.inc_eq,
      by cases qOpt <;> dsimp only [finSt, st'] <;> k5_field <;> exact hbt.alen_eq,
      by cases qOpt <;> dsimp only [finSt, st'] <;> k5_field <;> exact hbt.acap_eq,
      by cases qOpt <;> dsimp only [finSt, st'] <;> k5_field <;> exact hbt.na_eq,
      by cases qOpt <;> dsimp only [finSt, st'] <;> k5_field <;> exact hbt.nk_eq,
      by cases qOpt <;> dsimp only [finSt, st'] <;> k5_field <;> exact hbt.nan_eq,
      by cases qOpt <;> dsimp only [finSt, st'] <;> k5_field <;> exact hbt.st_eq,
      by cases qOpt <;> dsimp only [finSt, st'] <;> k5_field <;> exact hbt.ph_eq,
      by cases qOpt <;> dsimp only [finSt, st'] <;> k5_field <;> exact hbt.ht_eq,
      by cases qOpt <;> dsimp only [finSt, st'] <;> k5_field <;> exact hbt.qs_eq,
      by cases qOpt <;> dsimp only [finSt, st'] <;> k5_field <;> exact hbt.trl_eq,
      by cases qOpt <;> dsimp only [finSt, st'] <;> k5_field <;> exact hbt.fl_eq,
      by cases qOpt <;> dsimp only [finSt, st'] <;> k5_field <;> exact hbt.ass_eq,
      by cases qOpt <;> dsimp only [finSt, st'] <;> k5_field <;> exact hbt.ana_eq,
      by cases qOpt <;> dsimp only [finSt, st'] <;> k5_field <;> exact hbt.kl_eq,
      by cases qOpt <;> dsimp only [finSt, st'] <;> k5_field <;> exact hbt.wh_eq,
      by cases qOpt <;> dsimp only [finSt, st'] <;> k5_field <;> exact hbt.wn_eq,
      by cases qOpt <;> dsimp only [finSt, st'] <;> k5_field <;> exact hbt.wb_eq,
      by cases qOpt <;> dsimp only [finSt, st'] <;> k5_field <;> exact hbt.co_eq,
      by cases qOpt <;> dsimp only [finSt, st'] <;> k5_field <;> exact hbt.cs_eq,
      by cases qOpt <;> dsimp only [finSt, st'] <;> k5_field <;> exact hbt.ar_eq,
      ?_, ?_, ?_⟩
    · intro w hw ⟨i, hi, hiw⟩
      have hi' : i < te.toNat - 1 := by rw [hte_sub] at hi; exact hi
      have hne_v : w ≠ v := by
        rw [← hiw]
        have hnd :=
          k5_trl_nodup_var_ne hinv.shapes hnv hinv.assign (Nat.lt_trans hi' (by omega)) hte1_lt
            (by omega)
        rwa [List.getElem?_eq_getElem (by omega : te.toNat - 1 < ks.trl.length),
          Option.getD_some] at hnd
      have hold := hbt.kept_var w hw ⟨i, by omega, hiw⟩
      rw [hlvl_st, hrsn_st, hvals_st, List.getElem?_set_ne (Ne.symm hne_v),
        List.getElem?_set_ne (Ne.symm hne_v)]
      rcases hl_xor with ⟨_, _⟩ | ⟨_, _⟩ <;>
        exact ⟨hold.1, hold.2.1,
          by rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
             exact hold.2.2.1,
          by rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
             exact hold.2.2.2⟩
    · intro w hw hnone
      by_cases hwv : w = v
      · subst hwv; unfold k5MaxV at hnv
        have hlv_len : v < st.lvlArr.length := by rw [hbt.sh.lvlArr_len]; omega
        have hrs_len : v < st.rsn.length := by rw [hbt.sh.rsn_len]; omega
        have hv0_len : 2 * v < st.vals.length := by rw [hbt.sh.vals_len]; omega
        have hv1_len : 2 * v + 1 < st.vals.length := by rw [hbt.sh.vals_len]; omega
        rw [hlvl_st, hrsn_st, hvals_st, List.getElem?_set_self hlv_len,
          List.getElem?_set_self hrs_len]
        refine ⟨rfl, rfl, ?_, ?_⟩ <;> rcases hl_xor with ⟨h0a, h1a⟩ | ⟨h0a, h1a⟩
        · rw [← h0a, List.getElem?_set_ne (by omega), List.getElem?_set_self (by omega)]
        · rw [← h1a, List.getElem?_set_self (by simp; omega)]
        · rw [← h1a, List.getElem?_set_self (by simp; omega)]
        · rw [← h0a, List.getElem?_set_ne (by omega), List.getElem?_set_self (by omega)]
      · have hnone_old : ¬ ∃ i < te.toNat, (ks.trl[i]?.getD 0#32).toNat / 2 = w := by
          rintro ⟨i, hi, hiw⟩
          by_cases hie : i = te.toNat - 1
          · subst hie; rw [List.getElem?_eq_getElem (by omega : te.toNat - 1 < ks.trl.length),
              Option.getD_some] at hiw; exact hwv hiw.symm
          · exact hnone ⟨i, by rw [hte_sub]; omega, hiw⟩
        have hold := hbt.cleared_var w hw hnone_old
        rw [hlvl_st, hrsn_st, hvals_st, List.getElem?_set_ne (Ne.symm hwv),
          List.getElem?_set_ne (Ne.symm hwv)]
        rcases hl_xor with ⟨_, _⟩ | ⟨_, _⟩ <;>
          exact ⟨hold.1, hold.2.1,
            by rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
               exact hold.2.2.1,
            by rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
               exact hold.2.2.2⟩
    · intro i hlo hhi; rw [hte_sub] at hlo
      by_cases hie : i = te.toNat - 1
      · subst hie
        have hkept := hbt.kept_var v hv_lt ⟨te.toNat - 1, by omega, by
          rw [List.getElem?_eq_getElem (by omega : te.toNat - 1 < ks.trl.length), Option.getD_some]⟩
        rw [List.getElem?_eq_getElem (by omega : te.toNat - 1 < ks.trl.length),
          Option.getD_some] at hpop ⊢
        rw [hkept.1] at hpop; exact hpop
      · exact hbt.popped_gt i (by omega) hhi
  exact ⟨hmk none, fun qs => hmk (some qs)⟩

theorem k5BtLoopInv_finish {acap : Nat} {P : (Nat → Bool) → Prop} {ks : K512State}
    {target_lvl te : BitVec 32} {st : K512State} (hinv : K512Inv acap P ks)
    (hbt : K5BtLoopInv acap ks target_lvl te st)
    (hsync_below : target_lvl = 0#32 ∨ K512TrailSynced ks)
    (hexit : te = 0#32 ∨
      ∃ i < te.toNat, i = te.toNat - 1 ∧
        (st.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ target_lvl.toNat) :
    let st' := ((st.putHdr .trl_end te).putHdr .prop
      (if te.toNat < st.prop.toNat then te else st.prop)).putHdr .lvl target_lvl
    K512Inv acap P st' ∧ K512TrailSynced st' ∧ st'.lvl = target_lvl ∧
    st'.trl_end.toNat ≤ ks.trl_end.toNat ∧ K5BtPreserved ks st' ∧
    (∀ i < st'.trl_end.toNat,
      st'.trl[i]? = ks.trl[i]? ∧ st'.rsn[(st'.trl[i]?.getD 0#32).toNat / 2]? =
        ks.rsn[(st'.trl[i]?.getD 0#32).toNat / 2]? ∧
      (st'.lvlArr[(st'.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ target_lvl.toNat) := by
  intro st'
  have hnv := hinv.clauses.nv_le
  have htrl_len : ks.trl_end.toNat ≤ ks.trl.length := by
    rw [hinv.shapes.trl_len]; have := hinv.assign.trl_end_le; unfold k5MaxV at hnv; omega
  have hkept_lvl : ∀ i < te.toNat,
      (ks.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ target_lvl.toNat := by
    intro i hi
    rcases hexit with rfl | ⟨j, hj, hjeq, hle⟩
    · simp at hi
    · have hj_lt : j < ks.trl_end.toNat := Nat.lt_of_lt_of_le hj hbt.te_le
      have hlj := hinv.assign.trl_lt _ (k5_mem_trailLits_of_lt hj_lt htrl_len)
      have hkj := (hbt.kept_var _ (by omega) ⟨j, hj, rfl⟩).1
      rw [hkj] at hle
      exact Nat.le_trans (hinv.assign.trl_lvl_mono i j (by omega) hj_lt) hle
  have hsh' : st'.ShapesOk acap := ((hbt.sh.putHdr .trl_end _).putHdr .prop _).putHdr .lvl _
  have e_nv : st'.nv = ks.nv := by dsimp only [st']; k5_field; exact hbt.nv_eq
  have e_nc : st'.nc = ks.nc := by dsimp only [st']; k5_field; exact hbt.nc_eq
  have e_lvl : st'.lvl = target_lvl := by dsimp only [st']; k5_field
  have e_te : st'.trl_end = te := by dsimp only [st']; k5_field
  have e_un : st'.unass = st.unass := by dsimp only [st']; k5_field
  have e_pr : st'.prop = if te.toNat < st.prop.toNat then te else st.prop := by
    dsimp only [st']; k5_field
  have e_trl : st'.trl = ks.trl := by dsimp only [st']; k5_field; exact hbt.trl_eq
  have e_la : st'.lvlArr = st.lvlArr := by dsimp only [st']; k5_field
  have e_rs : st'.rsn = st.rsn := by dsimp only [st']; k5_field
  have e_va : st'.vals = st.vals := by dsimp only [st']; k5_field
  have hpres : K5BtPreserved ks st' :=
    { nv := e_nv, nc := e_nc, incons := by dsimp only [st']; k5_field; exact hbt.inc_eq
      alen := by dsimp only [st']; k5_field; exact hbt.alen_eq
      acap := by dsimp only [st']; k5_field; exact hbt.acap_eq
      nassump := by dsimp only [st']; k5_field; exact hbt.na_eq
      nkl := by dsimp only [st']; k5_field; exact hbt.nk_eq
      nana := by dsimp only [st']; k5_field; exact hbt.nan_eq
      status := by dsimp only [st']; k5_field; exact hbt.st_eq
      phase := by dsimp only [st']; k5_field; exact hbt.ph_eq
      hdrTail := by dsimp only [st']; k5_field; exact hbt.ht_eq
      assump := by dsimp only [st']; k5_field; exact hbt.ass_eq
      ana := by dsimp only [st']; k5_field; exact hbt.ana_eq
      kl := by dsimp only [st']; k5_field; exact hbt.kl_eq
      whead := by dsimp only [st']; k5_field; exact hbt.wh_eq
      wnext := by dsimp only [st']; k5_field; exact hbt.wn_eq
      wblit := by dsimp only [st']; k5_field; exact hbt.wb_eq
      clOff := by dsimp only [st']; k5_field; exact hbt.co_eq
      clSz := by dsimp only [st']; k5_field; exact hbt.cs_eq
      arena := by dsimp only [st']; k5_field; exact hbt.ar_eq
      flags2_eq := fun v _ => by
        have hfl : st'.flags = ks.flags := by dsimp only [st']; k5_field; exact hbt.fl_eq
        rw [hfl]
      lvlArr_kept := fun i hi => by
        rw [e_te] at hi; rw [e_trl, e_la]
        have hli :=
          hinv.assign.trl_lt _ (k5_mem_trailLits_of_lt (Nat.lt_of_lt_of_le hi hbt.te_le) htrl_len)
        exact (hbt.kept_var _ (by omega) ⟨i, hi, rfl⟩).1 }
  have hcl' : K512ClausesOk acap P st' :=
    { acap_ge := hinv.clauses.acap_ge, acap_lt := hinv.clauses.acap_lt
      acap_eq := hpres.acap.trans hinv.clauses.acap_eq
      nv_le := e_nv ▸ hinv.clauses.nv_le, nc_le := e_nc ▸ hinv.clauses.nc_le
      alen_le := hpres.alen ▸ hinv.clauses.alen_le
      nassump_le := hpres.nassump ▸ hinv.clauses.nassump_le
      nkl_le := hpres.nkl ▸ hinv.clauses.nkl_le, nana_le := hpres.nana ▸ hinv.clauses.nana_le
      cl_wf := by
        unfold k5ClauseLits k5ClauseOff k5ClauseSize
        rw [e_nc, e_nv, hpres.alen, hpres.clOff, hpres.clSz, hpres.arena]; exact hinv.clauses.cl_wf
      cl_mono := by
        unfold k5ClauseOff k5ClauseSize; rw [e_nc, hpres.clOff, hpres.clSz]
        exact hinv.clauses.cl_mono
      incons_ok := hpres.incons ▸ hinv.clauses.incons_ok
      assump_ok := by rw [e_nv, hpres.nassump, hpres.assump]; exact hinv.clauses.assump_ok
      flags_clean := fun v hv => by
        rw [e_nv] at hv; rw [hpres.flags2_eq v hv]; exact hinv.clauses.flags_clean v hv }
  have hw' : K512WatchesOk st' := by
    unfold K512WatchesOk k5ClauseSize k5ClauseOff
    rw [e_nv, e_nc, hpres.whead, hpres.wnext, hpres.wblit, hpres.clOff, hpres.clSz, hpres.arena]
    exact hinv.watches
  have hsync' : K512TrailSynced st' := fun i hi => by
    rw [e_te] at hi
    have hi_ks : i < ks.trl_end.toNat := Nat.lt_of_lt_of_le hi hbt.te_le
    let l := (ks.trl[i]?.getD 0#32).toNat
    have hl_lt : l < 2 * ks.nv.toNat := hinv.assign.trl_lt l (k5_mem_trailLits_of_lt hi_ks htrl_len)
    have hkv := hbt.kept_var (l / 2) (by omega) ⟨i, hi, rfl⟩
    have hvals_old : ks.vals[l]? = some 1#32 ∧ ks.vals[l ^^^ 1]? = some 2#32 := by
      rcases hsync_below with rfl | hsy
      · have hl0 : ks.lvlArr[l / 2]?.getD 0#32 = 0#32 :=
          BitVec.eq_of_toNat_eq (Nat.eq_zero_of_le_zero (hkept_lvl i hi))
        have h0 := hinv.assign.lvl0_ok i hi_ks hl0; exact ⟨h0.1, h0.2.1⟩
      · exact hsy i hi_ks
    change st'.vals[(st'.trl[i]?.getD 0#32).toNat]? = some 1#32 ∧
      st'.vals[(st'.trl[i]?.getD 0#32).toNat ^^^ 1]? = some 2#32
    rw [e_trl, e_va]; change st.vals[l]? = some 1#32 ∧ st.vals[l ^^^ 1]? = some 2#32
    have hpair : st.vals[l]? = ks.vals[l]? ∧ st.vals[l ^^^ 1]? = ks.vals[l ^^^ 1]? := by
      rcases k5_nat_xor1_cases l with ⟨he, hx⟩ | ⟨he, hx⟩
      · exact ⟨by rw [he]; exact hkv.2.2.1, by rw [hx]; exact hkv.2.2.2⟩
      · exact ⟨by rw [he]; exact hkv.2.2.2, by rw [hx]; exact hkv.2.2.1⟩
    rw [hpair.1, hpair.2]; exact hvals_old
  have hba' : K512BaseAssignOk P st' := by
    refine ⟨by rw [e_te, e_nv]; exact Nat.le_trans hbt.te_le hinv.assign.trl_end_le,
      by rw [e_pr, e_te]; split <;> omega,
      by rw [e_un, e_te, e_nv]; exact hbt.unass_eq,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro l hl; rw [e_nv] at hl; rw [e_va]
      by_cases hex : ∃ i < te.toNat, (ks.trl[i]?.getD 0#32).toNat / 2 = l / 2
      · have hkv := hbt.kept_var (l / 2) (by omega) hex
        rcases k5_nat_xor1_cases l with ⟨he, _⟩ | ⟨he, _⟩
        · rw [he, hkv.2.2.1, ← he]; exact hinv.assign.vals_dom l hl
        · rw [he, hkv.2.2.2, ← he]; exact hinv.assign.vals_dom l hl
      · have hcv := hbt.cleared_var (l / 2) (by omega) hex
        rcases k5_nat_xor1_cases l with ⟨he, _⟩ | ⟨he, _⟩
        · rw [he, hcv.2.2.1]; left; rfl
        · rw [he, hcv.2.2.2]; left; rfl
    · intro l hl; rw [e_nv] at hl; rw [e_va]
      by_cases hex : ∃ i < te.toNat, (ks.trl[i]?.getD 0#32).toNat / 2 = l / 2
      · have hkv := hbt.kept_var (l / 2) (by omega) hex
        have hpair : st.vals[l]? = ks.vals[l]? ∧ st.vals[l ^^^ 1]? = ks.vals[l ^^^ 1]? := by
          rcases k5_nat_xor1_cases l with ⟨he, hx⟩ | ⟨he, hx⟩
          · exact ⟨by rw [he]; exact hkv.2.2.1, by rw [hx]; exact hkv.2.2.2⟩
          · exact ⟨by rw [he]; exact hkv.2.2.2, by rw [hx]; exact hkv.2.2.1⟩
        rw [hpair.1, hpair.2]; exact hinv.assign.vals_neg_iff l hl
      · have hcv := hbt.cleared_var (l / 2) (by omega) hex
        have hpair : st.vals[l]? = some 0#32 ∧ st.vals[l ^^^ 1]? = some 0#32 := by
          rcases k5_nat_xor1_cases l with ⟨he, hx⟩ | ⟨he, hx⟩
          · exact ⟨by rw [he]; exact hcv.2.2.1, by rw [hx]; exact hcv.2.2.2⟩
          · exact ⟨by rw [he]; exact hcv.2.2.2, by rw [hx]; exact hcv.2.2.1⟩
        rw [hpair.1, hpair.2]; simp
    · intro l hl; rw [e_nv] at hl; rw [e_va, e_te, e_trl]
      by_cases hex : ∃ i < te.toNat, (ks.trl[i]?.getD 0#32).toNat / 2 = l / 2
      · refine ⟨fun _ => hex, fun _ => ?_⟩
        obtain ⟨i, hi, hiv⟩ := hex
        have hkv := hbt.kept_var (l / 2) (by omega) ⟨i, hi, hiv⟩
        have hnz := (hinv.assign.vals_nz_iff_trl l hl).mpr ⟨i, Nat.lt_of_lt_of_le hi hbt.te_le, hiv⟩
        rcases k5_nat_xor1_cases l with ⟨he, _⟩ | ⟨he, _⟩
        · rw [he, hkv.2.2.1, ← he]; exact hnz
        · rw [he, hkv.2.2.2, ← he]; exact hnz
      · have hcv := hbt.cleared_var (l / 2) (by omega) hex
        refine ⟨fun hnz => absurd ?_ hnz, fun h => absurd h hex⟩
        rcases k5_nat_xor1_cases l with ⟨he, _⟩ | ⟨he, _⟩
        · rw [he, hcv.2.2.1]; rfl
        · rw [he, hcv.2.2.2]; rfl
    · have hpf : k5TrailLits st' <+: k5TrailLits ks := by
        unfold k5TrailLits; rw [e_te, e_trl]
        exact List.IsPrefix.map BitVec.toNat (List.take_prefix_take_left hbt.te_le)
      exact hinv.assign.trl_nodup.sublist (hpf.map (· / 2)).sublist
    · intro l hl; rw [e_nv]
      have hpf : k5TrailLits st' <+: k5TrailLits ks := by
        unfold k5TrailLits; rw [e_te, e_trl]
        exact List.IsPrefix.map BitVec.toNat (List.take_prefix_take_left hbt.te_le)
      exact hinv.assign.trl_lt l (hpf.subset hl)
    · intro v hv; rw [e_nv] at hv; rw [e_la, e_lvl]
      by_cases hex : ∃ i < te.toNat, (ks.trl[i]?.getD 0#32).toNat / 2 = v
      · obtain ⟨i, hi, rfl⟩ := hex
        rw [(hbt.kept_var _ hv ⟨i, hi, rfl⟩).1]; exact hkept_lvl i hi
      · rw [(hbt.cleared_var v hv hex).1]; simp
    · intro v hv hz; rw [e_nv] at hv; rw [e_va] at hz; rw [e_la, e_rs]
      by_cases hex : ∃ i < te.toNat, (ks.trl[i]?.getD 0#32).toNat / 2 = v
      · exfalso; obtain ⟨i, hi, hiv⟩ := hex
        have hkv := hbt.kept_var v hv ⟨i, hi, hiv⟩
        rw [hkv.2.2.1] at hz
        exact (hinv.assign.vals_nz_iff_trl (2 * v) (by omega)).mpr
          ⟨i, Nat.lt_of_lt_of_le hi hbt.te_le, by omega⟩ hz
      · have hcv := hbt.cleared_var v hv hex; rw [hcv.1, hcv.2.1]; exact ⟨rfl, rfl⟩
    · intro i j hij hj; rw [e_te] at hj; rw [e_la, e_trl]
      have hi_ks := Nat.lt_of_lt_of_le (Nat.lt_of_le_of_lt hij hj) hbt.te_le
      have hj_ks := Nat.lt_of_lt_of_le hj hbt.te_le
      have hli := hinv.assign.trl_lt _ (k5_mem_trailLits_of_lt hi_ks htrl_len)
      have hlj := hinv.assign.trl_lt _ (k5_mem_trailLits_of_lt hj_ks htrl_len)
      rw [(hbt.kept_var _ (by omega) ⟨i, by omega, rfl⟩).1,
        (hbt.kept_var _ (by omega) ⟨j, hj, rfl⟩).1]
      exact hinv.assign.trl_lvl_mono i j hij hj_ks
    · intro i j hji hi hpos heq; rw [e_te] at hi
      rw [e_la, e_trl] at hpos heq; rw [e_trl, e_rs]
      have hi_ks := Nat.lt_of_lt_of_le hi hbt.te_le
      have hj_ks := Nat.lt_of_lt_of_le (Nat.lt_trans hji hi) hbt.te_le
      have hli := hinv.assign.trl_lt _ (k5_mem_trailLits_of_lt hi_ks htrl_len)
      have hlj := hinv.assign.trl_lt _ (k5_mem_trailLits_of_lt hj_ks htrl_len)
      have hki := hbt.kept_var _ (by omega) ⟨i, hi, rfl⟩
      have hkj := hbt.kept_var _ (by omega) ⟨j, Nat.lt_trans hji hi, rfl⟩
      rw [hki.1] at hpos heq; rw [hkj.1] at heq; rw [hki.2.1]
      exact hinv.assign.dec_earliest i j hji hi_ks hpos heq
    · intro i hi; dsimp only; intro hl0; rw [e_te] at hi
      have hi_ks := Nat.lt_of_lt_of_le hi hbt.te_le
      let l := (ks.trl[i]?.getD 0#32).toNat
      have hl_lt := hinv.assign.trl_lt l (k5_mem_trailLits_of_lt hi_ks htrl_len)
      have hkv := hbt.kept_var (l / 2) (by omega) ⟨i, hi, rfl⟩
      rw [e_la, e_trl] at hl0; change st.lvlArr[l / 2]?.getD 0#32 = 0#32 at hl0
      rw [hkv.1] at hl0
      have h0 := hinv.assign.lvl0_ok i hi_ks hl0
      have hsy := hsync' i (by rw [e_te]; exact hi)
      exact ⟨hsy.1, hsy.2, by rw [e_trl]; exact h0.2.2⟩
  have hre' : K512ReasonOk st' := fun i hi => by
    rw [e_te] at hi
    have hi_ks := Nat.lt_of_lt_of_le hi hbt.te_le
    let l := (ks.trl[i]?.getD 0#32).toNat
    have hl_lt := hinv.assign.trl_lt l (k5_mem_trailLits_of_lt hi_ks htrl_len)
    have hkv := hbt.kept_var (l / 2) (by omega) ⟨i, hi, rfl⟩
    change let l := (st'.trl[i]?.getD 0#32).toNat; let r := st'.rsn[l / 2]?.getD 0#32; _
    rw [e_trl, e_rs, hkv.2.1, e_nc]
    have hcl_eq : ∀ c, k5ClauseLits st' c = k5ClauseLits ks c := fun c => by
      unfold k5ClauseLits k5ClauseOff k5ClauseSize; rw [hpres.clOff, hpres.clSz, hpres.arena]
    rcases hinv.reasons i hi_ks with hnone | ⟨hr_lt, hmem, hoth⟩
    · exact Or.inl hnone
    · right; rw [hcl_eq]; exact ⟨hr_lt, hmem, hoth⟩
  refine ⟨⟨hsh', hcl', hw', hba', hre'⟩, hsync', e_lvl, by rw [e_te]; exact hbt.te_le, hpres, ?_⟩
  intro i hi; rw [e_te] at hi
  have hi_ks := Nat.lt_of_lt_of_le hi hbt.te_le
  have hl_lt := hinv.assign.trl_lt _ (k5_mem_trailLits_of_lt hi_ks htrl_len)
  have hkv := hbt.kept_var _ (by omega) ⟨i, hi, rfl⟩
  rw [e_trl, e_rs, e_la, hkv.2.1, hkv.1]; exact ⟨rfl, rfl, hkept_lvl i hi⟩

theorem k5Init_finish_inv {acap : Nat} {nv : BitVec 32} {st : K512State}
    (hsh : st.ShapesOk acap) (hge : k5MinScr - k5Base - k5SlabFixed ≤ acap) (hlt : acap <
      dimacsBound)
    (hnv_le : nv.toNat ≤ k5MaxV) (e_nv : st.nv = nv) (e_nc : st.nc = 0#32) (e_lvl : st.lvl = 0#32)
    (e_prop : st.prop = 0#32) (e_te : st.trl_end = 0#32) (e_un : st.unass = nv)
    (e_ac : st.acap = BitVec.ofNat 32 acap) (e_al : st.alen = 0#32) (e_in : st.incons = 0#32)
    (e_na : st.nassump = 0#32) (e_nk : st.nkl = 0#32) (e_nn : st.nana = 0#32)
    (hvars : ∀ v < nv.toNat, st.lvlArr[v]? = some 0#32 ∧ st.rsn[v]? = some 0xFFFFFFFF#32 ∧
      st.flags[v]? = some 0#32)
    (hlits : ∀ l < 2 * nv.toNat, st.vals[l]? = some 0#32 ∧ st.whead[l]? = some 0xFFFFFFFF#32) :
    (∀ P, K512Inv acap P st) ∧ K512TrailSynced st := by
  have hsync : K512TrailSynced st := fun i hi => by rw [e_te] at hi; simp at hi
  refine ⟨fun P => ⟨hsh, ?_, ?_, ?_, fun i hi => by rw [e_te] at hi; simp at hi⟩, hsync⟩
  · refine ⟨hge, hlt, e_ac, by rw [e_nv]; exact hnv_le, by rw [e_nc]; decide, by simp [e_al],
      by rw [e_na]; decide, by rw [e_nk]; decide, by rw [e_nn]; decide,
      fun cid hc => by rw [e_nc] at hc; simp at hc,
      fun _ _ _ hc => by rw [e_nc] at hc; simp at hc,
      fun hi => absurd e_in hi,
      fun i hi => by rw [e_na] at hi; simp at hi,
      fun v hv => by rw [e_nv] at hv; rw [(hvars v hv).2.2]; decide⟩
  · refine ⟨List.replicate (2 * nv.toNat) [], by rw [e_nv]; simp,
      by rw [List.flatten_replicate_nil]; exact List.nodup_nil, ?_, ?_⟩
    · intro l hl; rw [e_nv] at hl
      rw [(hlits l hl).2, Option.getD_some]
      simp only [List.getElem?_replicate, hl, ↓reduceIte, Option.getD_some]
      exact K5WChain.nil
    · intro l hl w hw; rw [e_nv] at hl
      simp only [List.getElem?_replicate, hl, ↓reduceIte, Option.getD_some] at hw
      cases hw
  · refine ⟨by simp [e_te], by simp [e_prop, e_te], by rw [e_un, e_te, e_nv]; simp,
      fun l hl => by rw [e_nv] at hl; rw [(hlits l hl).1]; left; rfl,
      fun l hl => by
        rw [e_nv] at hl
        have hnl : l ^^^ 1 < 2 * nv.toNat := by
          rcases k5_nat_xor1_cases l with ⟨_, _⟩ | ⟨_, _⟩ <;> omega
        rw [(hlits l hl).1, (hlits (l ^^^ 1) hnl).1]; simp,
      fun l hl => by
        rw [e_nv] at hl; rw [(hlits l hl).1]; simp [e_te],
      by unfold k5TrailLits; rw [e_te]; simp,
      fun l hl => by unfold k5TrailLits at hl; rw [e_te] at hl; simp at hl,
      fun v hv => by rw [e_nv] at hv; rw [(hvars v hv).1, e_lvl]; simp,
      fun v hv _ => by rw [e_nv] at hv; rw [(hvars v hv).1, (hvars v hv).2.1]; exact ⟨rfl, rfl⟩,
      fun _ _ _ hj => by rw [e_te] at hj; simp at hj,
      fun _ _ _ hi => by rw [e_te] at hi; simp at hi,
      fun _ hi => by rw [e_te] at hi; simp at hi⟩

/-- Appending a clause of length `sz ≥ 2` and attaching its two watches preserves `K512Inv`. -/
theorem k5AddClause_ge2_preserves {acap : Nat} {P : (Nat → Bool) → Prop} {ks : K512State}
    {ar : List (BitVec 32)} {xs : List (BitVec 32)} {sz : BitVec 32}
    (hinv : K512Inv acap P ks) (hsync : K512TrailSynced ks)
    (hnc_lt : ks.nc.toNat < k5MaxCl) (hsz2 : 2 ≤ sz.toNat) (hsz_max : sz.toNat < 2 ^ 16)
    (hsz_xs : sz.toNat ≤ xs.length) (hfit : ks.alen.toNat + sz.toNat ≤ acap)
    (har_len : ar.length = acap) (har_old : ∀ j < ks.alen.toNat, ar[j]? = ks.arena[j]?)
    (har_new : ∀ j < sz.toNat, ar[ks.alen.toNat + j]? = xs[j]?)
    (hxlits : ∀ j < sz.toNat, (xs[j]?.getD 0#32).toNat < 2 * ks.nv.toNat)
    (hent : SemEntails P ((xs.take sz.toNat).map BitVec.toNat)) :
    let stM := (((({ ks with arena := ar } : K512State).putHdr .alen (ks.alen + sz)).putArr
      .clOff ks.nc.toNat ks.alen).putArr .clSz ks.nc.toNat sz).putHdr .nc (ks.nc + 1#32)
    let ks' := k5WatchStep stM ks.nc (xs[0]'(by omega)) (xs[1]'(by omega))
    K512Inv acap P ks' ∧ K512TrailSynced ks' ∧ ks'.lvl = ks.lvl ∧ ks'.nv = ks.nv ∧
    ks'.nassump = ks.nassump ∧ ks'.assump = ks.assump ∧ ks'.trl_end = ks.trl_end ∧
    ks'.unass = ks.unass ∧ ks'.incons = ks.incons ∧
    (∀ M, (∀ j < sz.toNat, (xs[j]?.getD 0#32).toNat < 2 * M) →
      K512LitsBounded M ks → K512LitsBounded M ks') := by
  intro stM ks'
  have hacap_lt : acap < 2 ^ 28 := hinv.clauses.acap_lt
  have hnc_2048 : ks.nc.toNat < 2048 := hnc_lt
  have hnc1 : (ks.nc + 1#32).toNat = ks.nc.toNat + 1 := by bv_omega
  have hal1 : (ks.alen + sz).toNat = ks.alen.toNat + sz.toNat := by bv_omega
  have hsh_ar : ({ ks with arena := ar } : K512State).ShapesOk acap :=
    { hinv.shapes with arena_len := har_len }
  have hshM : stM.ShapesOk acap :=
    (((hsh_ar.putHdr .alen _).putArr .clOff _ _).putArr .clSz _ _).putHdr .nc _
  have hsh' := k5WatchStep_preserves_shapes hshM ks.nc (xs[0]'(by omega)) (xs[1]'(by omega))
  have hcl_old : ∀ c < ks.nc.toNat,
      k5ClauseOff stM c = k5ClauseOff ks c ∧ k5ClauseSize stM c = k5ClauseSize ks c ∧
      k5ClauseLits stM c = k5ClauseLits ks c := fun c hc => by
    have hoff : k5ClauseOff stM c = k5ClauseOff ks c := by
      unfold k5ClauseOff; dsimp only [stM]; k5_field; rw [List.getElem?_set_ne (by omega)]
    have hszc : k5ClauseSize stM c = k5ClauseSize ks c := by
      unfold k5ClauseSize; dsimp only [stM]; k5_field; rw [List.getElem?_set_ne (by omega)]
    have hwf := hinv.clauses.cl_wf c hc
    have hlits : k5ClauseLits stM c = k5ClauseLits ks c := by
      unfold k5ClauseLits; rw [hoff, hszc]
      have har_eq : stM.arena = ar := by dsimp only [stM]; k5_field
      rw [har_eq]; congr 1
      apply List.ext_getElem
      · simp [List.length_take, List.length_drop, har_len, hinv.shapes.arena_len]
      · intro k hk1 hk2
        have hk_sz : k < k5ClauseSize ks c := by simp [List.length_take] at hk1; omega
        have hal_le := hinv.clauses.alen_le
        have har0 := hinv.shapes.arena_len
        have hbd_al : k5ClauseOff ks c + k5ClauseSize ks c ≤ ks.alen.toNat := hwf.2.1
        simp only [List.getElem_take, List.getElem_drop]
        have hg := har_old (k5ClauseOff ks c + k) (by omega)
        rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at hg
        exact Option.some.inj hg
    exact ⟨hoff, hszc, hlits⟩
  have hnew_off : k5ClauseOff stM ks.nc.toNat = ks.alen.toNat := by
    unfold k5ClauseOff; dsimp only [stM]; k5_field
    rw [List.getElem?_set_self (by rw [hinv.shapes.clOff_len]; exact hnc_2048), Option.getD_some]
  have hnew_sz : k5ClauseSize stM ks.nc.toNat = sz.toNat := by
    unfold k5ClauseSize; dsimp only [stM]; k5_field
    rw [List.getElem?_set_self (by rw [hinv.shapes.clSz_len]; exact hnc_2048), Option.getD_some]
  have hnew_lits : k5ClauseLits stM ks.nc.toNat = (xs.take sz.toNat).map BitVec.toNat := by
    unfold k5ClauseLits; rw [hnew_off, hnew_sz]
    have har_eq : stM.arena = ar := by dsimp only [stM]; k5_field
    rw [har_eq]; congr 1
    apply List.ext_getElem
    · simp [List.length_take, List.length_drop, har_len]; omega
    · intro k hk1 _
      have hk_sz : k < sz.toNat := by simp [List.length_take] at hk1; omega
      simp only [List.getElem_take, List.getElem_drop]
      have hg := har_new k hk_sz
      rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at hg
      exact Option.some.inj hg
  have hks'_ar : ks'.arena = ar := by dsimp only [ks', k5WatchStep, k5WatchStep0, stM]; k5_field
  have hks'_co : ks'.clOff = stM.clOff := rfl
  have hks'_cs : ks'.clSz = stM.clSz := rfl
  have hks'_nc : ks'.nc = ks.nc + 1#32 := by
    dsimp only [ks', k5WatchStep, k5WatchStep0, stM]; k5_field
  have hks'_nv : ks'.nv = ks.nv := by dsimp only [ks', k5WatchStep, k5WatchStep0, stM]; k5_field
  have hks'_al : ks'.alen = ks.alen + sz := by
    dsimp only [ks', k5WatchStep, k5WatchStep0, stM]; k5_field
  have hcl' : K512ClausesOk acap P ks' := by
    refine ⟨hinv.clauses.acap_ge, hinv.clauses.acap_lt,
      by dsimp only [ks', k5WatchStep, k5WatchStep0, stM]; k5_field; exact hinv.clauses.acap_eq,
      by rw [hks'_nv]; exact hinv.clauses.nv_le, by rw [hks'_nc, hnc1]; unfold k5MaxCl at *; omega,
      by rw [hks'_al, hal1]; exact hfit,
      by dsimp only [ks', k5WatchStep, k5WatchStep0, stM]; k5_field; exact hinv.clauses.nassump_le,
      by dsimp only [ks', k5WatchStep, k5WatchStep0, stM]; k5_field; exact hinv.clauses.nkl_le,
      by dsimp only [ks', k5WatchStep, k5WatchStep0, stM]; k5_field; exact hinv.clauses.nana_le,
      ?_, ?_,
      by dsimp only [ks', k5WatchStep, k5WatchStep0, stM]; k5_field; exact hinv.clauses.incons_ok,
      by dsimp only [ks', k5WatchStep, k5WatchStep0, stM]; k5_field; exact hinv.clauses.assump_ok,
      by dsimp only [ks', k5WatchStep, k5WatchStep0, stM]; k5_field; exact hinv.clauses.flags_clean⟩
    · intro cid hc; rw [hks'_nc, hnc1] at hc
      have heq_cl : k5ClauseOff ks' cid = k5ClauseOff stM cid ∧
          k5ClauseSize ks' cid = k5ClauseSize stM cid ∧
            k5ClauseLits ks' cid = k5ClauseLits stM cid :=
        ⟨rfl, rfl, rfl⟩
      rw [heq_cl.1, heq_cl.2.1, heq_cl.2.2, hks'_al, hal1, hks'_nv]
      by_cases hcid : cid = ks.nc.toNat
      · subst hcid; rw [hnew_off, hnew_sz, hnew_lits]
        refine ⟨hsz2, Nat.le_refl _, fun l hl => ?_, hent⟩
        rw [List.mem_map] at hl; obtain ⟨b, hb, rfl⟩ := hl
        obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hb
        have hj_sz : j < sz.toNat := by simp [List.length_take] at hj; omega
        simp only [List.getElem_take]
        have hxj := hxlits j hj_sz
        rwa [List.getElem?_eq_getElem (by omega : j < xs.length), Option.getD_some] at hxj
      · have hlt : cid < ks.nc.toNat := by omega
        obtain ⟨ho, hs, hl⟩ := hcl_old cid hlt
        rw [ho, hs, hl]; have hw := hinv.clauses.cl_wf cid hlt
        exact ⟨hw.1, by omega, hw.2.2.1, hw.2.2.2⟩
    · intro c1 c2 h12 h2; rw [hks'_nc, hnc1] at h2
      change k5ClauseOff stM c1 + k5ClauseSize stM c1 ≤ k5ClauseOff stM c2
      have ho1 := hcl_old c1 (by omega)
      rw [ho1.1, ho1.2.1]
      by_cases h2e : c2 = ks.nc.toNat
      · subst h2e; rw [hnew_off]; exact (hinv.clauses.cl_wf c1 (by omega)).2.1
      · have ho2 := hcl_old c2 (by omega); rw [ho2.1]
        exact hinv.clauses.cl_mono c1 c2 h12 (by omega)
  have hwM : K512WatchesOk stM := by
    obtain ⟨chains, hlen, hnd, hwc, hbnd⟩ := hinv.watches
    refine ⟨chains, by dsimp only [stM]; k5_field; exact hlen, hnd,
      by dsimp only [stM]; k5_field; exact hwc, fun l hl w hw => ?_⟩
    have hl' : l < 2 * ks.nv.toNat := by revert hl; dsimp only [stM]; k5_field; exact id
    obtain ⟨hw1, hw2, hw3, hw4⟩ := hbnd l hl' w hw
    have ho := hcl_old (w / 2) (by omega)
    have har_get : stM.arena[k5ClauseOff ks (w / 2) + w % 2]? =
        ks.arena[k5ClauseOff ks (w / 2) + w % 2]? := by
      have har_eq : stM.arena = ar := by dsimp only [stM]; k5_field
      rw [har_eq]; have hwf := hinv.clauses.cl_wf (w / 2) (by omega)
      exact har_old _ (by omega)
    refine ⟨by dsimp only [stM]; k5_field; rw [hnc1]; omega,
      by rw [ho.2.1]; exact hw2, by rw [ho.1, har_get]; exact hw3,
      by dsimp only [stM]; k5_field; exact hw4⟩
  have hl0_lt : (xs[0]'(by omega)).toNat < 2 * stM.nv.toNat := by
    have h0 := hxlits 0 (by omega); rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at h0
    dsimp only [stM]; k5_field; exact h0
  have hl1_lt : (xs[1]'(by omega)).toNat < 2 * stM.nv.toNat := by
    have h1 := hxlits 1 (by omega); rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at h1
    dsimp only [stM]; k5_field; exact h1
  have hw' : K512WatchesOk ks' :=
    k5WatchStep_preserves_watches hshM hwM
      (by dsimp only [stM]; k5_field; rw [hnc1]; omega)
      (by dsimp only [stM]; k5_field; rw [hnc1]; unfold k5MaxCl at *; omega)
      (by dsimp only [stM]; k5_field; exact hinv.clauses.nv_le)
      hl0_lt hl1_lt (by rw [hnew_sz]; exact hsz2)
      (by rw [hnew_off]; have har_eq : stM.arena = ar := by dsimp only [stM]; k5_field
          have h0 := har_new 0 (by omega); rw [Nat.add_zero] at h0
          rw [har_eq, h0, List.getElem?_eq_getElem (by omega), Option.getD_some])
      (by rw [hnew_off]; have har_eq : stM.arena = ar := by dsimp only [stM]; k5_field
          rw [har_eq, har_new 1 (by omega), List.getElem?_eq_getElem (by omega), Option.getD_some])
      (fun chains hclen _ hwc => by
        obtain ⟨ch0, h0len, _, h0wc, h0bnd⟩ := hinv.watches
        have hwn_eq : stM.wnext = ks.wnext := by dsimp only [stM]; k5_field
        have hwh_eq : stM.whead = ks.whead := by dsimp only [stM]; k5_field
        have hnv_eq : stM.nv = ks.nv := by dsimp only [stM]; k5_field
        have hcheq : chains = ch0 := by
          apply List.ext_getElem (by rw [hclen, hnv_eq, h0len])
          intro x hx1 hx2
          have hx_nv : x < 2 * ks.nv.toNat := by omega
          have hc1 := hwc x (by rw [hnv_eq]; exact hx_nv)
          have hc2 := h0wc x hx_nv
          rw [hwn_eq, hwh_eq, List.getElem?_eq_getElem hx1, Option.getD_some] at hc1
          rw [List.getElem?_eq_getElem hx2, Option.getD_some] at hc2
          exact hc1.unique (by rw [hinv.shapes.wnext_len]; decide) hc2
        rw [hcheq]; constructor <;> intro hm <;>
          (obtain ⟨ch, hch_m, hw_m⟩ := List.mem_flatten.mp hm
           obtain ⟨x, hx, rfl⟩ := List.getElem_of_mem hch_m
           have hb := h0bnd x (by omega) _ (by simpa [List.getElem?_eq_getElem hx] using hw_m)
           omega))
  have hba' : K512BaseAssignOk P ks' := by
    have h1 : ks'.trl_end = ks.trl_end := by
      dsimp only [ks', k5WatchStep, k5WatchStep0, stM]; k5_field
    have h2 : ks'.prop = ks.prop := by dsimp only [ks', k5WatchStep, k5WatchStep0, stM]; k5_field
    have h3 : ks'.unass = ks.unass := by dsimp only [ks', k5WatchStep, k5WatchStep0, stM]; k5_field
    have h4 : ks'.vals = ks.vals := by dsimp only [ks', k5WatchStep, k5WatchStep0, stM]; k5_field
    have h5 : ks'.trl = ks.trl := by dsimp only [ks', k5WatchStep, k5WatchStep0, stM]; k5_field
    have h6 : ks'.lvl = ks.lvl := by dsimp only [ks', k5WatchStep, k5WatchStep0, stM]; k5_field
    have h7 : ks'.lvlArr = ks.lvlArr := by
      dsimp only [ks', k5WatchStep, k5WatchStep0, stM]; k5_field
    have h8 : ks'.rsn = ks.rsn := by dsimp only [ks', k5WatchStep, k5WatchStep0, stM]; k5_field
    exact ⟨by rw [h1, hks'_nv]; exact hinv.assign.trl_end_le,
      by rw [h2, h1]; exact hinv.assign.prop_le,
      by rw [h3, h1, hks'_nv]; exact hinv.assign.unass_eq,
      by rw [hks'_nv, h4]; exact hinv.assign.vals_dom,
      by rw [hks'_nv, h4]; exact hinv.assign.vals_neg_iff,
      by rw [hks'_nv, h4, h1, h5]; exact hinv.assign.vals_nz_iff_trl,
      by unfold k5TrailLits; rw [h1, h5]; exact hinv.assign.trl_nodup,
      by unfold k5TrailLits; rw [hks'_nv, h1, h5]; exact hinv.assign.trl_lt,
      by rw [hks'_nv, h7, h6]; exact hinv.assign.trl_lvl_le,
      by rw [hks'_nv, h4, h7, h8]; exact hinv.assign.unass_lvl_zero,
      by rw [h1, h7, h5]; exact hinv.assign.trl_lvl_mono,
      by rw [h1, h7, h5, h8]; exact hinv.assign.dec_earliest,
      by rw [h1, h5, h7, h4]; exact hinv.assign.lvl0_ok⟩
  have hre' : K512ReasonOk ks' := fun i hi => by
    have h1 : ks'.trl_end = ks.trl_end := by
      dsimp only [ks', k5WatchStep, k5WatchStep0, stM]; k5_field
    have h5 : ks'.trl = ks.trl := by dsimp only [ks', k5WatchStep, k5WatchStep0, stM]; k5_field
    have h8 : ks'.rsn = ks.rsn := by dsimp only [ks', k5WatchStep, k5WatchStep0, stM]; k5_field
    rw [h1] at hi
    change let l := (ks'.trl[i]?.getD 0#32).toNat; let r := ks'.rsn[l / 2]?.getD 0#32; _
    rw [h5, h8, hks'_nc]
    rcases hinv.reasons i hi with hnone | ⟨hr_lt, hmem, hoth⟩
    · exact Or.inl hnone
    · right; have ho := hcl_old _ hr_lt
      have hl_eq : k5ClauseLits ks' (ks.rsn[(ks.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat =
          k5ClauseLits ks (ks.rsn[(ks.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat := ho.2.2
      rw [hnc1, hl_eq]; exact ⟨by omega, hmem, hoth⟩
  have hsync' : K512TrailSynced ks' := by
    have h1 : ks'.trl_end = ks.trl_end := by
      dsimp only [ks', k5WatchStep, k5WatchStep0, stM]; k5_field
    have h4 : ks'.vals = ks.vals := by dsimp only [ks', k5WatchStep, k5WatchStep0, stM]; k5_field
    have h5 : ks'.trl = ks.trl := by dsimp only [ks', k5WatchStep, k5WatchStep0, stM]; k5_field
    intro i hi; rw [h1] at hi; unfold K512TrailSynced at hsync
    change ks'.vals[(ks'.trl[i]?.getD 0#32).toNat]? = some 1#32 ∧
      ks'.vals[(ks'.trl[i]?.getD 0#32).toNat ^^^ 1]? = some 2#32
    rw [h4, h5]; exact hsync i hi
  have hlb' : ∀ M, (∀ j < sz.toNat, (xs[j]?.getD 0#32).toNat < 2 * M) →
      K512LitsBounded M ks → K512LitsBounded M ks' := fun M hxsM hM => by
    constructor
    · intro cid hcid l hl
      rw [hks'_nc, hnc1] at hcid
      have heq_cl : k5ClauseLits ks' cid = k5ClauseLits stM cid := rfl
      rw [heq_cl] at hl
      by_cases hc : cid = ks.nc.toNat
      · subst hc; rw [hnew_lits] at hl
        rw [List.mem_map] at hl; obtain ⟨b, hb, rfl⟩ := hl
        obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hb
        have hj_sz : j < sz.toNat := by simp [List.length_take] at hj; omega
        simp only [List.getElem_take]
        have hx := hxsM j hj_sz
        rwa [List.getElem?_eq_getElem (by omega : j < xs.length), Option.getD_some] at hx
      · rw [(hcl_old cid (by omega)).2.2] at hl; exact hM.1 cid (by omega) l hl
    · intro w hw; rw [hks'_nc, hnc1] at hw
      have hw0 := k5_bv32_cid_w0 hnc_lt (Nat.le_refl _)
      have hw1 := k5_bv32_cid_w1 hnc_lt (Nat.le_refl _)
      have hw0_4096 : (ks.nc <<< (1 : Nat)).toNat < 4096 := by
        have := hw0.2; unfold k5MaxCl at this; omega
      have hw1_4096 : ((ks.nc <<< (1 : Nat)) ||| 1#32).toNat < 4096 := by
        have := hw1.2; unfold k5MaxCl at this; omega
      have hwb_eq : ks'.wblit =
          (ks.wblit.set (2 * ks.nc.toNat) (xs[1]'(by omega))).set
            (2 * ks.nc.toNat + 1) (xs[0]'(by omega)) := by
        dsimp only [ks', k5WatchStep, k5WatchStep0, stM]
        rw [hw0.1, hw1.1]; k5_field
      rw [hwb_eq]
      by_cases h1 : w = 2 * ks.nc.toNat + 1
      · subst h1
        rw [List.getElem?_set_self (by simp [hinv.shapes.wblit_len]; omega), Option.getD_some]
        have hx := hxsM 0 (by omega)
        rwa [List.getElem?_eq_getElem (by omega : 0 < xs.length), Option.getD_some] at hx
      · rw [List.getElem?_set_ne (Ne.symm h1)]
        by_cases h0 : w = 2 * ks.nc.toNat
        · subst h0
          rw [List.getElem?_set_self (by rw [hinv.shapes.wblit_len]; omega), Option.getD_some]
          have hx := hxsM 1 (by omega)
          rwa [List.getElem?_eq_getElem (by omega : 1 < xs.length), Option.getD_some] at hx
        · rw [List.getElem?_set_ne (Ne.symm h0)]; exact hM.2 w (by omega)
  exact ⟨⟨hsh', hcl', hw', hba', hre'⟩, hsync',
    by dsimp only [ks', k5WatchStep, k5WatchStep0, stM]; k5_field, hks'_nv,
    by dsimp only [ks', k5WatchStep, k5WatchStep0, stM]; k5_field,
    by dsimp only [ks', k5WatchStep, k5WatchStep0, stM]; k5_field,
    by dsimp only [ks', k5WatchStep, k5WatchStep0, stM]; k5_field,
    by dsimp only [ks', k5WatchStep, k5WatchStep0, stM]; k5_field,
    by dsimp only [ks', k5WatchStep, k5WatchStep0, stM]; k5_field, hlb'⟩

/-! ## 4. Parametric `(Γ : Env)` `Func.wp` Proofs (`7/24`) -/

/-- `1/24`: Parametric `Func.wp` proof for `full_k512_watch`. -/
theorem full_k512_watch_wp (Γ : Env) :
    ∀ args m Q X, k5WatchSpec args m Q X → Func.wp Γ full_k512_watch_body args m Q X := by
  rintro ⟨kPtr, cid, l0, l1, ⟨⟩⟩ m Q X ⟨acap, ks, R, hsh, hcap, hnv, hcid, hl0, hl1, hm, hQ⟩
  have h0 := k5_bv32_cid_w0 hcid (Nat.le_refl _)
  have h1 := k5_bv32_cid_w1 hcid (Nat.le_refl _)
  have hw0_len : (cid <<< (1 : Nat)).toNat < 4096 := by have := h0.2; unfold k5MaxCl at this; omega
  have hw1_len : ((cid <<< (1 : Nat)) ||| 1#32).toNat < 4096 := by
    have := h1.2; unfold k5MaxCl at this; omega
  have hl0_len : l0.toNat < 1024 := by unfold k5MaxV at hnv; omega
  have hl1_len : l1.toNat < 1024 := by unfold k5MaxV at hnv; omega
  have hmA := k5Mem_to_amem hsh hm; clear hm
  c0_hsteps!
  obtain ⟨_, hm'⟩ := k5MemA_to_mem hm
  refine hQ _ (Eq.mp (congrArg (fun x => (K512Mem kPtr x ⋆ R) _) ?_) hm')
  dsimp only [k5WatchStep, k5WatchStep0]; k5_ext

/-- `2/24`: Parametric `Func.wp` proof for `full_k512_assign`. -/
theorem full_k512_assign_wp (Γ : Env) :
    ∀ args m Q X, k5AssignSpec args m Q X → Func.wp Γ full_k512_assign_body args m Q X := by
  rintro ⟨kPtr, lit, rsn, ⟨⟩⟩ m Q X ⟨acap, ks, R, hsh, hcap, hnv, hlit, hte, hm, hQ⟩
  obtain ⟨hv_eq, hv_lt⟩ := k5_bv32_div2_lt hlit
  obtain ⟨hn_eq, hn_lt⟩ := k5_bv32_xor1_lt hlit
  have hl_1024 : lit.toNat < 1024 := by unfold k5MaxV at hnv; omega
  have hnl_1024 : (lit ^^^ 1#32).toNat < 1024 := by unfold k5MaxV at hnv; omega
  have hv_512 : (lit >>> (1 : Nat)).toNat < 512 := by unfold k5MaxV at hnv; omega
  have hte_512 : ks.trl_end.toNat < 512 := by unfold k5MaxV at hnv; omega
  have hmA := k5Mem_to_amem hsh hm; clear hm
  c0_hsteps_nogrp
  let ksPre := ((((((ks.putArr .vals lit.toNat 1#32).putArr .vals (lit ^^^ 1#32).toNat 2#32).putArr
    .lvlArr (lit >>> (1 : Nat)).toNat ks.lvl).putArr .rsn (lit >>> (1 : Nat)).toNat rsn).putArr
    .trl ks.trl_end.toNat lit).putHdr .trl_end (ks.trl_end + 1#32))
  let ksU := if (0 : BitVec 32).ult ks.unass then ksPre.putHdr .unass (ks.unass - 1#32) else ksPre
  have hult_iff : (0 : BitVec 32).ult ks.unass = true ↔ 0 < ks.unass.toNat := decide_eq_true_iff
  refine wp_join0 (fun m' => (K512MemA kPtr acap ksU ⋆ R) m') ?_ ?_
  · intro J m' hm'
    c0_hsteps!
    · obtain ⟨_, hm''⟩ := k5MemA_to_mem hm
      refine hQ _ (Eq.mp (congrArg (fun x => (K512Mem kPtr x ⋆ R) _) ?_) hm'')
      have hcond : (lit &&& 1#32) ≠ 0#32 := by simpa [k5_bv32_one] using ‹_›
      by_cases hu : (0 : BitVec 32).ult ks.unass = true
      · have hu_nat := hult_iff.mp hu
        dsimp only [ksU, ksPre, k5AssignStep]
        simp only [hu, ite_true, hu_nat, hcond, ne_eq, not_false_eq_true]
        k5_ext <;> simp [hv_eq]
      · have hu_nat : ¬ 0 < ks.unass.toNat := fun hp => hu (hult_iff.mpr hp)
        dsimp only [ksU, ksPre, k5AssignStep]
        simp only [hu, ite_false, hu_nat, hcond, ne_eq, not_false_eq_true, ite_true]
        k5_ext <;> simp [hv_eq]
    · obtain ⟨_, hm''⟩ := k5MemA_to_mem hm
      refine hQ _ (Eq.mp (congrArg (fun x => (K512Mem kPtr x ⋆ R) _) ?_) hm'')
      have hcond : (lit &&& 1#32) = 0#32 := by simpa [k5_bv32_one] using ‹_›
      by_cases hu : (0 : BitVec 32).ult ks.unass = true
      · have hu_nat := hult_iff.mp hu
        dsimp only [ksU, ksPre, k5AssignStep]
        simp only [hu, ite_true, hu_nat, hcond, ne_eq, not_true_eq_false, ite_false]
        k5_ext <;> simp [hv_eq]
      · have hu_nat : ¬ 0 < ks.unass.toNat := fun hp => hu (hult_iff.mpr hp)
        dsimp only [ksU, ksPre, k5AssignStep]
        simp only [hu, ite_false, hu_nat, hcond, ne_eq, not_true_eq_false]
        k5_ext <;> simp [hv_eq]
  · intro J hJ
    c0_hsteps!
    · have hu : (0 : BitVec 32).ult ks.unass = true := by
        apply hult_iff.mpr; revert hc; k5_field; intro hc; bv_omega
      refine hJ _ (Eq.mp (congrArg (fun x => (K512MemA kPtr acap x ⋆ R) _) ?_) hm)
      dsimp only [ksU, ksPre]; simp only [hu, ite_true]
      k5_ext <;> (first | rfl | (simp only [hv_eq, k5_bv32_one]; rfl))
    · have hu : (0 : BitVec 32).ult ks.unass = false :=
        Bool.eq_false_iff.mpr fun h => by
          have := hult_iff.mp h; revert hc; k5_field; intro hc; bv_omega
      refine hJ _ (Eq.mp (congrArg (fun x => (K512MemA kPtr acap x ⋆ R) _) ?_) hm)
      dsimp only [ksU, ksPre]; simp only [hu, Bool.false_eq_true, ite_false]
      k5_ext <;> (first | rfl | (simp only [hv_eq, k5_bv32_one]; rfl))

private def K5MtfSt (acap : Nat) (ks ks' : K512State) : Prop :=
  ks'.ShapesOk acap ∧ ∃ qf ql qs qst qp qn qsa,
    ks' = { ks with qfirst := qf, qlast := ql, qsearch := qs, qstamp := qst,
                    qprev := qp, qnext := qn, qstampArr := qsa }

private theorem K5MtfSt.base {acap : Nat} {ks : K512State} (hsh : ks.ShapesOk acap) :
    K5MtfSt acap ks ks :=
  ⟨hsh, ks.qfirst, ks.qlast, ks.qsearch, ks.qstamp, ks.qprev, ks.qnext, ks.qstampArr,
    by cases ks; rfl⟩
private theorem K5MtfSt.nv_eq {acap : Nat} {ks ks' : K512State} (r : K5MtfSt acap ks ks') :
    ks'.nv = ks.nv := by rcases r.2 with ⟨_, _, _, _, _, _, _, rfl⟩; rfl
private theorem K5MtfSt.putQf {acap : Nat} {ks ks' : K512State} (r : K5MtfSt acap ks ks')
    (v : BitVec 32) : K5MtfSt acap ks (ks'.putHdr .qfirst v) := by
  rcases r with ⟨hsh, qf, ql, qs, qst, qp, qn, qsa, rfl⟩
  exact ⟨hsh.putHdr .qfirst v, v, ql, qs, qst, qp, qn, qsa, rfl⟩
private theorem K5MtfSt.putQl {acap : Nat} {ks ks' : K512State} (r : K5MtfSt acap ks ks')
    (v : BitVec 32) : K5MtfSt acap ks (ks'.putHdr .qlast v) := by
  rcases r with ⟨hsh, qf, ql, qs, qst, qp, qn, qsa, rfl⟩
  exact ⟨hsh.putHdr .qlast v, qf, v, qs, qst, qp, qn, qsa, rfl⟩
private theorem K5MtfSt.putQs {acap : Nat} {ks ks' : K512State} (r : K5MtfSt acap ks ks')
    (v : BitVec 32) : K5MtfSt acap ks (ks'.putHdr .qsearch v) := by
  rcases r with ⟨hsh, qf, ql, qs, qst, qp, qn, qsa, rfl⟩
  exact ⟨hsh.putHdr .qsearch v, qf, ql, v, qst, qp, qn, qsa, rfl⟩
private theorem K5MtfSt.putQst {acap : Nat} {ks ks' : K512State} (r : K5MtfSt acap ks ks')
    (v : BitVec 32) : K5MtfSt acap ks (ks'.putHdr .qstamp v) := by
  rcases r with ⟨hsh, qf, ql, qs, qst, qp, qn, qsa, rfl⟩
  exact ⟨hsh.putHdr .qstamp v, qf, ql, qs, v, qp, qn, qsa, rfl⟩
private theorem K5MtfSt.putQp {acap : Nat} {ks ks' : K512State} (r : K5MtfSt acap ks ks')
    (i : Nat) (v : BitVec 32) : K5MtfSt acap ks (ks'.putArr .qprev i v) := by
  rcases r with ⟨hsh, qf, ql, qs, qst, qp, qn, qsa, rfl⟩
  exact ⟨hsh.putArr .qprev i v, qf, ql, qs, qst, qp.set i v, qn, qsa, rfl⟩
private theorem K5MtfSt.putQn {acap : Nat} {ks ks' : K512State} (r : K5MtfSt acap ks ks')
    (i : Nat) (v : BitVec 32) : K5MtfSt acap ks (ks'.putArr .qnext i v) := by
  rcases r with ⟨hsh, qf, ql, qs, qst, qp, qn, qsa, rfl⟩
  exact ⟨hsh.putArr .qnext i v, qf, ql, qs, qst, qp, qn.set i v, qsa, rfl⟩
private theorem K5MtfSt.putQsa {acap : Nat} {ks ks' : K512State} (r : K5MtfSt acap ks ks')
    (i : Nat) (v : BitVec 32) : K5MtfSt acap ks (ks'.putArr .qstampArr i v) := by
  rcases r with ⟨hsh, qf, ql, qs, qst, qp, qn, qsa, rfl⟩
  exact ⟨hsh.putArr .qstampArr i v, qf, ql, qs, qst, qp, qn, qsa.set i v, rfl⟩
private theorem K5MtfSt.finishA {acap : Nat} {ks ks' : K512State} {kPtr : BitVec 64}
    {R : Mem 64 → Prop} {m' : Mem 64} {Q : Post []}
    (hQ : ∀ qf' ql' qs' qst' qp' qn' qsa' m',
      let ks' : K512State := { ks with qfirst := qf', qlast := ql', qsearch := qs', qstamp := qst',
                                       qprev := qp', qnext := qn', qstampArr := qsa' }
      ks'.ShapesOk acap → (K512Mem kPtr ks' ⋆ R) m' → Q () m')
    (r : K5MtfSt acap ks ks') (hm' : (K512MemA kPtr acap ks' ⋆ R) m') : Q () m' := by
  obtain ⟨hsh, hm''⟩ := k5MemA_to_mem hm'
  rcases r with ⟨_, qf, ql, qs, qst, qp, qn, qsa, rfl⟩
  exact hQ qf ql qs qst qp qn qsa m' hsh hm''

/-- `3/24`: Parametric `Func.wp` proof for `full_k512_mtf`. -/
theorem full_k512_mtf_wp (Γ : Env) :
    ∀ args m Q X, k5MtfSpec args m Q X → Func.wp Γ full_k512_mtf_body args m Q X := by
  rintro ⟨kPtr, v, ⟨⟩⟩ m Q X ⟨acap, ks, R, hsh, hcap, hnv, hm, hQ⟩
  have hmA := k5Mem_to_amem hsh hm; clear hm
  c0_hsteps_nogrp
  · exact hQ _ _ _ _ _ _ _ m hsh (k5MemA_to_mem hmA).2
  · exact hQ _ _ _ _ _ _ _ m hsh (k5MemA_to_mem hmA).2
  · have hv_lt : v.toNat < ks.nv.toNat := by bv_omega
    have hv_512 : v.toNat < 512 := by unfold k5MaxV at hnv; omega
    have hv2_1024 : (v <<< (1 : Nat)).toNat < 1024 := by
      have := k5_shl1_toNat v; unfold k5MaxV at hnv; omega
    c0_hsteps_nogrp
    let pv := ks.qprev[v.toNat]?.getD 0#32
    let nxt := ks.qnext[v.toNat]?.getD 0#32
    refine wp_join_state0 (α := K512State)
      (fun st m' => K5MtfSt acap ks st ∧ (K512MemA kPtr acap st ⋆ R) m') ?_ ?_
    · intro J1 ks1 m1 ⟨hr1, hm1⟩
      have hnv1 := hr1.nv_eq
      c0_hsteps_nogrp
      refine wp_join_state0 (α := K512State)
        (fun st m' => K5MtfSt acap ks st ∧ (K512MemA kPtr acap st ⋆ R) m') ?_ ?_
      · intro J2 ks2 m2 ⟨hr2, hm2⟩
        have hnv2 := hr2.nv_eq
        c0_hsteps_nogrp
        refine wp_join_state0 (α := K512State)
          (fun st m' => K5MtfSt acap ks st ∧ (K512MemA kPtr acap st ⋆ R) m') ?_ ?_
        · intro J3 ks3 m3 ⟨hr3, hm3⟩
          have hnv3 := hr3.nv_eq
          c0_hsteps_nogrp
          let ol := ks3.qlast
          refine wp_join_state0 (α := K512State)
            (fun st m' => K5MtfSt acap ks st ∧ (K512MemA kPtr acap st ⋆ R) m') ?_ ?_
          · intro J4 ks4 m4 ⟨hr4, hm4⟩
            c0_hsteps_nogrp
            refine wp_join_state0 (α := K512State)
              (fun st m' => K5MtfSt acap ks st ∧ (K512MemA kPtr acap st ⋆ R) m') ?_ ?_
            · intro J5 ks5 m5 ⟨hr5, hm5⟩
              c0_hsteps!
              · exact (hr5.putQs v).finishA hQ hm
              · exact hr5.finishA hQ hm5
            · intro J5 hJ5
              c0_hsteps!
              · exact hJ5 _ _ ⟨(hr4.putQst _).putQsa _ _, hm⟩
              · exact hJ5 _ _ ⟨hr4, hm4⟩
          · intro J4 hJ4
            c0_hsteps_nogrp
            · c0_hsteps!
              exact hJ4 _ _ ⟨(((hr3.putQp v.toNat ol).putQn v.toNat 0xFFFFFFFF#32).putQl v).putQf
                v, hm⟩
            · have hol_512 : ol.toNat < 512 := by
                have : ol.toNat < ks.nv.toNat := by dsimp only [ol]; rw [← hnv3]; bv_omega
                unfold k5MaxV at hnv; omega
              c0_hsteps!
              exact hJ4 _ _ ⟨(((hr3.putQp v.toNat ol).putQn v.toNat 0xFFFFFFFF#32).putQl v).putQn
                ol.toNat v, hm⟩
        · intro J3 hJ3
          c0_hsteps_nogrp
          · c0_hsteps!; exact hJ3 _ _ ⟨hr2.putQl pv, hm⟩
          · have hn_512 : nxt.toNat < 512 := by
              have : nxt.toNat < ks.nv.toNat := by dsimp only [nxt]; rw [← hnv2]; bv_omega
              unfold k5MaxV at hnv; omega
            c0_hsteps!
            exact hJ3 _ _ ⟨hr2.putQp nxt.toNat pv, hm⟩
      · intro J2 hJ2
        c0_hsteps_nogrp
        · c0_hsteps!; exact hJ2 _ _ ⟨hr1.putQf nxt, hm⟩
        · have hp_512 : pv.toNat < 512 := by
            have : pv.toNat < ks.nv.toNat := by dsimp only [pv]; rw [← hnv1]; bv_omega
            unfold k5MaxV at hnv; omega
          c0_hsteps!
          exact hJ2 _ _ ⟨hr1.putQn pv.toNat nxt, hm⟩
    · intro J1 hJ1
      c0_hsteps!
      · exact hJ1 _ _ ⟨(K5MtfSt.base hsh).putQs pv, hm⟩
      · exact hJ1 _ _ ⟨(K5MtfSt.base hsh).putQs nxt, hm⟩
      · exact hJ1 _ _ ⟨K5MtfSt.base hsh, hmA⟩
      · exact hJ1 _ _ ⟨K5MtfSt.base hsh, hmA⟩
      · exact hJ1 _ _ ⟨K5MtfSt.base hsh, hmA⟩

/-- `4/24`: Parametric `Func.wp` proof for `full_k512_backtrack`. -/
theorem full_k512_backtrack_wp (Γ : Env) :
    ∀ args m Q X, k5BacktrackSpec args m Q X → Func.wp Γ full_k512_backtrack_body args m Q X := by
  rintro ⟨kPtr, target_lvl, ⟨⟩⟩ m Q X ⟨acap, P, ks, R, hinv, hsync_below, hm, hQ⟩
  have hnv := hinv.clauses.nv_le; have hsh := hinv.shapes
  have hmA := k5Mem_to_amem hsh hm; clear hm
  c0_hsteps_nogrp
  refine wp_join_state1 (fun st : BitVec 32 => st)
    (fun _ m' => (K512MemA kPtr acap ks ⋆ R) m') ?_ ?_
  · intro J0 best_st m0 hm0
    refine wp_while_break_state (β := BitVec 32 × BitVec 32 × K512State)
      (fun bst => (bst.1, bst.2.1, ()))
      (fun bst m' => K5BtLoopInv acap ks target_lvl bst.1 bst.2.2 ∧
        (bst.1 = 0#32 ∨ ∃ i < bst.1.toNat, i = bst.1.toNat - 1 ∧
          (bst.2.2.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ target_lvl.toNat) ∧
        (K512MemA kPtr acap bst.2.2 ⋆ R) m')
      (α := BitVec 32 × BitVec 32 × K512State)
      (fun st => (st.1, st.2.1, ())) (fun st => st.1.toNat)
      (fun st m' => K5BtLoopInv acap ks target_lvl st.1 st.2.2 ∧ (K512MemA kPtr acap st.2.2 ⋆ R) m')
      ?_ ?_ ?_
    · rintro B ⟨te, _best_st, st⟩ m' ⟨hbt, hexit, hm'⟩
      dsimp only at hbt hexit hm'
      c0_hsteps_nogrp
      let stProp := if te.toNat < st.prop.toNat then (st.putHdr .trl_end te).putHdr .prop te
        else st.putHdr .trl_end te
      refine wp_join0 (fun m'' => (K512MemA kPtr acap stProp ⋆ R) m'') ?_ ?_
      · intro Jf m'' hm''
        c0_hsteps!
        obtain ⟨_, hmFin⟩ := k5MemA_to_mem hm
        have hfin := k5BtLoopInv_finish hinv hbt hsync_below hexit
        have heq_st : stProp.putHdr .lvl target_lvl =
            ((st.putHdr .trl_end te).putHdr .prop
              (if te.toNat < st.prop.toNat then te else st.prop)).putHdr .lvl target_lvl := by
          dsimp only [stProp]
          by_cases hp : te.toNat < st.prop.toNat <;> simp only [hp, ite_true, ite_false] <;> k5_ext
        rw [heq_st] at hmFin
        rcases hfin with ⟨h1, h2, h3, h4, h5, h6⟩
        have h7 : ∀ i < ks.trl_end.toNat,
            (ks.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ target_lvl.toNat →
            i < (((st.putHdr .trl_end te).putHdr .prop
              (if te.toNat <
                st.prop.toNat then te else st.prop)).putHdr .lvl target_lvl).trl_end.toNat := by
          intro i hi hle
          have hte_eq : (((st.putHdr .trl_end te).putHdr .prop
              (if te.toNat < st.prop.toNat then te else st.prop)).putHdr .lvl target_lvl).trl_end =
                te := by
            k5_field
          rw [hte_eq]
          rcases Nat.lt_or_ge i te.toNat with hlt | hge
          · exact hlt
          · exfalso; have := hbt.popped_gt i hge hi; omega
        exact hQ _ _ h1 h2 h3 h4 h5 h6 h7 hmFin
      · intro Jf hJf
        have hpr_eq : (st.putHdr .trl_end te).prop = st.prop := by k5_field
        c0_hsteps!
        · apply hJf _; have hp : te.toNat < st.prop.toNat := by rw [← hpr_eq]; bv_omega
          simpa [stProp, hp] using hm
        · apply hJf _; have hp : ¬ te.toNat < st.prop.toNat := by rw [← hpr_eq]; bv_omega
          simpa [stProp, hp] using hm
    · rintro B L ⟨te, bst, st⟩ m' hB hL ⟨hbt, hm'⟩
      dsimp only at hbt hm'
      c0_hsplit
      · have hpos : 0 < te.toNat := by bv_omega
        have hte1_lt : te.toNat - 1 < ks.trl_end.toNat := by have := hbt.te_le; omega
        have hte1_512 : te.toNat - 1 < 512 := by
          have := hinv.assign.trl_end_le; have := hbt.te_le; unfold k5MaxV at hnv; omega
        have htrl_len : ks.trl_end.toNat ≤ ks.trl.length := by
          rw [hsh.trl_len]; have := hinv.assign.trl_end_le; unfold k5MaxV at hnv; omega
        let lit := ks.trl[te.toNat - 1]'(by omega)
        have hlit_get : st.trl[te.toNat - 1]?.getD 0#32 = lit := by
          rw [hbt.trl_eq, List.getElem?_eq_getElem (by omega : te.toNat - 1 < ks.trl.length),
            Option.getD_some]
        have hlit_lt : lit.toNat < 2 * ks.nv.toNat := by
          have hm1 := k5_mem_trailLits_of_lt hte1_lt htrl_len
          rw [List.getElem?_eq_getElem (by omega : te.toNat - 1 < ks.trl.length),
            Option.getD_some] at hm1
          exact hinv.assign.trl_lt lit.toNat hm1
        obtain ⟨hv_eq, _⟩ := k5_bv32_div2_lt hlit_lt
        obtain ⟨hn_eq, _⟩ := k5_bv32_xor1_lt hlit_lt
        have hv_st_512 : ((st.trl[te.toNat - 1]?.getD 0#32) >>> (1 : Nat)).toNat < 512 := by
          rw [hlit_get, hv_eq]; unfold k5MaxV at hnv; omega
        have hl_1024 : lit.toNat < 1024 := by unfold k5MaxV at hnv; omega
        have hnl_st_1024 : (st.trl[te.toNat - 1]?.getD 0#32 ^^^ (1 : BitVec 32)).toNat < 1024 := by
          rw [hlit_get, k5_bv32_one, hn_eq]; unfold k5MaxV at hnv; unfold litNeg
          rcases k5_nat_xor1_cases lit.toNat with ⟨_, _⟩ | ⟨_, _⟩ <;> omega
        c0_hsplit
        · refine hB (te, bst, st) m' ⟨hbt, Or.inr ⟨te.toNat - 1, Nat.sub_lt hpos Nat.one_pos, rfl,
          ?_⟩, hm'⟩
          rw [List.getElem?_eq_getElem (by omega : te.toNat - 1 < ks.trl.length), Option.getD_some]
          have hle_raw : (st.lvlArr[(st.trl[te.toNat - 1]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
              target_lvl.toNat := by bv_omega
          rwa [hlit_get] at hle_raw
        · have hstep := k5BtLoopInv_step hinv hbt hpos (by
            have hle_raw :
                ¬ (st.lvlArr[(st.trl[te.toNat - 1]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
                target_lvl.toNat := ‹_›
            rw [← hbt.trl_eq]; omega)
          c0_hsteps!
          · have hs2 := hstep.2 (st.trl[te.toNat - 1]?.getD 0#32 >>> (1 : Nat))
            refine hL (te - 1#32, _, _) _ (by dsimp only; bv_omega) ⟨hs2, ?_⟩
            refine Eq.mp (congrArg (fun x => (K512MemA kPtr acap x ⋆ R) _) ?_) hm
            k5_ext <;> (first | rfl | (simp only [lit, hlit_get, hv_eq, k5_bv32_one]; rfl))
          · refine hL (te - 1#32, bst, _) _ (by dsimp only; bv_omega) ⟨hstep.1, ?_⟩
            refine Eq.mp (congrArg (fun x => (K512MemA kPtr acap x ⋆ R) _) ?_) hm
            k5_ext <;> (first | rfl | (simp only [lit, hlit_get, hv_eq, k5_bv32_one]; rfl))
      · exact hB (te, bst, st) m' ⟨hbt, Or.inl (by bv_omega), hm'⟩
    · intro B L hB hL
      exact wp_jump_state (proj := fun st : BitVec 32 × BitVec 32 × K512State => (st.1, st.2.1, ()))
        (ks.trl_end, best_st, ks) rfl (hL (ks.trl_end, best_st, ks) m0 ⟨k5BtLoopInv_init hinv, hm0⟩)
  · intro J0 hJ0
    c0_hsplit
    · have hqs_512 : ks.qsearch.toNat < 512 := by
        have : ks.qsearch.toNat < ks.nv.toNat := by bv_omega
        unfold k5MaxV at hnv; omega
      c0_hsteps!; exact hJ0 _ m hmA
    · c0_hsteps!; exact hJ0 _ m hmA

private structure K5InitScalar (nv0 ac0 : BitVec 32) (st : K512State) : Prop where
  nv : st.nv = nv0
  nc : st.nc = 0#32
  lvl : st.lvl = 0#32
  prop : st.prop = 0#32
  trl_end : st.trl_end = 0#32
  unass : st.unass = nv0
  incons : st.incons = 0#32
  alen : st.alen = 0#32
  acap : st.acap = ac0
  nassump : st.nassump = 0#32
  nkl : st.nkl = 0#32
  nana : st.nana = 0#32

private theorem K5InitScalar.putArr {nv ac : BitVec 32} {st : K512State}
    (h : K5InitScalar nv ac st) (f : K5ArrField) (i : Nat) (v : BitVec 32) :
    K5InitScalar nv ac (st.putArr f i v) := by
  cases f <;> exact ⟨h.nv, h.nc, h.lvl, h.prop, h.trl_end, h.unass, h.incons, h.alen, h.acap,
    h.nassump, h.nkl, h.nana⟩

/-- `5/24`: Parametric `Func.wp` proof for `full_k512_init`. -/
theorem full_k512_init_wp (Γ : Env) :
    ∀ args m Q X, k5InitSpec args m Q X → Func.wp Γ full_k512_init_body args m Q X := by
  rintro ⟨hPtr, nv, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  have hsc_lt : c.scratch_cap < 2 ^ 64 := Nat.lt_trans c.hscr (by decide)
  c0_hsteps_nogrp
  · have hif : c.scratch_cap < k5MinScr ∨ k5MaxV < nv.toNat := Or.inl (by unfold k5MinScr; bv_omega)
    simp only [hif, ite_true] at hQ; exact hQ
  · have hif : c.scratch_cap < k5MinScr ∨ k5MaxV < nv.toNat := Or.inr (by unfold k5MaxV; bv_omega)
    simp only [hif, ite_true] at hQ; exact hQ
  · have hcap_ge : k5MinScr ≤ c.scratch_cap := by unfold k5MinScr; bv_omega
    have hnv_le : nv.toNat ≤ k5MaxV := by unfold k5MaxV; bv_omega
    have hnot : ¬ (c.scratch_cap < k5MinScr ∨ k5MaxV < nv.toNat) := by omega
    simp only [hnot, ite_false] at hQ
    let scr := s.scratch.scratch_buf
    have hscr_len : scr.length = c.scratch_cap := hlen.scratch_ok.scratch_buf_len
    have hscr_ge : 21792 ≤ scr.length := by unfold k5MinScr at hcap_ge; omega
    let acap := scr.length - 21792
    have hacap_ge : k5MinScr - k5Base - k5SlabFixed ≤ acap := by
      unfold k5MinScr k5Base k5SlabFixed at *; omega
    have hacap_lt : acap < dimacsBound := by have := c.hscr; unfold dimacsBound at *; omega
    let ks0 := K512State.ofSlab (scr.drop 2304)
    have hsh0 : ks0.ShapesOk acap := by
      have h1 := K512State.shapesOk_ofSlab (xs := scr.drop 2304) (by simp; omega)
      rwa [show (scr.drop 2304).length - 19488 = acap by simp [acap]; omega] at h1
    have hmF : (FullK512Frame c s ⋆ K512Mem (c.pScratchBuf + 9216#64) ks0 ⋆ R) m := by
      rw [fullMem_eq_k5Frame hscr_ge] at hm; exact sep_ac hm
    clear hm
    c0_hsteps_nogrp
    let kPtr := c.pScratchBuf + 9216#64
    have hmHdr : (array (t := i32) (c.pScratchBuf + BitVec.ofNat 64 2304 * 4)
        (k5HdrWords ks0) ⋆ ((K512Tree kPtr ks0).rest (k5Path 0) ⋆
          (FullK512Frame c s ⋆ R))) m :=
      k5Focus_hdr (sep_ac hmF)
    clear hmF
    refine wp_while_state1 (fun p : BitVec 32 × List (BitVec 32) => p.1) (fun p => 32 - p.1.toNat)
      (fun p m' => p.1.toNat ≤ 32 ∧ p.2.length = 32 ∧ (∀ j < p.1.toNat, p.2[j]? = some 0#32) ∧
        (array (t := i32) (c.pScratchBuf + BitVec.ofNat 64 2304 * 4) p.2 ⋆
          ((K512Tree kPtr ks0).rest (k5Path 0) ⋆ (FullK512Frame c s ⋆ R))) m')
      ?_ ?_
    · intro J hJ
      exact wp_jump_state (proj := fun p : BitVec 32 × List (BitVec 32) => (p.1, ()))
        (0#32, k5HdrWords ks0) rfl
        (hJ _ m ⟨by simp, k5HdrWords_length hsh0, fun _ hj => by simp at hj, hmHdr⟩)
    · rintro J ⟨i, hdrWs⟩ m' ⟨hi_le, hlen_w, hzeros, hm'⟩ ih
      dsimp only at hi_le hlen_w hzeros hm'
      c0_hsplit
      · have hi_lt : i.toNat < 32 := by bv_omega
        have hi_w : i.toNat < hdrWs.length := by rw [hlen_w]; exact hi_lt
        c0_hsteps!
        have hsw : (BitVec.setWidth 64 i).toNat = i.toNat := by have := i.isLt; simp; omega
        rw [hsw] at hm
        refine ih (i + 1#32, hdrWs.set i.toNat 0#32) _ (by bv_omega)
          ⟨by bv_omega, by simp [hlen_w], ?_, hm⟩
        intro j hj
        have hi1 : (i + 1#32).toNat = i.toNat + 1 := by bv_omega
        rw [hi1] at hj
        by_cases hji : j = i.toNat
        · subst hji; exact List.getElem?_set_self hi_w
        · rw [List.getElem?_set_ne (Ne.symm hji)]; exact hzeros j (by omega)
      · have hi_eq : i.toNat = 32 := by bv_omega
        have hrep : hdrWs = List.replicate 32 0#32 := by
          apply List.ext_getElem (by simp [hlen_w]); intro j hj _
          have hj32 : j < 32 := by simp [hlen_w] at hj; exact hj
          have hz := hzeros j (by omega)
          rw [List.getElem?_eq_getElem (by omega : j < hdrWs.length)] at hz
          rw [List.getElem_replicate]; exact Option.some.inj hz
        rw [hrep] at hm'
        let ks1 : K512State :=
          { ks0 with nv := 0#32, nc := 0#32, lvl := 0#32, prop := 0#32, trl_end := 0#32,
                     unass := 0#32, incons := 0#32, qfirst := 0#32, qlast := 0#32, qsearch := 0#32,
                     qstamp := 0#32, ticks := 0#32, tick_lim := 0#32, alen := 0#32, acap := 0#32,
                     nassump := 0#32, nkl := 0#32, nana := 0#32, status := 0#32, phase := 0#32,
                     hdrTail := List.replicate 12 0#32 }
        have hsh1 : ks1.ShapesOk acap := { hsh0 with hdrTail_len := by simp [ks1] }
        have hunf : (K512Mem kPtr ks1 ⋆ (FullK512Frame c s ⋆ R)) m' := by
          refine k5Unfocus_hdr (ks := ks0) (ks' := ks1) (hdr' := List.replicate 32 0#32) ?_ hm'
          simp only [K512Mem, K512Tree, k5Path, SepTree.set, SepTree.eval, k5HdrWords, ks1,
            List.replicate]; congr 1
        let kPtr0 := c.pScratchBuf + BitVec.ofNat 64 2304 * 4
        have hmA1 : (K512MemA kPtr0 acap ks1 ⋆ (FullK512Frame c s ⋆ R)) m' :=
          k5Mem_to_amem hsh1 hunf
        clear hm' hunf
        c0_hsteps_nogrp
        let ksH0 := (((ks1.putHdr .nv nv).putHdr .unass nv).putHdr .tick_lim 16384#32).putHdr
          .acap ((BitVec.ofNat 64 c.scratch_cap - 2304#64 - 19488#64).setWidth 32)
        let ksH := if nv == 0#32 then
            ((ksH0.putHdr .qfirst 0xFFFFFFFF#32).putHdr .qlast 0xFFFFFFFF#32).putHdr .qsearch
              0xFFFFFFFF#32
          else
            (((ksH0.putHdr .qfirst 0#32).putHdr .qlast (nv - 1#32)).putHdr
              .qsearch (nv - 1#32)).putHdr .qstamp nv
        have hshH : ksH.ShapesOk acap := by
          have hh0 := (((hsh1.putHdr .nv nv).putHdr .unass nv).putHdr .tick_lim 16384#32).putHdr
            .acap ((BitVec.ofNat 64 c.scratch_cap - 2304#64 - 19488#64).setWidth 32)
          dsimp only [ksH]; split
          · exact ((hh0.putHdr .qfirst _).putHdr .qlast _).putHdr .qsearch _
          · exact (((hh0.putHdr .qfirst _).putHdr .qlast _).putHdr .qsearch _).putHdr .qstamp _
        have e_acap : ksH.acap = BitVec.ofNat 32 acap := by
          have hh : ksH.acap = (BitVec.ofNat 64 c.scratch_cap - 2304#64 - 19488#64).setWidth 32 :=
            by
            dsimp only [ksH]; split <;> dsimp only [ksH0] <;> k5_field
          rw [hh]; apply BitVec.eq_of_toNat_eq
          have hsc := c.hscr; unfold dimacsBound at hsc
          simp only [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_ofNat]
          omega
        refine wp_join0 (fun m2 => (K512MemA kPtr0 acap ksH ⋆ (FullK512Frame c s ⋆ R)) m2) ?_ ?_
        · intro J2 m2 hm2
          c0_hsteps_nogrp
          have hInitH : K5InitScalar nv ksH.acap ksH := by
            dsimp only [ksH]; split <;> dsimp only [ksH0, ks1] <;>
              exact ⟨by k5_field, by k5_field, by k5_field, by k5_field, by k5_field, by k5_field,
                by k5_field, by k5_field, by k5_field, by k5_field, by k5_field, by k5_field⟩
          refine wp_while_state1 (fun p : BitVec 32 × K512State => p.1)
            (fun p => nv.toNat - p.1.toNat)
            (fun p m3 => p.1.toNat ≤ nv.toNat ∧ p.2.ShapesOk acap ∧ K5InitScalar nv ksH.acap p.2 ∧
              (∀ v < p.1.toNat, p.2.lvlArr[v]? = some 0#32 ∧ p.2.rsn[v]? = some 0xFFFFFFFF#32 ∧
                p.2.flags[v]? = some 0#32) ∧
              (K512MemA kPtr0 acap p.2 ⋆ (FullK512Frame c s ⋆ R)) m3)
            ?_ ?_
          · intro J3 hJ3
            exact wp_jump_state (proj := fun p : BitVec 32 × K512State => (p.1, ()))
              (0#32, ksH) rfl (hJ3 _ m2 ⟨by simp, hshH, hInitH, fun _ h => by simp at h, hm2⟩)
          · rintro J3 ⟨j, st⟩ m3 ⟨hj_le, hsh_st, hsc_st, hvars_st, hm3⟩ ih3
            dsimp only at hj_le hsh_st hsc_st hvars_st hm3
            c0_hsplit
            · have hj_lt : j.toNat < nv.toNat := by bv_omega
              have hj_512 : j.toNat < 512 := by unfold k5MaxV at hnv_le; omega
              c0_hsteps!
              all_goals
                have hj1 : (j + 1#32).toNat = j.toNat + 1 := by bv_omega
                refine ih3 (j + 1#32, _) _ (by dsimp only; rw [hj1]; omega)
                  ⟨by dsimp only; rw [hj1]; omega, ?_, ?_, ?_, hm⟩
                · exact (((((hsh_st.putArr .lvlArr _ _).putArr .rsn _ _).putArr .flags _ _).putArr
                    .qstampArr _ _).putArr .qprev _ _).putArr .qnext _ _
                · exact (((((hsc_st.putArr .lvlArr _ _).putArr .rsn _ _).putArr .flags _ _).putArr
                    .qstampArr _ _).putArr .qprev _ _).putArr .qnext _ _
                · intro v hv; rw [hj1] at hv
                  by_cases hvj : v = j.toNat
                  · subst hvj
                    exact ⟨by
                        k5_field
                        rw [List.getElem?_set_self (by rw [hsh_st.lvlArr_len]; exact hj_512)]; rfl,
                      by
                        k5_field
                        rw [List.getElem?_set_self (by rw [hsh_st.rsn_len]; exact hj_512)]; rfl,
                      by
                        k5_field
                        rw [List.getElem?_set_self (by rw [hsh_st.flags_len]; exact hj_512)]; rfl⟩
                  · have hvv := hvars_st v (by omega)
                    exact ⟨by k5_field; rw [List.getElem?_set_ne (Ne.symm hvj)]; exact hvv.1,
                      by k5_field; rw [List.getElem?_set_ne (Ne.symm hvj)]; exact hvv.2.1,
                      by k5_field; rw [List.getElem?_set_ne (Ne.symm hvj)]; exact hvv.2.2⟩
            · have hj_eq : j.toNat = nv.toNat := by bv_omega
              rw [hj_eq] at hvars_st
              c0_hsteps_nogrp
              have hnl_eq : (nv <<< (1 : Nat)).toNat = 2 * nv.toNat := by
                rw [k5_shl1_toNat]; unfold k5MaxV at hnv_le; omega
              refine wp_while_state1 (fun p : BitVec 32 × K512State => p.1)
                (fun p => 2 * nv.toNat - p.1.toNat)
                (fun p m4 => p.1.toNat ≤ 2 * nv.toNat ∧ p.2.ShapesOk acap ∧
                  K5InitScalar nv ksH.acap p.2 ∧
                  (∀ v < nv.toNat, p.2.lvlArr[v]? = some 0#32 ∧ p.2.rsn[v]? = some 0xFFFFFFFF#32 ∧
                    p.2.flags[v]? = some 0#32) ∧
                  (∀ l < p.1.toNat, p.2.vals[l]? = some 0#32 ∧ p.2.whead[l]? = some 0xFFFFFFFF#32) ∧
                  (K512MemA kPtr0 acap p.2 ⋆ (FullK512Frame c s ⋆ R)) m4)
                ?_ ?_
              · intro J4 hJ4
                exact wp_jump_state (proj := fun p : BitVec 32 × K512State => (p.1, ()))
                  (0#32, st) rfl (hJ4 _ m3 ⟨by simp, hsh_st, hsc_st, hvars_st, fun _ h => by
                    simp at h, hm3⟩)
              · rintro J4 ⟨k, st4⟩ m4 ⟨hk_le, hsh4, hsc4, hvars4, hlits4, hm4⟩ ih4
                dsimp only at hk_le hsh4 hsc4 hvars4 hlits4 hm4
                c0_hsplit
                · have hk_lt : k.toNat < 2 * nv.toNat := by rw [← hnl_eq]; bv_omega
                  have hk_1024 : k.toNat < 1024 := by unfold k5MaxV at hnv_le; omega
                  c0_hsteps!
                  let st4' := (st4.putArr .vals k.toNat 0#32).putArr .whead k.toNat 0xFFFFFFFF#32
                  have hk1 : (k + 1#32).toNat = k.toNat + 1 := by bv_omega
                  refine ih4 (k + 1#32, st4') _ (by dsimp only; rw [hk1]; omega)
                    ⟨by dsimp only; rw [hk1]; omega,
                     (hsh4.putArr .vals k.toNat 0#32).putArr .whead k.toNat 0xFFFFFFFF#32,
                     (hsc4.putArr .vals k.toNat 0#32).putArr .whead k.toNat 0xFFFFFFFF#32,
                     fun v hv => let hvv := hvars4 v hv
                     ⟨by k5_field; exact hvv.1, by k5_field; exact hvv.2.1,
                       by k5_field; exact hvv.2.2⟩,
                     ?_, hm⟩
                  intro l hl; rw [hk1] at hl
                  by_cases hlk : l = k.toNat
                  · subst hlk
                    exact ⟨by
                        dsimp only [st4']; k5_field
                        rw [List.getElem?_set_self (by rw [hsh4.vals_len]; exact hk_1024)],
                      by
                        dsimp only [st4']; k5_field
                        rw [List.getElem?_set_self (by rw [hsh4.whead_len]; exact hk_1024)]⟩
                  · have hll := hlits4 l (by omega)
                    exact ⟨by
                        dsimp only [st4']; k5_field
                        rw [List.getElem?_set_ne (Ne.symm hlk)]; exact hll.1,
                      by
                        dsimp only [st4']; k5_field
                        rw [List.getElem?_set_ne (Ne.symm hlk)]; exact hll.2⟩
                · have hk_eq : k.toNat = 2 * nv.toNat := by
                    have hnl : ¬ k.toNat < (nv <<< (1 : Nat)).toNat := ‹_›; rw [hnl_eq] at hnl
                    omega
                  rw [hk_eq] at hlits4
                  c0_hsteps!
                  have hfin := k5Init_finish_inv hsh4 hacap_ge hacap_lt hnv_le hsc4.nv hsc4.nc
                    hsc4.lvl hsc4.prop hsc4.trl_end hsc4.unass (hsc4.acap.trans e_acap) hsc4.alen
                    hsc4.incons hsc4.nassump hsc4.nkl hsc4.nana hvars4 hlits4
                  obtain ⟨_, hm4'⟩ := k5MemA_to_mem hm4
                  have hmJ := fullMem_join_k5 (c := c) (s := s) (acap := acap) (ks' := st4)
                    (R := R) (by change 2304 ≤ scr.length; omega) hsh4 (sep_ac hm4')
                  let scr' := s.scratch.scratch_buf.take 2304 ++ st4.toSlab
                  have htk_len : (s.scratch.scratch_buf.take 2304).length = 2304 :=
                    List.length_take_of_le (by change 2304 ≤ scr.length; omega)
                  have hscr'_len : scr'.length = c.scratch_cap := by
                    simp only [scr', List.length_append, htk_len, K512State.toSlab_length hsh4]
                    dsimp only [acap]; omega
                  have hpre : ∀ x < k5Base, scr'[x]? = s.scratch.scratch_buf[x]? := fun x hx => by
                    have htk : x < (s.scratch.scratch_buf.take 2304).length := by
                      rw [htk_len]; unfold k5Base at hx; omega
                    rw [List.getElem?_append_left htk,
                      List.getElem?_take_of_lt (by unfold k5Base at hx; omega)]
                  have hof : k5StateOfScratch scr' = st4 := by
                    unfold k5StateOfScratch k5Base
                    rw [k5_slab_drop_exact _ st4.toSlab htk_len]
                    exact K512State.ofSlab_toSlab hsh4
                  refine hQ scr' m4 (k5_fullState_lengthsOk_scratch hlen hscr'_len) hpre
                    (fun P => ⟨by omega, by rw [hscr'_len]; exact c.hscr, ?_⟩)
                    (by rw [hof]; exact hfin.2) (by rw [hof]; exact hsc4.nv)
                    (by rw [hof]; exact hsc4.nc)
                    (by rw [hof]; exact hsc4.lvl) (by rw [hof]; exact hsc4.prop)
                    (by rw [hof]; exact hsc4.trl_end) (by rw [hof]; exact hsc4.unass)
                    (by rw [hof]; exact hsc4.incons) (by rw [hof]; exact hsc4.nassump) hmJ
                  rw [hof, show scr'.length - (k5Base + k5SlabFixed) = acap by
                    unfold k5Base k5SlabFixed acap; omega]
                  exact hfin.1 P
        · intro J2 hJ2
          c0_hsteps!
          · exact hJ2 _ (by simp [ksH, show nv = 0#32 from by bv_omega]; exact hm)
          · exact hJ2 _ (by simp [ksH, show ¬ nv = 0#32 from by bv_omega]; exact hm)

/-- `6/24`: Parametric `Func.wp` proof for `full_k512_add_clause`. -/
theorem full_k512_add_clause_wp (Γ : Env)
    (hAssign : ∀ args m Q X, k5AssignSpec args m Q X →
      Γ "full_k512_assign" [i64, i32, i32] [] args m Q X)
    (hWatch : ∀ args m Q X, k5WatchSpec args m Q X →
      Γ "full_k512_watch" [i64, i32, i32, i32] [] args m Q X) :
    ∀ args m Q X, k5AddClauseSpec args m Q X →
      Func.wp Γ full_k512_add_clause_body args m Q X := by
  rintro ⟨hPtr, litsPtr, sz, ⟨⟩⟩ m Q X ⟨c, s, P, scr, xs, R, rfl, hlen, hscr_buf, hinv_s, hsync,
    hlvl0, hsz_xs, hsz_max, hxlits, hent, hm, hQ⟩
  rcases hinv_s with ⟨hscr_ge, hscr_lt, hinv⟩
  let acap := scr.length - (k5Base + k5SlabFixed)
  let ks := k5StateOfScratch scr
  have hsh : ks.ShapesOk acap := hinv.shapes
  have hnv : ks.nv.toNat ≤ k5MaxV := hinv.clauses.nv_le
  have hal : ks.alen.toNat ≤ acap := hinv.clauses.alen_le
  have hacap_lt : acap < 2 ^ 28 := hinv.clauses.acap_lt
  have hca_eq : ks.acap.toNat = acap := by
    rw [hinv.clauses.acap_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hscr_len : scr.length = c.scratch_cap := hscr_buf ▸ hlen.scratch_ok.scratch_buf_len
  have hscr_21792 : 21792 ≤ scr.length := by unfold k5MinScr at hscr_ge; omega
  let kPtr := c.pScratchBuf + BitVec.ofNat 64 2304 * 4
  have hmA : (K512MemA kPtr acap ks ⋆ (array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆
      (array (t := i32) litsPtr xs ⋆ (array (t := i32) c.pScratchBuf (scr.take 2304) ⋆ R)))) m :=
    fullAddClause5_mem_to_ka hscr_21792 hsh rfl hm
  clear hm
  have hreorg : ∀ {ks' : K512State} {m' : Mem 64} (hsh' : ks'.ShapesOk acap),
      (K512MemA kPtr acap ks' ⋆ (array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆
        (array (t := i32) litsPtr xs ⋆
          (array (t := i32) c.pScratchBuf (scr.take 2304) ⋆ R)))) m' →
      let scr' := scr.take 2304 ++ ks'.toSlab
      let s' : FullState := { s with scratch := { s.scratch with scratch_buf := scr' } }
      scr'.length = c.scratch_cap ∧ (∀ i < k5Base, scr'[i]? = scr[i]?) ∧
      (array64 (c.hdr + 32) (Full.hdrTailWords c s') ⋆ array (t := i32) c.pScratchBuf scr' ⋆
        array (t := i32) litsPtr xs ⋆ R) m' := by
    intro ks' m' hsh' hm' scr' s'
    have htk : (scr.take 2304).length = 2304 := List.length_take_of_le (by omega)
    have hlen' : scr'.length = c.scratch_cap := by
      simp only [scr', List.length_append, htk, K512State.toSlab_length hsh']
      unfold acap k5Base k5SlabFixed; omega
    have hpre : ∀ i < k5Base, scr'[i]? = scr[i]? := fun i hi => by
      rw [List.getElem?_append_left (by unfold k5Base at hi; omega),
        List.getElem?_take_of_lt (by unfold k5Base at hi; omega)]
    exact ⟨hlen', hpre, fullAddClause5_ka_to_mem (by omega) hsh' hm'⟩
  have hscr_orig : scr.take 2304 ++ ks.toSlab = scr := by
    unfold ks k5StateOfScratch k5Base
    rw [K512State.toSlab_ofSlab (by simp; omega), List.take_append_drop]
  have hof_slab : ∀ {ks' : K512State} (hsh' : ks'.ShapesOk acap),
      k5StateOfScratch (scr.take 2304 ++ ks'.toSlab) = ks' := fun {ks'} hsh' => by
    unfold k5StateOfScratch k5Base
    rw [k5_slab_drop_exact _ ks'.toSlab (by simp; omega)]; exact K512State.ofSlab_toSlab hsh'
  have hmk_inv : ∀ {ks' : K512State}, K512Inv acap P ks' →
      K512ScratchInv P (scr.take 2304 ++ ks'.toSlab) := fun {ks'} hi' => by
    have hlen' : (scr.take 2304 ++ ks'.toSlab).length = scr.length := by
      simp only [List.length_append, List.length_take_of_le (by omega : 2304 ≤ scr.length),
        K512State.toSlab_length hi'.shapes]; unfold acap k5Base k5SlabFixed; omega
    refine ⟨by omega, by omega, ?_⟩; rw [hof_slab hi'.shapes, hlen']; exact hi'
  c0_hsplit
  · -- sz == 0
    have hsz0 : sz = 0#32 := ‹_›
    have hunsat : ∀ β, ¬ P β := by
      rw [hsz0] at hent; simp at hent; exact SemEntails.unsat_of_nil hent
    c0_hsteps!
    have hinv' := k5SetIncons_preserves_inv hinv hunsat
    have hmF := hreorg hinv'.shapes hm
    exact hQ true _ _ hmF.1 hmF.2.1 (hmk_inv hinv') (by rw [hof_slab hinv'.shapes]; exact hsync)
      (by rw [hof_slab hinv'.shapes]; k5_field; exact hlvl0)
      (by rw [hof_slab hinv'.shapes]; k5_field)
      (by rw [hof_slab hinv'.shapes]; k5_field)
      (by unfold k5AssumpLitsS k5AssumpLits; rw [hof_slab hinv'.shapes]; k5_field)
      (fun h2 => by rw [hsz0] at h2; simp at h2)
      (fun M _ hM => by rw [hof_slab hinv'.shapes]; exact hM) hmF.2.2
  · c0_hsplit
    · -- sz == 1
      have hsz1 : sz = 1#32 := ‹_›
      have h0_xs : 0 < xs.length := by rw [hsz1] at hsz_xs; simp at hsz_xs; omega
      have hu_lt : (xs[0]'h0_xs).toNat < 2 * ks.nv.toNat := by
        have h := hxlits 0 (by rw [hsz1]; decide)
        rwa [List.getElem?_eq_getElem h0_xs, Option.getD_some] at h
      have hu_1024 : (xs[0]'h0_xs).toNat < 1024 := by unfold k5MaxV at hnv; omega
      have hent1 : SemEntails P [(xs[0]'h0_xs).toNat] := by
        have htk : (xs.take sz.toNat).map BitVec.toNat = [(xs[0]'h0_xs).toNat] := by
          rw [hsz1]; cases xs with | nil => simp at h0_xs | cons x _ => rfl
        rwa [htk] at hent
      c0_hsteps_nogrp
      refine LeanQbe.T.wp_unroll_group fun _ _ => ?_
      c0_hsplit
      · -- uv == 2u => incons = 1u
        have hfals : ks.vals[(xs[0]'h0_xs).toNat]? = some 2#32 := by
          have hv_eq : ks.vals[(xs[0]'h0_xs).toNat]?.getD 0#32 = 2#32 := by simpa using ‹_›
          rw [List.getElem?_eq_getElem (by rw [hsh.vals_len]; exact hu_1024),
            Option.getD_some] at hv_eq
          rw [List.getElem?_eq_getElem (by rw [hsh.vals_len]; exact hu_1024), hv_eq]
        have hunsat : ∀ β, ¬ P β := SemEntails.unsat_of_falsified hent1 fun x hx => by
          simp at hx; subst hx; exact (k5_falsified_lvl0_entails hinv hlvl0 hu_lt hfals).2
        c0_hsteps!
        have hinv' := k5SetIncons_preserves_inv hinv hunsat
        have hmF := hreorg hinv'.shapes hm
        exact hQ true _ _ hmF.1 hmF.2.1 (hmk_inv hinv') (by rw [hof_slab hinv'.shapes]; exact hsync)
          (by rw [hof_slab hinv'.shapes]; k5_field; exact hlvl0)
          (by rw [hof_slab hinv'.shapes]; k5_field) (by rw [hof_slab hinv'.shapes]; k5_field)
          (by unfold k5AssumpLitsS k5AssumpLits; rw [hof_slab hinv'.shapes]; k5_field)
          (fun h2 => by rw [hsz1] at h2; simp at h2)
          (fun M _ hM => by rw [hof_slab hinv'.shapes]; exact hM) hmF.2.2
      · refine LeanQbe.T.wp_unroll_group fun _ _ => ?_
        c0_hsplit
        · -- uv == 0u => assign(k, ul, 0xFFFFFFFFu)
          have hun0 : ks.vals[(xs[0]'h0_xs).toNat]? = some 0#32 := by
            have hv_eq : ks.vals[(xs[0]'h0_xs).toNat]?.getD 0#32 = 0#32 := by simpa using ‹_›
            rw [List.getElem?_eq_getElem (by rw [hsh.vals_len]; exact hu_1024),
              Option.getD_some] at hv_eq
            rw [List.getElem?_eq_getElem (by rw [hsh.vals_len]; exact hu_1024), hv_eq]
          have hte_lt := k5_trl_end_lt_of_unassigned hsh hnv hinv.assign hu_lt (by simp [hun0])
          obtain ⟨hinv', hsync'⟩ := k5AssignStep_preserves_inv hinv hsync hu_lt hun0
            (fun _ => hent1) (fun hpos => by rw [hlvl0] at hpos; simp at hpos) (Or.inl rfl)
          c0_call hAssign
          refine ⟨acap, ks, _, hsh, hacap_lt, hnv, hu_lt, hte_lt,
            (k5MemA_to_mem hmA).2, fun m' hm' => ?_⟩
          c0_hsteps!
          have hmF := hreorg hinv'.shapes (k5Mem_to_amem hinv'.shapes hm')
          exact hQ true _ _ hmF.1 hmF.2.1 (hmk_inv hinv')
            (by rw [hof_slab hinv'.shapes]; exact hsync')
            (by rw [hof_slab hinv'.shapes]; exact hlvl0)
            (by rw [hof_slab hinv'.shapes]; rfl) (by rw [hof_slab hinv'.shapes]; rfl)
            (by unfold k5AssumpLitsS k5AssumpLits; rw [hof_slab hinv'.shapes]; rfl)
            (fun h2 => by rw [hsz1] at h2; simp at h2)
            (fun M _ hM => by rw [hof_slab hinv'.shapes]; exact hM) hmF.2.2
        · -- uv == 1u => noop
          c0_hsteps!
          have hmF := hreorg hsh hmA; rw [hscr_orig] at hmF
          exact hQ true scr m hscr_len (fun _ _ => rfl) ⟨hscr_ge, hscr_lt, hinv⟩ hsync hlvl0
            rfl rfl rfl (fun h2 => by rw [hsz1] at h2; simp at h2) (fun _ _ hM => hM) hmF.2.2
    · -- sz >= 2
      have hsz2 : 2 ≤ sz.toNat := by
        have hne0 : sz ≠ 0#32 := ‹_›; have hne1 : sz ≠ 1#32 := ‹_›
        have h0 : sz.toNat ≠ 0 := fun h => hne0 (BitVec.eq_of_toNat_eq h)
        have h1 : sz.toNat ≠ 1 := fun h => hne1 (BitVec.eq_of_toNat_eq h); omega
      c0_hsplit
      · -- nc >= 2048 => false
        c0_hsteps!
        have hmF := hreorg hsh hmA; rw [hscr_orig] at hmF
        exact hQ false scr m hscr_len (fun _ _ => rfl) ⟨hscr_ge, hscr_lt, hinv⟩ hsync hlvl0
          rfl rfl rfl (fun _ => ⟨rfl, rfl, rfl⟩) (fun _ _ hM => hM) hmF.2.2
      · c0_hsplit
        · -- off + sz > acap => false
          c0_hsteps!
          have hmF := hreorg hsh hmA; rw [hscr_orig] at hmF
          exact hQ false scr m hscr_len (fun _ _ => rfl) ⟨hscr_ge, hscr_lt, hinv⟩ hsync hlvl0
            rfl rfl rfl (fun _ => ⟨rfl, rfl, rfl⟩) (fun _ _ hM => hM) hmF.2.2
        · have hnc_lt : ks.nc.toNat < k5MaxCl := by unfold k5MaxCl; bv_omega
          have hnc_2048 : ks.nc.toNat < 2048 := hnc_lt
          have hoff_fit : ks.alen.toNat + sz.toNat ≤ acap := by
            have hcap_lt : ks.acap.toNat < 2 ^ 28 := by rw [hca_eq]; exact hacap_lt
            have hal_ks : ks.alen.toNat ≤ ks.acap.toNat := by rw [hca_eq]; exact hal
            rw [← hca_eq]; bv_omega
          obtain ⟨Rfr, hRfr⟩ : ∃ Rfr : Mem 64 → Prop,
              Rfr = (array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆
                (array (t := i32) c.pScratchBuf (scr.take 2304) ⋆ R)) := ⟨_, rfl⟩
          have hmA_r : (K512MemA (c.pScratchBuf + BitVec.ofNat 64 2304 * 4) acap ks ⋆
              (array (t := i32) litsPtr xs ⋆ Rfr)) m := by
            rw [hRfr]; exact sep_ac hmA
          c0_hsteps_nogrp
          refine wp_while_state1 (fun p : BitVec 32 × List (BitVec 32) => p.1)
            (fun p => sz.toNat - p.1.toNat)
            (fun p m' => p.1.toNat ≤ sz.toNat ∧ p.2.length = acap ∧
              (∀ j < ks.alen.toNat, p.2[j]? = ks.arena[j]?) ∧
              (∀ j < p.1.toNat, p.2[ks.alen.toNat + j]? = xs[j]?) ∧
              (K512MemA (c.pScratchBuf + BitVec.ofNat 64 2304 * 4) acap
                { ks with arena := p.2 } ⋆ (array (t := i32) litsPtr xs ⋆ Rfr)) m')
            ?_ ?_
          · intro J hJ
            exact wp_jump_state (proj := fun p : BitVec 32 × List (BitVec 32) => (p.1, ()))
              (0#32, ks.arena) rfl
              (hJ _ m ⟨by simp, hsh.arena_len, fun _ _ => rfl, fun _ hj => by simp at hj, hmA_r⟩)
          · rintro J ⟨i, ar⟩ m' ⟨hi_le, har_len, har_old, har_new, hm'⟩ ih
            dsimp only at hi_le har_len har_old har_new hm' ⊢
            obtain ⟨st, hst⟩ : ∃ x : K512State, x = { ks with arena := ar } := ⟨_, rfl⟩
            rw [← hst] at hm'
            c0_hsplit
            · have hi_lt : i.toNat < sz.toNat := by bv_omega
              have hi_xs : i.toNat < xs.length := by omega
              have hoff_i_wrap : ks.alen.toNat + i.toNat < 2 ^ 28 := by omega
              have hoff_i_cap : ks.alen.toNat + i.toNat < acap := by omega
              iterate 9 c0_hstep
              refine wp_store_sep (K512MemATactics.store_k5_arena_off _ hoff_i_wrap hoff_i_cap hm')
                fun m2 hm => ?_
              c0_hsteps!
              have hi1 : (i + 1#32).toNat = i.toNat + 1 := by bv_omega
              refine ih (i + 1#32, ar.set (ks.alen.toNat + i.toNat) (xs[i.toNat]'hi_xs)) m2
                (by dsimp only; rw [hi1]; omega)
                ⟨by dsimp only; rw [hi1]; omega, by simp [har_len],
                 fun j hj => by rw [List.getElem?_set_ne (by omega)]; exact har_old j hj, ?_, ?_⟩
              · intro j hj; rw [hi1] at hj
                by_cases hji : j = i.toNat
                · subst hji; rw [List.getElem?_set_self (by rw [har_len]; exact hoff_i_cap),
                    List.getElem?_eq_getElem hi_xs]
                · rw [List.getElem?_set_ne (by omega)]; exact har_new j (by omega)
              · refine Eq.mp (congrArg (fun x =>
                  (K512MemA (c.pScratchBuf + BitVec.ofNat 64 2304 * 4) acap x ⋆ _) _) ?_) hm
                rw [hst]; apply k5State_ext <;> (try rfl)
            · have hi_eq : i.toNat = sz.toNat := by bv_omega
              rw [hi_eq] at har_new
              have h0_xs : 0 < xs.length := by omega
              have h1_xs : 1 < xs.length := by omega
              have hl0_lt : (xs[0]'h0_xs).toNat < 2 * ks.nv.toNat := by
                have h := hxlits 0 (by omega)
                rwa [List.getElem?_eq_getElem h0_xs, Option.getD_some] at h
              have hl1_lt : (xs[1]'h1_xs).toNat < 2 * ks.nv.toNat := by
                have h := hxlits 1 (by omega)
                rwa [List.getElem?_eq_getElem h1_xs, Option.getD_some] at h
              have hpres := k5AddClause_ge2_preserves hinv hsync hnc_lt hsz2 hsz_max hsz_xs
                hoff_fit har_len har_old har_new hxlits hent
              c0_hsteps_nogrp
              obtain ⟨hshM, hmM⟩ := k5MemA_to_mem hm
              c0_call hWatch
              refine ⟨acap, _, _, hshM, hacap_lt, by rw [hst]; exact hnv, hnc_lt,
                by rw [hst]; exact hl0_lt, by rw [hst]; exact hl1_lt, hmM, fun m2 hm2 => ?_⟩
              c0_hsteps!
              have hsh' := hpres.1.shapes
              have hm2_eq : (K512Mem (c.pScratchBuf + BitVec.ofNat 64 2304 * 4)
                  (k5WatchStep ((((({ ks with arena := ar } : K512State).putHdr .alen
                    (ks.alen + sz)).putArr .clOff ks.nc.toNat ks.alen).putArr .clSz ks.nc.toNat
                    sz).putHdr .nc (ks.nc + 1#32)) ks.nc (xs[0]'h0_xs) (xs[1]'h1_xs)) ⋆
                  (array (t := i32) litsPtr xs ⋆ Rfr)) m2 := by
                rw [hst] at hm2; exact hm2
              have hmF := hreorg hsh' (by
                have hA := k5Mem_to_amem hsh' hm2_eq; rw [hRfr] at hA; exact sep_ac hA)
              exact hQ true _ _ hmF.1 hmF.2.1 (hmk_inv hpres.1)
                (by rw [hof_slab hsh']; exact hpres.2.1)
                (by rw [hof_slab hsh']; exact hpres.2.2.1.trans hlvl0)
                (by rw [hof_slab hsh']; exact hpres.2.2.2.1)
                (by rw [hof_slab hsh']; exact hpres.2.2.2.2.1)
                (by unfold k5AssumpLitsS k5AssumpLits
                    rw [hof_slab hsh', hpres.2.2.2.2.1, hpres.2.2.2.2.2.1])
                (fun _ => ⟨by rw [hof_slab hsh']; exact hpres.2.2.2.2.2.2.1,
                  by rw [hof_slab hsh']; exact hpres.2.2.2.2.2.2.2.1,
                  by rw [hof_slab hsh']; exact hpres.2.2.2.2.2.2.2.2.1⟩)
                (fun M hxsM hM => by
                  rw [hof_slab hsh']; exact hpres.2.2.2.2.2.2.2.2.2 M hxsM hM) hmF.2.2

private theorem k5_arena_take2 {ar : List (BitVec 32)} {off acap : Nat} {a b : BitVec 32}
    (hlen : ar.length = acap) (h1 : off + 1 < acap) :
    ((((ar.set off a).set (off + 1) b).drop off).take 2).map BitVec.toNat =
      [a.toNat, b.toNat] := by
  have hlen0 : (ar.set off a).length = acap := by rw [List.length_set, hlen]
  have hlen1 : ((ar.set off a).set (off + 1) b).length = acap := by rw [List.length_set, hlen0]
  apply List.ext_getElem
  · simp only [List.length_map, List.length_take, List.length_drop, hlen1,
      List.length_cons, List.length_nil]
    omega
  · intro k hk1 _
    have hk2 : k < 2 := by simp at hk1; omega
    simp only [List.getElem_map, List.getElem_take, List.getElem_drop]
    rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl
    · simp only [Nat.add_zero, List.getElem_cons_zero]
      rw [List.getElem_set_ne (by omega : off + 1 ≠ off), List.getElem_set_self]
    · simp only [List.getElem_cons_succ, List.getElem_cons_zero]
      rw [List.getElem_set_self]

/-- `7/24`: Parametric `Func.wp` proof for `full_k512_add_live`. -/
theorem full_k512_add_live_wp (Γ : Env)
    (hBt : ∀ args m Q X, k5BacktrackSpec args m Q X →
      Γ "full_k512_backtrack" [i64, i32] [] args m Q X)
    (hAssign : ∀ args m Q X, k5AssignSpec args m Q X →
      Γ "full_k512_assign" [i64, i32, i32] [] args m Q X)
    (hWatch : ∀ args m Q X, k5WatchSpec args m Q X →
      Γ "full_k512_watch" [i64, i32, i32, i32] [] args m Q X) :
    ∀ args m Q X, k5AddLiveSpec args m Q X →
      Func.wp Γ full_k512_add_live_body args m Q X := by
  rintro ⟨hPtr, a, b, ⟨⟩⟩ m Q X ⟨c, s, P, R, rfl, hlen, hinv_s, ha_lt, hb_unit, hb_bin, hm, hQ⟩
  rcases hinv_s with ⟨hscr_ge, hscr_lt, hinv0⟩
  let scr := s.scratch.scratch_buf
  have hscr_len : scr.length = c.scratch_cap := hlen.scratch_ok.scratch_buf_len
  have hscr_21792 : 21792 ≤ scr.length := by
    dsimp only [scr]; unfold k5MinScr at hscr_ge; omega
  let acap := scr.length - (k5Base + k5SlabFixed)
  let ks0 := k5StateOfScratch scr
  have hacap_lt : acap < 2 ^ 28 := hinv0.clauses.acap_lt
  have hmF0 : (K512Mem (c.pScratchBuf + 9216#64) ks0 ⋆ (FullK512Frame c s ⋆ R)) m := by
    rw [fullMem_eq_k5Frame hscr_21792] at hm; exact sep_ac hm
  clear hm
  let kPtr := c.pScratchBuf + BitVec.ofNat 64 2304 * 4
  have finish : ∀ {ks' : K512State} {m' : Mem 64},
      K512Inv acap P ks' → K512TrailSynced ks' → ks'.nv = ks0.nv →
      ks'.nassump = ks0.nassump → ks'.assump = ks0.assump →
      (K512Mem kPtr ks' ⋆ (FullK512Frame c s ⋆ R)) m' → Q () m' := by
    intro ks' m' hinv' hsync' hnv' hna' hass' hm'
    have hmJ := fullMem_join_k5 (c := c) (s := s) (acap := acap) (ks' := ks') (R := R) (m := m')
      (by change 2304 ≤ scr.length; omega) hinv'.shapes
      (by dsimp only [kPtr] at hm'; rw [k5Ptr_base_eq] at hm'; exact sep_ac hm')
    let scr' := s.scratch.scratch_buf.take 2304 ++ ks'.toSlab
    have htk_len : (s.scratch.scratch_buf.take 2304).length = 2304 :=
      List.length_take_of_le (by change 2304 ≤ scr.length; omega)
    have hscr'_len : scr'.length = c.scratch_cap := by
      simp only [scr', List.length_append, htk_len, K512State.toSlab_length hinv'.shapes]
      unfold acap k5Base k5SlabFixed; omega
    have hpre : ∀ i < k5Base, scr'[i]? = s.scratch.scratch_buf[i]? := fun i hi => by
      rw [List.getElem?_append_left (by rw [htk_len]; unfold k5Base at hi; omega),
        List.getElem?_take_of_lt (by unfold k5Base at hi; omega)]
    have hof : k5StateOfScratch scr' = ks' := by
      unfold k5StateOfScratch k5Base
      rw [k5_slab_drop_exact _ ks'.toSlab htk_len]
      exact K512State.ofSlab_toSlab hinv'.shapes
    refine hQ scr' m' (k5_fullState_lengthsOk_scratch hlen hscr'_len) hpre
      ⟨by rw [hscr'_len, ← hscr_len]; exact hscr_ge, by rw [hscr'_len]; exact c.hscr, ?_⟩
      (by rw [hof]; exact hsync') (by rw [hof]; exact hnv') (by rw [hof]; exact hna')
      (by unfold k5AssumpLitsS k5AssumpLits; rw [hof, hna', hass']) hmJ
    rw [hof, show scr'.length - (k5Base + k5SlabFixed) = acap by
      unfold acap k5Base k5SlabFixed; omega]
    exact hinv'
  c0_hsteps_nogrp
  c0_call hBt
  refine ⟨acap, P, ks0, _, hinv0, Or.inl rfl,
    by rw [k5Ptr_base_eq]; exact hmF0,
    fun ks1 m1 hinv1 hsync1 hlvl1 _ hbtp _ _ hm1 => ?_⟩
  obtain ⟨Rfr, hRfr⟩ : ∃ Rfr : Mem 64 → Prop, Rfr = (FullK512Frame c s ⋆ R) := ⟨_, rfl⟩
  have hmA1 : (K512MemA (c.pScratchBuf + BitVec.ofNat 64 2304 * 4) acap ks1 ⋆ Rfr) m1 := by
    rw [hRfr]; exact k5Mem_to_amem hinv1.shapes hm1
  have finishR : ∀ {ks' : K512State} {m' : Mem 64},
      K512Inv acap P ks' → K512TrailSynced ks' → ks'.nv = ks0.nv →
      ks'.nassump = ks0.nassump → ks'.assump = ks0.assump →
      (K512Mem (c.pScratchBuf + BitVec.ofNat 64 2304 * 4) ks' ⋆ Rfr) m' → Q () m' :=
    fun hi hs h1 h2 h3 hm' => finish hi hs h1 h2 h3 (by rw [hRfr] at hm'; exact hm')
  clear hm1 hmF0
  have hnv1 := hinv1.clauses.nv_le
  have ha_lt1 : a.toNat < 2 * ks1.nv.toNat := by rw [hbtp.nv]; exact ha_lt
  have ha_1024 : a.toNat < 1024 := by unfold k5MaxV at hnv1; omega
  c0_hsplit
  · -- incons != 0
    c0_hsteps!
    exact finishR hinv1 hsync1 hbtp.nv hbtp.nassump hbtp.assump (k5MemA_to_mem hmA1).2
  · c0_hsplit
    · -- b == 0xFFFFFFFF (unit live clause [a])
      have hent_a := hb_unit ‹_›
      c0_hsteps_nogrp
      refine LeanQbe.T.wp_unroll_group fun _ _ => ?_
      c0_hsplit
      · -- va == 2 => incons = 1
        have hfals : ks1.vals[a.toNat]? = some 2#32 := by
          have hv_eq : ks1.vals[a.toNat]?.getD 0#32 = 2#32 := ‹_›
          rw [List.getElem?_eq_getElem (by rw [hinv1.shapes.vals_len]; exact ha_1024),
            Option.getD_some] at hv_eq
          rw [List.getElem?_eq_getElem (by rw [hinv1.shapes.vals_len]; exact ha_1024), hv_eq]
        have hunsat : ∀ β, ¬ P β := SemEntails.unsat_of_falsified hent_a fun x hx => by
          simp at hx; subst hx; exact (k5_falsified_lvl0_entails hinv1 hlvl1 ha_lt1 hfals).2
        c0_hsteps!
        have hinv2 := k5SetIncons_preserves_inv hinv1 hunsat
        exact finishR hinv2 hsync1 (by k5_field; exact hbtp.nv) (by k5_field; exact hbtp.nassump)
          (by k5_field; exact hbtp.assump) (k5MemA_to_mem hm).2
      · refine LeanQbe.T.wp_unroll_group fun _ _ => ?_
        c0_hsplit
        · -- va == 0 => assign(k, a, 0xFFFFFFFF)
          have hun0 : ks1.vals[a.toNat]? = some 0#32 := by
            have hv_eq : ks1.vals[a.toNat]?.getD 0#32 = 0#32 := ‹_›
            rw [List.getElem?_eq_getElem (by rw [hinv1.shapes.vals_len]; exact ha_1024),
              Option.getD_some] at hv_eq
            rw [List.getElem?_eq_getElem (by rw [hinv1.shapes.vals_len]; exact ha_1024), hv_eq]
          have hte_lt := k5_trl_end_lt_of_unassigned hinv1.shapes hnv1 hinv1.assign ha_lt1
            (by simp [hun0])
          obtain ⟨hinv2, hsync2⟩ := k5AssignStep_preserves_inv hinv1 hsync1 ha_lt1 hun0
            (fun _ => hent_a) (fun hpos => by rw [hlvl1] at hpos; simp at hpos) (Or.inl rfl)
          c0_call hAssign
          refine ⟨acap, ks1, _, hinv1.shapes, hacap_lt, hnv1, ha_lt1, hte_lt,
            (k5MemA_to_mem hmA1).2, fun m2 hm2 => ?_⟩
          c0_hsteps!
          exact finishR hinv2 hsync2 hbtp.nv hbtp.nassump hbtp.assump hm2
        · c0_hsteps!
          exact finishR hinv1 hsync1 hbtp.nv hbtp.nassump hbtp.assump (k5MemA_to_mem hmA1).2
    · -- b != 0xFFFFFFFF (binary live clause [a, b])
      obtain ⟨hb_lt0, hent_ab⟩ := hb_bin ‹_›
      have hb_lt1 : b.toNat < 2 * ks1.nv.toNat := by rw [hbtp.nv]; exact hb_lt0
      have hb_1024 : b.toNat < 1024 := by unfold k5MaxV at hnv1; omega
      have hca1 : ks1.acap.toNat = acap := by
        rw [hinv1.clauses.acap_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      c0_hsplit
      · c0_hsteps!
        exact finishR hinv1 hsync1 hbtp.nv hbtp.nassump hbtp.assump (k5MemA_to_mem hmA1).2
      · c0_hsplit
        · c0_hsteps!
          exact finishR hinv1 hsync1 hbtp.nv hbtp.nassump hbtp.assump (k5MemA_to_mem hmA1).2
        · have hnc_lt : ks1.nc.toNat < k5MaxCl := by unfold k5MaxCl; bv_omega
          have hnc_2048 : ks1.nc.toNat < 2048 := hnc_lt
          have hal_ks : ks1.alen.toNat ≤ ks1.acap.toNat := by rw [hca1]; exact hinv1.clauses.alen_le
          have hcap_lt : ks1.acap.toNat < 2 ^ 28 := by rw [hca1]; exact hacap_lt
          have hoff_fit : ks1.alen.toNat + 2 ≤ acap := by rw [← hca1]; bv_omega
          have hoff0_wrap : ks1.alen.toNat < 2 ^ 28 := by omega
          have hoff0_cap : ks1.alen.toNat < acap := by omega
          have hoff1_wrap : ks1.alen.toNat + (1 : BitVec 32).toNat < 2 ^ 28 := by
            change ks1.alen.toNat + 1 < 2 ^ 28; omega
          have hoff1_cap : ks1.alen.toNat + (1 : BitVec 32).toNat < acap := by
            change ks1.alen.toNat + 1 < acap; omega
          have har_len :
              ((ks1.arena.set ks1.alen.toNat a).set (ks1.alen.toNat + 1) b).length = acap := by
            simp [hinv1.shapes.arena_len]
          have hpres := k5AddClause_ge2_preserves (xs := [a, b]) (sz := 2#32)
            (ar := (ks1.arena.set ks1.alen.toNat a).set (ks1.alen.toNat + 1) b) hinv1 hsync1
            hnc_lt (by decide) (by decide) (by simp) hoff_fit har_len
            (fun j hj => by rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)])
            (fun j hj => by
              have hj2 : j < 2 := by change j < (2#32 : BitVec 32).toNat at hj; simp at hj; exact hj
              rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
              · rw [List.getElem?_set_ne (by omega), Nat.add_zero,
                  List.getElem?_set_self (by rw [hinv1.shapes.arena_len]; exact hoff0_cap)]; rfl
              · rw [List.getElem?_set_self (by simp [hinv1.shapes.arena_len]; exact hoff1_cap)]
                rfl)
            (fun j hj => by
              have hj2 : j < 2 := by change j < (2#32 : BitVec 32).toNat at hj; simp at hj; exact hj
              rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl <;> simpa)
            (by simpa using hent_ab)
          iterate 4 c0_hstep
          refine wp_store_sep (K512MemATactics.store_k5_arena a hoff0_wrap hoff0_cap hmA1)
            fun m_a hm_a => ?_
          iterate 5 c0_hstep
          refine wp_store_sep (K512MemATactics.store_k5_arena_off b hoff1_wrap hoff1_cap hm_a)
            fun m_b hm_b => ?_
          clear hm_a
          c0_hsteps_nogrp
          obtain ⟨hshM, hmM⟩ := k5MemA_to_mem hm
          let stM := (((({ ks1 with
              arena := (ks1.arena.set ks1.alen.toNat a).set (ks1.alen.toNat + 1) b } :
            K512State).putHdr .alen (ks1.alen + 2#32)).putArr .clOff ks1.nc.toNat ks1.alen).putArr
            .clSz ks1.nc.toNat 2#32).putHdr .nc (ks1.nc + 1#32)
          have hsh_stM : stM.ShapesOk acap := by
            have h1 : ({ ks1 with
                arena := (ks1.arena.set ks1.alen.toNat a).set (ks1.alen.toNat + 1) b } :
              K512State).ShapesOk acap := { hinv1.shapes with arena_len := har_len }
            exact (((h1.putHdr .alen _).putArr .clOff _ _).putArr .clSz _ _).putHdr .nc _
          have hmM_eq : (K512Mem (c.pScratchBuf + BitVec.ofNat 64 2304 * 4) stM ⋆ Rfr) m := by
            refine Eq.mp (congrArg (fun x =>
              (K512Mem (c.pScratchBuf + BitVec.ofNat 64 2304 * 4) x ⋆ Rfr) m) ?_) hmM
            dsimp only [stM]; k5_ext <;> simp
          c0_call hWatch
          refine ⟨acap, stM, Rfr, hsh_stM, hacap_lt, by dsimp only [stM]; k5_field; exact hnv1,
            hnc_lt, by dsimp only [stM]; k5_field; exact ha_lt1,
            by dsimp only [stM]; k5_field; exact hb_lt1, hmM_eq, fun m2 hm2 => ?_⟩
          let ks2_0 := k5WatchStep stM ks1.nc a b
          have hinv2 : K512Inv acap P ks2_0 := hpres.1
          have hsync2 : K512TrailSynced ks2_0 := hpres.2.1
          have hlvl2 : ks2_0.lvl = 0#32 := hpres.2.2.1.trans hlvl1
          have hnv2_eq : ks2_0.nv = ks0.nv := hpres.2.2.2.1.trans hbtp.nv
          have hna2_eq : ks2_0.nassump = ks0.nassump := hpres.2.2.2.2.1.trans hbtp.nassump
          have hass2_eq : ks2_0.assump = ks0.assump := hpres.2.2.2.2.2.1.trans hbtp.assump
          have hnv2 : ks2_0.nv.toNat ≤ k5MaxV := hinv2.clauses.nv_le
          have hnv21 : ks2_0.nv = ks1.nv := hpres.2.2.2.1
          have ha_lt2 : a.toNat < 2 * ks2_0.nv.toNat := by rw [hnv21]; exact ha_lt1
          have hb_lt2 : b.toNat < 2 * ks2_0.nv.toNat := by rw [hnv21]; exact hb_lt1
          have hcl_nc : k5ClauseLits ks2_0 ks1.nc.toNat = [a.toNat, b.toNat] := by
            have hoff : k5ClauseOff ks2_0 ks1.nc.toNat = ks1.alen.toNat := by
              unfold k5ClauseOff; dsimp only [ks2_0, k5WatchStep, k5WatchStep0, stM]; k5_field
              rw [List.getElem?_set_self (by rw [hinv1.shapes.clOff_len]; exact hnc_2048),
                Option.getD_some]
            have hsz : k5ClauseSize ks2_0 ks1.nc.toNat = 2 := by
              unfold k5ClauseSize; dsimp only [ks2_0, k5WatchStep, k5WatchStep0, stM]; k5_field
              rw [List.getElem?_set_self (by rw [hinv1.shapes.clSz_len]; exact hnc_2048),
                Option.getD_some]; rfl
            unfold k5ClauseLits; rw [hoff, hsz]
            have har_eq : ks2_0.arena =
                (ks1.arena.set ks1.alen.toNat a).set (ks1.alen.toNat + 1) b := by
              dsimp only [ks2_0, k5WatchStep, k5WatchStep0, stM]; k5_field
            rw [har_eq]
            exact k5_arena_take2 hinv1.shapes.arena_len hoff1_cap
          have hnc_lt2 : ks1.nc.toNat < ks2_0.nc.toNat := by
            have : ks2_0.nc = ks1.nc + 1#32 := by
              dsimp only [ks2_0, k5WatchStep, k5WatchStep0, stM]; k5_field
            rw [this]; bv_omega
          have hmA2 : (K512MemA (c.pScratchBuf + BitVec.ofNat 64 2304 * 4) acap ks2_0 ⋆ Rfr) m2 :=
            k5Mem_to_amem hinv2.shapes hm2
          clear hm2 hpres hnv21
          obtain ⟨ks2, hks2_def⟩ : ∃ x : K512State, x = ks2_0 := ⟨ks2_0, rfl⟩
          rw [← hks2_def] at hinv2 hsync2 hlvl2 hnv2_eq hna2_eq hass2_eq
          rw [← hks2_def] at hnv2 ha_lt2 hb_lt2 hcl_nc hnc_lt2 hmA2
          clear hks2_def ks2_0 hmM_eq hsh_stM stM
          c0_hsteps_nogrp
          refine LeanQbe.T.wp_unroll_group fun _ _ => ?_
          c0_hsplit
          · -- va == 2
            have hfals_a : ks2.vals[a.toNat]? = some 2#32 := by
              have hv_eq : ks2.vals[a.toNat]?.getD 0#32 = 2#32 := ‹_›
              rw [List.getElem?_eq_getElem (by rw [hinv2.shapes.vals_len]; exact ha_1024),
                Option.getD_some] at hv_eq
              rw [List.getElem?_eq_getElem (by rw [hinv2.shapes.vals_len]; exact ha_1024), hv_eq]
            obtain ⟨⟨ja, hja, hja_eq⟩, hent_na⟩ :=
              k5_falsified_lvl0_entails hinv2 hlvl2 ha_lt2 hfals_a
            refine LeanQbe.T.wp_unroll_group fun _ _ => ?_
            c0_hsplit
            · -- vb == 2 => incons = 1
              have hfals_b : ks2.vals[b.toNat]? = some 2#32 := by
                have hv_eq : ks2.vals[b.toNat]?.getD 0#32 = 2#32 := ‹_›
                rw [List.getElem?_eq_getElem (by rw [hinv2.shapes.vals_len]; exact hb_1024),
                  Option.getD_some] at hv_eq
                rw [List.getElem?_eq_getElem (by rw [hinv2.shapes.vals_len]; exact hb_1024), hv_eq]
              have hent_nb := (k5_falsified_lvl0_entails hinv2 hlvl2 hb_lt2 hfals_b).2
              have hunsat : ∀ β, ¬ P β := SemEntails.unsat_of_falsified hent_ab fun x hx => by
                simp at hx; rcases hx with rfl | rfl
                · exact hent_na
                · exact hent_nb
              c0_hsteps!
              have hinv3 := k5SetIncons_preserves_inv hinv2 hunsat
              exact finishR hinv3 hsync2 (by k5_field; exact hnv2_eq) (by k5_field; exact hna2_eq)
                (by k5_field; exact hass2_eq) (k5MemA_to_mem hm).2
            · refine LeanQbe.T.wp_unroll_group fun _ _ => ?_
              c0_hsplit
              · -- vb == 0 => assign(k, b, nc)
                have hun_b : ks2.vals[b.toNat]? = some 0#32 := by
                  have hv_eq : ks2.vals[b.toNat]?.getD 0#32 = 0#32 := ‹_›
                  rw [List.getElem?_eq_getElem (by rw [hinv2.shapes.vals_len]; exact hb_1024),
                    Option.getD_some] at hv_eq
                  rw [List.getElem?_eq_getElem (by rw [hinv2.shapes.vals_len]; exact hb_1024),
                    hv_eq]
                have hte_lt := k5_trl_end_lt_of_unassigned hinv2.shapes hnv2 hinv2.assign hb_lt2
                  (by simp [hun_b])
                have hent_b : SemEntails P [b.toNat] :=
                  SemEntails.unit_of_falsified hent_ab fun x hx hne => by
                    simp at hx; rcases hx with rfl | rfl
                    · exact hent_na
                    · exact absurd rfl hne
                obtain ⟨hinv3, hsync3⟩ := k5AssignStep_preserves_inv hinv2 hsync2 hb_lt2 hun_b
                  (fun _ => hent_b) (fun hpos => by rw [hlvl2] at hpos; simp at hpos)
                  (Or.inr ⟨hnc_lt2, by rw [hcl_nc]; simp, fun x hx hne => by
                    rw [hcl_nc] at hx; simp at hx; rcases hx with rfl | rfl
                    · exact ⟨ja, hja, hja_eq⟩
                    · exact absurd rfl hne⟩)
                c0_call hAssign
                refine ⟨acap, ks2, Rfr, hinv2.shapes, hacap_lt, hnv2, hb_lt2,
                  hte_lt, (k5MemA_to_mem hmA2).2, fun m3 hm3 => ?_⟩
                c0_hsteps!
                exact finishR hinv3 hsync3 hnv2_eq hna2_eq hass2_eq hm3
              · c0_hsteps!
                exact finishR hinv2 hsync2 hnv2_eq hna2_eq hass2_eq (k5MemA_to_mem hmA2).2
          · refine LeanQbe.T.wp_unroll_group fun _ _ => ?_
            c0_hsplit
            · c0_hsplit
              · -- va != 2, vb == 2, va == 0 => assign(k, a, nc)
                have hfals_b : ks2.vals[b.toNat]? = some 2#32 := by
                  have hv_eq : ks2.vals[b.toNat]?.getD 0#32 = 2#32 := ‹_›
                  rw [List.getElem?_eq_getElem (by rw [hinv2.shapes.vals_len]; exact hb_1024),
                    Option.getD_some] at hv_eq
                  rw [List.getElem?_eq_getElem (by rw [hinv2.shapes.vals_len]; exact hb_1024),
                    hv_eq]
                have hun_a : ks2.vals[a.toNat]? = some 0#32 := by
                  have hv_eq : ks2.vals[a.toNat]?.getD 0#32 = 0#32 := ‹_›
                  rw [List.getElem?_eq_getElem (by rw [hinv2.shapes.vals_len]; exact ha_1024),
                    Option.getD_some] at hv_eq
                  rw [List.getElem?_eq_getElem (by rw [hinv2.shapes.vals_len]; exact ha_1024),
                    hv_eq]
                obtain ⟨⟨jb, hjb, hjb_eq⟩, hent_nb⟩ :=
                  k5_falsified_lvl0_entails hinv2 hlvl2 hb_lt2 hfals_b
                have hte_lt := k5_trl_end_lt_of_unassigned hinv2.shapes hnv2 hinv2.assign ha_lt2
                  (by simp [hun_a])
                have hent_a : SemEntails P [a.toNat] :=
                  SemEntails.unit_of_falsified hent_ab fun x hx hne => by
                    simp at hx; rcases hx with rfl | rfl
                    · exact absurd rfl hne
                    · exact hent_nb
                obtain ⟨hinv3, hsync3⟩ := k5AssignStep_preserves_inv hinv2 hsync2 ha_lt2 hun_a
                  (fun _ => hent_a) (fun hpos => by rw [hlvl2] at hpos; simp at hpos)
                  (Or.inr ⟨hnc_lt2, by rw [hcl_nc]; simp, fun x hx hne => by
                    rw [hcl_nc] at hx; simp at hx; rcases hx with rfl | rfl
                    · exact absurd rfl hne
                    · exact ⟨jb, hjb, hjb_eq⟩⟩)
                c0_call hAssign
                refine ⟨acap, ks2, Rfr, hinv2.shapes, hacap_lt, hnv2, ha_lt2,
                  hte_lt, (k5MemA_to_mem hmA2).2, fun m3 hm3 => ?_⟩
                c0_hsteps!
                exact finishR hinv3 hsync3 hnv2_eq hna2_eq hass2_eq hm3
              · c0_hsteps!
                exact finishR hinv2 hsync2 hnv2_eq hna2_eq hass2_eq (k5MemA_to_mem hmA2).2
            · c0_hsteps!
              exact finishR hinv2 hsync2 hnv2_eq hna2_eq hass2_eq (k5MemA_to_mem hmA2).2

end LeanQbe.T.Examples.Kissat.FullM4Sweep
