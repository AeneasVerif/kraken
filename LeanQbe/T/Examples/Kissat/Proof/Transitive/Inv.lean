/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena1
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts
public import LeanQbe.T.Examples.Kissat.Proof.Spec.MemBridges
public import LeanQbe.T.Examples.Kissat.Proof.Spec.WitnessInv
public import LeanQbe.T.Examples.Kissat.Proof.Spec.WitnessInv1

/-!
# Transitive Reduction Outer & Compaction Invariants (`Proof.Transitive.Inv`)

Pure watch-slice tombstone, outer scan, and compaction invariants for `Src.Transitive`:
1. Binary entailment helpers (`sat_pair_elim`, `entails_pair_taut`, `entails_pair_trans`,
   `entails_unit_resolve_pair`, `entails_pair_collapse`, `getD_set2_ne`, `var_ne_xor_pair`).
2. `watchSlice_inv_bin`, `watchSlice_inv_large`, `watchSlice_append`, `TombWatchSliceOk`, and
   watch-slice relocation lemmas (`WatchSliceOk.relocate_same`, `DenseWatchSliceOk.relocate_same`).
3. `TransOuterBase`, `TransOuterInv`, and `TransCompactInv` with step/exit lemmas.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Transitive

open Std Std.Sat
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec

/-! ## 1. Pure Entailment & BitVec Helpers -/

theorem sat_pair_elim {α : Nat → Bool} {a b : Nat} (h : (cnfClause [a, b]).Sat α) :
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

theorem getD_set2_ne {α : Type} {xs : List α} {a b i : Nat} {x y d : α}
    (ha : i ≠ a) (hb : i ≠ b) : ((xs.set a x).set b y)[i]?.getD d = xs[i]?.getD d := by
  rw [List.getElem?_set_ne hb.symm, List.getElem?_set_ne ha.symm]

theorem var_ne_xor_pair {x y : Nat} (h : x / 2 ≠ y / 2) :
    x ≠ y ∧ x ≠ y ^^^ 1 ∧ x ^^^ 1 ≠ y ∧ x ^^^ 1 ≠ y ^^^ 1 :=
  ⟨fun e => h (by rw [e]), fun e => h (by rw [e, fullInv_var_xor1]),
   fun e => h (by rw [← e, fullInv_var_xor1]),
   fun e => h (by have := congrArg (· / 2) e; simpa only [fullInv_var_xor1] using this)⟩

theorem tr_tomb_mask7f : (0xFFFFFFFF#32 &&& 0x7FFFFFFF#32).toNat = 0x7FFFFFFF := by decide

theorem tr_tomb_bin_flag : (0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32 := by decide

/-! ## 2. Watch-Slice & Tombstone Invariants -/

theorem watchSlice_inv_bin {F_cur : List (List Nat)} {k : FullCoreState} {lit p len : Nat}
    {w0 : BitVec 32} (h : WatchSliceOk F_cur k lit p len) (hlen : 0 < len)
    (hget : k.wstk[p]? = some w0) (hflag : (w0 &&& 0x80000000#32) ≠ 0#32) :
    w0 ≠ 0xFFFFFFFF#32 ∧ (w0 &&& 0x7FFFFFFF#32).toNat < 2 * k.cur_vars ∧
    (cnfOfClauses F_cur).EntailsClause (cnfClause [lit, (w0 &&& 0x7FFFFFFF#32).toNat]) ∧
    WatchSliceOk F_cur k lit (p + 1) (len - 1) := by
  cases h with
  | empty => omega
  | bin h0 _ hne hlt hent hrest =>
    have hw := Option.some.inj (h0.symm.trans hget); subst hw
    exact ⟨hne, hlt, hent, by simpa using hrest⟩
  | large h0 _ hf _ _ _ =>
    have hw := Option.some.inj (h0.symm.trans hget); subst hw; exact absurd hf hflag

theorem watchSlice_inv_large {F_cur : List (List Nat)} {k : FullCoreState} {lit p len : Nat}
    {w0 : BitVec 32} (h : WatchSliceOk F_cur k lit p len) (hlen : 0 < len)
    (hget : k.wstk[p]? = some w0) (hflag : (w0 &&& 0x80000000#32) = 0#32) :
    2 ≤ len ∧ ∃ cref : BitVec 32, k.wstk[p + 1]? = some cref ∧
      cref.toNat < 0x80000000 ∧ cref.toNat ∈ fullArenaClauseRefsCore k ∧
      WatchSliceOk F_cur k lit (p + 2) (len - 2) := by
  cases h with
  | empty => omega
  | bin h0 hf _ _ _ =>
    have hw := Option.some.inj (h0.symm.trans hget); subst hw; exact absurd hflag hf
  | large h0 h1 _ hlt href hrest => exact ⟨by omega, _, h1, hlt, href, by simpa using hrest⟩

theorem watchSlice_append {F_cur : List (List Nat)} {k : FullCoreState} {lit p len1 len2 : Nat}
    (h1 : WatchSliceOk F_cur k lit p len1) (h2 : WatchSliceOk F_cur k lit (p + len1) len2) :
    WatchSliceOk F_cur k lit p (len1 + len2) := by
  induction h1 with
  | empty => simpa using h2
  | @bin p rem w0 h0 hf hn hl he _ ih =>
    rw [show p + (rem + 1) = (p + 1) + rem by omega] at h2
    rw [show rem + 1 + len2 = (rem + len2) + 1 by omega]; exact .bin h0 hf hn hl he (ih h2)
  | @large p rem w0 cr h0 h1 hf hl hr _ ih =>
    rw [show p + (rem + 2) = (p + 2) + rem by omega] at h2
    rw [show rem + 2 + len2 = (rem + len2) + 2 by omega]; exact .large h0 h1 hf hl hr (ih h2)

/-- Watch slice permitting `nt` tombstones (`0xFFFFFFFF#32`) interspersed among valid entries. -/
inductive TombWatchSliceOk (F_cur : List (List Nat)) (k : FullCoreState) (lit : Nat) :
    Nat → Nat → Nat → Prop where
  | empty {p} : TombWatchSliceOk F_cur k lit p 0 0
  | tomb {p rem nt} : k.wstk[p]? = some 0xFFFFFFFF#32 →
      TombWatchSliceOk F_cur k lit (p + 1) rem nt →
      TombWatchSliceOk F_cur k lit p (rem + 1) (nt + 1)
  | bin {p rem nt w0} : k.wstk[p]? = some w0 → (w0 &&& 0x80000000#32) ≠ 0#32 →
      w0 ≠ 0xFFFFFFFF#32 → (w0 &&& 0x7FFFFFFF#32).toNat < 2 * k.cur_vars →
      (cnfOfClauses F_cur).EntailsClause (cnfClause [lit, (w0 &&& 0x7FFFFFFF#32).toNat]) →
      TombWatchSliceOk F_cur k lit (p + 1) rem nt → TombWatchSliceOk F_cur k lit p (rem + 1) nt
  | large {p rem nt w0 cref} : k.wstk[p]? = some w0 → k.wstk[p + 1]? = some cref →
      (w0 &&& 0x80000000#32) = 0#32 → cref.toNat < 0x80000000 →
      cref.toNat ∈ fullArenaClauseRefsCore k →
      TombWatchSliceOk F_cur k lit (p + 2) rem nt → TombWatchSliceOk F_cur k lit p (rem + 2) nt

theorem TombWatchSliceOk.of_watchSlice {F_cur : List (List Nat)} {k : FullCoreState}
    {lit p rem : Nat} (h : WatchSliceOk F_cur k lit p rem) :
    TombWatchSliceOk F_cur k lit p rem 0 := by
  induction h with
  | empty => exact .empty
  | bin a b c d e _ ih => exact .bin a b c d e ih
  | large a b c d e _ ih => exact .large a b c d e ih

theorem TombWatchSliceOk.to_watchSlice {F_cur : List (List Nat)} {k : FullCoreState}
    {lit p rem : Nat} (h : TombWatchSliceOk F_cur k lit p rem 0) :
    WatchSliceOk F_cur k lit p rem := by
  generalize hnt : (0 : Nat) = nt at h
  induction h with
  | empty => exact .empty
  | tomb _ _ => omega
  | bin a b c d e _ ih => exact .bin a b c d e (ih hnt)
  | large a b c d e _ ih => exact .large a b c d e (ih hnt)

theorem TombWatchSliceOk.mono {F_cur : List (List Nat)} {k k' : FullCoreState}
    {lit p rem nt : Nat} (hvars : k.cur_vars ≤ k'.cur_vars)
    (hsub : ∀ r ∈ fullArenaClauseRefsCore k, r ∈ fullArenaClauseRefsCore k')
    (hwstk : ∀ idx, p ≤ idx → idx < p + rem → k'.wstk[idx]? = k.wstk[idx]?)
    (h : TombWatchSliceOk F_cur k lit p rem nt) : TombWatchSliceOk F_cur k' lit p rem nt := by
  induction h with
  | empty => exact .empty
  | @tomb p rem nt hp _ ih =>
    exact .tomb (by rw [hwstk p (by omega) (by omega), hp])
      (ih fun _ _ _ => hwstk _ (by omega) (by omega))
  | @bin p rem nt w0 hp hf hn hl he _ ih =>
    exact .bin (by rw [hwstk p (by omega) (by omega), hp]) hf hn (by omega) he
      (ih fun _ _ _ => hwstk _ (by omega) (by omega))
  | @large p rem nt w0 cref hp hp1 hf hl hr _ ih =>
    exact .large (by rw [hwstk p (by omega) (by omega), hp])
      (by rw [hwstk (p + 1) (by omega) (by omega), hp1]) hf hl (hsub _ hr)
      (ih fun _ _ _ => hwstk _ (by omega) (by omega))

theorem TombWatchSliceOk.append {F_cur : List (List Nat)} {k : FullCoreState}
    {lit p len1 len2 nt1 nt2 : Nat} (h1 : TombWatchSliceOk F_cur k lit p len1 nt1)
    (h2 : TombWatchSliceOk F_cur k lit (p + len1) len2 nt2) :
    TombWatchSliceOk F_cur k lit p (len1 + len2) (nt1 + nt2) := by
  induction h1 with
  | empty => simpa using h2
  | @tomb p rem nt hp _ ih =>
    rw [show p + (rem + 1) = (p + 1) + rem by omega] at h2
    rw [show rem + 1 + len2 = (rem + len2) + 1 by omega]
    rw [show nt + 1 + nt2 = (nt + nt2) + 1 by omega]; exact .tomb hp (ih h2)
  | @bin p rem nt w0 hp hf hn hl he _ ih =>
    rw [show p + (rem + 1) = (p + 1) + rem by omega] at h2
    rw [show rem + 1 + len2 = (rem + len2) + 1 by omega]; exact .bin hp hf hn hl he (ih h2)
  | @large p rem nt w0 cr hp hp1 hf hl hr _ ih =>
    rw [show p + (rem + 2) = (p + 2) + rem by omega] at h2
    rw [show rem + 2 + len2 = (rem + len2) + 2 by omega]; exact .large hp hp1 hf hl hr (ih h2)

theorem TombWatchSliceOk.nt_le_rem {F_cur : List (List Nat)} {k : FullCoreState}
    {lit p rem nt : Nat} (h : TombWatchSliceOk F_cur k lit p rem nt) : nt ≤ rem := by
  induction h <;> omega

theorem TombWatchSliceOk.eq_zero_of_rem0 {F_cur : List (List Nat)} {k : FullCoreState}
    {lit p nt : Nat} (h : TombWatchSliceOk F_cur k lit p 0 nt) : nt = 0 := by
  have := h.nt_le_rem; omega

theorem TombWatchSliceOk.inv_step {F_cur : List (List Nat)} {k : FullCoreState}
    {lit p len nt : Nat} {w0 : BitVec 32} (h : TombWatchSliceOk F_cur k lit p len nt)
    (hlen : 0 < len) (hget : k.wstk[p]? = some w0) :
    if (w0 &&& 0x80000000#32) = 0#32 then
      2 ≤ len ∧ ∃ cref : BitVec 32, k.wstk[p + 1]? = some cref ∧
        cref.toNat < 0x80000000 ∧ cref.toNat ∈ fullArenaClauseRefsCore k ∧
        TombWatchSliceOk F_cur k lit (p + 2) (len - 2) nt
    else if w0 = 0xFFFFFFFF#32 then
      1 ≤ nt ∧ TombWatchSliceOk F_cur k lit (p + 1) (len - 1) (nt - 1)
    else (w0 &&& 0x7FFFFFFF#32).toNat < 2 * k.cur_vars ∧
      (cnfOfClauses F_cur).EntailsClause (cnfClause [lit, (w0 &&& 0x7FFFFFFF#32).toNat]) ∧
      TombWatchSliceOk F_cur k lit (p + 1) (len - 1) nt := by
  cases h with
  | empty => omega
  | tomb hp hrest =>
    have hw := Option.some.inj (hp.symm.trans hget); subst hw
    simp only [tr_tomb_bin_flag, ↓reduceIte]; exact ⟨by omega, by simpa using hrest⟩
  | bin hp hf hn hl he hrest =>
    have hw := Option.some.inj (hp.symm.trans hget); subst hw
    simp only [hf, ↓reduceIte, hn]; exact ⟨hl, he, by simpa using hrest⟩
  | large hp hp1 hf hl hr hrest =>
    have hw := Option.some.inj (hp.symm.trans hget); subst hw
    simp only [hf, ↓reduceIte]; exact ⟨by omega, _, hp1, hl, hr, by simpa using hrest⟩

theorem TombWatchSliceOk.step_non_large {F_cur : List (List Nat)} {k : FullCoreState}
    {nl q lend nt : Nat} {qw : BitVec 32} (hq : q < lend) (hg : k.wstk[q]? = some qw)
    (hfl : (qw &&& 0x80000000#32) ≠ 0#32) (ht : TombWatchSliceOk F_cur k nl q (lend - q) nt) :
    ∃ nt2, TombWatchSliceOk F_cur k nl (q + 1) (lend - (q + 1)) nt2 := by
  have hs := ht.inv_step (by omega) hg; simp only [hfl, ↓reduceIte] at hs
  by_cases hq_t : qw = 0xFFFFFFFF#32 <;> simp only [hq_t, ↓reduceIte] at hs
  · exact ⟨nt - 1, by have hs2 := hs.2; rwa [show lend - q - 1 = lend - (q + 1) by omega] at hs2⟩
  · exact ⟨nt, by have hs3 := hs.2.2; rwa [show lend - q - 1 = lend - (q + 1) by omega] at hs3⟩

theorem WatchSliceOk.relocate_same {F_cur : List (List Nat)} {k k' : FullCoreState}
    {lit p p' rem : Nat} (hvars : k.cur_vars ≤ k'.cur_vars)
    (hsub : ∀ r ∈ fullArenaClauseRefsCore k, r ∈ fullArenaClauseRefsCore k')
    (hwstk : ∀ idx < rem, k'.wstk[p' + idx]? = k.wstk[p + idx]?)
    (h : WatchSliceOk F_cur k lit p rem) : WatchSliceOk F_cur k' lit p' rem := by
  induction h generalizing p' with
  | empty => exact .empty
  | @bin p rem w0 hp hf hn hl he _ ih =>
    exact .bin (by simpa using (hwstk 0 (by omega)).trans hp) hf hn (by omega) he
      (ih (p' := p' + 1) fun idx hi => by
        simpa [Nat.add_assoc] using hwstk (1 + idx) (by omega))
  | @large p rem w0 cr hp hp1 hf hl hr _ ih =>
    exact .large (by simpa using (hwstk 0 (by omega)).trans hp)
      (by simpa using (hwstk 1 (by omega)).trans hp1) hf hl (hsub _ hr)
      (ih (p' := p' + 2) fun idx hi => by
        simpa [Nat.add_assoc] using hwstk (2 + idx) (by omega))

theorem DenseWatchSliceOk.relocate_same {F_cur : List (List Nat)} {k k' : FullCoreState}
    {lit p p' rem : Nat} (hvars : k.cur_vars ≤ k'.cur_vars)
    (hsub : ∀ r ∈ fullArenaClauseRefsCore k, r ∈ fullArenaClauseRefsCore k')
    (hwstk : ∀ idx < rem, k'.wstk[p' + idx]? = k.wstk[p + idx]?)
    (h : DenseWatchSliceOk F_cur k lit p rem) : DenseWatchSliceOk F_cur k' lit p' rem := by
  induction h generalizing p' with
  | empty => exact .empty
  | @bin p rem w0 hp hf hn hl he _ ih =>
    exact .bin (by simpa using (hwstk 0 (by omega)).trans hp) hf hn (by omega) he
      (ih (p' := p' + 1) fun idx hi => by
        simpa [Nat.add_assoc] using hwstk (1 + idx) (by omega))
  | @occ p rem w0 cr hp hp1 hf hs1 hl hr _ ih =>
    exact .occ (by simpa using (hwstk 0 (by omega)).trans hp)
      (by simpa using (hwstk 1 (by omega)).trans hp1) hf hs1 hl (hsub _ hr)
      (ih (p' := p' + 2) fun idx hi => by
        simpa [Nat.add_assoc] using hwstk (2 + idx) (by omega))

/-! ## 3. Outer Scan & Compaction Invariants for `full_trans_lit_m6` -/

/-- Shared outer state & disjointness invariant of `full_trans_lit_m6` across scan & compaction. -/
structure TransOuterBase (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s0 : FullState) (src off end_v : Nat) (st : FullState) : Prop where
  len_ok : st.LengthsOk c
  core_pres : st.core.cur_vars = s0.core.cur_vars ∧ st.core.cur_level = 0 ∧
    s0.core.cur_level = 0 ∧ st.core.fuel = s0.core.fuel ∧ st.core.dense_mode = 0#64 ∧
    st.core.probing = s0.core.probing ∧ st.core.oom = s0.core.oom ∧
    st.core.inconsistent = s0.core.inconsistent ∧ st.core.arena = s0.core.arena ∧
    st.core.arena_len = s0.core.arena_len ∧ st.core.vals = s0.core.vals ∧
    st.core.lvl = s0.core.lvl ∧ st.core.rsns = s0.core.rsns ∧
    st.core.trail_pos = s0.core.trail_pos ∧ st.core.trail_end = s0.core.trail_end ∧
    (∀ i < s0.core.trail_end, st.core.trl[i]? = s0.core.trl[i]?) ∧ st.core.mrk = s0.core.mrk ∧
    st.core.lit_mark = s0.core.lit_mark ∧ st.core.flags = s0.core.flags ∧
    st.core.frame_trail = s0.core.frame_trail ∧ st.core.frame_dec = s0.core.frame_dec ∧
    st.core.wlen = s0.core.wlen
  scratch_pres : st.scratch.last_learned = s0.scratch.last_learned ∧
    st.scratch.extend_len = s0.scratch.extend_len
  off_le_end : off ≤ end_v
  src_off : fullWatchOffCore st.core src = off
  src_sz : fullWatchSizeCore st.core src = end_v - off
  end_le_wlen : end_v ≤ st.core.wlen
  off_pos : 1 ≤ off
  other_bounds : ∀ l < 2 * st.core.cur_vars, l ≠ src →
    fullWatchOffCore st.core l + fullWatchSizeCore st.core l ≤ st.core.wlen
  other_pos_off : ∀ l < 2 * st.core.cur_vars, l ≠ src →
    0 < fullWatchSizeCore st.core l → 1 ≤ fullWatchOffCore st.core l
  disjoint_all : ∀ l1 l2, l1 < 2 * st.core.cur_vars → l2 < 2 * st.core.cur_vars → l1 ≠ l2 →
    0 < fullWatchSizeCore st.core l1 → 0 < fullWatchSizeCore st.core l2 →
    fullWatchOffCore st.core l1 + fullWatchSizeCore st.core l1 ≤ fullWatchOffCore st.core l2 ∨
    fullWatchOffCore st.core l2 + fullWatchSizeCore st.core l2 ≤ fullWatchOffCore st.core l1
  other_no_sent : ∀ l < 2 * st.core.cur_vars, l ≠ src → ∀ idx < fullWatchSizeCore st.core l,
    st.core.wstk[fullWatchOffCore st.core l + idx]? ≠ some 0xFFFFFFFF#32
  other_slices : ∀ l < 2 * st.core.cur_vars, l ≠ src →
    WatchSliceOk F_cur st.core l (fullWatchOffCore st.core l) (fullWatchSizeCore st.core l)

/-- Outer scan invariant over `src`'s watch list `[off, p) ++ [p, end_v)`. -/
structure TransOuterInv (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s0 : FullState) (src off p end_v reduced : Nat) (st : FullState) : Prop where
  base : TransOuterBase c F0 F_cur s0 src off end_v st
  off_le_p : off ≤ p
  p_le_end : p ≤ end_v
  red_le : reduced ≤ p - off
  src_pref : TombWatchSliceOk F_cur st.core src off (p - off) reduced
  src_rem : WatchSliceOk F_cur st.core src p (end_v - p)

theorem TransOuterBase.frame_wstk {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 : FullState} {src off end_v : Nat} {st : FullState}
    (hb : TransOuterBase c F0 F_cur s0 src off end_v st) (hsrc_lt : src < 2 * st.core.cur_vars)
    {wstk' : List (BitVec 32)} {wu' tc' : BitVec 64} (hlen : wstk'.length = c.wcap)
    (hout : ∀ idx, (idx < off ∨ end_v ≤ idx) → wstk'[idx]? = st.core.wstk[idx]?) :
    TransOuterBase c F0 F_cur s0 src off end_v
      { st with core := { st.core with wstk := wstk', wusable := wu' }
                scratch := { st.scratch with trans_cnt := tc' } } := by
  have hdisj : ∀ l < 2 * st.core.cur_vars, l ≠ src → ∀ idx < fullWatchSizeCore st.core l,
      fullWatchOffCore st.core l + idx < off ∨ end_v ≤ fullWatchOffCore st.core l + idx := by
    intro l hl hls idx hidx; by_cases hoff_eq : off = end_v
    · subst hoff_eq; exact Nat.lt_or_ge _ _
    · have := hb.off_le_end
      rcases hb.disjoint_all src l hsrc_lt hl hls.symm (by rw [hb.src_sz]; omega) (by omega) with
        ha | hb2
      · rw [hb.src_off, hb.src_sz] at ha; right; omega
      · rw [hb.src_off] at hb2; left; omega
  exact { hb with
    len_ok := ⟨{ hb.len_ok.core_ok with wstk_len_arr := hlen },
      { hb.len_ok.scratch_ok with walk_vals_len := hb.len_ok.scratch_ok.walk_vals_len }⟩
    other_no_sent := fun l hl hls idx _ => by
      change wstk'[fullWatchOffCore st.core l + idx]? ≠ some 0xFFFFFFFF#32
      rw [hout _ (hdisj l hl hls idx ‹_›)]; exact hb.other_no_sent l hl hls idx ‹_›
    other_slices := fun l hl hls => WatchSliceOk.relocate_same (k := st.core)
      (k' := { st.core with wstk := wstk', wusable := wu' }) (Nat.le_refl _) (fun _ hr => hr)
      (fun idx hi => hout _ (hdisj l hl hls idx hi)) (hb.other_slices l hl hls) }

theorem TransOuterInv.src_full_tomb {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 : FullState} {src off p end_v reduced : Nat} {st : FullState}
    (h : TransOuterInv c F0 F_cur s0 src off p end_v reduced st) :
    TombWatchSliceOk F_cur st.core src off (end_v - off) reduced := by
  have h1 : off + (p - off) = p := by have := h.off_le_p; omega
  have h2 : p - off + (end_v - p) = end_v - off := by
    have := h.off_le_p; have := h.p_le_end; omega
  have hcomb := h.src_pref.append (by rw [h1]; exact TombWatchSliceOk.of_watchSlice h.src_rem)
  rwa [h2, Nat.add_zero] at hcomb

theorem TransOuterInv.init {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 : FullState} (hlen : s0.LengthsOk c) (hw : FullWitnessInv c F0 F_cur s0.core)
    (hdm : s0.core.dense_mode = 0#64) (hcl : s0.core.cur_level = 0)
    {src : Nat} (hsrc : src < 2 * s0.core.cur_vars) (hpos : 0 < fullWatchSizeCore s0.core src) :
    let off := fullWatchOffCore s0.core src
    TransOuterInv c F0 F_cur s0 src off off (off + fullWatchSizeCore s0.core src) 0 s0 := by
  have hwm : WatchesInv F_cur s0.core := by
    have hm := hw.watches; unfold ModeWatchesInv at hm; simp only [hdm, ↓reduceIte] at hm; exact hm
  exact {
    base :=
      { len_ok := hlen, scratch_pres := ⟨rfl, rfl⟩, off_le_end := by omega
        core_pres := ⟨rfl, hcl, hcl, rfl, hdm, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
          fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        src_off := rfl, src_sz := by omega, end_le_wlen := hwm.layout.bounds src hsrc
        off_pos := hwm.layout.pos_off src hsrc hpos
        other_bounds := fun l hl _ => hwm.layout.bounds l hl
        other_pos_off := fun l hl _ hp => hwm.layout.pos_off l hl hp
        disjoint_all := hwm.layout.disjoint
        other_no_sent := fun l hl _ => hwm.layout.no_sentinel l hl
        other_slices := fun l hl _ => hwm.slices l hl }
    off_le_p := Nat.le_refl _, p_le_end := by omega, red_le := by simp
    src_pref := by simp only [Nat.sub_self]; exact .empty
    src_rem := by simpa only [Nat.add_sub_cancel_left] using hwm.slices src hsrc }

theorem TransOuterBase.toWitness_of_src_clean {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s0 : FullState} {src off end_v : Nat} {st : FullState}
    (hw0 : FullWitnessInv c F0 F_cur s0.core) (hb : TransOuterBase c F0 F_cur s0 src off end_v st)
    (hclean : WatchSliceOk F_cur st.core src
      (fullWatchOffCore st.core src) (fullWatchSizeCore st.core src)) :
    FullWitnessInv c F0 F_cur st.core := by
  obtain ⟨hcv, hcl0, hs0cl0, _, hdm, _, _, hinc, har, hal, hvals, hlvl, hrsn, htp, hte, htrl, _, _,
    _, hft, hfd, _⟩ := hb.core_pres
  have hrefs : fullArenaClauseRefsCore st.core = fullArenaClauseRefsCore s0.core := by
    unfold fullArenaClauseRefsCore; rw [har, hal]
  have hgarb : ∀ r, fullArenaClauseGarbCore st.core r = fullArenaClauseGarbCore s0.core r :=
    fun r => by unfold fullArenaClauseGarbCore fullArenaHdrCore; rw [har]
  have hlits : ∀ r, fullArenaClauseLitsCore st.core r = fullArenaClauseLitsCore s0.core r :=
    fun r => by unfold fullArenaClauseLitsCore fullArenaClauseSizeCore; rw [har]
  have hsz_core : ∀ r, fullArenaClauseSizeCore st.core r = fullArenaClauseSizeCore s0.core r :=
    fun r => by unfold fullArenaClauseSizeCore; rw [har]
  have hlay : WatchStackLayout st.core :=
    { bounds := fun l hl => by
        by_cases hls : l = src
        · subst hls; have := hb.off_le_end; rw [hb.src_off, hb.src_sz]
          exact Nat.le_trans (by omega) hb.end_le_wlen
        · exact hb.other_bounds l hl hls
      pos_off := fun l hl hp =>
        if hls : l = src then by subst hls; rw [hb.src_off]; exact hb.off_pos
        else hb.other_pos_off l hl hls hp
      disjoint := hb.disjoint_all
      no_sentinel := fun l hl =>
        if hls : l = src then hls ▸ hclean.ne_sentinel else hb.other_no_sent l hl hls }
  have hwat : ModeWatchesInv F_cur st.core := by
    unfold ModeWatchesInv; simp only [hdm, ↓reduceIte]
    exact ⟨hlay, fun l hl => if hls : l = src then hls ▸ hclean else hb.other_slices l hl hls⟩
  have htrl_d : ∀ i < st.core.trail_end,
      (st.core.trl[i]?.getD 0#32).toNat = (s0.core.trl[i]?.getD 0#32).toNat :=
    fun i hi => by rw [htrl i (hte ▸ hi)]
  have hvals_d : ∀ l : Nat, st.core.vals[l]?.getD 0#8 = s0.core.vals[l]?.getD 0#8 :=
    fun l => by rw [hvals]
  have hlvl_d : ∀ v : Nat,
      (st.core.lvl[v]?.getD 0#32).toNat = (s0.core.lvl[v]?.getD 0#32).toNat :=
    fun v => by rw [hlvl]
  have hrsn_d : ∀ v : Nat, st.core.rsns[v]?.getD 0xFFFFFFFF#32 =
      s0.core.rsns[v]?.getD 0xFFFFFFFF#32 := fun v => by rw [hrsn]
  refine
    { ext_sound := hcv ▸ hw0.ext_sound, watches := hwat
      inconsistent_sound := fun hi => hw0.inconsistent_sound (hinc ▸ hi)
      arena :=
        { len_ok := hal ▸ hw0.arena.len_ok
          refs_wf := fun r hr => by
            rw [hrefs] at hr; rw [hal, har, hsz_core r]; exact hw0.arena.refs_wf r hr
          shrk_term := fun r hr hsh => by
            rw [hrefs] at hr; obtain ⟨t, ht1, ht2, hsent⟩ := hw0.arena.shrk_term r hr
              (by unfold fullArenaHdrCore at hsh ⊢; rwa [har] at hsh)
            exact ⟨t, by rw [hsz_core r]; exact ht1, by rw [hal]; exact ht2,
              by rw [har]; exact hsent⟩
          lits_lt := fun r hr hg l hl => by
            rw [hrefs] at hr; rw [hgarb r] at hg; rw [hlits r] at hl
            exact hcv ▸ hw0.arena.lits_lt r hr hg l hl
          entails := fun r hr hg => by
            rw [hrefs] at hr; rw [hgarb r] at hg; rw [hlits r]; exact hw0.arena.entails r hr hg }
      cur_level_le := by rw [hcl0]; exact Nat.zero_le _
      trail_lits_lt := fun i hi => by
        rw [hcv, htrl_d i hi]; exact hw0.trail_lits_lt i (hte ▸ hi)
      trail_vars_nodup := fun i j hi hj he => by
        rw [htrl_d i hi, htrl_d j hj] at he
        exact hw0.trail_vars_nodup i j (hte ▸ hi) (hte ▸ hj) he
      vals_domain := fun l hl => by rw [hvals_d l]; exact hw0.vals_domain l (hcv ▸ hl)
      vals_true_iff := fun l hl => by
        rw [hvals_d l, hte]; constructor
        · rintro h1; obtain ⟨i, hi, he⟩ := (hw0.vals_true_iff l (hcv ▸ hl)).mp h1
          exact ⟨i, hi, by rw [htrl_d i (hte ▸ hi), he]⟩
        · rintro ⟨i, hi, he⟩; rw [htrl_d i (hte ▸ hi)] at he
          exact (hw0.vals_true_iff l (hcv ▸ hl)).mpr ⟨i, hi, he⟩
      vals_false_iff := fun l hl => by
        rw [hvals_d l, hte]; constructor
        · rintro h1; obtain ⟨i, hi, he⟩ := (hw0.vals_false_iff l (hcv ▸ hl)).mp h1
          exact ⟨i, hi, by rw [htrl_d i (hte ▸ hi), he]⟩
        · rintro ⟨i, hi, he⟩; rw [htrl_d i (hte ▸ hi)] at he
          exact (hw0.vals_false_iff l (hcv ▸ hl)).mpr ⟨i, hi, he⟩
      lvl_le := fun i hi => by
        rw [hcl0, htrl_d i hi, hlvl_d]; have := hw0.lvl_le i (hte ▸ hi); omega
      dec_earliest := fun i j hi hj hleq hdec => by
        rw [htrl_d i hi, htrl_d j hj, hlvl_d, hlvl_d] at hleq
        rw [htrl_d j hj, hlvl_d, hrsn_d] at hdec
        exact hw0.dec_earliest i j (hte ▸ hi) (hte ▸ hj) hleq hdec
      levels_inhabited := fun L h1 h2 => by omega
      level0_sound := fun i hi hl0 => by
        rw [htrl_d i hi, hlvl_d] at hl0; rw [htrl_d i hi]
        exact hw0.level0_sound i (hte ▸ hi) hl0
      trail_pos_inv := fun i hi => by
        rw [htp, htrl_d i hi]; exact hw0.trail_pos_inv i (hte ▸ hi)
      level0_rsn_none := fun idx hidx hl0 => by
        rw [htrl_d idx hidx, hlvl_d] at hl0; rw [htrl_d idx hidx, hrsn_d]
        exact hw0.level0_rsn_none idx (hte ▸ hidx) hl0
      frame_trail_lt := fun L hL => by
        rw [hcl0] at hL; rw [hft, hte]; exact hw0.frame_trail_lt L (by omega)
      frame_trail_mono := fun L1 L2 h1 h2 => by
        rw [hcl0] at h2; rw [hft]; exact hw0.frame_trail_mono L1 L2 h1 (by omega)
      frame_trail_before_lt := fun L h1 h2 => by rw [hcl0] at h2; omega
      frame_dec_lt := fun L h1 h2 => by rw [hcl0] at h2; omega
      reason_inv := fun idx hidx hne => by
        rw [htrl_d idx hidx, hrsn_d] at hne ⊢
        have hl0 : (s0.core.lvl[(s0.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 :=
          by have := hw0.lvl_le idx (hte ▸ hidx); omega
        exact absurd (hw0.level0_rsn_none idx (hte ▸ hidx) hl0) hne
      reason_lit_mem := fun idx hidx hne _ => by
        rw [htrl_d idx hidx, hrsn_d] at hne
        have hl0 : (s0.core.lvl[(s0.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 :=
          by have := hw0.lvl_le idx (hte ▸ hidx); omega
        exact absurd (hw0.level0_rsn_none idx (hte ▸ hidx) hl0) hne }

theorem TransOuterBase.toSparse {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 : FullState} {src off end_v : Nat} {st : FullState}
    (hsp0 : FullSparseInv c F0 s0) (hw0 : FullWitnessInv c F0 F_cur s0.core)
    (hb : TransOuterBase c F0 F_cur s0 src off end_v st)
    (hclean : WatchSliceOk F_cur st.core src
      (fullWatchOffCore st.core src) (fullWatchSizeCore st.core src)) : FullSparseInv c F0 st := by
  have hw' := hb.toWitness_of_src_clean hw0 hclean
  obtain ⟨_, _, _, _, hdm, _, _, _, har, hal, _, _, _, _, _, _, hmrk, hlm, _, _, _, _⟩ :=
    hb.core_pres
  obtain ⟨hll, hel⟩ := hb.scratch_pres
  refine ⟨⟨hb.len_ok, F_cur, hw'⟩, ⟨fun v hv => hmrk ▸ hsp0.2.1.1 v hv,
    fun l hl => hlm ▸ hsp0.2.1.2 l hl⟩, ?_, ⟨?_, hel ▸ hsp0.2.2.2.1.2⟩, hdm⟩
  · intro r hr hng
    unfold fullArenaClauseRefs fullArenaClauseRefsCore at hr
    unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore at hng
    unfold fullArenaClauseLits fullArenaClauseLitsCore fullArenaClauseSizeCore
    rw [har, hal] at hr; rw [har] at hng ⊢; exact hsp0.2.2.1 r hr hng
  · intro i hi; dsimp only; unfold fullArenaClauseRefs fullArenaClauseRefsCore
    rw [hll, har, hal]; exact hsp0.2.2.2.1.1 i hi

theorem TransOuterInv.of_delete_bin_side {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 : FullState} {src off p end_v reduced dst : Nat} {st st' : FullState}
    (h : TransOuterInv c F0 F_cur s0 src off p end_v reduced st)
    (hsrc_lt : src < 2 * st.core.cur_vars) (hdst_lt : dst < 2 * st.core.cur_vars)
    (hdst_ne : dst ≠ src) (hst'_eq : st' = { st with core :=
      { st.core with wvec := st'.core.wvec, wstk := st'.core.wstk, wusable := st'.core.wusable } })
    (hlen' : st'.LengthsOk c) (hdst_ws : fullWatchOff st' dst = fullWatchOff st dst ∧
      fullWatchSize st' dst ≤ fullWatchSize st dst)
    (hother_ws : ∀ l < 2 * st.core.cur_vars, l ≠ dst →
      fullWatchOff st' l = fullWatchOff st l ∧ fullWatchSize st' l = fullWatchSize st l)
    (hwstk_out : ∀ idx < c.wcap,
      (idx < fullWatchOff st dst ∨ fullWatchOff st dst + fullWatchSize st dst ≤ idx) →
      st'.core.wstk[idx]? = st.core.wstk[idx]?)
    (hdst_slice : WatchSliceOk F_cur st.core dst (fullWatchOff st dst) (fullWatchSize st dst) →
      WatchSliceOk F_cur st'.core dst (fullWatchOff st' dst) (fullWatchSize st' dst)) :
    TransOuterInv c F0 F_cur s0 src off p end_v reduced st' := by
  dsimp only [fullWatchOff, fullWatchSize] at hdst_ws hother_ws hwstk_out hdst_slice
  have hb := h.base; have hcp := hb.core_pres
  have har' : st'.core.arena = st.core.arena := by rw [hst'_eq]
  have hal' : st'.core.arena_len = st.core.arena_len := by rw [hst'_eq]
  have hcv' : st'.core.cur_vars = st.core.cur_vars := by rw [hst'_eq]
  have hwlen' : st'.core.wlen = st.core.wlen := by rw [hst'_eq]
  have hrefs : ∀ r ∈ fullArenaClauseRefsCore st.core, r ∈ fullArenaClauseRefsCore st'.core :=
    fun r hr => by unfold fullArenaClauseRefsCore at hr ⊢; rwa [har', hal']
  have hws : ∀ l < 2 * st.core.cur_vars, fullWatchOffCore st'.core l = fullWatchOffCore st.core l ∧
      fullWatchSizeCore st'.core l ≤ fullWatchSizeCore st.core l := fun l hl => by
    by_cases hld : l = dst; · exact hld ▸ hdst_ws
    · exact ⟨(hother_ws l hl hld).1, by rw [(hother_ws l hl hld).2]; exact Nat.le_refl _⟩
  have hout_range : ∀ a b, b ≤ st.core.wlen → (fullWatchSizeCore st.core dst = 0 ∨
      b ≤ fullWatchOffCore st.core dst ∨
      fullWatchOffCore st.core dst + fullWatchSizeCore st.core dst ≤ a) →
      ∀ idx, a ≤ idx → idx < b → st'.core.wstk[idx]? = st.core.wstk[idx]? := by
    intro a b hb2 hdis idx ha1 ha2; have hcap := hb.len_ok.core_ok.wlen_le
    apply hwstk_out idx (by omega)
    rcases hdis with h0 | hlt | hgt
    · rw [h0]; rcases Nat.lt_or_ge idx (fullWatchOffCore st.core dst) with hlt | hge
      · exact Or.inl hlt
      · exact Or.inr (by omega)
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  have hsrc_ws := hother_ws src hsrc_lt hdst_ne.symm
  have hsrc_wstk : ∀ idx, off ≤ idx → idx < end_v → st'.core.wstk[idx]? = st.core.wstk[idx]? := by
    by_cases hoff_end : off = end_v
    · intro idx ha hb2; omega
    · have hlt : off < end_v := by have := hb.off_le_end; omega
      refine hout_range off end_v hb.end_le_wlen (by
        by_cases hdz : fullWatchSizeCore st.core dst = 0
        · exact Or.inl hdz
        · have hds := hb.disjoint_all src dst hsrc_lt hdst_lt hdst_ne.symm
            (by rw [hb.src_sz]; omega) (Nat.pos_of_ne_zero hdz)
          rw [hb.src_off, hb.src_sz, show off + (end_v - off) = end_v by omega] at hds
          exact Or.inr hds)
  have hslice_dst := hdst_slice (hb.other_slices dst hdst_lt hdst_ne)
  have hother_sl : ∀ l < 2 * st'.core.cur_vars, l ≠ src → WatchSliceOk F_cur st'.core l
      (fullWatchOffCore st'.core l) (fullWatchSizeCore st'.core l) := by
    intro l hl hls; rw [hcv'] at hl
    by_cases hld : l = dst
    · subst hld; exact hslice_dst
    · have hlws := hother_ws l hl hld; rw [hlws.1, hlws.2]
      refine WatchSliceOk.relocate_same (hb.other_bounds l hl hls |> fun _ => by omega) hrefs
        (fun idx hidx =>
        hout_range (fullWatchOffCore st.core l)
          (fullWatchOffCore st.core l + fullWatchSizeCore st.core l) (hb.other_bounds l hl hls)
          (by
            by_cases hdz : fullWatchSizeCore st.core dst = 0
            · exact Or.inl hdz
            · exact Or.inr (hb.disjoint_all l dst hl hdst_lt hld (by omega)
                (Nat.pos_of_ne_zero hdz))) _ (by omega) (by omega))
        (hb.other_slices l hl hls)
  exact
    { base :=
        { len_ok := hlen', core_pres := by rw [hst'_eq]; simpa using hcp
          scratch_pres := by rw [hst'_eq]; exact hb.scratch_pres
          off_le_end := hb.off_le_end, src_off := hsrc_ws.1.trans hb.src_off
          src_sz := hsrc_ws.2.trans hb.src_sz, end_le_wlen := hwlen'.symm ▸ hb.end_le_wlen
          off_pos := hb.off_pos
          other_bounds := fun l hl hls => by
            rw [hcv'] at hl; rw [hwlen']; have hw := hws l hl
            exact Nat.le_trans (by omega) (hb.other_bounds l hl hls)
          other_pos_off := fun l hl hls hpos => by
            rw [hcv'] at hl; have hw := hws l hl; rw [hw.1]
            exact hb.other_pos_off l hl hls (by omega)
          disjoint_all := fun l1 l2 h1 h2 hne hp1 hp2 => by
            rw [hcv'] at h1 h2
            obtain ⟨_, hw1s⟩ := hws l1 h1; obtain ⟨_, hw2s⟩ := hws l2 h2
            have hw1o := (hws l1 h1).1; have hw2o := (hws l2 h2).1
            rcases hb.disjoint_all l1 l2 h1 h2 hne (by omega) (by omega) with ha | hb2
            · exact Or.inl (by omega)
            · exact Or.inr (by omega)
          other_no_sent := fun l hl hls => (hother_sl l hl hls).ne_sentinel
          other_slices := hother_sl }
      off_le_p := h.off_le_p, p_le_end := h.p_le_end, red_le := h.red_le
      src_pref := h.src_pref.mono (by omega) hrefs fun idx ha _ =>
        hsrc_wstk idx ha (by have := h.p_le_end; omega)
      src_rem := WatchSliceOk.relocate_same (k := st.core) (by omega) hrefs (fun idx _ =>
        hsrc_wstk (p + idx) (by have := h.off_le_p; omega) (by omega)) h.src_rem }

theorem TransOuterInv.skip_bin {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 : FullState} {src off p end_v reduced : Nat} {st : FullState} {w0 : BitVec 32}
    (h : TransOuterInv c F0 F_cur s0 src off p end_v reduced st) (hp : p < end_v)
    (hget : st.core.wstk[p]? = some w0) (hflag : (w0 &&& 0x80000000#32) ≠ 0#32) :
    w0 ≠ 0xFFFFFFFF#32 ∧ (w0 &&& 0x7FFFFFFF#32).toNat < 2 * st.core.cur_vars ∧
    (cnfOfClauses F_cur).EntailsClause (cnfClause [src, (w0 &&& 0x7FFFFFFF#32).toNat]) ∧
    TransOuterInv c F0 F_cur s0 src off (p + 1) end_v reduced st := by
  obtain ⟨hne, hlt, hent, htail⟩ := watchSlice_inv_bin h.src_rem (by omega) hget hflag
  have h1 : TombWatchSliceOk F_cur st.core src p 1 0 := .bin hget hflag hne hlt hent .empty
  have hpref := h.src_pref.append
    (by rw [show off + (p - off) = p by have := h.off_le_p; omega]; exact h1)
  rw [show p - off + 1 = (p + 1) - off by have := h.off_le_p; omega, Nat.add_zero] at hpref
  exact ⟨hne, hlt, hent,
    { h with
      off_le_p := by have := h.off_le_p; omega
      p_le_end := by omega, red_le := by have := h.red_le; omega, src_pref := hpref
      src_rem := by rwa [show end_v - p - 1 = end_v - (p + 1) by omega] at htail }⟩

theorem TransOuterInv.skip_large {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 : FullState} {src off p end_v reduced : Nat} {st : FullState} {w0 : BitVec 32}
    (h : TransOuterInv c F0 F_cur s0 src off p end_v reduced st) (hp : p < end_v)
    (hget : st.core.wstk[p]? = some w0) (hflag : (w0 &&& 0x80000000#32) = 0#32) :
    p + 2 ≤ end_v ∧ TransOuterInv c F0 F_cur s0 src off (p + 2) end_v reduced st := by
  obtain ⟨hle, cr, h1, hcr, href, htail⟩ := watchSlice_inv_large h.src_rem (by omega) hget hflag
  have hs : TombWatchSliceOk F_cur st.core src p 2 0 := .large hget h1 hflag hcr href .empty
  have hpref := h.src_pref.append
    (by rw [show off + (p - off) = p by have := h.off_le_p; omega]; exact hs)
  rw [show p - off + 2 = (p + 2) - off by have := h.off_le_p; omega, Nat.add_zero] at hpref
  exact ⟨by omega,
    { h with
      off_le_p := by have := h.off_le_p; omega
      p_le_end := by omega, red_le := by have := h.red_le; omega, src_pref := hpref
      src_rem := by rwa [show end_v - p - 2 = end_v - (p + 2) by omega] at htail }⟩

theorem TransOuterInv.mark_tomb {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 : FullState} {src off p end_v reduced : Nat} {st : FullState} {w0 : BitVec 32}
    {wu' tc' : BitVec 64} (h : TransOuterInv c F0 F_cur s0 src off p end_v reduced st)
    (hp : p < end_v) (hsrc_lt : src < 2 * st.core.cur_vars)
    (hget : st.core.wstk[p]? = some w0) (hflag : (w0 &&& 0x80000000#32) ≠ 0#32) :
    let st' : FullState :=
      { st with core := { st.core with wstk := st.core.wstk.set p 0xFFFFFFFF#32, wusable := wu' }
                scratch := { st.scratch with trans_cnt := tc' } }
    TransOuterInv c F0 F_cur s0 src off (p + 1) end_v (reduced + 1) st' := by
  intro st'; obtain ⟨_, _, _, htail⟩ := watchSlice_inv_bin h.src_rem (by omega) hget hflag
  have hp_len : p < st.core.wstk.length := by
    have := h.base.end_le_wlen; have := h.base.len_ok.core_ok.wlen_le
    rw [h.base.len_ok.core_ok.wstk_len_arr]; omega
  have hset_ne : ∀ idx, idx ≠ p → st'.core.wstk[idx]? = st.core.wstk[idx]? :=
    fun idx hi => List.getElem?_set_ne hi.symm
  have hset_p : st'.core.wstk[p]? = some 0xFFFFFFFF#32 := List.getElem?_set_self hp_len
  have hpref := (TombWatchSliceOk.mono (k := st.core) (k' := st'.core) (Nat.le_refl _)
    (fun _ hr => hr) (fun idx _ hi => hset_ne idx (by have := h.off_le_p; omega)) h.src_pref).append
    (by rw [show off + (p - off) = p by have := h.off_le_p; omega]
        exact (show TombWatchSliceOk F_cur st'.core src p 1 1 from .tomb hset_p .empty))
  rw [show p - off + 1 = (p + 1) - off by have := h.off_le_p; omega] at hpref
  exact
    { base := h.base.frame_wstk hsrc_lt (by simp [h.base.len_ok.core_ok.wstk_len_arr])
        (fun idx ho => hset_ne idx (by have := h.off_le_p; rcases ho with ho | ho <;> omega))
      off_le_p := by have := h.off_le_p; omega
      p_le_end := by omega, red_le := by have := h.off_le_p; have := h.red_le; omega
      src_pref := hpref
      src_rem := WatchSliceOk.relocate_same (k := st.core) (k' := st'.core) (Nat.le_refl _)
        (fun _ hr => hr) (fun idx _ => hset_ne (p + 1 + idx) (by omega))
        (by rwa [show end_v - p - 1 = end_v - (p + 1) by omega] at htail) }

theorem TransOuterInv.with_scratch {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 : FullState} {src off p end_v reduced : Nat} {st : FullState} {sc' : FullScratch}
    (h : TransOuterInv c F0 F_cur s0 src off p end_v reduced st) (hok : sc'.LengthsOk c)
    (hll : sc'.last_learned = st.scratch.last_learned)
    (hel : sc'.extend_len = st.scratch.extend_len) :
    TransOuterInv c F0 F_cur s0 src off p end_v reduced { st with scratch := sc' } :=
  { h with
    base :=
      { h.base with
        len_ok := h.base.len_ok.with_scratch hok
        scratch_pres := ⟨hll.trans h.base.scratch_pres.1, hel.trans h.base.scratch_pres.2⟩ } }

theorem TransOuterInv.of_reduced0 {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 : FullState} {src off p end_v : Nat} {st : FullState}
    (hsp0 : FullSparseInv c F0 s0) (hw0 : FullWitnessInv c F0 F_cur s0.core)
    (h : TransOuterInv c F0 F_cur s0 src off p end_v 0 st) : FullSparseInv c F0 st :=
  h.base.toSparse hsp0 hw0
    (by rw [h.base.src_off, h.base.src_sz]; exact h.src_full_tomb.to_watchSlice)

theorem TransOuterInv.of_reduced0_full {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s0 : FullState} {src off p end_v : Nat} {st : FullState}
    (hsp0 : FullSparseInv c F0 s0) (hw0 : FullWitnessInv c F0 F_cur s0.core)
    (h : TransOuterInv c F0 F_cur s0 src off p end_v 0 st) :
    FullSparseInv c F0 st ∧ FullWitnessInv c F0 F_cur st.core :=
  have hcl : WatchSliceOk F_cur st.core src
      (fullWatchOffCore st.core src) (fullWatchSizeCore st.core src) := by
    rw [h.base.src_off, h.base.src_sz]; exact h.src_full_tomb.to_watchSlice
  ⟨h.base.toSparse hsp0 hw0 hcl, h.base.toWitness_of_src_clean hw0 hcl⟩

theorem TransOuterInv.del_side_and_tomb {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 : FullState} {src off p end_v reduced dst : Nat}
    {st_r st' : FullState} {w0 : BitVec 32} {wvec' wstk' : List (BitVec 32)} {wu' tc' : BitVec 64}
    (hto : TransOuterInv c F0 F_cur s0 src off p end_v reduced st_r) (hp_lt : p < end_v)
    (hp_wc : p < c.wcap) (hs_lt : src < 2 * st_r.core.cur_vars)
    (hd_lt : dst < 2 * st_r.core.cur_vars) (hd_ne : dst ≠ src)
    (hget : st_r.core.wstk[p]? = some w0)
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

/-- Compaction loop invariant: `src` watch list `[off, q)` cleanly compacted from `[p, end_v)`. -/
structure TransCompactInv (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s0 : FullState) (src off q p end_v reduced : Nat) (st : FullState) : Prop where
  base : TransOuterBase c F0 F_cur s0 src off end_v st
  q_range : off ≤ q ∧ q ≤ p ∧ p ≤ end_v
  red_le : p - q ≤ reduced
  comp_pref : WatchSliceOk F_cur st.core src off (q - off)
  comp_rem : TombWatchSliceOk F_cur st.core src p (end_v - p) (reduced - (p - q))

theorem TransCompactInv.init {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 : FullState} {src off p_old end_v reduced : Nat} {st : FullState}
    (h : TransOuterInv c F0 F_cur s0 src off p_old end_v reduced st) :
    TransCompactInv c F0 F_cur s0 src off off off end_v reduced st :=
  { base := h.base, q_range := ⟨Nat.le_refl _, Nat.le_refl _, h.base.off_le_end⟩
    red_le := by simp, comp_pref := by simp only [Nat.sub_self]; exact .empty
    comp_rem := by simpa only [Nat.sub_self, Nat.sub_zero] using h.src_full_tomb }

theorem TransCompactInv.step_tomb {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 : FullState} {src off q p end_v reduced : Nat} {st : FullState} {w0 : BitVec 32}
    (h : TransCompactInv c F0 F_cur s0 src off q p end_v reduced st) (hp : p < end_v)
    (hget : st.core.wstk[p]? = some w0) (htomb : w0 = 0xFFFFFFFF#32) :
    TransCompactInv c F0 F_cur s0 src off q (p + 1) end_v reduced st := by
  have hstep := h.comp_rem.inv_step (by omega) hget; subst htomb
  simp only [tr_tomb_bin_flag, ↓reduceIte] at hstep
  have hqr := h.q_range; have hrl := h.red_le; obtain ⟨_, htail⟩ := hstep
  exact
    { h with
      q_range := by omega, red_le := by omega
      comp_rem := by rwa [show end_v - p - 1 = end_v - (p + 1) by omega,
        show reduced - (p - q) - 1 = reduced - (p + 1 - q) by omega] at htail }

theorem TransCompactInv.step_bin {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 : FullState} {src off q p end_v reduced : Nat} {st : FullState} {w0 : BitVec 32}
    (h : TransCompactInv c F0 F_cur s0 src off q p end_v reduced st) (hp : p < end_v)
    (hsrc_lt : src < 2 * st.core.cur_vars) (hget : st.core.wstk[p]? = some w0)
    (hne : w0 ≠ 0xFFFFFFFF#32) (hflag : (w0 &&& 0x80000000#32) ≠ 0#32) :
    let st' := { st with core := { st.core with wstk := st.core.wstk.set q w0 } }
    TransCompactInv c F0 F_cur s0 src off (q + 1) (p + 1) end_v reduced st' := by
  intro st'; have hstep := h.comp_rem.inv_step (by omega) hget
  simp only [hflag, ↓reduceIte, hne] at hstep; obtain ⟨hlt, hent, htail⟩ := hstep
  have hqr := h.q_range
  have hqlen : q < st.core.wstk.length := by
    have := h.base.end_le_wlen; have := h.base.len_ok.core_ok.wlen_le
    rw [h.base.len_ok.core_ok.wstk_len_arr]; omega
  have hset_ne : ∀ idx, idx ≠ q → st'.core.wstk[idx]? = st.core.wstk[idx]? :=
    fun idx hi => List.getElem?_set_ne hi.symm
  have hpref := watchSlice_append (WatchSliceOk.relocate_same (k := st.core) (k' := st'.core)
    (p' := off) (Nat.le_refl _) (fun _ hr => hr) (fun idx hi => hset_ne (off + idx) (by omega))
    h.comp_pref)
    (by rw [show off + (q - off) = q by omega]
        exact .bin (List.getElem?_set_self hqlen) hflag hne hlt hent .empty)
  rw [show q - off + 1 = (q + 1) - off by omega] at hpref
  exact
    { base := h.base.frame_wstk hsrc_lt (wu' := st.core.wusable) (tc' := st.scratch.trans_cnt)
        (List.length_set.trans h.base.len_ok.core_ok.wstk_len_arr)
        (fun idx ho => hset_ne idx (by omega))
      q_range := by omega, red_le := by have := h.red_le; omega, comp_pref := hpref
      comp_rem := by
        rw [show p + 1 - (q + 1) = p - q by omega]
        exact TombWatchSliceOk.mono (k := st.core) (k' := st'.core) (Nat.le_refl _)
          (fun _ hr => hr) (fun idx ha _ => hset_ne idx (by omega))
          (by rwa [show end_v - p - 1 = end_v - (p + 1) by omega] at htail) }

theorem TransCompactInv.step_large {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 : FullState} {src off q p end_v reduced : Nat} {st : FullState} {w0 : BitVec 32}
    (h : TransCompactInv c F0 F_cur s0 src off q p end_v reduced st) (hp : p < end_v)
    (hsrc_lt : src < 2 * st.core.cur_vars) (hget : st.core.wstk[p]? = some w0)
    (hflag : (w0 &&& 0x80000000#32) = 0#32) : p + 1 < end_v ∧
    ∃ w1 : BitVec 32, st.core.wstk[p + 1]? = some w1 ∧
      let st1 := { st with core := { st.core with wstk := st.core.wstk.set q w0 } }
      let st' := { st1 with core := { st1.core with wstk := st1.core.wstk.set (q + 1) w1 } }
      TransCompactInv c F0 F_cur s0 src off (q + 2) (p + 2) end_v reduced st' := by
  have hstep := h.comp_rem.inv_step (by omega) hget; simp only [hflag, ↓reduceIte] at hstep
  obtain ⟨hle, cr, hcr_get, hcr_lt, hcr_ref, htail⟩ := hstep
  have hqr := h.q_range; refine ⟨by omega, cr, hcr_get, ?_⟩
  have hqlen : q < st.core.wstk.length := by
    have := h.base.end_le_wlen; have := h.base.len_ok.core_ok.wlen_le
    rw [h.base.len_ok.core_ok.wstk_len_arr]; omega
  have hq1len : q + 1 < (st.core.wstk.set q w0).length := by
    have := h.base.end_le_wlen; have := h.base.len_ok.core_ok.wlen_le
    rw [List.length_set, h.base.len_ok.core_ok.wstk_len_arr]; omega
  let st1 := { st with core := { st.core with wstk := st.core.wstk.set q w0 } }
  let st' := { st1 with core := { st1.core with wstk := st1.core.wstk.set (q + 1) cr } }
  have hset_ne : ∀ idx, idx ≠ q → idx ≠ q + 1 → st'.core.wstk[idx]? = st.core.wstk[idx]? :=
    fun idx h0 h1 => (List.getElem?_set_ne h1.symm).trans (List.getElem?_set_ne h0.symm)
  have hget_q : st'.core.wstk[q]? = some w0 :=
    (List.getElem?_set_ne (by omega : q + 1 ≠ q)).trans (List.getElem?_set_self hqlen)
  have hpref := watchSlice_append (WatchSliceOk.relocate_same (k := st.core) (k' := st'.core)
    (p' := off) (Nat.le_refl _) (fun _ hr => hr)
    (fun idx hi => hset_ne (off + idx) (by omega) (by omega)) h.comp_pref)
    (by rw [show off + (q - off) = q by omega]
        exact .large hget_q (List.getElem?_set_self hq1len) hflag hcr_lt hcr_ref .empty)
  rw [show q - off + 2 = (q + 2) - off by omega] at hpref
  exact
    { base := h.base.frame_wstk hsrc_lt (wu' := st.core.wusable) (tc' := st.scratch.trans_cnt)
        (by simp [h.base.len_ok.core_ok.wstk_len_arr])
        (fun idx ho => hset_ne idx (by omega) (by omega))
      q_range := by omega, red_le := by have := h.red_le; omega, comp_pref := hpref
      comp_rem := by
        rw [show p + 2 - (q + 2) = p - q by omega]
        exact TombWatchSliceOk.mono (k := st.core) (k' := st'.core) (Nat.le_refl _)
          (fun _ hr => hr) (fun idx ha _ => hset_ne idx (by omega) (by omega))
          (by rwa [show end_v - p - 2 = end_v - (p + 2) by omega] at htail) }

theorem TransCompactInv.at_end {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 : FullState} {src off q end_v reduced : Nat} {st : FullState}
    (h : TransCompactInv c F0 F_cur s0 src off q end_v end_v reduced st) :
    q = end_v - reduced ∧ off ≤ end_v - reduced ∧ end_v - reduced ≤ end_v ∧
    WatchSliceOk F_cur st.core src off (end_v - off - reduced) := by
  have hqr := h.q_range; have hrl := h.red_le
  have hz : reduced - (end_v - q) = 0 := by
    have hr := h.comp_rem; rw [Nat.sub_self] at hr; exact hr.eq_zero_of_rem0
  have hq : q = end_v - reduced := by omega
  have hp := h.comp_pref; rw [hq, show end_v - reduced - off = end_v - off - reduced by omega] at hp
  exact ⟨hq, by omega, by omega, hp⟩

theorem TransOuterBase.sentinel_fill_step {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 : FullState} {src off q_start q end_v : Nat} {st : FullState}
    (hb : TransOuterBase c F0 F_cur s0 src off end_v st) (hsrc_lt : src < 2 * st.core.cur_vars)
    (hq : off ≤ q_start ∧ q_start ≤ q ∧ q < end_v)
    (hsl : WatchSliceOk F_cur st.core src off (q_start - off)) :
    let st' := { st with core := { st.core with wstk := st.core.wstk.set q 0xFFFFFFFF#32 } }
    TransOuterBase c F0 F_cur s0 src off end_v st' ∧
    WatchSliceOk F_cur st'.core src off (q_start - off) :=
  ⟨hb.frame_wstk hsrc_lt (wu' := st.core.wusable) (tc' := st.scratch.trans_cnt)
    (by simp [hb.len_ok.core_ok.wstk_len_arr])
    (fun idx ho => List.getElem?_set_ne (by cases ho <;> omega)),
   WatchSliceOk.relocate_same (k := st.core) (p' := off) (Nat.le_refl _) (fun _ hr => hr)
    (fun idx hi => List.getElem?_set_ne (by omega)) hsl⟩

theorem TransOuterBase.of_compact_done_full {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 : FullState} {src off end_v reduced : Nat} {wu' : BitVec 64} {nb' : Nat} {st : FullState}
    (hsp0 : FullSparseInv c F0 s0) (hw0 : FullWitnessInv c F0 F_cur s0.core)
    (hb : TransOuterBase c F0 F_cur s0 src off end_v st) (hsrc_lt : src < 2 * st.core.cur_vars)
    (hred : reduced ≤ end_v - off)
    (hsl : WatchSliceOk F_cur st.core src off (end_v - off - reduced)) :
    let new_sz := BitVec.ofNat 32 ((end_v - off) - reduced)
    let st' := { st with core := { st.core with
      wvec := st.core.wvec.set (2 * src + 1) new_sz, wusable := wu', num_binary := nb' } }
    FullSparseInv c F0 st' ∧ FullWitnessInv c F0 F_cur st'.core := by
  intro new_sz st'
  have hnw : new_sz.toNat = end_v - off - reduced := by
    have := hb.end_le_wlen; have := hb.len_ok.core_ok.wlen_le; have := c.hwcap
    unfold dimacsBound at *; simp only [new_sz, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  have hwv_len : 2 * src + 1 < st.core.wvec.length := by
    rw [hb.len_ok.core_ok.wvec_len]; have := hb.len_ok.core_ok.cur_vars_le; omega
  have hwv_even : ∀ l < 2 * st.core.cur_vars,
      fullWatchOffCore st'.core l = fullWatchOffCore st.core l := fun l _ =>
    congrArg (fun o : Option (BitVec 32) => (o.getD 0#32).toNat)
      (List.getElem?_set_ne (by omega : 2 * src + 1 ≠ 2 * l))
  have hwv_odd_ne : ∀ l < 2 * st.core.cur_vars, l ≠ src →
      fullWatchSizeCore st'.core l = fullWatchSizeCore st.core l := fun l _ hls =>
    congrArg (fun o : Option (BitVec 32) => (o.getD 0#32).toNat)
      (List.getElem?_set_ne (by omega : 2 * src + 1 ≠ 2 * l + 1))
  have hsrc_off' : fullWatchOffCore st'.core src = off := (hwv_even src hsrc_lt).trans hb.src_off
  have hsrc_sz' : fullWatchSizeCore st'.core src = end_v - off - reduced := by
    unfold fullWatchSizeCore
    change ((st.core.wvec.set (2 * src + 1) new_sz)[2 * src + 1]?.getD 0#32).toNat = _
    rw [List.getElem?_set_self hwv_len]; simp [hnw]
  have hsl' : WatchSliceOk F_cur st'.core src
      (fullWatchOffCore st'.core src) (fullWatchSizeCore st'.core src) := by
    rw [hsrc_off', hsrc_sz']
    exact WatchSliceOk.relocate_same (k := st.core) (Nat.le_refl _)
      (fun _ hr => hr) (fun _ _ => rfl) hsl
  have hws : ∀ l < 2 * st.core.cur_vars, fullWatchOffCore st'.core l = fullWatchOffCore st.core l ∧
      fullWatchSizeCore st'.core l ≤ fullWatchSizeCore st.core l := fun l hl => by
    by_cases hls : l = src
    · subst hls; rw [hsrc_off', hsrc_sz', hb.src_off, hb.src_sz]; exact ⟨rfl, by omega⟩
    · exact ⟨hwv_even l hl, by rw [hwv_odd_ne l hl hls]; exact Nat.le_refl _⟩
  have := hb.off_le_end
  have hb' : TransOuterBase c F0 F_cur s0 src off (end_v - reduced) st' :=
    { len_ok := ⟨{ hb.len_ok.core_ok with wvec_len := by simp [st', hb.len_ok.core_ok.wvec_len] },
        hb.len_ok.scratch_ok⟩, core_pres := hb.core_pres, scratch_pres := hb.scratch_pres
      off_le_end := by omega, src_off := hsrc_off', src_sz := by rw [hsrc_sz']; omega
      end_le_wlen := Nat.le_trans (by omega) hb.end_le_wlen, off_pos := hb.off_pos
      other_bounds := fun l hl hls => by
        rw [(hws l hl).1]; have := (hws l hl).2
        exact Nat.le_trans (by omega) (hb.other_bounds l hl hls)
      other_pos_off := fun l hl hls hp => by
        rw [(hws l hl).1]; have := (hws l hl).2; exact hb.other_pos_off l hl hls (by omega)
      disjoint_all := fun l1 l2 h1 h2 hne hp1 hp2 => by
        obtain ⟨_, hw1s⟩ := hws l1 h1; obtain ⟨_, hw2s⟩ := hws l2 h2
        have hw1o := (hws l1 h1).1; have hw2o := (hws l2 h2).1
        exact Or.imp (fun ha => by omega) (fun hb2 => by omega)
          (hb.disjoint_all l1 l2 h1 h2 hne (by omega) (by omega))
      other_no_sent := fun l hl hls => by
        rw [hwv_even l hl, hwv_odd_ne l hl hls]; exact hb.other_no_sent l hl hls
      other_slices := fun l hl hls => by
        rw [hwv_even l hl, hwv_odd_ne l hl hls]
        exact WatchSliceOk.relocate_same (k := st.core) (Nat.le_refl _) (fun _ hr => hr)
          (fun _ _ => rfl) (hb.other_slices l hl hls) }
  exact ⟨hb'.toSparse hsp0 hw0 hsl', hb'.toWitness_of_src_clean hw0 hsl'⟩

theorem TransOuterBase.of_compact_done {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 : FullState} {src off end_v reduced : Nat} {wu' : BitVec 64} {nb' : Nat} {st : FullState}
    (hsp0 : FullSparseInv c F0 s0) (hw0 : FullWitnessInv c F0 F_cur s0.core)
    (hb : TransOuterBase c F0 F_cur s0 src off end_v st) (hsrc_lt : src < 2 * st.core.cur_vars)
    (hred : reduced ≤ end_v - off)
    (hsl : WatchSliceOk F_cur st.core src off (end_v - off - reduced)) :
    let new_sz := BitVec.ofNat 32 ((end_v - off) - reduced)
    let st' := { st with core := { st.core with
      wvec := st.core.wvec.set (2 * src + 1) new_sz, wusable := wu', num_binary := nb' } }
    FullSparseInv c F0 st' :=
  (hb.of_compact_done_full hsp0 hw0 hsrc_lt hred hsl).1

end LeanQbe.T.Examples.Kissat.Proof.Transitive
