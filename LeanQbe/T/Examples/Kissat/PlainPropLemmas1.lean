module

public import LeanQbe.T.Examples.Kissat.PlainSpec

/-!
# Kissat `D-Plain` BCP Helpers & `plain_find_repl` Proof (Part 1)

Provides scoped `PlainPropTactics`, `WatchSliceOk` / `SplitWatchesInv` compaction theory,
arena-swap & unit-propagation preservation lemmas, and the `Func.wp` proof of `plain_find_repl`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Plain

open Std Std.Sat Std.ExtHashMap LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.ProofUtil
  LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat Kraken.Bedrock2.Test

/-! ## 1. Scoped tactic & arithmetic helpers (`PlainPropTactics`) -/

namespace PlainPropTactics

theorem strip_le_32_64 {P : Prop} (h : P) : 32 ≤ 64 ∧ P := ⟨by decide, h⟩
theorem strip_le_8_32 {P : Prop} (h : P) : 8 ≤ 32 ∧ P := ⟨by decide, h⟩
theorem strip_le_8_64 {P : Prop} (h : P) : 8 ≤ 64 ∧ P := ⟨by decide, h⟩

scoped macro "pp_strip" : tactic =>
  `(tactic| first | apply strip_le_32_64 | apply strip_le_8_32 | apply strip_le_8_64)
scoped macro "pp_unmdata" : tactic =>
  `(tactic| first | change Func.wp _ _ _ _ _ _ | change wp _ _ _ _ _)
scoped macro "pp_step" : tactic => `(tactic| ((try pp_unmdata); (repeat pp_strip); c0_step))
scoped macro "pp_steps" : tactic =>
  `(tactic| (
      (try pp_unmdata)
      (repeat pp_strip)
      c0_steps
      repeat (any_goals (pp_strip; repeat pp_strip); c0_steps)))

attribute [scoped bv_c0 high] bv_c0_zext32_64
attribute [scoped bv_c0] bv32_lshr_1 bv32_and_1 bv32_xor_1 List.length_set Bool.false_eq_true

@[scoped bv_c0] theorem bv64_shl1_nat (x : BitVec 64) :
    (x <<< (1 : Nat)).toNat = (2 * x.toNat) % 2 ^ 64 := by
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm]

end PlainPropTactics

open scoped PlainPropTactics

/-! ## 2. Arithmetic & `WatchSliceOk` helpers -/

theorem bv32_sle0_eq_not_slt0 (x : BitVec 32) : (0#32).sle x = !(x.slt 0#32) := by
  simp only [BitVec.sle, BitVec.slt]; change decide (0 ≤ x.toInt) = !decide (x.toInt < 0)
  by_cases h : x.toInt < 0 <;> simp [h, show (0 ≤ x.toInt) ↔ ¬(x.toInt < 0) by omega]

theorem bv64_sub1_toNat {f : BitVec 64} (hf : f ≠ 0#64) :
    (f - 1#64).toNat = f.toNat - 1 := by
  have hpos : 0 < f.toNat := Nat.pos_of_ne_zero fun h0 =>
    hf (BitVec.eq_of_toNat_eq (by simpa using h0))
  bv_omega

theorem watchSlice_append {c : PlainCfg} {F0 : CNF Nat} {s : PlainState}
    {lit p len1 len2 : Nat}
    (h1 : WatchSliceOk c F0 s lit p len1)
    (h2 : WatchSliceOk c F0 s lit (p + len1) len2) :
    WatchSliceOk c F0 s lit p (len1 + len2) := by
  induction h1 with
  | @empty p => simpa using h2
  | @bin p rem w h0 hf hl he _ ih =>
    have hadd : p + (rem + 1) = (p + 1) + rem := by omega
    rw [hadd] at h2
    have hres := ih h2
    have hadd2 : rem + 1 + len2 = (rem + len2) + 1 := by omega
    rw [hadd2]; exact .bin h0 hf hl he hres
  | @large p rem w cr h0 h1 hf hl hr _ ih =>
    have hadd : p + (rem + 2) = (p + 2) + rem := by omega
    rw [hadd] at h2
    have hres := ih h2
    have hadd2 : rem + 2 + len2 = (rem + len2) + 2 := by omega
    rw [hadd2]; exact .large h0 h1 hf hl hr hres

/-! ## 3. `plain_find_repl` helpers & `Func.wp` proof -/

@[expose] def plainFindReplBad (c : PlainCfg) (s : PlainState) (cref k : Nat) : Prop :=
  let cand := (s.arena[cref + 3 + k]?.getD 0#32).toNat
  2 * c.mv ≤ cand ∨ ((s.vals[cand]?.getD 0#8).signExtend 32).slt 0#32 = true

private theorem plain_find_repl_ok {c : PlainCfg} {s : PlainState} {cref r idx : Nat}
    {hi_lt : idx < s.arena.length} {hj_lt : (s.arena[idx]'hi_lt).toNat < s.vals.length}
    (hlen : s.LengthsOk c) (hidx : idx = cref + 3 + r)
    (hsle : (0#32).sle ((s.vals[(s.arena[idx]'hi_lt).toNat]'hj_lt).signExtend 32) = true) :
    let cand := (s.arena[cref + 3 + r]?.getD 0#32).toNat
    cand < 2 * c.mv ∧ ((s.vals[cand]?.getD 0#8).signExtend 32).slt 0#32 = false := by
  subst hidx; have hvl := hlen.vals_len; dsimp only
  rw [List.getElem?_eq_getElem hi_lt, Option.getD_some,
    List.getElem?_eq_getElem hj_lt, Option.getD_some]
  refine ⟨by omega, ?_⟩
  rw [bv32_sle0_eq_not_slt0, Bool.not_eq_true'] at hsle; exact hsle

private theorem plain_find_repl_bad_slt {c : PlainCfg} {s : PlainState} {cref r idx : Nat}
    {hi_lt : idx < s.arena.length} {hj_lt : (s.arena[idx]'hi_lt).toNat < s.vals.length}
    (hidx : idx = cref + 3 + r)
    (h : (0#32).sle ((s.vals[(s.arena[idx]'hi_lt).toNat]'hj_lt).signExtend 32) = false) :
    plainFindReplBad c s cref r := by
  subst hidx; unfold plainFindReplBad; refine Or.inr ?_
  rw [List.getElem?_eq_getElem hi_lt, Option.getD_some,
    List.getElem?_eq_getElem hj_lt, Option.getD_some]
  rw [bv32_sle0_eq_not_slt0, Bool.not_eq_false'] at h; exact h

private theorem plain_find_repl_bad_oob {c : PlainCfg} {s : PlainState} {cref r idx nlits : Nat}
    {hi_lt : idx < s.arena.length} (hidx : idx = cref + 3 + r) (hnl : nlits = 2 * c.mv)
    (h : ¬ (s.arena[idx]'hi_lt).toNat < nlits) :
    plainFindReplBad c s cref r := by
  subst hidx; unfold plainFindReplBad; refine Or.inl ?_
  rw [List.getElem?_eq_getElem hi_lt, Option.getD_some]; omega

theorem plain_find_repl_wp_aux (Γ : Env) {c : PlainCfg} {s : PlainState}
    {R : Mem 64 → Prop} {cref : BitVec 64} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (hlen : s.LengthsOk c) (_hc3 : cref.toNat + 3 ≤ s.arena_len)
    (hsz3 : 3 ≤ arenaClauseSize s cref.toNat)
    (hfit : cref.toNat + 3 + arenaClauseSize s cref.toNat ≤ s.arena_len)
    (hm : (PlainMem c s ⋆ R) m)
    (hNone : (∀ k, 2 ≤ k → k < arenaClauseSize s cref.toNat →
        plainFindReplBad c s cref.toNat k) → Q (0xFFFFFFFF#64, ()) m)
    (hSome : ∀ (r : Nat) (m' : Mem 64), 2 ≤ r → r < arenaClauseSize s cref.toNat →
        (let cand := (s.arena[cref.toNat + 3 + r]?.getD 0#32).toNat
         cand < 2 * c.mv ∧ ((s.vals[cand]?.getD 0#8).signExtend 32).slt 0#32 = false) →
        (PlainMem c { s with arena := s.arena.set (cref.toNat + 1) (BitVec.ofNat 32 r) } ⋆ R) m' →
        Q (BitVec.ofNat 64 r, ()) m') :
    Func.wp Γ plain_find_repl_body (c.hdr, cref, ()) m Q X := by
  have hmv := c.hmv; have har := c.harena; unfold dimacsBound at hmv har
  have hal := hlen.arena_len_arr; have hale := hlen.arena_len_le; have hvl := hlen.vals_len
  have hc1 : (cref + 1).toNat = cref.toNat + 1 := by bv_omega
  have hc2 : (cref + 2).toNat = cref.toNat + 2 := by bv_omega
  have hc2_lt : (cref + 2).toNat < s.arena.length := by omega
  have hc1_lt : (cref + 1).toNat < s.arena.length := by omega
  have hsz_eq : (s.arena[(cref + 2).toNat]'hc2_lt).toNat = arenaClauseSize s cref.toNat := by
    unfold arenaClauseSize
    rw [List.getElem?_eq_getElem (show cref.toNat + 2 < s.arena.length by omega), Option.getD_some]
    exact congrArg BitVec.toNat (by congr 1)
  pp_step; pp_step; pp_step; pp_step; pp_step; pp_step
  generalize hsz_v : s.arena[(cref + 2).toNat]'hc2_lt = sz
  generalize hsr0_v : s.arena[(cref + 1).toNat]'hc1_lt = sr0
  have hsz_nat : sz.toNat = arenaClauseSize s cref.toNat := by rw [← hsz_v]; exact hsz_eq
  refine wp_join_group
    (fun (srch, ()) mj => 2 ≤ srch.toNat ∧ srch.toNat < sz.toNat ∧ mj = m)
    ?_ ?_
  · rintro _ ⟨srch, ⟨⟩⟩ mj ⟨hsrch2, hsrch_lt, rfl⟩
    pp_steps
    refine wp_loop_inv
      (fun (r, ()) ml => srch.toNat ≤ r.toNat ∧ r.toNat ≤ sz.toNat ∧
        ml = mj ∧ ∀ k, srch.toNat ≤ k → k < r.toNat → plainFindReplBad c s cref.toNat k)
      (fun (r, ()) _ => sz.toNat - r.toNat)
      (fun J hJ => by
        pp_steps
        exact hJ _ _ ⟨Nat.le_refl _, by omega, rfl, fun _ _ _ => by omega⟩)
      (fun J (r, ()) ml ⟨hr_ge, hr_le, rfl, hseen1⟩ ih => ?_)
    pp_steps
    · have hok := plain_find_repl_ok (cref := cref.toNat) (r := r.toNat) hlen (by c0_bound) hc
      have hset : { s with arena := s.arena.set (cref + 1).toNat r } =
          { s with arena := s.arena.set (cref.toNat + 1) (BitVec.ofNat 32 r.toNat) } := by
        rw [hc1, bv_ofNat_toNat_eq]
      rw [hset] at hm; rw [bv32_zext64_eq]
      exact hSome r.toNat _ (by omega) (by omega) hok hm
    · refine ih _ _ (by c0_bound) ⟨by c0_bound, by c0_bound, rfl, fun k hk1 hk2 =>
        if hkr : k = r.toNat then
          hkr ▸ plain_find_repl_bad_slt (cref := cref.toNat) (r := r.toNat) (by c0_bound) hc
        else hseen1 k hk1 (by c0_bound)⟩
    · refine ih _ _ (by c0_bound) ⟨by c0_bound, by c0_bound, rfl, fun k hk1 hk2 =>
        if hkr : k = r.toNat then
          hkr ▸ plain_find_repl_bad_oob (cref := cref.toNat) (r := r.toNat)
            (by c0_bound) (by c0_bound) hc
        else hseen1 k hk1 (by c0_bound)⟩
    · refine wp_loop_inv
        (fun (r2, ()) ml2 => 2 ≤ r2.toNat ∧ r2.toNat ≤ srch.toNat ∧ ml2 = ml ∧
          ∀ k, 2 ≤ k → k < r2.toNat → plainFindReplBad c s cref.toNat k)
        (fun (r2, ()) _ => srch.toNat - r2.toNat)
        (fun J2 hJ2 => by
          pp_steps
          exact hJ2 _ _ ⟨by decide, by c0_bound, rfl, fun _ _ _ => by c0_bound⟩)
        (fun J2 (r2, ()) ml2 ⟨hr2_ge, hr2_le, rfl, hseen2⟩ ih2 => ?_)
      pp_steps
      · have hok := plain_find_repl_ok (cref := cref.toNat) (r := r2.toNat) hlen (by c0_bound) hc
        have hset : { s with arena := s.arena.set (cref + 1).toNat r2 } =
            { s with arena := s.arena.set (cref.toNat + 1) (BitVec.ofNat 32 r2.toNat) } := by
          rw [hc1, bv_ofNat_toNat_eq]
        rw [hset] at hm; rw [bv32_zext64_eq]
        exact hSome r2.toNat _ hr2_ge (by omega) hok hm
      · refine ih2 _ _ (by c0_bound) ⟨by c0_bound, by c0_bound, rfl, fun k hk1 hk2 =>
          if hkr : k = r2.toNat then
            hkr ▸ plain_find_repl_bad_slt (cref := cref.toNat) (r := r2.toNat) (by c0_bound) hc
          else hseen2 k hk1 (by c0_bound)⟩
      · refine ih2 _ _ (by c0_bound) ⟨by c0_bound, by c0_bound, rfl, fun k hk1 hk2 =>
          if hkr : k = r2.toNat then
            hkr ▸ plain_find_repl_bad_oob (cref := cref.toNat) (r := r2.toNat)
              (by c0_bound) (by c0_bound) hc
          else hseen2 k hk1 (by c0_bound)⟩
      · refine hNone fun k hk2 hksz =>
          if hks : k < srch.toNat then hseen2 k hk2 (by omega) else hseen1 k (by omega) (by omega)
  · intro J hJ; pp_steps
    · exact hJ (2#32, ()) m ⟨by decide, by c0_bound, rfl⟩
    · exact hJ (2#32, ()) m ⟨by decide, by c0_bound, rfl⟩
    · exact hJ (sr0, ()) m ⟨by c0_bound, by c0_bound, rfl⟩

theorem plain_find_repl_wp (Γ : Env) :
    ∀ args m Q X, plainFindReplSpec args m Q X →
      Func.wp Γ plain_find_repl_body args m Q X := by
  rintro ⟨h, cref, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hc3, hsz3, hfit, hm, hNone, hSome⟩
  exact plain_find_repl_wp_aux Γ hlen hc3 hsz3 hfit hm hNone hSome

/-! ## 4. Non-watch core invariants, arena swaps, and trail-extension helpers -/

/-- State with cleared watches (`wvec := 0, wlen := 0`), allowing reuse of `PlainCoreInv`
preservation lemmas (`assign_preserves_core`, `swapCl_preserves_core`) while `not_lit`'s watch
slice is mid-compaction. -/
abbrev withEmptyWatches (c : PlainCfg) (s : PlainState) : PlainState :=
  { s with wvec := List.replicate (4 * c.mv) 0#32, wlen := 0 }

theorem watchesInv_empty (c : PlainCfg) (F0 : CNF Nat) (s : PlainState) :
    WatchesInv c F0 (withEmptyWatches c s) := by
  have hw0 : ∀ l < 2 * c.mv, watchOff (withEmptyWatches c s) l = 0 ∧
      watchSize (withEmptyWatches c s) l = 0 := fun l hl => by
    unfold watchOff watchSize withEmptyWatches
    simp [show 2 * l < 4 * c.mv by omega, show 2 * l + 1 < 4 * c.mv by omega]
  exact WatchesInv.of_slices
    (fun l hl => by obtain ⟨ho, hs⟩ := hw0 l hl; omega)
    (fun l hl hp => by obtain ⟨_, hs⟩ := hw0 l hl; omega)
    (fun l1 _ h1 _ _ hp1 _ => by obtain ⟨_, hs⟩ := hw0 l1 h1; omega)
    (fun l hl => by obtain ⟨ho, hs⟩ := hw0 l hl; rw [ho, hs]; exact .empty)

theorem plainCoreInv_to_nw {c : PlainCfg} {F0 : CNF Nat} {s : PlainState}
    (h : PlainCoreInv c F0 s) : PlainCoreInv c F0 (withEmptyWatches c s) :=
  { h with
    lengths :=
      { h.lengths with
        wvec_len := by simp
        wlen_le := Nat.zero_le _ }
    arena := { h.arena with len_ok := h.arena.len_ok }
    watches := watchesInv_empty c F0 s }

theorem plainCoreInv_of_nw {c : PlainCfg} {F0 : CNF Nat} {s : PlainState}
    (hnw : PlainCoreInv c F0 (withEmptyWatches c s))
    (hlen : s.LengthsOk c) (hwat : WatchesInv c F0 s) : PlainCoreInv c F0 s :=
  { hnw with
    lengths := hlen
    arena := { hnw.arena with len_ok := hnw.arena.len_ok }
    watches := hwat }

/-- Updating `ar[cref + 1] := srch` and swapping `ar[cref + 3 + k1]` with `ar[cref + 3 + k2]`
preserves non-watch core invariants, `arenaClauseRefs`, `arenaClauseSize`, `arenaClauseGarb`, and
clause-literal membership. -/
theorem arena_swap_preserves_nw {c : PlainCfg} {F0 : CNF Nat} {s : PlainState}
    (hnw : PlainCoreInv c F0 (withEmptyWatches c s)) {cref k1 k2 : Nat} {srch : BitVec 32}
    (hcref : cref ∈ arenaClauseRefs s)
    (hk1 : k1 < arenaClauseSize s cref) (hk2 : k2 < arenaClauseSize s cref) :
    have hbd : cref + 3 + arenaClauseSize s cref ≤ s.arena.length := by
      have h1 : cref + 3 + arenaClauseSize s cref ≤ arenaNextOff s.arena s.arena_len cref :=
        (hnw.arena.refs_wf cref hcref).2.2.1
      have h2 : arenaNextOff s.arena s.arena_len cref ≤ s.arena_len :=
        (hnw.arena.refs_wf cref hcref).2.2.2.1
      have h3 : s.arena_len ≤ c.arena_cap := hnw.lengths.arena_len_le
      have h4 : s.arena.length = c.arena_cap := hnw.lengths.arena_len_arr
      omega
    let l1 := s.arena[cref + 3 + k1]'(by omega)
    let l2 := s.arena[cref + 3 + k2]'(by omega)
    let arena' := ((s.arena.set (cref + 1) srch).set (cref + 3 + k1) l2).set (cref + 3 + k2) l1
    let s' : PlainState := { s with arena := arena' }
    PlainCoreInv c F0 (withEmptyWatches c s') ∧
    arenaClauseRefs s' = arenaClauseRefs s ∧
    (∀ r ∈ arenaClauseRefs s, arenaClauseSize s' r = arenaClauseSize s r ∧
      arenaClauseGarb s' r = arenaClauseGarb s r ∧
      ∀ l, l ∈ arenaClauseLits s' r ↔ l ∈ arenaClauseLits s r) := by
  intro hbd l1 l2 arena' s'
  have hcore' : PlainCoreInv c F0 (withEmptyWatches c s') :=
    swapCl_preserves_core hnw (cref := cref) (k1 := k1) (k2 := k2) (srch := srch)
      (wvec' := List.replicate (4 * c.mv) 0#32) (wstk' := s.wstk) (wsort' := s.heur.wsort)
      (wlen' := 0) (wusable' := s.wusable) hcref hk1 hk2
      (by simp) hnw.lengths.wstk_len_arr hnw.lengths.heur_ok.wsort_len (by omega)
      (watchesInv_empty c F0 s')
  have hmc : cref + 3 ≤ s.arena_len ∧ 3 ≤ arenaClauseSize s cref ∧
      cref + 3 + arenaClauseSize s cref ≤ arenaNextOff s.arena s.arena_len cref ∧
      arenaNextOff s.arena s.arena_len cref ≤ s.arena_len ∧
      (arenaNextOff s.arena s.arena_len cref = s.arena_len ∨
        arenaNextOff s.arena s.arena_len cref + 3 ≤ s.arena_len) :=
    hnw.arena.refs_wf cref hcref
  have har_set0 : arena'[cref]? = s.arena[cref]? := by
    simp only [arena']
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega)]
  have har_set2 : arena'[cref + 2]? = s.arena[cref + 2]? := by
    simp only [arena']
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega)]
  have har_out : ∀ i, (i < cref ∨ cref + 3 + arenaClauseSize s cref ≤ i) →
      arena'[i]? = s.arena[i]? := fun i hi => by
    simp only [arena']
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega)]
  have hrefs : arenaClauseRefs s' = arenaClauseRefs s := by
    refine arenaClauseRefs_congr rfl fun r hr => ?_
    by_cases hrc : r = cref
    · subst hrc
      exact arenaNextOff_congr_block har_set0 har_set2 fun k hk1' _ => har_out k (Or.inr hk1')
    · rcases Nat.lt_or_gt_of_ne hrc with hlt | hgt
      · have hdisj := arenaScanRefs_disjoint hr hcref hlt
        have hr_bd : r + 3 ≤ s.arena_len ∧ 3 ≤ arenaClauseSize s r ∧
            r + 3 + arenaClauseSize s r ≤ arenaNextOff s.arena s.arena_len r := by
          have h := hnw.arena.refs_wf r hr; exact ⟨h.1, h.2.1, h.2.2.1⟩
        exact arenaNextOff_congr_block (har_out r (Or.inl (by omega)))
          (har_out (r + 2) (Or.inl (by omega))) fun k _ _ => har_out k (Or.inl (by omega))
      · have hdisj : cref + 3 + arenaClauseSize s cref ≤ r := hnw.arena.disjoint hcref hr hgt
        exact arenaNextOff_congr_block (har_out r (Or.inr hdisj))
          (har_out (r + 2) (Or.inr (by omega))) fun k _ _ => har_out k (Or.inr (by omega))
  refine ⟨hcore', hrefs, fun r hr => ?_⟩
  have hout : r ≠ cref →
      r + 3 + arenaClauseSize s r ≤ cref ∨ cref + 3 + arenaClauseSize s cref ≤ r := fun hne =>
    (Nat.lt_or_gt_of_ne hne).elim (fun h => Or.inl (hnw.arena.disjoint hr hcref h))
      (fun h => Or.inr (hnw.arena.disjoint hcref hr h))
  have hsz_eq : arenaClauseSize s' r = arenaClauseSize s r := by
    unfold arenaClauseSize; dsimp only [s']
    by_cases hrc : r = cref
    · subst hrc; rw [har_set2]
    · rcases hout hrc with hlt | hgt
      · have h3 : 3 ≤ arenaClauseSize s r := (hnw.arena.refs_wf r hr).2.1
        rw [har_out (r + 2) (Or.inl (by omega))]
      · rw [har_out (r + 2) (Or.inr (by omega))]
  have hgarb_eq : arenaClauseGarb s' r = arenaClauseGarb s r := by
    unfold arenaClauseGarb arenaHdr; dsimp only [s']
    by_cases hrc : r = cref
    · subst hrc; rw [har_set0]
    · rcases hout hrc with hlt | hgt
      · rw [har_out r (Or.inl (by omega))]
      · rw [har_out r (Or.inr hgt)]
  refine ⟨hsz_eq, hgarb_eq, fun l => ?_⟩
  have hbd_r : r + 3 + arenaClauseSize s r ≤ s.arena.length := by
    have h1 : r + 3 + arenaClauseSize s r ≤ arenaNextOff s.arena s.arena_len r :=
      (hnw.arena.refs_wf r hr).2.2.1
    have h2 : arenaNextOff s.arena s.arena_len r ≤ s.arena_len := (hnw.arena.refs_wf r hr).2.2.2.1
    have h3 : s.arena_len ≤ c.arena_cap := hnw.lengths.arena_len_le
    have h4 : s.arena.length = c.arena_cap := hnw.lengths.arena_len_arr
    omega
  have hbd_r' : r + 3 + arenaClauseSize s' r ≤ s'.arena.length := by
    rw [hsz_eq]; simp [s', arena', hbd_r]
  rw [mem_arenaClauseLits_iff hbd_r', mem_arenaClauseLits_iff hbd_r]
  simp only [hsz_eq]
  by_cases hrc : r = cref
  · subst hrc
    have hsw_k : ∀ k (hk : k < arenaClauseSize s r),
        s'.arena[r + 3 + k]'(by simp [s', arena']; omega) =
          if k = k2 then l1 else if k = k1 then l2 else s.arena[r + 3 + k]'(by omega) := by
      intro k hk; dsimp only [s', arena']
      by_cases h2 : k = k2
      · subst k; simp [List.getElem_set_self]
      · simp only [h2, ↓reduceIte, List.getElem_set_ne (by omega : r + 3 + k2 ≠ r + 3 + k)]
        by_cases h1 : k = k1
        · subst k; simp [List.getElem_set_self]
        · simp only [h1, ↓reduceIte, List.getElem_set_ne (by omega : r + 3 + k1 ≠ r + 3 + k),
            List.getElem_set_ne (by omega : r + 1 ≠ r + 3 + k)]
    constructor
    · rintro ⟨k, hk, hget⟩; rw [hsw_k k hk] at hget
      split at hget
      · exact ⟨k1, hk1, hget⟩
      · split at hget
        · exact ⟨k2, hk2, hget⟩
        · exact ⟨k, hk, hget⟩
    · rintro ⟨k, hk, hget⟩
      by_cases h1 : k = k1
      · subst k; exact ⟨k2, hk2, by rw [hsw_k k2 hk2]; simp [l1, hget]⟩
      · by_cases h2 : k = k2
        · subst k; exact ⟨k1, hk1, by rw [hsw_k k1 hk1]; simp [Ne.symm h1, l2, hget]⟩
        · exact ⟨k, hk, by rw [hsw_k k hk]; simp [h1, h2, hget]⟩
  · have hget_eq : ∀ k (hk : k < arenaClauseSize s r),
        s'.arena[r + 3 + k]'(by simp [s', arena']; omega) =
          s.arena[r + 3 + k]'(by omega) := fun k hk => by
      have hopt : s'.arena[r + 3 + k]? = s.arena[r + 3 + k]? := by
        dsimp only [s']
        rcases hout hrc with hlt | hgt
        · exact har_out (r + 3 + k) (Or.inl (by omega))
        · exact har_out (r + 3 + k) (Or.inr (by omega))
      rw [List.getElem?_eq_getElem (by simp [s', arena']; omega),
        List.getElem?_eq_getElem (by omega)] at hopt
      exact Option.some.inj hopt
    exact ⟨fun ⟨k, hk, h⟩ => ⟨k, hk, by rw [← hget_eq k hk]; exact h⟩,
      fun ⟨k, hk, h⟩ => ⟨k, hk, by rw [hget_eq k hk]; exact h⟩⟩

/-- Updating only `ar[cref + 1] := srch` (as in `plain_find_repl`) preserves non-watch core
invariants and all clause projections. -/
theorem arena_setSrch_preserves_nw {c : PlainCfg} {F0 : CNF Nat} {s : PlainState}
    (hnw : PlainCoreInv c F0 (withEmptyWatches c s)) {cref : Nat} {srch : BitVec 32}
    (hcref : cref ∈ arenaClauseRefs s) :
    let s' : PlainState := { s with arena := s.arena.set (cref + 1) srch }
    PlainCoreInv c F0 (withEmptyWatches c s') ∧
    arenaClauseRefs s' = arenaClauseRefs s ∧
    (∀ r ∈ arenaClauseRefs s, arenaClauseSize s' r = arenaClauseSize s r ∧
      arenaClauseGarb s' r = arenaClauseGarb s r ∧
      ∀ l, l ∈ arenaClauseLits s' r ↔ l ∈ arenaClauseLits s r) := by
  have h3 : 3 ≤ arenaClauseSize s cref := (hnw.arena.refs_wf cref hcref).2.1
  have hbd : cref + 3 + arenaClauseSize s cref ≤ s.arena.length := by
    have h1 : cref + 3 + arenaClauseSize s cref ≤ arenaNextOff s.arena s.arena_len cref :=
      (hnw.arena.refs_wf cref hcref).2.2.1
    have h2 : arenaNextOff s.arena s.arena_len cref ≤ s.arena_len :=
      (hnw.arena.refs_wf cref hcref).2.2.2.1
    have h4 : s.arena_len ≤ c.arena_cap := hnw.lengths.arena_len_le
    have h5 : s.arena.length = c.arena_cap := hnw.lengths.arena_len_arr
    omega
  have hsw := arena_swap_preserves_nw hnw (cref := cref) (k1 := 0) (k2 := 0) (srch := srch)
    hcref (by omega) (by omega)
  have heq_ar : ((s.arena.set (cref + 1) srch).set (cref + 3 + 0)
      (s.arena[cref + 3 + 0]'(by omega))).set (cref + 3 + 0)
      (s.arena[cref + 3 + 0]'(by omega)) = s.arena.set (cref + 1) srch := by
    apply List.ext_getElem (by simp)
    intro i hi _
    by_cases h1 : i = cref + 3 + 0
    · subst h1; simp [List.getElem_set_ne (by omega : cref + 1 ≠ cref + 3 + 0)]
    · rw [List.getElem_set_ne (Ne.symm h1), List.getElem_set_ne (Ne.symm h1)]
  simpa only [heq_ar] using hsw

/-- Swapping `ar[cref + 3 + k1]` and `ar[cref + 3 + k2]` without modifying `ar[cref + 1]`
preserves non-watch core invariants and all clause projections. -/
theorem arena_swapLits_preserves_nw {c : PlainCfg} {F0 : CNF Nat} {s : PlainState}
    (hnw : PlainCoreInv c F0 (withEmptyWatches c s)) {cref k1 k2 : Nat}
    (hcref : cref ∈ arenaClauseRefs s)
    (hk1 : k1 < arenaClauseSize s cref) (hk2 : k2 < arenaClauseSize s cref) :
    have hbd : cref + 3 + arenaClauseSize s cref ≤ s.arena.length := by
      have h1 : cref + 3 + arenaClauseSize s cref ≤ arenaNextOff s.arena s.arena_len cref :=
        (hnw.arena.refs_wf cref hcref).2.2.1
      have h2 : arenaNextOff s.arena s.arena_len cref ≤ s.arena_len :=
        (hnw.arena.refs_wf cref hcref).2.2.2.1
      have h3 : s.arena_len ≤ c.arena_cap := hnw.lengths.arena_len_le
      have h4 : s.arena.length = c.arena_cap := hnw.lengths.arena_len_arr
      omega
    let l1 := s.arena[cref + 3 + k1]'(by omega)
    let l2 := s.arena[cref + 3 + k2]'(by omega)
    let s' : PlainState :=
      { s with arena := (s.arena.set (cref + 3 + k1) l2).set (cref + 3 + k2) l1 }
    PlainCoreInv c F0 (withEmptyWatches c s') ∧
    arenaClauseRefs s' = arenaClauseRefs s ∧
    (∀ r ∈ arenaClauseRefs s, arenaClauseSize s' r = arenaClauseSize s r ∧
      arenaClauseGarb s' r = arenaClauseGarb s r ∧
      ∀ l, l ∈ arenaClauseLits s' r ↔ l ∈ arenaClauseLits s r) := by
  intro hbd l1 l2 s'
  have h1lt : cref + 1 < s.arena.length := by omega
  have hsw := arena_swap_preserves_nw hnw (cref := cref) (k1 := k1) (k2 := k2)
    (srch := s.arena[cref + 1]'h1lt) hcref hk1 hk2
  have heq : s.arena.set (cref + 1) (s.arena[cref + 1]'h1lt) = s.arena :=
    List.set_getElem_self h1lt
  simpa only [heq] using hsw

/-- Every literal of live clause `cref` is `other` or falsified when `ar[cref+3] = other`,
`ar[cref+4] = not_lit` (falsified), and `plain_find_repl` found no replacement in `2 ..< sz`. -/
theorem clause_falsified_of_find_repl_none {c : PlainCfg} {F0 : CNF Nat} {st : PlainState}
    {cref not_lit other : Nat}
    (hnw : PlainCoreInv c F0 (withEmptyWatches c st))
    (hcref : cref ∈ arenaClauseRefs st) (hng : arenaClauseGarb st cref = false)
    (hbd : cref + 3 + arenaClauseSize st cref ≤ st.arena.length)
    (hother_at : (st.arena[cref + 3]'(by
      have h3 : 3 ≤ arenaClauseSize st cref := (hnw.arena.refs_wf cref hcref).2.1; omega)).toNat =
      other)
    (hnot_at : (st.arena[cref + 4]'(by
      have h3 : 3 ≤ arenaClauseSize st cref := (hnw.arena.refs_wf cref hcref).2.1; omega)).toNat =
      not_lit)
    (hnot_false : st.vals[not_lit]?.getD 0#8 = 0xFF#8)
    (hfind : ∀ k, 2 ≤ k → k < arenaClauseSize st cref → plainFindReplBad c st cref k) :
    ∀ l ∈ arenaClauseLits st cref, l = other ∨ st.vals[l]?.getD 0#8 = 0xFF#8 := by
  intro l hl
  obtain ⟨k, hk, hget⟩ := (mem_arenaClauseLits_iff hbd).mp hl
  match k with
  | 0 => exact Or.inl (by simpa using hget.symm.trans hother_at)
  | 1 =>
    have h4 : (st.arena[cref + 3 + 1]'(by omega)).toNat = not_lit := hnot_at
    exact Or.inr (by rw [← hget, h4]; exact hnot_false)
  | k' + 2 =>
    have hlt := hnw.arena.lits_lt cref hcref hng l hl
    have hf := hfind (k' + 2) (by omega) hk
    unfold plainFindReplBad at hf
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some, hget] at hf
    have hslt := hf.resolve_left (by omega)
    exact Or.inr ((i8_vals_slt0 (hnw.vals_domain l hlt)).mp hslt)

/-- Transitive trail-extension witness: pre-existing trail prefix and levels
are preserved, and every newly propagated literal is assigned at `s.cur_level`. -/
structure TrailExt (s st : PlainState) : Prop where
  te_ge : s.trail_end ≤ st.trail_end
  trl_pref : ∀ i < s.trail_end, st.trl[i]? = s.trl[i]?
  lvl_pres : ∀ i < s.trail_end,
    st.lvl[(s.trl[i]?.getD 0#32).toNat / 2]? = s.lvl[(s.trl[i]?.getD 0#32).toNat / 2]?
  new_lvl : ∀ i, s.trail_end ≤ i → i < st.trail_end →
    (st.lvl[(st.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = s.cur_level

theorem TrailExt.refl (s : PlainState) : TrailExt s s :=
  ⟨Nat.le_refl _, fun _ _ => rfl, fun _ _ => rfl, fun _ h1 h2 => by omega⟩

theorem TrailExt.trans {s s1 s2 : PlainState}
    (h1 : TrailExt s s1) (h2 : TrailExt s1 s2) (hcl : s1.cur_level = s.cur_level) :
    TrailExt s s2 := by
  refine ⟨Nat.le_trans h1.te_ge h2.te_ge,
    fun i hi => (h2.trl_pref i (by have := h1.te_ge; omega)).trans (h1.trl_pref i hi),
    fun i hi => ?_, fun i hi1 hi2 => ?_⟩
  · have hlt1 : i < s1.trail_end := by have := h1.te_ge; omega
    have htr := h1.trl_pref i hi
    have h2l := h2.lvl_pres i hlt1
    rw [htr] at h2l
    exact h2l.trans (h1.lvl_pres i hi)
  · by_cases hi : i < s1.trail_end
    · rw [h2.trl_pref i hi, h2.lvl_pres i hi]
      exact h1.new_lvl i hi1 hi
    · rw [← hcl]; exact h2.new_lvl i (by omega) hi2

theorem assign_trailExt {c : PlainCfg} {F0 : CNF Nat} {st : PlainState}
    (hnw : PlainCoreInv c F0 (withEmptyWatches c st))
    {lit rsn : BitVec 32} {phases' : List (BitVec 8)} {unfl' : BitVec 64}
    (hlit : lit.toNat < 2 * c.mv) (hun : st.vals[lit.toNat]?.getD 0#8 = 0#8) :
    let v := lit.toNat / 2
    let rsn' := if st.cur_level = 0 then 0xFFFFFFFF#32 else rsn
    let st' : PlainState :=
      { st with
        vals := (st.vals.set lit.toNat 1#8).set (lit.toNat ^^^ 1) 0xFF#8
        lvl := st.lvl.set v (BitVec.ofNat 32 st.cur_level)
        rsns := st.rsns.set v rsn'
        trl := st.trl.set st.trail_end lit
        trail_pos := st.trail_pos.set v (BitVec.ofNat 32 st.trail_end)
        trail_end := st.trail_end + 1
        unflushed := unfl'
        heur := { st.heur with phases := phases' } }
    TrailExt st st' := by
  intro v rsn' st'
  have hmv := c.hmv; unfold dimacsBound at hmv
  have hte_lt : st.trail_end < c.mv := hnw.trail_end_lt_of_unassigned hlit hun
  have hcur_lt : st.cur_level < 2 ^ 32 := by
    have h1 : st.cur_level ≤ st.trail_end := hnw.cur_level_le
    have h2 : st.trail_end ≤ c.mv := hnw.lengths.trail_end_le
    omega
  refine ⟨by dsimp [st']; omega, fun i hi => ?_, fun i hi => ?_, fun i hi1 hi2 => ?_⟩
  · dsimp [st']; exact List.getElem?_set_ne (by omega)
  · dsimp [st']
    have hnone := (hnw.vals_zero_iff hlit).mp hun
    exact List.getElem?_set_ne (Ne.symm (hnone i hi))
  · have hi_eq : i = st.trail_end := by dsimp [st'] at hi2; omega
    have htrl_l : st.trl.length = c.mv := hnw.lengths.trl_len
    have hlvl_l : st.lvl.length = c.mv := hnw.lengths.lvl_len
    subst hi_eq; dsimp [st']
    rw [List.getElem?_set_self (by omega), Option.getD_some]
    rw [List.getElem?_set_self (by omega), Option.getD_some]
    exact bv32_ofNat_toNat hcur_lt

/-- Binary-reason or large-clause-reason unit propagation via `plain_assign` preserves non-watch
`PlainCoreInv` and keeps `not_lit` falsified. -/
theorem unit_assign_preserves_nw {c : PlainCfg} {F0 : CNF Nat} {st : PlainState}
    (hnw : PlainCoreInv c F0 (withEmptyWatches c st))
    {other rsn : BitVec 32} {not_lit : Nat} {phases' : List (BitVec 8)} {unfl' : BitVec 64}
    (hother_lt : other.toNat < 2 * c.mv) (hph : phases'.length = c.mv)
    (hun : st.vals[other.toNat]?.getD 0#8 = 0#8)
    (hnot_lt : not_lit < 2 * c.mv) (hnot_false : st.vals[not_lit]?.getD 0#8 = 0xFF#8)
    (hl0 : st.cur_level = 0 → F0.EntailsClause (cnfClause [other.toNat]))
    (hrsn : st.cur_level ≠ 0 → rsn ≠ 0xFFFFFFFF#32 →
      if (rsn &&& 0x80000000#32) ≠ 0#32 then
        let ot := (rsn &&& 0x7FFFFFFF#32).toNat
        ot < 2 * c.mv ∧ F0.EntailsClause (cnfClause [other.toNat, ot]) ∧
        ∃ k < st.trail_end, (st.trl[k]?.getD 0#32).toNat = ot ^^^ 1
      else
        rsn.toNat ∈ arenaClauseRefs st ∧ arenaClauseGarb st rsn.toNat = false ∧
        ∀ q ∈ arenaClauseLits st rsn.toNat,
          q = other.toNat ∨ ∃ k < st.trail_end, (st.trl[k]?.getD 0#32).toNat = q ^^^ 1)
    (hrsn_mem : st.cur_level ≠ 0 → rsn ≠ 0xFFFFFFFF#32 → (rsn &&& 0x80000000#32) = 0#32 →
      other.toNat ∈ arenaClauseLits st rsn.toNat) :
    let v := other.toNat / 2
    let rsn' := if st.cur_level = 0 then 0xFFFFFFFF#32 else rsn
    let st' : PlainState :=
      { st with
        vals := (st.vals.set other.toNat 1#8).set (other.toNat ^^^ 1) 0xFF#8
        lvl := st.lvl.set v (BitVec.ofNat 32 st.cur_level)
        rsns := st.rsns.set v rsn'
        trl := st.trl.set st.trail_end other
        trail_pos := st.trail_pos.set v (BitVec.ofNat 32 st.trail_end)
        trail_end := st.trail_end + 1
        unflushed := unfl'
        heur := { st.heur with phases := phases' } }
    PlainCoreInv c F0 (withEmptyWatches c st') ∧ st'.vals[not_lit]?.getD 0#8 = 0xFF#8 := by
  intro v rsn' st'
  have hcore' : PlainCoreInv c F0 (withEmptyWatches c st') :=
    assign_preserves_core hnw hother_lt hph hun (by have := hnw.cur_level_le; omega)
      (fun L hL1 hLle => Or.inr (hnw.levels_inhabited L hL1 hLle)) hl0 hrsn hrsn_mem
  refine ⟨hcore', ?_⟩
  obtain ⟨i, hi, heq⟩ := (hnw.vals_false_iff not_lit hnot_lt).mp hnot_false
  have hi' : i < st.trail_end := hi
  refine (hcore'.vals_false_iff not_lit hnot_lt).mpr ⟨i, by change i < st.trail_end + 1; omega, ?_⟩
  change ((st.trl.set st.trail_end other)[i]?.getD 0#32).toNat = not_lit ^^^ 1
  rw [List.getElem?_set_ne (by omega : st.trail_end ≠ i)]
  exact heq

/-! ## 5. Mid-compaction watch-slice invariant (`SplitWatchesInv`) -/

/-- Mid-compaction watch invariant for `plain_prop_lit`: `not_lit`'s slice `[off, end_v)` is split
into valid compacted prefix `[off, q)` and valid uninspected suffix `[p, end_v)`, while all other
literals `l ≠ not_lit` retain full `WatchSliceOk` and pairwise disjointness. -/
structure SplitWatchesInv (c : PlainCfg) (F0 : CNF Nat) (st : PlainState)
    (not_lit off q p end_v : Nat) : Prop where
  layout : WatchStackLayout c st
  off_eq : watchOff st not_lit = off
  sz_eq : watchSize st not_lit = end_v - off
  sz_pos : 0 < end_v - off
  q_ge : off ≤ q
  q_le_p : q ≤ p
  p_le_end : p ≤ end_v
  other_slices : ∀ l < 2 * c.mv, l ≠ not_lit →
    WatchSliceOk c F0 st l (watchOff st l) (watchSize st l)
  kept_slice : WatchSliceOk c F0 st not_lit off (q - off)
  rem_slice : WatchSliceOk c F0 st not_lit p (end_v - p)

theorem SplitWatchesInv.init {c : PlainCfg} {F0 : CNF Nat} {s : PlainState} {not_lit : Nat}
    (hnot_lt : not_lit < 2 * c.mv)
    (hwat : WatchesInv c F0 s) (hpos : 0 < watchSize s not_lit) :
    SplitWatchesInv c F0 s not_lit (watchOff s not_lit) (watchOff s not_lit)
      (watchOff s not_lit) (watchOff s not_lit + watchSize s not_lit) :=
  { layout := hwat.layout
    off_eq := rfl
    sz_eq := by omega
    sz_pos := by omega
    q_ge := Nat.le_refl _
    q_le_p := Nat.le_refl _
    p_le_end := by omega
    other_slices := fun l hl _ => hwat.slices l hl
    kept_slice := by simp only [Nat.sub_self]; exact .empty
    rem_slice := by simpa only [Nat.add_sub_cancel_left] using hwat.slices not_lit hnot_lt }

theorem SplitWatchesInv.with_nonwatch {c : PlainCfg} {F0 : CNF Nat} {s s' : PlainState}
    {not_lit off q p end_v : Nat} (h : SplitWatchesInv c F0 s not_lit off q p end_v)
    (hwv : s'.wvec = s.wvec) (hws : s'.wstk = s.wstk) (hwl : s'.wlen = s.wlen)
    (href : arenaClauseRefs s' = arenaClauseRefs s) :
    SplitWatchesInv c F0 s' not_lit off q p end_v := by
  have hF : F0.Entails F0 := by rw [CNF.entails_def]; exact fun _ hx => hx
  have hsub : ∀ r ∈ arenaClauseRefs s, r ∈ arenaClauseRefs s' := fun _ hr => href ▸ hr
  have hwo : ∀ l, watchOff s' l = watchOff s l := fun l => by unfold watchOff; rw [hwv]
  have hwsz : ∀ l, watchSize s' l = watchSize s l := fun l => by unfold watchSize; rw [hwv]
  refine
    { layout := h.layout.with_wstk hwv hws hwl
      off_eq := by rw [hwo]; exact h.off_eq
      sz_eq := by rw [hwsz]; exact h.sz_eq
      sz_pos := h.sz_pos
      q_ge := h.q_ge
      q_le_p := h.q_le_p
      p_le_end := h.p_le_end
      other_slices := fun l hl hne => by
        rw [hwo, hwsz]
        exact (h.other_slices l hl hne).mono hF hsub fun _ _ _ => by rw [hws]
      kept_slice := h.kept_slice.mono hF hsub fun _ _ _ => by rw [hws]
      rem_slice := h.rem_slice.mono hF hsub fun _ _ _ => by rw [hws] }

theorem SplitWatchesInv.write_bin {c : PlainCfg} {F0 : CNF Nat} {st : PlainState}
    {not_lit off q p end_v : Nat} {w0 : BitVec 32}
    (h : SplitWatchesInv c F0 st not_lit off q (p + 1) end_v)
    (hnot_lt : not_lit < 2 * c.mv) (hqp : q ≤ p) (hq_lt : q < st.wstk.length)
    (hflag : (w0 &&& 0x80000000#32) ≠ 0#32)
    (hlt : (w0 &&& 0x7FFFFFFF#32).toNat < 2 * c.mv)
    (hent : F0.EntailsClause (cnfClause [not_lit, (w0 &&& 0x7FFFFFFF#32).toNat])) :
    SplitWatchesInv c F0 { st with wstk := st.wstk.set q w0 }
      not_lit off (q + 1) (p + 1) end_v := by
  have hmv := c.hmv; unfold dimacsBound at hmv
  have hne_ff : w0 ≠ 0xFFFFFFFF#32 := fun hff => by
    rw [hff] at hlt
    have hmask : (0xFFFFFFFF#32 &&& 0x7FFFFFFF#32).toNat = 0x7FFFFFFF := by decide
    omega
  have hF : F0.Entails F0 := by rw [CNF.entails_def]; exact fun _ hx => hx
  let st' : PlainState := { st with wstk := st.wstk.set q w0 }
  have hq_range : off ≤ q ∧ q < end_v := ⟨h.q_ge, by have := h.p_le_end; omega⟩
  refine
    { layout :=
        { bounds := h.layout.bounds
          pos_off := h.layout.pos_off
          disjoint := h.layout.disjoint
          no_sentinel := fun l hl k hk => by
            change (st.wstk.set q w0)[watchOff st l + k]? ≠ some 0xFFFFFFFF#32
            by_cases he : watchOff st l + k = q
            · rw [he, List.getElem?_set_self hq_lt]; simp [hne_ff]
            · rw [List.getElem?_set_ne (Ne.symm he)]; exact h.layout.no_sentinel l hl k hk }
      off_eq := h.off_eq, sz_eq := h.sz_eq, sz_pos := h.sz_pos
      q_ge := by omega, q_le_p := by omega, p_le_end := h.p_le_end
      other_slices := fun l hl hne => by
        change WatchSliceOk c F0 st' l (watchOff st l) (watchSize st l)
        by_cases hsz0 : watchSize st l = 0
        · rw [hsz0]; exact .empty
        · have hdisj := h.layout.disjoint l not_lit hl hnot_lt hne (by omega) (by
            rw [h.sz_eq]; exact h.sz_pos)
          rw [h.off_eq, h.sz_eq] at hdisj
          refine WatchSliceOk.mono (s := st) (s' := st') hF (fun _ hr => hr)
            (fun k hk1 hk2 => by
              change watchOff st l ≤ k at hk1; change k < watchOff st l + watchSize st l at hk2
              dsimp only [st']; exact List.getElem?_set_ne (by omega))
            (h.other_slices l hl hne)
      kept_slice := by
        have hsub : q + 1 - off = (q - off) + 1 := by have := h.q_ge; omega
        rw [hsub]
        refine WatchSliceOk.append_bin (s := st) (s' := st') (p' := off) (fun _ hr => hr)
          (fun k hk => by dsimp only [st']; exact List.getElem?_set_ne (by omega))
          h.kept_slice ?_ hflag hlt hent
        have hadd : off + (q - off) = q := by have := h.q_ge; omega
        dsimp only [st']; rw [hadd, List.getElem?_set_self hq_lt]
      rem_slice := WatchSliceOk.mono (s := st) (s' := st') hF (fun _ hr => hr)
        (fun k hk1 _ => by dsimp only [st']; exact List.getElem?_set_ne (by omega))
        h.rem_slice }

theorem SplitWatchesInv.write_large {c : PlainCfg} {F0 : CNF Nat} {st : PlainState}
    {not_lit off q p end_v : Nat} {w0 cref : BitVec 32}
    (h : SplitWatchesInv c F0 st not_lit off q (p + 2) end_v)
    (hnot_lt : not_lit < 2 * c.mv) (hqp : q ≤ p)
    (hq_lt : q < st.wstk.length) (hq1_lt : q + 1 < st.wstk.length)
    (hflag : (w0 &&& 0x80000000#32) = 0#32)
    (hlt : cref.toNat < 0x80000000) (href : cref.toNat ∈ arenaClauseRefs st) :
    SplitWatchesInv c F0 { st with wstk := (st.wstk.set q w0).set (q + 1) cref }
      not_lit off (q + 2) (p + 2) end_v := by
  have hne_w0 : w0 ≠ 0xFFFFFFFF#32 := fun hff => by
    rw [hff] at hflag; exact absurd hflag (by decide)
  have hne_cr : cref ≠ 0xFFFFFFFF#32 := fun hff => by
    rw [hff] at hlt
    have hffn : (0xFFFFFFFF#32).toNat = 0xFFFFFFFF := by decide
    omega
  have hF : F0.Entails F0 := by rw [CNF.entails_def]; exact fun _ hx => hx
  let st' : PlainState := { st with wstk := (st.wstk.set q w0).set (q + 1) cref }
  have hq_range : off ≤ q ∧ q + 1 < end_v := ⟨h.q_ge, by have := h.p_le_end; omega⟩
  refine
    { layout :=
        { bounds := h.layout.bounds
          pos_off := h.layout.pos_off
          disjoint := h.layout.disjoint
          no_sentinel := fun l hl k hk => by
            change ((st.wstk.set q w0).set (q + 1) cref)[watchOff st l + k]? ≠ some 0xFFFFFFFF#32
            by_cases h1 : watchOff st l + k = q + 1
            · rw [h1, List.getElem?_set_self (by simp; exact hq1_lt)]; simp [hne_cr]
            · rw [List.getElem?_set_ne (Ne.symm h1)]
              by_cases h0 : watchOff st l + k = q
              · rw [h0, List.getElem?_set_self hq_lt]; simp [hne_w0]
              · rw [List.getElem?_set_ne (Ne.symm h0)]; exact h.layout.no_sentinel l hl k hk }
      off_eq := h.off_eq, sz_eq := h.sz_eq, sz_pos := h.sz_pos
      q_ge := by omega, q_le_p := by omega, p_le_end := h.p_le_end
      other_slices := fun l hl hne => by
        change WatchSliceOk c F0 st' l (watchOff st l) (watchSize st l)
        by_cases hsz0 : watchSize st l = 0
        · rw [hsz0]; exact .empty
        · have hdisj := h.layout.disjoint l not_lit hl hnot_lt hne (by omega) (by
            rw [h.sz_eq]; exact h.sz_pos)
          rw [h.off_eq, h.sz_eq] at hdisj
          refine WatchSliceOk.mono (s := st) (s' := st') hF (fun _ hr => hr) (fun k hk1 hk2 => by
            change watchOff st l ≤ k at hk1; change k < watchOff st l + watchSize st l at hk2
            dsimp only [st']
            rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)])
            (h.other_slices l hl hne)
      kept_slice := by
        have hsub : q + 2 - off = (q - off) + 2 := by have := h.q_ge; omega
        rw [hsub]
        refine WatchSliceOk.append_large (s := st) (s' := st') (p' := off) (fun _ hr => hr)
          (fun k hk => by
            dsimp only [st']
            rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)])
          h.kept_slice ?_ ?_ hflag hlt href
        · have hadd : off + (q - off) = q := by have := h.q_ge; omega
          dsimp only [st']
          rw [hadd, List.getElem?_set_ne (by omega), List.getElem?_set_self hq_lt]
        · have hadd : off + (q - off) + 1 = q + 1 := by have := h.q_ge; omega
          dsimp only [st']; rw [hadd, List.getElem?_set_self (by simp; exact hq1_lt)]
      rem_slice := WatchSliceOk.mono (s := st) (s' := st') hF (fun _ hr => hr) (fun k hk1 _ => by
        dsimp only [st']
        rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)])
        h.rem_slice }

theorem SplitWatchesInv.after_push {c : PlainCfg} {F0 : CNF Nat} {st st' : PlainState}
    {not_lit repl off q p end_v : Nat} {w0 cref : BitVec 32} {pok : Bool}
    (h : SplitWatchesInv c F0 st not_lit off q p end_v)
    (hnot_lt : not_lit < 2 * c.mv) (hrepl_lt : repl < 2 * c.mv) (hne : repl ≠ not_lit)
    (href_eq : arenaClauseRefs st' = arenaClauseRefs st)
    (hlay' : WatchStackLayout c st')
    (hflag : (w0 &&& 0x80000000#32) = 0#32)
    (hlt : cref.toNat < 0x80000000) (href : cref.toNat ∈ arenaClauseRefs st)
    (hpres_other : ∀ l < 2 * c.mv, l ≠ repl →
      watchSize st' l = watchSize st l ∧
      ∀ k < watchSize st l, st'.wstk[watchOff st' l + k]? = st.wstk[watchOff st l + k]?)
    (hpok_t : pok = true →
      watchSize st' repl = watchSize st repl + 2 ∧
      (∀ k < watchSize st repl, st'.wstk[watchOff st' repl + k]? = st.wstk[watchOff st repl + k]?) ∧
      st'.wstk[watchOff st' repl + watchSize st repl]? = some w0 ∧
      st'.wstk[watchOff st' repl + watchSize st repl + 1]? = some cref)
    (hpok_f : pok = false →
      watchSize st' repl = watchSize st repl ∧
      ∀ k < watchSize st repl, st'.wstk[watchOff st' repl + k]? = st.wstk[watchOff st repl + k]?) :
    let off' := watchOff st' not_lit
    SplitWatchesInv c F0 st' not_lit off' (off' + (q - off)) (off' + (p - off))
      (off' + (end_v - off)) := by
  intro off'
  have hF : F0.Entails F0 := by rw [CNF.entails_def]; exact fun _ hx => hx
  have hsub : ∀ r ∈ arenaClauseRefs st, r ∈ arenaClauseRefs st' := fun _ hr => href_eq ▸ hr
  obtain ⟨hsz_not, hget_not⟩ := hpres_other not_lit hnot_lt (Ne.symm hne)
  rw [h.off_eq, h.sz_eq] at hget_not
  refine
    { layout := hlay'
      off_eq := rfl
      sz_eq := by rw [hsz_not, h.sz_eq]; omega
      sz_pos := by have := h.sz_pos; omega
      q_ge := by omega
      q_le_p := by have := h.q_ge; have := h.q_le_p; omega
      p_le_end := by have := h.q_ge; have := h.q_le_p; have := h.p_le_end; omega
      other_slices := fun l hl hln => by
        by_cases hlr : l = repl
        · subst hlr
          cases pok with
          | false =>
            obtain ⟨hsz_r, hget_r⟩ := hpok_f rfl
            rw [hsz_r]
            exact (h.other_slices l hl hln).relocate hF hsub hget_r
          | true =>
            obtain ⟨hsz_r, hget_r, hw0, hcr⟩ := hpok_t rfl
            rw [hsz_r]
            exact (h.other_slices l hl hln).append_large hsub hget_r hw0 hcr hflag hlt (hsub _ href)
        · obtain ⟨hsz_l, hget_l⟩ := hpres_other l hl hlr
          rw [hsz_l]
          exact (h.other_slices l hl hln).relocate hF hsub hget_l
      kept_slice := by
        rw [show off' + (q - off) - off' = q - off by omega]
        refine h.kept_slice.relocate hF hsub fun k hk => ?_
        exact hget_not k (by have := h.q_le_p; have := h.p_le_end; omega)
      rem_slice := by
        have hrem_len : off' + (end_v - off) - (off' + (p - off)) = end_v - p := by
          have := h.q_ge; have := h.q_le_p; have := h.p_le_end; omega
        rw [hrem_len]
        refine h.rem_slice.relocate hF hsub fun k hk => ?_
        have hk' := hget_not ((p - off) + k) (by have := h.q_ge; have := h.q_le_p; omega)
        have h1 : off' + (p - off + k) = off' + (p - off) + k := by omega
        have h2 : off + (p - off + k) = p + k := by have := h.q_ge; have := h.q_le_p; omega
        rwa [h1, h2] at hk' }

/-- Finalizing tail compaction + sentinel fill + `wvec[2 * not_lit + 1] := q_fin - off` restores
full `WatchesInv` (including `WatchStackLayout`). -/
theorem SplitWatchesInv.finish {c : PlainCfg} {F0 : CNF Nat} {st0 : PlainState}
    {not_lit off q0 p0 end_v : Nat} {wstk' : List (BitVec 32)} {wu' : BitVec 64}
    (h : SplitWatchesInv c F0 st0 not_lit off q0 p0 end_v)
    (hnot_lt : not_lit < 2 * c.mv) (hwv_len : st0.wvec.length = 4 * c.mv)
    (hwcap : c.wcap < 2 * dimacsBound) (hwlen_le : st0.wlen ≤ c.wcap)
    (hkeep_pre : ∀ k, off ≤ k → k < q0 → wstk'[k]? = st0.wstk[k]?)
    (hkeep_suf : ∀ k < end_v - p0, wstk'[q0 + k]? = st0.wstk[p0 + k]?)
    (hkeep_out : ∀ k, (k < off ∨ end_v ≤ k) → wstk'[k]? = st0.wstk[k]?) :
    let q_fin := q0 + (end_v - p0)
    let st' : PlainState :=
      { st0 with
        wstk := wstk'
        wvec := st0.wvec.set (2 * not_lit + 1) (BitVec.ofNat 32 (q_fin - off))
        wusable := wu' }
    WatchesInv c F0 st' := by
  intro q_fin st'
  unfold dimacsBound at hwcap
  have hnot_bd : off + (end_v - off) ≤ st0.wlen := by
    have := h.layout.bounds not_lit hnot_lt; rwa [h.off_eq, h.sz_eq] at this
  have hqfin_le : q_fin ≤ end_v := by
    dsimp only [q_fin]; have := h.q_le_p; have := h.p_le_end; omega
  have hsz_lt32 : q_fin - off < 2 ^ 32 := by omega
  have hwo : ∀ l, watchOff st' l = watchOff st0 l := fun l => by
    unfold watchOff; dsimp only [st']
    rw [List.getElem?_set_ne (by omega)]
  have hwsz_ne : ∀ l, l ≠ not_lit → watchSize st' l = watchSize st0 l := fun l hne => by
    unfold watchSize; dsimp only [st']
    rw [List.getElem?_set_ne (by omega)]
  have hwsz_not : watchSize st' not_lit = q_fin - off := by
    unfold watchSize; dsimp only [st']
    rw [List.getElem?_set_self (by omega), Option.getD_some, bv32_ofNat_toNat hsz_lt32]
  have hF : F0.Entails F0 := by rw [CNF.entails_def]; exact fun _ hx => hx
  have hslice_not : WatchSliceOk c F0 st' not_lit off (q_fin - off) := by
    have hpre : WatchSliceOk c F0 st' not_lit off (q0 - off) :=
      WatchSliceOk.mono (s := st0) (s' := st') hF (fun _ hr => hr)
        (fun k hk1 hk2 => hkeep_pre k hk1 (by have := h.q_ge; omega)) h.kept_slice
    have hsuf : WatchSliceOk c F0 st' not_lit q0 (end_v - p0) :=
      WatchSliceOk.relocate (s := st0) (s' := st') hF (fun _ hr => hr) hkeep_suf h.rem_slice
    have hsum : q_fin - off = (q0 - off) + (end_v - p0) := by
      dsimp only [q_fin]; have := h.q_ge; omega
    have hadd : off + (q0 - off) = q0 := by have := h.q_ge; omega
    rw [hsum]; exact watchSlice_append hpre (hadd.symm ▸ hsuf)
  have hslice_all : ∀ l < 2 * c.mv, WatchSliceOk c F0 st' l (watchOff st' l) (watchSize st' l) := by
    intro l hl
    by_cases hln : l = not_lit
    · subst hln; rw [hwo, h.off_eq, hwsz_not]; exact hslice_not
    · rw [hwo, hwsz_ne l hln]
      by_cases hsz0 : watchSize st0 l = 0
      · rw [hsz0]; exact .empty
      · have hdisj := h.layout.disjoint l not_lit hl hnot_lt hln (by omega) (by
          rw [h.sz_eq]; exact h.sz_pos)
        rw [h.off_eq, h.sz_eq] at hdisj
        exact WatchSliceOk.mono (s := st0) (s' := st') hF (fun _ hr => hr)
          (fun k hk1 hk2 => hkeep_out k (by omega)) (h.other_slices l hl hln)
  have hbounds : ∀ l < 2 * c.mv, watchOff st' l + watchSize st' l ≤ st'.wlen := by
    intro l hl
    by_cases hln : l = not_lit
    · subst hln; rw [hwo, h.off_eq, hwsz_not]; dsimp only [st']; omega
    · rw [hwo, hwsz_ne l hln]; exact h.layout.bounds l hl
  refine WatchesInv.of_slices hbounds (fun l hl hp => ?_) (fun l1 l2 h1 h2 hne hp1 hp2 => ?_)
    hslice_all
  · rw [hwo]
    by_cases hln : l = not_lit
    · subst hln; exact h.layout.pos_off l hl (by rw [h.sz_eq]; exact h.sz_pos)
    · exact h.layout.pos_off l hl (by rwa [← hwsz_ne l hln])
  · rw [hwo, hwo]
    by_cases h1n : l1 = not_lit
    · subst h1n; rw [h.off_eq, hwsz_not, hwsz_ne l2 (Ne.symm hne)]
      have hd := h.layout.disjoint l1 l2 h1 h2 hne (by rw [h.sz_eq]; exact h.sz_pos)
        (by rwa [← hwsz_ne l2 (Ne.symm hne)])
      rw [h.off_eq, h.sz_eq] at hd; omega
    · by_cases h2n : l2 = not_lit
      · subst h2n; rw [h.off_eq, hwsz_not, hwsz_ne l1 h1n]
        have hd := h.layout.disjoint l1 l2 h1 h2 hne (by rwa [← hwsz_ne l1 h1n])
          (by rw [h.sz_eq]; exact h.sz_pos)
        rw [h.off_eq, h.sz_eq] at hd; omega
      · rw [hwsz_ne l1 h1n, hwsz_ne l2 h2n]
        exact h.layout.disjoint l1 l2 h1 h2 hne (by rwa [← hwsz_ne l1 h1n])
          (by rwa [← hwsz_ne l2 h2n])

/-! ## 6. `plain_prop_lit` transition, bitvector, and tail-compaction helpers -/

theorem watchSlice_inv_bin {c : PlainCfg} {F0 : CNF Nat} {st : PlainState}
    {lit p len : Nat} {w0 : BitVec 32}
    (h : WatchSliceOk c F0 st lit p len) (hlen : 0 < len)
    (hget : st.wstk[p]? = some w0) (hflag : (w0 &&& 0x80000000#32) ≠ 0#32) :
    (w0 &&& 0x7FFFFFFF#32).toNat < 2 * c.mv ∧
    F0.EntailsClause (cnfClause [lit, (w0 &&& 0x7FFFFFFF#32).toNat]) ∧
    WatchSliceOk c F0 st lit (p + 1) (len - 1) := by
  cases h with
  | empty => omega
  | bin h0 _ hlt hent hrest =>
    have hw := Option.some.inj (h0.symm.trans hget); subst hw
    exact ⟨hlt, hent, by simpa using hrest⟩
  | large h0 _ hf _ _ _ =>
    have hw := Option.some.inj (h0.symm.trans hget); subst hw
    exact absurd hf hflag

theorem watchSlice_inv_large {c : PlainCfg} {F0 : CNF Nat} {st : PlainState}
    {lit p len : Nat} {w0 : BitVec 32}
    (h : WatchSliceOk c F0 st lit p len) (hlen : 0 < len)
    (hget : st.wstk[p]? = some w0) (hflag : (w0 &&& 0x80000000#32) = 0#32) :
    2 ≤ len ∧
    ∃ cref : BitVec 32, st.wstk[p + 1]? = some cref ∧
      cref.toNat < 0x80000000 ∧ cref.toNat ∈ arenaClauseRefs st ∧
      WatchSliceOk c F0 st lit (p + 2) (len - 2) := by
  cases h with
  | empty => omega
  | bin h0 hf _ _ _ =>
    have hw := Option.some.inj (h0.symm.trans hget); subst hw
    exact absurd hflag hf
  | large h0 h1 _ hlt href hrest =>
    exact ⟨by omega, _, h1, hlt, href, by simpa using hrest⟩

theorem SplitWatchesInv.advance_rem {c : PlainCfg} {F0 : CNF Nat} {st : PlainState}
    {not_lit off q p p' end_v : Nat}
    (h : SplitWatchesInv c F0 st not_lit off q p end_v)
    (hp : p ≤ p') (hp' : p' ≤ end_v)
    (hrem' : WatchSliceOk c F0 st not_lit p' (end_v - p')) :
    SplitWatchesInv c F0 st not_lit off q p' end_v :=
  { h with q_le_p := Nat.le_trans h.q_le_p hp, p_le_end := hp', rem_slice := hrem' }

theorem cnfClause_swap2 {F0 : CNF Nat} {a b : Nat}
    (h : F0.EntailsClause (cnfClause [a, b])) : F0.EntailsClause (cnfClause [b, a]) :=
  entails_of_mem_or_false h fun l hl => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl ⊢
    rcases hl with rfl | rfl <;> simp

theorem bv32_mask7f_flag0 (x : BitVec 32) : ((x &&& 0x7FFFFFFF#32) &&& 0x80000000#32) = 0#32 := by
  ext i hi; simp only [BitVec.getElem_and, BitVec.getElem_zero]
  have h : (0x7FFFFFFF#32)[i] = false ∨ (0x80000000#32)[i] = false := by
    revert i hi; decide
  rcases h with h | h <;> simp [h]

theorem bv32_bin_rsn_props {x : BitVec 32} (hx : x.toNat < 2 ^ 31 - 1) :
    let r := (x &&& 0x7FFFFFFF#32) ||| 0x80000000#32
    r ≠ 0xFFFFFFFF#32 ∧ (r &&& 0x80000000#32) ≠ 0#32 ∧ (r &&& 0x7FFFFFFF#32).toNat = x.toNat := by
  intro r
  have hmask : x &&& 0x7FFFFFFF#32 = x := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and]
    have h7f : (0x7FFFFFFF#32).toNat = 2 ^ 31 - 1 := by decide
    rw [h7f, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (by omega)]
  have hr_and_hi : r &&& 0x80000000#32 = 0x80000000#32 := by
    ext i hi; simp only [r, BitVec.getElem_or, BitVec.getElem_and]
    by_cases h : (0x80000000#32)[i] <;> simp [h]
  have hr_and_lo : r &&& 0x7FFFFFFF#32 = x := by
    rw [← hmask]; ext i hi
    simp only [r, BitVec.getElem_or, BitVec.getElem_and]
    have h : (0x7FFFFFFF#32)[i] = false ∨ (0x80000000#32)[i] = false := by
      revert i hi; decide
    rcases h with h | h <;> simp [h]
  refine ⟨fun hff => ?_, by rw [hr_and_hi]; decide, by rw [hr_and_lo]⟩
  have hlo : (0xFFFFFFFF#32 &&& 0x7FFFFFFF#32).toNat = 2 ^ 31 - 1 := by decide
  have hx' : x.toNat = (0xFFFFFFFF#32 &&& 0x7FFFFFFF#32).toNat := by
    rw [← hr_and_lo, hff]
  omega

theorem i8_vals_eq0_of_not_pos_neg {v : BitVec 8} (hdom : v = 0#8 ∨ v = 1#8 ∨ v = 0xFF#8)
    (hnp : (0#32).slt (v.signExtend 32) = false) (hnn : (v.signExtend 32).slt 0#32 = false) :
    v = 0#8 := by
  rcases hdom with rfl | rfl | rfl
  · rfl
  · exact absurd hnp (by decide)
  · exact absurd hnn (by decide)

theorem i8_vals_ne_of_slt_false {v1 v2 : BitVec 8}
    (h1 : v1 = 0xFF#8) (h2 : (v2.signExtend 32).slt 0#32 = false) : v1 ≠ v2 := by
  intro heq; rw [← heq, h1] at h2; exact absurd h2 (by decide)

/-- Conflict/OOM witness predicate for `plain_prop_lit` (`ok = false` postcondition). -/
@[expose] def PropLitConfl (c : PlainCfg) (F0 : CNF Nat) (st : PlainState) : Prop :=
  st.oom ≠ 0#64 ∨
  (st.confl_type = 1#64 ∧ st.confl_lit0.toNat < 2 * c.mv ∧ st.confl_lit1.toNat < 2 * c.mv ∧
    F0.EntailsClause (cnfClause [st.confl_lit0.toNat, st.confl_lit1.toNat]) ∧
    st.vals[st.confl_lit0.toNat]?.getD 0#8 = 0xFF#8 ∧
    st.vals[st.confl_lit1.toNat]?.getD 0#8 = 0xFF#8) ∨
  (st.confl_type = 2#64 ∧ st.confl_ref.toNat ∈ arenaClauseRefs st ∧
    arenaClauseGarb st st.confl_ref.toNat = false ∧
    ∀ l ∈ arenaClauseLits st st.confl_ref.toNat, st.vals[l]?.getD 0#8 = 0xFF#8)

theorem PropLitConfl.congr {c : PlainCfg} {F0 : CNF Nat} {s s' : PlainState}
    (h : PropLitConfl c F0 s) (hoom : s'.oom = s.oom) (hct : s'.confl_type = s.confl_type)
    (hcr : s'.confl_ref = s.confl_ref) (hc0 : s'.confl_lit0 = s.confl_lit0)
    (hc1 : s'.confl_lit1 = s.confl_lit1) (hv : s'.vals = s.vals)
    (hal : s'.arena_len = s.arena_len) (har : s'.arena = s.arena) :
    PropLitConfl c F0 s' := by
  have href : arenaClauseRefs s' = arenaClauseRefs s := by unfold arenaClauseRefs; rw [hal, har]
  have hgb : ∀ r, arenaClauseGarb s' r = arenaClauseGarb s r := fun r => by
    unfold arenaClauseGarb arenaHdr; rw [har]
  have hlt : ∀ r, arenaClauseLits s' r = arenaClauseLits s r := fun r => by
    unfold arenaClauseLits arenaClauseSize; rw [har]
  unfold PropLitConfl at h ⊢
  rw [hoom, hct, hcr, hc0, hc1, hv, href, hgb, hlt]
  exact h

/-- Updating only watch/conflict/OOM/heuristic fields preserves `PlainCoreInv` (empty watches). -/
theorem plainCoreInv_nw_congr {c : PlainCfg} {F0 : CNF Nat} {s s' : PlainState}
    (hnw : PlainCoreInv c F0 (withEmptyWatches c s)) (hlen' : s'.LengthsOk c)
    (hal : s'.arena_len = s.arena_len) (har : s'.arena = s.arena)
    (hte : s'.trail_end = s.trail_end) (hcl : s'.cur_level = s.cur_level)
    (hv : s'.vals = s.vals) (hl : s'.lvl = s.lvl) (hr : s'.rsns = s.rsns)
    (ht : s'.trl = s.trl) (htp : s'.trail_pos = s.trail_pos) :
    PlainCoreInv c F0 (withEmptyWatches c s') := by
  have href : arenaClauseRefs (withEmptyWatches c s') = arenaClauseRefs (withEmptyWatches c s) := by
    unfold arenaClauseRefs withEmptyWatches; rw [hal, har]
  have hsz : ∀ r, arenaClauseSize (withEmptyWatches c s') r =
      arenaClauseSize (withEmptyWatches c s) r := fun r => by
    unfold arenaClauseSize withEmptyWatches; rw [har]
  have hgb : ∀ r, arenaClauseGarb (withEmptyWatches c s') r =
      arenaClauseGarb (withEmptyWatches c s) r := fun r => by
    unfold arenaClauseGarb arenaHdr withEmptyWatches; rw [har]
  have hlt : ∀ r, arenaClauseLits (withEmptyWatches c s') r =
      arenaClauseLits (withEmptyWatches c s) r := fun r => by
    unfold arenaClauseLits withEmptyWatches; rw [har]; simp only [arenaClauseSize]
  refine
    { lengths := { hlen' with wvec_len := by simp, wlen_le := Nat.zero_le _ }
      arena :=
        { len_ok := hal.symm ▸ hnw.arena.len_ok
          refs_wf := fun r hmem => by
            have := hnw.arena.refs_wf r (href ▸ hmem)
            rw [hsz r]; simpa only [withEmptyWatches, hal, har] using this
          no_shrk := fun r hmem => by
            unfold arenaHdr withEmptyWatches; rw [har]
            exact hnw.arena.no_shrk r (href ▸ hmem)
          lits_lt := fun r hmem hng l hlm =>
            hnw.arena.lits_lt r (href ▸ hmem) (hgb r ▸ hng) l (hlt r ▸ hlm)
          entails := fun r hmem hng => by
            rw [hlt r]; exact hnw.arena.entails r (href ▸ hmem) (hgb r ▸ hng) }
      watches := watchesInv_empty c F0 s'
      cur_level_le := by change s'.cur_level ≤ s'.trail_end; rw [hcl, hte]; exact hnw.cur_level_le
      trail_lits_lt := fun i hi => by
        change (s'.trl[i]?.getD 0#32).toNat < 2 * c.mv; rw [ht]
        exact hnw.trail_lits_lt i (hte ▸ hi)
      trail_vars_nodup := fun i j hi hj heq =>
        hnw.trail_vars_nodup i j (hte ▸ hi) (hte ▸ hj)
          (by simpa only [withEmptyWatches, ht] using heq)
      vals_domain := fun l hl' => by
        simpa only [withEmptyWatches, hv] using hnw.vals_domain l hl'
      vals_true_iff := fun l hl' => by
        simpa only [withEmptyWatches, hv, hte, ht] using hnw.vals_true_iff l hl'
      vals_false_iff := fun l hl' => by
        simpa only [withEmptyWatches, hv, hte, ht] using hnw.vals_false_iff l hl'
      lvl_le := fun i hi => by
        simpa only [withEmptyWatches, hl, ht, hcl] using hnw.lvl_le i (hte ▸ hi)
      trail_mono := fun i j hij hj => by
        simpa only [withEmptyWatches, hl, ht] using hnw.trail_mono i j hij (hte ▸ hj)
      levels_inhabited := fun L hL1 hLle => by
        simpa only [withEmptyWatches, hte, hl, ht] using hnw.levels_inhabited L hL1 (hcl ▸ hLle)
      level0_sound := fun i hi hl0 => by
        simpa only [withEmptyWatches, ht] using
          hnw.level0_sound i (hte ▸ hi) (by simpa only [withEmptyWatches, hl, ht] using hl0)
      trail_pos_inv := fun i hi => by
        simpa only [withEmptyWatches, ht, htp] using hnw.trail_pos_inv i (hte ▸ hi)
      level0_rsn_none := fun idx hidx hl0 => by
        simpa only [withEmptyWatches, ht, hr] using
          hnw.level0_rsn_none idx (hte ▸ hidx) (by simpa only [withEmptyWatches, hl, ht] using hl0)
      reason_inv := fun idx hidx hne => by
        have hri := hnw.reason_inv idx (hte ▸ hidx)
          (by simpa only [withEmptyWatches, ht, hr] using hne)
        dsimp only at hri ⊢
        rw [href]
        simp only [hgb, hlt]
        simp only [withEmptyWatches] at hri ⊢
        rw [ht, hr]; exact hri
      reason_lit_mem := fun idx hidx hne hlg => by
        have hrm := hnw.reason_lit_mem idx (hte ▸ hidx)
          (by simpa only [withEmptyWatches, ht, hr] using hne)
          (by simpa only [withEmptyWatches, ht, hr] using hlg)
        dsimp only at hrm ⊢
        rw [hlt]; simpa only [withEmptyWatches, ht, hr] using hrm }

/-- Binary-watch `plain_assign` transition preserving `PlainCoreInv (withEmptyWatches)` +
`TrailExt` + `not_lit` falsified. -/
theorem bin_assign_nw_step {c : PlainCfg} {F0 : CNF Nat} {st : PlainState}
    (hnw : PlainCoreInv c F0 (withEmptyWatches c st))
    {not_lit other : BitVec 32} {phases' : List (BitVec 8)} {unfl' : BitVec 64}
    (hnot_lt : not_lit.toNat < 2 * c.mv) (hother_lt : other.toNat < 2 * c.mv)
    (hph : phases'.length = c.mv) (hun : st.vals[other.toNat]?.getD 0#8 = 0#8)
    (hnot_false : st.vals[not_lit.toNat]?.getD 0#8 = 0xFF#8)
    (hent : F0.EntailsClause (cnfClause [not_lit.toNat, other.toNat])) :
    let bin_rsn := (not_lit &&& 0x7FFFFFFF#32) ||| 0x80000000#32
    let v := other.toNat / 2
    let rsn' := if st.cur_level = 0 then 0xFFFFFFFF#32 else bin_rsn
    let st' : PlainState :=
      { st with
        vals := (st.vals.set other.toNat 1#8).set (other.toNat ^^^ 1) 0xFF#8
        lvl := st.lvl.set v (BitVec.ofNat 32 st.cur_level)
        rsns := st.rsns.set v rsn'
        trl := st.trl.set st.trail_end other
        trail_pos := st.trail_pos.set v (BitVec.ofNat 32 st.trail_end)
        trail_end := st.trail_end + 1
        unflushed := unfl'
        heur := { st.heur with phases := phases' } }
    PlainCoreInv c F0 (withEmptyWatches c st') ∧ st'.vals[not_lit.toNat]?.getD 0#8 = 0xFF#8 ∧
    TrailExt st st' := by
  intro bin_rsn v rsn' st'
  have hmv := c.hmv; unfold dimacsBound at hmv
  obtain ⟨_, hflag, hlo⟩ := bv32_bin_rsn_props (x := not_lit) (by omega)
  have hcore_not := unit_assign_preserves_nw hnw (rsn := bin_rsn) (not_lit := not_lit.toNat)
    (unfl' := unfl') hother_lt hph hun hnot_lt hnot_false
    (fun hl0 => entails_of_mem_or_false hent fun l hl => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl
      · obtain ⟨i, hi, heq⟩ := (hnw.vals_false_iff not_lit.toNat hnot_lt).mp hnot_false
        have hle : (st.lvl[(st.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ st.cur_level :=
          hnw.lvl_le i hi
        have hli : (st.lvl[(st.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 := by omega
        exact Or.inr (by have hs := hnw.level0_sound i hi hli; rwa [heq] at hs)
      · exact Or.inl (by simp))
    (fun _ _ => by
      dsimp only [bin_rsn]
      simp only [hflag, ne_eq, not_false_eq_true, ↓reduceIte, hlo]
      exact ⟨hnot_lt, cnfClause_swap2 hent,
        (hnw.vals_false_iff not_lit.toNat hnot_lt).mp hnot_false⟩)
    (fun _ _ hlg => absurd hlg hflag)
  exact ⟨hcore_not.1, hcore_not.2, assign_trailExt hnw hother_lt hun⟩

/-- Large-clause `plain_assign` transition preserving `PlainCoreInv (withEmptyWatches)` +
`TrailExt` + `not_lit` falsified. -/
theorem large_assign_nw_step {c : PlainCfg} {F0 : CNF Nat} {st : PlainState}
    (hnw : PlainCoreInv c F0 (withEmptyWatches c st))
    {cref other : BitVec 32} {not_lit : Nat} {phases' : List (BitVec 8)} {unfl' : BitVec 64}
    (hcr_lt : cref.toNat < 0x80000000) (hcref : cref.toNat ∈ arenaClauseRefs st)
    (hng : arenaClauseGarb st cref.toNat = false)
    (hother_lt : other.toNat < 2 * c.mv) (hph : phases'.length = c.mv)
    (hun : st.vals[other.toNat]?.getD 0#8 = 0#8)
    (hnot_lt : not_lit < 2 * c.mv) (hnot_false : st.vals[not_lit]?.getD 0#8 = 0xFF#8)
    (hother_mem : other.toNat ∈ arenaClauseLits st cref.toNat)
    (hunit : ∀ l ∈ arenaClauseLits st cref.toNat, l = other.toNat ∨ st.vals[l]?.getD 0#8 = 0xFF#8) :
    let v := other.toNat / 2
    let rsn' := if st.cur_level = 0 then 0xFFFFFFFF#32 else cref
    let st' : PlainState :=
      { st with
        vals := (st.vals.set other.toNat 1#8).set (other.toNat ^^^ 1) 0xFF#8
        lvl := st.lvl.set v (BitVec.ofNat 32 st.cur_level)
        rsns := st.rsns.set v rsn'
        trl := st.trl.set st.trail_end other
        trail_pos := st.trail_pos.set v (BitVec.ofNat 32 st.trail_end)
        trail_end := st.trail_end + 1
        unflushed := unfl'
        heur := { st.heur with phases := phases' } }
    PlainCoreInv c F0 (withEmptyWatches c st') ∧ st'.vals[not_lit]?.getD 0#8 = 0xFF#8 ∧
    TrailExt st st' := by
  intro v rsn' st'
  have hcr_flag : (cref &&& 0x80000000#32) = 0#32 := by
    apply BitVec.eq_of_toNat_eq
    have hhi : (0x80000000#32).toNat = 2 ^ 31 := by decide
    have hlt31 : cref.toNat < 2 ^ 31 := hcr_lt
    simp only [BitVec.toNat_and, hhi, BitVec.toNat_ofNat]
    have htest : ∀ i, Nat.testBit (cref.toNat &&& 2 ^ 31) i = false := fun i => by
      rw [Nat.testBit_and, Nat.testBit_two_pow]
      by_cases hi : 31 = i
      · subst hi; simp [Nat.testBit_lt_two_pow hlt31]
      · simp [hi]
    exact Nat.eq_of_testBit_eq fun i => by simp [htest]
  have hcore_not := unit_assign_preserves_nw hnw (rsn := cref) (not_lit := not_lit)
    (unfl' := unfl') hother_lt hph hun hnot_lt hnot_false
    (fun hl0 => entails_of_mem_or_false (hnw.arena.entails cref.toNat hcref hng) fun l hl => by
      rcases hunit l hl with rfl | hfl
      · exact Or.inl (by simp)
      · have hlt := hnw.arena.lits_lt cref.toNat hcref hng l hl
        obtain ⟨i, hi, heq⟩ := (hnw.vals_false_iff l hlt).mp hfl
        have hle : (st.lvl[(st.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ st.cur_level :=
          hnw.lvl_le i hi
        have hli : (st.lvl[(st.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 := by omega
        exact Or.inr (by have hs := hnw.level0_sound i hi hli; rwa [heq] at hs))
    (fun _ _ => by
      simp only [hcr_flag, ne_eq, not_true_eq_false, ↓reduceIte]
      refine ⟨hcref, hng, fun q hq => ?_⟩
      rcases hunit q hq with rfl | hfq
      · exact Or.inl rfl
      · exact Or.inr ((hnw.vals_false_iff q (hnw.arena.lits_lt cref.toNat hcref hng q hq)).mp hfq))
    (fun _ _ _ => hother_mem)
  exact ⟨hcore_not.1, hcore_not.2, assign_trailExt hnw hother_lt hun⟩

/-- Inductive array-copy step for Loop 2 of `plain_prop_lit` (`wstk[q] = wstk[p]`). -/
theorem propLit_loop2_step {w0 wc : List (BitVec 32)} {off q0 p0 p end_v : Nat}
    (hoff_q0 : off ≤ q0) (hq0_p0 : q0 ≤ p0) (hp0_p : p0 ≤ p) (hp_end : p < end_v)
    (hp_lt : p < wc.length) (hq_lt : q0 + (p - p0) < wc.length)
    (hpre : ∀ k, off ≤ k → k < q0 → wc[k]? = w0[k]?)
    (hsuf : ∀ k < p - p0, wc[q0 + k]? = w0[p0 + k]?)
    (hrem : ∀ k, p ≤ k → k < end_v → wc[k]? = w0[k]?)
    (hout : ∀ k, (k < off ∨ end_v ≤ k) → wc[k]? = w0[k]?) :
    let wc' := wc.set (q0 + (p - p0)) (wc[p]'hp_lt)
    (∀ k, off ≤ k → k < q0 → wc'[k]? = w0[k]?) ∧
    (∀ k < p + 1 - p0, wc'[q0 + k]? = w0[p0 + k]?) ∧
    (∀ k, p + 1 ≤ k → k < end_v → wc'[k]? = w0[k]?) ∧
    (∀ k, (k < off ∨ end_v ≤ k) → wc'[k]? = w0[k]?) := by
  intro wc'
  refine ⟨fun k hk1 hk2 => (List.getElem?_set_ne (by omega)).trans (hpre k hk1 hk2),
    fun k hk => ?_,
    fun k hk1 hk2 => (List.getElem?_set_ne (by omega)).trans (hrem k (by omega) hk2),
    fun k hk => (List.getElem?_set_ne (by omega)).trans (hout k hk)⟩
  by_cases hke : k = p - p0
  · subst hke
    rw [List.getElem?_set_self hq_lt, ← List.getElem?_eq_getElem hp_lt]
    have hp_eq : p0 + (p - p0) = p := by omega
    rw [hp_eq]; exact hrem p (Nat.le_refl _) hp_end
  · exact (List.getElem?_set_ne (by omega)).trans (hsuf k (by omega))

/-- Inductive sentinel-fill step for Loop 3 of `plain_prop_lit` (`wstk[k] = 0xFFFFFFFFu`). -/
theorem propLit_loop3_step {w2 wk : List (BitVec 32)} {q_fin k end_v : Nat}
    (hq_k : q_fin ≤ k) (hk_end : k < end_v)
    (hkeep : ∀ i, (i < q_fin ∨ end_v ≤ i) → wk[i]? = w2[i]?) :
    ∀ i, (i < q_fin ∨ end_v ≤ i) → (wk.set k 0xFFFFFFFF#32)[i]? = w2[i]? := fun i hi =>
  (List.getElem?_set_ne (by omega)).trans (hkeep i hi)

@[expose] def propLitMask (h0 : PlainHeur) (t : PlainState) : PlainState :=
  { t with
    vals := [], lvl := [], rsns := [], trl := [], trail_pos := [], trail_end := 0,
    unflushed := 0#64, wvec := [], arena := [], wstk := [], wlen := 0, wusable := 0#64,
    confl_type := 0#64, confl_ref := 0#64, confl_lit0 := 0#64, confl_lit1 := 0#64,
    oom := 0#64, heur := h0 }

theorem propLit_eq_upd {h0 : PlainHeur} {s st : PlainState}
    (h : AgreesExcept (propLitMask h0) s st) :
    st = { s with
      vals := st.vals, lvl := st.lvl, rsns := st.rsns, trl := st.trl, trail_pos := st.trail_pos,
      trail_end := st.trail_end, unflushed := st.unflushed, wvec := st.wvec, arena := st.arena,
      wstk := st.wstk, wlen := st.wlen, wusable := st.wusable, confl_type := st.confl_type,
      confl_ref := st.confl_ref, confl_lit0 := st.confl_lit0, confl_lit1 := st.confl_lit1,
      oom := st.oom, heur := st.heur } := by
  have hd1 : st.d_cur = s.d_cur := h.get PlainState.d_cur
  have hd2 : st.d_val = s.d_val := h.get PlainState.d_val
  have hal : st.arena_len = s.arena_len := h.get PlainState.arena_len
  have hag : st.arena_garbage = s.arena_garbage := h.get PlainState.arena_garbage
  have hfr : st.first_reducible = s.first_reducible := h.get PlainState.first_reducible
  have hni : st.num_irred = s.num_irred := h.get PlainState.num_irred
  have hnr : st.num_redundant = s.num_redundant := h.get PlainState.num_redundant
  have hnb : st.num_binary = s.num_binary := h.get PlainState.num_binary
  have hpb : st.probing = s.probing := h.get PlainState.probing
  have hpr : st.propagated = s.propagated := h.get PlainState.propagated
  have hcl : st.cur_level = s.cur_level := h.get PlainState.cur_level
  have hfl : st.fuel = s.fuel := h.get PlainState.fuel
  have htc : st.tmp_cnt = s.tmp_cnt := h.get PlainState.tmp_cnt
  have htl : st.tmp_len = s.tmp_len := h.get PlainState.tmp_len
  have hmcl : st.min_clr_len = s.min_clr_len := h.get PlainState.min_clr_len
  have hmcf : st.min_clr_full = s.min_clr_full := h.get PlainState.min_clr_full
  have hmrk : st.mrk = s.mrk := h.get PlainState.mrk
  have htmp : st.tmp = s.tmp := h.get PlainState.tmp
  have hmstk : st.min_stk = s.min_stk := h.get PlainState.min_stk
  have hmclr : st.min_clr = s.min_clr := h.get PlainState.min_clr
  cases st; cases s; simp only at *; subst_vars; rfl

theorem PlainHeur.LengthsOk.with_ticks {c : PlainCfg} {h : PlainHeur}
    (hok : h.LengthsOk c) (t : BitVec 64) :
    ({ h with search_ticks := t } : PlainHeur).LengthsOk c :=
  { hok with heap_len_arr := hok.heap_len_arr }

theorem TrailExt.congr {s s1 s2 : PlainState} (h : TrailExt s s1)
    (hte : s2.trail_end = s1.trail_end) (htrl : s2.trl = s1.trl) (hlvl : s2.lvl = s1.lvl) :
    TrailExt s s2 :=
  ⟨hte.symm ▸ h.te_ge, fun i hi => htrl ▸ h.trl_pref i hi,
    fun i hi => hlvl ▸ h.lvl_pres i hi,
    fun i h1 h2 => by rw [htrl, hlvl]; exact h.new_lvl i h1 (hte ▸ h2)⟩

theorem bv64_add_toNat {a b : BitVec 64} (h : a.toNat + b.toNat < 2 ^ 64) :
    (a + b).toNat = a.toNat + b.toNat := by simp [BitVec.toNat_add, Nat.mod_eq_of_lt h]
theorem bv64_add1_toNat {a : BitVec 64} (h : a.toNat + 1 < 2 ^ 64) :
    (a + (1 : BitVec 64)).toNat = a.toNat + 1 := bv64_add_toNat h
theorem bv64_add2_toNat {a : BitVec 64} (h : a.toNat + 2 < 2 ^ 64) :
    (a + (2 : BitVec 64)).toNat = a.toNat + 2 := bv64_add_toNat h
theorem bv64_add3_toNat {a : BitVec 64} (h : a.toNat + 3 < 2 ^ 64) :
    (a + (3 : BitVec 64)).toNat = a.toNat + 3 := bv64_add_toNat h
theorem bv64_add4_toNat {a : BitVec 64} (h : a.toNat + 4 < 2 ^ 64) :
    (a + (4 : BitVec 64)).toNat = a.toNat + 4 := bv64_add_toNat h
theorem bv64_sub_toNat {a b : BitVec 64} (h : b.toNat ≤ a.toNat) :
    (a - b).toNat = a.toNat - b.toNat := by rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr h)]
theorem bv64_shl1_u32 (x : BitVec 32) : (x.setWidth 64 <<< 1#64).toNat = 2 * x.toNat := by
  have hx := x.isLt
  have h1 : (x.setWidth 64 <<< 1#64).toNat = ((x.setWidth 64).toNat * 2) % 2 ^ 64 := by
    simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  rw [h1, bv_c0_zext32_64, Nat.mul_comm, Nat.mod_eq_of_lt (by omega)]

/-- Loop-body invariant bundle for `plain_prop_lit`. -/
structure PropLitInv (c : PlainCfg) (F0 : CNF Nat) (s st : PlainState)
    (not_lit off q p end_v : Nat) : Prop where
  len : st.LengthsOk c
  nw : PlainCoreInv c F0 (withEmptyWatches c st)
  sw : SplitWatchesInv c F0 st not_lit off q p end_v
  ag : AgreesExcept (propLitMask s.heur) s st
  tr : TrailExt s st
  rel : st.heur.rel_trigger = s.heur.rel_trigger
  not_f : st.vals[not_lit]?.getD 0#8 = 0xFF#8

theorem PropLitInv.end_lt_wcap {c : PlainCfg} {F0 : CNF Nat} {s st : PlainState}
    {not_lit off q p end_v : Nat} (h : PropLitInv c F0 s st not_lit off q p end_v)
    (hnot_lt : not_lit < 2 * c.mv) : end_v ≤ st.wlen ∧ st.wlen ≤ c.wcap := by
  have hb := h.sw.layout.bounds not_lit hnot_lt
  rw [h.sw.off_eq, h.sw.sz_eq] at hb
  have hge := h.sw.q_ge; have hqp := h.sw.q_le_p; have hpe := h.sw.p_le_end
  exact ⟨by omega, h.len.wlen_le⟩

theorem propLit_vals_neg {c : PlainCfg} {F0 : CNF Nat} {st : PlainState} {l : Nat}
    (hnw : PlainCoreInv c F0 (withEmptyWatches c st)) (hl : l < 2 * c.mv)
    (hlt : l < st.vals.length) (hslt : ((st.vals[l]'hlt).signExtend 32).slt 0#32 = true) :
    st.vals[l]?.getD 0#8 = 0xFF#8 := by
  have hget : st.vals[l]?.getD 0#8 = st.vals[l]'hlt := by simp [List.getElem?_eq_getElem hlt]
  rw [hget]; exact (i8_vals_slt0 (by rw [← hget]; exact hnw.vals_domain l hl)).mp hslt

theorem propLit_vals_un {c : PlainCfg} {F0 : CNF Nat} {st : PlainState} {l : Nat}
    (hnw : PlainCoreInv c F0 (withEmptyWatches c st)) (hl : l < 2 * c.mv)
    (hlt : l < st.vals.length)
    (hnp : (0#32).slt ((st.vals[l]'hlt).signExtend 32) = false)
    (hnn : ((st.vals[l]'hlt).signExtend 32).slt 0#32 = false) :
    st.vals[l]?.getD 0#8 = 0#8 := by
  have hget : st.vals[l]?.getD 0#8 = st.vals[l]'hlt := by simp [List.getElem?_eq_getElem hlt]
  rw [hget]
  exact i8_vals_eq0_of_not_pos_neg (by rw [← hget]; exact hnw.vals_domain l hl) hnp hnn

theorem propLit_hunit {c : PlainCfg} {F0 : CNF Nat} {st : PlainState}
    {cref other not_lit : BitVec 32}
    (hnw : PlainCoreInv c F0 (withEmptyWatches c st))
    (hcr_ref : cref.toNat ∈ arenaClauseRefs st) (hng : arenaClauseGarb st cref.toNat = false)
    (hfit : cref.toNat + 3 + arenaClauseSize st cref.toNat ≤ st.arena.length)
    (har3 : st.arena[cref.toNat + 3]? = some other)
    (har4 : st.arena[cref.toNat + 4]? = some not_lit)
    (hnot_f : st.vals[not_lit.toNat]?.getD 0#8 = 0xFF#8)
    (hbad : ∀ k, 2 ≤ k → k < arenaClauseSize st (cref.setWidth 64).toNat →
      plainFindReplBad c st (cref.setWidth 64).toNat k) :
    ∀ l ∈ arenaClauseLits st cref.toNat, l = other.toNat ∨ st.vals[l]?.getD 0#8 = 0xFF#8 := by
  have hcr64 : (cref.setWidth 64).toNat = cref.toNat := bv_c0_zext32_64 cref
  have hcsz3 : 3 ≤ arenaClauseSize st cref.toNat := (hnw.arena.refs_wf cref.toNat hcr_ref).2.1
  have h3 : (st.arena[cref.toNat + 3]'(by omega)).toNat = other.toNat :=
    congrArg BitVec.toNat (Option.some.inj ((List.getElem?_eq_getElem (by omega)).symm.trans har3))
  have h4 : (st.arena[cref.toNat + 4]'(by omega)).toNat = not_lit.toNat :=
    congrArg BitVec.toNat (Option.some.inj ((List.getElem?_eq_getElem (by omega)).symm.trans har4))
  exact clause_falsified_of_find_repl_none hnw hcr_ref hng (by omega) h3 h4 hnot_f
    (fun k hk1 hk2 => by have hb := hbad k hk1 (by rwa [hcr64]); rwa [hcr64] at hb)

theorem propLit_inv_drop {c : PlainCfg} {F0 : CNF Nat} {s st : PlainState}
    {not_lit off q p p' end_v : Nat} {ticks' : BitVec 64}
    (hpi : PropLitInv c F0 s st not_lit off q p end_v)
    (hsw : SplitWatchesInv c F0 st not_lit off q (p + 2) end_v) (hp' : p' = p + 2) :
    PropLitInv c F0 s { st with heur := { st.heur with search_ticks := ticks' } }
      not_lit off q p' end_v :=
  let hlen1 := hpi.len.with_heur (hpi.len.heur_ok.with_ticks ticks')
  { len := hlen1
    nw := plainCoreInv_nw_congr hpi.nw hlen1 rfl rfl rfl rfl rfl rfl rfl rfl rfl
    sw := hp'.symm ▸ hsw.with_nonwatch rfl rfl rfl rfl
    ag := hpi.ag.update (fun t => { t with heur := { st.heur with search_ticks := ticks' } })
    tr := hpi.tr.congr rfl rfl rfl, rel := hpi.rel, not_f := hpi.not_f }

theorem propLit_inv_keep_large {c : PlainCfg} {F0 : CNF Nat} {s st : PlainState}
    {not_lit off p0 : Nat} {q_v p_v end_v : BitVec 64} {w0 cref : BitVec 32}
    (hpi : PropLitInv c F0 s st not_lit off q_v.toNat p0 end_v.toNat)
    (hsw : SplitWatchesInv c F0 st not_lit off q_v.toNat (p_v.toNat + 2) end_v.toNat)
    (hnot_lt : not_lit < 2 * c.mv) (hq1 : (q_v + (1 : BitVec 64)).toNat = q_v.toNat + 1)
    (hq2 : (q_v + (2 : BitVec 64)).toNat = q_v.toNat + 2)
    (hp2 : (p_v + (1 : BitVec 64) + (1 : BitVec 64)).toNat = p_v.toNat + 2)
    (hq_le : q_v.toNat + 2 ≤ p_v.toNat + 2) (hp_le : p_v.toNat + 2 ≤ end_v.toNat)
    (hflag : (w0 &&& 0x80000000#32) = 0#32)
    (hcr_lt : cref.toNat < 0x80000000) (hcr_ref : cref.toNat ∈ arenaClauseRefs st) :
    PropLitInv c F0 s
      { st with wstk := (st.wstk.set q_v.toNat w0).set (q_v + (1 : BitVec 64)).toNat cref }
      not_lit off (q_v + (2 : BitVec 64)).toNat
      (p_v + (1 : BitVec 64) + (1 : BitVec 64)).toNat end_v.toNat := by
  have hlen_w := hpi.len.wstk_len_arr
  have ⟨hend_le, hwlen_le⟩ := hpi.end_lt_wcap hnot_lt
  have hlen1 : ({ st with
      wstk := (st.wstk.set q_v.toNat w0).set (q_v + (1 : BitVec 64)).toNat cref } :
      PlainState).LengthsOk c :=
    { hpi.len with wstk_len_arr := by simp [hlen_w] }
  have hsw1 := hsw.write_large hnot_lt (by omega) (by omega) (by omega) hflag hcr_lt hcr_ref
  exact
    { len := hlen1
      nw := plainCoreInv_nw_congr hpi.nw hlen1 rfl rfl rfl rfl rfl rfl rfl rfl rfl
      sw := by rw [hp2, hq2]; exact hsw1.with_nonwatch rfl (by simp only [hq1]) rfl rfl
      ag := hpi.ag.update (fun t => { t with wstk := _ })
      tr := hpi.tr.congr rfl rfl rfl, rel := hpi.rel, not_f := hpi.not_f }

theorem propLit_bin_confl {c : PlainCfg} {F0 : CNF Nat} {s st : PlainState}
    {not_lit w0 : BitVec 32} {off_v p_v q_v end_v : BitVec 64}
    (hpi : PropLitInv c F0 s st not_lit.toNat off_v.toNat q_v.toNat p_v.toNat end_v.toNat)
    (hsw1 : SplitWatchesInv c F0 { st with wstk := st.wstk.set q_v.toNat w0 }
      not_lit.toNat off_v.toNat (q_v.toNat + 1) (p_v.toNat + 1) end_v.toNat)
    (hnot_lt : not_lit.toNat < 2 * c.mv)
    (hother_lt : (w0 &&& 0x7FFFFFFF#32).toNat < 2 * c.mv)
    (hent : F0.EntailsClause (cnfClause [not_lit.toNat, (w0 &&& 0x7FFFFFFF#32).toNat]))
    (hov_f : st.vals[(w0 &&& 0x7FFFFFFF#32).toNat]?.getD 0#8 = 0xFF#8)
    (hp1 : (p_v + 1#64).toNat = p_v.toNat + 1) (hq1 : (q_v + 1#64).toNat = q_v.toNat + 1) :
    let other := w0 &&& 0x7FFFFFFF#32
    let st1 : PlainState :=
      { st with
        wstk := st.wstk.set q_v.toNat w0, confl_type := 1#64,
        confl_lit0 := not_lit.setWidth 64, confl_lit1 := other.setWidth 64,
        confl_ref := 0xFFFFFFFF#64 }
    PropLitInv c F0 s st1 not_lit.toNat off_v.toNat (q_v + 1#64).toNat (p_v + 1#64).toNat
      end_v.toNat ∧ PropLitConfl c F0 st1 := by
  intro other st1
  have hlen1 : st1.LengthsOk c :=
    { hpi.len with wstk_len_arr := by simp [st1, hpi.len.wstk_len_arr] }
  refine ⟨{ len := hlen1
            nw := plainCoreInv_nw_congr hpi.nw hlen1 rfl rfl rfl rfl rfl rfl rfl rfl rfl
            sw := by rw [hp1, hq1]; exact hsw1.with_nonwatch rfl rfl rfl rfl
            ag := hpi.ag.update (fun t => { t with
              wstk := st1.wstk, confl_type := 1#64, confl_lit0 := not_lit.setWidth 64,
              confl_lit1 := other.setWidth 64, confl_ref := 0xFFFFFFFF#64 })
            tr := hpi.tr.congr rfl rfl rfl, rel := hpi.rel, not_f := hpi.not_f },
    Or.inr (Or.inl ⟨rfl,
      by change (not_lit.setWidth 64).toNat < _; rw [bv_c0_zext32_64]; exact hnot_lt,
      by change (other.setWidth 64).toNat < _; rw [bv_c0_zext32_64]; exact hother_lt,
      by change F0.EntailsClause
           (cnfClause [(not_lit.setWidth 64).toNat, (other.setWidth 64).toNat])
         rw [bv_c0_zext32_64, bv_c0_zext32_64]; exact hent,
      by change st.vals[(not_lit.setWidth 64).toNat]?.getD 0#8 = 0xFF#8
         rw [bv_c0_zext32_64]; exact hpi.not_f,
      by change st.vals[(other.setWidth 64).toNat]?.getD 0#8 = 0xFF#8
         rw [bv_c0_zext32_64]; exact hov_f⟩)⟩

theorem propLit_large_confl {c : PlainCfg} {F0 : CNF Nat} {s st1 : PlainState}
    {not_lit other cref : BitVec 32} {off_v p_v q_v end_v : BitVec 64}
    (hpi1 : PropLitInv c F0 s st1 not_lit.toNat off_v.toNat q_v.toNat (p_v.toNat + 2) end_v.toNat)
    (hnot_lt : not_lit.toNat < 2 * c.mv) (hq_le : q_v.toNat ≤ p_v.toNat)
    (hq1 : (q_v + (1 : BitVec 64)).toNat = q_v.toNat + 1)
    (hq2 : (q_v + (2 : BitVec 64)).toNat = q_v.toNat + 2)
    (hp2 : (p_v + (1 : BitVec 64) + (1 : BitVec 64)).toNat = p_v.toNat + 2)
    (hcr_lt : cref.toNat < 0x80000000) (hcr_ref : cref.toNat ∈ arenaClauseRefs st1)
    (hng : arenaClauseGarb st1 cref.toNat = false)
    (hov_f : st1.vals[other.toNat]?.getD 0#8 = 0xFF#8)
    (hunit : ∀ l ∈ arenaClauseLits st1 cref.toNat,
      l = other.toNat ∨ st1.vals[l]?.getD 0#8 = 0xFF#8) :
    let st2 : PlainState :=
      { st1 with
        wstk := (st1.wstk.set q_v.toNat (other &&& 0x7FFFFFFF#32)).set
          (q_v + (1 : BitVec 64)).toNat cref
        confl_type := 2#64, confl_ref := cref.setWidth 64 }
    PropLitInv c F0 s st2 not_lit.toNat off_v.toNat (q_v + (2 : BitVec 64)).toNat
      (p_v + (1 : BitVec 64) + (1 : BitVec 64)).toNat end_v.toNat ∧ PropLitConfl c F0 st2 := by
  intro st2
  have hcr64 : (cref.setWidth 64).toNat = cref.toNat := bv_c0_zext32_64 cref
  have hlen_w := hpi1.len.wstk_len_arr
  have ⟨hend_le, hwlen_le⟩ := hpi1.end_lt_wcap hnot_lt
  have hlen2 : st2.LengthsOk c := { hpi1.len with wstk_len_arr := by simp [st2, hlen_w] }
  have hp_le := hpi1.sw.p_le_end
  have hsw2 := hpi1.sw.write_large hnot_lt hq_le (by omega) (by omega)
    (bv32_mask7f_flag0 other) hcr_lt hcr_ref
  refine ⟨{ len := hlen2
            nw := plainCoreInv_nw_congr hpi1.nw hlen2 rfl rfl rfl rfl rfl rfl rfl rfl rfl
            sw := by rw [hp2, hq2]; exact hsw2.with_nonwatch rfl (by simp only [st2, hq1]) rfl rfl
            ag := hpi1.ag.update (fun t => { t with
              wstk := st2.wstk, confl_type := 2#64, confl_ref := cref.setWidth 64 })
            tr := hpi1.tr.congr rfl rfl rfl, rel := hpi1.rel, not_f := hpi1.not_f },
    Or.inr (Or.inr ⟨rfl, by change (cref.setWidth 64).toNat ∈ _; rwa [hcr64],
      by change arenaClauseGarb st1 (cref.setWidth 64).toNat = false; rwa [hcr64], fun l hl => by
        change st1.vals[l]?.getD 0#8 = 0xFF#8
        have hl' : l ∈ arenaClauseLits st1 cref.toNat := by
          change l ∈ arenaClauseLits st1 (cref.setWidth 64).toNat at hl; rwa [hcr64] at hl
        rcases hunit l hl' with rfl | hfl; exact hov_f; exact hfl⟩)⟩

end LeanQbe.T.Examples.Kissat.Plain
