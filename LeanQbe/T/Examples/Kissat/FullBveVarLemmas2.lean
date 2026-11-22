module

public import LeanQbe.T.Examples.Kissat.FullBveVarLemmas1

/-!
# Kissat `D-Full` UNSAT-Only BVE Top-Shard Proofs — Part 2 (`Stage 4`)

Provides:
1. BCE geometry preservation helpers across `PH_GARB` marking (`FullBveTryBceEntryOk`,
   `FullBveTryBceOppOk`) and `FullBveEntryOkW.ext_need_bound`.
2. Parametric `(Γ : Env)` `Func.wp` proof for `full_bve_ext_need` (`full_bve_ext_need_wp`).
3. Parametric `(Γ : Env)` `Func.wp` proof for `full_bve_commit_res` (`full_bve_commit_res_wp`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Full

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open Kraken.Bedrock2.Test

open FullBveVarTactics FullBveVarSpecs FullBveVarHelpers
open scoped FullArenaTactics FullBveVarTactics

/-! ## 1. BCE geometry preservation & `ext_need` bounds (`FullBveVarHelpers`) -/

namespace FullBveVarHelpers

theorem FullBveTryBceEntryOk.of_arena_set_hdr {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hlen : s.LengthsOk c)
    (hw : FullWitnessInv c F0 F_cur s.core) {cref : Nat} (href : cref ∈ fullArenaClauseRefs s)
    (ag' : BitVec 64) {w : BitVec 32} (h : FullBveTryBceEntryOk c s w) :
    let s' : FullState :=
      { s with core :=
        { s.core with
          arena := s.core.arena.set cref (fullArenaHdr s cref ||| 0x00080000#32)
          arena_garbage := ag' } }
    FullBveTryBceEntryOk c s' w := by
  intro s'
  unfold FullBveTryBceEntryOk at h ⊢
  by_cases hb : (w &&& 0x80000000#32) ≠ 0#32
  · simp [hb] at h ⊢; exact h
  · simp only [hb, ↓reduceIte] at h ⊢
    have hmg := hw.arena.markGarb hlen.core_ok href ag'
    have hr' : w.toNat ∈ fullArenaClauseRefsCore s'.core := by rw [hmg.1]; exact h.1
    have hdisj : (w.toNat = cref) ∨
        (w.toNat + 3 + fullArenaClauseSizeCore s.core w.toNat ≤ cref ∨ cref + 3 ≤ w.toNat) := by
      by_cases heq : w.toNat = cref
      · exact Or.inl heq
      · right; rcases Nat.lt_or_gt_of_ne heq with hlt | hgt
        · exact Or.inl (hw.arena.disjoint h.1 href hlt)
        · exact Or.inr (by have := hw.arena.disjoint href h.1 hgt; omega)
    have hsz_eq :
        fullArenaClauseSizeCore s'.core w.toNat = fullArenaClauseSizeCore s.core w.toNat := by
      unfold fullArenaClauseSizeCore s'
      rcases hdisj with rfl | h1 | h2
      · rw [List.getElem?_set_ne (by omega)]
      · have := (hw.arena.refs_wf w.toNat h.1).2.1; rw [List.getElem?_set_ne (by omega)]
      · rw [List.getElem?_set_ne (by omega)]
    have hlits_eq :
        fullArenaClauseLitsCore s'.core w.toNat = fullArenaClauseLitsCore s.core w.toNat := by
      have har_len : s.core.arena_len ≤ s.core.arena.length := by
        have := hlen.core_ok.arena_len_le; have := hlen.core_ok.arena_len_arr; omega
      have hwf := hw.arena.refs_wf w.toNat h.1
      have hbd : w.toNat + 3 + fullArenaClauseSizeCore s.core w.toNat ≤ s.core.arena.length := by
        omega
      refine fullArenaClauseLitsCore_eq_of_hold hbd (by simpa [s'] using hbd) hsz_eq ?_
      intro j hj; dsimp only [s']; apply List.getElem?_set_ne
      rcases hdisj with rfl | h1 | h2 <;> omega
    change w.toNat ∈ fullArenaClauseRefsCore s'.core ∧
      w.toNat + 3 + fullArenaClauseSizeCore s'.core w.toNat ≤ s'.core.arena_len ∧
      (∀ l ∈ fullArenaClauseLitsCore s'.core w.toNat, l < 2 * c.max_vars) ∧
      ((fullArenaClauseLitsCore s'.core w.toNat).map (· / 2)).Nodup
    rw [hsz_eq, hlits_eq]; exact ⟨hr', h.2.1, h.2.2.1, h.2.2.2⟩

theorem FullBveTryBceOppOk.of_arena_set_hdr {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hlen : s.LengthsOk c)
    (hw : FullWitnessInv c F0 F_cur s.core) {cref : Nat} (href : cref ∈ fullArenaClauseRefs s)
    (ag' : BitVec 64) {w : BitVec 32} (h : FullBveTryBceOppOk c s w) :
    let s' : FullState :=
      { s with core :=
        { s.core with
          arena := s.core.arena.set cref (fullArenaHdr s cref ||| 0x00080000#32)
          arena_garbage := ag' } }
    FullBveTryBceOppOk c s' w := by
  intro s'
  unfold FullBveTryBceOppOk at h ⊢
  by_cases hb : (w &&& 0x80000000#32) ≠ 0#32
  · simp [hb] at h ⊢; exact h
  · simp only [hb, ↓reduceIte] at h ⊢
    have hmg := hw.arena.markGarb hlen.core_ok href ag'
    have hr' : w.toNat ∈ fullArenaClauseRefsCore s'.core := by rw [hmg.1]; exact h.1
    have hdisj : (w.toNat = cref) ∨
        (w.toNat + 3 + fullArenaClauseSizeCore s.core w.toNat ≤ cref ∨ cref + 3 ≤ w.toNat) := by
      by_cases heq : w.toNat = cref
      · exact Or.inl heq
      · right; rcases Nat.lt_or_gt_of_ne heq with hlt | hgt
        · exact Or.inl (hw.arena.disjoint h.1 href hlt)
        · exact Or.inr (by have := hw.arena.disjoint href h.1 hgt; omega)
    have hsz_eq :
        fullArenaClauseSizeCore s'.core w.toNat = fullArenaClauseSizeCore s.core w.toNat := by
      unfold fullArenaClauseSizeCore s'
      rcases hdisj with rfl | h1 | h2
      · rw [List.getElem?_set_ne (by omega)]
      · have := (hw.arena.refs_wf w.toNat h.1).2.1; rw [List.getElem?_set_ne (by omega)]
      · rw [List.getElem?_set_ne (by omega)]
    have hlits_eq :
        fullArenaClauseLitsCore s'.core w.toNat = fullArenaClauseLitsCore s.core w.toNat := by
      have har_len : s.core.arena_len ≤ s.core.arena.length := by
        have := hlen.core_ok.arena_len_le; have := hlen.core_ok.arena_len_arr; omega
      have hwf := hw.arena.refs_wf w.toNat h.1
      have hbd : w.toNat + 3 + fullArenaClauseSizeCore s.core w.toNat ≤ s.core.arena.length := by
        omega
      refine fullArenaClauseLitsCore_eq_of_hold hbd (by simpa [s'] using hbd) hsz_eq ?_
      intro j hj; dsimp only [s']; apply List.getElem?_set_ne
      rcases hdisj with rfl | h1 | h2 <;> omega
    change w.toNat ∈ fullArenaClauseRefsCore s'.core ∧
      w.toNat + 3 + fullArenaClauseSizeCore s'.core w.toNat ≤ s'.core.arena_len ∧
      (∀ l ∈ fullArenaClauseLitsCore s'.core w.toNat, l < 2 * c.max_vars)
    rw [hsz_eq, hlits_eq]; exact ⟨hr', h.2.1, h.2.2⟩

theorem FullBveTryBceEntryOk.with_same_arena {c : FullCfg} {s s' : FullState}
    (har : s'.core.arena = s.core.arena) (hal : s'.core.arena_len = s.core.arena_len)
    {w : BitVec 32} (h : FullBveTryBceEntryOk c s w) : FullBveTryBceEntryOk c s' w := by
  have hrefs : fullArenaClauseRefsCore s'.core = fullArenaClauseRefsCore s.core := by
    unfold fullArenaClauseRefsCore; rw [har, hal]
  have hsz : fullArenaClauseSizeCore s'.core w.toNat = fullArenaClauseSizeCore s.core w.toNat := by
    unfold fullArenaClauseSizeCore; rw [har]
  have hlits :
      fullArenaClauseLitsCore s'.core w.toNat = fullArenaClauseLitsCore s.core w.toNat := by
    unfold fullArenaClauseLitsCore; rw [har, hsz]
  unfold FullBveTryBceEntryOk fullArenaClauseRefs fullArenaClauseSize fullArenaClauseLits at h ⊢
  by_cases hb : (w &&& 0x80000000#32) ≠ 0#32
  · simp [hb] at h ⊢; exact h
  · simp only [hb, ↓reduceIte] at h ⊢; rw [hrefs, hsz, hlits, hal]; exact h

theorem FullBveTryBceOppOk.with_same_arena {c : FullCfg} {s s' : FullState}
    (har : s'.core.arena = s.core.arena) (hal : s'.core.arena_len = s.core.arena_len)
    {w : BitVec 32} (h : FullBveTryBceOppOk c s w) : FullBveTryBceOppOk c s' w := by
  have hrefs : fullArenaClauseRefsCore s'.core = fullArenaClauseRefsCore s.core := by
    unfold fullArenaClauseRefsCore; rw [har, hal]
  have hsz : fullArenaClauseSizeCore s'.core w.toNat = fullArenaClauseSizeCore s.core w.toNat := by
    unfold fullArenaClauseSizeCore; rw [har]
  have hlits :
      fullArenaClauseLitsCore s'.core w.toNat = fullArenaClauseLitsCore s.core w.toNat := by
    unfold fullArenaClauseLitsCore; rw [har, hsz]
  unfold FullBveTryBceOppOk fullArenaClauseRefs fullArenaClauseSize fullArenaClauseLits at h ⊢
  by_cases hb : (w &&& 0x80000000#32) ≠ 0#32
  · simp [hb] at h ⊢; exact h
  · simp only [hb, ↓reduceIte] at h ⊢; rw [hrefs, hsz, hlits, hal]; exact h

theorem FullBveEntryOkW.ext_need_bound {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s) {lit : Nat} {w : BitVec 32}
    (he : FullBveEntryOkW F_cur s lit w) :
    (w &&& 0x80000000#32) ≠ 0#32 ∨ w.toNat + 2 < c.arena_cap := by
  by_cases hb : (w &&& 0x80000000#32) ≠ 0#32
  · exact Or.inl hb
  · right; unfold FullBveEntryOkW at he; simp only [hb, ↓reduceIte] at he
    have hwf := h.2.1.arena.refs_wf w.toNat he.1
    have harle := h.1.core_ok.arena_len_le
    omega

theorem bv32_shl1_toNat {v : BitVec 32} (hv : 2 * v.toNat < 2 ^ 32) :
    (v <<< (BitVec.toNat (1 : BitVec 32) % 32)).toNat = 2 * v.toNat := by
  rw [show BitVec.toNat (1 : BitVec 32) % 32 = 1 from rfl,
    BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm, Nat.mod_eq_of_lt hv]

theorem bv32_or1_even_toNat {pl : BitVec 32} {n : Nat} (hp : pl.toNat = 2 * n) :
    (pl ||| 1#32).toNat = 2 * n + 1 := by
  rw [BitVec.toNat_or, show (1#32 : BitVec 32).toNat = 1 from rfl, hp]
  apply Nat.eq_of_testBit_eq
  intro k; rw [Nat.testBit_or]
  cases k with
  | zero => simp [Nat.testBit_zero]
  | succ k =>
    rw [Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_succ,
      show 2 * n / 2 = n by omega, show (1 : Nat) / 2 = 0 from rfl,
      show (2 * n + 1) / 2 = n by omega, Nat.zero_testBit, Bool.or_false]

theorem fullBveWeakItemOk_of_pres {s s' : FullState} {w : BitVec 32}
    (hcv : s'.core.cur_vars = s.core.cur_vars)
    (hrefs : fullArenaClauseRefs s' = fullArenaClauseRefs s)
    (h : FullBveWeakItemOk s w) : FullBveWeakItemOk s' w := by
  unfold FullBveWeakItemOk at h ⊢
  by_cases hb : (w &&& 0x80000000#32) ≠ 0#32
  · simp [hb] at h ⊢; omega
  · simp [hb] at h ⊢; rwa [hrefs]

theorem entries_to_extNeed {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s) {lit off cnt : Nat}
    (hok : ∀ i < cnt, FullBveEntryOkW F_cur s lit
      (s.scratch.scratch_buf[off + i]?.getD 0#32)) :
    ∀ i < cnt,
      let w := s.scratch.scratch_buf[off + i]?.getD 0#32
      (w &&& 0x80000000#32) ≠ 0#32 ∨ w.toNat + 2 < c.arena_cap :=
  fun i hi => FullBveEntryOkW.ext_need_bound h (hok i hi)

theorem range_map_eq_take_map {scr tmp : List (BitVec 32)} {rp tl : Nat}
    (htl : tl ≤ tmp.length) (hcp : ∀ k < tl, scr[rp + 1 + k]? = tmp[k]?) :
    (List.range tl).map (fun k => (scr[rp + 1 + k]?.getD 0#32).toNat) =
      (tmp.take tl).map BitVec.toNat := by
  apply List.ext_getElem
  · simp [List.length_take, Nat.min_eq_left htl]
  · intro j hj1 _
    simp only [List.getElem_map, List.getElem_range, List.getElem_take]
    have hj : j < tl := by simpa using hj1
    rw [hcp j hj, List.getElem?_eq_getElem (by omega), Option.getD_some]

theorem range_map_div2_eq_take_map {scr tmp : List (BitVec 32)} {rp tl : Nat}
    (htl : tl ≤ tmp.length) (hcp : ∀ k < tl, scr[rp + 1 + k]? = tmp[k]?) :
    (List.range tl).map (fun k => (scr[rp + 1 + k]?.getD 0#32).toNat / 2) =
      (tmp.take tl).map (fun x => x.toNat / 2) := by
  have hm := congrArg (List.map (· / 2)) (range_map_eq_take_map htl hcp)
  simpa only [List.map_map, Function.comp_def] using hm

theorem full_bve_entries_pres {F_cur : List (List Nat)} {s s' : FullState}
    {lit off cnt : Nat}
    (hvars : s.core.cur_vars ≤ s'.core.cur_vars)
    (har : s'.core.arena = s.core.arena) (hal : s'.core.arena_len = s.core.arena_len)
    {scr0 : List (BitVec 32)} (hbuf : ∀ idx < off + cnt, s'.scratch.scratch_buf[idx]? = scr0[idx]?)
    (hok : ∀ i < cnt, FullBveEntryOkW F_cur s lit (scr0[off + i]?.getD 0#32)) :
    ∀ i < cnt, FullBveEntryOkW F_cur s' lit
      (s'.scratch.scratch_buf[off + i]?.getD 0#32) := by
  intro i hi
  rw [hbuf (off + i) (by omega)]
  exact FullBveEntryOkW.with_state hvars har hal (hok i hi)

theorem full_bve_tryBce_pres {c : FullCfg} {s s' : FullState} {np nn : Nat}
    (har : s'.core.arena = s.core.arena) (hal : s'.core.arena_len = s.core.arena_len)
    {scr0 : List (BitVec 32)}
    (hp : ∀ i < np, FullBveTryBceEntryOk c s (scr0[i]?.getD 0#32))
    (hn : ∀ j < nn, FullBveTryBceOppOk c s (scr0[64 + j]?.getD 0#32)) :
    (∀ i < np, FullBveTryBceEntryOk c s' (scr0[i]?.getD 0#32)) ∧
    (∀ j < nn, FullBveTryBceOppOk c s' (scr0[64 + j]?.getD 0#32)) :=
  ⟨fun i hi => FullBveTryBceEntryOk.with_same_arena har hal (hp i hi),
   fun j hj => FullBveTryBceOppOk.with_same_arena har hal (hn j hj)⟩

theorem full_bve_tryBce_of_markGarb {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hlen : s.LengthsOk c) (hw : FullWitnessInv c F0 F_cur s.core)
    {cref : Nat} (href : cref ∈ fullArenaClauseRefs s) (ag' : BitVec 64) {np nn : Nat}
    {scr0 : List (BitVec 32)}
    (hp : ∀ i < np, FullBveTryBceEntryOk c s (scr0[i]?.getD 0#32))
    (hn : ∀ j < nn, FullBveTryBceOppOk c s (scr0[64 + j]?.getD 0#32)) :
    let s' : FullState :=
      { s with core :=
        { s.core with
          arena := s.core.arena.set cref (fullArenaHdr s cref ||| 0x00080000#32)
          arena_garbage := ag' } }
    (∀ i < np, FullBveTryBceEntryOk c s' (scr0[i]?.getD 0#32)) ∧
    (∀ j < nn, FullBveTryBceOppOk c s' (scr0[64 + j]?.getD 0#32)) :=
  ⟨fun i hi => FullBveTryBceEntryOk.of_arena_set_hdr hlen hw href ag' (hp i hi),
   fun j hj => FullBveTryBceOppOk.of_arena_set_hdr hlen hw href ag' (hn j hj)⟩

theorem denseInvW_of_extPush {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s s' : FullState} (h : FullDenseInvW c F0 F_cur s) (hlen' : s'.LengthsOk c)
    (hcore : PreservesCoreSlice (fullSafetySlice c).coreProj s s')
    (hll : s'.scratch.last_learned = s.scratch.last_learned)
    (hext : s'.scratch.extend_len ≤ c.extend_cap) : FullDenseInvW c F0 F_cur s' := by
  have heq : s'.core = s.core := fullCoreState_agrees_with_scratch hcore
  refine ⟨hlen', heq ▸ h.2.1, ?_, ?_, ?_, heq ▸ h.2.2.2.2.2.1, heq ▸ h.2.2.2.2.2.2⟩
  · unfold FullLitMarksClear FullMrkZero; rw [heq]; exact h.2.2.1
  · unfold FullArenaVarsNodup fullArenaClauseRefs fullArenaClauseGarb fullArenaClauseLits
    rw [heq]; exact h.2.2.2.1
  · exact ⟨FullLastLearnedWf.of_refs_subset h.2.2.2.2.1.1 hll fun r hr => by
      unfold fullArenaClauseRefs; rwa [heq], hext⟩

end FullBveVarHelpers

/-! ## 2. `Func.wp` Proof: `full_bve_ext_need` -/

theorem full_bve_ext_need_wp (Γ : Env) :
    ∀ args m Q X, fullBveExtNeedSpec args m Q X → Func.wp Γ full_bve_ext_need_body args m Q X := by
  rintro ⟨h, off, cnt, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hcnt, hok, hm, hQ⟩
  have harc := c.harena; have hsc := c.hscr; unfold dimacsBound at harc hsc
  have hscrl := hlen.scratch_ok.scratch_buf_len
  have harl := hlen.core_ok.arena_len_arr
  unfold Func.wp full_bve_ext_need_body
  bve_steps!
  refine wp_loop_inv (ts := [i64, i32])
    (fun (need, i, _) ml => i.toNat ≤ cnt.toNat ∧ ml = m)
    (fun (_, i, _) _ => cnt.toNat - i.toNat)
    (fun J hJ => by
      bve_steps!
      exact hJ (0#64, 0#32, PUnit.unit) m ⟨Nat.zero_le _, rfl⟩)
    (fun J ⟨need, i, ⟨⟩⟩ ml ⟨hi_le, rfl⟩ ih => by
      bve_steps
      · have hi_lt : i.toNat < cnt.toNat := by bv_omega
        exact ih (need + 2#64, i + 1#32, PUnit.unit) ml (by bv_omega) ⟨by bv_omega, rfl⟩
      · have hi_lt : i.toNat < cnt.toNat := by bv_omega
        have hoff_nat : (BitVec.setWidth 64 (off + i)).toNat = off.toNat + i.toNat := by bv_omega
        have hscr_idx : (BitVec.setWidth 64 (off + i)).toNat < s.scratch.scratch_buf.length := by
          omega
        have hnb : ¬ (s.scratch.scratch_buf[(BitVec.setWidth 64 (off + i)).toNat]'hscr_idx &&&
            0x80000000#32) ≠ 0#32 := by
          have h0 : (s.scratch.scratch_buf[(BitVec.setWidth 64 (off + i)).toNat]'hscr_idx &&&
              0x80000000#32) = 0#32 := by assumption
          exact fun h => h h0
        have hw_eq : s.scratch.scratch_buf[(BitVec.setWidth 64 (off + i)).toNat]'hscr_idx =
            s.scratch.scratch_buf[off.toNat + i.toNat]?.getD 0#32 := by
          rw [List.getElem?_eq_getElem (by omega : off.toNat + i.toNat <
            s.scratch.scratch_buf.length), Option.getD_some]
          simp only [hoff_nat]
        have hbd :
            (s.scratch.scratch_buf[(BitVec.setWidth 64 (off + i)).toNat]'hscr_idx).toNat + 2 <
              c.arena_cap := by
          rcases hok i.toNat hi_lt with hb | hbd
          · exact absurd (by simpa [← hw_eq] using hb) hnb
          · rw [hw_eq]; exact hbd
        have har_idx : (BitVec.setWidth 64
            (s.scratch.scratch_buf[(BitVec.setWidth 64 (off + i)).toNat]'hscr_idx) + 2#64).toNat <
            s.core.arena.length := by bv_omega
        bve_steps!
        exact ih _ ml (by bv_omega) ⟨by bv_omega, rfl⟩
      · exact hQ need)

/-! ## 3. `Func.wp` Proof: `full_bve_commit_res` -/

private theorem fullDenseInvW_with_wsort {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s) {wsort' : List (BitVec 32)}
    (hwl : wsort'.length = 2 * c.max_vars) :
    FullDenseInvW c F0 F_cur { s with scratch := { s.scratch with wsort := wsort' } } :=
  ⟨⟨h.1.core_ok, { h.1.scratch_ok with wsort_len := hwl }⟩,
   h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

private theorem fullArenaLits_eq_copied {k : FullCoreState} {scr : List (BitVec 32)}
    {cr0 p1 sz : Nat} (hbd : cr0 + 3 + sz ≤ k.arena.length) (hscr : p1 + sz ≤ scr.length)
    (hsz : (k.arena[cr0 + 2]?.getD 0#32).toNat = sz)
    (hcp : ∀ j < sz, k.arena[cr0 + 3 + j]? = scr[p1 + j]?) :
    fullArenaClauseLitsCore k cr0 =
      (List.range sz).map fun j => (scr[p1 + j]?.getD 0#32).toNat := by
  unfold fullArenaClauseLitsCore fullArenaClauseSizeCore
  rw [hsz]
  apply List.ext_getElem
  · simp [List.length_take, List.length_drop,
      Nat.min_eq_left (by omega : sz ≤ k.arena.length - (cr0 + 3))]
  · intro j hj1 _
    simp only [List.getElem_map, List.getElem_take, List.getElem_drop, List.getElem_range]
    have hj : j < sz := by simp [List.length_take, List.length_drop] at hj1; omega
    have hlt_ar : cr0 + 3 + j < k.arena.length := by omega
    have hlt_scr : p1 + j < scr.length := by omega
    have heq := hcp j hj
    rw [List.getElem?_eq_getElem hlt_ar, List.getElem?_eq_getElem hlt_scr, Option.some.injEq]
      at heq
    rw [List.getElem?_eq_getElem hlt_scr, Option.getD_some, heq]

private theorem fullResBuf_head_step {F_cur : List (List Nat)} {s : FullState} {r_end p : Nat}
    (hres : FullResBufOkW F_cur s r_end p) (hlt : p < r_end) :
    p + 1 + (s.scratch.scratch_buf[p]?.getD 0#32).toNat ≤ r_end ∧
      let sz := (s.scratch.scratch_buf[p]?.getD 0#32).toNat
      (∀ k < sz, (s.scratch.scratch_buf[p + 1 + k]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
      ((List.range sz).map fun k =>
        (s.scratch.scratch_buf[p + 1 + k]?.getD 0#32).toNat / 2).Nodup ∧
      (cnfOfClauses F_cur).EntailsClause (cnfClause ((List.range sz).map fun k =>
        (s.scratch.scratch_buf[p + 1 + k]?.getD 0#32).toNat)) ∧
      FullResBufOkW F_cur s r_end (p + 1 + sz) := by
  cases hres with
  | nil => exact absurd hlt (Nat.lt_irrefl _)
  | @cons _ sz0 hbd hsz hlts hnd hent htail =>
    subst hsz; exact ⟨hbd, hlts, hnd, hent, htail⟩

/-- Outer and inner `Func.wp` proof for `full_bve_commit_res`. -/
theorem full_bve_commit_res_wp (Γ : Env)
    (hAlloc : ∀ xs m Q X, fullAllocClSpec xs m Q X →
      Γ "full_alloc_cl" [i64, i32, i32, .bool] [i64] xs m Q X)
    (hWPush : ∀ xs m Q X, fullWatchPushSpec xs m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] xs m Q X)
    (hAddBin : ∀ xs m Q X, fullAddBinSpec xs m Q X →
      Γ "full_add_bin" [i64, i32, i32] [i64] xs m Q X)
    (hAddUnit : ∀ xs m Q X, fullAddUnitSpec xs m Q X →
      Γ "full_add_unit" [i64, i32] [.bool] xs m Q X) :
    ∀ args m Q X, fullBveCommitResSpec args m Q X →
      Func.wp Γ full_bve_commit_res_body args m Q X := by
  rintro ⟨h, r_off, r_end, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, s, R, rfl, hinv0, hle0, hcap0, hbuf0, hm0, hQ⟩
  have hmv := c.hmaxv; have harc := c.harena; have hsc := c.hscr
  unfold dimacsBound at hmv harc hsc
  unfold Func.wp full_bve_commit_res_body
  bve_steps!
  refine wp_loop_inv (ts := [i64])
    (fun (p, _) ml =>
      ∃ sl,
        FullDenseInvW c F0 F_cur sl ∧ sl.core.cur_vars = s.core.cur_vars ∧
        sl.core.fuel = s.core.fuel ∧ p.toNat ≤ r_end.toNat ∧
        FullResBufOkW F_cur sl r_end.toNat p.toNat ∧ (FullMem c sl ⋆ R) ml)
    (fun (p, _) _ => r_end.toNat - p.toNat)
    (fun J hJ => by
      bve_steps!
      exact hJ (r_off, PUnit.unit) m ⟨s, hinv0, rfl, rfl, hle0, hbuf0, hm0⟩)
    (fun J ⟨p, ⟨⟩⟩ ml ⟨sl, hinv, hcv_eq, hfl_eq, hp_le, hres, hm_lp⟩ ih => by
      have hcl := hinv.1.core_ok; have hsl := hinv.1.scratch_ok
      have hscrl := hsl.scratch_buf_len; have harl := hcl.arena_len_arr
      have harle := hcl.arena_len_le; have hcv := hcl.cur_vars_le
      bve_steps
      · -- sz == 0 -> inconsistent = 1, return 20
        have hp_lt : p.toNat < r_end.toNat := by bv_omega
        have hp_scr : p.toNat < sl.scratch.scratch_buf.length := by omega
        have hc0 : sl.scratch.scratch_buf[p.toNat]'hp_scr = 0#32 := by assumption
        obtain ⟨_, _, _, hent, _⟩ := fullResBuf_head_step hres hp_lt
        have hsz0 : (sl.scratch.scratch_buf[p.toNat]?.getD 0#32).toNat = 0 := by
          rw [List.getElem?_eq_getElem hp_scr, Option.getD_some, hc0]; rfl
        rw [hsz0] at hent
        have hent_nil : (cnfOfClauses F_cur).EntailsClause (cnfClause []) := by simpa using hent
        have hunsat_cur : (cnfOfClauses F_cur).Unsat := unsat_of_entails_nil hent_nil
        have hunsat0 : F0.Unsat := hinv.2.1.ext_sound.2 hunsat_cur
        let sl' := { sl with core := { sl.core with inconsistent := 1#64 } }
        exact hQ 20#64 sl' _ (FullDenseInvW.with_inconsistent hinv 1#64 (fun _ => hunsat_cur))
          hcv_eq hfl_eq (Or.inr (Or.inr rfl)) (fun _ => hunsat0) (by assumption)
      · -- sz == 1 -> full_add_unit
        have hp_lt : p.toNat < r_end.toNat := by bv_omega
        have hp_scr : p.toNat < sl.scratch.scratch_buf.length := by omega
        have hc1 : sl.scratch.scratch_buf[p.toNat]'hp_scr = 1#32 := by assumption
        obtain ⟨hbd, hlts, _, hent, htail⟩ := fullResBuf_head_step hres hp_lt
        have hsz1 : (sl.scratch.scratch_buf[p.toNat]?.getD 0#32).toNat = 1 := by
          rw [List.getElem?_eq_getElem hp_scr, Option.getD_some, hc1]; rfl
        rw [hsz1] at hbd hlts hent htail
        have hp1_nat : (p + 1#64).toNat = p.toNat + 1 := by bv_omega
        have hp1_scr : (p + 1#64).toNat < sl.scratch.scratch_buf.length := by omega
        have hlit_lt : (sl.scratch.scratch_buf[(p + 1#64).toNat]'hp1_scr).toNat <
            2 * sl.core.cur_vars := by
          have := hlts 0 (by omega)
          rw [List.getElem?_eq_getElem
            (by omega : p.toNat + 1 < sl.scratch.scratch_buf.length), Option.getD_some] at this
          simpa [hp1_nat] using this
        have hent1 : (cnfOfClauses F_cur).EntailsClause
            (cnfClause [(sl.scratch.scratch_buf[(p + 1#64).toNat]'hp1_scr).toNat]) := by
          have hls : (List.range 1).map (fun k =>
              (sl.scratch.scratch_buf[p.toNat + 1 + k]?.getD 0#32).toNat) =
              [(sl.scratch.scratch_buf[(p + 1#64).toNat]'hp1_scr).toNat] := by
            simp only [List.range_one, List.map_cons, List.map_nil, Nat.add_zero]
            simp only [hp1_nat, List.getElem?_eq_getElem
              (by omega : p.toNat + 1 < sl.scratch.scratch_buf.length), Option.getD_some]
          rw [← hls]; exact hent
        bve_steps
        refine wp_call_of_spec _ _ (hAddUnit _ _ _ X ⟨c, F0, F_cur, sl, R, rfl, hinv.1,
          hinv.2.1, (fun _ => hent1), by assumption, ?_⟩)
        dsimp only
        rintro ok vals' flags' lvl' rsns' trl' tp' te' prop' cl' unass' unfl' inc'
          sc' m' hlen' hw' hpres' hcl0 hokf_lt hokf hm'
        have hinv' := FullDenseInvW.of_addUnit hinv hlen' hw' hpres'.1 hcl0
        cases ok
        · obtain ⟨hu0, _⟩ := hokf_lt hlit_lt rfl
          bve_steps!
          exact hQ 20#64 _ m' hinv' hcv_eq hfl_eq (Or.inr (Or.inr rfl)) (fun _ => hu0) hm'
        · bve_steps!
          all_goals (try exact Bool.noConfusion (by assumption))
          have hnext_nat : (p + 1 + BitVec.setWidth 64
              (sl.scratch.scratch_buf[p.toNat]'hp_scr)).toNat = p.toNat + 1 + 1 := by
            rw [show (1 : BitVec 64) = 1#64 from rfl]
            have hs : (sl.scratch.scratch_buf[p.toNat]'hp_scr).toNat = 1 := by rw [hc1]; rfl
            bv_omega
          have hres' := FullResBufOkW.with_state (s := sl) (s' := { sl with
            core := { sl.core with
              vals := vals', flags := flags', lvl := lvl', rsns := rsns',
              trl := trl', trail_pos := tp', trail_end := te', propagated := prop',
              cur_level := cl', unassigned := unass', unflushed := unfl', inconsistent := inc' }
            scratch := sc' }) rfl (fun _ _ => by
              dsimp only; rw [hpres'.2.2.2.2.1]) htail
          refine ih _ m' (by dsimp only; rw [hnext_nat]; omega)
            ⟨_, hinv', hcv_eq, hfl_eq, by rw [hnext_nat]; omega, ?_, hm'⟩
          rw [hnext_nat]; exact hres'
      · -- sz == 2 -> full_add_bin
        have hp_lt : p.toNat < r_end.toNat := by bv_omega
        have hp_scr : p.toNat < sl.scratch.scratch_buf.length := by omega
        have hc2 : sl.scratch.scratch_buf[p.toNat]'hp_scr = 2#32 := by assumption
        obtain ⟨hbd, hlts, _, hent, htail⟩ := fullResBuf_head_step hres hp_lt
        have hsz2 : (sl.scratch.scratch_buf[p.toNat]?.getD 0#32).toNat = 2 := by
          rw [List.getElem?_eq_getElem hp_scr, Option.getD_some, hc2]; rfl
        rw [hsz2] at hbd hlts hent htail
        have hp1_nat : (p + 1#64).toNat = p.toNat + 1 := by bv_omega
        have hp1_scr : (p + 1#64).toNat < sl.scratch.scratch_buf.length := by omega
        have hp2_nat : (p + 1#64 + 1#64).toNat = p.toNat + 2 := by bv_omega
        have hp2_scr : (p + 1#64 + 1#64).toNat < sl.scratch.scratch_buf.length := by omega
        have ha_lt : (sl.scratch.scratch_buf[(p + 1#64).toNat]'hp1_scr).toNat <
            2 * sl.core.cur_vars := by
          have := hlts 0 (by omega)
          rw [List.getElem?_eq_getElem
            (by omega : p.toNat + 1 < sl.scratch.scratch_buf.length), Option.getD_some] at this
          simpa [hp1_nat] using this
        have hb_lt : (sl.scratch.scratch_buf[(p + 1#64 + 1#64).toNat]'hp2_scr).toNat <
            2 * sl.core.cur_vars := by
          have := hlts 1 (by omega)
          rw [show p.toNat + 1 + 1 = p.toNat + 2 by omega,
            List.getElem?_eq_getElem
              (by omega : p.toNat + 2 < sl.scratch.scratch_buf.length), Option.getD_some] at this
          simpa [hp2_nat] using this
        have hent2 : (cnfOfClauses F_cur).EntailsClause (cnfClause
            [(sl.scratch.scratch_buf[(p + 1#64).toNat]'hp1_scr).toNat,
             (sl.scratch.scratch_buf[(p + 1#64 + 1#64).toNat]'hp2_scr).toNat]) := by
          have hls : (List.range 2).map (fun k =>
              (sl.scratch.scratch_buf[p.toNat + 1 + k]?.getD 0#32).toNat) =
              [(sl.scratch.scratch_buf[(p + 1#64).toNat]'hp1_scr).toNat,
               (sl.scratch.scratch_buf[(p + 1#64 + 1#64).toNat]'hp2_scr).toNat] := by
            simp only [List.range_succ, List.range_zero, List.nil_append, List.map_append,
              List.map_cons, List.map_nil, Nat.add_zero]
            simp only [hp1_nat, hp2_nat,
              List.getElem?_eq_getElem
                (by omega : p.toNat + 1 < sl.scratch.scratch_buf.length),
              List.getElem?_eq_getElem
                (by omega : p.toNat + 2 < sl.scratch.scratch_buf.length),
              Option.getD_some, List.cons_append, List.nil_append]
          rw [← hls]; exact hent
        bve_steps
        refine wp_call_of_spec _ _ (hAddBin _ _ _ X ⟨c, F0, F_cur, sl, R, rfl, hinv.1,
          hinv.2.1, hinv.2.2.2.2.2.1, (fun _ _ => hent2), by assumption, ?_⟩)
        dsimp only
        rintro r vals' flags' lvl' rsns' trl' tp' te' unass' unfl' wvec' wstk' wlen' wu' nb'
          oom' inc' phases' wsort' m' hlen' hw' hrcodes hr20 hr2 hm'
        have hinv' := FullDenseInvW.of_addBin hinv hlen' hw'
        bve_steps!
        · exact hQ 20#64 _ m' hinv' hcv_eq hfl_eq (Or.inr (Or.inr rfl))
            (fun _ => (hr20 (by assumption)).1) hm'
        · exact hQ 2#64 _ m' hinv' hcv_eq hfl_eq (Or.inr (Or.inl rfl))
            (fun h => by cases h) hm'
        · have hnext_nat : (p + 1 + BitVec.setWidth 64
              (sl.scratch.scratch_buf[p.toNat]'hp_scr)).toNat = p.toNat + 1 + 2 := by
            rw [show (1 : BitVec 64) = 1#64 from rfl]
            have hs : (sl.scratch.scratch_buf[p.toNat]'hp_scr).toNat = 2 := by rw [hc2]; rfl
            bv_omega
          have hres' := FullResBufOkW.with_state (s := sl) (s' := { sl with
            core := { sl.core with
              vals := vals', flags := flags', lvl := lvl', rsns := rsns',
              trl := trl', trail_pos := tp', trail_end := te', unassigned := unass',
              unflushed := unfl', wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu',
              num_binary := nb', oom := oom', inconsistent := inc' }
            scratch := { sl.scratch with phases := phases', wsort := wsort' } })
            rfl (fun _ _ => rfl) htail
          refine ih _ m' (by dsimp only; rw [hnext_nat]; omega)
            ⟨_, hinv', hcv_eq, hfl_eq, by rw [hnext_nat]; omega, ?_, hm'⟩
          rw [hnext_nat]; exact hres'
      · -- sz >= 3 -> full_alloc_cl + copy + watch_push
        have hp_lt : p.toNat < r_end.toNat := by bv_omega
        have hp_scr : p.toNat < sl.scratch.scratch_buf.length := by omega
        obtain ⟨hbd, hlts, hnd, hent, htail⟩ := fullResBuf_head_step hres hp_lt
        let sz := (sl.scratch.scratch_buf[p.toNat]'hp_scr).toNat
        have hsz_bv : (sl.scratch.scratch_buf[p.toNat]'hp_scr).toNat = sz := rfl
        have hsz_def : (sl.scratch.scratch_buf[p.toNat]?.getD 0#32).toNat = sz := by
          rw [List.getElem?_eq_getElem hp_scr, Option.getD_some]
        rw [hsz_def] at hbd hlts hnd hent htail
        have hp1_nat : (p + 1#64).toNat = p.toNat + 1 := by bv_omega
        have hne0 : sl.scratch.scratch_buf[p.toNat]'hp_scr ≠ 0#32 := by assumption
        have hne1 : sl.scratch.scratch_buf[p.toNat]'hp_scr ≠ 1#32 := by assumption
        have hne2 : sl.scratch.scratch_buf[p.toNat]'hp_scr ≠ 2#32 := by assumption
        have hsz_ge3 : 3 ≤ sz := by
          rcases Nat.lt_or_ge sz 3 with hlt3 | hge3
          · exfalso
            rcases (by omega : sz = 0 ∨ sz = 1 ∨ sz = 2) with h0 | h1 | h2
            · exact hne0 (BitVec.eq_of_toNat_eq (by simp [hsz_bv, h0]))
            · exact hne1 (BitVec.eq_of_toNat_eq (by simp [hsz_bv, h1]))
            · exact hne2 (BitVec.eq_of_toNat_eq (by simp [hsz_bv, h2]))
          · exact hge3
        have hsz_lt31 : sz < 2 ^ 31 := by omega
        have hsz_lt64 : sz < 2 ^ 64 := by omega
        refine wp_call_of_spec _ _ (hAlloc _ _ _ X ⟨c, sl, R, rfl, hinv.1, by assumption, ?_⟩)
        simp only [LeanQbe.T.Arg.val_var]
        by_cases hoom_al : c.arena_cap - sl.core.arena_len < 3 +
            (sl.scratch.scratch_buf[p.toNat]'hp_scr).toNat
        · simp only [hoom_al, ite_true]
          bve_steps!
          · exact hQ 2#64 _ _ (FullDenseInvW.with_oom hinv 1#64) hcv_eq hfl_eq
              (Or.inr (Or.inl rfl)) (fun h => by cases h) (by assumption)
          · exfalso; exact (by assumption : (0xFFFFFFFF#64 : BitVec 64) ≠ 0xFFFFFFFF#64) rfl
        · simp only [hoom_al, ite_false]
          intro ar1 m1; try dsimp only
          intro hlen1 hhold1 hns1 hng1 hred1 hsz1 hm1
          have hoom_nat : ¬ c.arena_cap - sl.core.arena_len < 3 + sz := by
            simpa [hsz_bv] using hoom_al
          let cr0 := sl.core.arena_len
          have hcr0_le : cr0 + 3 + sz ≤ c.arena_cap := by
            dsimp only [cr0]; omega
          let cr : BitVec 64 := BitVec.ofNat 64 cr0
          have hcr0_lt31 : cr0 < 2 ^ 31 := by omega
          have hcr_nat : cr.toNat = cr0 := by
            simp [cr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : cr0 < 2 ^ 64)]
          have hcr_ne : cr ≠ 0xFFFFFFFF#64 := by
            intro heq; have := congrArg BitVec.toNat heq; rw [hcr_nat] at this
            have h32 : (0xFFFFFFFF#64 : BitVec 64).toNat = 2 ^ 32 - 1 := rfl
            omega
          bve_steps!
          -- Copy loop k < sz: ar[cr + 3 + k] = scr[p + 1 + k]
          refine wp_loop_inv (ts := [i32])
            (fun (k, _) mk =>
              ∃ ark,
                k.toNat ≤ sz ∧ ark.length = c.arena_cap ∧
                (∀ i < cr0, ark[i]? = sl.core.arena[i]?) ∧
                ark[cr0]? = ar1[cr0]? ∧ ark[cr0 + 2]? = ar1[cr0 + 2]? ∧
                (∀ j < k.toNat,
                  ark[cr0 + 3 + j]? = sl.scratch.scratch_buf[p.toNat + 1 + j]?) ∧
                (FullMem c { sl with core := { sl.core with
                  arena := ark, arena_len := cr0 + 3 + sz } } ⋆ R) mk)
            (fun (k, _) _ => sz - k.toNat)
            (fun Jc hJc => by
              bve_steps!
              refine hJc (0#32, PUnit.unit) m1 ⟨ar1, Nat.zero_le _, hlen1.core_ok.arena_len_arr,
                hhold1, rfl, rfl, (fun _ hj => by simp at hj), ?_⟩
              simpa [hsz_bv, cr0] using hm1)
            (fun Jc ⟨k, ⟨⟩⟩ mk ⟨ark, hk_le, hark_len, hark_hold, hark0, hark2, hark_cp,
                hmk⟩ ihc => by
              bve_steps
              · have hk_lt : k.toNat < sz := by bv_omega
                have hpk_scr : (p + 1#64 + BitVec.setWidth 64 k).toNat <
                    sl.scratch.scratch_buf.length := by bv_omega
                have hpk_nat : (p + 1#64 + BitVec.setWidth 64 k).toNat =
                    p.toNat + 1 + k.toNat := by bv_omega
                have hack_idx : (cr + 3#64 + BitVec.setWidth 64 k).toNat < ark.length := by
                  bv_omega
                have hack_nat : (cr + 3#64 + BitVec.setWidth 64 k).toNat =
                    cr0 + 3 + k.toNat := by bv_omega
                bve_steps!
                refine ihc (k + 1#32, PUnit.unit) _ (by bv_omega)
                  ⟨ark.set (cr0 + 3 + k.toNat)
                    (sl.scratch.scratch_buf[p.toNat + 1 + k.toNat]'(by omega)),
                    by bv_omega, by simp [hark_len], ?_, ?_, ?_, ?_, ?_⟩
                · intro i hi
                  rw [List.getElem?_set_ne (by omega)]; exact hark_hold i hi
                · rw [List.getElem?_set_ne (by omega)]; exact hark0
                · rw [List.getElem?_set_ne (by omega)]; exact hark2
                · intro j hj
                  have hk1 : (k + 1#32).toNat = k.toNat + 1 := by bv_omega
                  rw [hk1] at hj
                  by_cases hjk : j = k.toNat
                  · subst hjk
                    rw [List.getElem?_set_self (by omega),
                      List.getElem?_eq_getElem (by omega : p.toNat + 1 + k.toNat <
                        sl.scratch.scratch_buf.length)]
                  · rw [List.getElem?_set_ne (by omega)]
                    exact hark_cp j (by omega)
                · have hack_hm :
                      (BitVec.ofNat 64 sl.core.arena_len + 3 + BitVec.setWidth 64 k).toNat =
                        cr0 + 3 + k.toNat := hack_nat
                  have hpk_hm : (p + 1 + BitVec.setWidth 64 k).toNat = p.toNat + 1 + k.toNat :=
                    hpk_nat
                  have hpk_scr' :
                      (p + 1 + BitVec.setWidth 64 k).toNat < sl.scratch.scratch_buf.length :=
                    hpk_scr
                  have hval_eq :
                      sl.scratch.scratch_buf[(p + 1 + BitVec.setWidth 64 k).toNat]'hpk_scr' =
                        sl.scratch.scratch_buf[p.toNat + 1 + k.toNat]'(by omega) :=
                    Option.some.inj (by
                      rw [← List.getElem?_eq_getElem hpk_scr', hpk_hm,
                        List.getElem?_eq_getElem (by omega)])
                  rw [← hval_eq, ← hack_hm]
                  assumption
              · -- Done copy loop -> push watches k < sz
                have hk_eq : k.toNat = sz := by
                  have hlt_k : ¬ k.toNat < sz := by assumption
                  omega
                rw [hk_eq] at hark_cp
                let s2 : FullState :=
                  { sl with core := { sl.core with arena := ark, arena_len := cr0 + 3 + sz } }
                have hlen2 : s2.LengthsOk c :=
                  ⟨{ hcl with arena_len_arr := hark_len, arena_len_le := hcr0_le }, hsl⟩
                have hsz2_ar : (ark[cr0 + 2]?.getD 0#32).toNat = sz := by
                  rw [hark2]; simpa [hsz_bv] using hsz1
                have hs2_ar : cr0 + 3 + sz ≤ s2.core.arena.length := by
                  change cr0 + 3 + sz ≤ ark.length; rw [hark_len]; exact hcr0_le
                have hs2_scr : p.toNat + 1 + sz ≤ sl.scratch.scratch_buf.length := by omega
                have hlits_eq : fullArenaClauseLitsCore s2.core cr0 =
                    (List.range sz).map (fun j =>
                      (sl.scratch.scratch_buf[p.toNat + 1 + j]?.getD 0#32).toNat) :=
                  fullArenaLits_eq_copied hs2_ar hs2_scr hsz2_ar hark_cp
                have hns2 : (ark[cr0]?.getD 0#32 &&& 0x00800000#32) = 0#32 := by
                  rw [hark0]; exact hns1
                have hng2 : (ark[cr0]?.getD 0#32 &&& 0x00080000#32) = 0#32 := by
                  rw [hark0]; exact hng1
                have hrefs2 : fullArenaClauseRefsCore s2.core =
                    fullArenaClauseRefsCore sl.core ++ [cr0] :=
                  fullArenaClauseRefsCore_append hinv.2.1.arena hsz_ge3 rfl
                    hark_hold hns2 hsz2_ar
                have hwat2 : ModeWatchesInv F_cur s2.core :=
                  hinv.2.1.watches.with_wstk rfl rfl rfl rfl rfl
                    (fun r hr => by rw [hrefs2]; exact List.mem_append_left _ hr)
                refine wp_loop_inv (ts := [i32])
                  (fun (kw, _) mw =>
                    ∃ wvecw wstkw wlenw wuw wsortw,
                      kw.toNat ≤ sz ∧
                      let sw : FullState :=
                        { s2 with
                          core := { s2.core with wvec := wvecw, wstk := wstkw,
                                                 wlen := wlenw, wusable := wuw }
                          scratch := { s2.scratch with wsort := wsortw } }
                      sw.LengthsOk c ∧ ModeWatchesInv F_cur sw.core ∧
                      (FullMem c sw ⋆ R) mw)
                  (fun (kw, _) _ => sz - kw.toNat)
                  (fun Jw hJw => by
                    bve_steps!
                    exact hJw (0#32, PUnit.unit) mk
                      ⟨sl.core.wvec, sl.core.wstk, sl.core.wlen, sl.core.wusable,
                       sl.scratch.wsort, Nat.zero_le _, hlen2, hwat2, hmk⟩)
                  (fun Jw ⟨kw, ⟨⟩⟩ mw ⟨wvecw, wstkw, wlenw, wuw, wsortw, hkw_le, hlenw, hwatw,
                      hmw⟩ ihw => by
                    bve_steps
                    · have hkw_lt : kw.toNat < sz := by bv_omega
                      have har_idx :
                          (cr + 3#64 + BitVec.setWidth 64 kw).toNat < ark.length := by
                        bv_omega
                      have har_nat : (cr + 3#64 + BitVec.setWidth 64 kw).toNat =
                          cr0 + 3 + kw.toNat := by bv_omega
                      let w0w := (sl.scratch.scratch_buf[p.toNat]'hp_scr) &&& 0x7FFFFFFF#32
                      let cr32 := BitVec.setWidth 32 cr
                      have hw0w_nat : w0w.toNat = sz := by
                        dsimp only [w0w]
                        rw [bv32_and_litMask_toNat, hsz_bv, Nat.mod_eq_of_lt hsz_lt31]
                      have hw0w_ne : w0w ≠ 0xFFFFFFFF#32 := by
                        intro heq; have := congrArg BitVec.toNat heq; rw [hw0w_nat] at this
                        have : (0xFFFFFFFF#32 : BitVec 32).toNat = 2 ^ 32 - 1 := rfl; omega
                      have hw0w_msb : (w0w &&& 0x80000000#32) = 0#32 :=
                        bv32_and_msb_eq_zero_of_lt (by rw [hw0w_nat]; exact hsz_lt31)
                      have hcr32_nat : cr32.toNat = cr0 := by
                        dsimp only [cr32]
                        rw [BitVec.toNat_setWidth, hcr_nat,
                          Nat.mod_eq_of_lt (by omega : cr0 < 2 ^ 32)]
                      have hcr32_ne : cr32 ≠ 0xFFFFFFFF#32 := by
                        intro heq; have := congrArg BitVec.toNat heq; rw [hcr32_nat] at this
                        have : (0xFFFFFFFF#32 : BitVec 32).toNat = 2 ^ 32 - 1 := rfl; omega
                      let sw : FullState :=
                        { s2 with
                          core := { s2.core with wvec := wvecw, wstk := wstkw,
                                                 wlen := wlenw, wusable := wuw }
                          scratch := { s2.scratch with wsort := wsortw } }
                      bve_steps
                      refine wp_call_of_spec _ _ (hWPush _ mw _ X ⟨c, sw, R, rfl, hlenw,
                        hwatw.layout, (fun h => by cases h),
                        (fun _ => ⟨hw0w_ne, hcr32_ne⟩), hmw, ?_⟩)
                      dsimp only
                      rintro okw wvec' wstk' wlen' wu' wsort' mw' hlenw' hlayw' hotherw
                        hokt hokf hm'
                      simp only [LeanQbe.T.Arg.val_var, LeanQbe.T.Arg.val_imm]
                        at hotherw hokt hokf
                      have hwatw' : ModeWatchesInv F_cur
                          { sw.core with wvec := wvec', wstk := wstk',
                                         wlen := wlen', wusable := wu' } := by
                        refine fullWatchPush_preserves_modeWatchesInv (cnt := 2#32) hwatw hlayw'
                          rfl rfl (fun _ hr => hr) (fun h => by cases h) ?_ hotherw hokt
                          (fun hf => (hokf hf).1)
                        intro _
                        refine ⟨hw0w_msb, (fun _ => by
                          change 3 ≤ w0w.toNat; rw [hw0w_nat]; exact hsz_ge3),
                          (by rw [hcr32_nat]; omega), ?_⟩
                        change cr32.toNat ∈ fullArenaClauseRefsCore s2.core
                        rw [hcr32_nat, hrefs2]
                        exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
                      cases okw
                      · -- full_watch_push failed -> PH_GARB, arena_garbage += 3 + sz, oom = 1
                        have har_cr_idx : cr0 < ark.length := by omega
                        have har_cr_bv :
                            (BitVec.ofNat 64 sl.core.arena_len).toNat < ark.length := by
                          change cr.toNat < ark.length; rw [hcr_nat]; exact har_cr_idx
                        bve_steps!
                        let ark_g := ark.set cr0 ((ark[cr0]'har_cr_idx) ||| 0x00080000#32)
                        let ag' := sw.core.arena_garbage + 3#64 +
                          BitVec.setWidth 64 (sl.scratch.scratch_buf[p.toNat]'hp_scr)
                        let s_ws : FullState :=
                          { sl with scratch := { sl.scratch with wsort := wsort' } }
                        have hinv_ws := fullDenseInvW_with_wsort hinv hlenw'.scratch_ok.wsort_len
                        have hhold_g : ∀ i < cr0, ark_g[i]? = sl.core.arena[i]? :=
                          fun i hi => by
                            rw [List.getElem?_set_ne (by omega)]; exact hark_hold i hi
                        have hns_g : (ark_g[cr0]?.getD 0#32 &&& 0x00800000#32) = 0#32 := by
                          rw [List.getElem?_set_self (by omega), Option.getD_some,
                            bv32_bit23_or_garb]
                          have := hns2
                          rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at this
                          exact this
                        have hng_g : (ark_g[cr0]?.getD 0#32 &&& 0x00080000#32) ≠ 0#32 := by
                          rw [List.getElem?_set_self (by omega), Option.getD_some]
                          exact bv32_bit19_or_garb_ne0 _
                        have hsz_g : (ark_g[cr0 + 2]?.getD 0#32).toNat = sz := by
                          rw [List.getElem?_set_ne (by omega)]; exact hsz2_ar
                        have hlen_g : ({ s_ws with
                          core := { s_ws.core with
                            arena := ark_g, arena_len := cr0 + 3 + sz,
                            wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu',
                            arena_garbage := ag', oom := 1#64 } } : FullState).LengthsOk c :=
                          ⟨{ hlenw'.core_ok with arena_len_arr := by simp [ark_g, hark_len] },
                           hlenw'.scratch_ok⟩
                        have hrefs_g : fullArenaClauseRefsCore
                            { s_ws.core with arena := ark_g, arena_len := cr0 + 3 + sz } =
                            fullArenaClauseRefsCore sl.core ++ [cr0] :=
                          fullArenaClauseRefsCore_append hinv.2.1.arena hsz_ge3 rfl
                            hhold_g hns_g hsz_g
                        have hwat_g : ModeWatchesInv F_cur
                            { s_ws.core with
                              arena := ark_g, arena_len := cr0 + 3 + sz,
                              wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu',
                              arena_garbage := ag', oom := 1#64 } :=
                          hwatw'.with_wstk rfl rfl rfl rfl rfl
                            (fun r hr => by
                              change r ∈ fullArenaClauseRefsCore s2.core at hr
                              rw [hrefs2] at hr; exact hrefs_g ▸ hr)
                        have hinv_g := addGarbageClause_preserves_witness hinv_ws hlen_g hsz_ge3
                          hhold_g hns_g hng_g hsz_g hwat_g
                        refine hQ 2#64 _ _ hinv_g hcv_eq hfl_eq (Or.inr (Or.inl rfl))
                          (fun h => by cases h) ?_
                        have har_g_eq :
                            ark_g = ark.set (BitVec.ofNat 64 sl.core.arena_len).toNat
                              ((ark[(BitVec.ofNat 64 sl.core.arena_len).toNat]'(by
                                rw [show (BitVec.ofNat 64 sl.core.arena_len).toNat = cr0 from
                                  hcr_nat]; exact har_cr_idx)) ||| 0x00080000#32) := by
                          simp only [ark_g,
                            show (BitVec.ofNat 64 sl.core.arena_len).toNat = cr0 from hcr_nat, cr0]
                        have hst_g : ({ s_ws with
                          core := { s_ws.core with
                            arena := ark_g, arena_len := cr0 + 3 + sz,
                            wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu',
                            arena_garbage := ag', oom := 1#64 } } : FullState) =
                          { s2 with
                            core := { s2.core with
                              arena := ark.set (BitVec.ofNat 64 sl.core.arena_len).toNat
                                ((ark[(BitVec.ofNat 64 sl.core.arena_len).toNat]'(by
                                  rw [show (BitVec.ofNat 64 sl.core.arena_len).toNat = cr0 from
                                    hcr_nat]; exact har_cr_idx)) ||| 0x00080000#32),
                              wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu',
                              arena_garbage := sw.core.arena_garbage + 3 +
                                BitVec.setWidth 64 (sl.scratch.scratch_buf[p.toNat]'hp_scr),
                              oom := 1#64 }
                            scratch := { s2.scratch with wsort := wsort' } } := by
                          dsimp only [s_ws, ag', s2, cr0]
                          rw [har_g_eq]; rfl
                        rw [hst_g]; assumption
                      · -- full_watch_push succeeded -> kw + 1
                        refine wp_jnz_of (fun _ => ?_) (fun hf => Bool.noConfusion hf)
                        bve_steps!
                        have hkw1 : (kw + 1#32).toNat = kw.toNat + 1 := by
                          rw [BitVec.toNat_add, show (1#32 : BitVec 32).toNat = 1 from rfl,
                            Nat.mod_eq_of_lt (by omega : kw.toNat + 1 < 2 ^ 32)]
                        exact ihw (kw + 1#32, PUnit.unit) mw' (by dsimp only; rw [hkw1]; omega)
                          ⟨wvec', wstk', wlen', wu', wsort', by rw [hkw1]; omega,
                           hlenw', hwatw', hm'⟩
                    · -- watch_push loop finished -> num_irred++, p += 1 + sz
                      bve_steps!
                      let s_ws : FullState :=
                        { sl with scratch := { sl.scratch with wsort := wsortw } }
                      have hinv_ws := fullDenseInvW_with_wsort hinv hlenw.scratch_ok.wsort_len
                      have hlen_c : ({ s_ws with
                        core := { s_ws.core with
                          arena := ark, arena_len := cr0 + 3 + sz,
                          wvec := wvecw, wstk := wstkw, wlen := wlenw, wusable := wuw,
                          num_irred := sl.core.num_irred + 1#64 } } : FullState).LengthsOk c :=
                        ⟨{ hlenw.core_ok with arena_len_arr := hlenw.core_ok.arena_len_arr },
                         hlenw.scratch_ok⟩
                      have hwat_c : ModeWatchesInv F_cur
                          { s_ws.core with
                            arena := ark, arena_len := cr0 + 3 + sz,
                            wvec := wvecw, wstk := wstkw, wlen := wlenw, wusable := wuw,
                            num_irred := sl.core.num_irred + 1#64 } :=
                        hwatw.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr)
                      have hinv_c := addEntailedClause_preserves_witness hinv_ws hlen_c hsz_ge3
                        (by
                          intro l hl
                          have hl' : l ∈ (List.range sz).map (fun j =>
                              (sl.scratch.scratch_buf[p.toNat + 1 + j]?.getD 0#32).toNat) := by
                            simpa only [← hlits_eq] using hl
                          obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hl'
                          rw [List.mem_range] at hj; exact hlts j hj)
                        (by
                          change ((fullArenaClauseLitsCore s2.core cr0).map (· / 2)).Nodup
                          rw [hlits_eq, List.map_map]; simpa only [Function.comp_def] using hnd)
                        (by
                          change (cnfOfClauses F_cur).EntailsClause
                            (cnfClause (fullArenaClauseLitsCore s2.core cr0))
                          rw [hlits_eq]; exact hent)
                        hark_hold hns2 hsz2_ar hwat_c
                      have hnext_nat : (p + 1 + BitVec.setWidth 64
                          (sl.scratch.scratch_buf[p.toNat]'hp_scr)).toNat =
                          p.toNat + 1 + sz := by
                        rw [show (1 : BitVec 64) = 1#64 from rfl, BitVec.toNat_add,
                          BitVec.toNat_add,
                          show (1#64 : BitVec 64).toNat = 1 from rfl, BitVec.toNat_setWidth,
                          Nat.mod_eq_of_lt hsz_lt64,
                          Nat.mod_eq_of_lt (by omega : p.toNat + 1 < 2 ^ 64),
                          Nat.mod_eq_of_lt (by omega : p.toNat + 1 + sz < 2 ^ 64)]
                      have hres_c := FullResBufOkW.with_state (s := sl) (s' := { s_ws with
                        core := { s_ws.core with
                          arena := ark, arena_len := cr0 + 3 + sz,
                          wvec := wvecw, wstk := wstkw, wlen := wlenw, wusable := wuw,
                          num_irred := sl.core.num_irred + 1#64 } }) rfl (fun _ _ => rfl) htail
                      refine ih _ _ (by dsimp only; rw [hnext_nat]; omega)
                        ⟨_, hinv_c, hcv_eq, hfl_eq, by rw [hnext_nat]; omega, ?_,
                         by assumption⟩
                      dsimp only; rw [hnext_nat]; exact hres_c))
      · exact hQ 1#64 sl ml hinv hcv_eq hfl_eq (Or.inl rfl) (fun h => by cases h) hm_lp)

end LeanQbe.T.Examples.Kissat.Full
