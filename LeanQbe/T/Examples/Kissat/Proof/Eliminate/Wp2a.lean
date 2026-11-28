/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Eliminate.Helpers
public import LeanQbe.T.Examples.Kissat.Proof.Eliminate.Spec
import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena1
import LeanQbe.T.Examples.Kissat.Proof.Spec.WitnessInv
import LeanQbe.T.Examples.Kissat.Proof.Spec.WitnessInv1

/-!
# Kissat BVE `Func.wp` Helpers — Part 2a (`Wp2a`: invariants & `full_assign_lvl` level-0)

Pure invariant, arithmetic, resolution-buffer, and level-0 `full_assign_lvl` preservation lemmas
for `full_bve_var_m7_wp` (`Wp2.lean`). Zero legacy `Full*` imports; zero `@[expose]` on theorems.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Eliminate

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Definition.Spec

/-! ## 1. BVE Mode Offsets (`m8` vs `m7`) & Pure Entry/Weak Helpers -/

@[expose] public def bveOccLim (m8 : Bool) : Nat := if m8 then 2001 else 512
@[expose] public def bvePosMask (m8 : Bool) : Nat := if m8 then 4002 else 1024
@[expose] public def bveNegMask (m8 : Bool) : Nat := if m8 then 4066 else 1040
@[expose] public def bveGfIdx (m8 : Bool) : Nat := if m8 then 4130 else 1056
@[expose] public def bveRgIdx (m8 : Bool) : Nat := if m8 then 4131 else 1057
@[expose] public def bveROff (m8 : Bool) : Nat := if m8 then 4192 else 1088

public theorem bveMode_bounds {m8 : Bool} {scap : Nat}
    (h2048 : 2048 ≤ scap) (hm8 : m8 = decide (16384 ≤ scap)) :
    bveOccLim m8 ≤ 2001 ∧
    bveOccLim m8 + bveOccLim m8 ≤ bvePosMask m8 ∧
    bvePosMask m8 + (if m8 then 64 else 16) ≤ bveNegMask m8 ∧
    bveNegMask m8 + (if m8 then 64 else 16) ≤ bveGfIdx m8 ∧
    bveGfIdx m8 < bveRgIdx m8 ∧
    bveRgIdx m8 < bveROff m8 ∧
    bveROff m8 ≤ scap ∧
    (m8 = true → 16384 ≤ scap) ∧
    (m8 = false → 1088 ≤ scap) := by
  subst hm8
  by_cases h : 16384 ≤ scap
  · simp [bveOccLim, bvePosMask, bveNegMask, bveGfIdx, bveRgIdx, bveROff, h]; omega
  · simp [bveOccLim, bvePosMask, bveNegMask, bveGfIdx, bveRgIdx, bveROff, h]; omega

public theorem bve_mask_idx_lt {m8 : Bool} {i occ scap : Nat}
    (hocc : occ ≤ bveOccLim m8) (hi : i < occ)
    (hm8 : m8 = decide (16384 ≤ scap)) :
    bvePosMask m8 + (BitVec.ofNat 32 i >>> 5#32).toNat < bveROff m8 ∧
    bveNegMask m8 + (BitVec.ofNat 32 i >>> 5#32).toNat < bveROff m8 := by
  have hshift : (BitVec.ofNat 32 i >>> 5#32).toNat = i / 32 := by
    have hlt32 : i < 2 ^ 32 := by
      have : bveOccLim m8 ≤ 2001 := by cases m8 <;> simp [bveOccLim]
      omega
    simp [Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt hlt32]
  subst hm8; by_cases h : 16384 ≤ scap <;>
    simp [bveOccLim, bvePosMask, bveNegMask, bveROff, h] at hocc ⊢ <;> omega

public theorem bve_entries_congr {F_cur : List (List Nat)} {s s' : FullState}
    {lit off cnt : Nat}
    (hcv : s'.core.cur_vars = s.core.cur_vars)
    (har : s'.core.arena = s.core.arena) (hal : s'.core.arena_len = s.core.arena_len)
    (hscr : ∀ i < cnt, s'.scratch.scratch_buf[off + i]? = s.scratch.scratch_buf[off + i]?)
    (hent : ∀ i < cnt, FullBveEntryOkW F_cur s lit (s.scratch.scratch_buf[off + i]?.getD 0#32)) :
    ∀ i < cnt, FullBveEntryOkW F_cur s' lit (s'.scratch.scratch_buf[off + i]?.getD 0#32) := by
  intro i hi
  rw [hscr i hi]
  exact bveEntry_congr_core (hent i hi) hcv har hal

public theorem bve_weak_items_of_entries {F_cur : List (List Nat)} {s : FullState}
    {lit off cnt : Nat}
    (hent : ∀ i < cnt, FullBveEntryOkW F_cur s lit (s.scratch.scratch_buf[off + i]?.getD 0#32)) :
    ∀ i < cnt, FullBveWeakItemOk s.core (s.scratch.scratch_buf[off + i]?.getD 0#32) :=
  fun i hi => bveEntry_to_weak (hent i hi)

public theorem bve_weak_items_congr {s s' : FullState} {off cnt : Nat}
    (hcv : s'.core.cur_vars = s.core.cur_vars)
    (hrefs : fullArenaClauseRefs s' = fullArenaClauseRefs s)
    (hscr : s'.scratch.scratch_buf = s.scratch.scratch_buf)
    (hwk : ∀ i < cnt, FullBveWeakItemOk s.core (s.scratch.scratch_buf[off + i]?.getD 0#32)) :
    ∀ i < cnt, FullBveWeakItemOk s'.core (s'.scratch.scratch_buf[off + i]?.getD 0#32) := by
  intro i hi
  have h0 := hwk i hi
  rw [hscr]
  unfold FullBveWeakItemOk at h0 ⊢
  by_cases hc : (s.scratch.scratch_buf[off + i]?.getD 0#32) &&& 2147483648#32 ≠ 0#32
  · simp only [eq_true hc, ↓reduceIte] at h0 ⊢; rw [hcv]; exact h0
  · simp only [hc, ↓reduceIte] at h0 ⊢
    rw [show fullArenaClauseRefsCore s'.core = fullArenaClauseRefsCore s.core from hrefs]
    exact h0

public theorem bve_extNeed_pre_of_entries {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {lit off cnt : Nat} (hdw : FullDenseInvW c F0 F_cur s)
    (hent : ∀ i < cnt, FullBveEntryOkW F_cur s lit (s.scratch.scratch_buf[off + i]?.getD 0#32)) :
    ∀ i < cnt,
      let w := s.scratch.scratch_buf[off + i]?.getD 0#32
      w &&& 2147483648#32 ≠ 0#32 ∨ w.toNat + 2 < c.arena_cap :=
  fun i hi => bveEntry_to_extNeed hdw (hent i hi)

/-! ## 2. Early-Exit Unsat & Copy / Defrag Helpers -/

public theorem bve_rlen0_unsat {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hdw : FullDenseInvW c F0 F_cur s)
    (hent : (cnfOfClauses F_cur).EntailsClause
      (cnfClause (List.map BitVec.toNat (List.take 0 s.core.tmp)))) :
    F0.Unsat := by
  exact hdw.2.1.ext_sound.2 (unsat_of_entails_nil (by simpa using hent))

public theorem bve_rlen1_conflict_unsat {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hdw : FullDenseInvW c F0 F_cur s)
    (hul_lt : (s.core.tmp[0]?.getD 0#32).toNat < 2 * s.core.cur_vars)
    (htmp_ne : s.core.tmp ≠ [])
    (hent : (cnfOfClauses F_cur).EntailsClause
      (cnfClause (List.map BitVec.toNat (List.take 1 s.core.tmp))))
    (hneg : s.core.vals[(s.core.tmp[0]?.getD 0#32).toNat]?.getD 0#8 = 255#8) :
    F0.Unsat := by
  cases htmp : s.core.tmp with
  | nil => exact absurd htmp htmp_ne
  | cons u us =>
    simp only [htmp, List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil] at hent
    simp only [htmp, List.getElem?_cons_zero, Option.getD_some] at hul_lt hneg
    have h1 := elim_vals_neg_entails hdw.2.1 hdw.2.2.2.2.2.1 hul_lt hneg
    exact hdw.2.1.ext_sound.2 (elim_unsat_of_lit_and_neg hent h1)

public theorem bve_copy_post_resbuf_ok {F_cur : List (List Nat)} {s s' : FullState}
    {r0 r1 : Nat} {tmp : List (BitVec 32)} {tl : Nat}
    (hcv : s'.core.cur_vars = s.core.cur_vars)
    (htmp_len : tl ≤ tmp.length)
    (hscr_pre : ∀ idx < r1, s'.scratch.scratch_buf[idx]? = s.scratch.scratch_buf[idx]?)
    (hsz : (s'.scratch.scratch_buf[r1]?.getD 0#32).toNat = tl)
    (hcopy : ∀ k < tl, s'.scratch.scratch_buf[r1 + 1 + k]? = some (tmp[k]?.getD 0#32))
    (hbd : ∀ k < tl, (tmp[k]?.getD 0#32).toNat < 2 * s.core.cur_vars)
    (hnodup : (List.map (fun x => x.toNat / 2) (List.take tl tmp)).Nodup)
    (hent : (cnfOfClauses F_cur).EntailsClause
      (cnfClause (List.map BitVec.toNat (List.take tl tmp))))
    (hrb : FullResBufOkW F_cur s r1 r0) :
    FullResBufOkW F_cur s' (r1 + 1 + tl) r0 := by
  have htake : List.take tl tmp = List.map (fun k => tmp[k]?.getD 0#32) (List.range tl) := by
    apply List.ext_getElem
    · simp [Nat.min_eq_left htmp_len]
    · intro k hk1 hk2
      simp only [List.length_take, Nat.min_eq_left htmp_len] at hk1
      rw [List.getElem_take, List.getElem_map, List.getElem_range]
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
  have heq_lits : List.map (fun k => (s'.scratch.scratch_buf[r1 + 1 + k]?.getD 0#32).toNat)
      (List.range tl) = List.map BitVec.toNat (List.take tl tmp) := by
    rw [htake, List.map_map]; apply List.map_congr_left
    intro k hk; simp only [List.mem_range] at hk
    simp [hcopy k hk]
  have heq_vars : List.map (fun k => (s'.scratch.scratch_buf[r1 + 1 + k]?.getD 0#32).toNat / 2)
      (List.range tl) = List.map (fun x => x.toNat / 2) (List.take tl tmp) := by
    rw [htake, List.map_map]; apply List.map_congr_left
    intro k hk; simp only [List.mem_range] at hk
    simp [hcopy k hk]
  refine resBuf_append_block hcv hscr_pre hsz (fun k hk => ?_) (by rw [heq_vars]; exact hnodup)
    (by rw [heq_lits]; exact hent) hrb
  rw [hcopy k hk, Option.getD_some, hcv]; exact hbd k hk

public theorem bve_defrag_preserves_fullDenseInvW {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState}
    {wv' ws' wsort' : List (BitVec 32)} {wlen' : Nat}
    (hdw : FullDenseInvW c F0 F_cur s)
    (hlok' : FullState.LengthsOk c
      { core := { s.core with wlen := wlen', wusable := 0#64, wvec := wv', wstk := ws' }
        scratch := { s.scratch with wsort := wsort' } })
    (hlay' : WatchStackLayout
      { s.core with wlen := wlen', wusable := 0#64, wvec := wv', wstk := ws' })
    (hwat' : ∀ l < 2 * s.core.cur_vars,
      let s' : FullState :=
        { core := { s.core with wlen := wlen', wusable := 0#64, wvec := wv', wstk := ws' }
          scratch := { s.scratch with wsort := wsort' } }
      fullWatchSize s' l = fullWatchSize s l ∧
        ∀ k < fullWatchSize s l,
          ws'[fullWatchOff s' l + k]? = s.core.wstk[fullWatchOff s l + k]?) :
    FullDenseInvW c F0 F_cur
      { core := { s.core with wlen := wlen', wusable := 0#64, wvec := wv', wstk := ws' }
        scratch := { s.scratch with wsort := wsort' } } := by
  let s' : FullState :=
    { core := { s.core with wlen := wlen', wusable := 0#64, wvec := wv', wstk := ws' }
      scratch := { s.scratch with wsort := wsort' } }
  have hmw' : ModeWatchesInv F_cur s'.core :=
    fullWstackDefrag_preserves_modeWatchesInv hdw.2.1.watches hlay' rfl rfl (fun _ h => h) hwat'
  refine ⟨hlok', ⟨hdw.2.1.ext_sound, hdw.2.1.inconsistent_sound,
    { hdw.2.1.arena with len_ok := hdw.2.1.arena.len_ok }, hmw', hdw.2.1.cur_level_le,
    hdw.2.1.trail_lits_lt, hdw.2.1.trail_vars_nodup, hdw.2.1.vals_domain, hdw.2.1.vals_true_iff,
    hdw.2.1.vals_false_iff, hdw.2.1.lvl_le, hdw.2.1.dec_earliest, hdw.2.1.levels_inhabited,
    hdw.2.1.level0_sound, hdw.2.1.trail_pos_inv, hdw.2.1.level0_rsn_none,
    hdw.2.1.frame_trail_lt, hdw.2.1.frame_trail_mono, hdw.2.1.frame_trail_before_lt,
    hdw.2.1.frame_dec_lt, hdw.2.1.reason_inv, hdw.2.1.reason_lit_mem⟩,
    hdw.2.2.1, hdw.2.2.2.1, FullExtScratchOk.of_pres hdw.2.2.2.2.1 ⟨rfl, rfl⟩ fun _ hr => hr,
    hdw.2.2.2.2.2.1, hdw.2.2.2.2.2.2⟩

/-! ## 3. Level-0 `full_assign_lvl` Preservation of `FullDenseInvW` (Fixing `F_cur`) -/

private theorem bv32_ofNat_toNat_w2a {n : Nat} (hn : n < 2 ^ 32) :
    (BitVec.ofNat 32 n).toNat = n := by
  simp [Nat.mod_eq_of_lt hn]

public theorem bve_assign0_preserves_fullDenseInvW {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} {lit : BitVec 32}
    {flags' : List (BitVec 32)} {unass' : BitVec 64} {phases' : List (BitVec 8)}
    (hdw : FullDenseInvW c F0 F_cur s)
    (hlit : lit.toNat < 2 * s.core.cur_vars)
    (hun : s.core.vals[lit.toNat]?.getD 0#8 = 0#8)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause [lit.toNat]))
    (hfll : flags'.length = c.max_vars)
    (hphl : phases'.length = c.max_vars) :
    let v := lit.toNat / 2
    let s' : FullState :=
      { core := { s.core with
          unassigned := unass', unflushed := s.core.unflushed + 1#64,
          trail_end := s.core.trail_end + 1,
          vals := (s.core.vals.set lit.toNat 1#8).set (lit.toNat ^^^ 1) 255#8,
          flags := flags', lvl := s.core.lvl.set v 0#32,
          rsns := s.core.rsns.set v 0xFFFFFFFF#32,
          trl := s.core.trl.set s.core.trail_end lit,
          trail_pos := s.core.trail_pos.set v (BitVec.ofNat 32 s.core.trail_end) }
        scratch := { s.scratch with phases := phases' } }
    FullDenseInvW c F0 F_cur s' := by
  intro v s'
  have hcl := hdw.1.core_ok
  have hsok := hdw.1.scratch_ok
  have hw := hdw.2.1
  have hcl0 : s.core.cur_level = 0 := hdw.2.2.2.2.2.1
  have hte_lt : s.core.trail_end < s.core.cur_vars := hw.trail_end_lt_of_unassigned hlit hun
  have hnot_var : ∀ i < s.core.trail_end, (s.core.trl[i]?.getD 0#32).toNat / 2 ≠ v :=
    (hw.vals_zero_iff hlit).mp hun
  have hnlit_lt : (lit.toNat ^^^ 1) < 2 * s.core.cur_vars := litNeg_lt_two_mul hlit
  have hne_lit : lit.toNat ^^^ 1 ≠ lit.toNat := litNeg_ne_self lit.toNat
  have hv_lt : v < c.max_vars := by have := hcl.cur_vars_le; omega
  have hte_max : s.core.trail_end < c.max_vars := by have := hcl.cur_vars_le; omega
  have hte_lt32 : s.core.trail_end < 2 ^ 32 := by have := fullInv_max_vars_lt32 c; omega
  have hlen' : s'.LengthsOk c :=
    ⟨{ hcl with
      vals_len := by simp [s', hcl.vals_len], flags_len := hfll,
      lvl_len := by simp [s', hcl.lvl_len], rsns_len := by simp [s', hcl.rsns_len],
      trl_len := by simp [s', hcl.trl_len], trail_pos_len := by simp [s', hcl.trail_pos_len],
      trail_end_le := by dsimp [s']; omega,
      propagated_le := by have := hcl.propagated_le; dsimp [s']; omega },
     { hsok with phases_len := hphl }⟩
  have htrl_get : ∀ i < s.core.trail_end + 1,
      (s'.core.trl[i]?.getD 0#32).toNat =
        if i = s.core.trail_end then lit.toNat else (s.core.trl[i]?.getD 0#32).toNat :=
    fun i _ => by
      by_cases he : i = s.core.trail_end
      · subst he; simp [s', List.getElem?_set_self (by rw [hcl.trl_len]; exact hte_max)]
      · simp [s', he, List.getElem?_set_ne (Ne.symm he)]
  have hlvl_get : ∀ w < s.core.cur_vars,
      (s'.core.lvl[w]?.getD 0#32).toNat =
        if w = v then 0 else (s.core.lvl[w]?.getD 0#32).toNat := fun w _ => by
    by_cases he : w = v
    · subst he; simp [s', List.getElem?_set_self (by rw [hcl.lvl_len]; exact hv_lt)]
    · simp [s', he, List.getElem?_set_ne (Ne.symm he)]
  have hrsn_get : ∀ w < s.core.cur_vars,
      s'.core.rsns[w]?.getD 0xFFFFFFFF#32 =
        if w = v then 0xFFFFFFFF#32 else s.core.rsns[w]?.getD 0xFFFFFFFF#32 := fun w _ => by
    by_cases he : w = v
    · subst he; simp [s', List.getElem?_set_self (by rw [hcl.rsns_len]; exact hv_lt)]
    · simp [s', he, List.getElem?_set_ne (Ne.symm he)]
  have hvals_get : ∀ l < 2 * s.core.cur_vars,
      s'.core.vals[l]?.getD 0#8 =
        if l = lit.toNat ^^^ 1 then 0xFF#8 else if l = lit.toNat then 1#8
        else s.core.vals[l]?.getD 0#8 := fun l hl => by
    have hcm := hcl.cur_vars_le
    by_cases h1 : l = lit.toNat ^^^ 1
    · subst h1; dsimp only [s']; simp only [↓reduceIte]
      rw [List.getElem?_set_self (by simp [hcl.vals_len]; omega)]; rfl
    · dsimp only [s']; simp only [h1, ↓reduceIte]; rw [List.getElem?_set_ne (Ne.symm h1)]
      by_cases h2 : l = lit.toNat
      · subst h2; simp only [↓reduceIte]; rw [List.getElem?_set_self (by rw [hcl.vals_len]; omega)]
        rfl
      · simp only [h2, ↓reduceIte]; rw [List.getElem?_set_ne (Ne.symm h2)]
  refine ⟨hlen', {
    ext_sound := hw.ext_sound
    inconsistent_sound := hw.inconsistent_sound
    arena := { hw.arena with len_ok := hw.arena.len_ok }
    watches := hw.watches.with_wstk rfl rfl rfl rfl rfl fun _ hr => hr
    cur_level_le := by dsimp [s']; omega
    trail_lits_lt := fun i hi => by
      rw [htrl_get i hi]; split; · exact hlit
      · exact hw.trail_lits_lt i (by dsimp [s'] at hi; omega)
    trail_vars_nodup := fun i j hi hj hveq => by
      dsimp [s'] at hi hj; rw [htrl_get i hi, htrl_get j hj] at hveq
      split at hveq <;> split at hveq
      · omega
      · exact absurd hveq.symm (hnot_var j (by omega))
      · exact absurd hveq (hnot_var i (by omega))
      · exact hw.trail_vars_nodup i j (by omega) (by omega) hveq
    vals_domain := fun l hl => by
      rw [hvals_get l hl]; split; · exact Or.inr (Or.inr rfl)
      split; · exact Or.inr (Or.inl rfl)
      exact hw.vals_domain l hl
    vals_true_iff := fun l hl => by
      rw [hvals_get l hl]; dsimp [s']
      constructor
      · intro h1; by_cases hneg : l = lit.toNat ^^^ 1
        · simp [hneg] at h1
        · simp only [hneg, ↓reduceIte] at h1; by_cases hpos : l = lit.toNat
          · exact ⟨s.core.trail_end, by omega, by rw [htrl_get _ (by omega)]; simp [hpos]⟩
          · simp only [hpos, ↓reduceIte] at h1
            obtain ⟨i, hi, heq⟩ := (hw.vals_true_iff l hl).mp h1
            exact ⟨i, by omega,
              by rw [htrl_get i (by omega)]; simp [show i ≠ s.core.trail_end by omega, heq]⟩
      · rintro ⟨i, hi, heq⟩; rw [htrl_get i hi] at heq
        by_cases hie : i = s.core.trail_end
        · simp only [hie, ↓reduceIte] at heq; subst heq; simp [Ne.symm hne_lit]
        · simp only [hie, ↓reduceIte] at heq
          have hlv : l / 2 ≠ v := by rw [← heq]; exact hnot_var i (by omega)
          have h1 : l ≠ lit.toNat ^^^ 1 := fun h => hlv (by rw [h, fullInv_var_xor1])
          have h2 : l ≠ lit.toNat := fun h => hlv (by rw [h])
          simp only [h1, h2, ↓reduceIte]; exact (hw.vals_true_iff l hl).mpr ⟨i, by omega, heq⟩
    vals_false_iff := fun l hl => by
      rw [hvals_get l hl]; dsimp [s']
      constructor
      · intro h1; by_cases hneg : l = lit.toNat ^^^ 1
        · exact ⟨s.core.trail_end, by omega, by
            rw [htrl_get _ (by omega)]; simp only [↓reduceIte, hneg]; exact (litNeg_litNeg _).symm⟩
        · simp only [hneg, ↓reduceIte] at h1; by_cases hpos : l = lit.toNat
          · simp [hpos] at h1
          · simp only [hpos, ↓reduceIte] at h1
            obtain ⟨i, hi, heq⟩ := (hw.vals_false_iff l hl).mp h1
            exact ⟨i, by omega,
              by rw [htrl_get i (by omega)]; simp [show i ≠ s.core.trail_end by omega, heq]⟩
      · rintro ⟨i, hi, heq⟩; rw [htrl_get i hi] at heq
        by_cases hie : i = s.core.trail_end
        · simp only [hie, ↓reduceIte] at heq
          have hl_eq : l = lit.toNat ^^^ 1 := by
            have h := congrArg litNeg heq; have h1 : litNeg (l ^^^ 1) = l := litNeg_litNeg l
            rw [h1] at h; exact h.symm
          simp [hl_eq]
        · simp only [hie, ↓reduceIte] at heq
          have hlv : l / 2 ≠ v := by
            have h := hnot_var i (by omega); rw [heq] at h; rwa [fullInv_var_xor1] at h
          have h1 : l ≠ lit.toNat ^^^ 1 := fun h => hlv (by rw [h, fullInv_var_xor1])
          have h2 : l ≠ lit.toNat := fun h => hlv (by rw [h])
          simp only [h1, h2, ↓reduceIte]; exact (hw.vals_false_iff l hl).mpr ⟨i, by omega, heq⟩
    lvl_le := fun i hi => by
      dsimp [s'] at hi ⊢; rw [htrl_get i hi]
      by_cases hie : i = s.core.trail_end
      · simp only [hie, ↓reduceIte]; rw [hlvl_get v (by omega)]; simp [hcl0]
      · have hilt : i < s.core.trail_end := by omega
        simp only [hie, ↓reduceIte]; rw [hlvl_get _ (by have := hw.trail_lits_lt i hilt; omega)]
        have hle := hw.lvl_le i hilt
        rw [ite_eq_right (hnot_var i hilt)]
        omega
    dec_earliest := fun i j hi hj _ hdec => by
      exfalso; dsimp [s'] at hj; rw [htrl_get j hj] at hdec
      by_cases hje : j = s.core.trail_end
      · simp only [hje, ↓reduceIte] at hdec
        rw [hlvl_get v (by omega)] at hdec; simp at hdec
      · have hjlt : j < s.core.trail_end := by omega
        simp only [hje, ↓reduceIte] at hdec
        have := hw.lvl_le j hjlt; rw [hcl0] at this
        rw [hlvl_get _ (by have := hw.trail_lits_lt j hjlt; omega),
          ite_eq_right (hnot_var j hjlt)] at hdec
        omega
    levels_inhabited := fun L h1 hle => by exfalso; dsimp [s'] at hle; omega
    level0_sound := fun i hi hli => by
      dsimp [s'] at hi; rw [htrl_get i hi] at hli ⊢
      by_cases hie : i = s.core.trail_end
      · simp only [hie, ↓reduceIte] at hli ⊢; exact hent
      · have hilt : i < s.core.trail_end := by omega
        simp only [hie, ↓reduceIte] at hli ⊢
        rw [hlvl_get _ (by have := hw.trail_lits_lt i hilt; omega),
          ite_eq_right (hnot_var i hilt)] at hli
        exact hw.level0_sound i hilt hli
    trail_pos_inv := fun i hi => by
      dsimp [s'] at hi; rw [htrl_get i hi]
      by_cases hie : i = s.core.trail_end
      · subst hie; simp only [↓reduceIte]; dsimp only [s']
        rw [List.getElem?_set_self (by rw [hcl.trail_pos_len]; exact hv_lt),
          Option.getD_some, bv32_ofNat_toNat_w2a hte_lt32]
      · have hilt : i < s.core.trail_end := by omega
        simp only [hie, ↓reduceIte]; dsimp only [s']
        rw [List.getElem?_set_ne (Ne.symm (hnot_var i hilt))]
        exact hw.trail_pos_inv i hilt
    level0_rsn_none := fun idx hidx hli => by
      dsimp [s'] at hidx; rw [htrl_get idx hidx] at hli ⊢
      by_cases hie : idx = s.core.trail_end
      · simp only [hie, ↓reduceIte]; rw [hrsn_get v (by omega)]; simp
      · have hilt : idx < s.core.trail_end := by omega
        simp only [hie, ↓reduceIte] at hli ⊢
        have hnv := hnot_var idx hilt
        rw [hlvl_get _ (by have := hw.trail_lits_lt idx hilt; omega), ite_eq_right hnv] at hli
        rw [hrsn_get _ (by have := hw.trail_lits_lt idx hilt; omega), ite_eq_right hnv]
        exact hw.level0_rsn_none idx hilt hli
    frame_trail_lt := fun L hL => by
      dsimp [s'] at hL ⊢; have hLz : L = 0 := by omega
      subst hLz; have := hw.frame_trail_lt 0 (by omega); omega
    frame_trail_mono := fun L1 L2 _ h2 => by
      dsimp [s'] at h2 ⊢; have : L1 = 0 := by omega
      have : L2 = 0 := by omega
      subst_vars; exact Nat.le_refl _
    frame_trail_before_lt := fun L h1 hle => by exfalso; dsimp [s'] at hle; omega
    frame_dec_lt := fun L h1 hle => by exfalso; dsimp [s'] at hle; omega
    reason_inv := fun idx hidx hne => by
      dsimp [s'] at hidx; rw [htrl_get idx hidx] at hne ⊢
      by_cases hie : idx = s.core.trail_end
      · simp only [hie, ↓reduceIte] at hne
        rw [hrsn_get v (by omega)] at hne; simp at hne
      · have hilt : idx < s.core.trail_end := by omega
        simp only [hie, ↓reduceIte] at hne ⊢
        have hnv := hnot_var idx hilt
        have hidx_lt := hw.trail_lits_lt idx hilt
        rw [hrsn_get _ (by omega), ite_eq_right hnv] at hne ⊢
        have href_eq : fullArenaClauseRefsCore s'.core = fullArenaClauseRefsCore s.core := rfl
        have hgarb_eq : ∀ r, fullArenaClauseGarbCore s'.core r = fullArenaClauseGarbCore s.core r :=
          fun _ => rfl
        have hlits_eq : ∀ r, fullArenaClauseLitsCore s'.core r = fullArenaClauseLitsCore s.core r :=
          fun _ => rfl
        have hri := hw.reason_inv idx hilt hne
        by_cases hc :
            (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 &&&
              2147483648#32) ≠ 0#32
        · simp only [eq_true hc, ↓reduceIte] at hri ⊢
          refine ⟨hri.1, hri.2.1, ?_⟩
          obtain ⟨m, hm, hqm, hle⟩ := hri.2.2
          refine ⟨m, hm, ?_, ?_⟩
          · rw [htrl_get m (by omega), ite_eq_right (by omega)]; exact hqm
          · rw [hlvl_get _ (by omega), hlvl_get _ (by omega), ite_eq_right hnv]
            split
            · exact Nat.zero_le _
            · exact hle
        · simp only [hc, ↓reduceIte] at hri
          simp only [hc, ↓reduceIte, href_eq, hgarb_eq, hlits_eq]
          refine ⟨hri.1, hri.2.1, fun q hq => ?_⟩
          rcases hri.2.2 q hq with hq0 | ⟨m, hm, hqm, hle⟩
          · exact Or.inl hq0
          · have hq_lt : q < 2 * s.core.cur_vars :=
              hw.arena.lits_lt _ hri.1 hri.2.1 q hq
            refine Or.inr ⟨m, hm, ?_, ?_⟩
            · rw [htrl_get m (by omega), ite_eq_right (by omega)]; exact hqm
            · rw [hlvl_get (q / 2) (by omega), hlvl_get _ (by omega), ite_eq_right hnv]
              by_cases hqv : q / 2 = v
              · simp only [hqv, ↓reduceIte]; exact Nat.zero_le _
              · simp only [hqv, ↓reduceIte]; exact hle
    reason_lit_mem := fun idx hidx hne hlg => by
      dsimp [s'] at hidx; rw [htrl_get idx hidx] at hne hlg ⊢
      by_cases hie : idx = s.core.trail_end
      · simp only [hie, ↓reduceIte] at hne
        rw [hrsn_get v (by omega)] at hne; simp at hne
      · have hilt : idx < s.core.trail_end := by omega
        simp only [hie, ↓reduceIte] at hne hlg ⊢
        have hnv := hnot_var idx hilt
        rw [hrsn_get _ (by have := hw.trail_lits_lt idx hilt; omega), ite_eq_right hnv] at hne hlg ⊢
        simpa [fullArenaClauseLitsCore, fullArenaClauseSizeCore, s'] using
          hw.reason_lit_mem idx hilt hne hlg },
    hdw.2.2.1, hdw.2.2.2.1, FullExtScratchOk.of_pres hdw.2.2.2.2.1 ⟨rfl, rfl⟩ fun _ hr => hr,
    hcl0, hdw.2.2.2.2.2.2⟩

/-! ## 4. Loop Invariants for `full_bve_var_m7_wp` -/

@[expose] public def BveVarLoopsInv (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s_start : FullState) (m8 : Bool) (v np nn : BitVec 32)
    (rp _r_cnt _w_est : BitVec 64) (_fit : Bool) (_res_sz : BitVec 64)
    (s : FullState) (m : Mem 64) (R : Mem 64 → Prop) : Prop :=
  FullDenseInvW c F0 F_cur s ∧ TmkZero s ∧
  s.core.cur_vars = s_start.core.cur_vars ∧ s.core.fuel.toNat ≤ s_start.core.fuel.toNat ∧
  (∀ i < np.toNat, FullBveEntryOkW F_cur s (2 * v.toNat) (s.scratch.scratch_buf[i]?.getD 0#32)) ∧
  (∀ j < nn.toNat, FullBveEntryOkW F_cur s (2 * v.toNat + 1)
    (s.scratch.scratch_buf[bveOccLim m8 + j]?.getD 0#32)) ∧
  bveROff m8 ≤ rp.toNat ∧ rp.toNat ≤ c.scratch_cap ∧
  FullResBufOkW F_cur s rp.toNat (bveROff m8) ∧ (FullMem c s ⋆ R) m

end LeanQbe.T.Examples.Kissat.Proof.Eliminate
