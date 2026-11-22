module

public import LeanQbe.T.Examples.Kissat.FullM6BveFwdProof4
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Examples.Kissat.FullDenseWatchLemmas1
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Wave-2 `PR-W2D` (`RC-22`) Proofs — Part 5 (`full_bve_var_m6_wp`)

M1-clean proof module (`public section`, `0` `@[expose]`, `0` `import all`, `private` helpers):
- Proves `full_bve_var_m6_wp`, directly certifying canonical `FullFastBveBudgets.fullBveVarDefSpec`,
  plus canonical `Full.fullBveVarSpec` corollary `full_bve_var_m6_wp_canon`.
- Covers `occlim = 512`, `clslim = 100`, `resolve_gate`, `watch_stk` OOM pre-check with
  `full_wstack_defrag` retry before weakening, dense unit flush, and BCE fallback.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM6BveFwd

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullDenseWatchHelpers
open LeanQbe.T.Examples.Kissat.FullFastBveBudgets
open Kraken.Bedrock2.Test

open scoped FullArenaTactics

local macro "m6_call" h:term : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_))

private theorem m6_resBuf_mono5 {F_cur : List (List Nat)} {s s' : FullState}
    {r_end p : Nat} (hcv : s'.core.cur_vars = s.core.cur_vars)
    (heq : ∀ idx, p ≤ idx → idx < r_end →
      s'.scratch.scratch_buf[idx]? = s.scratch.scratch_buf[idx]?)
    (h : FullResBufOkW F_cur s r_end p) : FullResBufOkW F_cur s' r_end p := by
  induction h with
  | nil => exact .nil
  | @cons p sz hle hsz hlt hnd hent _ ih =>
    have h0 := heq p (Nat.le_refl _) (by omega)
    have hk : ∀ k < sz, s'.scratch.scratch_buf[p + 1 + k]? = s.scratch.scratch_buf[p + 1 + k]? :=
      fun k hk => heq (p + 1 + k) (by omega) (by omega)
    refine .cons hle (by rw [h0]; exact hsz)
      (fun k hkl => by rw [hk k hkl, hcv]; exact hlt k hkl) ?_ ?_
      (ih fun idx hi1 hi2 => heq idx (by omega) hi2)
    · have hm : ((List.range sz).map fun k =>
          (s'.scratch.scratch_buf[p + 1 + k]?.getD 0#32).toNat / 2) =
          ((List.range sz).map fun k =>
          (s.scratch.scratch_buf[p + 1 + k]?.getD 0#32).toNat / 2) :=
        List.map_congr_left fun k hkm => by rw [hk k (List.mem_range.mp hkm)]
      rw [hm]; exact hnd
    · have hm : ((List.range sz).map fun k =>
          (s'.scratch.scratch_buf[p + 1 + k]?.getD 0#32).toNat) =
          ((List.range sz).map fun k =>
          (s.scratch.scratch_buf[p + 1 + k]?.getD 0#32).toNat) :=
        List.map_congr_left fun k hkm => by rw [hk k (List.mem_range.mp hkm)]
      rw [hm]; exact hent

private theorem m6_resBuf_append5 {F_cur : List (List Nat)} {s s' : FullState}
    {r_off rp sz : Nat} (hcv : s'.core.cur_vars = s.core.cur_vars)
    (hpref : ∀ idx, r_off ≤ idx → idx < rp →
      s'.scratch.scratch_buf[idx]? = s.scratch.scratch_buf[idx]?)
    (h : FullResBufOkW F_cur s rp r_off)
    (hsz : (s'.scratch.scratch_buf[rp]?.getD 0#32).toNat = sz)
    (hlt : ∀ k < sz, (s'.scratch.scratch_buf[rp + 1 + k]?.getD 0#32).toNat < 2 * s'.core.cur_vars)
    (hnd : ((List.range sz).map fun k =>
      (s'.scratch.scratch_buf[rp + 1 + k]?.getD 0#32).toNat / 2).Nodup)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause ((List.range sz).map fun k =>
      (s'.scratch.scratch_buf[rp + 1 + k]?.getD 0#32).toNat))) :
    FullResBufOkW F_cur s' (rp + 1 + sz) r_off := by
  induction h with
  | nil => exact .cons (Nat.le_refl _) hsz hlt hnd hent .nil
  | @cons p psz hle hpsz hplt hpnd hpent _ ih =>
    have h0 := hpref p (Nat.le_refl _) (by omega)
    have hk : ∀ k < psz, s'.scratch.scratch_buf[p + 1 + k]? = s.scratch.scratch_buf[p + 1 + k]? :=
      fun k hk => hpref (p + 1 + k) (by omega) (by omega)
    refine .cons (by omega) (by rw [h0]; exact hpsz)
      (fun k hkl => by rw [hk k hkl, hcv]; exact hplt k hkl) ?_ ?_
      (ih fun idx hi1 hi2 => hpref idx (by omega) hi2)
    · have hm : ((List.range psz).map fun k =>
          (s'.scratch.scratch_buf[p + 1 + k]?.getD 0#32).toNat / 2) =
          ((List.range psz).map fun k =>
          (s.scratch.scratch_buf[p + 1 + k]?.getD 0#32).toNat / 2) :=
        List.map_congr_left fun k hkm => by rw [hk k (List.mem_range.mp hkm)]
      rw [hm]; exact hpnd
    · have hm : ((List.range psz).map fun k =>
          (s'.scratch.scratch_buf[p + 1 + k]?.getD 0#32).toNat) =
          ((List.range psz).map fun k =>
          (s.scratch.scratch_buf[p + 1 + k]?.getD 0#32).toNat) :=
        List.map_congr_left fun k hkm => by rw [hk k (List.mem_range.mp hkm)]
      rw [hm]; exact hpent

private theorem m6_bveEntry_weak {F_cur : List (List Nat)} {s : FullState} {lit : Nat}
    {w : BitVec 32} (h : FullBveEntryOkW F_cur s lit w) : FullBveWeakItemOk s.core w := by
  unfold FullBveEntryOkW at h; unfold FullBveWeakItemOk; split at h <;> simp_all

private theorem m6_bveEntry_bce {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hdw : FullDenseInvW c F0 F_cur s) {lit : Nat} {w : BitVec 32}
    (h : FullBveEntryOkW F_cur s lit w) :
    FullBveBceWeakOk c s w ∧
    ((w &&& 0x80000000#32) = 0#32 → ((fullArenaClauseLits s w.toNat).map (· / 2)).Nodup) := by
  unfold FullBveEntryOkW at h; unfold FullBveBceWeakOk
  have hcv := hdw.1.core_ok.cur_vars_le
  by_cases hb : (w &&& 0x80000000#32) ≠ 0#32
  · rw [ite_eq_left hb] at h ⊢; exact ⟨by omega, fun heq => absurd heq hb⟩
  · rw [ite_eq_right hb] at h ⊢
    have hwf := hdw.2.1.arena.refs_wf w.toNat h.1
    refine ⟨⟨h.1, Nat.le_trans hwf.2.2.1 hwf.2.2.2.1, fun l hl => ?_⟩,
      fun _ => hdw.2.2.2.1 w.toNat h.1 h.2⟩
    have := hdw.2.1.arena.lits_lt w.toNat h.1 h.2 l hl; omega

private theorem m6_bveEntry_extNeed {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hdw : FullDenseInvW c F0 F_cur s) {lit : Nat} {w : BitVec 32}
    (h : FullBveEntryOkW F_cur s lit w) :
    (w &&& 0x80000000#32) ≠ 0#32 ∨ w.toNat + 2 < c.arena_cap := by
  unfold FullBveEntryOkW at h
  by_cases hb : (w &&& 0x80000000#32) ≠ 0#32
  · exact Or.inl hb
  · right; rw [ite_eq_right hb] at h
    have hwf := hdw.2.1.arena.refs_wf w.toNat h.1
    have hal := hdw.1.core_ok.arena_len_le; omega

private theorem m6_bce_hm {c : FullCfg} {se : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {w w0 : BitVec 32} (hw_eq : w = w0)
    (hw0_lt : w0.toNat < se.core.arena.length)
    (hw_ne : w0.toNat ≠ (w0.setWidth 64 + 2#64).toNat)
    {hw : (w.setWidth 64).toNat < se.core.arena.length}
    {hw2 : (w.setWidth 64 + 2).toNat < (se.core.arena.set (w.setWidth 64).toNat
      (se.core.arena[(w.setWidth 64).toNat]'hw ||| 524288)).length}
    {hw0_2 : (w0.setWidth 64 + 2#64).toNat < se.core.arena.length}
    (hhdr : se.core.arena[w0.toNat]'hw0_lt = fullArenaHdr se w0.toNat)
    (hm : (FullMem c { se with
      core := { se.core with
        arena := se.core.arena.set (w.setWidth 64).toNat
          (se.core.arena[(w.setWidth 64).toNat]'hw ||| 524288),
        arena_garbage := se.core.arena_garbage + 3 +
          ((se.core.arena.set (w.setWidth 64).toNat
            (se.core.arena[(w.setWidth 64).toNat]'hw ||| 524288))[(w.setWidth 64 +
              2).toNat]'hw2).setWidth 64 }
      scratch := { se.scratch with bce_cnt := se.scratch.bce_cnt + 1 } } ⋆ R) m) :
    (FullMem c { se with
      core := { se.core with
        arena := se.core.arena.set w0.toNat (fullArenaHdr se w0.toNat ||| 0x00080000#32),
        arena_garbage := se.core.arena_garbage + 3#64 +
          (se.core.arena[(w0.setWidth 64 + 2#64).toNat]'hw0_2).setWidth 64 }
      scratch := { se.scratch with bce_cnt := se.scratch.bce_cnt + 1#64 } } ⋆ R) m := by
  subst hw_eq
  have hz : (w.setWidth 64).toNat = w.toNat := m6_zext32_toNat w
  have har_eq : se.core.arena.set (w.setWidth 64).toNat
      (se.core.arena[(w.setWidth 64).toNat]'hw ||| 524288) =
      se.core.arena.set w.toNat (fullArenaHdr se w.toNat ||| 0x00080000#32) := by
    exact congrArg (se.core.arena.set w.toNat)
      (by rw [m6_getElem_congr hz hw hw0_lt, hhdr]; rfl)
  have hag_eq : se.core.arena_garbage + 3 +
      ((se.core.arena.set (w.setWidth 64).toNat
        (se.core.arena[(w.setWidth 64).toNat]'hw ||| 524288))[(w.setWidth 64 +
          2).toNat]'hw2).setWidth 64 =
      se.core.arena_garbage + 3#64 +
      (se.core.arena[(w.setWidth 64 + 2#64).toNat]'hw0_2).setWidth 64 := by
    have h2 : (2 : BitVec 64) = 2#64 := rfl
    have hne' : (w.setWidth 64).toNat ≠ (w.setWidth 64 + 2).toNat := by
      rw [hz, h2]; exact hw_ne
    have hge_ne : (se.core.arena.set (w.setWidth 64).toNat
        (se.core.arena[(w.setWidth 64).toNat]'hw ||| 524288))[(w.setWidth 64 +
          2).toNat]'hw2 =
        se.core.arena[(w.setWidth 64 + 2).toNat]'(by
          rw [List.length_set] at hw2; exact hw2) := by
      rw [List.getElem_set_ne hne']
    have hge_eq : se.core.arena[(w.setWidth 64 + 2).toNat]'(by
        rw [List.length_set] at hw2; exact hw2) =
        se.core.arena[(w.setWidth 64 + 2#64).toNat]'hw0_2 :=
      m6_getElem_congr (by rw [h2]) _ hw0_2
    rw [hge_ne, hge_eq]; rfl
  have hs_eq : ({ se with
      core := { se.core with
        arena := se.core.arena.set (w.setWidth 64).toNat
          (se.core.arena[(w.setWidth 64).toNat]'hw ||| 524288),
        arena_garbage := se.core.arena_garbage + 3 +
          ((se.core.arena.set (w.setWidth 64).toNat
            (se.core.arena[(w.setWidth 64).toNat]'hw ||| 524288))[(w.setWidth 64 +
              2).toNat]'hw2).setWidth 64 }
      scratch := { se.scratch with bce_cnt := se.scratch.bce_cnt + 1 } } : FullState) =
      { se with
      core := { se.core with
        arena := se.core.arena.set w.toNat (fullArenaHdr se w.toNat ||| 0x00080000#32),
        arena_garbage := se.core.arena_garbage + 3#64 +
          (se.core.arena[(w.setWidth 64 + 2#64).toNat]'hw0_2).setWidth 64 }
      scratch := { se.scratch with bce_cnt := se.scratch.bce_cnt + 1#64 } } := by
    rw [hag_eq, har_eq, show (1 : BitVec 64) = 1#64 from rfl]
  rwa [hs_eq] at hm

private theorem m6_bveEntry_core {F_cur : List (List Nat)} {s s' : FullState}
    {lit : Nat} {w : BitVec 32} (h : FullBveEntryOkW F_cur s lit w)
    (hcv : s'.core.cur_vars = s.core.cur_vars) (har : s'.core.arena = s.core.arena)
    (hal : s'.core.arena_len = s.core.arena_len) : FullBveEntryOkW F_cur s' lit w := by
  unfold FullBveEntryOkW at h ⊢
  by_cases hb : (w &&& 0x80000000#32) ≠ 0#32
  · rw [ite_eq_left hb] at h ⊢; exact ⟨by rw [hcv]; exact h.1, h.2⟩
  · rw [ite_eq_right hb] at h ⊢
    have hrefs : fullArenaClauseRefs s' = fullArenaClauseRefs s := by
      unfold fullArenaClauseRefs fullArenaClauseRefsCore; rw [har, hal]
    have hgb : fullArenaClauseGarb s' w.toNat = fullArenaClauseGarb s w.toNat := by
      unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore; rw [har]
    rw [hrefs, hgb]; exact h

private theorem m6_bceWeak_congr {c : FullCfg} {s s' : FullState} {w : BitVec 32}
    (h : FullBveBceWeakOk c s w) (hrefs : fullArenaClauseRefs s' = fullArenaClauseRefs s)
    (hal : s'.core.arena_len = s.core.arena_len)
    (hsz : ∀ r ∈ fullArenaClauseRefs s, fullArenaClauseSize s' r = fullArenaClauseSize s r)
    (hlits : ∀ r ∈ fullArenaClauseRefs s, fullArenaClauseLits s' r = fullArenaClauseLits s r) :
    FullBveBceWeakOk c s' w := by
  unfold FullBveBceWeakOk at h ⊢
  by_cases hb : (w &&& 0x80000000#32) ≠ 0#32
  · rw [ite_eq_left hb] at h ⊢; exact h
  · rw [ite_eq_right hb] at h ⊢; rw [hrefs, hal, hsz _ h.1, hlits _ h.1]; exact h

private theorem m6_fullDenseInvW_setInact {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (h : FullDenseInvW c F0 F_cur s)
    {fl' : List (BitVec 32)} {unass' : BitVec 64} (hfl : fl'.length = c.max_vars) :
    FullDenseInvW c F0 F_cur
      { s with core := { s.core with flags := fl', unassigned := unass' } } :=
  ⟨⟨{ h.1.core_ok with flags_len := hfl }, h.1.scratch_ok⟩,
   { h.2.1 with
     arena := { h.2.1.arena with len_ok := h.2.1.arena.len_ok }
     watches := h.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) },
   h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

private theorem m6_fullDenseInvW_delBin {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s)
    {wvec' wstk' : List (BitVec 32)} {wu' nb' : BitVec 64}
    (hlen' : ({ s with core :=
      { s.core with wvec := wvec', wstk := wstk', wusable := wu', num_binary := nb' } } :
      FullState).LengthsOk c)
    (hw' : ModeWatchesInv F_cur
      { s.core with wvec := wvec', wstk := wstk', wusable := wu', num_binary := nb' }) :
    FullDenseInvW c F0 F_cur
      { s with core :=
        { s.core with wvec := wvec', wstk := wstk', wusable := wu', num_binary := nb' } } :=
  ⟨hlen', { h.2.1 with arena := { h.2.1.arena with len_ok := h.2.1.arena.len_ok }, watches := hw' },
   h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

private theorem m6_pl_nl_eq5 (v : BitVec 32) (hv : v.toNat < 2 * 2 ^ 28) :
    (v <<< (1 : Nat)).toNat = 2 * v.toNat ∧
    ((v <<< (1 : Nat)) ||| (1 : BitVec 32)).toNat = 2 * v.toNat + 1 := by
  have h1 : (v <<< (1 : Nat)).toNat = 2 * v.toNat := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]; omega
  have h2 : ((v <<< (1 : Nat)) ||| (1 : BitVec 32)).toNat = 2 * v.toNat + 1 := by
    rw [BitVec.toNat_or, h1, show ((1 : BitVec 32)).toNat = 1 from rfl]
    apply Nat.eq_of_testBit_eq; intro i
    cases i with
    | zero => simp [Nat.testBit_zero, Nat.mul_add_mod_self_left]
    | succ j =>
      rw [Nat.testBit_or, Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_succ]
      simp [Nat.mul_add_div (by omega : 0 < 2)]
  exact ⟨h1, h2⟩

private theorem m6_markGarb_pres_lits {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s) {cref : Nat}
    (href : cref ∈ fullArenaClauseRefs s) {ag' : BitVec 64} :
    let ar' := s.core.arena.set cref (fullArenaHdr s cref ||| 0x00080000#32)
    let s' : FullState := { s with core := { s.core with arena := ar', arena_garbage := ag' } }
    FullDenseInvW c F0 F_cur s' ∧ fullArenaClauseRefs s' = fullArenaClauseRefs s ∧
    (∀ r ∈ fullArenaClauseRefs s,
      fullArenaClauseSize s' r = fullArenaClauseSize s r ∧
      fullArenaClauseLits s' r = fullArenaClauseLits s r) := by
  intro ar' s'
  have hcl := h.1.core_ok; have hw := h.2.1
  have hcref_wf := hw.arena.refs_wf cref href
  have har_len : cref < s.core.arena.length := by
    have := hcl.arena_len_le; have := hcl.arena_len_arr; omega
  have hmg := m6_fullDenseInvW_markGarb h href (arena' := ar') (ag' := ag')
    (by simp [ar', hcl.arena_len_arr]) (Or.inl (List.getElem?_set_self har_len))
    (fun i hne _ => List.getElem?_set_ne (Ne.symm hne))
  refine ⟨hmg.1, hmg.2, fun r hr => ?_⟩
  have hwf := hw.arena.refs_wf r hr
  have hbd : r + 3 + fullArenaClauseSizeCore s.core r ≤ s.core.arena.length := by
    have := hcl.arena_len_le; have := hcl.arena_len_arr; omega
  have hsz : fullArenaClauseSizeCore s'.core r = fullArenaClauseSizeCore s.core r := by
    unfold fullArenaClauseSizeCore; dsimp only [s', ar']
    by_cases hrc : r = cref
    · subst hrc; rw [List.getElem?_set_ne (by omega)]
    · rcases Nat.lt_or_gt_of_ne hrc with hlt | hgt
      · have := fullArenaScanRefs_disjoint hr href hlt
        rw [List.getElem?_set_ne (by omega)]
      · have := fullArenaScanRefs_disjoint href hr hgt
        rw [List.getElem?_set_ne (by omega)]
  have hlits : fullArenaClauseLitsCore s'.core r = fullArenaClauseLitsCore s.core r :=
    fullArenaClauseLitsCore_eq_of_hold hbd (by simp [s', ar', hbd]) hsz fun j hj => by
      dsimp only [s', ar']
      by_cases hrc : r = cref
      · subst hrc; exact List.getElem?_set_ne (by omega)
      · rcases Nat.lt_or_gt_of_ne hrc with hlt | hgt
        · have := fullArenaScanRefs_disjoint hr href hlt
          exact List.getElem?_set_ne (by omega)
        · have := fullArenaScanRefs_disjoint href hr hgt
          exact List.getElem?_set_ne (by omega)
  exact ⟨hsz, hlits⟩

private theorem m6_fullDenseInvW_set_scratch5 {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (h : FullDenseInvW c F0 F_cur s)
    {scr' : List (BitVec 32)} (hlen : scr'.length = c.scratch_cap) :
    FullDenseInvW c F0 F_cur
      { s with scratch := { s.scratch with scratch_buf := scr' } } :=
  m6_fullDenseInvW_with_scratch h
    { walk_vals_len := h.1.scratch_ok.walk_vals_len
      phases_len := h.1.scratch_ok.phases_len
      phases_target_len := h.1.scratch_ok.phases_target_len
      phases_best_len := h.1.scratch_ok.phases_best_len
      walk_best_len := h.1.scratch_ok.walk_best_len
      heap_len_arr := h.1.scratch_ok.heap_len_arr
      pos_len := h.1.scratch_ok.pos_len
      shrink_stk_len := h.1.scratch_ok.shrink_stk_len
      q_prev_len := h.1.scratch_ok.q_prev_len
      q_next_len := h.1.scratch_ok.q_next_len
      q_stamp_len := h.1.scratch_ok.q_stamp_len
      wsort_len := h.1.scratch_ok.wsort_len
      work_stk1_len := h.1.scratch_ok.work_stk1_len
      work_stk2_len := h.1.scratch_ok.work_stk2_len
      tarjan_mark_len := h.1.scratch_ok.tarjan_mark_len
      tarjan_reach_len := h.1.scratch_ok.tarjan_reach_len
      score_len := h.1.scratch_ok.score_len
      sim_sig_len := h.1.scratch_ok.sim_sig_len
      glue_used_len := h.1.scratch_ok.glue_used_len
      last_learned_len := h.1.scratch_ok.last_learned_len
      delayed_len_arr := h.1.scratch_ok.delayed_len_arr
      red_refs_len := h.1.scratch_ok.red_refs_len
      extend_stk_len := h.1.scratch_ok.extend_stk_len
      scratch_buf_len := hlen }
    rfl rfl

private theorem m6_list_take_map_eq_range {xs : List (BitVec 32)} {n : Nat} (hn : n ≤ xs.length) :
    (xs.take n).map BitVec.toNat =
      (List.range n).map (fun k => (xs[k]?.getD 0#32).toNat) := by
  apply List.ext_getElem
  · simp [hn]
  · intro i hi1 hi2
    simp only [List.getElem_map, List.getElem_take, List.getElem_range]
    have hi : i < n := by simp at hi2; exact hi2
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]

private theorem m6_list_take_map_div2_eq_range {xs : List (BitVec 32)} {n : Nat}
    (hn : n ≤ xs.length) :
    (xs.take n).map (fun x => x.toNat / 2) =
      (List.range n).map (fun k => (xs[k]?.getD 0#32).toNat / 2) := by
  apply List.ext_getElem
  · simp [hn]
  · intro i hi1 hi2
    simp only [List.getElem_map, List.getElem_take, List.getElem_range]
    have hi : i < n := by simp at hi2; exact hi2
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]

private theorem m6_denseInv_of_extPush {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s s' : FullState} (h : FullDenseInvW c F0 F_cur s) (hlen' : s'.LengthsOk c)
    (hcore : s'.core = s.core) (hll : s'.scratch.last_learned = s.scratch.last_learned)
    (hext : s'.scratch.extend_len ≤ c.extend_cap) : FullDenseInvW c F0 F_cur s' :=
  ⟨hlen', hcore ▸ h.2.1,
   ⟨fun v hv => by rw [hcore]; exact h.2.2.1.1 v hv,
    fun l hl => by rw [hcore]; exact h.2.2.1.2 l hl⟩,
   fun r hr hng => by
     change r ∈ fullArenaClauseRefsCore s'.core at hr; rw [hcore] at hr
     change fullArenaClauseGarbCore s'.core r = false at hng; rw [hcore] at hng
     change ((fullArenaClauseLitsCore s'.core r).map (· / 2)).Nodup
     rw [hcore]; exact h.2.2.2.1 r hr hng,
   ⟨fun k hk => by
     change s'.scratch.last_learned[k]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 ∨
       _ ∈ fullArenaClauseRefsCore s'.core
     rw [hll, hcore]; exact h.2.2.2.2.1.1 k hk, hext⟩,
   by rw [hcore]; exact h.2.2.2.2.2.1, by rw [hcore]; exact h.2.2.2.2.2.2⟩

/-! ## 1. `full_bve_var_m6_wp` (Canonical `FullFastBveBudgets.fullBveVarDefSpec`) -/

/-- Parametric `Func.wp` proof for `full_bve_var_m6`, directly certifying canonical
`FullFastBveBudgets.fullBveVarDefSpec`. -/
theorem full_bve_var_m6_wp (Γ : Env)
    (hCollect : ∀ a m Q X, Full.fullBveCollectSpec a m Q X →
      Γ "full_bve_collect_m6" [i64, i32, i64, i32] [i32] a m Q X)
    (hExtNeed : ∀ a m Q X, Full.fullBveExtNeedSpec a m Q X →
      Γ "full_bve_ext_need" [i64, i32, i32] [i64] a m Q X)
    (hWeaken : ∀ a m Q X, FullFastBveBudgets.fullBveWeakenTmkSpec a m Q X →
      Γ "full_bve_weaken" [i64, i32, i32, i32] [.bool] a m Q X)
    (hSetInact : ∀ a m Q X, Full.fullSetInactiveSpec a m Q X →
      Γ "full_set_inactive" [i64, i32, i32] [] a m Q X)
    (hGates : ∀ a m Q X, fullBveGatesM6Spec a m Q X →
      Γ "full_bve_gates_m6" [i64, i32, i32, i32] [] a m Q X)
    (hResPair : ∀ a m Q X, Full.fullBveResolvePairSpec a m Q X →
      Γ "full_bve_resolve_pair" [i64, i32, i32, i32] [.bool] a m Q X)
    (hDefrag : ∀ a m Q X, Full.fullWstackDefragSpec a m Q X →
      Γ "full_wstack_defrag" [i64] [] a m Q X)
    (hCommit : ∀ a m Q X, FullFastBveBudgets.fullBveCommitResTmkSpec a m Q X →
      Γ "full_bve_commit_res" [i64, i64, i64] [i64] a m Q X)
    (hFlushUnits : ∀ a m Q X, fullDenseFlushUnitsM6Spec a m Q X →
      Γ "full_dense_flush_units_m6" [i64] [.bool] a m Q X)
    (hTryBce : ∀ a m Q X, Full.fullBveTryBceSpec a m Q X →
      Γ "full_bve_try_bce" [i64, i32, i32, i32, i32] [.bool] a m Q X)
    (hExtPush2 : ∀ a m Q X, FullFastBveBudgets.fullExtendPush2TmkSpec a m Q X →
      Γ "full_extend_push2" [i64, i32, i32] [.bool] a m Q X)
    (hDelBin : ∀ a m Q X, Full.fullDeleteBinarySpec a m Q X →
      Γ "full_delete_binary" [i64, i32, i32] [] a m Q X)
    (hExtPushCl : ∀ a m Q X, FullFastBveBudgets.fullExtendPushClTmkSpec a m Q X →
      Γ "full_extend_push_cl" [i64, i32, i32] [.bool] a m Q X) :
    ∀ a m Q X, FullFastBveBudgets.fullBveVarDefSpec a m Q X →
      Func.wp Γ full_bve_var_m6_body a m Q X := by
  rintro ⟨h, v, ⟨⟩⟩ m0 Q X ⟨c, F0, s0, R, rfl, hd0, htmk0, hv_lt, hm0, hQ⟩
  have hmx := c.hmaxv; have hsc := c.hscr; have harc := c.harena; have hwc := c.hwcap
  unfold dimacsBound at hmx hsc harc hwc
  obtain ⟨F_cur, hdw0⟩ := hd0.exists_witness
  have hcv_le := hdw0.1.core_ok.cur_vars_le
  have hplnl := m6_pl_nl_eq5 v (by omega)
  unfold Func.wp full_bve_var_m6_body
  c0_hsplit
  · c0_hsteps!
    exact hQ 1#64 s0 m0 hd0 htmk0 (Nat.le_refl _) (Nat.le_refl _) (Or.inl rfl) (by simp) hm0
  · have hsc2048 : 2048 ≤ c.scratch_cap := by
      rw [Nat.mod_eq_of_lt (by omega), show (2048 : BitVec 64).toNat = 2048 from rfl] at hc
      omega
    c0_hsteps_nogrp
    -- Collect positive occurrences into `scr[0 ..< np)` (`cap = 512`)
    m6_call hCollect
    dsimp only [vals, Arg.val]
    refine ⟨c, F0, F_cur, s0, 0, R, rfl, hdw0, by rw [hplnl.1]; omega,
      by simp, by simp; omega, hm0, ?_⟩
    intro np scr1 m1
    dsimp only
    intro hsc1 hout1 hnp_ok hm1
    let s1 : FullState := { s0 with scratch := { s0.scratch with scratch_buf := scr1 } }
    have hdw1 : FullDenseInvW c F0 F_cur s1 := m6_fullDenseInvW_set_scratch5 hdw0 hsc1
    c0_hsteps_nogrp
    -- Collect negative occurrences into `scr[512 ..< 512 + nn)` (`cap = 512`)
    m6_call hCollect
    dsimp only [vals, Arg.val]
    refine ⟨c, F0, F_cur, s1, 512, R, rfl, hdw1, by dsimp only [s1]; rw [hplnl.2]; omega,
      by rfl, by simp; omega, hm1, ?_⟩
    intro nn scr2 m2
    dsimp only
    intro hsc2 hout2 hnn_ok hm2
    let s2 : FullState := { s1 with scratch := { s1.scratch with scratch_buf := scr2 } }
    have hdw2 : FullDenseInvW c F0 F_cur s2 := m6_fullDenseInvW_set_scratch5 hdw1 hsc2
    c0_hsplit
    · c0_hsteps!
      exact hQ 1#64 s2 m2 hdw2.toDense htmk0 (Nat.le_refl _) (Nat.le_refl _) (Or.inl rfl)
        (by simp) hm2
    · have hnp_ne : np ≠ 0xFFFFFFFF#32 := hc
      c0_hsplit
      · c0_hsteps!
        exact hQ 1#64 s2 m2 hdw2.toDense htmk0 (Nat.le_refl _) (Nat.le_refl _) (Or.inl rfl)
          (by simp) hm2
      · have hnn_ne : nn ≠ 0xFFFFFFFF#32 := hc
        obtain ⟨hnp512, hent_p1⟩ := hnp_ok.resolve_left hnp_ne
        obtain ⟨hnn512, hent_n2⟩ := hnn_ok.resolve_left hnn_ne
        have hnp512' : np.toNat ≤ 512 := by simpa using hnp512
        have hnn512' : nn.toNat ≤ 512 := by simpa using hnn512
        have hent_p2 : ∀ i < np.toNat,
            FullBveEntryOkW F_cur s2 (2 * v.toNat) (scr2[i]?.getD 0#32) := fun i hi => by
          rw [hout2 i (by omega) (Or.inl (by omega))]
          have h := hent_p1 i hi; rw [Nat.zero_add, hplnl.1] at h
          exact m6_bveEntry_core h rfl rfl rfl
        have hent_n2' : ∀ j < nn.toNat,
            FullBveEntryOkW F_cur s2 (2 * v.toNat + 1) (scr2[512 + j]?.getD 0#32) := fun j hj => by
          have h := hent_n2 j hj; rw [hplnl.2] at h; exact h
        c0_hsteps_nogrp
        m6_call hExtNeed
        dsimp only [vals, Arg.val]
        refine ⟨c, s2, R, rfl, hdw2.1, by simp; omega, fun i hi => by
          dsimp only [s2]; rw [show ((0 : BitVec 32)).toNat = 0 from rfl, Nat.zero_add]
          exact m6_bveEntry_extNeed hdw2 (hent_p2 i hi), hm2, ?_⟩
        intro en1
        c0_hsteps_nogrp
        m6_call hExtNeed
        dsimp only [vals, Arg.val]
        refine ⟨c, s2, R, rfl, hdw2.1, by simp; omega, fun j hj => by
          dsimp only [s2]; exact m6_bveEntry_extNeed hdw2 (hent_n2' j hj), hm2, ?_⟩
        intro en2
        -- Pure-literal fast path (`ext_ok && (np == 0 || nn == 0)`) and general BVE path (`J25`)
        c0_hsteps_nogrp
        refine wp_join0 (P := fun mj => mj = m2)
          (fun _ mj hmj => by
            rcases hmj.symm with rfl
            c0_hsteps_nogrp
            refine wp_join_state (ts := [i64, i64, i64, .bool])
              (α := BitVec 64 × BitVec 64 × BitVec 64 × Bool × FullState)
              (fun x => (x.1, x.2.1, x.2.2.1, x.2.2.2.1, ()))
              (fun x mi =>
                let si := x.2.2.2.2
                let rp := x.1
                FullDenseInvW c F0 F_cur si ∧ TmkZero si ∧
                si.core.cur_vars = s0.core.cur_vars ∧ si.core.arena = s2.core.arena ∧
                si.core.arena_len = s2.core.arena_len ∧
                si.core.fuel.toNat ≤ s0.core.fuel.toNat ∧
                1088 ≤ rp.toNat ∧ rp.toNat ≤ c.scratch_cap ∧
                FullResBufOkW F_cur si rp.toNat 1088 ∧
                (∀ k < np.toNat, si.scratch.scratch_buf[k]? = s2.scratch.scratch_buf[k]?) ∧
                (∀ k < nn.toNat,
                  si.scratch.scratch_buf[512 + k]? = s2.scratch.scratch_buf[512 + k]?) ∧
                (FullMem c si ⋆ R) mi)
              (fun _ ⟨rp, r_cnt, w_est, fit, si⟩ mi
                  ⟨hdwi, htmki, hcvi, hari, hali, hfli, hrp_lo, hrp_hi, hres_i, hkeep_pi,
                    hkeep_ni, hmi⟩ => by
                c0_hsteps_nogrp
                -- Post-resolution: `ar_need`/`w_need` pre-check (with optional `wstack_defrag`),
                -- then commit (`fit = true`) or BCE fallback (`fit = false`).
                refine wp_join_state (ts := [.bool]) (α := Bool × FullState) (fun x => (x.1, ()))
                  (fun x mp =>
                    FullDenseInvW c F0 F_cur x.2 ∧ TmkZero x.2 ∧
                    x.2.core.cur_vars = s0.core.cur_vars ∧ x.2.core.arena = s2.core.arena ∧
                    x.2.core.arena_len = s2.core.arena_len ∧
                    x.2.core.fuel.toNat ≤ s0.core.fuel.toNat ∧
                    FullResBufOkW F_cur x.2 rp.toNat 1088 ∧
                    (∀ k < np.toNat, x.2.scratch.scratch_buf[k]? = s2.scratch.scratch_buf[k]?) ∧
                    (∀ k < nn.toNat,
                      x.2.scratch.scratch_buf[512 + k]? = s2.scratch.scratch_buf[512 + k]?) ∧
                    (FullMem c x.2 ⋆ R) mp)
                  (fun _ ⟨fit_f, sf⟩ mf
                      ⟨hdwf, htmkf, hcvf, harf, half, hflf, hresf, hkeep_pf, hkeep_nf, hmf⟩ => by
                    dsimp only at hcvf harf half hflf
                    have hent_pf : ∀ k < np.toNat, FullBveEntryOkW F_cur sf (2 * v.toNat)
                        (sf.scratch.scratch_buf[k]?.getD 0#32) := fun k hk => (by
                      rw [hkeep_pf k hk]; exact m6_bveEntry_core (hent_p2 k hk) hcvf harf half)
                    have hent_nf : ∀ k < nn.toNat, FullBveEntryOkW F_cur sf (2 * v.toNat + 1)
                        (sf.scratch.scratch_buf[512 + k]?.getD 0#32) := fun k hk => (by
                      rw [hkeep_nf k hk]
                      exact m6_bveEntry_core (hent_n2' k hk) hcvf harf half)
                    c0_hsplit
                    · -- `fit_f = true`: weaken `pl` & `nl`, set inactive, commit, flush units
                      c0_hsteps_nogrp
                      refine wp_join0 (P := fun mo => ∃ so : FullState,
                          FullDenseInvW c F0 F_cur so ∧ TmkZero so ∧
                          so.core.cur_vars = s0.core.cur_vars ∧
                          so.core.fuel.toNat ≤ s0.core.fuel.toNat ∧
                          (FullMem c so ⋆ R) mo)
                        (fun _ mo ⟨so, hdwo, htmko, hcvo, hflo, hmo⟩ => by
                          c0_hsteps!
                          let soom : FullState := { so with core := { so.core with oom := 1#64 } }
                          exact hQ 2#64 soom _ (m6_fullDenseInvW_with_oom hdwo 1#64).toDense htmko
                            (by dsimp only [soom]; omega) hflo (Or.inr (Or.inl rfl)) (by simp) hm)
                        (fun J39 hJ39 => by
                          c0_hsteps_nogrp
                          m6_call hWeaken
                          dsimp only [vals, Arg.val]
                          refine ⟨c, F0, F_cur, sf, R, rfl, hdwf, htmkf,
                            by rw [hplnl.1, hcvf]; omega,
                            by rw [show (0 : BitVec 32).toNat = 0 from rfl]; omega, fun k hk => by
                              rw [show (0 : BitVec 32).toNat = 0 from rfl, Nat.zero_add]
                              exact m6_bveEntry_weak (hent_pf k hk), hmf, ?_⟩
                          intro ok1 sw1 mw1 hdww1 htmkw1 hcvw1 hflw1 hscrw1 hrefsw1 hmw1
                          c0_hsplit
                          · c0_hsteps_nogrp
                            m6_call hWeaken
                            dsimp only [vals, Arg.val]
                            refine ⟨c, F0, F_cur, sw1, R, rfl, hdww1, htmkw1,
                              by rw [hplnl.2, hcvw1, hcvf]; omega,
                              by rw [show (512 : BitVec 32).toNat = 512 from rfl]; omega,
                              fun k hk => by
                                rw [hscrw1, show ((512 : BitVec 32)).toNat = 512 from rfl]
                                have hwk := m6_bveEntry_weak (hent_nf k hk)
                                unfold FullBveWeakItemOk at hwk ⊢
                                split at hwk
                                · next hb =>
                                    rw [ite_eq_left hb] at ⊢; rw [hcvw1]; exact hwk
                                · next hb =>
                                    rw [ite_eq_right hb] at ⊢
                                    change _ ∈ fullArenaClauseRefs sw1; rw [hrefsw1]; exact hwk,
                              hmw1, ?_⟩
                            intro ok2 sw2 mw2 hdww2 htmkw2 hcvw2 hflw2 hscrw2 _ hmw2
                            c0_hsplit
                            · c0_hsteps_nogrp
                              m6_call hSetInact
                              dsimp only [vals, Arg.val]
                              refine ⟨c, sw2, R, rfl, hdww2.1, hmw2, ?_⟩
                              rw [ite_eq_right (by rw [hcvw2, hcvw1, hcvf]; omega)]
                              intro fl' unass' m_i hfl_i
                              dsimp only
                              intro hm_i
                              let si' : FullState := { sw2 with core := { sw2.core with
                                flags := fl', unassigned := unass' } }
                              have hdwi' := m6_fullDenseInvW_setInact hdww2
                                (unass' := unass') hfl_i
                              c0_hsteps_nogrp
                              let sbve : FullState := { si' with scratch := { si'.scratch with
                                bve_cnt := si'.scratch.bve_cnt + 1#64 } }
                              have hdwbve := m6_fullDenseInvW_with_scratch hdwi'
                                (sc' := sbve.scratch) { hdwi'.1.scratch_ok with } rfl rfl
                              have hres_bve : FullResBufOkW F_cur sbve rp.toNat 1088 :=
                                m6_resBuf_mono5 (s := sf) (s' := sbve)
                                  (hcvw2.trans hcvw1)
                                  (fun idx _ _ => by dsimp only [sbve, si']; rw [hscrw2, hscrw1])
                                  hresf
                              m6_call hCommit
                              refine ⟨c, F0, F_cur, sbve, R, rfl, hdwbve, htmkw2.congr rfl rfl,
                                by simp; omega, hrp_hi, by simpa using hres_bve, hm, ?_⟩
                              intro cr_r sc mc hdwc htmkc hcvc hflc hcr_disj hcr20 hmc
                              dsimp only [sbve, si'] at hcvc hflc
                              c0_hsplit
                              · c0_hsteps!
                                exact hQ 20#64 sc mc hdwc.toDense htmkc (by omega)
                                  (by rw [hflc, hflw2, hflw1]; exact hflf)
                                  (Or.inr (Or.inr rfl)) (fun _ => hcr20 hc) hmc
                              · c0_hsplit
                                · c0_hsteps_nogrp
                                  m6_call hFlushUnits
                                  refine fullDenseFlushUnitsM6Spec_intro rfl hdwc hmc ?_
                                  intro ok_u su mu hdwu hcvu _ hflu _ htmku _ _ _ _ _ hfu hmu
                                  c0_hsplit
                                  · c0_hsteps!
                                    exact hQ cr_r su mu hdwu.toDense (htmkc.congr hcvu htmku)
                                      (by omega) (by rw [hflu, hflc, hflw2, hflw1]; exact hflf)
                                      hcr_disj (fun h => hcr20 h) hmu
                                  · c0_hsteps!
                                    exact hQ 20#64 su mu hdwu.toDense (htmkc.congr hcvu htmku)
                                      (by omega) (by rw [hflu, hflc, hflw2, hflw1]; exact hflf)
                                      (Or.inr (Or.inr rfl)) (fun _ => hfu (by simpa using hc)) hmu
                                · c0_hsteps!
                                  exact hQ cr_r sc mc hdwc.toDense htmkc (by omega)
                                    (by rw [hflc, hflw2, hflw1]; exact hflf) hcr_disj hcr20 hmc
                            · c0_hsteps!
                              exact hJ39 mw2 ⟨sw2, hdww2, htmkw2, hcvw2.trans (hcvw1.trans hcvf),
                                by rw [hflw2, hflw1]; exact hflf, hmw2⟩
                          · c0_hsteps!
                            exact hJ39 mw1 ⟨sw1, hdww1, htmkw1, hcvw1.trans hcvf,
                              by rw [hflw1]; exact hflf, hmw1⟩)
                    · -- `fit_f = false`: BCE fallback on `P[0..np)` then `N[0..nn)`
                      have hbce_p0 : ∀ k < np.toNat,
                          let w := sf.scratch.scratch_buf[k]?.getD 0#32
                          FullBveBceWeakOk c sf w ∧
                          ((w &&& 0x80000000#32) = 0#32 →
                            ((fullArenaClauseLits sf w.toNat).map (· / 2)).Nodup) :=
                        fun k hk => m6_bveEntry_bce hdwf (hent_pf k hk)
                      have hbce_n0 : ∀ k < nn.toNat,
                          let w := sf.scratch.scratch_buf[512 + k]?.getD 0#32
                          FullBveBceWeakOk c sf w ∧
                          ((w &&& 0x80000000#32) = 0#32 →
                            ((fullArenaClauseLits sf w.toNat).map (· / 2)).Nodup) :=
                        fun k hk => m6_bveEntry_bce hdwf (hent_nf k hk)
                      c0_hsteps_nogrp
                      -- BCE loop 1: `i < np`
                      refine wp_loop_group (ts := [i32])
                        (fun rem_b1 (ib1, ()) mb1 => ∃ sb1 : FullState,
                          ib1.toNat ≤ np.toNat ∧ rem_b1 = np.toNat - ib1.toNat ∧
                          FullDenseInvW c F0 F_cur sb1 ∧ TmkZero sb1 ∧
                          sb1.core.cur_vars = s0.core.cur_vars ∧
                          sb1.core.arena_len = sf.core.arena_len ∧
                          sb1.core.fuel = sf.core.fuel ∧
                          sb1.scratch.scratch_buf = sf.scratch.scratch_buf ∧
                          fullArenaClauseRefs sb1 = fullArenaClauseRefs sf ∧
                          (∀ r ∈ fullArenaClauseRefs sf,
                            fullArenaClauseSize sb1 r = fullArenaClauseSize sf r ∧
                            fullArenaClauseLits sb1 r = fullArenaClauseLits sf r) ∧
                          (FullMem c sb1 ⋆ R) mb1)
                        ?_ ?_
                      · rintro Lb1 rem_b1 ⟨ib1, ⟨⟩⟩ mb1 hLb1
                          ⟨sb1, hib1_le, rfl, hdwb1, htmkb1, hcvb1, halb1, hflb1, hscrb1,
                            hrefsb1, hperb1, hmb1⟩
                        c0_hsplit
                        · have hib1_lt : ib1.toNat < np.toNat := hc
                          have hib1_sc : (ib1.setWidth 64).toNat <
                              sb1.scratch.scratch_buf.length := by
                            rw [hdwb1.1.scratch_ok.scratch_buf_len, m6_zext32_toNat]; omega
                          have hib1_1 : (ib1 + 1#32).toNat = ib1.toNat + 1 := by c0_bound
                          let wb1 := sb1.scratch.scratch_buf[(ib1.setWidth 64).toNat]'hib1_sc
                          have hwb1_eq : wb1 = sf.scratch.scratch_buf[ib1.toNat]?.getD 0#32 := by
                            have h0 : some wb1 = sf.scratch.scratch_buf[ib1.toNat]? := by
                              dsimp only [wb1]
                              rw [← List.getElem?_eq_getElem hib1_sc, hscrb1, m6_zext32_toNat]
                            rw [← h0]; rfl
                          have hbce_w := hbce_p0 ib1.toNat hib1_lt
                          let P_bce1 : FullState → Mem 64 → Prop := fun sj mj =>
                            FullDenseInvW c F0 F_cur sj ∧ TmkZero sj ∧
                            sj.core.cur_vars = s0.core.cur_vars ∧
                            sj.core.arena_len = sf.core.arena_len ∧
                            sj.core.fuel = sf.core.fuel ∧
                            sj.scratch.scratch_buf = sf.scratch.scratch_buf ∧
                            fullArenaClauseRefs sj = fullArenaClauseRefs sf ∧
                            (∀ r ∈ fullArenaClauseRefs sf,
                              fullArenaClauseSize sj r = fullArenaClauseSize sf r ∧
                              fullArenaClauseLits sj r = fullArenaClauseLits sf r) ∧
                            (FullMem c sj ⋆ R) mj
                          c0_hsteps_nogrp
                          refine wp_join_state (ts := []) (α := FullState) (fun _ => ()) P_bce1
                            (fun _ sj mj h => by
                              c0_hsteps!
                              exact hLb1 (np.toNat - (ib1 + 1#32).toNat) (ib1 + 1#32, ()) mj
                                (by omega) ⟨sj, by omega, rfl, h⟩)
                            (fun Jb1_step hJb1_step => by
                              c0_hsteps_nogrp
                              m6_call hTryBce
                              dsimp only [vals, Arg.val]
                              refine ⟨c, F0, F_cur, sb1, R, rfl, hdwb1, by rw [hplnl.1]; omega,
                                by rw [show sb1.scratch.scratch_buf[(ib1.setWidth 64).toNat] = wb1
                                       from rfl, hwb1_eq]
                                   exact m6_bceWeak_congr hbce_w.1 hrefsb1 halb1
                                     (fun r hr => (hperb1 r hr).1) (fun r hr => (hperb1 r hr).2),
                                fun hnb => by
                                  rw [show sb1.scratch.scratch_buf[(ib1.setWidth 64).toNat] = wb1
                                    from rfl, hwb1_eq] at hnb ⊢
                                  have hmem := hbce_w.1; unfold FullBveBceWeakOk at hmem
                                  simp only [hnb, ne_eq, not_true_eq_false, ↓reduceIte] at hmem
                                  rw [(hperb1 _ hmem.1).2]; exact hbce_w.2 hnb,
                                by simp; omega, fun k hk => by
                                  rw [show ((512 : BitVec 32)).toNat = 512 from rfl, hscrb1]
                                  exact m6_bceWeak_congr (hbce_n0 k hk).1 hrefsb1 halb1
                                    (fun r hr => (hperb1 r hr).1) (fun r hr => (hperb1 r hr).2),
                                hmb1, ?_⟩
                              intro blk lm_t tmp_t m_t st_b hdwt_b hm_t
                              have htmkt_b : TmkZero st_b := htmkb1
                              c0_hsplit
                              · refine wp_join_state (ts := []) (α := FullState) (fun _ => ())
                                    P_bce1
                                    (fun _ sj mj h => by c0_hsteps!; exact hJb1_step sj mj h)
                                    (fun Jb1 hJb1 => by
                                  have hib1_sc2 : (ib1.setWidth 64).toNat <
                                      st_b.scratch.scratch_buf.length := hib1_sc
                                  c0_hsplit
                                  · refine wp_join_state (ts := []) (α := FullState) (fun _ => ())
                                      P_bce1 ?_ ?_
                                    · intro _ sj mj h; c0_hsteps!; exact hJb1 sj mj h
                                    · intro J_b1 hJ_b1
                                      c0_hsteps_nogrp
                                      m6_call hExtPush2
                                      dsimp only [fullSafetySlice_mem, fullSafetySlice_coreProj,
                                        fullSafetySlice_safe, vals, Arg.val]
                                      refine ⟨c, st_b, R, ⟨rfl, hdwt_b.2.2.2.2.1.2⟩, hdwt_b.1,
                                        hm_t, ?_⟩
                                      rintro ⟨ok_e, ⟨⟩⟩ se me hpr_e hlen_e hpost_e hm_e
                                      dsimp only [fullSafetySlice_mem, fullSafetySlice_coreProj,
                                        fullSafetySlice_safe] at hpr_e hlen_e hm_e
                                      have hcore_e : se.core = st_b.core :=
                                        fullCoreState_agrees_with_scratch (c := c) hpr_e
                                      have hdwe := m6_denseInv_of_extPush hdwt_b hlen_e hcore_e
                                        hpost_e.1 hpost_e.2.1
                                      have htmke : TmkZero se :=
                                        htmkt_b.congr (congrArg FullCoreState.cur_vars hcore_e)
                                          hpost_e.2.2.2
                                      have hsc_e : se.scratch.scratch_buf =
                                          sf.scratch.scratch_buf :=
                                        hpost_e.2.2.1.trans hscrb1
                                      dsimp only
                                      c0_hsplit
                                      · have hib1_sce : (ib1.setWidth 64).toNat <
                                            se.scratch.scratch_buf.length := by
                                          rw [hdwe.1.scratch_ok.scratch_buf_len, m6_zext32_toNat]
                                          omega
                                        c0_hsteps_nogrp
                                        m6_call hDelBin
                                        refine ⟨c, se, R, rfl, hdwe.1,
                                          (m6_denseWatchesInv_of_w hdwe).layout, hm_e, ?_⟩
                                        intro wvec' wstk' wu' nb' m_d sd hlen_d _ hwm_d hm_d
                                        have hdwd := m6_fullDenseInvW_delBin hdwe hlen_d
                                          (hwm_d F_cur hdwe.2.1.watches)
                                        c0_hsteps!
                                        let sd2 : FullState := { sd with scratch := { sd.scratch
                                          with bce_cnt := sd.scratch.bce_cnt + 1#64 } }
                                        have hdwd2 := m6_fullDenseInvW_with_scratch hdwd
                                          (sc' := sd2.scratch) { hdwd.1.scratch_ok with } rfl rfl
                                        exact hJ_b1 sd2 _ ⟨hdwd2, htmke,
                                          (congrArg FullCoreState.cur_vars hcore_e).trans hcvb1,
                                          (congrArg FullCoreState.arena_len hcore_e).trans halb1,
                                          (congrArg FullCoreState.fuel hcore_e).trans hflb1,
                                          hsc_e, by
                                            unfold fullArenaClauseRefs fullArenaClauseRefsCore
                                            dsimp only [sd2, sd]
                                            rw [congrArg FullCoreState.arena hcore_e,
                                              congrArg FullCoreState.arena_len hcore_e]
                                            exact hrefsb1,
                                          fun r hr => by
                                            unfold fullArenaClauseSize fullArenaClauseSizeCore
                                              fullArenaClauseLits fullArenaClauseLitsCore
                                            dsimp only [sd2, sd]
                                            rw [congrArg FullCoreState.arena hcore_e]
                                            exact hperb1 r hr, hm⟩
                                      · c0_hsteps!
                                        exact hJ_b1 se me ⟨hdwe, htmke,
                                          (congrArg FullCoreState.cur_vars hcore_e).trans hcvb1,
                                          (congrArg FullCoreState.arena_len hcore_e).trans halb1,
                                          (congrArg FullCoreState.fuel hcore_e).trans hflb1,
                                          hsc_e, by
                                            unfold fullArenaClauseRefs fullArenaClauseRefsCore
                                            rw [congrArg FullCoreState.arena hcore_e,
                                              congrArg FullCoreState.arena_len hcore_e]
                                            exact hrefsb1,
                                          fun r hr => by
                                            have har_stb : st_b.core.arena = sb1.core.arena := rfl
                                            have hp := hperb1 r hr
                                            unfold fullArenaClauseSize fullArenaClauseLits
                                              fullArenaClauseLitsCore fullArenaClauseSizeCore at hp
                                            unfold fullArenaClauseSize fullArenaClauseLits
                                              fullArenaClauseLitsCore fullArenaClauseSizeCore
                                            rw [congrArg FullCoreState.arena hcore_e, har_stb]
                                            exact hp, hm_e⟩
                                  · have hwb1_nb : (wb1 &&& 0x80000000#32) = 0#32 := hc
                                    refine wp_join_state (ts := []) (α := FullState) (fun _ => ())
                                      P_bce1 ?_ ?_
                                    · intro _ sj mj h; c0_hsteps!; exact hJb1 sj mj h
                                    · intro J_c1 hJ_c1
                                      c0_hsteps_nogrp
                                      m6_call hExtPushCl
                                      dsimp only [fullSafetySlice_mem, fullSafetySlice_coreProj,
                                        fullSafetySlice_safe, vals, Arg.val]
                                      refine ⟨c, st_b, R, ⟨rfl, hdwt_b.2.2.2.2.1.2⟩, hdwt_b.1,
                                        hm_t, ?_⟩
                                      rintro ⟨ok_e, ⟨⟩⟩ se me hpr_e hlen_e hpost_e hm_e
                                      dsimp only [fullSafetySlice_mem, fullSafetySlice_coreProj,
                                        fullSafetySlice_safe] at hpr_e hlen_e hm_e
                                      have hcore_e : se.core = st_b.core :=
                                        fullCoreState_agrees_with_scratch (c := c) hpr_e
                                      have hdwe := m6_denseInv_of_extPush hdwt_b hlen_e hcore_e
                                        hpost_e.1 hpost_e.2.1
                                      have htmke : TmkZero se :=
                                        htmkt_b.congr (congrArg FullCoreState.cur_vars hcore_e)
                                          hpost_e.2.2.2
                                      have hsc_e : se.scratch.scratch_buf =
                                          sf.scratch.scratch_buf :=
                                        hpost_e.2.2.1.trans hscrb1
                                      have hrefse : fullArenaClauseRefs se =
                                          fullArenaClauseRefs sf := by
                                        unfold fullArenaClauseRefs fullArenaClauseRefsCore
                                        rw [congrArg FullCoreState.arena hcore_e,
                                          congrArg FullCoreState.arena_len hcore_e]
                                        exact hrefsb1
                                      dsimp only
                                      c0_hsplit
                                      · have hib1_sce : (ib1.setWidth 64).toNat <
                                            se.scratch.scratch_buf.length := by
                                          rw [hdwe.1.scratch_ok.scratch_buf_len, m6_zext32_toNat]
                                          omega
                                        let ccr := se.scratch.scratch_buf[(ib1.setWidth 64).toNat]'
                                          hib1_sce
                                        have hccr_eq : ccr = wb1 := by
                                          have hopt : some ccr = some wb1 := by
                                            dsimp only [ccr, wb1]
                                            rw [← List.getElem?_eq_getElem hib1_sce,
                                              ← List.getElem?_eq_getElem hib1_sc, hpost_e.2.2.1]
                                          exact Option.some.inj hopt
                                        have hccr_ref : ccr.toNat ∈ fullArenaClauseRefs se := by
                                          rw [hrefse, hccr_eq]
                                          have hmem := hbce_w.1
                                          unfold FullBveBceWeakOk at hmem
                                          rw [← hwb1_eq] at hmem
                                          rw [ite_eq_right (by intro h; exact h hwb1_nb)] at hmem
                                          exact hmem.1
                                        have hccr_wf := hdwe.2.1.arena.refs_wf ccr.toNat hccr_ref
                                        have hale := hdwe.1.core_ok.arena_len_le
                                        have hccr_ar : ccr.toNat < se.core.arena.length := by
                                          rw [hdwe.1.core_ok.arena_len_arr]; omega
                                        have hccr2_ar : (ccr.setWidth 64 + 2#64).toNat <
                                            se.core.arena.length := by
                                          rw [hdwe.1.core_ok.arena_len_arr]; c0_bound
                                        have hccr2_ar' :
                                            (ccr.toNat + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64 <
                                              (se.core.arena.set ccr.toNat
                                                (se.core.arena[ccr.toNat]'hccr_ar |||
                                                  0x00080000#32)).length := by
                                          rw [List.length_set, hdwe.1.core_ok.arena_len_arr]
                                          simp; c0_bound
                                        c0_hsteps!
                                        have hmg := m6_markGarb_pres_lits hdwe hccr_ref
                                          (ag' := se.core.arena_garbage + 3#64 +
                                            (se.core.arena[(ccr.setWidth 64 + 2#64).toNat]'
                                              hccr2_ar).setWidth 64)
                                        let sg : FullState := { se with
                                          core := { se.core with
                                            arena := se.core.arena.set ccr.toNat
                                              (fullArenaHdr se ccr.toNat ||| 0x00080000#32),
                                            arena_garbage := se.core.arena_garbage + 3#64 +
                                              (se.core.arena[(ccr.setWidth 64 + 2#64).toNat]'
                                                hccr2_ar).setWidth 64 }
                                          scratch := { se.scratch with
                                            bce_cnt := se.scratch.bce_cnt + 1#64 } }
                                        have hdwg := m6_fullDenseInvW_with_scratch hmg.1
                                          (sc' := sg.scratch) { hdwe.1.scratch_ok with } rfl rfl
                                        have hhdr_c : se.core.arena[ccr.toNat]'hccr_ar =
                                            fullArenaHdr se ccr.toNat := by
                                          unfold fullArenaHdr fullArenaHdrCore
                                          rw [List.getElem?_eq_getElem hccr_ar, Option.getD_some]
                                        exact hJ_c1 sg _ ⟨hdwg, htmke,
                                          (congrArg FullCoreState.cur_vars hcore_e).trans hcvb1,
                                          (congrArg FullCoreState.arena_len hcore_e).trans halb1,
                                          (congrArg FullCoreState.fuel hcore_e).trans hflb1,
                                          hsc_e, hmg.2.1.trans hrefse, fun r hr => by
                                            have hp1 := hmg.2.2 r (hrefse.symm ▸ hr)
                                            have hp2 := hperb1 r hr
                                            have hpe : fullArenaClauseSize se r =
                                                fullArenaClauseSize sb1 r ∧
                                                fullArenaClauseLits se r =
                                                fullArenaClauseLits sb1 r := by
                                              unfold fullArenaClauseSize fullArenaClauseLits
                                                fullArenaClauseLitsCore fullArenaClauseSizeCore
                                              rw [congrArg FullCoreState.arena hcore_e]
                                              exact ⟨rfl, rfl⟩
                                            exact ⟨hp1.1.trans (hpe.1.trans hp2.1),
                                              hp1.2.trans (hpe.2.trans hp2.2)⟩,
                                          by
                                            dsimp only at hm
                                            have hccr_z : (ccr.setWidth 64).toNat = ccr.toNat :=
                                              m6_zext32_toNat ccr
                                            have hccr_lt : ccr.toNat < 2 ^ 32 := ccr.isLt
                                            have hhm_ne : ccr.toNat ≠
                                                (ccr.setWidth 64 + 2#64).toNat := by
                                              rw [BitVec.toNat_add, hccr_z,
                                                show (2#64 : BitVec 64).toNat = 2 from rfl,
                                                Nat.mod_eq_of_lt (by omega)]
                                              omega
                                            exact m6_bce_hm (w0 := ccr) rfl hccr_ar hhm_ne
                                              (hw0_2 := hccr2_ar) hhdr_c hm⟩
                                      · c0_hsteps!
                                        exact hJ_c1 se me ⟨hdwe, htmke,
                                          (congrArg FullCoreState.cur_vars hcore_e).trans hcvb1,
                                          (congrArg FullCoreState.arena_len hcore_e).trans halb1,
                                          (congrArg FullCoreState.fuel hcore_e).trans hflb1,
                                          hsc_e, hrefse, fun r hr => by
                                            have har_stb : st_b.core.arena = sb1.core.arena := rfl
                                            have hp := hperb1 r hr
                                            unfold fullArenaClauseSize fullArenaClauseLits
                                              fullArenaClauseLitsCore fullArenaClauseSizeCore at hp
                                            unfold fullArenaClauseSize fullArenaClauseLits
                                              fullArenaClauseLitsCore fullArenaClauseSizeCore
                                            rw [congrArg FullCoreState.arena hcore_e, har_stb]
                                            exact hp, hm_e⟩)
                              · c0_hsteps!
                                exact hJb1_step st_b m_t ⟨hdwt_b, htmkt_b, hcvb1, halb1, hflb1,
                                  hscrb1, hrefsb1, hperb1, hm_t⟩)
                        · -- BCE loop 2: `j < nn`
                          c0_hsteps_nogrp
                          refine wp_loop_group (ts := [i32])
                            (fun rem_b2 (jb2, ()) mb2 => ∃ sb2 : FullState,
                              jb2.toNat ≤ nn.toNat ∧ rem_b2 = nn.toNat - jb2.toNat ∧
                              FullDenseInvW c F0 F_cur sb2 ∧ TmkZero sb2 ∧
                              sb2.core.cur_vars = s0.core.cur_vars ∧
                              sb2.core.arena_len = sf.core.arena_len ∧
                              sb2.core.fuel = sf.core.fuel ∧
                              sb2.scratch.scratch_buf = sf.scratch.scratch_buf ∧
                              fullArenaClauseRefs sb2 = fullArenaClauseRefs sf ∧
                              (∀ r ∈ fullArenaClauseRefs sf,
                                fullArenaClauseSize sb2 r = fullArenaClauseSize sf r ∧
                                fullArenaClauseLits sb2 r = fullArenaClauseLits sf r) ∧
                              (FullMem c sb2 ⋆ R) mb2)
                            ?_ ?_
                          · rintro Lb2 rem_b2 ⟨jb2, ⟨⟩⟩ mb2 hLb2
                              ⟨sb2, hjb2_le, rfl, hdwb2, htmkb2, hcvb2, halb2, hflb2, hscrb2,
                                hrefsb2, hperb2, hmb2⟩
                            c0_hsplit
                            · have hjb2_lt : jb2.toNat < nn.toNat := hc
                              have hjb2_sc : ((512#32 + jb2).setWidth 64).toNat <
                                  sb2.scratch.scratch_buf.length := by
                                rw [hdwb2.1.scratch_ok.scratch_buf_len, m6_zext32_toNat]
                                c0_bound
                              have hjb2_1 : (jb2 + 1#32).toNat = jb2.toNat + 1 := by c0_bound
                              let wb2 := sb2.scratch.scratch_buf[((512#32 + jb2).setWidth
                                64).toNat]'hjb2_sc
                              have hwb2_eq : wb2 =
                                  sf.scratch.scratch_buf[512 + jb2.toNat]?.getD 0#32 := by
                                have h0 : some wb2 = sf.scratch.scratch_buf[512 + jb2.toNat]? := by
                                  dsimp only [wb2]
                                  rw [← List.getElem?_eq_getElem hjb2_sc, hscrb2,
                                    m6_zext32_toNat]
                                  congr 1; c0_bound
                                rw [← h0]; rfl
                              have hbce_w := hbce_n0 jb2.toNat hjb2_lt
                              let P_bce2 : FullState → Mem 64 → Prop := fun sj mj =>
                                FullDenseInvW c F0 F_cur sj ∧ TmkZero sj ∧
                                sj.core.cur_vars = s0.core.cur_vars ∧
                                sj.core.arena_len = sf.core.arena_len ∧
                                sj.core.fuel = sf.core.fuel ∧
                                sj.scratch.scratch_buf = sf.scratch.scratch_buf ∧
                                fullArenaClauseRefs sj = fullArenaClauseRefs sf ∧
                                (∀ r ∈ fullArenaClauseRefs sf,
                                  fullArenaClauseSize sj r = fullArenaClauseSize sf r ∧
                                  fullArenaClauseLits sj r = fullArenaClauseLits sf r) ∧
                                (FullMem c sj ⋆ R) mj
                              c0_hsteps_nogrp
                              refine wp_join_state (ts := []) (α := FullState) (fun _ => ())
                                P_bce2 ?_ ?_
                              · intro _ sj mj h
                                c0_hsteps!
                                exact hLb2 (nn.toNat - (jb2 + 1#32).toNat) (jb2 + 1#32, ()) mj
                                  (by omega) ⟨sj, by omega, rfl, h⟩
                              · intro Jb2_step hJb2_step
                                c0_hsteps_nogrp
                                m6_call hTryBce
                                dsimp only [vals, Arg.val]
                                refine ⟨c, F0, F_cur, sb2, R, rfl, hdwb2,
                                  by rw [hplnl.2]; omega,
                                  by change FullBveBceWeakOk c sb2 wb2
                                     rw [hwb2_eq]
                                     exact m6_bceWeak_congr hbce_w.1 hrefsb2 halb2
                                       (fun r hr => (hperb2 r hr).1) (fun r hr => (hperb2 r hr).2),
                                  fun hnb => by
                                    have hnb' : (wb2 &&& 0x80000000#32) = 0#32 := hnb
                                    rw [hwb2_eq] at hnb'
                                    have hmem := hbce_w.1; unfold FullBveBceWeakOk at hmem
                                    simp only [hnb', ne_eq, not_true_eq_false, ↓reduceIte] at hmem
                                    have hwl_eq :
                                        fullArenaClauseLits sb2
                                          (sb2.scratch.scratch_buf[(BitVec.setWidth 64
                                            ((512 : BitVec 32) + jb2)).toNat]).toNat =
                                        fullArenaClauseLits sb2 wb2.toNat := rfl
                                    rw [hwl_eq, hwb2_eq, (hperb2 _ hmem.1).2]
                                    exact hbce_w.2 hnb',
                                  by simp; omega, fun k hk => by
                                    rw [show ((0 : BitVec 32)).toNat = 0 from rfl,
                                      Nat.zero_add, hscrb2]
                                    exact m6_bceWeak_congr (hbce_p0 k hk).1 hrefsb2 halb2
                                      (fun r hr => (hperb2 r hr).1) (fun r hr => (hperb2 r hr).2),
                                  hmb2, ?_⟩
                                intro blk lm_t tmp_t m_t st_b hdwt_b hm_t
                                have htmkt_b : TmkZero st_b := htmkb2
                                c0_hsplit
                                · refine wp_join_state (ts := []) (α := FullState) (fun _ => ())
                                      P_bce2 ?_ ?_
                                  · intro _ sj mj h; c0_hsteps!; exact hJb2_step sj mj h
                                  · intro Jb2 hJb2
                                    c0_hsplit
                                    · refine wp_join_state (ts := []) (α := FullState)
                                        (fun _ => ()) P_bce2 ?_ ?_
                                      · intro _ sj mj h; c0_hsteps!; exact hJb2 sj mj h
                                      ·
                                            intro J_b2 hJ_b2
                                            c0_hsteps_nogrp
                                            m6_call hExtPush2
                                            dsimp only [fullSafetySlice_mem,
                                              fullSafetySlice_coreProj, fullSafetySlice_safe,
                                              vals, Arg.val]
                                            refine ⟨c, st_b, R, ⟨rfl, hdwt_b.2.2.2.2.1.2⟩,
                                              hdwt_b.1, hm_t, ?_⟩
                                            rintro ⟨ok_e, ⟨⟩⟩ se me hpr_e hlen_e hpost_e hm_e
                                            dsimp only [fullSafetySlice_mem,
                                              fullSafetySlice_coreProj,
                                              fullSafetySlice_safe] at hpr_e hlen_e hm_e
                                            have hcore_e : se.core = st_b.core :=
                                              fullCoreState_agrees_with_scratch (c := c) hpr_e
                                            have hdwe := m6_denseInv_of_extPush hdwt_b hlen_e
                                              hcore_e hpost_e.1 hpost_e.2.1
                                            have htmke : TmkZero se :=
                                              htmkt_b.congr
                                                (congrArg FullCoreState.cur_vars hcore_e)
                                                hpost_e.2.2.2
                                            have hsc_e : se.scratch.scratch_buf =
                                                sf.scratch.scratch_buf :=
                                              hpost_e.2.2.1.trans hscrb2
                                            dsimp only
                                            c0_hsplit
                                            · c0_hsteps_nogrp
                                              m6_call hDelBin
                                              refine ⟨c, se, R, rfl, hdwe.1,
                                                (m6_denseWatchesInv_of_w hdwe).layout, hm_e, ?_⟩
                                              intro wvec' wstk' wu' nb' m_d sd hlen_d _ hwm_d hm_d
                                              have hdwd := m6_fullDenseInvW_delBin hdwe hlen_d
                                                (hwm_d F_cur hdwe.2.1.watches)
                                              c0_hsteps!
                                              let sd2 : FullState := { sd with scratch :=
                                                { sd.scratch with
                                                  bce_cnt := sd.scratch.bce_cnt + 1#64 } }
                                              have hdwd2 := m6_fullDenseInvW_with_scratch hdwd
                                                (sc' := sd2.scratch) { hdwd.1.scratch_ok with }
                                                rfl rfl
                                              exact hJ_b2 sd2 _ ⟨hdwd2, htmke,
                                                (congrArg FullCoreState.cur_vars hcore_e).trans
                                                  hcvb2,
                                                (congrArg FullCoreState.arena_len hcore_e).trans
                                                  halb2,
                                                (congrArg FullCoreState.fuel hcore_e).trans hflb2,
                                                hsc_e, by
                                                  unfold fullArenaClauseRefs fullArenaClauseRefsCore
                                                  dsimp only [sd2, sd]
                                                  rw [congrArg FullCoreState.arena hcore_e,
                                                    congrArg FullCoreState.arena_len hcore_e]
                                                  exact hrefsb2,
                                                fun r hr => by
                                                  unfold fullArenaClauseSize fullArenaClauseSizeCore
                                                    fullArenaClauseLits fullArenaClauseLitsCore
                                                  dsimp only [sd2, sd]
                                                  rw [congrArg FullCoreState.arena hcore_e]
                                                  exact hperb2 r hr, hm⟩
                                            · c0_hsteps!
                                              exact hJ_b2 se me ⟨hdwe, htmke,
                                                (congrArg FullCoreState.cur_vars hcore_e).trans
                                                  hcvb2,
                                                (congrArg FullCoreState.arena_len hcore_e).trans
                                                  halb2,
                                                (congrArg FullCoreState.fuel hcore_e).trans hflb2,
                                                hsc_e, by
                                                  unfold fullArenaClauseRefs fullArenaClauseRefsCore
                                                  rw [congrArg FullCoreState.arena hcore_e,
                                                    congrArg FullCoreState.arena_len hcore_e]
                                                  exact hrefsb2,
                                                fun r hr => by
                                                  have har_stb : st_b.core.arena = sb2.core.arena :=
                                                    rfl
                                                  have hp := hperb2 r hr
                                                  unfold fullArenaClauseSize fullArenaClauseLits
                                                    fullArenaClauseLitsCore fullArenaClauseSizeCore
                                                    at hp ⊢
                                                  rw [congrArg FullCoreState.arena hcore_e, har_stb]
                                                  exact hp, hm_e⟩
                                    · have hwb2_nb : (wb2 &&& 0x80000000#32) = 0#32 := hc
                                      refine wp_join_state (ts := []) (α := FullState)
                                        (fun _ => ()) P_bce2 ?_ ?_
                                      · intro _ sj mj h; c0_hsteps!; exact hJb2 sj mj h
                                      ·
                                            intro J_c2 hJ_c2
                                            c0_hsteps_nogrp
                                            m6_call hExtPushCl
                                            dsimp only [fullSafetySlice_mem,
                                              fullSafetySlice_coreProj, fullSafetySlice_safe,
                                              vals, Arg.val]
                                            refine ⟨c, st_b, R, ⟨rfl, hdwt_b.2.2.2.2.1.2⟩,
                                              hdwt_b.1, hm_t, ?_⟩
                                            rintro ⟨ok_e, ⟨⟩⟩ se me hpr_e hlen_e hpost_e hm_e
                                            dsimp only [fullSafetySlice_mem,
                                              fullSafetySlice_coreProj,
                                              fullSafetySlice_safe] at hpr_e hlen_e hm_e
                                            have hcore_e : se.core = st_b.core :=
                                              fullCoreState_agrees_with_scratch (c := c) hpr_e
                                            have hdwe := m6_denseInv_of_extPush hdwt_b hlen_e
                                              hcore_e hpost_e.1 hpost_e.2.1
                                            have htmke : TmkZero se :=
                                              htmkt_b.congr
                                                (congrArg FullCoreState.cur_vars hcore_e)
                                                hpost_e.2.2.2
                                            have hsc_e : se.scratch.scratch_buf =
                                                sf.scratch.scratch_buf :=
                                              hpost_e.2.2.1.trans hscrb2
                                            have hrefse : fullArenaClauseRefs se =
                                                fullArenaClauseRefs sf := by
                                              unfold fullArenaClauseRefs fullArenaClauseRefsCore
                                              rw [congrArg FullCoreState.arena hcore_e,
                                                congrArg FullCoreState.arena_len hcore_e]
                                              exact hrefsb2
                                            dsimp only
                                            c0_hsplit
                                            · have hwb2_ref : wb2.toNat ∈
                                                  fullArenaClauseRefs se := by
                                                rw [hrefse]
                                                have hmem := hbce_w.1
                                                unfold FullBveBceWeakOk at hmem
                                                rw [← hwb2_eq] at hmem
                                                rw [ite_eq_right
                                                  (by intro h; exact h hwb2_nb)] at hmem
                                                exact hmem.1
                                              have hwb2_wf := hdwe.2.1.arena.refs_wf wb2.toNat
                                                hwb2_ref
                                              have hale := hdwe.1.core_ok.arena_len_le
                                              have hwb2_ar : wb2.toNat < se.core.arena.length := by
                                                rw [hdwe.1.core_ok.arena_len_arr]; omega
                                              have hwb2_2ar : (wb2.setWidth 64 + 2#64).toNat <
                                                  se.core.arena.length := by
                                                rw [hdwe.1.core_ok.arena_len_arr]; c0_bound
                                              have hwb2_2ar' :
                                                  (wb2.toNat + BitVec.toNat (2 : BitVec 64)) %
                                                      2 ^ 64 <
                                                    (se.core.arena.set wb2.toNat
                                                      (se.core.arena[wb2.toNat]'hwb2_ar |||
                                                        0x00080000#32)).length := by
                                                rw [List.length_set, hdwe.1.core_ok.arena_len_arr]
                                                simp; c0_bound
                                              c0_hsteps!
                                              have hmg := m6_markGarb_pres_lits hdwe hwb2_ref
                                                (ag' := se.core.arena_garbage + 3#64 +
                                                  (se.core.arena[(wb2.setWidth 64 + 2#64).toNat]'
                                                    hwb2_2ar).setWidth 64)
                                              let sg : FullState := { se with
                                                core := { se.core with
                                                  arena := se.core.arena.set wb2.toNat
                                                    (fullArenaHdr se wb2.toNat ||| 0x00080000#32),
                                                  arena_garbage := se.core.arena_garbage + 3#64 +
                                                    (se.core.arena[(wb2.setWidth 64 + 2#64).toNat]'
                                                      hwb2_2ar).setWidth 64 }
                                                scratch := { se.scratch with
                                                  bce_cnt := se.scratch.bce_cnt + 1#64 } }
                                              have hdwg := m6_fullDenseInvW_with_scratch hmg.1
                                                (sc' := sg.scratch) { hdwe.1.scratch_ok with }
                                                rfl rfl
                                              have hhdr_c : se.core.arena[wb2.toNat]'hwb2_ar =
                                                  fullArenaHdr se wb2.toNat := by
                                                unfold fullArenaHdr fullArenaHdrCore
                                                rw [List.getElem?_eq_getElem hwb2_ar,
                                                  Option.getD_some]
                                              exact hJ_c2 sg _ ⟨hdwg, htmke,
                                                (congrArg FullCoreState.cur_vars hcore_e).trans
                                                  hcvb2,
                                                (congrArg FullCoreState.arena_len hcore_e).trans
                                                  halb2,
                                                (congrArg FullCoreState.fuel hcore_e).trans hflb2,
                                                hsc_e, hmg.2.1.trans hrefse, fun r hr => by
                                                  have hp1 := hmg.2.2 r (hrefse.symm ▸ hr)
                                                  have hp2 := hperb2 r hr
                                                  have hpe : fullArenaClauseSize se r =
                                                      fullArenaClauseSize sb2 r ∧
                                                      fullArenaClauseLits se r =
                                                      fullArenaClauseLits sb2 r := by
                                                    unfold fullArenaClauseSize fullArenaClauseLits
                                                      fullArenaClauseLitsCore
                                                      fullArenaClauseSizeCore
                                                    rw [congrArg FullCoreState.arena hcore_e]
                                                    exact ⟨rfl, rfl⟩
                                                  exact ⟨hp1.1.trans (hpe.1.trans hp2.1),
                                                    hp1.2.trans (hpe.2.trans hp2.2)⟩,
                                                by
                                                  dsimp only at hm
                                                  have hwb2_z : (wb2.setWidth 64).toNat =
                                                      wb2.toNat := m6_zext32_toNat wb2
                                                  have hwb2_lt : wb2.toNat < 2 ^ 32 := wb2.isLt
                                                  have hhm_ne : wb2.toNat ≠
                                                      (wb2.setWidth 64 + 2#64).toNat := by
                                                    rw [BitVec.toNat_add, hwb2_z,
                                                      show (2#64 : BitVec 64).toNat = 2 from rfl,
                                                      Nat.mod_eq_of_lt (by omega)]
                                                    omega
                                                  have hsb_lt : (BitVec.setWidth 64
                                                      ((512 : BitVec 32) + jb2)).toNat <
                                                      sb2.scratch.scratch_buf.length := by
                                                    rw [show (512 : BitVec 32) = 512#32 from rfl]
                                                    exact hjb2_sc
                                                  have hw_eq : sb2.scratch.scratch_buf[(
                                                      BitVec.setWidth 64
                                                        ((512 : BitVec 32) +
                                                          jb2)).toNat]'hsb_lt = wb2 :=
                                                    m6_getElem_congr (by
                                                      rw [show (512 : BitVec 32) = 512#32 from rfl])
                                                      hsb_lt hjb2_sc
                                                  exact m6_bce_hm (w0 := wb2) hw_eq hwb2_ar hhm_ne
                                                    (hw0_2 := hwb2_2ar) hhdr_c hm⟩
                                            · c0_hsteps!
                                              exact hJ_c2 se me ⟨hdwe, htmke,
                                                (congrArg FullCoreState.cur_vars hcore_e).trans
                                                  hcvb2,
                                                (congrArg FullCoreState.arena_len hcore_e).trans
                                                  halb2,
                                                (congrArg FullCoreState.fuel hcore_e).trans hflb2,
                                                hsc_e, hrefse, fun r hr => by
                                                  have har_stb : st_b.core.arena = sb2.core.arena :=
                                                    rfl
                                                  have hp := hperb2 r hr
                                                  unfold fullArenaClauseSize fullArenaClauseLits
                                                    fullArenaClauseLitsCore fullArenaClauseSizeCore
                                                    at hp ⊢
                                                  rw [congrArg FullCoreState.arena hcore_e, har_stb]
                                                  exact hp, hm_e⟩
                                · c0_hsteps!
                                  exact hJb2_step st_b m_t ⟨hdwt_b, htmkt_b, hcvb2, halb2, hflb2,
                                    hscrb2, hrefsb2, hperb2, hm_t⟩
                            · c0_hsteps!
                              exact hQ 1#64 sb2 mb2 hdwb2.toDense htmkb2 (by omega)
                                (by rw [hflb2]; omega) (Or.inl rfl) (by simp) hmb2
                          · intro Lb2 hLb2; c0_hsteps!
                            exact hLb2 nn.toNat (0#32, ()) mb1
                              ⟨sb1, Nat.zero_le _, by simp, hdwb1, htmkb1, hcvb1, halb1, hflb1,
                               hscrb1, hrefsb1, hperb1, hmb1⟩
                      · intro Lb1 hLb1; c0_hsteps!
                        exact hLb1 np.toNat (0#32, ()) mf
                          ⟨sf, Nat.zero_le _, by simp, hdwf, htmkf, hcvf, rfl, rfl, rfl, rfl,
                           fun _ _ => ⟨rfl, rfl⟩, hmf⟩)
                  (fun Jpre hJpre => by
                    c0_hsplit
                    · c0_hsteps_nogrp
                      refine wp_join_state (ts := [.bool]) (α := Bool × FullState)
                        (fun x => (x.1, ()))
                        (fun x md =>
                          FullDenseInvW c F0 F_cur x.2 ∧ TmkZero x.2 ∧
                          x.2.core.cur_vars = s0.core.cur_vars ∧
                          x.2.core.arena = s2.core.arena ∧
                          x.2.core.arena_len = s2.core.arena_len ∧
                          x.2.core.fuel.toNat ≤ s0.core.fuel.toNat ∧
                          FullResBufOkW F_cur x.2 rp.toNat 1088 ∧
                          (∀ k < np.toNat,
                            x.2.scratch.scratch_buf[k]? = s2.scratch.scratch_buf[k]?) ∧
                          (∀ k < nn.toNat,
                            x.2.scratch.scratch_buf[512 + k]? =
                              s2.scratch.scratch_buf[512 + k]?) ∧
                          (FullMem c x.2 ⋆ R) md)
                        (fun _ ⟨b45, s45⟩ md h45 => by
                          c0_hsteps!; exact hJpre (b45, s45) md h45)
                        (fun J45p hJ45p => by
                          c0_hsplit
                          · c0_hsteps!
                            exact hJ45p (false, si) mi ⟨hdwi, htmki, hcvi, hari, hali, hfli,
                              hres_i, hkeep_pi, hkeep_ni, hmi⟩
                          · c0_hsteps_nogrp
                            refine wp_join_state (ts := [.bool]) (α := Bool × FullState)
                              (fun x => (x.1, ()))
                              (fun x md =>
                                FullDenseInvW c F0 F_cur x.2 ∧ TmkZero x.2 ∧
                                x.2.core.cur_vars = s0.core.cur_vars ∧
                                x.2.core.arena = s2.core.arena ∧
                                x.2.core.arena_len = s2.core.arena_len ∧
                                x.2.core.fuel.toNat ≤ s0.core.fuel.toNat ∧
                                FullResBufOkW F_cur x.2 rp.toNat 1088 ∧
                                (∀ k < np.toNat,
                                  x.2.scratch.scratch_buf[k]? =
                                    s2.scratch.scratch_buf[k]?) ∧
                                (∀ k < nn.toNat,
                                  x.2.scratch.scratch_buf[512 + k]? =
                                    s2.scratch.scratch_buf[512 + k]?) ∧
                                (FullMem c x.2 ⋆ R) md)
                              (fun _ ⟨b52, s52⟩ md h52 => by
                                c0_hsteps!; exact hJ45p (b52, s52) md h52)
                              (fun J52p hJ52p => by
                                c0_hsplit
                                · c0_hsteps_nogrp
                                  refine wp_join_state (ts := []) (α := FullState)
                                    (fun _ => ())
                                    (fun sd md =>
                                      FullDenseInvW c F0 F_cur sd ∧ TmkZero sd ∧
                                      sd.core.cur_vars = s0.core.cur_vars ∧
                                      sd.core.arena = s2.core.arena ∧
                                      sd.core.arena_len = s2.core.arena_len ∧
                                      sd.core.fuel.toNat ≤ s0.core.fuel.toNat ∧
                                      FullResBufOkW F_cur sd rp.toNat 1088 ∧
                                      (∀ k < np.toNat,
                                        sd.scratch.scratch_buf[k]? =
                                          s2.scratch.scratch_buf[k]?) ∧
                                      (∀ k < nn.toNat,
                                        sd.scratch.scratch_buf[512 + k]? =
                                          s2.scratch.scratch_buf[512 + k]?) ∧
                                      (FullMem c sd ⋆ R) md)
                                    (fun _ sd md ⟨hdwd, htmkd, hcvd, hard, hald, hfld, hresd,
                                        hkeep_pd, hkeep_nd, hmd⟩ => by
                                      c0_hsteps_nogrp
                                      refine wp_join_state (ts := [.bool])
                                        (α := Bool × FullState) (fun x => (x.1, ()))
                                        (fun x md' =>
                                          FullDenseInvW c F0 F_cur x.2 ∧ TmkZero x.2 ∧
                                          x.2.core.cur_vars = s0.core.cur_vars ∧
                                          x.2.core.arena = s2.core.arena ∧
                                          x.2.core.arena_len = s2.core.arena_len ∧
                                          x.2.core.fuel.toNat ≤ s0.core.fuel.toNat ∧
                                          FullResBufOkW F_cur x.2 rp.toNat 1088 ∧
                                          (∀ k < np.toNat,
                                            x.2.scratch.scratch_buf[k]? =
                                              s2.scratch.scratch_buf[k]?) ∧
                                          (∀ k < nn.toNat,
                                            x.2.scratch.scratch_buf[512 + k]? =
                                              s2.scratch.scratch_buf[512 + k]?) ∧
                                          (FullMem c x.2 ⋆ R) md')
                                        (fun _ ⟨b60, s60⟩ md' h60 => by
                                          c0_hsteps!; exact hJ52p (b60, s60) md' h60)
                                        (fun J60p hJ60p => by
                                          c0_hsplit
                                          · c0_hsteps!
                                            exact hJ60p (false, sd) md ⟨hdwd, htmkd, hcvd,
                                              hard, hald, hfld, hresd, hkeep_pd, hkeep_nd,
                                              hmd⟩
                                          · c0_hsteps!
                                            exact hJ60p (fit, sd) md ⟨hdwd, htmkd, hcvd,
                                              hard, hald, hfld, hresd, hkeep_pd, hkeep_nd,
                                              hmd⟩))
                                    (fun Jd hJd => by
                                      c0_hsplit
                                      · c0_hsteps_nogrp
                                        m6_call hDefrag
                                        refine ⟨c, si, R, rfl, hdwi.1,
                                          (m6_denseWatchesInv_of_w hdwi).layout, hmi, ?_⟩
                                        intro wvec' wstk' wlen' wsort' md sd hlen_d hlay_d _
                                          hslice_d hmd
                                        have hdwd := m6_fullDenseInvW_of_wstackDefrag hdwi
                                          hlen_d hlay_d hslice_d
                                        c0_hsteps!
                                        exact hJd sd md ⟨hdwd, htmki, hcvi, hari, hali, hfli,
                                          m6_resBuf_mono5 (s := si) (s' := sd) rfl
                                            (fun _ _ _ => rfl) hres_i,
                                          hkeep_pi, hkeep_ni, hmd⟩
                                      · c0_hsteps!
                                        exact hJd si mi ⟨hdwi, htmki, hcvi, hari, hali, hfli,
                                          hres_i, hkeep_pi, hkeep_ni, hmi⟩)
                                · c0_hsteps!
                                  exact hJ52p (fit, si) mi ⟨hdwi, htmki, hcvi, hari, hali,
                                    hfli, hres_i, hkeep_pi, hkeep_ni, hmi⟩))
                    · c0_hsteps!
                      exact hJpre (fit, si) mi ⟨hdwi, htmki, hcvi, hari, hali, hfli,
                        hres_i, hkeep_pi, hkeep_ni, hmi⟩))
              (fun J32 hJ32 => by
                c0_hsplit
                · c0_hsteps_nogrp
                  m6_call hGates
                  refine fullBveGatesM6Spec_intro rfl hdw2 htmk0 (by omega) hv_lt hnp512'
                    hnn512' hent_p2 hent_n2' hm2 ?_
                  intro s3 m3 hdw3 htmk3 hcv3 har3 hal3 hfl3 hp3 hn3 hm3
                  have hent_p3 : ∀ i < np.toNat, FullBveEntryOkW F_cur s3 (2 * v.toNat)
                      (s3.scratch.scratch_buf[i]?.getD 0#32) := fun i hi => by
                    rw [hp3 i hi]; exact m6_bveEntry_core (hent_p2 i hi) hcv3 har3 hal3
                  have hent_n3 : ∀ j < nn.toNat, FullBveEntryOkW F_cur s3 (2 * v.toNat + 1)
                      (s3.scratch.scratch_buf[512 + j]?.getD 0#32) := fun j hj => by
                    rw [hn3 j hj]; exact m6_bveEntry_core (hent_n2' j hj) hcv3 har3 hal3
                  have h1056 : 1056 < s3.scratch.scratch_buf.length := by
                    rw [hdw3.1.scratch_ok.scratch_buf_len]; omega
                  have h1057 : 1057 < s3.scratch.scratch_buf.length := by
                    rw [hdw3.1.scratch_ok.scratch_buf_len]; omega
                  c0_hsteps_nogrp
                  refine wp_loop_group (ts := [i64, i64, i64, .bool, i32])
                    (fun rem_i (rp, r_cnt, w_est, fit, i, ()) mi => ∃ si : FullState,
                      i.toNat ≤ np.toNat ∧ rem_i = np.toNat - i.toNat ∧
                      FullDenseInvW c F0 F_cur si ∧ TmkZero si ∧
                      si.core.cur_vars = s0.core.cur_vars ∧ si.core.arena = s3.core.arena ∧
                      si.core.arena_len = s3.core.arena_len ∧
                      si.core.fuel.toNat ≤ s0.core.fuel.toNat ∧
                      1088 ≤ rp.toNat ∧ rp.toNat ≤ c.scratch_cap ∧
                      FullResBufOkW F_cur si rp.toNat 1088 ∧
                      (∀ k < 1088, si.scratch.scratch_buf[k]? = s3.scratch.scratch_buf[k]?) ∧
                      (FullMem c si ⋆ R) mi)
                    ?_ ?_
                  · rintro Li rem_i ⟨rp, r_cnt, w_est, fit, i, ⟨⟩⟩ mi hLi
                      ⟨si, hi_le, rfl, hdwi, htmki, hcvi, hari, hali, hfli, hrp_lo, hrp_hi,
                        hres_i, hkeep_i, hmi⟩
                    c0_hsplit
                    · have hi_lt : i.toNat < np.toNat := hc
                      c0_hsplit
                      · have hi_mask_sc : ((1024#32 + (i >>> (5 : Nat))).setWidth 64).toNat <
                            si.scratch.scratch_buf.length := by
                          rw [hdwi.1.scratch_ok.scratch_buf_len, m6_zext32_toNat]
                          have hi5 : (i >>> (5 : Nat)).toNat = i.toNat / 32 := by
                            rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
                          rw [BitVec.toNat_add, hi5]; simp only [BitVec.toNat_ofNat]
                          rw [Nat.mod_eq_of_lt (by omega)]; omega
                        have hi1 : (i + 1#32).toNat = i.toNat + 1 := by c0_bound
                        c0_hsteps_nogrp
                        -- Inner resolution loop (`j < nn && fit`)
                        refine wp_loop_break_group
                          (brkTs := [i64, i64, i64, .bool, i32])
                          (lpTs := [i64, i64, i64, i32])
                          (fun (rp_b, rcnt_b, west_b, fit_b, _ib, ()) mb => ∃ sb : FullState,
                            FullDenseInvW c F0 F_cur sb ∧ TmkZero sb ∧
                            sb.core.cur_vars = s0.core.cur_vars ∧ sb.core.arena = s3.core.arena ∧
                            sb.core.arena_len = s3.core.arena_len ∧
                            sb.core.fuel.toNat ≤ s0.core.fuel.toNat ∧
                            1088 ≤ rp_b.toNat ∧ rp_b.toNat ≤ c.scratch_cap ∧
                            FullResBufOkW F_cur sb rp_b.toNat 1088 ∧
                            (∀ k < 1088, sb.scratch.scratch_buf[k]? =
                              s3.scratch.scratch_buf[k]?) ∧
                            (FullMem c sb ⋆ R) mb)
                          (fun rem_j (rp_j, rcnt_j, west_j, j, ()) mj => ∃ sj : FullState,
                            j.toNat ≤ nn.toNat ∧ rem_j = nn.toNat - j.toNat ∧
                            FullDenseInvW c F0 F_cur sj ∧ TmkZero sj ∧
                            sj.core.cur_vars = s0.core.cur_vars ∧ sj.core.arena = s3.core.arena ∧
                            sj.core.arena_len = s3.core.arena_len ∧
                            sj.core.fuel.toNat ≤ s0.core.fuel.toNat ∧
                            1088 ≤ rp_j.toNat ∧ rp_j.toNat ≤ c.scratch_cap ∧
                            FullResBufOkW F_cur sj rp_j.toNat 1088 ∧
                            (∀ k < 1088, sj.scratch.scratch_buf[k]? =
                              s3.scratch.scratch_buf[k]?) ∧
                            (FullMem c sj ⋆ R) mj)
                          ?_ ?_ ?_
                        · rintro _ ⟨rp_b, rcnt_b, west_b, fit_b, _ib, ⟨⟩⟩ mb
                            ⟨sb, hdwb, htmkb, hcvb, harb, halb, hflb, hrpb_lo, hrpb_hi,
                              hresb, hkeepb, hmb⟩
                          c0_hsteps!
                          exact hLi (np.toNat - (i + 1#32).toNat)
                            (rp_b, rcnt_b, west_b, fit_b, i + 1#32, ()) mb (by omega)
                            ⟨sb, by omega, rfl, hdwb, htmkb, hcvb, harb, halb, hflb,
                             hrpb_lo, hrpb_hi, hresb, hkeepb, hmb⟩
                        · rintro Bj Lj rem_j ⟨rp_j, rcnt_j, west_j, j, ⟨⟩⟩ mj hBj hLj
                            ⟨sj, hj_le, rfl, hdwj, htmkj, hcvj, harj, halj, hflj, hrpj_lo,
                              hrpj_hi, hresj, hkeepj, hmj⟩
                          c0_hsplit
                          · have hj_lt : j.toNat < nn.toNat := hc
                            c0_hsplit
                            · have hj_mask_sc : ((1040#32 + (j >>> (5 : Nat))).setWidth 64).toNat <
                                  sj.scratch.scratch_buf.length := by
                                rw [hdwj.1.scratch_ok.scratch_buf_len, m6_zext32_toNat]
                                have hj5 : (j >>> (5 : Nat)).toNat = j.toNat / 32 := by
                                  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
                                rw [BitVec.toNat_add, hj5]; simp only [BitVec.toNat_ofNat]
                                rw [Nat.mod_eq_of_lt (by omega)]; omega
                              have hj1 : (j + 1#32).toNat = j.toNat + 1 := by c0_bound
                              -- Compute `need_pair = !gf || (rg ? (pi || nj) : (pi != nj))`
                              c0_hsteps_nogrp
                              refine wp_join_state_pure (ts := [.bool]) (α := Bool)
                                (fun np_b => (np_b, ())) (fun _ => True)
                                (fun _ np_b _ => by
                                  c0_hsteps_nogrp
                                  refine wp_join_state (ts := [i64, i64, i64, .bool])
                                    (α := BitVec 64 × BitVec 64 × BitVec 64 × Bool × FullState)
                                    (fun x => (x.1, x.2.1, x.2.2.1, x.2.2.2.1, ()))
                                    (fun x mk =>
                                      let sk := x.2.2.2.2
                                      FullDenseInvW c F0 F_cur sk ∧ TmkZero sk ∧
                                      sk.core.cur_vars = s0.core.cur_vars ∧
                                      sk.core.arena = s3.core.arena ∧
                                      sk.core.arena_len = s3.core.arena_len ∧
                                      sk.core.fuel.toNat ≤ s0.core.fuel.toNat ∧
                                      1088 ≤ x.1.toNat ∧ x.1.toNat ≤ c.scratch_cap ∧
                                      FullResBufOkW F_cur sk x.1.toNat 1088 ∧
                                      (∀ k < 1088, sk.scratch.scratch_buf[k]? =
                                        s3.scratch.scratch_buf[k]?) ∧
                                      (FullMem c sk ⋆ R) mk)
                                    (fun _ ⟨rp_k, rcnt_k, west_k, fit_k, sk⟩ mk
                                        ⟨hdwk, htmkk, hcvk, hark, halk, hflk, hrpk_lo, hrpk_hi,
                                          hresk, hkeepk, hmk⟩ => by
                                      c0_hsteps!
                                      exact hLj (nn.toNat - (j + 1#32).toNat)
                                        (rp_k, rcnt_k, west_k, j + 1#32, ()) mk (by rw [hj1]; omega)
                                        ⟨sk, by rw [hj1]; omega, rfl, hdwk, htmkk, hcvk, hark, halk,
                                         hflk, hrpk_lo, hrpk_hi, hresk, hkeepk, hmk⟩)
                                    (fun J81 hJ81 => by
                                      c0_hsplit
                                      · have hi_scj : (i.setWidth 64).toNat <
                                            sj.scratch.scratch_buf.length := by
                                          rw [hdwj.1.scratch_ok.scratch_buf_len, m6_zext32_toNat]
                                          omega
                                        have hj_scj : (((512 : BitVec 32) + j).setWidth 64).toNat <
                                            sj.scratch.scratch_buf.length := by
                                          rw [hdwj.1.scratch_ok.scratch_buf_len, m6_zext32_toNat]
                                          c0_bound
                                        c0_hsteps_nogrp
                                        m6_call hResPair
                                        dsimp only [vals, Arg.val]
                                        refine ⟨c, F0, F_cur, sj, R, rfl, hdwj, by omega,
                                          (by
                                            have hget : sj.scratch.scratch_buf[(i.setWidth
                                                64).toNat]'hi_scj =
                                                s3.scratch.scratch_buf[i.toNat]?.getD 0#32 := by
                                              have h0 := hkeepj i.toNat (by omega)
                                              rw [← h0, List.getElem?_eq_getElem (by
                                                rw [m6_zext32_toNat] at hi_scj; exact hi_scj),
                                                Option.getD_some]
                                              exact m6_getElem_congr (m6_zext32_toNat i) _ _
                                            rw [hget]
                                            exact m6_bveEntry_core (hent_p3 i.toNat hi_lt)
                                              (hcvj.trans hcv3.symm) harj halj),
                                          (by
                                            have hget : sj.scratch.scratch_buf[(((512 : BitVec 32) +
                                                j).setWidth 64).toNat]'hj_scj =
                                                s3.scratch.scratch_buf[512 + j.toNat]?.getD
                                                  0#32 := by
                                              have h0 := hkeepj (512 + j.toNat) (by omega)
                                              have h512 :
                                                  (((512 : BitVec 32) + j).setWidth 64).toNat =
                                                    512 + j.toNat := by
                                                rw [m6_zext32_toNat]; c0_bound
                                              rw [← h0, List.getElem?_eq_getElem (by
                                                rw [← h512]; exact hj_scj), Option.getD_some]
                                              exact m6_getElem_congr h512 _ _
                                            rw [hget]
                                            exact m6_bveEntry_core (hent_n3 j.toNat hj_lt)
                                              (hcvj.trans hcv3.symm) harj halj),
                                          hmj, ?_⟩
                                        intro ok_r lm_r tmp_r tl_r m_r
                                        dsimp only
                                        intro hdwr htl_le hres_ok hm_r
                                        let sr : FullState := { sj with core := { sj.core with
                                          lit_mark := lm_r, tmp := tmp_r, tmp_len := tl_r } }
                                        have htmkr : TmkZero sr := htmkj
                                        have hres_sr : FullResBufOkW F_cur sr rp_j.toNat 1088 :=
                                          m6_resBuf_mono5 (s := sj) (s' := sr) rfl
                                            (fun _ _ _ => rfl) hresj
                                        c0_hsplit
                                        · obtain ⟨hr_lt, hr_nd, hr_ent⟩ :=
                                            hres_ok (by simpa using hc)
                                          have htl_cv : tl_r ≤ c.max_vars := by
                                            have := hdwr.1.core_ok.cur_vars_le; omega
                                          c0_hsplit
                                          · c0_hsteps!
                                            exact hBj
                                              (rp_j, rcnt_j + 1#64, west_j, false, j, ()) m_r
                                              ⟨sr, hdwr, htmkr, hcvj, harj, halj, hflj, hrpj_lo,
                                               hrpj_hi, hres_sr, hkeepj, hm_r⟩
                                          · have htl100 : tl_r ≤ 100 := by
                                              rw [Nat.mod_eq_of_lt (by omega : tl_r < 2 ^ 64),
                                                show (100 : BitVec 64).toNat = 100 from rfl] at hc
                                              omega
                                            c0_hsplit
                                            · c0_hsteps!
                                              exact hBj
                                                (rp_j, rcnt_j + 1#64, west_j, false, j, ())
                                                m_r ⟨sr, hdwr, htmkr, hcvj, harj, halj, hflj,
                                                 hrpj_lo, hrpj_hi, hres_sr, hkeepj, hm_r⟩
                                            · c0_hsplit
                                              · c0_hsteps!
                                                exact hBj
                                                  (rp_j, rcnt_j + 1#64, west_j, false, j, ())
                                                  m_r ⟨sr, hdwr, htmkr, hcvj, harj, halj, hflj,
                                                   hrpj_lo, hrpj_hi, hres_sr, hkeepj, hm_r⟩
                                              · have hrp_sum : (rp_j + 1#64 +
                                                    BitVec.ofNat 64 tl_r).toNat =
                                                    rp_j.toNat + 1 + tl_r := by c0_bound
                                                have hrp_fit : rp_j.toNat + 1 + tl_r ≤
                                                    c.scratch_cap := by
                                                  rw [show (1 : BitVec 64).toNat = 1 from rfl,
                                                    Nat.mod_eq_of_lt (by omega :
                                                      c.scratch_cap < 2 ^ 64),
                                                    Nat.mod_eq_of_lt (by omega :
                                                      rp_j.toNat + 1 + tl_r < 2 ^ 64)] at hc
                                                  omega
                                                have hrp_sc : rp_j.toNat <
                                                    sr.scratch.scratch_buf.length := by
                                                  rw [hdwr.1.scratch_ok.scratch_buf_len]; omega
                                                c0_hsteps_nogrp
                                                let scr_w0 := sr.scratch.scratch_buf.set rp_j.toNat
                                                  ((BitVec.ofNat 64 tl_r).setWidth 32)
                                                have hlen_w0 :
                                                    (BitVec.ofNat 64 tl_r).setWidth 32 =
                                                      BitVec.ofNat 32 tl_r := by
                                                  apply BitVec.eq_of_toNat_eq
                                                  simp
                                                -- Copy `tmp[0 ..< tl_r)` into `scr[rp_j+1..)`
                                                refine wp_loop_group (ts := [i64, i32])
                                                  (fun rem_k (wk, k, ()) mk =>
                                                    ∃ scr_k : List (BitVec 32),
                                                      let sk : FullState := { sr with scratch :=
                                                        { sr.scratch with scratch_buf := scr_k } }
                                                      scr_k.length = c.scratch_cap ∧
                                                      k.toNat ≤ tl_r ∧ rem_k = tl_r - k.toNat ∧
                                                      (∀ idx < rp_j.toNat, scr_k[idx]? =
                                                        sr.scratch.scratch_buf[idx]?) ∧
                                                      scr_k[rp_j.toNat]? = some (BitVec.ofNat 32
                                                        tl_r) ∧
                                                      (∀ t < k.toNat,
                                                        scr_k[rp_j.toNat + 1 + t]? = tmp_r[t]?) ∧
                                                      (FullMem c sk ⋆ R) mk)
                                                  ?_ ?_
                                                · rintro Lk rem_k ⟨wk, k, ⟨⟩⟩ mk hLk
                                                    ⟨scr_k, hsck, hk_le, rfl, hpre_k, hsz_k, hcp_k,
                                                      hmk⟩
                                                  c0_hsplit
                                                  · have hk_lt : k.toNat < tl_r := by
                                                      rw [Nat.mod_eq_of_lt (by omega :
                                                        tl_r < 2 ^ 64)] at hc
                                                      exact hc
                                                    have hk_tmp : (k.setWidth 64).toNat <
                                                        tmp_r.length := by
                                                      rw [hdwr.1.core_ok.tmp_len_arr,
                                                        m6_zext32_toNat]; omega
                                                    have hk_sc :
                                                        (rp_j + 1#64 + k.setWidth 64).toNat <
                                                        scr_k.length := by rw [hsck]; c0_bound
                                                    have hk_sc_eq : (rp_j + 1#64 + k.setWidth
                                                        64).toNat = rp_j.toNat + 1 + k.toNat := by
                                                      c0_bound
                                                    have hk1 : (k + 1#32).toNat = k.toNat + 1 := by
                                                      c0_bound
                                                    c0_hsteps_nogrp
                                                    let scr_k' := scr_k.set (rp_j + 1#64 +
                                                      k.setWidth 64).toNat
                                                      (tmp_r[(k.setWidth 64).toNat]'hk_tmp)
                                                    have hstep_k : ∀ (wk' : BitVec 64) m_step,
                                                        (FullMem c { sr with scratch :=
                                                          { sr.scratch with scratch_buf := scr_k' }
                                                          } ⋆ R) m_step →
                                                        Lk (wk', k + 1#32, ()) m_step :=
                                                      fun wk' m_step hm_s =>
                                                        hLk (tl_r - (k + 1#32).toNat)
                                                          (wk', k + 1#32, ()) m_step (by omega)
                                                          ⟨scr_k', by simp [scr_k', hsck], by omega,
                                                           rfl,
                                                           fun idx hidx => by
                                                             dsimp only [scr_k']
                                                             rw [List.getElem?_set_ne (by omega)]
                                                             exact hpre_k idx hidx,
                                                           by
                                                             dsimp only [scr_k']
                                                             rw [List.getElem?_set_ne (by omega)]
                                                             exact hsz_k,
                                                           fun t ht => by
                                                             dsimp only [scr_k']
                                                             rcases Nat.lt_or_eq_of_le
                                                               (Nat.lt_succ_iff.mp (hk1 ▸ ht))
                                                               with h | h
                                                             · rw [List.getElem?_set_ne (by omega)]
                                                               exact hcp_k t h
                                                             · subst h
                                                               rw [← hk_sc_eq,
                                                                 List.getElem?_set_self hk_sc,
                                                                 List.getElem?_eq_getElem (by
                                                                   rw [m6_zext32_toNat] at hk_tmp
                                                                   exact hk_tmp)]
                                                               exact congrArg some
                                                                 (m6_getElem_congr
                                                                   (m6_zext32_toNat k) _ _), hm_s⟩
                                                    refine wp_join_state_pure (ts := [i64])
                                                      (α := BitVec 64) (fun x => (x, ()))
                                                      (fun _ => True)
                                                      (fun _ wk' _ => by
                                                        c0_hsteps!; exact hstep_k wk' _ hm)
                                                      (fun Jw hJw => by
                                                        c0_hsplit
                                                        · c0_hsplit
                                                          · have hlk_lt :
                                                                (tmp_r[(k.setWidth 64).toNat]'
                                                                hk_tmp).toNat <
                                                                2 * sr.core.cur_vars := by
                                                              have hlt_k : k.toNat <
                                                                  tmp_r.length := by
                                                                rw [m6_zext32_toNat] at hk_tmp
                                                                exact hk_tmp
                                                              have h0 := hr_lt k.toNat hk_lt
                                                              rw [List.getElem?_eq_getElem hlt_k,
                                                                Option.getD_some] at h0
                                                              rw [m6_getElem_congr
                                                                (m6_zext32_toNat k) hk_tmp hlt_k]
                                                              exact h0
                                                            have hlk_wv : ((tmp_r[(k.setWidth
                                                                64).toNat]'hk_tmp).setWidth 64 <<<
                                                                (1 : Nat) + 1#64).toNat <
                                                                sr.core.wvec.length := by
                                                              rw [hdwr.1.core_ok.wvec_len]
                                                              have hcv_r :
                                                                  sr.core.cur_vars ≤ c.max_vars :=
                                                                hdwr.1.core_ok.cur_vars_le
                                                              have hlk_le_r : (tmp_r[(k.setWidth
                                                                  64).toNat]'hk_tmp).toNat <
                                                                  2 * sr.core.cur_vars := by
                                                                rw [m6_getElem_congr
                                                                  (m6_zext32_toNat k) hk_tmp (by
                                                                    rw [m6_zext32_toNat] at hk_tmp
                                                                    exact hk_tmp)]
                                                                exact hlk_lt
                                                              rw [BitVec.toNat_add,
                                                                BitVec.toNat_shiftLeft,
                                                                Nat.shiftLeft_eq,
                                                                BitVec.toNat_setWidth]
                                                              simp only [BitVec.toNat_ofNat,
                                                                Nat.reducePow]
                                                              rw [Nat.mod_eq_of_lt (by omega),
                                                                Nat.mod_eq_of_lt (by omega),
                                                                Nat.mod_eq_of_lt (by omega)]
                                                              omega
                                                            c0_hsteps!; exact hJw _ trivial
                                                          · c0_hsteps!; exact hJw wk trivial
                                                        · c0_hsteps!; exact hJw wk trivial)
                                                  · -- Append completed resolvent to `FullResBufOkW`
                                                    have hk_eq : k.toNat = tl_r := by
                                                      rw [Nat.mod_eq_of_lt (by omega :
                                                        tl_r < 2 ^ 64)] at hc
                                                      change ¬ k.toNat < tl_r at hc; omega
                                                    let s_ap : FullState := { sr with scratch :=
                                                      { sr.scratch with scratch_buf := scr_k } }
                                                    have hdw_ap : FullDenseInvW c F0 F_cur s_ap :=
                                                      m6_fullDenseInvW_set_scratch5 hdwr hsck
                                                    have hrp_next : (rp_j + 1#64 +
                                                        BitVec.ofNat 64 tl_r).toNat =
                                                        rp_j.toNat + 1 + tl_r := by c0_bound
                                                    have hcp_full : ∀ t < tl_r,
                                                        scr_k[rp_j.toNat + 1 + t]? = tmp_r[t]? :=
                                                      fun t ht => hcp_k t (by omega)
                                                    have hres_ap : FullResBufOkW F_cur s_ap
                                                        (rp_j + 1#64 + BitVec.ofNat 64 tl_r).toNat
                                                        1088 := by
                                                      rw [hrp_next]
                                                      refine m6_resBuf_append5 (s := sr)
                                                        (s' := s_ap) rfl
                                                        (fun idx _ hi2 => hpre_k idx hi2) hres_sr
                                                        (by
                                                          dsimp only [s_ap]; rw [hsz_k,
                                                            Option.getD_some, BitVec.toNat_ofNat,
                                                            Nat.mod_eq_of_lt (by omega)])
                                                        (fun t ht => by
                                                          dsimp only [s_ap]; rw [hcp_full t ht]
                                                          exact hr_lt t ht) ?_ ?_
                                                      · have hmap : ((List.range tl_r).map fun t =>
                                                            (s_ap.scratch.scratch_buf[rp_j.toNat +
                                                              1 + t]?.getD 0#32).toNat / 2) =
                                                            (tmp_r.take tl_r).map
                                                              (fun x => x.toNat / 2) := by
                                                          rw [m6_list_take_map_div2_eq_range (by
                                                            rw [hdwr.1.core_ok.tmp_len_arr]; omega)]
                                                          exact List.map_congr_left fun t htm => by
                                                            dsimp only [s_ap]
                                                            rw [hcp_full t (List.mem_range.mp htm)]
                                                        rw [hmap]; exact hr_nd
                                                      · have hmap : ((List.range tl_r).map fun t =>
                                                            (s_ap.scratch.scratch_buf[rp_j.toNat +
                                                              1 + t]?.getD 0#32).toNat) =
                                                            (tmp_r.take tl_r).map BitVec.toNat := by
                                                          rw [m6_list_take_map_eq_range (by
                                                            rw [hdwr.1.core_ok.tmp_len_arr]; omega)]
                                                          exact List.map_congr_left fun t htm => by
                                                            dsimp only [s_ap]
                                                            rw [hcp_full t (List.mem_range.mp htm)]
                                                        rw [hmap]; exact hr_ent
                                                    c0_hsteps!
                                                    exact hJ81 (rp_j + 1#64 + BitVec.ofNat 64 tl_r,
                                                      rcnt_j + 1#64, wk, fit, s_ap) mk
                                                      ⟨hdw_ap, htmkr, hcvj, harj, halj, hflj,
                                                       by rw [hrp_next]; omega,
                                                       by rw [hrp_next]; omega, hres_ap,
                                                       fun idx hidx =>
                                                         (hpre_k idx (by omega)).trans
                                                           (hkeepj idx hidx), hmk⟩
                                                · intro Lk hLk; c0_hsteps!
                                                  exact hLk tl_r (west_j, 0#32, ()) _
                                                    ⟨scr_w0, by
                                                       dsimp only [scr_w0, sr]
                                                       rw [List.length_set]
                                                       exact hdwj.1.scratch_ok.scratch_buf_len,
                                                     Nat.zero_le _, by simp,
                                                     fun idx hidx => by
                                                       dsimp only [scr_w0]
                                                       exact List.getElem?_set_ne (by omega),
                                                     by dsimp only [scr_w0]; rw [hlen_w0]
                                                        exact List.getElem?_set_self hrp_sc,
                                                     fun _ h => by
                                                       rw [show (0#32).toNat = 0 from rfl] at h
                                                       omega, hm⟩
                                        · c0_hsteps!
                                          exact hJ81 (rp_j, rcnt_j, west_j, fit, sr) m_r
                                            ⟨hdwr, htmkr, hcvj, harj, halj, hflj, hrpj_lo, hrpj_hi,
                                             hres_sr, hkeepj, hm_r⟩
                                      · c0_hsteps!
                                        exact hJ81 (rp_j, rcnt_j, west_j, fit, sj) mj
                                          ⟨hdwj, htmkj, hcvj, harj, halj, hflj, hrpj_lo, hrpj_hi,
                                           hresj, hkeepj, hmj⟩))
                                    (fun Jn hJn => by
                                      c0_hsplit
                                      · refine wp_join_state_pure (ts := [i32]) (α := BitVec 32)
                                          (fun x => (x, ())) (fun _ => True)
                                          (fun _ _ _ => by
                                            c0_hsplit <;> (c0_hsteps!; exact hJn _ trivial))
                                          (fun J80 hJ80 => by
                                            c0_hsplit
                                            · refine wp_join_state_pure (ts := [.bool]) (α := Bool)
                                                (fun b => (b, ())) (fun _ => True)
                                                (fun _ _ _ => by c0_hsteps!; exact hJ80 _ trivial)
                                                (fun J81p hJ81p => by
                                                  c0_hsplit
                                                  · c0_hsteps!; exact hJ81p true trivial
                                                  · c0_hsplit
                                                    · c0_hsteps!; exact hJ81p true trivial
                                                    · c0_hsteps!; exact hJ81p false trivial)
                                            · c0_hsteps!; exact hJ80 _ trivial)
                                      · c0_hsteps!; exact hJn true trivial)
                            · c0_hsteps!
                              exact hBj (rp_j, rcnt_j, west_j, fit, j, ()) mj
                                ⟨sj, hdwj, htmkj, hcvj, harj, halj, hflj, hrpj_lo, hrpj_hi,
                                 hresj, hkeepj, hmj⟩
                          · c0_hsteps!
                            exact hBj (rp_j, rcnt_j, west_j, fit, j, ()) mj
                              ⟨sj, hdwj, htmkj, hcvj, harj, halj, hflj, hrpj_lo, hrpj_hi,
                               hresj, hkeepj, hmj⟩
                        · intro _ Lj _ hLj; c0_hsteps!
                          exact hLj nn.toNat (rp, r_cnt, w_est, 0#32, ()) mi
                            ⟨si, Nat.zero_le _, by simp, hdwi, htmki, hcvi, hari, hali, hfli,
                             hrp_lo, hrp_hi, hres_i, hkeep_i, hmi⟩
                      · c0_hsteps!
                        exact hJ32 (rp, r_cnt, w_est, fit, si) mi
                          ⟨hdwi, htmki, hcvi, hari.trans har3, hali.trans hal3, hfli, hrp_lo,
                           hrp_hi, hres_i, fun k hk => (hkeep_i k (by omega)).trans (hp3 k hk),
                           fun k hk => (hkeep_i (512 + k) (by omega)).trans (hn3 k hk), hmi⟩
                    · c0_hsteps!
                      exact hJ32 (rp, r_cnt, w_est, fit, si) mi
                        ⟨hdwi, htmki, hcvi, hari.trans har3, hali.trans hal3, hfli, hrp_lo,
                         hrp_hi, hres_i, fun k hk => (hkeep_i k (by omega)).trans (hp3 k hk),
                         fun k hk => (hkeep_i (512 + k) (by omega)).trans (hn3 k hk), hmi⟩
                  · intro Li hLi; c0_hsteps!
                    exact hLi np.toNat (1088#64, 0#64, 0#64, _, 0#32, ()) m3
                      ⟨s3, Nat.zero_le _, by simp, hdw3, htmk3, hcv3, rfl, rfl, hfl3,
                       by simp, by simp; omega, .nil, fun _ _ => rfl, hm3⟩
                · c0_hsteps!
                  exact hJ32 (1088#64, 0#64, 0#64, _, s2) m2
                    ⟨hdw2, htmk0, rfl, rfl, rfl, Nat.le_refl _, by simp, by simp; omega, .nil,
                     fun _ _ => rfl, fun _ _ => rfl, hm2⟩))
          (fun J25 hJ25 => by
            c0_hsplit
            · refine wp_join0 (P := fun mj => mj = m2 ∧ (np = 0#32 ∨ nn = 0#32))
                (fun _ mj ⟨hmj, hnp_nn⟩ => by
                  rcases hmj.symm with rfl
                  refine wp_join_state (ts := []) (α := FullState) (fun _ => ())
                    (fun sw moom =>
                      FullDenseInvW c F0 F_cur sw ∧ TmkZero sw ∧
                      sw.core.cur_vars = s0.core.cur_vars ∧
                      sw.core.fuel.toNat ≤ s0.core.fuel.toNat ∧
                      (FullMem c sw ⋆ R) moom)
                    (fun _ sw moom ⟨hdww, htmkw, hcvw, hflw, hmw⟩ => by
                      c0_hsteps!
                      let soom : FullState := { sw with core := { sw.core with oom := 1#64 } }
                      exact hQ 2#64 soom _ (m6_fullDenseInvW_with_oom hdww 1#64).toDense htmkw
                        (by dsimp only [soom]; omega) hflw (Or.inr (Or.inl rfl)) (by simp) hm)
                    (fun J27 hJ27 => by
                      refine wp_join_state (ts := []) (α := FullState) (fun _ => ())
                        (fun sp mp =>
                          FullDenseInvW c F0 F_cur sp ∧ TmkZero sp ∧
                          sp.core.cur_vars = s0.core.cur_vars ∧
                          sp.core.fuel.toNat ≤ s0.core.fuel.toNat ∧
                          (∀ j < nn.toNat, FullBveEntryOkW F_cur sp (2 * v.toNat + 1)
                            (sp.scratch.scratch_buf[512 + j]?.getD 0#32)) ∧
                          (FullMem c sp ⋆ R) mp)
                        (fun _ sp mp ⟨hdwp, htmkp, hcvp, hflp, hent_np, hmp⟩ => by
                          refine wp_join_state (ts := []) (α := FullState) (fun _ => ())
                            (fun sn mn =>
                              FullDenseInvW c F0 F_cur sn ∧ TmkZero sn ∧
                              sn.core.cur_vars = s0.core.cur_vars ∧
                              sn.core.fuel.toNat ≤ s0.core.fuel.toNat ∧
                              (FullMem c sn ⋆ R) mn) ?_ ?_
                          · intro _ sn mn ⟨hdwn, htmkn, hcvn, hfln, hmn⟩
                            c0_hsteps_nogrp
                            m6_call hSetInact
                            dsimp only [vals, Arg.val]
                            refine ⟨c, sn, R, rfl, hdwn.1, hmn, ?_⟩
                            rw [ite_eq_right (by omega)]
                            intro fl' unass' m_i hfl_i
                            dsimp only
                            intro hm_i
                            let si : FullState :=
                              { sn with core := { sn.core with
                                flags := fl', unassigned := unass' } }
                            have hdwi := m6_fullDenseInvW_setInact hdwn
                              (unass' := unass') hfl_i
                            c0_hsteps!
                            let sf : FullState :=
                              { si with scratch := { si.scratch with
                                bve_cnt := si.scratch.bve_cnt + 1#64 } }
                            have hdwf := m6_fullDenseInvW_with_scratch hdwi
                              (sc' := sf.scratch) { hdwi.1.scratch_ok with } rfl rfl
                            exact hQ 1#64 sf _ hdwf.toDense (htmkn.congr rfl rfl)
                              (by dsimp only [sf, si]; omega)
                              hfln (Or.inl rfl) (by simp) hm
                          · intro J29 hJ29
                            c0_hsplit
                            · c0_hsteps_nogrp
                              m6_call hWeaken
                              dsimp only [vals, Arg.val]
                              refine ⟨c, F0, F_cur, sp, R, rfl, hdwp, htmkp,
                                by rw [hplnl.2, hcvp]; omega,
                                by rw [show (512 : BitVec 32).toNat = 512 from rfl]; omega,
                                fun j hj => by
                                  rw [show (512 : BitVec 32).toNat = 512 from rfl]
                                  exact m6_bveEntry_weak (hent_np j hj),
                                hmp, ?_⟩
                              intro ok_w sw mw hdww htmkw hcvw hflw _ _ hmw
                              c0_hsplit
                              · c0_hsteps!
                                exact hJ29 sw mw ⟨hdww, htmkw, hcvw.trans hcvp,
                                  by rw [hflw]; exact hflp, hmw⟩
                              · c0_hsteps!
                                exact hJ27 sw mw ⟨hdww, htmkw, hcvw.trans hcvp,
                                  by rw [hflw]; exact hflp, hmw⟩
                            · c0_hsteps!
                              exact hJ29 sp mp ⟨hdwp, htmkp, hcvp, hflp, hmp⟩)
                        (fun J28 hJ28 => by
                          c0_hsplit
                          · c0_hsteps_nogrp
                            m6_call hWeaken
                            dsimp only [vals, Arg.val]
                            refine ⟨c, F0, F_cur, s2, R, rfl, hdw2, htmk0,
                              by dsimp only [s2, s1]; rw [hplnl.1]; omega,
                              by rw [show (0 : BitVec 32).toNat = 0 from rfl, Nat.zero_add]; omega,
                              fun i hi => by
                                dsimp only [s2]
                                rw [show (0 : BitVec 32).toNat = 0 from rfl, Nat.zero_add]
                                exact m6_bveEntry_weak (hent_p2 i hi),
                              hm2, ?_⟩
                            intro ok_w sw mw hdww htmkw hcvw hflw _ _ hmw
                            c0_hsplit
                            · c0_hsteps!
                              refine hJ28 sw mw
                                ⟨hdww, htmkw, hcvw, by rw [hflw]; exact Nat.le_refl _,
                                  fun j hj => ?_, hmw⟩
                              exfalso
                              have hnp0 : np ≠ 0#32 := fun h => by subst h; simp at hc
                              have hnn0 := hnp_nn.resolve_left hnp0
                              rw [hnn0, show (0#32).toNat = 0 from rfl] at hj; omega
                            · c0_hsteps!
                              exact hJ27 sw mw ⟨hdww, htmkw, hcvw,
                                by rw [hflw]; exact Nat.le_refl _, hmw⟩
                          · c0_hsteps!
                            exact hJ28 s2 m2 ⟨hdw2, htmk0, rfl, Nat.le_refl _, hent_n2', hm2⟩)))
                (fun J26 hJ26 => by
                  c0_hsplit
                  · c0_hsteps!; exact hJ26 m2 ⟨rfl, Or.inl hc⟩
                  · c0_hsplit
                    · c0_hsteps!; exact hJ26 m2 ⟨rfl, Or.inr hc⟩
                    · c0_hsteps!; exact hJ25 m2 rfl)
            · c0_hsteps!; exact hJ25 m2 rfl)

/-- Canonical `Full.fullBveVarSpec` corollary for `full_bve_var_m6` (when `TmkZero s`). -/
theorem full_bve_var_m6_wp_canon (Γ : Env)
    (hCollect : ∀ a m Q X, Full.fullBveCollectSpec a m Q X →
      Γ "full_bve_collect_m6" [i64, i32, i64, i32] [i32] a m Q X)
    (hExtNeed : ∀ a m Q X, Full.fullBveExtNeedSpec a m Q X →
      Γ "full_bve_ext_need" [i64, i32, i32] [i64] a m Q X)
    (hWeaken : ∀ a m Q X, FullFastBveBudgets.fullBveWeakenTmkSpec a m Q X →
      Γ "full_bve_weaken" [i64, i32, i32, i32] [.bool] a m Q X)
    (hSetInact : ∀ a m Q X, Full.fullSetInactiveSpec a m Q X →
      Γ "full_set_inactive" [i64, i32, i32] [] a m Q X)
    (hGates : ∀ a m Q X, fullBveGatesM6Spec a m Q X →
      Γ "full_bve_gates_m6" [i64, i32, i32, i32] [] a m Q X)
    (hResPair : ∀ a m Q X, Full.fullBveResolvePairSpec a m Q X →
      Γ "full_bve_resolve_pair" [i64, i32, i32, i32] [.bool] a m Q X)
    (hDefrag : ∀ a m Q X, Full.fullWstackDefragSpec a m Q X →
      Γ "full_wstack_defrag" [i64] [] a m Q X)
    (hCommit : ∀ a m Q X, FullFastBveBudgets.fullBveCommitResTmkSpec a m Q X →
      Γ "full_bve_commit_res" [i64, i64, i64] [i64] a m Q X)
    (hFlushUnits : ∀ a m Q X, fullDenseFlushUnitsM6Spec a m Q X →
      Γ "full_dense_flush_units_m6" [i64] [.bool] a m Q X)
    (hTryBce : ∀ a m Q X, Full.fullBveTryBceSpec a m Q X →
      Γ "full_bve_try_bce" [i64, i32, i32, i32, i32] [.bool] a m Q X)
    (hExtPush2 : ∀ a m Q X, FullFastBveBudgets.fullExtendPush2TmkSpec a m Q X →
      Γ "full_extend_push2" [i64, i32, i32] [.bool] a m Q X)
    (hDelBin : ∀ a m Q X, Full.fullDeleteBinarySpec a m Q X →
      Γ "full_delete_binary" [i64, i32, i32] [] a m Q X)
    (hExtPushCl : ∀ a m Q X, FullFastBveBudgets.fullExtendPushClTmkSpec a m Q X →
      Γ "full_extend_push_cl" [i64, i32, i32] [.bool] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {s : FullState} {v : BitVec 32} {R : Mem 64 → Prop}
    {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (hd : FullDenseInv c F0 s) (htmk : TmkZero s) (hv : v.toNat < s.core.cur_vars)
    (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ r s' m',
      FullDenseInv c F0 s' → s.core.cur_vars ≤ s'.core.cur_vars →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 1#64 ∨ r = 2#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m') :
    Func.wp Γ full_bve_var_m6_body (c.hdr, v, ()) m Q X :=
  full_bve_var_m6_wp Γ hCollect hExtNeed hWeaken hSetInact hGates hResPair hDefrag hCommit
    hFlushUnits hTryBce hExtPush2 hDelBin hExtPushCl _ _ _ _
    ⟨c, F0, s, R, rfl, hd, htmk, hv, hm,
      fun r s' m' h1 _ h2 h3 h4 h5 hm' => hQ r s' m' h1 h2 h3 h4 h5 hm'⟩

end LeanQbe.T.Examples.Kissat.FullM6BveFwd
