module

public import LeanQbe.T.Examples.Kissat.FullM6BveFwdProof1
public import LeanQbe.T.Examples.Kissat.FullDefSweepLemmas1
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Examples.Kissat.FullDenseWatchLemmas1
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat M6 BVE/Forward Proofs — Part 4 (Cluster 3: BVE & Gate Extraction)

M1-clean proof module (`public section`, `0` `@[expose]`, `0` `import all`, `private` helpers):
1. `full_bve_collect_m6_wp` (certifies canonical `Full.fullBveCollectSpec`)
2. `full_bve_mark_and_m6_wp`, `full_bve_get_tern_m6_wp`, `full_bve_match_tern_m6_wp`,
   `full_bve_find_ite_m6_wp`, `full_bve_gates_m6_wp`
3. `full_bve_var_m6_wp` (certifies canonical `FullFastBveBudgets.fullBveVarDefSpec` +
   canonical `Full.fullBveVarSpec` corollary)
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

/-! ## 1. Pure BVE Helper Lemmas -/

private theorem m6_resBuf_mono {F_cur : List (List Nat)} {s s' : FullState}
    {r_end p : Nat} (hcv : s'.core.cur_vars = s.core.cur_vars)
    (heq : ∀ idx, p ≤ idx → idx < r_end →
      s'.scratch.scratch_buf[idx]? = s.scratch.scratch_buf[idx]?)
    (h : FullResBufOkW F_cur s r_end p) : FullResBufOkW F_cur s' r_end p := by
  induction h with
  | nil => exact .nil
  | @cons p sz hle hsz hlt hnd hent _ ih =>
    have h0 : s'.scratch.scratch_buf[p]? = s.scratch.scratch_buf[p]? :=
      heq p (Nat.le_refl _) (by omega)
    have hk : ∀ k < sz, s'.scratch.scratch_buf[p + 1 + k]? = s.scratch.scratch_buf[p + 1 + k]? :=
      fun k hk => heq (p + 1 + k) (by omega) (by omega)
    refine .cons hle (by rw [h0]; exact hsz)
      (fun k hkl => by rw [hk k hkl, hcv]; exact hlt k hkl) ?_ ?_
      (ih fun idx hi1 hi2 => heq idx (by omega) hi2)
    · have hmap : ((List.range sz).map fun k =>
          (s'.scratch.scratch_buf[p + 1 + k]?.getD 0#32).toNat / 2) =
          ((List.range sz).map fun k =>
          (s.scratch.scratch_buf[p + 1 + k]?.getD 0#32).toNat / 2) :=
        List.map_congr_left fun k hkm => by rw [hk k (List.mem_range.mp hkm)]
      rw [hmap]; exact hnd
    · have hmap : ((List.range sz).map fun k =>
          (s'.scratch.scratch_buf[p + 1 + k]?.getD 0#32).toNat) =
          ((List.range sz).map fun k =>
          (s.scratch.scratch_buf[p + 1 + k]?.getD 0#32).toNat) :=
        List.map_congr_left fun k hkm => by rw [hk k (List.mem_range.mp hkm)]
      rw [hmap]; exact hent

private theorem m6_resBuf_append {F_cur : List (List Nat)} {s s' : FullState}
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
    have h0 : s'.scratch.scratch_buf[p]? = s.scratch.scratch_buf[p]? :=
      hpref p (Nat.le_refl _) (by omega)
    have hk : ∀ k < psz, s'.scratch.scratch_buf[p + 1 + k]? = s.scratch.scratch_buf[p + 1 + k]? :=
      fun k hk => hpref (p + 1 + k) (by omega) (by omega)
    refine .cons (by omega) (by rw [h0]; exact hpsz)
      (fun k hkl => by rw [hk k hkl, hcv]; exact hplt k hkl) ?_ ?_
      (ih fun idx hi1 hi2 => hpref idx (by omega) hi2)
    · have hmap : ((List.range psz).map fun k =>
          (s'.scratch.scratch_buf[p + 1 + k]?.getD 0#32).toNat / 2) =
          ((List.range psz).map fun k =>
          (s.scratch.scratch_buf[p + 1 + k]?.getD 0#32).toNat / 2) :=
        List.map_congr_left fun k hkm => by rw [hk k (List.mem_range.mp hkm)]
      rw [hmap]; exact hpnd
    · have hmap : ((List.range psz).map fun k =>
          (s'.scratch.scratch_buf[p + 1 + k]?.getD 0#32).toNat) =
          ((List.range psz).map fun k =>
          (s.scratch.scratch_buf[p + 1 + k]?.getD 0#32).toNat) :=
        List.map_congr_left fun k hkm => by rw [hk k (List.mem_range.mp hkm)]
      rw [hmap]; exact hpent

private theorem m6_bveEntry_to_weak {F_cur : List (List Nat)} {s : FullState} {lit : Nat}
    {w : BitVec 32} (h : FullBveEntryOkW F_cur s lit w) : FullBveWeakItemOk s.core w := by
  unfold FullBveEntryOkW at h; unfold FullBveWeakItemOk
  split at h <;> simp_all

private theorem m6_and_garb_zero_of_mask4 {hdr : BitVec 32}
    (h : (hdr &&& (0x00080000#32 ||| 0x00400000#32)) = 0#32) :
    (hdr &&& 0x00080000#32) = 0#32 := by
  have hmask : ((0x00080000#32 ||| 0x00400000#32) &&& 0x00080000#32) = 0x00080000#32 := by
    decide
  calc hdr &&& 0x00080000#32
      = hdr &&& ((0x00080000#32 ||| 0x00400000#32) &&& 0x00080000#32) := by rw [hmask]
    _ = (hdr &&& (0x00080000#32 ||| 0x00400000#32)) &&& 0x00080000#32 := by
      rw [BitVec.and_assoc]
    _ = 0#32 := by rw [h, BitVec.zero_and]

private theorem m6_bveEntry_to_bceWeak {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hdw : FullDenseInvW c F0 F_cur s) {lit : Nat} {w : BitVec 32}
    (h : FullBveEntryOkW F_cur s lit w) :
    FullBveBceWeakOk c s w ∧
    ((w &&& 0x80000000#32) = 0#32 → ((fullArenaClauseLits s w.toNat).map (· / 2)).Nodup) := by
  unfold FullBveEntryOkW at h; unfold FullBveBceWeakOk
  have hcv := hdw.1.core_ok.cur_vars_le
  by_cases hb : (w &&& 0x80000000#32) ≠ 0#32
  · rw [ite_eq_left hb] at h ⊢
    exact ⟨by omega, fun heq => absurd heq hb⟩
  · rw [ite_eq_right hb] at h ⊢
    have hwf := hdw.2.1.arena.refs_wf w.toNat h.1
    refine ⟨⟨h.1, Nat.le_trans hwf.2.2.1 hwf.2.2.2.1, fun l hl => ?_⟩,
      fun _ => hdw.2.2.2.1 w.toNat h.1 h.2⟩
    have := hdw.2.1.arena.lits_lt w.toNat h.1 h.2 l hl; omega

private theorem m6_bveEntry_to_extNeed {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hdw : FullDenseInvW c F0 F_cur s) {lit : Nat} {w : BitVec 32}
    (h : FullBveEntryOkW F_cur s lit w) :
    (w &&& 0x80000000#32) ≠ 0#32 ∨ w.toNat + 2 < c.arena_cap := by
  unfold FullBveEntryOkW at h
  by_cases hb : (w &&& 0x80000000#32) ≠ 0#32
  · exact Or.inl hb
  · right; rw [ite_eq_right hb] at h
    have hwf := hdw.2.1.arena.refs_wf w.toNat h.1
    have hal := hdw.1.core_ok.arena_len_le; omega

private theorem m6_bveEntry_mono_scratch {F_cur : List (List Nat)} {s : FullState}
    {sc' : FullScratch} {lit : Nat} {w : BitVec 32}
    (h : FullBveEntryOkW F_cur s lit w) :
    FullBveEntryOkW F_cur { s with scratch := sc' } lit w := h

private theorem m6_bveEntry_congr_core {F_cur : List (List Nat)} {s s' : FullState}
    {lit : Nat} {w : BitVec 32} (h : FullBveEntryOkW F_cur s lit w)
    (hcv : s'.core.cur_vars = s.core.cur_vars) (har : s'.core.arena = s.core.arena)
    (hal : s'.core.arena_len = s.core.arena_len) :
    FullBveEntryOkW F_cur s' lit w := by
  unfold FullBveEntryOkW at h ⊢
  by_cases hb : (w &&& 0x80000000#32) ≠ 0#32
  · rw [ite_eq_left hb] at h ⊢; exact ⟨by rw [hcv]; exact h.1, h.2⟩
  · rw [ite_eq_right hb] at h ⊢
    have hrefs : fullArenaClauseRefs s' = fullArenaClauseRefs s := by
      unfold fullArenaClauseRefs fullArenaClauseRefsCore; rw [har, hal]
    have hgb : fullArenaClauseGarb s' w.toNat = fullArenaClauseGarb s w.toNat := by
      unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore; rw [har]
    rw [hrefs, hgb]; exact h

private theorem m6_bceWeak_mono_markGarb {c : FullCfg} {s s' : FullState} {w : BitVec 32}
    (h : FullBveBceWeakOk c s w) (hrefs : fullArenaClauseRefs s' = fullArenaClauseRefs s)
    (hal : s'.core.arena_len = s.core.arena_len)
    (hsz : ∀ r ∈ fullArenaClauseRefs s, fullArenaClauseSize s' r = fullArenaClauseSize s r)
    (hlits : ∀ r ∈ fullArenaClauseRefs s, fullArenaClauseLits s' r = fullArenaClauseLits s r) :
    FullBveBceWeakOk c s' w := by
  unfold FullBveBceWeakOk at h ⊢
  by_cases hb : (w &&& 0x80000000#32) ≠ 0#32
  · rw [ite_eq_left hb] at h ⊢; exact h
  · rw [ite_eq_right hb] at h ⊢; rw [hrefs, hal, hsz _ h.1, hlits _ h.1]; exact h

private theorem m6_fullDenseInvW_with_lit_mark4 {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (h : FullDenseInvW c F0 F_cur s)
    {lm' : List (BitVec 8)} (hlm_len : lm'.length = 2 * c.max_vars)
    (hlm_clr : ∀ l < 2 * c.max_vars, lm'[l]?.getD 0#8 = 0#8) :
    FullDenseInvW c F0 F_cur { s with core := { s.core with lit_mark := lm' } } :=
  ⟨⟨{ h.1.core_ok with lit_mark_len := hlm_len }, h.1.scratch_ok⟩,
   { h.2.1 with
     arena := { h.2.1.arena with len_ok := h.2.1.arena.len_ok }
     watches := h.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) },
   ⟨h.2.2.1.1, hlm_clr⟩, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

private theorem m6_fullDenseInvW_of_delBin {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
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

private theorem m6_fullDenseInvW_of_setInactive {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (h : FullDenseInvW c F0 F_cur s)
    {fl' : List (BitVec 32)} {unass' : BitVec 64} (hfl : fl'.length = c.max_vars) :
    FullDenseInvW c F0 F_cur
      { s with core := { s.core with flags := fl', unassigned := unass' } } :=
  ⟨⟨{ h.1.core_ok with flags_len := hfl }, h.1.scratch_ok⟩,
   { h.2.1 with
     arena := { h.2.1.arena with len_ok := h.2.1.arena.len_ok }
     watches := h.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) },
   h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

private theorem m6_pl_nl_eq (v : BitVec 32) (hv : v.toNat < 2 * 2 ^ 28) :
    (v <<< (1 : Nat)).toNat = 2 * v.toNat ∧
    ((v <<< (1 : Nat)) ||| 1#32).toNat = 2 * v.toNat + 1 := by
  have h1 : (v <<< (1 : Nat)).toNat = 2 * v.toNat := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]; omega
  have h2 : ((v <<< (1 : Nat)) ||| 1#32).toNat = 2 * v.toNat + 1 := by
    rw [BitVec.toNat_or, h1, BitVec.toNat_ofNat]
    have h1m : 1 % 2 ^ 32 = 1 := rfl
    rw [h1m]
    apply Nat.eq_of_testBit_eq; intro i
    cases i with
    | zero =>
      rw [Nat.testBit_or, Nat.testBit_zero, Nat.testBit_zero, Nat.testBit_zero, Nat.mul_mod_right]
      simp [show (2 * v.toNat + 1) % 2 = 1 by omega]
    | succ j =>
      rw [Nat.testBit_or, Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_succ]
      simp [Nat.mul_add_div (by omega : 0 < 2)]
  exact ⟨h1, h2⟩

/-! ## 2. `full_bve_collect_m6` (Canonical `Full.fullBveCollectSpec`) -/

/-- Parametric `Func.wp` proof for `full_bve_collect_m6`, directly certifying canonical
`Full.fullBveCollectSpec`. -/
theorem full_bve_collect_m6_wp (Γ : Env) :
    ∀ a m Q X, Full.fullBveCollectSpec a m Q X →
      Func.wp Γ full_bve_collect_m6_body a m Q X := by
  rintro ⟨h, lit, out_ptr, cap, ⟨⟩⟩ m0 Q X
    ⟨c, F0, F_cur, s0, out_off, R, rfl, hdw0, hlit_lt, hout_ptr, hoff_le, hm0, hQ⟩
  have hmx := c.hmaxv; have hwc := c.hwcap; have harc := c.harena; have hsc := c.hscr
  unfold dimacsBound at hmx hwc harc hsc
  have hcv_le := hdw0.1.core_ok.cur_vars_le
  have hwlen_le := hdw0.1.core_ok.wlen_le
  have hdw_s0 := m6_denseWatchesInv_of_w hdw0
  have hbd := hdw_s0.layout.bounds lit.toNat hlit_lt
  have hlv0 : (lit.setWidth 64 <<< (1 : Nat)).toNat < s0.core.wvec.length := by
    rw [hdw0.1.core_ok.wvec_len]; c0_bound
  have hlv1 : (lit.setWidth 64 <<< (1 : Nat) + 1#64).toNat < s0.core.wvec.length := by
    rw [hdw0.1.core_ok.wvec_len]; c0_bound
  unfold Func.wp full_bve_collect_m6_body
  c0_hsteps_nogrp
  let off_l := (s0.core.wvec[(lit.setWidth 64 <<< (1 : Nat)).toNat]'hlv0).setWidth 64
  let sz_l := (s0.core.wvec[(lit.setWidth 64 <<< (1 : Nat) + 1#64).toNat]'hlv1).setWidth 64
  let end_l := off_l + sz_l
  have hoff_eq : off_l.toNat = fullWatchOffCore s0.core lit.toNat := by
    unfold off_l fullWatchOffCore
    rw [List.getElem?_eq_getElem (by rw [hdw0.1.core_ok.wvec_len]; omega), Option.getD_some,
      m6_zext32_toNat]
    exact congrArg BitVec.toNat (m6_getElem_congr (by c0_bound) _ _)
  have hsz_eq : sz_l.toNat = fullWatchSizeCore s0.core lit.toNat := by
    unfold sz_l fullWatchSizeCore
    rw [List.getElem?_eq_getElem (by rw [hdw0.1.core_ok.wvec_len]; omega), Option.getD_some,
      m6_zext32_toNat]
    exact congrArg BitVec.toNat (m6_getElem_congr (by c0_bound) _ _)
  have hend_eq : end_l.toNat = off_l.toNat + sz_l.toNat := by
    dsimp only [end_l]; rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
  have hsum_c0 :
      ((s0.core.wvec[2 * lit.toNat % 2 ^ 64]'(by
          rw [hdw0.1.core_ok.wvec_len]; omega)).toNat +
        (s0.core.wvec[(2 * lit.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(by
          rw [hdw0.1.core_ok.wvec_len]; simp; omega)).toNat) % 2 ^ 64 = end_l.toNat := by
    have h1 : (s0.core.wvec[2 * lit.toNat % 2 ^ 64]'(by
        rw [hdw0.1.core_ok.wvec_len]; omega)).toNat = off_l.toNat := by
      rw [hoff_eq]; unfold fullWatchOffCore
      rw [List.getElem?_eq_getElem (by rw [hdw0.1.core_ok.wvec_len]; omega), Option.getD_some]
      exact congrArg BitVec.toNat (m6_getElem_congr (by omega) _ _)
    have h2 : (s0.core.wvec[(2 * lit.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(by
        rw [hdw0.1.core_ok.wvec_len]; simp; omega)).toNat = sz_l.toNat := by
      rw [hsz_eq]; unfold fullWatchSizeCore
      rw [List.getElem?_eq_getElem (by rw [hdw0.1.core_ok.wvec_len]; omega), Option.getD_some]
      exact congrArg BitVec.toNat (m6_getElem_congr (by simp; omega) _ _)
    rw [h1, h2, Nat.mod_eq_of_lt (by omega), hend_eq]
  refine wp_loop_break_group (brkTs := [i64, i32]) (lpTs := [i64, i32])
    (fun (_p_b, cnt_b, ()) mb => ∃ scr_b : List (BitVec 32),
      let sb : FullState := { s0 with scratch := { s0.scratch with scratch_buf := scr_b } }
      scr_b.length = c.scratch_cap ∧ cnt_b.toNat ≤ cap.toNat ∧
      (∀ i < c.scratch_cap, (i < out_off ∨ out_off + cap.toNat ≤ i) →
        scr_b[i]? = s0.scratch.scratch_buf[i]?) ∧
      (∀ i < cnt_b.toNat, FullBveEntryOkW F_cur sb lit.toNat (scr_b[out_off + i]?.getD 0#32)) ∧
      (FullMem c sb ⋆ R) mb)
    (fun rem (p, cnt, ()) mp => ∃ scr_p : List (BitVec 32),
      let sp : FullState := { s0 with scratch := { s0.scratch with scratch_buf := scr_p } }
      scr_p.length = c.scratch_cap ∧ p.toNat ≤ end_l.toNat ∧ rem = end_l.toNat - p.toNat ∧
      cnt.toNat ≤ cap.toNat ∧
      DenseWatchSliceOk F_cur s0.core lit.toNat p.toNat rem ∧
      (∀ i < c.scratch_cap, (i < out_off ∨ out_off + cap.toNat ≤ i) →
        scr_p[i]? = s0.scratch.scratch_buf[i]?) ∧
      (∀ i < cnt.toNat, FullBveEntryOkW F_cur sp lit.toNat (scr_p[out_off + i]?.getD 0#32)) ∧
      (FullMem c sp ⋆ R) mp)
    ?_ ?_ ?_
  · rintro _ ⟨_p_b, cnt_b, ⟨⟩⟩ mb ⟨scr_b, hlen_b, hcnt_b, hout_b, hent_b, hmb⟩
    c0_hsteps!; exact hQ cnt_b scr_b mb hlen_b hout_b (Or.inr ⟨hcnt_b, hent_b⟩) hmb
  · rintro B L rem ⟨p, cnt, ⟨⟩⟩ mp hB hL
      ⟨scr_p, hlen_p, hp_le, hrem, hcnt_le, hslice, hout_p, hent_p, hmp⟩
    c0_hsplit
    · have hp_lt : p.toNat < end_l.toNat := by rw [hsum_c0] at hc; exact hc
      have hpw : p.toNat < s0.core.wstk.length := by rw [hdw0.1.core_ok.wstk_len_arr]; omega
      have hp1_nat : (p + 1#64).toNat = p.toNat + 1 := by c0_bound
      cases hslice with
      | empty => omega
      | @bin _ rem1 w0 hwp hflag _ hot_lt hent_bin hrest =>
        have hw0_eq : s0.core.wstk[p.toNat]'hpw = w0 := by
          rw [List.getElem?_eq_getElem hpw] at hwp; exact Option.some.inj hwp
        let ot := w0 &&& 0x7FFFFFFF#32
        have hot_lt' : ot.toNat < 2 * s0.core.cur_vars := hot_lt
        have hot_v : (ot.setWidth 64).toNat < s0.core.vals.length := by
          rw [hdw0.1.core_ok.vals_len, m6_zext32_toNat]; omega
        c0_hsplit
        · rw [hw0_eq]
          c0_hsplit
          · c0_hsteps!
            exact hL rem1 (p + 1#64, cnt, ()) mp (by omega)
              ⟨scr_p, hlen_p, by omega, by omega, hcnt_le, by rw [hp1_nat]; exact hrest,
               hout_p, hent_p, hmp⟩
          · c0_hsplit
            · c0_hsteps!; exact hQ 0xFFFFFFFF#32 scr_p mp hlen_p hout_p (Or.inl rfl) hmp
            · have hcnt_lt : cnt.toNat < cap.toNat := by omega
              have hcnt1 : (cnt + 1#32).toNat = cnt.toNat + 1 := by c0_bound
              have hidx_sc : out_off + cnt.toNat < scr_p.length := by omega
              have hsc_ptr : out_ptr + cnt.setWidth 64 * 4 =
                  c.pScratchBuf + BitVec.ofNat 64 (4 * (out_off + cnt.toNat)) := by
                rw [hout_ptr, BitVec.add_assoc]; congr 1
                apply BitVec.eq_of_toNat_eq
                simp [BitVec.toNat_add, BitVec.toNat_mul]; omega
              c0_hsteps
              rw [hsc_ptr]
              c0_hsteps!
              let scr' := scr_p.set (out_off + cnt.toNat) w0
              have hw0_ok : FullBveEntryOkW F_cur
                  { s0 with scratch := { s0.scratch with scratch_buf := scr' } } lit.toNat w0 := by
                unfold FullBveEntryOkW; rw [ite_eq_left hflag]
                exact ⟨hot_lt, hent_bin⟩
              exact hL rem1 (p + 1#64, cnt + 1#32, ()) _ (by omega)
                ⟨scr', by simp [scr', hlen_p], by omega, by omega, by omega,
                 by rw [hp1_nat]; exact hrest,
                 fun i hi hor => by
                   dsimp only [scr']; rw [List.getElem?_set_ne (by omega)]; exact hout_p i hi hor,
                 fun i hi => by
                   dsimp only [scr']
                   rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp (hcnt1 ▸ hi)) with h | h
                   · rw [List.getElem?_set_ne (by omega)]
                     exact m6_bveEntry_mono_scratch (hent_p i h)
                   · subst h; rw [List.getElem?_set_self hidx_sc, Option.getD_some]
                     exact hw0_ok, hm⟩
        · rw [hw0_eq] at hc; exact absurd hc hflag
      | @occ _ rem2 w0 cr hwp hwp1 hflag _ hcr_lt31 href_cr hrest =>
        have hw0_eq : s0.core.wstk[p.toNat]'hpw = w0 := by
          rw [List.getElem?_eq_getElem hpw] at hwp; exact Option.some.inj hwp
        have hp1_w : (p + 1#64).toNat < s0.core.wstk.length := by
          rw [hdw0.1.core_ok.wstk_len_arr]; omega
        have hp1_c0 : (p.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 = p.toNat + 1 := by
          simp; omega
        have hcr_eq :
            s0.core.wstk[(p.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(by
              rw [hdw0.1.core_ok.wstk_len_arr]; omega) = cr := by
          rw [List.getElem?_eq_getElem (by rw [hdw0.1.core_ok.wstk_len_arr]; omega)] at hwp1
          exact (m6_getElem_congr hp1_c0 _ _).trans (Option.some.inj hwp1)
        have hcr_eq' : s0.core.wstk[(p + (1 : BitVec 64)).toNat]'hp1_w = cr :=
          (m6_getElem_congr (by c0_bound) _ _).trans hcr_eq
        have hp2_nat : (p + 1#64 + 1#64).toNat = p.toNat + 2 := by c0_bound
        have hrest' : DenseWatchSliceOk F_cur s0.core lit.toNat
            (p + 1#64 + 1#64).toNat rem2 := by
          rw [hp2_nat]; exact hrest
        have hwf_cr := hdw0.2.1.arena.refs_wf cr.toNat href_cr
        have hal_le := hdw0.1.core_ok.arena_len_le
        have har_len_cr : cr.toNat < s0.core.arena.length := by
          rw [hdw0.1.core_ok.arena_len_arr]; omega
        c0_hsplit
        · rw [hw0_eq] at hc; exact absurd hflag hc
        · c0_hsplit
          · rw [hsum_c0] at hc; simp at hc; omega
          · c0_hsplit
            · c0_hsteps!
              exact hL rem2 (p + 1#64 + 1#64, cnt, ()) mp (by omega)
                ⟨scr_p, hlen_p, by omega, by omega, hcnt_le, hrest', hout_p, hent_p, hmp⟩
            · simp only [hcr_eq, hcr_eq'] at hc ⊢
              have hng_cr : fullArenaClauseGarb s0 cr.toNat = false := by
                unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore
                rw [List.getElem?_eq_getElem har_len_cr, Option.getD_some]
                rw [m6_and_garb_zero_of_mask4 hc]; rfl
              have hcr2_ar : (cr.setWidth 64 + 2#64).toNat < s0.core.arena.length := by
                rw [hdw0.1.core_ok.arena_len_arr]; c0_bound
              c0_hsplit
              · c0_hsteps!; exact hQ 0xFFFFFFFF#32 scr_p mp hlen_p hout_p (Or.inl rfl) hmp
              · c0_hsplit
                · c0_hsteps!; exact hQ 0xFFFFFFFF#32 scr_p mp hlen_p hout_p (Or.inl rfl) hmp
                · have hcnt_lt : cnt.toNat < cap.toNat := by omega
                  have hcnt1 : (cnt + 1#32).toNat = cnt.toNat + 1 := by c0_bound
                  have hidx_sc : out_off + cnt.toNat < scr_p.length := by omega
                  have hcr_nobin : (cr &&& 0x80000000#32) = 0#32 := by
                    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_and]
                    have hlt : cr.toNat < 2 ^ 31 := hcr_lt31
                    have : (cr.toNat &&& (0x80000000#32 : BitVec 32).toNat) = 0 := by
                      apply Nat.eq_of_testBit_eq; intro k
                      simp only [Nat.testBit_and, Nat.zero_testBit]
                      by_cases hk : k = 31
                      · subst hk; rw [Nat.testBit_lt_two_pow hlt]; simp
                      · have : (0x80000000#32 : BitVec 32).toNat.testBit k = false := by
                          change (2 ^ 31 : Nat).testBit k = false
                          rw [Nat.testBit_two_pow]; exact decide_eq_false (Ne.symm hk)
                        rw [this]; simp
                    simpa using this
                  have hsc_ptr : out_ptr + cnt.setWidth 64 * 4 =
                      c.pScratchBuf + BitVec.ofNat 64 (4 * (out_off + cnt.toNat)) := by
                    rw [hout_ptr, BitVec.add_assoc]; congr 1
                    apply BitVec.eq_of_toNat_eq
                    simp [BitVec.toNat_add, BitVec.toNat_mul]; omega
                  c0_hsteps
                  rw [hsc_ptr]
                  c0_hsteps!
                  let scr' := scr_p.set (out_off + cnt.toNat) cr
                  have hcr_ok : FullBveEntryOkW F_cur
                      { s0 with scratch := { s0.scratch with scratch_buf := scr' } }
                      lit.toNat cr := by
                    unfold FullBveEntryOkW; rw [ite_eq_right (fun h => h hcr_nobin)]
                    exact ⟨href_cr, hng_cr⟩
                  exact hL rem2 (p + 1#64 + 1#64, cnt + 1#32, ()) _ (by omega)
                    ⟨scr', by simp [scr', hlen_p], by omega, by omega, by omega, hrest',
                     fun i hi hor => by
                       dsimp only [scr']; rw [List.getElem?_set_ne (by omega)]
                       exact hout_p i hi hor,
                     fun i hi => by
                       dsimp only [scr']
                       rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp (hcnt1 ▸ hi)) with h | h
                       · rw [List.getElem?_set_ne (by omega)]
                         exact m6_bveEntry_mono_scratch (hent_p i h)
                       · subst h; rw [List.getElem?_set_self hidx_sc, Option.getD_some]
                         exact hcr_ok, hm⟩
    · c0_hsteps!; exact hB (p, cnt, ()) mp ⟨scr_p, hlen_p, hcnt_le, hout_p, hent_p, hmp⟩
  · intro _ L _ hL; c0_hsteps!
    exact hL sz_l.toNat (off_l, 0#32, ()) m0
      ⟨s0.scratch.scratch_buf, hdw0.1.scratch_ok.scratch_buf_len, by omega, by omega,
       Nat.zero_le _, by rw [hoff_eq, hsz_eq]; exact hdw_s0.slices lit.toNat hlit_lt,
       fun _ _ _ => rfl, fun _ h => by simp at h, hm0⟩

/-! ## 3. Gate Extraction Helpers (`mark_and`, `get_tern`, `match_tern`, `find_ite`, `gates`) -/

/-- Contract for `full_bve_mark_and_m6`: marks an AND-gate binary mask at `scr[mask_off..+16)`
while checking `vals[l]`, restoring `lit_mark`, and preserving `FullDenseInvW`. -/
def fullBveMarkAndM6Spec : Spec [i64, i32, i32, i32, i32, i32] [.bool] :=
  fun (h, v_lit, cr, n_off, nn, mask_off, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧
      cr.toNat ∈ fullArenaClauseRefs s ∧ fullArenaClauseGarb s cr.toNat = false ∧
      n_off.toNat + nn.toNat ≤ mask_off.toNat ∧ mask_off.toNat + 16 ≤ c.scratch_cap ∧
      nn.toNat ≤ 512 ∧
      (∀ j < nn.toNat, FullBveEntryOkW F_cur s (v_lit.toNat ^^^ 1)
        (s.scratch.scratch_buf[n_off.toNat + j]?.getD 0#32)) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (ok : Bool) lm' scr' m',
        let s' : FullState :=
          { s with
            core := { s.core with lit_mark := lm' }
            scratch := { s.scratch with scratch_buf := scr' } }
        FullDenseInvW c F0 F_cur s' →
        (∀ i < c.scratch_cap, (i < mask_off.toNat ∨ mask_off.toNat + 16 ≤ i) →
          scr'[i]? = s.scratch.scratch_buf[i]?) →
        (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

theorem fullBveMarkAndM6Spec_noExit :
    ∀ xs m Q X, fullBveMarkAndM6Spec xs m Q X →
      fullBveMarkAndM6Spec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => h

/-- Parametric `Func.wp` proof for `full_bve_mark_and_m6`. -/
theorem full_bve_mark_and_m6_wp (Γ : Env) :
    ∀ a m Q X, fullBveMarkAndM6Spec a m Q X →
      Func.wp Γ full_bve_mark_and_m6_body a m Q X := by
  rintro ⟨h, v_lit, cr, n_off, nn, mask_off, ⟨⟩⟩ m0 Q X
    ⟨c, F0, F_cur, s0, R, rfl, hdw0, href, hng, hnoff, hmoff, hnn512, hent_n, hm0, hQ⟩
  have hmx := c.hmaxv; have harc := c.harena; have hsc := c.hscr
  unfold dimacsBound at hmx harc hsc
  have hwf := hdw0.2.1.arena.refs_wf cr.toNat href
  have hal_le := hdw0.1.core_ok.arena_len_le
  have hcv_le := hdw0.1.core_ok.cur_vars_le
  have hcr2_ar : (cr.setWidth 64 + 2#64).toNat < s0.core.arena.length := by
    rw [hdw0.1.core_ok.arena_len_arr]; c0_bound
  let sz := s0.core.arena[(cr.setWidth 64 + 2#64).toNat]'hcr2_ar
  have hsz_eq : sz.toNat = fullArenaClauseSizeCore s0.core cr.toNat := by
    unfold sz fullArenaClauseSizeCore
    rw [List.getElem?_eq_getElem (by rw [hdw0.1.core_ok.arena_len_arr]; omega), Option.getD_some]
    exact congrArg BitVec.toNat (m6_getElem_congr (by c0_bound) _ _)
  have hC_len : (fullArenaClauseLits s0 cr.toNat).length = sz.toNat := by
    unfold fullArenaClauseLits fullArenaClauseLitsCore
    simp only [List.length_map, List.length_take, List.length_drop]
    rw [hdw0.1.core_ok.arena_len_arr]; omega
  unfold Func.wp full_bve_mark_and_m6_body
  c0_hsteps_nogrp
  -- Loop 1: mark `lm[l ^ 1] = 1` for unassigned `l != v_lit`
  refine wp_loop_break_group (brkTs := [i32, .bool, i32]) (lpTs := [i32, i32])
    (fun (need_b, sat_b, _ib, ()) m1 => ∃ lm1 : List (BitVec 8),
      let s1 : FullState := { s0 with core := { s0.core with lit_mark := lm1 } }
      lm1.length = 2 * c.max_vars ∧
      (∀ x < 2 * c.max_vars, lm1[x]?.getD 0#8 ≠ 0#8 →
        (x ^^^ 1) ∈ fullArenaClauseLits s0 cr.toNat) ∧
      (FullMem c s1 ⋆ R) m1)
    (fun rem1 (need_i, i, ()) m1 => ∃ lm1 : List (BitVec 8),
      let s1 : FullState := { s0 with core := { s0.core with lit_mark := lm1 } }
      lm1.length = 2 * c.max_vars ∧ i.toNat ≤ sz.toNat ∧ rem1 = sz.toNat - i.toNat ∧
      (∀ x < 2 * c.max_vars, lm1[x]?.getD 0#8 ≠ 0#8 →
        (x ^^^ 1) ∈ fullArenaClauseLits s0 cr.toNat) ∧
      (FullMem c s1 ⋆ R) m1)
    ?_ ?_ ?_
  · rintro _ ⟨need_b, sat_b, _ib, ⟨⟩⟩ m1 ⟨lm1, hlm1, hsup1, hm1⟩
    c0_hsteps_nogrp
    refine wp_join0 (P := fun mj => mj = m1)
      (fun _ mj hm_eq => by
        subst mj
        -- `sat || need == 0`: unmark `lm1` and return `false`
        c0_hsteps_nogrp
        refine wp_loop_group (ts := [i32])
          (fun rem_u (iu, ()) mu => ∃ lm_u : List (BitVec 8),
            let su : FullState := { s0 with core := { s0.core with lit_mark := lm_u } }
            lm_u.length = 2 * c.max_vars ∧ iu.toNat ≤ sz.toNat ∧ rem_u = sz.toNat - iu.toNat ∧
            (∀ x < 2 * c.max_vars, lm_u[x]?.getD 0#8 ≠ 0#8 →
              (x ^^^ 1) ∈ (fullArenaClauseLits s0 cr.toNat).drop iu.toNat) ∧
            (FullMem c su ⋆ R) mu)
          ?_ ?_
        · rintro Lu rem_u ⟨iu, ⟨⟩⟩ mu hLu ⟨lm_u, hlmu, hiu_le, rfl, hrem_lm, hmu⟩
          c0_hsplit
          · have hiu_lt : iu.toNat < sz.toNat := hc
            have hcri : (cr.setWidth 64 + 3#64 + iu.setWidth 64).toNat <
                s0.core.arena.length := by
              rw [hdw0.1.core_ok.arena_len_arr]; c0_bound
            let li := s0.core.arena[(cr.setWidth 64 + 3#64 + iu.setWidth 64).toNat]'hcri
            have hli_lt : li.toNat < 2 * s0.core.cur_vars := by
              have hmem : li.toNat ∈ fullArenaClauseLitsCore s0.core cr.toNat := by
                rw [mem_fullArenaClauseLitsCore_iff (by rw [hdw0.1.core_ok.arena_len_arr]; omega)]
                exact ⟨iu.toNat, by omega, congrArg BitVec.toNat
                  (m6_getElem_congr (by c0_bound) _ _)⟩
              exact hdw0.2.1.arena.lits_lt cr.toNat href hng _ hmem
            have hlin_lm : ((li ^^^ 1#32).setWidth 64).toNat < lm_u.length := by
              rw [hlmu, m6_zext32_toNat]; change li.toNat ^^^ 1 < 2 * c.max_vars
              have := fullInv_var_xor1 li.toNat; omega
            have hiu1 : (iu + 1#32).toNat = iu.toNat + 1 := by c0_bound
            c0_hsteps!
            exact hLu (sz.toNat - (iu + 1#32).toNat) (iu + 1#32, ()) _ (by omega)
              ⟨lm_u.set ((li ^^^ 1#32).setWidth 64).toNat 0#8, by simp [hlmu], by omega, rfl,
               fun x hx hnz => by
                 rw [m6_zext32_toNat] at hnz
                 by_cases hxe : x = (li ^^^ 1#32).toNat
                 · subst hxe; rw [List.getElem?_set_self (by
                     rw [m6_zext32_toNat] at hlin_lm; exact hlin_lm), Option.getD_some] at hnz
                   exact absurd rfl hnz
                 · rw [List.getElem?_set_ne (Ne.symm hxe)] at hnz
                   have hmem := hrem_lm x hx hnz
                   have hdrop_eq : (fullArenaClauseLits s0 cr.toNat).drop iu.toNat =
                       li.toNat :: (fullArenaClauseLits s0 cr.toNat).drop (iu + 1#32).toNat := by
                     rw [hiu1, List.drop_eq_getElem_cons (by omega)]
                     congr 1; unfold fullArenaClauseLits fullArenaClauseLitsCore
                     simp only [List.getElem_map, List.getElem_take, List.getElem_drop]
                     exact congrArg BitVec.toNat (m6_getElem_congr (by c0_bound) _ _)
                   rw [hdrop_eq, List.mem_cons] at hmem
                   refine hmem.resolve_left fun heq => hxe ?_
                   have := congrArg (· ^^^ 1) heq
                   rw [Nat.xor_assoc] at this; simpa using this, hm⟩
          · have hiu_eq : iu.toNat = sz.toNat := by
              have hiu_ge : sz.toNat ≤ iu.toNat := by
                dsimp only [sz]; simpa using Nat.le_of_not_lt hc
              exact Nat.le_antisymm hiu_le hiu_ge
            have hlm_clr : ∀ x < 2 * c.max_vars, lm_u[x]?.getD 0#8 = 0#8 :=
              fun x hx => Classical.byContradiction fun hnz => by
                have hmem := hrem_lm x hx hnz
                rw [hiu_eq, ← hC_len, List.drop_length] at hmem; cases hmem
            c0_hsteps!
            exact hQ false lm_u s0.scratch.scratch_buf mu
              (m6_fullDenseInvW_with_lit_mark4 hdw0 hlmu hlm_clr) (fun _ _ _ => rfl) hmu
        · intro Lu hLu; c0_hsteps!
          exact hLu sz.toNat (0#32, ()) m1 ⟨lm1, hlm1, Nat.zero_le _, by simp, hsup1, hm1⟩)
      (fun J0 hJ0 => by
        c0_hsplit
        · c0_hsteps!; exact hJ0 m1 rfl
        · c0_hsplit
          · c0_hsteps!; exact hJ0 m1 rfl
          · -- Zero `scr[mask_off ..< mask_off + 16)`, scan `scr[n_off ..< n_off + nn)`
            c0_hsteps_nogrp
            refine wp_loop_group (ts := [i32])
              (fun rem_z (k, ()) mz => ∃ scr_z : List (BitVec 32),
                let sz_s : FullState :=
                  { s0 with
                    core := { s0.core with lit_mark := lm1 },
                    scratch := { s0.scratch with scratch_buf := scr_z } }
                scr_z.length = c.scratch_cap ∧ k.toNat ≤ 16 ∧ rem_z = 16 - k.toNat ∧
                (∀ i < c.scratch_cap, (i < mask_off.toNat ∨ mask_off.toNat + 16 ≤ i) →
                  scr_z[i]? = s0.scratch.scratch_buf[i]?) ∧
                (FullMem c sz_s ⋆ R) mz)
              ?_ ?_
            · rintro Lz rem_z ⟨k, ⟨⟩⟩ mz hLz ⟨scr_z, hscz, hk_le, rfl, hout_z, hmz⟩
              c0_hsplit
              · have hk_lt : k.toNat < 16 := hc
                have hmk_sc : ((mask_off + k).setWidth 64).toNat < scr_z.length := by
                  rw [hscz, m6_zext32_toNat]; c0_bound
                have hk1 : (k + 1#32).toNat = k.toNat + 1 := by c0_bound
                c0_hsteps!
                exact hLz (16 - (k + 1#32).toNat) (k + 1#32, ()) _ (by omega)
                  ⟨scr_z.set ((mask_off + k).setWidth 64).toNat 0#32, by simp [hscz], by omega,
                   rfl, fun i hi hor => by
                     rw [List.getElem?_set_ne (by rw [m6_zext32_toNat]; c0_bound)]
                     exact hout_z i hi hor, hm⟩
              · -- Match binaries in `scr[n_off ..< n_off + nn)`
                c0_hsteps_nogrp
                refine wp_loop_group (ts := [i32, i32])
                  (fun rem_j (matched, j, ()) mj =>
                    ∃ (lm_j : List (BitVec 8)) (scr_j : List (BitVec 32)),
                    let sj : FullState :=
                      { s0 with
                        core := { s0.core with lit_mark := lm_j },
                        scratch := { s0.scratch with scratch_buf := scr_j } }
                    lm_j.length = 2 * c.max_vars ∧ scr_j.length = c.scratch_cap ∧
                    j.toNat ≤ nn.toNat ∧ rem_j = nn.toNat - j.toNat ∧
                    (∀ x < 2 * c.max_vars, lm_j[x]?.getD 0#8 ≠ 0#8 →
                      (x ^^^ 1) ∈ fullArenaClauseLits s0 cr.toNat) ∧
                    (∀ i < c.scratch_cap, (i < mask_off.toNat ∨ mask_off.toNat + 16 ≤ i) →
                      scr_j[i]? = s0.scratch.scratch_buf[i]?) ∧
                    (FullMem c sj ⋆ R) mj)
                  ?_ ?_
                · rintro Lj rem_j ⟨matched, j, ⟨⟩⟩ mj hLj
                    ⟨lm_j, scr_j, hlmj, hscj, hj_le, rfl, hsup_j, hout_j, hmj⟩
                  c0_hsplit
                  · have hj_lt : j.toNat < nn.toNat := hc
                    have hnj_sc : ((n_off + j).setWidth 64).toNat < scr_j.length := by
                      rw [hscj, m6_zext32_toNat]; c0_bound
                    have hj1 : (j + 1#32).toNat = j.toNat + 1 := by c0_bound
                    let wj := scr_j[((n_off + j).setWidth 64).toNat]'hnj_sc
                    c0_hsteps_nogrp
                    refine wp_join_state (ts := [i32])
                      (α := BitVec 32 × List (BitVec 8) × List (BitVec 32)) (fun x => (x.1, ()))
                      (fun x mx => x.2.1.length = 2 * c.max_vars ∧ x.2.2.length = c.scratch_cap ∧
                        (∀ y < 2 * c.max_vars, x.2.1[y]?.getD 0#8 ≠ 0#8 →
                          (y ^^^ 1) ∈ fullArenaClauseLits s0 cr.toNat) ∧
                        (∀ i < c.scratch_cap, (i < mask_off.toNat ∨ mask_off.toNat + 16 ≤ i) →
                          x.2.2[i]? = s0.scratch.scratch_buf[i]?) ∧
                        (FullMem c { s0 with
                          core := { s0.core with lit_mark := x.2.1 },
                          scratch := { s0.scratch with scratch_buf := x.2.2 } } ⋆ R) mx)
                      (fun _ ⟨m', lm', scr'⟩ mx ⟨hlm', hsc', hsup', hout', hmx⟩ => by
                        c0_hsteps!
                        exact hLj (nn.toNat - (j + 1#32).toNat) (m', j + 1#32, ()) mx (by omega)
                          ⟨lm', scr', hlm', hsc', by omega, rfl, hsup', hout', hmx⟩)
                      (fun Jm hJm => by
                        c0_hsplit
                        · -- Binary entry: check `lm_j[ot] == 1`
                          have hwj_orig :
                              wj = s0.scratch.scratch_buf[n_off.toNat + j.toNat]?.getD 0#32 := by
                            have hnj_eq :
                                ((n_off + j).setWidth 64).toNat = n_off.toNat + j.toNat := by
                              rw [m6_zext32_toNat]; c0_bound
                            have hget :=
                              hout_j (n_off.toNat + j.toNat) (by omega) (Or.inl (by omega))
                            have hnj' : n_off.toNat + j.toNat < scr_j.length := by omega
                            rw [List.getElem?_eq_getElem hnj'] at hget
                            rw [← hget, Option.getD_some]
                            exact m6_getElem_congr hnj_eq hnj_sc hnj'
                          have hwj_flag : (wj &&& 0x80000000#32) ≠ 0#32 := hc
                          have hent_j := hent_n j.toNat hj_lt
                          rw [← hwj_orig] at hent_j
                          unfold FullBveEntryOkW at hent_j
                          rw [ite_eq_left hwj_flag] at hent_j
                          let ot := wj &&& 0x7FFFFFFF#32
                          have hot_lt : ot.toNat < 2 * s0.core.cur_vars := hent_j.1
                          have hot_lm : (ot.setWidth 64).toNat < lm_j.length := by
                            rw [hlmj, m6_zext32_toNat]; omega
                          c0_hsteps_nogrp
                          refine wp_join_state (ts := [i32])
                            (α := BitVec 32 × List (BitVec 8) × List (BitVec 32))
                            (fun x => (x.1, ()))
                            (fun x mx => x.2.1.length = 2 * c.max_vars ∧
                              x.2.2.length = c.scratch_cap ∧
                              (∀ y < 2 * c.max_vars, x.2.1[y]?.getD 0#8 ≠ 0#8 →
                                (y ^^^ 1) ∈ fullArenaClauseLits s0 cr.toNat) ∧
                              (∀ i < c.scratch_cap,
                                (i < mask_off.toNat ∨ mask_off.toNat + 16 ≤ i) →
                                x.2.2[i]? = s0.scratch.scratch_buf[i]?) ∧
                              (FullMem c { s0 with
                                core := { s0.core with lit_mark := x.2.1 },
                                scratch := { s0.scratch with scratch_buf := x.2.2 } } ⋆ R) mx)
                            (fun _ ⟨m', lm', scr'⟩ mx ⟨hlm', hsc', hsup', hout', hmx⟩ => by
                              c0_hsteps!
                              exact hJm (m', lm', scr') mx ⟨hlm', hsc', hsup', hout', hmx⟩)
                            (fun J41 hJ41 => by
                              c0_hsplit
                              · have hidx_lt : ((mask_off + (j >>> (5 : Nat))).setWidth 64).toNat <
                                    scr_j.length := by
                                  rw [hscj, m6_zext32_toNat]
                                  have hj5 : (j >>> (5 : Nat)).toNat = j.toNat / 32 := by
                                    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
                                  rw [BitVec.toNat_add, hj5, Nat.mod_eq_of_lt (by omega)]; omega
                                have hot_sup :
                                    (ot.toNat ^^^ 1) ∈ fullArenaClauseLits s0 cr.toNat := by
                                  apply hsup_j ot.toNat (by omega)
                                  have hlt_l : ot.toNat < lm_j.length := by rw [hlmj]; omega
                                  rw [List.getElem?_eq_getElem hlt_l, Option.getD_some]
                                  have hidx_ot : ot.toNat = (scr_j[(n_off.toNat + j.toNat) %
                                      2 ^ 32]'(by omega) &&& (2147483647 : BitVec 32)).toNat :=
                                    congrArg (fun x => (x &&& (2147483647 : BitVec 32)).toNat)
                                      (m6_getElem_congr (by
                                        rw [m6_zext32_toNat, BitVec.toNat_add,
                                          Nat.mod_eq_of_lt (by omega)]) _ _)
                                  intro h0
                                  have h1 : BitVec.setWidth 32 (lm_j[ot.toNat]'hlt_l) =
                                      1#32 :=
                                    (congrArg (BitVec.setWidth 32)
                                      (m6_getElem_congr hidx_ot _ _)).trans hc
                                  rw [h0] at h1; cases h1
                                c0_hsteps!
                                exact hJ41
                                  (matched + 1#32, lm_j.set (ot.setWidth 64).toNat 2#8, _) _
                                  ⟨by simp [hlmj], by simp [hscj],
                                   fun x hx hnz => by
                                     rw [m6_zext32_toNat] at hnz
                                     by_cases hxe : x = ot.toNat
                                     · subst hxe; exact hot_sup
                                     · rw [List.getElem?_set_ne (Ne.symm hxe)] at hnz
                                       exact hsup_j x hx hnz,
                                   fun i hi hor => by
                                     have hj5 : (j >>> (5 : Nat)).toNat = j.toNat / 32 := by
                                       rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
                                     have hmi : ((mask_off + (j >>> (5 : Nat))).setWidth 64).toNat =
                                         mask_off.toNat + j.toNat / 32 := by
                                       rw [m6_zext32_toNat, BitVec.toNat_add, hj5,
                                         Nat.mod_eq_of_lt (by omega)]
                                     rw [List.getElem?_set_ne (by rw [hmi]; omega)]
                                     exact hout_j i hi hor, hm⟩
                              · c0_hsteps!
                                exact hJ41
                                  (matched, lm_j, scr_j) mj ⟨hlmj, hscj, hsup_j, hout_j, hmj⟩)
                        · c0_hsteps!
                          exact hJm (matched, lm_j, scr_j) mj ⟨hlmj, hscj, hsup_j, hout_j, hmj⟩)
                  · -- Unmark `lm_j`, return `true` if `matched >= need_b`, else zero & `false`
                    c0_hsteps_nogrp
                    refine wp_loop_group (ts := [i32])
                      (fun rem_u (iu, ()) mu => ∃ lm_u : List (BitVec 8),
                        let su : FullState :=
                          { s0 with
                            core := { s0.core with lit_mark := lm_u },
                            scratch := { s0.scratch with scratch_buf := scr_j } }
                        lm_u.length = 2 * c.max_vars ∧ iu.toNat ≤ sz.toNat ∧
                        rem_u = sz.toNat - iu.toNat ∧
                        (∀ x < 2 * c.max_vars, lm_u[x]?.getD 0#8 ≠ 0#8 →
                          (x ^^^ 1) ∈ (fullArenaClauseLits s0 cr.toNat).drop iu.toNat) ∧
                        (FullMem c su ⋆ R) mu)
                      ?_ ?_
                    · rintro Lu rem_u ⟨iu, ⟨⟩⟩ mu hLu ⟨lm_u, hlmu, hiu_le, rfl, hrem_lm, hmu⟩
                      c0_hsplit
                      · have hiu_lt : iu.toNat < sz.toNat := hc
                        have hcri : (cr.setWidth 64 + 3#64 + iu.setWidth 64).toNat <
                            s0.core.arena.length := by
                          rw [hdw0.1.core_ok.arena_len_arr]; c0_bound
                        let li := s0.core.arena[(cr.setWidth 64 + 3#64 + iu.setWidth 64).toNat]'hcri
                        have hli_lt : li.toNat < 2 * s0.core.cur_vars := by
                          have hmem : li.toNat ∈ fullArenaClauseLitsCore s0.core cr.toNat := by
                            rw [mem_fullArenaClauseLitsCore_iff (by
                              rw [hdw0.1.core_ok.arena_len_arr]; omega)]
                            exact ⟨iu.toNat, by omega, congrArg BitVec.toNat
                              (m6_getElem_congr (by c0_bound) _ _)⟩
                          exact hdw0.2.1.arena.lits_lt cr.toNat href hng _ hmem
                        have hlin_lm : ((li ^^^ 1#32).setWidth 64).toNat < lm_u.length := by
                          rw [hlmu, m6_zext32_toNat]; change li.toNat ^^^ 1 < 2 * c.max_vars
                          have := fullInv_var_xor1 li.toNat; omega
                        have hiu1 : (iu + 1#32).toNat = iu.toNat + 1 := by c0_bound
                        c0_hsteps!
                        exact hLu (sz.toNat - (iu + 1#32).toNat) (iu + 1#32, ()) _ (by omega)
                          ⟨lm_u.set ((li ^^^ 1#32).setWidth 64).toNat 0#8, by simp [hlmu], by omega,
                           rfl, fun x hx hnz => by
                             rw [m6_zext32_toNat] at hnz
                             by_cases hxe : x = (li ^^^ 1#32).toNat
                             · subst hxe; rw [List.getElem?_set_self (by
                                 rw [m6_zext32_toNat] at hlin_lm; exact hlin_lm),
                                 Option.getD_some] at hnz
                               exact absurd rfl hnz
                             · rw [List.getElem?_set_ne (Ne.symm hxe)] at hnz
                               have hmem := hrem_lm x hx hnz
                               have hdrop_eq : (fullArenaClauseLits s0 cr.toNat).drop iu.toNat =
                                   li.toNat :: (fullArenaClauseLits s0 cr.toNat).drop
                                     (iu + 1#32).toNat := by
                                 rw [hiu1, List.drop_eq_getElem_cons (by omega)]
                                 congr 1; unfold fullArenaClauseLits fullArenaClauseLitsCore
                                 simp only [List.getElem_map, List.getElem_take, List.getElem_drop]
                                 exact congrArg BitVec.toNat (m6_getElem_congr (by c0_bound) _ _)
                               rw [hdrop_eq, List.mem_cons] at hmem
                               refine hmem.resolve_left fun heq => hxe ?_
                               have := congrArg (· ^^^ 1) heq
                               rw [Nat.xor_assoc] at this; simpa using this, hm⟩
                      · have hiu_eq : iu.toNat = sz.toNat := by
                          have hiu_ge : sz.toNat ≤ iu.toNat := by
                            dsimp only [sz]; simpa using Nat.le_of_not_lt hc
                          exact Nat.le_antisymm hiu_le hiu_ge
                        have hlm_clr : ∀ x < 2 * c.max_vars, lm_u[x]?.getD 0#8 = 0#8 :=
                          fun x hx => Classical.byContradiction fun hnz => by
                            have hmem := hrem_lm x hx hnz
                            rw [hiu_eq, ← hC_len, List.drop_length] at hmem; cases hmem
                        have hdw_lm := m6_fullDenseInvW_with_lit_mark4 hdw0 hlmu hlm_clr
                        c0_hsplit
                        · c0_hsteps!
                          exact hQ true lm_u scr_j mu
                            (m6_fullDenseInvW_with_scratch hdw_lm
                              { hdw0.1.scratch_ok with scratch_buf_len := hscj } rfl rfl)
                            hout_j hmu
                        · c0_hsteps_nogrp
                          refine wp_loop_group (ts := [i32])
                            (fun rem_z2 (k2, ()) mz2 => ∃ scr_z2 : List (BitVec 32),
                              let sz2 : FullState :=
                                { s0 with
                                  core := { s0.core with lit_mark := lm_u },
                                  scratch := { s0.scratch with scratch_buf := scr_z2 } }
                              scr_z2.length = c.scratch_cap ∧ k2.toNat ≤ 16 ∧
                              rem_z2 = 16 - k2.toNat ∧
                              (∀ i < c.scratch_cap, (i < mask_off.toNat ∨ mask_off.toNat + 16 ≤ i) →
                                scr_z2[i]? = s0.scratch.scratch_buf[i]?) ∧
                              (FullMem c sz2 ⋆ R) mz2)
                            ?_ ?_
                          · rintro Lz2 rem_z2 ⟨k2, ⟨⟩⟩ mz2 hLz2
                              ⟨scr_z2, hscz2, hk2_le, rfl, hout2, hmz2⟩
                            c0_hsplit
                            · have hk2_lt : k2.toNat < 16 := hc
                              have hmk2 : ((mask_off + k2).setWidth 64).toNat < scr_z2.length := by
                                rw [hscz2, m6_zext32_toNat]; c0_bound
                              have hk21 : (k2 + 1#32).toNat = k2.toNat + 1 := by c0_bound
                              c0_hsteps!
                              exact hLz2 (16 - (k2 + 1#32).toNat) (k2 + 1#32, ()) _ (by omega)
                                ⟨scr_z2.set ((mask_off + k2).setWidth 64).toNat 0#32,
                                 by simp [hscz2], by omega, rfl, fun i hi hor => by
                                   rw [List.getElem?_set_ne (by rw [m6_zext32_toNat]; c0_bound)]
                                   exact hout2 i hi hor, hm⟩
                            · c0_hsteps!
                              exact hQ false lm_u scr_z2 mz2
                                (m6_fullDenseInvW_with_scratch hdw_lm
                                  { hdw0.1.scratch_ok with scratch_buf_len := hscz2 } rfl rfl)
                                hout2 hmz2
                          · intro Lz2 hLz2; c0_hsteps!
                            exact hLz2 16 (0#32, ()) mu
                              ⟨scr_j, hscj, Nat.zero_le _, by simp, hout_j, hmu⟩
                    · intro Lu hLu; c0_hsteps!
                      exact hLu sz.toNat (0#32, ()) mj
                        ⟨lm_j, hlmj, Nat.zero_le _, by simp, hsup_j, hmj⟩
                · intro Lj hLj; c0_hsteps!
                  exact hLj nn.toNat (0#32, 0#32, ()) mz
                    ⟨lm1, scr_z, hlm1, hscz, Nat.zero_le _, by simp, hsup1, hout_z, hmz⟩
            · intro Lz hLz; c0_hsteps!
              exact hLz 16 (0#32, ()) m1
                ⟨s0.scratch.scratch_buf, hdw0.1.scratch_ok.scratch_buf_len, Nat.zero_le _, by simp,
                 fun _ _ _ => rfl, hm1⟩)
  · rintro B1 L1 rem1 ⟨need_i, i, ⟨⟩⟩ m1 hB1 hL1 ⟨lm1, hlm1, hi_le, rfl, hsup1, hm1⟩
    c0_hsplit
    · have hi_lt : i.toNat < sz.toNat := hc
      have hcri : (cr.setWidth 64 + 3#64 + i.setWidth 64).toNat < s0.core.arena.length := by
        rw [hdw0.1.core_ok.arena_len_arr]; c0_bound
      let li := s0.core.arena[(cr.setWidth 64 + 3#64 + i.setWidth 64).toNat]'hcri
      have hli_mem : li.toNat ∈ fullArenaClauseLits s0 cr.toNat := by
        change li.toNat ∈ fullArenaClauseLitsCore s0.core cr.toNat
        rw [mem_fullArenaClauseLitsCore_iff (by rw [hdw0.1.core_ok.arena_len_arr]; omega)]
        exact ⟨i.toNat, by omega, congrArg BitVec.toNat (m6_getElem_congr (by c0_bound) _ _)⟩
      have hli_lt : li.toNat < 2 * s0.core.cur_vars :=
        hdw0.2.1.arena.lits_lt cr.toNat href hng _ hli_mem
      have hli_v : (li.setWidth 64).toNat < s0.core.vals.length := by
        rw [hdw0.1.core_ok.vals_len, m6_zext32_toNat]; omega
      have hlin_lm : ((li ^^^ 1#32).setWidth 64).toNat < lm1.length := by
        rw [hlm1, m6_zext32_toNat]; change li.toNat ^^^ 1 < 2 * c.max_vars
        have := fullInv_var_xor1 li.toNat; omega
      have hi1 : (i + 1#32).toNat = i.toNat + 1 := by c0_bound
      c0_hsteps_nogrp
      refine wp_join_state (ts := [i32, .bool]) (α := BitVec 32 × List (BitVec 8))
        (fun x => (x.1, false, ()))
        (fun x mj =>
          x.2.length = 2 * c.max_vars ∧
          (∀ y < 2 * c.max_vars, x.2[y]?.getD 0#8 ≠ 0#8 →
            (y ^^^ 1) ∈ fullArenaClauseLits s0 cr.toNat) ∧
          (FullMem c { s0 with core := { s0.core with lit_mark := x.2 } } ⋆ R) mj)
        (fun _ ⟨nd', lm'⟩ mj ⟨hlm', hsup', hmj⟩ => by
          c0_hsteps!
          exact hL1 (sz.toNat - (i + 1#32).toNat) (nd', i + 1#32, ()) mj (by omega)
            ⟨lm', hlm', by omega, rfl, hsup', hmj⟩)
        (fun J1 hJ1 => by
          c0_hsplit
          · c0_hsplit
            · c0_hsteps!; exact hB1 (need_i, true, i, ()) m1 ⟨lm1, hlm1, hsup1, hm1⟩
            · c0_hsteps_nogrp
              refine wp_join_state (ts := [i32]) (α := BitVec 32 × List (BitVec 8))
                (fun x => (x.1, ()))
                (fun x mj =>
                  x.2.length = 2 * c.max_vars ∧
                  (∀ y < 2 * c.max_vars, x.2[y]?.getD 0#8 ≠ 0#8 →
                    (y ^^^ 1) ∈ fullArenaClauseLits s0 cr.toNat) ∧
                  (FullMem c { s0 with core := { s0.core with lit_mark := x.2 } } ⋆ R) mj)
                (fun _ p mj h => by c0_hsteps!; exact hJ1 p mj h)
                (fun J40 hJ40 => by
                  c0_hsplit
                  · c0_hsteps!
                    exact hJ40 (need_i + 1#32, lm1.set ((li ^^^ 1#32).setWidth 64).toNat 1#8) _
                      ⟨by simp [hlm1], fun y hy hnz => by
                        rw [m6_zext32_toNat] at hnz
                        by_cases hye : y = (li ^^^ 1#32).toNat
                        · subst hye; change (li.toNat ^^^ 1) ^^^ 1 ∈ _
                          rw [Nat.xor_assoc]; simpa using hli_mem
                        · rw [List.getElem?_set_ne (Ne.symm hye)] at hnz; exact hsup1 y hy hnz, hm⟩
                  · c0_hsteps!; exact hJ40 (need_i, lm1) m1 ⟨hlm1, hsup1, hm1⟩)
          · c0_hsteps!; exact hJ1 (need_i, lm1) m1 ⟨hlm1, hsup1, hm1⟩)
    · c0_hsteps!; exact hB1 (need_i, false, i, ()) m1 ⟨lm1, hlm1, hsup1, hm1⟩
  · intro _ L1 _ hL1; c0_hsteps!
    exact hL1 sz.toNat (0#32, 0#32, ()) m0
      ⟨s0.core.lit_mark, hdw0.1.core_ok.lit_mark_len, Nat.zero_le _, by simp,
       fun x hx hnz => absurd (hdw0.2.2.1.2 x hx) hnz, hm0⟩

/-- Contract for `full_bve_get_tern_m6`: extracts 2 unassigned non-`v_lit` literals of live clause
`cr` into `scr[out_off..+2)` when `cr` reduces to a ternary clause on `v_lit`. -/
def fullBveGetTernM6Spec : Spec [i64, i32, i32, i32] [.bool] :=
  fun (h, _v_lit, cr, out_off, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧
      cr.toNat ∈ fullArenaClauseRefs s ∧ fullArenaClauseGarb s cr.toNat = false ∧
      out_off.toNat + 2 ≤ c.scratch_cap ∧ (FullMem c s ⋆ R) m ∧
      ∀ (ok : Bool) scr' m',
        let s' : FullState := { s with scratch := { s.scratch with scratch_buf := scr' } }
        scr'.length = c.scratch_cap →
        (∀ i < c.scratch_cap, (i < out_off.toNat ∨ out_off.toNat + 2 ≤ i) →
          scr'[i]? = s.scratch.scratch_buf[i]?) →
        (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

theorem fullBveGetTernM6Spec_noExit :
    ∀ xs m Q X, fullBveGetTernM6Spec xs m Q X →
      fullBveGetTernM6Spec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => h

/-- Parametric `Func.wp` proof for `full_bve_get_tern_m6`. -/
theorem full_bve_get_tern_m6_wp (Γ : Env) :
    ∀ a m Q X, fullBveGetTernM6Spec a m Q X →
      Func.wp Γ full_bve_get_tern_m6_body a m Q X := by
  rintro ⟨h, v_lit, cr, out_off, ⟨⟩⟩ m0 Q X
    ⟨c, F0, F_cur, s0, R, rfl, hdw0, href, hng, hout, hm0, hQ⟩
  have hmx := c.hmaxv; have harc := c.harena; have hsc := c.hscr
  unfold dimacsBound at hmx harc hsc
  have hwf := hdw0.2.1.arena.refs_wf cr.toNat href
  have hal_le := hdw0.1.core_ok.arena_len_le
  have hcv_le := hdw0.1.core_ok.cur_vars_le
  have hcr2_ar : (cr.setWidth 64 + 2#64).toNat < s0.core.arena.length := by
    rw [hdw0.1.core_ok.arena_len_arr]; c0_bound
  let sz := s0.core.arena[(cr.setWidth 64 + 2#64).toNat]'hcr2_ar
  have hsz_eq : sz.toNat = fullArenaClauseSizeCore s0.core cr.toNat := by
    unfold sz fullArenaClauseSizeCore
    rw [List.getElem?_eq_getElem (by rw [hdw0.1.core_ok.arena_len_arr]; omega), Option.getD_some]
    exact congrArg BitVec.toNat (m6_getElem_congr (by c0_bound) _ _)
  unfold Func.wp full_bve_get_tern_m6_body
  c0_hsteps_nogrp
  refine wp_loop_group (ts := [i32, i32, i32, i32])
    (fun rem (cnt, l0, l1, i, ()) mi =>
      mi = m0 ∧ i.toNat ≤ sz.toNat ∧ rem = sz.toNat - i.toNat)
    ?_ ?_
  · rintro L rem ⟨cnt, l0, l1, i, ⟨⟩⟩ mi hL ⟨hm_eq, hi_le, rfl⟩
    subst mi
    c0_hsplit
    · have hi_lt : i.toNat < sz.toNat := hc
      have hcri : (cr.setWidth 64 + 3#64 + i.setWidth 64).toNat < s0.core.arena.length := by
        rw [hdw0.1.core_ok.arena_len_arr]; c0_bound
      let li := s0.core.arena[(cr.setWidth 64 + 3#64 + i.setWidth 64).toNat]'hcri
      have hli_lt : li.toNat < 2 * s0.core.cur_vars := by
        have hmem : li.toNat ∈ fullArenaClauseLitsCore s0.core cr.toNat := by
          rw [mem_fullArenaClauseLitsCore_iff (by rw [hdw0.1.core_ok.arena_len_arr]; omega)]
          exact ⟨i.toNat, by omega, congrArg BitVec.toNat (m6_getElem_congr (by c0_bound) _ _)⟩
        exact hdw0.2.1.arena.lits_lt cr.toNat href hng _ hmem
      have hli_v : (li.setWidth 64).toNat < s0.core.vals.length := by
        rw [hdw0.1.core_ok.vals_len, m6_zext32_toNat]; omega
      have hi1 : (i + 1#32).toNat = i.toNat + 1 := by c0_bound
      c0_hsteps_nogrp
      refine wp_join_state_pure (ts := [i32, i32, i32]) (α := BitVec 32 × BitVec 32 × BitVec 32)
        (fun x => (x.1, x.2.1, x.2.2, ())) (fun _ => True)
        (fun _ ⟨c', a', b'⟩ _ => by
          c0_hsteps!
          exact hL (sz.toNat - (i + 1#32).toNat) (c', a', b', i + 1#32, ()) m0 (by omega)
            ⟨rfl, by omega, rfl⟩)
        (fun J hJ => by
          c0_hsplit
          · c0_hsplit
            · c0_hsteps!
              exact hQ false s0.scratch.scratch_buf m0 hdw0.1.scratch_ok.scratch_buf_len
                (fun _ _ _ => rfl) hm0
            · c0_hsteps_nogrp
              refine wp_join_state_pure (ts := [i32, i32, i32])
                (α := BitVec 32 × BitVec 32 × BitVec 32)
                (fun x => (x.1, x.2.1, x.2.2, ())) (fun _ => True)
                (fun _ x _ => by c0_hsteps!; exact hJ x trivial)
                (fun J37 hJ37 => by
                  c0_hsplit
                  · c0_hsteps_nogrp
                    refine wp_join_state_pure (ts := [i32, i32]) (α := BitVec 32 × BitVec 32)
                      (fun p => (p.1, p.2, ())) (fun _ => True)
                      (fun _ ⟨a', b'⟩ _ => by
                        c0_hsteps!; exact hJ37 (cnt + 1#32, a', b') trivial)
                      (fun J42 hJ42 => by
                        c0_hsplit
                        · c0_hsteps!; exact hJ42 (li, l1) trivial
                        · c0_hsplit
                          · c0_hsteps!; exact hJ42 (l0, li) trivial
                          · c0_hsteps!
                            exact hQ false s0.scratch.scratch_buf m0
                              hdw0.1.scratch_ok.scratch_buf_len (fun _ _ _ => rfl) hm0)
                  · c0_hsteps!; exact hJ37 (cnt, l0, l1) trivial)
          · c0_hsteps!; exact hJ (cnt, l0, l1) trivial)
    · c0_hsplit
      · c0_hsteps!
        exact hQ false s0.scratch.scratch_buf m0 hdw0.1.scratch_ok.scratch_buf_len
          (fun _ _ _ => rfl) hm0
      · have ho0 : (out_off.setWidth 64).toNat < s0.scratch.scratch_buf.length := by
          rw [hdw0.1.scratch_ok.scratch_buf_len, m6_zext32_toNat]; omega
        have ho1 : ((out_off + 1#32).setWidth 64).toNat < s0.scratch.scratch_buf.length := by
          rw [hdw0.1.scratch_ok.scratch_buf_len, m6_zext32_toNat]; c0_bound
        c0_hsteps!
        exact hQ true _ _ (by simp [hdw0.1.scratch_ok.scratch_buf_len])
          (fun i hi hor => by
            rw [List.getElem?_set_ne (by rw [m6_zext32_toNat]; c0_bound),
              List.getElem?_set_ne (by rw [m6_zext32_toNat]; omega)]) hm
  · intro L hL; c0_hsteps!
    exact hL sz.toNat (0#32, 0#32, 0#32, 0#32, ()) m0 ⟨rfl, Nat.zero_le _, by simp⟩

/-- Contract for `full_bve_match_tern_m6`: searches `scr[n_off ..< n_off + nn)` for a matching
shortened binary or ternary clause for ITE gate extraction (`scr[1064..1065]` scratch). -/
def fullBveMatchTernM6Spec : Spec [i64, i32, i32, i32, i32, i32] [i32] :=
  fun (h, nl, _x, _y, n_off, nn, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ 1066 ≤ c.scratch_cap ∧
      n_off.toNat + nn.toNat ≤ 1024 ∧ nn.toNat ≤ 512 ∧
      (∀ j < nn.toNat, FullBveEntryOkW F_cur s nl.toNat
        (s.scratch.scratch_buf[n_off.toNat + j]?.getD 0#32)) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (r : BitVec 32) scr' m',
        let s' : FullState := { s with scratch := { s.scratch with scratch_buf := scr' } }
        scr'.length = c.scratch_cap →
        (∀ i < c.scratch_cap, (i < 1064 ∨ 1066 ≤ i) →
          scr'[i]? = s.scratch.scratch_buf[i]?) →
        (r = 0xFFFFFFFF#32 ∨ (r &&& 0x7FFFFFFF#32).toNat < nn.toNat) →
        (FullMem c s' ⋆ R) m' → Q (r, ()) m'

theorem fullBveMatchTernM6Spec_noExit :
    ∀ xs m Q X, fullBveMatchTernM6Spec xs m Q X →
      fullBveMatchTernM6Spec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => h

/-- Parametric `Func.wp` proof for `full_bve_match_tern_m6`. -/
theorem full_bve_match_tern_m6_wp (Γ : Env)
    (hGetTern : ∀ a m Q X, fullBveGetTernM6Spec a m Q X →
      Γ "full_bve_get_tern_m6" [i64, i32, i32, i32] [.bool] a m Q X) :
    ∀ a m Q X, fullBveMatchTernM6Spec a m Q X →
      Func.wp Γ full_bve_match_tern_m6_body a m Q X := by
  rintro ⟨h, nl, x, y, n_off, nn, ⟨⟩⟩ m0 Q X
    ⟨c, F0, F_cur, s0, R, rfl, hdw0, hsc1066, hnoff, hnn512, hent_n, hm0, hQ⟩
  have hsc := c.hscr; unfold dimacsBound at hsc
  unfold Func.wp full_bve_match_tern_m6_body
  c0_hsteps_nogrp
  refine wp_loop_group (ts := [i32])
    (fun rem (j, ()) mj => ∃ scr_j : List (BitVec 32),
      let sj : FullState := { s0 with scratch := { s0.scratch with scratch_buf := scr_j } }
      scr_j.length = c.scratch_cap ∧ j.toNat ≤ nn.toNat ∧ rem = nn.toNat - j.toNat ∧
      (∀ i < c.scratch_cap, (i < 1064 ∨ 1066 ≤ i) →
        scr_j[i]? = s0.scratch.scratch_buf[i]?) ∧
      (FullMem c sj ⋆ R) mj)
    ?_ ?_
  · rintro L rem ⟨j, ⟨⟩⟩ mj hL ⟨scr_j, hscj, hj_le, rfl, hout_j, hmj⟩
    let sj : FullState := { s0 with scratch := { s0.scratch with scratch_buf := scr_j } }
    c0_hsplit
    · have hj_lt : j.toNat < nn.toNat := hc
      have hnj_sc : ((n_off + j).setWidth 64).toNat < scr_j.length := by
        rw [hscj, m6_zext32_toNat]; c0_bound
      have hj1 : (j + 1#32).toNat = j.toNat + 1 := by c0_bound
      let wj := scr_j[((n_off + j).setWidth 64).toNat]'hnj_sc
      have hwj_orig : wj = s0.scratch.scratch_buf[n_off.toNat + j.toNat]?.getD 0#32 := by
        have hnj_eq : ((n_off + j).setWidth 64).toNat = n_off.toNat + j.toNat := by
          rw [m6_zext32_toNat]; c0_bound
        have hget := hout_j (n_off.toNat + j.toNat) (by omega) (Or.inl (by omega))
        have hnj' : n_off.toNat + j.toNat < scr_j.length := by omega
        rw [List.getElem?_eq_getElem hnj'] at hget
        rw [← hget, Option.getD_some]
        exact m6_getElem_congr hnj_eq hnj_sc hnj'
      c0_hsteps_nogrp
      refine wp_join_state (ts := []) (α := List (BitVec 32)) (fun _ => ())
        (fun scr_n mn => scr_n.length = c.scratch_cap ∧
          (∀ i < c.scratch_cap, (i < 1064 ∨ 1066 ≤ i) →
            scr_n[i]? = s0.scratch.scratch_buf[i]?) ∧
          (FullMem c { s0 with scratch := { s0.scratch with scratch_buf := scr_n } } ⋆ R) mn)
        (fun _ scr_n mn ⟨hsc_n, hout_n, hm_n⟩ => by
          c0_hsteps!
          exact hL (nn.toNat - (j + 1#32).toNat) (j + 1#32, ()) mn (by omega)
            ⟨scr_n, hsc_n, by omega, rfl, hout_n, hm_n⟩)
        (fun Jm hJm => by
          c0_hsplit
          · have hj_mask : ((j ||| 0x80000000#32) &&& 0x7FFFFFFF#32) = j := by
              apply BitVec.eq_of_toNat_eq
              have h1 : ((j ||| 0x80000000#32) &&& 0x7FFFFFFF#32) = (j &&& 0x7FFFFFFF#32) := by
                ext i hi; simp only [BitVec.getElem_and, BitVec.getElem_or]
                have h0 : ((0x80000000#32 &&& 0x7FFFFFFF#32) : BitVec 32)[i] = false := by
                  have : (0x80000000#32 &&& 0x7FFFFFFF#32) = 0#32 := by decide
                  rw [this]; simp
                simp only [BitVec.getElem_and] at h0
                rw [Bool.and_or_distrib_right, h0, Bool.or_false]
              rw [h1, BitVec.toNat_and,
                show (0x7FFFFFFF#32 : BitVec 32).toNat = 2 ^ 31 - 1 by decide,
                Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (by omega)]
            c0_hsteps_nogrp
            refine wp_join0 (P := fun mt => mt = mj)
              (fun _ mt hmt => by
                subst mt
                c0_hsteps!; exact hQ (j ||| 0x80000000#32) scr_j mj hscj hout_j
                  (Or.inr (by rw [hj_mask]; exact hj_lt)) hmj)
              (fun J20 hJ20 => by
                c0_hsplit
                · c0_hsteps!; exact hJ20 mj rfl
                · c0_hsplit
                  · c0_hsteps!; exact hJ20 mj rfl
                  · c0_hsteps!; exact hJm scr_j mj ⟨hscj, hout_j, hmj⟩)
          · c0_hsteps_nogrp
            refine wp_join_state (ts := []) (α := List (BitVec 32)) (fun _ => ())
              (fun scr_n mn => scr_n.length = c.scratch_cap ∧
                (∀ i < c.scratch_cap, (i < 1064 ∨ 1066 ≤ i) →
                  scr_n[i]? = s0.scratch.scratch_buf[i]?) ∧
                (FullMem c { s0 with scratch := { s0.scratch with scratch_buf := scr_n } } ⋆ R) mn)
              (fun _ scr_n mn ⟨hsc_n, hout_n, hm_n⟩ => by
                c0_hsteps!; exact hJm scr_n mn ⟨hsc_n, hout_n, hm_n⟩)
              (fun J19 hJ19 => by
                have hent_j := hent_n j.toNat hj_lt
                rw [← hwj_orig] at hent_j
                unfold FullBveEntryOkW at hent_j
                rw [ite_eq_right (fun h => h hc)] at hent_j
                have hdw_j : FullDenseInvW c F0 F_cur sj :=
                  m6_fullDenseInvW_with_scratch hdw0
                    { hdw0.1.scratch_ok with scratch_buf_len := hscj } rfl rfl
                c0_hsteps_nogrp
                m6_call hGetTern
                refine ⟨c, F0, F_cur, sj, R, rfl, hdw_j, hent_j.1, hent_j.2, by simp; omega,
                  hmj, ?_⟩
                intro ok scr_k m_k s_k hsc_k hout_k hm_k
                have hout_k' : ∀ i < c.scratch_cap, (i < 1064 ∨ 1066 ≤ i) →
                    scr_k[i]? = s0.scratch.scratch_buf[i]? := fun i hi hor =>
                  (hout_k i hi hor).trans (hout_j i hi hor)
                c0_hsplit
                · have h1064 : 1064 < scr_k.length := by omega
                  have h1065 : 1065 < scr_k.length := by omega
                  have hj_mask : (j &&& 0x7FFFFFFF#32).toNat = j.toNat := by
                    rw [BitVec.toNat_and,
                      show (0x7FFFFFFF#32 : BitVec 32).toNat = 2 ^ 31 - 1 by decide,
                      Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (by omega)]
                  c0_hsteps_nogrp
                  refine wp_join0 (P := fun mt => mt = m_k)
                    (fun _ mt hmt => by
                      subst mt
                      c0_hsplit
                      · c0_hsplit
                        · c0_hsteps!; exact hQ j scr_k m_k hsc_k hout_k'
                            (Or.inr (by rw [hj_mask]; exact hj_lt)) hm_k
                        · c0_hsteps!; exact hJ19 scr_k m_k ⟨hsc_k, hout_k', hm_k⟩
                      · c0_hsteps!; exact hJ19 scr_k m_k ⟨hsc_k, hout_k', hm_k⟩)
                    (fun J29 hJ29 => by
                      c0_hsplit
                      · c0_hsplit
                        · c0_hsteps!; exact hQ j scr_k m_k hsc_k hout_k'
                            (Or.inr (by rw [hj_mask]; exact hj_lt)) hm_k
                        · c0_hsteps!; exact hJ29 m_k rfl
                      · c0_hsteps!; exact hJ29 m_k rfl)
                · c0_hsteps!; exact hJ19 scr_k m_k ⟨hsc_k, hout_k', hm_k⟩))
    · c0_hsteps!; exact hQ 0xFFFFFFFF#32 scr_j mj hscj hout_j (Or.inl rfl) hmj
  · intro L hL; c0_hsteps!
    exact hL nn.toNat (0#32, ()) m0
      ⟨s0.scratch.scratch_buf, hdw0.1.scratch_ok.scratch_buf_len, Nat.zero_le _, by simp,
       fun _ _ _ => rfl, hm0⟩

/-- Contract for `full_bve_find_ite_m6`: structural `ifthenelse` gate extraction preserving
`scr[0 ..< 1024)` and writing only `scr[1024 ..< 1066)`. -/
def fullBveFindIteM6Spec : Spec [i64, i32, i32, i32] [.bool] := fun (h, v, np, nn, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ 1066 ≤ c.scratch_cap ∧
    v.toNat < s.core.cur_vars ∧ np.toNat ≤ 512 ∧ nn.toNat ≤ 512 ∧
    (∀ i < np.toNat, FullBveEntryOkW F_cur s (2 * v.toNat)
      (s.scratch.scratch_buf[i]?.getD 0#32)) ∧
    (∀ j < nn.toNat, FullBveEntryOkW F_cur s (2 * v.toNat + 1)
      (s.scratch.scratch_buf[512 + j]?.getD 0#32)) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ (ok : Bool) scr' m',
      let s' : FullState := { s with scratch := { s.scratch with scratch_buf := scr' } }
      scr'.length = c.scratch_cap →
      (∀ i < c.scratch_cap, (i < 1024 ∨ 1066 ≤ i) →
        scr'[i]? = s.scratch.scratch_buf[i]?) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

theorem fullBveFindIteM6Spec_noExit :
    ∀ xs m Q X, fullBveFindIteM6Spec xs m Q X →
      fullBveFindIteM6Spec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => h

/-- Parametric `Func.wp` proof for `full_bve_find_ite_m6`. -/
theorem full_bve_find_ite_m6_wp (Γ : Env)
    (hGetTern : ∀ a m Q X, fullBveGetTernM6Spec a m Q X →
      Γ "full_bve_get_tern_m6" [i64, i32, i32, i32] [.bool] a m Q X)
    (hMatchTern : ∀ a m Q X, fullBveMatchTernM6Spec a m Q X →
      Γ "full_bve_match_tern_m6" [i64, i32, i32, i32, i32, i32] [i32] a m Q X) :
    ∀ a m Q X, fullBveFindIteM6Spec a m Q X →
      Func.wp Γ full_bve_find_ite_m6_body a m Q X := by
  rintro ⟨h, v, np, nn, ⟨⟩⟩ m0 Q X
    ⟨c, F0, F_cur, s0, R, rfl, hdw0, hsc1066, hv_lt, hnp512, hnn512, hent_p, hent_n, hm0, hQ⟩
  have hmx := c.hmaxv; have hsc := c.hscr; unfold dimacsBound at hmx hsc
  have hcv_le := hdw0.1.core_ok.cur_vars_le
  have hplnl := m6_pl_nl_eq v (by omega)
  unfold Func.wp full_bve_find_ite_m6_body
  c0_hsteps_nogrp
  refine wp_join_state_pure (ts := [i32]) (α := BitVec 32) (fun plim => (plim, ()))
    (fun plim => plim.toNat ≤ np.toNat ∧ plim.toNat ≤ 64)
    (fun _ plim ⟨hpl_np, hpl_64⟩ => by
      c0_hsteps_nogrp
      refine wp_loop_group (ts := [i32])
        (fun rem0 (i0, ()) m1 => ∃ scr1 : List (BitVec 32),
          let s1 : FullState := { s0 with scratch := { s0.scratch with scratch_buf := scr1 } }
          scr1.length = c.scratch_cap ∧ i0.toNat ≤ plim.toNat ∧ rem0 = plim.toNat - i0.toNat ∧
          (∀ i < c.scratch_cap, (i < 1024 ∨ 1066 ≤ i) →
            scr1[i]? = s0.scratch.scratch_buf[i]?) ∧
          (FullMem c s1 ⋆ R) m1)
        ?_ ?_
      · rintro L0 rem0 ⟨i0, ⟨⟩⟩ m1 hL0 ⟨scr1, hsc1, hi0_le, rfl, hout1, hm1⟩
        let s1 : FullState := { s0 with scratch := { s0.scratch with scratch_buf := scr1 } }
        c0_hsplit
        · have hi0_lt : i0.toNat < plim.toNat := hc
          have hi0_sc : (i0.setWidth 64).toNat < scr1.length := by
            rw [hsc1, m6_zext32_toNat]; omega
          have hi01 : (i0 + 1#32).toNat = i0.toNat + 1 := by c0_bound
          let w0 := scr1[(i0.setWidth 64).toNat]'hi0_sc
          have hw0_orig : w0 = s0.scratch.scratch_buf[i0.toNat]?.getD 0#32 := by
            have hget := hout1 i0.toNat (by omega) (Or.inl (by omega))
            have hi0' : i0.toNat < scr1.length := by omega
            rw [List.getElem?_eq_getElem hi0'] at hget
            rw [← hget, Option.getD_some]
            exact m6_getElem_congr (m6_zext32_toNat i0) hi0_sc hi0'
          c0_hsteps_nogrp
          refine wp_join_state (ts := []) (α := List (BitVec 32)) (fun _ => ())
            (fun scr_j mj => scr_j.length = c.scratch_cap ∧
              (∀ i < c.scratch_cap, (i < 1024 ∨ 1066 ≤ i) →
                scr_j[i]? = s0.scratch.scratch_buf[i]?) ∧
              (FullMem c { s0 with scratch := { s0.scratch with scratch_buf := scr_j } } ⋆ R) mj)
            (fun _ scr_j mj ⟨hsc_j, hout_j, hm_j⟩ => by
              c0_hsteps!
              exact hL0 (plim.toNat - (i0 + 1#32).toNat) (i0 + 1#32, ()) mj (by omega)
                ⟨scr_j, hsc_j, by omega, rfl, hout_j, hm_j⟩)
            (fun J0 hJ0 => by
              c0_hsplit
              · have hent_0 := hent_p i0.toNat (by omega)
                rw [← hw0_orig] at hent_0; unfold FullBveEntryOkW at hent_0
                rw [ite_eq_right (fun h => h hc)] at hent_0
                have hdw1 : FullDenseInvW c F0 F_cur s1 :=
                  m6_fullDenseInvW_with_scratch hdw0
                    { hdw0.1.scratch_ok with scratch_buf_len := hsc1 } rfl rfl
                c0_hsteps_nogrp
                m6_call hGetTern
                refine ⟨c, F0, F_cur, s1, R, rfl, hdw1, hent_0.1, hent_0.2, by simp; omega, hm1, ?_⟩
                intro ok0 scr2 m2 s2 hsc2 hout2 hm2
                have hout2' : ∀ i < c.scratch_cap, (i < 1024 ∨ 1066 ≤ i) →
                    scr2[i]? = s0.scratch.scratch_buf[i]? := fun i hi hor =>
                  (hout2 i hi (by rcases hor with h | h <;> simp <;> omega)).trans (hout1 i hi hor)
                c0_hsplit
                · have h1060 : 1060 < scr2.length := by omega
                  have h1061 : 1061 < scr2.length := by omega
                  c0_hsteps_nogrp
                  refine wp_loop_group (ts := [i32])
                    (fun rem1 (i1, ()) m3 => ∃ scr3 : List (BitVec 32),
                      let s3 : FullState :=
                        { s0 with scratch := { s0.scratch with scratch_buf := scr3 } }
                      scr3.length = c.scratch_cap ∧ i1.toNat ≤ plim.toNat ∧
                      rem1 = plim.toNat - i1.toNat ∧
                      (∀ i < c.scratch_cap, (i < 1024 ∨ 1066 ≤ i) →
                        scr3[i]? = s0.scratch.scratch_buf[i]?) ∧
                      (FullMem c s3 ⋆ R) m3)
                    ?_ ?_
                  · rintro L1 rem1 ⟨i1, ⟨⟩⟩ m3 hL1 ⟨scr3, hsc3, hi1_le, rfl, hout3, hm3⟩
                    let s3 : FullState :=
                      { s0 with scratch := { s0.scratch with scratch_buf := scr3 } }
                    c0_hsplit
                    · have hi1_lt : i1.toNat < plim.toNat := hc
                      have hi1_sc : (i1.setWidth 64).toNat < scr3.length := by
                        rw [hsc3, m6_zext32_toNat]; omega
                      have hi11 : (i1 + 1#32).toNat = i1.toNat + 1 := by c0_bound
                      let w1 := scr3[(i1.setWidth 64).toNat]'hi1_sc
                      have hw1_orig : w1 = s0.scratch.scratch_buf[i1.toNat]?.getD 0#32 := by
                        have hget := hout3 i1.toNat (by omega) (Or.inl (by omega))
                        have hi1' : i1.toNat < scr3.length := by omega
                        rw [List.getElem?_eq_getElem hi1'] at hget
                        rw [← hget, Option.getD_some]
                        exact m6_getElem_congr (m6_zext32_toNat i1) hi1_sc hi1'
                      c0_hsteps_nogrp
                      refine wp_join_state (ts := []) (α := List (BitVec 32)) (fun _ => ())
                        (fun scr_k mk => scr_k.length = c.scratch_cap ∧
                          (∀ i < c.scratch_cap, (i < 1024 ∨ 1066 ≤ i) →
                            scr_k[i]? = s0.scratch.scratch_buf[i]?) ∧
                          (FullMem c { s0 with scratch := { s0.scratch with
                            scratch_buf := scr_k } } ⋆ R) mk)
                        (fun _ scr_k mk ⟨hsc_k, hout_k, hm_k⟩ => by
                          c0_hsteps!
                          exact hL1 (plim.toNat - (i1 + 1#32).toNat) (i1 + 1#32, ()) mk (by omega)
                            ⟨scr_k, hsc_k, by omega, rfl, hout_k, hm_k⟩)
                        (fun J1 hJ1 => by
                          c0_hsplit
                          · have hent_1 := hent_p i1.toNat (by omega)
                            rw [← hw1_orig] at hent_1; unfold FullBveEntryOkW at hent_1
                            rw [ite_eq_right (fun h => h hc)] at hent_1
                            have hdw3 : FullDenseInvW c F0 F_cur s3 :=
                              m6_fullDenseInvW_with_scratch hdw0
                                { hdw0.1.scratch_ok with scratch_buf_len := hsc3 } rfl rfl
                            c0_hsteps_nogrp
                            m6_call hGetTern
                            refine ⟨c, F0, F_cur, s3, R, rfl, hdw3, hent_1.1, hent_1.2,
                              by simp; omega, hm3, ?_⟩
                            intro ok1 scr4 m4 s4 hsc4 hout4 hm4
                            have hout4' : ∀ i < c.scratch_cap, (i < 1024 ∨ 1066 ≤ i) →
                                scr4[i]? = s0.scratch.scratch_buf[i]? := fun i hi hor =>
                              (hout4 i hi (by rcases hor with h | h <;> simp <;> omega)).trans
                                (hout3 i hi hor)
                            c0_hsplit
                            · have h1062 : 1062 < scr4.length := by omega
                              have h1063 : 1063 < scr4.length := by omega
                              -- 4-way if/else-if chain computing `(ok, cond, u, w)`
                              c0_hsteps_nogrp
                              refine wp_join_state_pure (ts := [.bool, i32, i32, i32])
                                (α := Bool × BitVec 32 × BitVec 32 × BitVec 32)
                                (fun t => (t.1, t.2.1, t.2.2.1, t.2.2.2, ()))
                                (fun _ => True)
                                (fun _ ⟨ok_m, cond, u, w⟩ _ => by
                                  c0_hsteps_nogrp
                                  refine wp_join_state (ts := []) (α := List (BitVec 32))
                                    (fun _ => ())
                                    (fun scr_k mk => scr_k.length = c.scratch_cap ∧
                                      (∀ i < c.scratch_cap, (i < 1024 ∨ 1066 ≤ i) →
                                        scr_k[i]? = s0.scratch.scratch_buf[i]?) ∧
                                      (FullMem c { s0 with scratch := { s0.scratch with
                                        scratch_buf := scr_k } } ⋆ R) mk)
                                    (fun _ scr_k mk ⟨hsc_k, hout_k, hm_k⟩ => by
                                      c0_hsteps!; exact hJ1 scr_k mk ⟨hsc_k, hout_k, hm_k⟩)
                                    (fun J54 hJ54 => by
                                      c0_hsplit
                                      · c0_hsplit
                                        · c0_hsplit
                                          · let s4' : FullState := { s0 with scratch :=
                                              { s0.scratch with scratch_buf := scr4 } }
                                            have hdw4 : FullDenseInvW c F0 F_cur s4' :=
                                              m6_fullDenseInvW_with_scratch hdw0
                                                { hdw0.1.scratch_ok with scratch_buf_len := hsc4 }
                                                rfl rfl
                                            c0_hsteps_nogrp
                                            m6_call hMatchTern
                                            dsimp only [vals, Arg.val]
                                            refine ⟨c, F0, F_cur, s4', R, rfl, hdw4, hsc1066,
                                              by simp; omega, hnn512, fun j hj => by
                                                dsimp only [s4']
                                                rw [show (512 : BitVec 32).toNat = 512 from rfl,
                                                  hout4' (512 + j) (by omega) (Or.inl (by omega)),
                                                  show ((v <<< 1 : BitVec 32) ||| 1) =
                                                    (v <<< (1 : Nat)) ||| 1#32 from rfl, hplnl.2]
                                                exact m6_bveEntry_mono_scratch (hent_n j hj),
                                              hm4, ?_⟩
                                            intro m0_r scr5 m5 s5 hsc5 hout5 hm0_ok hm5
                                            dsimp only [s5] at hm5
                                            have hout5' :
                                                ∀ i < c.scratch_cap, (i < 1024 ∨ 1066 ≤ i) →
                                                scr5[i]? = s0.scratch.scratch_buf[i]? :=
                                              fun i hi hor =>
                                                (hout5 i hi (by
                                                  rcases hor with h | h <;> omega)).trans
                                                  (hout4' i hi hor)
                                            c0_hsteps_nogrp
                                            refine wp_join_state (ts := []) (α := List (BitVec 32))
                                              (fun _ => ())
                                              (fun scr_k mk => scr_k.length = c.scratch_cap ∧
                                                (∀ i < c.scratch_cap, (i < 1024 ∨ 1066 ≤ i) →
                                                  scr_k[i]? = s0.scratch.scratch_buf[i]?) ∧
                                                (FullMem c { s0 with scratch := { s0.scratch with
                                                  scratch_buf := scr_k } } ⋆ R) mk)
                                              (fun _ scr_k mk ⟨hsc_k, hout_k, hm_k⟩ => by
                                                c0_hsteps!
                                                exact hJ54 scr_k mk ⟨hsc_k, hout_k, hm_k⟩)
                                              (fun J60 hJ60 => by
                                                c0_hsplit
                                                · have hj0_lt :
                                                      (m0_r &&& 0x7FFFFFFF#32).toNat <
                                                      nn.toNat := hm0_ok.resolve_left hc
                                                  let s5' : FullState := { s0 with scratch :=
                                                    { s0.scratch with scratch_buf := scr5 } }
                                                  have hdw5 : FullDenseInvW c F0 F_cur s5' :=
                                                    m6_fullDenseInvW_with_scratch hdw0
                                                      { hdw0.1.scratch_ok with
                                                        scratch_buf_len := hsc5 } rfl rfl
                                                  c0_hsteps_nogrp
                                                  m6_call hMatchTern
                                                  dsimp only [vals, Arg.val]
                                                  refine ⟨c, F0, F_cur, s5', R, rfl, hdw5, hsc1066,
                                                    by simp; omega, hnn512, fun j hj => by
                                                      dsimp only [s5']
                                                      rw [show (512 : BitVec 32).toNat = 512
                                                          from rfl,
                                                        hout5' (512 + j) (by omega)
                                                          (Or.inl (by omega)),
                                                        show ((v <<< 1 : BitVec 32) ||| 1) =
                                                          (v <<< (1 : Nat)) ||| 1#32 from rfl,
                                                        hplnl.2]
                                                      exact m6_bveEntry_mono_scratch (hent_n j hj),
                                                    hm5, ?_⟩
                                                  intro m1_r scr6 m6 s6 hsc6 hout6 hm1_ok hm6
                                                  dsimp only [s6] at hm6
                                                  have hout6' : ∀ i < c.scratch_cap,
                                                      (i < 1024 ∨ 1066 ≤ i) →
                                                      scr6[i]? = s0.scratch.scratch_buf[i]? :=
                                                    fun i hi hor =>
                                                      (hout6 i hi
                                                        (by rcases hor with h | h <;> omega)).trans
                                                        (hout5' i hi hor)
                                                  c0_hsteps_nogrp
                                                  refine wp_join_state (ts := [])
                                                    (α := List (BitVec 32)) (fun _ => ())
                                                    (fun scr_k mk => scr_k.length = c.scratch_cap ∧
                                                      (∀ i < c.scratch_cap,
                                                        (i < 1024 ∨ 1066 ≤ i) →
                                                        scr_k[i]? = s0.scratch.scratch_buf[i]?) ∧
                                                      (FullMem c { s0 with scratch :=
                                                        { s0.scratch with scratch_buf := scr_k } } ⋆
                                                        R) mk)
                                                    (fun _ scr_k mk ⟨hsc_k, hout_k, hm_k⟩ => by
                                                      c0_hsteps!
                                                      exact hJ60 scr_k mk ⟨hsc_k, hout_k, hm_k⟩)
                                                    (fun J65 hJ65 => by
                                                      c0_hsplit
                                                      · have hj1_lt :
                                                            (m1_r &&& 0x7FFFFFFF#32).toNat <
                                                            nn.toNat := hm1_ok.resolve_left hc
                                                        c0_hsplit
                                                        · have hi0_idx : ((1024#32 + (i0 >>>
                                                              (5 : Nat))).setWidth 64).toNat =
                                                              1024 + i0.toNat / 32 := by
                                                            rw [m6_zext32_toNat, BitVec.toNat_add,
                                                              BitVec.toNat_ushiftRight,
                                                              Nat.shiftRight_eq_div_pow]
                                                            simp only [BitVec.toNat_ofNat,
                                                              Nat.reducePow]
                                                            rw [Nat.mod_eq_of_lt (by omega)]
                                                          have hi1_idx : ((1024#32 + (i1 >>>
                                                              (5 : Nat))).setWidth 64).toNat =
                                                              1024 + i1.toNat / 32 := by
                                                            rw [m6_zext32_toNat, BitVec.toNat_add,
                                                              BitVec.toNat_ushiftRight,
                                                              Nat.shiftRight_eq_div_pow]
                                                            simp only [BitVec.toNat_ofNat,
                                                              Nat.reducePow]
                                                            rw [Nat.mod_eq_of_lt (by omega)]
                                                          have hj0_idx : ((1040#32 +
                                                              ((m0_r &&& 0x7FFFFFFF#32) >>>
                                                                (5 : Nat))).setWidth 64).toNat =
                                                              1040 +
                                                                (m0_r &&& 0x7FFFFFFF#32).toNat /
                                                                32 := by
                                                            rw [m6_zext32_toNat, BitVec.toNat_add,
                                                              BitVec.toNat_ushiftRight,
                                                              Nat.shiftRight_eq_div_pow]
                                                            simp only [BitVec.toNat_ofNat,
                                                              Nat.reducePow]
                                                            rw [Nat.mod_eq_of_lt (by omega)]
                                                          have hj1_idx : ((1040#32 +
                                                              ((m1_r &&& 0x7FFFFFFF#32) >>>
                                                                (5 : Nat))).setWidth 64).toNat =
                                                              1040 +
                                                                (m1_r &&& 0x7FFFFFFF#32).toNat /
                                                                32 := by
                                                            rw [m6_zext32_toNat, BitVec.toNat_add,
                                                              BitVec.toNat_ushiftRight,
                                                              Nat.shiftRight_eq_div_pow]
                                                            simp only [BitVec.toNat_ofNat,
                                                              Nat.reducePow]
                                                            rw [Nat.mod_eq_of_lt (by omega)]
                                                          have hi0_b : ((1024#32 + (i0 >>>
                                                              (5 : Nat))).setWidth 64).toNat <
                                                              scr6.length := by omega
                                                          have hi1_b : ((1024#32 + (i1 >>>
                                                              (5 : Nat))).setWidth 64).toNat <
                                                              scr6.length := by omega
                                                          have hj0_b : ((1040#32 +
                                                              ((m0_r &&& 0x7FFFFFFF#32) >>>
                                                                (5 : Nat))).setWidth 64).toNat <
                                                              scr6.length := by omega
                                                          have hj1_b : ((1040#32 +
                                                              ((m1_r &&& 0x7FFFFFFF#32) >>>
                                                                (5 : Nat))).setWidth 64).toNat <
                                                              scr6.length := by omega
                                                          have h1056 : 1056 < scr6.length := by
                                                            omega
                                                          have h1057 : 1057 < scr6.length := by
                                                            omega
                                                          c0_hsteps_nogrp
                                                          refine wp_join_state_pure (ts := [i32])
                                                            (α := BitVec 32) (fun v57 => (v57, ()))
                                                            (fun _ => True)
                                                            (fun _ v57 _ => by
                                                              c0_hsteps!
                                                              refine hQ true _ _ ?_ ?_ hm
                                                              · simp [hsc6]
                                                              · intro i hi hor
                                                                dsimp only
                                                                have hi0_e : ((1024 + i0 >>>
                                                                    (5 : Nat) :
                                                                    BitVec 32).setWidth 64).toNat =
                                                                    1024 + i0.toNat / 32 := by
                                                                  rw [show (1024 : BitVec 32) =
                                                                    1024#32 from rfl]
                                                                  exact hi0_idx
                                                                have hi1_e : ((1024 + i1 >>>
                                                                    (5 : Nat) :
                                                                    BitVec 32).setWidth 64).toNat =
                                                                    1024 + i1.toNat / 32 := by
                                                                  rw [show (1024 : BitVec 32) =
                                                                    1024#32 from rfl]
                                                                  exact hi1_idx
                                                                have hj0_e : ((1040 + (m0_r &&&
                                                                    2147483647) >>> (5 : Nat) :
                                                                    BitVec 32).setWidth 64).toNat =
                                                                    1040 + (m0_r &&&
                                                                      0x7FFFFFFF#32).toNat / 32 :=
                                                                  by
                                                                    rw [show (1040 : BitVec 32) =
                                                                        1040#32 from rfl,
                                                                      show (2147483647 :
                                                                        BitVec 32) =
                                                                        0x7FFFFFFF#32 from rfl]
                                                                    exact hj0_idx
                                                                have hj1_e : ((1040 + (m1_r &&&
                                                                    2147483647) >>> (5 : Nat) :
                                                                    BitVec 32).setWidth 64).toNat =
                                                                    1040 + (m1_r &&&
                                                                      0x7FFFFFFF#32).toNat / 32 :=
                                                                  by
                                                                    rw [show (1040 : BitVec 32) =
                                                                        1040#32 from rfl,
                                                                      show (2147483647 :
                                                                        BitVec 32) =
                                                                        0x7FFFFFFF#32 from rfl]
                                                                    exact hj1_idx
                                                                rw [List.getElem?_set_ne (by
                                                                    rw [show (1057#64).toNat =
                                                                      1057 from rfl]; omega),
                                                                  List.getElem?_set_ne (by
                                                                    rw [show (1056#64).toNat =
                                                                      1056 from rfl]; omega),
                                                                  List.getElem?_set_ne (by
                                                                    rw [hj1_e]; omega),
                                                                  List.getElem?_set_ne (by
                                                                    rw [hj0_e]; omega),
                                                                  List.getElem?_set_ne (by
                                                                    rw [hi1_e]; omega),
                                                                  List.getElem?_set_ne (by
                                                                    rw [hi0_e]; omega)]
                                                                exact hout6' i hi hor)
                                                            (fun J57 hJ57 => by
                                                              c0_hsplit
                                                              · c0_hsteps!; exact hJ57 1#32 trivial
                                                              · c0_hsteps!; exact hJ57 0#32 trivial)
                                                        · c0_hsteps!
                                                          exact hJ65 scr6 m6 ⟨hsc6, hout6', hm6⟩
                                                      · c0_hsteps!
                                                        exact hJ65 scr6 m6 ⟨hsc6, hout6', hm6⟩)
                                                · c0_hsteps!
                                                  exact hJ60 scr5 m5 ⟨hsc5, hout5', hm5⟩)
                                          · c0_hsteps!; exact hJ54 scr4 m4 ⟨hsc4, hout4', hm4⟩
                                        · c0_hsteps!; exact hJ54 scr4 m4 ⟨hsc4, hout4', hm4⟩
                                      · c0_hsteps!; exact hJ54 scr4 m4 ⟨hsc4, hout4', hm4⟩))
                                (fun Jm hJm => by
                                  c0_hsplit
                                  · c0_hsteps!; exact hJm (true, _, _, _) trivial
                                  · c0_hsteps_nogrp
                                    refine wp_join_state_pure (ts := [.bool, i32, i32, i32])
                                      (α := Bool × BitVec 32 × BitVec 32 × BitVec 32)
                                      (fun t => (t.1, t.2.1, t.2.2.1, t.2.2.2, ()))
                                      (fun _ => True)
                                      (fun _ t _ => by c0_hsteps!; exact hJm t trivial)
                                      (fun J52 hJ52 => by
                                        c0_hsplit
                                        · c0_hsteps!; exact hJ52 (true, _, _, _) trivial
                                        · c0_hsteps_nogrp
                                          refine wp_join_state_pure (ts := [.bool, i32, i32, i32])
                                            (α := Bool × BitVec 32 × BitVec 32 × BitVec 32)
                                            (fun t => (t.1, t.2.1, t.2.2.1, t.2.2.2, ()))
                                            (fun _ => True)
                                            (fun _ t _ => by c0_hsteps!; exact hJ52 t trivial)
                                            (fun J55 hJ55 => by
                                              c0_hsplit
                                              · c0_hsteps!; exact hJ55 (true, _, _, _) trivial
                                              · c0_hsteps_nogrp
                                                refine wp_join_state_pure
                                                  (ts := [.bool, i32, i32, i32])
                                                  (α := Bool × BitVec 32 × BitVec 32 × BitVec 32)
                                                  (fun t => (t.1, t.2.1, t.2.2.1, t.2.2.2, ()))
                                                  (fun _ => True)
                                                  (fun _ t _ => by c0_hsteps!; exact hJ55 t trivial)
                                                  (fun J58 hJ58 => by
                                                    c0_hsplit
                                                    · c0_hsteps!
                                                      exact hJ58 (true, _, _, _) trivial
                                                    · c0_hsteps!
                                                      exact hJ58
                                                        (false, 0#32, 0#32, 0#32) trivial))))
                            · c0_hsteps!; exact hJ1 scr4 m4 ⟨hsc4, hout4', hm4⟩
                          · c0_hsteps!; exact hJ1 scr3 m3 ⟨hsc3, hout3, hm3⟩)
                    · c0_hsteps!; exact hJ0 scr3 m3 ⟨hsc3, hout3, hm3⟩
                  · intro L1 hL1; c0_hsteps!
                    exact hL1 (plim.toNat - (i0 + 1#32).toNat) (i0 + 1#32, ()) m2
                      ⟨scr2, hsc2, by omega, rfl, hout2', hm2⟩
                · c0_hsteps!; exact hJ0 scr2 m2 ⟨hsc2, hout2', hm2⟩
              · c0_hsteps!; exact hJ0 scr1 m1 ⟨hsc1, hout1, hm1⟩)
        · c0_hsteps!; exact hQ false scr1 m1 hsc1 hout1 hm1
      · intro L0 hL0; c0_hsteps!
        exact hL0 plim.toNat (0#32, ()) m0
          ⟨s0.scratch.scratch_buf, hdw0.1.scratch_ok.scratch_buf_len, Nat.zero_le _, by simp,
           fun _ _ _ => rfl, hm0⟩)
    (fun Jpl hJpl => by
      c0_hsplit
      · c0_hsteps!; exact hJpl np ⟨Nat.le_refl _, hc⟩
      · c0_hsteps!; exact hJpl 64#32 ⟨by simp at hc ⊢; omega, by simp⟩)

/-- Contract for `full_bve_gates_m6`: runs Equiv / AND / ITE / Kitten `full_find_definition`
gate extraction while preserving `FullDenseInvW`, `TmkZero`, `cur_vars`, `arena`, `arena_len`,
`fuel ≤`, `scr[0 ..< np)`, and `scr[512 ..< 512 + nn)`. -/
def fullBveGatesM6Spec : Spec [i64, i32, i32, i32] [] := fun (h, v, np, nn, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ TmkZero s ∧ 1088 ≤ c.scratch_cap ∧
    v.toNat < s.core.cur_vars ∧ np.toNat ≤ 512 ∧ nn.toNat ≤ 512 ∧
    (∀ i < np.toNat, FullBveEntryOkW F_cur s (2 * v.toNat)
      (s.scratch.scratch_buf[i]?.getD 0#32)) ∧
    (∀ j < nn.toNat, FullBveEntryOkW F_cur s (2 * v.toNat + 1)
      (s.scratch.scratch_buf[512 + j]?.getD 0#32)) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ s' m',
      FullDenseInvW c F0 F_cur s' → TmkZero s' →
      s'.core.cur_vars = s.core.cur_vars → s'.core.arena = s.core.arena →
      s'.core.arena_len = s.core.arena_len → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (∀ i < np.toNat, s'.scratch.scratch_buf[i]? = s.scratch.scratch_buf[i]?) →
      (∀ j < nn.toNat, s'.scratch.scratch_buf[512 + j]? = s.scratch.scratch_buf[512 + j]?) →
      (FullMem c s' ⋆ R) m' → Q () m'

theorem fullBveGatesM6Spec_noExit :
    ∀ xs m Q X, fullBveGatesM6Spec xs m Q X →
      fullBveGatesM6Spec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => h

theorem fullBveGatesM6Spec_intro {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {R : Mem 64 → Prop} {h : BitVec 64} {v np nn : BitVec 32}
    {m : Mem 64} {Q : Post []} {X : XPost}
    (hh : h = c.hdr) (hdw : FullDenseInvW c F0 F_cur s) (htmk : TmkZero s)
    (hsc : 1088 ≤ c.scratch_cap) (hv : v.toNat < s.core.cur_vars)
    (hnp : np.toNat ≤ 512) (hnn : nn.toNat ≤ 512)
    (hp : ∀ i < np.toNat, FullBveEntryOkW F_cur s (2 * v.toNat)
      (s.scratch.scratch_buf[i]?.getD 0#32))
    (hn : ∀ j < nn.toNat, FullBveEntryOkW F_cur s (2 * v.toNat + 1)
      (s.scratch.scratch_buf[512 + j]?.getD 0#32))
    (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ s' m',
      FullDenseInvW c F0 F_cur s' → TmkZero s' →
      s'.core.cur_vars = s.core.cur_vars → s'.core.arena = s.core.arena →
      s'.core.arena_len = s.core.arena_len → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (∀ i < np.toNat, s'.scratch.scratch_buf[i]? = s.scratch.scratch_buf[i]?) →
      (∀ j < nn.toNat, s'.scratch.scratch_buf[512 + j]? = s.scratch.scratch_buf[512 + j]?) →
      (FullMem c s' ⋆ R) m' → Q () m') :
    fullBveGatesM6Spec (h, v, np, nn, ()) m Q X :=
  ⟨c, F0, F_cur, s, R, hh, hdw, htmk, hsc, hv, hnp, hnn, hp, hn, hm, hQ⟩

private theorem m6_fullDenseInvW_set_scratch {c : FullCfg} {F0 : CNF Nat}
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

/-- Parametric `Func.wp` proof for `full_bve_gates_m6`. -/
theorem full_bve_gates_m6_wp (Γ : Env)
    (hMarkAnd : ∀ a m Q X, fullBveMarkAndM6Spec a m Q X →
      Γ "full_bve_mark_and_m6" [i64, i32, i32, i32, i32, i32] [.bool] a m Q X)
    (hFindIte : ∀ a m Q X, fullBveFindIteM6Spec a m Q X →
      Γ "full_bve_find_ite_m6" [i64, i32, i32, i32] [.bool] a m Q X)
    (hFindDef : ∀ a m Q X, FullDefSweep.fullFindDefinitionSpec a m Q X →
      Γ "full_find_definition" [i64, i32, i32, i32] [] a m Q X) :
    ∀ a m Q X, fullBveGatesM6Spec a m Q X →
      Func.wp Γ full_bve_gates_m6_body a m Q X := by
  rintro ⟨h, v, np, nn, ⟨⟩⟩ m0 Q X
    ⟨c, F0, F_cur, s0, R, rfl, hdw0, htmk0, hsc1088, hv_lt, hnp512, hnn512, hent_p, hent_n,
      hm0, hQ⟩
  have hmx := c.hmaxv; have hsc := c.hscr; unfold dimacsBound at hmx hsc
  have hcv_le := hdw0.1.core_ok.cur_vars_le
  have hplnl := m6_pl_nl_eq v (by omega)
  unfold Func.wp full_bve_gates_m6_body
  c0_hsteps_nogrp
  -- Zero `scr[1024 ..< 1058)`
  refine wp_loop_group (ts := [i32])
    (fun rem0 (k, ()) mk => ∃ scr0 : List (BitVec 32),
      let sk : FullState := { s0 with scratch := { s0.scratch with scratch_buf := scr0 } }
      scr0.length = c.scratch_cap ∧ k.toNat ≤ 34 ∧ rem0 = 34 - k.toNat ∧
      (∀ i < 1024, scr0[i]? = s0.scratch.scratch_buf[i]?) ∧ (FullMem c sk ⋆ R) mk)
    ?_ ?_
  · rintro L0 rem0 ⟨k, ⟨⟩⟩ mk hL0 ⟨scr0, hsc0, hk_le, rfl, hkeep0, hmk⟩
    c0_hsplit
    · have hk_lt : k.toNat < 34 := hc
      have hidx : ((1024#32 + k).setWidth 64).toNat < scr0.length := by
        rw [hsc0, m6_zext32_toNat]; c0_bound
      have hk1 : (k + 1#32).toNat = k.toNat + 1 := by c0_bound
      c0_hsteps!
      exact hL0 (34 - (k + 1#32).toNat) (k + 1#32, ()) _ (by omega)
        ⟨scr0.set ((1024#32 + k).setWidth 64).toNat 0#32, by simp [hsc0], by omega, rfl,
         fun i hi => by
           rw [List.getElem?_set_ne (by rw [m6_zext32_toNat]; c0_bound)]; exact hkeep0 i hi, hm⟩
    · -- Loop 1: Equiv & positive AND-gate search (`i < np`)
      c0_hsteps_nogrp
      refine wp_loop_group (ts := [i32])
        (fun rem1 (i, ()) m1 => ∃ (lm1 : List (BitVec 8)) (scr1 : List (BitVec 32)),
          let s1 : FullState :=
            { s0 with
              core := { s0.core with lit_mark := lm1 },
              scratch := { s0.scratch with scratch_buf := scr1 } }
          FullDenseInvW c F0 F_cur s1 ∧ i.toNat ≤ np.toNat ∧ rem1 = np.toNat - i.toNat ∧
          (∀ idx < 1024, scr1[idx]? = s0.scratch.scratch_buf[idx]?) ∧
          (FullMem c s1 ⋆ R) m1)
        ?_ ?_
      · rintro L1 rem1 ⟨i, ⟨⟩⟩ m1 hL1 ⟨lm1, scr1, hdw1, hi_le, rfl, hkeep1, hm1⟩
        let s1 : FullState :=
          { s0 with
            core := { s0.core with lit_mark := lm1 },
            scratch := { s0.scratch with scratch_buf := scr1 } }
        c0_hsplit
        · have hi_lt : i.toNat < np.toNat := hc
          have hsc1_len : scr1.length = c.scratch_cap := hdw1.1.scratch_ok.scratch_buf_len
          have hi_sc : (i.setWidth 64).toNat < scr1.length := by
            rw [hsc1_len, m6_zext32_toNat]; omega
          have hi1 : (i + 1#32).toNat = i.toNat + 1 := by c0_bound
          let wp_i := scr1[(i.setWidth 64).toNat]'hi_sc
          have hwp_orig : wp_i = s0.scratch.scratch_buf[i.toNat]?.getD 0#32 := by
            have hget := hkeep1 i.toNat (by omega)
            have hi' : i.toNat < scr1.length := by omega
            rw [List.getElem?_eq_getElem hi'] at hget
            rw [← hget, Option.getD_some]
            exact m6_getElem_congr (m6_zext32_toNat i) hi_sc hi'
          c0_hsteps_nogrp
          refine wp_join_state (ts := []) (α := List (BitVec 8) × List (BitVec 32)) (fun _ => ())
            (fun p mj =>
              let sj : FullState :=
                { s0 with
                  core := { s0.core with lit_mark := p.1 },
                  scratch := { s0.scratch with scratch_buf := p.2 } }
              FullDenseInvW c F0 F_cur sj ∧
              (∀ idx < 1024, p.2[idx]? = s0.scratch.scratch_buf[idx]?) ∧
              (FullMem c sj ⋆ R) mj)
            (fun _ ⟨lm_n, scr_n⟩ mj ⟨hdw_n, hkeep_n, hm_n⟩ => by
              c0_hsteps!
              exact hL1 (np.toNat - (i + 1#32).toNat) (i + 1#32, ()) mj (by omega)
                ⟨lm_n, scr_n, hdw_n, by omega, rfl, hkeep_n, hm_n⟩)
            (fun J1 hJ1 => by
              c0_hsplit
              · -- Binary `wp_i`: scan `j < nn` for opposite binary (Equiv gate)
                c0_hsteps_nogrp
                refine wp_loop_group (ts := [i32])
                  (fun rem_j (j, ()) mj => mj = m1 ∧ j.toNat ≤ nn.toNat ∧
                    rem_j = nn.toNat - j.toNat)
                  ?_ ?_
                · rintro Lj rem_j ⟨j, ⟨⟩⟩ mj hLj ⟨hm_j, hj_le, rfl⟩
                  subst mj
                  c0_hsplit
                  · have hj_lt : j.toNat < nn.toNat := hc
                    have hj_sc : ((512#32 + j).setWidth 64).toNat < scr1.length := by
                      rw [hsc1_len, m6_zext32_toNat]; c0_bound
                    have hj1 : (j + 1#32).toNat = j.toNat + 1 := by c0_bound
                    c0_hsteps_nogrp
                    refine wp_join0 (P := fun mj => mj = m1)
                      (fun _ mj hmj => by
                        subst mj
                        c0_hsteps!
                        exact hLj (nn.toNat - (j + 1#32).toNat) (j + 1#32, ()) m1 (by omega)
                          ⟨rfl, by omega, rfl⟩)
                      (fun J30 hJ30 => by
                        c0_hsplit
                        · c0_hsplit
                          · have hi_idx : ((1024 + i >>> (5 : Nat) : BitVec 32).setWidth 64).toNat =
                                1024 + i.toNat / 32 := by
                              rw [m6_zext32_toNat, BitVec.toNat_add,
                                show (1024 : BitVec 32).toNat = 1024 from rfl,
                                BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
                                show 2 ^ 5 = 32 from rfl, Nat.mod_eq_of_lt (by omega)]
                            have hj_idx : ((1040 + j >>> (5 : Nat) : BitVec 32).setWidth 64).toNat =
                                1040 + j.toNat / 32 := by
                              rw [m6_zext32_toNat, BitVec.toNat_add,
                                show (1040 : BitVec 32).toNat = 1040 from rfl,
                                BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
                                show 2 ^ 5 = 32 from rfl, Nat.mod_eq_of_lt (by omega)]
                            have hi_b : ((1024#32 + (i >>> (5 : Nat))).setWidth 64).toNat <
                                scr1.length := by
                              rw [hsc1_len, m6_zext32_toNat, BitVec.toNat_add, BitVec.toNat_ofNat,
                                BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
                                show 2 ^ 5 = 32 from rfl, Nat.mod_eq_of_lt (by omega)]; omega
                            have hj_b : ((1040#32 + (j >>> (5 : Nat))).setWidth 64).toNat <
                                scr1.length := by
                              rw [hsc1_len, m6_zext32_toNat, BitVec.toNat_add, BitVec.toNat_ofNat,
                                BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
                                show 2 ^ 5 = 32 from rfl, Nat.mod_eq_of_lt (by omega)]; omega
                            have h1056 : 1056 < scr1.length := by rw [hsc1_len]; omega
                            have h1057 : 1057 < scr1.length := by rw [hsc1_len]; omega
                            c0_hsteps!
                            refine hQ _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hm
                            · exact m6_fullDenseInvW_set_scratch hdw1 (by simp [hsc1_len])
                            · exact htmk0
                            · rfl
                            · rfl
                            · rfl
                            · exact Nat.le_refl _
                            · intro k hk
                              rw [hi_idx, hj_idx,
                                List.getElem?_set_ne
                                  (by rw [show (1057#64).toNat = 1057 from rfl]; omega),
                                List.getElem?_set_ne
                                  (by rw [show (1056#64).toNat = 1056 from rfl]; omega),
                                List.getElem?_set_ne (by omega),
                                List.getElem?_set_ne (by omega)]
                              exact hkeep1 k (by omega)
                            · intro k hk
                              rw [hi_idx, hj_idx,
                                List.getElem?_set_ne
                                  (by rw [show (1057#64).toNat = 1057 from rfl]; omega),
                                List.getElem?_set_ne
                                  (by rw [show (1056#64).toNat = 1056 from rfl]; omega),
                                List.getElem?_set_ne (by omega),
                                List.getElem?_set_ne (by omega)]
                              exact hkeep1 (512 + k) (by omega)
                          · c0_hsteps!; exact hJ30 m1 rfl
                        · c0_hsteps!; exact hJ30 m1 rfl)
                  · c0_hsteps!; exact hJ1 (lm1, scr1) m1 ⟨hdw1, hkeep1, hm1⟩
                · intro Lj hLj; c0_hsteps!
                  exact hLj nn.toNat (0#32, ()) m1 ⟨rfl, Nat.zero_le _, by simp⟩
              · -- Large `wp_i`: try `full_bve_mark_and_m6(h, pl, wp_i, 512, nn, 1040)`
                have hent_i := hent_p i.toNat hi_lt
                rw [← hwp_orig] at hent_i; unfold FullBveEntryOkW at hent_i
                rw [ite_eq_right (fun h => h hc)] at hent_i
                c0_hsteps_nogrp
                m6_call hMarkAnd
                dsimp only [vals, Arg.val]
                refine ⟨c, F0, F_cur, s1, R, rfl, hdw1, hent_i.1, hent_i.2, by simp; omega,
                  by simp; omega, hnn512, fun j hj => by
                    rw [show (512 : BitVec 32).toNat = 512 from rfl, hkeep1 (512 + j) (by omega)]
                    have hxor : (v <<< (1 : Nat)).toNat ^^^ 1 = 2 * v.toNat + 1 := by
                      rw [hplnl.1]; have := m6_xor1_mod2 (2 * v.toNat)
                      have := fullInv_var_xor1 (2 * v.toNat); omega
                    rw [show (v <<< 1 : BitVec 32) = v <<< (1 : Nat) from rfl, hxor]
                    exact m6_bveEntry_congr_core (hent_n j hj) rfl rfl rfl, hm1, ?_⟩
                intro ok_a lm2 scr2 m2 s2 hdw2 hout2 hm2
                dsimp only [s2] at hm2
                have hkeep2 : ∀ idx < 1024, scr2[idx]? = s0.scratch.scratch_buf[idx]? :=
                  fun idx hi =>
                    (hout2 idx (by omega) (Or.inl (by simp; omega))).trans (hkeep1 idx hi)
                c0_hsplit
                · have hsc2_len : scr2.length = c.scratch_cap := hdw2.1.scratch_ok.scratch_buf_len
                  have hi_idx : ((1024 + i >>> (5 : Nat) : BitVec 32).setWidth 64).toNat =
                      1024 + i.toNat / 32 := by
                    rw [m6_zext32_toNat, BitVec.toNat_add,
                      show (1024 : BitVec 32).toNat = 1024 from rfl,
                      BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
                      show 2 ^ 5 = 32 from rfl, Nat.mod_eq_of_lt (by omega)]
                  have hi_b : ((1024#32 + (i >>> (5 : Nat))).setWidth 64).toNat < scr2.length := by
                    rw [hsc2_len, m6_zext32_toNat, BitVec.toNat_add, BitVec.toNat_ofNat,
                      BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
                      show 2 ^ 5 = 32 from rfl, Nat.mod_eq_of_lt (by omega)]; omega
                  have h1056 : 1056 < scr2.length := by rw [hsc2_len]; omega
                  have h1057 : 1057 < scr2.length := by rw [hsc2_len]; omega
                  c0_hsteps!
                  refine hQ _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hm
                  · exact m6_fullDenseInvW_set_scratch hdw2 (by simp [hsc2_len])
                  · exact htmk0
                  · rfl
                  · rfl
                  · rfl
                  · exact Nat.le_refl _
                  · intro k hk
                    rw [hi_idx,
                      List.getElem?_set_ne
                        (by rw [show (1057#64).toNat = 1057 from rfl]; omega),
                      List.getElem?_set_ne
                        (by rw [show (1056#64).toNat = 1056 from rfl]; omega),
                      List.getElem?_set_ne (by omega)]; exact hkeep2 k (by omega)
                  · intro k hk
                    rw [hi_idx,
                      List.getElem?_set_ne
                        (by rw [show (1057#64).toNat = 1057 from rfl]; omega),
                      List.getElem?_set_ne
                        (by rw [show (1056#64).toNat = 1056 from rfl]; omega),
                      List.getElem?_set_ne (by omega)]; exact hkeep2 (512 + k) (by omega)
                · c0_hsteps!; exact hJ1 (lm2, scr2) m2 ⟨hdw2, hkeep2, hm2⟩)
        · -- Loop 2: negative AND-gate search (`j < nn`)
          c0_hsteps_nogrp
          refine wp_loop_group (ts := [i32])
            (fun rem2 (j, ()) m2 => ∃ (lm2 : List (BitVec 8)) (scr2 : List (BitVec 32)),
              let s2 : FullState :=
                { s0 with
                  core := { s0.core with lit_mark := lm2 },
                  scratch := { s0.scratch with scratch_buf := scr2 } }
              FullDenseInvW c F0 F_cur s2 ∧ j.toNat ≤ nn.toNat ∧ rem2 = nn.toNat - j.toNat ∧
              (∀ idx < 1024, scr2[idx]? = s0.scratch.scratch_buf[idx]?) ∧
              (FullMem c s2 ⋆ R) m2)
            ?_ ?_
          · rintro L2 rem2 ⟨j, ⟨⟩⟩ m2 hL2 ⟨lm2, scr2, hdw2, hj_le, rfl, hkeep2, hm2⟩
            let s2 : FullState :=
              { s0 with
                core := { s0.core with lit_mark := lm2 },
                scratch := { s0.scratch with scratch_buf := scr2 } }
            c0_hsplit
            · have hj_lt : j.toNat < nn.toNat := hc
              have hj_sc : ((512#32 + j).setWidth 64).toNat < scr2.length := by
                rw [hdw2.1.scratch_ok.scratch_buf_len, m6_zext32_toNat]; c0_bound
              have hj1 : (j + 1#32).toNat = j.toNat + 1 := by c0_bound
              let wn_j := scr2[((512#32 + j).setWidth 64).toNat]'hj_sc
              have hwn_orig : wn_j = s0.scratch.scratch_buf[512 + j.toNat]?.getD 0#32 := by
                have h512 : ((512#32 + j).setWidth 64).toNat = 512 + j.toNat := by
                  rw [m6_zext32_toNat]; c0_bound
                have hget := hkeep2 (512 + j.toNat) (by omega)
                have hj' : 512 + j.toNat < scr2.length := by omega
                rw [List.getElem?_eq_getElem hj'] at hget
                rw [← hget, Option.getD_some]
                exact m6_getElem_congr h512 hj_sc hj'
              c0_hsteps_nogrp
              refine wp_join_state (ts := []) (α := List (BitVec 8) × List (BitVec 32))
                (fun _ => ())
                (fun p mj =>
                  let sj : FullState :=
                    { s0 with
                      core := { s0.core with lit_mark := p.1 },
                      scratch := { s0.scratch with scratch_buf := p.2 } }
                  FullDenseInvW c F0 F_cur sj ∧
                  (∀ idx < 1024, p.2[idx]? = s0.scratch.scratch_buf[idx]?) ∧
                  (FullMem c sj ⋆ R) mj)
                (fun _ ⟨lm_n, scr_n⟩ mj ⟨hdw_n, hkeep_n, hm_n⟩ => by
                  c0_hsteps!
                  exact hL2 (nn.toNat - (j + 1#32).toNat) (j + 1#32, ()) mj (by omega)
                    ⟨lm_n, scr_n, hdw_n, by omega, rfl, hkeep_n, hm_n⟩)
                (fun J2 hJ2 => by
                  c0_hsplit
                  · have hent_j := hent_n j.toNat hj_lt
                    rw [← hwn_orig] at hent_j; unfold FullBveEntryOkW at hent_j
                    rw [ite_eq_right (fun h => h hc)] at hent_j
                    c0_hsteps_nogrp
                    m6_call hMarkAnd
                    dsimp only [vals, Arg.val]
                    refine ⟨c, F0, F_cur, s2, R, rfl, hdw2, hent_j.1, hent_j.2, by simp; omega,
                      by simp; omega, hnp512, fun k hk => by
                        rw [show (0 : BitVec 32).toNat = 0 from rfl, Nat.zero_add,
                          hkeep2 k (by omega)]
                        have hxor : ((v <<< (1 : Nat)) ||| 1#32).toNat ^^^ 1 = 2 * v.toNat := by
                          rw [hplnl.2]; have := m6_xor1_mod2 (2 * v.toNat + 1)
                          have := fullInv_var_xor1 (2 * v.toNat + 1); omega
                        rw [show ((v <<< 1 : BitVec 32) ||| 1) =
                            (v <<< (1 : Nat)) ||| 1#32 from rfl, hxor]
                        exact m6_bveEntry_congr_core (hent_p k hk) rfl rfl rfl, hm2, ?_⟩
                    intro ok_a lm3 scr3 m3 s3 hdw3 hout3 hm3
                    dsimp only [s3] at hm3
                    have hkeep3 : ∀ idx < 1024, scr3[idx]? = s0.scratch.scratch_buf[idx]? :=
                      fun idx hi =>
                        (hout3 idx (by omega) (Or.inl (by simp; omega))).trans (hkeep2 idx hi)
                    c0_hsplit
                    · have hsc3_len : scr3.length = c.scratch_cap :=
                        hdw3.1.scratch_ok.scratch_buf_len
                      have hj_idx : ((1040 + j >>> (5 : Nat) : BitVec 32).setWidth 64).toNat =
                          1040 + j.toNat / 32 := by
                        rw [m6_zext32_toNat, BitVec.toNat_add,
                          show (1040 : BitVec 32).toNat = 1040 from rfl,
                          BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
                          show 2 ^ 5 = 32 from rfl, Nat.mod_eq_of_lt (by omega)]
                      have hj_b : ((1040#32 + (j >>> (5 : Nat))).setWidth 64).toNat <
                          scr3.length := by
                        rw [hsc3_len, m6_zext32_toNat, BitVec.toNat_add, BitVec.toNat_ofNat,
                          BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
                          show 2 ^ 5 = 32 from rfl, Nat.mod_eq_of_lt (by omega)]; omega
                      have h1056 : 1056 < scr3.length := by rw [hsc3_len]; omega
                      have h1057 : 1057 < scr3.length := by rw [hsc3_len]; omega
                      c0_hsteps!
                      refine hQ _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hm
                      · exact m6_fullDenseInvW_set_scratch hdw3 (by simp [hsc3_len])
                      · exact htmk0
                      · rfl
                      · rfl
                      · rfl
                      · exact Nat.le_refl _
                      · intro k hk
                        rw [hj_idx,
                          List.getElem?_set_ne
                            (by rw [show (1057#64).toNat = 1057 from rfl]; omega),
                          List.getElem?_set_ne
                            (by rw [show (1056#64).toNat = 1056 from rfl]; omega),
                          List.getElem?_set_ne (by omega)]; exact hkeep3 k (by omega)
                      · intro k hk
                        rw [hj_idx,
                          List.getElem?_set_ne
                            (by rw [show (1057#64).toNat = 1057 from rfl]; omega),
                          List.getElem?_set_ne
                            (by rw [show (1056#64).toNat = 1056 from rfl]; omega),
                          List.getElem?_set_ne (by omega)]; exact hkeep3 (512 + k) (by omega)
                    · c0_hsteps!; exact hJ2 (lm3, scr3) m3 ⟨hdw3, hkeep3, hm3⟩
                  · c0_hsteps!; exact hJ2 (lm2, scr2) m2 ⟨hdw2, hkeep2, hm2⟩)
            · -- Phase 3: structural `ifthenelse` gate extraction
              c0_hsteps_nogrp
              m6_call hFindIte
              refine ⟨c, F0, F_cur, s2, R, rfl, hdw2, by omega, hv_lt, hnp512, hnn512,
                fun k hk => by
                  change k < np.toNat at hk
                  dsimp only [s2]; rw [hkeep2 k (by omega)]
                  exact m6_bveEntry_congr_core (hent_p k hk) rfl rfl rfl,
                fun k hk => by
                  change k < nn.toNat at hk
                  dsimp only [s2]; rw [hkeep2 (512 + k) (by omega)]
                  exact m6_bveEntry_congr_core (hent_n k hk) rfl rfl rfl, hm2, ?_⟩
              intro ok_ite scr3 m3 s3 hsc3 hout3 hm3
              have hdw3 : FullDenseInvW c F0 F_cur s3 :=
                m6_fullDenseInvW_with_scratch hdw2
                  { hdw2.1.scratch_ok with scratch_buf_len := hsc3 } rfl rfl
              have hkeep3 : ∀ idx < 1024, scr3[idx]? = s0.scratch.scratch_buf[idx]? :=
                fun idx hi => (hout3 idx (by omega) (Or.inl hi)).trans (hkeep2 idx hi)
              c0_hsplit
              · c0_hsteps!
                exact hQ s3 m3 hdw3 htmk0 rfl rfl rfl (Nat.le_refl _)
                  (fun k hk => hkeep3 k (by omega)) (fun k hk => hkeep3 (512 + k) (by omega)) hm3
              · -- Phase 4: Kitten `full_find_definition` fallback when `cap >= 10240`
                c0_hsteps_nogrp
                refine wp_join_state (ts := [i32, i32]) (α := BitVec 32 × BitVec 32 × FullState)
                  (fun x => (x.1, x.2.1, ()))
                  (fun x mf => FullDenseInvW c F0 F_cur x.2.2 ∧ TmkZero x.2.2 ∧
                    x.2.2.core.cur_vars = s0.core.cur_vars ∧ x.2.2.core.arena = s0.core.arena ∧
                    x.2.2.core.arena_len = s0.core.arena_len ∧
                    x.2.2.core.fuel.toNat ≤ s0.core.fuel.toNat ∧
                    (∀ k < np.toNat, x.2.2.scratch.scratch_buf[k]? = s0.scratch.scratch_buf[k]?) ∧
                    (∀ k < nn.toNat,
                      x.2.2.scratch.scratch_buf[512 + k]? = s0.scratch.scratch_buf[512 + k]?) ∧
                    (FullMem c x.2.2 ⋆ R) mf)
                  (fun _ ⟨_, _, sf⟩ mf ⟨hdwf, htmkf, hcvf, harf, half, hflf, hpf, hnf, hmf⟩ => by
                    c0_hsteps!; exact hQ sf mf hdwf htmkf hcvf harf half hflf hpf hnf hmf)
                  (fun J18 hJ18 => by
                    c0_hsplit
                    · have hnp64 : np.toNat ≤ 64 := hc
                      c0_hsplit
                      · have hnn64 : nn.toNat ≤ 64 := hc
                        c0_hsplit
                        · have hsc10240 : 10240 ≤ c.scratch_cap := by
                            rw [Nat.mod_eq_of_lt (by omega)] at hc; exact hc
                          c0_hsteps_nogrp
                          -- Copy `scr[512 ..< 512 + nn)` into `scr[64 ..< 64 + nn)`
                          refine wp_loop_group (ts := [i32])
                            (fun rem_cp (jc, ()) mc => ∃ scr_c : List (BitVec 32),
                              let sc : FullState :=
                                { s3 with scratch := { s3.scratch with scratch_buf := scr_c } }
                              scr_c.length = c.scratch_cap ∧ jc.toNat ≤ nn.toNat ∧
                              rem_cp = nn.toNat - jc.toNat ∧
                              (∀ k < np.toNat, scr_c[k]? = s0.scratch.scratch_buf[k]?) ∧
                              (∀ k < jc.toNat, scr_c[64 + k]? = s0.scratch.scratch_buf[512 + k]?) ∧
                              (∀ k < nn.toNat, scr_c[512 + k]? = s0.scratch.scratch_buf[512 + k]?) ∧
                              (FullMem c sc ⋆ R) mc)
                            ?_ ?_
                          · rintro Lc rem_cp ⟨jc, ⟨⟩⟩ mc hLc
                              ⟨scr_c, hscc, hjc_le, rfl, hp_c, hn64_c, hn512_c, hmc⟩
                            c0_hsplit
                            · have hjc_lt : jc.toNat < nn.toNat := hc
                              have h512_sc : ((512 + jc : BitVec 32).setWidth 64).toNat <
                                  scr_c.length := by
                                rw [hscc, m6_zext32_toNat, BitVec.toNat_add,
                                  show (512 : BitVec 32).toNat = 512 from rfl,
                                  Nat.mod_eq_of_lt (by omega)]; omega
                              have h64_sc : ((64 + jc : BitVec 32).setWidth 64).toNat <
                                  scr_c.length := by
                                rw [hscc, m6_zext32_toNat, BitVec.toNat_add,
                                  show (64 : BitVec 32).toNat = 64 from rfl,
                                  Nat.mod_eq_of_lt (by omega)]; omega
                              have hjc1 : (jc + 1#32).toNat = jc.toNat + 1 := by c0_bound
                              have h512_eq :
                                  ((512 + jc : BitVec 32).setWidth 64).toNat = 512 + jc.toNat := by
                                rw [m6_zext32_toNat, BitVec.toNat_add,
                                  show (512 : BitVec 32).toNat = 512 from rfl,
                                  Nat.mod_eq_of_lt (by omega)]
                              have h64_eq : ((64 + jc : BitVec 32).setWidth 64).toNat =
                                  64 + jc.toNat := by
                                rw [m6_zext32_toNat, BitVec.toNat_add,
                                  show (64 : BitVec 32).toNat = 64 from rfl,
                                  Nat.mod_eq_of_lt (by omega)]
                              c0_hsteps!
                              exact hLc (nn.toNat - (jc + 1#32).toNat) (jc + 1#32, ()) _ (by omega)
                                ⟨_, by simp [hscc], by omega, rfl,
                                 fun k hk => by
                                   rw [show ((64 + jc : BitVec 32).setWidth 64).toNat =
                                       64 + jc.toNat from h64_eq, List.getElem?_set_ne (by omega)]
                                   exact hp_c k hk,
                                 fun k hk => by
                                   rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp (hjc1 ▸ hk))
                                     with h | h
                                   · rw [show ((64 + jc : BitVec 32).setWidth 64).toNat =
                                         64 + jc.toNat from h64_eq,
                                       List.getElem?_set_ne (by omega)]
                                     exact hn64_c k h
                                   · subst h
                                     rw [show ((64 + jc : BitVec 32).setWidth 64).toNat =
                                         64 + jc.toNat from h64_eq,
                                       List.getElem?_set_self (by rw [hscc]; omega)]
                                     rw [m6_getElem_congr h512_eq h512_sc (by rw [hscc]; omega),
                                       ← List.getElem?_eq_getElem (by rw [hscc]; omega)]
                                     exact hn512_c jc.toNat hjc_lt,
                                 fun k hk => by
                                   rw [show ((64 + jc : BitVec 32).setWidth 64).toNat =
                                       64 + jc.toNat from h64_eq, List.getElem?_set_ne (by omega)]
                                   exact hn512_c k hk, hm⟩
                            · have hjc_eq : jc.toNat = nn.toNat := by omega
                              have h128 : 128 < scr_c.length := by omega
                              have h129 : 129 < scr_c.length := by omega
                              have h130 : 130 < scr_c.length := by omega
                              have h131 : 131 < scr_c.length := by omega
                              c0_hsteps_nogrp
                              let scr_d0 := (((scr_c.set 128 0#32).set 129 0#32).set 130 0#32).set
                                131 0#32
                              let sd0 : FullState :=
                                { s3 with scratch := { s3.scratch with scratch_buf := scr_d0 } }
                              have hdwd0 : FullDenseInvW c F0 F_cur sd0 :=
                                m6_fullDenseInvW_with_scratch hdw3
                                  { hdw3.1.scratch_ok with
                                    scratch_buf_len := by simp [scr_d0, hscc] }
                                  rfl rfl
                              have hp_d0 : ∀ k < np.toNat,
                                  scr_d0[k]? = s0.scratch.scratch_buf[k]? := fun k hk => by
                                dsimp only [scr_d0]
                                rw [List.getElem?_set_ne (by omega),
                                  List.getElem?_set_ne (by omega),
                                  List.getElem?_set_ne (by omega),
                                  List.getElem?_set_ne (by omega)]
                                exact hp_c k hk
                              have hn_d0 : ∀ k < nn.toNat,
                                  scr_d0[64 + k]? = s0.scratch.scratch_buf[512 + k]? :=
                                fun k hk => by
                                  dsimp only [scr_d0]
                                  rw [List.getElem?_set_ne (by omega),
                                    List.getElem?_set_ne (by omega),
                                    List.getElem?_set_ne (by omega),
                                    List.getElem?_set_ne (by omega)]
                                  exact hn64_c k (by omega)
                              m6_call hFindDef
                              refine ⟨c, F0, F_cur, sd0, R, rfl, hdwd0, by omega, htmk0, hv_lt,
                                hnp64, hnn64, fun k hk => by
                                  dsimp only [sd0]; rw [hp_d0 k hk]
                                  exact m6_bveEntry_congr_core (hent_p k hk) rfl rfl rfl,
                                fun k hk => by
                                  dsimp only [sd0]; rw [hn_d0 k hk]
                                  exact m6_bveEntry_congr_core (hent_n k hk) rfl rfl rfl, hm, ?_⟩
                              intro sd1 md1
                              dsimp only
                              intro hdwd1 htmk1 hcv1 _ har1 hal1 hfl1 hscr1 _ hmd1
                              have h128_1 : 128 < sd1.scratch.scratch_buf.length := by
                                rw [hdwd1.1.scratch_ok.scratch_buf_len]; omega
                              have h129_1 : 129 < sd1.scratch.scratch_buf.length := by
                                rw [hdwd1.1.scratch_ok.scratch_buf_len]; omega
                              have h130_1 : 130 < sd1.scratch.scratch_buf.length := by
                                rw [hdwd1.1.scratch_ok.scratch_buf_len]; omega
                              have h131_1 : 131 < sd1.scratch.scratch_buf.length := by
                                rw [hdwd1.1.scratch_ok.scratch_buf_len]; omega
                              c0_hsteps_nogrp
                              -- Restore `scr[512 ..< 512 + nn)` from `scr[64 ..< 64 + nn)`
                              refine wp_loop_group (ts := [i32])
                                (fun rem_r (jr, ()) mr => ∃ scr_r : List (BitVec 32),
                                  let sr : FullState :=
                                    { sd1 with
                                      scratch := { sd1.scratch with scratch_buf := scr_r } }
                                  scr_r.length = c.scratch_cap ∧ jr.toNat ≤ nn.toNat ∧
                                  rem_r = nn.toNat - jr.toNat ∧
                                  (∀ k < np.toNat, scr_r[k]? = s0.scratch.scratch_buf[k]?) ∧
                                  (∀ k < nn.toNat,
                                    scr_r[64 + k]? = s0.scratch.scratch_buf[512 + k]?) ∧
                                  (∀ k < jr.toNat,
                                    scr_r[512 + k]? = s0.scratch.scratch_buf[512 + k]?) ∧
                                  (FullMem c sr ⋆ R) mr)
                                ?_ ?_
                              · rintro Lr rem_r ⟨jr, ⟨⟩⟩ mr hLr
                                  ⟨scr_r, hscr, hjr_le, rfl, hp_r, hn64_r, hn512_r, hmr⟩
                                c0_hsplit
                                · have hjr_lt : jr.toNat < nn.toNat := hc
                                  have h64_sc :
                                      ((64 + jr : BitVec 32).setWidth 64).toNat < scr_r.length := by
                                    rw [hscr, m6_zext32_toNat, BitVec.toNat_add,
                                      show (64 : BitVec 32).toNat = 64 from rfl,
                                      Nat.mod_eq_of_lt (by omega)]; omega
                                  have h512_sc : ((512 + jr : BitVec 32).setWidth 64).toNat <
                                      scr_r.length := by
                                    rw [hscr, m6_zext32_toNat, BitVec.toNat_add,
                                      show (512 : BitVec 32).toNat = 512 from rfl,
                                      Nat.mod_eq_of_lt (by omega)]; omega
                                  have hjr1 : (jr + 1#32).toNat = jr.toNat + 1 := by c0_bound
                                  have h64_eq : ((64 + jr : BitVec 32).setWidth 64).toNat =
                                      64 + jr.toNat := by
                                    rw [m6_zext32_toNat, BitVec.toNat_add,
                                      show (64 : BitVec 32).toNat = 64 from rfl,
                                      Nat.mod_eq_of_lt (by omega)]
                                  have h512_eq : ((512 + jr : BitVec 32).setWidth 64).toNat =
                                      512 + jr.toNat := by
                                    rw [m6_zext32_toNat, BitVec.toNat_add,
                                      show (512 : BitVec 32).toNat = 512 from rfl,
                                      Nat.mod_eq_of_lt (by omega)]
                                  c0_hsteps!
                                  exact hLr (nn.toNat - (jr + 1#32).toNat) (jr + 1#32, ()) _
                                    (by omega) ⟨_, by simp [hscr], by omega, rfl,
                                      fun k hk => by
                                        rw [show ((512 + jr : BitVec 32).setWidth 64).toNat =
                                            512 + jr.toNat from h512_eq,
                                          List.getElem?_set_ne (by omega)]
                                        exact hp_r k hk,
                                      fun k hk => by
                                        rw [show ((512 + jr : BitVec 32).setWidth 64).toNat =
                                            512 + jr.toNat from h512_eq,
                                          List.getElem?_set_ne (by omega)]
                                        exact hn64_r k hk,
                                      fun k hk => by
                                        rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp (hjr1 ▸ hk))
                                          with h | h
                                        · rw [show ((512 + jr : BitVec 32).setWidth 64).toNat =
                                              512 + jr.toNat from h512_eq,
                                            List.getElem?_set_ne (by omega)]
                                          exact hn512_r k h
                                        · subst h
                                          rw [show ((512 + jr : BitVec 32).setWidth 64).toNat =
                                              512 + jr.toNat from h512_eq,
                                            List.getElem?_set_self (by rw [hscr]; omega)]
                                          rw [m6_getElem_congr h64_eq h64_sc (by rw [hscr]; omega),
                                            ← List.getElem?_eq_getElem (by rw [hscr]; omega)]
                                          exact hn64_r jr.toNat hjr_lt, hm⟩
                                · have hjr_eq : jr.toNat = nn.toNat := by omega
                                  c0_hsteps_nogrp
                                  -- Zero `scr[1024 ..< 1058)` and write masks if non-zero
                                  refine wp_loop_group (ts := [i32])
                                    (fun rem_z (kz, ()) mz => ∃ scr_z : List (BitVec 32),
                                      let sz' : FullState :=
                                        { sd1 with scratch := { sd1.scratch with
                                          scratch_buf := scr_z } }
                                      scr_z.length = c.scratch_cap ∧ kz.toNat ≤ 34 ∧
                                      rem_z = 34 - kz.toNat ∧
                                      (∀ k < np.toNat, scr_z[k]? = s0.scratch.scratch_buf[k]?) ∧
                                      (∀ k < nn.toNat,
                                        scr_z[512 + k]? = s0.scratch.scratch_buf[512 + k]?) ∧
                                      (FullMem c sz' ⋆ R) mz)
                                    ?_ ?_
                                  · rintro Lz rem_z ⟨kz, ⟨⟩⟩ mz hLz
                                      ⟨scr_z, hscz, hkz_le, rfl, hp_z, hn_z, hmz⟩
                                    c0_hsplit
                                    · have hkz_lt : kz.toNat < 34 := hc
                                      have hidx : ((1024#32 + kz).setWidth 64).toNat <
                                          scr_z.length := by
                                        rw [hscz, m6_zext32_toNat]; c0_bound
                                      have hkz1 : (kz + 1#32).toNat = kz.toNat + 1 := by c0_bound
                                      c0_hsteps!
                                      exact hLz (34 - (kz + 1#32).toNat) (kz + 1#32, ()) _
                                        (by omega) ⟨_, by simp [hscz], by omega, rfl,
                                         fun k hk => by
                                           rw [List.getElem?_set_ne (by
                                             rw [m6_zext32_toNat]; c0_bound)]
                                           exact hp_z k hk,
                                         fun k hk => by
                                           rw [List.getElem?_set_ne (by
                                             rw [m6_zext32_toNat]; c0_bound)]
                                           exact hn_z k hk, hm⟩
                                    · c0_hsteps_nogrp
                                      refine wp_join0 (P := fun mj => ∃ sf : FullState,
                                          FullDenseInvW c F0 F_cur sf ∧ TmkZero sf ∧
                                          sf.core.cur_vars = s0.core.cur_vars ∧
                                          sf.core.arena = s0.core.arena ∧
                                          sf.core.arena_len = s0.core.arena_len ∧
                                          sf.core.fuel.toNat ≤ s0.core.fuel.toNat ∧
                                          (∀ k < np.toNat,
                                            sf.scratch.scratch_buf[k]? =
                                              s0.scratch.scratch_buf[k]?) ∧
                                          (∀ k < nn.toNat,
                                            sf.scratch.scratch_buf[512 + k]? =
                                              s0.scratch.scratch_buf[512 + k]?) ∧
                                          (FullMem c sf ⋆ R) mj)
                                        (by
                                          rintro _ mj ⟨sf, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
                                          c0_hsteps!
                                          exact hJ18 (_, _, sf) mj
                                            ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩)
                                        (fun J61 hJ61 => by
                                          c0_hsplit
                                          · have h1024 : 1024 < scr_z.length := by omega
                                            have h1025 : 1025 < scr_z.length := by omega
                                            have h1040 : 1040 < scr_z.length := by omega
                                            have h1041 : 1041 < scr_z.length := by omega
                                            have h1056 : 1056 < scr_z.length := by omega
                                            have h1057 : 1057 < scr_z.length := by omega
                                            have h1024_e : (1024#64).toNat = 1024 := rfl
                                            have h1025_e : (1025#64).toNat = 1025 := rfl
                                            have h1040_e : (1040#64).toNat = 1040 := rfl
                                            have h1041_e : (1041#64).toNat = 1041 := rfl
                                            have h1056_e : (1056#64).toNat = 1056 := rfl
                                            have h1057_e : (1057#64).toNat = 1057 := rfl
                                            c0_hsteps!
                                            refine hJ61 _ ⟨_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hm⟩
                                            · exact m6_fullDenseInvW_set_scratch hdwd1
                                                (by simp [hscz])
                                            · exact htmk1
                                            · exact hcv1
                                            · exact har1
                                            · exact hal1
                                            · exact hfl1
                                            · intro k hk
                                              rw [List.getElem?_set_ne (by rw [h1057_e]; omega),
                                                List.getElem?_set_ne (by rw [h1056_e]; omega),
                                                List.getElem?_set_ne (by rw [h1041_e]; omega),
                                                List.getElem?_set_ne (by rw [h1040_e]; omega),
                                                List.getElem?_set_ne (by rw [h1025_e]; omega),
                                                List.getElem?_set_ne (by rw [h1024_e]; omega)]
                                              exact hp_z k hk
                                            · intro k hk
                                              rw [List.getElem?_set_ne (by rw [h1057_e]; omega),
                                                List.getElem?_set_ne (by rw [h1056_e]; omega),
                                                List.getElem?_set_ne (by rw [h1041_e]; omega),
                                                List.getElem?_set_ne (by rw [h1040_e]; omega),
                                                List.getElem?_set_ne (by rw [h1025_e]; omega),
                                                List.getElem?_set_ne (by rw [h1024_e]; omega)]
                                              exact hn_z k hk
                                          · c0_hsteps!
                                            exact hJ61 mz ⟨_,
                                              m6_fullDenseInvW_set_scratch hdwd1 hscz,
                                              htmk1, hcv1, har1, hal1, hfl1, hp_z, hn_z, hmz⟩)
                                  · intro Lz hLz; c0_hsteps!
                                    exact hLz 34 (0#32, ()) mr
                                      ⟨scr_r, hscr, Nat.zero_le _, by simp, hp_r,
                                       fun k hk => hn512_r k (by omega), hmr⟩
                              · intro Lr hLr; c0_hsteps!
                                exact hLr nn.toNat (0#32, ()) md1
                                  ⟨sd1.scratch.scratch_buf, hdwd1.1.scratch_ok.scratch_buf_len,
                                   Nat.zero_le _, by simp,
                                   fun k hk => (hscr1 k (by omega) (Or.inl (by omega))).trans
                                     (hp_d0 k hk),
                                   fun k hk => (hscr1 (64 + k) (by omega) (Or.inl (by omega))).trans
                                     (hn_d0 k hk),
                                   fun _ h => by simp at h, hmd1⟩
                          · intro Lc hLc; c0_hsteps!
                            exact hLc nn.toNat (0#32, ()) m3
                              ⟨scr3, hsc3, Nat.zero_le _, by simp,
                               fun k hk => hkeep3 k (by omega),
                               fun _ h => by have : (0#32).toNat = 0 := rfl; omega,
                               fun k hk => hkeep3 (512 + k) (by omega), hm3⟩
                        · c0_hsteps!
                          exact hJ18 (_, _, s3) m3 ⟨hdw3, htmk0, rfl, rfl, rfl, Nat.le_refl _,
                            fun k hk => hkeep3 k (by omega),
                            fun k hk => hkeep3 (512 + k) (by omega), hm3⟩
                      · c0_hsteps!
                        exact hJ18 (_, _, s3) m3 ⟨hdw3, htmk0, rfl, rfl, rfl, Nat.le_refl _,
                          fun k hk => hkeep3 k (by omega),
                          fun k hk => hkeep3 (512 + k) (by omega), hm3⟩
                    · c0_hsteps!
                      exact hJ18 (_, _, s3) m3 ⟨hdw3, htmk0, rfl, rfl, rfl, Nat.le_refl _,
                        fun k hk => hkeep3 k (by omega),
                        fun k hk => hkeep3 (512 + k) (by omega), hm3⟩)
          · intro L2 hL2; c0_hsteps!
            exact hL2 nn.toNat (0#32, ()) m1 ⟨lm1, scr1, hdw1, Nat.zero_le _, by simp, hkeep1, hm1⟩
      · intro L1 hL1; c0_hsteps!
        exact hL1 np.toNat (0#32, ()) mk
          ⟨s0.core.lit_mark, scr0,
           m6_fullDenseInvW_with_scratch hdw0
             { hdw0.1.scratch_ok with scratch_buf_len := hsc0 } rfl rfl,
           Nat.zero_le _, by simp, hkeep0, hmk⟩
  · intro L0 hL0; c0_hsteps!
    exact hL0 34 (0#32, ()) m0
      ⟨s0.scratch.scratch_buf, hdw0.1.scratch_ok.scratch_buf_len, Nat.zero_le _, by simp,
       fun _ _ => rfl, hm0⟩

end LeanQbe.T.Examples.Kissat.FullM6BveFwd
