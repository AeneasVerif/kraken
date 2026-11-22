module

public import LeanQbe.T.Examples.Kissat.FullM6WatchGcProof1b
public import LeanQbe.T.Examples.Kissat.FullM6WatchGcProof2b
public meta import Lean.Elab.Tactic
public meta import LeanQbe.T.Logic.C0Step

/-!
# Kissat M6 `PR-W2E-lite` Proofs Part 2c: `full_move_red_end_m6_wp` & Sweep Helpers

Proves pure prefix-validation, `WatchSliceLtOk`/`FullWitnessInv`, `MoveRangeChain` concatenation,
and `fullMoveRedEndSpec` -> `CompactPrefixOk`/`SweepReasonMapInv` bridge lemmas, followed by
`full_move_red_end_m6_wp` unifying the `scratch_buf`, in-place `ar + dst`, and `PH_RSN`-clear
fallback branches.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM6WatchGc

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat.Full
open FullReduceSpecs FullReduceHelpers
open Kraken.Bedrock2.Test
open scoped FullArenaTactics FullReduceTactics M6Tactics1 M6Tactics2a

local macro "m6_tiny_simp" : tactic =>
  `(tactic| simp only [
      LeanQbe.T.op1_eq_mk, LeanQbe.T.op2_eq_mk,
      LeanQbe.T.wp_let_add_eq, LeanQbe.T.wp_let_mul_eq, LeanQbe.T.wp_let_and_eq,
      LeanQbe.T.wp_let_cmp_eq, LeanQbe.T.wp_let_zext_eq, LeanQbe.T.wp_let_sext_eq,
      LeanQbe.T.wp_let_trunc_eq,
      LeanQbe.T.OpCode.eq, LeanQbe.T.OpCode.ne, LeanQbe.T.OpCode.ult, LeanQbe.T.OpCode.sgt,
      LeanQbe.T.vals_nil, LeanQbe.T.vals_cons, LeanQbe.T.Arg.val_var, LeanQbe.T.Arg.val_imm,
      LeanQbe.T.Ty.hasFloat_vec, LeanQbe.T.Ty.hasFloat, LeanQbe.T.Ty.isFloatTree,
      LeanQbe.T.evalBits_eq_beq, LeanQbe.T.evalBits_ne_bne,
      LeanQbe.T.evalBits_ult_eq, LeanQbe.T.evalBits_sgt_eq,
      LeanQbe.T.lift1, LeanQbe.T.lift2, LeanQbe.T.liftCmp,
      cast_eq, Bool.false_eq_true, ite_false, ite_true,
      BitVec.reduceSignExtend, BitVec.reduceSetWidth, BitVec.reduceAdd, BitVec.reduceMul])

local macro "m6_tiny_lets" : tactic =>
  `(tactic| (
    try m6_unmdata
    try repeat (first | (m6_strip; try m6_tiny_simp) | m6_tiny_simp)))

local macro "m6_fast" : tactic => `(tactic| (m6_tiny_lets; m6_steps))

/-! ## 1. `CleanIrredChain` Prefix Validation & `PH_RSN`-Clear Helpers -/

/-- Valid irredundant non-garb, non-shrk prefix chain `[lo, hi)` checked by `full_arena_sweep_m6`
when `h->first_reducible > 0`. Note `0x00C80000 = PH_SHRK | PH_RED | PH_GARB`. -/
inductive CleanIrredChain (ar : List (BitVec 32)) : Nat → Nat → Prop where
  | empty {p} : CleanIrredChain ar p p
  | step {p hi} :
      p + 3 ≤ hi → (ar[p]?.getD 0#32 &&& 0x00C80000#32) = 0#32 →
      3 ≤ (ar[p + 2]?.getD 0#32).toNat →
      p + 3 + (ar[p + 2]?.getD 0#32).toNat ≤ hi →
      CleanIrredChain ar (p + 3 + (ar[p + 2]?.getD 0#32).toNat) hi →
      CleanIrredChain ar p hi

theorem CleanIrredChain.le {ar : List (BitVec 32)} {lo hi : Nat}
    (h : CleanIrredChain ar lo hi) : lo ≤ hi := by
  induction h with
  | empty => exact Nat.le_refl _
  | step _ _ _ _ _ ih => omega

theorem CleanIrredChain.snoc {ar : List (BitVec 32)} {lo p p' : Nat}
    (h : CleanIrredChain ar lo p) (hp3 : p + 3 ≤ p')
    (hfl : (ar[p]?.getD 0#32 &&& 0x00C80000#32) = 0#32)
    (hsz : 3 ≤ (ar[p + 2]?.getD 0#32).toNat)
    (hp_eq : p + 3 + (ar[p + 2]?.getD 0#32).toNat = p') :
    CleanIrredChain ar lo p' := by
  induction h with
  | empty => exact .step hp3 hfl hsz (le_of_eq hp_eq) (by rw [hp_eq]; exact .empty)
  | @step a hi ha3 hafl hasz hafit _ ih =>
    have hhi : hi ≤ p' := by omega
    exact .step (Nat.le_trans ha3 hhi) hafl hasz (Nat.le_trans hafit hhi) (ih hp3 hfl hsz hp_eq)

theorem bv32_mask_00C80000_props (x : BitVec 32)
    (h : (x &&& 0x00C80000#32) = 0#32) :
    (x &&& 0x00800000#32) = 0#32 ∧ (x &&& 0x00080000#32) = 0#32 ∧
    (x &&& 0x00400000#32) = 0#32 ∧ (x &&& 0x00880000#32) = 0#32 := by
  have hbit : ∀ m : BitVec 32, (0x00C80000#32 &&& m) = m → (x &&& m) = 0#32 := fun m hm => by
    have h1 : (x &&& (0x00C80000#32 &&& m)) = 0#32 := by
      rw [← BitVec.and_assoc, h, BitVec.zero_and]
    rwa [hm] at h1
  exact ⟨hbit 0x00800000#32 rfl, hbit 0x00080000#32 rfl,
    hbit 0x00400000#32 rfl, hbit 0x00880000#32 rfl⟩

theorem bv32_clear_rsn_keeps_clean (x : BitVec 32) :
    ((x &&& ~~~0x00200000#32) &&& 0x00C80000#32) = (x &&& 0x00C80000#32) := by
  rw [BitVec.and_assoc]; rfl

private theorem clean_nextOff_eq {ar : List (BitVec 32)} {p hi alen : Nat}
    (_hp3 : p + 3 ≤ hi) (hfl : (ar[p]?.getD 0#32 &&& 0x00C80000#32) = 0#32)
    (hfit : p + 3 + (ar[p + 2]?.getD 0#32).toNat ≤ hi) (hle : hi ≤ alen) :
    fullArenaNextOff ar alen p = p + 3 + (ar[p + 2]?.getD 0#32).toNat := by
  have hsh := (bv32_mask_00C80000_props _ hfl).1
  unfold fullArenaNextOff
  have h1 : ¬ (p + 3 > alen) := by omega
  have h2 : ¬ (p + 3 + (ar[p + 2]?.getD 0#32).toNat > alen) := by omega
  simp [h1, h2, hsh]

theorem cleanIrredChain_mem_next {c : FullCfg} {F_cur : List (List Nat)}
    {k : FullCoreState} {p fp : Nat} (ha : FullArenaClausesInv c F_cur k)
    (hc : CleanIrredChain k.arena p fp) (hfp : fp < k.arena_len)
    (hp : p ∈ fullArenaClauseRefsCore k) :
    fp ∈ fullArenaClauseRefsCore k ∧
    (∀ fuel, fp - p ≤ fuel → ∀ r ∈ fullArenaScanRefs k.arena fp p fuel,
      r ∈ fullArenaClauseRefsCore k ∧ r < fp ∧
      (k.arena[r]?.getD 0#32 &&& 0x00C80000#32) = 0#32 ∧
      3 ≤ (k.arena[r + 2]?.getD 0#32).toNat ∧
      r + 3 + (k.arena[r + 2]?.getD 0#32).toNat ≤ fp) ∧
    (∀ r ∈ fullArenaClauseRefsCore k, p ≤ r → r < fp →
      r ∈ fullArenaScanRefs k.arena fp p (fp - p)) := by
  induction hc with
  | empty =>
    refine ⟨hp, fun fuel _ r hr => ?_, fun _ h1 h2 => by omega⟩
    cases fuel with
    | zero => simp [fullArenaScanRefs] at hr
    | succ f =>
      unfold fullArenaScanRefs at hr
      split at hr
      · omega
      · contradiction
  | @step p fp hp3 hfl hsz hfit htl ih =>
    let nxt := p + 3 + (k.arena[p + 2]?.getD 0#32).toNat
    have hnxt_al : fullArenaNextOff k.arena k.arena_len p = nxt :=
      clean_nextOff_eq hp3 hfl hfit (by omega)
    have hnxt_fp : fullArenaNextOff k.arena fp p = nxt :=
      clean_nextOff_eq hp3 hfl hfit (Nat.le_refl fp)
    have hnxt_mem : nxt ∈ fullArenaClauseRefsCore k := by
      have hor := fullArenaClauseRefs_next_or_end ha hp
      rw [hnxt_al] at hor
      exact hor.resolve_left (by have := htl.le; omega)
    obtain ⟨hfp_mem, ih_fwd, ih_bwd⟩ := ih hfp hnxt_mem
    refine ⟨hfp_mem, fun fuel hf r hr => ?_, fun r hr hpr hrlt => ?_⟩
    · cases fuel with
      | zero => omega
      | succ f =>
        unfold fullArenaScanRefs at hr
        simp only [hp3, ↓reduceIte, hnxt_fp, List.mem_cons] at hr
        rcases hr with rfl | hrest
        · exact ⟨hp, by omega, hfl, hsz, hfit⟩
        · exact ih_fwd f (by omega) r hrest
    · rcases Nat.eq_or_lt_of_le hpr with rfl | hlt
      · have hsub : fp - p = (fp - p - 1) + 1 := by omega
        rw [hsub]; unfold fullArenaScanRefs; simp [hp3]
      · have hdisj := fullArenaScanRefs_disjoint hp hr hlt
        rw [hnxt_al] at hdisj
        have hsub : fp - p = (fp - p - 1) + 1 := by omega
        rw [hsub]; unfold fullArenaScanRefs
        simp only [hp3, ↓reduceIte, hnxt_fp, List.mem_cons]
        right
        rw [fullArenaScanRefs_fuel_ge (f1 := fp - p - 1) (f2 := fp - nxt)
          (by omega) (Nat.le_refl _)]
        exact ih_bwd r hr hdisj hrlt

theorem cleanIrredChain_disjoint_lt {ar : List (BitVec 32)} {lo cp fp : Nat}
    (hc1 : CleanIrredChain ar lo cp) (hc2 : CleanIrredChain ar cp fp) :
    ∀ r ∈ fullArenaScanRefs ar fp lo fp, r < cp →
      r + 3 + (ar[r + 2]?.getD 0#32).toNat ≤ cp := by
  have hle2 := hc2.le
  suffices h : ∀ p hi, hi ≤ fp → CleanIrredChain ar p hi →
      ∀ r ∈ fullArenaScanRefs ar fp p (fp - p), r < hi →
        r + 3 + (ar[r + 2]?.getD 0#32).toNat ≤ hi by
    intro r hr hrcp
    have hf : r ∈ fullArenaScanRefs ar fp lo (fp - lo) := by
      rwa [fullArenaScanRefs_fuel_ge (f1 := fp - lo) (f2 := fp) (Nat.le_refl _) (by omega)]
    exact h lo cp hle2 hc1 r hf hrcp
  intro p hi hhi hc1'
  induction hc1' with
  | empty => intro r hr hrcp; have hbd := fullArenaScanRefs_mem_bounds hr; omega
  | @step p hi hp3 hfl hsz hfit _ ih =>
    intro r hr hrcp
    have hp3f : p + 3 ≤ fp := by omega
    have hsub : fp - p = (fp - p - 1) + 1 := by omega
    have hnxt_fp : fullArenaNextOff ar fp p = p + 3 + (ar[p + 2]?.getD 0#32).toNat :=
      clean_nextOff_eq hp3 hfl hfit hhi
    rw [hsub] at hr; unfold fullArenaScanRefs at hr
    simp only [hp3f, ↓reduceIte, hnxt_fp, List.mem_cons] at hr
    rcases hr with rfl | hrest
    · exact hfit
    · rw [fullArenaScanRefs_fuel_ge (f1 := fp - p - 1)
          (f2 := fp - (p + 3 + (ar[p + 2]?.getD 0#32).toNat))
          (by omega) (Nat.le_refl _)] at hrest
      exact ih hhi r hrest hrcp

private theorem scanRefs_split_at {ar : List (BitVec 32)} {alen fp : Nat}
    (hfp : fp ≤ alen) :
    ∀ fuel pos, fp - pos ≤ fuel →
      (pos = fp ∨ (pos + 3 ≤ fp ∧
        (∀ r ∈ fullArenaScanRefs ar fp pos fuel,
          fullArenaNextOff ar alen r = fullArenaNextOff ar fp r ∧
          (fullArenaNextOff ar fp r = fp ∨ fullArenaNextOff ar fp r + 3 ≤ fp)))) →
      fullArenaScanRefs ar alen pos (fuel + (alen - fp)) =
        fullArenaScanRefs ar fp pos fuel ++ fullArenaScanRefs ar alen fp (alen - fp) := by
  intro fuel
  induction fuel with
  | zero =>
    intro pos hf hpos
    rcases hpos with rfl | ⟨hle, _⟩
    · simp [fullArenaScanRefs]
    · omega
  | succ f ih =>
    intro pos hf hpos
    rcases hpos with rfl | ⟨hle, hstep⟩
    · have hnot : ¬ (pos + 3 ≤ pos) := by omega
      have h0 : fullArenaScanRefs ar pos pos (f + 1) = [] := by
        unfold fullArenaScanRefs; simp [hnot]
      rw [h0, List.nil_append]
      exact fullArenaScanRefs_fuel_ge (by omega) (Nat.le_refl _)
    · have hp_al : pos + 3 ≤ alen := by omega
      have hloc := hstep pos (by simp [fullArenaScanRefs, hle])
      have hb := fullArenaNextOff_bounds (ar := ar) (alen := fp) (cref := pos) hle
      have hplus : f + 1 + (alen - fp) = (f + (alen - fp)) + 1 := by omega
      have hL : fullArenaScanRefs ar alen pos (f + 1 + (alen - fp)) =
          pos :: fullArenaScanRefs ar alen (fullArenaNextOff ar fp pos) (f + (alen - fp)) := by
        rw [hplus, fullArenaScanRefs.eq_2]; simp [hp_al, hloc.1]
      have hR : fullArenaScanRefs ar fp pos (f + 1) =
          pos :: fullArenaScanRefs ar fp (fullArenaNextOff ar fp pos) f := by
        rw [fullArenaScanRefs.eq_2]; simp [hle]
      rw [hL, hR, List.cons_append]
      congr 1
      refine ih (fullArenaNextOff ar fp pos) (by omega) ?_
      rcases hloc.2 with heq | h3
      · exact Or.inl heq
      · exact Or.inr ⟨h3, fun r hr => hstep r (by rw [hR, List.mem_cons]; exact Or.inr hr)⟩

theorem prefix_cleared_ok {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {k : FullCoreState} {ar' : List (BitVec 32)} {fp : Nat}
    (hlen : k.LengthsOk c) (hw : FullWitnessInv c F0 F_cur k)
    (hnd : ∀ r ∈ fullArenaClauseRefsCore k, fullArenaClauseGarbCore k r = false →
      ((fullArenaClauseLitsCore k r).map (· / 2)).Nodup)
    (hfp_pos : 0 < fp) (hfp_lt : fp < k.arena_len)
    (hc0 : CleanIrredChain k.arena 0 fp) (har' : ar'.length = c.arena_cap)
    (htail : ∀ i, fp ≤ i → i < k.arena_len → ar'[i]? = k.arena[i]?)
    (hmatch : ∀ r ∈ fullArenaClauseRefsCore { k with arena_len := fp },
      (ar'[r]?.getD 0#32 &&& 0x00C80000#32) = 0#32 ∧
      ar'[r + 2]? = k.arena[r + 2]? ∧
      ∀ j < (k.arena[r + 2]?.getD 0#32).toNat, ar'[r + 3 + j]? = k.arena[r + 3 + j]?) :
    let k' : FullCoreState := { k with arena := ar' }
    fp ∈ fullArenaClauseRefsCore k' ∧
    CompactPrefixOk c F_cur s k' fp ∧
    SweepReasonMapInv k k' fp fp ∧
    FullWitnessInv c F0 F_cur k' ∧
    (∀ r ∈ fullArenaClauseRefsCore k', fullArenaClauseGarbCore k' r = false →
      ((fullArenaClauseLitsCore k' r).map (· / 2)).Nodup) ∧
    (∀ r ∈ fullArenaClauseRefsCore k', fp ≤ r → ar'[r]? = k.arena[r]?) := by
  intro k'
  have h0_mem : 0 ∈ fullArenaClauseRefsCore k :=
    fullArenaClauseRefs_zero_mem hw.arena (by omega)
  obtain ⟨hfp_mem, hfwd0, hbwd0⟩ := cleanIrredChain_mem_next hw.arena hc0 hfp_lt h0_mem
  have hlen_fp : 0 + 3 ≤ fp := by
    cases hc0 with
    | empty => omega
    | step hp3 _ _ _ _ => exact hp3
  have hstep_fp : ∀ r ∈ fullArenaScanRefs k.arena fp 0 fp,
      fullArenaNextOff k.arena k.arena_len r = fullArenaNextOff k.arena fp r ∧
      (fullArenaNextOff k.arena fp r = fp ∨ fullArenaNextOff k.arena fp r + 3 ≤ fp) := by
    intro r hr
    obtain ⟨hr_mem, hr_lt, hfl, hsz, hfit⟩ := hfwd0 fp (Nat.le_refl fp) r hr
    have hna := clean_nextOff_eq (by omega) hfl hfit (Nat.le_of_lt hfp_lt)
    have hnf := clean_nextOff_eq (by omega) hfl hfit (Nat.le_refl fp)
    refine ⟨hna.trans hnf.symm, ?_⟩
    rw [hnf]
    by_cases he : r + 3 + (k.arena[r + 2]?.getD 0#32).toNat = fp
    · exact Or.inl he
    · right
      have hnxt_mem : r + 3 + (k.arena[r + 2]?.getD 0#32).toNat ∈
          fullArenaClauseRefsCore k := by
        have hor := fullArenaClauseRefs_next_or_end hw.arena hr_mem
        rw [hna] at hor; exact hor.resolve_left (by omega)
      have hnxt_in := hbwd0 _ hnxt_mem (by omega) (by omega)
      have hnxt_f := hfwd0 fp (Nat.le_refl fp) _ hnxt_in
      omega
  have hrefs_fp_eq : fullArenaClauseRefsCore { k' with arena_len := fp } =
      fullArenaClauseRefsCore { k with arena_len := fp } := by
    refine fullArenaClauseRefsCore_congr
      (k1 := { k with arena_len := fp }) (k2 := { k' with arena_len := fp }) rfl fun r hr => ?_
    obtain ⟨hfl', hr2', _⟩ := hmatch r hr
    obtain ⟨_, hr_lt, hfl, hsz, hfit⟩ := hfwd0 fp (Nat.le_refl fp) r hr
    have h1 := clean_nextOff_eq (by omega) hfl' (by rw [hr2']; exact hfit) (Nat.le_refl fp)
    have h2 := clean_nextOff_eq (by omega) hfl hfit (Nat.le_refl fp)
    rw [h1, h2, hr2']
  have hmeta_fp : ∀ r ∈ fullArenaClauseRefsCore { k' with arena_len := fp },
      r ∈ fullArenaClauseRefsCore k ∧ r < fp ∧
      (ar'[r]?.getD 0#32 &&& 0x00800000#32) = 0#32 ∧
      (ar'[r]?.getD 0#32 &&& 0x00080000#32) = 0#32 ∧
      fullArenaClauseSizeCore { k' with arena_len := fp } r =
        fullArenaClauseSizeCore k r ∧
      fullArenaClauseGarbCore { k' with arena_len := fp } r = false ∧
      fullArenaClauseLitsCore { k' with arena_len := fp } r =
        fullArenaClauseLitsCore k r := by
    intro r hr; rw [hrefs_fp_eq] at hr
    obtain ⟨hr_k, hr_lt, hfl, hsz, hfit⟩ := hfwd0 fp (Nat.le_refl fp) r hr
    obtain ⟨hfl', hr2', hlits'⟩ := hmatch r hr
    have hbits := bv32_mask_00C80000_props _ hfl'
    have hsz_eq : fullArenaClauseSizeCore { k' with arena_len := fp } r =
        fullArenaClauseSizeCore k r := by
      unfold fullArenaClauseSizeCore; dsimp only [k']; rw [hr2']
    have hgarb' : fullArenaClauseGarbCore { k' with arena_len := fp } r = false := by
      unfold fullArenaClauseGarbCore fullArenaHdrCore; dsimp only [k']; simp [hbits.2.1]
    have hlits_eq : fullArenaClauseLitsCore { k' with arena_len := fp } r =
        fullArenaClauseLitsCore k r :=
      fullArenaClauseLitsCore_eq_of_hold
        (by unfold fullArenaClauseSizeCore
            have := hlen.arena_len_le; have := hlen.arena_len_arr; omega)
        (by unfold fullArenaClauseSizeCore; dsimp only [k']; rw [har']
            have := hlen.arena_len_le; omega)
        hsz_eq (fun j hj => hlits' j hj)
    exact ⟨hr_k, hr_lt, hbits.1, hbits.2.1, hsz_eq, hgarb', hlits_eq⟩
  have ha_fp : FullArenaClausesInv c F_cur { k' with arena_len := fp } := by
    refine ⟨Or.inr hlen_fp, fun r hr => ?_, fun r hr hsh => ?_, fun r hr _ l hl => ?_,
        fun r hr _ => ?_⟩
    · obtain ⟨hr_k, hr_lt, hsh', hgb', hsz', _, _⟩ := hmeta_fp r hr
      rw [hrefs_fp_eq] at hr
      obtain ⟨_, _, _, hsz, hfit⟩ := hfwd0 fp (Nat.le_refl fp) r hr
      obtain ⟨hfl', hr2', _⟩ := hmatch r hr
      have hnxt := clean_nextOff_eq (ar := ar') (by omega) hfl' (by rw [hr2']; exact hfit)
        (Nat.le_refl fp)
      have hsz_ar' : (ar'[r + 2]?.getD 0#32).toNat = (k.arena[r + 2]?.getD 0#32).toNat := by
        rw [hr2']
      rw [hnxt]; dsimp only [k', fullArenaClauseSizeCore]; rw [hsz_ar']
      have hor := (hstep_fp r hr).2; rw [clean_nextOff_eq (by omega)
        (hfwd0 fp (Nat.le_refl fp) r hr).2.2.1 hfit (Nat.le_refl fp)] at hor
      exact ⟨by omega, hsz, Nat.le_refl _, hfit, hor⟩
    · exact absurd (hmeta_fp r hr).2.2.1 hsh
    · obtain ⟨hr_k, _, _, _, _, _, hlits'⟩ := hmeta_fp r hr
      rw [hlits'] at hl
      have hr_fp : r ∈ fullArenaClauseRefsCore { k with arena_len := fp } :=
        hrefs_fp_eq ▸ hr
      have hgk : fullArenaClauseGarbCore k r = false := by
        unfold fullArenaClauseGarbCore fullArenaHdrCore
        have hfl := (hfwd0 fp (Nat.le_refl fp) r hr_fp).2.2.1
        simp [(bv32_mask_00C80000_props _ hfl).2.1]
      exact hw.arena.lits_lt r hr_k hgk l hl
    · obtain ⟨hr_k, _, _, _, _, _, hlits'⟩ := hmeta_fp r hr
      rw [hlits']
      have hr_fp : r ∈ fullArenaClauseRefsCore { k with arena_len := fp } :=
        hrefs_fp_eq ▸ hr
      have hgk : fullArenaClauseGarbCore k r = false := by
        unfold fullArenaClauseGarbCore fullArenaHdrCore
        have hfl := (hfwd0 fp (Nat.le_refl fp) r hr_fp).2.2.1
        simp [(bv32_mask_00C80000_props _ hfl).2.1]
      exact hw.arena.entails r hr_k hgk
  have hscan_k : fullArenaClauseRefsCore k =
      fullArenaClauseRefsCore { k with arena_len := fp } ++
      fullArenaScanRefs k.arena k.arena_len fp (k.arena_len - fp) := by
    unfold fullArenaClauseRefsCore
    have hsp := scanRefs_split_at (ar := k.arena) (alen := k.arena_len) (fp := fp)
      (Nat.le_of_lt hfp_lt) fp 0 (Nat.le_refl fp) (Or.inr ⟨hlen_fp, hstep_fp⟩)
    rw [fullArenaScanRefs_fuel_ge (f1 := k.arena_len) (f2 := fp + (k.arena_len - fp))
      (Nat.le_refl _) (by omega)]
    exact hsp
  have htail_scan : fullArenaScanRefs ar' k.arena_len fp (k.arena_len - fp) =
      fullArenaScanRefs k.arena k.arena_len fp (k.arena_len - fp) := by
    apply fullArenaScanRefs_congr
    intro r hr
    have hmem_tail : r ∈ fullArenaClauseRefsCore k := by
      rw [hscan_k, List.mem_append]; exact Or.inr hr
    have hbd := fullArenaScanRefs_mem_bounds hr
    have hwf := hw.arena.refs_wf r hmem_tail
    refine fullArenaNextOff_congr_block (htail r hbd.1 (by omega))
      (htail (r + 2) (by omega) (by omega)) (fun i hi1 hi2 => htail i (by omega) (by omega))
  have hscan_k' : fullArenaClauseRefsCore k' =
      fullArenaClauseRefsCore { k' with arena_len := fp } ++
      fullArenaScanRefs ar' k.arena_len fp (k.arena_len - fp) := by
    have ha_fp_step : ∀ r ∈ fullArenaScanRefs ar' fp 0 fp,
        fullArenaNextOff ar' k.arena_len r = fullArenaNextOff ar' fp r ∧
        (fullArenaNextOff ar' fp r = fp ∨ fullArenaNextOff ar' fp r + 3 ≤ fp) := by
      intro r hr
      have hrk : r ∈ fullArenaClauseRefsCore { k with arena_len := fp } := by
        rw [← hrefs_fp_eq]; exact hr
      obtain ⟨hfl', hr2', _⟩ := hmatch r hrk
      obtain ⟨_, _, hfl, hsz, hfit⟩ := hfwd0 fp (Nat.le_refl fp) r hrk
      have h1 := clean_nextOff_eq (ar := ar') (by omega) hfl' (by rw [hr2']; exact hfit)
        (Nat.le_of_lt hfp_lt)
      have h2 := clean_nextOff_eq (ar := ar') (by omega) hfl' (by rw [hr2']; exact hfit)
        (Nat.le_refl fp)
      refine ⟨h1.trans h2.symm, ?_⟩
      have hor := (hstep_fp r hrk).2
      rw [clean_nextOff_eq (by omega) hfl hfit (Nat.le_refl fp)] at hor
      rwa [h2, hr2']
    have hsp := scanRefs_split_at (ar := ar') (alen := k.arena_len) (fp := fp)
      (Nat.le_of_lt hfp_lt) fp 0 (Nat.le_refl fp) (Or.inr ⟨hlen_fp, ha_fp_step⟩)
    unfold fullArenaClauseRefsCore; dsimp only [k']
    rw [fullArenaScanRefs_fuel_ge (f1 := k.arena_len) (f2 := fp + (k.arena_len - fp))
      (Nat.le_refl _) (by omega)]
    exact hsp
  have hrefs_k_eq : fullArenaClauseRefsCore k' = fullArenaClauseRefsCore k := by
    rw [hscan_k', htail_scan, hrefs_fp_eq, hscan_k]
  have hcl_k : ∀ r ∈ fullArenaClauseRefsCore k',
      fullArenaHdrCore k' r = (if r < fp then ar'[r]?.getD 0#32 else fullArenaHdrCore k r) ∧
      fullArenaClauseSizeCore k' r = fullArenaClauseSizeCore k r ∧
      fullArenaClauseGarbCore k' r = fullArenaClauseGarbCore k r ∧
      fullArenaClauseLitsCore k' r = fullArenaClauseLitsCore k r := by
    intro r hr; rw [hrefs_k_eq] at hr
    by_cases hlt : r < fp
    · have hr_fp : r ∈ fullArenaClauseRefsCore { k' with arena_len := fp } := by
        rw [hrefs_fp_eq]; exact hbwd0 r hr (Nat.zero_le _) hlt
      obtain ⟨_, _, _, _, hsz', hgb', hlits'⟩ := hmeta_fp r hr_fp
      have hr_kfp : r ∈ fullArenaClauseRefsCore { k with arena_len := fp } :=
        hrefs_fp_eq ▸ hr_fp
      have hgk : fullArenaClauseGarbCore k r = false := by
        unfold fullArenaClauseGarbCore fullArenaHdrCore
        have hfl := (hfwd0 fp (Nat.le_refl fp) r hr_kfp).2.2.1
        simp [(bv32_mask_00C80000_props _ hfl).2.1]
      exact ⟨by simp [hlt, fullArenaHdrCore, k'], hsz', hgb'.trans hgk.symm, hlits'⟩
    · have hge : fp ≤ r := by omega
      have hwf := hw.arena.refs_wf r hr
      have hwf_bd : r + 3 + fullArenaClauseSizeCore k r ≤ k.arena.length := by
        have := hlen.arena_len_arr; have := hlen.arena_len_le
        have := hwf.2.2.1; have := hwf.2.2.2.1; omega
      have hn : ¬ (r < fp) := by omega
      have h0 := htail r hge (by omega)
      have h2 := htail (r + 2) (by omega) (by omega)
      have hsz : fullArenaClauseSizeCore k' r = fullArenaClauseSizeCore k r := by
        unfold fullArenaClauseSizeCore; dsimp only [k']; rw [h2]
      refine ⟨by simp [hn, fullArenaHdrCore, k', h0], hsz,
        by unfold fullArenaClauseGarbCore fullArenaHdrCore; dsimp only [k']; rw [h0],
        fullArenaClauseLitsCore_eq_of_hold
          hwf_bd
          (by have hwf2 := hwf.2.2.1; unfold fullArenaClauseSizeCore at hwf2
              have := hwf.2.2.2.1; have := hlen.arena_len_le
              dsimp only [k']; rw [har']; unfold fullArenaClauseSizeCore; omega)
          hsz
          (fun j hj => by
            unfold fullArenaClauseSizeCore at hj
            have hwf2 := hwf.2.2.1; unfold fullArenaClauseSizeCore at hwf2
            have := hwf.2.2.2.1
            exact htail (r + 3 + j) (by omega) (by omega))⟩
  have hfp_k' : fp ∈ fullArenaClauseRefsCore k' := hrefs_k_eq ▸ hfp_mem
  have hcmp' : CompactPrefixOk c F_cur s k' fp := by
    refine ⟨ha_fp, fun r hr => ?_, fun _ r hr => ?_⟩
    · obtain ⟨_, _, hsh', _, _, hgb', _⟩ := hmeta_fp r hr
      exact ⟨hsh', hgb'⟩
    · obtain ⟨hr_k, _, _, _, _, _, hlits'⟩ := hmeta_fp r hr
      rw [hlits']
      have hr_kfp : r ∈ fullArenaClauseRefsCore { k with arena_len := fp } :=
        hrefs_fp_eq ▸ hr
      have hgk : fullArenaClauseGarbCore k r = false := by
        unfold fullArenaClauseGarbCore fullArenaHdrCore
        have hfl := (hfwd0 fp (Nat.le_refl fp) r hr_kfp).2.2.1
        simp [(bv32_mask_00C80000_props _ hfl).2.1]
      exact hnd r hr_k hgk
  have hrm' : SweepReasonMapInv k k' fp fp := by
    intro idx hidx; dsimp only
    let v := (k.trl[idx]?.getD 0#32).toNat / 2
    let r0 := k.rsns[v]?.getD 0xFFFFFFFF#32
    change (if r0 = 0xFFFFFFFF#32 ∨ (r0 &&& 0x80000000#32) ≠ 0#32 then _ else _)
    split
    · rfl
    · rename_i hc1
      have hne0 : r0 ≠ 0xFFFFFFFF#32 := fun h => hc1 (Or.inl h)
      have hlg0 : (r0 &&& 0x80000000#32) = 0#32 :=
        Classical.byContradiction fun h => hc1 (Or.inr h)
      have hri := hw.reason_inv idx hidx hne0
      change (if (r0 &&& 0x80000000#32) ≠ 0#32 then _ else _) at hri
      rw [ite_eq_right (fun h => h hlg0)] at hri
      split
      · rename_i hlt
        have hr_fp : r0.toNat ∈ fullArenaClauseRefsCore { k' with arena_len := fp } := by
          rw [hrefs_fp_eq]; exact hbwd0 r0.toNat hri.1 (Nat.zero_le _) hlt
        obtain ⟨_, _, _, _, _, hgb', hlits'⟩ := hmeta_fp r0.toNat hr_fp
        exact ⟨hlt, (bv32_lt_highbit_iff r0).mpr hlg0, hne0, hlg0, hr_fp, hgb', hlits'⟩
      · rfl
  have hw' : FullWitnessInv c F0 F_cur k' := by
    refine { hw with
      arena := ⟨hw.arena.len_ok, fun r hr => ?_, fun r hr hsh => ?_, fun r hr hng l hl => ?_,
        fun r hr hng => ?_⟩
      watches := hw.watches.with_wstk (k' := k') rfl rfl rfl rfl rfl (fun r hr => hrefs_k_eq ▸ hr)
      reason_inv := fun idx hidx hne => ?_
      reason_lit_mem := fun idx hidx hne hlg => ?_ }
    · have hrk := hrefs_k_eq ▸ hr
      have hwf := hw.arena.refs_wf r hrk
      have hsz_e := (hcl_k r hr).2.1
      have hnx_e : fullArenaNextOff ar' k.arena_len r =
          fullArenaNextOff k.arena k.arena_len r := by
        by_cases hlt : r < fp
        · have hrf : r ∈ fullArenaClauseRefsCore { k' with arena_len := fp } := by
            rw [hrefs_fp_eq]; exact hbwd0 r hrk (Nat.zero_le _) hlt
          have hrf_k : r ∈ fullArenaClauseRefsCore { k with arena_len := fp } :=
            hrefs_fp_eq ▸ hrf
          obtain ⟨hfl', hr2', _⟩ := hmatch r hrf_k
          obtain ⟨_, _, hfl, _, hfit⟩ := hfwd0 fp (Nat.le_refl fp) r hrf_k
          have h1 := clean_nextOff_eq (ar := ar') (by omega) hfl' (by rw [hr2']; exact hfit)
            (Nat.le_of_lt hfp_lt)
          have h2 := clean_nextOff_eq (ar := k.arena) (by omega) hfl hfit
            (Nat.le_of_lt hfp_lt)
          rw [h1, h2, hr2']
        · refine fullArenaNextOff_congr_block (htail r (by omega) (by omega))
            (htail (r + 2) (by omega) (by omega))
            (fun i hi1 hi2 => htail i (by omega) (by omega))
      dsimp only [k'] at hwf hnx_e hsz_e ⊢; rw [hnx_e, hsz_e]; exact hwf
    · have hrk := hrefs_k_eq ▸ hr
      have hhdr := (hcl_k r hr).1
      by_cases hlt : r < fp
      · have hrf : r ∈ fullArenaClauseRefsCore { k' with arena_len := fp } := by
          rw [hrefs_fp_eq]; exact hbwd0 r hrk (Nat.zero_le _) hlt
        exact absurd (hmeta_fp r hrf).2.2.1 hsh
      · dsimp only [k'] at hhdr hsh; rw [hhdr, ite_eq_right (fun h => absurd h hlt)] at hsh
        obtain ⟨t, ht1, ht2, hst⟩ := hw.arena.shrk_term r hrk hsh
        exact ⟨t, by rw [(hcl_k r hr).2.1]; exact ht1, ht2,
          by dsimp only [k']; rw [htail t (by omega) ht2, hst]⟩
    · have hrk := hrefs_k_eq ▸ hr
      rw [(hcl_k r hr).2.2.1] at hng; rw [(hcl_k r hr).2.2.2] at hl
      exact hw.arena.lits_lt r hrk hng l hl
    · have hrk := hrefs_k_eq ▸ hr
      rw [(hcl_k r hr).2.2.1] at hng; rw [(hcl_k r hr).2.2.2]
      exact hw.arena.entails r hrk hng
    · have hri := hw.reason_inv idx hidx hne
      dsimp only [k'] at hri ⊢
      split at hri
      · split
        · exact hri
        · contradiction
      · split
        · contradiction
        · refine ⟨hrefs_k_eq ▸ hri.1, ?_, ?_⟩
          · rw [(hcl_k _ (hrefs_k_eq ▸ hri.1)).2.2.1]; exact hri.2.1
          · intro q hq; rw [(hcl_k _ (hrefs_k_eq ▸ hri.1)).2.2.2] at hq; exact hri.2.2 q hq
    · have hri := hw.reason_inv idx hidx hne
      have hb : ¬ (k.rsns[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD
          0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32 := fun h => absurd hlg h
      rw [ite_eq_right hb] at hri
      rw [(hcl_k _ (hrefs_k_eq ▸ hri.1)).2.2.2]
      exact hw.reason_lit_mem idx hidx hne hlg
  have hnd' : ∀ r ∈ fullArenaClauseRefsCore k', fullArenaClauseGarbCore k' r = false →
      ((fullArenaClauseLitsCore k' r).map (· / 2)).Nodup := fun r hr hng => by
    rw [(hcl_k r hr).2.2.1] at hng; rw [(hcl_k r hr).2.2.2]
    exact hnd r (hrefs_k_eq ▸ hr) hng
  have htail' : ∀ r ∈ fullArenaClauseRefsCore k', fp ≤ r → ar'[r]? = k.arena[r]? :=
    fun r hr hge => by
      rw [hrefs_k_eq] at hr
      have hwf := hw.arena.refs_wf r hr
      exact htail r hge (by omega)
  exact ⟨hfp_k', hcmp', hrm', hw', hnd', htail'⟩

/-! ## 2. `WatchSliceLtOk` / `SweepReasonMapInv` & `MoveRangeChain` Bridges -/

theorem WatchSliceLtOk.ofBinOnly {F_cur : List (List Nat)} {k : FullCoreState} {lit p rem : Nat}
    (h : BinOnlyWatchSliceOk F_cur k lit p rem) : WatchSliceLtOk 0 F_cur k lit p rem := by
  induction h with
  | empty => exact .empty
  | bin hp hf hne hlt hent _ ih => exact .bin hp hf hne hlt hent ih

theorem modeWatchesInv_of_watchSliceLtOk {F_cur : List (List Nat)} {k : FullCoreState}
    {keep dst : Nat} (hdk : 0 < keep → k.dense_mode = 0#64)
    (hlt : ∀ l < 2 * k.cur_vars,
      WatchSliceLtOk keep F_cur k l (fullWatchOffCore k l) (fullWatchSizeCore k l))
    (hlay : WatchStackLayout { k with arena_len := dst })
    (hkeep : ∀ r ∈ fullArenaClauseRefsCore k, r < keep →
      r ∈ fullArenaClauseRefsCore { k with arena_len := dst }) :
    ModeWatchesInv F_cur { k with arena_len := dst } := by
  have hrefl : (cnfOfClauses F_cur).Entails (cnfOfClauses F_cur) := by
    rw [CNF.entails_def]; exact fun _ h => h
  unfold ModeWatchesInv
  split
  · refine ⟨hlay, fun l hl => ?_⟩
    exact ((hlt l hl).relocate (k := k) (k' := { k with arena_len := dst })
      hrefl (Nat.le_refl _) hkeep (fun _ _ => rfl)).toWatchSliceOk
  · rename_i hne
    have hkz : keep = 0 := Classical.byContradiction fun hp => hne (hdk (Nat.pos_of_ne_zero hp))
    subst hkz
    refine ⟨hlay, fun l hl => ?_⟩
    exact ((hlt l hl).relocate (k := k) (k' := { k with arena_len := dst })
      hrefl (Nat.le_refl _) hkeep (fun _ _ => rfl)).toBinOnly.toDenseWatchSliceOk

theorem SweepReasonMapInv.toFullWitnessInvLt {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {k0 kL : FullCoreState} {keep dst : Nat}
    (hlenL : kL.LengthsOk c) (hw0 : FullWitnessInv c F0 F_cur k0)
    (ha' : FullArenaClausesInv c F_cur { kL with arena_len := dst })
    (hdk : 0 < keep → kL.dense_mode = 0#64)
    (hlay : WatchStackLayout { kL with arena_len := dst })
    (hlt : ∀ l < 2 * kL.cur_vars,
      WatchSliceLtOk keep F_cur kL l (fullWatchOffCore kL l) (fullWatchSizeCore kL l))
    (hkeep : ∀ r ∈ fullArenaClauseRefsCore kL, r < keep →
      r ∈ fullArenaClauseRefsCore { kL with arena_len := dst })
    (hvals : kL.vals = k0.vals) (hlvl : kL.lvl = k0.lvl) (htrl : kL.trl = k0.trl)
    (htp : kL.trail_pos = k0.trail_pos) (hte : kL.trail_end = k0.trail_end)
    (hcl : kL.cur_level = k0.cur_level) (hcv : kL.cur_vars = k0.cur_vars)
    (hft : kL.frame_trail = k0.frame_trail) (hfd : kL.frame_dec = k0.frame_dec)
    (hinc : kL.inconsistent = k0.inconsistent) (hrm : SweepReasonMapInv k0 kL k0.arena_len dst) :
    FullWitnessInv c F0 F_cur { kL with arena_len := dst } := by
  let kZ : FullCoreState := { kL with wvec := List.replicate (4 * c.max_vars) 0#32, wlen := 0 }
  have hwvec0 : BinOnlyWatchesInv F_cur kZ := by
    have hoff0 : ∀ l < 2 * kL.cur_vars, fullWatchOffCore kZ l = 0 := fun l hl => by
      unfold fullWatchOffCore
      have hbd : 2 * l < 4 * c.max_vars := by have := hlenL.cur_vars_le; omega
      have hlen_rep : 2 * l < (List.replicate (4 * c.max_vars) 0#32).length := by simp; omega
      dsimp only [kZ]
      rw [List.getElem?_eq_getElem hlen_rep, List.getElem_replicate]; rfl
    have hsz0 : ∀ l < 2 * kL.cur_vars, fullWatchSizeCore kZ l = 0 := fun l hl => by
      unfold fullWatchSizeCore
      have hbd : 2 * l + 1 < 4 * c.max_vars := by have := hlenL.cur_vars_le; omega
      have hlen_rep : 2 * l + 1 < (List.replicate (4 * c.max_vars) 0#32).length := by simp; omega
      dsimp only [kZ]
      rw [List.getElem?_eq_getElem hlen_rep, List.getElem_replicate]; rfl
    refine ⟨⟨fun l hl => by rw [hoff0 l hl, hsz0 l hl]; simp,
        fun l hl hpos => by rw [hsz0 l hl] at hpos; omega,
        fun l1 _ h1 _ _ hpos => by rw [hsz0 l1 h1] at hpos; omega,
        fun l hl k hk => by rw [hsz0 l hl] at hk; omega⟩,
      fun l hl => by rw [hsz0 l hl]; exact .empty⟩
  have haZ : FullArenaClausesInv c F_cur { kZ with arena_len := dst } :=
    ⟨ha'.len_ok, ha'.refs_wf, ha'.shrk_term, ha'.lits_lt, ha'.entails⟩
  have hwBase := SweepReasonMapInv.toFullWitnessInv (c := c) (F0 := F0) (F_cur := F_cur)
    (k0 := k0) (kL := kZ) (dst := dst) hw0 haZ hwvec0 hvals hlvl htrl htp hte hcl hcv hft hfd
    hinc hrm
  exact { hwBase with
    arena := ⟨ha'.len_ok, ha'.refs_wf, ha'.shrk_term, ha'.lits_lt, ha'.entails⟩
    watches := modeWatchesInv_of_watchSliceLtOk hdk hlt hlay hkeep }

theorem fullArenaClauseRefsCore_mono_prefix {c : FullCfg} {F_cur : List (List Nat)}
    {k : FullCoreState} {alen1 alen2 : Nat} (hle : alen1 ≤ alen2)
    (ha1 : FullArenaClausesInv c F_cur { k with arena_len := alen1 }) :
    ∀ r ∈ fullArenaClauseRefsCore { k with arena_len := alen1 },
      r ∈ fullArenaClauseRefsCore { k with arena_len := alen2 } ∧
      fullArenaClauseGarbCore { k with arena_len := alen2 } r =
        fullArenaClauseGarbCore { k with arena_len := alen1 } r ∧
      fullArenaClauseLitsCore { k with arena_len := alen2 } r =
        fullArenaClauseLitsCore { k with arena_len := alen1 } r := by
  have go : ∀ fuel pos,
      (∀ q ∈ fullArenaScanRefs k.arena alen1 pos fuel,
        fullArenaNextOff k.arena alen2 q = fullArenaNextOff k.arena alen1 q) →
      ∀ r ∈ fullArenaScanRefs k.arena alen1 pos fuel,
        r ∈ fullArenaScanRefs k.arena alen2 pos (fuel + (alen2 - alen1)) := by
    intro fuel
    induction fuel with
    | zero => intro _ _ r hr; simp [fullArenaScanRefs] at hr
    | succ f ih =>
      intro pos hnx r hr
      unfold fullArenaScanRefs at hr
      split at hr
      · rename_i hp1
        have hp2 : pos + 3 ≤ alen2 := by omega
        have hnxt := hnx pos (by simp [fullArenaScanRefs, hp1])
        have hstep : f + 1 + (alen2 - alen1) = (f + (alen2 - alen1)) + 1 := by omega
        rw [hstep]; unfold fullArenaScanRefs
        simp only [hp2, ↓reduceIte, hnxt, List.mem_cons]
        simp only [List.mem_cons] at hr
        rcases hr with rfl | hrest
        · exact Or.inl rfl
        · right
          exact ih (fullArenaNextOff k.arena alen1 pos)
            (fun q hq => hnx q (by simp [fullArenaScanRefs, hp1, hq])) r hrest
      · simp at hr
  intro r hr
  have hnext := ha1.arenaNextOff_extend (arena' := k.arena) (alen' := alen2) hle (fun _ _ => rfl)
  have hr2 := go alen1 0 hnext r hr
  rw [fullArenaScanRefs_fuel_ge (f1 := alen1 + (alen2 - alen1)) (f2 := alen2)
    (by omega) (Nat.le_refl _)] at hr2
  exact ⟨hr2, rfl, rfl⟩

theorem moveRangeChain_append {ar : List (BitVec 32)} {a b c rw1 rw2 : Nat}
    (h1 : MoveRangeChain ar a b rw1) (h2 : MoveRangeChain ar b c rw2) :
    MoveRangeChain ar a c (rw1 + rw2) := by
  induction h1 with
  | empty => simpa using h2
  | @step p hi rw h3 hfl hsz hfit _ ih =>
    have hb := h2.le.1
    rw [Nat.add_assoc]
    exact MoveRangeChain.step (by omega) hfl hsz (by omega) (ih h2)

theorem moveRangeChain_snoc {ar : List (BitVec 32)} {a p p' rw : Nat}
    (h : MoveRangeChain ar a p rw) (h3 : p + 3 ≤ p')
    (hfl : (ar[p]?.getD 0#32 &&& 0x00880000#32) = 0#32)
    (hsz : 3 ≤ (ar[p + 2]?.getD 0#32).toNat)
    (hp_eq : p + 3 + (ar[p + 2]?.getD 0#32).toNat = p') :
    MoveRangeChain ar a p'
      (rw + if (ar[p]?.getD 0#32 &&& 0x00400000#32) ≠ 0#32 then
        3 + (ar[p + 2]?.getD 0#32).toNat else 0) :=
  moveRangeChain_append h
    (.step h3 hfl hsz (le_of_eq hp_eq) (by rw [hp_eq]; exact .empty))

theorem refInChain_split {ar : List (BitVec 32)} {a b c rw1 r : Nat}
    (h1 : MoveRangeChain ar a b rw1) (hr : RefInChain ar a c r) :
    RefInChain ar a b r ∨ RefInChain ar b c r := by
  induction h1 with
  | empty => exact Or.inr hr
  | @step p b rw h3 hfl hsz hfit htl ih =>
    cases hr with
    | head => exact Or.inl (.head h3 hfl hsz hfit)
    | tail _ _ _ _ hr_tl =>
      rcases ih hr_tl with hr1 | hr2
      · exact Or.inl (.tail h3 hfl hsz hfit hr1)
      · exact Or.inr hr2

theorem refInChain_append_left {ar : List (BitVec 32)} {a b c r : Nat}
    (hb : b ≤ c) (hr : RefInChain ar a b r) : RefInChain ar a c r := by
  induction hr with
  | head h3 hfl hsz hfit => exact .head (by omega) hfl hsz (by omega)
  | tail h3 hfl hsz hfit _ ih => exact .tail (by omega) hfl hsz (by omega) (ih hb)

theorem refInChain_append_right {ar : List (BitVec 32)} {a b c rw1 r : Nat}
    (h1 : MoveRangeChain ar a b rw1) (hr : RefInChain ar b c r) :
    RefInChain ar a c r := by
  induction h1 with
  | empty => exact hr
  | @step p b rw h3 hfl hsz hfit _ ih =>
    have hbc : b ≤ c := Nat.le_trans hr.bounds.1 (by have := hr.bounds.2; omega)
    exact .tail (by omega) hfl hsz (by omega) (ih hr)

theorem refInChain_of_moveRangeChain {ar : List (BitVec 32)} {lo hi rw r : Nat}
    (hmv : MoveRangeChain ar lo hi rw) (hr : RefInChain ar lo hi r) :
    r < hi ∧ (ar[r]?.getD 0#32 &&& 0x00880000#32) = 0#32 ∧
    3 ≤ (ar[r + 2]?.getD 0#32).toNat ∧
    r + 3 + (ar[r + 2]?.getD 0#32).toNat ≤ hi := by
  induction hmv generalizing r with
  | empty => exfalso; have := hr.bounds; omega
  | @step p hi rw h3 hfl hsz hfit _ ih =>
    cases hr with
    | head => exact ⟨by omega, hfl, hsz, hfit⟩
    | tail _ _ _ _ htl => exact ih htl

theorem moveRedRsnUnique_of_witness {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} {lo hi : Nat} (hw : FullWitnessInv c F0 F_cur k)
    (hhi : hi < 0x80000000) :
    MoveRedRsnUnique k.arena k.vals k.rsns k.cur_vars lo hi := by
  refine MoveRedRsnUnique.intro fun r _ _ v1 v2 hv1 hv2 hval1 hval2 hrs1 hrs2 => ?_
  have hlt1 : ∃ l1, l1 < 2 * k.cur_vars ∧ l1 / 2 = v1 ∧ k.vals[l1]?.getD 0#8 = 1#8 := by
    rcases hval1 with h | h
    · exact ⟨2 * v1, by omega, by omega, h⟩
    · exact ⟨2 * v1 + 1, by omega, by omega, h⟩
  have hlt2 : ∃ l2, l2 < 2 * k.cur_vars ∧ l2 / 2 = v2 ∧ k.vals[l2]?.getD 0#8 = 1#8 := by
    rcases hval2 with h | h
    · exact ⟨2 * v2, by omega, by omega, h⟩
    · exact ⟨2 * v2 + 1, by omega, by omega, h⟩
  rcases hlt1 with ⟨l1, hl1_lt, hl1_v, hl1_val⟩
  rcases hlt2 with ⟨l2, hl2_lt, hl2_v, hl2_val⟩
  obtain ⟨idx1, hidx1, htrl1⟩ := (hw.vals_true_iff l1 hl1_lt).mp hl1_val
  obtain ⟨idx2, hidx2, htrl2⟩ := (hw.vals_true_iff l2 hl2_lt).mp hl2_val
  have hv_trl1 : (k.trl[idx1]?.getD 0#32).toNat / 2 = v1 := by rw [htrl1]; exact hl1_v
  have hv_trl2 : (k.trl[idx2]?.getD 0#32).toNat / 2 = v2 := by rw [htrl2]; exact hl2_v
  have hr_eq1 : k.rsns[(k.trl[idx1]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 =
      BitVec.ofNat 32 r := by
    rw [hv_trl1]; apply BitVec.eq_of_toNat_eq
    rw [hrs1, bv32_ofNat_toNat (by omega)]
  have hr_eq2 : k.rsns[(k.trl[idx2]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 =
      BitVec.ofNat 32 r := by
    rw [hv_trl2]; apply BitVec.eq_of_toNat_eq
    rw [hrs2, bv32_ofNat_toNat (by omega)]
  have hid_eq := fullWitness_reason_unique hw hidx1 hidx2 (by omega) hr_eq1 hr_eq2
  rw [← hv_trl1, ← hv_trl2, hid_eq]

private theorem refInChain_mem_refs {c : FullCfg} {F_cur : List (List Nat)}
    {k : FullCoreState} {hi : Nat}
    (ha : FullArenaClausesInv c F_cur { k with arena_len := hi }) :
    ∀ p rw, MoveRangeChain k.arena p hi rw →
      (p = hi ∨ p ∈ fullArenaClauseRefsCore { k with arena_len := hi }) →
      ∀ r, RefInChain k.arena p hi r → r ∈ fullArenaClauseRefsCore { k with arena_len := hi } := by
  intro p rw hmv
  induction hmv with
  | empty => intro _ r hr; exfalso; have := hr.bounds; omega
  | @step p hi rw h3 hfl hsz hfit htl ih =>
    intro hp_mem r hr
    have hp_m : p ∈ fullArenaClauseRefsCore { k with arena_len := hi } :=
      hp_mem.resolve_left (by omega)
    cases hr with
    | head => exact hp_m
    | tail _ _ _ _ hr_tl =>
      have hsh : (k.arena[p]?.getD 0#32 &&& 0x00800000#32) = 0#32 := by
        have h1 : (k.arena[p]?.getD 0#32 &&& (0x00880000#32 &&& 0x00800000#32)) = 0#32 := by
          rw [← BitVec.and_assoc, hfl, BitVec.zero_and]
        rwa [show (0x00880000#32 &&& 0x00800000#32) = 0x00800000#32 from rfl] at h1
      have hnx : fullArenaNextOff k.arena hi p = p + 3 + (k.arena[p + 2]?.getD 0#32).toNat := by
        unfold fullArenaNextOff
        simp [show ¬ (p + 3 > hi) by omega,
          show ¬ (p + 3 + (k.arena[p + 2]?.getD 0#32).toNat > hi) by omega, hsh]
      have hnx_or := fullArenaClauseRefs_next_or_end ha hp_m
      rw [hnx] at hnx_or
      rcases hnx_or with h_end | hnx_mem
      · exfalso; dsimp only at h_end
        have h1 := hr_tl.bounds.1; rw [h_end] at h1
        have h2 := hr_tl.bounds.2; omega
      · exact ih ha (Or.inr hnx_mem) r hr_tl

theorem compactPrefix_extend_move_chain {c : FullCfg} {F_cur : List (List Nat)}
    {s : FullState} {kE kM : FullCoreState} {first_red dst rwM : Nat}
    (hcmpE : CompactPrefixOk c F_cur s kE dst)
    (hcmp_fr : CompactPrefixOk c F_cur s kM first_red)
    (harE_len : kE.arena.length = c.arena_cap)
    (hkM_len : kM.arena.length = c.arena_cap)
    (hkM_cv : kM.cur_vars = kE.cur_vars)
    (hdst_cap : dst ≤ c.arena_cap)
    (hmvM : MoveRangeChain kM.arena first_red dst rwM)
    (hmap : ∀ r, RefInChain kM.arena first_red dst r →
      ∃ src ∈ fullArenaClauseRefsCore { kE with arena_len := dst },
        fullArenaClauseGarbCore { kE with arena_len := dst } src = false ∧
        (kM.arena[r + 2]?.getD 0#32).toNat = (kE.arena[src + 2]?.getD 0#32).toNat ∧
        ∀ j < (kE.arena[src + 2]?.getD 0#32).toNat, kM.arena[r + 3 + j]? = kE.arena[src + 3 + j]?) :
    CompactPrefixOk c F_cur s kM dst ∧
    ∀ r, RefInChain kM.arena first_red dst r →
      r ∈ fullArenaClauseRefsCore { kM with arena_len := dst } ∧
      fullArenaClauseGarbCore { kM with arena_len := dst } r = false ∧
      fullArenaClauseLitsCore { kM with arena_len := dst } r =
        fullArenaClauseLitsCore kM r := by
  suffices h : ∀ p rwP, MoveRangeChain kM.arena p dst rwP → first_red ≤ p →
      CompactPrefixOk c F_cur s kM p →
      (∀ r, RefInChain kM.arena p dst r → RefInChain kM.arena first_red dst r) →
      CompactPrefixOk c F_cur s kM dst ∧
      ∀ r, RefInChain kM.arena p dst r →
        r ∈ fullArenaClauseRefsCore { kM with arena_len := dst } ∧
        fullArenaClauseGarbCore { kM with arena_len := dst } r = false ∧
        fullArenaClauseLitsCore { kM with arena_len := dst } r =
          fullArenaClauseLitsCore kM r by
    exact h first_red rwM hmvM (Nat.le_refl _) hcmp_fr (fun _ hr => hr)
  intro p rwP hmvP
  induction hmvP with
  | empty =>
    intro _ hcmp_p _
    exact ⟨hcmp_p, fun r hr => by exfalso; have := hr.bounds; omega⟩
  | @step p dst rw h3 hfl hsz hfit _ ih =>
    intro hfr_p hcmp_p hsub_ref
    let szM := (kM.arena[p + 2]?.getD 0#32).toNat
    have hr_p : RefInChain kM.arena first_red dst p := hsub_ref p (.head h3 hfl hsz hfit)
    obtain ⟨src, hsrc_mem, hsrc_ng, hsz_eq, hlits_eq⟩ := hmap p hr_p
    have hwf_src := hcmpE.1.refs_wf src hsrc_mem
    have hsrc_sz_eq : fullArenaClauseSizeCore { kE with arena_len := dst } src =
        (kE.arena[src + 2]?.getD 0#32).toNat := rfl
    have hsrc_bd : src + 3 + (kE.arena[src + 2]?.getD 0#32).toNat ≤ kE.arena.length := by
      dsimp only [fullArenaClauseSizeCore] at hwf_src; omega
    have hlits_m_eq : ((kM.arena.drop (p + 3)).take szM).map BitVec.toNat =
        fullArenaClauseLitsCore { kE with arena_len := dst } src := by
      unfold fullArenaClauseLitsCore
      dsimp only [szM]
      rw [hsrc_sz_eq, hsz_eq]
      congr 1
      apply List.ext_getElem
      · have h_km_bd : p + 3 + (kE.arena[src + 2]?.getD 0#32).toNat ≤ kM.arena.length := by omega
        rw [List.length_take, List.length_drop, List.length_take, List.length_drop]
        omega
      · intro j hj1 hj2
        simp only [List.getElem_take, List.getElem_drop]
        have hj_lt : j < (kE.arena[src + 2]?.getD 0#32).toNat := by
          simp [List.length_take] at hj1; omega
        have h1 := hlits_eq j hj_lt
        rw [List.getElem?_eq_getElem (by omega : p + 3 + j < kM.arena.length),
          List.getElem?_eq_getElem (by omega : src + 3 + j < kE.arena.length)] at h1
        exact Option.some.inj h1
    have hnoshrk : (kM.arena[p]?.getD 0#32 &&& 0x00800000#32) = 0#32 := by
      have h1 : (kM.arena[p]?.getD 0#32 &&& (0x00880000#32 &&& 0x00800000#32)) = 0#32 := by
        rw [← BitVec.and_assoc, hfl, BitVec.zero_and]
      rwa [show (0x00880000#32 &&& 0x00800000#32) = 0x00800000#32 from rfl] at h1
    have hnogarb : (kM.arena[p]?.getD 0#32 &&& 0x00080000#32) = 0#32 := by
      have h1 : (kM.arena[p]?.getD 0#32 &&& (0x00880000#32 &&& 0x00080000#32)) = 0#32 := by
        rw [← BitVec.and_assoc, hfl, BitVec.zero_and]
      rwa [show (0x00880000#32 &&& 0x00080000#32) = 0x00080000#32 from rfl] at h1
    have hlits_lt : ∀ j < szM, (kM.arena[p + 3 + j]?.getD 0#32).toNat < 2 * kM.cur_vars := by
      intro j hj
      have hj' : j < (kE.arena[src + 2]?.getD 0#32).toNat := by simpa [szM, hsz_eq] using hj
      have hl1 := hlits_eq j hj'
      have hlt_src := hcmpE.1.lits_lt src hsrc_mem hsrc_ng
        (kE.arena[src + 3 + j]?.getD 0#32).toNat (by
          have hbd : src + 3 + fullArenaClauseSizeCore { kE with arena_len := dst } src ≤
              kE.arena.length := by
            dsimp only [fullArenaClauseSizeCore]; exact hsrc_bd
          rw [mem_fullArenaClauseLitsCore_iff hbd]
          refine ⟨j, hj', ?_⟩
          rw [List.getElem?_eq_getElem (by omega : src + 3 + j < kE.arena.length),
            Option.getD_some])
      dsimp at hlt_src
      rwa [hl1, hkM_cv]
    have hent : (cnfOfClauses F_cur).EntailsClause
        (cnfClause (((kM.arena.drop (p + 3)).take szM).map BitVec.toNat)) := by
      rw [hlits_m_eq]; exact hcmpE.1.entails src hsrc_mem hsrc_ng
    obtain ⟨hrefs_nxt, ha_nxt, hold_nxt, hno_nxt⟩ := compactArena_append_block
      (k := kM) (k' := kM) (dst := p) (new_sz := szM) hcmp_p.1 hcmp_p.2.1 rfl hsz hkM_len hkM_len
      (by omega) (fun _ _ => rfl) hnoshrk hnogarb rfl hlits_lt hent
    have hnd_nxt : ∀ hnd_s, ∀ r ∈ fullArenaClauseRefsCore { kM with arena_len := p + 3 + szM },
        ((fullArenaClauseLitsCore { kM with arena_len := p + 3 + szM } r).map
          (· / 2)).Nodup := fun hnd_s r hr => by
      rw [hrefs_nxt, List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | h_eq
      · rw [(hold_nxt r hr).2.2]; exact hcmp_p.2.2 hnd_s r hr
      · rw [h_eq]; unfold fullArenaClauseLitsCore
        have hsz_r : fullArenaClauseSizeCore { kM with arena_len := p + 3 + szM } p = szM := rfl
        rw [hsz_r, hlits_m_eq]
        exact hcmpE.2.2 hnd_s src hsrc_mem
    obtain ⟨hcmp_end, hmap_tl⟩ := ih hcmpE hdst_cap hmvM hmap (by dsimp only [szM] at *; omega)
      ⟨ha_nxt, hno_nxt, hnd_nxt⟩
      (fun r hr => hsub_ref r (.tail h3 hfl hsz hfit hr))
    refine ⟨hcmp_end, fun r hr => ?_⟩
    cases hr with
    | head =>
      have hp_in_nxt : p ∈ fullArenaClauseRefsCore { kM with arena_len := p + 3 + szM } := by
        rw [hrefs_nxt, List.mem_append, List.mem_singleton]; exact Or.inr rfl
      have hmono := fullArenaClauseRefsCore_mono_prefix (k := kM) (alen1 := p + 3 + szM)
        (alen2 := dst) hfit ha_nxt p hp_in_nxt
      refine ⟨hmono.1, ?_, ?_⟩
      · rw [hmono.2.1]
        exact (hno_nxt p hp_in_nxt).2
      · exact hmono.2.2
    | tail _ _ _ _ hr_tl => exact hmap_tl r hr_tl

private theorem moveRangeChain_scanRefs {ar : List (BitVec 32)} :
    ∀ {p dst rw : Nat}, MoveRangeChain ar p dst rw →
      ∀ fuel, dst - p ≤ fuel →
        ∀ r ∈ fullArenaScanRefs ar dst p fuel, RefInChain ar p dst r := by
  intro p dst rw hmv
  induction hmv with
  | empty =>
    intro fuel _ r hr
    cases fuel with
    | zero => simp [fullArenaScanRefs] at hr
    | succ f =>
      unfold fullArenaScanRefs at hr
      split at hr
      · omega
      · contradiction
  | @step p dst rw h3 hfl hsz hfit _ ih =>
    intro fuel hfl_le r hr
    cases fuel with
    | zero => omega
    | succ f =>
      have hsh : (ar[p]?.getD 0#32 &&& 0x00800000#32) = 0#32 := by
        have h1 : (ar[p]?.getD 0#32 &&& (0x00880000#32 &&& 0x00800000#32)) = 0#32 := by
          rw [← BitVec.and_assoc, hfl, BitVec.zero_and]
        rwa [show (0x00880000#32 &&& 0x00800000#32) = 0x00800000#32 from rfl] at h1
      have hnx : fullArenaNextOff ar dst p = p + 3 + (ar[p + 2]?.getD 0#32).toNat := by
        unfold fullArenaNextOff
        simp [show ¬ (p + 3 > dst) by omega,
          show ¬ (p + 3 + (ar[p + 2]?.getD 0#32).toNat > dst) by omega, hsh]
      unfold fullArenaScanRefs at hr
      simp only [h3, ↓reduceIte, hnx, List.mem_cons] at hr
      rcases hr with rfl | hrest
      · exact .head h3 hfl hsz hfit
      · exact .tail h3 hfl hsz hfit (ih f (by omega) r hrest)

private theorem moveRangeChain_partition_refs {c : FullCfg} {F_cur : List (List Nat)}
    {k : FullCoreState} {first_red dst rw : Nat}
    (ha_fr : FullArenaClausesInv c F_cur { k with arena_len := first_red })
    (hmv : MoveRangeChain k.arena first_red dst rw) :
    ∀ r ∈ fullArenaClauseRefsCore { k with arena_len := dst },
      (r < first_red ∧ r ∈ fullArenaClauseRefsCore { k with arena_len := first_red }) ∨
      (first_red ≤ r ∧ RefInChain k.arena first_red dst r) := by
  have hfr_le : first_red ≤ dst := hmv.le.1
  have hsplit : fullArenaClauseRefsCore { k with arena_len := dst } =
      fullArenaClauseRefsCore { k with arena_len := first_red } ++
      fullArenaScanRefs k.arena dst first_red (dst - first_red) := by
    unfold fullArenaClauseRefsCore; dsimp only
    rw [fullArenaScanRefs_fuel_ge (f1 := dst) (f2 := first_red + (dst - first_red))
      (Nat.le_refl _) (by omega)]
    apply scanRefs_split_at (ar := k.arena) (alen := dst) (fp := first_red) hfr_le
      first_red 0 (Nat.le_refl first_red)
    rcases ha_fr.len_ok with h0 | h3
    · exact Or.inl h0.symm
    · refine Or.inr ⟨h3, fun q hq => ?_⟩
      have hwf := ha_fr.refs_wf q hq
      have hnx := ha_fr.arenaNextOff_extend (arena' := k.arena) (alen' := dst)
        hfr_le (fun _ _ => rfl) q hq
      exact ⟨hnx, hwf.2.2.2.2⟩
  intro r hr
  rw [hsplit, List.mem_append] at hr
  rcases hr with hr1 | hr2
  · exact Or.inl ⟨by have := (ha_fr.refs_wf r hr1).1; dsimp only at this; omega, hr1⟩
  · have hch := moveRangeChain_scanRefs hmv (dst - first_red) (Nat.le_refl _) r hr2
    exact Or.inr ⟨hch.bounds.1, hch⟩

open Classical in
theorem move_red_end_compact_and_rsn {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s s0 sE : FullState} {arM rsnsM : List (BitVec 32)} {first_red dst rwE rwM : Nat}
    (hw0 : FullWitnessInv c F0 F_cur s0.core)
    (hcmpE : CompactPrefixOk c F_cur s sE.core dst)
    (hcmpE_fr : CompactPrefixOk c F_cur s sE.core first_red)
    (harE_len : sE.core.arena.length = c.arena_cap)
    (harM_len : arM.length = c.arena_cap)
    (_hrsM_len : rsnsM.length = c.max_vars)
    (hfr_dst : first_red < dst) (hdst_cap : dst ≤ c.arena_cap)
    (hfr_inE : first_red ∈ fullArenaClauseRefsCore { sE.core with arena_len := dst })
    (hmvE : MoveRangeChain sE.core.arena first_red dst rwE)
    (hmvM : MoveRangeChain arM first_red dst rwM)
    (hpreM : ∀ i < first_red, arM[i]? = sE.core.arena[i]?)
    (hblkM : ∀ r, RefInChain arM first_red dst r →
      (arM[r]?.getD 0#32 &&& 0x00200000#32) = 0#32 ∧
      ∃ src, RefInChain sE.core.arena first_red dst src ∧
        (arM[r + 2]?.getD 0#32).toNat = (sE.core.arena[src + 2]?.getD 0#32).toNat ∧
        ∀ j < (sE.core.arena[src + 2]?.getD 0#32).toNat,
          arM[r + 3 + j]? = sE.core.arena[src + 3 + j]?)
    (hrmE : 0 < s.core.cur_level → SweepReasonMapInv s0.core sE.core s0.core.arena_len dst)
    (hrs_marked : 0 < s.core.cur_level → ∀ r, RefInChain sE.core.arena first_red dst r →
      ∀ idx < s0.core.trail_end,
        (sE.core.rsns[(s0.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat = r →
        (sE.core.arena[r]?.getD 0#32 &&& 0x00200000#32) ≠ 0#32 ∧
        ∃ j < (sE.core.arena[r + 2]?.getD 0#32).toNat,
          let lit := (sE.core.arena[r + 3 + j]?.getD 0#32).toNat
          lit / 2 = (s0.core.trl[idx]?.getD 0#32).toNat / 2 ∧
          sE.core.vals[lit]?.getD 0#8 = 1#8)
    (hcv_eq : sE.core.cur_vars = s0.core.cur_vars)
    (hw0_tl_lt : ∀ idx < s0.core.trail_end,
      (s0.core.trl[idx]?.getD 0#32).toNat < 2 * s0.core.cur_vars)
    (hrsnsM : ∀ v < sE.core.cur_vars,
      let r0 := sE.core.rsns[v]?.getD 0xFFFFFFFF#32
      if first_red ≤ r0.toNat ∧ r0.toNat < dst ∧
          RefInChain sE.core.arena first_red dst r0.toNat ∧
          (sE.core.arena[r0.toNat]?.getD 0#32 &&& 0x00200000#32) ≠ 0#32 ∧
          ∃ j < (sE.core.arena[r0.toNat + 2]?.getD 0#32).toNat,
            let lit := (sE.core.arena[r0.toNat + 3 + j]?.getD 0#32).toNat
            lit / 2 = v ∧ sE.core.vals[lit]?.getD 0#8 = 1#8
      then
        let r' := (rsnsM[v]?.getD 0xFFFFFFFF#32).toNat
        first_red ≤ r' ∧ r' < dst ∧ r' < 0x80000000 ∧
        RefInChain arM first_red dst r' ∧
        (arM[r' + 2]?.getD 0#32).toNat = (sE.core.arena[r0.toNat + 2]?.getD 0#32).toNat ∧
        ∀ j < (sE.core.arena[r0.toNat + 2]?.getD 0#32).toNat,
          arM[r' + 3 + j]? = sE.core.arena[r0.toNat + 3 + j]?
      else rsnsM[v]?.getD 0xFFFFFFFF#32 = r0) :
    let kM : FullCoreState := { sE.core with arena := arM, rsns := rsnsM }
    CompactPrefixOk c F_cur s kM dst ∧
    (0 < s.core.cur_level → SweepReasonMapInv s0.core kM s0.core.arena_len dst) := by
  intro kM
  have ⟨hcmpM_fr, hcongr_fr⟩ := arenaPrefix_preserves_compact (k := sE.core)
    (k' := { sE.core with arena := arM }) hcmpE_fr rfl harE_len harM_len (by omega)
    (fun i hi => hpreM i hi)
  have hcmpM_fr' : CompactPrefixOk c F_cur s kM first_red :=
    CompactPrefixOk.with_rsns hcmpM_fr
  have hmap : ∀ r, RefInChain kM.arena first_red dst r →
      ∃ src ∈ fullArenaClauseRefsCore { sE.core with arena_len := dst },
        fullArenaClauseGarbCore { sE.core with arena_len := dst } src = false ∧
        (kM.arena[r + 2]?.getD 0#32).toNat = (sE.core.arena[src + 2]?.getD 0#32).toNat ∧
        ∀ j < (sE.core.arena[src + 2]?.getD 0#32).toNat,
          kM.arena[r + 3 + j]? = sE.core.arena[src + 3 + j]? := by
    intro r hr
    obtain ⟨_, src, hsrc_ch, hsz_e, hlits_e⟩ := hblkM r hr
    have hsrc_mem := refInChain_mem_refs hcmpE.1 first_red rwE hmvE (Or.inr hfr_inE) src hsrc_ch
    exact ⟨src, hsrc_mem, (hcmpE.2.1 src hsrc_mem).2, hsz_e, hlits_e⟩
  obtain ⟨hcmpM_dst, hchain_mem⟩ := compactPrefix_extend_move_chain hcmpE hcmpM_fr'
    harE_len harM_len rfl hdst_cap hmvM hmap
  refine ⟨hcmpM_dst, fun hpos => ?_⟩
  have hrmE' := hrmE hpos
  have hmk' := hrs_marked hpos
  have hpart := moveRangeChain_partition_refs hcmpE_fr.1 hmvE
  intro idx hidx; have h := hrmE' idx hidx; dsimp only at h ⊢
  let v := (s0.core.trl[idx]?.getD 0#32).toNat / 2
  let r0 := s0.core.rsns[v]?.getD 0xFFFFFFFF#32
  have hv_lt : v < sE.core.cur_vars := by
    have := hw0_tl_lt idx hidx; rw [hcv_eq]; exact Nat.div_lt_of_lt_mul this
  change (if r0 = 0xFFFFFFFF#32 ∨ (r0 &&& 0x80000000#32) ≠ 0#32 then _ else _) at h ⊢
  split at h
  · rename_i hc1; simp only [hc1, ↓reduceIte]
    change rsnsM[v]?.getD 0xFFFFFFFF#32 = r0
    have hrsn_v := hrsnsM v hv_lt
    by_cases hcond : first_red ≤ (sE.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat ∧
        (sE.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat < dst ∧
        RefInChain sE.core.arena first_red dst (sE.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat ∧
        (sE.core.arena[(sE.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat]?.getD 0#32 &&&
          0x00200000#32) ≠ 0#32 ∧
        ∃ j < (sE.core.arena[(sE.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat + 2]?.getD 0#32).toNat,
          let lit := (sE.core.arena[(sE.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat + 3 + j]?.getD
            0#32).toNat
          lit / 2 = v ∧ sE.core.vals[lit]?.getD 0#8 = 1#8
    · exfalso
      have h_eq : sE.core.rsns[v]?.getD 0xFFFFFFFF#32 = r0 := h
      rw [h_eq] at hcond
      have hr0_lt : r0.toNat < dst := hcond.2.1
      have hcap_lt : c.arena_cap < 0x80000000 := Nat.lt_trans c.harena (by decide)
      rcases hc1 with hff | hhi
      · rw [hff] at hr0_lt; simp at hr0_lt; omega
      · exact hhi ((bv32_lt_highbit_iff r0).mp (by omega))
    · rw [ite_eq_right (fun h1 => absurd h1 hcond)] at hrsn_v; exact hrsn_v.trans h
  · rename_i hc1; simp only [hc1, ↓reduceIte]
    split at h
    · rename_i hlt_s0
      simp only [hlt_s0, ↓reduceIte]
      obtain ⟨hrE_lt, hrE_lt8, hrE_ne, hrE_lg, hrE_ref, hrE_ng, hrE_lits⟩ := h
      let rE := sE.core.rsns[v]?.getD 0xFFFFFFFF#32
      rcases hpart rE.toNat hrE_ref with ⟨hrE_lt_fr, hrE_fr⟩ | ⟨hrE_ge_fr, hrE_ch⟩
      · have hcond_f : ¬ (first_red ≤ rE.toNat ∧ rE.toNat < dst ∧
            RefInChain sE.core.arena first_red dst rE.toNat ∧
            (sE.core.arena[rE.toNat]?.getD 0#32 &&& 0x00200000#32) ≠ 0#32 ∧
            ∃ j < (sE.core.arena[rE.toNat + 2]?.getD 0#32).toNat,
              let lit := (sE.core.arena[rE.toNat + 3 + j]?.getD 0#32).toNat
              lit / 2 = v ∧ sE.core.vals[lit]?.getD 0#8 = 1#8) := fun h1 => by omega
        have hrsn_v := hrsnsM v hv_lt
        rw [ite_eq_right (fun h1 => absurd h1 hcond_f)] at hrsn_v
        change (rsnsM[v]?.getD 0xFFFFFFFF#32).toNat < dst ∧
          (rsnsM[v]?.getD 0xFFFFFFFF#32).toNat < 0x80000000 ∧
          rsnsM[v]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 ∧
          (rsnsM[v]?.getD 0xFFFFFFFF#32 &&& 0x80000000#32) = 0#32 ∧
          (rsnsM[v]?.getD 0xFFFFFFFF#32).toNat ∈
            fullArenaClauseRefsCore { kM with arena_len := dst } ∧
          fullArenaClauseGarbCore { kM with arena_len := dst }
            (rsnsM[v]?.getD 0xFFFFFFFF#32).toNat = false ∧
          fullArenaClauseLitsCore { kM with arena_len := dst }
            (rsnsM[v]?.getD 0xFFFFFFFF#32).toNat =
            fullArenaClauseLitsCore s0.core r0.toNat
        rw [hrsn_v]
        have hrM_fr : rE.toNat ∈ fullArenaClauseRefsCore { kM with arena_len := first_red } := by
          rw [show fullArenaClauseRefsCore { kM with arena_len := first_red } =
              fullArenaClauseRefsCore { sE.core with arena_len := first_red } from
            hcongr_fr.1]
          exact hrE_fr
        have hmono := fullArenaClauseRefsCore_mono_prefix (k := kM) (alen1 := first_red)
          (alen2 := dst) (by omega) hcmpM_fr'.1 rE.toNat hrM_fr
        have hcgr := hcongr_fr.2 rE.toNat hrE_fr
        have hgb_e : fullArenaClauseGarbCore { sE.core with arena_len := first_red } rE.toNat =
            false := by
          have := (fullArenaClauseRefsCore_mono_prefix (k := sE.core) (alen1 := first_red)
            (alen2 := dst) (by omega) hcmpE_fr.1 rE.toNat hrE_fr).2.1
          rw [← this]; exact hrE_ng
        have hlits_e : fullArenaClauseLitsCore { sE.core with arena_len := first_red } rE.toNat =
            fullArenaClauseLitsCore s0.core r0.toNat := by
          have := (fullArenaClauseRefsCore_mono_prefix (k := sE.core) (alen1 := first_red)
            (alen2 := dst) (by omega) hcmpE_fr.1 rE.toNat hrE_fr).2.2
          rw [← this]; exact hrE_lits
        have hgb_m : fullArenaClauseGarbCore { kM with arena_len := first_red } rE.toNat =
            fullArenaClauseGarbCore
              { sE.core with arena := arM, arena_len := first_red } rE.toNat :=
          rfl
        have hlits_m : fullArenaClauseLitsCore { kM with arena_len := first_red } rE.toNat =
            fullArenaClauseLitsCore
              { sE.core with arena := arM, arena_len := first_red } rE.toNat :=
          rfl
        refine ⟨hrE_lt, hrE_lt8, hrE_ne, hrE_lg, hmono.1, ?_, ?_⟩
        · rw [hmono.2.1, hgb_m, hcgr.1, hgb_e]
        · rw [hmono.2.2, hlits_m, hcgr.2, hlits_e]
      · obtain ⟨hmrk, j, hj, hlv, hval⟩ := hmk' rE.toNat hrE_ch idx hidx rfl
        have hrsn_v := hrsnsM v hv_lt
        have hcond_t : first_red ≤ rE.toNat ∧ rE.toNat < dst ∧
            RefInChain sE.core.arena first_red dst rE.toNat ∧
            (sE.core.arena[rE.toNat]?.getD 0#32 &&& 0x00200000#32) ≠ 0#32 ∧
            ∃ j < (sE.core.arena[rE.toNat + 2]?.getD 0#32).toNat,
              let lit := (sE.core.arena[rE.toNat + 3 + j]?.getD 0#32).toNat
              lit / 2 = v ∧ sE.core.vals[lit]?.getD 0#8 = 1#8 :=
          ⟨hrE_ge_fr, hrE_lt, hrE_ch, hmrk, j, hj, hlv, hval⟩
        dsimp only at hrsn_v
        split at hrsn_v
        · obtain ⟨hfr_r', hr'_dst, hr'_lt8, hr'_ch, hsz'_eq, hlits'_eq⟩ := hrsn_v
          obtain ⟨hr'_mem, hr'_ng, hr'_lits⟩ := hchain_mem _ hr'_ch
          have hne' : rsnsM[v]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 := fun hff => by
            have h1 := congrArg BitVec.toNat hff; simp at h1; omega
          have hlg' : (rsnsM[v]?.getD 0xFFFFFFFF#32 &&& 0x80000000#32) = 0#32 :=
            (bv32_lt_highbit_iff _).mp hr'_lt8
          refine ⟨hr'_dst, hr'_lt8, hne', hlg', hr'_mem, hr'_ng, ?_⟩
          rw [hr'_lits, ← hrE_lits]
          have hlits_r' : fullArenaClauseLitsCore kM (rsnsM[v]?.getD 0xFFFFFFFF#32).toNat =
              fullArenaClauseLitsCore { sE.core with arena_len := dst } rE.toNat := by
            unfold fullArenaClauseLitsCore
            have hszM : fullArenaClauseSizeCore kM (rsnsM[v]?.getD 0xFFFFFFFF#32).toNat =
                fullArenaClauseSizeCore { sE.core with arena_len := dst } rE.toNat := by
              unfold fullArenaClauseSizeCore; exact hsz'_eq
            rw [hszM]
            congr 1
            have hbd1 : (rsnsM[v]?.getD 0xFFFFFFFF#32).toNat + 3 +
                fullArenaClauseSizeCore { sE.core with arena_len := dst } rE.toNat ≤
                kM.arena.length := by
              unfold fullArenaClauseSizeCore
              rw [← hsz'_eq, harM_len]
              exact Nat.le_trans hr'_ch.bounds.2 hdst_cap
            have hbd2 : rE.toNat + 3 +
                fullArenaClauseSizeCore { sE.core with arena_len := dst } rE.toNat ≤
                sE.core.arena.length := by
              unfold fullArenaClauseSizeCore
              rw [harE_len]
              exact Nat.le_trans hrE_ch.bounds.2 hdst_cap
            apply List.ext_getElem
            · simp only [List.length_take, List.length_drop]
              rw [Nat.min_eq_left (Nat.le_sub_of_add_le' hbd1),
                Nat.min_eq_left (Nat.le_sub_of_add_le' hbd2)]
            · intro q hq1 _
              simp only [List.getElem_take, List.getElem_drop]
              have hq : q < fullArenaClauseSizeCore
                  { sE.core with arena_len := dst } rE.toNat := by
                simp only [List.length_take, List.length_drop] at hq1
                exact Nat.lt_of_lt_of_le hq1 (Nat.min_le_left _ _)
              have heq := hlits'_eq q hq
              have h1 := hbd1; have h2 := hbd2
              unfold fullArenaClauseSizeCore at h1 h2 hq
              rw [List.getElem?_eq_getElem (by omega :
                    (rsnsM[v]?.getD 0xFFFFFFFF#32).toNat + 3 + q < kM.arena.length),
                  List.getElem?_eq_getElem (by omega :
                    rE.toNat + 3 + q < sE.core.arena.length)] at heq
              exact Option.some.inj heq
          exact hlits_r'
        · exact absurd hcond_t ‹_›
    · rename_i hnlt_s0
      simp only [hnlt_s0, ↓reduceIte]
      have hrsn_v := hrsnsM v hv_lt
      by_cases hcond : first_red ≤ (sE.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat ∧
          (sE.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat < dst ∧
          RefInChain sE.core.arena first_red dst (sE.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat ∧
          (sE.core.arena[(sE.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat]?.getD 0#32 &&&
            0x00200000#32) ≠ 0#32 ∧
          ∃ j < (sE.core.arena[(sE.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat + 2]?.getD 0#32).toNat,
            let lit := (sE.core.arena[(sE.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat + 3 + j]?.getD
              0#32).toNat
            lit / 2 = v ∧ sE.core.vals[lit]?.getD 0#8 = 1#8
      · exfalso
        have heq : sE.core.rsns[v]?.getD 0xFFFFFFFF#32 = r0 := h
        rw [heq] at hcond
        have hr0_lt : r0.toNat < dst := hcond.2.1
        have hne0 : r0 ≠ 0xFFFFFFFF#32 := fun hff => by
          rw [hff] at hr0_lt; simp at hr0_lt
          have hcap_lt : c.arena_cap < 0x80000000 := Nat.lt_trans c.harena (by decide)
          omega
        have hcap_lt : c.arena_cap < 0x80000000 := Nat.lt_trans c.harena (by decide)
        have hlt8 : r0.toNat < 0x80000000 := by omega
        have hlg0 : (r0 &&& 0x80000000#32) = 0#32 := (bv32_lt_highbit_iff r0).mp hlt8
        have hri := hw0.reason_inv idx hidx hne0
        change (if (r0 &&& 0x80000000#32) ≠ 0#32 then _ else _) at hri
        rw [ite_eq_right (fun h0 => h0 hlg0)] at hri
        have hlt_s0 : r0.toNat < s0.core.arena_len := by
          have := (hw0.arena.refs_wf _ hri.1).1; omega
        contradiction
      · rw [ite_eq_right (fun h1 => absurd h1 hcond)] at hrsn_v
        change rsnsM[v]?.getD 0xFFFFFFFF#32 = r0; exact hrsn_v.trans h

/-! ## 3. `fullMoveRedEndSpec` & `full_move_red_end_m6_wp` -/

open Classical in
def fullMoveRedEndSpec : Spec [i64, i64, i64] [] :=
  fun (h, first_red, dst, ()) m Q _ =>
    ∃ (c : FullCfg) (s : FullState) (rw0 : Nat) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧
      first_red.toNat < dst.toNat ∧ dst.toNat ≤ c.arena_cap ∧
      0 < rw0 ∧ MoveRangeChain s.core.arena first_red.toNat dst.toNat rw0 ∧
      (∀ l < 2 * s.core.cur_vars, s.core.vals[l]?.getD 0#8 = 0#8 ∨
        s.core.vals[l]?.getD 0#8 = 1#8 ∨ s.core.vals[l]?.getD 0#8 = 0xFF#8) ∧
      MoveRedRsnUnique s.core.arena s.core.vals s.core.rsns s.core.cur_vars
        first_red.toNat dst.toNat ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (ar' rsns' : List (BitVec 32)) (fred' : BitVec 64) (sc' : FullScratch)
          (rwOut : Nat) (m' : Mem 64),
        let s' : FullState :=
          { s with
            core := { s.core with arena := ar', rsns := rsns', first_reducible := fred' }
            scratch := sc' }
        ar'.length = c.arena_cap → rsns'.length = c.max_vars → sc'.LengthsOk c →
        sc'.extend_len = s.scratch.extend_len → sc'.work_stk2 = s.scratch.work_stk2 →
        (∀ i < first_red.toNat, ar'[i]? = s.core.arena[i]?) →
        MoveRangeChain ar' first_red.toNat dst.toNat rwOut →
        (∀ r, RefInChain ar' first_red.toNat dst.toNat r →
          (ar'[r]?.getD 0#32 &&& 0x00200000#32) = 0#32 ∧
          ∃ src, RefInChain s.core.arena first_red.toNat dst.toNat src ∧
            (ar'[r + 2]?.getD 0#32).toNat = (s.core.arena[src + 2]?.getD 0#32).toNat ∧
            ∀ j < (s.core.arena[src + 2]?.getD 0#32).toNat,
              ar'[r + 3 + j]? = s.core.arena[src + 3 + j]?) →
        (∀ v < s.core.cur_vars,
          let r0 := s.core.rsns[v]?.getD 0xFFFFFFFF#32
          if first_red.toNat ≤ r0.toNat ∧ r0.toNat < dst.toNat ∧
              RefInChain s.core.arena first_red.toNat dst.toNat r0.toNat ∧
              (s.core.arena[r0.toNat]?.getD 0#32 &&& 0x00200000#32) ≠ 0#32 ∧
              ∃ j < (s.core.arena[r0.toNat + 2]?.getD 0#32).toNat,
                let lit := (s.core.arena[r0.toNat + 3 + j]?.getD 0#32).toNat
                lit / 2 = v ∧ s.core.vals[lit]?.getD 0#8 = 1#8
          then
            let r' := (rsns'[v]?.getD 0xFFFFFFFF#32).toNat
            first_red.toNat ≤ r' ∧ r' < dst.toNat ∧ r' < 0x80000000 ∧
            RefInChain ar' first_red.toNat dst.toNat r' ∧
            (ar'[r' + 2]?.getD 0#32).toNat = (s.core.arena[r0.toNat + 2]?.getD 0#32).toNat ∧
            ∀ j < (s.core.arena[r0.toNat + 2]?.getD 0#32).toNat,
              ar'[r' + 3 + j]? = s.core.arena[r0.toNat + 3 + j]?
          else rsns'[v]?.getD 0xFFFFFFFF#32 = r0) →
        (FullMem c s' ⋆ R) m' → Q () m'

open Classical in
theorem fullMoveRedEndSpec.intro {h first_red dst : BitVec 64} {m : Mem 64}
    {Q : Post []} {X : XPost} (c : FullCfg) (s : FullState) (rw0 : Nat) (R : Mem 64 → Prop)
    (hh : h = c.hdr) (hlen : s.LengthsOk c)
    (hfr : first_red.toNat < dst.toNat) (hdst : dst.toNat ≤ c.arena_cap)
    (hrw : 0 < rw0) (hmv : MoveRangeChain s.core.arena first_red.toNat dst.toNat rw0)
    (hdom : ∀ l < 2 * s.core.cur_vars, s.core.vals[l]?.getD 0#8 = 0#8 ∨
      s.core.vals[l]?.getD 0#8 = 1#8 ∨ s.core.vals[l]?.getD 0#8 = 0xFF#8)
    (huniq : MoveRedRsnUnique s.core.arena s.core.vals s.core.rsns s.core.cur_vars
      first_red.toNat dst.toNat)
    (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ (ar' rsns' : List (BitVec 32)) (fred' : BitVec 64) (sc' : FullScratch)
        (rwOut : Nat) (m' : Mem 64),
      let s' : FullState :=
        { s with
          core := { s.core with arena := ar', rsns := rsns', first_reducible := fred' }
          scratch := sc' }
      ar'.length = c.arena_cap → rsns'.length = c.max_vars → sc'.LengthsOk c →
      sc'.extend_len = s.scratch.extend_len → sc'.work_stk2 = s.scratch.work_stk2 →
      (∀ i < first_red.toNat, ar'[i]? = s.core.arena[i]?) →
      MoveRangeChain ar' first_red.toNat dst.toNat rwOut →
      (∀ r, RefInChain ar' first_red.toNat dst.toNat r →
        (ar'[r]?.getD 0#32 &&& 0x00200000#32) = 0#32 ∧
        ∃ src, RefInChain s.core.arena first_red.toNat dst.toNat src ∧
          (ar'[r + 2]?.getD 0#32).toNat = (s.core.arena[src + 2]?.getD 0#32).toNat ∧
          ∀ j < (s.core.arena[src + 2]?.getD 0#32).toNat,
            ar'[r + 3 + j]? = s.core.arena[src + 3 + j]?) →
      (∀ v < s.core.cur_vars,
        let r0 := s.core.rsns[v]?.getD 0xFFFFFFFF#32
        if first_red.toNat ≤ r0.toNat ∧ r0.toNat < dst.toNat ∧
            RefInChain s.core.arena first_red.toNat dst.toNat r0.toNat ∧
            (s.core.arena[r0.toNat]?.getD 0#32 &&& 0x00200000#32) ≠ 0#32 ∧
            ∃ j < (s.core.arena[r0.toNat + 2]?.getD 0#32).toNat,
              let lit := (s.core.arena[r0.toNat + 3 + j]?.getD 0#32).toNat
              lit / 2 = v ∧ s.core.vals[lit]?.getD 0#8 = 1#8
        then
          let r' := (rsns'[v]?.getD 0xFFFFFFFF#32).toNat
          first_red.toNat ≤ r' ∧ r' < dst.toNat ∧ r' < 0x80000000 ∧
          RefInChain ar' first_red.toNat dst.toNat r' ∧
          (ar'[r' + 2]?.getD 0#32).toNat = (s.core.arena[r0.toNat + 2]?.getD 0#32).toNat ∧
          ∀ j < (s.core.arena[r0.toNat + 2]?.getD 0#32).toNat,
            ar'[r' + 3 + j]? = s.core.arena[r0.toNat + 3 + j]?
        else rsns'[v]?.getD 0xFFFFFFFF#32 = r0) →
      (FullMem c s' ⋆ R) m' → Q () m') :
    fullMoveRedEndSpec (h, first_red, dst, ()) m Q X :=
  ⟨c, s, rw0, R, hh, hlen, hfr, hdst, hrw, hmv, hdom, huniq, hm, hQ⟩

private def MoveRedFallInv (c : FullCfg) (s : FullState) (first_red dst : BitVec 64)
    (R : Mem 64 → Prop) (arg : Tup Val [i64]) (mL : Mem 64) : Prop :=
  let (p, ()) := arg
  first_red.toNat ≤ p.toNat ∧ p.toNat ≤ dst.toNat ∧
  ∃ (arL : List (BitVec 32)) (rwOrig rwRem rwDone : Nat),
    arL.length = c.arena_cap ∧
    (∀ i < first_red.toNat, arL[i]? = s.core.arena[i]?) ∧
    (∀ i, p.toNat ≤ i → arL[i]? = s.core.arena[i]?) ∧
    MoveRangeChain s.core.arena first_red.toNat p.toNat rwOrig ∧
    MoveRangeChain s.core.arena p.toNat dst.toNat rwRem ∧
    MoveRangeChain arL first_red.toNat p.toNat rwDone ∧
    (∀ r, RefInChain s.core.arena first_red.toNat p.toNat r →
      RefInChain arL first_red.toNat p.toNat r ∧
      (arL[r + 2]?.getD 0#32).toNat = (s.core.arena[r + 2]?.getD 0#32).toNat ∧
      ∀ j < (s.core.arena[r + 2]?.getD 0#32).toNat,
        arL[r + 3 + j]? = s.core.arena[r + 3 + j]?) ∧
    (∀ r, RefInChain arL first_red.toNat p.toNat r →
      (arL[r]?.getD 0#32 &&& 0x00200000#32) = 0#32 ∧
      ∃ src, RefInChain s.core.arena first_red.toNat dst.toNat src ∧
        (arL[r + 2]?.getD 0#32).toNat = (s.core.arena[src + 2]?.getD 0#32).toNat ∧
        ∀ j < (s.core.arena[src + 2]?.getD 0#32).toNat,
          arL[r + 3 + j]? = s.core.arena[src + 3 + j]?) ∧
    (FullMem c { s with core := { s.core with arena := arL } } ⋆ R) mL

private theorem full_move_red_buf_call_prep {c : FullCfg} {s : FullState}
    {first_red dst : BitVec 64} {rw0 : Nat} (hlen : s.LengthsOk c)
    (_hfr : first_red.toNat < dst.toNat) (hdst : dst.toNat ≤ c.arena_cap)
    (hmv : MoveRangeChain s.core.arena first_red.toNat dst.toNat rw0) :
    let arPre := s.core.arena.take dst.toNat
    arPre.length = dst.toNat ∧ MoveRangeChain arPre first_red.toNat dst.toNat rw0 ∧
    (∀ i < first_red.toNat,
      ∀ i' < dst.toNat, i' = i → arPre[i']? = s.core.arena[i]?) := by
  intro arPre
  have hal := hlen.core_ok.arena_len_arr
  refine ⟨by simp [arPre, List.length_take, hal, hdst],
    hmv.congr (fun i _ hi => List.getElem?_take_of_lt hi),
    fun i hi i' hi' heq => by subst heq; exact List.getElem?_take_of_lt hi'⟩

open Classical in
theorem full_move_red_end_m6_wp (Γ : Env)
    (hBuf : ∀ a m Q X, fullMoveRedEndBufSpec a m Q X →
      Γ "full_move_red_end_buf_m6" [i64, i64, i64, i64] [] a m Q X) :
    ∀ a m Q X, fullMoveRedEndSpec a m Q X →
      Func.wp Γ full_move_red_end_m6_body a m Q X := by
  rintro ⟨h, first_red, dst, ⟨⟩⟩ m Q X
    ⟨c, s, rw0, R, rfl, hlen, hfr_lt, hdst_cap, hrw_pos, hmv0, hdom, huniq, hm, hQ⟩
  have harc := c.harena; have hmaxv := c.hmaxv; have hscr := c.hscr
  have hal := hlen.core_ok.arena_len_arr
  have hrl := hlen.core_ok.rsns_len; have hsbl := hlen.scratch_ok.scratch_buf_len
  unfold dimacsBound at harc hmaxv hscr
  m6_tiny_lets; m6_nojoin
  -- Loop 1: scan `[first_red, dst)` computing `red_words`
  refine wp_loop_inv
    (fun (x : Tup Val [i64, i64]) mL =>
      let (p, rwAcc, ()) := x
      first_red.toNat ≤ p.toNat ∧ p.toNat ≤ dst.toNat ∧ mL = m ∧
      ∃ rwRem, MoveRangeChain s.core.arena p.toNat dst.toNat rwRem ∧
        rwAcc.toNat + rwRem = rw0)
    (fun (p, _) _ => dst.toNat - p.toNat)
    (fun J1 hLoop1 => by
      m6_tiny_lets; m6_nojoin
      exact hLoop1 (first_red, 0#64, ()) m ⟨Nat.le_refl _, by omega, rfl, rw0, hmv0, by simp⟩)
    (fun J1 (p, rwAcc, ()) mL ⟨hfr_p, hp_dst, hmL, rwRem, hmvRem, hrw_sum⟩ hLoop1 => ?_)
  · rw [hmL]
    m6_to_jnz; apply wp_jnz_of <;> (intro hc; try simp only [Arg.val_var] at hc)
    · have hp_lt : p.toNat < dst.toNat := by c0_cond hc; exact hc
      generalize hp_nat : p.toNat = pn at hmvRem
      cases hmvRem with
      | empty => omega
      | @step _ _ rwTl hp3 _ hsz hfit htl =>
        rw [← hp_nat] at hp3 hsz hfit htl hrw_sum
        have hp2_eq : (p + 2#64).toNat = p.toNat + 2 := bv64_add2_lt (by omega)
        have hp_al : p.toNat < s.core.arena.length := by omega
        have hp2_al : (p + 2#64).toNat < s.core.arena.length := by rw [hp2_eq]; omega
        let hdr := s.core.arena[p.toNat]'hp_al
        let sz32 := s.core.arena[(p + 2#64).toNat]'hp2_al
        have hsz32_nat : sz32.toNat = (s.core.arena[p.toNat + 2]?.getD 0#32).toNat := by
          simp [sz32, hp2_eq,
            List.getElem?_eq_getElem (by omega : p.toNat + 2 < s.core.arena.length)]
        have hhdr_def : hdr = s.core.arena[p.toNat]?.getD 0#32 := by
          simp [hdr, List.getElem?_eq_getElem hp_al]
        have hclen_eq : (3#64 + sz32.setWidth 64).toNat = 3 + sz32.toNat := by
          rw [BitVec.toNat_add, BitVec.toNat_setWidth, show (3#64).toNat = 3 from rfl,
            Nat.mod_eq_of_lt (by have := sz32.isLt; omega), Nat.mod_eq_of_lt (by omega)]
        have hp_nxt : (p + (3#64 + sz32.setWidth 64)).toNat = p.toNat + 3 + sz32.toNat := by
          have := hsz32_nat; have := hfit
          rw [BitVec.toNat_add, hclen_eq, Nat.mod_eq_of_lt (by omega)]; omega
        m6_to_group_strip
        refine wp_join_group
          (fun (rwAcc' : Tup Val [i64]) mJ =>
            m = mJ ∧
            rwAcc'.fst.toNat = rwAcc.toNat +
              if (hdr &&& 0x00400000#32) ≠ 0#32 then 3 + sz32.toNat else 0)
          ?_ ?_
        · rintro _ ⟨rw', ⟨⟩⟩ mJ ⟨rfl, hrw'⟩
          m6_tiny_lets; m6_nojoin
          refine hLoop1 (p + (3#64 + sz32.setWidth 64), rw', ()) m
            (by dsimp only; rw [hp_nxt, hsz32_nat]; omega)
            ⟨by rw [hp_nxt]; omega, by rw [hp_nxt, hsz32_nat]; exact hfit, rfl, rwTl,
             by rw [hp_nxt, hsz32_nat]; exact htl,
             by rw [hrw', hsz32_nat, hhdr_def, Nat.add_assoc]; exact hrw_sum⟩
        · intro Jif hJif
          m6_to_jnz; apply wp_jnz_of <;> (intro hc_red; try simp only [Arg.val_var] at hc_red)
          · have hred_ne : (hdr &&& 0x00400000#32) ≠ 0#32 := by c0_cond hc_red; exact hc_red
            have hrw_add : (rwAcc + (3#64 + sz32.setWidth 64)).toNat =
                rwAcc.toNat + (3 + sz32.toNat) := by
              have : rwAcc.toNat + (3 + sz32.toNat) ≤ rw0 := by
                have h_sum := hrw_sum
                rw [← hhdr_def, ← hsz32_nat] at h_sum
                split at h_sum
                · omega
                · contradiction
              have := hmv0.le
              rw [BitVec.toNat_add, hclen_eq, Nat.mod_eq_of_lt (by omega)]
            m6_tiny_lets; rw [wp_jump]; apply hJif
            refine ⟨rfl, ?_⟩
            dsimp only [vals_cons, vals_nil, Arg.val_var]
            change (rwAcc + (3#64 + sz32.setWidth 64)).toNat = _
            rw [hrw_add]
            split
            · rfl
            · contradiction
          · have hred_0 : (hdr &&& 0x00400000#32) = 0#32 := by c0_cond hc_red; exact hc_red
            m6_tiny_lets; rw [wp_jump]; apply hJif
            refine ⟨rfl, ?_⟩
            dsimp only [vals_cons, vals_nil, Arg.val_var]
            split
            · contradiction
            · simp
    · have hp_eq : p.toNat = dst.toNat := by c0_cond hc; omega
      rw [hp_eq] at hmvRem
      have hrwRem0 : rwRem = 0 := by have := hmvRem.le; omega
      have hrw_eq : rwAcc.toNat = rw0 := by omega
      clear hLoop1 J1
      m6_to_jnz; apply wp_jnz_of <;> (intro hc; try simp only [Arg.val_var] at hc)
      · exfalso; have h0 : rwAcc.toNat = 0 := by
          c0_cond hc; exact congrArg BitVec.toNat hc
        omega
      · m6_to_jnz; apply wp_jnz_of <;> (intro hc_sc; try simp only [Arg.val_var] at hc_sc)
        · -- Branch 1: `red_words <= scratch_cap`
          have hrw_sc : rw0 ≤ c.scratch_cap := by c0_cond hc_sc; omega
          obtain ⟨harPre_l, hmvPre, _⟩ := full_move_red_buf_call_prep hlen hfr_lt hdst_cap hmv0
          let arPre := s.core.arena.take dst.toNat
          let arTail := s.core.arena.drop dst.toNat
          have hm_sp : (array (t := i32) c.pArena arPre ⋆
              array (t := i32) c.pScratchBuf s.scratch.scratch_buf ⋆
              FullMemArenaOut c s ⋆
              (array (t := i32) (c.pArena + BitVec.ofNat 64 (4 * dst.toNat)) arTail ⋆ R)) m := by
            rw [fullMem_eq_arenaOut, array32_split_at (k := dst.toNat) (by omega)] at hm
            exact sep_ac hm
          m6_steps; c0_call hBuf
          refine fullMoveRedEndBufSpec.intro c s arPre s.scratch.scratch_buf rw0
            (array (t := i32) (c.pArena + BitVec.ofNat 64 (4 * dst.toNat)) arTail ⋆ R)
            rfl hlen (by omega) hdst_cap harPre_l (by rw [hsbl]; exact hrw_sc)
            (by unfold dimacsBound; omega) hmvPre hdom huniq.cast_ar hm_sp ?_
          intro arOut bufOut rsns' fred' mid m'
          dsimp only
          intro harO_l hbufO_l hrsns'_l hfr_mid hmid_dst hpreO hmv_lo hmv_hi hblkO hrsnsO _ hmemO
          m6_steps
          let ar' := arOut ++ arTail
          have har'_l : ar'.length = c.arena_cap := by
            simp [ar', harO_l, arTail, List.length_drop, hal]; omega
          have htk' : ar'.take dst.toNat = arOut := by simp [ar', harO_l]
          have hdr' : ar'.drop dst.toNat = arTail := by simp [ar', harO_l]
          let sFin : FullState :=
            { s with
              core := { s.core with arena := ar', rsns := rsns', first_reducible := fred' },
              scratch := { s.scratch with scratch_buf := bufOut } }
          have hm_fin : (FullMem c sFin ⋆ R) m' := by
            rw [fullMem_eq_arenaOut,
              array32_split_at (k := dst.toNat) (by dsimp only [sFin]; rw [har'_l]; exact hdst_cap),
              htk', hdr']
            dsimp only [sFin]
            rw [fullMemArenaOut_congr_arena_buf]
            exact sep_ac hmemO
          have hmv_lo' : MoveRangeChain ar' first_red.toNat mid 0 :=
            hmv_lo.congr (fun i _ hi => by
              dsimp only [ar']; rw [List.getElem?_append_left (by omega)])
          have hmv_hi' : MoveRangeChain ar' mid dst.toNat (dst.toNat - mid) :=
            hmv_hi.congr (fun i _ hi => by
              dsimp only [ar']; rw [List.getElem?_append_left (by omega)])
          have har'_take : ∀ i < dst.toNat, ar'[i]? = arOut[i]? := fun i hi => by
            dsimp only [ar']; rw [List.getElem?_append_left (by omega)]
          exact hQ ar' rsns' fred' { s.scratch with scratch_buf := bufOut }
            (0 + (dst.toNat - mid)) m' har'_l hrsns'_l
            { hlen.scratch_ok with scratch_buf_len := hbufO_l.trans hsbl } rfl rfl
            (fun i hi => by
              rw [har'_take i (by omega), hpreO i hi]
              exact List.getElem?_take_of_lt (by omega))
            (moveRangeChain_append hmv_lo' hmv_hi')
            (fun r hr => by
              have hsp : RefInChain arOut first_red.toNat mid r ∨
                  RefInChain arOut mid dst.toNat r := by
                rcases refInChain_split hmv_lo' hr with h1 | h2
                · exact Or.inl (h1.congr (fun i _ hi => (har'_take i (by omega)).symm))
                · exact Or.inr (h2.congr (fun i _ hi => (har'_take i (by omega)).symm))
              have hrb := hr.bounds
              obtain ⟨hflO, _, src, hsrcPre, hszO, hlitsO⟩ := hblkO r hsp
              have hsrcOrig : RefInChain s.core.arena first_red.toNat dst.toNat src :=
                hsrcPre.congr (fun i _ hi => (List.getElem?_take_of_lt hi).symm)
              have hsrcb := hsrcOrig.bounds
              refine ⟨by rw [har'_take r (by omega)]; exact hflO, src, hsrcOrig, ?_, ?_⟩
              · rw [har'_take (r + 2) (by omega), ← hszO]
                dsimp only [arPre]; rw [List.getElem?_take_of_lt (by omega : src + 2 < dst.toNat)]
              · intro j hj
                have hk_eq : (ar'[r + 2]?.getD 0#32).toNat = (arOut[r + 2]?.getD 0#32).toNat := by
                  rw [har'_take (r + 2) (by have := hrb.2; omega)]
                have hj' : j < (arOut[r + 2]?.getD 0#32).toNat := by
                  rw [← hszO]; dsimp only [arPre]
                  rwa [List.getElem?_take_of_lt (by have := hsrcb.2; omega : src + 2 < dst.toNat)]
                have hlt_r : r + 3 + j < dst.toNat := by
                  have := hrb.2; rw [hk_eq] at this; omega
                rw [har'_take (r + 3 + j) hlt_r, hlitsO j hj']
                exact List.getElem?_take_of_lt (by have := hsrcb.2; omega))
            (fun v hv => by
              have hv0 := hrsnsO v hv; dsimp only at hv0 ⊢
              by_cases hc0 : first_red.toNat ≤ (s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat ∧
                  (s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat < dst.toNat ∧
                  RefInChain s.core.arena first_red.toNat dst.toNat
                    (s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat ∧
                  (s.core.arena[(s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat]?.getD 0#32 &&&
                    0x00200000#32) ≠ 0#32 ∧
                  ∃ j < (s.core.arena[(s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat + 2]?.getD
                    0#32).toNat,
                    let lit := (s.core.arena[(s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat + 3 +
                      j]?.getD 0#32).toNat
                    lit / 2 = v ∧ s.core.vals[lit]?.getD 0#8 = 1#8
              · have hcPre : first_red.toNat ≤ (s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat ∧
                    (s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat < dst.toNat ∧
                    RefInChain arPre first_red.toNat dst.toNat
                      (s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat ∧
                    (arPre[(s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat]?.getD 0#32 &&&
                      0x00200000#32) ≠ 0#32 ∧
                    ∃ j < (arPre[(s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat + 2]?.getD
                      0#32).toNat,
                      let lit := (arPre[(s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat + 3 +
                        j]?.getD 0#32).toNat
                      lit / 2 = v ∧ s.core.vals[lit]?.getD 0#8 = 1#8 := by
                  obtain ⟨h1, h2, h3, h4, j, hj, hlv, hval⟩ := hc0
                  have h3b := h3.bounds
                  rw [← List.getElem?_take_of_lt h2] at h4
                  rw [← List.getElem?_take_of_lt (by have := h3b.2; omega :
                    (s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat + 3 + j < dst.toNat)] at hlv hval
                  rw [← List.getElem?_take_of_lt (by omega :
                    (s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat + 2 < dst.toNat)] at hj
                  exact ⟨h1, h2, h3.congr (fun i _ hi => List.getElem?_take_of_lt hi),
                    h4, j, hj, hlv, hval⟩
                dsimp only at hcPre hc0
                split at hv0
                · split
                  · obtain ⟨ha, hb, hc8, hd, he, hf⟩ := hv0
                    have hch' : RefInChain ar' first_red.toNat dst.toNat
                        (rsns'[v]?.getD 0xFFFFFFFF#32).toNat := by
                      rcases hd with h1 | h2
                      · exact refInChain_append_left hmid_dst
                          (h1.congr (fun i _ hi => har'_take i (by omega)))
                      · exact refInChain_append_right hmv_lo'
                          (h2.congr (fun i _ hi => har'_take i (by omega)))
                    have hrb' := hch'.bounds
                    refine ⟨ha, hb, hc8, hch', ?_, fun j hj => ?_⟩
                    · rw [har'_take _ (by have := hrb'.2; omega), he]
                      dsimp only [arPre]
                      rw [List.getElem?_take_of_lt (by have := hc0.2.2.1.bounds.2; omega)]
                    · have hsz_pre : (arPre[(s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat + 2]?.getD
                          0#32).toNat = (s.core.arena[(s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat +
                          2]?.getD 0#32).toNat := by
                        dsimp only [arPre]
                        rw [List.getElem?_take_of_lt (by have := hc0.2.2.1.bounds.2; omega)]
                      have hj' : j < (arPre[(s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat + 2]?.getD
                          0#32).toNat := by rw [hsz_pre]; exact hj
                      have hlt_r' : (rsns'[v]?.getD 0xFFFFFFFF#32).toNat + 3 + j < dst.toNat := by
                        have h1 := hrb'.2
                        rw [har'_take _ (by omega)] at h1
                        omega
                      rw [har'_take _ hlt_r', hf j hj']
                      exact List.getElem?_take_of_lt (by have := hc0.2.2.1.bounds.2; omega)
                  · exact absurd hc0 ‹_›
                · exact absurd hcPre ‹_›
              · have hcPre_f : ¬ (first_red.toNat ≤ (s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat ∧
                    (s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat < dst.toNat ∧
                    RefInChain arPre first_red.toNat dst.toNat
                      (s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat ∧
                    (arPre[(s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat]?.getD 0#32 &&&
                      0x00200000#32) ≠ 0#32 ∧
                    ∃ j < (arPre[(s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat + 2]?.getD
                      0#32).toNat,
                      let lit := (arPre[(s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat + 3 +
                        j]?.getD 0#32).toNat
                      lit / 2 = v ∧ s.core.vals[lit]?.getD 0#8 = 1#8) := fun hPre => hc0 <| by
                  obtain ⟨h1, h2, h3, h4, j, hj, hlv, hval⟩ := hPre
                  have h3orig := h3.congr (fun i _ hi => (List.getElem?_take_of_lt hi).symm)
                  have h3b := h3orig.bounds
                  dsimp only [arPre] at h4 hj hlv hval
                  rw [List.getElem?_take_of_lt h2] at h4
                  rw [List.getElem?_take_of_lt (by omega :
                    (s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat + 2 < dst.toNat)] at hj
                  rw [List.getElem?_take_of_lt (by omega :
                    (s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat + 3 + j < dst.toNat)] at hlv hval
                  exact ⟨h1, h2, h3orig, h4, j, hj, hlv, hval⟩
                rw [ite_eq_right (fun h => absurd h hcPre_f)] at hv0
                rw [ite_eq_right (fun h => absurd h hc0)]
                exact hv0)
            hm_fin
        · m6_to_jnz; apply wp_jnz_of <;> (intro hc_ar; try simp only [Arg.val_var] at hc_ar)
          · -- Branch 2: `dst + red_words <= arena_cap`
            have hadd_ovf : (dst + rwAcc).toNat = dst.toNat + rw0 := by
              have := hmv0.le; rw [BitVec.toNat_add, hrw_eq, Nat.mod_eq_of_lt (by omega)]
            have hrw_ar : dst.toNat + rw0 ≤ c.arena_cap := by
              c0_cond hc_ar
              rw [hrw_eq, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hc_ar
              exact hc_ar
            obtain ⟨harPre_l, hmvPre, _⟩ := full_move_red_buf_call_prep hlen hfr_lt hdst_cap hmv0
            let arPre := s.core.arena.take dst.toNat
            let arTail := s.core.arena.drop dst.toNat
            have harTail_l : arTail.length = c.arena_cap - dst.toNat := by
              simp [arTail, List.length_drop, hal]
            have hm_sp : (array (t := i32) c.pArena arPre ⋆
                array (t := i32) (c.pArena + dst * 4#64) arTail ⋆
                FullMemArenaOut c s ⋆
                (array (t := i32) c.pScratchBuf s.scratch.scratch_buf ⋆ R)) m := by
              rw [fullMem_eq_arenaOut, array32_split_at (k := dst.toNat) (by omega),
                ← bv64_mul4_eq_ofNat dst] at hm
              exact sep_ac hm
            m6_steps; c0_call hBuf
            refine fullMoveRedEndBufSpec.intro c s arPre arTail rw0
              (array (t := i32) c.pScratchBuf s.scratch.scratch_buf ⋆ R)
              rfl hlen (by omega) hdst_cap harPre_l (by rw [harTail_l]; omega)
              (by unfold dimacsBound; omega) hmvPre hdom huniq.cast_ar hm_sp ?_
            intro arOut bufOut rsns' fred' mid m'
            dsimp only
            intro harO_l hbufO_l hrsns'_l hfr_mid hmid_dst hpreO hmv_lo hmv_hi hblkO hrsnsO _ hmemO
            m6_steps
            let ar' := arOut ++ bufOut
            have har'_l : ar'.length = c.arena_cap := by
              simp [ar', harO_l, hbufO_l, harTail_l]; omega
            have htk' : ar'.take dst.toNat = arOut := by simp [ar', harO_l]
            have hdr' : ar'.drop dst.toNat = bufOut := by simp [ar', harO_l]
            let sFin : FullState :=
              { s with
                core := { s.core with arena := ar', rsns := rsns', first_reducible := fred' } }
            have hm_fin : (FullMem c sFin ⋆ R) m' := by
              rw [fullMem_eq_arenaOut,
                array32_split_at (k := dst.toNat)
                  (by dsimp only [sFin]; rw [har'_l]; exact hdst_cap),
                htk', hdr', ← bv64_mul4_eq_ofNat dst]
              dsimp only [sFin]
              rw [fullMemArenaOut_congr_arena_buf]
              exact sep_ac hmemO
            have hmv_lo' : MoveRangeChain ar' first_red.toNat mid 0 :=
              hmv_lo.congr (fun i _ hi => by
                dsimp only [ar']; rw [List.getElem?_append_left (by omega)])
            have hmv_hi' : MoveRangeChain ar' mid dst.toNat (dst.toNat - mid) :=
              hmv_hi.congr (fun i _ hi => by
                dsimp only [ar']; rw [List.getElem?_append_left (by omega)])
            have har'_take : ∀ i < dst.toNat, ar'[i]? = arOut[i]? := fun i hi => by
              dsimp only [ar']; rw [List.getElem?_append_left (by omega)]
            exact hQ ar' rsns' fred' s.scratch (0 + (dst.toNat - mid)) m' har'_l hrsns'_l
              hlen.scratch_ok rfl rfl
              (fun i hi => by
                rw [har'_take i (by omega), hpreO i hi]
                exact List.getElem?_take_of_lt (by omega))
              (moveRangeChain_append hmv_lo' hmv_hi')
              (fun r hr => by
                have hsp : RefInChain arOut first_red.toNat mid r ∨
                    RefInChain arOut mid dst.toNat r := by
                  rcases refInChain_split hmv_lo' hr with h1 | h2
                  · exact Or.inl (h1.congr (fun i _ hi => (har'_take i (by omega)).symm))
                  · exact Or.inr (h2.congr (fun i _ hi => (har'_take i (by omega)).symm))
                have hrb := hr.bounds
                obtain ⟨hflO, _, src, hsrcPre, hszO, hlitsO⟩ := hblkO r hsp
                have hsrcOrig : RefInChain s.core.arena first_red.toNat dst.toNat src :=
                  hsrcPre.congr (fun i _ hi => (List.getElem?_take_of_lt hi).symm)
                have hsrcb := hsrcOrig.bounds
                refine ⟨by rw [har'_take r (by omega)]; exact hflO, src, hsrcOrig, ?_, ?_⟩
                · rw [har'_take (r + 2) (by omega), ← hszO]
                  dsimp only [arPre]; rw [List.getElem?_take_of_lt (by omega : src + 2 < dst.toNat)]
                · intro j hj
                  have hk_eq : (ar'[r + 2]?.getD 0#32).toNat = (arOut[r + 2]?.getD 0#32).toNat := by
                    rw [har'_take (r + 2) (by have := hrb.2; omega)]
                  have hj' : j < (arOut[r + 2]?.getD 0#32).toNat := by
                    rw [← hszO]; dsimp only [arPre]
                    rwa [List.getElem?_take_of_lt (by have := hsrcb.2; omega : src + 2 < dst.toNat)]
                  have hlt_r : r + 3 + j < dst.toNat := by
                    have := hrb.2; rw [hk_eq] at this; omega
                  rw [har'_take (r + 3 + j) hlt_r, hlitsO j hj']
                  exact List.getElem?_take_of_lt (by have := hsrcb.2; omega))
              (fun v hv => by
                have hv0 := hrsnsO v hv; dsimp only at hv0 ⊢
                by_cases hc0 : first_red.toNat ≤ (s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat ∧
                    (s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat < dst.toNat ∧
                    RefInChain s.core.arena first_red.toNat dst.toNat
                      (s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat ∧
                    (s.core.arena[(s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat]?.getD 0#32 &&&
                      0x00200000#32) ≠ 0#32 ∧
                    ∃ j < (s.core.arena[(s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat + 2]?.getD
                      0#32).toNat,
                      let lit := (s.core.arena[(s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat + 3 +
                        j]?.getD 0#32).toNat
                      lit / 2 = v ∧ s.core.vals[lit]?.getD 0#8 = 1#8
                · have hcPre : first_red.toNat ≤ (s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat ∧
                      (s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat < dst.toNat ∧
                      RefInChain arPre first_red.toNat dst.toNat
                        (s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat ∧
                      (arPre[(s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat]?.getD 0#32 &&&
                        0x00200000#32) ≠ 0#32 ∧
                      ∃ j < (arPre[(s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat + 2]?.getD
                        0#32).toNat,
                        let lit := (arPre[(s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat + 3 +
                          j]?.getD 0#32).toNat
                        lit / 2 = v ∧ s.core.vals[lit]?.getD 0#8 = 1#8 := by
                    obtain ⟨h1, h2, h3, h4, j, hj, hlv, hval⟩ := hc0
                    have h3b := h3.bounds
                    rw [← List.getElem?_take_of_lt h2] at h4
                    rw [← List.getElem?_take_of_lt (by have := h3b.2; omega :
                      (s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat + 3 + j < dst.toNat)] at hlv hval
                    rw [← List.getElem?_take_of_lt (by omega :
                      (s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat + 2 < dst.toNat)] at hj
                    exact ⟨h1, h2, h3.congr (fun i _ hi => List.getElem?_take_of_lt hi),
                      h4, j, hj, hlv, hval⟩
                  dsimp only at hcPre hc0
                  split at hv0
                  · split
                    · obtain ⟨ha, hb, hc8, hd, he, hf⟩ := hv0
                      have hch' : RefInChain ar' first_red.toNat dst.toNat
                          (rsns'[v]?.getD 0xFFFFFFFF#32).toNat := by
                        rcases hd with h1 | h2
                        · exact refInChain_append_left hmid_dst
                            (h1.congr (fun i _ hi => har'_take i (by omega)))
                        · exact refInChain_append_right hmv_lo'
                            (h2.congr (fun i _ hi => har'_take i (by omega)))
                      have hrb' := hch'.bounds
                      refine ⟨ha, hb, hc8, hch', ?_, fun j hj => ?_⟩
                      · rw [har'_take _ (by have := hrb'.2; omega), he]
                        dsimp only [arPre]
                        rw [List.getElem?_take_of_lt (by have := hc0.2.2.1.bounds.2; omega)]
                      · have hsz_pre : (arPre[(s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat + 2]?.getD
                            0#32).toNat = (s.core.arena[(s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat +
                            2]?.getD 0#32).toNat := by
                          dsimp only [arPre]
                          rw [List.getElem?_take_of_lt (by have := hc0.2.2.1.bounds.2; omega)]
                        have hj' : j < (arPre[(s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat + 2]?.getD
                            0#32).toNat := by rw [hsz_pre]; exact hj
                        have hlt_r' : (rsns'[v]?.getD 0xFFFFFFFF#32).toNat + 3 + j < dst.toNat := by
                          have h1 := hrb'.2
                          rw [har'_take _ (by omega)] at h1
                          omega
                        rw [har'_take _ hlt_r', hf j hj']
                        exact List.getElem?_take_of_lt (by have := hc0.2.2.1.bounds.2; omega)
                    · exact absurd hc0 ‹_›
                  · exact absurd hcPre ‹_›
                · have hcPre_f : ¬ (first_red.toNat ≤ (s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat ∧
                      (s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat < dst.toNat ∧
                      RefInChain arPre first_red.toNat dst.toNat
                        (s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat ∧
                      (arPre[(s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat]?.getD 0#32 &&&
                        0x00200000#32) ≠ 0#32 ∧
                      ∃ j < (arPre[(s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat + 2]?.getD
                        0#32).toNat,
                        let lit := (arPre[(s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat + 3 +
                          j]?.getD 0#32).toNat
                        lit / 2 = v ∧ s.core.vals[lit]?.getD 0#8 = 1#8) := fun hPre => hc0 <| by
                    obtain ⟨h1, h2, h3, h4, j, hj, hlv, hval⟩ := hPre
                    have h3orig := h3.congr (fun i _ hi => (List.getElem?_take_of_lt hi).symm)
                    have h3b := h3orig.bounds
                    dsimp only [arPre] at h4 hj hlv hval
                    rw [List.getElem?_take_of_lt h2] at h4
                    rw [List.getElem?_take_of_lt (by omega :
                      (s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat + 2 < dst.toNat)] at hj
                    rw [List.getElem?_take_of_lt (by omega :
                      (s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat + 3 + j < dst.toNat)] at hlv hval
                    exact ⟨h1, h2, h3orig, h4, j, hj, hlv, hval⟩
                  rw [ite_eq_right (fun h => absurd h hcPre_f)] at hv0
                  rw [ite_eq_right (fun h => absurd h hc0)]
                  exact hv0)
              hm_fin
          · -- Branch 3: fallback in-place `PH_RSN` clear over `[first_red, dst)`
            m6_tiny_lets; m6_nojoin
            refine wp_loop_inv (MoveRedFallInv c s first_red dst R)
              (fun (pf, ()) _ => dst.toNat - pf.toNat)
              (fun Jf hLoopF => by
                m6_tiny_lets; m6_nojoin
                exact hLoopF (first_red, ()) m ⟨Nat.le_refl _, by omega, s.core.arena, 0, rw0, 0,
                  hal, fun _ _ => rfl, fun _ _ => rfl, .empty, hmv0, .empty,
                  fun r hr => by exfalso; have := hr.bounds; omega,
                  fun r hr => by exfalso; have := hr.bounds; omega, hm⟩)
              (fun Jf (pf, ()) mf ⟨hfr_pf, hpf_dst, arL, rwOrigF, rwRemF, rwDoneF, harL_l,
                  hpreL, htailL, hmvOrigF, hmvRemF, hmvDoneF, hforL, hblkL, hmf⟩ hLoopF => ?_)
            · m6_to_jnz; apply wp_jnz_of <;> (intro hc_f; try simp only [Arg.val_var] at hc_f)
              · have hpf_lt : pf.toNat < dst.toNat := by c0_cond hc_f; exact hc_f
                generalize hpf_nat : pf.toNat = pfn at hmvRemF
                cases hmvRemF with
                | empty => omega
                | @step _ _ rwTlF hp3 hfl hsz hfit htl =>
                  rw [← hpf_nat] at hp3 hfl hsz hfit htl
                  have hp2_eq : (pf + 2#64).toNat = pf.toNat + 2 := bv64_add2_lt (by omega)
                  have hp_al : pf.toNat < arL.length := by omega
                  have hp2_al : (pf + 2#64).toNat < arL.length := by rw [hp2_eq]; omega
                  let hdrL := arL[pf.toNat]'hp_al
                  let sz32 := arL[(pf + 2#64).toNat]'hp2_al
                  have hsz_eq : sz32.toNat = (s.core.arena[pf.toNat + 2]?.getD 0#32).toNat := by
                    have h1 := congrArg (fun o => (o.getD 0#32).toNat)
                      (htailL (pf.toNat + 2) (by omega))
                    rw [List.getElem?_eq_getElem (by omega : pf.toNat + 2 < arL.length),
                      Option.getD_some] at h1
                    dsimp only [sz32]
                    simpa only [hp2_eq] using h1
                  have hhdr_eq : hdrL = s.core.arena[pf.toNat]?.getD 0#32 := by
                    have h1 := htailL pf.toNat (Nat.le_refl _)
                    simp only [hdrL, List.getElem?_eq_getElem hp_al,
                      List.getElem?_eq_getElem (by omega : pf.toNat < s.core.arena.length)] at h1 ⊢
                    rw [Option.some.inj h1, Option.getD_some]
                  have hp_nxt : (pf + 3#64 + sz32.setWidth 64).toNat =
                      pf.toNat + 3 + sz32.toNat := by
                    rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_setWidth,
                      show (3#64).toNat = 3 from rfl,
                      Nat.mod_eq_of_lt (by have := sz32.isLt; omega),
                      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
                  m6_steps
                  let arL' := arL.set pf.toNat (hdrL &&& ~~~0x00200000#32)
                  have hblk_new : (arL'[pf.toNat]?.getD 0#32 &&& 0x00200000#32) = 0#32 ∧
                      (arL'[pf.toNat]?.getD 0#32 &&& 0x00880000#32) = 0#32 := by
                    rw [List.getElem?_set_self hp_al, Option.getD_some]
                    refine ⟨by rw [BitVec.and_assoc,
                        show (~~~0x00200000#32 &&& 0x00200000#32) = 0#32 from rfl,
                        BitVec.and_zero], ?_⟩
                    rw [BitVec.and_assoc,
                      show (~~~0x00200000#32 &&& 0x00880000#32) = 0x00880000#32 from rfl,
                      hhdr_eq]
                    exact hfl
                  have hmvDone' : MoveRangeChain arL' first_red.toNat
                      (pf.toNat + 3 + sz32.toNat)
                      (rwDoneF + if (arL'[pf.toNat]?.getD 0#32 &&& 0x00400000#32) ≠ 0#32 then
                        3 + (arL'[pf.toNat + 2]?.getD 0#32).toNat else 0) :=
                    moveRangeChain_snoc
                      (hmvDoneF.congr (fun i _ hi => List.getElem?_set_ne (by omega)))
                      (by omega) hblk_new.2
                      (by rw [List.getElem?_set_ne (by omega), htailL (pf.toNat + 2) (by omega)]
                          exact hsz)
                      (by rw [List.getElem?_set_ne (by omega), htailL (pf.toNat + 2) (by omega),
                            ← hsz_eq])
                  have hmvOrig' : MoveRangeChain s.core.arena first_red.toNat
                      (pf.toNat + 3 + sz32.toNat)
                      (rwOrigF + if (s.core.arena[pf.toNat]?.getD 0#32 &&& 0x00400000#32) ≠ 0#32
                        then 3 + (s.core.arena[pf.toNat + 2]?.getD 0#32).toNat else 0) :=
                    moveRangeChain_snoc hmvOrigF (by omega) hfl hsz (by rw [← hsz_eq])
                  have hdone_congr : MoveRangeChain arL' first_red.toNat pf.toNat rwDoneF :=
                    hmvDoneF.congr (fun i _ hi => List.getElem?_set_ne (by omega))
                  refine hLoopF (pf + 3#64 + sz32.setWidth 64, ()) _
                    (by dsimp only; rw [hp_nxt, hsz_eq]; omega)
                    ⟨by rw [hp_nxt]; omega, by rw [hp_nxt, hsz_eq]; exact hfit, arL', _, rwTlF, _,
                     by simp [arL', harL_l],
                     fun i hi => by rw [List.getElem?_set_ne (by omega)]; exact hpreL i hi,
                     fun i hi => by rw [List.getElem?_set_ne (by omega)]
                                    exact htailL i (by rw [hp_nxt] at hi; omega),
                     by rw [hp_nxt]; exact hmvOrig',
                     by rw [hp_nxt, hsz_eq]; exact htl,
                     by rw [hp_nxt]; exact hmvDone',
                     fun r hr => ?_, fun r hr => ?_, by dsimp only [arL', hdrL]; exact hm⟩
                  · rw [hp_nxt] at hr
                    rcases refInChain_split hmvOrigF hr with hprev | hcur
                    · obtain ⟨hrL_p, hsz_p, hlits_p⟩ := hforL r hprev
                      have hpb := hprev.bounds
                      have hrL_nxt : RefInChain arL' first_red.toNat
                          (pf.toNat + 3 + sz32.toNat) r :=
                        refInChain_append_left (by omega)
                          (hrL_p.congr (ar2 := arL')
                            (fun i _ hi => List.getElem?_set_ne (by omega)))
                      refine ⟨by rw [hp_nxt]; exact hrL_nxt,
                        by rw [List.getElem?_set_ne (by omega)]; exact hsz_p,
                        fun j hj => by
                          have := hpb.2
                          rw [List.getElem?_set_ne (by omega)]
                          exact hlits_p j hj⟩
                    · cases hcur with
                      | head =>
                        have hhr : RefInChain arL' first_red.toNat
                            (pf.toNat + 3 + sz32.toNat) pf.toNat :=
                          refInChain_append_right hdone_congr
                            (.head (by omega) hblk_new.2
                              (by rw [List.getElem?_set_ne (by omega),
                                    htailL (pf.toNat + 2) (by omega)]; exact hsz)
                              (by rw [List.getElem?_set_ne (by omega),
                                    htailL (pf.toNat + 2) (by omega), ← hsz_eq]
                                  exact Nat.le_refl _))
                        refine ⟨by rw [hp_nxt]; exact hhr, ?_, ?_⟩
                        · rw [List.getElem?_set_ne (by omega), htailL (pf.toNat + 2) (by omega)]
                        · intro j _; rw [List.getElem?_set_ne (by omega),
                            htailL (pf.toNat + 3 + j) (by omega)]
                      | tail _ _ _ _ hr_tl => exfalso; have := hr_tl.bounds; omega
                  · rw [hp_nxt] at hr
                    rcases refInChain_split hdone_congr hr with hprev | hcur
                    · have hprevL := hprev.congr
                        (fun i _ hi => (List.getElem?_set_ne (by omega)).symm)
                      have hpb := hprevL.bounds
                      obtain ⟨hfl_p, src, hsrc_ch, hsz_p, hlits_p⟩ := hblkL r hprevL
                      rw [hsz_p] at hpb
                      refine ⟨by rw [List.getElem?_set_ne (by omega)]; exact hfl_p, src, hsrc_ch,
                        by rw [List.getElem?_set_ne (by omega)]; exact hsz_p,
                        fun j hj => by
                          rw [List.getElem?_set_ne (by have := hpb.2; omega)]
                          exact hlits_p j hj⟩
                    · have hsz_arL' : (arL'[pf.toNat + 2]?.getD 0#32).toNat = sz32.toNat := by
                        rw [List.getElem?_set_ne (by omega),
                          htailL (pf.toNat + 2) (by omega), ← hsz_eq]
                      cases hcur with
                      | head =>
                        have hpf_ch : RefInChain s.core.arena first_red.toNat dst.toNat
                            pf.toNat :=
                          refInChain_append_left hfit
                            (refInChain_append_right hmvOrigF
                              (.head (by omega) hfl hsz (by rw [← hsz_eq]; exact Nat.le_refl _)))
                        refine ⟨hblk_new.1, pf.toNat, hpf_ch, ?_, ?_⟩
                        · rw [List.getElem?_set_ne (by omega), htailL (pf.toNat + 2) (by omega)]
                        · intro j _; rw [List.getElem?_set_ne (by omega),
                            htailL (pf.toNat + 3 + j) (by omega)]
                      | tail _ _ _ _ hr_tl =>
                        exfalso; rw [hsz_arL'] at hr_tl; have := hr_tl.bounds; omega
              · have hpf_eq : pf.toNat = dst.toNat := by c0_cond hc_f; omega
                rw [hpf_eq] at hmvDoneF hforL hblkL
                m6_steps
                exact hQ arL s.core.rsns first_red s.scratch rwDoneF _ harL_l hrl hlen.scratch_ok
                  rfl rfl hpreL hmvDoneF hblkL (fun v hv => by
                    dsimp only
                    split
                    · next hcond =>
                      obtain ⟨h1, h2, h3, _, _, _, _, _⟩ := hcond
                      obtain ⟨hch_L, hsz_L, hlits_L⟩ :=
                        hforL (s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat h3
                      exact ⟨h1, h2, by have := hdst_cap; omega, hch_L, hsz_L, hlits_L⟩
                    · rfl)
                  hm

theorem fullMoveRedEndSpec_xirrel {a m Q X X'}
    (h : fullMoveRedEndSpec a m Q X) : fullMoveRedEndSpec a m Q X' := h

end LeanQbe.T.Examples.Kissat.FullM6WatchGc
