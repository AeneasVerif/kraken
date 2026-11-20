module

public import LeanQbe.T.Frontend.C0
public import LeanQbe.T.FlatLemmas
public import LeanQbe.T.Logic.C0Agrees
meta import LeanQbe.T.Frontend.C0

/-!
# End-to-end test of `C0Agrees` (`AgreesExcept` algebra + `SafetySlice` combinators)

Tests both `wp_loop_agreesExcept` and `wp_safety_slice` (plus `SafetySlice.spec`,
`wp_safety_slice_call`, `wp_loop_safety_slice{,_state,_break}`, `PrefixAgrees`, `SliceAgrees`,
`OutsideSliceAgrees`, and `open scoped LeanQbe.T.C0Agrees` with `grind`) on a realistic
17-field, 5-array Kissat-style C0 solver module:

* **17-field `KsHdr` struct** (`KsHdr.sizeof = 136`): 5 immutable array pointers (`p_vals`,
  `p_trl`, `p_scores`, `p_phases`, `p_wit`), 6 core soundness fields (`nvars`, `nclauses`,
  `trail_end`, `level`, `propagated`, `status`), and 6 heuristic/WalkSAT/witness scratch fields
  (`heap_len`, `score_inc`, `walk_flips`, `phase_epoch`, `wit_len`, `ticks`).
* **5 arrays in memory**: core `vals` (`u8[2*nvars]`), core `trl` (`u32[nvars]`), and scratch
  `scores` (`u64[nvars]`), `phases` (`u8[nvars]`), `wit` (`u32[nvars]`).
* **6 linked C0 functions** (`Env.ofTable_moduleOk`, `Env.ofTable_noExit`):
  1. `ks_rephase_rescale`: safety-only SSA loop (`wp_loop_safety_slice_pure`).
  2. `ks_walksat_pass`: calls `ks_rephase_rescale` (`wp_safety_slice_call`) + state-measure loop
     (`wp_loop_safety_slice_state_pure`).
  3. `ks_find_unassigned`: read-only core scan with `break` (`wp_loop_safety_slice_pure`, with
     the forward break-join unrolled automatically by `c0_agrees_steps!`).
  4. `ks_decay_window`: SSA loop via `wp_loop_agreesExcept_mem` (and direct `wp_loop_agreesExcept`)
     with `OutsideSliceAgrees`.
  5. `ks_backtrack`: core-mutating trail pop (`wp_loop_agreesExcept_state_mem`, `PrefixAgrees`).
  6. `ks_search_step`: top-level CDCL caller holding `CoreSoundInv`, transporting `CoreSoundInv`
     across `ks_walksat_pass` in one step (`wp_safety_slice_call`), then calling `ks_backtrack`.

## Proof-to-C0 LOC ratio

Counted as non-blank lines of this file:
* C0 code of the six functions (`void ks_rephase_rescale` .. closing `}` of `ks_search_step`): 72.
* The six `*_wp` theorems, statements and proofs (`ks_rephase_wp` .. `ks_search_wp`): 148,
  i.e. **2.06 : 1** (target `<= 3 : 1`).
* Also counting all six `Spec` definitions and three masks (`decayMask`, `btMask`, `scratchMask`,
  43 non-blank lines): 191, i.e. **2.65 : 1** (still `<= 3 : 1`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbeTest.T.C0AgreesTest

open LeanQbe.T
open LeanQbe.T.Frontend.C0
open LeanQbe.T.C0Step
open scoped LeanQbe.T.C0Agrees

/-! ## 1. Realistic 17-field, 5-array Kissat-style C0 litmus module -/

c0_decl_and_layout! ks "
typedef struct {
  u64 p_vals; u64 p_trl; u64 p_scores; u64 p_phases; u64 p_wit;
  u64 nvars; u64 nclauses; u64 trail_end; u64 level; u64 propagated; u64 status;
  u64 heap_len; u64 score_inc; u64 walk_flips; u64 phase_epoch; u64 wit_len; u64 ticks;
} KsHdr;

void ks_rephase_rescale(KsHdr *s) {
  u64 n = s->nvars;
  u64 v = 0ULL;
  while (v < n) {
    ((u64 *)s->p_scores)[v] = ((u64 *)s->p_scores)[v] >> 1ULL;
    u8 pv = ((u8 *)s->p_vals)[v + v];
    if (pv != (u8)0) { ((u8 *)s->p_phases)[v] = pv; }
    ((u32 *)s->p_wit)[v] = (u32)v;
    s->ticks = s->ticks + 1ULL;
    v = v + 1ULL;
  }
  s->score_inc = s->score_inc >> 1ULL;
  s->phase_epoch = s->phase_epoch + 1ULL;
}

u64 ks_walksat_pass(KsHdr *s, u64 budget) {
  ks_rephase_rescale(s);
  u64 n = s->nvars;
  if (n == 0ULL) { return 0ULL; }
  u64 flipped = 0ULL;
  while (s->walk_flips < budget) {
    u64 idx = s->walk_flips % n;
    ((u8 *)s->p_phases)[idx] = ((u8 *)s->p_phases)[idx] ^ (u8)1;
    ((u32 *)s->p_wit)[idx] = (u32)idx;
    s->walk_flips = s->walk_flips + 1ULL;
    s->wit_len = idx + 1ULL;
    flipped = flipped + 1ULL;
  }
  return flipped;
}

u64 ks_find_unassigned(KsHdr *s) {
  u64 n = s->nvars;
  u64 v = 0ULL;
  u64 found = n;
  while (v < n) {
    s->ticks = s->ticks + 1ULL;
    if (((u8 *)s->p_vals)[v + v] == (u8)0) {
      found = v;
      break;
    }
    v = v + 1ULL;
  }
  return found;
}

void ks_decay_window(KsHdr *s, u64 lim) {
  u64 i = 0ULL;
  while (i < lim) {
    ((u64 *)s->p_scores)[i] = ((u64 *)s->p_scores)[i] >> 1ULL;
    s->ticks = s->ticks + 1ULL;
    i = i + 1ULL;
  }
}

void ks_backtrack(KsHdr *s, u64 target_te, u64 target_lvl) {
  while (target_te < s->trail_end) {
    s->trail_end = s->trail_end - 1ULL;
    u32 lit = ((u32 *)s->p_trl)[s->trail_end];
    u64 l64 = (u64)lit;
    u64 v = l64 >> 1ULL;
    if (v < s->nvars) {
      ((u8 *)s->p_phases)[v] = (u8)((lit & 1u) ^ 1u);
      ((u8 *)s->p_vals)[l64] = (u8)0;
      ((u8 *)s->p_vals)[l64 ^ 1ULL] = (u8)0;
    }
    s->ticks = s->ticks + 1ULL;
  }
  s->level = target_lvl;
  if (s->trail_end < s->propagated) { s->propagated = s->trail_end; }
}

u64 ks_search_step(KsHdr *s, u64 budget, u64 target_te, u64 target_lvl) {
  u64 flips = ks_walksat_pass(s, budget);
  ks_backtrack(s, target_te, target_lvl);
  return flips;
}
"

example : KsHdr.sizeof = 136 := rfl

/-! ## 2. Solver state, core soundness projection, `SafetySlice`, and masks -/

structure KsState where
  hdr : KsHdr
  vals : List (BitVec 8)
  trl : List (BitVec 32)
  scores : List (BitVec 64)
  phases : List (BitVec 8)
  wit : List (BitVec 32)

/-- Core soundness projection: immutable geometry/pointers + core scalar fields + core arrays. -/
structure KsCore where
  p_vals : BitVec 64
  p_trl : BitVec 64
  p_scores : BitVec 64
  p_phases : BitVec 64
  p_wit : BitVec 64
  nvars : BitVec 64
  nclauses : BitVec 64
  trail_end : BitVec 64
  level : BitVec 64
  propagated : BitVec 64
  status : BitVec 64
  vals : List (BitVec 8)
  trl : List (BitVec 32)

def ksCoreProj (s : KsState) : KsCore :=
  ⟨s.hdr.p_vals, s.hdr.p_trl, s.hdr.p_scores, s.hdr.p_phases, s.hdr.p_wit,
   s.hdr.nvars, s.hdr.nclauses, s.hdr.trail_end, s.hdr.level, s.hdr.propagated,
   s.hdr.status, s.vals, s.trl⟩

def KsMem (sp : BitVec 64) (s : KsState) : Mem 64 → Prop :=
  KsHdr.At sp s.hdr ⋆
  array (t := i8) s.hdr.p_vals s.vals ⋆
  array (t := i32) s.hdr.p_trl s.trl ⋆
  array (t := i64) s.hdr.p_scores s.scores ⋆
  array (t := i8) s.hdr.p_phases s.phases ⋆
  array (t := i32) s.hdr.p_wit s.wit

structure KsSafe (s : KsState) : Prop where
  nvars_lt : s.hdr.nvars.toNat < 2 ^ 30
  trail_le : s.hdr.trail_end.toNat ≤ s.hdr.nvars.toNat
  vals_len : s.vals.length = 2 * s.hdr.nvars.toNat
  trl_len : s.trl.length = s.hdr.nvars.toNat
  scores_len : s.scores.length = s.hdr.nvars.toNat
  phases_len : s.phases.length = s.hdr.nvars.toNat
  wit_len_arr : s.wit.length = s.hdr.nvars.toNat

/-- Safety slice for all heuristic / WalkSAT / phase / witness-scratch C0 functions. -/
abbrev ksSlice (sp : BitVec 64) : SafetySlice KsState KsCore :=
  ⟨KsMem sp, ksCoreProj, KsSafe⟩

/-- Trail-values consistency over `KsCore` (independent of `propagated` cursor). -/
structure TrailValsInv (k : KsCore) : Prop where
  nvars_lt : k.nvars.toNat < 2 ^ 30
  trail_le : k.trail_end.toNat ≤ k.nvars.toNat
  trail_lits_lt : ∀ i < k.trail_end.toNat, (k.trl[i]?.getD 0#32).toNat < 2 * k.nvars.toNat
  trail_vars_nodup : ∀ i j, i < k.trail_end.toNat → j < k.trail_end.toNat →
    (k.trl[i]?.getD 0#32).toNat / 2 = (k.trl[j]?.getD 0#32).toNat / 2 → i = j
  trail_true : ∀ i < k.trail_end.toNat,
    k.vals[(k.trl[i]?.getD 0#32).toNat]?.getD 0#8 = 1#8
  trail_neg_false : ∀ i < k.trail_end.toNat,
    k.vals[(k.trl[i]?.getD 0#32).toNat ^^^ 1]?.getD 0#8 = 0xFF#8

/-- Core soundness invariant depending ONLY on `KsCore`. -/
structure CoreSoundInv (k : KsCore) : Prop where
  tv : TrailValsInv k
  prop_le : k.propagated.toNat ≤ k.trail_end.toNat

/-- Mask for `ks_decay_window` (only mutates `scores` and `ticks`). -/
abbrev decayMask (s : KsState) : KsState :=
  { s with hdr := { s.hdr with ticks := 0 }, scores := [] }

/-- Mask for `ks_backtrack` (only mutates `trail_end`, `level`, `propagated`, `ticks`,
`vals`, `phases`). The remaining 13 struct fields and 3 arrays are framed automatically. -/
abbrev btMask (s : KsState) : KsState :=
  { s with
    hdr := { s.hdr with trail_end := 0, level := 0, propagated := 0, ticks := 0 },
    vals := [], phases := [] }

/-- Mask for scratch-only mutations (subsumes `decayMask`). -/
abbrev scratchMask (s : KsState) : KsState :=
  { s with
    hdr := { s.hdr with
      heap_len := 0, score_inc := 0, walk_flips := 0, phase_epoch := 0, wit_len := 0, ticks := 0 },
    scores := [], phases := [], wit := [] }

/-! ## 3. Small pure bitvector / invariant step helpers -/

private theorem bv64_lshr1_nat (x : BitVec 64) : (x >>> (1 : Nat)).toNat = x.toNat / 2 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

private theorem bv64_lshr1_toNat (x : BitVec 64) : (x >>> 1#64).toNat = x.toNat / 2 :=
  bv64_lshr1_nat x

private theorem nat_xor1_eq (n : Nat) : n ^^^ 1 = n + 1 - 2 * (n % 2) := by
  apply Nat.eq_of_testBit_eq; intro b
  cases b with
  | zero => simp [Nat.testBit_zero]; omega
  | succ k =>
    have h2 : (n + 1 - 2 * (n % 2)) / 2 = n / 2 := by omega
    have h1 : (1 / 2 : Nat) = 0 := rfl
    rw [Nat.testBit_xor, Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_succ, h1, h2]
    simp

private theorem bv64_xor1_toNat (x : BitVec 64) :
    (x ^^^ 1#64).toNat = x.toNat + 1 - 2 * (x.toNat % 2) := by
  rw [BitVec.toNat_xor, BitVec.toNat_ofNat]
  exact nat_xor1_eq x.toNat

private theorem bv64_xor1_one (x : BitVec 64) :
    (x ^^^ (1 : BitVec 64)).toNat = x.toNat + 1 - 2 * (x.toNat % 2) :=
  bv64_xor1_toNat x

private theorem bv8_zext32_eq0 (b : BitVec 8) : b.setWidth 32 = 0#32 ↔ b = 0#8 := by
  constructor
  · intro h; apply BitVec.eq_of_toNat_eq
    have ht := congrArg BitVec.toNat h
    bv_omega
  · rintro rfl; rfl

attribute [local bv_c0] List.length_set bv64_lshr1_nat bv64_lshr1_toNat
  bv64_xor1_toNat bv64_xor1_one

private theorem ksSafe_set_scratch {s : KsState} (h : KsSafe s)
    {sc : List (BitVec 64)} {ph : List (BitVec 8)} {wi : List (BitVec 32)}
    {hl si wf pe wl tk : BitVec 64}
    (hsc : sc.length = s.scores.length) (hph : ph.length = s.phases.length)
    (hwi : wi.length = s.wit.length) :
    KsSafe { s with
      hdr := { s.hdr with heap_len := hl, score_inc := si, walk_flips := wf,
                          phase_epoch := pe, wit_len := wl, ticks := tk },
      scores := sc, phases := ph, wit := wi } :=
  ⟨h.nvars_lt, h.trail_le, h.vals_len, h.trl_len,
    hsc.trans h.scores_len, hph.trans h.phases_len, hwi.trans h.wit_len_arr⟩

private theorem ksSafe_bt_step {s : KsState} (h : KsSafe s)
    {te : BitVec 64} (hte : te.toNat ≤ s.hdr.nvars.toNat)
    {vs ph : List (BitVec 8)} {tk : BitVec 64}
    (hvs : vs.length = s.vals.length) (hph : ph.length = s.phases.length) :
    KsSafe { s with hdr := { s.hdr with trail_end := te, ticks := tk },
                    vals := vs, phases := ph } :=
  ⟨h.nvars_lt, hte, hvs.trans h.vals_len, h.trl_len,
    h.scores_len, hph.trans h.phases_len, h.wit_len_arr⟩

private theorem trailVals_pop_step {s : KsState} (hs : KsSafe s) (htv : TrailValsInv (ksCoreProj s))
    (hpos : 0 < s.hdr.trail_end.toNat) {lit : BitVec 32} {ph : List (BitVec 8)} {tk : BitVec 64}
    (hl : s.trl[(s.hdr.trail_end - 1).toNat]'(by
      have := hs.trail_le; have := hs.trl_len; bv_omega) = lit) :
    let te' := s.hdr.trail_end - 1
    let l64 := lit.setWidth 64
    TrailValsInv (ksCoreProj
      { s with hdr := { s.hdr with trail_end := te', ticks := tk },
               vals := (s.vals.set l64.toNat 0#8).set (l64 ^^^ 1).toNat 0#8,
               phases := ph }) := by
  intro te' l64
  have hte' : (s.hdr.trail_end - 1).toNat = s.hdr.trail_end.toNat - 1 := by bv_omega
  have hl64 : l64.toNat = lit.toNat := bv_c0_zext32_64 lit
  have hxor : (l64 ^^^ 1).toNat / 2 = lit.toNat / 2 := by
    rw [bv64_xor1_one, hl64]; omega
  have hget : (s.trl[te'.toNat]?.getD 0#32) = lit := by
    have hte_lt : (s.hdr.trail_end - 1).toNat < s.trl.length := by
      have := hs.trl_len; have := hs.trail_le; omega
    dsimp only [te']
    rw [getElem?_getD_of_lt _ hte_lt, hl]
  refine ⟨htv.nvars_lt, by dsimp only [ksCoreProj]; rw [hte']; have := hs.trail_le; omega,
    fun i hi => htv.trail_lits_lt i (by dsimp only [ksCoreProj] at hi ⊢; rw [hte'] at hi; omega),
    fun i j hi hj => htv.trail_vars_nodup i j
      (by dsimp only [ksCoreProj] at hi ⊢; rw [hte'] at hi; omega)
      (by dsimp only [ksCoreProj] at hj ⊢; rw [hte'] at hj; omega), ?_, ?_⟩
  · intro i hi
    have hi' : i < (ksCoreProj s).trail_end.toNat := by
      dsimp only [ksCoreProj] at hi ⊢; rw [hte'] at hi; omega
    have hne : (s.trl[i]?.getD 0#32).toNat / 2 ≠ lit.toNat / 2 := fun heq =>
      (by dsimp only [ksCoreProj] at hi; omega : i ≠ te'.toNat)
        (htv.trail_vars_nodup i te'.toNat hi' (by dsimp only [ksCoreProj, te']; rw [hte']; omega)
          (by dsimp only [ksCoreProj]; rw [hget]; exact heq))
    dsimp only [ksCoreProj]
    rw [getElem?_getD_set_ne _ _ _ (by omega), getElem?_getD_set_ne _ _ _ (by omega)]
    exact htv.trail_true i hi'
  · intro i hi
    have hi' : i < (ksCoreProj s).trail_end.toNat := by
      dsimp only [ksCoreProj] at hi ⊢; rw [hte'] at hi; omega
    have hne : (s.trl[i]?.getD 0#32).toNat / 2 ≠ lit.toNat / 2 := fun heq =>
      (by dsimp only [ksCoreProj] at hi; omega : i ≠ te'.toNat)
        (htv.trail_vars_nodup i te'.toNat hi' (by dsimp only [ksCoreProj, te']; rw [hte']; omega)
          (by dsimp only [ksCoreProj]; rw [hget]; exact heq))
    have hxi : ((s.trl[i]?.getD 0#32).toNat ^^^ 1) / 2 = (s.trl[i]?.getD 0#32).toNat / 2 := by
      rw [nat_xor1_eq]; omega
    dsimp only [ksCoreProj]
    rw [getElem?_getD_set_ne _ _ _ (by omega), getElem?_getD_set_ne _ _ _ (by omega)]
    exact htv.trail_neg_false i hi'

/-! ## 4. Contracts (`SafetySlice.spec` + `AgreesExcept`) -/

def ksRephaseSpec : Spec [i64] [] :=
  SafetySlice.spec ksSlice (fun sp (p, ()) _ => p = sp)

def ksWalksatSpec : Spec [i64, i64] [i64] :=
  SafetySlice.spec ksSlice (fun sp (p, _, ()) _ => p = sp)

def ksFindUnassignedSpec : Spec [i64] [i64] :=
  SafetySlice.spec ksSlice (fun sp (p, ()) _ => p = sp)
    (fun _ _ (r, ()) s _ =>
      (r.toNat < s.hdr.nvars.toNat ∧ s.vals[2 * r.toNat]?.getD 0#8 = 0#8) ∨
      (r = s.hdr.nvars ∧ ∀ w < s.hdr.nvars.toNat, s.vals[2 * w]?.getD 0#8 ≠ 0#8))

def ksDecayWindowSpec : Spec [i64, i64] [] := fun (sp, lim, ()) m Q _ =>
  ∃ (s : KsState) (R : Mem 64 → Prop),
    KsSafe s ∧ lim.toNat ≤ s.hdr.nvars.toNat ∧ (KsMem sp s ⋆ R) m ∧
    ∀ s' m', AgreesExcept decayMask s s' → KsSafe s' →
      OutsideSliceAgrees 0 lim.toNat s.scores s'.scores →
      (KsMem sp s' ⋆ R) m' → Q () m'

def ksBacktrackSpec : Spec [i64, i64, i64] [] := fun (sp, tgt, tlvl, ()) m Q _ =>
  ∃ (s : KsState) (R : Mem 64 → Prop),
    KsSafe s ∧ CoreSoundInv (ksCoreProj s) ∧ (KsMem sp s ⋆ R) m ∧
    ∀ s' m', AgreesExcept btMask s s' → KsSafe s' → CoreSoundInv (ksCoreProj s') →
      s'.hdr.trail_end.toNat = min s.hdr.trail_end.toNat tgt.toNat →
      s'.hdr.level = tlvl → PrefixAgrees s'.hdr.trail_end.toNat s.trl s'.trl →
      (KsMem sp s' ⋆ R) m' → Q () m'

def ksSearchStepSpec : Spec [i64, i64, i64, i64] [i64] :=
  fun (sp, _budget, tgt, tlvl, ()) m Q _ =>
    ∃ (s : KsState) (R : Mem 64 → Prop),
      KsSafe s ∧ CoreSoundInv (ksCoreProj s) ∧ (KsMem sp s ⋆ R) m ∧
      ∀ r s' m', KsSafe s' → CoreSoundInv (ksCoreProj s') →
        s'.hdr.trail_end.toNat = min s.hdr.trail_end.toNat tgt.toNat →
        s'.hdr.level = tlvl → (KsMem sp s' ⋆ R) m' → Q (r, ()) m'

/-! ## 5. `Func.wp` proofs (demonstrating `<= 3:1` proof-to-C0 LOC ratio) -/

theorem ks_rephase_wp (Γ : Env) :
    ∀ a m Q X, ksRephaseSpec a m Q X → Func.wp Γ ks_rephase_rescale_body a m Q X := by
  rintro ⟨p, ⟨⟩⟩ m Q X ⟨sp, s, R, rfl, hsafe, hm, hQ⟩
  have hnv := hsafe.nvars_lt; dsimp only [ksSlice, KsMem] at hm; c0_agrees_steps!
  refine wp_loop_safety_slice_pure (ts := [i64]) (ksSlice p) s R
    (fun _ v => v.1.toNat ≤ s.hdr.nvars.toNat) (fun v => s.hdr.nvars.toNat - v.1.toNat)
    (fun L hL => by c0_agrees_steps!; exact hL s (0#64, ()) m hm rfl hsafe (by simp))
    (fun L s' (v, ()) ml hcore hs' hvle hml hL => ?_)
  have hvl := hs'.vals_len; have hsl := hs'.scores_len
  have hpl := hs'.phases_len; have hwl := hs'.wit_len_arr
  have hnv' : s'.hdr.nvars = s.hdr.nvars := hcore.get KsCore.nvars
  rw [hnv'] at hvl hsl hpl hwl; dsimp only [ksSlice, KsMem] at hml; c0_agrees_steps!
  · refine hL { s' with hdr := { s'.hdr with ticks := s'.hdr.ticks + 1 },
                        scores := _, phases := _, wit := _ }
      (v + 1, ()) m (by dsimp only [ksSlice, KsMem]; c0_frame) (by c0_bound) rfl
      (ksSafe_set_scratch hs' (by simp) (by simp) (by simp)) (by c0_bound)
  · refine hL { s' with hdr := { s'.hdr with ticks := s'.hdr.ticks + 1 }, scores := _, wit := _ }
      (v + 1, ()) m (by dsimp only [ksSlice, KsMem]; c0_frame) (by c0_bound) rfl
      (ksSafe_set_scratch hs' (by simp) rfl (by simp)) (by c0_bound)
  · exact hQ () { s' with hdr := { s'.hdr with score_inc := s'.hdr.score_inc >>> 1,
                                               phase_epoch := s'.hdr.phase_epoch + 1 } } m
      hcore (ksSafe_set_scratch hs' rfl rfl rfl) trivial (by dsimp only [ksSlice, KsMem]; c0_frame)

theorem ks_walksat_wp (Γ : Env)
    (hRephase : ∀ a m Q X, ksRephaseSpec a m Q X → Γ "ks_rephase_rescale" [i64] [] a m Q X) :
    ∀ a m Q X, ksWalksatSpec a m Q X → Func.wp Γ ks_walksat_pass_body a m Q X := by
  rintro ⟨p, budget, ⟨⟩⟩ m Q X ⟨sp, s, R, rfl, hsafe, hm, hQ⟩
  c0_agrees_steps!
  refine wp_safety_slice_call (c := p) hRephase (fun _ => True) trivial rfl hsafe hm
    fun () s1 m1 hcore1 hs1 _ _ hm1 => ?_
  have hnv1 := hs1.nvars_lt; dsimp only [ksSlice, KsMem] at hm1; c0_agrees_steps!
  · exact hQ (0#64, ()) s1 m1 hcore1 hs1 trivial hm1
  · have hn0 : s1.hdr.nvars ≠ 0#64 := hc
    refine wp_loop_safety_slice_state_pure (ts := [i64]) (ksSlice p) s1 R (fun _ _ => True)
      (fun s' _ => budget.toNat - s'.hdr.walk_flips.toNat)
      (fun L hL => by c0_agrees_steps!; exact hL s1 (0#64, ()) m1 hm1 rfl hs1 trivial)
      (fun L s' (fl, ()) ml hcore2 hs' _ hml hL => ?_)
    have hpl := hs'.phases_len; have hwl := hs'.wit_len_arr
    have hnv' : s'.hdr.nvars = s1.hdr.nvars := hcore2.get KsCore.nvars
    rw [hnv'] at hpl hwl
    have hmod : (s'.hdr.walk_flips % s1.hdr.nvars).toNat < s1.hdr.nvars.toNat := by
      rw [BitVec.toNat_umod]; exact Nat.mod_lt _ (by bv_omega)
    dsimp only [ksSlice, KsMem] at hml; c0_agrees_steps!
    · refine hL { s' with
          hdr := { s'.hdr with walk_flips := s'.hdr.walk_flips + 1,
                               wit_len := s'.hdr.walk_flips % s1.hdr.nvars + 1 },
          phases := _, wit := _ }
        (fl + 1, ()) m (by dsimp only [ksSlice, KsMem]; c0_frame) (by bv_omega) rfl
        (ksSafe_set_scratch hs' rfl (by simp) (by simp)) trivial
    · exact hQ (fl, ()) s' ml (hcore1.trans hcore2) hs' trivial hml

theorem ks_find_wp (Γ : Env) :
    ∀ a m Q X, ksFindUnassignedSpec a m Q X → Func.wp Γ ks_find_unassigned_body a m Q X := by
  rintro ⟨p, ⟨⟩⟩ m Q X ⟨sp, s, R, rfl, hsafe, hm, hQ⟩
  have hnv := hsafe.nvars_lt; dsimp only [ksSlice, KsMem] at hm; c0_agrees_steps!
  refine wp_loop_safety_slice_pure (ts := [i64]) (ksSlice p) s R
    (fun _ (v, ()) => v.toNat ≤ s.hdr.nvars.toNat ∧
      ∀ w < v.toNat, s.vals[2 * w]?.getD 0#8 ≠ 0#8)
    (fun (v, ()) => s.hdr.nvars.toNat - v.toNat)
    (fun L hL => by c0_agrees_steps!; exact hL s (0#64, ()) m hm rfl hsafe ⟨by simp, by simp⟩)
    (fun L s' (v, ()) ml hcore hs' ⟨hvle, hall⟩ hml hL => ?_)
  have hvl := hs'.vals_len; have hvs : s'.vals = s.vals := hcore.get KsCore.vals
  have hnv' : s'.hdr.nvars = s.hdr.nvars := hcore.get KsCore.nvars
  rw [hnv'] at hvl; dsimp only [ksSlice, KsMem] at hml; c0_agrees_steps!
  · have hv2 : (v.toNat + v.toNat) % 2 ^ 64 = 2 * v.toNat := by omega
    refine hQ (v, ()) { s' with hdr := { s'.hdr with ticks := s'.hdr.ticks + 1 } } m hcore
      (ksSafe_set_scratch hs' rfl rfl rfl) (Or.inl ⟨by c0_bound, ?_⟩)
      (by dsimp only [ksSlice, KsMem]; c0_frame)
    rw [← hvs, getElem?_getD_of_lt _ (by omega)]
    exact (bv8_zext32_eq0 _).mp (by simpa [hv2] using hc)
  · refine hL { s' with hdr := { s'.hdr with ticks := s'.hdr.ticks + 1 } } (v + 1#64, ()) m
      (by dsimp only [ksSlice, KsMem]; c0_frame) (by bv_omega) rfl
      (ksSafe_set_scratch hs' rfl rfl rfl) ⟨by bv_omega, fun w hw => ?_⟩
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ (by bv_omega : w < v.toNat + 1)) with hlt | rfl
    · exact hall w hlt
    · have hv2 : (v.toNat + v.toNat) % 2 ^ 64 = 2 * v.toNat := by omega
      rw [← hvs, getElem?_getD_of_lt _ (by omega)]
      intro h0; exact hc (by simpa [hv2] using (bv8_zext32_eq0 _).mpr h0)
  · exact hQ (s.hdr.nvars, ()) s' ml hcore hs'
      (Or.inr ⟨rfl, fun w hw => hall w (by bv_omega)⟩) hml

theorem ks_decay_wp (Γ : Env) :
    ∀ a m Q X, ksDecayWindowSpec a m Q X → Func.wp Γ ks_decay_window_body a m Q X := by
  rintro ⟨sp, lim, ⟨⟩⟩ m Q X ⟨s, R, hsafe, hlim, hm, hQ⟩
  c0_agrees_steps!
  refine wp_loop_agreesExcept_mem (ts := [i64]) decayMask s (KsMem sp) R
    (fun s' i => i.1.toNat ≤ lim.toNat ∧ KsSafe s' ∧
      OutsideSliceAgrees 0 lim.toNat s.scores s'.scores)
    (fun i => lim.toNat - i.1.toNat)
    (fun L hL => by c0_agrees_steps!; exact hL s (0#64, ()) m hm rfl ⟨by simp, hsafe, .refl _ _ _⟩)
    (fun L s' (i, ()) ml hag ⟨hile, hs', hout⟩ hml hL => ?_)
  have hsl := hs'.scores_len; have hnv' : s'.hdr.nvars = s.hdr.nvars := hag.get (·.hdr.nvars)
  rw [hnv'] at hsl; unfold KsMem at hml; c0_agrees_steps!
  · exact hL { s' with hdr := { s'.hdr with ticks := s'.hdr.ticks + 1 }, scores := _ }
      (i + 1#64, ()) m (by dsimp only [KsMem]; c0_frame) (by bv_omega) rfl
      ⟨by bv_omega, ksSafe_set_scratch hs' (by simp) rfl rfl,
        hout.update_set _ (by omega) (by c0_bound)⟩
  · exact hQ s' ml hag hs' hout hml

theorem ks_backtrack_wp (Γ : Env) :
    ∀ a m Q X, ksBacktrackSpec a m Q X → Func.wp Γ ks_backtrack_body a m Q X := by
  rintro ⟨sp, tgt, tlvl, ⟨⟩⟩ m Q X ⟨s, R, hsafe, hcore0, hm, hQ⟩
  c0_agrees_steps!
  refine wp_loop_agreesExcept_state_mem (ts := []) btMask s (KsMem sp) R
    (fun s' _ => KsSafe s' ∧ TrailValsInv (ksCoreProj s') ∧
      s'.hdr.trail_end.toNat ≤ s.hdr.trail_end.toNat ∧
      (s'.hdr.trail_end.toNat < s.hdr.trail_end.toNat → tgt.toNat ≤ s'.hdr.trail_end.toNat))
    (fun s' _ => s'.hdr.trail_end.toNat)
    (fun L hL => by
      c0_agrees_steps!; exact hL s () m hm rfl ⟨hsafe, hcore0.tv, Nat.le_refl _, by omega⟩)
    (fun L s' () ml hag ⟨hs', htv', hle, hgt⟩ hml hL => ?_)
  have hnv := hs'.nvars_lt; have hvl := hs'.vals_len
  have htl := hs'.trl_len; have hpl := hs'.phases_len; have hte_le := hs'.trail_le
  unfold KsMem at hml; c0_agrees_steps!
  · refine hL { s' with
        hdr := { s'.hdr with trail_end := s'.hdr.trail_end - 1, ticks := s'.hdr.ticks + 1 },
        vals := _, phases := _ }
      () m (by dsimp only [KsMem]; c0_frame) (by bv_omega) rfl ?_
    exact ⟨ksSafe_bt_step hs' (by bv_omega) (by simp) (by simp),
      trailVals_pop_step hs' htv' (by bv_omega) rfl, by bv_omega, by bv_omega⟩
  · have hpos : 0 < s'.hdr.trail_end.toNat := by bv_omega
    have htr_lt := htv'.trail_lits_lt (s'.hdr.trail_end.toNat - 1)
      (by dsimp only [ksCoreProj]; omega)
    dsimp only [ksCoreProj] at htr_lt; rw [getElem?_getD_of_lt _ (by omega)] at htr_lt
    have hidx : (2 ^ 64 - BitVec.toNat (1 : BitVec 64) + s'.hdr.trail_end.toNat) % 2 ^ 64 =
        s'.hdr.trail_end.toNat - 1 := by simp only [BitVec.reduceToNat]; omega
    simp only [hidx] at hc; omega
  · refine hQ { s' with hdr := { s'.hdr with level := tlvl, propagated := s'.hdr.trail_end } } m
      (hag.update _) ⟨hs'.nvars_lt, hs'.trail_le, hs'.vals_len, hs'.trl_len,
        hs'.scores_len, hs'.phases_len, hs'.wit_len_arr⟩
      ⟨⟨htv'.1, htv'.2, htv'.3, htv'.4, htv'.5, htv'.6⟩, by dsimp [ksCoreProj]; omega⟩
      (by bv_omega) rfl (PrefixAgrees.of_agreesExcept (hag.update _) KsState.trl _)
      (by dsimp only [KsMem]; c0_frame)
  · refine hQ { s' with hdr := { s'.hdr with level := tlvl } } m
      (hag.update _) ⟨hs'.nvars_lt, hs'.trail_le, hs'.vals_len, hs'.trl_len,
        hs'.scores_len, hs'.phases_len, hs'.wit_len_arr⟩
      ⟨⟨htv'.1, htv'.2, htv'.3, htv'.4, htv'.5, htv'.6⟩, by dsimp [ksCoreProj]; bv_omega⟩
      (by bv_omega) rfl (PrefixAgrees.of_agreesExcept (hag.update _) KsState.trl _)
      (by dsimp only [KsMem]; c0_frame)

theorem ks_search_wp (Γ : Env)
    (hWalk : ∀ a m Q X, ksWalksatSpec a m Q X → Γ "ks_walksat_pass" [i64, i64] [i64] a m Q X)
    (hBt : ∀ a m Q X, ksBacktrackSpec a m Q X → Γ "ks_backtrack" [i64, i64, i64] [] a m Q X) :
    ∀ a m Q X, ksSearchStepSpec a m Q X → Func.wp Γ ks_search_step_body a m Q X := by
  rintro ⟨sp, budget, tgt, tlvl, ⟨⟩⟩ m Q X ⟨s, R, hsafe, hcore, hm, hQ⟩
  c0_steps
  refine wp_safety_slice_call hWalk CoreSoundInv hcore rfl hsafe hm
    fun (fl, ()) s1 m1 hpres hs1 hcore1 _ hm1 => ?_
  c0_steps; c0_call hBt
  refine ⟨s1, R, hs1, hcore1, hm1, fun s2 m2 _ hs2 hcore2 hte hlvl _ hm2 => ?_⟩
  c0_steps
  have hte_eq : s1.hdr.trail_end = s.hdr.trail_end := hpres.get KsCore.trail_end
  exact hQ fl s2 m2 hs2 hcore2 (by rw [hte, hte_eq]) hlvl hm2

/-! ## 6. Whole-module `Env.ofTable` soundness & `noExit` -/

def ksTable : List SpecEntry :=
  [⟨"ks_rephase_rescale", [i64], [], ksRephaseSpec, true⟩,
   ⟨"ks_walksat_pass", [i64, i64], [i64], ksWalksatSpec, true⟩,
   ⟨"ks_find_unassigned", [i64], [i64], ksFindUnassignedSpec, true⟩,
   ⟨"ks_decay_window", [i64, i64], [], ksDecayWindowSpec, true⟩,
   ⟨"ks_backtrack", [i64, i64, i64], [], ksBacktrackSpec, true⟩,
   ⟨"ks_search_step", [i64, i64, i64, i64], [i64], ksSearchStepSpec, true⟩]

abbrev ksEnv : Env := Env.ofTable ksTable

theorem ksEnv_rephase :
    ∀ a m Q X, ksRephaseSpec a m Q X → ksEnv "ks_rephase_rescale" [i64] [] a m Q X :=
  fun _ _ _ _ h => Env.ofTable_of_mem (e := ⟨"ks_rephase_rescale", [i64], [], ksRephaseSpec, true⟩)
    (by simp [ksTable]) (by decide) h

theorem ksEnv_walksat :
    ∀ a m Q X, ksWalksatSpec a m Q X → ksEnv "ks_walksat_pass" [i64, i64] [i64] a m Q X :=
  fun _ _ _ _ h =>
    Env.ofTable_of_mem (e := ⟨"ks_walksat_pass", [i64, i64], [i64], ksWalksatSpec, true⟩)
      (by simp [ksTable]) (by decide) h

theorem ksEnv_backtrack :
    ∀ a m Q X, ksBacktrackSpec a m Q X → ksEnv "ks_backtrack" [i64, i64, i64] [] a m Q X :=
  fun _ _ _ _ h =>
    Env.ofTable_of_mem (e := ⟨"ks_backtrack", [i64, i64, i64], [], ksBacktrackSpec, true⟩)
      (by simp [ksTable]) (by decide) h

theorem ks_module_checkAcyclic : ks_module.checkAcyclic = true := by t_kernel_rfl

theorem ks_rephase_wf : Func.Wf ks_rephase_rescale_body := by t_wf_reify
theorem ks_walksat_wf : Func.Wf ks_walksat_pass_body := by t_wf_reify
theorem ks_find_wf : Func.Wf ks_find_unassigned_body := by t_wf_reify
theorem ks_decay_wf : Func.Wf ks_decay_window_body := by t_wf_reify
theorem ks_bt_wf : Func.Wf ks_backtrack_body := by t_wf_reify
theorem ks_search_wf : Func.Wf ks_search_step_body := by t_wf_reify

theorem ksEnv_moduleOk : ModuleOk ksEnv ks_module :=
  Env.ofTable_moduleOk ks_module_checkAcyclic
    ⟨ks_rephase_wf, ks_walksat_wf, ks_find_wf, ks_decay_wf, ks_bt_wf, ks_search_wf, trivial⟩
    ⟨.of (ks_rephase_wp _), .of (ks_walksat_wp _ ksEnv_rephase),
     .of (ks_find_wp _), .of (ks_decay_wp _), .of (ks_backtrack_wp _),
     .of (ks_search_wp _ ksEnv_walksat ksEnv_backtrack), trivial⟩

theorem ksEnv_noExit :
    ∀ f as bs xs m Q X X', ksEnv f as bs xs m Q X → ksEnv f as bs xs m Q X' :=
  Env.ofTable_noExit (by simp [ksTable])

/-! ## 7. Algebraic laws & scoped `grind` unit tests -/

theorem algebra_mono_trans (s₀ s₁ s₂ : KsState)
    (h1 : AgreesExcept decayMask s₀ s₁) (h2 : AgreesExcept scratchMask s₁ s₂) :
    AgreesExcept scratchMask s₀ s₂ ∧
    PreservesCoreSlice ksCoreProj s₀ s₂ ∧
    s₂.hdr.nclauses = s₀.hdr.nclauses ∧
    ((s₂.vals.drop 2).take 4) = ((s₀.vals.drop 2).take 4) := by
  have hm : AgreesExcept scratchMask s₀ s₂ := h1.trans_mono h2
  exact ⟨hm, PreservesCoreSlice.of_agreesExcept hm, hm.get (·.hdr.nclauses),
    hm.arr_slice KsState.vals 2 4⟩

theorem algebra_grind_smoke (s₀ s₁ s₂ : KsState) (xs ys zs : List (BitVec 32))
    (h1 : AgreesExcept scratchMask s₀ s₁) (h2 : AgreesExcept scratchMask s₁ s₂)
    (hp : PrefixAgrees 5 xs ys) (hs : SliceAgrees 2 6 ys zs)
    (ho : OutsideSliceAgrees 3 5 xs zs) :
    AgreesExcept scratchMask s₀ s₂ ∧ zs[2]? = xs[2]? ∧ zs[0]? = xs[0]? := by
  grind

theorem slice_func_transport (Γ : Env) (sp : BitVec 64) (s : KsState)
    (R : Mem 64 → Prop) (m : Mem 64) (Q : Post []) (X : XPost)
    (hSafe : KsSafe s) (hInv : CoreSoundInv (ksCoreProj s)) (hm : (KsMem sp s ⋆ R) m)
    (hQ : ∀ s' m', KsSafe s' → CoreSoundInv (ksCoreProj s') → (KsMem sp s' ⋆ R) m' → Q () m') :
    Func.wp Γ ks_rephase_rescale_body (sp, ()) m Q X :=
  wp_safety_slice_func (ks_rephase_wp Γ) CoreSoundInv hInv rfl hSafe hm
    fun () s' m' _ hs' hinv' _ hm' => hQ s' m' hs' hinv' hm'

theorem loop_agrees_direct (Γ : Env) :
    ∀ a m Q X, ksDecayWindowSpec a m Q X → Func.wp Γ ks_decay_window_body a m Q X := by
  rintro ⟨sp, lim, ⟨⟩⟩ m Q X ⟨s, R, hsafe, hlim, hm, hQ⟩
  c0_agrees_steps!
  refine wp_loop_agreesExcept (ts := [i64]) decayMask s
    (fun s' i ml => i.1.toNat ≤ lim.toNat ∧ KsSafe s' ∧
      OutsideSliceAgrees 0 lim.toNat s.scores s'.scores ∧ (KsMem sp s' ⋆ R) ml)
    (fun i _ => lim.toNat - i.1.toNat)
    (fun L hL => by
      c0_agrees_steps!; exact hL s (0#64, ()) m rfl ⟨by simp, hsafe, .refl _ _ _, hm⟩)
    (fun L s' (i, ()) ml hag ⟨hile, hs', hout, hml⟩ hL => ?_)
  have hsl := hs'.scores_len; have hnv' : s'.hdr.nvars = s.hdr.nvars := hag.get (·.hdr.nvars)
  rw [hnv'] at hsl; unfold KsMem at hml; c0_agrees_steps!
  · refine hL { s' with hdr := { s'.hdr with ticks := s'.hdr.ticks + 1 }, scores := _ }
      (i + 1#64, ()) m (by bv_omega) rfl ⟨by bv_omega, ?_, ?_, by dsimp only [KsMem]; c0_frame⟩
    · exact ksSafe_set_scratch hs' (by simp) rfl rfl
    · exact hout.update_set _ (by omega) (by c0_bound)
  · exact hQ s' ml hag hs' hout hml

theorem slice_direct_wp (Γ : Env) (sp : BitVec 64) (s : KsState)
    (R : Mem 64 → Prop) (m : Mem 64) (Q : Post []) (X : XPost)
    (hSafe : KsSafe s) (hInv : CoreSoundInv (ksCoreProj s)) (hm : (KsMem sp s ⋆ R) m)
    (hQ : ∀ s' m', KsSafe s' → CoreSoundInv (ksCoreProj s') → (KsMem sp s' ⋆ R) m' → Q () m') :
    Func.wp Γ ks_rephase_rescale_body (sp, ()) m Q X :=
  wp_safety_slice_full (ksSlice sp)
    (dependsOnCoreAndSafe_proj_and_safe ksCoreProj KsSafe CoreSoundInv) ⟨hInv, hSafe⟩
    (fun _ _ => True)
    (ks_rephase_wp Γ (sp, ()) m _ X ⟨sp, s, R, rfl, hSafe, hm,
      fun () s' _ hcore hs' _ hm' => ⟨s', hcore, hs', trivial, hm'⟩⟩)
    fun () s' m' _ hs' ⟨hinv', _⟩ _ hm' => hQ s' m' hs' hinv' hm'

theorem slice_expr_wp (Γ : Env) (sp : BitVec 64) (s : KsState)
    (R : Mem 64 → Prop) (m : Mem 64) (Q : Post []) (X : XPost)
    (hSafe : KsSafe s) (hInv : CoreSoundInv (ksCoreProj s)) (hm : (KsMem sp s ⋆ R) m)
    (hQ : ∀ s' m', KsSafe s' → CoreSoundInv (ksCoreProj s') → (KsMem sp s' ⋆ R) m' → Q () m') :
    Func.wp Γ ks_rephase_rescale_body (sp, ()) m Q X :=
  wp_safety_slice (ksSlice sp) CoreSoundInv hInv (fun _ _ => True)
    (ks_rephase_wp Γ (sp, ()) m _ X ⟨sp, s, R, rfl, hSafe, hm,
      fun () s' _ hcore hs' _ hm' => ⟨s', hcore, hs', trivial, hm'⟩⟩)
    fun () s' m' _ hs' hinv' _ hm' => hQ s' m' hs' hinv' hm'

#print axioms ks_rephase_wp
#print axioms ks_walksat_wp
#print axioms ks_find_wp
#print axioms ks_decay_wp
#print axioms ks_backtrack_wp
#print axioms ks_search_wp
#print axioms ksEnv_moduleOk
#print axioms ksEnv_noExit
#print axioms algebra_mono_trans
#print axioms algebra_grind_smoke
#print axioms slice_func_transport
#print axioms loop_agrees_direct
#print axioms slice_direct_wp
#print axioms slice_expr_wp

end LeanQbeTest.T.C0AgreesTest
