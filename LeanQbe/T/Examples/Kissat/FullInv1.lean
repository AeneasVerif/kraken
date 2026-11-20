module

public import LeanQbe.T.Examples.Kissat.FullArena1

/-!
# Kissat `D-Full` UNSAT-Only Core Invariant & `ChronoTrailInv` Bridge (`Stage 4`, Part 1)

Builds on `FullArena1` and `LayerAFull` (`ExtUnsatSound`, `ChronoTrailInv`) to define:
1. `PH_SHRK`-aware `COMPACT` `ward` 32-bit word-arena projections (`fullArenaHdr`,
   `fullArenaClauseSize`, `fullArenaClauseGarb`, `fullArenaClauseShrk`, `fullArenaClauseLits`,
   `fullArenaNextOff`, `fullArenaClauseRefs`, `FullArenaClausesInv`).
2. Mode-indexed watch invariant (`ModeWatchesInv`) covering both `dense_mode = 0` (`WatchesInv`
   two-watched-literal stack) and `dense_mode ≠ 0` (`DenseWatchesInv` binary watches + `(sz, cref)`
   occurrence entries).
3. Stage-4 UNSAT-only core soundness invariant `FullCoreInv` (existential formula witness `F_cur`
   with `ExtUnsatSound F0 cur_vars F_cur`), `FullMarksClear`, `FullInv`, and its constructive
   projection `toChronoState` proving `ChronoTrailInv` and UNSAT conflict refutation.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.Full

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open Kraken.Bedrock2.Test

theorem fullInv_var_xor1 (l : Nat) : (l ^^^ 1) / 2 = l / 2 := litVar_litNeg l

theorem fullInv_max_vars_lt32 (c : FullCfg) : c.max_vars < 2 ^ 32 := by
  have hm := c.hmaxv; unfold dimacsBound at hm; omega

private theorem bit23_or_garb (x : BitVec 32) :
    ((x ||| 0x00080000#32) &&& 0x00800000#32) = (x &&& 0x00800000#32) := by
  ext i hi
  have hsub : ((0x00080000#32)[i] && (0x00800000#32)[i]) = false := by
    rw [← BitVec.getElem_and]
    change (0#32 : BitVec 32)[i] = false
    exact BitVec.getElem_zero hi
  simp only [BitVec.getElem_and, BitVec.getElem_or]
  rw [Bool.and_or_distrib_right, hsub, Bool.or_false]

private theorem bit19_or_garb_ne0 (x : BitVec 32) :
    ((x ||| 0x00080000#32) &&& 0x00080000#32) ≠ 0#32 := by
  intro h; have h19 := congrArg (·[19]) h
  revert h19; simp [show (0x00080000#32)[19] = true from rfl]

/-! ## 1. `PH_SHRK`-aware `COMPACT` `ward` arena scanner and `FullArenaClausesInv` -/

def fullArenaHdrCore (k : FullCoreState) (cref : Nat) : BitVec 32 := k.arena[cref]?.getD 0#32

def fullArenaClauseSizeCore (k : FullCoreState) (cref : Nat) : Nat :=
  (k.arena[cref + 2]?.getD 0#32).toNat

def fullArenaClauseGarbCore (k : FullCoreState) (cref : Nat) : Bool :=
  (fullArenaHdrCore k cref &&& 0x00080000#32) != 0#32

def fullArenaClauseShrkCore (k : FullCoreState) (cref : Nat) : Bool :=
  (fullArenaHdrCore k cref &&& 0x00800000#32) != 0#32

def fullArenaClauseLitsCore (k : FullCoreState) (cref : Nat) : List Nat :=
  ((k.arena.drop (cref + 3)).take (fullArenaClauseSizeCore k cref)).map BitVec.toNat

@[inline] abbrev fullArenaHdr (s : FullState) (cref : Nat) : BitVec 32 :=
  fullArenaHdrCore s.core cref

@[inline] abbrev fullArenaClauseSize (s : FullState) (cref : Nat) : Nat :=
  fullArenaClauseSizeCore s.core cref

@[inline] abbrev fullArenaClauseGarb (s : FullState) (cref : Nat) : Bool :=
  fullArenaClauseGarbCore s.core cref

@[inline] abbrev fullArenaClauseShrk (s : FullState) (cref : Nat) : Bool :=
  fullArenaClauseShrkCore s.core cref

@[inline] abbrev fullArenaClauseLits (s : FullState) (cref : Nat) : List Nat :=
  fullArenaClauseLitsCore s.core cref

theorem mem_fullArenaClauseLitsCore_iff {k : FullCoreState} {cref l : Nat}
    (h : cref + 3 + fullArenaClauseSizeCore k cref ≤ k.arena.length) :
    l ∈ fullArenaClauseLitsCore k cref ↔
      ∃ (j : Nat) (_hj : j < fullArenaClauseSizeCore k cref),
        (k.arena[cref + 3 + j]'(by omega)).toNat = l := by
  unfold fullArenaClauseLitsCore; rw [List.mem_map]; constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨j, hj, hget⟩ := List.mem_iff_getElem.mp hx
    have hj' : j < fullArenaClauseSizeCore k cref := by
      rw [List.length_take, List.length_drop] at hj; omega
    refine ⟨j, hj', ?_⟩; rw [List.getElem_take, List.getElem_drop] at hget
    exact congrArg BitVec.toNat hget
  · rintro ⟨j, hj, hget⟩
    refine ⟨k.arena[cref + 3 + j]'(by omega), ?_, hget⟩
    have hlt : j < ((k.arena.drop (cref + 3)).take (fullArenaClauseSizeCore k cref)).length := by
      rw [List.length_take, List.length_drop]; omega
    simpa [List.getElem_take, List.getElem_drop] using List.getElem_mem hlt

theorem fullArenaClauseLitsCore_eq_of_hold {k k' : FullCoreState} {r : Nat}
    (h1 : r + 3 + fullArenaClauseSizeCore k r ≤ k.arena.length)
    (h2 : r + 3 + fullArenaClauseSizeCore k r ≤ k'.arena.length)
    (hsz : fullArenaClauseSizeCore k' r = fullArenaClauseSizeCore k r)
    (hhold : ∀ j < fullArenaClauseSizeCore k r, k'.arena[r + 3 + j]? = k.arena[r + 3 + j]?) :
    fullArenaClauseLitsCore k' r = fullArenaClauseLitsCore k r := by
  unfold fullArenaClauseLitsCore; rw [hsz]
  apply List.ext_getElem
  · simp only [List.length_map, List.length_take, List.length_drop]
    rw [Nat.min_eq_left (by omega), Nat.min_eq_left (by omega)]
  · intro j hj1 _
    simp only [List.getElem_map, List.getElem_take, List.getElem_drop]
    have hj : j < fullArenaClauseSizeCore k r := by
      simp only [List.length_map, List.length_take, List.length_drop] at hj1; omega
    have heq := hhold j hj
    rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at heq
    exact congrArg BitVec.toNat (Option.some.inj heq)

theorem fullArenaClauseLitsCore_set_outside {k : FullCoreState} {cref r : Nat}
    {v : BitVec 32} (hbd : r + 3 + fullArenaClauseSizeCore k r ≤ k.arena.length)
    (hdisj : r + 3 + fullArenaClauseSizeCore k r ≤ cref ∨ cref + 3 ≤ r) :
    let k' := { k with arena := k.arena.set cref v }
    fullArenaClauseSizeCore k' r = fullArenaClauseSizeCore k r ∧
    fullArenaClauseLitsCore k' r = fullArenaClauseLitsCore k r := by
  intro k'
  have hsz : fullArenaClauseSizeCore k' r = fullArenaClauseSizeCore k r := by
    unfold fullArenaClauseSizeCore; dsimp only [k']
    rcases hdisj with h1 | h2 <;> rw [List.getElem?_set_ne (by omega)]
  refine ⟨hsz, fullArenaClauseLitsCore_eq_of_hold hbd (by simp [k', hbd]) hsz fun j hj => ?_⟩
  dsimp only [k']; rcases hdisj with h1 | h2 <;> exact List.getElem?_set_ne (by omega)

/-- Skip shrunk padding words up to and including `0xFFFFFFFFu` (`full_arena_next` loop). -/
def fullArenaSkipShrk (ar : List (BitVec 32)) (alen p : Nat) : Nat → Nat
  | 0 => min p alen
  | fuel + 1 =>
    if p < alen then
      if ar[p]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 then fullArenaSkipShrk ar alen (p + 1) fuel
      else p + 1
    else alen

theorem fullArenaSkipShrk_bounds {ar : List (BitVec 32)} {alen : Nat} :
    ∀ {fuel p : Nat}, p ≤ alen →
      p ≤ fullArenaSkipShrk ar alen p fuel ∧ fullArenaSkipShrk ar alen p fuel ≤ alen
  | 0, p, _ => by simp [fullArenaSkipShrk]; omega
  | fuel + 1, p, hle => by
    unfold fullArenaSkipShrk; split
    · split
      · have ih := fullArenaSkipShrk_bounds (ar := ar) (alen := alen) (fuel := fuel)
          (p := p + 1) (by omega)
        omega
      · omega
    · omega

theorem fullArenaSkipShrk_congr {ar1 ar2 : List (BitVec 32)} {alen : Nat} :
    ∀ {fuel p : Nat},
      (∀ k, p ≤ k → k < fullArenaSkipShrk ar1 alen p fuel → ar2[k]? = ar1[k]?) →
      fullArenaSkipShrk ar2 alen p fuel = fullArenaSkipShrk ar1 alen p fuel
  | 0, _, _ => rfl
  | fuel + 1, p, heq => by
    unfold fullArenaSkipShrk; split
    · rename_i hlt
      have hb := fullArenaSkipShrk_bounds (ar := ar1) (alen := alen) (fuel := fuel)
        (p := p + 1) (by omega)
      have h0 : p < fullArenaSkipShrk ar1 alen p (fuel + 1) := by
        unfold fullArenaSkipShrk; simp only [hlt, ↓reduceIte]; split <;> omega
      have hpk : ar2[p]? = ar1[p]? := heq p (Nat.le_refl p) h0
      simp only [hpk]; split
      · rename_i hne
        refine fullArenaSkipShrk_congr (fuel := fuel) (p := p + 1) fun k hk1 hk2 =>
          heq k (by omega) (by
            unfold fullArenaSkipShrk
            simp only [hlt, hne, ↓reduceIte, ne_eq, not_false_eq_true]; exact hk2)
      · rfl
    · rfl

theorem fullArenaSkipShrk_hits_sentinel {ar : List (BitVec 32)} {alen t : Nat} :
    ∀ {fuel p : Nat}, p ≤ t → t < alen → ar[t]? = some 0xFFFFFFFF#32 → t - p + 1 ≤ fuel →
      let nxt := fullArenaSkipShrk ar alen p fuel
      ∃ t0, p ≤ t0 ∧ t0 ≤ t ∧ nxt = t0 + 1 ∧ ar[t0]? = some 0xFFFFFFFF#32
  | 0, _, _, _, _, hf => by omega
  | fuel + 1, p, hpt, hta, hsent, hf => by
    have hpa : p < alen := by omega
    unfold fullArenaSkipShrk; simp only [hpa, ↓reduceIte]; split
    · rename_i hne
      have hp_ne : p ≠ t := by rintro rfl; simp [hsent] at hne
      obtain ⟨t0, h1, h2, h3, h4⟩ := fullArenaSkipShrk_hits_sentinel (ar := ar) (alen := alen)
        (t := t) (fuel := fuel) (p := p + 1) (by omega) hta hsent (by omega)
      exact ⟨t0, by omega, h2, h3, h4⟩
    · rename_i heq
      have heqv : ar[p]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 :=
        Classical.byContradiction fun hn => heq hn
      have hlen_t : t < ar.length := (List.getElem?_eq_some_iff.mp hsent).1
      have hp_some : ar[p]? = some (ar[p]'(by omega)) := List.getElem?_eq_getElem (by omega)
      rw [hp_some, Option.getD_some] at heqv
      exact ⟨p, Nat.le_refl p, hpt, rfl, by rw [hp_some, heqv]⟩

theorem fullArenaSkipShrk_eq_of_sentinel {ar1 ar2 : List (BitVec 32)} {al1 al2 t : Nat}
    (ht : t < al1) (hal : al1 ≤ al2) (hsent : ar1[t]? = some 0xFFFFFFFF#32)
    (hhold : ∀ i < al1, ar2[i]? = ar1[i]?) :
    ∀ {fuel1 fuel2 p : Nat}, p ≤ t → t - p + 1 ≤ fuel1 → t - p + 1 ≤ fuel2 →
      fullArenaSkipShrk ar2 al2 p fuel2 = fullArenaSkipShrk ar1 al1 p fuel1
  | 0, _, _, _, h1, _ => by omega
  | _, 0, _, _, _, h2 => by omega
  | f1 + 1, f2 + 1, p, hpt, h1, h2 => by
    have hpa1 : p < al1 := by omega
    have hpa2 : p < al2 := by omega
    have hpeq : ar2[p]? = ar1[p]? := hhold p hpa1
    unfold fullArenaSkipShrk; simp only [hpa1, hpa2, ↓reduceIte, hpeq]; split
    · rename_i hne
      have hp_ne : p ≠ t := by rintro rfl; simp [hsent] at hne
      exact fullArenaSkipShrk_eq_of_sentinel ht hal hsent hhold (by omega) (by omega) (by omega)
    · rfl

/-- Word offset of the block immediately following `cref` (matches `full_arena_next`). -/
def fullArenaNextOff (ar : List (BitVec 32)) (alen cref : Nat) : Nat :=
  if cref + 3 > alen then alen
  else
    let hdr := ar[cref]?.getD 0#32
    let sz := (ar[cref + 2]?.getD 0#32).toNat
    let p := cref + 3 + sz
    if p > alen then alen
    else if (hdr &&& 0x00800000#32) ≠ 0#32 then fullArenaSkipShrk ar alen p (alen - p)
    else p

theorem fullArenaNextOff_bounds {ar : List (BitVec 32)} {alen cref : Nat}
    (hle : cref + 3 ≤ alen) :
    cref < fullArenaNextOff ar alen cref ∧ fullArenaNextOff ar alen cref ≤ alen := by
  unfold fullArenaNextOff
  have hnot : ¬ (cref + 3 > alen) := by omega
  simp only [hnot, ↓reduceIte]; split
  · exact ⟨by omega, by omega⟩
  · split
    · rename_i hle_p _
      have hb := fullArenaSkipShrk_bounds (ar := ar) (alen := alen)
        (p := cref + 3 + (ar[cref + 2]?.getD 0#32).toNat)
        (fuel := alen - (cref + 3 + (ar[cref + 2]?.getD 0#32).toNat)) (by omega)
      omega
    · exact ⟨by omega, by omega⟩

theorem fullArenaNextOff_congr_block {ar1 ar2 : List (BitVec 32)} {alen r : Nat}
    (h0 : ar2[r]? = ar1[r]?) (h2 : ar2[r + 2]? = ar1[r + 2]?)
    (hpad : ∀ k, r + 3 + (ar1[r + 2]?.getD 0#32).toNat ≤ k →
      k < fullArenaNextOff ar1 alen r → ar2[k]? = ar1[k]?) :
    fullArenaNextOff ar2 alen r = fullArenaNextOff ar1 alen r := by
  unfold fullArenaNextOff; split
  · rfl
  · rename_i hnot; simp only [h0, h2]; split
    · rfl
    · split
      · rename_i hle_p hshrk
        refine fullArenaSkipShrk_congr fun k hk1 hk2 => hpad k hk1 ?_
        unfold fullArenaNextOff
        simp only [hnot, ↓reduceIte, hle_p, hshrk, ne_eq, not_false_eq_true]; exact hk2
      · rfl

theorem fullArenaNextOff_hits_sentinel {ar : List (BitVec 32)} {alen r t : Nat}
    (hr3 : r + 3 ≤ alen) (hshrk : (ar[r]?.getD 0#32 &&& 0x00800000#32) ≠ 0#32)
    (ht1 : r + 3 + (ar[r + 2]?.getD 0#32).toNat ≤ t) (ht2 : t < alen)
    (hsent : ar[t]? = some 0xFFFFFFFF#32) :
    let nxt := fullArenaNextOff ar alen r
    ∃ t0, r + 3 + (ar[r + 2]?.getD 0#32).toNat ≤ t0 ∧ t0 ≤ t ∧ nxt = t0 + 1 ∧
      ar[t0]? = some 0xFFFFFFFF#32 := by
  have hnot1 : ¬ (r + 3 > alen) := by omega
  have hnot2 : ¬ (r + 3 + (ar[r + 2]?.getD 0#32).toNat > alen) := by omega
  unfold fullArenaNextOff
  simp only [hnot1, hnot2, hshrk, ↓reduceIte, ne_eq, not_false_eq_true]
  exact fullArenaSkipShrk_hits_sentinel ht1 ht2 hsent (by omega)

def fullArenaScanRefs (ar : List (BitVec 32)) (alen pos : Nat) : Nat → List Nat
  | 0 => []
  | fuel + 1 =>
    if pos + 3 ≤ alen then pos :: fullArenaScanRefs ar alen (fullArenaNextOff ar alen pos) fuel
    else []

def fullArenaClauseRefsCore (k : FullCoreState) : List Nat :=
  fullArenaScanRefs k.arena k.arena_len 0 k.arena_len

@[inline] abbrev fullArenaClauseRefs (s : FullState) : List Nat := fullArenaClauseRefsCore s.core

theorem fullArenaScanRefs_fuel_ge {ar : List (BitVec 32)} {alen : Nat} :
    ∀ {f1 f2 pos : Nat}, alen - pos ≤ f1 → alen - pos ≤ f2 →
      fullArenaScanRefs ar alen pos f1 = fullArenaScanRefs ar alen pos f2
  | 0, f2, pos, h1, _ => by
    have hp : ¬ (pos + 3 ≤ alen) := by omega
    cases f2 <;> simp [fullArenaScanRefs, hp]
  | f1 + 1, 0, pos, _, h2 => by
    have hp : ¬ (pos + 3 ≤ alen) := by omega
    simp [fullArenaScanRefs, hp]
  | f1 + 1, f2 + 1, pos, h1, h2 => by
    unfold fullArenaScanRefs; split
    · rename_i hle
      have hnb := fullArenaNextOff_bounds (ar := ar) (alen := alen) (cref := pos) hle
      rw [fullArenaScanRefs_fuel_ge (ar := ar) (alen := alen) (f1 := f1) (f2 := f2)
        (pos := fullArenaNextOff ar alen pos) (by omega) (by omega)]
    · rfl

theorem fullArenaScanRefs_mem_bounds {ar : List (BitVec 32)} {alen : Nat} :
    ∀ {fuel pos r : Nat}, r ∈ fullArenaScanRefs ar alen pos fuel → pos ≤ r ∧ r + 3 ≤ alen
  | 0, _, _, h => by simp [fullArenaScanRefs] at h
  | fuel + 1, pos, r, h => by
    unfold fullArenaScanRefs at h; split at h
    · rename_i hle; simp only [List.mem_cons] at h
      rcases h with rfl | hrest
      · exact ⟨Nat.le_refl _, hle⟩
      · have hb := fullArenaNextOff_bounds (ar := ar) (alen := alen) (cref := pos) hle
        have ih := fullArenaScanRefs_mem_bounds hrest; omega
    · simp at h

theorem fullArenaScanRefs_disjoint {ar : List (BitVec 32)} {alen : Nat} :
    ∀ {fuel pos r1 r2 : Nat},
      r1 ∈ fullArenaScanRefs ar alen pos fuel → r2 ∈ fullArenaScanRefs ar alen pos fuel →
      r1 < r2 → fullArenaNextOff ar alen r1 ≤ r2
  | 0, _, _, _, h1, _, _ => by simp [fullArenaScanRefs] at h1
  | fuel + 1, pos, r1, r2, h1, h2, hlt => by
    unfold fullArenaScanRefs at h1 h2; split at h1
    · rename_i hle; simp only [hle, ↓reduceIte, List.mem_cons] at h1 h2
      have hb := fullArenaNextOff_bounds (ar := ar) (alen := alen) (cref := pos) hle
      rcases h1 with rfl | h1' <;> rcases h2 with rfl | h2'
      · omega
      · exact (fullArenaScanRefs_mem_bounds h2').1
      · have hb1 := fullArenaScanRefs_mem_bounds h1'; omega
      · exact fullArenaScanRefs_disjoint h1' h2' hlt
    · simp at h1

theorem fullArenaScanRefs_congr {ar1 ar2 : List (BitVec 32)} {alen : Nat} :
    ∀ {fuel pos : Nat},
      (∀ r ∈ fullArenaScanRefs ar1 alen pos fuel,
        fullArenaNextOff ar2 alen r = fullArenaNextOff ar1 alen r) →
      fullArenaScanRefs ar2 alen pos fuel = fullArenaScanRefs ar1 alen pos fuel
  | 0, _, _ => rfl
  | fuel + 1, pos, h => by
    unfold fullArenaScanRefs; split
    · rename_i hle
      have heq := h pos (by simp [fullArenaScanRefs, hle])
      rw [heq]
      rw [fullArenaScanRefs_congr (ar1 := ar1) (ar2 := ar2) (alen := alen) (fuel := fuel)
        (pos := fullArenaNextOff ar1 alen pos)
        fun r hr => h r (by simp [fullArenaScanRefs, hle, hr])]
    · rfl

theorem fullArenaClauseRefsCore_congr {k1 k2 : FullCoreState} (hlen : k2.arena_len = k1.arena_len)
    (heq : ∀ r ∈ fullArenaClauseRefsCore k1,
      fullArenaNextOff k2.arena k1.arena_len r = fullArenaNextOff k1.arena k1.arena_len r) :
    fullArenaClauseRefsCore k2 = fullArenaClauseRefsCore k1 := by
  unfold fullArenaClauseRefsCore; rw [hlen]; exact fullArenaScanRefs_congr heq

theorem fullArenaScanRefs_last {ar : List (BitVec 32)} {alen : Nat} :
    ∀ {fuel pos : Nat}, alen - pos ≤ fuel → pos + 3 ≤ alen →
      (∀ r ∈ fullArenaScanRefs ar alen pos fuel,
        fullArenaNextOff ar alen r = alen ∨ fullArenaNextOff ar alen r + 3 ≤ alen) →
      ∃ r ∈ fullArenaScanRefs ar alen pos fuel, fullArenaNextOff ar alen r = alen
  | 0, _, _, _, _ => by omega
  | fuel + 1, pos, hfl, hle, hchain => by
    unfold fullArenaScanRefs at hchain ⊢; simp only [hle, ↓reduceIte] at hchain ⊢
    rcases hchain pos List.mem_cons_self with hlast | hmore
    · exact ⟨pos, List.mem_cons_self, hlast⟩
    · have hb := fullArenaNextOff_bounds (ar := ar) (alen := alen) (cref := pos) hle
      obtain ⟨r, hr, hre⟩ := fullArenaScanRefs_last (fuel := fuel)
        (pos := fullArenaNextOff ar alen pos) (by omega) hmore
        fun r' hr' => hchain r' (List.mem_cons_of_mem _ hr')
      exact ⟨r, List.mem_cons_of_mem _ hr, hre⟩

private theorem fullArenaScanRefs_append_one {ar : List (BitVec 32)} {alen sz : Nat}
    (hsz : 3 ≤ sz) (hhdr : (ar[alen]?.getD 0#32 &&& 0x00800000#32) = 0#32)
    (hsz_eq : (ar[alen + 2]?.getD 0#32).toNat = sz) :
    ∀ fuel, 2 ≤ fuel → fullArenaScanRefs ar (alen + 3 + sz) alen fuel = [alen]
  | fuel + 1, hf => by
    have hp : alen + 3 ≤ alen + 3 + sz := by omega
    have hnxt : fullArenaNextOff ar (alen + 3 + sz) alen = alen + 3 + sz := by
      unfold fullArenaNextOff; simp [hsz_eq, hhdr]
    cases fuel with
    | zero => omega
    | succ f' =>
      have hp2 : ¬ (alen + 3 + sz + 3 ≤ alen + 3 + sz) := by omega
      simp [fullArenaScanRefs, hp, hnxt, hp2]

theorem fullArenaScanRefs_eq_of_prefix {ar1 ar2 : List (BitVec 32)} {alen sz : Nat}
    (hsz : 3 ≤ sz) (hhdr2 : (ar2[alen]?.getD 0#32 &&& 0x00800000#32) = 0#32)
    (hsz2 : (ar2[alen + 2]?.getD 0#32).toNat = sz)
    (hchain : ∀ pos, pos ∈ fullArenaScanRefs ar1 alen 0 alen →
      fullArenaNextOff ar1 alen pos = alen ∨ fullArenaNextOff ar1 alen pos + 3 ≤ alen)
    (hlast : alen = 0 ∨
      ∃ r ∈ fullArenaScanRefs ar1 alen 0 alen, fullArenaNextOff ar1 alen r = alen)
    (hhold : ∀ r ∈ fullArenaScanRefs ar1 alen 0 alen,
      fullArenaNextOff ar2 (alen + 3 + sz) r = fullArenaNextOff ar1 alen r) :
    fullArenaScanRefs ar2 (alen + 3 + sz) 0 (alen + 3 + sz) =
      fullArenaScanRefs ar1 alen 0 alen ++ [alen] := by
  have go : ∀ (fuel pos : Nat), alen - pos ≤ fuel →
      (pos = alen ∨ (pos + 3 ≤ alen ∧
        (∀ r ∈ fullArenaScanRefs ar1 alen pos fuel,
          fullArenaNextOff ar1 alen r = alen ∨ fullArenaNextOff ar1 alen r + 3 ≤ alen))) →
      (∀ r ∈ fullArenaScanRefs ar1 alen pos fuel,
        fullArenaNextOff ar2 (alen + 3 + sz) r = fullArenaNextOff ar1 alen r) →
      fullArenaScanRefs ar2 (alen + 3 + sz) pos (fuel + 3 + sz) =
        fullArenaScanRefs ar1 alen pos fuel ++ [alen] := by
    intro fuel; induction fuel with
    | zero =>
      intro pos _ hpos _
      rcases hpos with rfl | ⟨hle, _⟩
      · simp [fullArenaScanRefs]
        exact fullArenaScanRefs_append_one hsz hhdr2 hsz2 (3 + sz) (by omega)
      · omega
    | succ f ih =>
      intro pos hfl hpos hsub
      rcases hpos with rfl | ⟨hle, hstep_ok⟩
      · have h1 : ¬ (pos + 3 ≤ pos) := by omega
        rw [fullArenaScanRefs]; simp only [h1, ↓reduceIte, List.nil_append]
        exact fullArenaScanRefs_append_one hsz hhdr2 hsz2 (f + 1 + 3 + sz) (by omega)
      · have hp2 : pos + 3 ≤ alen + 3 + sz := by omega
        have hnxt := hsub pos (by simp [fullArenaScanRefs, hle])
        have hb := fullArenaNextOff_bounds (ar := ar1) (alen := alen) (cref := pos) hle
        have hstep : f + 1 + 3 + sz = (f + 3 + sz) + 1 := by omega
        rw [hstep]; unfold fullArenaScanRefs
        simp only [hle, hp2, ↓reduceIte, hnxt, List.cons_append]; congr 1
        have hok := hstep_ok pos (by simp [fullArenaScanRefs, hle])
        refine ih (fullArenaNextOff ar1 alen pos) (by omega) ?_ ?_
        · rcases hok with hn | hn3
          · exact Or.inl hn
          · exact Or.inr ⟨hn3, fun r hr => hstep_ok r (by simp [fullArenaScanRefs, hle, hr])⟩
        · intro r hr; exact hsub r (by simp [fullArenaScanRefs, hle, hr])
  rcases hlast with rfl | ⟨r, hr, _⟩
  · exact go 0 0 (by omega) (Or.inl rfl) (fun _ h => by simp [fullArenaScanRefs] at h)
  · have ha3 : 3 ≤ alen := by have := fullArenaScanRefs_mem_bounds hr; omega
    simpa [Nat.add_assoc] using go alen 0 (by omega) (Or.inr ⟨ha3, hchain⟩) hhold

/-- `PH_SHRK`-aware arena clause-database invariant: contiguous blocks in `0 ..< k.arena_len`,
with explicit `0xFFFFFFFF#32` terminator witness whenever `PH_SHRK` (`0x00800000#32`) is set;
every live clause has size `≥ 3`, literals `< 2 * k.cur_vars`, and is entailed by `F_cur`. -/
structure FullArenaClausesInv (_c : FullCfg) (F_cur : List (List Nat))
    (k : FullCoreState) : Prop where
  len_ok : k.arena_len = 0 ∨ 3 ≤ k.arena_len
  refs_wf : ∀ r ∈ fullArenaClauseRefsCore k,
    r + 3 ≤ k.arena_len ∧ 3 ≤ fullArenaClauseSizeCore k r ∧
    r + 3 + fullArenaClauseSizeCore k r ≤ fullArenaNextOff k.arena k.arena_len r ∧
    fullArenaNextOff k.arena k.arena_len r ≤ k.arena_len ∧
    (fullArenaNextOff k.arena k.arena_len r = k.arena_len ∨
     fullArenaNextOff k.arena k.arena_len r + 3 ≤ k.arena_len)
  shrk_term : ∀ r ∈ fullArenaClauseRefsCore k,
    (fullArenaHdrCore k r &&& 0x00800000#32) ≠ 0#32 →
    ∃ t, r + 3 + fullArenaClauseSizeCore k r ≤ t ∧ t < k.arena_len ∧
      k.arena[t]? = some 0xFFFFFFFF#32
  lits_lt : ∀ r ∈ fullArenaClauseRefsCore k, fullArenaClauseGarbCore k r = false →
    ∀ l ∈ fullArenaClauseLitsCore k r, l < 2 * k.cur_vars
  entails : ∀ r ∈ fullArenaClauseRefsCore k, fullArenaClauseGarbCore k r = false →
    (cnfOfClauses F_cur).EntailsClause (cnfClause (fullArenaClauseLitsCore k r))

theorem FullArenaClausesInv.mono {c : FullCfg} {F F' : List (List Nat)} {k : FullCoreState}
    (hF : (cnfOfClauses F').Entails (cnfOfClauses F)) (h : FullArenaClausesInv c F k) :
    FullArenaClausesInv c F' k :=
  { h with entails := fun r hr hg => CNF.entails_clause_trans hF (h.entails r hr hg) }

theorem FullArenaClausesInv.disjoint {c : FullCfg} {F_cur : List (List Nat)}
    {k : FullCoreState} (h : FullArenaClausesInv c F_cur k) {r1 r2 : Nat}
    (hr1 : r1 ∈ fullArenaClauseRefsCore k) (hr2 : r2 ∈ fullArenaClauseRefsCore k) (hlt : r1 < r2) :
    r1 + 3 + fullArenaClauseSizeCore k r1 ≤ r2 := by
  have h1 := fullArenaScanRefs_disjoint hr1 hr2 hlt
  have h2 := (h.refs_wf r1 hr1).2.2.1; omega

theorem FullArenaClausesInv.chain_end {c : FullCfg} {F_cur : List (List Nat)}
    {k : FullCoreState} (h : FullArenaClausesInv c F_cur k) :
    k.arena_len = 0 ∨
      ∃ r ∈ fullArenaClauseRefsCore k, fullArenaNextOff k.arena k.arena_len r = k.arena_len := by
  rcases h.len_ok with hz | h3
  · exact Or.inl hz
  · exact Or.inr (fullArenaScanRefs_last (by omega) h3 fun r hr => (h.refs_wf r hr).2.2.2.2)

theorem FullArenaClausesInv.arenaNextOff_extend {c : FullCfg} {F_cur : List (List Nat)}
    {k : FullCoreState} (h : FullArenaClausesInv c F_cur k)
    {arena' : List (BitVec 32)} {alen' : Nat} (hal : k.arena_len ≤ alen')
    (hhold : ∀ i < k.arena_len, arena'[i]? = k.arena[i]?) :
    ∀ r ∈ fullArenaClauseRefsCore k,
      fullArenaNextOff arena' alen' r = fullArenaNextOff k.arena k.arena_len r := by
  intro r hr
  have hwf := h.refs_wf r hr
  have hbd : r + 3 + fullArenaClauseSizeCore k r ≤ k.arena_len := by omega
  have ha0 := hhold r (by omega); have ha2 := hhold (r + 2) (by omega)
  have h1 : ¬ (r + 3 > k.arena_len) := by omega
  have h1' : ¬ (r + 3 > alen') := by omega
  have h2 : ¬ (r + 3 + (k.arena[r + 2]?.getD 0#32).toNat > k.arena_len) := by
    unfold fullArenaClauseSizeCore at hbd; omega
  have h2' : ¬ (r + 3 + (k.arena[r + 2]?.getD 0#32).toNat > alen') := by omega
  unfold fullArenaNextOff; simp only [h1, h1', ↓reduceIte, ha0, ha2, h2, h2']
  by_cases hshrk : (k.arena[r]?.getD 0#32 &&& 0x00800000#32) = 0#32
  · simp [hshrk]
  · simp only [hshrk, ne_eq, not_false_eq_true, ↓reduceIte]
    obtain ⟨t, ht1, ht2, hsent⟩ := h.shrk_term r hr hshrk
    unfold fullArenaClauseSizeCore at ht1
    exact fullArenaSkipShrk_eq_of_sentinel ht2 hal hsent hhold ht1 (by omega) (by omega)

theorem fullArenaClauseRefsCore_append {c : FullCfg} {F_cur : List (List Nat)}
    {k k' : FullCoreState} {len : Nat}
    (ha : FullArenaClausesInv c F_cur k) (hge3 : 3 ≤ len)
    (halen : k'.arena_len = k.arena_len + 3 + len)
    (hhold : ∀ i < k.arena_len, k'.arena[i]? = k.arena[i]?)
    (hnoshrk : (k'.arena[k.arena_len]?.getD 0#32 &&& 0x00800000#32) = 0#32)
    (hsz : (k'.arena[k.arena_len + 2]?.getD 0#32).toNat = len) :
    fullArenaClauseRefsCore k' = fullArenaClauseRefsCore k ++ [k.arena_len] := by
  unfold fullArenaClauseRefsCore; rw [halen]
  exact fullArenaScanRefs_eq_of_prefix hge3 hnoshrk hsz
    (fun r hr => (ha.refs_wf r hr).2.2.2.2) ha.chain_end
    (ha.arenaNextOff_extend (by omega) hhold)

theorem FullArenaClausesInv.markGarb {c : FullCfg} {F_cur : List (List Nat)}
    {k : FullCoreState} (h : FullArenaClausesInv c F_cur k)
    (hlen : k.LengthsOk c) {cref : Nat} (href : cref ∈ fullArenaClauseRefsCore k)
    (ag' : BitVec 64) :
    let k' :=
      { k with
        arena := k.arena.set cref (fullArenaHdrCore k cref ||| 0x00080000#32)
        arena_garbage := ag' }
    fullArenaClauseRefsCore k' = fullArenaClauseRefsCore k ∧ FullArenaClausesInv c F_cur k' := by
  intro k'
  have hcref_wf := h.refs_wf cref href
  have har_len : cref < k.arena.length := by
    have := hlen.arena_len_le; have := hlen.arena_len_arr; omega
  have hget_cref : k.arena[cref]? = some (fullArenaHdrCore k cref) := by
    unfold fullArenaHdrCore; rw [List.getElem?_eq_getElem har_len, Option.getD_some]
  have ha_cref : k'.arena[cref]? = some (fullArenaHdrCore k cref ||| 0x00080000#32) :=
    List.getElem?_set_self har_len
  have hne_outside : ∀ r ∈ fullArenaClauseRefsCore k, r ≠ cref →
      (r + 3 + fullArenaClauseSizeCore k r ≤ cref ∧ fullArenaNextOff k.arena k.arena_len r ≤ cref) ∨
      (cref + 3 ≤ fullArenaNextOff k.arena k.arena_len cref ∧
        fullArenaNextOff k.arena k.arena_len cref ≤ r) := by
    intro r hr hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · exact Or.inl ⟨by have := fullArenaScanRefs_disjoint hr href hlt
                       have := (h.refs_wf r hr).2.2.1; omega,
        fullArenaScanRefs_disjoint hr href hlt⟩
    · exact Or.inr ⟨by omega, fullArenaScanRefs_disjoint href hr hgt⟩
  have hnxt : ∀ r ∈ fullArenaClauseRefsCore k,
      fullArenaNextOff k'.arena k.arena_len r = fullArenaNextOff k.arena k.arena_len r := by
    intro r hr; by_cases hrc : r = cref
    · subst r
      have h2eq : k'.arena[cref + 2]? = k.arena[cref + 2]? := List.getElem?_set_ne (by omega)
      have h1 : ¬ (cref + 3 > k.arena_len) := by omega
      have h2 : ¬ (cref + 3 + (k.arena[cref + 2]?.getD 0#32).toNat > k.arena_len) := by
        unfold fullArenaClauseSizeCore at hcref_wf; omega
      unfold fullArenaNextOff
      simp only [h1, ↓reduceIte, h2eq, h2, ha_cref, Option.getD_some]
      rw [bit23_or_garb, show fullArenaHdrCore k cref = k.arena[cref]?.getD 0#32 from rfl]
      split
      · exact fullArenaSkipShrk_congr fun i hi _ => List.getElem?_set_ne (by omega)
      · rfl
    · refine fullArenaNextOff_congr_block (List.getElem?_set_ne (Ne.symm hrc)) ?_ ?_
      · rcases hne_outside r hr hrc with ⟨hlt, _⟩ | ⟨h3, hgt⟩
        · have := (h.refs_wf r hr).2.1; exact List.getElem?_set_ne (by omega)
        · exact List.getElem?_set_ne (by omega)
      · intro i hi1 _
        rcases hne_outside r hr hrc with ⟨_, hle⟩ | ⟨h3, hgt⟩
        · exact List.getElem?_set_ne (by omega)
        · have := (h.refs_wf r hr).2.2.1; exact List.getElem?_set_ne (by omega)
  have hrefs : fullArenaClauseRefsCore k' = fullArenaClauseRefsCore k :=
    fullArenaClauseRefsCore_congr rfl hnxt
  have hsz_eq : ∀ r ∈ fullArenaClauseRefsCore k,
      fullArenaClauseSizeCore k' r = fullArenaClauseSizeCore k r := fun r hr => by
    unfold fullArenaClauseSizeCore; dsimp only [k']
    by_cases hrc : r = cref
    · subst r; rw [List.getElem?_set_ne (by omega)]
    · rcases hne_outside r hr hrc with ⟨hlt, _⟩ | ⟨h3, hgt⟩
      · have := (h.refs_wf r hr).2.1; rw [List.getElem?_set_ne (by omega)]
      · rw [List.getElem?_set_ne (by omega)]
  have hlits_eq : ∀ r ∈ fullArenaClauseRefsCore k, r ≠ cref →
      fullArenaClauseLitsCore k' r = fullArenaClauseLitsCore k r := fun r hr hne => by
    have hwf := h.refs_wf r hr
    have hk_bd : r + 3 + fullArenaClauseSizeCore k r ≤ k.arena.length := by
      have := hlen.arena_len_le; have := hlen.arena_len_arr; omega
    have hout : r + 3 + fullArenaClauseSizeCore k r ≤ cref ∨ cref + 3 ≤ r := by
      rcases hne_outside r hr hne with ⟨h1, _⟩ | ⟨h3, h2⟩ <;> omega
    exact (fullArenaClauseLitsCore_set_outside hk_bd hout).2
  refine ⟨hrefs, ⟨h.len_ok, ?_, ?_, ?_, ?_⟩⟩
  · intro r hr; rw [hrefs] at hr; have hwf := h.refs_wf r hr
    dsimp only [k'] at hnxt ⊢; rw [hnxt r hr, hsz_eq r hr]; exact hwf
  · intro r hr hsh; rw [hrefs] at hr
    have hsh0 : (fullArenaHdrCore k r &&& 0x00800000#32) ≠ 0#32 := by
      by_cases hrc : r = cref
      · subst r; unfold fullArenaHdrCore at hsh ⊢
        simpa [ha_cref, hget_cref, bit23_or_garb] using hsh
      · unfold fullArenaHdrCore at hsh ⊢; simpa [k', List.getElem?_set_ne (Ne.symm hrc)] using hsh
    obtain ⟨t, ht1, ht2, hsent⟩ := h.shrk_term r hr hsh0
    have hget_r : k.arena[r]? = some (fullArenaHdrCore k r) := by
      have hr3 := (h.refs_wf r hr).1
      have : r < k.arena.length := by have := hlen.arena_len_le; have := hlen.arena_len_arr; omega
      unfold fullArenaHdrCore; rw [List.getElem?_eq_getElem this, Option.getD_some]
    have hsh_ar : (k.arena[r]?.getD 0#32 &&& 0x00800000#32) ≠ 0#32 := by
      rw [hget_r, Option.getD_some]; exact hsh0
    obtain ⟨t0, ht0_lo, _, ht0_nxt, ht0_sent⟩ :=
      fullArenaNextOff_hits_sentinel (h.refs_wf r hr).1 hsh_ar ht1 ht2 hsent
    have ht0_ne : t0 ≠ cref := by
      by_cases hrc : r = cref
      · subst r; have := (h.refs_wf cref hr).2.1; omega
      · rcases hne_outside r hr hrc with ⟨_, hle⟩ | ⟨h3, hgt⟩
        · omega
        · have := (h.refs_wf r hr).2.1; omega
    have hszr := hsz_eq r hr
    have hkal : k'.arena_len = k.arena_len := rfl
    refine ⟨t0, by rw [hszr]; exact ht0_lo, by omega, ?_⟩
    dsimp only [k']; rw [List.getElem?_set_ne ht0_ne.symm]; exact ht0_sent
  · intro r hr hng l hl; rw [hrefs] at hr
    have hne : r ≠ cref := by
      rintro rfl; unfold fullArenaClauseGarbCore fullArenaHdrCore at hng
      rw [ha_cref, Option.getD_some] at hng; simp [bit19_or_garb_ne0] at hng
    have hng0 : fullArenaClauseGarbCore k r = false := by
      unfold fullArenaClauseGarbCore fullArenaHdrCore at hng ⊢
      simpa [k', List.getElem?_set_ne (Ne.symm hne)] using hng
    rw [hlits_eq r hr hne] at hl; exact h.lits_lt r hr hng0 l hl
  · intro r hr hng; rw [hrefs] at hr
    have hne : r ≠ cref := by
      rintro rfl; unfold fullArenaClauseGarbCore fullArenaHdrCore at hng
      rw [ha_cref, Option.getD_some] at hng; simp [bit19_or_garb_ne0] at hng
    have hng0 : fullArenaClauseGarbCore k r = false := by
      unfold fullArenaClauseGarbCore fullArenaHdrCore at hng ⊢
      simpa [k', List.getElem?_set_ne (Ne.symm hne)] using hng
    rw [hlits_eq r hr hne]; exact h.entails r hr hng0

/-! ## 2. Mode-indexed watches (`WatchesInv` 2WL & `DenseWatchesInv` binary + occ) -/

def fullWatchOffCore (k : FullCoreState) (l : Nat) : Nat := (k.wvec[2 * l]?.getD 0#32).toNat
def fullWatchSizeCore (k : FullCoreState) (l : Nat) : Nat := (k.wvec[2 * l + 1]?.getD 0#32).toNat
@[inline] abbrev fullWatchOff (s : FullState) (l : Nat) : Nat := fullWatchOffCore s.core l
@[inline] abbrev fullWatchSize (s : FullState) (l : Nat) : Nat := fullWatchSizeCore s.core l

theorem binWatchWord_ne_sentinel {w0 : BitVec 32}
    (hlt : (w0 &&& 0x7FFFFFFF#32).toNat < 0x7FFFFFFF) : w0 ≠ 0xFFFFFFFF#32 := by
  intro h; subst h; revert hlt; decide

/-- Sparse 2WL slice (`dense_mode = 0`): binary watch (`w0 &&& 0x80000000 ≠ 0`) or 2-word large
watch `(w0, cref)` with `cref ∈ fullArenaClauseRefsCore`. -/
inductive WatchSliceOk (F_cur : List (List Nat)) (k : FullCoreState) (lit : Nat) :
    Nat → Nat → Prop where
  | empty {p} : WatchSliceOk F_cur k lit p 0
  | bin {p rem w0} :
      k.wstk[p]? = some w0 → (w0 &&& 0x80000000#32) ≠ 0#32 → w0 ≠ 0xFFFFFFFF#32 →
      (w0 &&& 0x7FFFFFFF#32).toNat < 2 * k.cur_vars →
      (cnfOfClauses F_cur).EntailsClause (cnfClause [lit, (w0 &&& 0x7FFFFFFF#32).toNat]) →
      WatchSliceOk F_cur k lit (p + 1) rem → WatchSliceOk F_cur k lit p (rem + 1)
  | large {p rem w0 cref} :
      k.wstk[p]? = some w0 → k.wstk[p + 1]? = some cref →
      (w0 &&& 0x80000000#32) = 0#32 → cref.toNat < 0x80000000 →
      cref.toNat ∈ fullArenaClauseRefsCore k →
      WatchSliceOk F_cur k lit (p + 2) rem → WatchSliceOk F_cur k lit p (rem + 2)

/-- Dense occurrence slice (`dense_mode ≠ 0`): binary watch or 2-word `(sz & 0x7FFFFFFF, cref)`
occurrence entry (`3 ≤ w0.toNat`, `cref ∈ fullArenaClauseRefsCore`). -/
inductive DenseWatchSliceOk (F_cur : List (List Nat)) (k : FullCoreState) (lit : Nat) :
    Nat → Nat → Prop where
  | empty {p} : DenseWatchSliceOk F_cur k lit p 0
  | bin {p rem w0} :
      k.wstk[p]? = some w0 → (w0 &&& 0x80000000#32) ≠ 0#32 → w0 ≠ 0xFFFFFFFF#32 →
      (w0 &&& 0x7FFFFFFF#32).toNat < 2 * k.cur_vars →
      (cnfOfClauses F_cur).EntailsClause (cnfClause [lit, (w0 &&& 0x7FFFFFFF#32).toNat]) →
      DenseWatchSliceOk F_cur k lit (p + 1) rem → DenseWatchSliceOk F_cur k lit p (rem + 1)
  | occ {p rem w0 cref} :
      k.wstk[p]? = some w0 → k.wstk[p + 1]? = some cref →
      (w0 &&& 0x80000000#32) = 0#32 → 3 ≤ w0.toNat → cref.toNat < 0x80000000 →
      cref.toNat ∈ fullArenaClauseRefsCore k →
      DenseWatchSliceOk F_cur k lit (p + 2) rem → DenseWatchSliceOk F_cur k lit p (rem + 2)

theorem WatchSliceOk.mono {F F' : List (List Nat)} {k k' : FullCoreState} {lit p rem : Nat}
    (hF : (cnfOfClauses F').Entails (cnfOfClauses F)) (hvars : k.cur_vars ≤ k'.cur_vars)
    (hsub : ∀ r ∈ fullArenaClauseRefsCore k, r ∈ fullArenaClauseRefsCore k')
    (hwstk : ∀ idx, p ≤ idx → idx < p + rem → k'.wstk[idx]? = k.wstk[idx]?)
    (h : WatchSliceOk F k lit p rem) : WatchSliceOk F' k' lit p rem := by
  induction h with
  | empty => exact .empty
  | @bin p rem w0 hp hflag hne hlt hent _ ih =>
    exact .bin (by rw [hwstk p (by omega) (by omega), hp]) hflag hne (by omega)
      (CNF.entails_clause_trans hF hent) (ih fun idx hi1 hi2 => hwstk idx (by omega) (by omega))
  | @large p rem w0 cref hp hp1 hflag hlt href _ ih =>
    exact .large (by rw [hwstk p (by omega) (by omega), hp])
      (by rw [hwstk (p + 1) (by omega) (by omega), hp1])
      hflag hlt (hsub _ href) (ih fun idx hi1 hi2 => hwstk idx (by omega) (by omega))

theorem DenseWatchSliceOk.mono {F F' : List (List Nat)} {k k' : FullCoreState} {lit p rem : Nat}
    (hF : (cnfOfClauses F').Entails (cnfOfClauses F)) (hvars : k.cur_vars ≤ k'.cur_vars)
    (hsub : ∀ r ∈ fullArenaClauseRefsCore k, r ∈ fullArenaClauseRefsCore k')
    (hwstk : ∀ idx, p ≤ idx → idx < p + rem → k'.wstk[idx]? = k.wstk[idx]?)
    (h : DenseWatchSliceOk F k lit p rem) : DenseWatchSliceOk F' k' lit p rem := by
  induction h with
  | empty => exact .empty
  | @bin p rem w0 hp hflag hne hlt hent _ ih =>
    exact .bin (by rw [hwstk p (by omega) (by omega), hp]) hflag hne (by omega)
      (CNF.entails_clause_trans hF hent) (ih fun idx hi1 hi2 => hwstk idx (by omega) (by omega))
  | @occ p rem w0 cref hp hp1 hflag hsz hlt href _ ih =>
    exact .occ (by rw [hwstk p (by omega) (by omega), hp])
      (by rw [hwstk (p + 1) (by omega) (by omega), hp1])
      hflag hsz hlt (hsub _ href) (ih fun idx hi1 hi2 => hwstk idx (by omega) (by omega))

theorem WatchSliceOk.ne_sentinel {F_cur : List (List Nat)} {k : FullCoreState} {lit p rem : Nat}
    (h : WatchSliceOk F_cur k lit p rem) :
    ∀ idx < rem, k.wstk[p + idx]? ≠ some 0xFFFFFFFF#32 := by
  induction h with
  | empty => intro _ hk; omega
  | @bin p rem w0 hp _ hne _ _ _ ih =>
    intro idx hk; cases idx with
    | zero => rw [Nat.add_zero, hp]; exact fun heq => hne (Option.some.inj heq)
    | succ k' => simpa [Nat.add_assoc, Nat.add_comm 1 k'] using ih k' (by omega)
  | @large p rem w0 cref hp hp1 hflag hlt _ _ ih =>
    intro idx hk; rcases idx with _ | _ | k''
    · rw [Nat.add_zero, hp]; intro heq; have hw := Option.some.inj heq
      subst hw; revert hflag; decide
    · rw [hp1]; intro heq; have hc := Option.some.inj heq; subst hc; revert hlt; decide
    · simpa [show p + 2 + k'' = p + (k'' + 2) by omega] using ih k'' (by omega)

theorem DenseWatchSliceOk.ne_sentinel {F_cur : List (List Nat)} {k : FullCoreState}
    {lit p rem : Nat} (h : DenseWatchSliceOk F_cur k lit p rem) :
    ∀ idx < rem, k.wstk[p + idx]? ≠ some 0xFFFFFFFF#32 := by
  induction h with
  | empty => intro _ hk; omega
  | @bin p rem w0 hp _ hne _ _ _ ih =>
    intro idx hk; cases idx with
    | zero => rw [Nat.add_zero, hp]; exact fun heq => hne (Option.some.inj heq)
    | succ k' => simpa [Nat.add_assoc, Nat.add_comm 1 k'] using ih k' (by omega)
  | @occ p rem w0 cref hp hp1 hflag _ hlt _ _ ih =>
    intro idx hk; rcases idx with _ | _ | k''
    · rw [Nat.add_zero, hp]; intro heq; have hw := Option.some.inj heq
      subst hw; revert hflag; decide
    · rw [hp1]; intro heq; have hc := Option.some.inj heq; subst hc; revert hlt; decide
    · simpa [show p + 2 + k'' = p + (k'' + 2) by omega] using ih k'' (by omega)

/-- Pure structural watch-stack layout invariant (`0 ..< 2 * k.cur_vars`). -/
structure WatchStackLayout (k : FullCoreState) : Prop where
  bounds : ∀ l < 2 * k.cur_vars, fullWatchOffCore k l + fullWatchSizeCore k l ≤ k.wlen
  pos_off : ∀ l < 2 * k.cur_vars, 0 < fullWatchSizeCore k l → 1 ≤ fullWatchOffCore k l
  disjoint : ∀ l1 l2, l1 < 2 * k.cur_vars → l2 < 2 * k.cur_vars → l1 ≠ l2 →
    0 < fullWatchSizeCore k l1 → 0 < fullWatchSizeCore k l2 →
    fullWatchOffCore k l1 + fullWatchSizeCore k l1 ≤ fullWatchOffCore k l2 ∨
    fullWatchOffCore k l2 + fullWatchSizeCore k l2 ≤ fullWatchOffCore k l1
  no_sentinel : ∀ l < 2 * k.cur_vars, ∀ idx < fullWatchSizeCore k l,
    k.wstk[fullWatchOffCore k l + idx]? ≠ some 0xFFFFFFFF#32

theorem WatchStackLayout.with_wstk {k k' : FullCoreState} (h : WatchStackLayout k)
    (hvars : k'.cur_vars = k.cur_vars) (hw : k'.wvec = k.wvec) (hs : k'.wstk = k.wstk)
    (hl : k'.wlen = k.wlen) : WatchStackLayout k' :=
  ⟨fun l hl' => by
     unfold fullWatchOffCore fullWatchSizeCore; rw [hw, hl]; exact h.bounds l (hvars ▸ hl'),
   fun l hl' hpos => by
     unfold fullWatchSizeCore at hpos; unfold fullWatchOffCore
     rw [hw] at hpos ⊢; exact h.pos_off l (hvars ▸ hl') hpos,
   fun l1 l2 h1 h2 hne hp1 hp2 => by
     unfold fullWatchSizeCore at hp1 hp2; unfold fullWatchOffCore fullWatchSizeCore
     rw [hw] at hp1 hp2 ⊢; exact h.disjoint l1 l2 (hvars ▸ h1) (hvars ▸ h2) hne hp1 hp2,
   fun l hl' idx hidx => by
     unfold fullWatchSizeCore at hidx; unfold fullWatchOffCore; rw [hw] at hidx ⊢; rw [hs]
     exact h.no_sentinel l (hvars ▸ hl') idx hidx⟩

/-- Sparse 2WL invariant (`dense_mode = 0`). -/
structure WatchesInv (F_cur : List (List Nat)) (k : FullCoreState) : Prop where
  layout : WatchStackLayout k
  slices : ∀ l < 2 * k.cur_vars,
    WatchSliceOk F_cur k l (fullWatchOffCore k l) (fullWatchSizeCore k l)

/-- Dense occurrence invariant (`dense_mode ≠ 0`). -/
structure DenseWatchesInv (F_cur : List (List Nat)) (k : FullCoreState) : Prop where
  layout : WatchStackLayout k
  slices : ∀ l < 2 * k.cur_vars,
    DenseWatchSliceOk F_cur k l (fullWatchOffCore k l) (fullWatchSizeCore k l)

/-- Mode-indexed watch invariant covering sparse 2WL (`dense_mode = 0`) and dense mode
(`dense_mode ≠ 0`). -/
def ModeWatchesInv (F_cur : List (List Nat)) (k : FullCoreState) : Prop :=
  if k.dense_mode = 0#64 then WatchesInv F_cur k else DenseWatchesInv F_cur k

theorem WatchesInv.of_slices {F_cur : List (List Nat)} {k : FullCoreState}
    (hb : ∀ l < 2 * k.cur_vars, fullWatchOffCore k l + fullWatchSizeCore k l ≤ k.wlen)
    (hp : ∀ l < 2 * k.cur_vars, 0 < fullWatchSizeCore k l → 1 ≤ fullWatchOffCore k l)
    (hd : ∀ l1 l2, l1 < 2 * k.cur_vars → l2 < 2 * k.cur_vars → l1 ≠ l2 →
      0 < fullWatchSizeCore k l1 → 0 < fullWatchSizeCore k l2 →
      fullWatchOffCore k l1 + fullWatchSizeCore k l1 ≤ fullWatchOffCore k l2 ∨
      fullWatchOffCore k l2 + fullWatchSizeCore k l2 ≤ fullWatchOffCore k l1)
    (hs : ∀ l < 2 * k.cur_vars,
      WatchSliceOk F_cur k l (fullWatchOffCore k l) (fullWatchSizeCore k l)) :
    WatchesInv F_cur k :=
  ⟨⟨hb, hp, hd, fun l hl => (hs l hl).ne_sentinel⟩, hs⟩

theorem DenseWatchesInv.of_slices {F_cur : List (List Nat)} {k : FullCoreState}
    (hb : ∀ l < 2 * k.cur_vars, fullWatchOffCore k l + fullWatchSizeCore k l ≤ k.wlen)
    (hp : ∀ l < 2 * k.cur_vars, 0 < fullWatchSizeCore k l → 1 ≤ fullWatchOffCore k l)
    (hd : ∀ l1 l2, l1 < 2 * k.cur_vars → l2 < 2 * k.cur_vars → l1 ≠ l2 →
      0 < fullWatchSizeCore k l1 → 0 < fullWatchSizeCore k l2 →
      fullWatchOffCore k l1 + fullWatchSizeCore k l1 ≤ fullWatchOffCore k l2 ∨
      fullWatchOffCore k l2 + fullWatchSizeCore k l2 ≤ fullWatchOffCore k l1)
    (hs : ∀ l < 2 * k.cur_vars,
      DenseWatchSliceOk F_cur k l (fullWatchOffCore k l) (fullWatchSizeCore k l)) :
    DenseWatchesInv F_cur k :=
  ⟨⟨hb, hp, hd, fun l hl => (hs l hl).ne_sentinel⟩, hs⟩

theorem ModeWatchesInv.mono {F F' : List (List Nat)} {k : FullCoreState}
    (hF : (cnfOfClauses F').Entails (cnfOfClauses F)) (h : ModeWatchesInv F k) :
    ModeWatchesInv F' k := by
  by_cases hc : k.dense_mode = 0#64 <;> simp only [ModeWatchesInv, hc, ↓reduceIte] at h ⊢
  · exact ⟨h.layout, fun l hl =>
      (h.slices l hl).mono hF (Nat.le_refl _) (fun _ r => r) (fun _ _ _ => rfl)⟩
  · exact ⟨h.layout, fun l hl =>
      (h.slices l hl).mono hF (Nat.le_refl _) (fun _ r => r) (fun _ _ _ => rfl)⟩

theorem ModeWatchesInv.with_wstk {F_cur : List (List Nat)} {k k' : FullCoreState}
    (h : ModeWatchesInv F_cur k) (hdm : k'.dense_mode = k.dense_mode)
    (hvars : k'.cur_vars = k.cur_vars) (hw : k'.wvec = k.wvec) (hs : k'.wstk = k.wstk)
    (hl : k'.wlen = k.wlen)
    (ha : ∀ r ∈ fullArenaClauseRefsCore k, r ∈ fullArenaClauseRefsCore k') :
    ModeWatchesInv F_cur k' := by
  by_cases hc : k.dense_mode = 0#64 <;>
    simp only [ModeWatchesInv, hdm, hc, ↓reduceIte] at h ⊢
  · refine ⟨h.layout.with_wstk hvars hw hs hl, fun l hl' => ?_⟩
    simpa [fullWatchOffCore, fullWatchSizeCore, hw] using
      (h.slices l (hvars ▸ hl')).mono (by rw [CNF.entails_def]; exact fun _ p => p)
        (by omega) ha (fun _ _ _ => by simp [hs])
  · refine ⟨h.layout.with_wstk hvars hw hs hl, fun l hl' => ?_⟩
    simpa [fullWatchOffCore, fullWatchSizeCore, hw] using
      (h.slices l (hvars ▸ hl')).mono (by rw [CNF.entails_def]; exact fun _ p => p)
        (by omega) ha (fun _ _ _ => by simp [hs])

theorem ModeWatchesInv.layout {F_cur : List (List Nat)} {k : FullCoreState}
    (h : ModeWatchesInv F_cur k) : WatchStackLayout k := by
  by_cases hc : k.dense_mode = 0#64 <;> simp only [ModeWatchesInv, hc, ↓reduceIte] at h
  · exact h.layout
  · exact h.layout

theorem ModeWatchesInv.bounds {F_cur : List (List Nat)} {k : FullCoreState}
    (h : ModeWatchesInv F_cur k) :
    ∀ l < 2 * k.cur_vars, fullWatchOffCore k l + fullWatchSizeCore k l ≤ k.wlen :=
  h.layout.bounds

theorem ModeWatchesInv.no_sentinel {F_cur : List (List Nat)} {k : FullCoreState}
    (h : ModeWatchesInv F_cur k) :
    ∀ l < 2 * k.cur_vars, ∀ idx < fullWatchSizeCore k l,
      k.wstk[fullWatchOffCore k l + idx]? ≠ some 0xFFFFFFFF#32 :=
  h.layout.no_sentinel

/-! ## 3. Stage-4 UNSAT-only core invariant, `ChronoTrailInv` bridge, & refutation -/

/-- Witnessed Stage-4 core invariant linking `FullCoreState` to an UNSAT-equivalent current
formula `F_cur` (`ExtUnsatSound F0 k.cur_vars F_cur`), chronological trail/reason DAG,
`frame_trail`/`frame_dec` bounds, `PH_SHRK`-aware arena, and mode-indexed watches. -/
structure FullWitnessInv (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (k : FullCoreState) : Prop where
  ext_sound : ExtUnsatSound F0 k.cur_vars F_cur
  inconsistent_sound : k.inconsistent ≠ 0#64 → (cnfOfClauses F_cur).Unsat
  arena : FullArenaClausesInv c F_cur k
  watches : ModeWatchesInv F_cur k
  cur_level_le : k.cur_level ≤ k.trail_end
  trail_lits_lt : ∀ i < k.trail_end, (k.trl[i]?.getD 0#32).toNat < 2 * k.cur_vars
  trail_vars_nodup : ∀ i j, i < k.trail_end → j < k.trail_end →
    (k.trl[i]?.getD 0#32).toNat / 2 = (k.trl[j]?.getD 0#32).toNat / 2 → i = j
  vals_domain : ∀ l < 2 * k.cur_vars,
    k.vals[l]?.getD 0#8 = 0#8 ∨ k.vals[l]?.getD 0#8 = 1#8 ∨ k.vals[l]?.getD 0#8 = 0xFF#8
  vals_true_iff : ∀ l < 2 * k.cur_vars,
    k.vals[l]?.getD 0#8 = 1#8 ↔ ∃ i < k.trail_end, (k.trl[i]?.getD 0#32).toNat = l
  vals_false_iff : ∀ l < 2 * k.cur_vars,
    k.vals[l]?.getD 0#8 = 0xFF#8 ↔ ∃ i < k.trail_end, (k.trl[i]?.getD 0#32).toNat = l ^^^ 1
  lvl_le : ∀ i < k.trail_end,
    (k.lvl[(k.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ k.cur_level
  dec_earliest : ∀ i j, i < k.trail_end → j < k.trail_end →
    (k.lvl[(k.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat =
    (k.lvl[(k.trl[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat →
    (0 < (k.lvl[(k.trl[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ∧
      k.rsns[(k.trl[j]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32) → j ≤ i
  levels_inhabited : ∀ L, 1 ≤ L → L ≤ k.cur_level →
    ∃ i < k.trail_end, (k.lvl[(k.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = L
  level0_sound : ∀ i < k.trail_end,
    (k.lvl[(k.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 →
    (cnfOfClauses F_cur).EntailsClause (cnfClause [(k.trl[i]?.getD 0#32).toNat])
  trail_pos_inv : ∀ i < k.trail_end,
    (k.trail_pos[(k.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = i
  level0_rsn_none : ∀ idx < k.trail_end,
    (k.lvl[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 →
    k.rsns[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32
  frame_trail_lt : ∀ L ≤ k.cur_level, (k.frame_trail[L]?.getD 0#32).toNat ≤ k.trail_end
  frame_trail_mono : ∀ L1 L2, L1 ≤ L2 → L2 ≤ k.cur_level →
    (k.frame_trail[L1]?.getD 0#32).toNat ≤ (k.frame_trail[L2]?.getD 0#32).toNat
  frame_trail_before_lt : ∀ L, 1 ≤ L → L ≤ k.cur_level →
    ∀ i < (k.frame_trail[L]?.getD 0#32).toNat,
      (k.lvl[(k.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat < L
  frame_dec_lt : ∀ L, 1 ≤ L → L ≤ k.cur_level →
    (k.frame_dec[L]?.getD 0#32).toNat < 2 * k.cur_vars
  reason_inv : ∀ idx < k.trail_end,
    let p := (k.trl[idx]?.getD 0#32).toNat
    let rsn := k.rsns[p / 2]?.getD 0xFFFFFFFF#32
    rsn ≠ 0xFFFFFFFF#32 →
      if (rsn &&& 0x80000000#32) ≠ 0#32 then
        let ot := (rsn &&& 0x7FFFFFFF#32).toNat
        ot < 2 * k.cur_vars ∧ (cnfOfClauses F_cur).EntailsClause (cnfClause [p, ot]) ∧
        ∃ m < idx, (k.trl[m]?.getD 0#32).toNat = ot ^^^ 1 ∧
          (k.lvl[ot / 2]?.getD 0#32).toNat ≤ (k.lvl[p / 2]?.getD 0#32).toNat
      else
        rsn.toNat ∈ fullArenaClauseRefsCore k ∧ fullArenaClauseGarbCore k rsn.toNat = false ∧
        ∀ q ∈ fullArenaClauseLitsCore k rsn.toNat,
          q = p ∨ ∃ m < idx, (k.trl[m]?.getD 0#32).toNat = q ^^^ 1 ∧
            (k.lvl[q / 2]?.getD 0#32).toNat ≤ (k.lvl[p / 2]?.getD 0#32).toNat
  reason_lit_mem : ∀ idx < k.trail_end,
    let p := (k.trl[idx]?.getD 0#32).toNat
    let rsn := k.rsns[p / 2]?.getD 0xFFFFFFFF#32
    rsn ≠ 0xFFFFFFFF#32 → (rsn &&& 0x80000000#32) = 0#32 →
      p ∈ fullArenaClauseLitsCore k rsn.toNat

/-- Stage-4 UNSAT-only core invariant (existentially packaging `F_cur`). -/
structure FullCoreInv (c : FullCfg) (F0 : CNF Nat) (s : FullState) : Prop where
  lengths : s.LengthsOk c
  witness : ∃ F_cur, FullWitnessInv c F0 F_cur s.core

/-- All entries of `s.core.mrk[0 ..< s.core.cur_vars)` are zero. -/
def FullMarksClear (s : FullState) : Prop :=
  ∀ v < s.core.cur_vars, s.core.mrk[v]?.getD 0#8 = 0#8

/-- Complete Stage-4 CDCL + inprocessing solver invariant (`FullCoreInv` + `FullMarksClear`). -/
structure FullInv (c : FullCfg) (F0 : CNF Nat) (s : FullState) : Prop where
  core : FullCoreInv c F0 s
  marks : FullMarksClear s

/-- Constructive projection from `FullCoreState` + `F_cur` to `LayerAFull.ChronoState`.
Only non-garbage arena slots become `some c` so `db_sound` holds under GC and weakening. -/
def toChronoState (k : FullCoreState) (F_cur : List (List Nat)) : ChronoState :=
  let clauses : Array (Option Clause) :=
    ((List.range k.arena_len).map fun r =>
      if r ∈ fullArenaClauseRefsCore k ∧ fullArenaClauseGarbCore k r = false then
        some
          { lits := fullArenaClauseLitsCore k r
            redundant := (fullArenaHdrCore k r &&& 0x00100000#32) != 0#32
            garbage := false
            glue := (fullArenaHdrCore k r &&& 0xFFFF#32).toNat }
      else none).toArray
  let reasons : Array Reason :=
    ((List.range k.cur_vars).map fun v =>
      let lv := (k.lvl[v]?.getD 0#32).toNat
      let rsn := k.rsns[v]?.getD 0xFFFFFFFF#32
      if lv = 0 then Reason.unit
      else if rsn = 0xFFFFFFFF#32 then Reason.decision
      else if (rsn &&& 0x80000000#32) ≠ 0#32 then Reason.binary (rsn &&& 0x7FFFFFFF#32).toNat
      else Reason.large rsn.toNat).toArray
  let isDec : Array Bool :=
    ((List.range k.cur_vars).map fun v =>
      decide (0 < (k.lvl[v]?.getD 0#32).toNat ∧
        k.rsns[v]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32)).toArray
  { cdcl :=
      { f0 := cnfOfClauses F_cur
        numVars := k.cur_vars
        clauses := clauses
        units := []
        trail := ((k.trl.take k.trail_end).map BitVec.toNat).toArray
        levels := ((k.lvl.take k.cur_vars).map BitVec.toNat).toArray
        reasons := reasons
        level := k.cur_level
        inconsistent := decide (k.inconsistent ≠ 0#64) }
    isDec := isDec
    frames := ((k.frame_trail.take (k.cur_level + 1)).map BitVec.toNat).toArray }

private theorem toArray_getElem?_eq {α : Type} (xs : List α) (i : Nat) :
    xs.toArray[i]? = xs[i]? := by
  by_cases hi : i < xs.length
  · have hlt : i < xs.toArray.size := by simpa using hi
    rw [Array.getElem?_eq_getElem hlt, List.getElem?_eq_getElem hi]; rfl
  · have hge : ¬ i < xs.toArray.size := by simpa using hi
    rw [Array.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]

theorem fullWitnessInv_to_chronoTrailInv {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hlen : k.LengthsOk c) (hw : FullWitnessInv c F0 F_cur k) :
    ChronoTrailInv (toChronoState k F_cur) ∧
      (toChronoState k F_cur).cdcl.f0 = cnfOfClauses F_cur := by
  let cs := toChronoState k F_cur
  have htrl_sz : cs.cdcl.trail.size = k.trail_end := by
    change ((k.trl.take k.trail_end).map BitVec.toNat).toArray.size = k.trail_end
    rw [show ∀ (xs : List Nat), xs.toArray.size = xs.length from fun _ => rfl,
      List.length_map, List.length_take]
    have := hlen.trl_len; have := hlen.trail_end_le; have := hlen.cur_vars_le; omega
  have htrl_get : ∀ i (hi : i < cs.cdcl.trail.size),
      cs.cdcl.trail[i] = (k.trl[i]?.getD 0#32).toNat := fun i hi => by
    have hilt : i < k.trail_end := htrl_sz ▸ hi
    have hik : i < k.trl.length := by
      have := hlen.trl_len; have := hlen.trail_end_le; have := hlen.cur_vars_le; omega
    change ((k.trl.take k.trail_end).map BitVec.toNat)[i]'(by
      rw [List.length_map, List.length_take]; omega) = _
    rw [List.getElem_map, List.getElem_take, List.getElem?_eq_getElem hik, Option.getD_some]
  have hsl : ∀ l, litVar l < k.cur_vars →
      stateLevel cs.cdcl l = (k.lvl[litVar l]?.getD 0#32).toNat := fun l hlt => by
    have hlv := hlen.lvl_len; have hcv := hlen.cur_vars_le
    unfold stateLevel; rw [Array.getD_eq_getD_getElem?]
    change ((k.lvl.take k.cur_vars).map BitVec.toNat).toArray[litVar l]?.getD 0 = _
    rw [toArray_getElem?_eq, List.getElem?_map, List.getElem?_take, ite_eq_left hlt,
      List.getElem?_eq_getElem (by omega), Option.map_some, Option.getD_some, Option.getD_some]
  have hsr : ∀ l, litVar l < k.cur_vars →
      stateReason cs.cdcl l =
        if (k.lvl[litVar l]?.getD 0#32).toNat = 0 then Reason.unit
        else if k.rsns[litVar l]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 then Reason.decision
        else if (k.rsns[litVar l]?.getD 0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32 then
          Reason.binary (k.rsns[litVar l]?.getD 0xFFFFFFFF#32 &&& 0x7FFFFFFF#32).toNat
        else Reason.large (k.rsns[litVar l]?.getD 0xFFFFFFFF#32).toNat := fun l hlt => by
    unfold stateReason; rw [Array.getD_eq_getD_getElem?]
    change (((List.range k.cur_vars).map fun v => _).toArray[litVar l]?).getD Reason.unit = _
    rw [toArray_getElem?_eq, List.getElem?_map, List.getElem?_range hlt,
      Option.map_some, Option.getD_some]
  have hisdec : ∀ l, litVar l < k.cur_vars →
      cs.isDecision l =
        decide (0 < (k.lvl[litVar l]?.getD 0#32).toNat ∧
          k.rsns[litVar l]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32) := fun l hlt => by
    unfold ChronoState.isDecision; rw [Array.getD_eq_getD_getElem?]
    change (((List.range k.cur_vars).map fun v => _).toArray[litVar l]?).getD false = _
    rw [toArray_getElem?_eq, List.getElem?_map, List.getElem?_range hlt,
      Option.map_some, Option.getD_some]
  have hdec_sync : ∀ i (hi : i < cs.cdcl.trail.size),
      cs.isDecision cs.cdcl.trail[i] =
        decide (stateReason cs.cdcl cs.cdcl.trail[i] = .decision) := fun i hi => by
    have hilt : i < k.trail_end := htrl_sz ▸ hi
    have hlt : litVar cs.cdcl.trail[i] < k.cur_vars := by
      rw [htrl_get i hi]; exact Nat.div_lt_of_lt_mul (hw.trail_lits_lt i hilt)
    rw [hisdec _ hlt, hsr _ hlt]
    by_cases h0 : (k.lvl[litVar cs.cdcl.trail[i]]?.getD 0#32).toNat = 0
    · simp [h0]
    · by_cases hr : k.rsns[litVar cs.cdcl.trail[i]]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32
      · simp [h0, Nat.zero_lt_of_ne_zero h0, hr]
      · by_cases hb : (k.rsns[litVar cs.cdcl.trail[i]]?.getD 0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32
        · simp [h0, hr, hb]
        · simp [h0, hr, hb]
  refine ⟨⟨?_, ?_, hdec_sync, ?_, ?_, ?_, ?_, ?_⟩, rfl⟩
  · intro i j hi hj hveq; rw [htrl_get i hi, htrl_get j hj] at hveq
    exact hw.trail_vars_nodup i j (htrl_sz ▸ hi) (htrl_sz ▸ hj) hveq
  · intro i hi
    have hilt : i < k.trail_end := htrl_sz ▸ hi
    have hlt : litVar cs.cdcl.trail[i] < k.cur_vars := by
      rw [htrl_get i hi]; exact Nat.div_lt_of_lt_mul (hw.trail_lits_lt i hilt)
    rw [hsl _ hlt, htrl_get i hi]; exact hw.lvl_le i hilt
  · intro i j hi hj hleq hdec
    have hilt := htrl_sz ▸ hi; have hjlt := htrl_sz ▸ hj
    have hli : litVar cs.cdcl.trail[i] < k.cur_vars := by
      rw [htrl_get i hi]; exact Nat.div_lt_of_lt_mul (hw.trail_lits_lt i hilt)
    have hlj : litVar cs.cdcl.trail[j] < k.cur_vars := by
      rw [htrl_get j hj]; exact Nat.div_lt_of_lt_mul (hw.trail_lits_lt j hjlt)
    rw [hsl _ hli, hsl _ hlj, htrl_get i hi, htrl_get j hj] at hleq
    rw [hisdec _ hlj, htrl_get j hj] at hdec
    exact hw.dec_earliest i j hilt hjlt hleq (of_decide_eq_true hdec)
  · intro cid cl hget
    change (((List.range k.arena_len).map fun r => _).toArray[cid]?) = some (some cl) at hget
    rw [toArray_getElem?_eq, List.getElem?_map] at hget
    by_cases hlt : cid < k.arena_len
    · rw [List.getElem?_range hlt] at hget; simp only [Option.map_some, Option.some.injEq] at hget
      by_cases hc : cid ∈ fullArenaClauseRefsCore k ∧ fullArenaClauseGarbCore k cid = false
      · rw [ite_eq_left hc] at hget; cases hget; exact hw.arena.entails cid hc.1 hc.2
      · rw [ite_eq_right hc] at hget; cases hget
    · rw [List.getElem?_eq_none (by simp; omega)] at hget; cases hget
  · intro u hu; cases hu
  · intro i hi
    have hilt : i < k.trail_end := htrl_sz ▸ hi
    let p := (k.trl[i]?.getD 0#32).toNat
    have hp_lt : p < 2 * k.cur_vars := hw.trail_lits_lt i hilt
    have hp_v : litVar p < k.cur_vars := Nat.div_lt_of_lt_mul hp_lt
    have heql : cs.cdcl.trail[i] = p := htrl_get i hi
    change match stateReason cs.cdcl cs.cdcl.trail[i] with | _ => _
    rw [heql, hsr p hp_v, show litVar p = p / 2 from rfl]
    by_cases hlv0 : (k.lvl[p / 2]?.getD 0#32).toNat = 0
    · rw [ite_eq_left hlv0]
      exact ⟨by rw [hsl p hp_v]; exact hlv0, hw.level0_sound i hilt hlv0⟩
    · rw [ite_eq_right hlv0]
      by_cases hrsn : k.rsns[p / 2]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32
      · rw [ite_eq_left hrsn]; rw [hsl p hp_v]; exact Nat.zero_lt_of_ne_zero hlv0
      · rw [ite_eq_right hrsn]
        have hri := hw.reason_inv i hilt hrsn
        change (if (k.rsns[p / 2]?.getD 0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32 then _ else _)
          at hri
        by_cases hbin : (k.rsns[p / 2]?.getD 0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32
        · rw [ite_eq_left hbin] at hri ⊢
          obtain ⟨hot_lt, hent, m, hm_lt, hmeq, hlvl_le⟩ := hri
          have hm_sz : m < cs.cdcl.trail.size := htrl_sz ▸ by omega
          have hot_v : litVar ((k.rsns[p / 2]?.getD 0xFFFFFFFF#32 &&& 0x7FFFFFFF#32).toNat) <
              k.cur_vars := Nat.div_lt_of_lt_mul hot_lt
          refine ⟨hent, m, hm_sz, hm_lt, htrl_get m hm_sz ▸ hmeq, ?_, ?_⟩
          · rw [hsl _ hot_v, hsl p hp_v]; exact hlvl_le
          · rw [hsl _ hot_v, hsl p hp_v]
            exact (Nat.lt_or_eq_of_le hlvl_le).elim Or.inl fun he => Or.inr ⟨he, hm_lt⟩
        · have hbin' : (k.rsns[p / 2]?.getD 0xFFFFFFFF#32 &&& 0x80000000#32) = 0#32 :=
            Classical.byContradiction fun h => hbin h
          rw [ite_eq_right hbin] at hri ⊢
          obtain ⟨href, hng, hall⟩ := hri
          dsimp only [p] at href hng hall ⊢
          have hr_lt : (k.rsns[(k.trl[i]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat <
              k.arena_len := by
            have := (hw.arena.refs_wf _ href).1; omega
          have hmem_p := hw.reason_lit_mem i hilt hrsn hbin'
          refine ⟨{ lits := fullArenaClauseLitsCore k
                      (k.rsns[(k.trl[i]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat
                    redundant := (fullArenaHdrCore k
                      (k.rsns[(k.trl[i]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat &&&
                      0x00100000#32) != 0#32
                    garbage := false
                    glue := (fullArenaHdrCore k
                      (k.rsns[(k.trl[i]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat &&&
                      0xFFFF#32).toNat },
            ?_, rfl, hmem_p, ?_⟩
          · change (((List.range k.arena_len).map fun r => _).toArray[
              (k.rsns[(k.trl[i]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat]?) = _
            rw [toArray_getElem?_eq, List.getElem?_map, List.getElem?_range hr_lt]
            simp [href, hng]
          · intro q hq hne
            rcases hall q hq with rfl | ⟨m, hm_lt, hmeq, hlvl_le⟩
            · exact absurd rfl hne
            · have hm_sz : m < cs.cdcl.trail.size := htrl_sz ▸ by omega
              have hq_v : litVar q < k.cur_vars :=
                Nat.div_lt_of_lt_mul (hw.arena.lits_lt _ href hng q hq)
              refine ⟨m, hm_sz, hm_lt, htrl_get m hm_sz ▸ hmeq, ?_, ?_⟩
              · rw [hsl _ hq_v, hsl p hp_v]; exact hlvl_le
              · rw [hsl _ hq_v, hsl p hp_v]
                exact (Nat.lt_or_eq_of_le hlvl_le).elim Or.inl fun he => Or.inr ⟨he, hm_lt⟩
  · intro hinc; simp only [toChronoState, decide_eq_true_eq] at hinc
    exact hw.inconsistent_sound hinc

theorem fullCoreInv_to_chronoTrailInv {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hinv : FullCoreInv c F0 s) :
    ∃ F_cur, ExtUnsatSound F0 s.core.cur_vars F_cur ∧
      FullWitnessInv c F0 F_cur s.core ∧ ChronoTrailInv (toChronoState s.core F_cur) := by
  obtain ⟨F_cur, hw⟩ := hinv.witness
  exact ⟨F_cur, hw.ext_sound, hw, (fullWitnessInv_to_chronoTrailInv hinv.lengths.core_ok hw).1⟩

theorem FullWitnessInv.vals_zero_iff {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (h : FullWitnessInv c F0 F_cur k) {l : Nat} (hl : l < 2 * k.cur_vars) :
    k.vals[l]?.getD 0#8 = 0#8 ↔ ∀ i < k.trail_end, (k.trl[i]?.getD 0#32).toNat / 2 ≠ l / 2 := by
  constructor
  · intro hz i hi hvar
    rcases (litVar_eq_iff _ l).mp hvar with h1 | h2
    · have ht := (h.vals_true_iff l hl).mpr ⟨i, hi, h1⟩; rw [hz] at ht; cases ht
    · have hf := (h.vals_false_iff l hl).mpr ⟨i, hi, h2⟩; rw [hz] at hf; cases hf
  · intro hnone
    rcases h.vals_domain l hl with h0 | h1 | h2
    · exact h0
    · obtain ⟨i, hi, heq⟩ := (h.vals_true_iff l hl).mp h1; exact absurd (by rw [heq]) (hnone i hi)
    · obtain ⟨i, hi, heq⟩ := (h.vals_false_iff l hl).mp h2
      exact absurd (by rw [heq, fullInv_var_xor1]) (hnone i hi)

theorem FullWitnessInv.trail_end_lt_of_unassigned {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {k : FullCoreState} (h : FullWitnessInv c F0 F_cur k) {l : Nat}
    (hl : l < 2 * k.cur_vars) (hun : k.vals[l]?.getD 0#8 = 0#8) : k.trail_end < k.cur_vars :=
  inj_lt_of_missing (fun i => (k.trl[i]?.getD 0#32).toNat / 2)
    (fun i j hi hj heq => h.trail_vars_nodup i j hi hj heq)
    (fun i hi => by have := h.trail_lits_lt i hi; omega) (by omega) ((h.vals_zero_iff hl).mp hun)

theorem FullCoreInv.inconsistent_unsat {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullCoreInv c F0 s) (hinc : s.core.inconsistent ≠ 0#64) : F0.Unsat := by
  obtain ⟨_, hw⟩ := h.witness; exact hw.ext_sound.2 (hw.inconsistent_sound hinc)

theorem FullCoreInv.level0_unsat_of_bin_conflict {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullCoreInv c F0 s) (hl0 : s.core.cur_level = 0) {l0 l1 : Nat}
    (h0lt : l0 < 2 * s.core.cur_vars) (h1lt : l1 < 2 * s.core.cur_vars)
    (hent : ∀ F_cur, FullWitnessInv c F0 F_cur s.core →
      (cnfOfClauses F_cur).EntailsClause (cnfClause [l0, l1]))
    (hf0 : s.core.vals[l0]?.getD 0#8 = 0xFF#8) (hf1 : s.core.vals[l1]?.getD 0#8 = 0xFF#8) :
    F0.Unsat := by
  obtain ⟨F_cur, hw⟩ := h.witness
  refine hw.ext_sound.2
    (unsat_of_entails_nil (entails_of_mem_or_false (hent F_cur hw) fun l hl => ?_))
  right; simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl
  · obtain ⟨i, hi, hieq⟩ := (hw.vals_false_iff l h0lt).mp hf0
    have hs := hw.level0_sound i hi (by have := hw.lvl_le i hi; omega); rwa [hieq] at hs
  · obtain ⟨i, hi, hieq⟩ := (hw.vals_false_iff l h1lt).mp hf1
    have hs := hw.level0_sound i hi (by have := hw.lvl_le i hi; omega); rwa [hieq] at hs

theorem FullCoreInv.level0_unsat_of_conflict {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullCoreInv c F0 s) (hl0 : s.core.cur_level = 0)
    {cref : Nat} (href : cref ∈ fullArenaClauseRefs s) (hg : fullArenaClauseGarb s cref = false)
    (hfals : ∀ l ∈ fullArenaClauseLits s cref, s.core.vals[l]?.getD 0#8 = 0xFF#8) : F0.Unsat := by
  obtain ⟨F_cur, hw⟩ := h.witness
  refine hw.ext_sound.2 (unsat_of_entails_nil
    (entails_of_mem_or_false (hw.arena.entails cref href hg) fun l hl => Or.inr ?_))
  obtain ⟨i, hi, hieq⟩ := (hw.vals_false_iff l (hw.arena.lits_lt cref href hg l hl)).mp (hfals l hl)
  have hs := hw.level0_sound i hi (by have := hw.lvl_le i hi; omega); rwa [hieq] at hs

end LeanQbe.T.Examples.Kissat.Full
