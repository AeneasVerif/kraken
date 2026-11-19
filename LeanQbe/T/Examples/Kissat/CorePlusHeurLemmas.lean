module

public import LeanQbe.T.Examples.Kissat.CorePlusSpec
public import LeanQbe.T.Logic.C0Step
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat `D-Core+` Heuristic & Decision `Func.wp` Proofs (`Wave 1b`)

Proves `Func.wp` contracts for all 8 Group-A heuristic helpers plus `kissat_decide`:
1. Binary max-heap operations: `kissat_heap_sift_up_wp`, `kissat_heap_sift_down_wp`,
   `kissat_heap_push_wp`, `kissat_heap_pop_max_wp` (plus heap-length-preserving/decreasing
   strengthenings `corePlusHeapSiftDownSpec'` / `corePlusHeapPopMaxSpec'` for `kissat_decide`
   Loop-1 termination).
2. EVSIDS scoring and reluctant restarts: `kissat_rescale_scores_wp`, `kissat_bump_var_wp`,
   `kissat_bump_decay_wp`, `kissat_tick_reluctant_wp`.
3. Decision procedure: `kissat_decide_wp` (`corePlusDecideSpec`).

All proofs use flat `withH s h` heuristic framing with `@[local c0_load]` / `@[local c0_store]`
adapters over `CorePlusMem`, keeping every core soundness field untouched in Group A.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.CorePlus

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open Kraken.Bedrock2.Test

/-! ## 1. Flat heuristic framing (`withH`), `CorePlusMem` `c0_load`/`c0_store`, and BV helpers -/

/-- Flat heuristic-only update on `CorePlusState` so repeated stores never nest 26-field updates. -/
private def withH (s : CorePlusState) (h : HeurState) : CorePlusState :=
  { s with heur := h }

private theorem cp_load_heap0 {c : CorePlusCfg} {s : CorePlusState} {R : Mem 64 → Prop}
    {m : Mem 64} (hm : (CorePlusMem c s ⋆ R) m) (hi : 0 < s.heur.heap.length) :
    loadVal m i32 (c.pHeap + 0#64) = some (s.heur.heap[0]'hi) :=
  load_arena_heap (i := 0) hi hm

private theorem cp_store_heap0 {c : CorePlusCfg} {s : CorePlusState} {R : Mem 64 → Prop}
    {m : Mem 64} (v : BitVec 32) (hm : (CorePlusMem c s ⋆ R) m) (hi : 0 < s.heur.heap.length) :
    storeOk m i32 (c.pHeap + 0#64) ∧
      (CorePlusMem c { s with heur := { s.heur with heap := s.heur.heap.set 0 v } } ⋆ R)
        (storeMem m i32 (c.pHeap + 0#64) v) :=
  store_arena_heap (i := 0) v hi hm

attribute [local c0_load] cp_load_heap0
attribute [local c0_store] cp_store_heap0

private theorem heur_heap_mk (a b c d e f g h i j k hp ps sc ph) :
    (HeurState.mk a b c d e f g h i j k hp ps sc ph).heap = hp := rfl
private theorem heur_pos_mk (a b c d e f g h i j k hp ps sc ph) :
    (HeurState.mk a b c d e f g h i j k hp ps sc ph).pos = ps := rfl
private theorem heur_score_mk (a b c d e f g h i j k hp ps sc ph) :
    (HeurState.mk a b c d e f g h i j k hp ps sc ph).score = sc := rfl
private theorem heur_phases_mk (a b c d e f g h i j k hp ps sc ph) :
    (HeurState.mk a b c d e f g h i j k hp ps sc ph).phases = ph := rfl
private theorem heur_heap_len_mk (a b c d e f g h i j k hp ps sc ph) :
    (HeurState.mk a b c d e f g h i j k hp ps sc ph).heap_len = a := rfl

private theorem bv32_toNat_mod64 (x : BitVec 32) : x.toNat % 2 ^ 64 = x.toNat :=
  Nat.mod_eq_of_lt (Nat.lt_trans x.isLt (by decide))

private theorem bv32_toNat_mod64' (x : BitVec 32) :
    x.toNat % 18446744073709551616 = x.toNat := bv32_toNat_mod64 x

private theorem bv32_setWidth64_toNat (x : BitVec 32) :
    (BitVec.setWidth 64 x).toNat = x.toNat := by
  rw [BitVec.toNat_setWidth]; exact bv32_toNat_mod64 x

private theorem bv64_shl1_nat_toNat (x : BitVec 64) :
    (x <<< (1 : Nat)).toNat = (2 * x.toNat) % 2 ^ 64 := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; simp [Nat.mul_comm]

private theorem bv64_one_toNat : (1 : BitVec 64).toNat = 1 := rfl

private theorem bv64_shl1_bv_toNat (x : BitVec 64) :
    (x <<< (1 : BitVec 64)).toNat = (2 * x.toNat) % 2 ^ 64 := bv64_shl1_nat_toNat x

private theorem bv64_shl1_lit_toNat (x : BitVec 64) :
    (x <<< 1#64).toNat = (2 * x.toNat) % 2 ^ 64 := bv64_shl1_nat_toNat x

private theorem withH_heur (s : CorePlusState) (h : HeurState) : (withH s h).heur = h := rfl
private theorem withH_cur_level (s : CorePlusState) (h : HeurState) :
    (withH s h).cur_level = s.cur_level := rfl
private theorem withH_vals (s : CorePlusState) (h : HeurState) : (withH s h).vals = s.vals := rfl

private theorem state_heur_mk (a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13
    b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 hr) :
    (CorePlusState.mk a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13
      b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 hr).heur = hr := rfl

attribute [local bv_c0] List.length_set BitVec.toNat_zero bv64_one_toNat
  withH_heur withH_cur_level withH_vals state_heur_mk
  heur_heap_mk heur_pos_mk heur_score_mk heur_phases_mk heur_heap_len_mk
  bv32_setWidth64_toNat bv32_toNat_mod64 bv32_toNat_mod64'
  bv64_shl1_nat_toNat bv64_shl1_bv_toNat bv64_shl1_lit_toNat

private theorem withH_nested (s : CorePlusState) (h1 h2 : HeurState) :
    { { s with heur := h1 } with heur := h2 } = withH s h2 := rfl

private theorem withH_eq (s : CorePlusState) (h : HeurState) :
    { s with heur := h } = withH s h := rfl

/-- Single C0 step stripping `mdata` and discharging decidable width/divisor side conditions. -/
local macro "cp_step" : tactic => `(tactic|
  (try (change wp _ _ _ _ _); c0_step; repeat (any_goals (refine ⟨by decide, ?_⟩))))

/-- `c0_steps` extended to strip `mdata` and discharge decidable width/divisor side conditions. -/
local macro "cp_steps" : tactic => `(tactic|
  (try (change wp _ _ _ _ _); c0_steps; repeat (any_goals (refine ⟨by decide, ?_⟩; c0_steps))))

private theorem bv32_parent_lt {p : BitVec 32} (hp : 0 < p.toNat) :
    ((p - 1) >>> (1 : BitVec 32)).toNat < p.toNat := by
  have hp_lt := p.isLt
  have hsub : (p - 1).toNat = p.toNat - 1 := by
    rw [BitVec.toNat_sub]; change (2 ^ 32 - 1 + p.toNat) % 2 ^ 32 = p.toNat - 1; omega
  change ((p - 1) >>> 1).toNat < p.toNat
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, hsub]; omega

private theorem bv64_shl1_toNat {x : BitVec 64} (hx : x.toNat < 2 ^ 63) :
    (x <<< (1 : BitVec 64)).toNat = 2 * x.toNat := by
  change (x <<< 1).toNat = 2 * x.toNat
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega

private theorem bv64_shl1_add1_toNat {x : BitVec 64} (hx : x.toNat < 2 ^ 62) :
    ((x <<< (1 : BitVec 64)) + 1#64).toNat = 2 * x.toNat + 1 := by
  rw [BitVec.toNat_add, bv64_shl1_toNat (by omega)]
  change (2 * x.toNat + 1) % 2 ^ 64 = 2 * x.toNat + 1
  omega

private theorem bv64_shl1_or1_trunc32 {v : BitVec 64} (hv : 2 * v.toNat + 1 < 2 ^ 32) :
    ((v <<< (1 : BitVec 64)).setWidth 32 ||| 1#32).toNat = 2 * v.toNat + 1 := by
  have hsh : ((v <<< (1 : BitVec 64)).setWidth 32).toNat = 2 * v.toNat := by
    rw [BitVec.toNat_setWidth, bv64_shl1_toNat (by omega)]
    exact Nat.mod_eq_of_lt (by omega)
  have hor : (2 * v.toNat) ||| 1 = 2 * v.toNat + 1 := by
    apply Nat.eq_of_testBit_eq; intro i
    cases i with
    | zero => simp [Nat.testBit_zero]
    | succ k =>
      rw [Nat.testBit_or, Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_succ]
      have h1 : (1 / 2 : Nat) = 0 := rfl
      have hd1 : (2 * v.toNat + 1) / 2 = v.toNat := by omega
      have hd2 : (2 * v.toNat) / 2 = v.toNat := by omega
      rw [h1, hd1, hd2]; simp
  rw [BitVec.toNat_or, hsh]; change (2 * v.toNat) ||| 1 = 2 * v.toNat + 1; exact hor

private theorem HeurState.LengthsOk.same {c : CorePlusCfg} {h h' : HeurState}
    (hok : h.LengthsOk c)
    (h1 : h'.heap.length = h.heap.length := by rfl)
    (h2 : h'.pos.length = h.pos.length := by rfl)
    (h3 : h'.score.length = h.score.length := by rfl)
    (h4 : h'.phases.length = h.phases.length := by rfl)
    (h5 : h'.heap_len = h.heap_len := by rfl) : h'.LengthsOk c :=
  ⟨h1.trans hok.heap_len_arr, h2.trans hok.pos_len, h3.trans hok.score_len,
    h4.trans hok.phases_len, h5 ▸ hok.heap_len_le⟩

private theorem HeurState.LengthsOk.set_heap {c : CorePlusCfg} {h : HeurState}
    (hok : h.LengthsOk c) {i : Nat} {v : BitVec 32} :
    ({ h with heap := h.heap.set i v } : HeurState).LengthsOk c :=
  { hok with heap_len_arr := by simp [hok.heap_len_arr] }

private theorem HeurState.LengthsOk.set_pos {c : CorePlusCfg} {h : HeurState}
    (hok : h.LengthsOk c) {i : Nat} {v : BitVec 32} :
    ({ h with pos := h.pos.set i v } : HeurState).LengthsOk c :=
  { hok with pos_len := by simp [hok.pos_len] }

private theorem HeurState.LengthsOk.set_score {c : CorePlusCfg} {h : HeurState}
    (hok : h.LengthsOk c) {i : Nat} {v : BitVec 64} :
    ({ h with score := h.score.set i v } : HeurState).LengthsOk c :=
  { hok with score_len := by simp [hok.score_len] }

private theorem ofNat64_eq_zero_iff {n : Nat} (hn : n < 2 ^ 64) :
    BitVec.ofNat 64 n = 0#64 ↔ n = 0 := by
  constructor
  · intro h; have ht := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn] at ht; exact ht
  · rintro rfl; rfl

/-! ## 2. Group A: All 8 heuristic `Func.wp` proofs -/

theorem kissat_heap_sift_up_wp (Γ : Env) :
    ∀ args m Q X, corePlusHeapSiftUpSpec args m Q X →
      Func.wp Γ kissat_heap_sift_up_body args m Q X := by
  rintro ⟨h, v, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  have hmv := c.hmv; unfold dimacsBound at hmv
  have hok := hlen.heur_ok
  have hhl := hok.heap_len_arr; have hpl := hok.pos_len
  have hsl := hok.score_len; have hle := hok.heap_len_le
  change (CorePlusMem c (withH s s.heur) ⋆ R) m at hm
  unfold Func.wp kissat_heap_sift_up_body
  cp_steps
  · exact hQ _ _ hok hm
  · exact hQ _ _ hok hm
  · exact hQ _ _ hok hm
  · refine wp_loop_inv (ts := [i32])
      (fun (p, ()) ml => ∃ h' : HeurState, p.toNat < c.mv ∧ h'.LengthsOk c ∧
        (CorePlusMem c (withH s h') ⋆ R) ml)
      (fun (p, ()) _ => p.toNat) (fun L hL => ?_) (fun L (p, ()) ml ⟨h', hp, hok', hml⟩ hL => ?_)
    · cp_steps; exact hL (_, ()) m ⟨s.heur, by c0_bound, hok, hm⟩
    · have hhl' := hok'.heap_len_arr; have hpl' := hok'.pos_len; have hsl' := hok'.score_len
      cp_steps
      · have hpp_lt : ((p - 1) >>> (1 : BitVec 32)).toNat < p.toNat :=
          bv32_parent_lt (by c0_bound)
        refine wp_load_of (c0_load_arena_heap
          (by rw [bv32_setWidth64_toNat, withH_heur, hhl']; exact Nat.lt_trans hpp_lt hp) hml) ?_
        cp_steps
        · refine hQ _ m ?_ hm
          exact ⟨by simp [withH, hhl'], by simp [withH, hpl'], hok'.score_len, hok'.phases_len,
            hok'.heap_len_le⟩
        · refine hQ _ m ?_ hm
          exact ⟨by simp [withH, hhl'], by simp [withH, hpl'], hok'.score_len, hok'.phases_len,
            hok'.heap_len_le⟩
        · refine hL (_, ()) m hpp_lt ⟨_, Nat.lt_trans hpp_lt hp, ?_, hm⟩
          exact ⟨by simp [withH, hhl'], by simp [withH, hpl'], hok'.score_len, hok'.phases_len,
            hok'.heap_len_le⟩
      · refine hQ _ m ?_ hm
        exact ⟨by simp [withH, hhl'], by simp [withH, hpl'], hok'.score_len, hok'.phases_len,
          hok'.heap_len_le⟩

theorem kissat_heap_sift_down_wp (Γ : Env) :
    ∀ args m Q X, corePlusHeapSiftDownSpec args m Q X →
      Func.wp Γ kissat_heap_sift_down_body args m Q X := by
  rintro ⟨h, v, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  have hmv := c.hmv; unfold dimacsBound at hmv
  have hok := hlen.heur_ok
  have hhl := hok.heap_len_arr; have hpl := hok.pos_len
  have hsl := hok.score_len; have hle := hok.heap_len_le
  change (CorePlusMem c (withH s s.heur) ⋆ R) m at hm
  unfold Func.wp kissat_heap_sift_down_body
  cp_steps
  · exact hQ _ _ hok rfl rfl hm
  · exact hQ _ _ hok rfl rfl hm
  · exact hQ _ _ hok rfl rfl hm
  · refine wp_loop_inv (ts := [i32])
      (fun (p, ()) ml => ∃ h' : HeurState, p.toNat < s.heur.heap_len ∧ h'.LengthsOk c ∧
        h'.heap_len = s.heur.heap_len ∧ h'.rel_trigger = s.heur.rel_trigger ∧
        (CorePlusMem c (withH s h') ⋆ R) ml)
      (fun (p, ()) _ => s.heur.heap_len - p.toNat) (fun L hL => ?_)
      (fun L (p, ()) ml ⟨h', hp, hok', hlen_eq, hrel_eq, hml⟩ hL => ?_)
    · cp_steps; exact hL (_, ()) m ⟨s.heur, by c0_bound, hok, rfl, rfl, hm⟩
    · have hhl' := hok'.heap_len_arr; have hpl' := hok'.pos_len; have hsl' := hok'.score_len
      cp_step; cp_step
      all_goals try cases hc
      cp_step
      · apply hJ; cp_steps
        refine hQ _ m ?_ ?_ ?_ hm
        · exact ⟨by simp [withH, hhl'], by simp [withH, hpl'], hok'.score_len, hok'.phases_len,
            hok'.heap_len_le⟩
        · exact hlen_eq
        · exact hrel_eq
      cp_step; cp_step; cp_step; cp_step
      · apply hJ; cp_steps
        refine hQ _ m ?_ ?_ ?_ hm
        · exact ⟨by simp [withH, hhl'], by simp [withH, hpl'], hok'.score_len, hok'.phases_len,
            hok'.heap_len_le⟩
        · exact hlen_eq
        · exact hrel_eq
      cp_step
      refine wp_join_group (ts := [i64, i32, i64])
        (fun (cp, cv, _csc, ()) m1 =>
          p.toNat < cp.toNat ∧ cp.toNat < s.heur.heap_len ∧ cv.toNat < c.mv ∧
          (CorePlusMem c (withH s h') ⋆ R) m1) ?_ ?_
      · rintro _ ⟨cp, cv, csc, ⟨⟩⟩ m1 ⟨hgt, hcp_lt, hcv_lt, hm1⟩
        cp_steps
        · refine hQ _ m ?_ ?_ ?_ hm
          · exact ⟨by simp [withH, hhl'], by simp [withH, hpl'], hok'.score_len, hok'.phases_len,
              hok'.heap_len_le⟩
          · exact hlen_eq
          · exact hrel_eq
        · refine hL (_, ()) m (by c0_bound) ⟨_, by c0_bound, ?_, ?_, ?_, hm⟩
          · exact ⟨by simp [withH, hhl'], by simp [withH, hpl'], hok'.score_len, hok'.phases_len,
              hok'.heap_len_le⟩
          · exact hlen_eq
          · exact hrel_eq
      · intro Js hJs
        cp_steps
        · refine wp_load_of (c0_load_arena_score (by simp only [bv_c0] at *; omega) hml) ?_
          cp_steps
          refine hJs (_, _, _, ()) ml ⟨by c0_bound, by c0_bound, ?_, hml⟩
          simp only [bv_c0] at *; omega
        all_goals
          refine hJs (_, _, _, ()) ml ⟨by c0_bound, by c0_bound, ?_, hml⟩
          simp only [bv_c0] at *; omega

theorem kissat_heap_push_wp (Γ : Env)
    (hSiftUp : ∀ a m Q X, corePlusHeapSiftUpSpec a m Q X →
      Γ "kissat_heap_sift_up" [i64, i32] [] a m Q X) :
    ∀ args m Q X, corePlusHeapPushSpec args m Q X →
      Func.wp Γ kissat_heap_push_body args m Q X := by
  rintro ⟨h, v, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  have hmv := c.hmv; unfold dimacsBound at hmv
  have hok := hlen.heur_ok
  have hhl := hok.heap_len_arr; have hpl := hok.pos_len; have hle := hok.heap_len_le
  change (CorePlusMem c (withH s s.heur) ⋆ R) m at hm
  unfold Func.wp kissat_heap_push_body
  cp_steps
  · exact hQ _ _ hok hm
  · exact hQ _ _ hok hm
  · exact hQ _ _ hok hm
  · c0_call hSiftUp
    refine ⟨c, _, R, rfl, ?_, hm, fun heur' m' hok' hm' => hQ heur' m' hok' hm'⟩
    exact hlen.with_heur ⟨by simp [withH, hhl], by simp [withH, hpl], hok.score_len,
      hok.phases_len, by c0_bound⟩

theorem kissat_heap_pop_max_wp (Γ : Env)
    (hSiftDown : ∀ a m Q X, corePlusHeapSiftDownSpec a m Q X →
      Γ "kissat_heap_sift_down" [i64, i32] [] a m Q X) :
    ∀ args m Q X, corePlusHeapPopMaxSpec args m Q X →
      Func.wp Γ kissat_heap_pop_max_body args m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  have hmv := c.hmv; unfold dimacsBound at hmv
  have hok := hlen.heur_ok
  have hhl := hok.heap_len_arr; have hpl := hok.pos_len; have hle := hok.heap_len_le
  change (CorePlusMem c (withH s s.heur) ⋆ R) m at hm
  unfold Func.wp kissat_heap_pop_max_body
  cp_step; cp_step; cp_step
  · exact hQ 0xFFFFFFFF#64 _ _ (Or.inl rfl) hok
      (fun _ => by have h0 := (ofNat64_eq_zero_iff (by omega)).mp hc; omega) rfl hm
  cp_step; cp_step
  have hpos : 0 < s.heur.heap_len := by
    by_cases h0 : s.heur.heap_len = 0
    · exact absurd ((ofNat64_eq_zero_iff (by omega)).mpr h0) (by assumption)
    · omega
  cp_step; cp_step; cp_step; cp_step; cp_step; cp_step; cp_step
  refine wp_join_group (ts := [])
    (fun () m1 => ∃ h1 : HeurState, h1.LengthsOk c ∧ h1.heap_len = s.heur.heap_len - 1 ∧
      h1.rel_trigger = s.heur.rel_trigger ∧ (CorePlusMem c (withH s h1) ⋆ R) m1) ?_ ?_
  · rintro _ ⟨⟩ m1 ⟨h1, hok1, hlen1, hrel1, hm1⟩
    have hhl1 := hok1.heap_len_arr; have hpl1 := hok1.pos_len
    refine wp_join_group (ts := [])
      (fun () m2 => ∃ h2 : HeurState, h2.LengthsOk c ∧ h2.heap_len = s.heur.heap_len - 1 ∧
        h2.rel_trigger = s.heur.rel_trigger ∧ (CorePlusMem c (withH s h2) ⋆ R) m2) ?_ ?_
    · rintro _ ⟨⟩ m2 ⟨h2, hok2, hlen2, hrel2, hm2⟩
      cp_steps
      · exact hQ 0xFFFFFFFF#64 _ _ (Or.inl rfl) hok2 (fun _ => hlen2) hrel2 hm2
      · exact hQ _ _ _ (Or.inr (by c0_bound)) hok2 (fun _ => hlen2) hrel2 hm2
    · intro J2 hJ2
      cp_steps
      · c0_call hSiftDown
        refine ⟨c, _, R, rfl, hlen.with_heur hok1.set_heap.set_pos, hm,
          fun heur' m' hok' hlen' hrel' hm' => ?_⟩
        rw [withH_nested] at hm'
        cp_steps
        exact hJ2 () m' ⟨heur', hok', by rw [hlen']; exact hlen1,
          by rw [hrel']; exact hrel1, hm'⟩
      · exact hJ2 () m1 ⟨h1, hok1, hlen1, hrel1, hm1⟩
      · exact hJ2 () m1 ⟨h1, hok1, hlen1, hrel1, hm1⟩
  · intro J1 hJ1
    cp_steps
    all_goals
      refine hJ1 () m ⟨_, ?_, ?_, ?_, hm⟩
      · exact ⟨by simp [withH, hhl], by simp [withH, hpl], hok.score_len, hok.phases_len,
          by c0_bound⟩
      · c0_bound
      · rfl

theorem kissat_rescale_scores_wp (Γ : Env) :
    ∀ args m Q X, corePlusRescaleScoresSpec args m Q X →
      Func.wp Γ kissat_rescale_scores_body args m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  have hmv := c.hmv; unfold dimacsBound at hmv
  have hok := hlen.heur_ok
  change (CorePlusMem c (withH s s.heur) ⋆ R) m at hm
  unfold Func.wp kissat_rescale_scores_body
  cp_steps
  refine wp_loop_inv (ts := [i64])
    (fun (v, ()) ml => ∃ h' : HeurState, v.toNat ≤ c.mv ∧ h'.LengthsOk c ∧
      (CorePlusMem c (withH s h') ⋆ R) ml)
    (fun (v, ()) _ => c.mv - v.toNat) (fun J hJ => ?_)
    (fun J (v, ()) ml ⟨h', hvle, hok', hml⟩ hJ => ?_)
  · cp_steps; exact hJ _ _ ⟨s.heur, by simp, hok, hm⟩
  · have hsl' := hok'.score_len
    cp_steps
    · exact hJ _ _ (by c0_bound) ⟨_, by c0_bound, hok'.set_score, hm⟩
    · exact hQ _ _ hok'.same hm
    · exact hQ _ _ hok'.same hm

theorem kissat_bump_var_wp (Γ : Env)
    (hSiftUp : ∀ a m Q X, corePlusHeapSiftUpSpec a m Q X →
      Γ "kissat_heap_sift_up" [i64, i32] [] a m Q X)
    (hRescale : ∀ a m Q X, corePlusRescaleScoresSpec a m Q X →
      Γ "kissat_rescale_scores" [i64] [] a m Q X) :
    ∀ args m Q X, corePlusBumpVarSpec args m Q X →
      Func.wp Γ kissat_bump_var_body args m Q X := by
  rintro ⟨h, v, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  have hmv := c.hmv; unfold dimacsBound at hmv
  have hok := hlen.heur_ok; have hsl := hok.score_len
  change (CorePlusMem c (withH s s.heur) ⋆ R) m at hm
  unfold Func.wp kissat_bump_var_body
  cp_step; cp_step; cp_step
  · exact hQ _ _ hok hm
  cp_step; cp_step; cp_step
  refine wp_join_group (ts := [i64])
    (fun _ m0 => (CorePlusMem c (withH s s.heur) ⋆ R) m0) ?_ ?_
  · rintro _ ⟨nsc, ⟨⟩⟩ m0 hm0
    cp_steps
    c0_call hSiftUp
    refine ⟨c, _, R, rfl, hlen.with_heur hok.set_score, hm, fun heur1 m1 hok1 hm1 => ?_⟩
    rw [withH_nested] at hm1
    cp_steps
    · c0_call hRescale
      refine ⟨c, _, R, rfl, hlen.with_heur hok1, hm1, fun heur2 m2 hok2 hm2 => ?_⟩
      rw [withH_nested] at hm2; apply hJ; cp_steps; exact hQ heur2 m2 hok2 hm2
    · exact hQ heur1 m1 hok1 hm1
  · intro J0 hJ0; cp_steps
    all_goals exact hJ0 _ m hm

theorem kissat_bump_decay_wp (Γ : Env)
    (hRescale : ∀ a m Q X, corePlusRescaleScoresSpec a m Q X →
      Γ "kissat_rescale_scores" [i64] [] a m Q X) :
    ∀ args m Q X, corePlusBumpDecaySpec args m Q X →
      Func.wp Γ kissat_bump_decay_body args m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  have hok := hlen.heur_ok
  change (CorePlusMem c (withH s s.heur) ⋆ R) m at hm
  unfold Func.wp kissat_bump_decay_body
  cp_step; cp_step
  refine wp_join_group (ts := [i64])
    (fun _ m1 => (CorePlusMem c (withH s s.heur) ⋆ R) m1) ?_ ?_
  · rintro _ ⟨inc1, ⟨⟩⟩ m1 hm1
    refine wp_join_group (ts := [i64])
      (fun _ m2 => ∃ h2 : HeurState, h2.LengthsOk c ∧ (CorePlusMem c (withH s h2) ⋆ R) m2) ?_ ?_
    · rintro _ ⟨inc2, ⟨⟩⟩ m2 ⟨h2, hok2, hm2⟩
      cp_steps
      · c0_call hRescale
        refine ⟨c, _, R, rfl, hlen.with_heur hok2.same, hm, fun heur3 m3 hok3 hm3 => ?_⟩
        rw [withH_nested] at hm3; apply hJ; cp_steps; exact hQ heur3 m3 hok3 hm3
      · exact hQ _ _ hok2.same hm
    · intro J2 hJ2
      cp_steps
      · c0_call hRescale
        refine ⟨c, _, R, rfl, hlen.with_heur hok, hm1, fun heur2 m2 hok2 hm2 => ?_⟩
        rw [withH_nested] at hm2; cp_steps
        exact hJ2 (_, ()) m2 ⟨heur2, hok2, hm2⟩
      · exact hJ2 (inc1, ()) m1 ⟨s.heur, hok, hm1⟩
  · intro J1 hJ1; cp_steps
    all_goals exact hJ1 _ m hm

theorem kissat_tick_reluctant_wp (Γ : Env) :
    ∀ args m Q X, corePlusTickReluctantSpec args m Q X →
      Func.wp Γ kissat_tick_reluctant_body args m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  have hok := hlen.heur_ok
  change (CorePlusMem c (withH s s.heur) ⋆ R) m at hm
  unfold Func.wp kissat_tick_reluctant_body
  change wp _ _ _ _ _
  c0_step; c0_step; c0_step
  · exact hQ _ _ hok hm
  c0_step; c0_step
  · exact hQ _ _ hok hm
  -- Join 1: `if (h->rel_wait > 0) h->rel_wait -= 1`
  refine wp_join_group
    (fun () m1 => ∃ h1 : HeurState, h1.LengthsOk c ∧ (CorePlusMem c (withH s h1) ⋆ R) m1)
    ?_ ?_
  · rintro _ ⟨⟩ m1 ⟨h1, hok1, hm1⟩
    change wp _ _ _ _ _
    c0_step; c0_step; c0_step
    · exact hQ _ _ hok1 hm1
    c0_step; c0_step
    -- Join 2: `if (u == 0 || v == 0) { u = 1; v = 1; }`
    refine wp_join_group
      (fun (_uv : Tup Val [i64, i64]) m2 =>
        ∃ h2 : HeurState, h2.LengthsOk c ∧ (CorePlusMem c (withH s h2) ⋆ R) m2) ?_ ?_
    · rintro _ ⟨u2, v2, ⟨⟩⟩ m2 ⟨h2, hok2, hm2⟩
      -- Join 3: `if ((u & -u) == v) { u++; v = 1; } else { v <<= 1; }`
      refine wp_join_group
        (fun (_uv : Tup Val [i64, i64]) m3 =>
          ∃ h3 : HeurState, h3.LengthsOk c ∧ (CorePlusMem c (withH s h3) ⋆ R) m3) ?_ ?_
      · rintro _ ⟨u3, v3, ⟨⟩⟩ m3 ⟨h3, hok3, hm3⟩
        -- Join 4: `if (v == 0 || v > 2^30 || rel_period > 2^30) { u = 1; v = 1; }`
        refine wp_join_group
          (fun (_uv : Tup Val [i64, i64]) m4 =>
            ∃ h4 : HeurState, h4.LengthsOk c ∧ (CorePlusMem c (withH s h4) ⋆ R) m4) ?_ ?_
        · rintro _ ⟨u4, v4, ⟨⟩⟩ m4 ⟨h4, hok4, hm4⟩
          cp_steps
          all_goals exact hQ _ _ hok4.same hm
        · intro J4 hJ4; cp_steps
          all_goals exact hJ4 _ _ ⟨h3, hok3, hm3⟩
      · intro J3 hJ3; cp_steps
        all_goals exact hJ3 _ _ ⟨h2, hok2, hm2⟩
    · intro J2 hJ2; cp_steps
      all_goals exact hJ2 _ _ ⟨h1, hok1, hm1⟩
  · intro J1 hJ1; cp_steps
    all_goals exact hJ1 () _ ⟨_, hok.same, hm⟩

/-! ## 4. Decision procedure (`kissat_decide_wp`) -/

/-- Helper for `decide_assign_preserves_core`: `vals` true/false iff trail membership after
pushing a fresh decision literal `lit`. -/
private theorem decide_assign_vals_iff {c : CorePlusCfg} {F0 : CNF Nat}
    {s : CorePlusState} (hinv : CorePlusCoreInv c F0 s) {lit : BitVec 32}
    {vals' : List (BitVec 8)} {trl' : List (BitVec 32)}
    (hnot_var : ∀ i < s.trail_end, (s.trl[i]?.getD 0#32).toNat / 2 ≠ lit.toNat / 2)
    (htrl_get : ∀ i < s.trail_end + 1,
      (trl'[i]?.getD 0#32).toNat =
        if i = s.trail_end then lit.toNat else (s.trl[i]?.getD 0#32).toNat)
    (hvals_get : ∀ l < 2 * c.mv,
      vals'[l]?.getD 0#8 =
        if l = lit.toNat ^^^ 1 then 0xFF#8
        else if l = lit.toNat then 1#8 else s.vals[l]?.getD 0#8) :
    (∀ l < 2 * c.mv, vals'[l]?.getD 0#8 = 1#8 ↔
        ∃ i < s.trail_end + 1, (trl'[i]?.getD 0#32).toNat = l) ∧
      (∀ l < 2 * c.mv, vals'[l]?.getD 0#8 = 0xFF#8 ↔
        ∃ i < s.trail_end + 1, (trl'[i]?.getD 0#32).toNat = l ^^^ 1) := by
  have hne_lit : lit.toNat ^^^ 1 ≠ lit.toNat := litNeg_ne_self lit.toNat
  refine ⟨fun l hl => ?_, fun l hl => ?_⟩
  · rw [hvals_get l hl]
    constructor
    · intro h1
      by_cases hneg : l = lit.toNat ^^^ 1
      · simp [hneg] at h1
      · simp only [hneg, ↓reduceIte] at h1
        by_cases hpos : l = lit.toNat
        · exact ⟨s.trail_end, by omega, by rw [htrl_get _ (by omega)]; simp [hpos]⟩
        · simp only [hpos, ↓reduceIte] at h1
          obtain ⟨i, hi, heq⟩ := (hinv.vals_true_iff l hl).mp h1
          exact ⟨i, by omega,
            by rw [htrl_get i (by omega)]; simp [show i ≠ s.trail_end by omega, heq]⟩
    · rintro ⟨i, hi, heq⟩
      rw [htrl_get i hi] at heq
      by_cases hie : i = s.trail_end
      · simp only [hie, ↓reduceIte] at heq; subst heq; simp [Ne.symm hne_lit]
      · simp only [hie, ↓reduceIte] at heq
        have hlv : l / 2 ≠ lit.toNat / 2 := by rw [← heq]; exact hnot_var i (by omega)
        have h1 : l ≠ lit.toNat ^^^ 1 := fun h => hlv (by rw [h]; exact litVar_litNeg _)
        have h2 : l ≠ lit.toNat := fun h => hlv (by rw [h])
        simp only [h1, h2, ↓reduceIte]; exact (hinv.vals_true_iff l hl).mpr ⟨i, by omega, heq⟩
  · rw [hvals_get l hl]
    constructor
    · intro h1
      by_cases hneg : l = lit.toNat ^^^ 1
      · refine ⟨s.trail_end, by omega, ?_⟩
        rw [htrl_get _ (by omega)]; simp only [↓reduceIte, hneg]; exact (litNeg_litNeg _).symm
      · simp only [hneg, ↓reduceIte] at h1
        by_cases hpos : l = lit.toNat
        · simp [hpos] at h1
        · simp only [hpos, ↓reduceIte] at h1
          obtain ⟨i, hi, heq⟩ := (hinv.vals_false_iff l hl).mp h1
          exact ⟨i, by omega,
            by rw [htrl_get i (by omega)]; simp [show i ≠ s.trail_end by omega, heq]⟩
    · rintro ⟨i, hi, heq⟩
      rw [htrl_get i hi] at heq
      by_cases hie : i = s.trail_end
      · simp only [hie, ↓reduceIte] at heq
        have hl_eq : l = lit.toNat ^^^ 1 := by
          have h := congrArg litNeg heq; have h1 : litNeg (l ^^^ 1) = l := litNeg_litNeg l
          rw [h1] at h; exact h.symm
        simp [hl_eq]
      · simp only [hie, ↓reduceIte] at heq
        have hlv : l / 2 ≠ lit.toNat / 2 := by
          have h := hnot_var i (by omega); rw [heq] at h
          have h1 : (l ^^^ 1) / 2 = l / 2 := litVar_litNeg l; rwa [h1] at h
        have h1 : l ≠ lit.toNat ^^^ 1 := fun h => hlv (by rw [h]; exact litVar_litNeg _)
        have h2 : l ≠ lit.toNat := fun h => hlv (by rw [h])
        simp only [h1, h2, ↓reduceIte]; exact (hinv.vals_false_iff l hl).mpr ⟨i, by omega, heq⟩

/-- Pushing a fresh decision literal at `cur_level + 1` preserves `CorePlusCoreInv`. -/
private theorem decide_assign_preserves_core {c : CorePlusCfg} {F0 : CNF Nat}
    {s : CorePlusState} (hinv : CorePlusCoreInv c F0 s) {lit : BitVec 32}
    {phases' : List (BitVec 8)} (hlit : lit.toNat < 2 * c.mv) (hph : phases'.length = c.mv)
    (hun : s.vals[lit.toNat]?.getD 0#8 = 0#8) :
    let v := lit.toNat / 2
    let s' : CorePlusState :=
      { s with
        cur_level := s.cur_level + 1
        vals := (s.vals.set lit.toNat 1#8).set (lit.toNat ^^^ 1) 0xFF#8
        lvl := s.lvl.set v (BitVec.ofNat 32 (s.cur_level + 1))
        rsns := s.rsns.set v 0xFFFFFFFF#32
        trl := s.trl.set s.trail_end lit
        trail_end := s.trail_end + 1
        heur := { s.heur with phases := phases' } }
    CorePlusCoreInv c F0 s' := by
  intro v s'
  have hmv := c.hmv; unfold dimacsBound at hmv
  have hte_lt : s.trail_end < c.mv := hinv.trail_end_lt_of_unassigned hlit hun
  have hnot_var : ∀ i < s.trail_end, (s.trl[i]?.getD 0#32).toNat / 2 ≠ v :=
    (hinv.vals_zero_iff hlit).mp hun
  have hnlit_lt : (lit.toNat ^^^ 1) < 2 * c.mv := litNeg_lt_two_mul hlit
  have hlen := hinv.lengths; have hcur_le := hinv.cur_level_le
  have hcur1_lt : s.cur_level + 1 < 2 ^ 32 := by omega
  have hs'_te : s'.trail_end = s.trail_end + 1 := rfl
  have hs'_cl : s'.cur_level = s.cur_level + 1 := rfl
  have htrl_get : ∀ i < s.trail_end + 1,
      (s'.trl[i]?.getD 0#32).toNat =
        if i = s.trail_end then lit.toNat else (s.trl[i]?.getD 0#32).toNat := fun i hi => by
    by_cases he : i = s.trail_end
    · subst he; simp [s', List.getElem?_set_self (by rw [hlen.trl_len]; omega)]
    · simp [s', he, List.getElem?_set_ne (Ne.symm he)]
  have hlvl_get : ∀ w < c.mv,
      (s'.lvl[w]?.getD 0#32).toNat =
        if w = v then s.cur_level + 1 else (s.lvl[w]?.getD 0#32).toNat := fun w hw => by
    by_cases he : w = v
    · subst he
      simp [s', List.getElem?_set_self (by rw [hlen.lvl_len]; omega), bv32_ofNat_toNat hcur1_lt]
    · simp [s', he, List.getElem?_set_ne (Ne.symm he)]
  have hvals_get : ∀ l < 2 * c.mv,
      s'.vals[l]?.getD 0#8 =
        if l = lit.toNat ^^^ 1 then 0xFF#8
        else if l = lit.toNat then 1#8 else s.vals[l]?.getD 0#8 := fun l hl => by
    by_cases h1 : l = lit.toNat ^^^ 1
    · subst h1; dsimp only [s']; simp only [↓reduceIte]
      rw [List.getElem?_set_self (by simp [hlen.vals_len]; exact hnlit_lt)]; rfl
    · dsimp only [s']; simp only [h1, ↓reduceIte]
      rw [List.getElem?_set_ne (Ne.symm h1)]
      by_cases h2 : l = lit.toNat
      · subst h2; simp only [↓reduceIte]
        rw [List.getElem?_set_self (by rw [hlen.vals_len]; exact hlit)]; rfl
      · simp only [h2, ↓reduceIte]; rw [List.getElem?_set_ne (Ne.symm h2)]
  have hlen' : s'.LengthsOk c :=
    { hlen with
      vals_len := by simp [s', hlen.vals_len]
      lvl_len := by simp [s', hlen.lvl_len]
      rsns_len := by simp [s', hlen.rsns_len]
      trl_len := by simp [s', hlen.trl_len]
      trail_end_le := by rw [hs'_te]; omega
      propagated_le := by dsimp [s']; have := hlen.propagated_le; omega
      cur_level_lt := hcur1_lt
      heur_ok := { hlen.heur_ok with phases_len := hph } }
  obtain ⟨hv_true, hv_false⟩ := decide_assign_vals_iff hinv hnot_var htrl_get hvals_get
  refine ⟨hlen', ⟨hinv.clauses.bounds, hinv.clauses.disjoint, hinv.clauses.lits_lt,
      hinv.clauses.entails⟩, by rw [hs'_cl, hs'_te]; omega, ?_, ?_, ?_, hv_true, hv_false,
      ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi; rw [hs'_te] at hi; rw [htrl_get i hi]; split
    · exact hlit
    · exact hinv.trail_lits_lt i (by omega)
  · intro i j hi hj hveq
    rw [hs'_te] at hi hj; rw [htrl_get i hi, htrl_get j hj] at hveq
    split at hveq <;> split at hveq
    · omega
    · exact absurd hveq.symm (hnot_var j (by omega))
    · exact absurd hveq (hnot_var i (by omega))
    · exact hinv.trail_vars_nodup i j (by omega) (by omega) hveq
  · intro l hl; rw [hvals_get l hl]
    split; · exact Or.inr (Or.inr rfl)
    split; · exact Or.inr (Or.inl rfl)
    exact hinv.vals_domain l hl
  · intro i hi; rw [hs'_te] at hi; rw [hs'_cl, htrl_get i hi]
    by_cases hie : i = s.trail_end
    · simp only [hie, ↓reduceIte]; rw [hlvl_get v (by omega)]; simp
    · simp only [hie, ↓reduceIte]
      have hilt : i < s.trail_end := by omega
      rw [hlvl_get _ (by have := hinv.trail_lits_lt i hilt; omega)]
      simp only [hnot_var i hilt, ↓reduceIte]; have := hinv.lvl_le i hilt; omega
  · intro i j hij hj; rw [hs'_te] at hj; rw [htrl_get i (by omega), htrl_get j hj]
    by_cases hje : j = s.trail_end
    · simp only [hje, ↓reduceIte]; rw [hlvl_get v (by omega)]; simp only [↓reduceIte]
      by_cases hie : i = s.trail_end
      · simp only [hie, ↓reduceIte]; rw [hlvl_get v (by omega)]; simp
      · simp only [hie, ↓reduceIte]
        have hilt : i < s.trail_end := by omega
        rw [hlvl_get _ (by have := hinv.trail_lits_lt i hilt; omega)]
        simp only [hnot_var i hilt, ↓reduceIte]; have := hinv.lvl_le i hilt; omega
    · have hjlt : j < s.trail_end := by omega
      have hilt : i < s.trail_end := by omega
      simp only [show i ≠ s.trail_end by omega, hje, ↓reduceIte]
      rw [hlvl_get _ (by have := hinv.trail_lits_lt i hilt; omega),
        hlvl_get _ (by have := hinv.trail_lits_lt j hjlt; omega)]
      simp only [hnot_var i hilt, hnot_var j hjlt, ↓reduceIte]
      exact hinv.trail_mono i j hij hjlt
  · intro L hL1 hLle; rw [hs'_cl] at hLle; rw [hs'_te]
    by_cases hLeq : L = s.cur_level + 1
    · subst hLeq
      refine ⟨s.trail_end, by omega, ?_⟩
      rw [htrl_get _ (by omega)]; simp only [↓reduceIte]; rw [hlvl_get v (by omega)]; simp
    · obtain ⟨i, hi, hli⟩ := hinv.levels_inhabited L hL1 (by omega)
      refine ⟨i, by omega, ?_⟩
      rw [htrl_get i (by omega)]; simp only [show i ≠ s.trail_end by omega, ↓reduceIte]
      rw [hlvl_get _ (by have := hinv.trail_lits_lt i hi; omega)]
      simp [hnot_var i hi, hli]
  · intro i hi hli; rw [hs'_te] at hi; rw [htrl_get i hi] at hli ⊢
    by_cases hie : i = s.trail_end
    · simp only [hie, ↓reduceIte] at hli; rw [hlvl_get v (by omega)] at hli; simp at hli
    · simp only [hie, ↓reduceIte] at hli ⊢
      have hilt : i < s.trail_end := by omega
      rw [hlvl_get _ (by have := hinv.trail_lits_lt i hilt; omega)] at hli
      simp only [hnot_var i hilt, ↓reduceIte] at hli
      exact hinv.level0_sound i hilt hli
  · intro idx hidx; rw [hs'_te] at hidx; dsimp only; rw [htrl_get idx hidx]
    by_cases hie : idx = s.trail_end
    · simp only [hie, ↓reduceIte]
      have hr : s'.rsns[v]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 := by
        dsimp only [s']; rw [List.getElem?_set_self (by rw [hlen.rsns_len]; omega)]; rfl
      rw [hr]; intro hne; exact absurd rfl hne
    · simp only [hie, ↓reduceIte]
      have hilt : idx < s.trail_end := by omega
      have hnv : (s.trl[idx]?.getD 0#32).toNat / 2 ≠ v := hnot_var idx hilt
      have hr : s'.rsns[(s.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 =
          s.rsns[(s.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 := by
        simp [s', List.getElem?_set_ne (Ne.symm hnv)]
      rw [hr]; intro hne
      obtain ⟨hrc, hall⟩ := hinv.reason_inv idx hilt hne
      refine ⟨hrc, fun q hq => ?_⟩
      have hq' : q ∈ clauseLits s
          (s.rsns[(s.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat := by
        simpa [clauseLits, clauseOff, clauseSize, s'] using hq
      exact (hall q hq').elim Or.inl fun ⟨k, hk, hkeq⟩ => Or.inr ⟨k, hk, by
        rw [htrl_get k (by omega)]; simp [show k ≠ s.trail_end by omega, hkeq]⟩

private theorem i8_sext32_eq0_iff {b : BitVec 8}
    (hdom : b = 0#8 ∨ b = 1#8 ∨ b = 0xFF#8) :
    (b.signExtend 32 = 0#32) ↔ b = 0#8 := by
  rcases hdom with rfl | rfl | rfl <;> decide

/-- Post-loop decision step once an unassigned variable `ch < mv` has been selected. -/
private theorem decide_commit_var {Γ : Env} {Q : Post [i64]} {X : XPost}
    {c : CorePlusCfg} {F0 : CNF Nat} {s : CorePlusState} {h2 : HeurState} {R : Mem 64 → Prop}
    {ch : BitVec 64}
    (hAssign : ∀ a m Q X, corePlusAssignSpec a m Q X →
      Γ "kissat_assign" [i64, i32, i32] [] a m Q X)
    (hinv : CorePlusInv c F0 s) (hok2 : h2.LengthsOk c)
    (hrel2 : h2.rel_trigger = s.heur.rel_trigger)
    (hch_lt : ch.toNat < c.mv) (hch_un : s.vals[2 * ch.toNat]?.getD 0#8 = 0#8)
    (hQ : ∀ r vals' lvl' rsns' trl' te' cl' heur' m',
      let s' : CorePlusState := { s with
        vals := vals', lvl := lvl', rsns := rsns', trl := trl',
        trail_end := te', cur_level := cl', heur := heur' }
      CorePlusInv c F0 s' → (r = 0#64 ∨ r = 1#64) →
      heur'.rel_trigger = s.heur.rel_trigger →
      (r = 0#64 → vals' = s.vals ∧ lvl' = s.lvl ∧ rsns' = s.rsns ∧ trl' = s.trl ∧
        te' = s.trail_end ∧ cl' = s.cur_level ∧
        ∀ v < c.mv, s.vals[2 * v]?.getD 0#8 ≠ 0#8) →
      ((∀ v < c.mv, s.vals[2 * v]?.getD 0#8 ≠ 0#8) →
        r = 0#64 ∧ vals' = s.vals ∧ lvl' = s.lvl ∧ rsns' = s.rsns ∧ trl' = s.trl ∧
        te' = s.trail_end ∧ cl' = s.cur_level) →
      (CorePlusMem c s' ⋆ R) m' → Q (r, ()) m')
    {lit : BitVec 32} (hlit_eq : lit.toNat = 2 * ch.toNat ∨ lit.toNat = 2 * ch.toNat + 1)
    {m3 : Mem 64}
    (hm3 : (CorePlusMem c (withH { s with cur_level := s.cur_level + 1 } h2) ⋆ R) m3) :
    wp Γ Q X (Expr.call (as := [i64, i32, i32]) (bs := []) "kissat_assign"
      (Arg.var c.hdr, Arg.var lit, Arg.imm 0xFFFFFFFF#32, ())
      fun _ => Expr.ret (Arg.imm 1#64, ())) m3 := by
  have hmv := c.hmv; unfold dimacsBound at hmv
  have hcore := hinv.core; have hlen := hcore.lengths
  have hte_lt : s.trail_end < c.mv := hcore.trail_end_lt_of_unassigned (by omega) hch_un
  have hcl_le := hcore.cur_level_le
  have hcl_lt : s.cur_level + 1 < 2 ^ 32 := by omega
  have hlit_lt : lit.toNat < 2 * c.mv := by omega
  have hlit_un : s.vals[lit.toNat]?.getD 0#8 = 0#8 := by
    rw [hcore.vals_zero_iff hlit_lt]
    have hz := (hcore.vals_zero_iff (by omega : 2 * ch.toNat < 2 * c.mv)).mp hch_un
    intro i hi; have := hz i hi; omega
  c0_call hAssign
  refine ⟨c, { s with cur_level := s.cur_level + 1, heur := h2 }, R, rfl,
    { hlen with cur_level_lt := hcl_lt, heur_ok := hok2 }, hm3, ?_⟩
  have hnot_guard : ¬ (c.mv ≤ lit.toNat / 2 ∨ c.mv ≤ s.trail_end) := by omega
  simp only [hnot_guard, ↓reduceIte]
  intro ph' m4 hph' _ hm4
  cp_steps
  have hcore' := decide_assign_preserves_core (hcore.with_heur hok2) hlit_lt hph' hlit_un
  exact hQ 1#64 _ _ _ _ _ _ _ m4 ⟨hcore', hinv.marks⟩ (Or.inr rfl) hrel2
    (fun h => by cases h) (fun hall => absurd hch_un (hall ch.toNat hch_lt)) hm4

theorem kissat_decide_wp (Γ : Env)
    (hPopMax : ∀ a m Q X, corePlusHeapPopMaxSpec a m Q X →
      Γ "kissat_heap_pop_max" [i64] [i64] a m Q X)
    (hAssign : ∀ a m Q X, corePlusAssignSpec a m Q X →
      Γ "kissat_assign" [i64, i32, i32] [] a m Q X) :
    ∀ args m Q X, corePlusDecideSpec args m Q X →
      Func.wp Γ kissat_decide_body args m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hinv, hm, hQ⟩
  have hmv := c.hmv; unfold dimacsBound at hmv
  have hcore := hinv.core; have hlen := hcore.lengths; have hvl := hlen.vals_len
  change (CorePlusMem c (withH s s.heur) ⋆ R) m at hm
  unfold Func.wp kissat_decide_body
  change wp _ _ _ _ _
  -- Step past the 4 header loads to the outer `break` group of Loop 1.
  c0_step; c0_step; c0_step; c0_step; c0_step
  -- Use `wp_join_group` on Loop 1's break continuation `J1(ch)` so Loop 1 + Loop 2 stay linear.
  refine wp_join_group (ts := [i64])
    (fun (ch, ()) m1 => ∃ h1 : HeurState, h1.LengthsOk c ∧
      h1.rel_trigger = s.heur.rel_trigger ∧
      (ch = 0xFFFFFFFFFFFFFFFF#64 ∨
        (ch.toNat < c.mv ∧ s.vals[2 * ch.toNat]?.getD 0#8 = 0#8)) ∧
      (CorePlusMem c (withH s h1) ⋆ R) m1) ?_ ?_
  · rintro _ ⟨ch1, ⟨⟩⟩ m1 ⟨h1, hok1, hrel1, hch1, hm1⟩
    -- Join after optional scan loop (`if (chosen == ~0) { scan 0..mv }`).
    refine wp_join_group (ts := [i64])
      (fun (ch2, ()) m2 => ∃ h2 : HeurState, h2.LengthsOk c ∧
        h2.rel_trigger = s.heur.rel_trigger ∧
        ((ch2 = 0xFFFFFFFFFFFFFFFF#64 ∧ ∀ w < c.mv, s.vals[2 * w]?.getD 0#8 ≠ 0#8) ∨
          (ch2.toNat < c.mv ∧ s.vals[2 * ch2.toNat]?.getD 0#8 = 0#8)) ∧
        (CorePlusMem c (withH s h2) ⋆ R) m2) ?_ ?_
    · rintro _ ⟨ch2, ⟨⟩⟩ m2 ⟨h2, hok2, hrel2, hch2, hm2⟩
      have hph2 := hok2.phases_len
      change wp _ _ _ _ _
      c0_step; c0_step
      · rcases hch2 with ⟨_, hall⟩ | ⟨hlt, _⟩
        · exact hQ 0#64 s.vals s.lvl s.rsns s.trl s.trail_end s.cur_level h2 m2
            (hinv.with_heur hok2) (Or.inl rfl) hrel2
            (fun _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, hall⟩)
            (fun _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩) hm2
        · have hmax : ch2.toNat = 2 ^ 64 - 1 := by
            have := congrArg BitVec.toNat hc; simpa using this
          omega
      · rcases hch2 with ⟨heq, _⟩ | ⟨hch_lt, hch_un⟩
        · exact absurd heq hc
        have hte_lt : s.trail_end < c.mv :=
          hcore.trail_end_lt_of_unassigned (by omega) hch_un
        have hcl_le := hcore.cur_level_le
        have hcl1 : (BitVec.ofNat 64 (withH s h2).cur_level + (1 : BitVec 64)).toNat =
            s.cur_level + 1 := by c0_bound
        cp_steps
        all_goals
          rw [hcl1] at hm
          refine decide_commit_var hAssign hinv hok2 hrel2 hch_lt hch_un hQ ?_ hm
          first
            | (right; exact bv64_shl1_or1_trunc32 (by omega))
            | (left; rw [BitVec.toNat_setWidth]; c0_bound)
    · intro J2 hJ2
      cp_steps
      · -- Scan loop `v = 0 .. mv` (outer break already unrolled by `cp_steps`!)
        refine wp_loop_inv (ts := [i64])
          (fun (v, ()) ml => v.toNat ≤ c.mv ∧ (∀ w < v.toNat, s.vals[2 * w]?.getD 0#8 ≠ 0#8) ∧
            (CorePlusMem c (withH s h1) ⋆ R) ml)
          (fun (v, ()) _ => c.mv - v.toNat) (fun L2 hL2 => ?_)
          (fun L2 (v, ()) ml ⟨hvle, hall, hml⟩ hL2 => ?_)
        · cp_steps; exact hL2 (0#64, ()) m1 ⟨by simp, by simp, hm1⟩
        · cp_steps
          · have h2v : (v <<< (1 : BitVec 64)).toNat = 2 * v.toNat :=
              bv64_shl1_toNat (by c0_bound)
            have hget : s.vals[2 * v.toNat]?.getD 0#8 = 0#8 := by
              have hdom := hcore.vals_domain (2 * v.toNat) (by c0_bound)
              rw [List.getElem?_eq_getElem (by c0_bound), Option.getD_some] at hdom ⊢
              have h1' : (s.vals[(v <<< (1 : BitVec 64)).toNat]'(by c0_bound)).signExtend 32 =
                  0#32 := hc
              have hdom' : s.vals[(v <<< (1 : BitVec 64)).toNat]'(by c0_bound) = 0#8 ∨
                  s.vals[(v <<< (1 : BitVec 64)).toNat]'(by c0_bound) = 1#8 ∨
                  s.vals[(v <<< (1 : BitVec 64)).toNat]'(by c0_bound) = 0xFF#8 := by
                simp only [h2v]; exact hdom
              have h0 := (i8_sext32_eq0_iff hdom').mp h1'
              simp only [h2v] at h0; exact h0
            exact hJ2 (v, ()) ml ⟨h1, hok1, hrel1, Or.inr ⟨by c0_bound, hget⟩, hml⟩
          · refine hL2 (_, ()) ml (by c0_bound) ⟨by c0_bound, fun w hw => ?_, hml⟩
            rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ (by c0_bound : w < v.toNat + 1)) with
              hlt | rfl
            · exact hall w hlt
            · intro h0
              have h2v : (v <<< (1 : BitVec 64)).toNat = 2 * v.toNat :=
                bv64_shl1_toNat (by c0_bound)
              rw [List.getElem?_eq_getElem (by c0_bound), Option.getD_some] at h0
              have h1' : (s.vals[(v <<< (1 : BitVec 64)).toNat]'(by c0_bound)).signExtend 32 =
                  0#32 := by
                have h0' : s.vals[(v <<< (1 : BitVec 64)).toNat]'(by c0_bound) = 0#8 := by
                  simp only [h2v]; exact h0
                rw [h0']; rfl
              exact hc h1'
          · exact hJ2 (ch1, ()) ml
              ⟨h1, hok1, hrel1, Or.inl ⟨by assumption, fun w hw => hall w (by c0_bound)⟩, hml⟩
      · rcases hch1 with heq | hfound
        · exact absurd heq hc
        · exact hJ2 (ch1, ()) m1 ⟨h1, hok1, hrel1, Or.inr hfound, hm1⟩
  · intro J1 hJ1
    -- Loop 1 (`while (h->heap_len > 0 && h->heap_len <= mv)`), variant `h1.heap_len`
    refine wp_loop_group (ts := [])
      (fun n () ml => ∃ h1 : HeurState, n = h1.heap_len ∧ h1.LengthsOk c ∧
        h1.rel_trigger = s.heur.rel_trigger ∧ (CorePlusMem c (withH s h1) ⋆ R) ml) ?_ ?_
    · rintro L1 n ⟨⟩ ml ih1 ⟨h1, rfl, hok1, hrel1, hml⟩
      have hhl1 := hok1.heap_len_arr; have hle1 := hok1.heap_len_le
      cp_steps
      · exact hJ1 (0xFFFFFFFFFFFFFFFF#64, ()) ml ⟨h1, hok1, hrel1, Or.inl rfl, hml⟩
      · have htop_lt : (h1.heap[0]'(by c0_bound)).toNat < c.mv := by c0_bound
        have ht64 : ((h1.heap[0]'(by c0_bound)).setWidth 64).toNat =
            (h1.heap[0]'(by c0_bound)).toNat := by
          rw [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by omega)
        have h2t : ((h1.heap[0]'(by c0_bound)).setWidth 64 <<< (1 : BitVec 64)).toNat =
            2 * (h1.heap[0]'(by c0_bound)).toNat := by
          have := bv64_shl1_toNat (x := (h1.heap[0]'(by c0_bound)).setWidth 64) (by omega)
          rwa [ht64] at this
        have hget : s.vals[2 * (h1.heap[0]'(by c0_bound)).toNat]?.getD 0#8 = 0#8 := by
          have hdom := hcore.vals_domain (2 * (h1.heap[0]'(by c0_bound)).toNat) (by omega)
          rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at hdom ⊢
          have h1' :
              (s.vals[((h1.heap[0]'(by c0_bound)).setWidth 64 <<<
                (1 : BitVec 64)).toNat]'(by c0_bound)).signExtend 32 = 0#32 := hc
          have hdom' :
              s.vals[((h1.heap[0]'(by c0_bound)).setWidth 64 <<<
                (1 : BitVec 64)).toNat]'(by c0_bound) = 0#8 ∨
              s.vals[((h1.heap[0]'(by c0_bound)).setWidth 64 <<<
                (1 : BitVec 64)).toNat]'(by c0_bound) = 1#8 ∨
              s.vals[((h1.heap[0]'(by c0_bound)).setWidth 64 <<<
                (1 : BitVec 64)).toNat]'(by c0_bound) = 0xFF#8 := by
            simp only [h2t]; exact hdom
          have h0 := (i8_sext32_eq0_iff hdom').mp h1'
          simp only [h2t] at h0; exact h0
        have hget' : s.vals[2 * ((h1.heap[0]'(by c0_bound)).setWidth 64).toNat]?.getD 0#8 =
            0#8 := by rwa [ht64]
        exact hJ1 (_, ()) ml ⟨h1, hok1, hrel1, Or.inr ⟨by c0_bound, hget'⟩, hml⟩
      · c0_call hPopMax
        refine ⟨c, _, R, rfl, hlen.with_heur hok1, hml, fun _ h2 m2 _ hok2 hdec hrel2 hm2 => ?_⟩
        rw [withH_nested] at hm2
        cp_steps
        exact ih1 h2.heap_len () m2 (by
          have hd : h2.heap_len = h1.heap_len - 1 := hdec ⟨by c0_bound, hle1⟩
          omega)
          ⟨h2, rfl, hok2, by rw [hrel2]; exact hrel1, hm2⟩
      · exact hJ1 (0xFFFFFFFFFFFFFFFF#64, ()) ml ⟨h1, hok1, hrel1, Or.inl rfl, hml⟩
    · intro L1 hL1; cp_steps
      exact hL1 s.heur.heap_len () m ⟨s.heur, rfl, hlen.heur_ok, rfl, hm⟩

end LeanQbe.T.Examples.Kissat.CorePlus
