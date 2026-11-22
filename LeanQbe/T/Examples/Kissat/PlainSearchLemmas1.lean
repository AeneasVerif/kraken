module

public import LeanQbe.T.Examples.Kissat.PlainSpec

/-!
# Kissat `D-Plain` Search, Mode, Restart, and Rephase `Func.wp` Proofs — Part 1 (`Stage 3`)

Proves parametric `(Γ : Env)` `Func.wp` contracts for the Stage-3 search/control functions
in `LeanQbe/T/Examples/Kissat/Plain.lean` matching `plainSpecTable`:
1. `plain_restart_due_wp` (`plainRestartDueSpec`)
2. `plain_rephase_wp` (`plainRephaseSpec`)
3. `plain_switch_mode_wp` (`plainSwitchModeSpec`)
4. `plain_decide_wp` (`plainDecideSpec`)

`plain_lucky_scan_wp` and `plain_lucky_wp` live in `PlainSearchLemmas.lean`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Plain

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open Kraken.Bedrock2.Test

/-! ## 1. Scoped tactics & invariant/bit-vector helpers -/

namespace PlainTopTactics

theorem bv64_shl1_toNat {x : BitVec 64} (hx : x.toNat < 2 ^ 63) :
    (x <<< 1).toNat = 2 * x.toNat := by
  bv_omega

theorem bv64_shr1_toNat (x : BitVec 64) : (x >>> 1).toNat = x.toNat / 2 := by
  bv_omega

theorem bv64_shr8_ne_zero {x : BitVec 64} (hx : 256 < x.toNat) : x >>> 8 ≠ 0#64 := by
  bv_omega

theorem bv64_ofNat_eq_zero_iff {n : Nat} (hn : n < 2 ^ 64) :
    BitVec.ofNat 64 n = 0#64 ↔ n = 0 := by
  constructor
  · intro h
    have ht := congrArg BitVec.toNat h
    simpa [bv64_ofNat_toNat hn] using ht
  · rintro rfl; rfl

theorem bv64_ofNat_ne_zero_iff {n : Nat} (hn : n < 2 ^ 64) :
    BitVec.ofNat 64 n ≠ 0#64 ↔ n ≠ 0 :=
  not_congr (bv64_ofNat_eq_zero_iff hn)

theorem bv32_lit_even_toNat {v : BitVec 64} (hv : v.toNat < 2 ^ 30) :
    ((v <<< 1).setWidth 32).toNat = 2 * v.toNat := by
  bv_omega

theorem bv32_lit_odd_toNat {v : BitVec 64} (hv : v.toNat < 2 ^ 30) :
    (((v <<< 1).setWidth 32) ||| 1).toNat = 2 * v.toNat + 1 := by
  have he : ((v <<< 1).setWidth 32).toNat = 2 * v.toNat := bv32_lit_even_toNat hv
  rw [BitVec.toNat_or, he, show (1 : BitVec 32).toNat = 1 from rfl]
  change (2 * v.toNat) ||| 1 = 2 * v.toNat + 1
  apply Nat.eq_of_testBit_eq; intro i
  cases i with
  | zero => simp [Nat.testBit_zero]
  | succ k =>
    rw [Nat.testBit_or, Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_succ]
    have h1 : (1 / 2 : Nat) = 0 := rfl
    have hd : (2 * v.toNat + 1) / 2 = v.toNat := by omega
    have hd2 : (2 * v.toNat) / 2 = v.toNat := by omega
    rw [h1, hd, hd2]; simp

theorem bv8_sext32_eq_zero {x : BitVec 8}
    (h : x.signExtend 32 = (0#8 : BitVec 8).signExtend 32) : x = 0#8 := by
  ext i hi
  have hg := congrArg (fun b : BitVec 32 => b[i]'(by omega)) h
  simpa [BitVec.getElem_signExtend, hi] using hg

@[scoped bv_c0] theorem bv_c0_list_length_set {α : Type} (xs : List α) (i : Nat) (v : α) :
    (xs.set i v).length = xs.length := List.length_set

@[scoped bv_c0] theorem bv_c0_vals_with_heur (s : PlainState) (h : PlainHeur) :
    ({ s with heur := h }).vals = s.vals := rfl

@[scoped bv_c0] theorem bv_c0_heur_with_heur (s : PlainState) (h : PlainHeur) :
    ({ s with heur := h }).heur = h := rfl

@[scoped bv_c0] theorem bv_c0_cur_level_with_heur (s : PlainState) (h : PlainHeur) :
    ({ s with heur := h }).cur_level = s.cur_level := rfl

@[scoped bv_c0] theorem bv_c0_arena_with_probing (s : PlainState) (p : BitVec 64) :
    ({ s with probing := p }).arena = s.arena := rfl

@[scoped bv_c0] theorem bv_c0_vals_with_probing (s : PlainState) (p : BitVec 64) :
    ({ s with probing := p }).vals = s.vals := rfl

@[scoped bv_c0] theorem bv_c0_wvec_with_probing (s : PlainState) (p : BitVec 64) :
    ({ s with probing := p }).wvec = s.wvec := rfl

@[scoped bv_c0] theorem bv_c0_wstk_with_probing (s : PlainState) (p : BitVec 64) :
    ({ s with probing := p }).wstk = s.wstk := rfl

@[scoped c0_load] theorem c0_load_arena_heap_zero {c : PlainCfg} {s : PlainState}
    {R : Mem 64 → Prop} {m : Mem 64} (hi : 0 < s.heur.heap.length)
    (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i32 c.pHeap = some s.heur.heap[0] := by
  simpa using load_arena_heap (i := 0) hi hm

@[scoped c0_load] theorem c0_load_arena_heap_add_zero {c : PlainCfg} {s : PlainState}
    {R : Mem 64 → Prop} {m : Mem 64} (hi : 0 < s.heur.heap.length)
    (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i32 (c.pHeap + 0#64) = some s.heur.heap[0] := by
  simpa using load_arena_heap (i := 0) hi hm

end PlainTopTactics

section SearchProofs

open PlainTopTactics
open scoped PlainTopTactics

/-- Fast `PlainHeur.LengthsOk` transport across scalar-only field updates (avoids `whnf` over
52-field `PlainHeur` record equality). -/
private theorem heurOk_scalar {c : PlainCfg} {h : PlainHeur} (hok : h.LengthsOk c)
    {h' : PlainHeur}
    (hh : h'.heap = h.heap := by rfl) (hp : h'.pos = h.pos := by rfl)
    (hs : h'.score = h.score := by rfl) (hph : h'.phases = h.phases := by rfl)
    (hpt : h'.phases_target = h.phases_target := by rfl)
    (hpb : h'.phases_best = h.phases_best := by rfl)
    (hw : h'.wsort = h.wsort := by rfl) (hsh : h'.shrink_stk = h.shrink_stk := by rfl)
    (hr : h'.red_refs = h.red_refs := by rfl) (hg : h'.glue_used = h.glue_used := by rfl)
    (hqp : h'.q_prev = h.q_prev := by rfl) (hqn : h'.q_next = h.q_next := by rfl)
    (hqs : h'.q_stamp = h.q_stamp := by rfl) (hd : h'.delayed = h.delayed := by rfl) :
    h'.LengthsOk c :=
  ⟨hh ▸ hok.heap_len_arr, hp ▸ hok.pos_len, hs ▸ hok.score_len, hph ▸ hok.phases_len,
   hpt ▸ hok.phases_target_len, hpb ▸ hok.phases_best_len, hw ▸ hok.wsort_len,
   hsh ▸ hok.shrink_stk_len, hr ▸ hok.red_refs_len, hg ▸ hok.glue_used_len,
   hqp ▸ hok.q_prev_len, hqn ▸ hok.q_next_len, hqs ▸ hok.q_stamp_len, hd ▸ hok.delayed_len_arr⟩

/-- Depth-1 heuristic store packer from `{ s with heur := h }` (prevents exponential record
nesting across sequential stores without higher-order unification). -/
private theorem pack_heur_store {c : PlainCfg} {s : PlainState} {h h' : PlainHeur}
    {R : Mem 64 → Prop} {m m' : Mem 64} {addr : BitVec 64} {ty : Ty}
    (hst : storeOk m ty addr ∧ (PlainMem c { { s with heur := h } with heur := h' } ⋆ R) m')
    (hok : h'.LengthsOk c) :
    storeOk m ty addr ∧ ∃ h1 : PlainHeur, h1 = h' ∧ h1.LengthsOk c ∧
      (PlainMem c { s with heur := h1 } ⋆ R) m' :=
  ⟨hst.1, h', rfl, hok, hst.2⟩

/-- Depth-1 heuristic store packer starting from plain `s`. -/
private theorem pack_heur_store0 {c : PlainCfg} {s : PlainState} {h' : PlainHeur}
    {R : Mem 64 → Prop} {m m' : Mem 64} {addr : BitVec 64} {ty : Ty}
    (hst : storeOk m ty addr ∧ (PlainMem c { s with heur := h' } ⋆ R) m')
    (hok : h'.LengthsOk c) :
    storeOk m ty addr ∧ ∃ h1 : PlainHeur, h1 = h' ∧ h1.LengthsOk c ∧
      (PlainMem c { s with heur := h1 } ⋆ R) m' :=
  ⟨hst.1, h', rfl, hok, hst.2⟩

/-- Depth-1 `cur_level` store over `{ s with heur := h }`. -/
private theorem store_cur_level_with_heur {c : PlainCfg} {s : PlainState} {h : PlainHeur}
    {R : Mem 64 → Prop} {m : Mem 64} (v : Nat) (hv : v < 2 ^ 64)
    (hm : (PlainMem c { s with heur := h } ⋆ R) m) :
    storeOk m i64 (c.hdr + 160) ∧
    (PlainMem c { s with cur_level := v, heur := h } ⋆ R)
      (storeMem m i64 (c.hdr + 160) (BitVec.ofNat 64 v)) :=
  store_arena_cur_level v hv hm

/-- `PlainCoreInv` is independent of `probing` and `fuel`. -/
theorem plainCoreInv_with_probing {c : PlainCfg} {F0 : CNF Nat} {s : PlainState}
    (h : PlainCoreInv c F0 s) (p : BitVec 64) :
    PlainCoreInv c F0 { s with probing := p } :=
  { h with
    lengths := { h.lengths with }
    arena := { h.arena with }
    watches := h.watches.with_wstk rfl rfl rfl rfl }

theorem plainInv_with_probing {c : PlainCfg} {F0 : CNF Nat} {s : PlainState}
    (h : PlainInv c F0 s) (p : BitVec 64) :
    PlainInv c F0 { s with probing := p } :=
  ⟨plainCoreInv_with_probing h.core p, h.marks⟩

theorem plainCoreInv_with_fuel {c : PlainCfg} {F0 : CNF Nat} {s : PlainState}
    (h : PlainCoreInv c F0 s) (f : BitVec 64) :
    PlainCoreInv c F0 { s with fuel := f } :=
  { h with
    lengths := { h.lengths with }
    arena := { h.arena with }
    watches := h.watches.with_wstk rfl rfl rfl rfl }

theorem plainInv_with_fuel {c : PlainCfg} {F0 : CNF Nat} {s : PlainState}
    (h : PlainInv c F0 s) (f : BitVec 64) :
    PlainInv c F0 { s with fuel := f } :=
  ⟨plainCoreInv_with_fuel h.core f, h.marks⟩

theorem level0_unsat_of_prop_conflict {c : PlainCfg} {F0 : CNF Nat} {s : PlainState}
    (hcore : PlainCoreInv c F0 s) (hl0 : s.cur_level = 0)
    (hc : (s.confl_type = 1#64 ∧ s.confl_lit0.toNat < 2 * c.mv ∧ s.confl_lit1.toNat < 2 * c.mv ∧
      F0.EntailsClause (cnfClause [s.confl_lit0.toNat, s.confl_lit1.toNat]) ∧
      s.vals[s.confl_lit0.toNat]?.getD 0#8 = 0xFF#8 ∧
      s.vals[s.confl_lit1.toNat]?.getD 0#8 = 0xFF#8) ∨
     (s.confl_type = 2#64 ∧ s.confl_ref.toNat ∈ arenaClauseRefs s ∧
      arenaClauseGarb s s.confl_ref.toNat = false ∧
      ∀ l ∈ arenaClauseLits s s.confl_ref.toNat, s.vals[l]?.getD 0#8 = 0xFF#8)) :
    F0.Unsat := by
  rcases hc with ⟨_, h0, h1, hent, hf0, hf1⟩ | ⟨_, href, hng, hfals⟩
  · exact hcore.level0_unsat_of_bin_conflict hl0 h0 h1 hent hf0 hf1
  · exact hcore.level0_unsat_of_conflict hl0 href hng hfals

theorem analyze_confl_of_prop {c : PlainCfg} {F0 : CNF Nat} {s : PlainState}
    (hc : (s.confl_type = 1#64 ∧ s.confl_lit0.toNat < 2 * c.mv ∧ s.confl_lit1.toNat < 2 * c.mv ∧
      F0.EntailsClause (cnfClause [s.confl_lit0.toNat, s.confl_lit1.toNat]) ∧
      s.vals[s.confl_lit0.toNat]?.getD 0#8 = 0xFF#8 ∧
      s.vals[s.confl_lit1.toNat]?.getD 0#8 = 0xFF#8) ∨
     (s.confl_type = 2#64 ∧ s.confl_ref.toNat ∈ arenaClauseRefs s ∧
      arenaClauseGarb s s.confl_ref.toNat = false ∧
      ∀ l ∈ arenaClauseLits s s.confl_ref.toNat, s.vals[l]?.getD 0#8 = 0xFF#8)) :
    ((s.confl_type = 1#64 ∧ s.confl_lit0.toNat < 2 * c.mv ∧ s.confl_lit1.toNat < 2 * c.mv ∧
      F0.EntailsClause (cnfClause [s.confl_lit0.toNat, s.confl_lit1.toNat]) ∧
      s.vals[s.confl_lit0.toNat]?.getD 0#8 = 0xFF#8 ∧
      s.vals[s.confl_lit1.toNat]?.getD 0#8 = 0xFF#8) ∨
     (s.confl_type ≠ 1#64 ∧ s.confl_ref.toNat ∈ arenaClauseRefs s ∧
      arenaClauseGarb s s.confl_ref.toNat = false ∧
      ∀ l ∈ arenaClauseLits s s.confl_ref.toNat, s.vals[l]?.getD 0#8 = 0xFF#8)) := by
  rcases hc with hbin | ⟨ht2, hrest⟩
  · exact Or.inl hbin
  · exact Or.inr ⟨by rw [ht2]; decide, hrest⟩

/-- `PlainMem` only inspects `s.heur.heap_len` modulo `2^64`. -/
private theorem plainMem_norm_heap_len (c : PlainCfg) (s : PlainState) :
    PlainMem c { s with
        heur := { s.heur with heap_len := (BitVec.ofNat 64 s.heur.heap_len).toNat } } =
      PlainMem c s := by
  dsimp only [PlainMem, PlainCoreArrays, PlainHeurArrays, hdrTailWords]
  simp only [bv_ofNat_toNat_eq]

/-- Decision assignment (`cur_level := s.cur_level + 1`, `rsn := 0xFFFFFFFF#32`) on an unassigned
literal preserves `PlainCoreInv`. -/
theorem decide_assign_preserves_core {c : PlainCfg} {F0 : CNF Nat} {s : PlainState}
    (hinv : PlainCoreInv c F0 s) {lit : BitVec 32} {phases' : List (BitVec 8)}
    (hlit : lit.toNat < 2 * c.mv) (hph : phases'.length = c.mv)
    (hun : s.vals[lit.toNat]?.getD 0#8 = 0#8) :
    let v := lit.toNat / 2
    let s' : PlainState :=
      { s with
        cur_level := s.cur_level + 1
        vals := (s.vals.set lit.toNat 1#8).set (lit.toNat ^^^ 1) 0xFF#8
        lvl := s.lvl.set v (BitVec.ofNat 32 (s.cur_level + 1))
        rsns := s.rsns.set v 0xFFFFFFFF#32
        trl := s.trl.set s.trail_end lit
        trail_pos := s.trail_pos.set v (BitVec.ofNat 32 s.trail_end)
        trail_end := s.trail_end + 1
        heur := { s.heur with phases := phases' } }
    PlainCoreInv c F0 s' := by
  intro v s'
  have hmv := c.hmv; unfold dimacsBound at hmv
  have hte_lt : s.trail_end < c.mv := hinv.trail_end_lt_of_unassigned hlit hun
  have hnot_var : ∀ i < s.trail_end, (s.trl[i]?.getD 0#32).toNat / 2 ≠ v :=
    (hinv.vals_zero_iff hlit).mp hun
  have hnlit_lt : (lit.toNat ^^^ 1) < 2 * c.mv := litNeg_lt_two_mul hlit
  have hne_lit : lit.toNat ^^^ 1 ≠ lit.toNat := litNeg_ne_self lit.toNat
  have hlen := hinv.lengths
  have hcur_le := hinv.cur_level_le
  have hcur1_lt : s.cur_level + 1 < 2 ^ 32 := by omega
  have hs'_te : s'.trail_end = s.trail_end + 1 := rfl
  have hs'_cl : s'.cur_level = s.cur_level + 1 := rfl
  have htrl_get : ∀ i < s.trail_end + 1,
      (s'.trl[i]?.getD 0#32).toNat =
        if i = s.trail_end then lit.toNat else (s.trl[i]?.getD 0#32).toNat := by
    intro i hi
    by_cases he : i = s.trail_end
    · subst he; simp [s', List.getElem?_set_self (by rw [hlen.trl_len]; omega)]
    · simp [s', he, List.getElem?_set_ne (Ne.symm he)]
  have hlvl_get : ∀ w < c.mv,
      (s'.lvl[w]?.getD 0#32).toNat =
        if w = v then s.cur_level + 1 else (s.lvl[w]?.getD 0#32).toNat := by
    intro w hw
    by_cases he : w = v
    · subst he
      simp [s', List.getElem?_set_self (by rw [hlen.lvl_len]; omega), bv32_ofNat_toNat hcur1_lt]
    · simp [s', he, List.getElem?_set_ne (Ne.symm he)]
  have hvals_get : ∀ l < 2 * c.mv,
      s'.vals[l]?.getD 0#8 =
        if l = lit.toNat ^^^ 1 then 0xFF#8
        else if l = lit.toNat then 1#8
        else s.vals[l]?.getD 0#8 := by
    intro l hl
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
      trail_pos_len := by simp [s', hlen.trail_pos_len]
      trail_end_le := by rw [hs'_te]; omega
      propagated_le := by dsimp [s']; have := hlen.propagated_le; omega
      heur_ok := { hlen.heur_ok with phases_len := hph } }
  have harena' : ArenaClausesInv c F0 s' := { hinv.arena with len_ok := hinv.arena.len_ok }
  have hwat' : WatchesInv c F0 s' := hinv.watches.with_wstk rfl rfl rfl rfl
  refine ⟨hlen', harena', hwat', by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi; rw [hs'_te] at hi; rw [htrl_get i hi]; split
    · exact hlit
    · exact hinv.trail_lits_lt i (by omega)
  · intro i j hi hj hveq; rw [hs'_te] at hi hj; rw [htrl_get i hi, htrl_get j hj] at hveq
    split at hveq <;> split at hveq
    · omega
    · exact absurd hveq.symm (hnot_var j (by omega))
    · exact absurd hveq (hnot_var i (by omega))
    · exact hinv.trail_vars_nodup i j (by omega) (by omega) hveq
  · intro l hl; rw [hvals_get l hl]
    split; · exact Or.inr (Or.inr rfl)
    split; · exact Or.inr (Or.inl rfl)
    exact hinv.vals_domain l hl
  · intro l hl; rw [hvals_get l hl, hs'_te]
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
    · rintro ⟨i, hi, heq⟩; rw [htrl_get i hi] at heq
      by_cases hie : i = s.trail_end
      · simp only [hie, ↓reduceIte] at heq; subst heq; simp [Ne.symm hne_lit]
      · simp only [hie, ↓reduceIte] at heq
        have hlv : l / 2 ≠ v := by rw [← heq]; exact hnot_var i (by omega)
        have h1 : l ≠ lit.toNat ^^^ 1 := fun h => hlv (by rw [h]; exact litVar_litNeg _)
        have h2 : l ≠ lit.toNat := fun h => hlv (by rw [h])
        simp only [h1, h2, ↓reduceIte]; exact (hinv.vals_true_iff l hl).mpr ⟨i, by omega, heq⟩
  · intro l hl; rw [hvals_get l hl, hs'_te]
    constructor
    · intro h1
      by_cases hneg : l = lit.toNat ^^^ 1
      · exact ⟨s.trail_end, by omega, by
          rw [htrl_get _ (by omega)]; simp only [↓reduceIte, hneg]; exact (litNeg_litNeg _).symm⟩
      · simp only [hneg, ↓reduceIte] at h1
        by_cases hpos : l = lit.toNat
        · simp [hpos] at h1
        · simp only [hpos, ↓reduceIte] at h1
          obtain ⟨i, hi, heq⟩ := (hinv.vals_false_iff l hl).mp h1
          exact ⟨i, by omega,
            by rw [htrl_get i (by omega)]; simp [show i ≠ s.trail_end by omega, heq]⟩
    · rintro ⟨i, hi, heq⟩; rw [htrl_get i hi] at heq
      by_cases hie : i = s.trail_end
      · simp only [hie, ↓reduceIte] at heq
        have hl_eq : l = lit.toNat ^^^ 1 := by
          have h := congrArg litNeg heq
          have h1 : litNeg (l ^^^ 1) = l := litNeg_litNeg l
          rw [h1] at h; exact h.symm
        simp [hl_eq]
      · simp only [hie, ↓reduceIte] at heq
        have hlv : l / 2 ≠ v := by
          have h := hnot_var i (by omega); rw [heq] at h
          rwa [show (l ^^^ 1) / 2 = l / 2 from litVar_litNeg l] at h
        have h1 : l ≠ lit.toNat ^^^ 1 := fun h => hlv (by rw [h]; exact litVar_litNeg _)
        have h2 : l ≠ lit.toNat := fun h => hlv (by rw [h])
        simp only [h1, h2, ↓reduceIte]; exact (hinv.vals_false_iff l hl).mpr ⟨i, by omega, heq⟩
  · intro i hi; rw [hs'_te] at hi; rw [hs'_cl, htrl_get i hi]
    by_cases hie : i = s.trail_end
    · simp only [hie, ↓reduceIte]; rw [hlvl_get v (by omega)]; simp
    · have hilt : i < s.trail_end := by omega
      simp only [hie, ↓reduceIte]
      rw [hlvl_get _ (by have := hinv.trail_lits_lt i hilt; omega)]
      simp only [hnot_var i hilt, ↓reduceIte]; have := hinv.lvl_le i hilt; omega
  · intro i j hij hj; rw [hs'_te] at hj; rw [htrl_get i (by omega), htrl_get j hj]
    by_cases hje : j = s.trail_end
    · simp only [hje, ↓reduceIte]; rw [hlvl_get v (by omega)]; simp only [↓reduceIte]
      by_cases hie : i = s.trail_end
      · simp only [hie, ↓reduceIte]; rw [hlvl_get v (by omega)]; simp
      · have hilt : i < s.trail_end := by omega
        simp only [hie, ↓reduceIte]
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
    · subst hLeq; refine ⟨s.trail_end, by omega, ?_⟩
      rw [htrl_get _ (by omega)]; simp only [↓reduceIte]; rw [hlvl_get v (by omega)]; simp
    · obtain ⟨i, hi, hli⟩ := hinv.levels_inhabited L hL1 (by omega)
      refine ⟨i, by omega, ?_⟩
      rw [htrl_get i (by omega)]; simp only [show i ≠ s.trail_end by omega, ↓reduceIte]
      rw [hlvl_get _ (by have := hinv.trail_lits_lt i hi; omega)]
      simp [hnot_var i hi, hli]
  · intro i hi hli; rw [hs'_te] at hi; rw [htrl_get i hi] at hli ⊢
    by_cases hie : i = s.trail_end
    · simp only [hie, ↓reduceIte] at hli
      rw [hlvl_get v (by omega)] at hli; simp only [↓reduceIte] at hli; omega
    · have hilt : i < s.trail_end := by omega
      simp only [hie, ↓reduceIte] at hli ⊢
      rw [hlvl_get _ (by have := hinv.trail_lits_lt i hilt; omega)] at hli
      simp only [hnot_var i hilt, ↓reduceIte] at hli; exact hinv.level0_sound i hilt hli
  · intro i hi; rw [hs'_te] at hi; rw [htrl_get i hi]
    have hte_lt32 : s.trail_end < 2 ^ 32 := by omega
    by_cases hie : i = s.trail_end
    · subst hie; simp only [↓reduceIte]
      dsimp only [s', v]
      rw [List.getElem?_set_self (by rw [hlen.trail_pos_len]; omega), Option.getD_some,
        bv32_ofNat_toNat hte_lt32]
    · have hilt : i < s.trail_end := by omega
      simp only [hie, ↓reduceIte]
      have hnv : (s.trl[i]?.getD 0#32).toNat / 2 ≠ v := hnot_var i hilt
      simp [s', List.getElem?_set_ne (Ne.symm hnv), hinv.trail_pos_inv i hilt]
  · intro idx hidx hli; rw [hs'_te] at hidx; rw [htrl_get idx hidx] at hli ⊢
    by_cases hie : idx = s.trail_end
    · simp only [hie, ↓reduceIte] at hli
      rw [hlvl_get v (by omega)] at hli; simp only [↓reduceIte] at hli; omega
    · have hilt : idx < s.trail_end := by omega
      simp only [hie, ↓reduceIte] at hli ⊢
      have hnv : (s.trl[idx]?.getD 0#32).toNat / 2 ≠ v := hnot_var idx hilt
      rw [hlvl_get _ (by have := hinv.trail_lits_lt idx hilt; omega)] at hli
      simp only [hnv, ↓reduceIte] at hli
      simp [s', List.getElem?_set_ne (Ne.symm hnv), hinv.level0_rsn_none idx hilt hli]
  · intro idx hidx; rw [hs'_te] at hidx; dsimp only; rw [htrl_get idx hidx]
    by_cases hie : idx = s.trail_end
    · simp only [hie, ↓reduceIte]
      have hr : s'.rsns[v]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 := by
        dsimp only [s']; rw [List.getElem?_set_self (by rw [hlen.rsns_len]; omega)]; rfl
      rw [hr]; intro hne; exact absurd rfl hne
    · have hilt : idx < s.trail_end := by omega
      simp only [hie, ↓reduceIte]
      have hnv : (s.trl[idx]?.getD 0#32).toNat / 2 ≠ v := hnot_var idx hilt
      have hr : s'.rsns[(s.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 =
          s.rsns[(s.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 := by
        simp [s', List.getElem?_set_ne (Ne.symm hnv)]
      rw [hr]; intro hne; have hrs := hinv.reason_inv idx hilt hne
      split at hrs <;> split
      · obtain ⟨k, hk, hkeq⟩ := hrs.2.2
        exact ⟨hrs.1, hrs.2.1, ⟨k, hk, by
          rw [htrl_get k (by omega)]; simp [show k ≠ s.trail_end by omega, hkeq]⟩⟩
      · rename_i h1 h2; exact absurd h1 h2
      · rename_i h1 h2; exact absurd h2 h1
      · refine ⟨hrs.1, hrs.2.1, fun q hq => ?_⟩
        have hq' : q ∈ arenaClauseLits s
            (s.rsns[(s.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat := by
          simpa [arenaClauseLits, arenaClauseSize, s'] using hq
        exact (hrs.2.2 q hq').elim Or.inl fun ⟨k, hk, hkeq⟩ => Or.inr ⟨k, hk, by
          rw [htrl_get k (by omega)]; simp [show k ≠ s.trail_end by omega, hkeq]⟩
  · intro idx hidx; rw [hs'_te] at hidx; dsimp only; rw [htrl_get idx hidx]
    by_cases hie : idx = s.trail_end
    · simp only [hie, ↓reduceIte]
      have hr : s'.rsns[v]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 := by
        dsimp only [s']; rw [List.getElem?_set_self (by rw [hlen.rsns_len]; omega)]; rfl
      rw [hr]; intro hne; exact absurd rfl hne
    · have hilt : idx < s.trail_end := by omega
      simp only [hie, ↓reduceIte]
      have hnv : (s.trl[idx]?.getD 0#32).toNat / 2 ≠ v := hnot_var idx hilt
      have hr : s'.rsns[(s.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 =
          s.rsns[(s.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 := by
        simp [s', List.getElem?_set_ne (Ne.symm hnv)]
      rw [hr]; intro hne hbi
      have hmem := hinv.reason_lit_mem idx hilt hne hbi
      simpa [arenaClauseLits, arenaClauseSize, s'] using hmem

/-- If `p ∈ arenaClauseRefs s` and `arenaNextOff s.arena s.arena_len p < s.arena_len`,
then the next block offset is also in `arenaClauseRefs s`. -/
theorem arenaClauseRefs_next {c : PlainCfg} {F0 : CNF Nat} {s : PlainState}
    (ha : ArenaClausesInv c F0 s) {p : Nat} (hp : p ∈ arenaClauseRefs s)
    (hlt : arenaNextOff s.arena s.arena_len p < s.arena_len) :
    arenaNextOff s.arena s.arena_len p ∈ arenaClauseRefs s := by
  have go : ∀ (fuel pos : Nat),
      s.arena_len - pos ≤ fuel →
      p ∈ arenaScanRefs s.arena s.arena_len pos fuel →
      arenaNextOff s.arena s.arena_len p + 3 ≤ s.arena_len →
      arenaNextOff s.arena s.arena_len p ∈ arenaScanRefs s.arena s.arena_len pos fuel := by
    intro fuel
    induction fuel with
    | zero => intro _ _ h _; simp [arenaScanRefs] at h
    | succ f ih =>
      intro pos hfl hmem hn3
      unfold arenaScanRefs at hmem ⊢
      split at hmem
      · rename_i hle
        simp only [hle, ↓reduceIte, List.mem_cons] at hmem ⊢
        have hb := arenaNextOff_bounds (ar := s.arena) (alen := s.arena_len) (cref := pos) hle
        rcases hmem with rfl | hrest
        · right
          cases f with
          | zero => omega
          | succ f' => unfold arenaScanRefs; simp [hn3]
        · exact Or.inr (ih (arenaNextOff s.arena s.arena_len pos) (by omega) hrest hn3)
      · simp at hmem
  have hwf := ha.refs_wf p hp
  have hn3 : arenaNextOff s.arena s.arena_len p + 3 ≤ s.arena_len := by
    rcases hwf.2.2.2.2 with he | h3
    · omega
    · exact h3
  exact go s.arena_len 0 (by omega) hp hn3

/-! ## 2. `plain_restart_due_wp` -/

theorem plain_restart_due_wp (Γ : Env) :
    ∀ args m Q X, plainRestartDueSpec args m Q X →
      Func.wp Γ plain_restart_due_body args m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  unfold Func.wp plain_restart_due_body; wp_unfold
  refine ⟨_, load_arena_cur_level hm, ?_⟩
  refine ⟨fun _ => hQ 0#64 s.heur m hlen.heur_ok (Or.inl rfl) hm, fun _ => ?_⟩
  refine ⟨_, load_arena_stable hm, ?_⟩
  refine ⟨fun _ => ?_, fun _ => ?_⟩
  · refine ⟨_, load_arena_rel_trigger hm, ?_⟩
    refine ⟨fun _ => ?_, fun _ => hQ 0#64 s.heur m hlen.heur_ok (Or.inl rfl) hm⟩
    obtain ⟨hok, hm1⟩ := store_arena_rel_trigger 0#64 hm
    exact ⟨hok, hQ 1#64 _ _ (heurOk_scalar hlen.heur_ok) (Or.inr rfl) hm1⟩
  · refine ⟨_, load_arena_conflicts hm, _, load_arena_restart_limit hm, ?_⟩
    refine ⟨fun _ => hQ 0#64 s.heur m hlen.heur_ok (Or.inl rfl) hm, fun _ => ?_⟩
    refine ⟨_, load_arena_ema_fast_exp hm, _, load_arena_ema_slow_exp hm, ?_⟩
    have hsh24 : (1 : BitVec 64) <<< ((BitVec.signExtend 64 (24 : BitVec 32)).toNat % 64) =
        16777216#64 := rfl
    have hsh8 : ((BitVec.signExtend 64 (8 : BitVec 32)).toNat % 64) = 8 := rfl
    rw [hsh24]
    let fd : BitVec 64 := 16777216#64 - s.heur.ema_fast_exp
    let sd : BitVec 64 := 16777216#64 - s.heur.ema_slow_exp
    refine ⟨fun _ => hQ 0#64 s.heur m hlen.heur_ok (Or.inl rfl) hm, fun h1 => ?_⟩
    have hfd : 256 < fd.toNat := by
      change fd.ule 256#64 = false at h1
      simp only [BitVec.ule, decide_eq_false_iff_not] at h1; bv_omega
    refine ⟨fun _ => hQ 0#64 s.heur m hlen.heur_ok (Or.inl rfl) hm, fun h2 => ?_⟩
    have hsd : 256 < sd.toNat := by
      change sd.ule 256#64 = false at h2
      simp only [BitVec.ule, decide_eq_false_iff_not] at h2; bv_omega
    refine ⟨_, load_arena_ema_fast_biased hm, ?_⟩
    rw [hsh8]
    refine ⟨bv64_shr8_ne_zero hfd, _, load_arena_ema_slow_biased hm, ?_⟩
    wp_unfold; rw [hsh8]
    refine ⟨bv64_shr8_ne_zero hsd, ?_⟩
    refine ⟨fun _ => ?_, fun _ => hQ 0#64 s.heur m hlen.heur_ok (Or.inl rfl) hm⟩
    refine ⟨_, load_arena_conflicts hm, ?_⟩
    obtain ⟨hok, hm1⟩ := store_arena_restart_limit (s.heur.conflicts + 1#64) hm
    exact ⟨hok, hQ 1#64 _ _ (heurOk_scalar hlen.heur_ok) (Or.inr rfl) hm1⟩

/-! ## 3. `plain_rephase_wp` -/

theorem plain_rephase_wp (Γ : Env)
    (hBt : ∀ args m Q X, plainBacktrackSpec args m Q X →
      Γ "plain_backtrack" [i64, i64] [] args m Q X)
    (hLog : ∀ args m Q X, plainIlog10Spec args m Q X →
      Γ "plain_ilog10" [i64] [i64] args m Q X) :
    ∀ args m Q X, plainRephaseSpec args m Q X →
      Func.wp Γ plain_rephase_body args m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hinv, hm, hQ⟩
  have hmv := c.hmv; unfold dimacsBound at hmv
  c0_steps
  c0_call hBt
  refine ⟨c, s, R, rfl, hinv.core.lengths, hinv.core.trail_lits_lt, hm, ?_⟩
  intro vals1 lvl1 rsns1 te1 prop1 heur1 m1 s1 _ _ _ _ _ hcore_fn hm1
  have hcore1 : PlainCoreInv c F0 s1 := (hcore_fn F0 hinv.core (Nat.zero_le _)).1
  have hinv1 : PlainInv c F0 s1 := ⟨hcore1, hinv.marks⟩
  wp_unfold
  refine ⟨_, load_arena_rephased hm1, ?_⟩
  obtain ⟨hok_rp, heur_rp, _, hsel_ok, hm1'⟩ :=
    pack_heur_store0 (store_arena_rephased (heur1.rephased + 1) hm1)
      (heurOk_scalar hcore1.lengths.heur_ok)
  refine ⟨hok_rp, _, load_arena_rephased hm1', by decide,
    _, load_arena_phases_ptr hm1', _, load_arena_phases_target_ptr hm1',
    _, load_arena_phases_best_ptr hm1', _, load_arena_mv hm1', ?_⟩
  -- Join after the 3-way `sel` phase-update `if / else if / else` (carries dead `k : i64`)
  refine wp_join_group
    (fun (_k, ()) m2 => ∃ heur2 : PlainHeur, heur2.LengthsOk c ∧
      (PlainMem c { s1 with heur := heur2 } ⋆ R) m2)
    (fun _ ⟨_k, ⟨⟩⟩ m2 ⟨heur2, hok2, hm2⟩ => by
      c0_steps
      refine wp_loop_inv
        (fun (kv, ()) ml => ∃ heurL : PlainHeur, kv.toNat ≤ c.mv ∧ heurL.LengthsOk c ∧
          (PlainMem c { s1 with heur := heurL } ⋆ R) ml)
        (fun (kv, ()) _ => c.mv - kv.toNat)
        (fun J hJ => by
          c0_steps
          exact hJ (0#64, ()) m2 ⟨heur2, Nat.zero_le _, hok2, hm2⟩)
        (fun J ⟨kv, ⟨⟩⟩ ml ⟨heurL, hkle, hokL, hml⟩ ih => by
          wp_unfold
          refine ⟨fun hc => ?_, fun _ => ?_⟩
          · have hklt : kv.toNat < c.mv := by
              change kv.ult (BitVec.ofNat 64 c.mv) = true at hc
              simp only [BitVec.ult, decide_eq_true_eq] at hc; bv_omega
            have hph_len : heurL.phases.length = c.mv := hokL.phases_len
            have hpt_len : heurL.phases_target.length = c.mv := hokL.phases_target_len
            refine ⟨_, c0_load_arena_phases (i := kv) (by dsimp; omega) hml, ?_⟩
            obtain ⟨hst, heurL', _, hokL', hml'⟩ :=
              pack_heur_store
                (c0_store_arena_phases_target (i := kv) (heurL.phases[kv.toNat]'(by omega))
                  (by dsimp; omega) hml)
                { hokL with phases_target_len := by simp [hpt_len] }
            have hinc : (kv + 1#64).toNat = kv.toNat + 1 := by bv_omega
            exact ⟨hst, ih (kv + 1#64, ()) _ (by dsimp; omega) ⟨heurL', by omega, hokL', hml'⟩⟩
          · obtain ⟨hok_ta, h1, _, hok1, hm_ta⟩ :=
              pack_heur_store (store_arena_target_assigned 0 hml) (heurOk_scalar hokL)
            refine ⟨hok_ta, _, load_arena_rephased hm_ta, ?_⟩
            c0_call hLog
            intro lg _ _
            wp_unfold
            refine ⟨_, load_arena_conflicts hm_ta, _, load_arena_rephased hm_ta, ?_⟩
            obtain ⟨hok_rl, h2, _, hok2, hm_rl⟩ :=
              pack_heur_store
                (store_arena_rephase_limit
                  (h1.conflicts + 1000 + 100 * h1.rephased * lg) hm_ta)
                (heurOk_scalar hok1)
            exact ⟨hok_rl, hQ vals1 lvl1 rsns1 te1 prop1 h2 _ (hinv1.with_heur hok2) hm_rl⟩))
    (fun J hJ => by
      -- Join for `sel == 0 || sel == 2`
      refine wp_join_group
        (fun () m0 => (PlainMem c { s1 with heur := heur_rp } ⋆ R) m0)
        (fun _ ⟨⟩ m0 hm0 => by
          c0_steps
          refine wp_loop_inv
            (fun (kv, ()) ml => ∃ heurL : PlainHeur, kv.toNat ≤ c.mv ∧ heurL.LengthsOk c ∧
              (PlainMem c { s1 with heur := heurL } ⋆ R) ml)
            (fun (kv, ()) _ => c.mv - kv.toNat)
            (fun J1 hJ1 => by
              c0_steps; exact hJ1 (0#64, ()) m0 ⟨heur_rp, Nat.zero_le _, hsel_ok, hm0⟩)
            (fun J1 ⟨kv, ⟨⟩⟩ ml ⟨heurL, hkle, hokL, hml⟩ ih => by
              wp_unfold
              refine ⟨fun hc => ?_, fun _ => ?_⟩
              · have hklt : kv.toNat < c.mv := by
                  change kv.ult (BitVec.ofNat 64 c.mv) = true at hc
                  simp only [BitVec.ult, decide_eq_true_eq] at hc; bv_omega
                have hpb_len : heurL.phases_best.length = c.mv := hokL.phases_best_len
                have hph_len : heurL.phases.length = c.mv := hokL.phases_len
                have hinc : (kv + 1#64).toNat = kv.toNat + 1 := by bv_omega
                refine wp_join_group
                  (fun () ml' => ∃ heurL' : PlainHeur, heurL'.LengthsOk c ∧
                    (PlainMem c { s1 with heur := heurL' } ⋆ R) ml')
                  (fun _ ⟨⟩ ml' ⟨heurL', hokL', hml'⟩ => by
                    wp_unfold
                    exact ih (kv + 1#64, ()) ml' (by dsimp; omega)
                      ⟨heurL', by omega, hokL', hml'⟩)
                  (fun Jif hJif => by
                    wp_unfold
                    refine ⟨_, c0_load_arena_phases_best (i := kv) (by dsimp; omega) hml, ?_⟩
                    refine ⟨fun _ => ?_, fun _ => hJif () ml ⟨heurL, hokL, hml⟩⟩
                    refine ⟨_, c0_load_arena_phases_best (i := kv) (by dsimp; omega) hml, ?_⟩
                    obtain ⟨hst, heurL', _, hokL', hml'⟩ :=
                      pack_heur_store
                        (c0_store_arena_phases (i := kv) (heurL.phases_best[kv.toNat]'(by omega))
                          (by dsimp; omega) hml)
                        { hokL with phases_len := by simp [hph_len] }
                    exact ⟨hst, hJif () _ ⟨heurL', hokL', hml'⟩⟩)
              · obtain ⟨hok_ba, heurB, _, hokB, hmB⟩ :=
                  pack_heur_store (store_arena_best_assigned 0 hml) (heurOk_scalar hokL)
                exact ⟨hok_ba, hJ _ _ ⟨heurB, hokB, hmB⟩⟩))
        (fun J0 hJ0 => by
          wp_unfold
          refine ⟨fun _ => hJ0 () _ hm1', fun _ => ?_⟩
          refine ⟨fun _ => hJ0 () _ hm1', fun _ => ?_⟩
          refine wp_join_group
            (fun (_k, ()) m2 => ∃ heur2 : PlainHeur, heur2.LengthsOk c ∧
              (PlainMem c { s1 with heur := heur2 } ⋆ R) m2)
            (fun _ ⟨k2, ⟨⟩⟩ m2 hm2 => hJ (k2, ()) m2 hm2)
            (fun Je hJe => by
              wp_unfold
              refine ⟨fun _ => ?_, fun _ => ?_⟩
              · -- sel == 1
                refine wp_loop_inv
                  (fun (kv, ()) ml => ∃ heurL : PlainHeur, kv.toNat ≤ c.mv ∧ heurL.LengthsOk c ∧
                    (PlainMem c { s1 with heur := heurL } ⋆ R) ml)
                  (fun (kv, ()) _ => c.mv - kv.toNat)
                  (fun J1 hJ1 => by
                    c0_steps; exact hJ1 (0#64, ()) _ ⟨heur_rp, Nat.zero_le _, hsel_ok, hm1'⟩)
                  (fun J1 ⟨kv, ⟨⟩⟩ ml ⟨heurL, hkle, hokL, hml⟩ ih => by
                    c0_steps
                    · have hklt : kv.toNat < c.mv := by bv_omega
                      have hph_len : heurL.phases.length = c.mv := hokL.phases_len
                      have hinc : (kv + 1#64).toNat = kv.toNat + 1 := by bv_omega
                      wp_unfold
                      obtain ⟨hst, heurL', _, hokL', hml'⟩ :=
                        pack_heur_store
                          (c0_store_arena_phases (i := kv) (BitVec.setWidth 8 (0#32 - 1#32))
                            (by dsimp; omega) hml)
                          { hokL with phases_len := by simp [hph_len] }
                      exact ⟨hst, ih (kv + 1#64, ()) _ (by dsimp; omega)
                        ⟨heurL', by omega, hokL', hml'⟩⟩
                    · exact hJe _ _ ⟨heurL, hokL, hml⟩)
              · -- sel == 3
                refine wp_loop_inv
                  (fun (kv, ()) ml => ∃ heurL : PlainHeur, kv.toNat ≤ c.mv ∧ heurL.LengthsOk c ∧
                    (PlainMem c { s1 with heur := heurL } ⋆ R) ml)
                  (fun (kv, ()) _ => c.mv - kv.toNat)
                  (fun J1 hJ1 => by
                    c0_steps; exact hJ1 (0#64, ()) _ ⟨heur_rp, Nat.zero_le _, hsel_ok, hm1'⟩)
                  (fun J1 ⟨kv, ⟨⟩⟩ ml ⟨heurL, hkle, hokL, hml⟩ ih => by
                    c0_steps
                    · have hklt : kv.toNat < c.mv := by bv_omega
                      have hph_len : heurL.phases.length = c.mv := hokL.phases_len
                      have hinc : (kv + 1#64).toNat = kv.toNat + 1 := by bv_omega
                      wp_unfold
                      obtain ⟨hst, heurL', _, hokL', hml'⟩ :=
                        pack_heur_store
                          (c0_store_arena_phases (i := kv) (BitVec.setWidth 8 1#32)
                            (by dsimp; omega) hml)
                          { hokL with phases_len := by simp [hph_len] }
                      exact ⟨hst, ih (kv + 1#64, ()) _ (by dsimp; omega)
                        ⟨heurL', by omega, hokL', hml'⟩⟩
                    · exact hJe _ _ ⟨heurL, hokL, hml⟩))))

/-! ## 4. `plain_switch_mode_wp` -/

theorem plain_switch_mode_wp (Γ : Env)
    (hDown : ∀ args m Q X, plainHeapDownSpec args m Q X →
      Γ "plain_heap_down" [i64, i32] [] args m Q X)
    (hLog : ∀ args m Q X, plainIlog10Spec args m Q X →
      Γ "plain_ilog10" [i64] [i64] args m Q X) :
    ∀ args m Q X, plainSwitchModeSpec args m Q X →
      Func.wp Γ plain_switch_mode_body args m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  have hmv := c.hmv; unfold dimacsBound at hmv
  unfold Func.wp plain_switch_mode_body; wp_unfold
  refine wp_join_group
    (fun () m1 => ∃ heur1 : PlainHeur, heur1.LengthsOk c ∧
      (PlainMem c { s with heur := heur1 } ⋆ R) m1)
    (fun _ ⟨⟩ m1 ⟨heur1, hok1, hm1⟩ => by
      wp_unfold
      refine ⟨_, load_arena_switched hm1, ?_⟩
      obtain ⟨hs1, h1, _, hok_1, hm_1⟩ :=
        pack_heur_store (store_arena_switched (heur1.switched + 1) hm1) (heurOk_scalar hok1)
      refine ⟨hs1, _, load_arena_mode_count hm_1, ?_⟩
      obtain ⟨hs2, h2, _, hok_2, hm_2⟩ :=
        pack_heur_store (store_arena_mode_count (h1.mode_count + 1) hm_1) (heurOk_scalar hok_1)
      obtain ⟨hs3, h3, _, hok_3, hm_3⟩ :=
        pack_heur_store (store_arena_ema_fast_biased 0 hm_2) (heurOk_scalar hok_2)
      obtain ⟨hs4, h4, _, hok_4, hm_4⟩ :=
        pack_heur_store (store_arena_ema_fast_exp 16777216#64 hm_3) (heurOk_scalar hok_3)
      obtain ⟨hs5, h5, _, hok_5, hm_5⟩ :=
        pack_heur_store (store_arena_ema_slow_biased 0 hm_4) (heurOk_scalar hok_4)
      obtain ⟨hs6, h6, _, hok_6, hm_6⟩ :=
        pack_heur_store (store_arena_ema_slow_exp 16777216#64 hm_5) (heurOk_scalar hok_5)
      refine ⟨hs2, hs3, hs4, hs5, hs6, _, load_arena_conflicts hm_6, ?_⟩
      obtain ⟨hs7, h7, _, hok_7, hm_7⟩ :=
        pack_heur_store (store_arena_restart_limit (h6.conflicts + 1) hm_6) (heurOk_scalar hok_6)
      exact ⟨hs7, hQ h7 _ hok_7 hm_7⟩)
    (fun J hJ => by
      wp_unfold
      refine ⟨_, load_arena_stable hm, ?_⟩
      refine ⟨fun _ => ?_, fun _ => ?_⟩
      · -- h->stable == 0ULL
        refine ⟨_, load_arena_conflicts hm, _, load_arena_mode_confl_lim hm, ?_⟩
        refine ⟨fun _ => hQ s.heur m hlen.heur_ok hm, fun _ => ?_⟩
        obtain ⟨hok1, hs1, _, h1_ok, hm1⟩ :=
          pack_heur_store0 (store_arena_stable 1 hm) (heurOk_scalar hlen.heur_ok)
        refine ⟨hok1, _, load_arena_search_ticks hm1, _, load_arena_mode_saved_ticks hm1, ?_⟩
        refine wp_join_group
          (fun (_dt, ()) m0 => ∃ heur0 : PlainHeur, heur0.LengthsOk c ∧
            (PlainMem c { s with heur := heur0 } ⋆ R) m0)
          (fun _ ⟨dt, ⟨⟩⟩ m0 ⟨heur0, hok0, hm0⟩ => by
            wp_unfold
            refine ⟨_, load_arena_search_ticks hm0, ?_⟩
            obtain ⟨hs_tl, ht1, _, hok_t1, hm_t1⟩ :=
              pack_heur_store
                (store_arena_mode_tick_lim (heur0.search_ticks + dt) hm0) (heurOk_scalar hok0)
            refine ⟨hs_tl, _, load_arena_search_ticks hm_t1, ?_⟩
            obtain ⟨hs_st, ht2, _, hok_t2, hm_t2⟩ :=
              pack_heur_store
                (store_arena_mode_saved_ticks ht1.search_ticks hm_t1) (heurOk_scalar hok_t1)
            refine ⟨hs_st, _, load_arena_mv hm_t2, _, load_arena_values hm_t2,
              _, load_arena_heap_ptr hm_t2, _, load_arena_pos_ptr hm_t2, ?_⟩
            -- Loop 1: rebuild heap from unassigned vars (`while (v < mv)`)
            refine wp_loop_inv
              (fun (nv, vv, ()) ml => ∃ heurL : PlainHeur,
                vv.toNat ≤ c.mv ∧ nv.toNat ≤ vv.toNat ∧ heurL.LengthsOk c ∧
                (PlainMem c { s with heur := heurL } ⋆ R) ml)
              (fun (_nv, vv, ()) _ => c.mv - vv.toNat)
              (fun J1 hJ1 => by
                c0_steps
                exact hJ1 (0#64, 0#64, ()) _ ⟨ht2, Nat.zero_le _, Nat.zero_le _, hok_t2, hm_t2⟩)
              (fun J1 ⟨nv, vv, ⟨⟩⟩ ml ⟨heurL, hvle, hnle, hokL, hml⟩ ih => by
                wp_unfold
                refine ⟨fun hc => ?_, fun _ => ?_⟩
                · have hvlt : vv.toNat < c.mv := by
                    change vv.ult (BitVec.ofNat 64 c.mv) = true at hc
                    simp only [BitVec.ult, decide_eq_true_eq] at hc; bv_omega
                  have h2v : (vv <<< 1).toNat = 2 * vv.toNat := bv64_shl1_toNat (by omega)
                  have hvl : s.vals.length = 2 * c.mv := hlen.vals_len
                  have hhl : heurL.heap.length = c.mv := hokL.heap_len_arr
                  have hpl : heurL.pos.length = c.mv := hokL.pos_len
                  have hv1 : (vv + 1#64).toNat = vv.toNat + 1 := by bv_omega
                  refine wp_join_group
                    (fun (nv', ()) ml' => ∃ heurL' : PlainHeur,
                      nv'.toNat ≤ vv.toNat + 1 ∧ heurL'.LengthsOk c ∧
                      (PlainMem c { s with heur := heurL' } ⋆ R) ml')
                    (fun _ ⟨nv', ⟨⟩⟩ ml' ⟨heurL', hnle', hokL', hml'⟩ => by
                      wp_unfold
                      exact ih (nv', vv + 1#64, ()) ml' (by dsimp; omega)
                        ⟨heurL', by omega, by omega, hokL', hml'⟩)
                    (fun Jif hJif => by
                      wp_unfold
                      refine ⟨_, c0_load_arena_vals (i := vv <<< 1) (by dsimp; omega) hml, ?_⟩
                      refine ⟨fun _ => ?_, fun _ => ?_⟩
                      · obtain ⟨hst_h, hh1, _, hok_h1, hml1⟩ :=
                          pack_heur_store
                            (c0_store_arena_heap (i := nv) (vv.setWidth 32) (by dsimp; omega) hml)
                            { hokL with heap_len_arr := by simp [hhl] }
                        have hpl1 : hh1.pos.length = c.mv := hok_h1.pos_len
                        obtain ⟨hst_p, hh2, _, hok_h2, hml2⟩ :=
                          pack_heur_store
                            (c0_store_arena_pos (i := vv) (nv.setWidth 32) (by dsimp; omega) hml1)
                            { hok_h1 with pos_len := by simp [hpl1] }
                        have hn1 : (nv + 1).toNat = nv.toNat + 1 := by bv_omega
                        exact ⟨hst_h, hst_p, hJif (nv + 1, ()) _ ⟨hh2, by omega, hok_h2, hml2⟩⟩
                      · obtain ⟨hst_p, hh2, _, hok_h2, hml2⟩ :=
                          pack_heur_store
                            (c0_store_arena_pos (i := vv) 0xFFFFFFFF#32 (by dsimp; omega) hml)
                            { hokL with pos_len := by simp [hpl] }
                        exact ⟨hst_p, hJif (nv, ()) _ ⟨hh2, by omega, hok_h2, hml2⟩⟩)
                · obtain ⟨hst_hl, hh_hl, _, hok_hl, hml_hl⟩ :=
                    pack_heur_store (store_arena_heap_len nv.toNat (by omega) hml)
                      (heurOk_scalar hokL)
                  rw [bv_ofNat_toNat_eq] at hml_hl
                  refine ⟨hst_hl, ?_⟩
                  -- Loop 2: Floyd heapify (`while (s > 0ULL)`)
                  refine wp_loop_inv
                    (fun (sv, ()) ml2 => ∃ heurH : PlainHeur,
                      sv.toNat ≤ c.mv ∧ heurH.LengthsOk c ∧
                      (PlainMem c { s with heur := heurH } ⋆ R) ml2)
                    (fun (sv, ()) _ => sv.toNat)
                    (fun J2 hJ2 => by
                      c0_steps
                      have hs_le : (nv >>> 1).toNat ≤ c.mv := by
                        rw [bv64_shr1_toNat]; omega
                      exact hJ2 (nv >>> 1, ()) _ ⟨hh_hl, hs_le, hok_hl, hml_hl⟩)
                    (fun J2 ⟨sv, ⟨⟩⟩ ml2 ⟨heurH, hsle, hokH, hml2⟩ ih2 => by
                      c0_steps
                      · have hspos : 0 < sv.toNat := by bv_omega
                        have hsub : (sv - 1#64).toNat = sv.toNat - 1 := by bv_omega
                        have hhl : heurH.heap.length = c.mv := hokH.heap_len_arr
                        refine ⟨_, c0_load_arena_heap (i := sv - 1#64) (by dsimp; omega) hml2, ?_⟩
                        c0_call hDown
                        refine ⟨c, { s with heur := heurH }, R, rfl, hlen.with_heur hokH,
                          hml2, ?_⟩
                        intro heurH' mH' hokH' _ _ hmH'
                        exact ih2 (sv - 1#64, ()) mH' (by dsimp; omega)
                          ⟨heurH', by omega, hokH', hmH'⟩
                      · c0_steps
                        exact hJ () ml2 ⟨heurH, hokH, hml2⟩)))
          (fun Jd hJd => by
            c0_steps
            · exact hJd _ _ ⟨hs1, h1_ok, hm1⟩
            · exact hJd _ _ ⟨hs1, h1_ok, hm1⟩)
      · -- h->stable != 0ULL
        refine ⟨_, load_arena_search_ticks hm, _, load_arena_mode_tick_lim hm, ?_⟩
        refine ⟨fun _ => hQ s.heur m hlen.heur_ok hm, fun _ => ?_⟩
        obtain ⟨hok0, hs0, _, h0_ok, hm0⟩ :=
          pack_heur_store0 (store_arena_stable 0 hm) (heurOk_scalar hlen.heur_ok)
        refine ⟨hok0, _, load_arena_mv hm0, _, load_arena_switched hm0, ?_⟩
        c0_call hLog
        intro lg _ _
        wp_unfold
        refine ⟨_, load_arena_conflicts hm0, ?_⟩
        obtain ⟨hs1, h1, _, h1_ok, hm1⟩ :=
          pack_heur_store
            (store_arena_mode_confl_lim
              (hs0.conflicts + 1000 * ((hs0.switched + 2) >>> 1) * lg) hm0)
            (heurOk_scalar h0_ok)
        refine ⟨hs1, _, load_arena_search_ticks hm1, ?_⟩
        obtain ⟨hs2, h2, _, h2_ok, hm2⟩ :=
          pack_heur_store (store_arena_mode_saved_ticks h1.search_ticks hm1) (heurOk_scalar h1_ok)
        refine ⟨hs2, _, load_arena_q_last hm2, ?_⟩
        obtain ⟨hs3, h3, _, h3_ok, hm3⟩ :=
          pack_heur_store (store_arena_q_search_idx h2.q_last hm2) (heurOk_scalar h2_ok)
        refine ⟨hs3, ?_⟩
        refine wp_join_group
          (fun () mq => ∃ h4 : PlainHeur, h4.LengthsOk c ∧
            (PlainMem c { s with heur := h4 } ⋆ R) mq)
          (fun _ ⟨⟩ mq hmq => hJ () mq hmq)
          (fun Jq hJq => by
            wp_unfold
            refine ⟨_, load_arena_q_search_idx hm3, ?_⟩
            refine ⟨fun hlt => ?_, fun _ => hJq () _ ⟨h3, h3_ok, hm3⟩⟩
            have hql : h3.q_search_idx.toNat < c.mv := by
              change h3.q_search_idx.ult (BitVec.ofNat 64 c.mv) = true at hlt
              simp only [BitVec.ult, decide_eq_true_eq] at hlt; bv_omega
            have hqsl : h3.q_stamp.length = c.mv := h3_ok.q_stamp_len
            refine ⟨_, load_arena_q_stamp hm3, _, load_arena_q_search_idx hm3,
              _, c0_load_arena_q_stamp_arr (i := h3.q_search_idx) (by dsimp; omega) hm3, ?_⟩
            obtain ⟨hs4, h4, _, h4_ok, hm4⟩ :=
              pack_heur_store
                (store_arena_q_search_stamp
                  ((h3.q_stamp[h3.q_search_idx.toNat]'(by omega)).setWidth 64) hm3)
                (heurOk_scalar h3_ok)
            exact ⟨hs4, hJq () _ ⟨h4, h4_ok, hm4⟩⟩))

/-! ## 5. `plain_decide_wp` -/

theorem plain_decide_wp (Γ : Env)
    (hPop : ∀ args m Q X, plainHeapPopSpec args m Q X →
      Γ "plain_heap_pop" [i64] [i64] args m Q X)
    (hAssign : ∀ args m Q X, plainAssignSpec args m Q X →
      Γ "plain_assign" [i64, i32, i32] [] args m Q X) :
    ∀ args m Q X, plainDecideSpec args m Q X →
      Func.wp Γ plain_decide_body args m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hinv, hm, hQ⟩
  have hmv := c.hmv; unfold dimacsBound at hmv
  have hlen := hinv.core.lengths
  let h0 : PlainHeur := { s.heur with heap_len := (BitVec.ofNat 64 s.heur.heap_len).toNat }
  have hok0 : h0.LengthsOk c := heurOk_scalar hlen.heur_ok
  have hm0 : (PlainMem c { s with heur := h0 } ⋆ R) m := by
    rwa [plainMem_norm_heap_len]
  clear hm
  unfold Func.wp plain_decide_body; wp_unfold
  refine ⟨_, load_arena_values hm0, _, load_arena_phases_ptr hm0,
    _, load_arena_phases_target_ptr hm0, _, load_arena_heap_ptr hm0,
    _, load_arena_q_prev hm0, _, load_arena_q_stamp hm0, _, load_arena_mv hm0, ?_⟩
  -- Join after `if (h->stable != 0) ... else ...`
  refine wp_join_group
    (fun (chosen, ()) m1 => ∃ heur1 : PlainHeur,
      heur1.LengthsOk c ∧ heur1.rel_trigger = s.heur.rel_trigger ∧
      (chosen = 0xFFFFFFFFFFFFFFFF#64 ∨
        (chosen.toNat < c.mv ∧ s.vals[2 * chosen.toNat]?.getD 0#8 = 0#8)) ∧
      (PlainMem c { s with heur := heur1 } ⋆ R) m1)
    (fun _ ⟨chosen, ⟨⟩⟩ m1 ⟨heur1, hok1, hrt1, hch1, hm1⟩ => by
      wp_unfold
      -- Fallback linear scan `if (chosen == ~0) { while (v < mv) ... }`
      refine wp_join_group
        (fun (chosen2, ()) m2 => m2 = m1 ∧
          ((chosen2 = 0xFFFFFFFFFFFFFFFF#64 ∧ ∀ v < c.mv, s.vals[2 * v]?.getD 0#8 ≠ 0#8) ∨
           (chosen2 ≠ 0xFFFFFFFFFFFFFFFF#64 ∧ chosen2.toNat < c.mv ∧
             s.vals[2 * chosen2.toNat]?.getD 0#8 = 0#8)))
        (fun _ ⟨chosen2, ⟨⟩⟩ m2 ⟨hm2, hch2⟩ => by
          subst hm2
          wp_unfold
          refine ⟨fun hch_max => ?_, fun hch_ne => ?_⟩
          · -- chosen2 == ~0 -> return 0ULL
            rcases hch2 with ⟨_, hall⟩ | ⟨hne, _⟩
            · exact hQ 0#64 s.vals s.lvl s.rsns s.trl s.trail_pos s.trail_end s.cur_level
                s.unflushed heur1 m2 (hinv.with_heur hok1) (Or.inl rfl) hrt1
                (fun _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, hall⟩)
                (fun _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩) hm1
            · exact absurd hch_max hne
          · -- chosen2 != ~0 -> decide on `chosen2`
            rcases hch2 with ⟨heq, _⟩ | ⟨_, hclt, hun2⟩
            · exact absurd heq hch_ne
            have hte_lt : s.trail_end < c.mv :=
              hinv.core.trail_end_lt_of_unassigned (by omega) hun2
            have hcl_le : s.cur_level ≤ s.trail_end := hinv.core.cur_level_le
            have hphl : heur1.phases.length = c.mv := hok1.phases_len
            have hptl : heur1.phases_target.length = c.mv := hok1.phases_target_len
            refine ⟨_, load_arena_cur_level hm1, ?_⟩
            dsimp only
            obtain ⟨hok_cl, hm1'⟩ :=
              store_cur_level_with_heur (s := s) (h := heur1) (s.cur_level + 1) (by omega) hm1
            rw [show BitVec.ofNat 64 s.cur_level + 1 = BitVec.ofNat 64 (s.cur_level + 1) from by
              rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, bv_add_ofNat]]
            refine ⟨hok_cl, _, c0_load_arena_phases (i := chosen2) (by dsimp; omega) hm1', ?_⟩
            -- Join on `dph` after `if (stable != 0 && ptgt[chosen] != 0) dph = ptgt[chosen]`
            refine wp_join_group
              (fun (_dph, ()) m3 =>
                (PlainMem c { s with cur_level := s.cur_level + 1, heur := heur1 } ⋆ R) m3)
              (fun _ ⟨dph, ⟨⟩⟩ m3 hm3 => by
                wp_unfold
                -- Join on `lit` after `(dph < 0) ? ((chosen << 1) | 1) : (chosen << 1)`
                refine wp_join_group
                  (fun (lit, ()) m4 => m4 = m3 ∧ lit.toNat < 2 * c.mv ∧
                    lit.toNat / 2 = chosen2.toNat)
                  (fun _ ⟨lit, ⟨⟩⟩ m4 ⟨hm4, hlit_lt, hlit_v⟩ => by
                    subst hm4
                    have hcore1 : PlainCoreInv c F0 { s with heur := heur1 } :=
                      hinv.core.with_heur hok1
                    have hun_lit : s.vals[lit.toNat]?.getD 0#8 = 0#8 := by
                      rw [hinv.core.vals_zero_iff hlit_lt, hlit_v]
                      have h0' := (hinv.core.vals_zero_iff
                        (by omega : 2 * chosen2.toNat < 2 * c.mv)).mp hun2
                      simpa using h0'
                    c0_steps
                    c0_call hAssign
                    let s_pre : PlainState :=
                      { s with cur_level := s.cur_level + 1, heur := heur1 }
                    have hpre_len : s_pre.LengthsOk c := { hlen with heur_ok := hok1 }
                    refine ⟨c, s_pre, R, rfl, hpre_len, by dsimp [s_pre]; omega, hm3, ?_⟩
                    have hnot_oob : ¬ (c.mv ≤ lit.toNat / 2 ∨ c.mv ≤ s_pre.trail_end) := by
                      dsimp [s_pre]; omega
                    simp only [hnot_oob, ↓reduceIte]
                    intro phases' m5 hph' _ hm5
                    have hcl_ne0 : s_pre.cur_level ≠ 0 := by dsimp [s_pre]; omega
                    simp only [hcl_ne0, ↓reduceIte] at hm5
                    have hcore' : PlainCoreInv c F0
                        { s with
                          vals := (s.vals.set lit.toNat 1#8).set (lit.toNat ^^^ 1) 0xFF#8
                          lvl := s.lvl.set (lit.toNat / 2) (BitVec.ofNat 32 (s.cur_level + 1))
                          rsns := s.rsns.set (lit.toNat / 2) 0xFFFFFFFF#32
                          trl := s.trl.set s.trail_end lit
                          trail_pos := s.trail_pos.set (lit.toNat / 2)
                            (BitVec.ofNat 32 s.trail_end)
                          trail_end := s.trail_end + 1
                          cur_level := s.cur_level + 1
                          heur := { heur1 with phases := phases' } } :=
                      decide_assign_preserves_core hcore1 hlit_lt hph' hun_lit
                    c0_steps
                    exact hQ 1#64 _ _ _ _ _ _ _ _ _ m5 ⟨hcore', hinv.marks⟩ (Or.inr rfl) hrt1
                      (fun h => by cases h)
                      (fun hall => absurd hun2 (hall chosen2.toNat hclt)) hm5)
                  (fun Jl hJl => by
                    c0_steps
                    · exact hJl _ m3 ⟨rfl, by rw [bv32_lit_odd_toNat (by omega)]; omega,
                        by rw [bv32_lit_odd_toNat (by omega)]; omega⟩
                    · exact hJl _ m3 ⟨rfl, by rw [bv32_lit_even_toNat (by omega)]; omega,
                        by rw [bv32_lit_even_toNat (by omega)]; omega⟩))
              (fun Jd hJd => by
                c0_steps
                all_goals exact hJd _ _ hm1'))
        (fun Jf hJf => by
          wp_unfold
          refine ⟨fun hch_eq => ?_, fun hch_ne => ?_⟩
          · -- chosen == ~0: linear scan `while (v < mv)` with break block `(chosen, v, ())`
            refine wp_loop_break_group
              (fun ((ch2, _vv, ()) : Tup Val [i64, i64]) mb => mb = m1 ∧
                ((ch2 = 0xFFFFFFFFFFFFFFFF#64 ∧ ∀ v < c.mv, s.vals[2 * v]?.getD 0#8 ≠ 0#8) ∨
                 (ch2 ≠ 0xFFFFFFFFFFFFFFFF#64 ∧ ch2.toNat < c.mv ∧
                   s.vals[2 * ch2.toNat]?.getD 0#8 = 0#8)))
              (fun rem ((vv, ()) : Tup Val [i64]) ml => ml = m1 ∧ vv.toNat ≤ c.mv ∧
                rem = c.mv - vv.toNat ∧ ∀ w < vv.toNat, s.vals[2 * w]?.getD 0#8 ≠ 0#8)
              (fun _ ⟨ch2, _, ⟨⟩⟩ mb ⟨hmb, hch⟩ => hJf (ch2, ()) mb ⟨hmb, hch⟩)
              (fun B _ rem ⟨vv, ⟨⟩⟩ ml hB ih ⟨hml, hvle, hrem, hall⟩ => by
                subst hml
                c0_steps
                · have hvlt : vv.toNat < c.mv := by bv_omega
                  have h2v : (vv <<< 1).toNat = 2 * vv.toNat := bv64_shl1_toNat (by omega)
                  have hvl : s.vals.length = 2 * c.mv := hlen.vals_len
                  wp_unfold
                  refine ⟨_, c0_load_arena_vals (i := vv <<< 1) (by dsimp; omega) hm1, ?_⟩
                  refine ⟨fun hz => ?_, fun hnz => ?_⟩
                  · have hne_max : vv ≠ 0xFFFFFFFFFFFFFFFF#64 := by bv_omega
                    have hveq : s.vals[(vv <<< 1).toNat]'(by omega) = 0#8 :=
                      bv8_sext32_eq_zero hz
                    have hv0 : s.vals[2 * vv.toNat]?.getD 0#8 = 0#8 := by
                      rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
                      simpa [h2v] using hveq
                    exact hB (vv, vv, ()) ml ⟨rfl, Or.inr ⟨hne_max, hvlt, hv0⟩⟩
                  · have hv1 : (vv + 1#64).toNat = vv.toNat + 1 := by bv_omega
                    have hvne : s.vals[(vv <<< 1).toNat]'(by omega) ≠ 0#8 := fun he =>
                      hnz (by change (s.vals[(vv <<< 1).toNat]'(by omega)).signExtend 32 =
                        (0#8 : BitVec 8).signExtend 32; rw [he])
                    have hvnz : s.vals[2 * vv.toNat]?.getD 0#8 ≠ 0#8 := by
                      rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
                      simpa [h2v] using hvne
                    exact ih (c.mv - (vv.toNat + 1)) (vv + 1#64, ()) ml (by omega)
                      ⟨rfl, by omega, by omega, fun w hw => by
                        by_cases hwe : w = vv.toNat
                        · subst w; exact hvnz
                        · exact hall w (by omega)⟩
                · have hveq : vv.toNat = c.mv := by bv_omega
                  exact hB (chosen, vv, ()) ml
                    ⟨rfl, Or.inl ⟨hch_eq, hveq ▸ hall⟩⟩)
              (fun _ _ _ hL => by
                c0_steps
                exact hL c.mv (0#64, ()) m1
                  ⟨rfl, Nat.zero_le _, by simp, fun _ h => by bv_omega⟩)
          · rcases hch1 with heq | ⟨hclt, hun⟩
            · exact absurd heq hch_ne
            · have hne : chosen ≠ 0xFFFFFFFFFFFFFFFF#64 := by bv_omega
              exact hJf (chosen, ()) m1 ⟨rfl, Or.inr ⟨hne, hclt, hun⟩⟩))
    (fun J hJ => by
      wp_unfold
      refine ⟨_, load_arena_stable hm0, ?_⟩
      refine ⟨fun _ => ?_, fun _ => ?_⟩
      · -- h->stable != 0: VSIDS heap pop loop with break block `(chosen, ())`
        refine wp_loop_break_group
          (fun ((chosen, ()) : Tup Val [i64]) mb => ∃ heur1 : PlainHeur,
            heur1.LengthsOk c ∧ heur1.rel_trigger = s.heur.rel_trigger ∧
            (chosen = 0xFFFFFFFFFFFFFFFF#64 ∨
              (chosen.toNat < c.mv ∧ s.vals[2 * chosen.toNat]?.getD 0#8 = 0#8)) ∧
            (PlainMem c { s with heur := heur1 } ⋆ R) mb)
          (fun rem () ml => ∃ heurL : PlainHeur,
            rem = heurL.heap_len ∧ heurL.heap_len < 2 ^ 64 ∧
            heurL.LengthsOk c ∧ heurL.rel_trigger = s.heur.rel_trigger ∧
            (PlainMem c { s with heur := heurL } ⋆ R) ml)
          (fun _ ⟨chosen, ⟨⟩⟩ mb hres => hJ (chosen, ()) mb hres)
          (fun B _ rem ⟨⟩ ml hB ih ⟨heurL, hrem, hhl_lt, hokL, hrtL, hml⟩ => by
            c0_steps
            · have hpos : 0 < heurL.heap_len := by bv_omega
              have hle : heurL.heap_len ≤ c.mv := by bv_omega
              have hhl : heurL.heap.length = c.mv := hokL.heap_len_arr
              wp_unfold
              refine ⟨_, c0_load_arena_heap_add_zero (by dsimp; omega) hml, ?_⟩
              refine ⟨fun _ =>
                  hB (0xFFFFFFFFFFFFFFFF#64, ()) ml ⟨heurL, hokL, hrtL, Or.inl rfl, hml⟩,
                fun hlt => ?_⟩
              have htlt : (heurL.heap[0]'(by omega)).toNat < c.mv := by
                simp only [BitVec.ule, decide_eq_false_iff_not,
                  BitVec.toNat_setWidth, BitVec.toNat_ofNat] at hlt
                omega
              have h2t : ((heurL.heap[0]'(by omega)).setWidth 64 <<< 1).toNat =
                  2 * (heurL.heap[0]'(by omega)).toNat := by bv_omega
              have hvl : s.vals.length = 2 * c.mv := hlen.vals_len
              refine ⟨_, c0_load_arena_vals (i := (heurL.heap[0]'(by omega)).setWidth 64 <<< 1)
                (by dsimp; omega) hml, ?_⟩
              refine ⟨fun hz => ?_, fun _ => ?_⟩
              · have htz : s.vals[2 * (heurL.heap[0]'(by omega)).toNat]?.getD 0#8 = 0#8 := by
                  rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
                  simpa [h2t] using bv8_sext32_eq_zero hz
                exact hB _ ml ⟨heurL, hokL, hrtL,
                  Or.inr ⟨by bv_omega, by
                    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]; exact htz⟩, hml⟩
              · c0_call hPop
                refine ⟨c, { s with heur := heurL }, R, rfl, hlen.with_heur hokL, hml, ?_⟩
                intro _ heurL' mL' _ hokL' hdec hrt' hmL'
                have hhl' : heurL'.heap_len = heurL.heap_len - 1 := hdec ⟨hpos, hle⟩
                c0_steps
                exact ih heurL'.heap_len () mL' (by omega)
                  ⟨heurL', rfl, by omega, hokL', hrt'.trans hrtL, hmL'⟩
            · exact hB (0xFFFFFFFFFFFFFFFF#64, ()) ml ⟨heurL, hokL, hrtL, Or.inl rfl, hml⟩
            · exact hB (0xFFFFFFFFFFFFFFFF#64, ()) ml ⟨heurL, hokL, hrtL, Or.inl rfl, hml⟩)
          (fun _ _ _ hL => by
            c0_steps
            exact hL h0.heap_len () m ⟨h0, rfl, (BitVec.ofNat 64 s.heur.heap_len).isLt,
              hok0, rfl, hm0⟩)
      · -- h->stable == 0: VMTF 2-pass queue search
        refine ⟨_, load_arena_q_search_idx hm0, ?_⟩
        refine wp_loop_break_group
          (fun ((chosen, cur, _st, ()) : Tup Val [i64, i64, i64]) mb => mb = m ∧
            (chosen = 0xFFFFFFFFFFFFFFFF#64 ∨
              (chosen.toNat < c.mv ∧ s.vals[2 * chosen.toNat]?.getD 0#8 = 0#8)))
          (fun rem ((cur, steps, ()) : Tup Val [i64, i64]) ml => ml = m ∧
            steps.toNat ≤ c.mv ∧ rem = c.mv - steps.toNat)
          (fun _ ⟨chosen, cur, _st, ⟨⟩⟩ mb ⟨hmb, hch⟩ => by
            subst mb
            refine wp_join_group
              (fun ((chosen_f, _cur_f, _st_f, ()) : Tup Val [i64, i64, i64]) mf =>
                ∃ heur1 : PlainHeur, heur1.LengthsOk c ∧
                  heur1.rel_trigger = s.heur.rel_trigger ∧
                  (chosen_f = 0xFFFFFFFFFFFFFFFF#64 ∨
                    (chosen_f.toNat < c.mv ∧ s.vals[2 * chosen_f.toNat]?.getD 0#8 = 0#8)) ∧
                  (PlainMem c { s with heur := heur1 } ⋆ R) mf)
              (fun _ ⟨chosen_f, _, _, ⟨⟩⟩ mf hres => hJ (chosen_f, ()) mf hres)
              (fun Jv1 hJv1 => by
                wp_unfold
                refine ⟨fun hclt_b => ?_, fun _ => ?_⟩
                · have hclt : cur.toNat < c.mv := by
                    change cur.ult (BitVec.ofNat 64 c.mv) = true at hclt_b
                    simp only [BitVec.ult, decide_eq_true_eq] at hclt_b; bv_omega
                  obtain ⟨hs1, h1, hh1, hok1, hm1⟩ :=
                    pack_heur_store (store_arena_q_search_idx cur hm0) (heurOk_scalar hok0)
                  have hqsl1 : h1.q_stamp.length = c.mv := hok1.q_stamp_len
                  refine ⟨hs1, _, c0_load_arena_q_stamp_arr (i := cur) (by dsimp; omega) hm1, ?_⟩
                  obtain ⟨hs2, h2, hh2, hok2, hm2⟩ :=
                    pack_heur_store
                      (store_arena_q_search_stamp
                        ((h1.q_stamp[cur.toNat]'(by omega)).setWidth 64) hm1)
                      (heurOk_scalar hok1)
                  have hrt2 : h2.rel_trigger = s.heur.rel_trigger := by
                    rw [hh2]; dsimp; rw [hh1]
                  exact ⟨hs2, hJv1 (chosen, cur, _st, ()) _ ⟨h2, hok2, hrt2, hch, hm2⟩⟩
                · refine ⟨_, load_arena_q_last hm0, ?_⟩
                  refine wp_loop_break_group
                    (fun ((chosen', cur', _st', ()) : Tup Val [i64, i64, i64]) mb2 => mb2 = m ∧
                      (chosen' = 0xFFFFFFFFFFFFFFFF#64 ∨
                        (chosen'.toNat < c.mv ∧ s.vals[2 * chosen'.toNat]?.getD 0#8 = 0#8)))
                    (fun rem ((cur', steps', ()) : Tup Val [i64, i64]) ml2 => ml2 = m ∧
                      steps'.toNat ≤ c.mv ∧ rem = c.mv - steps'.toNat)
                    (fun _ ⟨chosen', cur', _st', ⟨⟩⟩ mb2 ⟨hmb2, hch'⟩ => by
                      subst mb2
                      refine wp_join_group
                        (fun () mf => ∃ heur1 : PlainHeur, heur1.LengthsOk c ∧
                          heur1.rel_trigger = s.heur.rel_trigger ∧
                          (PlainMem c { s with heur := heur1 } ⋆ R) mf)
                        (fun _ ⟨⟩ mf ⟨heur1, hok1, hrt1, hmf⟩ =>
                          hJv1 (chosen', cur', _st', ()) mf ⟨heur1, hok1, hrt1, hch', hmf⟩)
                        (fun Jv2 hJv2 => by
                          wp_unfold
                          refine ⟨fun hclt_b => ?_, fun _ => hJv2 () m ⟨h0, hok0, rfl, hm0⟩⟩
                          have hclt : cur'.toNat < c.mv := by
                            change cur'.ult (BitVec.ofNat 64 c.mv) = true at hclt_b
                            simp only [BitVec.ult, decide_eq_true_eq] at hclt_b; bv_omega
                          obtain ⟨hs1, h1, hh1, hok1, hm1⟩ :=
                            pack_heur_store (store_arena_q_search_idx cur' hm0) (heurOk_scalar hok0)
                          have hqsl1 : h1.q_stamp.length = c.mv := hok1.q_stamp_len
                          refine ⟨hs1, _, c0_load_arena_q_stamp_arr (i := cur')
                            (by dsimp; omega) hm1, ?_⟩
                          obtain ⟨hs2, h2, hh2, hok2, hm2⟩ :=
                            pack_heur_store
                              (store_arena_q_search_stamp
                                ((h1.q_stamp[cur'.toNat]'(by omega)).setWidth 64) hm1)
                              (heurOk_scalar hok1)
                          have hrt2 : h2.rel_trigger = s.heur.rel_trigger := by
                            rw [hh2]; dsimp; rw [hh1]
                          exact ⟨hs2, hJv2 () _ ⟨h2, hok2, hrt2, hm2⟩⟩))
                    (fun B _ rem ⟨cur', steps', ⟨⟩⟩ ml2 hB ih ⟨hml2, hsle, hrem⟩ => by
                      subst ml2
                      c0_steps
                      · have hclt : cur'.toNat < c.mv := by bv_omega
                        have hslt : steps'.toNat < c.mv := by bv_omega
                        have h2c : (cur' <<< 1).toNat = 2 * cur'.toNat := bv64_shl1_toNat (by omega)
                        have hvl : s.vals.length = 2 * c.mv := hlen.vals_len
                        have hqpl : h0.q_prev.length = c.mv := hok0.q_prev_len
                        wp_unfold
                        refine ⟨_, c0_load_arena_vals (i := cur' <<< 1) (by dsimp; omega) hm0, ?_⟩
                        refine ⟨fun hz => ?_, fun _ => ?_⟩
                        · have hcz : s.vals[2 * cur'.toNat]?.getD 0#8 = 0#8 := by
                            rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
                            simpa [h2c] using bv8_sext32_eq_zero hz
                          exact hB _ m ⟨rfl, Or.inr ⟨hclt, hcz⟩⟩
                        · have hs1 : (steps' + 1).toNat = steps'.toNat + 1 := by bv_omega
                          refine ⟨_, c0_load_arena_q_prev_arr (i := cur')
                            (by dsimp; omega) hm0, ?_⟩
                          exact ih (c.mv - (steps'.toNat + 1)) _ m (by omega)
                            ⟨rfl, by omega, by omega⟩
                      · exact hB _ m ⟨rfl, hch⟩
                      · exact hB _ m ⟨rfl, hch⟩)
                    (fun _ _ _ hL => by
                      c0_steps
                      exact hL c.mv (_, 0#64, ()) m ⟨rfl, Nat.zero_le _, by simp⟩)))
          (fun B _ rem ⟨cur, steps, ⟨⟩⟩ ml hB ih ⟨hml, hsle, hrem⟩ => by
            subst ml
            c0_steps
            · have hclt : cur.toNat < c.mv := by bv_omega
              have hslt : steps.toNat < c.mv := by bv_omega
              have h2c : (cur <<< 1).toNat = 2 * cur.toNat := bv64_shl1_toNat (by omega)
              have hvl : s.vals.length = 2 * c.mv := hlen.vals_len
              have hqpl : h0.q_prev.length = c.mv := hok0.q_prev_len
              wp_unfold
              refine ⟨_, c0_load_arena_vals (i := cur <<< 1) (by dsimp; omega) hm0, ?_⟩
              refine ⟨fun hz => ?_, fun _ => ?_⟩
              · have hcz : s.vals[2 * cur.toNat]?.getD 0#8 = 0#8 := by
                  rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
                  simpa [h2c] using bv8_sext32_eq_zero hz
                exact hB _ m ⟨rfl, Or.inr ⟨hclt, hcz⟩⟩
              · have hs1 : (steps + 1).toNat = steps.toNat + 1 := by bv_omega
                refine ⟨_, c0_load_arena_q_prev_arr (i := cur) (by dsimp; omega) hm0, ?_⟩
                exact ih (c.mv - (steps.toNat + 1)) _ m (by omega)
                  ⟨rfl, by omega, by omega⟩
            · exact hB _ m ⟨rfl, Or.inl rfl⟩
            · exact hB _ m ⟨rfl, Or.inl rfl⟩)
          (fun _ _ _ hL => by
            c0_steps
            exact hL c.mv (_, 0#64, ()) m ⟨rfl, Nat.zero_le _, by simp⟩))

end SearchProofs

end LeanQbe.T.Examples.Kissat.Plain
