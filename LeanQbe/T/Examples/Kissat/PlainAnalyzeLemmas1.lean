module

public import LeanQbe.T.Examples.Kissat.PlainSpec

/-!
# Kissat `D-Plain` Conflict-Analysis Helpers & 1-UIP Resolvent Theory (Part 1)

Builds on `PlainSpec` to provide:
1. Scoped `PlainAnalyzeTactics` adapters for `PlainMem` analysis loads/stores and bitwise leaves.
2. Arena usage-bump preservation (`arenaBumpUsage_preserves_core`) for `plain_analyze_rsn`.
3. Pure 1-UIP semantic resolvent theory (`lowerLits`, `curTrailIdxs`, `curLits`,
   `activeResolvent`, `LowerInv`, `MarksCov`, `analyzeLit_preserves`, `analyzeRsn_preserves`,
   `clear_marks_restores_marksClear`, `tmp_take_eq_cons_lowerLits`, `swap_tmp_props`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Plain

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.C0Step
open Kraken.Bedrock2.Test

/-! ## 1. Scoped tactic helpers (`PlainAnalyzeTactics`) -/

namespace PlainAnalyzeTactics

private theorem mask27_bit : ∀ i : Fin 32, (0x07FFFFFF#32)[i.val] = decide (i.val < 27) := by decide
private theorem mask19_bit : ∀ i : Fin 32, (0x00080000#32)[i.val] = decide (i.val = 19) := by decide
private theorem mask23_bit : ∀ i : Fin 32, (0x00800000#32)[i.val] = decide (i.val = 23) := by decide
private theorem mask31_bit : ∀ i : Fin 32, (0x80000000#32)[i.val] = decide (i.val = 31) := by decide
private theorem maskLo31_bit :
    ∀ i : Fin 32, (0x7FFFFFFF#32)[i.val] = decide (i.val < 31) := by decide

theorem bv32_mask_usage_garb (hdr u : BitVec 32) :
    (((hdr &&& 0x07FFFFFF#32) ||| (u <<< 27)) &&& 0x00080000#32) = (hdr &&& 0x00080000#32) := by
  ext i hi
  simp only [BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_shiftLeft,
    mask27_bit ⟨i, hi⟩, mask19_bit ⟨i, hi⟩]
  by_cases h19 : i = 19 <;> simp [h19]

theorem bv32_mask_usage_shrk (hdr u : BitVec 32) :
    (((hdr &&& 0x07FFFFFF#32) ||| (u <<< 27)) &&& 0x00800000#32) = (hdr &&& 0x00800000#32) := by
  ext i hi
  simp only [BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_shiftLeft,
    mask27_bit ⟨i, hi⟩, mask23_bit ⟨i, hi⟩]
  by_cases h23 : i = 23 <;> simp [h23]

theorem bin_rsn_mask_props {l : BitVec 32} (hl : l.toNat < 2 ^ 31 - 1) :
    let rsn : BitVec 32 := (l &&& 0x7FFFFFFF#32) ||| 0x80000000#32
    rsn ≠ 0xFFFFFFFF#32 ∧ (rsn &&& 0x80000000#32) ≠ 0#32 ∧
      (rsn &&& 0x7FFFFFFF#32).toNat = l.toNat := by
  intro rsn
  have hbit31 : l[31] = false := by
    rw [BitVec.getElem_eq_testBit_toNat, Nat.testBit, Nat.shiftRight_eq_div_pow,
      Nat.div_eq_of_lt (by omega : l.toNat < 2 ^ 31)]; rfl
  have hand_hi : (rsn &&& 0x80000000#32) = 0x80000000#32 := by
    ext i hi
    simp only [rsn, BitVec.getElem_and, BitVec.getElem_or, mask31_bit ⟨i, hi⟩]
    by_cases h31 : i = 31 <;> simp [h31]
  have hand_lo : (rsn &&& 0x7FFFFFFF#32) = l := by
    ext i hi
    simp only [rsn, BitVec.getElem_and, BitVec.getElem_or, mask31_bit ⟨i, hi⟩, maskLo31_bit ⟨i, hi⟩]
    by_cases h31 : i = 31
    · subst h31; simp [hbit31]
    · simp [h31, show i < 31 by omega]
  refine ⟨?_, ?_, congrArg BitVec.toNat hand_lo⟩
  · intro heq
    have := congrArg (fun x => x &&& 0x7FFFFFFF#32) heq
    rw [hand_lo] at this
    have hnat := congrArg BitVec.toNat this
    have hff : (0xFFFFFFFF#32 &&& 0x7FFFFFFF#32).toNat = 2 ^ 31 - 1 := rfl
    rw [hff] at hnat
    omega
  · rw [hand_hi]; decide

attribute [scoped bv_c0] bv32_lshr_1

@[scoped bv_c0] theorem bv32_mask_lo31_toNat (x : BitVec 32) :
    (x &&& 0x7FFFFFFF#32).toNat = x.toNat % 2 ^ 31 := by
  simpa [BitVec.toNat_and, show (0x7FFFFFFF#32).toNat = 2 ^ 31 - 1 from rfl] using
    Nat.and_two_pow_sub_one_eq_mod x.toNat 31

@[scoped bv_c0] theorem bv32_mask_glue_toNat (x : BitVec 32) :
    (x &&& 0x7FFFF#32).toNat = x.toNat % 2 ^ 19 := by
  simpa [BitVec.toNat_and, show (0x7FFFF#32).toNat = 2 ^ 19 - 1 from rfl] using
    Nat.and_two_pow_sub_one_eq_mod x.toNat 19

end PlainAnalyzeTactics

open PlainAnalyzeTactics
open scoped PlainAnalyzeTactics

/-! ## 2. Private list-counting helpers -/

private theorem filter_length_flip_one {α : Type} (p p' : α → Bool) (k : α) :
    ∀ (xs : List α), xs.Nodup → k ∈ xs →
      p k = false → p' k = true →
      (∀ x ∈ xs, x ≠ k → p' x = p x) →
      (xs.filter p').length = (xs.filter p).length + 1
  | [], _, hmem, _, _, _ => by simp at hmem
  | x :: xs, hnd, hmem, hpk, hp'k, hagree => by
    rw [List.nodup_cons] at hnd
    rcases List.mem_cons.mp hmem with rfl | hmem'
    · have hfeq : xs.filter p' = xs.filter p := List.filter_congr fun y hy =>
        hagree y (List.mem_cons_of_mem _ hy) (fun heq => hnd.1 (heq ▸ hy))
      simp [hpk, hp'k, hfeq]
    · have hne : x ≠ k := fun heq => hnd.1 (heq ▸ hmem')
      have hx := hagree x List.mem_cons_self hne
      have ih := filter_length_flip_one p p' k xs hnd.2 hmem' hpk hp'k
        fun y hy => hagree y (List.mem_cons_of_mem _ hy)
      cases hp : p x <;> simp [hx, hp, ih] <;> omega

private theorem filter_length_eq_zero_of_false {α : Type} {p : α → Bool} {xs : List α}
    (h : ∀ x ∈ xs, p x = false) : (xs.filter p).length = 0 := by
  have : xs.filter p = [] := List.filter_eq_nil_iff.mpr fun x hx => by simp [h x hx]
  simp [this]

private theorem nodup_length_le_of_subset {α : Type} [DecidableEq α] :
    ∀ {xs ys : List α}, xs.Nodup → (∀ x ∈ xs, x ∈ ys) → xs.length ≤ ys.length
  | [], _, _, _ => Nat.zero_le _
  | x :: xs, ys, hnd, hsub => by
    rw [List.nodup_cons] at hnd
    have hx : x ∈ ys := hsub x List.mem_cons_self
    have hle := nodup_length_le_of_subset hnd.2 fun y hy =>
      (List.mem_erase_of_ne (by rintro rfl; exact hnd.1 hy)).mpr
        (hsub y (List.mem_cons_of_mem _ hy))
    have hlen := List.length_erase_of_mem hx
    have hpos := List.length_pos_of_mem hx
    simp only [List.length_cons]; omega

private theorem nodup_length_eq_of_bij {xs ys : List Nat} (f : Nat → Nat)
    (hxs : xs.Nodup) (hys : ys.Nodup)
    (hmap : ∀ x ∈ xs, f x ∈ ys)
    (hinj : ∀ x1 ∈ xs, ∀ x2 ∈ xs, f x1 = f x2 → x1 = x2)
    (hsurj : ∀ y ∈ ys, ∃ x ∈ xs, f x = y) : xs.length = ys.length := by
  have h1 : (xs.map f).length ≤ ys.length :=
    nodup_length_le_of_subset (nodup_map_of_inj hxs hinj) fun y hy => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy; exact hmap x hx
  have h2 : ys.length ≤ (xs.map f).length :=
    nodup_length_le_of_subset hys fun y hy => by
      obtain ⟨x, hx, rfl⟩ := hsurj y hy; exact List.mem_map_of_mem hx
  rw [List.length_map] at h1 h2; omega

private theorem filter_length_add_of_disj {α : Type} (p1 p2 : α → Bool) :
    ∀ (xs : List α), (∀ x ∈ xs, ¬ (p1 x = true ∧ p2 x = true)) →
      (xs.filter fun x => p1 x || p2 x).length = (xs.filter p1).length + (xs.filter p2).length
  | [], _ => rfl
  | x :: xs, hdisj => by
    have htail := filter_length_add_of_disj p1 p2 xs fun y hy => hdisj y (List.mem_cons_of_mem _ hy)
    have hx := hdisj x List.mem_cons_self
    cases hp1 : p1 x <;> cases hp2 : p2 x <;> simp_all <;> omega

private theorem range_succ_filter (n : Nat) (p : Nat → Bool) :
    (List.range (n + 1)).filter p = (List.range n).filter p ++ if p n then [n] else [] := by
  rw [List.range_succ, List.filter_append]
  cases hp : p n <;> simp [hp]

/-! ## 3. Arena clause usage-bump preservation (`plain_analyze_rsn`) -/

/-- Updating bits `27..31` (usage count) of header word `ar[cref]` for `cref ∈ arenaClauseRefs s`
preserves `arenaClauseRefs`, `arenaClauseSize`, `arenaClauseGarb`, `arenaClauseLits`, and
`PlainCoreInv`. -/
theorem arenaBumpUsage_preserves_core {c : PlainCfg} {F0 : CNF Nat} {s : PlainState}
    (hcore : PlainCoreInv c F0 s) {cref : Nat} (hcref : cref ∈ arenaClauseRefs s)
    (u : BitVec 32) :
    let hdr := s.arena[cref]?.getD 0#32
    let hdr' := (hdr &&& 0x07FFFFFF#32) ||| (u <<< 27)
    let s' : PlainState := { s with arena := s.arena.set cref hdr' }
    PlainCoreInv c F0 s' ∧
    arenaClauseRefs s' = arenaClauseRefs s ∧
    (∀ r ∈ arenaClauseRefs s, arenaClauseSize s' r = arenaClauseSize s r ∧
      arenaClauseGarb s' r = arenaClauseGarb s r ∧
      arenaClauseLits s' r = arenaClauseLits s r) := by
  intro hdr hdr' s'
  have hlen := hcore.lengths
  have hcref_wf := hcore.arena.refs_wf cref hcref
  have hcref_lt : cref < s.arena.length := by
    have := hlen.arena_len_arr; have := hlen.arena_len_le; omega
  have hgarb_hdr : (hdr' &&& 0x00080000#32) = (hdr &&& 0x00080000#32) :=
    bv32_mask_usage_garb hdr u
  have hshrk_hdr : (hdr' &&& 0x00800000#32) = (hdr &&& 0x00800000#32) :=
    bv32_mask_usage_shrk hdr u
  have har_self : s'.arena[cref]? = some hdr' := List.getElem?_set_self hcref_lt
  have har_ne : ∀ k, k ≠ cref → s'.arena[k]? = s.arena[k]? := fun k hk =>
    List.getElem?_set_ne (Ne.symm hk)
  have hnxt_eq : ∀ r ∈ arenaClauseRefs s,
      arenaNextOff s'.arena s.arena_len r = arenaNextOff s.arena s.arena_len r := by
    intro r hr
    by_cases hrc : r = cref
    · subst r
      unfold arenaNextOff
      have hnot : ¬ (cref + 3 > s.arena_len) := by omega
      simp only [hnot, ↓reduceIte, har_self, Option.getD_some, har_ne (cref + 2) (by omega)]
      split
      · rfl
      · rename_i hle_p
        change (if (hdr' &&& 0x00800000#32) ≠ 0#32 then _ else _) =
          if (hdr &&& 0x00800000#32) ≠ 0#32 then _ else _
        rw [hshrk_hdr]
        split
        · exact arenaSkipShrk_congr fun k hk1 _ => har_ne k (by omega)
        · rfl
    · rcases Nat.lt_or_gt_of_ne hrc with hlt | hgt
      · have hdisj := arenaScanRefs_disjoint hr hcref hlt
        have hr_wf := hcore.arena.refs_wf r hr
        exact arenaNextOff_congr_block (har_ne r hrc) (har_ne (r + 2) (by omega))
          fun k _ hk2 => har_ne k (by omega)
      · exact arenaNextOff_congr_block (har_ne r hrc) (har_ne (r + 2) (by omega))
          fun k hk1 _ => har_ne k (by omega)
  have hrefs : arenaClauseRefs s' = arenaClauseRefs s := arenaClauseRefs_congr rfl hnxt_eq
  have hprops : ∀ r ∈ arenaClauseRefs s, arenaClauseSize s' r = arenaClauseSize s r ∧
      arenaClauseGarb s' r = arenaClauseGarb s r ∧
      arenaClauseLits s' r = arenaClauseLits s r := by
    intro r hr
    have hr_wf := hcore.arena.refs_wf r hr
    have hnot_in : ∀ k, r + 2 ≤ k → k < r + 3 + arenaClauseSize s r → k ≠ cref := by
      intro k hk1 hk2 heq; subst k
      by_cases hrc : r = cref
      · omega
      · rcases Nat.lt_or_gt_of_ne hrc with hlt | hgt
        · have := hcore.arena.disjoint hr hcref hlt; omega
        · omega
    have hsz : arenaClauseSize s' r = arenaClauseSize s r := by
      unfold arenaClauseSize; rw [har_ne (r + 2) (hnot_in (r + 2) (Nat.le_refl _) (by omega))]
    have hgarb : arenaClauseGarb s' r = arenaClauseGarb s r := by
      unfold arenaClauseGarb arenaHdr
      by_cases hrc : r = cref
      · subst r; rw [har_self, Option.getD_some]; change (hdr' &&& 0x00080000#32 != 0#32) = _
        rw [hgarb_hdr]
      · rw [har_ne r hrc]
    have hlits : arenaClauseLits s' r = arenaClauseLits s r := by
      have hbd1 : r + 3 + arenaClauseSize s r ≤ s.arena.length := by
        have := hlen.arena_len_arr; have := hlen.arena_len_le; omega
      have hbd2 : r + 3 + arenaClauseSize s r ≤ s'.arena.length := by
        simpa [s'] using hbd1
      unfold arenaClauseLits; rw [hsz]
      apply List.ext_getElem
      · simp only [List.length_map, List.length_take, List.length_drop]
        rw [Nat.min_eq_left (by omega), Nat.min_eq_left (by omega)]
      · intro k hk1 _
        simp only [List.getElem_map, List.getElem_take, List.getElem_drop]
        have hks : k < arenaClauseSize s r := by
          simp only [List.length_map, List.length_take, List.length_drop] at hk1; omega
        have hopt := har_ne (r + 3 + k) (hnot_in (r + 3 + k) (by omega) (by omega))
        rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at hopt
        exact congrArg BitVec.toNat (Option.some.inj hopt)
    exact ⟨hsz, hgarb, hlits⟩
  have hlen' : s'.LengthsOk c := { hlen with arena_len_arr := by simp [s', hlen.arena_len_arr] }
  have harena' : ArenaClausesInv c F0 s' := by
    refine ⟨hcore.arena.len_ok, ?_, ?_, ?_, ?_⟩
    · intro r hr; rw [hrefs] at hr
      have hwf := hcore.arena.refs_wf r hr
      change _ ∧ _ ∧ _ ∧ _ ∧ _
      rw [hnxt_eq r hr, (hprops r hr).1]; exact hwf
    · intro r hr; rw [hrefs] at hr; unfold arenaHdr
      by_cases hrc : r = cref
      · subst r; rw [har_self, Option.getD_some]
        exact hshrk_hdr.trans (hcore.arena.no_shrk cref hr)
      · rw [har_ne r hrc]; exact hcore.arena.no_shrk r hr
    · intro r hr hng; rw [hrefs] at hr; rw [(hprops r hr).2.1] at hng
      rw [(hprops r hr).2.2]; exact hcore.arena.lits_lt r hr hng
    · intro r hr hng; rw [hrefs] at hr; rw [(hprops r hr).2.1] at hng
      rw [(hprops r hr).2.2]; exact hcore.arena.entails r hr hng
  have hwat' : WatchesInv c F0 s' := hcore.watches.with_wstk rfl rfl rfl hrefs
  refine ⟨{ hcore with
      lengths := hlen', arena := harena', watches := hwat'
      reason_inv := fun idx hidx hne => by
        dsimp only [s'] at hne ⊢
        have hrs := hcore.reason_inv idx hidx hne
        split at hrs <;> split
        · exact hrs
        · rename_i h1 h2; exact absurd h1 h2
        · rename_i h1 h2; exact absurd h2 h1
        · refine ⟨hrefs ▸ hrs.1, (hprops _ hrs.1).2.1.trans hrs.2.1, fun q hq => ?_⟩
          rw [(hprops _ hrs.1).2.2] at hq; exact hrs.2.2 q hq
      reason_lit_mem := fun idx hidx hne hlo => by
        dsimp only [s'] at hne hlo
        have hrs := hcore.reason_inv idx hidx hne
        split at hrs
        · rename_i h; exact absurd hlo h
        · rw [(hprops _ hrs.1).2.2]; exact hcore.reason_lit_mem idx hidx hne hlo },
    hrefs, hprops⟩

/-! ## 4. Pure 1-UIP semantic resolvent definitions and preservation lemmas -/

theorem mem_rsnLits_bin {s : PlainState} {rsn : BitVec 32}
    (hne : rsn ≠ 0xFFFFFFFF#32) (hbin : (rsn &&& 0x80000000#32) ≠ 0#32) {l : Nat} :
    l ∈ rsnLits s rsn ↔ l = (rsn &&& 0x7FFFFFFF#32).toNat := by
  simp [rsnLits, hne, hbin]

theorem mem_rsnLits_large {s : PlainState} {rsn : BitVec 32}
    (hne : rsn ≠ 0xFFFFFFFF#32) (hlo : (rsn &&& 0x80000000#32) = 0#32) {l : Nat} :
    l ∈ rsnLits s rsn ↔ l ∈ arenaClauseLits s rsn.toNat := by
  simp [rsnLits, hne, hlo]

/-- Lower-level literals accumulated in `tmp[1 ..< tl)`. -/
@[expose] def lowerLits (tmp : List (BitVec 32)) (tl : Nat) : List Nat :=
  ((tmp.drop 1).take (tl - 1)).map BitVec.toNat

/-- Marked current-level trail indices strictly below `idx`. -/
@[expose] def curTrailIdxs (s : PlainState) (mrk : List (BitVec 8)) (idx : Nat) : List Nat :=
  (List.range idx).filter fun j =>
    let v := (s.trl[j]?.getD 0#32).toNat / 2
    decide (mrk[v]?.getD 0#8 ≠ 0#8) &&
      decide ((s.lvl[v]?.getD 0#32).toNat = s.cur_level)

/-- Negated marked current-level trail literals strictly below `idx`. -/
@[expose] def curLits (s : PlainState) (mrk : List (BitVec 8)) (idx : Nat) : List Nat :=
  (curTrailIdxs s mrk idx).map fun j => (s.trl[j]?.getD 0#32).toNat ^^^ 1

/-- Active 1-UIP resolvent clause (`lowerLits ++ curLits`). -/
@[expose] def activeResolvent (s : PlainState) (tmp : List (BitVec 32)) (mrk : List (BitVec 8))
    (tl idx : Nat) : List Nat :=
  lowerLits tmp tl ++ curLits s mrk idx

/-- Well-formedness of lower-level literals in `tmp[1 ..< tl)`. -/
@[expose] def LowerInv (c : PlainCfg) (s : PlainState) (tmp : List (BitVec 32))
    (mrk : List (BitVec 8)) (tl : Nat) : Prop :=
  ∀ j, 1 ≤ j → j < tl →
    let l := (tmp[j]?.getD 0#32).toNat
    l < 2 * c.mv ∧ s.vals[l]?.getD 0#8 = 0xFF#8 ∧
    0 < (s.lvl[l / 2]?.getD 0#32).toNat ∧ (s.lvl[l / 2]?.getD 0#32).toNat < s.cur_level ∧
    mrk[l / 2]?.getD 0#8 ≠ 0#8

/-- Coverage of all nonzero entries in `mrk` by `tmp[1 ..< tl)` or `cur_level` trail entries. -/
@[expose] def MarksCov (c : PlainCfg) (s : PlainState) (tmp : List (BitVec 32))
    (mrk : List (BitVec 8)) (tl : Nat) : Prop :=
  ∀ v < c.mv, mrk[v]?.getD 0#8 ≠ 0#8 →
    (∃ j, 1 ≤ j ∧ j < tl ∧ (tmp[j]?.getD 0#32).toNat / 2 = v) ∨
    (∃ j < s.trail_end, (s.trl[j]?.getD 0#32).toNat / 2 = v ∧
      (s.lvl[v]?.getD 0#32).toNat = s.cur_level)

theorem mem_lowerLits_iff {tmp : List (BitVec 32)} {tl l : Nat}
    (h1 : 1 ≤ tl) (hle : tl ≤ tmp.length) :
    l ∈ lowerLits tmp tl ↔ ∃ j, 1 ≤ j ∧ j < tl ∧ (tmp[j]?.getD 0#32).toNat = l := by
  unfold lowerLits; rw [List.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨k, hk, hget⟩ := List.mem_iff_getElem.mp hx
    have hklt : k < tl - 1 := by rw [List.length_take, List.length_drop] at hk; omega
    rw [List.getElem_take, List.getElem_drop] at hget
    refine ⟨1 + k, by omega, by omega, ?_⟩
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some, hget]
  · rintro ⟨j, hj1, hjlt, hget⟩
    have hlt : j - 1 < ((tmp.drop 1).take (tl - 1)).length := by
      rw [List.length_take, List.length_drop]; omega
    refine ⟨tmp[j]'(by omega), ?_, ?_⟩
    · have hmem := List.getElem_mem hlt
      have hidx : 1 + (j - 1) = j := by omega
      simpa [List.getElem_take, List.getElem_drop, Nat.add_comm, hidx] using hmem
    · rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at hget

theorem curTrailIdxs_succ_true {s : PlainState} {mrk : List (BitVec 8)} {idx : Nat}
    (hm : mrk[(s.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#8 ≠ 0#8)
    (hl : (s.lvl[(s.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = s.cur_level) :
    curTrailIdxs s mrk (idx + 1) = curTrailIdxs s mrk idx ++ [idx] := by
  unfold curTrailIdxs; rw [range_succ_filter]; simp [hm, hl]

theorem curTrailIdxs_succ_false {s : PlainState} {mrk : List (BitVec 8)} {idx : Nat}
    (h : ¬ (mrk[(s.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#8 ≠ 0#8 ∧
      (s.lvl[(s.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = s.cur_level)) :
    curTrailIdxs s mrk (idx + 1) = curTrailIdxs s mrk idx := by
  unfold curTrailIdxs; rw [range_succ_filter]
  by_cases h1 : mrk[(s.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#8 ≠ 0#8
  · have h2 : (s.lvl[(s.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≠ s.cur_level :=
      fun he => h ⟨h1, he⟩
    simp [h1, h2]
  · simp [h1]

theorem curLits_succ_true {s : PlainState} {mrk : List (BitVec 8)} {idx : Nat}
    (hm : mrk[(s.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#8 ≠ 0#8)
    (hl : (s.lvl[(s.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = s.cur_level) :
    curLits s mrk (idx + 1) = curLits s mrk idx ++ [(s.trl[idx]?.getD 0#32).toNat ^^^ 1] := by
  unfold curLits; rw [curTrailIdxs_succ_true hm hl, List.map_append]; rfl

theorem curLits_succ_false {s : PlainState} {mrk : List (BitVec 8)} {idx : Nat}
    (h : ¬ (mrk[(s.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#8 ≠ 0#8 ∧
      (s.lvl[(s.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = s.cur_level)) :
    curLits s mrk (idx + 1) = curLits s mrk idx := by
  unfold curLits; rw [curTrailIdxs_succ_false h]

theorem same_core_lengths {c : PlainCfg} {s : PlainState} (hlen : s.LengthsOk c)
    {mrk' : List (BitVec 8)} {tmp' : List (BitVec 32)} {tc' tl' : Nat}
    (hm : mrk'.length = c.mv) (ht : tmp'.length = c.mv) (htl : tl' ≤ c.mv) :
    ({ s with mrk := mrk', tmp := tmp', tmp_cnt := tc', tmp_len := tl' } : PlainState).LengthsOk
      c :=
  { hlen with mrk_len := hm, tmp_len_arr := ht, tmp_len_le := htl }

theorem same_core_plainCoreInv {c : PlainCfg} {F0 : CNF Nat} {s : PlainState}
    (hcore : PlainCoreInv c F0 s) {mrk' : List (BitVec 8)} {tmp' : List (BitVec 32)}
    {tc' tl' : Nat} (hm : mrk'.length = c.mv) (ht : tmp'.length = c.mv) (htl : tl' ≤ c.mv) :
    PlainCoreInv c F0 { s with mrk := mrk', tmp := tmp', tmp_cnt := tc', tmp_len := tl' } :=
  { hcore with
    lengths := same_core_lengths hcore.lengths hm ht htl
    arena := { hcore.arena with len_ok := hcore.arena.len_ok }
    watches := hcore.watches.with_wstk rfl rfl rfl rfl }

/-- Unified bridge from a clause/reason analysis step (`plain_analyze_rsn` or `plain_analyze_lit`)
into the 1-UIP analysis invariant. `LitPred` is the set of literals in the analyzed reason. -/
theorem analyzeStep_preserves {c : PlainCfg} {F0 : CNF Nat} {s : PlainState}
    (hcore : PlainCoreInv c F0 s) (LitPred : Nat → Prop)
    {mrk mrk' : List (BitVec 8)} {tmp tmp' : List (BitVec 32)}
    {tc tc' tl tl' idx skip_var : Nat}
    (hidx : idx ≤ s.trail_end) (h1 : 1 ≤ tl) (htl_le : tl ≤ tl') (htl'_mv : tl' ≤ c.mv)
    (ht_len : tmp.length = c.mv) (ht'_len : tmp'.length = c.mv)
    (htc_eq : tc = (curTrailIdxs s mrk idx).length) (htc_le : tc ≤ tc')
    (hlow : LowerInv c s tmp mrk tl) (hcov : MarksCov c s tmp mrk tl)
    (hlits_lt : ∀ q, LitPred q → q < 2 * c.mv)
    (hclause : ∀ q, LitPred q →
      q / 2 = skip_var ∨ ∃ k < idx, (s.trl[k]?.getD 0#32).toNat = q ^^^ 1)
    (hmpres : ∀ v < c.mv, mrk[v]?.getD 0#8 ≠ 0#8 → mrk'[v]?.getD 0#8 = mrk[v]?.getD 0#8)
    (htpres : ∀ k < tl, tmp'[k]? = tmp[k]?)
    (hnewm : ∀ v < c.mv, mrk[v]?.getD 0#8 = 0#8 → mrk'[v]?.getD 0#8 ≠ 0#8 →
      ∃ l, LitPred l ∧ l / 2 = v ∧ v ≠ skip_var ∧
        0 < (s.lvl[v]?.getD 0#32).toNat ∧ (s.lvl[v]?.getD 0#32).toNat ≤ s.cur_level)
    (hnewt : ∀ j, tl ≤ j → j < tl' →
      let l := (tmp'[j]?.getD 0#32).toNat
      LitPred l ∧ l < 2 * c.mv ∧ l / 2 ≠ skip_var ∧
      0 < (s.lvl[l / 2]?.getD 0#32).toNat ∧ (s.lvl[l / 2]?.getD 0#32).toNat < s.cur_level ∧
      mrk'[l / 2]?.getD 0#8 ≠ 0#8)
    (hcnt : tc' - tc =
      ((List.range c.mv).filter fun v =>
        decide (mrk[v]?.getD 0#8 = 0#8) &&
        decide (mrk'[v]?.getD 0#8 ≠ 0#8) &&
        decide ((s.lvl[v]?.getD 0#32).toNat = s.cur_level)).length)
    (hall : ∀ l, LitPred l →
      l / 2 < c.mv ∧
      (l / 2 ≠ skip_var →
        (0 < (s.lvl[l / 2]?.getD 0#32).toNat → mrk'[l / 2]?.getD 0#8 ≠ 0#8) ∧
        (mrk[l / 2]?.getD 0#8 = 0#8 →
          (s.lvl[l / 2]?.getD 0#32).toNat ≤ s.cur_level ∧
          (0 < (s.lvl[l / 2]?.getD 0#32).toNat →
            (s.lvl[l / 2]?.getD 0#32).toNat < s.cur_level →
            ∃ j, tl ≤ j ∧ j < tl' ∧ (tmp'[j]?.getD 0#32).toNat / 2 = l / 2)))) :
    tc' = (curTrailIdxs s mrk' idx).length ∧
    LowerInv c s tmp' mrk' tl' ∧
    MarksCov c s tmp' mrk' tl' ∧
    (∀ l ∈ lowerLits tmp tl, l ∈ lowerLits tmp' tl') ∧
    (∀ l ∈ curLits s mrk idx, l ∈ curLits s mrk' idx) ∧
    (∀ q, LitPred q →
      q / 2 = skip_var ∨ q ∈ activeResolvent s tmp' mrk' tl' idx ∨
        F0.EntailsClause (cnfClause [litNeg q])) := by
  have hlow' : LowerInv c s tmp' mrk' tl' := by
    intro j hj1 hjlt
    by_cases hjold : j < tl
    · rw [htpres j hjold]
      obtain ⟨h1', h2', h3', h4', h5'⟩ := hlow j hj1 hjold
      exact ⟨h1', h2', h3', h4', by rw [hmpres _ (by omega) h5']; exact h5'⟩
    · obtain ⟨hmem, hlt, hne, hpos, hcl, hmk⟩ := hnewt j (by omega) hjlt
      rcases hclause _ hmem with heq | ⟨k, hk, hkeq⟩
      · exact absurd heq hne
      · exact ⟨hlt, (hcore.vals_false_iff _ hlt).mpr ⟨k, by omega, hkeq⟩, hpos, hcl, hmk⟩
  have hcov' : MarksCov c s tmp' mrk' tl' := by
    intro v hv hnz'
    by_cases hv0 : mrk[v]?.getD 0#8 = 0#8
    · obtain ⟨l, hlmem, rfl, hne, hpos, hle⟩ := hnewm v hv hv0 hnz'
      by_cases hcl : (s.lvl[l / 2]?.getD 0#32).toNat = s.cur_level
      · rcases hclause l hlmem with heq | ⟨k, hk, hkeq⟩
        · exact absurd heq hne
        · exact Or.inr ⟨k, by omega, by rw [hkeq]; exact litVar_litNeg l, hcl⟩
      · obtain ⟨_, hrest⟩ := hall l hlmem
        obtain ⟨j, hj1, hj2, hjeq⟩ := (hrest hne).2 hv0 |>.2 hpos (by omega)
        exact Or.inl ⟨j, by omega, hj2, hjeq⟩
    · rcases hcov v hv hv0 with ⟨j, hj1, hj2, hjeq⟩ | htrl
      · exact Or.inl ⟨j, hj1, by omega, by rw [htpres j hj2]; exact hjeq⟩
      · exact Or.inr htrl
  have htc' : tc' = (curTrailIdxs s mrk' idx).length := by
    let pOld : Nat → Bool := fun j =>
      let v := (s.trl[j]?.getD 0#32).toNat / 2
      decide (mrk[v]?.getD 0#8 ≠ 0#8) && decide ((s.lvl[v]?.getD 0#32).toNat = s.cur_level)
    let pNew : Nat → Bool := fun j =>
      let v := (s.trl[j]?.getD 0#32).toNat / 2
      decide (mrk[v]?.getD 0#8 = 0#8) && decide (mrk'[v]?.getD 0#8 ≠ 0#8) &&
        decide ((s.lvl[v]?.getD 0#32).toNat = s.cur_level)
    have hsplit : curTrailIdxs s mrk' idx =
        (List.range idx).filter (fun j => pOld j || pNew j) := by
      unfold curTrailIdxs; apply List.filter_congr; intro j hj
      have hjlt : j < idx := List.mem_range.mp hj
      have hvlt : (s.trl[j]?.getD 0#32).toNat / 2 < c.mv := by
        have := hcore.trail_lits_lt j (by omega); omega
      dsimp only [pOld, pNew]
      by_cases h0 : mrk[(s.trl[j]?.getD 0#32).toNat / 2]?.getD 0#8 = 0#8
      · simp [h0]
      · rw [hmpres _ hvlt h0]; simp [h0]
    have hadd : (curTrailIdxs s mrk' idx).length =
        ((List.range idx).filter pOld).length + ((List.range idx).filter pNew).length := by
      rw [hsplit]
      exact filter_length_add_of_disj pOld pNew (List.range idx) fun j _ ⟨h1, h2⟩ => by
        simp [pOld, pNew] at h1 h2; exact h1.1 h2.1.1
    have hbij : ((List.range idx).filter pNew).length =
        ((List.range c.mv).filter fun v =>
          decide (mrk[v]?.getD 0#8 = 0#8) &&
          decide (mrk'[v]?.getD 0#8 ≠ 0#8) &&
          decide ((s.lvl[v]?.getD 0#32).toNat = s.cur_level)).length := by
      refine nodup_length_eq_of_bij (fun j => (s.trl[j]?.getD 0#32).toNat / 2)
        (List.Nodup.sublist List.filter_sublist List.nodup_range)
        (List.Nodup.sublist List.filter_sublist List.nodup_range)
        (fun j hj => ?_) (fun j1 hj1 j2 hj2 heq => ?_) (fun v hv => ?_)
      · rw [List.mem_filter, List.mem_range] at hj ⊢
        have hvlt : (s.trl[j]?.getD 0#32).toNat / 2 < c.mv := by
          have := hcore.trail_lits_lt j (by omega); omega
        exact ⟨hvlt, hj.2⟩
      · rw [List.mem_filter, List.mem_range] at hj1 hj2
        exact hcore.trail_vars_nodup j1 j2 (by omega) (by omega) heq
      · rw [List.mem_filter, List.mem_range] at hv
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hv
        obtain ⟨hvlt, ⟨hm0, hmnz'⟩, hcl⟩ := hv
        obtain ⟨l, hlmem, rfl, hne, _, _⟩ := hnewm v hvlt hm0 hmnz'
        rcases hclause l hlmem with heq | ⟨k, hk, hkeq⟩
        · exact absurd heq hne
        · have hkvar : (s.trl[k]?.getD 0#32).toNat / 2 = l / 2 := by
            rw [hkeq]; exact litVar_litNeg l
          refine ⟨k, List.mem_filter.mpr ⟨List.mem_range.mpr hk, ?_⟩, hkvar⟩
          simp [pNew, hkvar, hm0, hmnz', hcl]
    have hold_eq : ((List.range idx).filter pOld).length = tc := htc_eq.symm
    omega
  have hlow_sub : ∀ l ∈ lowerLits tmp tl, l ∈ lowerLits tmp' tl' := by
    intro l hl
    rw [mem_lowerLits_iff h1 (by omega)] at hl
    obtain ⟨j, hj1, hj2, hget⟩ := hl
    rw [mem_lowerLits_iff (by omega) (by omega)]
    exact ⟨j, hj1, by omega, by rw [htpres j hj2]; exact hget⟩
  have hcur_sub : ∀ l ∈ curLits s mrk idx, l ∈ curLits s mrk' idx := by
    intro l hl
    unfold curLits curTrailIdxs at hl ⊢
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hl
    rw [List.mem_filter, List.mem_range] at hj
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hj
    have hvlt : (s.trl[j]?.getD 0#32).toNat / 2 < c.mv := by
      have := hcore.trail_lits_lt j (by omega); omega
    refine List.mem_map.mpr ⟨j, List.mem_filter.mpr ⟨List.mem_range.mpr hj.1, ?_⟩, rfl⟩
    simp [hmpres _ hvlt hj.2.1, hj.2.1, hj.2.2]
  have hq_res : ∀ q, LitPred q →
      q / 2 = skip_var ∨ q ∈ activeResolvent s tmp' mrk' tl' idx ∨
        F0.EntailsClause (cnfClause [litNeg q]) := by
    intro q hq
    rcases hclause q hq with heq | ⟨k, hk, hkeq⟩
    · exact Or.inl heq
    · by_cases hskip : q / 2 = skip_var
      · exact Or.inl hskip
      · right
        have hqlt : q < 2 * c.mv := hlits_lt q hq
        have hq_fals : s.vals[q]?.getD 0#8 = 0xFF#8 :=
          (hcore.vals_false_iff q hqlt).mpr ⟨k, by omega, hkeq⟩
        have hkvar : (s.trl[k]?.getD 0#32).toNat / 2 = q / 2 := by
          rw [hkeq]; exact litVar_litNeg q
        have hvl_le : (s.lvl[q / 2]?.getD 0#32).toNat ≤ s.cur_level := by
          rw [← hkvar]; exact hcore.lvl_le k (by omega)
        by_cases hvl0 : (s.lvl[q / 2]?.getD 0#32).toNat = 0
        · right
          have hs0 := hcore.level0_sound k (by omega) (by rw [hkvar]; exact hvl0)
          rwa [hkeq] at hs0
        · left
          obtain ⟨_, hq_rest⟩ := hall q hq
          have hq_mrk' : mrk'[q / 2]?.getD 0#8 ≠ 0#8 := (hq_rest hskip).1 (by omega)
          by_cases hcl : (s.lvl[q / 2]?.getD 0#32).toNat = s.cur_level
          · apply List.mem_append_right
            refine List.mem_map.mpr ⟨k, List.mem_filter.mpr ⟨List.mem_range.mpr hk, ?_⟩, ?_⟩
            · simp [hkvar, hq_mrk', hcl]
            · rw [hkeq]; exact litNeg_litNeg q
          · apply List.mem_append_left
            rw [mem_lowerLits_iff (by omega) (by omega)]
            rcases hcov' (q / 2) (by omega) hq_mrk' with ⟨j, hj1, hj2, hjeq⟩ | ⟨_, _, _, hbad⟩
            · obtain ⟨hl_lt, hl_fals, _, _, _⟩ := hlow' j hj1 hj2
              exact ⟨j, hj1, hj2, hcore.falsified_lit_unique hl_lt hqlt hjeq hl_fals hq_fals⟩
            · omega
  exact ⟨htc', hlow', hcov', hlow_sub, hcur_sub, hq_res⟩

/-- `plain_clear_marks(h, idx)` restores `MarksClear` once `curTrailIdxs s mrk idx = []`. -/
theorem clear_marks_restores_marksClear {c : PlainCfg} {s : PlainState}
    {tmp : List (BitVec 32)} {mrk mrk' : List (BitVec 8)} {tl idx : Nat}
    (hcov : MarksCov c s tmp mrk tl)
    (hzero : (curTrailIdxs s mrk idx).length = 0)
    (hpres : ∀ v < c.mv, mrk[v]?.getD 0#8 = 0#8 → mrk'[v]?.getD 0#8 = 0#8)
    (hclrt : ∀ i, 1 ≤ i → i < tl → (tmp[i]?.getD 0#32).toNat / 2 < c.mv →
      mrk'[(tmp[i]?.getD 0#32).toNat / 2]?.getD 0#8 = 0#8)
    (hclrr : ∀ j, idx ≤ j → j < s.trail_end → (s.trl[j]?.getD 0#32).toNat / 2 < c.mv →
      mrk'[(s.trl[j]?.getD 0#32).toNat / 2]?.getD 0#8 = 0#8) :
    ∀ v < c.mv, mrk'[v]?.getD 0#8 = 0#8 := by
  intro v hv
  by_cases hm0 : mrk[v]?.getD 0#8 = 0#8
  · exact hpres v hv hm0
  · rcases hcov v hv hm0 with ⟨i, hi1, hilt, hveq⟩ | ⟨j, hjlt, hveq, hcl⟩
    · rw [← hveq]; exact hclrt i hi1 hilt (by omega)
    · have hjge : idx ≤ j := by
        by_cases hlt : j < idx
        · exfalso
          have hmem : j ∈ curTrailIdxs s mrk idx :=
            List.mem_filter.mpr ⟨List.mem_range.mpr hlt, by simp [hveq, hm0, hcl]⟩
          have hpos := List.length_pos_of_mem hmem; omega
        · omega
      rw [← hveq]; exact hclrr j hjge hjlt (by omega)

theorem tmp_take_eq_cons_lowerLits {tmp : List (BitVec 32)} {tl : Nat} {uip : BitVec 32}
    (h1 : 1 ≤ tl) (h0 : tmp[0]? = some uip) :
    (tmp.take tl).map BitVec.toNat = uip.toNat :: lowerLits tmp tl := by
  unfold lowerLits
  cases tmp with
  | nil => simp at h0
  | cons x xs =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h0; subst h0
    cases tl with
    | zero => omega
    | succ k => simp [List.take_succ_cons]

theorem swap_tmp_props {tmp : List (BitVec 32)} {tl max_idx : Nat} {uip : BitVec 32}
    (h2 : 2 ≤ tl) (hle : tl ≤ tmp.length) (hm1 : 1 ≤ max_idx) (hmlt : max_idx < tl)
    (h0 : tmp[0]? = some uip) :
    let w1 := tmp[1]'(by omega)
    let wm := tmp[max_idx]'(by omega)
    let tmp_sw := (tmp.set 1 wm).set max_idx w1
    (∀ l, l ∈ (tmp_sw.take tl).map BitVec.toNat ↔ l ∈ (tmp.take tl).map BitVec.toNat) ∧
    (∀ l ∈ (tmp_sw.take tl).map BitVec.toNat,
      l = uip.toNat ∨ ∃ j, 1 ≤ j ∧ j < tl ∧ (tmp[j]?.getD 0#32).toNat = l) ∧
    tmp_sw[0]? = some uip ∧
    (tl = 2 → tmp_sw[1]? = tmp[1]?) := by
  intro w1 wm tmp_sw
  have hlen_sw : tmp_sw.length = tmp.length := by simp [tmp_sw]
  have hmem_take : ∀ (xs : List (BitVec 32)), tl ≤ xs.length → ∀ l,
      l ∈ (xs.take tl).map BitVec.toNat ↔ ∃ j, j < tl ∧ (xs[j]?.getD 0#32).toNat = l := by
    intro xs hxs l
    rw [List.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨j, hj, hget⟩ := List.mem_iff_getElem.mp hx
      have hjlt : j < tl := by rw [List.length_take] at hj; omega
      rw [List.getElem_take] at hget
      exact ⟨j, hjlt, by rw [List.getElem?_eq_getElem (by omega), Option.getD_some, hget]⟩
    · rintro ⟨j, hj, hget⟩
      have hj' : j < (xs.take tl).length := by rw [List.length_take]; omega
      refine ⟨xs[j]'(by omega), ?_, ?_⟩
      · simpa [List.getElem_take] using List.getElem_mem hj'
      · rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at hget
  have hiff : ∀ l, l ∈ (tmp_sw.take tl).map BitVec.toNat ↔ l ∈ (tmp.take tl).map BitVec.toNat := by
    intro l
    rw [hmem_take tmp_sw (by omega), hmem_take tmp hle]
    constructor
    · rintro ⟨j, hj, hget⟩
      by_cases hjm : j = max_idx
      · subst j
        rw [show tmp_sw[max_idx]? = some w1 from List.getElem?_set_self (by simp; omega),
          Option.getD_some] at hget
        exact ⟨1, by omega,
          by rw [List.getElem?_eq_getElem (by omega), Option.getD_some]; exact hget⟩
      · rw [show tmp_sw[j]? = (tmp.set 1 wm)[j]? from List.getElem?_set_ne (Ne.symm hjm)] at hget
        by_cases hj1 : j = 1
        · subst j
          rw [List.getElem?_set_self (by omega), Option.getD_some] at hget
          exact ⟨max_idx, hmlt,
            by rw [List.getElem?_eq_getElem (by omega), Option.getD_some]; exact hget⟩
        · rw [List.getElem?_set_ne (Ne.symm hj1)] at hget
          exact ⟨j, hj, hget⟩
    · rintro ⟨j, hj, hget⟩
      by_cases hj1 : j = 1
      · subst j
        refine ⟨max_idx, hmlt, ?_⟩
        rw [show tmp_sw[max_idx]? = some w1 from List.getElem?_set_self (by simp; omega),
          Option.getD_some]
        rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at hget
      · by_cases hjm : j = max_idx
        · subst j
          refine ⟨1, by omega, ?_⟩
          rw [show tmp_sw[1]? = (tmp.set 1 wm)[1]? from List.getElem?_set_ne hj1,
            List.getElem?_set_self (by omega), Option.getD_some]
          rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at hget
        · refine ⟨j, hj, ?_⟩
          rw [show tmp_sw[j]? = (tmp.set 1 wm)[j]? from List.getElem?_set_ne (Ne.symm hjm),
            List.getElem?_set_ne (Ne.symm hj1)]
          exact hget
  refine ⟨hiff, fun l hl => ?_, ?_, fun htl2 => ?_⟩
  · rw [hiff, hmem_take tmp hle] at hl
    obtain ⟨j, hj, hget⟩ := hl
    cases j with
    | zero => rw [h0, Option.getD_some] at hget; exact Or.inl hget.symm
    | succ k => exact Or.inr ⟨k + 1, by omega, hj, hget⟩
  · dsimp only [tmp_sw]
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega), h0]
  · have hm_eq : max_idx = 1 := by omega
    subst hm_eq
    dsimp only [tmp_sw]
    rw [List.getElem?_set_self (by simp; omega), List.getElem?_eq_getElem (by omega)]

/-! ## 5. `plain_analyze_lit` (`plainAnalyzeLitSpec`) -/

theorem plain_analyze_lit_wp (Γ : Env) :
    ∀ args m Q X, plainAnalyzeLitSpec args m Q X →
      Func.wp Γ plain_analyze_lit_body args m Q X := by
  rintro ⟨h, lit, skip_var, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hcur32, htl_mv, htc_fit, hm, hQ⟩
  obtain hmv : c.mv < 2 ^ 28 := c.hmv
  obtain hlit32 : lit.toNat < 2 ^ 32 := lit.isLt
  obtain hml := hlen.mrk_len; obtain hll := hlen.lvl_len; obtain htl := hlen.tmp_len_arr
  obtain hcur_tr : ((BitVec.ofNat 64 s.cur_level).setWidth 32).toNat = s.cur_level := by
    rw [bv64_trunc32_ofNat hcur32, bv32_ofNat_toNat hcur32]
  obtain hvmod : lit.toNat / 2 % 2 ^ 64 = lit.toNat / 2 := Nat.mod_eq_of_lt (by omega)
  obtain hcurmod : s.cur_level % 2 ^ 64 % 2 ^ 32 = s.cur_level := by
    rw [Nat.mod_eq_of_lt (by omega : s.cur_level < 2 ^ 64), Nat.mod_eq_of_lt hcur32]
  obtain hret_false_same : Q (false, ()) m :=
    hQ false s.mrk s.tmp s.tmp_cnt s.tmp_len m hlen (Nat.le_refl _) (by omega) htl_mv
      (Nat.le_refl _) (by grind) (fun _ _ _ => rfl) (fun _ _ => rfl)
      (fun _ _ h0 hnz => absurd h0 hnz) (fun _ h1 h2 => by omega) (fun hc => by cases hc) hm
  obtain hret_true_same :
      lit.toNat / 2 < c.mv →
      (lit.toNat / 2 = skip_var.toNat ∨ s.mrk[lit.toNat / 2]?.getD 0#8 ≠ 0#8 ∨
        (s.lvl[lit.toNat / 2]?.getD 0#32).toNat = 0) →
      Q (true, ()) m := fun hvlt hcase => by
    refine hQ true s.mrk s.tmp s.tmp_cnt s.tmp_len m hlen (Nat.le_refl _) (by omega) htl_mv
      (Nat.le_refl _) (by grind) (fun _ _ _ => rfl) (fun _ _ => rfl)
      (fun _ _ h0 hnz => absurd h0 hnz) (fun _ h1 h2 => by omega) (fun _ => ⟨hvlt, fun hne => ?_⟩)
      hm
    rcases hcase with h | h | h
    · exact absurd h hne
    · exact ⟨fun _ => h, fun hm0 => absurd hm0 h⟩
    · exact ⟨fun hpos => by omega,
        fun _ => ⟨by omega, fun hpos _ => by omega, fun hpos => by omega⟩⟩
  c0_steps
  all_goals simp only [hvmod, hcurmod,
    Nat.mod_eq_of_lt (by omega : c.mv < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : s.tmp_len < 2 ^ 64)] at *
  · -- (u64)v >= mv
    exact hret_false_same
  · -- vlvl > cur_lvl
    exact hret_false_same
  · -- vlvl == cur_lvl
    have hvlt : lit.toNat / 2 < c.mv := by omega
    have hvne : lit.toNat / 2 ≠ skip_var.toNat := by
      intro heq; apply ‹¬ lit >>> 1 = skip_var›
      apply BitVec.eq_of_toNat_eq; rw [bv32_lshr_1]; exact heq
    have hm0 : s.mrk[lit.toNat / 2]?.getD 0#8 = 0#8 := by
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
      have h0 : (s.mrk[lit.toNat / 2]'(by omega)).setWidth 32 = 0#32 := by assumption
      bv_omega
    have hm1 : (s.mrk.set (lit.toNat / 2) 1#8)[lit.toNat / 2]?.getD 0#8 ≠ 0#8 := by
      rw [List.getElem?_set_self (by omega)]; decide
    have hvl_eq : (s.lvl[lit.toNat / 2]?.getD 0#32).toNat = s.cur_level := by
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
      have h1 : s.lvl[lit.toNat / 2]'(by omega) = (BitVec.ofNat 64 s.cur_level).setWidth 32 := by
        assumption
      rw [h1, hcur_tr]
    have hvl_pos : 0 < (s.lvl[lit.toNat / 2]?.getD 0#32).toNat := by
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
      have h1 : (0 : BitVec 32).toNat < (s.lvl[lit.toNat / 2]'(by omega)).toNat := by assumption
      exact h1
    have htc1 : (BitVec.ofNat 64 s.tmp_cnt + 1).toNat = s.tmp_cnt + 1 := by
      simp only [bv_c0, BitVec.reduceToNat]; omega
    refine hQ true (s.mrk.set (lit.toNat / 2) 1#8) s.tmp (s.tmp_cnt + 1) s.tmp_len _
      { hlen with mrk_len := by simp [hml] } (Nat.le_refl _) (by omega) htl_mv (by omega)
      (by simp [hvlt, hm0, hm1, hvl_eq]) ?_ (fun _ _ => rfl) ?_ (fun _ h1 h2 => by omega) ?_ ?_
    · intro v hv hnz; rw [List.getElem?_set_ne (by rintro rfl; exact hnz hm0)]
    · intro v hv hv0 hnz'
      by_cases hve : v = lit.toNat / 2
      · subst v; exact ⟨rfl, hvne, hvl_pos, by omega⟩
      · rw [List.getElem?_set_ne (Ne.symm hve)] at hnz'; exact absurd hv0 hnz'
    · intro _; exact ⟨hvlt, fun _ => ⟨fun _ => hm1, fun _ => ⟨by omega, fun _ _ => rfl,
        fun _ hlt => by omega⟩⟩⟩
    · simpa only [bv_c0_zext32_64, bv32_lshr_1, htc1, trunc32_8_one] using hm
  · -- 0 < vlvl < cur_lvl, tmp_len >= mv
    have hvlt : lit.toNat / 2 < c.mv := by omega
    have hvne : lit.toNat / 2 ≠ skip_var.toNat := by
      intro heq; apply ‹¬ lit >>> 1 = skip_var›
      apply BitVec.eq_of_toNat_eq; rw [bv32_lshr_1]; exact heq
    have hm0 : s.mrk[lit.toNat / 2]?.getD 0#8 = 0#8 := by
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
      have h0 : (s.mrk[lit.toNat / 2]'(by omega)).setWidth 32 = 0#32 := by assumption
      bv_omega
    have hvl_pos : 0 < (s.lvl[lit.toNat / 2]?.getD 0#32).toNat := by
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
      have h1 : (0 : BitVec 32).toNat < (s.lvl[lit.toNat / 2]'(by omega)).toNat := by assumption
      exact h1
    have hvl_lt : (s.lvl[lit.toNat / 2]?.getD 0#32).toNat < s.cur_level := by
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
      have hle : ¬ s.cur_level < (s.lvl[lit.toNat / 2]'(by omega)).toNat := by assumption
      have hne : s.lvl[lit.toNat / 2]'(by omega) ≠ (BitVec.ofNat 64 s.cur_level).setWidth 32 := by
        assumption
      have hne' : (s.lvl[lit.toNat / 2]'(by omega)).toNat ≠ s.cur_level := fun heq =>
        hne (BitVec.eq_of_toNat_eq (by rw [heq, hcur_tr]))
      omega
    refine hQ false (s.mrk.set (lit.toNat / 2) 1#8) s.tmp s.tmp_cnt s.tmp_len _
      { hlen with mrk_len := by simp [hml] } (Nat.le_refl _) (by omega) htl_mv (Nat.le_refl _)
      (by simp [show (s.lvl[lit.toNat / 2]?.getD 0#32).toNat ≠ s.cur_level by omega])
      ?_ (fun _ _ => rfl) ?_ (fun _ h1 h2 => by omega) (fun hc => by cases hc) ?_
    · intro v hv hnz; rw [List.getElem?_set_ne (by rintro rfl; exact hnz hm0)]
    · intro v hv hv0 hnz'
      by_cases hve : v = lit.toNat / 2
      · subst v; exact ⟨rfl, hvne, hvl_pos, by omega⟩
      · rw [List.getElem?_set_ne (Ne.symm hve)] at hnz'; exact absurd hv0 hnz'
    · simpa only [bv_c0_zext32_64, bv32_lshr_1, trunc32_8_one] using hm
  · -- 0 < vlvl < cur_lvl, tmp_len < mv
    have hvlt : lit.toNat / 2 < c.mv := by omega
    have htl_lt : s.tmp_len < c.mv := by omega
    have htl1 : (BitVec.ofNat 64 s.tmp_len + 1).toNat = s.tmp_len + 1 := by
      simp only [bv_c0, BitVec.reduceToNat]; omega
    have hvne : lit.toNat / 2 ≠ skip_var.toNat := by
      intro heq; apply ‹¬ lit >>> 1 = skip_var›
      apply BitVec.eq_of_toNat_eq; rw [bv32_lshr_1]; exact heq
    have hm0 : s.mrk[lit.toNat / 2]?.getD 0#8 = 0#8 := by
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
      have h0 : (s.mrk[lit.toNat / 2]'(by omega)).setWidth 32 = 0#32 := by assumption
      bv_omega
    have hm1 : (s.mrk.set (lit.toNat / 2) 1#8)[lit.toNat / 2]?.getD 0#8 ≠ 0#8 := by
      rw [List.getElem?_set_self (by omega)]; decide
    have hvl_pos : 0 < (s.lvl[lit.toNat / 2]?.getD 0#32).toNat := by
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
      have h1 : (0 : BitVec 32).toNat < (s.lvl[lit.toNat / 2]'(by omega)).toNat := by assumption
      exact h1
    have hvl_lt : (s.lvl[lit.toNat / 2]?.getD 0#32).toNat < s.cur_level := by
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
      have hle : ¬ s.cur_level < (s.lvl[lit.toNat / 2]'(by omega)).toNat := by assumption
      have hne : s.lvl[lit.toNat / 2]'(by omega) ≠ (BitVec.ofNat 64 s.cur_level).setWidth 32 := by
        assumption
      have hne' : (s.lvl[lit.toNat / 2]'(by omega)).toNat ≠ s.cur_level := fun heq =>
        hne (BitVec.eq_of_toNat_eq (by rw [heq, hcur_tr]))
      omega
    refine hQ true (s.mrk.set (lit.toNat / 2) 1#8) (s.tmp.set s.tmp_len lit)
      s.tmp_cnt (s.tmp_len + 1) _
      { hlen with mrk_len := by simp [hml], tmp_len_arr := by simp [htl],
                  tmp_len_le := by dsimp; omega }
      (by omega) (Nat.le_refl _) (by omega) (Nat.le_refl _)
      (by simp [show (s.lvl[lit.toNat / 2]?.getD 0#32).toNat ≠ s.cur_level by omega])
      ?_ ?_ ?_ ?_ ?_ ?_
    · intro v hv hnz; rw [List.getElem?_set_ne (by rintro rfl; exact hnz hm0)]
    · intro k hk; rw [List.getElem?_set_ne (by omega)]
    · intro v hv hv0 hnz'
      by_cases hve : v = lit.toNat / 2
      · subst v; exact ⟨rfl, hvne, hvl_pos, by omega⟩
      · rw [List.getElem?_set_ne (Ne.symm hve)] at hnz'; exact absurd hv0 hnz'
    · intro j hj1 hj2
      have hje : j = s.tmp_len := by omega
      subst j
      exact ⟨by rw [List.getElem?_set_self (by omega)]; rfl, hvlt, hvne, hm0, hvl_pos, hvl_lt, hm1⟩
    · intro _
      exact ⟨hvlt, fun _ => ⟨fun _ => hm1, fun _ => ⟨by omega, fun _ hbad => by omega,
        fun _ _ => ⟨rfl, List.getElem?_set_self (by omega)⟩⟩⟩⟩
    · simpa only [bv_c0_zext32_64, bv32_lshr_1, bv64_ofNat_toNat (by omega : s.tmp_len < 2 ^ 64),
        htl1, trunc32_8_one] using hm
  · -- vlvl == 0
    have hvlt : lit.toNat / 2 < c.mv := by omega
    apply hret_true_same hvlt; right; right
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
    have h0 : ¬ (0 : BitVec 32).toNat < (s.lvl[lit.toNat / 2]'(by omega)).toNat := by assumption
    simp at h0; omega
  · -- mrk[v] != 0
    have hvlt : lit.toNat / 2 < c.mv := by omega
    apply hret_true_same hvlt; right; left
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
    have hnz : (s.mrk[lit.toNat / 2]'(by omega)).setWidth 32 ≠ 0#32 := by assumption
    intro h0; apply hnz; rw [h0]; rfl
  · -- v == skip_var
    have hvlt : lit.toNat / 2 < c.mv := by omega
    apply hret_true_same hvlt; left
    have heq : lit >>> 1 = skip_var := by assumption
    have := congrArg BitVec.toNat heq; rwa [bv32_lshr_1] at this

/-! ## 6. `plain_analyze_rsn` core proof -/

theorem filter_step_of_lit {s_mrk mrk1 mrk2 : List (BitVec 8)} {lvl : List (BitVec 32)}
    {mv cur_level tc0 tc1 tc2 v : Nat}
    (hmpres0 : ∀ w < mv, s_mrk[w]?.getD 0#8 ≠ 0#8 → mrk1[w]?.getD 0#8 = s_mrk[w]?.getD 0#8)
    (hmpres1 : ∀ w < mv, mrk1[w]?.getD 0#8 ≠ 0#8 → mrk2[w]?.getD 0#8 = mrk1[w]?.getD 0#8)
    (hnew1 : ∀ w < mv, mrk1[w]?.getD 0#8 = 0#8 → mrk2[w]?.getD 0#8 ≠ 0#8 → v = w)
    (htc_ge : tc0 ≤ tc1)
    (hcnt1 : tc1 - tc0 =
      ((List.range mv).filter fun w =>
        decide (s_mrk[w]?.getD 0#8 = 0#8) &&
        decide (mrk1[w]?.getD 0#8 ≠ 0#8) &&
        decide ((lvl[w]?.getD 0#32).toNat = cur_level)).length)
    (htc2 : tc2 = tc1 +
      if v < mv ∧ mrk1[v]?.getD 0#8 = 0#8 ∧ mrk2[v]?.getD 0#8 ≠ 0#8 ∧
         (lvl[v]?.getD 0#32).toNat = cur_level then 1 else 0) :
    tc2 - tc0 =
      ((List.range mv).filter fun w =>
        decide (s_mrk[w]?.getD 0#8 = 0#8) &&
        decide (mrk2[w]?.getD 0#8 ≠ 0#8) &&
        decide ((lvl[w]?.getD 0#32).toNat = cur_level)).length := by
  have hne_iff : ∀ w < mv, w ≠ v → (mrk2[w]?.getD 0#8 ≠ 0#8 ↔ mrk1[w]?.getD 0#8 ≠ 0#8) := by
    intro w hw hne
    constructor
    · intro h2 h1; exact hne (hnew1 w hw h1 h2).symm
    · intro h1; rw [hmpres1 w hw h1]; exact h1
  split at htc2
  · rename_i hC
    obtain ⟨hv, hm1, hm2, hcl⟩ := hC
    have hs0 : s_mrk[v]?.getD 0#8 = 0#8 := Classical.byContradiction fun hnz => by
      rw [hmpres0 v hv hnz] at hm1; exact hnz hm1
    have hflip := filter_length_flip_one
      (fun w => decide (s_mrk[w]?.getD 0#8 = 0#8) &&
        decide (mrk1[w]?.getD 0#8 ≠ 0#8) &&
        decide ((lvl[w]?.getD 0#32).toNat = cur_level))
      (fun w => decide (s_mrk[w]?.getD 0#8 = 0#8) &&
        decide (mrk2[w]?.getD 0#8 ≠ 0#8) &&
        decide ((lvl[w]?.getD 0#32).toNat = cur_level))
      v (List.range mv) List.nodup_range (List.mem_range.mpr hv)
      (by simp [hm1]) (by simp [hs0, hm2, hcl])
      (fun w hw hne => by simp [hne_iff w (List.mem_range.mp hw) hne])
    rw [hflip, ← hcnt1]; omega
  · rename_i hC
    rw [Nat.add_zero] at htc2
    subst htc2; rw [hcnt1]; congr 1; apply List.filter_congr; intro w hw
    have hwlt := List.mem_range.mp hw
    by_cases hwe : w = v
    · subst w
      by_cases hm1 : mrk1[v]?.getD 0#8 = 0#8
      · by_cases hcl : (lvl[v]?.getD 0#32).toNat = cur_level
        · have hm2 : mrk2[v]?.getD 0#8 = 0#8 :=
            Classical.byContradiction fun hnz => hC ⟨hwlt, hm1, hnz, hcl⟩
          simp [hm1, hm2]
        · simp [hcl]
      · rw [hmpres1 v hwlt hm1]
    · simp [hne_iff w hwlt hwe]

theorem plain_analyze_rsn_wp (Γ : Env)
    (hLit : ∀ args m Q X, plainAnalyzeLitSpec args m Q X →
      Γ "plain_analyze_lit" [i64, i32, i32] [.bool] args m Q X) :
    ∀ args m Q X, plainAnalyzeRsnSpec args m Q X →
      Func.wp Γ plain_analyze_rsn_body args m Q X := by
  rintro ⟨h, rsn, skip_var, ⟨⟩⟩ m Q X
    ⟨c, F0, s, R, rfl, hcore, htl_mv, htc_fit, hrsn_ref, hm, hQ⟩
  obtain hmv : c.mv < 2 ^ 28 := c.hmv
  obtain har_cap : c.arena_cap < 2 * 2 ^ 28 := c.harena
  obtain hlen := hcore.lengths
  obtain hcur32 : s.cur_level < 2 ^ 32 := by
    have := hcore.cur_level_le; have := hlen.trail_end_le; omega
  obtain har_len := hlen.arena_len_arr
  obtain har_le := hlen.arena_len_le
  obtain hgu_len := hlen.heur_ok.glue_used_len
  obtain hret_false_same : Q (false, ()) m := by
    refine hQ false s.mrk s.tmp s.tmp_cnt s.tmp_len s.arena s.heur m hcore
      (Nat.le_refl _) htl_mv (Nat.le_refl _) rfl (fun _ _ => ⟨rfl, rfl, rfl⟩)
      (fun _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ h0 hnz => absurd h0 hnz)
      (fun _ h1 h2 => by omega) ?_ (fun hc => by cases hc) hm
    rw [Nat.sub_self, filter_length_eq_zero_of_false]; intro v _; simp
  c0_step; c0_step
  · exact hret_false_same
  · c0_step
    · -- Binary watch reason: `plain_analyze_lit(h, rsn & 0x7FFFFFFF, skip_var)`
      have hne : rsn ≠ 0xFFFFFFFF#32 := by assumption
      have hbin : (rsn &&& 0x80000000#32) ≠ 0#32 := by assumption
      c0_steps
      refine wp_call_of_spec _ _ (hLit (c.hdr, rsn &&& 0x7FFFFFFF#32, skip_var, ()) _ _ _
        ⟨c, s, R, rfl, hlen, hcur32, htl_mv, by omega, hm, ?_⟩)
      intro ok mrk' tmp' tc' tl' m' _ hlen' htl_ge htl_inc htl_le htc_ge htc_eq hmpres htpres
        hnewm hnewt hok hm'
      c0_steps
      refine hQ ok mrk' tmp' tc' tl' s.arena s.heur m'
        (same_core_plainCoreInv hcore hlen'.mrk_len hlen'.tmp_len_arr htl_le)
        htl_ge htl_le htc_ge rfl (fun _ _ => ⟨rfl, rfl, rfl⟩) hmpres htpres ?_ ?_ ?_ ?_ hm'
      · intro v hv h0 hnz
        obtain ⟨rfl, hne', hpos, hle⟩ := hnewm v hv h0 hnz
        exact ⟨(rsn &&& 0x7FFFFFFF#32).toNat, (mem_rsnLits_bin hne hbin).mpr rfl,
          rfl, hne', hpos, hle⟩
      · intro j hj1 hj2
        obtain ⟨heq, hlt, hne', h0, hpos, hcl, hmk⟩ := hnewt j hj1 hj2
        exact ⟨(mem_rsnLits_bin hne hbin).mpr heq, by omega, by omega, by rwa [heq],
          by rwa [heq], by rwa [heq], by rwa [heq]⟩
      · exact filter_step_of_lit (fun _ _ _ => rfl) hmpres
          (fun w hw h0 hnz => (hnewm w hw h0 hnz).1) (Nat.le_refl _)
          (by rw [Nat.sub_self, filter_length_eq_zero_of_false]; intro _ _; simp) htc_eq
      · intro hok'
        obtain ⟨hvlt, hrest⟩ := hok hok'
        refine ⟨hne, fun _ => hvlt, fun h0 => absurd h0 hbin, fun l hl => ?_⟩
        rw [mem_rsnLits_bin hne hbin] at hl; subst hl
        refine ⟨hvlt, fun hne' => ?_⟩
        obtain ⟨hm1, h0r⟩ := hrest hne'
        refine ⟨hm1, fun h0 => ?_⟩
        obtain ⟨hle, _, hlow⟩ := h0r h0
        exact ⟨hle, fun hpos hlt =>
          let ⟨htl1, htget⟩ := hlow hpos hlt
          ⟨s.tmp_len, Nat.le_refl _, by omega, by rw [htget]; rfl⟩⟩
    · -- Large arena clause reason (`rsn.toNat ∈ arenaClauseRefs s`)
      obtain hne : rsn ≠ 0xFFFFFFFF#32 := by assumption
      obtain hlarge : (rsn &&& 0x80000000#32) = 0#32 := by assumption
      obtain href : rsn.toNat ∈ arenaClauseRefs s := hrsn_ref hne hlarge
      obtain ⟨hbd3, hsz3, hbd, hbd_le, _⟩ := hcore.arena.refs_wf rsn.toNat href
      obtain hsz_get : (s.arena[rsn.toNat + 2]'(by omega)).toNat = arenaClauseSize s rsn.toNat := by
        unfold arenaClauseSize; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
      obtain hhdr_get : s.arena[rsn.toNat]'(by omega) = s.arena[rsn.toNat]?.getD 0#32 := by
        rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
      obtain hrsn_mod : rsn.toNat % 2 ^ 64 = rsn.toNat := Nat.mod_eq_of_lt (by omega)
      c0_step; c0_step; c0_step; try exact hret_false_same
      c0_step; c0_step; c0_step; try exact hret_false_same
      c0_step; c0_step; try exact hret_false_same
      -- Collapse `if ((hdr & PH_RED) != 0u)` via `wp_join_group`.
      refine wp_join_group
        (fun () m1 => ∃ arena1 heur1,
          let s1 : PlainState := { s with arena := arena1, heur := heur1 }
          PlainCoreInv c F0 s1 ∧ arenaClauseRefs s1 = arenaClauseRefs s ∧
          (∀ r ∈ arenaClauseRefs s, arenaClauseSize s1 r = arenaClauseSize s r ∧
            arenaClauseGarb s1 r = arenaClauseGarb s r ∧
            arenaClauseLits s1 r = arenaClauseLits s r) ∧
          (∀ k < arenaClauseSize s rsn.toNat,
            arena1[rsn.toNat + 3 + k]? = s.arena[rsn.toNat + 3 + k]?) ∧
          (PlainMem c s1 ⋆ R) m1) ?_ ?_
      · -- Post-`PH_RED`: `u32 i = 0u; while (i < sz) { ... } return true;`
        rintro _ ⟨⟩ m1 ⟨arena1, heur1, hcore1, hrefs1, hcl1, har1_eq, hm1⟩
        c0_steps
        let s1 : PlainState := { s with arena := arena1, heur := heur1 }
        have hlen1 : s1.LengthsOk c := hcore1.lengths
        have har1_len : arena1.length = c.arena_cap := hlen1.arena_len_arr
        let sz : Nat := arenaClauseSize s rsn.toNat
        let LoopInv : Nat → List (BitVec 8) → List (BitVec 32) → Nat → Nat → Prop :=
          fun i mrk' tmp' tc' tl' =>
            i ≤ sz ∧ mrk'.length = c.mv ∧ tmp'.length = c.mv ∧
            s.tmp_len ≤ tl' ∧ tl' ≤ c.mv ∧ s.tmp_cnt ≤ tc' ∧
            (∀ v < c.mv, s.mrk[v]?.getD 0#8 ≠ 0#8 → mrk'[v]?.getD 0#8 = s.mrk[v]?.getD 0#8) ∧
            (∀ k < s.tmp_len, tmp'[k]? = s.tmp[k]?) ∧
            (∀ v < c.mv, s.mrk[v]?.getD 0#8 = 0#8 → mrk'[v]?.getD 0#8 ≠ 0#8 →
              ∃ l ∈ arenaClauseLits s rsn.toNat, l / 2 = v ∧ v ≠ skip_var.toNat ∧
                0 < (s.lvl[v]?.getD 0#32).toNat ∧ (s.lvl[v]?.getD 0#32).toNat ≤ s.cur_level) ∧
            (∀ v < c.mv, s.mrk[v]?.getD 0#8 = 0#8 → mrk'[v]?.getD 0#8 ≠ 0#8 →
              (s.lvl[v]?.getD 0#32).toNat < s.cur_level →
              ∃ j, s.tmp_len ≤ j ∧ j < tl' ∧ (tmp'[j]?.getD 0#32).toNat / 2 = v) ∧
            (∀ j, s.tmp_len ≤ j → j < tl' →
              let l := (tmp'[j]?.getD 0#32).toNat
              l ∈ arenaClauseLits s rsn.toNat ∧ l < 2 * c.mv ∧ l / 2 ≠ skip_var.toNat ∧
              s.mrk[l / 2]?.getD 0#8 = 0#8 ∧ 0 < (s.lvl[l / 2]?.getD 0#32).toNat ∧
              (s.lvl[l / 2]?.getD 0#32).toNat < s.cur_level ∧ mrk'[l / 2]?.getD 0#8 ≠ 0#8) ∧
            (tc' - s.tmp_cnt =
              ((List.range c.mv).filter fun v =>
                decide (s.mrk[v]?.getD 0#8 = 0#8) &&
                decide (mrk'[v]?.getD 0#8 ≠ 0#8) &&
                decide ((s.lvl[v]?.getD 0#32).toNat = s.cur_level)).length) ∧
            (∀ k < i,
              let l := (s.arena[rsn.toNat + 3 + k]?.getD 0#32).toNat
              l / 2 < c.mv ∧
              (l / 2 ≠ skip_var.toNat →
                (0 < (s.lvl[l / 2]?.getD 0#32).toNat → mrk'[l / 2]?.getD 0#8 ≠ 0#8) ∧
                (s.mrk[l / 2]?.getD 0#8 = 0#8 →
                  (s.lvl[l / 2]?.getD 0#32).toNat ≤ s.cur_level ∧
                  (0 < (s.lvl[l / 2]?.getD 0#32).toNat →
                    (s.lvl[l / 2]?.getD 0#32).toNat < s.cur_level →
                    ∃ j, s.tmp_len ≤ j ∧ j < tl' ∧ (tmp'[j]?.getD 0#32).toNat / 2 = l / 2))))
        refine wp_loop_group
          (fun r (iv, ()) ml => ∃ i mrk' tmp' tc' tl',
            r = sz - i ∧ iv = BitVec.ofNat 32 i ∧ LoopInv i mrk' tmp' tc' tl' ∧
            (PlainMem c { s with
              mrk := mrk', tmp := tmp', tmp_cnt := tc', tmp_len := tl',
              arena := arena1, heur := heur1 } ⋆ R) ml) ?_ ?_
        · rintro L r ⟨iv, ⟨⟩⟩ ml ih ⟨i, mrk', tmp', tc', tl', rfl, rfl, hli, hml⟩
          obtain ⟨hile, hml_l, htl_l, htl_ge, htl_le, htc_ge, hmpres, htpres, hnewm, hnewlow,
            hnewt, hcnt, hdone⟩ := hli
          c0_step; c0_step
          · -- `i < sz`: load `l = arena1[rsn + 3 + i]` and call `plain_analyze_lit`
            obtain hi32 : i < 2 ^ 32 := by omega
            obtain hsz_mod : (rsn.toNat + (2#64).toNat) % 2 ^ 64 = rsn.toNat + 2 := by
              change (rsn.toNat + 2) % 2 ^ 64 = rsn.toNat + 2; omega
            obtain hilt : i < sz := by
              have hlt_bv : i % 2 ^ 32 <
                  (s.arena[(rsn.toNat + (2#64).toNat) % 2 ^ 64]'(by omega)).toNat := by assumption
              rw [Nat.mod_eq_of_lt hi32] at hlt_bv
              have hidx_eq : s.arena[(rsn.toNat + (2#64).toNat) % 2 ^ 64]'(by omega) =
                  s.arena[rsn.toNat + 2]'(by omega) := by simp only [hsz_mod]
              rw [hidx_eq, hsz_get] at hlt_bv; exact hlt_bv
            obtain hidx_l : ((rsn.setWidth 64 + 3) + (BitVec.ofNat 32 i).setWidth 64).toNat =
                rsn.toNat + 3 + i := by
              simp only [bv_c0, BitVec.reduceToNat]; omega
            c0_steps
            have htc_le_mv : tc' - s.tmp_cnt ≤ c.mv := by
              rw [hcnt]; exact Nat.le_trans (List.length_filter_le _ _) (by simp)
            let st : PlainState :=
              { s1 with mrk := mrk', tmp := tmp', tmp_cnt := tc', tmp_len := tl' }
            have hst_len : st.LengthsOk c :=
              { hlen1 with mrk_len := hml_l, tmp_len_arr := htl_l, tmp_len_le := htl_le }
            let l_bv : BitVec 32 :=
              arena1[((rsn.setWidth 64 + 3) + (BitVec.ofNat 32 i).setWidth 64).toNat]'(by omega)
            have hl_eq : l_bv = s.arena[rsn.toNat + 3 + i]'(by omega) := by
              have h1 : arena1[rsn.toNat + 3 + i]? = some l_bv := by
                rw [← hidx_l]; exact List.getElem?_eq_getElem (by omega)
              rw [har1_eq i hilt, List.getElem?_eq_getElem (by omega)] at h1
              exact (Option.some.inj h1).symm
            have hl_get : (s.arena[rsn.toNat + 3 + i]?.getD 0#32).toNat = l_bv.toNat := by
              rw [List.getElem?_eq_getElem (by omega), Option.getD_some, ← hl_eq]
            have hl_mem : l_bv.toNat ∈ arenaClauseLits s rsn.toNat :=
              (mem_arenaClauseLits_iff (by omega)).mpr ⟨i, hilt, by rw [← hl_eq]⟩
            refine wp_call_of_spec _ _ (hLit (c.hdr, l_bv, skip_var, ()) _ _ _
              ⟨c, st, R, rfl, hst_len, hcur32, htl_le, by dsimp [st]; omega, hml, ?_⟩)
            intro ok2 mrk2 tmp2 tc2 tl2 m2 _ hlen2 htl2_ge htl2_inc htl2_le htc2_ge htc2_eq
              hmpres2 htpres2 hnewm2 hnewt2 hok2 hm2
            dsimp only [st, s1] at hlen2 htl2_ge htl2_inc htl2_le htc2_ge htc2_eq
            dsimp only [st, s1] at hmpres2 htpres2 hnewm2 hnewt2 hok2 hm2
            have hmpres_comb : ∀ v < c.mv, s.mrk[v]?.getD 0#8 ≠ 0#8 →
                mrk2[v]?.getD 0#8 = s.mrk[v]?.getD 0#8 := fun v hv hnz => by
              have h1 := hmpres v hv hnz
              rw [hmpres2 v hv (by rwa [h1]), h1]
            have htpres_comb : ∀ k < s.tmp_len, tmp2[k]? = s.tmp[k]? := fun k hk => by
              rw [htpres2 k (by omega), htpres k hk]
            have hnewm_comb : ∀ v < c.mv, s.mrk[v]?.getD 0#8 = 0#8 → mrk2[v]?.getD 0#8 ≠ 0#8 →
                ∃ l ∈ arenaClauseLits s rsn.toNat, l / 2 = v ∧ v ≠ skip_var.toNat ∧
                  0 < (s.lvl[v]?.getD 0#32).toNat ∧ (s.lvl[v]?.getD 0#32).toNat ≤ s.cur_level := by
              intro v hv hs0 hmnz2
              by_cases hm1 : mrk'[v]?.getD 0#8 = 0#8
              · obtain ⟨rfl, hne', hpos, hle⟩ := hnewm2 v hv hm1 hmnz2
                exact ⟨l_bv.toNat, hl_mem, rfl, hne', hpos, hle⟩
              · exact hnewm v hv hs0 hm1
            have hnewt_comb : ∀ j, s.tmp_len ≤ j → j < tl2 →
                let l := (tmp2[j]?.getD 0#32).toNat
                l ∈ arenaClauseLits s rsn.toNat ∧ l < 2 * c.mv ∧ l / 2 ≠ skip_var.toNat ∧
                s.mrk[l / 2]?.getD 0#8 = 0#8 ∧ 0 < (s.lvl[l / 2]?.getD 0#32).toNat ∧
                (s.lvl[l / 2]?.getD 0#32).toNat < s.cur_level ∧ mrk2[l / 2]?.getD 0#8 ≠ 0#8 := by
              intro j hj1 hj2
              by_cases hjold : j < tl'
              · rw [htpres2 j hjold]
                obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hnewt j hj1 hjold
                exact ⟨h1, h2, h3, h4, h5, h6, by rw [hmpres2 _ (by omega) h7]; exact h7⟩
              · obtain ⟨heq, hlt, hne', hm1_0, hpos, hcl, hmk2⟩ := hnewt2 j (by omega) hj2
                have hs0 : s.mrk[l_bv.toNat / 2]?.getD 0#8 = 0#8 :=
                  Classical.byContradiction fun hnz => by
                    rw [hmpres _ hlt hnz] at hm1_0; exact hnz hm1_0
                exact ⟨by rwa [heq], by omega, by omega, by rwa [heq], by rwa [heq], by rwa [heq],
                  by rwa [heq]⟩
            have hcnt2 : tc2 - s.tmp_cnt =
                ((List.range c.mv).filter fun v =>
                  decide (s.mrk[v]?.getD 0#8 = 0#8) &&
                  decide (mrk2[v]?.getD 0#8 ≠ 0#8) &&
                  decide ((s.lvl[v]?.getD 0#32).toNat = s.cur_level)).length :=
              filter_step_of_lit hmpres hmpres2 (fun w hw h0 hnz => (hnewm2 w hw h0 hnz).1)
                htc_ge hcnt htc2_eq
            cases ok2 with
            | false =>
              wp_unfold
              refine hQ false mrk2 tmp2 tc2 tl2 arena1 heur1 m2
                (same_core_plainCoreInv hcore1 hlen2.mrk_len hlen2.tmp_len_arr htl2_le)
                (by omega) htl2_le (by omega) hrefs1 hcl1 hmpres_comb htpres_comb
                (fun v hv hs0 hmnz2 =>
                  let ⟨l, hl, hr⟩ := hnewm_comb v hv hs0 hmnz2
                  ⟨l, (mem_rsnLits_large hne hlarge).mpr hl, hr⟩)
                (fun j hj1 hj2 =>
                  let ⟨h1, hr⟩ := hnewt_comb j hj1 hj2
                  ⟨(mem_rsnLits_large hne hlarge).mpr h1, hr⟩)
                hcnt2 (fun hc => by cases hc) hm2
            | true =>
              wp_unfold
              obtain ⟨hvlt, hrest⟩ := hok2 rfl
              have hi_add : BitVec.ofNat 32 i + (1 : BitVec 32) = BitVec.ofNat 32 (i + 1) := by
                apply BitVec.eq_of_toNat_eq
                simp only [bv_c0, show (1 : BitVec 32).toNat = 1 from rfl]
              rw [hi_add]
              refine ih (sz - (i + 1)) _ _ (by omega) ⟨i + 1, mrk2, tmp2, tc2, tl2, rfl, rfl,
                ⟨by omega, hlen2.mrk_len, hlen2.tmp_len_arr, by omega, htl2_le, by omega,
                  hmpres_comb, htpres_comb, hnewm_comb, ?_, hnewt_comb, hcnt2, ?_⟩, hm2⟩
              · intro v hv hs0 hmnz2 hltcl
                by_cases hm1 : mrk'[v]?.getD 0#8 = 0#8
                · obtain ⟨rfl, hne', hpos, _⟩ := hnewm2 v hv hm1 hmnz2
                  obtain ⟨htl1, htget⟩ := ((hrest hne').2 hm1).2.2 hpos hltcl
                  exact ⟨tl', htl_ge, by omega, by rw [htget]; rfl⟩
                · obtain ⟨j, hj1, hj2, hjeq⟩ := hnewlow v hv hs0 hm1 hltcl
                  exact ⟨j, hj1, by omega, by rw [htpres2 j hj2]; exact hjeq⟩
              · intro k hk
                by_cases hki : k = i
                · subst hki; dsimp only; rw [hl_get]
                  refine ⟨hvlt, fun hne' => ?_⟩
                  obtain ⟨hpos_m, hm1_r⟩ := hrest hne'
                  refine ⟨hpos_m, fun hs0 => ?_⟩
                  by_cases hm1 : mrk'[l_bv.toNat / 2]?.getD 0#8 = 0#8
                  · obtain ⟨hle, _, hlow⟩ := hm1_r hm1
                    exact ⟨hle, fun hpos hltcl =>
                      let ⟨htl1, htget⟩ := hlow hpos hltcl
                      ⟨tl', htl_ge, by omega, by rw [htget]; rfl⟩⟩
                  · obtain ⟨_, _, _, _, _, hle⟩ := hnewm _ hvlt hs0 hm1
                    exact ⟨hle, fun _ hltcl =>
                      let ⟨j, hj1, hj2, hjeq⟩ := hnewlow _ hvlt hs0 hm1 hltcl
                      ⟨j, hj1, by omega, by rw [htpres2 j hj2]; exact hjeq⟩⟩
                · obtain ⟨hkv, hkrest⟩ := hdone k (by omega)
                  refine ⟨hkv, fun hne' => ?_⟩
                  obtain ⟨h1, h2⟩ := hkrest hne'
                  refine ⟨fun hp => by rw [hmpres2 _ hkv (h1 hp)]; exact h1 hp, fun hs0 => ?_⟩
                  obtain ⟨hle, hlow⟩ := h2 hs0
                  exact ⟨hle, fun hpos hltcl =>
                    let ⟨j, hj1, hj2, hjeq⟩ := hlow hpos hltcl
                    ⟨j, hj1, by omega, by rw [htpres2 j hj2]; exact hjeq⟩⟩
          · -- `i ≥ sz` (`i = sz`): return `true`
            c0_steps
            have hi32 : i < 2 ^ 32 := by omega
            have hsz_mod : (rsn.toNat + (2#64).toNat) % 2 ^ 64 = rsn.toNat + 2 := by
              change (rsn.toNat + 2) % 2 ^ 64 = rsn.toNat + 2; omega
            have hieq : i = sz := by
              have hge_bv : ¬ i % 2 ^ 32 <
                  (s.arena[(rsn.toNat + (2#64).toNat) % 2 ^ 64]'(by omega)).toNat := by assumption
              rw [Nat.mod_eq_of_lt hi32] at hge_bv
              have hidx_eq : s.arena[(rsn.toNat + (2#64).toNat) % 2 ^ 64]'(by omega) =
                  s.arena[rsn.toNat + 2]'(by omega) := by simp only [hsz_mod]
              rw [hidx_eq, hsz_get] at hge_bv; omega
            refine hQ true mrk' tmp' tc' tl' arena1 heur1 ml
              (same_core_plainCoreInv hcore1 hml_l htl_l htl_le)
              htl_ge htl_le htc_ge hrefs1 hcl1 hmpres htpres
              (fun v hv hs0 hmnz =>
                let ⟨l, hl, hr⟩ := hnewm v hv hs0 hmnz
                ⟨l, (mem_rsnLits_large hne hlarge).mpr hl, hr⟩)
              (fun j hj1 hj2 =>
                let ⟨h1, hr⟩ := hnewt j hj1 hj2
                ⟨(mem_rsnLits_large hne hlarge).mpr h1, hr⟩)
              hcnt ?_ hml
            intro _
            refine ⟨hne, fun hbad => absurd hlarge hbad,
              fun _ => ⟨by omega, hsz3, by omega⟩, fun l hl => ?_⟩
            rw [mem_rsnLits_large hne hlarge] at hl
            obtain ⟨k, hk, hget⟩ := (mem_arenaClauseLits_iff (by omega)).mp hl
            have hkget : (s.arena[rsn.toNat + 3 + k]?.getD 0#32).toNat = l := by
              rw [List.getElem?_eq_getElem (by omega), Option.getD_some, hget]
            simpa [hkget] using hdone k (by omega)
        · -- Loop entry: `i = 0`
          intro L hL; c0_steps
          refine hL sz _ m1 ⟨0, s.mrk, s.tmp, s.tmp_cnt, s.tmp_len, by omega, rfl,
            ⟨Nat.zero_le _, hlen.mrk_len, hlen.tmp_len_arr, Nat.le_refl _, htl_mv, Nat.le_refl _,
              fun _ _ _ => rfl, fun _ _ => rfl, fun _ _ h0 hnz => absurd h0 hnz,
              fun _ _ h0 hnz _ => absurd h0 hnz, fun _ h1 h2 => by omega,
              by rw [Nat.sub_self, filter_length_eq_zero_of_false]; intro _ _; simp,
              fun _ hk => by omega⟩, hm1⟩
      · -- `if ((hdr & PH_RED) != 0u)` body before join (decomposed into sequential joins)
        intro Jred hJred; c0_let_simp; c0_step
        · -- `(hdr & PH_RED) ≠ 0#32`: load `gu = h->glue_used`, then 3 tiny joins
          c0_step
          refine wp_join_group (ts := [i64])
            (fun (gi, ()) m_gi => gi.toNat < 64 ∧ (PlainMem c s ⋆ R) m_gi) ?_ ?_
          · rintro _ ⟨gi, ⟨⟩⟩ m_gi ⟨hgi_lt, hm_gi⟩
            c0_let_simp
            refine wp_join_group (ts := [])
              (fun () m_gu => ∃ heur1, heur1.LengthsOk c ∧
                (PlainMem c { s with heur := heur1 } ⋆ R) m_gu) ?_ ?_
            · rintro _ ⟨⟩ m_gu ⟨heur1, hh1, hm_gu⟩
              c0_let_simp
              refine wp_join_group (ts := [i32])
                (fun (new_u, ()) m_nu => (PlainMem c { s with heur := heur1 } ⋆ R) m_nu) ?_ ?_
              · rintro _ ⟨new_u, ⟨⟩⟩ m_nu hm_nu
                c0_steps
                · obtain ⟨hc', hr', hcl'⟩ :=
                    arenaBumpUsage_preserves_core (hcore.with_heur hh1) href new_u
                  exact hJred () _ ⟨_, heur1, hc', hr', hcl',
                    fun k _ => List.getElem?_set_ne (by omega),
                    by simpa only [bv_c0_zext32_64, hhdr_get,
                      show (134217727 : BitVec 32) = 0x07FFFFFF#32 from rfl,
                      show new_u <<< (27 : BitVec 32) = new_u <<< (27 : Nat) from rfl] using hm⟩
                · exact hJred () _ ⟨s.arena, heur1, hcore.with_heur hh1, rfl,
                    fun _ _ => ⟨rfl, rfl, rfl⟩, fun _ _ => rfl, hm_nu⟩
              · intro Jnu hJnu; c0_steps
                · exact hJnu _ _ hm_gu
                · exact hJnu _ _ hm_gu
            · intro Jgu hJgu; c0_steps
              · refine hJgu () _ ⟨_, ?_, hm⟩
                exact { hlen.heur_ok with glue_used_len := by simp [hgu_len] }
              · exact hJgu () _ ⟨s.heur, hlen.heur_ok, hm_gi⟩
          · intro Jgi hJgi; c0_steps
            · exact hJgi _ _ ⟨by decide, hm⟩
            · refine hJgi _ _ ⟨?_, hm⟩
              simp only [bv_c0, hrsn_mod, BitVec.reduceToNat] at *; omega
        · -- `(hdr & PH_RED) = 0#32`
          c0_steps
          exact hJred () _ ⟨s.arena, s.heur, hcore, rfl, fun _ _ => ⟨rfl, rfl, rfl⟩,
            fun _ _ => rfl, hm⟩

/-! ## 5. Factored 1-UIP semantic helpers for `PlainAnalyzeLemmas` -/

theorem bv64_confl_ref_u32 {r : BitVec 64} (hr : r.toNat < 2 ^ 31 - 1) :
    (r.setWidth 32).toNat = r.toNat ∧ r.setWidth 32 ≠ 0xFFFFFFFF#32 ∧
    (r.setWidth 32 &&& 0x80000000#32) = 0#32 := by
  have hto : (r.setWidth 32).toNat = r.toNat := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
  refine ⟨hto, fun heq => by
    have := congrArg BitVec.toNat heq; rw [hto] at this
    have : (0xFFFFFFFF#32).toNat = 2 ^ 32 - 1 := rfl; omega, ?_⟩
  ext i hi; simp only [BitVec.getElem_and, BitVec.getElem_zero]
  by_cases h31 : i = 31
  · subst h31
    have hb : (r.setWidth 32)[31] = false := by
      rw [BitVec.getElem_eq_testBit_toNat, hto, Nat.testBit, Nat.shiftRight_eq_div_pow,
        Nat.div_eq_of_lt (by omega : r.toNat < 2 ^ 31)]; rfl
    simp [hb]
  · have hm : (0x80000000#32)[i] = false := by
      rw [BitVec.getElem_eq_testBit_toNat]
      have h8 : (0x80000000#32).toNat = 2 ^ 31 := rfl
      rw [h8, Nat.testBit_two_pow]; simp [Ne.symm h31]
    simp [hm]

theorem swap_tmp_get_1 {tmp : List (BitVec 32)} {tl max_idx : Nat}
    (h2 : 2 ≤ tl) (hle : tl ≤ tmp.length) (hm1 : 1 ≤ max_idx) (hmlt : max_idx < tl) :
    ((tmp.set 1 (tmp[max_idx]'(by omega))).set max_idx (tmp[1]'(by omega)))[1]? =
      some (tmp[max_idx]'(by omega)) := by
  by_cases hm : max_idx = 1
  · subst hm; exact List.getElem?_set_self (by simp; omega)
  · rw [List.getElem?_set_ne hm, List.getElem?_set_self (by omega)]

theorem tmp_take2_eq {tmp : List (BitVec 32)} {uip l1 : BitVec 32}
    (h0 : tmp[0]? = some uip) (h1 : tmp[1]? = some l1) :
    (tmp.take 2).map BitVec.toNat = [uip.toNat, l1.toNat] := by
  rcases tmp with _ | ⟨a, _ | ⟨b, ys⟩⟩
  · simp at h0
  · simp at h1
  · simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq] at h0 h1
    subst h0 h1; rfl

theorem ofNat64_pos {n : Nat} (h : ¬ BitVec.ofNat 64 n = 0#64) : 0 < n := by
  cases n with | zero => exact absurd rfl h | succ _ => omega
theorem ofNat64_eq_zero {n : Nat} (hn : n < 2 ^ 64) (h : BitVec.ofNat 64 n = 0#64) : n = 0 := by
  simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn] using congrArg BitVec.toNat h
theorem ofNat64_eq_one {n : Nat} (hn : n < 2 ^ 64) (h : BitVec.ofNat 64 n = 1#64) : n = 1 := by
  simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn] using congrArg BitVec.toNat h

theorem analyze_uip_entails {F0 : CNF Nat} {s : PlainState} {mrk_l : List (BitVec 8)}
    {tmp_l : List (BitVec 32)} {tl_l idx : Nat} {p_bv : BitVec 32}
    (hcl_succ : curLits s mrk_l idx = curLits s mrk_l (idx - 1) ++ [p_bv.toNat ^^^ 1])
    (hct_zero : (curTrailIdxs s mrk_l (idx - 1)).length = 0)
    (hent_l : F0.EntailsClause (cnfClause (activeResolvent s tmp_l mrk_l tl_l idx))) :
    F0.EntailsClause (cnfClause ((p_bv ^^^ 1#32).toNat :: lowerLits tmp_l tl_l)) := by
  have hcl_nil : curLits s mrk_l (idx - 1) = [] := by
    unfold curLits; simp [List.eq_nil_of_length_eq_zero hct_zero]
  unfold activeResolvent at hent_l; rw [hcl_succ, hcl_nil, List.nil_append] at hent_l
  refine entails_of_mem_or_false hent_l fun l hl => Or.inl ?_
  rcases List.mem_append.mp hl with h1 | h2
  · exact List.mem_cons_of_mem _ h1
  · simp only [List.mem_singleton] at h2; rw [h2, ← bv32_xor_1]; exact List.mem_cons_self

theorem analyze_resolve_sem {c : PlainCfg} {F0 : CNF Nat} {s : PlainState}
    (hcore : PlainCoreInv c F0 s) {mrk_l mrk2 : List (BitVec 8)} {tmp_l tmp2 : List (BitVec 32)}
    {tc_l tc2 tl_l tl2 idx : Nat} {arena_l arena2 : List (BitVec 32)}
    {heur_l heur2 : PlainHeur} {p_bv rsn_bv : BitVec 32}
    (hidx_pos : 0 < idx) (hidx_le : idx ≤ s.trail_end)
    (hp_get : (s.trl[idx - 1]?.getD 0#32).toNat = p_bv.toNat)
    (hrsn_get : s.rsns[(s.trl[idx - 1]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 = rsn_bv)
    (hrsn_ne : rsn_bv ≠ 0xFFFFFFFF#32)
    (hcore_l1 : PlainCoreInv c F0 { s with
      mrk := mrk_l, tmp := tmp_l, tmp_cnt := tc_l - 1, tmp_len := tl_l,
      arena := arena_l, heur := heur_l })
    (hcore2 : PlainCoreInv c F0 { s with
      mrk := mrk2, tmp := tmp2, tmp_cnt := tc2, tmp_len := tl2,
      arena := arena2, heur := heur2 })
    (htl1 : 1 ≤ tl_l) (htl2_ge : tl_l ≤ tl2) (htl2_le : tl2 ≤ c.mv)
    (htc_sub : tc_l - 1 = (curTrailIdxs s mrk_l (idx - 1)).length) (htc2_ge : tc_l - 1 ≤ tc2)
    (hcl_succ : curLits s mrk_l idx = curLits s mrk_l (idx - 1) ++ [p_bv.toNat ^^^ 1])
    (hlow_l : LowerInv c s tmp_l mrk_l tl_l) (hcov_l : MarksCov c s tmp_l mrk_l tl_l)
    (hent_l : F0.EntailsClause (cnfClause (activeResolvent s tmp_l mrk_l tl_l idx)))
    (hmp2 : ∀ v < c.mv, mrk_l[v]?.getD 0#8 ≠ 0#8 → mrk2[v]?.getD 0#8 = mrk_l[v]?.getD 0#8)
    (htp2 : ∀ k < tl_l, tmp2[k]? = tmp_l[k]?)
    (hnm2 : ∀ v < c.mv, mrk_l[v]?.getD 0#8 = 0#8 → mrk2[v]?.getD 0#8 ≠ 0#8 →
      ∃ l ∈ rsnLits { s with
        mrk := mrk_l, tmp := tmp_l, tmp_cnt := tc_l - 1, tmp_len := tl_l,
        arena := arena_l, heur := heur_l } rsn_bv, l / 2 = v ∧ v ≠ p_bv.toNat / 2 ∧
        0 < (s.lvl[v]?.getD 0#32).toNat ∧ (s.lvl[v]?.getD 0#32).toNat ≤ s.cur_level)
    (hnt2 : ∀ j, tl_l ≤ j → j < tl2 → let l := (tmp2[j]?.getD 0#32).toNat
      l ∈ rsnLits { s with
        mrk := mrk_l, tmp := tmp_l, tmp_cnt := tc_l - 1, tmp_len := tl_l,
        arena := arena_l, heur := heur_l } rsn_bv ∧ l < 2 * c.mv ∧ l / 2 ≠ p_bv.toNat / 2 ∧
      mrk_l[l / 2]?.getD 0#8 = 0#8 ∧ 0 < (s.lvl[l / 2]?.getD 0#32).toNat ∧
      (s.lvl[l / 2]?.getD 0#32).toNat < s.cur_level ∧ mrk2[l / 2]?.getD 0#8 ≠ 0#8)
    (hcnt2 : tc2 - (tc_l - 1) = ((List.range c.mv).filter fun v =>
      decide (mrk_l[v]?.getD 0#8 = 0#8) && decide (mrk2[v]?.getD 0#8 ≠ 0#8) &&
      decide ((s.lvl[v]?.getD 0#32).toNat = s.cur_level)).length)
    (hall2 : ∀ l ∈ rsnLits { s with
      mrk := mrk_l, tmp := tmp_l, tmp_cnt := tc_l - 1, tmp_len := tl_l,
      arena := arena_l, heur := heur_l } rsn_bv,
      l / 2 < c.mv ∧ (l / 2 ≠ p_bv.toNat / 2 →
        (0 < (s.lvl[l / 2]?.getD 0#32).toNat → mrk2[l / 2]?.getD 0#8 ≠ 0#8) ∧
        (mrk_l[l / 2]?.getD 0#8 = 0#8 → (s.lvl[l / 2]?.getD 0#32).toNat ≤ s.cur_level ∧
          (0 < (s.lvl[l / 2]?.getD 0#32).toNat → (s.lvl[l / 2]?.getD 0#32).toNat < s.cur_level →
            ∃ j, tl_l ≤ j ∧ j < tl2 ∧ (tmp2[j]?.getD 0#32).toNat / 2 = l / 2)))) :
    tc2 = (curTrailIdxs s mrk2 (idx - 1)).length ∧ LowerInv c s tmp2 mrk2 tl2 ∧
    MarksCov c s tmp2 mrk2 tl2 ∧
    F0.EntailsClause (cnfClause (activeResolvent s tmp2 mrk2 tl2 (idx - 1))) := by
  let sl1 : PlainState := { s with
    mrk := mrk_l, tmp := tmp_l, tmp_cnt := tc_l - 1,
    tmp_len := tl_l, arena := arena_l, heur := heur_l }
  have hrinv := hcore_l1.reason_inv (idx - 1) (by dsimp [sl1]; omega)
    (by dsimp [sl1]; rwa [hrsn_get])
  dsimp only [sl1] at hrinv; rw [hrsn_get, hp_get] at hrinv
  have hrinv_bin : (rsn_bv &&& 0x80000000#32) ≠ 0#32 →
      (rsn_bv &&& 0x7FFFFFFF#32).toNat < 2 * c.mv ∧
      F0.EntailsClause (cnfClause [p_bv.toNat, (rsn_bv &&& 0x7FFFFFFF#32).toNat]) ∧
      ∃ k < idx - 1, (s.trl[k]?.getD 0#32).toNat = (rsn_bv &&& 0x7FFFFFFF#32).toNat ^^^ 1 := by
    intro hb; split at hrinv
    · exact hrinv
    · rename_i h; exact absurd hb h
  have hrinv_large : (rsn_bv &&& 0x80000000#32) = 0#32 →
      rsn_bv.toNat ∈ arenaClauseRefs sl1 ∧ arenaClauseGarb sl1 rsn_bv.toNat = false ∧
      ∀ q ∈ arenaClauseLits sl1 rsn_bv.toNat,
        q = p_bv.toNat ∨ ∃ k < idx - 1, (s.trl[k]?.getD 0#32).toNat = q ^^^ 1 := by
    intro hlo; split at hrinv
    · rename_i h; exact absurd hlo h
    · exact hrinv
  have hlits_lt_r : ∀ q, q ∈ rsnLits sl1 rsn_bv → q < 2 * c.mv := fun q hq => by
    by_cases hb : (rsn_bv &&& 0x80000000#32) ≠ 0#32
    · rw [mem_rsnLits_bin hrsn_ne hb] at hq; subst hq; exact (hrinv_bin hb).1
    · have hlo := Classical.byContradiction hb; rw [mem_rsnLits_large hrsn_ne hlo] at hq
      obtain ⟨h1, h2, _⟩ := hrinv_large hlo; exact hcore_l1.arena.lits_lt rsn_bv.toNat h1 h2 q hq
  have hclause_r : ∀ q, q ∈ rsnLits sl1 rsn_bv →
      q / 2 = p_bv.toNat / 2 ∨ ∃ k < idx - 1, (s.trl[k]?.getD 0#32).toNat = q ^^^ 1 := by
    intro q hq; by_cases hb : (rsn_bv &&& 0x80000000#32) ≠ 0#32
    · rw [mem_rsnLits_bin hrsn_ne hb] at hq; subst hq; exact Or.inr (hrinv_bin hb).2.2
    · have hlo := Classical.byContradiction hb; rw [mem_rsnLits_large hrsn_ne hlo] at hq
      exact ((hrinv_large hlo).2.2 q hq).elim (fun he => Or.inl (by rw [he])) Or.inr
  obtain ⟨htc2_eq, hlow2, hcov2, hlow_sub, hcur_sub, hq2⟩ :=
    analyzeStep_preserves hcore (fun q => q ∈ rsnLits sl1 rsn_bv) (by omega) htl1 htl2_ge htl2_le
      hcore_l1.lengths.tmp_len_arr hcore2.lengths.tmp_len_arr htc_sub htc2_ge hlow_l hcov_l
      hlits_lt_r hclause_r hmp2 htp2 hnm2
      (fun j h1 h2 => let ⟨a, b, d, _, e, f, g⟩ := hnt2 j h1 h2; ⟨a, b, d, e, f, g⟩) hcnt2 hall2
  refine ⟨htc2_eq, hlow2, hcov2, ?_⟩
  have hres_right : ∀ l ∈ activeResolvent s tmp_l mrk_l tl_l idx,
      l = p_bv.toNat ^^^ 1 ∨ l ∈ activeResolvent s tmp2 mrk2 tl2 (idx - 1) ∨
        F0.EntailsClause (cnfClause [litNeg l]) := fun l hl => by
    unfold activeResolvent at hl
    rcases List.mem_append.mp hl with hl1 | hl2
    · exact Or.inr (Or.inl (List.mem_append_left _ (hlow_sub l hl1)))
    · rw [hcl_succ] at hl2
      rcases List.mem_append.mp hl2 with hl2a | hl2b
      · exact Or.inr (Or.inl (List.mem_append_right _ (hcur_sub l hl2a)))
      · simp only [List.mem_singleton] at hl2b; exact Or.inl hl2b
  by_cases hb : (rsn_bv &&& 0x80000000#32) ≠ 0#32
  · obtain ⟨_, hent_b, k, hk, hkeq⟩ := hrinv_bin hb
    refine entails_resolve_to (p := p_bv.toNat) hent_b hent_l (fun q hq => ?_) hres_right
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact Or.inl rfl
    · rcases hq2 _ ((mem_rsnLits_bin hrsn_ne hb).mpr rfl) with hv_eq | hmem | hf
      · have := hcore.trail_vars_nodup k (idx - 1) (by omega) (by omega)
          (by rw [hkeq, hp_get]; exact (litVar_litNeg _).trans hv_eq); omega
      · exact Or.inr (Or.inl hmem)
      · exact Or.inr (Or.inr hf)
  · have hlo := Classical.byContradiction hb; obtain ⟨h1, h2, h3⟩ := hrinv_large hlo
    refine entails_resolve_to (p := p_bv.toNat)
      (hcore_l1.arena.entails rsn_bv.toNat h1 h2) hent_l (fun q hq => ?_) hres_right
    rcases hq2 q ((mem_rsnLits_large hrsn_ne hlo).mpr hq) with hv_eq | hmem | hf
    · rcases h3 q hq with rfl | ⟨k, hk, hkeq⟩
      · exact Or.inl rfl
      · have := hcore.trail_vars_nodup k (idx - 1) (by omega) (by omega)
          (by rw [hkeq, hp_get]; exact (litVar_litNeg q).trans hv_eq); omega
    · exact Or.inr (Or.inl hmem)
    · exact Or.inr (Or.inr hf)

theorem curTrailIdxs_of_marksClear {c : PlainCfg} {F0 : CNF Nat} {s : PlainState}
    (hinv : PlainInv c F0 s) : (curTrailIdxs s s.mrk s.trail_end).length = 0 := by
  unfold curTrailIdxs; rw [List.filter_eq_nil_iff.mpr fun j hj => by
    have := hinv.core.trail_lits_lt j (List.mem_range.mp hj)
    simp [hinv.marks ((s.trl[j]?.getD 0#32).toNat / 2) (by omega)]]; rfl

theorem analyze_large_seed_sem {c : PlainCfg} {F0 : CNF Nat} {s : PlainState}
    (hinv : PlainInv c F0 s) {mrk1 : List (BitVec 8)} {tmp1 : List (BitVec 32)} {tc1 tl1 : Nat}
    (href : s.confl_ref.toNat ∈ arenaClauseRefs s)
    (hng : arenaClauseGarb s s.confl_ref.toNat = false)
    (hfals : ∀ l ∈ arenaClauseLits s s.confl_ref.toNat, s.vals[l]?.getD 0#8 = 0xFF#8)
    (hcr_nat : (s.confl_ref.setWidth 32).toNat = s.confl_ref.toNat)
    (hcr_ne : s.confl_ref.setWidth 32 ≠ 0xFFFFFFFF#32)
    (hcr_lo : (s.confl_ref.setWidth 32 &&& 0x80000000#32) = 0#32)
    (htl1_ge : 1 ≤ tl1) (htl1_mv : tl1 ≤ c.mv) (ht_len1 : tmp1.length = c.mv)
    (hmp1 : ∀ v < c.mv, s.mrk[v]?.getD 0#8 ≠ 0#8 → mrk1[v]?.getD 0#8 = s.mrk[v]?.getD 0#8)
    (htp1 : ∀ k < 1, tmp1[k]? = s.tmp[k]?)
    (hnm1 : ∀ v < c.mv, s.mrk[v]?.getD 0#8 = 0#8 → mrk1[v]?.getD 0#8 ≠ 0#8 →
      ∃ l ∈ rsnLits { s with tmp_cnt := 0, tmp_len := 1 } (s.confl_ref.setWidth 32),
        l / 2 = v ∧ v ≠ (0xFFFFFFFF#32).toNat ∧
        0 < (s.lvl[v]?.getD 0#32).toNat ∧ (s.lvl[v]?.getD 0#32).toNat ≤ s.cur_level)
    (hnt1 : ∀ j, 1 ≤ j → j < tl1 → let l := (tmp1[j]?.getD 0#32).toNat
      l ∈ rsnLits { s with tmp_cnt := 0, tmp_len := 1 } (s.confl_ref.setWidth 32) ∧
      l < 2 * c.mv ∧ l / 2 ≠ (0xFFFFFFFF#32).toNat ∧ s.mrk[l / 2]?.getD 0#8 = 0#8 ∧
      0 < (s.lvl[l / 2]?.getD 0#32).toNat ∧ (s.lvl[l / 2]?.getD 0#32).toNat < s.cur_level ∧
      mrk1[l / 2]?.getD 0#8 ≠ 0#8)
    (hcnt1 : tc1 - 0 = ((List.range c.mv).filter fun v =>
      decide (s.mrk[v]?.getD 0#8 = 0#8) && decide (mrk1[v]?.getD 0#8 ≠ 0#8) &&
      decide ((s.lvl[v]?.getD 0#32).toNat = s.cur_level)).length)
    (hall1 : ∀ l ∈ rsnLits { s with tmp_cnt := 0, tmp_len := 1 } (s.confl_ref.setWidth 32),
      l / 2 < c.mv ∧ (l / 2 ≠ (0xFFFFFFFF#32).toNat →
        (0 < (s.lvl[l / 2]?.getD 0#32).toNat → mrk1[l / 2]?.getD 0#8 ≠ 0#8) ∧
        (s.mrk[l / 2]?.getD 0#8 = 0#8 → (s.lvl[l / 2]?.getD 0#32).toNat ≤ s.cur_level ∧
          (0 < (s.lvl[l / 2]?.getD 0#32).toNat → (s.lvl[l / 2]?.getD 0#32).toNat < s.cur_level →
            ∃ j, 1 ≤ j ∧ j < tl1 ∧ (tmp1[j]?.getD 0#32).toNat / 2 = l / 2)))) :
    tc1 = (curTrailIdxs s mrk1 s.trail_end).length ∧ LowerInv c s tmp1 mrk1 tl1 ∧
    MarksCov c s tmp1 mrk1 tl1 ∧
    F0.EntailsClause (cnfClause (activeResolvent s tmp1 mrk1 tl1 s.trail_end)) := by
  have hcore := hinv.core; have hmv := c.hmv; unfold dimacsBound at hmv
  have hct0 : (curTrailIdxs s s.mrk s.trail_end).length = 0 := curTrailIdxs_of_marksClear hinv
  have hmem_iff : ∀ q, q ∈ rsnLits { s with tmp_cnt := 0, tmp_len := 1 }
      (s.confl_ref.setWidth 32) ↔ q ∈ arenaClauseLits s s.confl_ref.toNat := fun _ => by
    rw [mem_rsnLits_large hcr_ne hcr_lo, hcr_nat]; rfl
  obtain ⟨htc1_eq, hlow1, hcov1, _, _, hq1⟩ :=
    analyzeStep_preserves hcore (fun q => q ∈ arenaClauseLits s s.confl_ref.toNat)
      (Nat.le_refl _) (Nat.le_refl _) htl1_ge htl1_mv hcore.lengths.tmp_len_arr ht_len1
      hct0.symm (Nat.zero_le _) (fun _ h1 h2 => by omega)
      (fun v hv hnz => absurd (hinv.marks v hv) hnz)
      (fun q hq => hcore.arena.lits_lt s.confl_ref.toNat href hng q hq)
      (fun q hq => Or.inr ((hcore.vals_false_iff q
        (hcore.arena.lits_lt s.confl_ref.toNat href hng q hq)).mp (hfals q hq)))
      hmp1 htp1 (fun v hv h0 hz => let ⟨l, hl, hr⟩ := hnm1 v hv h0 hz; ⟨l, (hmem_iff l).mp hl, hr⟩)
      (fun j h1 h2 => let ⟨a, b, d, _, e, f, g⟩ := hnt1 j h1 h2; ⟨(hmem_iff _).mp a, b, d, e, f, g⟩)
      hcnt1 (fun l hl => hall1 l ((hmem_iff l).mpr hl))
  refine ⟨htc1_eq, hlow1, hcov1, entails_of_mem_or_false
    (hcore.arena.entails s.confl_ref.toNat href hng) fun q hq => ?_⟩
  rcases hq1 q hq with hskip | hmem | hf
  · have := hcore.arena.lits_lt s.confl_ref.toNat href hng q hq
    have : (0xFFFFFFFF#32).toNat = 2 ^ 32 - 1 := rfl; omega
  · exact Or.inl hmem
  · exact Or.inr hf

end LeanQbe.T.Examples.Kissat.Plain
