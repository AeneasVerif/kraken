module

public import LeanQbe.T.Examples.Kissat.FullM7Bump
public import LeanQbe.T.Examples.Kissat.FullSpec2
public import LeanQbe.T.Examples.Kissat.FullOneLitConflLemmas
import LeanQbe.T.AbiLemmas
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Logic.Bytes
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.Cells
import LeanQbe.T.Logic.ControlComb
import LeanQbe.T.Logic.MemLemmas
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Wave-4H Proofs: `Func.wp`, `ModuleOk`, & UNSAT Non-Vacuity (`FullM7BumpProof`)

M1-clean verification (`public section`, zero `@[expose]`) for `FullM7Bump`:
1. Exact Knuth LCG spec (`m7RngNextExactSpec`) and canonical `Full.fullRngNextSpec` for
   `full_rng_next_m7`.
2. `m7Log10Q16Spec` & `m7ScaleDeltaSpec` (preserving `FullSafetySlice`, certifying `delta = 0 -> 0`
   and `delta <= scaled`) for `full_log10_q16_m7` and `full_scale_delta_m7`.
3. `m7BumpSiftSpec` & `m7BumpSortStampsSpec` (certifying permutation AND ascending `(q_stamp, v)`
   order `BumpSortedAsc`), `m7BumpReasonsSpec`, and canonical `Full.fullBumpAnalyzedSpec` for
   `full_bump_analyzed_m7` (preserving `FullAnaMarksCov`, `LengthsOk`, `FullExtScratchPres`, and
   `work_stk2`).
4. Closed `10`-row `m7BumpSpecTable`, `m7BumpEnv`, `m7BumpEnv_noExit`, `m7Bump_moduleOk`, and
   drop-in correctness (`m7RngNextFn_wp`, `m7ScaleDeltaFn_wp`, `m7ScaleDeltaM6Fn_wp`,
   `m7BumpAnalyzedFn_wp`).
5. Concrete `Mem 64` UNSAT non-vacuity (`nv_m7_rng_next`, `nv_m7_scale_delta`,
   `nv_m7_bump_analyzed`, `XPost := False`, `0` model-finding proofs).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM7Bump

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open Kraken.Bedrock2.Test

/-! ## 1. Public Specifications & Ordering Predicates -/

/-- Exact 64-bit Knuth LCG update value for `kissat_next_random64`. -/
def m7KnuthNext (x : BitVec 64) : BitVec 64 :=
  x * 6364136223846793005#64 + 1442695040888963407#64

/-- Stronger functional spec for `full_rng_next_m7` certifying exact Knuth LCG recurrence. -/
def m7RngNextExactSpec : Spec [i64] [i64] :=
  SafetySlice.spec fullSafetySlice
    (fun c (h, ()) _ => h = c.hdr)
    (fun _ _ (r, ()) s s' =>
      let nxt := m7KnuthNext s.scratch.rng_state
      s'.scratch = { s.scratch with rng_state := s'.scratch.rng_state } ∧
      r = nxt >>> 32#64 ∧ s'.scratch.rng_state = nxt)

/-- Bounded Q16 `log10` specification (`r < 20 * 65536` and `10 <= x -> 65536 <= r`). -/
def m7Log10Q16Spec : Spec [i64] [i64] := fun (x, ()) m Q _ =>
  ∀ r : BitVec 64, r.toNat < 20 * 65536 → (10 ≤ x.toNat → 65536 ≤ r.toNat) → Q (r, ()) m

/-- Safety-slice scaling specification for `full_scale_delta_m7` preserving state identically and
guaranteeing `delta = 0 -> 0` and `delta.toNat <= r.toNat`. -/
def m7ScaleDeltaSpec : Spec [i64, i64] [i64] :=
  SafetySlice.spec fullSafetySlice
    (fun c (h, _, ()) _ => h = c.hdr)
    (fun _ (_, delta, ()) (r, ()) s s' =>
      s' = s ∧ (delta = 0#64 → r = 0#64) ∧ delta.toNat ≤ r.toNat)

/-- Legacy M6-compatible scale-delta specification (`s' = s`, matches `FullM6Tiers`). -/
def m7ScaleDeltaCompatSpec : Spec [i64, i64] [i64] :=
  SafetySlice.spec fullSafetySlice
    (fun c (h, _, ()) _ => h = c.hdr)
    (fun _ _ _ s s' => s' = s)

/-- Lexicographic key `(q_stamp[v], v)` matching `full_bump_sift_m7`. -/
def bumpStampKey (cv : Nat) (qs : List (BitVec 32)) (v : BitVec 32) : Nat × Nat :=
  let q := if v.toNat < cv then (qs[v.toNat]?.getD 0#32).toNat else 0
  (q, v.toNat)

/-- Total preorder on analyzed variables by `(q_stamp[v], v)`. -/
def bumpStampLe (cv : Nat) (qs : List (BitVec 32)) (a b : BitVec 32) : Prop :=
  let ka := bumpStampKey cv qs a
  let kb := bumpStampKey cv qs b
  ka.1 < kb.1 ∨ (ka.1 = kb.1 ∧ ka.2 ≤ kb.2)

/-- Max-heap invariant on `ws[lo ..< n)` ordered by `bumpStampLe cv qs`. -/
def FullBumpMaxHeap (cv : Nat) (qs ws : List (BitVec 32)) (lo n : Nat) : Prop :=
  ∀ i, lo ≤ i → i < n →
    (2 * i + 1 < n → bumpStampLe cv qs (ws[2 * i + 1]?.getD 0#32) (ws[i]?.getD 0#32)) ∧
    (2 * i + 2 < n → bumpStampLe cv qs (ws[2 * i + 2]?.getD 0#32) (ws[i]?.getD 0#32))

/-- Ascending sortedness on `ws[0 ..< n)` under `bumpStampLe cv qs`. -/
def BumpSortedAsc (cv n : Nat) (qs ws : List (BitVec 32)) : Prop :=
  ∀ i j, i ≤ j → j < n → bumpStampLe cv qs (ws[i]?.getD 0#32) (ws[j]?.getD 0#32)

/-- Heap sift contract for `full_bump_sift_m7(h, start, n)`. -/
def m7BumpSiftSpec : Spec [i64, i64, i64] [] :=
  fun (h, start, n, ()) m Q _ =>
    ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧
      start.toNat < n.toNat ∧ n.toNat ≤ s.core.cur_vars ∧
      FullBumpMaxHeap s.core.cur_vars s.scratch.q_stamp s.scratch.work_stk1
        (start.toNat + 1) n.toNat ∧
      (FullMem c s ⋆ R) m ∧
      ∀ ws1' m',
        ws1'.length = 2 * c.max_vars →
        (ws1'.take n.toNat).Perm (s.scratch.work_stk1.take n.toNat) →
        (∀ k, n.toNat ≤ k → ws1'[k]? = s.scratch.work_stk1[k]?) →
        FullBumpMaxHeap s.core.cur_vars s.scratch.q_stamp ws1' start.toNat n.toNat →
        (FullMem c { s with scratch := { s.scratch with work_stk1 := ws1' } } ⋆ R) m' →
        Q () m'

/-- Ascending `q_stamp` heapsort contract for `full_bump_sort_stamps_m7(h, n)`. -/
def m7BumpSortStampsSpec : Spec [i64, i64] [] := fun (h, n, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ n.toNat ≤ s.core.cur_vars ∧
    (FullMem c s ⋆ R) m ∧
    ∀ ws1' m',
      ws1'.length = 2 * c.max_vars →
      (ws1'.take n.toNat).Perm (s.scratch.work_stk1.take n.toNat) →
      (∀ k, n.toNat ≤ k → ws1'[k]? = s.scratch.work_stk1[k]?) →
      BumpSortedAsc s.core.cur_vars n.toNat s.scratch.q_stamp ws1' →
      (FullMem c { s with scratch := { s.scratch with work_stk1 := ws1' } } ⋆ R) m' →
      Q () m'

/-- Reason-side literal marking & rollback contract for `full_bump_reasons_m7(h)`. -/
def m7BumpReasonsSpec : Spec [i64] [] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ FullAnaMarksCov c s ∧ (FullMem c s ⋆ R) m ∧
    ∀ mrk' mcl' ws1' m',
      let s' : FullState :=
        { core := { s.core with mrk := mrk', min_clr_len := mcl' }
          scratch := { s.scratch with work_stk1 := ws1' } }
      s'.LengthsOk c → FullAnaMarksCov c s' → (FullMem c s' ⋆ R) m' → Q () m'

/-! ## 2. Private Arithmetic, Heap, Permutation & Mark-Coverage Helpers -/

section BumpHelpers

private theorem zext32_toNat (x : BitVec 32) : (BitVec.setWidth 64 x).toNat = x.toNat :=
  zext_toNat x (by decide)

private theorem bv32_ofNat_toNat' {n : Nat} (hn : n < 2 ^ 32) :
    (BitVec.ofNat 32 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]

private theorem bv64_ofNat_toNat' {n : Nat} (hn : n < 2 ^ 64) :
    (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]

private theorem pow10_lt_64 {d : Nat} (hd : d ≤ 19) : 10 ^ d < 2 ^ 64 := by
  have h1 : 10 ^ d ≤ 10 ^ 19 := Nat.pow_le_pow_right (by decide) hd
  exact Nat.lt_of_le_of_lt h1 (by decide)

private theorem shift_split_65536 {k : Nat} (hk : k < 16) :
    (65536 >>> k) = (32768 >>> k) + (65536 >>> (k + 1)) := by
  have hk_cases : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨
      k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨ k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15 := by omega
  rcases hk_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

private theorem bumpStampLe_refl (cv : Nat) (qs : List (BitVec 32)) (a : BitVec 32) :
    bumpStampLe cv qs a a :=
  Or.inr ⟨rfl, Nat.le_refl _⟩

private theorem bumpStampLe_trans {cv : Nat} {qs : List (BitVec 32)} {a b c : BitVec 32}
    (hab : bumpStampLe cv qs a b) (hbc : bumpStampLe cv qs b c) :
    bumpStampLe cv qs a c := by
  rcases hab with ha | ⟨ha1, ha2⟩ <;> rcases hbc with hb | ⟨hb1, hb2⟩
  · exact Or.inl (Nat.lt_trans ha hb)
  · exact Or.inl (hb1 ▸ ha)
  · exact Or.inl (ha1 ▸ hb)
  · exact Or.inr ⟨ha1.trans hb1, Nat.le_trans ha2 hb2⟩

private theorem bumpStampLe_total (cv : Nat) (qs : List (BitVec 32)) (a b : BitVec 32) :
    bumpStampLe cv qs a b ∨ bumpStampLe cv qs b a := by
  unfold bumpStampLe bumpStampKey
  omega

private theorem maxHeap_root_ge {cv : Nat} {qs ws : List (BitVec 32)} {n : Nat}
    (hheap : FullBumpMaxHeap cv qs ws 0 n) :
    ∀ i, i < n → bumpStampLe cv qs (ws[i]?.getD 0#32) (ws[0]?.getD 0#32) := by
  intro i
  induction i using Nat.strongRecOn with
  | ind i ih =>
    intro hi
    cases i with
    | zero => exact bumpStampLe_refl cv qs _
    | succ k =>
      let p := k / 2
      have hp_lt : p < k + 1 := Nat.lt_of_le_of_lt (Nat.div_le_self k 2) (Nat.lt_succ_self k)
      have hp_n : p < n := Nat.lt_trans hp_lt hi
      have hparent := ih p hp_lt hp_n
      have hchild := hheap p (Nat.zero_le _) hp_n
      have heq : 2 * p + 1 = k + 1 ∨ 2 * p + 2 = k + 1 := by omega
      rcases heq with h1 | h2
      · have hc : ws[k + 1]?.getD 0#32 = ws[2 * p + 1]?.getD 0#32 := by rw [h1]
        rw [hc]; exact bumpStampLe_trans (hchild.1 (by omega)) hparent
      · have hc : ws[k + 1]?.getD 0#32 = ws[2 * p + 2]?.getD 0#32 := by rw [h2]
        rw [hc]; exact bumpStampLe_trans (hchild.2 (by omega)) hparent

private def swapIdx (i j k : Nat) : Nat :=
  if k = i then j else if k = j then i else k

private theorem swap_getElem?_eq {α : Type} [Inhabited α] (d : α) (xs : List α)
    {i j : Nat} (hi : i < xs.length) (hj : j < xs.length) (k : Nat) :
    ((xs.set i (xs[j]'hj)).set j (xs[i]'hi))[k]?.getD d =
      xs[swapIdx i j k]?.getD d := by
  unfold swapIdx
  by_cases hkj : k = j
  · subst hkj; rw [List.getElem?_set_self (by simp; omega)]
    by_cases hki : k = i <;> simp [hki, List.getElem?_eq_getElem hi]
  · rw [List.getElem?_set_ne (by omega)]
    by_cases hki : k = i
    · subst hki; rw [List.getElem?_set_self (by omega)]; simp [List.getElem?_eq_getElem hj]
    · rw [List.getElem?_set_ne (by omega)]; simp [hki, hkj]

private theorem swap_getElem?_raw {α : Type} (xs : List α) {i j : Nat}
    (hi : i < xs.length) (hj : j < xs.length) (k : Nat) :
    ((xs.set i (xs[j]'hj)).set j (xs[i]'hi))[k]? = xs[swapIdx i j k]? := by
  unfold swapIdx
  by_cases hkj : k = j
  · subst hkj; rw [List.getElem?_set_self (by simp; omega)]
    by_cases hki : k = i <;> simp [hki, List.getElem?_eq_getElem hi]
  · rw [List.getElem?_set_ne (by omega)]
    by_cases hki : k = i
    · subst hki; rw [List.getElem?_set_self (by omega)]; simp [List.getElem?_eq_getElem hj]
    · rw [List.getElem?_set_ne (by omega)]; simp [hki, hkj]

private theorem count_set_eq {α : Type} [DecidableEq α] (l : List α) (i : Nat) (v x : α)
    (hi : i < l.length) :
    (l.set i v).count x + (if l[i] = x then 1 else 0) =
      l.count x + (if v = x then 1 else 0) := by
  induction l generalizing i with
  | nil => simp at hi
  | cons a t ih =>
    cases i with
    | zero =>
      simp only [List.set_cons_zero, List.getElem_cons_zero, List.count_cons, beq_iff_eq]
      by_cases hax : a = x <;> by_cases hvx : v = x <;> simp [hax, hvx] <;> omega
    | succ i' =>
      simp only [List.set_cons_succ, List.getElem_cons_succ, List.count_cons, beq_iff_eq]
      have hih := ih i' (by simpa using hi)
      omega

private theorem take_set_of_lt {α : Type} (xs : List α) (i n : Nat) (v : α) (hi : i < n) :
    (xs.set i v).take n = (xs.take n).set i v := by
  induction xs generalizing i n with
  | nil => simp
  | cons a t ih =>
    cases n with
    | zero => omega
    | succ n' =>
      cases i with
      | zero => simp
      | succ i' => simp [ih i' n' (by omega)]

private theorem swap_perm_aux {α : Type} [DecidableEq α] (xs : List α) {i j : Nat}
    (hi : i < xs.length) (hj : j < xs.length) :
    ((xs.set i (xs[j]'hj)).set j (xs[i]'hi)).Perm xs := by
  rw [List.perm_iff_count]
  intro x
  have h1 := count_set_eq xs i (xs[j]'hj) x hi
  have h2 := count_set_eq (xs.set i (xs[j]'hj)) j (xs[i]'hi) x (by rw [List.length_set]; exact hj)
  by_cases hij : j = i
  · subst hij
    have hxi : (xs.set j (xs[j]'hj))[j]'(by rw [List.length_set]; exact hj) = xs[j]'hj := by
      simp
    rw [hxi] at h2
    omega
  · have hxj : (xs.set i (xs[j]'hj))[j]'(by rw [List.length_set]; exact hj) = xs[j]'hj :=
      List.getElem_set_ne (Ne.symm hij) _
    rw [hxj] at h2
    omega

private theorem swap_perm_take {α : Type} [DecidableEq α] (xs : List α) {i j n : Nat}
    (hi : i < n) (hj : j < n) (hn : n ≤ xs.length) :
    (((xs.set i (xs[j]'(by omega))).set j (xs[i]'(by omega))).take n).Perm (xs.take n) := by
  rw [take_set_of_lt _ j n _ hj, take_set_of_lt _ i n _ hi]
  have hln : (xs.take n).length = n := by rw [List.length_take]; exact Nat.min_eq_left hn
  have hti : (xs.take n)[i]'(by rw [hln]; exact hi) = xs[i]'(by omega) := List.getElem_take
  have htj : (xs.take n)[j]'(by rw [hln]; exact hj) = xs[j]'(by omega) := List.getElem_take
  have hp := swap_perm_aux (xs.take n) (by rw [hln]; exact hi) (by rw [hln]; exact hj)
  rwa [hti, htj] at hp

private theorem take_split_add {α : Type} (xs : List α) {m n : Nat} (hmn : m ≤ n) :
    xs.take n = xs.take m ++ (xs.drop m).take (n - m) := by
  induction xs generalizing m n with
  | nil => simp
  | cons a t ih =>
    cases m with
    | zero => simp
    | succ m' =>
      cases n with
      | zero => omega
      | succ n' =>
        simp only [List.take_succ_cons, List.drop_succ_cons, List.cons_append,
          Nat.succ_sub_succ_eq_sub]
        exact congrArg (a :: ·) (ih (by omega))

private theorem perm_take_smaller {α : Type} {xs ys : List α} {m n : Nat}
    (hmn : m ≤ n) (hperm : (xs.take m).Perm (ys.take m))
    (heq : ∀ k, m ≤ k → xs[k]? = ys[k]?)
    (_hxl : n ≤ xs.length) (_hyl : n ≤ ys.length) :
    (xs.take n).Perm (ys.take n) := by
  have hx := take_split_add xs hmn
  have hy := take_split_add ys hmn
  have hdrop : (xs.drop m).take (n - m) = (ys.drop m).take (n - m) := by
    refine List.ext_getElem? fun k => ?_
    rw [List.getElem?_take, List.getElem?_take]
    by_cases hk : k < n - m
    · simp only [hk, ↓reduceIte, List.getElem?_drop]; exact heq (m + k) (by omega)
    · simp only [hk, ↓reduceIte]
  rw [hx, hy, hdrop]
  exact hperm.append_right _

private theorem take_set_append_one {α : Type} (xs : List α) {n : Nat} (v : α)
    (hn : n < xs.length) :
    (xs.set n v).take (n + 1) = xs.take n ++ [v] := by
  induction xs generalizing n with
  | nil => simp at hn
  | cons a t ih =>
    cases n with
    | zero => simp
    | succ n' =>
      simp only [List.set_cons_succ, List.take_succ_cons, List.cons_append]
      exact congrArg (a :: ·) (ih (by simpa using hn))

private theorem nodup_map_take_set {xs : List (BitVec 32)} {n : Nat} {v : BitVec 32}
    (hn : n < xs.length)
    (hnd : ((xs.take n).map BitVec.toNat).Nodup)
    (hfresh : ∀ k < n, (xs[k]?.getD 0#32).toNat ≠ v.toNat) :
    (((xs.set n v).take (n + 1)).map BitVec.toNat).Nodup := by
  rw [take_set_append_one xs v hn, List.map_append, List.map_singleton, List.nodup_append]
  refine ⟨hnd, by simp, fun a ha b hb he => ?_⟩
  simp only [List.mem_singleton] at hb; subst hb; subst he
  rw [List.mem_map] at ha
  obtain ⟨u, hu, hua⟩ := ha
  rw [List.mem_iff_getElem] at hu
  obtain ⟨k, hk, huk⟩ := hu
  rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hn)] at hk
  rw [List.getElem_take] at huk
  have hkget : (xs[k]?.getD 0#32).toNat = v.toNat := by
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some, huk, hua]
  exact absurd hkget (hfresh k hk)

private theorem anaMarksCov_perm {c : FullCfg} {s : FullState} {ws1' : List (BitVec 32)}
    (hlen : s.LengthsOk c) (hcov : FullAnaMarksCov c s)
    (hwl : ws1'.length = 2 * c.max_vars)
    (hperm : (ws1'.take s.core.min_clr_len).Perm (s.scratch.work_stk1.take s.core.min_clr_len)) :
    FullAnaMarksCov c { core := s.core, scratch := { s.scratch with work_stk1 := ws1' } } := by
  rcases hcov with ⟨hmcl, hnd, helem, hcov'⟩
  have hcv_le := hlen.core_ok.cur_vars_le
  have hwsl := hlen.scratch_ok.work_stk1_len
  have hml1 : (s.scratch.work_stk1.take s.core.min_clr_len).length = s.core.min_clr_len := by
    rw [List.length_take, hwsl]; omega
  have hml2 : (ws1'.take s.core.min_clr_len).length = s.core.min_clr_len := by
    rw [List.length_take, hwl]; omega
  refine ⟨hmcl, (List.Perm.nodup_iff (hperm.map BitVec.toNat)).mpr hnd, ?_, ?_⟩
  · intro k hk
    dsimp only at hk ⊢
    have hk_in : ws1'[k]'(by rw [hwl]; omega) ∈ ws1'.take s.core.min_clr_len := by
      have : (ws1'.take s.core.min_clr_len)[k]'(by rw [hml2]; exact hk) =
          ws1'[k]'(by rw [hwl]; omega) := List.getElem_take
      rw [← this]; exact List.getElem_mem _
    have hmem := (hperm.mem_iff).mp hk_in
    rw [List.mem_iff_getElem] at hmem
    obtain ⟨j, hj, hj_eq⟩ := hmem
    rw [hml1] at hj
    rw [List.getElem_take] at hj_eq
    have heq : (ws1'[k]?.getD 0#32) = (s.scratch.work_stk1[j]?.getD 0#32) := by
      rw [List.getElem?_eq_getElem (by rw [hwl]; omega),
        List.getElem?_eq_getElem (by rw [hwsl]; omega), Option.getD_some, Option.getD_some, hj_eq]
    rw [heq]
    exact helem j hj
  · intro v hv hnz
    dsimp only at hnz ⊢
    obtain ⟨i, hi, hiv⟩ := hcov' v hv hnz
    have hi_in : s.scratch.work_stk1[i]'(by rw [hwsl]; omega) ∈
        s.scratch.work_stk1.take s.core.min_clr_len := by
      have : (s.scratch.work_stk1.take s.core.min_clr_len)[i]'(by rw [hml1]; exact hi) =
          s.scratch.work_stk1[i]'(by rw [hwsl]; omega) := List.getElem_take
      rw [← this]; exact List.getElem_mem _
    have hmem := (hperm.mem_iff).mpr hi_in
    rw [List.mem_iff_getElem] at hmem
    obtain ⟨j, hj, hj_eq⟩ := hmem
    rw [hml2] at hj
    rw [List.getElem_take] at hj_eq
    refine ⟨j, hj, ?_⟩
    rw [List.getElem?_eq_getElem (by rw [hwl]; omega), Option.getD_some, hj_eq]
    rw [List.getElem?_eq_getElem (by rw [hwsl]; omega), Option.getD_some] at hiv
    exact hiv

end BumpHelpers

/-! ## 3. `full_rng_next_m7` (`m7RngNextExactSpec` & Canonical `Full.fullRngNextSpec`) -/

section RngNextProof

open scoped FullArenaTactics

private theorem m7_hlen_rng {c : FullCfg} {s : FullState}
    (h : s.LengthsOk c) (v : BitVec 64) :
    ({ core := s.core, scratch := { s.scratch with rng_state := v } } : FullState).LengthsOk c :=
  ⟨h.core_ok,
    { walk_vals_len := h.scratch_ok.walk_vals_len
      phases_len := h.scratch_ok.phases_len
      phases_target_len := h.scratch_ok.phases_target_len
      phases_best_len := h.scratch_ok.phases_best_len
      walk_best_len := h.scratch_ok.walk_best_len
      heap_len_arr := h.scratch_ok.heap_len_arr
      pos_len := h.scratch_ok.pos_len
      shrink_stk_len := h.scratch_ok.shrink_stk_len
      q_prev_len := h.scratch_ok.q_prev_len
      q_next_len := h.scratch_ok.q_next_len
      q_stamp_len := h.scratch_ok.q_stamp_len
      wsort_len := h.scratch_ok.wsort_len
      work_stk1_len := h.scratch_ok.work_stk1_len
      work_stk2_len := h.scratch_ok.work_stk2_len
      tarjan_mark_len := h.scratch_ok.tarjan_mark_len
      tarjan_reach_len := h.scratch_ok.tarjan_reach_len
      score_len := h.scratch_ok.score_len
      sim_sig_len := h.scratch_ok.sim_sig_len
      glue_used_len := h.scratch_ok.glue_used_len
      last_learned_len := h.scratch_ok.last_learned_len
      delayed_len_arr := h.scratch_ok.delayed_len_arr
      red_refs_len := h.scratch_ok.red_refs_len
      extend_stk_len := h.scratch_ok.extend_stk_len
      scratch_buf_len := h.scratch_ok.scratch_buf_len }⟩

/-- Stronger WP theorem certifying exact 64-bit Knuth LCG transition for `full_rng_next_m7`. -/
theorem full_rng_next_m7_wp_exact (Γ : Env) :
    ∀ a m Q X, m7RngNextExactSpec a m Q X → Func.wp Γ full_rng_next_m7_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  dsimp only [fullSafetySlice] at hm hlen hQ
  c0_steps
  let nxt := m7KnuthNext s.scratch.rng_state
  let s' : FullState := { core := s.core, scratch := { s.scratch with rng_state := nxt } }
  have hscr : s'.scratch = { s.scratch with rng_state := s'.scratch.rng_state } := rfl
  refine hQ (nxt >>> 32#64, ()) s' _ rfl (m7_hlen_rng hlen nxt) ⟨hscr, rfl, rfl⟩ ?_
  simpa [s', nxt, m7KnuthNext] using hm

/-- Drop-in WP theorem certifying canonical `Full.fullRngNextSpec` for `full_rng_next_m7`. -/
theorem full_rng_next_m7_wp (Γ : Env) :
    ∀ a m Q X, fullRngNextSpec a m Q X → Func.wp Γ full_rng_next_m7_body a m Q X := by
  intro a m Q X ⟨c, s, R, hc, hlen, hm, hQ⟩
  refine full_rng_next_m7_wp_exact Γ a m Q X ⟨c, s, R, hc, hlen, hm, ?_⟩
  rintro ⟨r, ⟨⟩⟩ s' m' hcore hlen' ⟨hscr, _⟩ hm'
  exact hQ (r, ()) s' m' hcore hlen' hscr hm'

end RngNextProof

/-! ## 4. `full_log10_q16_m7` & `full_scale_delta_m7` -/

section ScaleDeltaProof

open scoped FullArenaTactics

private theorem c0_bound_pow10_mul {d p : BitVec 64} (hd : d.toNat < 19)
    (hple : p.toNat ≤ 10 ^ d.toNat) : p.toNat * 10 < 2 ^ 64 := by
  have h1 : p.toNat * 10 ≤ 10 ^ (d.toNat + 1) := by
    rw [Nat.pow_succ]; exact Nat.mul_le_mul_right 10 hple
  exact Nat.lt_of_le_of_lt h1 (pow10_lt_64 (by omega))

theorem full_log10_q16_m7_wp (Γ : Env) :
    ∀ a m Q X, m7Log10Q16Spec a m Q X → Func.wp Γ full_log10_q16_m7_body a m Q X := by
  rintro ⟨x, ⟨⟩⟩ mem Q X hQ
  c0_hsteps_nogrp
  · exact hQ 0#64 (by decide) (fun hx10 => by c0_bound)
  · refine wp_loop_inv (ts := [i64, i64])
      (fun (d, p, ()) m1 =>
        mem = m1 ∧ 1 ≤ d.toNat ∧ d.toNat ≤ 19 ∧ 10 ≤ p.toNat ∧ p.toNat ≤ 10 ^ d.toNat)
      (fun (d, _, ()) _ => 19 - d.toNat) ?_ ?_
    · intro J hJ
      c0_hsteps; exact hJ (1#64, 10#64, ()) mem ⟨rfl, by decide, by decide, by decide, by decide⟩
    · rintro J ⟨d, p, ⟨⟩⟩ _ ⟨rfl, hd1, hd19, hp10, hple⟩ hJ
      refine wp_join_group (ts := []) (fun _ m1 => mem = m1) ?_ ?_
      · rintro _ ⟨⟩ _ rfl
        c0_hsteps_nogrp
        refine wp_join_group (ts := [i64]) (fun _ m1 => mem = m1) ?_ ?_
        · rintro _ ⟨mv, ⟨⟩⟩ _ rfl
          c0_hsteps_nogrp
          refine wp_loop_inv (ts := [i64, i64, i64, i64])
            (fun (mv', frac, step, k, ()) m1 =>
              mem = m1 ∧ k.toNat ≤ 16 ∧ step = (32768#64 >>> k.toNat) ∧
              frac.toNat + (65536 >>> k.toNat) ≤ 65536)
            (fun (_, _, _, k, ()) _ => 16 - k.toNat) ?_ ?_
          · intro Jk hJk
            c0_hsteps; exact hJk (mv, 0#64, 32768#64, 0#64, ()) mem
              ⟨rfl, by decide, rfl, by decide⟩
          · rintro Jk ⟨mv', frac, step, k, ⟨⟩⟩ _ ⟨rfl, hk16, hstep, hfrac⟩ hJk
            c0_hsteps_nogrp
            · have hk_lt : k.toNat < 16 := by c0_bound
              have hk1 : (k + 1#64).toNat = k.toNat + 1 := by bv_omega
              have hs1 : (step >>> 1#64) = (32768#64 >>> (k + 1#64).toNat) := by
                rw [hk1, hstep]
                apply BitVec.eq_of_toNat_eq
                have hshr1 : ∀ v : BitVec 64, (v >>> 1#64).toNat = v.toNat / 2 := by
                  intro v; simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
                rw [hshr1]
                simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
                  Nat.div_div_eq_div_mul, ← Nat.pow_succ]
              have hstep_toNat : step.toNat = 32768 >>> k.toNat := by
                rw [hstep, BitVec.toNat_ushiftRight]; rfl
              have hsplit := shift_split_65536 hk_lt
              refine wp_join_group (ts := [i64, i64])
                (fun (m2, fr2, ()) m1 =>
                  mem = m1 ∧ fr2.toNat + (65536 >>> (k + 1#64).toNat) ≤ 65536) ?_ ?_
              · rintro _ ⟨m2, fr2, ⟨⟩⟩ _ ⟨rfl, hfr2⟩
                c0_hsteps
                exact hJk (m2, fr2, step >>> 1#64, k + 1#64, ()) mem (by dsimp only; omega)
                  ⟨rfl, by omega, hs1, hfr2⟩
              · intro _ hJfr
                c0_hsteps_nogrp
                · have hst_le : step.toNat ≤ 32768 := by
                    rw [hstep_toNat, Nat.shiftRight_eq_div_pow]; exact Nat.div_le_self _ _
                  have hfr_le65536 : frac.toNat ≤ 65536 := Nat.le_trans (Nat.le_add_right _ _) hfrac
                  have hfr_lt : frac.toNat + step.toNat < 2 ^ 64 := by omega
                  have hfr_eq : (frac + step).toNat = frac.toNat + step.toNat := by
                    rw [BitVec.toNat_add, Nat.mod_eq_of_lt hfr_lt]
                  refine hJfr (_, frac + step, ()) mem ⟨rfl, ?_⟩
                  rw [hfr_eq, hstep_toNat, hk1]
                  omega
                · refine hJfr (_, frac, ()) mem ⟨rfl, ?_⟩
                  rw [hk1]; omega
            · have hk_eq : k.toNat = 16 := by c0_bound
              have hfr_lt : frac.toNat < 65536 := by
                rw [hk_eq] at hfrac
                have h65 : 65536 >>> 16 = 1 := rfl
                omega
              have hres_eq : (d * 65536#64 + frac).toNat = d.toNat * 65536 + frac.toNat := by
                have hmul : (d * 65536#64).toNat = d.toNat * 65536 := by bv_omega
                rw [BitVec.toNat_add, hmul, Nat.mod_eq_of_lt (by omega)]
              refine hQ (d * 65536#64 + frac) ?_ (fun _ => ?_)
              · rw [hres_eq]; omega
              · rw [hres_eq]; omega
        · intro _ hJm
          c0_hsteps_nogrp
          · exact hJm (_, ()) mem rfl
          · have hge1m : 1000000 ≤ p.toNat := by c0_bound
            intro h0
            have h1 := congrArg BitVec.toNat h0
            rw [BitVec.toNat_udiv] at h1
            change p.toNat / 1000000 = 0 at h1
            omega
          · exact hJm (_, ()) mem rfl
      · intro _ hJexit
        c0_hsteps_nogrp
        · have hd_lt : d.toNat < 19 := by c0_bound
          have hp10' : p.toNat * 10 < 2 ^ 64 := c0_bound_pow10_mul hd_lt hple
          have hd1' : (d + 1#64).toNat = d.toNat + 1 := by bv_omega
          have hp_mul : (p * 10#64).toNat = p.toNat * 10 := by
            rw [BitVec.toNat_mul, show (10#64).toNat = 10 from rfl, Nat.mod_eq_of_lt hp10']
          exact hJ (d + 1#64, p * 10#64, ()) mem (by dsimp only; omega)
            ⟨rfl, by omega, by omega, by omega, by
              rw [hd1', hp_mul, Nat.pow_succ]; exact Nat.mul_le_mul_right 10 hple⟩
        · exact hJexit () mem rfl
        · exact hJexit () mem rfl

private theorem scale_delta_fff_bounds {f_abs : BitVec 64} (hf_le : f_abs.toNat ≤ 983040) :
    let fff_q16 := ((9#64 * f_abs * f_abs) >>> 17#64) + 1638400#64
    1638400 ≤ fff_q16.toNat ∧ fff_q16.toNat ≤ 67993600 := by
  intro fff_q16
  have hmul9 : (9#64 * f_abs).toNat = 9 * f_abs.toNat := by bv_omega
  have hsq_le : 9 * f_abs.toNat * f_abs.toNat ≤ 9 * 983040 * 983040 := by
    have h1 : 9 * f_abs.toNat ≤ 9 * 983040 := Nat.mul_le_mul_left 9 hf_le
    exact Nat.mul_le_mul h1 hf_le
  have hsq_lt : 9 * f_abs.toNat * f_abs.toNat < 2 ^ 64 :=
    Nat.lt_of_le_of_lt hsq_le (by decide)
  have hsq : (9#64 * f_abs * f_abs).toNat = 9 * f_abs.toNat * f_abs.toNat := by
    rw [BitVec.toNat_mul, hmul9, Nat.mod_eq_of_lt hsq_lt]
  have hshr : ((9#64 * f_abs * f_abs) >>> 17#64).toNat ≤ 66355200 := by
    have h17 : ∀ v : BitVec 64, (v >>> 17#64).toNat = v.toNat / 2 ^ 17 := by
      intro v; simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    rw [h17, hsq]
    have h2 : (9 * f_abs.toNat * f_abs.toNat) / 2 ^ 17 ≤ (9 * 983040 * 983040) / 2 ^ 17 :=
      Nat.div_le_div_right hsq_le
    exact Nat.le_trans h2 (by decide)
  dsimp only [fff_q16]
  have hsum_lt : ((9#64 * f_abs * f_abs) >>> 17#64).toNat + 1638400 < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (Nat.add_le_add_right hshr 1638400) (by decide)
  have hadd : (((9#64 * f_abs * f_abs) >>> 17#64) + 1638400#64).toNat =
      ((9#64 * f_abs * f_abs) >>> 17#64).toNat + 1638400 := by
    rw [BitVec.toNat_add, show (1638400#64).toNat = 1638400 from rfl, Nat.mod_eq_of_lt hsum_lt]
  clear hsq_le hsq_lt hsq hmul9
  omega

private theorem scale_delta_branch1 {fff delta : BitVec 64}
    (hf1 : 1638400 ≤ fff.toNat) (hlim : delta ≤ 0xFFFFFFFFFFFFFFFF#64 / fff) :
    delta.toNat ≤ ((fff * delta) >>> 16#64).toNat := by
  have hdle : delta.toNat ≤ 18446744073709551615 / fff.toNat := by
    have h1 : delta.toNat ≤ (0xFFFFFFFFFFFFFFFF#64 / fff).toNat := BitVec.le_def.mp hlim
    rwa [BitVec.toNat_udiv] at h1
  have hprod_lt : fff.toNat * delta.toNat < 2 ^ 64 := by
    have hdiv := Nat.mul_div_le 18446744073709551615 fff.toNat
    have hmul : fff.toNat * delta.toNat ≤ fff.toNat * (18446744073709551615 / fff.toNat) :=
      Nat.mul_le_mul_left fff.toNat hdle
    exact Nat.lt_of_le_of_lt (Nat.le_trans hmul hdiv) (by decide)
  have hmul_eq : (fff * delta).toNat = fff.toNat * delta.toNat := by
    rw [BitVec.toNat_mul, Nat.mod_eq_of_lt hprod_lt]
  have hshr16 : ∀ v : BitVec 64, (v >>> 16#64).toNat = v.toNat / 65536 := by
    intro v; simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  rw [hshr16, hmul_eq]
  have hge : 1638400 * delta.toNat ≤ fff.toNat * delta.toNat := Nat.mul_le_mul_right _ hf1
  have hdiv : (1638400 * delta.toNat) / 65536 ≤ (fff.toNat * delta.toNat) / 65536 :=
    Nat.div_le_div_right hge
  have h25 : (1638400 * delta.toNat) / 65536 = 25 * delta.toNat := by
    rw [show 1638400 * delta.toNat = (25 * delta.toNat) * 65536 by omega]
    exact Nat.mul_div_cancel _ (by decide)
  rw [h25] at hdiv
  exact Nat.le_trans (Nat.le_mul_of_pos_left _ (by decide : 0 < 25)) hdiv

private theorem scale_delta_branch2 {fff delta : BitVec 64}
    (hf1 : 1638400 ≤ fff.toNat) (hf2 : fff.toNat ≤ 67993600)
    (hhi : delta >>> (16 : Nat) ≤ (18446744073709551615 : BitVec 64) / fff)
    (hnoovf : ((delta >>> (16 : Nat)) * fff) ≤
      (18446744073709551615 : BitVec 64) -
        (((delta &&& (65535 : BitVec 64)) * fff) >>> (16 : Nat))) :
    delta.toNat ≤ ((delta >>> (16 : Nat)) * fff +
      (((delta &&& (65535 : BitVec 64)) * fff) >>> (16 : Nat))).toNat := by
  let hi := delta >>> (16 : Nat)
  let lo := delta &&& (65535 : BitVec 64)
  have hshr16 : ∀ v : BitVec 64, (v >>> (16 : Nat)).toNat = v.toNat / 65536 := by
    intro v; simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have hhi_eq : hi.toNat = delta.toNat / 65536 := hshr16 delta
  have hlo_eq : lo.toNat = delta.toNat % 65536 := by
    change delta.toNat &&& (2 ^ 16 - 1) = delta.toNat % 2 ^ 16
    exact Nat.and_two_pow_sub_one_eq_mod delta.toNat 16
  have hlo_lt : lo.toNat < 65536 := by rw [hlo_eq]; exact Nat.mod_lt _ (by decide)
  have hq1_lt : hi.toNat * fff.toNat < 2 ^ 64 := by
    have h1 : hi.toNat ≤ 18446744073709551615 / fff.toNat := by
      have h' : hi.toNat ≤ ((18446744073709551615 : BitVec 64) / fff).toNat := BitVec.le_def.mp hhi
      rwa [BitVec.toNat_udiv] at h'
    have h2 := Nat.mul_div_le 18446744073709551615 fff.toNat
    have h3 : hi.toNat * fff.toNat ≤ (18446744073709551615 / fff.toNat) * fff.toNat :=
      Nat.mul_le_mul_right fff.toNat h1
    rw [Nat.mul_comm (18446744073709551615 / fff.toNat) fff.toNat] at h3
    exact Nat.lt_of_le_of_lt (Nat.le_trans h3 h2) (by decide)
  have hq1_eq : (hi * fff).toNat = hi.toNat * fff.toNat := by
    rw [BitVec.toNat_mul, Nat.mod_eq_of_lt hq1_lt]
  have hlo_mul_lt : lo.toNat * fff.toNat < 2 ^ 64 := by
    have h1 : lo.toNat * fff.toNat ≤ 65535 * 67993600 := Nat.mul_le_mul (by omega) hf2
    exact Nat.lt_of_le_of_lt h1 (by decide)
  have hq2_eq : ((lo * fff) >>> (16 : Nat)).toNat = (lo.toNat * fff.toNat) / 65536 := by
    rw [hshr16, BitVec.toNat_mul, Nat.mod_eq_of_lt hlo_mul_lt]
  have hq1_ge : 25 * 65536 * hi.toNat ≤ (hi * fff).toNat := by
    rw [hq1_eq]
    have h1 := Nat.mul_le_mul_left hi.toNat hf1
    omega
  have hq2_ge : 25 * lo.toNat ≤ ((lo * fff) >>> (16 : Nat)).toNat := by
    rw [hq2_eq]
    have h1 := Nat.div_le_div_right (Nat.mul_le_mul_left lo.toNat hf1) (c := 65536)
    have h2 : (lo.toNat * 1638400) / 65536 = 25 * lo.toNat := by
      rw [show lo.toNat * 1638400 = (25 * lo.toNat) * 65536 by omega]
      exact Nat.mul_div_cancel _ (by decide)
    rw [h2] at h1; exact h1
  have hq2_lt : ((lo * fff) >>> (16 : Nat)).toNat ≤ 18446744073709551615 := by
    have hlt := ((lo * fff) >>> (16 : Nat)).isLt; omega
  have hsum_lt : (hi * fff).toNat + ((lo * fff) >>> (16 : Nat)).toNat < 2 ^ 64 := by
    have hle : (hi * fff).toNat ≤
        ((18446744073709551615 : BitVec 64) - ((lo * fff) >>> (16 : Nat))).toNat :=
      BitVec.le_def.mp hnoovf
    have hsub : ((18446744073709551615 : BitVec 64) - ((lo * fff) >>> (16 : Nat))).toNat =
        18446744073709551615 - ((lo * fff) >>> (16 : Nat)).toNat := by
      bv_omega
    rw [hsub] at hle
    exact Nat.lt_of_le_of_lt (Nat.add_le_of_le_sub hq2_lt hle) (by decide)
  rw [show (hi * fff + ((lo * fff) >>> (16 : Nat))).toNat =
      (hi * fff).toNat + ((lo * fff) >>> (16 : Nat)).toNat by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt hsum_lt]]
  have hdecomp : delta.toNat = hi.toNat * 65536 + lo.toNat := by
    rw [hhi_eq, hlo_eq]; exact (Nat.div_add_mod' delta.toNat 65536).symm
  omega

/-- Safety-slice WP theorem for `full_scale_delta_m7` certifying `m7ScaleDeltaSpec`. -/
theorem full_scale_delta_m7_wp (Γ : Env)
    (hLog : ∀ a m Q X, m7Log10Q16Spec a m Q X → Γ "full_log10_q16_m7" [i64] [i64] a m Q X) :
    ∀ a m Q X, m7ScaleDeltaSpec a m Q X → Func.wp Γ full_scale_delta_m7_body a m Q X := by
  rintro ⟨h, delta, ⟨⟩⟩ mem Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  dsimp only [fullSafetySlice] at hm hlen hQ
  have hCont : ∀ r : BitVec 64, (delta = 0#64 → r = 0#64) → delta.toNat ≤ r.toNat →
      Q (r, ()) mem :=
    fun r h0 hle => hQ (r, ()) s mem rfl hlen ⟨rfl, h0, hle⟩ hm
  clear hQ
  c0_hsteps_nogrp
  · exact hCont 0#64 (fun _ => rfl) (by
      have h0 : delta = 0#64 := BitVec.eq_of_toNat_eq (by
        clear hCont hlen hm R c s hLog; c0_bound)
      rw [h0]; exact Nat.le_refl _)
  · have hdn0 : delta ≠ 0#64 := fun h0 => by
      clear hCont hlen hm R c s hLog; subst h0; simp at *
    refine wp_join_group (ts := [i64]) (fun _ m1 => mem = m1) ?_ ?_
    · rintro _ ⟨clauses, ⟨⟩⟩ _ rfl
      c0_hsteps_nogrp
      refine wp_join_group (ts := [i64]) (fun _ m1 => mem = m1) ?_ ?_
      · rintro _ ⟨arg, ⟨⟩⟩ _ rfl
        clear s R hlen hm
        c0_hsteps_nogrp
        c0_call hLog
        intro l hl1 hl10
        clear hLog hl10 arg c
        c0_hsteps_nogrp
        refine wp_join_group (ts := [i64])
          (fun (l1, ()) m1 => mem = m1 ∧ 65536 ≤ l1.toNat) ?_ ?_
        · rintro _ ⟨l1, ⟨⟩⟩ _ ⟨rfl, hl1'⟩
          clear l hl1
          c0_hsteps_nogrp
          refine wp_join_group (ts := [i64])
            (fun (l2, ()) m1 => mem = m1 ∧ 65536 ≤ l2.toNat ∧ l2.toNat ≤ 1310720) ?_ ?_
          · rintro _ ⟨l2, ⟨⟩⟩ _ ⟨rfl, hl2a, hl2b⟩
            clear l1 hl1'
            c0_hsteps_nogrp
            refine wp_join_group (ts := [i64])
              (fun (f_abs, ()) m1 => mem = m1 ∧ f_abs.toNat ≤ 983040) ?_ ?_
            · rintro _ ⟨f_abs, ⟨⟩⟩ _ ⟨rfl, hfa⟩
              clear l2 hl2a hl2b
              obtain ⟨hf1, hf2⟩ := scale_delta_fff_bounds hfa
              have hfff_ne0 : ((9#64 * f_abs * f_abs) >>> 17#64) + 1638400#64 ≠ 0#64 := by
                intro h0; have h1 := congrArg BitVec.toNat h0
                change (((9#64 * f_abs * f_abs) >>> 17#64) + 1638400#64).toNat = 0 at h1
                rw [h1] at hf1; exact absurd hf1 (by decide)
              have heq_f : (((9#64 * f_abs * f_abs) >>> 17#64) + 1638400#64) =
                  ((9 * f_abs * f_abs) >>> OfNat.ofNat 17 + 1638400 : BitVec 64) := rfl
              rw [heq_f] at hf1 hf2
              c0_hstep; c0_hstep; c0_hstep; c0_hstep; c0_hstep; c0_hstep
              dsimp only
              generalize ((9 * f_abs * f_abs) >>> OfNat.ofNat 17 + 1638400 : BitVec 64) = fff
                at hf1 hf2 ⊢
              c0_step; c0_step
              · rename_i hc
                c0_steps
                refine hCont _ (fun hd0 => absurd hd0 hdn0) ?_
                exact scale_delta_branch1 hf1 (BitVec.le_def.mpr hc)
              · c0_step
                · refine wp_jnz_of (fun _ => ?_) (fun hc2 => ?_)
                  · c0_steps
                    exact hCont 0xFFFFFFFFFFFFFFFF#64 (fun hd0 => absurd hd0 hdn0)
                      (Nat.le_sub_one_of_lt delta.isLt)
                  · c0_steps
                    refine hCont _ (fun hd0 => absurd hd0 hdn0) ?_
                    dsimp only [Arg.val] at hc2
                    unfold BitVec.ult at hc2
                    rw [decide_eq_false_iff_not] at hc2
                    have hhi : delta >>> (16 : Nat) ≤ (18446744073709551615 : BitVec 64) / fff :=
                      BitVec.le_def.mpr (by assumption)
                    exact scale_delta_branch2 hf1 hf2 hhi (BitVec.le_def.mpr (Nat.le_of_not_lt hc2))
                · c0_steps
                  exact hCont 0xFFFFFFFFFFFFFFFF#64 (fun hd0 => absurd hd0 hdn0)
                    (Nat.le_sub_one_of_lt delta.isLt)
            · intro _ hJf
              c0_hsteps_nogrp
              · refine hJf (_, ()) mem ⟨rfl, ?_⟩
                have hle : (327680 : BitVec 64).toNat ≤ l2.toNat := by assumption
                rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr hle)]
                have h32 : (327680 : BitVec 64).toNat = 327680 := by decide
                rw [h32] at hle ⊢; change l2.toNat - 327680 ≤ 983040; omega
              · refine hJf (_, ()) mem ⟨rfl, ?_⟩
                have hlt : ¬ (327680 : BitVec 64).toNat ≤ l2.toNat := by assumption
                have hle : l2.toNat ≤ (327680 : BitVec 64).toNat := Nat.le_of_not_le hlt
                rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr hle)]
                have h32 : (327680 : BitVec 64).toNat = 327680 := by decide
                rw [h32] at hle ⊢; change 327680 - l2.toNat ≤ 983040; omega
          · intro _ hJl2
            c0_hsteps_nogrp
            · exact hJl2 (1310720#64, ()) mem ⟨rfl, by decide, by decide⟩
            · exact hJl2 (l1, ()) mem ⟨rfl, hl1', Nat.le_of_not_lt (by assumption)⟩
        · intro _ hJl1
          c0_hsteps_nogrp
          · exact hJl1 (65536#64, ()) mem ⟨rfl, by decide⟩
          · exact hJl1 (l, ()) mem ⟨rfl, Nat.le_of_not_lt (by assumption)⟩
      · intro _ hJa
        c0_hsteps_nogrp
        · exact hJa (_, ()) mem rfl
        · exact hJa (_, ()) mem rfl
    · intro _ hJc
      c0_hsteps_nogrp
      · exact hJc (_, ()) mem rfl
      · exact hJc (_, ()) mem rfl

/-- Drop-in legacy M6-compatible WP theorem (`s' = s`) for `full_scale_delta_m7`. -/
theorem full_scale_delta_m7_wp_compat (Γ : Env)
    (hLog : ∀ a m Q X, m7Log10Q16Spec a m Q X → Γ "full_log10_q16_m7" [i64] [i64] a m Q X) :
    ∀ a m Q X, m7ScaleDeltaCompatSpec a m Q X → Func.wp Γ full_scale_delta_m7_body a m Q X := by
  intro a m Q X ⟨c, s, R, hc, hlen, hm, hQ⟩
  refine full_scale_delta_m7_wp Γ hLog a m Q X ⟨c, s, R, hc, hlen, hm, ?_⟩
  rintro ⟨r, ⟨⟩⟩ s' m' hcore hlen' ⟨hs', _⟩ hm'
  exact hQ (r, ()) s' m' hcore hlen' hs' hm'

end ScaleDeltaProof

/-! ## 5. `full_bump_sift_m7` & `full_bump_sort_stamps_m7` -/

section BumpSortProof

open scoped FullArenaTactics

private theorem bump_maxHeap_empty (cv : Nat) (qs ws : List (BitVec 32)) (n : Nat) :
    FullBumpMaxHeap cv qs ws n n := fun _ h1 h2 => absurd h1 (Nat.not_le_of_gt h2)

private theorem bump_sift_done {cv lo n root : Nat} {qs ws : List (BitVec 32)}
    (hlo : lo ≤ root) (hr_lt : root < n)
    (hheap : ∀ i, lo ≤ i → i < n → i ≠ root →
      (2 * i + 1 < n → bumpStampLe cv qs (ws[2 * i + 1]?.getD 0#32) (ws[i]?.getD 0#32)) ∧
      (2 * i + 2 < n → bumpStampLe cv qs (ws[2 * i + 2]?.getD 0#32) (ws[i]?.getD 0#32)))
    (hroot :
      (2 * root + 1 < n →
        bumpStampLe cv qs (ws[2 * root + 1]?.getD 0#32) (ws[root]?.getD 0#32)) ∧
      (2 * root + 2 < n →
        bumpStampLe cv qs (ws[2 * root + 2]?.getD 0#32) (ws[root]?.getD 0#32))) :
    FullBumpMaxHeap cv qs ws lo n := by
  intro i hil hin
  by_cases hir : i = root
  · subst hir; exact hroot
  · exact hheap i hil hin hir

private theorem bump_sift_step {cv lo n root ch : Nat} {qs ws : List (BitVec 32)}
    (hlo : lo ≤ root) (hch_lt : ch < n)
    (hch_eq : ch = 2 * root + 1 ∨ ch = 2 * root + 2)
    (hws_len : n ≤ ws.length)
    (hheap : ∀ i, lo ≤ i → i < n → i ≠ root →
      (2 * i + 1 < n → bumpStampLe cv qs (ws[2 * i + 1]?.getD 0#32) (ws[i]?.getD 0#32)) ∧
      (2 * i + 2 < n → bumpStampLe cv qs (ws[2 * i + 2]?.getD 0#32) (ws[i]?.getD 0#32)))
    (hpar : lo < root → ∃ p, lo ≤ p ∧ (2 * p + 1 = root ∨ 2 * p + 2 = root) ∧
      (2 * root + 1 < n → bumpStampLe cv qs (ws[2 * root + 1]?.getD 0#32) (ws[p]?.getD 0#32)) ∧
      (2 * root + 2 < n → bumpStampLe cv qs (ws[2 * root + 2]?.getD 0#32) (ws[p]?.getD 0#32)))
    (hgt : ¬ bumpStampLe cv qs (ws[ch]?.getD 0#32) (ws[root]?.getD 0#32))
    (hsib :
      (2 * root + 1 < n → bumpStampLe cv qs (ws[2 * root + 1]?.getD 0#32) (ws[ch]?.getD 0#32)) ∧
      (2 * root + 2 < n → bumpStampLe cv qs (ws[2 * root + 2]?.getD 0#32) (ws[ch]?.getD 0#32))) :
    let ws' := (ws.set root (ws[ch]'(Nat.lt_of_lt_of_le hch_lt hws_len))).set ch
      (ws[root]'(Nat.lt_of_lt_of_le
        (Nat.lt_of_lt_of_le (by clear hpar hheap; rcases hch_eq with ha | hb <;> omega) hch_lt)
        hws_len))
    (∀ i, lo ≤ i → i < n → i ≠ ch →
      (2 * i + 1 < n → bumpStampLe cv qs (ws'[2 * i + 1]?.getD 0#32) (ws'[i]?.getD 0#32)) ∧
      (2 * i + 2 < n → bumpStampLe cv qs (ws'[2 * i + 2]?.getD 0#32) (ws'[i]?.getD 0#32))) ∧
    (lo < ch → ∃ p, lo ≤ p ∧ (2 * p + 1 = ch ∨ 2 * p + 2 = ch) ∧
      (2 * ch + 1 < n → bumpStampLe cv qs (ws'[2 * ch + 1]?.getD 0#32) (ws'[p]?.getD 0#32)) ∧
      (2 * ch + 2 < n → bumpStampLe cv qs (ws'[2 * ch + 2]?.getD 0#32) (ws'[p]?.getD 0#32))) := by
  intro ws'
  have hr_lt : root < n := by clear hpar hheap; omega
  have hr_len : root < ws.length := by clear hpar hheap; omega
  have hch_len : ch < ws.length := by clear hpar hheap; omega
  have hswap := fun k => swap_getElem?_eq 0#32 ws hr_len hch_len k
  have hne_rc : root ≠ ch := by clear hpar hheap; rcases hch_eq with ha | hb <;> omega
  have hne_1r : 2 * root + 1 ≠ root := by clear hpar hheap; omega
  have hne_2r : 2 * root + 2 ≠ root := by clear hpar hheap; omega
  have hrc : bumpStampLe cv qs (ws[root]?.getD 0#32) (ws[ch]?.getD 0#32) := by
    rcases bumpStampLe_total cv qs (ws[root]?.getD 0#32) (ws[ch]?.getD 0#32) with h1 | h2
    · exact h1
    · exact absurd h2 hgt
  have hroot_new :
      (2 * root + 1 < n →
        bumpStampLe cv qs (ws'[2 * root + 1]?.getD 0#32) (ws'[root]?.getD 0#32)) ∧
      (2 * root + 2 < n →
        bumpStampLe cv qs (ws'[2 * root + 2]?.getD 0#32) (ws'[root]?.getD 0#32)) := by
    have hrw : ws'[root]?.getD 0#32 = ws[ch]?.getD 0#32 := by
      rw [hswap]; simp [swapIdx]
    rw [hrw]
    constructor <;> intro hbd
    · rw [hswap]
      rcases hch_eq with h1 | h2
      · have heq : 2 * root + 1 = ch := h1.symm
        rw [heq]
        simp only [swapIdx, hne_rc.symm, ↓reduceIte]
        exact hrc
      · have hne_1c : 2 * root + 1 ≠ ch := by rw [h2]; exact Nat.ne_of_lt (by omega)
        simp only [swapIdx, hne_1r, hne_1c, ↓reduceIte]
        exact hsib.1 hbd
    · rw [hswap]
      rcases hch_eq with h1 | h2
      · have hne_2c : 2 * root + 2 ≠ ch := by rw [h1]; exact Nat.ne_of_gt (by omega)
        simp only [swapIdx, hne_2r, hne_2c, ↓reduceIte]
        exact hsib.2 hbd
      · have heq : 2 * root + 2 = ch := h2.symm
        rw [heq]
        simp only [swapIdx, hne_rc.symm, ↓reduceIte]
        exact hrc
  refine ⟨?_, ?_⟩
  · intro i hil hin hic
    by_cases hir : i = root
    · subst hir; exact hroot_new
    · have hi_old := hheap i hil hin hir
      have hiw : ws'[i]?.getD 0#32 = ws[i]?.getD 0#32 := by
        rw [hswap]; simp [swapIdx, hir, hic]
      rw [hiw]
      constructor <;> intro hbd
      · rw [hswap]
        by_cases h1r : 2 * i + 1 = root
        · have hlo_root : lo < root := Nat.lt_of_le_of_lt hil (by omega)
          obtain ⟨p, hp1, hp2, hpr1, hpr2⟩ := hpar hlo_root
          have hpi : p = i := by
            rcases hp2 with ha | hb
            · have : 2 * p + 1 = 2 * i + 1 := ha.trans h1r.symm
              omega
            · exfalso; have : 2 * p + 2 = 2 * i + 1 := hb.trans h1r.symm; omega
          subst hpi
          simp only [swapIdx, h1r, ↓reduceIte]
          rcases hch_eq with ha | hb
          · have h2p1 : 2 * root + 1 < n := by rw [← ha]; exact hch_lt
            rw [ha]; exact hpr1 h2p1
          · have h2p2 : 2 * root + 2 < n := by rw [← hb]; exact hch_lt
            rw [hb]; exact hpr2 h2p2
        · have h1c : 2 * i + 1 ≠ ch := by
            intro heq
            rcases hch_eq with ha | hb
            · have : 2 * i + 1 = 2 * root + 1 := heq.trans ha
              exact hir (by clear hpar hheap hi_old; omega)
            · have : 2 * i + 1 = 2 * root + 2 := heq.trans hb
              clear hpar hheap hi_old; omega
          simp only [swapIdx, h1r, h1c, ↓reduceIte]
          exact hi_old.1 hbd
      · rw [hswap]
        by_cases h2r : 2 * i + 2 = root
        · have hlo_root : lo < root := Nat.lt_of_le_of_lt hil (by clear hpar hheap hi_old; omega)
          obtain ⟨p, hp1, hp2, hpr1, hpr2⟩ := hpar hlo_root
          have hpi : p = i := by
            clear hpr1 hpr2 hheap hi_old
            rcases hp2 with ha | hb
            · exfalso; have : 2 * p + 1 = 2 * i + 2 := ha.trans h2r.symm; omega
            · have : 2 * p + 2 = 2 * i + 2 := hb.trans h2r.symm; omega
          subst hpi
          simp only [swapIdx, h2r, ↓reduceIte]
          rcases hch_eq with ha | hb
          · have h2p1 : 2 * root + 1 < n := by rw [← ha]; exact hch_lt
            rw [ha]; exact hpr1 h2p1
          · have h2p2 : 2 * root + 2 < n := by rw [← hb]; exact hch_lt
            rw [hb]; exact hpr2 h2p2
        · have h2c : 2 * i + 2 ≠ ch := by
            intro heq
            rcases hch_eq with ha | hb
            · have : 2 * i + 2 = 2 * root + 1 := heq.trans ha
              clear hpar hheap hi_old; omega
            · have : 2 * i + 2 = 2 * root + 2 := heq.trans hb
              exact hir (by clear hpar hheap hi_old; omega)
          simp only [swapIdx, h2r, h2c, ↓reduceIte]
          exact hi_old.2 hbd
  · intro _
    have hch_ne_r : ch ≠ root := hne_rc.symm
    have hlt_rch : root < ch := by clear hpar hheap; rcases hch_eq with ha | hb <;> omega
    have hch_le : lo ≤ ch := Nat.le_trans hlo (Nat.le_of_lt hlt_rch)
    have hch_old := hheap ch hch_le hch_lt hch_ne_r
    have hrw : ws'[root]?.getD 0#32 = ws[ch]?.getD 0#32 := by
      rw [hswap]; simp [swapIdx]
    have hne_c1r : 2 * ch + 1 ≠ root := Nat.ne_of_gt (by clear hpar hheap; omega)
    have hne_c1c : 2 * ch + 1 ≠ ch := Nat.ne_of_gt (by clear hpar hheap; omega)
    have hne_c2r : 2 * ch + 2 ≠ root := Nat.ne_of_gt (by clear hpar hheap; omega)
    have hne_c2c : 2 * ch + 2 ≠ ch := Nat.ne_of_gt (by clear hpar hheap; omega)
    have hch_par : 2 * root + 1 = ch ∨ 2 * root + 2 = ch := by
      rcases hch_eq with ha | hb
      · exact Or.inl ha.symm
      · exact Or.inr hb.symm
    refine ⟨root, hlo, hch_par, ?_⟩
    rw [hrw]
    constructor <;> intro hbd
    · rw [hswap]
      simp only [swapIdx, hne_c1r, hne_c1c, ↓reduceIte]
      exact hch_old.1 hbd
    · rw [hswap]
      simp only [swapIdx, hne_c2r, hne_c2c, ↓reduceIte]
      exact hch_old.2 hbd

private theorem bumpStampLe_of_u32_cmp {cv : Nat} {qs : List (BitVec 32)} {a b qa qb : BitVec 32}
    (ha : (if a.toNat < cv then qs[a.toNat]?.getD 0#32 else 0#32) = qa)
    (hb : (if b.toNat < cv then qs[b.toNat]?.getD 0#32 else 0#32) = qb)
    (hcmp : qb.toNat < qa.toNat ∨ (qb.toNat = qa.toNat ∧ b.toNat ≤ a.toNat)) :
    bumpStampLe cv qs b a := by
  unfold bumpStampLe bumpStampKey
  have ha' : (if a.toNat < cv then (qs[a.toNat]?.getD 0#32).toNat else 0) = qa.toNat := by
    by_cases h : a.toNat < cv
    · simp only [h, ↓reduceIte] at ha ⊢; rw [ha]
    · simp only [h, ↓reduceIte] at ha ⊢; rw [← ha]; rfl
  have hb' : (if b.toNat < cv then (qs[b.toNat]?.getD 0#32).toNat else 0) = qb.toNat := by
    by_cases h : b.toNat < cv
    · simp only [h, ↓reduceIte] at hb ⊢; rw [hb]
    · simp only [h, ↓reduceIte] at hb ⊢; rw [← hb]; rfl
  dsimp only
  rw [ha', hb']
  exact hcmp

theorem full_bump_sift_m7_wp (Γ : Env) :
    ∀ a m Q X, m7BumpSiftSpec a m Q X → Func.wp Γ full_bump_sift_m7_body a m Q X := by
  rintro ⟨h, start, n, ⟨⟩⟩ m0 Q X ⟨c, s, R, rfl, hlen, hstn, hncv, hheap0, hm0, hQ⟩
  have hmax : c.max_vars < 2 * dimacsBound := c.hmaxv
  unfold dimacsBound at hmax
  obtain hcv_le := hlen.core_ok.cur_vars_le
  obtain hqsl := hlen.scratch_ok.q_stamp_len
  obtain hwsl := hlen.scratch_ok.work_stk1_len
  c0_hsteps_nogrp
  · refine wp_join_group (ts := [i64])
      (fun (_, ()) m1 =>
        ∃ ws1 : List (BitVec 32),
          ws1.length = 2 * c.max_vars ∧
          (ws1.take n.toNat).Perm (s.scratch.work_stk1.take n.toNat) ∧
          (∀ k, n.toNat ≤ k → ws1[k]? = s.scratch.work_stk1[k]?) ∧
          FullBumpMaxHeap s.core.cur_vars s.scratch.q_stamp ws1 start.toNat n.toNat ∧
          (FullMem c { core := s.core, scratch := { s.scratch with work_stk1 := ws1 } } ⋆ R) m1)
      ?_ ?_
    · rintro _ ⟨_, ⟨⟩⟩ m1 ⟨ws1, hwl, hperm, htail, hheap, hm1⟩
      c0_hsteps_nogrp
      exact hQ ws1 m1 hwl hperm htail hheap hm1
    · intro _ hJbrk
      c0_hsteps_nogrp
      refine wp_loop_inv (ts := [i64])
        (fun (root, ()) m1 =>
          ∃ ws1 : List (BitVec 32),
            start.toNat ≤ root.toNat ∧ root.toNat < n.toNat ∧
            ws1.length = 2 * c.max_vars ∧
            (ws1.take n.toNat).Perm (s.scratch.work_stk1.take n.toNat) ∧
            (∀ k, n.toNat ≤ k → ws1[k]? = s.scratch.work_stk1[k]?) ∧
            (∀ i, start.toNat ≤ i → i < n.toNat → i ≠ root.toNat →
              (2 * i + 1 < n.toNat → bumpStampLe s.core.cur_vars s.scratch.q_stamp
                (ws1[2 * i + 1]?.getD 0#32) (ws1[i]?.getD 0#32)) ∧
              (2 * i + 2 < n.toNat → bumpStampLe s.core.cur_vars s.scratch.q_stamp
                (ws1[2 * i + 2]?.getD 0#32) (ws1[i]?.getD 0#32))) ∧
            (start.toNat < root.toNat →
              ∃ p, start.toNat ≤ p ∧ (2 * p + 1 = root.toNat ∨ 2 * p + 2 = root.toNat) ∧
                (2 * root.toNat + 1 < n.toNat → bumpStampLe s.core.cur_vars s.scratch.q_stamp
                  (ws1[2 * root.toNat + 1]?.getD 0#32) (ws1[p]?.getD 0#32)) ∧
                (2 * root.toNat + 2 < n.toNat → bumpStampLe s.core.cur_vars s.scratch.q_stamp
                  (ws1[2 * root.toNat + 2]?.getD 0#32) (ws1[p]?.getD 0#32))) ∧
            (FullMem c { core := s.core, scratch := { s.scratch with work_stk1 := ws1 } } ⋆ R) m1)
        (fun (root, ()) _ => n.toNat - root.toNat) ?_ ?_
      · intro J hJ
        c0_hsteps
        exact hJ (start, ()) m0 ⟨s.scratch.work_stk1, Nat.le_refl _, hstn, hwsl, List.Perm.refl _,
          fun _ _ => rfl, fun i hi1 hi2 hine =>
            hheap0 i (Nat.lt_of_le_of_ne hi1 (Ne.symm hine)) hi2,
          fun hlt => absurd hlt (Nat.lt_irrefl _), by simpa using hm0⟩
      · rintro J ⟨root, ⟨⟩⟩ m1
          ⟨ws1, hsr, hrn, hwl, hperm, htail, hheap, hpar, hm1⟩ hLoop
        clear hm0
        let s1 : FullState := { core := s.core, scratch := { s.scratch with work_stk1 := ws1 } }
        have hm1' : (FullMem c s1 ⋆ R) m1 := hm1
        have hroot_lt29 : root.toNat < 2 ^ 29 := by omega
        have hshl : (root <<< 1#64).toNat = 2 * root.toNat := by
          simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega
        have hch_eq : (root <<< 1#64 + 1#64).toNat = 2 * root.toNat + 1 := by
          rw [BitVec.toNat_add, hshl, show (1#64).toNat = 1 from rfl, Nat.mod_eq_of_lt (by omega)]
        c0_hsteps_nogrp
        · refine hJbrk (root, ()) m1 ⟨ws1, hwl, hperm, htail, bump_sift_done hsr hrn hheap ?_, hm1'⟩
          constructor
          · intro h1
            have hge : n.toNat ≤ (root <<< 1#64 + 1#64).toNat := by c0_bound
            omega
          · intro h2
            have hge : n.toNat ≤ (root <<< 1#64 + 1#64).toNat := by c0_bound
            omega
        · have hch_lt_n : 2 * root.toNat + 1 < n.toNat := by c0_bound
          have hch_wl : (root <<< 1#64 + 1#64).toNat < s1.scratch.work_stk1.length := by
            dsimp only [s1]; rw [hwl]; omega
          let cl := s1.scratch.work_stk1[(root <<< 1#64 + 1#64).toNat]'hch_wl
          refine wp_load_of (FullArenaTactics.c0_load_full_work_stk1 hch_wl hm1') ?_
          refine wp_join_group (ts := [i32]) (fun (cq, ()) m2 => m1 = m2 ∧
              cq = if cl.toNat < s.core.cur_vars then
                s.scratch.q_stamp[cl.toNat]?.getD 0#32 else 0#32) ?_ ?_
          · rintro _ ⟨cq, ⟨⟩⟩ _ ⟨rfl, hcq⟩
            c0_hsteps_nogrp
            refine wp_join_group (ts := [i64, i32, i32])
              (fun (ch', cl', cq', ()) m2 => m1 = m2 ∧
                (ch'.toNat = 2 * root.toNat + 1 ∨ ch'.toNat = 2 * root.toNat + 2) ∧
                ch'.toNat < n.toNat ∧
                cl' = ws1[ch'.toNat]?.getD 0#32 ∧
                cq' = (if cl'.toNat < s.core.cur_vars then
                  s.scratch.q_stamp[cl'.toNat]?.getD 0#32 else 0#32) ∧
                (2 * root.toNat + 1 < n.toNat → bumpStampLe s.core.cur_vars s.scratch.q_stamp
                  (ws1[2 * root.toNat + 1]?.getD 0#32) cl') ∧
                (2 * root.toNat + 2 < n.toNat → bumpStampLe s.core.cur_vars s.scratch.q_stamp
                  (ws1[2 * root.toNat + 2]?.getD 0#32) cl')) ?_ ?_
            · rintro _ ⟨ch', cl', cq', ⟨⟩⟩ _ ⟨rfl, hch_or, hch_n, hcl', hcq', hsib⟩
              c0_hsteps_nogrp
              have hrl_wl : root.toNat < s1.scratch.work_stk1.length := by
                dsimp only [s1]; rw [hwl]; omega
              let rl := s1.scratch.work_stk1[root.toNat]'hrl_wl
              refine wp_join_group (ts := [i32]) (fun (rq, ()) m2 => m1 = m2 ∧
                  rq = if rl.toNat < s.core.cur_vars then
                    s.scratch.q_stamp[rl.toNat]?.getD 0#32 else 0#32) ?_ ?_
              · rintro _ ⟨rq, ⟨⟩⟩ _ ⟨rfl, hrq⟩
                c0_hsteps
                · have hr_gt : cq'.toNat < rq.toNat := by c0_bound
                  have hle_cr : bumpStampLe s.core.cur_vars s.scratch.q_stamp cl' rl :=
                    bumpStampLe_of_u32_cmp hrq.symm hcq'.symm (Or.inl hr_gt)
                  have hrl_raw : rl = ws1[root.toNat]?.getD 0#32 := by
                    dsimp only [rl, s1]
                    rw [List.getElem?_eq_getElem (by rw [hwl]; omega), Option.getD_some]
                  refine hJbrk (root, ()) m1 ⟨ws1, hwl, hperm, htail,
                    bump_sift_done hsr hrn hheap
                      ⟨fun h1 => bumpStampLe_trans (hsib.1 h1)
                        (by rw [← hrl_raw]; exact hle_cr),
                       fun h2 => bumpStampLe_trans (hsib.2 h2)
                        (by rw [← hrl_raw]; exact hle_cr)⟩, hm1'⟩
                · have hr_ge : rq.toNat = cq'.toNat ∧ cl'.toNat ≤ rl.toNat := by
                    constructor <;> c0_bound
                  have hle_cr : bumpStampLe s.core.cur_vars s.scratch.q_stamp cl' rl :=
                    bumpStampLe_of_u32_cmp hrq.symm hcq'.symm (Or.inr ⟨hr_ge.1.symm, hr_ge.2⟩)
                  have hrl_raw : rl = ws1[root.toNat]?.getD 0#32 := by
                    dsimp only [rl, s1]
                    rw [List.getElem?_eq_getElem (by rw [hwl]; omega), Option.getD_some]
                  refine hJbrk (root, ()) m1 ⟨ws1, hwl, hperm, htail,
                    bump_sift_done hsr hrn hheap
                      ⟨fun h1 => bumpStampLe_trans (hsib.1 h1)
                        (by rw [← hrl_raw]; exact hle_cr),
                       fun h2 => bumpStampLe_trans (hsib.2 h2)
                        (by rw [← hrl_raw]; exact hle_cr)⟩, hm1'⟩
                · have hnot : ¬ bumpStampLe s.core.cur_vars s.scratch.q_stamp cl' rl := by
                    intro hle
                    have hrq' := congrArg BitVec.toNat hrq
                    have hcq'' := congrArg BitVec.toNat hcq'
                    simp only [apply_ite BitVec.toNat,
                      show (0#32 : BitVec 32).toNat = 0 from rfl] at hrq' hcq''
                    unfold bumpStampLe bumpStampKey at hle
                    dsimp only at hle
                    rw [← hrq', ← hcq''] at hle
                    rcases hle with h1 | ⟨h1, h2⟩
                    · c0_bound
                    · dsimp only [rl] at h2; c0_bound
                  have hch_len : ch'.toNat < ws1.length := by rw [hwl]; omega
                  have hset_len : ch'.toNat < (ws1.set root.toNat cl').length := by
                    rw [List.length_set]; exact hch_len
                  c0_hsteps_nogrp
                  have hrl_raw : rl = ws1[root.toNat]?.getD 0#32 := by
                    dsimp only [rl, s1]
                    rw [List.getElem?_eq_getElem (by rw [hwl]; omega), Option.getD_some]
                  have hstep := bump_sift_step hsr hch_n hch_or (by omega) hheap hpar
                    (by simpa [hcl', hrl_raw] using hnot) (by rw [← hcl']; exact hsib)
                  have hcl'_eq : cl' = ws1[ch'.toNat]'(by rw [hwl]; omega) := by
                    rw [hcl', List.getElem?_eq_getElem (by rw [hwl]; omega), Option.getD_some]
                  have hrl_eq : rl = ws1[root.toNat]'(by rw [hwl]; omega) := rfl
                  let ws2 := (ws1.set root.toNat (ws1[ch'.toNat]'(by rw [hwl]; omega))).set
                    ch'.toNat (ws1[root.toNat]'(by rw [hwl]; omega))
                  have hperm2 : (ws2.take n.toNat).Perm (s.scratch.work_stk1.take n.toNat) :=
                    (swap_perm_take ws1 (by omega) hch_n (by omega)).trans hperm
                  have htail2 : ∀ k, n.toNat ≤ k → ws2[k]? = s.scratch.work_stk1[k]? := by
                    intro k hk
                    rw [swap_getElem?_raw ws1 (by rw [hwl]; omega) (by rw [hwl]; omega) k]
                    have hsw : swapIdx root.toNat ch'.toNat k = k := by
                      unfold swapIdx; simp [show k ≠ root.toNat by omega,
                        show k ≠ ch'.toNat by omega]
                    rw [hsw]; exact htail k hk
                  have hm3' : (FullMem c { core := s.core, scratch :=
                      { s.scratch with work_stk1 := ws2 } } ⋆ R) m := by
                    simpa [ws2, hcl'_eq, hrl_eq, s1] using hm
                  refine hLoop (ch', ()) m
                    (by dsimp only; rcases hch_or with hca | hcb <;> omega)
                    ⟨ws2, by omega, hch_n, by simp [ws2, hwl], hperm2, htail2,
                      hstep.1, hstep.2, hm3'⟩
                · have hnot : ¬ bumpStampLe s.core.cur_vars s.scratch.q_stamp cl' rl := by
                    intro hle
                    have hrq' := congrArg BitVec.toNat hrq
                    have hcq'' := congrArg BitVec.toNat hcq'
                    simp only [apply_ite BitVec.toNat,
                      show (0#32 : BitVec 32).toNat = 0 from rfl] at hrq' hcq''
                    unfold bumpStampLe bumpStampKey at hle
                    dsimp only at hle
                    rw [← hrq', ← hcq''] at hle
                    rcases hle with h1 | ⟨h1, h2⟩
                    · c0_bound
                    · dsimp only [rl] at h2; c0_bound
                  have hch_len : ch'.toNat < ws1.length := by rw [hwl]; omega
                  have hset_len : ch'.toNat < (ws1.set root.toNat cl').length := by
                    rw [List.length_set]; exact hch_len
                  c0_hsteps_nogrp
                  have hrl_raw : rl = ws1[root.toNat]?.getD 0#32 := by
                    dsimp only [rl, s1]
                    rw [List.getElem?_eq_getElem (by rw [hwl]; omega), Option.getD_some]
                  have hstep := bump_sift_step hsr hch_n hch_or (by omega) hheap hpar
                    (by simpa [hcl', hrl_raw] using hnot) (by rw [← hcl']; exact hsib)
                  have hcl'_eq : cl' = ws1[ch'.toNat]'(by rw [hwl]; omega) := by
                    rw [hcl', List.getElem?_eq_getElem (by rw [hwl]; omega), Option.getD_some]
                  have hrl_eq : rl = ws1[root.toNat]'(by rw [hwl]; omega) := rfl
                  let ws2 := (ws1.set root.toNat (ws1[ch'.toNat]'(by rw [hwl]; omega))).set
                    ch'.toNat (ws1[root.toNat]'(by rw [hwl]; omega))
                  have hperm2 : (ws2.take n.toNat).Perm (s.scratch.work_stk1.take n.toNat) :=
                    (swap_perm_take ws1 (by omega) hch_n (by omega)).trans hperm
                  have htail2 : ∀ k, n.toNat ≤ k → ws2[k]? = s.scratch.work_stk1[k]? := by
                    intro k hk
                    rw [swap_getElem?_raw ws1 (by rw [hwl]; omega) (by rw [hwl]; omega) k]
                    have hsw : swapIdx root.toNat ch'.toNat k = k := by
                      unfold swapIdx; simp [show k ≠ root.toNat by omega,
                        show k ≠ ch'.toNat by omega]
                    rw [hsw]; exact htail k hk
                  have hm3' : (FullMem c { core := s.core, scratch :=
                      { s.scratch with work_stk1 := ws2 } } ⋆ R) m := by
                    simpa [ws2, hcl'_eq, hrl_eq, s1] using hm
                  refine hLoop (ch', ()) m
                    (by dsimp only; rcases hch_or with hca | hcb <;> omega)
                    ⟨ws2, by omega, hch_n, by simp [ws2, hwl], hperm2, htail2,
                      hstep.1, hstep.2, hm3'⟩
              · intro _ hJrq
                c0_hsteps_nogrp
                · try rw [zext32_toNat] at hc
                  rw [Nat.mod_eq_of_lt (by omega)] at hc
                  have hcv' : rl.toNat < s.core.cur_vars := hc
                  have hrl_lt : rl.toNat < s1.scratch.q_stamp.length := by
                    dsimp only [s1]; rw [hqsl]; exact Nat.lt_of_lt_of_le hcv' hcv_le
                  refine wp_load_of (FullArenaTactics.c0_load_full_q_stamp
                    (by rwa [zext32_toNat]) hm1') ?_
                  refine hJrq (_, ()) m1 ⟨rfl, ?_⟩
                  simp only [hcv', ↓reduceIte]
                  dsimp only [Arg.val, rl, s1]
                  rw [List.getElem?_eq_getElem (by
                      rw [hqsl]; exact Nat.lt_of_lt_of_le hcv' hcv_le), Option.getD_some]
                  simp only [zext32_toNat]
                · try rw [zext32_toNat] at hc
                  rw [Nat.mod_eq_of_lt (by omega)] at hc
                  have hcv' : ¬ rl.toNat < s.core.cur_vars := hc
                  refine hJrq (0#32, ()) m1 ⟨rfl, by simp only [hcv', ↓reduceIte]⟩
            · intro _ hJsib
              have hcl_raw : cl = ws1[2 * root.toNat + 1]?.getD 0#32 := by
                dsimp only [cl, s1]
                rw [← hch_eq, List.getElem?_eq_getElem (by rw [hwl]; omega), Option.getD_some]
              c0_hsteps_nogrp
              · have hs_lt_n : 2 * root.toNat + 2 < n.toNat := by c0_bound
                have hsl_eq : (root <<< 1#64 + 1#64 + 1#64).toNat = 2 * root.toNat + 2 := by
                  bv_omega
                have hsl_wl :
                    (root <<< 1#64 + 1#64 + 1#64).toNat < s1.scratch.work_stk1.length := by
                  dsimp only [s1]; rw [hwl, hsl_eq]; omega
                let sl := s1.scratch.work_stk1[(root <<< 1#64 + 1#64 + 1#64).toNat]'hsl_wl
                refine wp_load_of (FullArenaTactics.c0_load_full_work_stk1 hsl_wl hm1') ?_
                refine wp_join_group (ts := [i32]) (fun (sq, ()) m2 => m1 = m2 ∧
                    sq = if sl.toNat < s.core.cur_vars then
                      s.scratch.q_stamp[sl.toNat]?.getD 0#32 else 0#32) ?_ ?_
                · rintro _ ⟨sq, ⟨⟩⟩ _ ⟨rfl, hsq⟩
                  have hsl_raw : sl = ws1[2 * root.toNat + 2]?.getD 0#32 := by
                    dsimp only [sl, s1]
                    rw [← hsl_eq, List.getElem?_eq_getElem
                      (by rw [hwl, hsl_eq]; exact Nat.lt_of_lt_of_le hs_lt_n (by omega)),
                      Option.getD_some]
                  have hsl_c0 : ((root <<< 1#64).toNat + 1 + 1) % 18446744073709551616 =
                      (root <<< 1#64 + 1#64 + 1#64).toNat := by bv_omega
                  have hch_c0 : ((root <<< 1#64).toNat + 1) % 18446744073709551616 =
                      (root <<< 1#64 + 1#64).toNat := by bv_omega
                  c0_hsteps
                  · try simp only [hsl_c0, hch_c0] at hc
                    have hlt : cq.toNat < sq.toNat := by c0_bound
                    have hcs := bumpStampLe_of_u32_cmp hsq.symm hcq.symm (Or.inl hlt)
                    refine hJsib (root <<< 1#64 + 1#64 + 1#64, sl, sq, ()) m1
                      ⟨rfl, Or.inr hsl_eq, by rw [hsl_eq]; exact hs_lt_n,
                        by rw [hsl_eq]; exact hsl_raw, hsq,
                        fun _ => by rw [← hcl_raw]; exact hcs,
                        fun _ => by rw [← hsl_raw]; exact bumpStampLe_refl _ _ _⟩
                  · try simp only [hsl_c0, hch_c0] at hc
                    have hge : sq.toNat = cq.toNat ∧ cl.toNat < sl.toNat := by
                      constructor <;> c0_bound
                    have hcs := bumpStampLe_of_u32_cmp hsq.symm hcq.symm
                      (Or.inr ⟨hge.1.symm, Nat.le_of_lt hge.2⟩)
                    refine hJsib (root <<< 1#64 + 1#64 + 1#64, sl, sq, ()) m1
                      ⟨rfl, Or.inr hsl_eq, by rw [hsl_eq]; exact hs_lt_n,
                        by rw [hsl_eq]; exact hsl_raw, hsq,
                        fun _ => by rw [← hcl_raw]; exact hcs,
                        fun _ => by rw [← hsl_raw]; exact bumpStampLe_refl _ _ _⟩
                  · try simp only [hsl_c0, hch_c0] at hc
                    have hsc : bumpStampLe s.core.cur_vars s.scratch.q_stamp sl cl := by
                      have hcq' := congrArg BitVec.toNat hcq
                      have hsq' := congrArg BitVec.toNat hsq
                      simp only [apply_ite BitVec.toNat,
                        show (0#32 : BitVec 32).toNat = 0 from rfl] at hcq' hsq'
                      rcases bumpStampLe_total s.core.cur_vars s.scratch.q_stamp sl cl with
                        h1 | h2
                      · exact h1
                      · unfold bumpStampLe bumpStampKey at h2 ⊢; dsimp only at h2 ⊢
                        rw [← hcq', ← hsq'] at h2 ⊢
                        rcases h2 with h2a | ⟨h2a, h2b⟩
                        · exfalso; c0_bound
                        · have hleq : sl.toNat ≤ cl.toNat := Nat.le_of_not_lt hc
                          exact Or.inr ⟨h2a.symm, hleq⟩
                    refine hJsib (root <<< 1#64 + 1#64, cl, cq, ()) m1
                      ⟨rfl, Or.inl hch_eq, by rw [hch_eq]; exact hch_lt_n,
                        by rw [hch_eq]; exact hcl_raw, hcq,
                        fun _ => by rw [← hcl_raw]; exact bumpStampLe_refl _ _ _,
                        fun _ => by rw [← hsl_raw]; exact hsc⟩
                  · try simp only [hsl_c0, hch_c0] at hc
                    have hsc : bumpStampLe s.core.cur_vars s.scratch.q_stamp sl cl := by
                      have hcq' := congrArg BitVec.toNat hcq
                      have hsq' := congrArg BitVec.toNat hsq
                      simp only [apply_ite BitVec.toNat,
                        show (0#32 : BitVec 32).toNat = 0 from rfl] at hcq' hsq'
                      rcases bumpStampLe_total s.core.cur_vars s.scratch.q_stamp sl cl with
                        h1 | h2
                      · exact h1
                      · unfold bumpStampLe bumpStampKey at h2 ⊢; dsimp only at h2 ⊢
                        rw [← hcq', ← hsq'] at h2 ⊢
                        rcases h2 with h2a | ⟨h2a, h2b⟩
                        · exfalso; c0_bound
                        · exact absurd (BitVec.eq_of_toNat_eq h2a.symm) hc
                    refine hJsib (root <<< 1#64 + 1#64, cl, cq, ()) m1
                      ⟨rfl, Or.inl hch_eq, by rw [hch_eq]; exact hch_lt_n,
                        by rw [hch_eq]; exact hcl_raw, hcq,
                        fun _ => by rw [← hcl_raw]; exact bumpStampLe_refl _ _ _,
                        fun _ => by rw [← hsl_raw]; exact hsc⟩
                · intro _ hJsq
                  c0_hsteps_nogrp
                  · have hidx_eq : ((root <<< 1#64).toNat + 1 + 1) % 2 ^ 64 =
                        (root <<< 1#64 + 1#64 + 1#64).toNat := by bv_omega
                    simp only [hidx_eq, Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64)]
                      at hc
                    have hcv' : sl.toNat < s.core.cur_vars := hc
                    have hsl_lt : sl.toNat < s1.scratch.q_stamp.length := by
                      dsimp only [s1]; rw [hqsl]; exact Nat.lt_of_lt_of_le hcv' hcv_le
                    refine wp_load_of (FullArenaTactics.c0_load_full_q_stamp
                      (by rwa [zext32_toNat]) hm1') ?_
                    refine hJsq (_, ()) m1 ⟨rfl, ?_⟩
                    simp only [hcv', ↓reduceIte]
                    dsimp only [Arg.val, sl, s1]
                    rw [List.getElem?_eq_getElem (by
                        rw [hqsl]; exact Nat.lt_of_lt_of_le hcv' hcv_le), Option.getD_some]
                    simp only [zext32_toNat]
                  · have hidx_eq : ((root <<< 1#64).toNat + 1 + 1) % 2 ^ 64 =
                        (root <<< 1#64 + 1#64 + 1#64).toNat := by bv_omega
                    simp only [hidx_eq, Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64)]
                      at hc
                    have hcv' : ¬ sl.toNat < s.core.cur_vars := hc
                    refine hJsq (0#32, ()) m1 ⟨rfl, by simp only [hcv', ↓reduceIte]⟩
              · refine hJsib (root <<< 1#64 + 1#64, cl, cq, ()) m1
                  ⟨rfl, Or.inl hch_eq, by rw [hch_eq]; exact hch_lt_n,
                    by rw [hch_eq]; exact hcl_raw, hcq,
                    fun _ => by rw [← hcl_raw]; exact bumpStampLe_refl _ _ _,
                    fun h2 => absurd h2 (by c0_bound)⟩
          · intro _ hJcq
            c0_hsteps_nogrp
            · have hidx_eq : ((root <<< 1#64).toNat + 1) % 2 ^ 64 =
                  (root <<< 1#64 + 1#64).toNat := by bv_omega
              simp only [hidx_eq, Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64)] at hc
              have hcv' : cl.toNat < s.core.cur_vars := hc
              have hcl_lt : cl.toNat < s1.scratch.q_stamp.length := by
                dsimp only [s1]; rw [hqsl]; exact Nat.lt_of_lt_of_le hcv' hcv_le
              refine wp_load_of (FullArenaTactics.c0_load_full_q_stamp
                (by rwa [zext32_toNat]) hm1') ?_
              refine hJcq (_, ()) m1 ⟨rfl, ?_⟩
              simp only [hcv', ↓reduceIte]
              dsimp only [Arg.val, cl, s1]
              rw [List.getElem?_eq_getElem (by
                  rw [hqsl]; exact Nat.lt_of_lt_of_le hcv' hcv_le), Option.getD_some]
              simp only [zext32_toNat]
            · have hidx_eq : ((root <<< 1#64).toNat + 1) % 2 ^ 64 =
                  (root <<< 1#64 + 1#64).toNat := by bv_omega
              simp only [hidx_eq, Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64)] at hc
              have hcv' : ¬ cl.toNat < s.core.cur_vars := hc
              refine hJcq (0#32, ()) m1 ⟨rfl, by simp only [hcv', ↓reduceIte]⟩
        · rename_i hc; cases hc

private theorem sort_extract_step {cv n end_v : Nat} {qs ws : List (BitVec 32)}
    (hend1 : 1 ≤ end_v) (hendn : end_v < n) (hwl : n ≤ ws.length)
    (hheap : FullBumpMaxHeap cv qs ws 0 (end_v + 1))
    (hsuf : ∀ i j, end_v + 1 ≤ i → i ≤ j → j < n →
      bumpStampLe cv qs (ws[i]?.getD 0#32) (ws[j]?.getD 0#32))
    (hcross : ∀ i j, i < end_v + 1 → end_v + 1 ≤ j → j < n →
      bumpStampLe cv qs (ws[i]?.getD 0#32) (ws[j]?.getD 0#32)) :
    let ws' := (ws.set 0 (ws[end_v]'(by omega))).set end_v (ws[0]'(by omega))
    FullBumpMaxHeap cv qs ws' 1 end_v ∧
    (∀ i j, end_v ≤ i → i ≤ j → j < n →
      bumpStampLe cv qs (ws'[i]?.getD 0#32) (ws'[j]?.getD 0#32)) ∧
    (∀ i j, i < end_v → end_v ≤ j → j < n →
      bumpStampLe cv qs (ws'[i]?.getD 0#32) (ws'[j]?.getD 0#32)) := by
  intro ws'
  have h0_len : 0 < ws.length := by omega
  have he_len : end_v < ws.length := by omega
  have hsw := fun k => swap_getElem?_eq 0#32 ws h0_len he_len k
  refine ⟨?_, ?_, ?_⟩
  · intro i hi1 hie
    have hi_old := hheap i (by omega) (by omega)
    have h1 : ws'[i]?.getD 0#32 = ws[i]?.getD 0#32 := by
      rw [hsw]; simp [swapIdx, show i ≠ 0 by omega, show i ≠ end_v by omega]
    constructor <;> intro hbd
    · rw [h1, hsw]
      simp [swapIdx, show 2 * i + 1 ≠ end_v by omega]
      exact hi_old.1 (by omega)
    · rw [h1, hsw]
      simp [swapIdx, show 2 * i + 2 ≠ end_v by omega]
      exact hi_old.2 (by omega)
  · intro i j hie hij hj
    rcases Nat.eq_or_lt_of_le hij with rfl | hlt
    · exact bumpStampLe_refl cv qs _
    · by_cases hi_eq : i = end_v
      · subst hi_eq
        have hj_gt : i + 1 ≤ j := by omega
        have hwi : ws'[i]?.getD 0#32 = ws[0]?.getD 0#32 := by
          rw [hsw]; simp [swapIdx, show i ≠ 0 by omega]
        have hwj : ws'[j]?.getD 0#32 = ws[j]?.getD 0#32 := by
          rw [hsw]; simp [swapIdx, show j ≠ 0 by omega, show j ≠ i by omega]
        rw [hwi, hwj]
        exact hcross 0 j (by omega) hj_gt hj
      · have hi_gt : end_v + 1 ≤ i := by omega
        have hwi : ws'[i]?.getD 0#32 = ws[i]?.getD 0#32 := by
          rw [hsw]; simp [swapIdx, show i ≠ 0 by omega, show i ≠ end_v by omega]
        have hwj : ws'[j]?.getD 0#32 = ws[j]?.getD 0#32 := by
          rw [hsw]; simp [swapIdx, show j ≠ 0 by omega, show j ≠ end_v by omega]
        rw [hwi, hwj]
        exact hsuf i j hi_gt (Nat.le_of_lt hlt) hj
  · intro i j hie hj1 hj
    have hsi : (ws'[i]?.getD 0#32) =
        ws[if i = 0 then end_v else i]?.getD 0#32 := by
      rw [hsw]
      by_cases hi0 : i = 0
      · subst hi0; simp [swapIdx]
      · simp [swapIdx, hi0, show i ≠ end_v by omega]
    have hidx : (if i = 0 then end_v else i) < end_v + 1 := by
      by_cases hi0 : i = 0 <;> simp [hi0] <;> omega
    rw [hsi]
    by_cases hje : j = end_v
    · subst hje
      have hwj : ws'[j]?.getD 0#32 = ws[0]?.getD 0#32 := by
        rw [hsw]; simp [swapIdx, show j ≠ 0 by omega]
      rw [hwj]
      exact maxHeap_root_ge hheap _ hidx
    · have hj_gt : end_v + 1 ≤ j := by omega
      have hwj : ws'[j]?.getD 0#32 = ws[j]?.getD 0#32 := by
        rw [hsw]; simp [swapIdx, show j ≠ 0 by omega, show j ≠ end_v by omega]
      rw [hwj]
      exact hcross _ j hidx hj_gt hj

theorem full_bump_sort_stamps_m7_wp (Γ : Env)
    (hSift : ∀ a m Q X, m7BumpSiftSpec a m Q X → Γ "full_bump_sift_m7" [i64, i64, i64] [] a m Q X) :
    ∀ a m Q X, m7BumpSortStampsSpec a m Q X → Func.wp Γ full_bump_sort_stamps_m7_body a m Q X := by
  rintro ⟨h, n, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hncv, hm, hQ⟩
  have hmax : c.max_vars < 2 * dimacsBound := c.hmaxv
  unfold dimacsBound at hmax
  obtain hcv_le := hlen.core_ok.cur_vars_le
  obtain hwsl := hlen.scratch_ok.work_stk1_len
  c0_hsteps_nogrp
  · refine hQ s.scratch.work_stk1 m hwsl (List.Perm.refl _) (fun _ _ => rfl) ?_ hm
    intro i j hij hj
    have hn1 : n.toNat ≤ 1 := by c0_bound
    have hij_eq : i = j := by omega
    subst hij_eq; exact bumpStampLe_refl _ _ _
  · have hn_gt1 : 1 < n.toNat := by c0_bound
    refine wp_loop_inv (ts := [i64])
      (fun (st, ()) m1 =>
        ∃ ws1 : List (BitVec 32),
          st.toNat ≤ n.toNat / 2 ∧
          ws1.length = 2 * c.max_vars ∧
          (ws1.take n.toNat).Perm (s.scratch.work_stk1.take n.toNat) ∧
          (∀ k, n.toNat ≤ k → ws1[k]? = s.scratch.work_stk1[k]?) ∧
          FullBumpMaxHeap s.core.cur_vars s.scratch.q_stamp ws1 st.toNat n.toNat ∧
          (FullMem c { core := s.core, scratch := { s.scratch with work_stk1 := ws1 } } ⋆ R) m1)
      (fun (st, ()) _ => st.toNat) ?_ ?_
    · intro J hJ
      c0_hsteps
      have hhalf : (n >>> 1#64).toNat = n.toNat / 2 := by
        simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
      refine hJ (n >>> 1#64, ()) m ⟨s.scratch.work_stk1, by rw [hhalf]; exact Nat.le_refl _,
        hwsl, List.Perm.refl _, fun _ _ => rfl, ?_, by simpa using hm⟩
      intro i hi1 hi2
      have hch1 : ¬ 2 * i + 1 < n.toNat := by omega
      have hch2 : ¬ 2 * i + 2 < n.toNat := by omega
      exact ⟨fun h => absurd h hch1, fun h => absurd h hch2⟩
    · rintro J ⟨st, ⟨⟩⟩ m1 ⟨ws1, hst_le, hwl, hperm, htail, hheap, hm1⟩ hJ
      let s1 : FullState := { core := s.core, scratch := { s.scratch with work_stk1 := ws1 } }
      c0_hsteps_nogrp
      · have hst_pos : 0 < st.toNat := by c0_bound
        have hst_sub : (st - 1#64).toNat = st.toNat - 1 := by bv_omega
        have hst_n : (st - 1#64).toNat < n.toNat := by omega
        have hheap' : FullBumpMaxHeap s.core.cur_vars s.scratch.q_stamp ws1
            ((st - 1#64).toNat + 1) n.toNat := by
          rwa [hst_sub, Nat.sub_add_cancel hst_pos]
        have hlen1 : s1.LengthsOk c :=
          ⟨hlen.core_ok, { hlen.scratch_ok with work_stk1_len := hwl }⟩
        c0_call hSift
        refine ⟨c, s1, R, rfl, hlen1, hst_n, hncv, hheap', hm1, ?_⟩
        intro ws2 m2 hwl2 hperm2 htail2 hheap2 hm2
        have hperm_all : (ws2.take n.toNat).Perm (s.scratch.work_stk1.take n.toNat) :=
          hperm2.trans hperm
        have htail_all : ∀ k, n.toNat ≤ k → ws2[k]? = s.scratch.work_stk1[k]? := by
          intro k hk; rw [htail2 k hk, htail k hk]
        exact hJ (st - 1#64, ()) m2 (by dsimp only; omega)
          ⟨ws2, by omega, hwl2, hperm_all, htail_all, hheap2, hm2⟩
      · have hst0 : st.toNat = 0 := by c0_bound
        rw [hst0] at hheap
        refine wp_loop_inv (ts := [i64])
          (fun (ev, ()) m3 =>
            ∃ ws3 : List (BitVec 32),
              1 ≤ ev.toNat ∧ ev.toNat ≤ n.toNat ∧
              ws3.length = 2 * c.max_vars ∧
              (ws3.take n.toNat).Perm (s.scratch.work_stk1.take n.toNat) ∧
              (∀ k, n.toNat ≤ k → ws3[k]? = s.scratch.work_stk1[k]?) ∧
              FullBumpMaxHeap s.core.cur_vars s.scratch.q_stamp ws3 0 ev.toNat ∧
              (∀ i j, ev.toNat ≤ i → i ≤ j → j < n.toNat →
                bumpStampLe s.core.cur_vars s.scratch.q_stamp
                  (ws3[i]?.getD 0#32) (ws3[j]?.getD 0#32)) ∧
              (∀ i j, i < ev.toNat → ev.toNat ≤ j → j < n.toNat →
                bumpStampLe s.core.cur_vars s.scratch.q_stamp
                  (ws3[i]?.getD 0#32) (ws3[j]?.getD 0#32)) ∧
              (FullMem c { core := s.core, scratch := { s.scratch with work_stk1 := ws3 } } ⋆ R)
                m3)
          (fun (ev, ()) _ => ev.toNat) ?_ ?_
        · intro Je hJe
          c0_hsteps
          exact hJe (n, ()) m1 ⟨ws1, by omega, Nat.le_refl _, hwl, hperm, htail, hheap,
            fun _ _ _ _ hj => absurd hj (by omega), fun _ _ _ _ hj => absurd hj (by omega), hm1⟩
        · rintro Je ⟨ev, ⟨⟩⟩ m3
            ⟨ws3, he1, hen, hwl3, hperm3, htail3, hheap3, hsuf3, hcross3, hm3⟩ hJe
          let s3 : FullState := { core := s.core, scratch := { s.scratch with work_stk1 := ws3 } }
          c0_hsteps_nogrp
          · have hev_gt1 : 1 < ev.toNat := by c0_bound
            have hle1 : (1 : BitVec 64) ≤ ev := by
              rw [BitVec.le_def]; change 1 ≤ ev.toNat; omega
            have hev_sub : (ev - 1).toNat = ev.toNat - 1 := by
              rw [BitVec.toNat_sub_of_le hle1]; rfl
            have h0_lt : 0 < ws3.length := by rw [hwl3]; omega
            have hev_lt : (ev - 1).toNat < ws3.length := by rw [hwl3, hev_sub]; omega
            have hset0_lt : (ev - 1).toNat <
                (ws3.set 0 (ws3[(ev - 1).toNat]'hev_lt)).length := by
              rw [List.length_set]; exact hev_lt
            c0_hsteps_nogrp
            let ws4 := (ws3.set 0 (ws3[ev.toNat - 1]'(by rw [hwl3]; omega))).set
              (ev.toNat - 1) (ws3[0]'(by rw [hwl3]; omega))
            have hheap3' : FullBumpMaxHeap s.core.cur_vars s.scratch.q_stamp ws3
                0 ((ev.toNat - 1) + 1) := by
              rwa [Nat.sub_add_cancel he1]
            have hsuf3' : ∀ i j, (ev.toNat - 1) + 1 ≤ i → i ≤ j → j < n.toNat →
                bumpStampLe s.core.cur_vars s.scratch.q_stamp
                  (ws3[i]?.getD 0#32) (ws3[j]?.getD 0#32) := by
              rwa [Nat.sub_add_cancel he1]
            have hcross3' : ∀ i j, i < (ev.toNat - 1) + 1 → (ev.toNat - 1) + 1 ≤ j →
                j < n.toNat → bumpStampLe s.core.cur_vars s.scratch.q_stamp
                  (ws3[i]?.getD 0#32) (ws3[j]?.getD 0#32) := by
              rwa [Nat.sub_add_cancel he1]
            have hext := sort_extract_step (by omega) (by omega) (by omega)
              hheap3' hsuf3' hcross3'
            let s4' : FullState :=
              { core := s.core, scratch := { s.scratch with work_stk1 := ws4 } }
            have hlen4' : s4'.LengthsOk c :=
              ⟨hlen.core_ok, { hlen.scratch_ok with
                work_stk1_len := by
                  dsimp only [s4', ws4]; rw [List.length_set, List.length_set, hwl3] }⟩
            have hev_lt_max : (ev - 1).toNat < 2 * c.max_vars := by rw [hev_sub]; omega
            have hev_mod : (18446744073709551615 + ev.toNat) % 18446744073709551616 =
                ev.toNat - 1 := by omega
            c0_call hSift
            refine ⟨c, s4', R, rfl, hlen4', ?_,
              by dsimp only [s4']; rw [hev_sub]; omega, ?_, ?_, ?_⟩
            · change 0 < (ev - 1).toNat; rw [hev_sub]; omega
            · try dsimp only [s4']
              rw [hev_sub]; exact hext.1
            · simpa [s4', ws4, hev_mod, hev_sub] using hm
            · intro ws5 m6 hwl5 hperm5 htail5 hheap5 hm6
              have hperm_all : (ws5.take n.toNat).Perm (s.scratch.work_stk1.take n.toNat) := by
                have hp_ws4 : (ws4.take n.toNat).Perm (s.scratch.work_stk1.take n.toNat) :=
                  (swap_perm_take ws3 (by omega) (by omega) (by omega)).trans hperm3
                have hp_up : (ws5.take n.toNat).Perm (ws4.take n.toNat) :=
                  perm_take_smaller (by rw [hev_sub]; omega)
                    (by simpa [hev_sub] using hperm5) htail5
                    (by rw [hwl5]; omega)
                    (by dsimp only [ws4]; rw [List.length_set, List.length_set, hwl3]; omega)
                exact hp_up.trans hp_ws4
              have htail_all : ∀ k, n.toNat ≤ k → ws5[k]? = s.scratch.work_stk1[k]? := by
                intro k hk
                rw [htail5 k (by rw [hev_sub]; omega)]
                rw [swap_getElem?_raw ws3 (by rw [hwl3]; omega) (by rw [hwl3]; omega) k]
                have hsw : swapIdx 0 (ev.toNat - 1) k = k := by
                  unfold swapIdx; simp [show k ≠ 0 by omega, show k ≠ ev.toNat - 1 by omega]
                rw [hsw]; exact htail3 k hk
              have hsuf5 : ∀ i j, (ev - 1).toNat ≤ i → i ≤ j → j < n.toNat →
                  bumpStampLe s.core.cur_vars s.scratch.q_stamp
                    (ws5[i]?.getD 0#32) (ws5[j]?.getD 0#32) := by
                intro i j hij hle hj
                have hsi : ws5[i]? = ws4[i]? := htail5 i (by rw [hev_sub]; omega)
                have hsj : ws5[j]? = ws4[j]? := htail5 j (by rw [hev_sub]; omega)
                have hsi' : ws5[i]?.getD 0#32 = ws4[i]?.getD 0#32 := by rw [hsi]
                have hsj' : ws5[j]?.getD 0#32 = ws4[j]?.getD 0#32 := by rw [hsj]
                rw [hsi', hsj']
                exact hext.2.1 i j (by rw [hev_sub] at hij; exact hij) hle hj
              have hcross5 : ∀ i j, i < (ev - 1).toNat → (ev - 1).toNat ≤ j →
                  j < n.toNat → bumpStampLe s.core.cur_vars s.scratch.q_stamp
                    (ws5[i]?.getD 0#32) (ws5[j]?.getD 0#32) := by
                intro i j hi hj1 hj
                have hmem_i : ws5[i]'(by rw [hwl5]; omega) ∈
                    ws5.take (ev - 1).toNat := by
                  have : (ws5.take (ev - 1).toNat)[i]'(by
                      rw [List.length_take, hwl5]; omega) =
                      ws5[i]'(by rw [hwl5]; omega) := List.getElem_take
                  rw [← this]; exact List.getElem_mem _
                have hmem_i4 := (hperm5.mem_iff).mp hmem_i
                rw [List.mem_iff_getElem] at hmem_i4
                obtain ⟨k, hk, hkeq⟩ := hmem_i4
                rw [List.length_take, show s4'.scratch.work_stk1.length = 2 * c.max_vars by
                    dsimp only [s4', ws4]; rw [List.length_set, List.length_set, hwl3],
                  Nat.min_eq_left (by rw [hev_sub]; omega)] at hk
                rw [List.getElem_take] at hkeq
                have hwi : ws5[i]?.getD 0#32 = ws4[k]?.getD 0#32 := by
                  have hws4_len : ws4.length = 2 * c.max_vars := by
                    dsimp only [ws4]; rw [List.length_set, List.length_set, hwl3]
                  rw [List.getElem?_eq_getElem (by rw [hwl5]; omega),
                    List.getElem?_eq_getElem (by rw [hws4_len]; omega),
                    Option.getD_some, Option.getD_some, ← hkeq]
                have hwj : ws5[j]?.getD 0#32 = ws4[j]?.getD 0#32 :=
                  congrArg (·.getD 0#32) (htail5 j (by rw [hev_sub]; omega))
                rw [hwi, hwj]
                exact hext.2.2 k j (by rw [hev_sub] at hk; exact hk)
                  (by rw [hev_sub] at hj1; exact hj1) hj
              exact hJe (ev - 1, ()) m6 (by dsimp only; rw [hev_sub]; omega)
                ⟨ws5, by rw [hev_sub]; omega, by rw [hev_sub]; omega, hwl5, hperm_all, htail_all,
                  hheap5, hsuf5, hcross5, hm6⟩
          · have hev_eq1 : ev.toNat = 1 := by c0_bound
            refine hQ ws3 m3 hwl3 hperm3 htail3 ?_ hm3
            intro i j hij hj
            by_cases hi0 : i = 0
            · subst hi0
              rcases Nat.eq_zero_or_pos j with rfl | hjpos
              · exact bumpStampLe_refl _ _ _
              · exact hcross3 0 j (by omega) (by omega) hj
            · exact hsuf3 i j (by omega) hij hj

end BumpSortProof

/-! ## 6. WP Proofs for `full_bump_reasons_m7` and `full_bump_analyzed_m7` -/

section BumpAnalyzedProof

open scoped FullArenaTactics

private theorem m7_add32 {Γ} {rs : List Ty} {Q : Post rs} {X} {a b : Arg Val i32} {k m} :
    wp Γ Q X (.let_ (Op.mk (.add i32) (a, b, ())) k) m =
      wp Γ Q X (k (a.val + b.val, ())) m := by simp [wp_let_add_eq, lift2]
private theorem m7_add64 {Γ} {rs : List Ty} {Q : Post rs} {X} {a b : Arg Val i64} {k m} :
    wp Γ Q X (.let_ (Op.mk (.add i64) (a, b, ())) k) m =
      wp Γ Q X (k (a.val + b.val, ())) m := by simp [wp_let_add_eq, lift2]
private theorem m7_sub64 {Γ} {rs : List Ty} {Q : Post rs} {X} {a b : Arg Val i64} {k m} :
    wp Γ Q X (.let_ (Op.mk (.sub i64) (a, b, ())) k) m =
      wp Γ Q X (k (a.val - b.val, ())) m := by simp [wp_let_sub_eq, lift2]
private theorem m7_mul64 {Γ} {rs : List Ty} {Q : Post rs} {X} {a b : Arg Val i64} {k m} :
    wp Γ Q X (.let_ (Op.mk (.mul i64) (a, b, ())) k) m =
      wp Γ Q X (k (a.val * b.val, ())) m := by simp [wp_let_mul_eq, lift2]
private theorem m7_lshr32_imm1 {Γ} {rs : List Ty} {Q : Post rs} {X} {a : Arg Val i32} {k m} :
    wp Γ Q X (.let_ (Op.mk (.lshr i32) (a, .imm 1, ())) k) m =
      wp Γ Q X (k (a.val >>> (1 : Nat), ())) m := by simp [wp_let_lshr_eq, lift2]
private theorem m7_lshr32_imm1' {Γ} {rs : List Ty} {Q : Post rs} {X} {a : Arg Val i32} {k m} :
    wp Γ Q X (.let_ (Op.mk (.lshr i32) (a, .imm 1#32, ())) k) m =
      wp Γ Q X (k (a.val >>> (1 : Nat), ())) m := by simp [wp_let_lshr_eq, lift2]
private theorem m7_lshr32 {Γ} {rs : List Ty} {Q : Post rs} {X} {a b : Arg Val i32} {k m} :
    wp Γ Q X (.let_ (Op.mk (.lshr i32) (a, b, ())) k) m =
      wp Γ Q X (k (a.val >>> (b.val.toNat % 32), ())) m := by simp [wp_let_lshr_eq, lift2]
private theorem m7_and32 {Γ} {rs : List Ty} {Q : Post rs} {X} {a b : Arg Val i32} {k m} :
    wp Γ Q X (.let_ (Op.mk (.and i32) (a, b, ())) k) m =
      wp Γ Q X (k (a.val &&& b.val, ())) m := by simp [wp_let_and_eq, lift2]
private theorem m7_zext32_64 {Γ} {rs : List Ty} {Q : Post rs} {X} {a : Arg Val i32} {k m} :
    wp Γ Q X (.let_ (Op.mk (.zext 32 64) (a, ())) k) m =
      wp Γ Q X (k (a.val.setWidth 64, ())) m := by simp [wp_let_zext_eq]
private theorem m7_zext8_32 {Γ} {rs : List Ty} {Q : Post rs} {X} {a : Arg Val i8} {k m} :
    wp Γ Q X (.let_ (Op.mk (.zext 8 32) (a, ())) k) m =
      wp Γ Q X (k (a.val.setWidth 32, ())) m := by simp [wp_let_zext_eq]
private theorem m7_trunc32_8 {Γ} {rs : List Ty} {Q : Post rs} {X} {a : Arg Val i32} {k m} :
    wp Γ Q X (.let_ (Op.mk (.trunc 32 8) (a, ())) k) m =
      wp Γ Q X (k (a.val.setWidth 8, ())) m := by simp [wp_let_trunc_eq]
private theorem m7_ult32 {Γ} {rs : List Ty} {Q : Post rs} {X} {a b : Arg Val i32} {h} {k m} :
    wp Γ Q X (.let_ (Op.mk (.cmp .ult i32 .bool h) (a, b, ())) k) m =
      wp Γ Q X (k (a.val.ult b.val, ())) m := by simp [wp_let_cmp_eq, liftCmp, evalBits_ult_eq]
private theorem m7_ule32 {Γ} {rs : List Ty} {Q : Post rs} {X} {a b : Arg Val i32} {h} {k m} :
    wp Γ Q X (.let_ (Op.mk (.cmp .ule i32 .bool h) (a, b, ())) k) m =
      wp Γ Q X (k (a.val.ule b.val, ())) m := by simp [wp_let_cmp_eq, liftCmp, evalBits_ule_eq]
private theorem m7_ugt32 {Γ} {rs : List Ty} {Q : Post rs} {X} {a b : Arg Val i32} {h} {k m} :
    wp Γ Q X (.let_ (Op.mk (.cmp .ugt i32 .bool h) (a, b, ())) k) m =
      wp Γ Q X (k (b.val.ult a.val, ())) m := by simp [wp_let_cmp_eq, liftCmp, evalBits_ugt_eq]
private theorem m7_uge32 {Γ} {rs : List Ty} {Q : Post rs} {X} {a b : Arg Val i32} {h} {k m} :
    wp Γ Q X (.let_ (Op.mk (.cmp .uge i32 .bool h) (a, b, ())) k) m =
      wp Γ Q X (k (b.val.ule a.val, ())) m := by simp [wp_let_cmp_eq, liftCmp, evalBits_uge_eq]
private theorem m7_eq32 {Γ} {rs : List Ty} {Q : Post rs} {X} {a b : Arg Val i32} {h} {k m} :
    wp Γ Q X (.let_ (Op.mk (.cmp .eq i32 .bool h) (a, b, ())) k) m =
      wp Γ Q X (k (a.val == b.val, ())) m := by simp [wp_let_cmp_eq, liftCmp, evalBits_eq_beq]
private theorem m7_ne32 {Γ} {rs : List Ty} {Q : Post rs} {X} {a b : Arg Val i32} {h} {k m} :
    wp Γ Q X (.let_ (Op.mk (.cmp .ne i32 .bool h) (a, b, ())) k) m =
      wp Γ Q X (k (a.val != b.val, ())) m := by simp [wp_let_cmp_eq, liftCmp, evalBits_ne_bne]
private theorem m7_ult64 {Γ} {rs : List Ty} {Q : Post rs} {X} {a b : Arg Val i64} {h} {k m} :
    wp Γ Q X (.let_ (Op.mk (.cmp .ult i64 .bool h) (a, b, ())) k) m =
      wp Γ Q X (k (a.val.ult b.val, ())) m := by simp [wp_let_cmp_eq, liftCmp, evalBits_ult_eq]
private theorem m7_ule64 {Γ} {rs : List Ty} {Q : Post rs} {X} {a b : Arg Val i64} {h} {k m} :
    wp Γ Q X (.let_ (Op.mk (.cmp .ule i64 .bool h) (a, b, ())) k) m =
      wp Γ Q X (k (a.val.ule b.val, ())) m := by simp [wp_let_cmp_eq, liftCmp, evalBits_ule_eq]
private theorem m7_ugt64 {Γ} {rs : List Ty} {Q : Post rs} {X} {a b : Arg Val i64} {h} {k m} :
    wp Γ Q X (.let_ (Op.mk (.cmp .ugt i64 .bool h) (a, b, ())) k) m =
      wp Γ Q X (k (b.val.ult a.val, ())) m := by simp [wp_let_cmp_eq, liftCmp, evalBits_ugt_eq]
private theorem m7_uge64 {Γ} {rs : List Ty} {Q : Post rs} {X} {a b : Arg Val i64} {h} {k m} :
    wp Γ Q X (.let_ (Op.mk (.cmp .uge i64 .bool h) (a, b, ())) k) m =
      wp Γ Q X (k (b.val.ule a.val, ())) m := by simp [wp_let_cmp_eq, liftCmp, evalBits_uge_eq]
private theorem m7_eq64 {Γ} {rs : List Ty} {Q : Post rs} {X} {a b : Arg Val i64} {h} {k m} :
    wp Γ Q X (.let_ (Op.mk (.cmp .eq i64 .bool h) (a, b, ())) k) m =
      wp Γ Q X (k (a.val == b.val, ())) m := by simp [wp_let_cmp_eq, liftCmp, evalBits_eq_beq]
private theorem m7_ne64 {Γ} {rs : List Ty} {Q : Post rs} {X} {a b : Arg Val i64} {h} {k m} :
    wp Γ Q X (.let_ (Op.mk (.cmp .ne i64 .bool h) (a, b, ())) k) m =
      wp Γ Q X (k (a.val != b.val, ())) m := by simp [wp_let_cmp_eq, liftCmp, evalBits_ne_bne]
private theorem m7_copy64 {Γ} {rs : List Ty} {Q : Post rs} {X} {a : Arg Val i64} {k m} :
    wp Γ Q X (.let_ (Op.mk (.copy i64) (a, ())) k) m =
      wp Γ Q X (k (a.val, ())) m := by simp [wp_let_copy_eq]
private theorem m7_copy32 {Γ} {rs : List Ty} {Q : Post rs} {X} {a : Arg Val i32} {k m} :
    wp Γ Q X (.let_ (Op.mk (.copy i32) (a, ())) k) m =
      wp Γ Q X (k (a.val, ())) m := by simp [wp_let_copy_eq]
private theorem m7_fst {α β : Type _} (a : α) (b : β) : (a, b).fst = a := rfl
private theorem m7_jnz_eq {Γ} {rs : List Ty} {Q : Post rs} {X} {c : Val .bool} {t e m} :
    wp Γ Q X (.jnz (.var c) t e) m =
      ((c = true → wp Γ Q X t m) ∧ (c = false → wp Γ Q X e m)) := rfl
private theorem m7_ret0 {Γ} {Q : Post []} {X} {m} :
    wp Γ Q X (.ret ()) m = Q () m := rfl

local macro "m7_lets" : tactic => `(tactic| repeat (first
  | rw [m7_fst] | rw [m7_lshr32_imm1] | rw [m7_lshr32_imm1']
  | rw [m7_add32] | rw [m7_add64] | rw [m7_sub64] | rw [m7_mul64]
  | rw [m7_lshr32] | rw [m7_and32] | rw [m7_zext32_64] | rw [m7_zext8_32] | rw [m7_trunc32_8]
  | rw [m7_ult32] | rw [m7_ule32] | rw [m7_ugt32] | rw [m7_uge32] | rw [m7_eq32] | rw [m7_ne32]
  | rw [m7_ult64] | rw [m7_ule64] | rw [m7_ugt64] | rw [m7_uge64] | rw [m7_eq64] | rw [m7_ne64]
  | rw [m7_copy64] | rw [m7_copy32]
  | rw [Arg.val_var] | rw [Arg.val_imm]))

local macro "m7_ld " lem:term : tactic =>
  `(tactic| (m7_lets; refine LeanQbe.T.wp_load_of ($lem) ?_))

local macro "m7_st" m:ident "," h:ident ":=" lem:term : tactic =>
  `(tactic| ((m7_lets; apply LeanQbe.T.wp_store_sep; · exact $lem); intro $m:ident $h:ident))

local macro "m7_jnz" : tactic => `(tactic| rw [m7_jnz_eq])

private theorem m7b_zext32 (x : BitVec 32) : (BitVec.setWidth 64 x).toNat = x.toNat :=
  zext_toNat x (by decide)

private theorem m7b_ofNat64 {n : Nat} (hn : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]

private theorem m7b_ult64 {a b : BitVec 64} (h : a.ult b = true) : a.toNat < b.toNat := by
  simpa [BitVec.ult] using h

private theorem m7b_not_ult64 {a b : BitVec 64} (h : a.ult b = false) : b.toNat ≤ a.toNat := by
  simp [BitVec.ult] at h; exact h

private theorem m7b_ule64 {a b : BitVec 64} (h : a.ule b = true) : a.toNat ≤ b.toNat := by
  simpa [BitVec.ule] using h

private theorem m7b_bv8_zero {x : BitVec 8} (h : (x.setWidth 32 == 0#32) = true) : x = 0#8 := by
  have hx := beq_iff_eq.mp h
  apply BitVec.eq_of_toNat_eq
  have hx' := congrArg BitVec.toNat hx
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := x.isLt; omega)] at hx'
  exact hx'

private theorem m7b_nodup_inj {xs : List Nat} (hnd : xs.Nodup) :
    ∀ {i j : Nat} (hi : i < xs.length) (hj : j < xs.length), xs[i] = xs[j] → i = j := by
  induction xs with
  | nil => intro i _ hi; simp at hi
  | cons a t ih =>
    rw [List.nodup_cons] at hnd
    intro i j hi hj heq
    cases i with
    | zero =>
      cases j with
      | zero => rfl
      | succ j' =>
        exfalso; apply hnd.1
        simp only [List.getElem_cons_zero, List.getElem_cons_succ] at heq
        rw [heq]; exact List.getElem_mem _
    | succ i' =>
      cases j with
      | zero =>
        exfalso; apply hnd.1
        simp only [List.getElem_cons_zero, List.getElem_cons_succ] at heq
        rw [← heq]; exact List.getElem_mem _
      | succ j' =>
        exact congrArg Nat.succ (ih hnd.2 (by simpa using hi)
          (by simpa using hj) (by simpa using heq))

private def BumpReasonsState (s : FullState) (mrk1 : List (BitVec 8)) (mcl1 : Nat)
    (ws1 : List (BitVec 32)) : FullState :=
  { core := { s.core with mrk := mrk1, min_clr_len := mcl1 }
    scratch := { s.scratch with work_stk1 := ws1 } }

private def BumpReasonsInv (c : FullCfg) (s s1 : FullState) : Prop :=
  s1.LengthsOk c ∧
  (∃ mrk1 mcl1 ws1, s1 = BumpReasonsState s mrk1 mcl1 ws1) ∧
  FullAnaMarksCov c s1

private theorem bumpReasonsInv_init {c : FullCfg} {s : FullState}
    (hlen : s.LengthsOk c) (hcov : FullAnaMarksCov c s) : BumpReasonsInv c s s :=
  ⟨hlen, ⟨s.core.mrk, s.core.min_clr_len, s.scratch.work_stk1, by cases s; rfl⟩, hcov⟩

private theorem bumpReasonsState_upd {s s1 : FullState}
    (h : ∃ mrk0 mcl0 ws0, s1 = BumpReasonsState s mrk0 mcl0 ws0)
    (mrk' : List (BitVec 8)) (mcl' : Nat) (ws' : List (BitVec 32)) :
    ∃ mrk1 mcl1 ws1,
      { core := { s1.core with mrk := mrk', min_clr_len := mcl' }
        scratch := { s1.scratch with work_stk1 := ws' } } =
      BumpReasonsState s mrk1 mcl1 ws1 := by
  rcases h with ⟨mrk0, mcl0, ws0, rfl⟩
  exact ⟨mrk', mcl', ws', rfl⟩

private theorem bumpReasons_fields {s s1 : FullState}
    (h : ∃ mrk1 mcl1 ws1, s1 = BumpReasonsState s mrk1 mcl1 ws1) :
    s1.core.cur_vars = s.core.cur_vars ∧ s1.core.tmp_len = s.core.tmp_len ∧
    s1.core.arena_len = s.core.arena_len ∧ s1.core.tmp = s.core.tmp ∧
    s1.core.rsns = s.core.rsns ∧ s1.core.lvl = s.core.lvl ∧
    s1.core.arena = s.core.arena := by
  rcases h with ⟨mrk1, mcl1, ws1, rfl⟩
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem bumpReasons_lengths_upd {c : FullCfg} {s1 : FullState}
    (hlen : s1.LengthsOk c) (mrk' : List (BitVec 8)) (mcl' : Nat) (ws1' : List (BitVec 32))
    (hmrk : mrk'.length = c.max_vars) (hmcl : mcl' ≤ c.max_vars)
    (hws1 : ws1'.length = 2 * c.max_vars) :
    ({ core := { s1.core with mrk := mrk', min_clr_len := mcl' }
       scratch := { s1.scratch with work_stk1 := ws1' } } : FullState).LengthsOk c :=
  ⟨{ hlen.core_ok with mrk_len := hmrk, min_clr_len_le := hmcl },
   { hlen.scratch_ok with work_stk1_len := hws1 }⟩

private theorem take_set_append_self {α : Type _} (xs : List α) (n : Nat) (v : α)
    (hn : n < xs.length) :
    (xs.set n v).take (n + 1) = xs.take n ++ [v] := by
  induction xs generalizing n with
  | nil => simp at hn
  | cons x t ih =>
    cases n with
    | zero => simp
    | succ n' =>
      simp only [List.set_cons_succ, List.take_succ_cons, List.cons_append]
      exact congrArg (x :: ·) (ih n' (by simpa using hn))

private theorem bumpReasons_push {c : FullCfg} {s s1 : FullState} {ov : BitVec 32}
    (hinv : BumpReasonsInv c s s1) (hov_lt : ov.toNat < s1.core.cur_vars)
    (hmrk0 : s1.core.mrk[ov.toNat]?.getD 0#8 = 0#8)
    (hmcl_lt : s1.core.min_clr_len < s1.core.cur_vars) :
    BumpReasonsInv c s
      { core := { s1.core with
          mrk := s1.core.mrk.set ov.toNat 1#8
          min_clr_len := s1.core.min_clr_len + 1 }
        scratch :=
          { s1.scratch with work_stk1 := s1.scratch.work_stk1.set s1.core.min_clr_len ov } } := by
  rcases hinv with ⟨hlen1, hbr1, hcov1⟩
  have hcov1' := hcov1.2.2.2; have helem1 := hcov1.2.2.1
  have hnd1 := hcov1.2.1; have hmcl1 := hcov1.1
  have hcv_le := hlen1.core_ok.cur_vars_le
  have hmrl := hlen1.core_ok.mrk_len; have hwsl := hlen1.scratch_ok.work_stk1_len
  let mcl := s1.core.min_clr_len
  have hmcl_ws : mcl < s1.scratch.work_stk1.length := by dsimp [mcl]; rw [hwsl]; omega
  have hov_mrk : ov.toNat < s1.core.mrk.length := by rw [hmrl]; omega
  let mrk2 := s1.core.mrk.set ov.toNat 1#8
  let ws2 := s1.scratch.work_stk1.set mcl ov
  have hmrk2_len : mrk2.length = c.max_vars := by dsimp [mrk2]; rw [List.length_set, hmrl]
  have hws2_len : ws2.length = 2 * c.max_vars := by dsimp [ws2]; rw [List.length_set, hwsl]
  have hmrk2_self : mrk2[ov.toNat]?.getD 0#8 = 1#8 := by
    dsimp [mrk2]
    rw [List.getElem?_eq_getElem (by rw [List.length_set]; exact hov_mrk),
      List.getElem_set_self, Option.getD_some]
  have hws2_self : ws2[mcl]?.getD 0#32 = ov := by
    dsimp [ws2]
    rw [List.getElem?_eq_getElem (by rw [List.length_set]; exact hmcl_ws),
      List.getElem_set_self, Option.getD_some]
  refine ⟨bumpReasons_lengths_upd hlen1 mrk2 (mcl + 1) ws2 hmrk2_len (by dsimp [mcl]; omega)
    hws2_len, bumpReasonsState_upd hbr1 mrk2 (mcl + 1) ws2, ?_⟩
  have hnotin : ov.toNat ∉ (s1.scratch.work_stk1.take mcl).map BitVec.toNat := by
    intro hmem
    obtain ⟨w, hw, hwv⟩ := List.mem_map.mp hmem
    obtain ⟨j, hj_len, hj_eq⟩ := List.mem_iff_getElem.mp hw
    have hj_lt : j < mcl := by
      rw [List.length_take, Nat.min_eq_left (by omega)] at hj_len; exact hj_len
    simp only [List.getElem_take] at hj_eq
    have hj_nz := (helem1 j hj_lt).2
    have hj_eq' : (s1.scratch.work_stk1[j]?.getD 0#32).toNat = ov.toNat := by
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some, hj_eq, hwv]
    rw [hj_eq'] at hj_nz; exact hj_nz hmrk0
  have htake : (ws2.take (mcl + 1)).map BitVec.toNat =
      (s1.scratch.work_stk1.take mcl).map BitVec.toNat ++ [ov.toNat] := by
    dsimp [ws2]; rw [take_set_append_self _ mcl ov hmcl_ws, List.map_append]; rfl
  refine ⟨by dsimp [mcl]; omega, ?_, ?_, ?_⟩
  · rw [htake]
    exact List.nodup_append.mpr ⟨hnd1, by simp, fun a ha b hb => by
      simp only [List.mem_singleton] at hb; subst hb; exact fun hba => hnotin (hba ▸ ha)⟩
  · intro k hk
    dsimp only
    by_cases hkm : k < mcl
    · have hws_k : ws2[k]?.getD 0#32 = s1.scratch.work_stk1[k]?.getD 0#32 :=
        congrArg (·.getD 0#32) (List.getElem?_set_ne (by omega))
      rw [hws_k]
      refine ⟨(helem1 k hkm).1, ?_⟩
      by_cases hke : (s1.scratch.work_stk1[k]?.getD 0#32).toNat = ov.toNat
      · rw [hke, hmrk2_self]; decide
      · have : mrk2[(s1.scratch.work_stk1[k]?.getD 0#32).toNat]? =
            s1.core.mrk[(s1.scratch.work_stk1[k]?.getD 0#32).toNat]? := by
          dsimp [mrk2]; exact List.getElem?_set_ne (Ne.symm hke)
        rw [this]; exact (helem1 k hkm).2
    · have hkm_eq : k = mcl := by dsimp [mcl] at hk; omega
      subst hkm_eq; rw [hws2_self, hmrk2_self]; exact ⟨hov_lt, by decide⟩
  · intro v hv hnz
    dsimp only at hnz ⊢
    by_cases hvo : v = ov.toNat
    · subst hvo; exact ⟨mcl, by dsimp [mcl]; omega, by rw [hws2_self]⟩
    · have hnz1 : s1.core.mrk[v]?.getD 0#8 ≠ 0#8 := by
        have : mrk2[v]? = s1.core.mrk[v]? := by
          dsimp [mrk2]; exact List.getElem?_set_ne (Ne.symm hvo)
        rwa [← this]
      obtain ⟨i, hi, hiv⟩ := hcov1' v hv hnz1
      have hws_i : ws2[i]?.getD 0#32 = s1.scratch.work_stk1[i]?.getD 0#32 :=
        congrArg (·.getD 0#32) (List.getElem?_set_ne (by omega))
      exact ⟨i, by omega, by rw [hws_i]; exact hiv⟩

private theorem bumpReasons_push_mem {c : FullCfg} {s s1 : FullState}
    {R : Mem 64 → Prop} {m3 : Mem 64} (ov : BitVec 32)
    (hinv1 : BumpReasonsInv c s s1) (hov_lt : ov.toNat < s1.core.cur_vars)
    (hmrk0 : s1.core.mrk[ov.toNat]?.getD 0#8 = 0#8)
    (hmcl_lt : s1.core.min_clr_len < s1.core.cur_vars)
    (hm3 : (FullMem c
      { core :=
          { s1.core with
            mrk := s1.core.mrk.set ov.toNat 1#8
            min_clr_len := (BitVec.ofNat 64 s1.core.min_clr_len + 1#64).toNat }
        scratch :=
          { s1.scratch with work_stk1 := s1.scratch.work_stk1.set s1.core.min_clr_len ov } } ⋆
      R) m3) :
    ∃ s3 : FullState, BumpReasonsInv c s s3 ∧ (FullMem c s3 ⋆ R) m3 := by
  have hmax : c.max_vars < 2 * dimacsBound := c.hmaxv
  unfold dimacsBound at hmax
  have hcv_le := hinv1.1.core_ok.cur_vars_le
  have hadd : (BitVec.ofNat 64 s1.core.min_clr_len + 1#64).toNat = s1.core.min_clr_len + 1 := by
    bv_omega
  rw [hadd] at hm3
  exact ⟨_, bumpReasons_push hinv1 hov_lt hmrk0 hmcl_lt, hm3⟩

private theorem bumpReasons_pop {c : FullCfg} {s s3 : FullState}
    (hinv : BumpReasonsInv c s s3) (hpos : 0 < s3.core.min_clr_len) :
    let mcl1 := s3.core.min_clr_len - 1
    let rv := s3.scratch.work_stk1[mcl1]'(by
      rw [hinv.1.scratch_ok.work_stk1_len]
      have := hinv.2.2.1; have := hinv.1.core_ok.cur_vars_le; omega)
    rv.toNat < s3.core.cur_vars ∧
    BumpReasonsInv c s
      { core := { s3.core with mrk := s3.core.mrk.set rv.toNat 0#8, min_clr_len := mcl1 }
        scratch := s3.scratch } := by
  rcases hinv with ⟨hlen3, hbr3, hcov3⟩
  have hcov3' := hcov3.2.2.2; have helem3 := hcov3.2.2.1
  have hnd3 := hcov3.2.1; have hmcl3 := hcov3.1
  have hcv_le := hlen3.core_ok.cur_vars_le
  have hmrl := hlen3.core_ok.mrk_len; have hwsl := hlen3.scratch_ok.work_stk1_len
  let mcl1 := s3.core.min_clr_len - 1
  have hmcl1_ws : mcl1 < s3.scratch.work_stk1.length := by dsimp [mcl1]; rw [hwsl]; omega
  let rv := s3.scratch.work_stk1[mcl1]'hmcl1_ws
  have hrv_get : s3.scratch.work_stk1[mcl1]?.getD 0#32 = rv := by
    rw [List.getElem?_eq_getElem hmcl1_ws, Option.getD_some]
  have hrv_lt : rv.toNat < s3.core.cur_vars := by
    simpa only [hrv_get] using (helem3 mcl1 (by dsimp [mcl1]; omega)).1
  have hrv_mrk : rv.toNat < s3.core.mrk.length := by
    rw [hmrl]; exact Nat.lt_of_lt_of_le hrv_lt hcv_le
  refine ⟨hrv_lt, ?_⟩
  let mrk4 := s3.core.mrk.set rv.toNat 0#8
  have hmrk4_len : mrk4.length = c.max_vars := by dsimp [mrk4]; rw [List.length_set, hmrl]
  have hmrk4_self : mrk4[rv.toNat]?.getD 0#8 = 0#8 := by
    dsimp [mrk4]
    rw [List.getElem?_eq_getElem (by rw [List.length_set]; exact hrv_mrk),
      List.getElem_set_self, Option.getD_some]
  refine ⟨bumpReasons_lengths_upd hlen3 mrk4 mcl1 s3.scratch.work_stk1 hmrk4_len
    (by dsimp [mcl1]; omega) hwsl, bumpReasonsState_upd hbr3 mrk4 mcl1 s3.scratch.work_stk1, ?_⟩
  have htake_sub : ((s3.scratch.work_stk1.take mcl1).map BitVec.toNat).Nodup := by
    have h1 : s3.scratch.work_stk1.take mcl1 =
        (s3.scratch.work_stk1.take s3.core.min_clr_len).take mcl1 := by
      rw [List.take_take, Nat.min_eq_left (by dsimp [mcl1]; omega)]
    rw [h1, List.map_take]
    exact hnd3.sublist (List.take_sublist _ _)
  have htake_len : ((s3.scratch.work_stk1.take s3.core.min_clr_len).map BitVec.toNat).length =
      s3.core.min_clr_len := by
    rw [List.length_map, List.length_take, hwsl, Nat.min_eq_left (by omega)]
  refine ⟨by dsimp [mcl1]; omega, htake_sub, ?_, ?_⟩
  · intro k hk
    dsimp only
    refine ⟨(helem3 k (by dsimp [mcl1] at hk; omega)).1, ?_⟩
    have hne_rv : (s3.scratch.work_stk1[k]?.getD 0#32).toNat ≠ rv.toNat := by
      intro heq
      have hk_take :
          k < ((s3.scratch.work_stk1.take s3.core.min_clr_len).map BitVec.toNat).length := by
        rw [htake_len]; dsimp [mcl1] at hk; omega
      have hm_take :
          mcl1 < ((s3.scratch.work_stk1.take s3.core.min_clr_len).map BitVec.toNat).length := by
        rw [htake_len]; dsimp [mcl1]; omega
      have hidx_eq : ((s3.scratch.work_stk1.take s3.core.min_clr_len).map BitVec.toNat)[k]'hk_take =
          ((s3.scratch.work_stk1.take s3.core.min_clr_len).map BitVec.toNat)[mcl1]'hm_take := by
        simp only [List.getElem_map, List.getElem_take]
        rw [List.getElem?_eq_getElem (by rw [hwsl]; dsimp [mcl1] at hk; omega),
          Option.getD_some] at heq
        exact heq
      have := m7b_nodup_inj hnd3 hk_take hm_take hidx_eq
      dsimp [mcl1] at hk; omega
    have : mrk4[(s3.scratch.work_stk1[k]?.getD 0#32).toNat]? =
        s3.core.mrk[(s3.scratch.work_stk1[k]?.getD 0#32).toNat]? := by
      dsimp [mrk4]; exact List.getElem?_set_ne (Ne.symm hne_rv)
    rw [this]; exact (helem3 k (by dsimp [mcl1] at hk; omega)).2
  · intro v hv hnz
    dsimp only at hnz ⊢
    have hne_rv : v ≠ rv.toNat := by
      intro hve; subst hve; exact hnz hmrk4_self
    have hnz3 : s3.core.mrk[v]?.getD 0#8 ≠ 0#8 := by
      have : mrk4[v]? = s3.core.mrk[v]? := List.getElem?_set_ne (Ne.symm hne_rv)
      rwa [← this]
    obtain ⟨i, hi, hiv⟩ := hcov3' v hv hnz3
    have hine : i ≠ mcl1 := by
      intro him; subst him; rw [hrv_get] at hiv; exact hne_rv hiv.symm
    exact ⟨i, by omega, hiv⟩

private theorem bumpReasons_push_wp {Γ : Env} {Q : Post []} {X : XPost}
    {c : FullCfg} {s s1 : FullState} {R : Mem 64 → Prop} {m1 : Mem 64}
    {cvv : Val i64} {Jpush : Cont []} (ov uv : BitVec 32)
    {h1 h2 h3 : Ty.bool = i32.mask} {h4 : Ty.bool = i64.mask}
    (hcvv : cvv.toNat = s.core.cur_vars) (hinv1 : BumpReasonsInv c s s1)
    (hm1 : (FullMem c s1 ⋆ R) m1)
    (hJpush : ∀ (xs : Tup Val []) (m : Mem 64),
      (∃ s2 : FullState, BumpReasonsInv c s s2 ∧ (FullMem c s2 ⋆ R) m) → Jpush xs m) :
    wp Γ Q X
      (Expr.jnz (Arg.var ((ov.setWidth 64).ult cvv))
        (Expr.let_ (Op.mk (.cmp .ne i32 .bool h1) (.var ov, .var uv, ())) fun p =>
        Expr.jnz (.var p.fst)
          (Expr.let_ (Op.mk (.zext 32 64) (.var ov, ())) fun p =>
          Expr.let_ (Op.mk (.mul i64) (.var p.fst, .imm 4, ())) fun p =>
          Expr.let_ (Op.mk (.add i64) (.var c.pLevel, .var p.fst, ())) fun p =>
          Expr.load i32 (.var p.fst) fun ld =>
          Expr.let_ (Op.mk (.cmp .ugt i32 .bool h2) (.var ld, .imm 0, ())) fun p =>
          Expr.jnz (.var p.fst)
            (Expr.let_ (Op.mk (.zext 32 64) (.var ov, ())) fun p =>
            Expr.let_ (Op.mk (.add i64) (.var c.pMark, .var p.fst, ())) fun p =>
            Expr.load i8 (.var p.fst) fun ld =>
            Expr.let_ (Op.mk (.trunc 32 8) (.imm 0, ())) fun p =>
            Expr.let_ (Op.mk (.zext 8 32) (.var ld, ())) fun p_1 =>
            Expr.let_ (Op.mk (.zext 8 32) (.var p.fst, ())) fun p =>
            Expr.let_ (Op.mk (.cmp .eq i32 .bool h3) (.var p_1.fst, .var p.fst, ())) fun p =>
            Expr.jnz (.var p.fst)
              (Expr.group (fun (_ : Tup Cont [[]]) =>
                  Blocks.cons (fun (_ : Tup Val []) => Expr.jump Jpush ()) Blocks.nil)
                fun Js =>
                Expr.let_ (Op.mk (.add i64) (.var c.hdr, .imm 272, ())) fun p =>
                Expr.load i64 (.var p.fst) fun ld =>
                Expr.let_ (Op.mk (.cmp .ult i64 .bool h4) (.var ld, .var cvv, ())) fun p =>
                Expr.jnz (.var p.fst)
                  (Expr.let_ (Op.mk (.zext 32 64) (.var ov, ())) fun p =>
                  Expr.let_ (Op.mk (.add i64) (.var c.pMark, .var p.fst, ())) fun p =>
                  Expr.let_ (Op.mk (.trunc 32 8) (.imm 1, ())) fun p_2 =>
                  Expr.store (.var p_2.fst) (.var p.fst)
                    (Expr.let_ (Op.mk (.add i64) (.var c.hdr, .imm 272, ())) fun p =>
                    Expr.load i64 (.var p.fst) fun ld =>
                    Expr.let_ (Op.mk (.mul i64) (.var ld, .imm 4, ())) fun p =>
                    Expr.let_ (Op.mk (.add i64) (.var c.pWorkStk1, .var p.fst, ())) fun p =>
                    Expr.store (t := i32) (.var (ov : Val i32)) (.var p.fst)
                      (Expr.let_ (Op.mk (.add i64) (.var c.hdr, .imm 272, ())) fun p =>
                      Expr.load i64 (.var p.fst) fun ld =>
                      Expr.let_ (Op.mk (.add i64) (.var ld, .imm 1, ())) fun p =>
                      Expr.let_ (Op.mk (.add i64) (.var c.hdr, .imm 272, ())) fun p_3 =>
                      Expr.store (.var p.fst) (.var p_3.fst) (Expr.jump Js.fst ()))))
                  (Expr.jump Js.fst ()))
              (Expr.jump Jpush ()))
            (Expr.jump Jpush ()))
          (Expr.jump Jpush ()))
        (Expr.jump Jpush ()))
      m1 := by
  have hlen1 := hinv1.1
  have hcv1 : s1.core.cur_vars = s.core.cur_vars := (bumpReasons_fields hinv1.2.1).1
  have hcv_le : s.core.cur_vars ≤ c.max_vars := by
    rw [← hcv1]; exact hlen1.core_ok.cur_vars_le
  have hmax : c.max_vars < 2 * dimacsBound := c.hmaxv
  unfold dimacsBound at hmax
  m7_jnz
  refine ⟨fun hov_ult => ?_, fun _ => by m7_lets; exact hJpush () m1 ⟨s1, hinv1, hm1⟩⟩
  have hov_lt : ov.toNat < s1.core.cur_vars := by
    have h1 := m7b_ult64 hov_ult
    rw [hcvv] at h1; rwa [hcv1]
  m7_lets; m7_jnz
  refine ⟨fun _ => ?_, fun _ => by m7_lets; exact hJpush () m1 ⟨s1, hinv1, hm1⟩⟩
  have hov_lvl : (ov.setWidth 64).toNat < s1.core.lvl.length := by
    rw [m7b_zext32, hlen1.core_ok.lvl_len]
    exact Nat.lt_of_lt_of_le hov_lt (by rw [hcv1]; exact hcv_le)
  m7_ld (FullArenaTactics.c0_load_full_lvl (s := s1) hov_lvl hm1)
  m7_lets; m7_jnz
  refine ⟨fun _ => ?_, fun _ => by m7_lets; exact hJpush () m1 ⟨s1, hinv1, hm1⟩⟩
  have hov_mrk : (ov.setWidth 64).toNat < s1.core.mrk.length := by
    rw [m7b_zext32, hlen1.core_ok.mrk_len]
    exact Nat.lt_of_lt_of_le hov_lt (by rw [hcv1]; exact hcv_le)
  m7_ld (FullArenaTactics.c0_load_full_mrk (s := s1) hov_mrk hm1)
  m7_lets; m7_jnz
  refine ⟨fun hmrk_eq => ?_, fun _ => by m7_lets; exact hJpush () m1 ⟨s1, hinv1, hm1⟩⟩
  have hmrk0 : s1.core.mrk[ov.toNat]?.getD 0#8 = 0#8 := by
    have hmrk_lt : ov.toNat < s1.core.mrk.length := by
      rw [hlen1.core_ok.mrk_len]; exact Nat.lt_of_lt_of_le hov_lt (by rw [hcv1]; exact hcv_le)
    rw [List.getElem?_eq_getElem hmrk_lt, Option.getD_some]
    exact m7b_bv8_zero hmrk_eq
  refine wp_join_group (ts := [])
    (fun _ m2 => ∃ s2 : FullState, BumpReasonsInv c s s2 ∧ (FullMem c s2 ⋆ R) m2)
    (fun _ _ m2 ⟨s2, hinv2, hm2⟩ => by m7_lets; exact hJpush () m2 ⟨s2, hinv2, hm2⟩)
    (fun Js hJs => ?_)
  m7_ld (FullArenaTactics.load_full_min_clr_len (s := s1) hm1)
  m7_lets; m7_jnz
  refine ⟨fun hmcl_ult => ?_, fun _ => by m7_lets; exact hJs () m1 ⟨s1, hinv1, hm1⟩⟩
  have hmcl_lt : s1.core.min_clr_len < s1.core.cur_vars := by
    have h1 := m7b_ult64 hmcl_ult
    rw [m7b_ofNat64 (by have := hlen1.core_ok.min_clr_len_le; omega), hcvv] at h1
    rwa [hcv1]
  m7_st m1a, hm1a := FullArenaTactics.c0_store_full_mrk (s := s1)
    ((1 : BitVec 32).setWidth 8) hov_mrk hm1
  rw [show (1 : BitVec 32).setWidth 8 = 1#8 from rfl, m7b_zext32] at hm1a
  let s1a : FullState :=
    { s1 with core := { s1.core with mrk := s1.core.mrk.set ov.toNat 1#8 } }
  have hm1a' : (FullMem c s1a ⋆ R) m1a := hm1a
  m7_ld (FullArenaTactics.load_full_min_clr_len (s := s1a) hm1a')
  have hmcl_ws : (BitVec.ofNat 64 s1a.core.min_clr_len).toNat <
      s1a.scratch.work_stk1.length := by
    dsimp only [s1a]
    rw [m7b_ofNat64 (by have := hlen1.core_ok.min_clr_len_le; omega),
      hlen1.scratch_ok.work_stk1_len]
    rw [hcv1] at hmcl_lt; omega
  m7_st m1b, hm1b := FullArenaTactics.c0_store_full_work_stk1 (s := s1a) ov hmcl_ws hm1a'
  rw [show s1a.core.min_clr_len = s1.core.min_clr_len from rfl,
    m7b_ofNat64 (by have := hlen1.core_ok.min_clr_len_le; omega)] at hm1b
  let s1b : FullState :=
    { s1a with scratch :=
      { s1a.scratch with work_stk1 := s1.scratch.work_stk1.set s1.core.min_clr_len ov } }
  have hm1b' : (FullMem c s1b ⋆ R) m1b := hm1b
  m7_ld (FullArenaTactics.load_full_min_clr_len (s := s1b) hm1b')
  m7_lets
  m7_st m1c, hm1c := FullArenaTactics.c0_store_full_min_clr_len (s := s1b)
    (BitVec.ofNat 64 s1.core.min_clr_len + 1#64) hm1b'
  have hpush := bumpReasons_push_mem ov hinv1 hov_lt hmrk0 hmcl_lt hm1c
  m7_lets; exact hJs () m1c hpush

private theorem bumpReasons_rollback_wp {Γ : Env} {Q : Post []} {X : XPost}
    {c : FullCfg} {s s1 : FullState} {R : Mem 64 → Prop} {m1 : Mem 64}
    {cvv limv : Val i64} {Jlim : Cont []} {h1 h2 h3 : Ty.bool = i64.mask}
    (hcvv : cvv.toNat = s.core.cur_vars) (hmcl_cv : s.core.min_clr_len ≤ s.core.cur_vars)
    (hinv1 : BumpReasonsInv c s s1) (hm1 : (FullMem c s1 ⋆ R) m1)
    (hJlim : ∀ (xs : Tup Val []) (m : Mem 64),
      (∃ s2 : FullState, BumpReasonsInv c s s2 ∧ (FullMem c s2 ⋆ R) m) → Jlim xs m) :
    wp Γ Q X
      (Expr.let_ (Op.mk (.add i64) (.var c.hdr, .imm 272, ())) fun p =>
      Expr.load i64 (.var p.fst) fun ld =>
      Expr.let_ (Op.mk (.cmp .ugt i64 .bool h1) (.var ld, .var limv, ())) fun p =>
      Expr.jnz (.var p.fst)
        (Expr.group
          (fun (Jrb : Tup Cont [[]]) =>
            Blocks.cons
              (fun (_ : Tup Val []) =>
                Expr.let_ (Op.mk (.add i64) (.var c.hdr, .imm 272, ())) fun p =>
                Expr.load i64 (.var p.fst) fun ld =>
                Expr.let_ (Op.mk (.cmp .ugt i64 .bool h2)
                  (.var ld, .var (BitVec.ofNat 64 s.core.min_clr_len), ())) fun p =>
                Expr.jnz (.var p.fst)
                  (Expr.let_ (Op.mk (.add i64) (.var c.hdr, .imm 272, ())) fun p =>
                  Expr.load i64 (.var p.fst) fun ld =>
                  Expr.let_ (Op.mk (.sub i64) (.var ld, .imm 1, ())) fun p =>
                  Expr.let_ (Op.mk (.add i64) (.var c.hdr, .imm 272, ())) fun p_1 =>
                  Expr.store (.var p.fst) (.var p_1.fst)
                    (Expr.let_ (Op.mk (.add i64) (.var c.hdr, .imm 272, ())) fun p =>
                    Expr.load i64 (.var p.fst) fun ld =>
                    Expr.let_ (Op.mk (.mul i64) (.var ld, .imm 4, ())) fun p =>
                    Expr.let_ (Op.mk (.add i64) (.var c.pWorkStk1, .var p.fst, ())) fun p =>
                    Expr.load i32 (.var p.fst) fun rv =>
                    Expr.group
                      (fun (_ : Tup Cont [[]]) =>
                        Blocks.cons (fun (_ : Tup Val []) => Expr.jump Jrb.fst ()) Blocks.nil)
                      fun JrbStep =>
                      Expr.let_ (Op.mk (.zext 32 64) (.var rv, ())) fun p =>
                      Expr.let_ (Op.mk (.cmp .ult i64 .bool h3) (.var p.fst, .var cvv, ())) fun p =>
                      Expr.jnz (.var p.fst)
                        (Expr.let_ (Op.mk (.zext 32 64) (.var rv, ())) fun p =>
                        Expr.let_ (Op.mk (.add i64) (.var c.pMark, .var p.fst, ())) fun p =>
                        Expr.let_ (Op.mk (.trunc 32 8) (.imm 0, ())) fun p_1 =>
                        Expr.store (.var p_1.fst) (.var p.fst) (Expr.jump JrbStep.fst ()))
                        (Expr.jump JrbStep.fst ())))
                  (Expr.jump Jlim ()))
              Blocks.nil)
          fun Jrb => Expr.jump Jrb.fst ())
        (Expr.jump Jlim ()))
      m1 := by
  have hmax : c.max_vars < 2 * dimacsBound := c.hmaxv
  unfold dimacsBound at hmax
  m7_ld (FullArenaTactics.load_full_min_clr_len (s := s1) hm1)
  m7_lets; m7_jnz
  refine ⟨fun _ => ?_, fun _ => by m7_lets; exact hJlim () m1 ⟨s1, hinv1, hm1⟩⟩
  refine wp_loop_inv (ts := [])
    (fun _ m3 => ∃ s3 : FullState, BumpReasonsInv c s s3 ∧ (FullMem c s3 ⋆ R) m3)
    (fun _ m3 => ((loadVal m3 i64 (c.hdr + 272)).getD 0#64).toNat) ?_ ?_
  · intro Jrb hJrb
    m7_lets; exact hJrb () m1 ⟨s1, hinv1, hm1⟩
  · rintro Jrb ⟨⟩ m3 ⟨s3, hinv3, hm3⟩ hJrb
    rw [Blocks.get_here]
    have hinv3_pk := hinv3; have hlen3 := hinv3.1
    have hmcl3_le := hlen3.core_ok.min_clr_len_le
    have hmcl3_64 : s3.core.min_clr_len < 2 ^ 64 := by omega
    have hmrl3 := hlen3.core_ok.mrk_len; have hwsl3 := hlen3.scratch_ok.work_stk1_len
    have hcv3 := (bumpReasons_fields hinv3.2.1).1
    have hload3 : (loadVal m3 i64 (c.hdr + 272)).getD 0#64 =
        BitVec.ofNat 64 s3.core.min_clr_len := by
      rw [FullArenaTactics.load_full_min_clr_len hm3]; rfl
    m7_ld (FullArenaTactics.load_full_min_clr_len (s := s3) hm3)
    m7_lets; m7_jnz
    refine ⟨fun hsav_b => ?_, fun _ => by m7_lets; exact hJlim () m3 ⟨s3, hinv3_pk, hm3⟩⟩
    have hcv_le0 : s.core.cur_vars ≤ c.max_vars := by
      have h1 := hinv1.1.core_ok.cur_vars_le
      rwa [(bumpReasons_fields hinv1.2.1).1] at h1
    have hsav_lt : s.core.min_clr_len < s3.core.min_clr_len := by
      have h1 := m7b_ult64 hsav_b
      rwa [m7b_ofNat64 (by omega), m7b_ofNat64 hmcl3_64] at h1
    have hpos3 : 0 < s3.core.min_clr_len := by omega
    have hm1_sub : (BitVec.ofNat 64 s3.core.min_clr_len - 1#64).toNat =
        s3.core.min_clr_len - 1 := by bv_omega
    obtain ⟨hrv_lt, hpop⟩ := bumpReasons_pop hinv3_pk hpos3
    m7_ld (FullArenaTactics.load_full_min_clr_len (s := s3) hm3)
    m7_st m3a, hm3a := FullArenaTactics.c0_store_full_min_clr_len (s := s3)
      (BitVec.ofNat 64 s3.core.min_clr_len - 1#64) hm3
    rw [hm1_sub] at hm3a
    let s3a : FullState :=
      { s3 with core := { s3.core with min_clr_len := s3.core.min_clr_len - 1 } }
    have hm3a' : (FullMem c s3a ⋆ R) m3a := hm3a
    have hws_idx : (BitVec.ofNat 64 (s3.core.min_clr_len - 1)).toNat <
        s3a.scratch.work_stk1.length := by
      rw [m7b_ofNat64 (n := s3.core.min_clr_len - 1) (by omega)]
      dsimp only [s3a]; rw [hwsl3]; omega
    m7_ld (FullArenaTactics.load_full_min_clr_len (s := s3a) hm3a')
    m7_ld (FullArenaTactics.c0_load_full_work_stk1 (s := s3a) hws_idx hm3a')
    m7_lets
    refine wp_join_group (ts := [])
      (fun _ m4 => ∃ s4 : FullState, BumpReasonsInv c s s4 ∧
        ((loadVal m4 i64 (c.hdr + 272)).getD 0#64).toNat <
          ((loadVal m3 i64 (c.hdr + 272)).getD 0#64).toNat ∧
        (FullMem c s4 ⋆ R) m4)
      (fun _ _ m4 ⟨s4, hinv4, hdec, hm4⟩ => by m7_lets; exact hJrb () m4 hdec ⟨s4, hinv4, hm4⟩)
      (fun JrbStep hJrbStep => ?_)
    let rv32 := s3a.scratch.work_stk1[(BitVec.ofNat 64 (s3.core.min_clr_len - 1)).toNat]'hws_idx
    have hrv_lt' : rv32.toNat < s3.core.cur_vars := by
      dsimp only [rv32, s3a]
      simpa only [m7b_ofNat64 (n := s3.core.min_clr_len - 1) (by omega)] using hrv_lt
    have hmrk_bd : (rv32.setWidth 64).toNat < s3a.core.mrk.length := by
      have hcv3_le := hlen3.core_ok.cur_vars_le
      rw [m7b_zext32]; dsimp only [s3a]; rw [hmrl3]; rw [hcv3] at hrv_lt' hcv3_le; omega
    m7_lets; m7_jnz; refine ⟨fun _ => ?_, fun hrv_no => ?_⟩
    · m7_st m4, hm4 := FullArenaTactics.c0_store_full_mrk (s := s3a)
        ((0 : BitVec 32).setWidth 8) hmrk_bd hm3a'
      rw [show (0 : BitVec 32).setWidth 8 = 0#8 from rfl, m7b_zext32] at hm4
      let s4 : FullState :=
        { core := { s3.core with
            mrk := s3.core.mrk.set rv32.toNat 0#8
            min_clr_len := s3.core.min_clr_len - 1 }
          scratch := s3.scratch }
      have hm4' : (FullMem c s4 ⋆ R) m4 := hm4
      have hpop' : BumpReasonsInv c s s4 := by
        dsimp only [s4, rv32, s3a]
        simpa only [m7b_ofNat64 (n := s3.core.min_clr_len - 1) (by omega)] using hpop
      have hdec : ((loadVal m4 i64 (c.hdr + 272)).getD 0#64).toNat <
          ((loadVal m3 i64 (c.hdr + 272)).getD 0#64).toNat := by
        rw [FullArenaTactics.load_full_min_clr_len hm4', hload3]
        dsimp only [Option.getD_some]
        rw [m7b_ofNat64 (n := s4.core.min_clr_len) (by dsimp [s4]; omega), m7b_ofNat64 hmcl3_64]
        dsimp [s4]; omega
      m7_lets; exact hJrbStep () m4 ⟨_, hpop', hdec, hm4'⟩
    · exfalso
      have hnot := m7b_not_ult64 hrv_no
      dsimp only [s3a] at hnot
      rw [m7b_zext32, hcvv, ← hcv3] at hnot
      simp only [m7b_ofNat64 (n := s3.core.min_clr_len - 1) (by omega)] at hnot
      omega

/-- WP theorem for `full_bump_reasons_m7` certifying `m7BumpReasonsSpec`. -/
theorem full_bump_reasons_m7_wp (Γ : Env) :
    ∀ a m Q X, m7BumpReasonsSpec a m Q X → Func.wp Γ full_bump_reasons_m7_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hcov0, hm, hQ⟩
  have hmax : c.max_vars < 2 * dimacsBound := c.hmaxv
  have harena_cap : c.arena_cap < 2 * dimacsBound := c.harena
  unfold dimacsBound at hmax harena_cap
  have hal_lt0 : s.core.arena_len < 2 ^ 64 := by
    have := hlen.core_ok.arena_len_le; omega
  have hcv_le := hlen.core_ok.cur_vars_le
  have htl_le := hlen.core_ok.tmp_len_le
  have hmcl_cv := hcov0.1
  unfold Func.wp full_bump_reasons_m7_body; dsimp only [full_bump_reasons_m7_body]
  m7_ld (FullArenaTactics.load_full_cur_vars hm)
  m7_lets
  refine wp_join_group (ts := [i64]) (fun (cvv, ()) m1 => m = m1 ∧ cvv.toNat = s.core.cur_vars)
    ?_ ?_
  · rintro _ ⟨cvv, ⟨⟩⟩ m1 ⟨hm1, hcvv⟩
    rcases hm1 with rfl
    m7_ld (FullArenaTactics.load_full_tmp_len hm)
    m7_lets
    refine wp_join_group (ts := [i64])
      (fun (tlv, ()) m1 => m = m1 ∧ tlv.toNat = min s.core.tmp_len s.core.cur_vars) ?_ ?_
    · rintro _ ⟨tlv, ⟨⟩⟩ m1 ⟨hm1, htlv⟩
      rcases hm1 with rfl
      m7_ld (FullArenaTactics.load_full_min_clr_len hm)
      m7_lets; m7_jnz
      refine ⟨fun _ => by
          m7_lets
          exact hQ s.core.mrk s.core.min_clr_len s.scratch.work_stk1 m hlen hcov0 hm,
        fun _ => ?_⟩
      m7_lets; m7_jnz
      refine ⟨fun _ => by
          m7_lets
          exact hQ s.core.mrk s.core.min_clr_len s.scratch.work_stk1 m hlen hcov0 hm,
        fun _ => ?_⟩
      m7_lets
      refine wp_join_group (ts := [i64]) (fun (_, ()) m1 => m = m1) ?_ ?_
      · rintro _ ⟨limv, ⟨⟩⟩ m1 hm1
        rcases hm1 with rfl
        m7_ld (FullArenaTactics.load_full_arena_len hm)
        m7_ld (FullArenaTactics.load_full_tmp_lits_ptr hm)
        m7_ld (FullArenaTactics.load_full_reason_ptr hm)
        m7_ld (FullArenaTactics.load_full_level_ptr hm)
        m7_ld (FullArenaTactics.load_full_mark_ptr hm)
        m7_ld (FullArenaTactics.load_full_work_stk1_ptr hm)
        m7_ld (FullArenaTactics.load_full_arena_ptr hm)
        m7_lets
        refine wp_loop_inv (ts := [i64])
          (fun (i, ()) m1 => i.toNat ≤ tlv.toNat ∧
            ∃ s1 : FullState, BumpReasonsInv c s s1 ∧ (FullMem c s1 ⋆ R) m1)
          (fun (i, ()) _ => tlv.toNat - i.toNat) ?_ ?_
        · intro Jloop hLoop
          m7_lets
          exact hLoop (0#64, ()) m ⟨by simp, s, bumpReasonsInv_init hlen hcov0, hm⟩
        · rintro Jloop ⟨i, ⟨⟩⟩ m1 ⟨hi_le, s1, hinv1, hm1⟩ hLoop
          rw [Blocks.get_here]
          have hinv1_pk := hinv1
          rcases bumpReasons_fields hinv1.2.1 with
            ⟨hcv1, htl1, hal1, htmp1, hrsns1, hlvl1, har1⟩
          have hlen1 := hinv1.1
          have htll1 := hlen1.core_ok.tmp_len_arr; have hrsnl1 := hlen1.core_ok.rsns_len
          have harl1 := hlen1.core_ok.arena_len_arr; have hale1 := hlen1.core_ok.arena_len_le
          m7_lets; m7_jnz
          refine ⟨fun hilt => ?_, fun _ => ?_⟩
          · clear hQ hm hcov0 hlen
            have hi_lt : i.toNat < tlv.toNat := m7b_ult64 hilt
            have hi_tmp : i.toNat < s1.core.tmp.length := by
              rw [htll1]
              exact Nat.lt_of_lt_of_le hi_lt (Nat.le_trans (by rw [htlv]; exact Nat.min_le_left _ _)
                htl_le)
            m7_ld (FullArenaTactics.c0_load_full_tmp (s := s1) hi_tmp hm1)
            m7_lets
            refine wp_join_group (ts := [])
              (fun _ m2 => ∃ s2 : FullState, BumpReasonsInv c s s2 ∧ (FullMem c s2 ⋆ R) m2)
              (fun Jstep _ m2 ⟨s2, hinv2, hm2⟩ => by
                m7_lets
                exact hLoop (i + 1#64, ()) m2 (by dsimp only; bv_omega)
                  ⟨by bv_omega, s2, hinv2, hm2⟩)
              (fun Jstep hJstep => ?_)
            let uv32 := s1.core.tmp[i.toNat]'hi_tmp >>> (1 : Nat)
            m7_lets; m7_jnz
            refine ⟨fun huv_ult => ?_, fun _ => by m7_lets; exact hJstep () m1 ⟨s1, hinv1_pk, hm1⟩⟩
            have huv_lt : uv32.toNat < s1.core.cur_vars := by
              have h1 := m7b_ult64 huv_ult
              rw [m7b_zext32, hcvv] at h1; rwa [hcv1]
            have huv_rsn : (uv32.setWidth 64).toNat < s1.core.rsns.length := by
              rw [m7b_zext32, hrsnl1]; exact Nat.lt_of_lt_of_le huv_lt (by rw [hcv1]; exact hcv_le)
            m7_ld (FullArenaTactics.c0_load_full_rsns (s := s1) huv_rsn hm1)
            m7_lets
            refine wp_join_group (ts := [])
              (fun _ m2 => ∃ s2 : FullState, BumpReasonsInv c s s2 ∧ (FullMem c s2 ⋆ R) m2)
              (fun _ _ m2 ⟨s2, hinv2, hm2⟩ => by m7_lets; exact hJstep () m2 ⟨s2, hinv2, hm2⟩)
              (fun Jrsn hJrsn => ?_)
            m7_lets; m7_jnz
            refine ⟨fun _ => ?_, fun _ => by m7_lets; exact hJrsn () m1 ⟨s1, hinv1_pk, hm1⟩⟩
            refine wp_join_group (ts := [])
              (fun _ m2 => ∃ s2 : FullState, BumpReasonsInv c s s2 ∧ (FullMem c s2 ⋆ R) m2)
              (fun _ _ m2 ⟨s2, hinv2, hm2⟩ => by m7_lets; exact hJrsn () m2 ⟨s2, hinv2, hm2⟩)
              (fun Jbin hJbin => ?_)
            m7_lets; m7_jnz
            refine ⟨fun _ => ?_, fun _ => ?_⟩
            · m7_lets
              refine wp_join_group (ts := [])
                (fun _ m2 => ∃ s2 : FullState, BumpReasonsInv c s s2 ∧ (FullMem c s2 ⋆ R) m2)
                (fun _ _ m2 ⟨s2, hinv2, hm2⟩ => by m7_lets; exact hJbin () m2 ⟨s2, hinv2, hm2⟩)
                (fun Jpush hJpush => ?_)
              let olit := (s1.core.rsns[(uv32.setWidth 64).toNat]'huv_rsn) &&& 0x7FFFFFFF#32
              m7_lets
              exact bumpReasons_push_wp (olit >>> (1 : Nat)) uv32 hcvv hinv1_pk hm1 hJpush
            · refine wp_join_group (ts := [])
                (fun _ m2 => ∃ s2 : FullState, BumpReasonsInv c s s2 ∧ (FullMem c s2 ⋆ R) m2)
                (fun _ _ m2 ⟨s2, hinv2, hm2⟩ => by m7_lets; exact hJbin () m2 ⟨s2, hinv2, hm2⟩)
                (fun Jar hJar => ?_)
              let rsn32 := s1.core.rsns[(uv32.setWidth 64).toNat]'huv_rsn
              m7_lets; m7_jnz
              refine ⟨fun h3 => ?_, fun _ => by m7_lets; exact hJar () m1 ⟨s1, hinv1_pk, hm1⟩⟩
              have h3_le : 3 ≤ s1.core.arena_len := by
                have h1 := m7b_ule64 h3
                rw [m7b_ofNat64 hal_lt0] at h1; rw [hal1]; exact h1
              m7_lets; m7_jnz
              refine ⟨fun hrsn3_le => ?_, fun _ => by m7_lets; exact hJar () m1 ⟨s1, hinv1_pk, hm1⟩⟩
              have hrsn3 : rsn32.toNat + 3 ≤ s1.core.arena_len := by
                have h1 := m7b_ule64 hrsn3_le
                have hal_lt : s1.core.arena_len < 2 ^ 64 := by rw [hal1]; exact hal_lt0
                have hz := m7b_zext32 rsn32; have := rsn32.isLt
                rw [hal1]; dsimp only [rsn32]; bv_omega
              have hrsn2_lt : (rsn32.setWidth 64 + 2#64).toNat < s1.core.arena.length := by
                rw [harl1]
                have hadd2 : (rsn32.setWidth 64 + 2#64).toNat = rsn32.toNat + 2 := by
                  have := rsn32.isLt
                  rw [BitVec.toNat_add, m7b_zext32, show (2#64).toNat = 2 from rfl,
                    Nat.mod_eq_of_lt (by omega)]
                rw [hadd2]; omega
              m7_ld (FullArenaTactics.c0_load_full_arena (s := s1) hrsn2_lt hm1)
              m7_lets
              refine wp_join_group (ts := [])
                (fun _ m2 => ∃ s2 : FullState, BumpReasonsInv c s s2 ∧ (FullMem c s2 ⋆ R) m2)
                (fun _ _ m2 ⟨s2, hinv2, hm2⟩ => by m7_lets; exact hJar () m2 ⟨s2, hinv2, hm2⟩)
                (fun Jsz hJsz => ?_)
              let sz32 := s1.core.arena[(rsn32.setWidth 64 + 2#64).toNat]'hrsn2_lt
              m7_lets; m7_jnz
              refine ⟨fun _ => ?_, fun _ => by m7_lets; exact hJsz () m1 ⟨s1, hinv1_pk, hm1⟩⟩
              m7_lets; m7_jnz
              refine ⟨fun hrsn_sz_le => ?_,
                fun _ => by m7_lets; exact hJsz () m1 ⟨s1, hinv1_pk, hm1⟩⟩
              have hrsn_sz : rsn32.toNat + 3 + sz32.toNat ≤ s1.core.arena_len := by
                have h1 := m7b_ule64 hrsn_sz_le
                have hadd3 : (rsn32.setWidth 64 + 3#64).toNat = rsn32.toNat + 3 := by
                  have := rsn32.isLt
                  rw [BitVec.toNat_add, m7b_zext32, show (3#64).toNat = 3 from rfl,
                    Nat.mod_eq_of_lt (by omega)]
                dsimp only [rsn32, sz32] at hrsn3 hadd3 h1 ⊢
                rw [hal1] at hrsn3 ⊢
                have := (s1.core.arena[((s1.core.rsns[(uv32.setWidth 64).toNat]'huv_rsn).setWidth
                  64 + 2#64).toNat]'hrsn2_lt).isLt
                have := (s1.core.rsns[(uv32.setWidth 64).toNat]'huv_rsn).isLt
                bv_omega
              refine wp_loop_inv (ts := [i64])
                (fun (k, ()) m2 => k.toNat ≤ sz32.toNat ∧
                  ∃ s2 : FullState, BumpReasonsInv c s s2 ∧ (FullMem c s2 ⋆ R) m2)
                (fun (k, ()) _ => sz32.toNat - k.toNat) ?_ ?_
              · intro Jk hJk
                m7_lets; exact hJk (0#64, ()) m1 ⟨by simp, s1, hinv1_pk, hm1⟩
              · rintro Jk ⟨k, ⟨⟩⟩ m2 ⟨hk_le, s2, hinv2, hm2⟩ hJk
                clear hLoop hi_le hJstep hJrsn hJbin hJar
                rw [Blocks.get_here]
                have hinv2_pk := hinv2
                rcases bumpReasons_fields hinv2.2.1 with ⟨_, _, hal2, _, _, _, _⟩
                have hlen2 := hinv2.1
                m7_lets; m7_jnz
                refine ⟨fun hk_ult => ?_, fun _ => by m7_lets; exact hJsz () m2 ⟨s2, hinv2_pk, hm2⟩⟩
                have hk_lt : k.toNat < sz32.toNat := by
                  have h1 := m7b_ult64 hk_ult; rwa [m7b_zext32] at h1
                have hk_ar : (rsn32.setWidth 64 + 3#64 + k).toNat < s2.core.arena.length := by
                  have haddk :
                      (rsn32.setWidth 64 + 3#64 + k).toNat = rsn32.toNat + 3 + k.toNat := by
                    have := rsn32.isLt; have := sz32.isLt
                    rw [BitVec.toNat_add, BitVec.toNat_add, m7b_zext32,
                      show (3#64).toNat = 3 from rfl, Nat.mod_eq_of_lt (by omega),
                      Nat.mod_eq_of_lt (by omega)]
                  rw [hlen2.core_ok.arena_len_arr, haddk]
                  have : s2.core.arena_len = s1.core.arena_len := by rw [hal2, hal1]
                  omega
                m7_ld (FullArenaTactics.c0_load_full_arena (s := s2) hk_ar hm2)
                m7_lets
                refine wp_join_group (ts := [])
                  (fun _ m3 => ∃ s3 : FullState, BumpReasonsInv c s s3 ∧ (FullMem c s3 ⋆ R) m3)
                  (fun _ _ m3 ⟨s3, hinv3, hm3⟩ => by
                    m7_lets
                    exact hJk (k + 1#64, ()) m3 (by dsimp only; have := sz32.isLt; bv_omega)
                      ⟨by have := sz32.isLt; bv_omega, s3, hinv3, hm3⟩)
                  (fun Jpush hJpush => ?_)
                m7_lets
                exact bumpReasons_push_wp
                  (s2.core.arena[(rsn32.setWidth 64 + 3#64 + k).toNat]'hk_ar >>> (1 : Nat))
                  uv32 hcvv hinv2_pk hm2 hJpush
          · clear hinv1 hLoop hi_le
            refine wp_join_group (ts := [])
              (fun _ m2 => ∃ s2 : FullState, BumpReasonsInv c s s2 ∧ (FullMem c s2 ⋆ R) m2) ?_ ?_
            · rintro _ ⟨⟩ m2 ⟨s2, hinv2, hm2⟩
              rcases hinv2 with ⟨hlen2, hbr2, hcov2⟩
              rcases hbr2 with ⟨mrk2, mcl2, ws2, rfl⟩
              m7_lets; exact hQ mrk2 mcl2 ws2 m2 hlen2 hcov2 hm2
            · intro Jlim hJlim
              exact bumpReasons_rollback_wp hcvv hmcl_cv hinv1_pk hm1 hJlim
      · intro _ hJlim
        m7_lets; m7_jnz
        refine ⟨fun _ => by m7_lets; exact hJlim _ m rfl, fun _ => by m7_lets; exact hJlim _ m rfl⟩
    · intro _ hJtl
      m7_lets; m7_jnz
      refine ⟨fun hlt => ?_, fun hle => ?_⟩
      · have h1 := m7b_ult64 hlt
        rw [hcvv, m7b_ofNat64 (by omega)] at h1
        m7_lets; exact hJtl (cvv, ()) m ⟨rfl, by rw [hcvv, Nat.min_eq_right (Nat.le_of_lt h1)]⟩
      · have h1 := m7b_not_ult64 hle
        rw [hcvv, m7b_ofNat64 (by omega)] at h1
        m7_lets
        exact hJtl (BitVec.ofNat 64 s.core.tmp_len, ()) m
          ⟨rfl, by rw [m7b_ofNat64 (by omega), Nat.min_eq_left h1]⟩
  · intro _ hJcv
    m7_ld (FullArenaTactics.load_full_max_vars hm)
    m7_lets; m7_jnz
    refine ⟨fun hgt => ?_, fun _ => by
      m7_lets; exact hJcv (BitVec.ofNat 64 s.core.cur_vars, ()) m ⟨rfl, m7b_ofNat64 (by omega)⟩⟩
    exfalso
    have h1 := m7b_ult64 hgt
    rw [m7b_ofNat64 (by omega), m7b_ofNat64 (by omega)] at h1
    omega

private def BumpAnaLoopInv (c : FullCfg) (s0 s2 : FullState) : Prop :=
  s2.LengthsOk c ∧ s2.core = s0.core ∧ FullExtScratchPres s0 s2 ∧
  s2.scratch.work_stk1 = s0.scratch.work_stk1 ∧ s2.scratch.work_stk2 = s0.scratch.work_stk2

private theorem bumpAnaLoopInv_init {c : FullCfg} {s0 : FullState}
    (hlen : s0.LengthsOk c) : BumpAnaLoopInv c s0 s0 :=
  ⟨hlen, rfl, ⟨rfl, rfl⟩, rfl, rfl⟩

private theorem bumpAnaLoopInv_step {c : FullCfg} {s0 s2 s3 : FullState}
    (hinv : BumpAnaLoopInv c s0 s2) (hlen3 : s3.LengthsOk c)
    (hcore : PreservesCoreSlice (fullSafetySlice c).coreProj s2 s3)
    (hpr : FullProbeScratchPres s2 s3) : BumpAnaLoopInv c s0 s3 :=
  ⟨hlen3, Eq.trans hcore hinv.2.1,
    ⟨hpr.1.1.trans hinv.2.2.1.1, hpr.1.2.trans hinv.2.2.1.2⟩,
    hpr.2.1.trans hinv.2.2.2.1, hpr.2.2.1.trans hinv.2.2.2.2⟩

private theorem fullAnaMarksCov_of_eq {c : FullCfg} {s1 s2 : FullState}
    (hcov : FullAnaMarksCov c s1) (hcore : s2.core = s1.core)
    (hws1 : s2.scratch.work_stk1 = s1.scratch.work_stk1) : FullAnaMarksCov c s2 := by
  unfold FullAnaMarksCov at hcov ⊢; rwa [hcore, hws1]

private theorem full_state_repack {s s_fin : FullState} {mrk1 : List (BitVec 8)} {mcl1 : Nat}
    (hcore : s_fin.core = { s.core with mrk := mrk1, min_clr_len := mcl1 }) :
    s_fin = { s with core := { s.core with mrk := mrk1, min_clr_len := mcl1 },
                     scratch := s_fin.scratch } := by
  cases s_fin; dsimp only at hcore ⊢; rw [hcore]

private theorem bump_active_loop_wp {Γ : Env} {Q : Post []} {X : XPost}
    {c : FullCfg} {s0 : FullState} {R : Mem 64 → Prop} {m0 : Mem 64}
    {cnt cvv : Val i64} (fnName : Sym) (exitK : Expr Val Cont [])
    {h1 h2 : Ty.bool = i64.mask} {h3 : Ty.bool = i32.mask}
    (hFn : ∀ a m Q' X', fullSafetyVarVoidSpec a m Q' X' → Γ fnName [i64, i32] [] a m Q' X')
    (hcnt_ws : cnt.toNat ≤ 2 * c.max_vars) (hcvv : cvv = BitVec.ofNat 64 s0.core.cur_vars)
    (hcv0_le : s0.core.cur_vars ≤ c.max_vars) (hlen0 : s0.LengthsOk c)
    (hm0 : (FullMem c s0 ⋆ R) m0)
    (hExit : ∀ s3 m3, BumpAnaLoopInv c s0 s3 → (FullMem c s3 ⋆ R) m3 → wp Γ Q X exitK m3) :
    wp Γ Q X
      (Expr.group
        (fun (Js_1 : Tup Cont [[i64]]) =>
          Blocks.cons
            (fun (p_5 : Tup Val [i64]) =>
              Expr.let_ (Op.mk (.cmp .ult i64 .bool h1) (.var p_5.fst, .var cnt, ())) fun p =>
              Expr.jnz (.var p.fst)
                (Expr.let_ (Op.mk (.mul i64) (.var p_5.fst, .imm 4, ())) fun p_6 =>
                Expr.let_ (Op.mk (.add i64) (.var c.pWorkStk1, .var p_6.fst, ())) fun p_6 =>
                Expr.load i32 (.var p_6.fst) fun bv =>
                Expr.group
                  (fun (_ : Tup Cont [[]]) =>
                    Blocks.cons
                      (fun (_ : Tup Val []) =>
                        Expr.let_ (Op.mk (.add i64) (.var p_5.fst, .imm 1, ())) fun p_7 =>
                        Expr.jump Js_1.fst (.var p_7.fst, ()))
                      Blocks.nil)
                  fun Js_2 =>
                  Expr.let_ (Op.mk (.zext 32 64) (.var bv, ())) fun p_6 =>
                  Expr.let_ (Op.mk (.cmp .ult i64 .bool h2) (.var p_6.fst, .var cvv, ())) fun p_6 =>
                  Expr.jnz (.var p_6.fst)
                    (Expr.let_ (Op.mk (.zext 32 64) (.var bv, ())) fun p_6 =>
                    Expr.let_ (Op.mk (.mul i64) (.var p_6.fst, .imm 4, ())) fun p_6 =>
                    Expr.let_ (Op.mk (.add i64) (.var c.pFlags, .var p_6.fst, ())) fun p_6 =>
                    Expr.load i32 (.var p_6.fst) fun ld =>
                    Expr.let_ (Op.mk (.and i32) (.var ld, .imm 1, ())) fun p_6 =>
                    Expr.let_ (Op.mk (.cmp .ne i32 .bool h3) (.var p_6.fst, .imm 0, ())) fun p_6 =>
                    Expr.jnz (.var p_6.fst)
                      (Expr.call fnName (as := [i64, i32]) (bs := [])
                        (Arg.var c.hdr, Arg.var bv, ()) fun _ => Expr.jump Js_2.fst ())
                      (Expr.jump Js_2.fst ()))
                    (Expr.jump Js_2.fst ()))
                exitK)
            Blocks.nil)
        fun Js => Expr.jump Js.fst (.imm 0, ()))
      m0 := by
  have hmax : c.max_vars < 2 * dimacsBound := c.hmaxv
  unfold dimacsBound at hmax
  refine wp_loop_inv (ts := [i64])
    (fun (iv, ()) m3 => iv.toNat ≤ cnt.toNat ∧
      ∃ s3 : FullState, BumpAnaLoopInv c s0 s3 ∧ (FullMem c s3 ⋆ R) m3)
    (fun (iv, ()) _ => cnt.toNat - iv.toNat) ?_ ?_
  · intro Jiv hJiv
    m7_lets; exact hJiv (0#64, ()) m0 ⟨by simp, s0, bumpAnaLoopInv_init hlen0, hm0⟩
  · rintro Jiv ⟨iv, ⟨⟩⟩ m3 ⟨hiv_le, s3, hinv3, hm3⟩ hJiv
    clear hm0 hlen0
    rw [Blocks.get_here]
    have hinv3_pk := hinv3
    rcases hinv3 with ⟨hlen3, hcore3, _hext3, _hws3_1, _hws3_2⟩
    m7_lets
    refine wp_jnz_of (fun hiv_ult => ?_) (fun _ => ?_)
    · have hiv_lt : iv.toNat < cnt.toNat := m7b_ult64 hiv_ult
      have hiv_ws : iv.toNat < s3.scratch.work_stk1.length := by
        rw [hlen3.scratch_ok.work_stk1_len]; omega
      m7_ld (FullArenaTactics.c0_load_full_work_stk1 (s := s3) hiv_ws hm3)
      m7_lets
      refine wp_join_group (ts := [])
        (fun _ m4 => ∃ s4 : FullState, BumpAnaLoopInv c s0 s4 ∧ (FullMem c s4 ⋆ R) m4)
        (fun _ _ m4 ⟨s4, hinv4, hm4⟩ => by
          m7_lets
          exact hJiv (iv + 1#64, ()) m4 (by dsimp only; bv_omega) ⟨by bv_omega, s4, hinv4, hm4⟩)
        (fun Jstep hJstep => ?_)
      let bv32 := s3.scratch.work_stk1[iv.toNat]'hiv_ws
      m7_lets
      refine wp_jnz_of (fun hbv_ult => ?_)
        (fun _ => by m7_lets; exact hJstep () m3 ⟨s3, hinv3_pk, hm3⟩)
      have hbv_lt : bv32.toNat < s3.core.cur_vars := by
        have h1 := m7b_ult64 hbv_ult
        rw [m7b_zext32, hcvv, m7b_ofNat64 (n := s0.core.cur_vars) (by omega), ← hcore3] at h1
        exact h1
      have hbv_flg : (bv32.setWidth 64).toNat < s3.core.flags.length := by
        rw [m7b_zext32, hlen3.core_ok.flags_len]
        exact Nat.lt_of_lt_of_le hbv_lt (by rw [hcore3]; exact hcv0_le)
      m7_ld (FullArenaTactics.c0_load_full_flags (s := s3) hbv_flg hm3)
      m7_lets
      refine wp_jnz_of (fun _ => ?_) (fun _ => by m7_lets; exact hJstep () m3 ⟨s3, hinv3_pk, hm3⟩)
      c0_call hFn
      refine ⟨c, s3, R, rfl, hlen3, hm3, ?_⟩
      intro _ s4 m4 hcore4 hlen4 hpr4 hm4
      m7_lets
      exact hJstep () m4 ⟨s4, bumpAnaLoopInv_step hinv3_pk hlen4 hcore4 hpr4, hm4⟩
    · exact hExit s3 m3 hinv3_pk hm3

/-- WP theorem for `full_bump_analyzed_m7` certifying `Full.fullBumpAnalyzedSpec`. -/
theorem full_bump_analyzed_m7_wp (Γ : Env)
    (hReasons : ∀ a m Q X, m7BumpReasonsSpec a m Q X →
      Γ "full_bump_reasons_m7" [i64] [] a m Q X)
    (hSort : ∀ a m Q X, m7BumpSortStampsSpec a m Q X →
      Γ "full_bump_sort_stamps_m7" [i64, i64] [] a m Q X)
    (hBumpVar : ∀ a m Q X, fullBumpVarSpec a m Q X → Γ "full_bump_var" [i64, i32] [] a m Q X)
    (hDecay : ∀ a m Q X, fullBumpDecaySpec a m Q X → Γ "full_bump_decay" [i64] [] a m Q X)
    (hQmtf : ∀ a m Q X, fullQueueMtfSpec a m Q X → Γ "full_queue_mtf" [i64, i32] [] a m Q X) :
    ∀ a m Q X, fullBumpAnalyzedSpec a m Q X → Func.wp Γ full_bump_analyzed_m7_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hcov, hm, hQ⟩
  have hmax : c.max_vars < 2 * dimacsBound := c.hmaxv
  unfold dimacsBound at hmax
  unfold Func.wp full_bump_analyzed_m7_body; dsimp only [full_bump_analyzed_m7_body]
  m7_ld (FullArenaTactics.load_full_probing hm)
  m7_lets
  refine wp_jnz_of (fun _ => ?_) (fun _ => ?_)
  · rw [m7_ret0]
    exact hQ s.core.mrk s.core.min_clr_len s.scratch m hlen hcov ⟨rfl, rfl⟩ rfl hm
  · m7_lets
    c0_call hReasons
    refine ⟨c, s, R, rfl, hlen, hcov, hm, ?_⟩
    intro mrk1 mcl1 ws1 m1 _ hlen1 hcov1 hm1
    let s1 : FullState :=
      { s with core := { s.core with mrk := mrk1, min_clr_len := mcl1 },
               scratch := { s.scratch with work_stk1 := ws1 } }
    have hm1' : (FullMem c s1 ⋆ R) m1 := hm1
    have hext1 : FullExtScratchPres s s1 := ⟨rfl, rfl⟩
    have hws2_1 : s1.scratch.work_stk2 = s.scratch.work_stk2 := rfl
    have hcv1_le : s1.core.cur_vars ≤ c.max_vars := hlen1.core_ok.cur_vars_le
    have hmcl1_le : s1.core.min_clr_len ≤ s1.core.cur_vars := hcov1.1
    clear hReasons hm hcov hlen
    m7_ld (FullArenaTactics.load_full_min_clr_len (s := s1) hm1')
    m7_ld (FullArenaTactics.load_full_cur_vars (s := s1) hm1')
    m7_ld (FullArenaTactics.load_full_max_vars (s := s1) hm1')
    m7_lets
    refine wp_jnz_of (fun hgt => ?_) (fun _ => ?_)
    · exfalso
      have h1 := m7b_ult64 hgt
      rw [m7b_ofNat64 (by omega), m7b_ofNat64 (by omega)] at h1; omega
    · m7_lets
      refine wp_join_group (ts := [i64])
        (fun (cnt, ()) m1a => m1a = m1 ∧ cnt.toNat = min s1.core.min_clr_len s1.core.cur_vars)
        ?_ ?_
      · rintro _ ⟨cnt, ⟨⟩⟩ _ ⟨rfl, hcnt⟩
        have hcnt_eq : cnt.toNat = s1.core.min_clr_len := by
          rw [hcnt, Nat.min_eq_left hmcl1_le]
        have hcnt_ws : cnt.toNat ≤ 2 * c.max_vars := by omega
        have hcnt_cv : cnt.toNat ≤ s1.core.cur_vars := by omega
        m7_ld (FullArenaTactics.load_full_work_stk1_ptr (s := s1) hm1')
        m7_ld (FullArenaTactics.load_full_flags_ptr (s := s1) hm1')
        m7_lets
        refine wp_join_group (ts := []) (fun _ m_fin => Q () m_fin)
          (fun _ _ m_fin hq => by rw [Blocks.get_here, m7_ret0]; exact hq)
          (fun Jfin hJfin => ?_)
        m7_ld (FullArenaTactics.load_full_stable (s := s1) hm1')
        m7_lets
        refine wp_jnz_of (fun _ => ?_) (fun _ => ?_)
        · clear hBumpVar hDecay
          m7_lets
          c0_call hSort
          refine ⟨c, s1, R, rfl, hlen1, hcnt_cv, hm1', ?_⟩
          intro ws2 m2 hwl2 hperm2 htail2 _hm2_sort hm2
          let s2 : FullState := { s1 with scratch := { s1.scratch with work_stk1 := ws2 } }
          have hlen2 : s2.LengthsOk c :=
            ⟨hlen1.core_ok, { hlen1.scratch_ok with work_stk1_len := hwl2 }⟩
          have hcov2 : FullAnaMarksCov c s2 :=
            anaMarksCov_perm hlen1 hcov1 hwl2 (by rwa [hcnt_eq] at hperm2)
          have hext2 : FullExtScratchPres s s2 := hext1
          have hws2_2 : s2.scratch.work_stk2 = s.scratch.work_stk2 := rfl
          have hm2' : (FullMem c s2 ⋆ R) m2 := hm2
          clear hSort hm1' hperm2 htail2 hwl2 hlen1 hcov1 hext1 hws2_1
          refine bump_active_loop_wp (s0 := s2) "full_queue_mtf" _ hQmtf hcnt_ws rfl
            hcv1_le hlen2 hm2' ?_
          intro s3 m3 ⟨hlen3, hcore3, hext3, hws3_1, hws3_2⟩ hm3
          have hs3_core : s3.core = { s.core with mrk := mrk1, min_clr_len := mcl1 } := hcore3
          have hcov3 := fullAnaMarksCov_of_eq hcov2 hs3_core hws3_1
          have hext3_s : FullExtScratchPres s s3 :=
            ⟨hext3.1.trans hext2.1, hext3.2.trans hext2.2⟩
          have hws3_s : s3.scratch.work_stk2 = s.scratch.work_stk2 := hws3_2.trans hws2_2
          have hrepack := full_state_repack hs3_core
          have hlen3' : { s with
              core := { s.core with mrk := mrk1, min_clr_len := mcl1 },
              scratch := s3.scratch }.LengthsOk c := by rw [← hrepack]; exact hlen3
          have hcov3' : FullAnaMarksCov c { s with
              core := { s.core with mrk := mrk1, min_clr_len := mcl1 },
              scratch := s3.scratch } := by rw [← hrepack]; exact hcov3
          have hm3' : (FullMem c { s with
              core := { s.core with mrk := mrk1, min_clr_len := mcl1 },
              scratch := s3.scratch } ⋆ R) m3 := by rw [← hrepack]; exact hm3
          m7_lets
          exact hJfin () m3 (hQ mrk1 mcl1 s3.scratch m3 hlen3' hcov3' hext3_s hws3_s hm3')
        · clear hSort hQmtf
          refine bump_active_loop_wp "full_bump_var" _ hBumpVar hcnt_ws rfl hcv1_le hlen1 hm1' ?_
          intro s3 m3 hinv3 hm3
          m7_lets
          c0_call hDecay
          refine ⟨c, s3, R, rfl, hinv3.1, hm3, ?_⟩
          intro _ s4 m4 hcore4 hlen4 hpr4 hm4
          have hinv4 := bumpAnaLoopInv_step hinv3 hlen4 hcore4 hpr4
          have hs4_core : s4.core = { s.core with mrk := mrk1, min_clr_len := mcl1 } := hinv4.2.1
          have hcov4 := fullAnaMarksCov_of_eq hcov1 hs4_core hinv4.2.2.2.1
          have hext4 : FullExtScratchPres s s4 :=
            ⟨hinv4.2.2.1.1.trans hext1.1, hinv4.2.2.1.2.trans hext1.2⟩
          have hws4 : s4.scratch.work_stk2 = s.scratch.work_stk2 :=
            hinv4.2.2.2.2.trans hws2_1
          have hrepack := full_state_repack hs4_core
          have hlen4' : { s with
              core := { s.core with mrk := mrk1, min_clr_len := mcl1 },
              scratch := s4.scratch }.LengthsOk c := by rw [← hrepack]; exact hlen4
          have hcov4' : FullAnaMarksCov c { s with
              core := { s.core with mrk := mrk1, min_clr_len := mcl1 },
              scratch := s4.scratch } := by rw [← hrepack]; exact hcov4
          have hm4' : (FullMem c { s with
              core := { s.core with mrk := mrk1, min_clr_len := mcl1 },
              scratch := s4.scratch } ⋆ R) m4 := by rw [← hrepack]; exact hm4
          m7_lets
          exact hJfin () m4 (hQ mrk1 mcl1 s4.scratch m4 hlen4' hcov4' hext4 hws4 hm4')
      · intro _ hJcnt
        m7_lets
        refine wp_jnz_of (fun hgt => ?_) (fun hle => ?_)
        · have h1 := m7b_ult64 hgt
          rw [m7b_ofNat64 (n := s1.core.cur_vars) (by omega),
            m7b_ofNat64 (n := s1.core.min_clr_len) (by omega)] at h1
          m7_lets
          exact hJcnt (BitVec.ofNat 64 s1.core.cur_vars, ()) m1 ⟨rfl, by
            rw [m7b_ofNat64 (n := s1.core.cur_vars) (by omega),
              Nat.min_eq_right (Nat.le_of_lt h1)]⟩
        · have h1 := m7b_not_ult64 hle
          rw [m7b_ofNat64 (n := s1.core.cur_vars) (by omega),
            m7b_ofNat64 (n := s1.core.min_clr_len) (by omega)] at h1
          m7_lets
          exact hJcnt (BitVec.ofNat 64 s1.core.min_clr_len, ()) m1 ⟨rfl, by
            rw [m7b_ofNat64 (n := s1.core.min_clr_len) (by omega), Nat.min_eq_left h1]⟩

end BumpAnalyzedProof

/-! ## 7. `m7Bump_moduleOk`, `m7BumpEnv_noExit`, Drop-ins & Concrete UNSAT Non-Vacuity -/

section ModuleOkSection

/-- Spec table covering all `7` M7 Bump/LCG fns and `3` externs (`noExit := true`). -/
def m7BumpSpecTable : List SpecEntry :=
  [ .ofFn full_rng_next_m7 m7RngNextExactSpec true
  , .ofFn full_log10_q16_m7 m7Log10Q16Spec true
  , .ofFn full_scale_delta_m7 m7ScaleDeltaSpec true
  , .ofFn full_bump_sift_m7 m7BumpSiftSpec true
  , .ofFn full_bump_sort_stamps_m7 m7BumpSortStampsSpec true
  , .ofFn full_bump_reasons_m7 m7BumpReasonsSpec true
  , .ofFn full_bump_analyzed_m7 fullBumpAnalyzedSpec true
  , ⟨"full_bump_var", [i64, i32], [], fullBumpVarSpec, true⟩
  , ⟨"full_bump_decay", [i64], [], fullBumpDecaySpec, true⟩
  , ⟨"full_queue_mtf", [i64, i32], [], fullQueueMtfSpec, true⟩
  ]

/-- Executable contract environment for `m7BumpModule`. -/
def m7BumpEnv : Env := Env.ofTable m7BumpSpecTable

theorem m7BumpSpecTable_nodup : (m7BumpSpecTable.map SpecEntry.name).Nodup := by decide

/-- Every entry in `m7BumpSpecTable` ignores abnormal exit continuations (`noExit = true`). -/
theorem m7BumpEnv_noExit :
    ∀ f as bs xs m Q X X', m7BumpEnv f as bs xs m Q X → m7BumpEnv f as bs xs m Q X' :=
  Env.ofTable_noExit fun e he => by
    simp only [m7BumpSpecTable, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

private theorem m7Bump_row {e : SpecEntry} (he : e ∈ m7BumpSpecTable) (hno : e.noExit = true)
    (hx : ∀ xs m Q X, e.spec xs m Q X → e.spec xs m Q (fun _ _ _ _ => False)) :
    ∀ xs m Q X, e.spec xs m Q X → m7BumpEnv e.name e.as e.rs xs m Q X :=
  fun xs m Q X h =>
    Env.ofTable_of_mem he m7BumpSpecTable_nodup
      (by simpa [SpecEntry.eff, hno] using hx xs m Q X h)

private theorem allFns_of_mem {P : Fn → Prop} :
    ∀ {fs : List Fn}, (∀ f ∈ fs, P f) → AllFns P fs
  | [], _ => trivial
  | _ :: _, h => ⟨h _ List.mem_cons_self, allFns_of_mem fun f hf => h f (List.mem_cons_of_mem _ hf)⟩

/-- Row-by-row table implementation for `m7BumpFns` under `m7BumpEnv`. -/
theorem m7Bump_tableImpl : TableImpl m7BumpEnv m7BumpFns m7BumpSpecTable := by
  have hLog := m7Bump_row (e := .ofFn full_log10_q16_m7 m7Log10Q16Spec true)
    (by simp [m7BumpSpecTable]) rfl (fun _ _ _ _ h => h)
  have hSift := m7Bump_row (e := .ofFn full_bump_sift_m7 m7BumpSiftSpec true)
    (by simp [m7BumpSpecTable]) rfl (fun _ _ _ _ h => h)
  have hSort := m7Bump_row (e := .ofFn full_bump_sort_stamps_m7 m7BumpSortStampsSpec true)
    (by simp [m7BumpSpecTable]) rfl (fun _ _ _ _ h => h)
  have hRsn := m7Bump_row (e := .ofFn full_bump_reasons_m7 m7BumpReasonsSpec true)
    (by simp [m7BumpSpecTable]) rfl (fun _ _ _ _ h => h)
  have hBVar := m7Bump_row (e := ⟨"full_bump_var", [i64, i32], [], fullBumpVarSpec, true⟩)
    (by simp [m7BumpSpecTable]) rfl (fun _ _ _ _ h => h)
  have hDec := m7Bump_row (e := ⟨"full_bump_decay", [i64], [], fullBumpDecaySpec, true⟩)
    (by simp [m7BumpSpecTable]) rfl (fun _ _ _ _ h => h)
  have hQmtf := m7Bump_row (e := ⟨"full_queue_mtf", [i64, i32], [], fullQueueMtfSpec, true⟩)
    (by simp [m7BumpSpecTable]) rfl (fun _ _ _ _ h => h)
  refine ⟨.of (full_rng_next_m7_wp_exact m7BumpEnv),
    .of (full_log10_q16_m7_wp m7BumpEnv),
    .of (full_scale_delta_m7_wp m7BumpEnv hLog),
    .of (full_bump_sift_m7_wp m7BumpEnv),
    .of (full_bump_sort_stamps_m7_wp m7BumpEnv hSift),
    .of (full_bump_reasons_m7_wp m7BumpEnv),
    .of (full_bump_analyzed_m7_wp m7BumpEnv hRsn hSort hBVar hDec hQmtf),
    trivial⟩

/-- Whole-module WP correctness theorem for `m7BumpModule` under `m7BumpEnv`. -/
theorem m7Bump_moduleOk : ModuleOk m7BumpEnv m7BumpModule :=
  Env.ofTable_moduleOk m7Bump_acyclic (allFns_of_mem m7BumpFns_wf) m7Bump_tableImpl

/-- Drop-in WP correctness for `m7RngNextFn` (`Full.fullRngNextSpec`). -/
theorem m7RngNextFn_wp (Γ : Env) :
    ∀ a m Q X, fullRngNextSpec a m Q X → Func.wp Γ m7RngNextFn.body a m Q X :=
  full_rng_next_m7_wp Γ

/-- Drop-in exact-LCG WP correctness for `m7RngNextFn` (`m7RngNextExactSpec`). -/
theorem m7RngNextFn_wp_exact (Γ : Env) :
    ∀ a m Q X, m7RngNextExactSpec a m Q X → Func.wp Γ m7RngNextFn.body a m Q X :=
  full_rng_next_m7_wp_exact Γ

/-- Drop-in WP correctness for `m7ScaleDeltaFn` (`m7ScaleDeltaSpec`). -/
theorem m7ScaleDeltaFn_wp (Γ : Env)
    (hLog : ∀ a m Q X, m7Log10Q16Spec a m Q X → Γ "full_log10_q16_m7" [i64] [i64] a m Q X) :
    ∀ a m Q X, m7ScaleDeltaSpec a m Q X → Func.wp Γ m7ScaleDeltaFn.body a m Q X :=
  full_scale_delta_m7_wp Γ hLog

/-- Drop-in `M6`-compatible WP correctness for `m7ScaleDeltaM6Fn` (`m7ScaleDeltaCompatSpec`). -/
theorem m7ScaleDeltaM6Fn_wp (Γ : Env)
    (hLog : ∀ a m Q X, m7Log10Q16Spec a m Q X → Γ "full_log10_q16_m7" [i64] [i64] a m Q X) :
    ∀ a m Q X, m7ScaleDeltaCompatSpec a m Q X → Func.wp Γ m7ScaleDeltaM6Fn.body a m Q X :=
  full_scale_delta_m7_wp_compat Γ hLog

/-- Drop-in WP correctness for `m7BumpAnalyzedFn` (`Full.fullBumpAnalyzedSpec`). -/
theorem m7BumpAnalyzedFn_wp (Γ : Env)
    (hReasons : ∀ a m Q X, m7BumpReasonsSpec a m Q X →
      Γ "full_bump_reasons_m7" [i64] [] a m Q X)
    (hSort : ∀ a m Q X, m7BumpSortStampsSpec a m Q X →
      Γ "full_bump_sort_stamps_m7" [i64, i64] [] a m Q X)
    (hBumpVar : ∀ a m Q X, fullBumpVarSpec a m Q X → Γ "full_bump_var" [i64, i32] [] a m Q X)
    (hDecay : ∀ a m Q X, fullBumpDecaySpec a m Q X → Γ "full_bump_decay" [i64] [] a m Q X)
    (hQmtf : ∀ a m Q X, fullQueueMtfSpec a m Q X → Γ "full_queue_mtf" [i64, i32] [] a m Q X) :
    ∀ a m Q X, fullBumpAnalyzedSpec a m Q X → Func.wp Γ m7BumpAnalyzedFn.body a m Q X :=
  full_bump_analyzed_m7_wp Γ hReasons hSort hBumpVar hDecay hQmtf

end ModuleOkSection

section ConcreteNonVacuity

/-- Minimal 1-variable UNSAT formula `nvOneLitF0 = {(x0), (¬x0)}` is unsatisfiable. -/
theorem nvM7F0_unsat : nvOneLitF0.Unsat := by
  rw [CNF.unsat_iff_not_sat]
  intro α hα
  have h0 : (cnfClause [0]).Sat α :=
    (CNF.sat_iff_all_mem_sat.mp hα) _
      (CNF.Internal.mem_iff.mpr (by dsimp only [nvOneLitF0]; simp [cnfOfClauses]))
  have h1 : (cnfClause [1]).Sat α :=
    (CNF.sat_iff_all_mem_sat.mp hα) _
      (CNF.Internal.mem_iff.mpr (by dsimp only [nvOneLitF0]; simp [cnfOfClauses]))
  rw [CNF.Clause.sat_iff_exists_mem_eq] at h0 h1
  obtain ⟨⟨v0, p0⟩, hm0, he0⟩ := h0; obtain ⟨⟨v1, p1⟩, hm1, he1⟩ := h1
  rw [mem_cnfClause_iff] at hm0 hm1
  simp only [List.mem_singleton] at hm0 hm1
  cases p0 <;> cases p1 <;> simp [litOfLiteral, mkLit] at hm0 hm1
  · have hv0 : v0 = 0 := by omega
    have hv1 : v1 = 0 := by omega
    subst hv0 hv1; dsimp only at he0 he1; rw [he0] at he1; cases he1
  · omega

/-- Concrete `FullAnaMarksCov` on the clean `nvOneLitState` (`min_clr_len = 0`). -/
theorem nvM7_anaMarksCov : FullAnaMarksCov nvOneLitCfg nvOneLitState := by
  refine ⟨by decide, by decide, fun k hk => absurd hk (Nat.not_lt_zero _), fun v hv hnz => ?_⟩
  have hv0 : v = 0 := by
    change v < nvOneLitState.core.cur_vars at hv
    change v < 1 at hv; omega
  subst hv0
  exact absurd (rfl : nvOneLitState.core.mrk[0]?.getD 0#8 = 0#8) hnz

/-- Concrete `Mem 64` UNSAT non-vacuity for `full_rng_next_m7` (`XPost := False`). -/
theorem nv_m7_rng_next :
    Func.wp m7BumpEnv full_rng_next_m7_body (nvOneLitCfg.hdr, ()) nvOneLitMem
      (fun (r, ()) m' =>
        nvOneLitF0.Unsat ∧
        r = (6364136223846793005#64 * nvOneLitState.scratch.rng_state +
          1442695040888963407#64) >>> (32 : Nat) ∧
        ∃ s' : FullState,
          s'.core = nvOneLitState.core ∧
          s'.scratch.rng_state =
            6364136223846793005#64 * nvOneLitState.scratch.rng_state + 1442695040888963407#64 ∧
          FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvOneLitCfg nvOneLitState ⋆ emp) nvOneLitMem := by
    rw [sep_emp]; exact nvOneLitMem_ok
  refine full_rng_next_m7_wp_exact m7BumpEnv _ _ _ _
    ⟨nvOneLitCfg, nvOneLitState, emp, rfl, nvOneLit_lengths, hm, ?_⟩
  intro res s' m' hs_core _hlen' hr hm'
  rcases res with ⟨r, ⟨⟩⟩
  dsimp only [m7KnuthNext] at hr
  rw [sep_emp] at hm'
  exact ⟨nvM7F0_unsat, by simpa [BitVec.mul_comm] using hr.2.1,
    s', hs_core, by simpa [BitVec.mul_comm] using hr.2.2, hm'⟩

/-- Concrete `Mem 64` UNSAT non-vacuity for `full_scale_delta_m7` (`XPost := False`). -/
theorem nv_m7_scale_delta :
    Func.wp m7BumpEnv full_scale_delta_m7_body (nvOneLitCfg.hdr, 100#64, ()) nvOneLitMem
      (fun (r, ()) m' => nvOneLitF0.Unsat ∧ 100 ≤ r.toNat ∧ FullMem nvOneLitCfg nvOneLitState m')
      (fun _ _ _ _ => False) := by
  have hLog := m7Bump_row (e := .ofFn full_log10_q16_m7 m7Log10Q16Spec true)
    (by simp [m7BumpSpecTable]) rfl (fun _ _ _ _ h => h)
  have hm : (FullMem nvOneLitCfg nvOneLitState ⋆ emp) nvOneLitMem := by
    rw [sep_emp]; exact nvOneLitMem_ok
  refine full_scale_delta_m7_wp m7BumpEnv hLog _ _ _ _
    ⟨nvOneLitCfg, nvOneLitState, emp, rfl, nvOneLit_lengths, hm, ?_⟩
  intro res s' m' hs_core _hlen' ⟨hs_scr, _h0, hle⟩ hm'
  rcases res with ⟨r, ⟨⟩⟩
  rw [hs_scr, sep_emp] at hm'
  exact ⟨nvM7F0_unsat, hle, hm'⟩

/-- Concrete `Mem 64` UNSAT non-vacuity for `full_bump_analyzed_m7` (`XPost := False`). -/
theorem nv_m7_bump_analyzed :
    Func.wp m7BumpEnv full_bump_analyzed_m7_body (nvOneLitCfg.hdr, ()) nvOneLitMem
      (fun _ m' =>
        nvOneLitF0.Unsat ∧
        ∃ s' : FullState,
          s'.LengthsOk nvOneLitCfg ∧ FullAnaMarksCov nvOneLitCfg s' ∧
          FullExtScratchPres nvOneLitState s' ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) := by
  have hRsn := m7Bump_row (e := .ofFn full_bump_reasons_m7 m7BumpReasonsSpec true)
    (by simp [m7BumpSpecTable]) rfl (fun _ _ _ _ h => h)
  have hSort := m7Bump_row (e := .ofFn full_bump_sort_stamps_m7 m7BumpSortStampsSpec true)
    (by simp [m7BumpSpecTable]) rfl (fun _ _ _ _ h => h)
  have hBVar := m7Bump_row (e := ⟨"full_bump_var", [i64, i32], [], fullBumpVarSpec, true⟩)
    (by simp [m7BumpSpecTable]) rfl (fun _ _ _ _ h => h)
  have hDec := m7Bump_row (e := ⟨"full_bump_decay", [i64], [], fullBumpDecaySpec, true⟩)
    (by simp [m7BumpSpecTable]) rfl (fun _ _ _ _ h => h)
  have hQmtf := m7Bump_row (e := ⟨"full_queue_mtf", [i64, i32], [], fullQueueMtfSpec, true⟩)
    (by simp [m7BumpSpecTable]) rfl (fun _ _ _ _ h => h)
  have hm : (FullMem nvOneLitCfg nvOneLitState ⋆ emp) nvOneLitMem := by
    rw [sep_emp]; exact nvOneLitMem_ok
  refine full_bump_analyzed_m7_wp m7BumpEnv hRsn hSort hBVar hDec hQmtf _ _ _ _
    ⟨nvOneLitCfg, nvOneLitState, emp, rfl, nvOneLit_lengths, nvM7_anaMarksCov, hm, ?_⟩
  intro mrk' mcl' sc' m' _ hlen' hcov' hext' _hws2 hm'
  rw [sep_emp] at hm'
  exact ⟨nvM7F0_unsat, _, hlen', hcov', hext', hm'⟩

end ConcreteNonVacuity

end LeanQbe.T.Examples.Kissat.FullM7Bump

