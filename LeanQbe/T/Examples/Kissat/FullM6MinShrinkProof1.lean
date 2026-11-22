module

public import LeanQbe.T.Examples.Kissat.FullM6MinShrinkProof0
import LeanQbe.T.Examples.Kissat.FullMinLemmas1
import LeanQbe.T.Examples.Kissat.FullWalkExtLemmas2
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat M6 `PR-W2B` Proof Shard 1 (Sorted VMTF Bumping & Delayed Analyze Restore)

Proves `Func.wp` for `4` functions in `FullM6MinShrink.lean` (UNSAT-only, no `@[expose]`):
1. `full_ana_sift_m6` (`m6AnaSiftSpec`)
2. `full_sort_ana_qs_m6` (`m6SortAnaQsSpec`)
3. `full_bump_analyzed_m6` (`Full.fullBumpAnalyzedSpec`)
4. `full_restore_bump_ana_m6` (`m6RestoreBumpAnaSpec`)
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM6MinShrink

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.C0HeadStep
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full hiding
  full_bump_analyzed_body full_bump_analyzed_wf full_bump_analyzed_wp
open LeanQbe.T.Examples.Kissat.Full.FullWalkExtHelpers
open LeanQbe.T.Examples.Kissat.Full.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.Full.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.Full.FullMinTactics
open Kraken.Bedrock2.Test

/-! ## 1. Wave-2B Specs for `ana_sift`, `sort_ana_qs`, and `restore_bump_ana` -/

/-- Heap sift contract for `full_ana_sift_m6(qs, ana, cv, start, n)`. -/
def m6AnaSiftSpec : Spec [i64, i64, i64, i64, i64] [] :=
  fun (qs_ptr, ana_ptr, cv, start, n, ()) m Q _ =>
    ∃ (qs ana : List (BitVec 32)) (R : Mem 64 → Prop),
      cv.toNat ≤ qs.length ∧ start.toNat ≤ n.toNat ∧ n.toNat ≤ ana.length ∧
      n.toNat < 2 ^ 62 ∧
      (∀ k < n.toNat, (ana[k]?.getD 0#32).toNat < cv.toNat) ∧
      (array (t := i32) qs_ptr qs ⋆ array (t := i32) ana_ptr ana ⋆ R) m ∧
      ∀ ana' m',
        ana'.length = ana.length → (ana'.take n.toNat).Perm (ana.take n.toNat) →
        (∀ k, n.toNat ≤ k → ana'[k]? = ana[k]?) →
        (∀ k < n.toNat, (ana'[k]?.getD 0#32).toNat < cv.toNat) →
        (array (t := i32) qs_ptr qs ⋆ array (t := i32) ana_ptr ana' ⋆ R) m' → Q () m'

/-- Ascending `q_stamp` heapsort contract for `work_stk1[0..n)`. -/
def m6SortAnaQsSpec : Spec [i64, i64] [] := fun (h, n, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ n.toNat ≤ s.core.cur_vars ∧
    (∀ k < n.toNat, (s.scratch.work_stk1[k]?.getD 0#32).toNat < s.core.cur_vars) ∧
    (Full.FullMem c s ⋆ R) m ∧
    ∀ ws1' m',
      ws1'.length = 2 * c.max_vars →
      (ws1'.take n.toNat).Perm (s.scratch.work_stk1.take n.toNat) →
      (∀ k, n.toNat ≤ k → ws1'[k]? = s.scratch.work_stk1[k]?) →
      (∀ k < n.toNat, (ws1'[k]?.getD 0#32).toNat < s.core.cur_vars) →
      (Full.FullMem c { s with scratch := { s.scratch with work_stk1 := ws1' } } ⋆ R) m' →
      Q () m'

/-- Delayed conflict-variable restore, bump, and clear contract (`full_restore_bump_ana_m6`). -/
def m6RestoreBumpAnaSpec : Spec [i64] [] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧
    (∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 = 0#8) ∧
    (Full.FullMem c s ⋆ R) m ∧
    ∀ mrk' mcl' sc' m',
      let s' : FullState :=
        { core := { s.core with mrk := mrk', min_clr_len := mcl' }, scratch := sc' }
      s'.LengthsOk c → (∀ v < c.max_vars, mrk'[v]?.getD 0#8 = 0#8) →
      (s.core.probing = 0#64 → mcl' = 0) →
      (s.core.probing ≠ 0#64 → mcl' = s.core.min_clr_len) →
      Full.FullExtScratchPres s s' → sc'.work_stk2 = s.scratch.work_stk2 →
      (Full.FullMem c s' ⋆ R) m' → Q () m'

theorem m6RestoreBumpAnaSpec_of {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {Q : Post []} {X : XPost} (hlen : s.LengthsOk c)
    (hmrk0 : ∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 = 0#8) (hm : (Full.FullMem c s ⋆ R) m)
    (hQ : ∀ mrk' mcl' sc' m',
      let s' : FullState :=
        { core := { s.core with mrk := mrk', min_clr_len := mcl' }, scratch := sc' }
      s'.LengthsOk c → (∀ v < c.max_vars, mrk'[v]?.getD 0#8 = 0#8) →
      (s.core.probing = 0#64 → mcl' = 0) →
      (s.core.probing ≠ 0#64 → mcl' = s.core.min_clr_len) →
      Full.FullExtScratchPres s s' → sc'.work_stk2 = s.scratch.work_stk2 →
      (Full.FullMem c s' ⋆ R) m' → Q () m') :
    m6RestoreBumpAnaSpec (c.hdr, ()) m Q X :=
  ⟨c, s, R, rfl, hlen, hmrk0, hm, hQ⟩

theorem m6AnaSiftSpec_monoX {xs : Tup Val [i64, i64, i64, i64, i64]} {m : Mem 64}
    {Q : Post []} {X X' : XPost} (h : m6AnaSiftSpec xs m Q X) : m6AnaSiftSpec xs m Q X' := by
  rcases xs with ⟨_, _, _, _, _, ⟨⟩⟩; exact h

theorem m6SortAnaQsSpec_monoX {xs : Tup Val [i64, i64]} {m : Mem 64} {Q : Post []}
    {X X' : XPost} (h : m6SortAnaQsSpec xs m Q X) : m6SortAnaQsSpec xs m Q X' := by
  rcases xs with ⟨_, _, ⟨⟩⟩; exact h

theorem m6RestoreBumpAnaSpec_monoX {xs : Tup Val [i64]} {m : Mem 64} {Q : Post []}
    {X X' : XPost} (h : m6RestoreBumpAnaSpec xs m Q X) : m6RestoreBumpAnaSpec xs m Q X' := by
  rcases xs with ⟨_, ⟨⟩⟩; exact h

/-! ## 2. Private list, permutation, footprint, and bump invariants -/

private theorem count_set_eq {α : Type} [DecidableEq α] (l : List α) (i : Nat) (v x : α)
    (hi : i < l.length) :
    (l.set i v).count x + (if l[i] = x then 1 else 0) =
      l.count x + (if v = x then 1 else 0) := by
  induction l generalizing i with
  | nil => simp at hi
  | cons a as ih =>
    cases i with
    | zero => simp [List.count_cons]; omega
    | succ i' =>
      have hi' : i' < as.length := by simpa using hi
      have ih' := ih i' hi'
      simp only [List.set_cons_succ, List.count_cons, List.getElem_cons_succ] at ih' ⊢
      omega

private theorem swap_perm {α : Type} [DecidableEq α] {xs : List α} {i j : Nat}
    (hi : i < xs.length) (hj : j < xs.length) :
    ((xs.set i (xs[j]'hj)).set j (xs[i]'hi)).Perm xs := by
  by_cases hij : i = j
  · subst hij; rw [List.set_getElem_self hi, List.set_getElem_self hi]
  · rw [List.perm_iff_count]; intro x
    have h1 := count_set_eq xs i (xs[j]'hj) x hi
    have h2 := count_set_eq (xs.set i (xs[j]'hj)) j (xs[i]'hi) x (by rw [List.length_set]; exact hj)
    rw [List.getElem_set_ne hij] at h2; omega

private theorem take_set_lt {α : Type} (xs : List α) {n i : Nat} (v : α) (hi : i < n) :
    (xs.set i v).take n = (xs.take n).set i v := by
  induction xs generalizing n i with
  | nil => simp
  | cons x xs ih =>
    cases n with
    | zero => omega
    | succ n' =>
      cases i with
      | zero => simp
      | succ i' => simp only [List.take_succ_cons, List.set_cons_succ]; rw [ih (by omega)]

private theorem swap_take_perm {xs : List (BitVec 32)} {n i j : Nat}
    (hi : i < n) (hj : j < n) (hn : n ≤ xs.length) :
    let xs' := (xs.set i (xs[j]'(by omega))).set j (xs[i]'(by omega))
    xs'.length = xs.length ∧ (xs'.take n).Perm (xs.take n) ∧
    (∀ k, n ≤ k → xs'[k]? = xs[k]?) ∧
    (∀ k < n, ∃ src < n, xs'[k]? = xs[src]?) := by
  intro xs'
  refine ⟨by simp [xs'], ?_, fun k hk => ?_, fun k hk => ?_⟩
  · have hi_t : i < (xs.take n).length := by simp; omega
    have hj_t : j < (xs.take n).length := by simp; omega
    have hsw : xs'.take n =
        (((xs.take n).set i ((xs.take n)[j]'hj_t)).set j ((xs.take n)[i]'hi_t)) := by
      dsimp only [xs']
      rw [take_set_lt _ _ hj, take_set_lt _ _ hi]
      simp [List.getElem_take]
    rw [hsw]; exact swap_perm hi_t hj_t
  · dsimp only [xs']; rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
  · by_cases hkj : k = j
    · refine ⟨i, hi, ?_⟩
      dsimp only [xs']; rw [hkj, List.getElem?_set_self (by simp; omega)]
      simp [List.getElem?_eq_getElem (by omega : i < xs.length)]
    · by_cases hki : k = i
      · refine ⟨j, hj, ?_⟩
        dsimp only [xs']
        rw [List.getElem?_set_ne (Ne.symm hkj), hki, List.getElem?_set_self (by omega)]
        simp [List.getElem?_eq_getElem (by omega : j < xs.length)]
      · refine ⟨k, hk, ?_⟩
        dsimp only [xs']
        rw [List.getElem?_set_ne (Ne.symm hkj), List.getElem?_set_ne (Ne.symm hki)]

private theorem list_take_split_eq {α : Type} {xs ys : List α} {m n : Nat}
    (hmn : m ≤ n) (hxs : n ≤ xs.length) (hys : xs.length = ys.length)
    (hsuf : ∀ k, m ≤ k → k < n → ys[k]? = xs[k]?) :
    ys.take n = ys.take m ++ (xs.drop m).take (n - m) := by
  refine List.ext_getElem (by simp; omega) fun k hk1 hk2 => ?_
  simp only [List.length_take, List.length_append, List.length_drop] at hk1 hk2
  by_cases hkm : k < m
  · rw [List.getElem_take, List.getElem_append_left (by simp; omega), List.getElem_take]
  · have hlen_l : (ys.take m).length = m := by simp; omega
    rw [List.getElem_take, List.getElem_append_right (by omega), List.getElem_take,
      List.getElem_drop]
    have hs := hsuf k (by omega) (by omega)
    rw [List.getElem?_eq_getElem (by omega : k < ys.length),
      List.getElem?_eq_getElem (by omega : k < xs.length)] at hs
    have heq := Option.some.inj hs
    simpa [hlen_l, show m + (k - m) = k by omega] using heq

private theorem perm_take_of_perm_prefix_eq_suffix {xs ys : List (BitVec 32)} {m n : Nat}
    (hmn : m ≤ n) (hn : n ≤ xs.length) (hl : ys.length = xs.length)
    (hperm : (ys.take m).Perm (xs.take m)) (hsuf : ∀ k, m ≤ k → ys[k]? = xs[k]?) :
    (ys.take n).Perm (xs.take n) := by
  rw [list_take_split_eq hmn hn hl.symm (fun k h1 _ => hsuf k h1),
    list_take_split_eq hmn hn rfl (fun _ _ _ => rfl)]
  exact hperm.append_right _

private theorem anaMarksCov_perm {c : FullCfg} {s : FullState} {ws1' : List (BitVec 32)}
    (hlen_s : s.LengthsOk c) (hcov : Full.FullAnaMarksCov c s)
    (hlen : ws1'.length = 2 * c.max_vars)
    (hperm : (ws1'.take s.core.min_clr_len).Perm
      (s.scratch.work_stk1.take s.core.min_clr_len))
    (_hsuf : ∀ k, s.core.min_clr_len ≤ k → ws1'[k]? = s.scratch.work_stk1[k]?) :
    Full.FullAnaMarksCov c { s with scratch := { s.scratch with work_stk1 := ws1' } } := by
  have hcv_le := hlen_s.core_ok.cur_vars_le
  have hwsl := hlen_s.scratch_ok.work_stk1_len
  rcases hcov with ⟨hmcl, hnd, hel, hmrk⟩
  refine ⟨hmcl, (hperm.map BitVec.toNat).nodup_iff.mpr hnd, fun k hk => ?_, fun v hv hnz => ?_⟩
  · dsimp only at hk
    have hk_len : k < (ws1'.take s.core.min_clr_len).length := by simp; omega
    have hmem : ws1'[k]'(by omega) ∈ s.scratch.work_stk1.take s.core.min_clr_len :=
      hperm.mem_iff.mp (by
        have := List.getElem_mem hk_len; simpa [List.getElem_take] using this)
    obtain ⟨j, hj, hjeq⟩ := List.mem_iff_getElem.mp hmem
    simp only [List.length_take, Nat.lt_min] at hj
    rw [List.getElem_take] at hjeq
    have hget : ws1'[k]?.getD 0#32 =
        s.scratch.work_stk1[j]?.getD 0#32 := by
      rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem hj.2, hjeq]
    rw [hget]; exact hel j hj.1
  · obtain ⟨i, hi, hieq⟩ := hmrk v hv hnz
    dsimp only at hieq ⊢
    have hi_len : i < (s.scratch.work_stk1.take s.core.min_clr_len).length := by simp; omega
    have hmem : s.scratch.work_stk1[i]'(by omega) ∈ ws1'.take s.core.min_clr_len :=
      hperm.symm.mem_iff.mp (by
        have := List.getElem_mem hi_len; simpa [List.getElem_take] using this)
    obtain ⟨j, hj, hjeq⟩ := List.mem_iff_getElem.mp hmem
    simp only [List.length_take, Nat.lt_min] at hj
    rw [List.getElem_take] at hjeq
    refine ⟨j, hj.1, ?_⟩
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some, hjeq]
    rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at hieq

private def fullRestSansQsWs1 (c : FullCfg) (s : FullState) : Mem 64 → Prop :=
  dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
  array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆ Full.FullCoreArrays c s.core ⋆
  (Full.FullScrByteArrs c s.scratch ⋆
    (array (t := i32) c.pHeap s.scratch.heap ⋆ array (t := i32) c.pPos s.scratch.pos ⋆
      array (t := i32) c.pShrinkStk s.scratch.shrink_stk ⋆
      array (t := i32) c.pQPrev s.scratch.q_prev ⋆
      array (t := i32) c.pQNext s.scratch.q_next) ⋆
    (array (t := i32) c.pWsort s.scratch.wsort ⋆
      array (t := i32) c.pWorkStk2 s.scratch.work_stk2 ⋆
      array (t := i32) c.pTarjanMark s.scratch.tarjan_mark ⋆
      array (t := i32) c.pTarjanReach s.scratch.tarjan_reach) ⋆
    Full.FullScrMetaArrs c s.scratch ⋆ Full.FullScrDynArrs c s.scratch) ⋆
  c.pad

private theorem fullMem_to_qs_ws1 {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (Full.FullMem c s ⋆ R) m) :
    (array (t := i32) c.pQStamp s.scratch.q_stamp ⋆
      array (t := i32) c.pWorkStk1 s.scratch.work_stk1 ⋆ (fullRestSansQsWs1 c s ⋆ R)) m := by
  unfold Full.FullMem Full.FullScratchArrays Full.FullScrU32A Full.FullScrWksArrs at hm
  unfold fullRestSansQsWs1
  exact sep_ac hm

private theorem fullMem_of_qs_ws1 {c : FullCfg} {s : FullState} {ws1' : List (BitVec 32)}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (array (t := i32) c.pQStamp s.scratch.q_stamp ⋆
      array (t := i32) c.pWorkStk1 ws1' ⋆ (fullRestSansQsWs1 c s ⋆ R)) m) :
    (Full.FullMem c { s with scratch := { s.scratch with work_stk1 := ws1' } } ⋆ R) m := by
  unfold Full.FullMem Full.FullScratchArrays Full.FullScrU32A Full.FullScrWksArrs
  unfold fullRestSansQsWs1 at hm
  have h0 : ({ s with scratch := { s.scratch with work_stk1 := ws1' } } : FullState).core =
      s.core := rfl
  have h1 : Full.hdrTailWords c { s with scratch := { s.scratch with work_stk1 := ws1' } } =
      Full.hdrTailWords c s := rfl
  have h2 : Full.FullScrByteArrs c { s.scratch with work_stk1 := ws1' } =
      Full.FullScrByteArrs c s.scratch := rfl
  have h3 : Full.FullScrMetaArrs c { s.scratch with work_stk1 := ws1' } =
      Full.FullScrMetaArrs c s.scratch := rfl
  have h4 : Full.FullScrDynArrs c { s.scratch with work_stk1 := ws1' } =
      Full.FullScrDynArrs c s.scratch := rfl
  rw [h0, h1, h2, h3, h4]
  exact sep_ac hm

private theorem setWidth32_eq_zero {x : BitVec 8} (h : BitVec.setWidth 32 x = 0#32) : x = 0#8 := by
  ext i hi
  have h1 := congrArg (·[i]) h
  simpa [BitVec.getElem_setWidth, hi, show i < 32 by omega] using h1

private def BumpAnaInv (c : FullCfg) (s s1 : FullState) (saved : Nat) : Prop :=
  s1.LengthsOk c ∧
  s1.core = { s.core with mrk := s1.core.mrk, min_clr_len := s1.core.min_clr_len } ∧
  s1.scratch = { s.scratch with work_stk1 := s1.scratch.work_stk1 } ∧
  saved ≤ s1.core.min_clr_len ∧ Full.FullAnaMarksCov c s1 ∧
  (∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 ≠ 0#8 →
    s1.core.mrk[v]?.getD 0#8 = s.core.mrk[v]?.getD 0#8) ∧
  (∀ k, saved ≤ k → k < s1.core.min_clr_len →
    (s1.scratch.work_stk1[k]?.getD 0#32).toNat < s.core.cur_vars ∧
    s.core.mrk[(s1.scratch.work_stk1[k]?.getD 0#32).toNat]?.getD 0#8 = 0#8)

private theorem bumpAnaInv_init {c : FullCfg} {s : FullState}
    (hlen : s.LengthsOk c) (hcov : Full.FullAnaMarksCov c s) :
    BumpAnaInv c s s s.core.min_clr_len :=
  ⟨hlen, rfl, rfl, Nat.le_refl _, hcov, fun _ _ _ => rfl, fun _ hk1 hk2 => by omega⟩

private theorem bumpAnaInv_step {c : FullCfg} {s s1 : FullState} {saved ov : Nat}
    (hinv : BumpAnaInv c s s1 saved) (hov : ov < s.core.cur_vars)
    (hmrk0 : s1.core.mrk[ov]?.getD 0#8 = 0#8) (_hmcl : s1.core.min_clr_len < s.core.cur_vars) :
    let ov32 := BitVec.ofNat 32 ov
    let s2 : FullState :=
      { core :=
          { s1.core with mrk := s1.core.mrk.set ov 1#8, min_clr_len := s1.core.min_clr_len + 1 }
        scratch :=
          { s1.scratch with work_stk1 := s1.scratch.work_stk1.set s1.core.min_clr_len ov32 } }
    BumpAnaInv c s s2 saved := by
  rcases hinv with ⟨hlen1, hcore1, hscr1, hsav, ⟨_, hnd, helem, hcov⟩, hpres, hnew⟩
  have hcv_le := hlen1.core_ok.cur_vars_le
  have hcv1 : s1.core.cur_vars = s.core.cur_vars := by rw [hcore1]
  have hmax : c.max_vars < 2 * dimacsBound := c.hmaxv
  unfold dimacsBound at hmax
  have hov_max : ov < c.max_vars := by omega
  have hov32_toNat : (BitVec.ofNat 32 ov).toNat = ov := bv32_ofNat_toNat (by omega)
  have hmcl_lt_ws : s1.core.min_clr_len < s1.scratch.work_stk1.length := by
    rw [hlen1.scratch_ok.work_stk1_len]; omega
  have hov_lt_mrk : ov < s1.core.mrk.length := by rw [hlen1.core_ok.mrk_len]; omega
  refine ⟨⟨{ hlen1.core_ok with
      mrk_len := by simp [hlen1.core_ok.mrk_len]
      min_clr_len_le := by dsimp only; omega },
    { hlen1.scratch_ok with work_stk1_len := by simp [hlen1.scratch_ok.work_stk1_len] }⟩,
    by rw [hcore1], by rw [hscr1], by dsimp only; omega, ⟨by dsimp only; omega, ?_, ?_, ?_⟩,
    ?_, ?_⟩
  · exact nodup_map_take_append hmcl_lt_ws hnd fun k hk he =>
      (helem k hk).2 (by rw [he, hov32_toNat]; exact hmrk0)
  · intro k hk; dsimp only at hk ⊢
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk) with hlt | rfl
    · rw [List.getElem?_set_ne (by omega)]
      have hne : (s1.scratch.work_stk1[k]?.getD 0#32).toNat ≠ ov := fun he =>
        (helem k hlt).2 (he ▸ hmrk0)
      exact ⟨(helem k hlt).1, by rw [List.getElem?_set_ne (Ne.symm hne)]; exact (helem k hlt).2⟩
    · rw [List.getElem?_set_self hmcl_lt_ws, Option.getD_some, hov32_toNat,
        List.getElem?_set_self hov_lt_mrk, Option.getD_some]
      exact ⟨by omega, by decide⟩
  · intro v hv hnz
    by_cases hveq : v = ov
    · subst v; refine ⟨s1.core.min_clr_len, by dsimp only; omega, ?_⟩
      dsimp only; rw [List.getElem?_set_self hmcl_lt_ws, Option.getD_some, hov32_toNat]
    · have hnz1 : s1.core.mrk[v]?.getD 0#8 ≠ 0#8 := by
        dsimp only at hnz; rwa [List.getElem?_set_ne (Ne.symm hveq)] at hnz
      obtain ⟨k, hk, hkeq⟩ := hcov v hv hnz1
      exact ⟨k, by dsimp only; omega, by
        dsimp only; rw [List.getElem?_set_ne (by omega)]; exact hkeq⟩
  · intro v hv hnz
    by_cases hveq : v = ov
    · subst v; rw [hpres ov hv hnz] at hmrk0; exact absurd hmrk0 hnz
    · dsimp only; rw [List.getElem?_set_ne (Ne.symm hveq)]; exact hpres v hv hnz
  · intro k hks hkm
    by_cases hkeq : k = s1.core.min_clr_len
    · subst k; dsimp only; rw [List.getElem?_set_self hmcl_lt_ws, Option.getD_some, hov32_toNat]
      refine ⟨hov, ?_⟩
      exact Classical.byContradiction fun hnz => by
        have heq := hpres ov hov_max hnz
        rw [heq] at hmrk0; exact hnz hmrk0
    · dsimp only at hkm ⊢; rw [List.getElem?_set_ne (Ne.symm hkeq)]
      exact hnew k hks (by omega)

private theorem bumpAnaInv_rollback {c : FullCfg} {s s1 : FullState} {saved : Nat}
    (hinv : BumpAnaInv c s s1 saved) (_hlt : saved < s1.core.min_clr_len) :
    let mcl' := s1.core.min_clr_len - 1
    let rv := (s1.scratch.work_stk1[mcl']?.getD 0#32).toNat
    rv < s.core.cur_vars ∧
    let s2 : FullState :=
      { core := { s1.core with mrk := s1.core.mrk.set rv 0#8, min_clr_len := mcl' }
        scratch := s1.scratch }
    BumpAnaInv c s s2 saved := by
  rcases hinv with ⟨hlen1, hcore1, hscr1, hsav, ⟨hmcl_le, hnd, helem, hcov⟩, hpres, hnew⟩
  have hcv_le := hlen1.core_ok.cur_vars_le
  have hcv1 : s1.core.cur_vars = s.core.cur_vars := by rw [hcore1]
  have hmcl' : s1.core.min_clr_len - 1 < s1.core.min_clr_len := by omega
  obtain ⟨hrv_lt, hrv_mrk0⟩ := hnew (s1.core.min_clr_len - 1) (by omega) hmcl'
  refine ⟨hrv_lt, ⟨{ hlen1.core_ok with
      mrk_len := by simp [hlen1.core_ok.mrk_len]
      min_clr_len_le := by dsimp only; omega },
    hlen1.scratch_ok⟩, by rw [hcore1], hscr1, by dsimp only; omega,
    ⟨by dsimp only; omega, nodup_map_take_sub1 hnd, ?_, ?_⟩, ?_, ?_⟩
  · intro k hk; dsimp only at hk ⊢
    have hne := nodup_map_take_ne (by rw [hlen1.scratch_ok.work_stk1_len]; omega) hnd hk
    exact ⟨(helem k (by omega)).1,
      by rw [List.getElem?_set_ne (Ne.symm hne)]; exact (helem k (by omega)).2⟩
  · intro v hv hnz
    have hne : v ≠ (s1.scratch.work_stk1[s1.core.min_clr_len - 1]?.getD 0#32).toNat := by
      intro he; dsimp only at hnz; rw [he, List.getElem?_set_self (by
        rw [hlen1.core_ok.mrk_len]; omega), Option.getD_some] at hnz
      exact hnz rfl
    have hnz1 : s1.core.mrk[v]?.getD 0#8 ≠ 0#8 := by
      dsimp only at hnz; rwa [List.getElem?_set_ne (Ne.symm hne)] at hnz
    obtain ⟨k, hk, hkeq⟩ := hcov v hv hnz1
    refine ⟨k, ?_, hkeq⟩
    have hkne : k ≠ s1.core.min_clr_len - 1 := by
      intro hke; subst hke; exact hne hkeq.symm
    dsimp only; omega
  · intro v hv hnz
    have hne : v ≠ (s1.scratch.work_stk1[s1.core.min_clr_len - 1]?.getD 0#32).toNat := by
      intro he; rw [he] at hnz; exact hnz hrv_mrk0
    dsimp only; rw [List.getElem?_set_ne (Ne.symm hne)]; exact hpres v hv hnz
  · intro k hks hkm; exact hnew k hks (by dsimp only at hkm; omega)

/-! ## 3. `full_ana_sift_m6` and `full_sort_ana_qs_m6` `Func.wp` proofs -/

theorem full_ana_sift_m6_wp (Γ : Env) :
    ∀ args m Q X, m6AnaSiftSpec args m Q X →
      Func.wp Γ full_ana_sift_m6_body args m Q X := by
  rintro ⟨qs_ptr, ana_ptr, cv, start, n, ⟨⟩⟩ m Q X
    ⟨qs, ana, R, hcv_qs, hst_n, hn_ana, hn62, hcov, hm, hQ⟩
  c0_hsteps_nogrp
  refine wp_join_group (ts := [i64]) (fun _ m1 => Q () m1)
    (fun _ _ _ hq => by c0_hsteps; exact hq) ?_
  intro Jbrk hBrk
  c0_hsteps_nogrp
  refine wp_loop_inv
    (fun (root, ()) mL =>
      root.toNat ≤ n.toNat ∧ ∃ anaL : List (BitVec 32),
        anaL.length = ana.length ∧ (anaL.take n.toNat).Perm (ana.take n.toNat) ∧
        (∀ k, n.toNat ≤ k → anaL[k]? = ana[k]?) ∧
        (∀ k < n.toNat, (anaL[k]?.getD 0#32).toNat < cv.toNat) ∧
        (array (t := i32) qs_ptr qs ⋆ array (t := i32) ana_ptr anaL ⋆ R) mL)
    (fun (root, ()) _ => n.toNat - root.toNat) (fun J hLoop => ?_)
    (fun J (root, ()) mL ⟨hrt_le, anaL, hlenL, hpermL, houtL, hcovL, hmL⟩ hLoop => ?_)
  · c0_hsteps
    exact hLoop (start, ()) m ⟨hst_n, ana, rfl, List.Perm.refl _, fun _ _ => rfl, hcov, hm⟩
  · have hch_eq : ((root <<< (1 : Nat)) + 1#64).toNat = 2 * root.toNat + 1 := by
      have hsh : (root <<< (1 : Nat)).toNat = 2 * root.toNat := by c0_bound
      rw [BitVec.toNat_add, hsh]; simp; omega
    c0_hsteps_nogrp
    · exact hBrk _ mL (hQ anaL mL hlenL hpermL houtL hcovL hmL)
    · have hch_lt : 2 * root.toNat + 1 < n.toNat := by
        have : ((root <<< (1 : Nat)) + 1#64).toNat < n.toNat := by c0_bound
        omega
      have hrt_lt : root.toNat < n.toNat := by omega
      have hch_ana : ((root <<< (1 : Nat)) + 1#64).toNat < anaL.length := by omega
      let ac := anaL[((root <<< (1 : Nat)) + 1#64).toNat]'hch_ana
      have hac_lt : (ac.setWidth 64).toNat < qs.length := by
        have hg := hcovL (2 * root.toNat + 1) hch_lt
        rw [List.getElem?_eq_getElem (by omega : 2 * root.toNat + 1 < anaL.length),
          Option.getD_some] at hg
        rw [zext_toNat _ (by decide)]
        have hac_eq : ac.toNat =
            (anaL[2 * root.toNat + 1]'(by omega)).toNat := by
          dsimp only [ac]; congr 2
        omega
      c0_hsteps_nogrp
      refine wp_join_group (ts := [i32]) (fun (qc, ()) m1 => mL = m1)
        (fun Jqc (qc, ()) m1 hm1 => ?_) (fun Jqc hJqc => ?_)
      · rcases hm1 with rfl; rw [Blocks.get_here]; dsimp only
        c0_hsteps_nogrp
        refine wp_join_group (ts := [i64, i32])
          (fun (ch, qc', ()) m2 =>
            mL = m2 ∧ ch.toNat < n.toNat ∧ root.toNat < ch.toNat)
          (fun Jch (ch, qc', ()) m2 ⟨hm2, hch_n, hrt_ch⟩ => ?_) (fun Jch hJch => ?_)
        · rcases hm2 with rfl; rw [Blocks.get_here]; dsimp only
          have hrt_ana : root.toNat < anaL.length := by omega
          let ar := anaL[root.toNat]'hrt_ana
          have har_lt : (ar.setWidth 64).toNat < qs.length := by
            have hg := hcovL root.toNat hrt_lt
            rw [List.getElem?_eq_getElem hrt_ana, Option.getD_some] at hg
            rw [zext_toNat _ (by decide)]
            dsimp only [ar]; omega
          c0_hsteps_nogrp
          refine wp_join_group (ts := [i32]) (fun (qr, ()) m3 => mL = m3)
            (fun Jqr (qr, ()) m3 hm3 => ?_) (fun Jqr hJqr => ?_)
          · rcases hm3 with rfl; rw [Blocks.get_here]; dsimp only
            c0_hsteps_nogrp
            · exact hBrk _ mL (hQ anaL mL hlenL hpermL houtL hcovL hmL)
            · have hch_ana' : ch.toNat < anaL.length := by omega
              have hrt_ana' :
                  root.toNat < (anaL.set ch.toNat (anaL[ch.toNat]'hch_ana')).length :=
                by simp [hrt_ana]
              c0_hsteps
              obtain ⟨hsl, hsp, hso, hsc⟩ :=
                swap_take_perm (xs := anaL) hrt_lt hch_n (by omega)
              refine hLoop (ch, ()) m (by dsimp only; omega) ⟨by omega, _,
                by simpa only [hlenL] using hsl, hsp.trans hpermL,
                fun k hk => (hso k hk).trans (houtL k hk), fun k hk => ?_, ?_⟩
              · obtain ⟨src, hsrc, heq⟩ := hsc k hk
                rw [heq]; exact hcovL src hsrc
              · simp only [sep_emp] at hm
                simpa only [hrt_ana, hch_ana'] using sep_ac hm
          · c0_hsteps
            · exact hJqr _ mL rfl
            · exact hJqr _ mL rfl
        · c0_hsteps_nogrp
          · have hch1_eq : (((root <<< (1 : Nat)) + 1#64) + 1#64).toNat =
                2 * root.toNat + 2 := by
              rw [BitVec.toNat_add, hch_eq]; simp; omega
            have hch1_lt : 2 * root.toNat + 2 < n.toNat := by
              have : (((root <<< (1 : Nat)) + 1#64) + 1#64).toNat < n.toNat := by c0_bound
              omega
            have hch1_ana : (((root <<< (1 : Nat)) + 1#64) + 1#64).toNat < anaL.length := by omega
            let ac1 := anaL[(((root <<< (1 : Nat)) + 1#64) + 1#64).toNat]'hch1_ana
            have hac1_lt : (ac1.setWidth 64).toNat < qs.length := by
              have hg := hcovL (2 * root.toNat + 2) hch1_lt
              rw [List.getElem?_eq_getElem (by omega : 2 * root.toNat + 2 < anaL.length),
                Option.getD_some] at hg
              rw [zext_toNat _ (by decide)]
              have hac1_eq : ac1.toNat =
                  (anaL[2 * root.toNat + 2]'(by omega)).toNat := by
                dsimp only [ac1]; congr 2
              omega
            c0_hsteps_nogrp
            refine wp_join_group (ts := [i32]) (fun (qc1, ()) m2 => mL = m2)
              (fun Jqc1 (qc1, ()) m2 hm2 => ?_) (fun Jqc1 hJqc1 => ?_)
            · rcases hm2 with rfl; rw [Blocks.get_here]; dsimp only
              c0_hsteps
              · exact hJch _ mL ⟨rfl, by erw [hch1_eq]; exact hch1_lt, by erw [hch1_eq]; omega⟩
              · exact hJch _ mL ⟨rfl, by erw [hch_eq]; exact hch_lt, by erw [hch_eq]; omega⟩
            · c0_hsteps
              · exact hJqc1 _ mL rfl
              · exact hJqc1 _ mL rfl
          · exact hJch _ mL ⟨rfl, by erw [hch_eq]; exact hch_lt, by erw [hch_eq]; omega⟩
      · c0_hsteps
        · exact hJqc _ mL rfl
        · exact hJqc _ mL rfl
    · cases hc

theorem full_sort_ana_qs_m6_wp (Γ : Env)
    (hSift : ∀ args m Q X, m6AnaSiftSpec args m Q X →
      Γ "full_ana_sift_m6" [i64, i64, i64, i64, i64] [] args m Q X) :
    ∀ args m Q X, m6SortAnaQsSpec args m Q X →
      Func.wp Γ full_sort_ana_qs_m6_body args m Q X := by
  rintro ⟨h, n, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hn_cv, hcov, hm, hQ⟩
  have hmax : c.max_vars < 2 * dimacsBound := c.hmaxv
  unfold dimacsBound at hmax
  have hcv_le := hlen.core_ok.cur_vars_le
  have hwsl := hlen.scratch_ok.work_stk1_len
  have hqsl := hlen.scratch_ok.q_stamp_len
  c0_hsteps_nogrp
  · exact hQ s.scratch.work_stk1 m hwsl (List.Perm.refl _) (fun _ _ => rfl) hcov hm
  · have hn_ge2 : 2 ≤ n.toNat := by
      have h1 : ¬ n.toNat ≤ (1#64).toNat := by c0_bound
      rw [show (1#64).toNat = 1 from rfl] at h1; omega
    have hm_focus := fullMem_to_qs_ws1 hm
    clear hm
    let ws0 := s.scratch.work_stk1
    let R' := fullRestSansQsWs1 c s ⋆ R
    let LoopInv : Nat → List (BitVec 32) → Prop := fun bnd wsL =>
      wsL.length = 2 * c.max_vars ∧ (wsL.take n.toNat).Perm (ws0.take n.toNat) ∧
      (∀ k, n.toNat ≤ k → wsL[k]? = ws0[k]?) ∧
      (∀ k < bnd, (wsL[k]?.getD 0#32).toNat < s.core.cur_vars)
    refine wp_loop_inv
      (fun (start, ()) m1 => start.toNat ≤ n.toNat / 2 ∧ ∃ wsL,
        LoopInv n.toNat wsL ∧ (array (t := i32) c.pQStamp s.scratch.q_stamp ⋆
          array (t := i32) c.pWorkStk1 wsL ⋆ R') m1)
      (fun (start, ()) _ => start.toNat) (fun J1 hJ1 => ?_)
      (fun J1 (start, ()) m1 ⟨hst_le, ws1, hli1, hm1⟩ hJ1 => ?_)
    · c0_hsteps
      exact hJ1 (n >>> (1 : Nat), ()) m ⟨by
        rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.pow_one]
        exact Nat.le_refl _, ws0, ⟨hwsl, List.Perm.refl _, fun _ _ => rfl, hcov⟩, hm_focus⟩
    · c0_hsteps_nogrp
      · have hst_pos : 0 < start.toNat := by c0_bound
        have hst_m1 : (start - 1).toNat = start.toNat - 1 := by bv_omega
        c0_call hSift
        refine ⟨s.scratch.q_stamp, ws1, R',
          by rw [hqsl, bv64_ofNat_toNat (by omega)]; exact hcv_le,
          by rw [hst_m1]; omega, by rw [hli1.1]; omega, by omega,
          by rw [bv64_ofNat_toNat (by omega)]; exact hli1.2.2.2, hm1, ?_⟩
        intro ws2 m2 hl2 hp2 hsuf2 hcov2 hm2
        rw [bv64_ofNat_toNat (by omega)] at hcov2
        exact hJ1 (start - 1, ()) m2 (by dsimp only; omega)
          ⟨by rw [hst_m1]; omega, ws2,
            ⟨by rw [hl2, hli1.1], hp2.trans hli1.2.1,
              fun k hk => (hsuf2 k hk).trans (hli1.2.2.1 k hk), hcov2⟩, hm2⟩
      · have hnm1 : (n - 1#64).toNat = n.toNat - 1 := by bv_omega
        refine wp_loop_inv
          (fun (endb, ()) m2 => endb.toNat < n.toNat ∧ ∃ wsL,
            LoopInv n.toNat wsL ∧ (array (t := i32) c.pQStamp s.scratch.q_stamp ⋆
              array (t := i32) c.pWorkStk1 wsL ⋆ R') m2)
          (fun (endb, ()) _ => endb.toNat) (fun J2 hJ2 => ?_)
          (fun J2 (endb, ()) m2 ⟨hend_lt, ws2, hli2, hm2⟩ hJ2 => ?_)
        · c0_hsteps
          exact hJ2 (n - 1#64, ()) m1 ⟨by rw [hnm1]; omega, ws1, hli1, hm1⟩
        · c0_hsteps_nogrp
          · have hend_pos : 0 < endb.toNat := by c0_bound
            have h0_lt : 0 < ws2.length := by rw [hli2.1]; omega
            have he_lt : endb.toNat < ws2.length := by rw [hli2.1]; omega
            have hend_m1 : (endb - 1).toNat = endb.toNat - 1 := by bv_omega
            let ws3 := (ws2.set 0 (ws2[endb.toNat]'he_lt)).set endb.toNat (ws2[0]'h0_lt)
            obtain ⟨hsl3, hsp3, hso3, hsc3⟩ := swap_take_perm (xs := ws2) (by omega : 0 < n.toNat)
              hend_lt (by rw [hli2.1]; omega)
            have hcov3 : ∀ k < n.toNat, (ws3[k]?.getD 0#32).toNat < s.core.cur_vars := by
              intro k hk; obtain ⟨src, hsrc, heq⟩ := hsc3 k hk
              rw [heq]; exact hli2.2.2.2 src hsrc
            c0_hsteps_nogrp
            c0_call hSift
            refine ⟨s.scratch.q_stamp, ws3, R',
              by rw [hqsl, bv64_ofNat_toNat (by omega)]; exact hcv_le,
              by simp, by rw [hsl3, hli2.1]; omega, by omega,
              by rw [bv64_ofNat_toNat (by omega)]; exact fun k hk => hcov3 k (by omega), ?_, ?_⟩
            · simp only [sep_emp] at hm; exact sep_ac hm
            · intro ws4 m4 hl4 hp4 hsuf4 _ hm4
              have hws3_len : ws3.length = 2 * c.max_vars := hsl3.trans hli2.1
              have hws4_len : ws4.length = 2 * c.max_vars := hl4.trans hws3_len
              have hp4_n : (ws4.take n.toNat).Perm (ws3.take n.toNat) :=
                perm_take_of_perm_prefix_eq_suffix (by omega) (by rw [hsl3, hli2.1]; omega)
                  hl4 hp4 hsuf4
              have hcov4 : ∀ k < n.toNat, (ws4[k]?.getD 0#32).toNat < s.core.cur_vars := by
                intro k hk
                by_cases hke : k < endb.toNat
                · have hk4 : k < (ws4.take n.toNat).length := by rw [List.length_take]; omega
                  have hmem : ws4[k]'(by rw [hws4_len]; omega) ∈ ws3.take n.toNat :=
                    hp4_n.mem_iff.mp (by
                      have := List.getElem_mem hk4; simpa [List.getElem_take] using this)
                  obtain ⟨j, hj, hjeq⟩ := List.mem_iff_getElem.mp hmem
                  simp only [List.length_take, Nat.lt_min] at hj
                  rw [List.getElem_take] at hjeq
                  rw [List.getElem?_eq_getElem (by rw [hws4_len]; omega),
                    Option.getD_some, ← hjeq]
                  have := hcov3 j hj.1
                  rwa [List.getElem?_eq_getElem (by rw [hws3_len]; omega),
                    Option.getD_some] at this
                · rw [hsuf4 k (by omega)]; exact hcov3 k hk
              exact hJ2 (endb - 1, ()) m4 (by dsimp only; omega) ⟨by rw [hend_m1]; omega, ws4,
                ⟨by rw [hl4, hsl3, hli2.1], hp4_n.trans (hsp3.trans hli2.2.1),
                  fun k hk => (hsuf4 k (by omega)).trans ((hso3 k hk).trans (hli2.2.2.1 k hk)),
                  hcov4⟩, hm4⟩
          · exact hQ ws2 m2 hli2.1 hli2.2.1 hli2.2.2.1 hli2.2.2.2 (fullMem_of_qs_ws1 hm2)

/-! ## 4. `full_bump_analyzed_m6` `Func.wp` proof against `Full.fullBumpAnalyzedSpec` -/

private theorem bv64_ult_toNat {a b : BitVec 64} (h : a.ult b = true) : a.toNat < b.toNat := by
  simpa [BitVec.ult] using h

private theorem bv64_not_ult_toNat {a b : BitVec 64} (h : a.ult b = false) :
    b.toNat ≤ a.toNat := by
  simp [BitVec.ult] at h; exact h

private theorem bv64_ule_toNat {a b : BitVec 64} (h : a.ule b = true) : a.toNat ≤ b.toNat := by
  simpa [BitVec.ule] using h

private theorem bv32_ult_toNat {a b : BitVec 32} (h : a.ult b = true) : a.toNat < b.toNat := by
  simpa [BitVec.ult] using h

private theorem bv8_zext32_beq_zero {x : BitVec 8} (h : (x.setWidth 32 == 0#32) = true) :
    x = 0#8 :=
  setWidth32_eq_zero (beq_iff_eq.mp h)

private theorem bumpAna_push_post {c : FullCfg} {s s1 : FullState} {saved : Nat}
    {R : Mem 64 → Prop} {m3 : Mem 64} (ov : BitVec 32)
    (hinv1 : BumpAnaInv c s s1 saved) (hov_lt : ov.toNat < s.core.cur_vars)
    (hmrk0 : s1.core.mrk[ov.toNat]?.getD 0#8 = 0#8)
    (hmcl_lt : s1.core.min_clr_len < s.core.cur_vars)
    (hm3 : (FullMem c
      { core :=
          { s1.core with
            mrk := s1.core.mrk.set ov.toNat 1#8
            min_clr_len := (BitVec.ofNat 64 s1.core.min_clr_len + 1).toNat }
        scratch :=
          { s1.scratch with work_stk1 := s1.scratch.work_stk1.set s1.core.min_clr_len ov } } ⋆
      R) m3) :
    ∃ s3 : FullState, BumpAnaInv c s s3 saved ∧ (FullMem c s3 ⋆ R) m3 := by
  have hmax : c.max_vars < 2 * dimacsBound := c.hmaxv
  unfold dimacsBound at hmax
  have hcv_le : s.core.cur_vars ≤ c.max_vars := by
    rw [← congrArg FullCoreState.cur_vars hinv1.2.1]; exact hinv1.1.core_ok.cur_vars_le
  have h_mcl1 : (BitVec.ofNat 64 s1.core.min_clr_len + 1).toNat = s1.core.min_clr_len + 1 :=
    bv64_ofNat_add1 (by omega : s1.core.min_clr_len + 1 < 2 ^ 64)
  rw [h_mcl1] at hm3
  have hinv3 := bumpAnaInv_step hinv1 hov_lt hmrk0 hmcl_lt
  have hbv_ov : BitVec.ofNat 32 ov.toNat = ov :=
    BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ov.isLt])
  refine ⟨_, ?_, hm3⟩
  simpa only [hbv_ov] using hinv3

local macro "ml_bump_push" c_var:ident s_var:ident hinv_var:ident hm_var:ident ov_var:ident
    hov_lt:ident hmrk0:ident hmcl_lt:ident hmrk_bd:ident hwsl:ident hJ:ident : tactic =>
  `(tactic| (
    ml_st m_a, hm_a := c0_store_full_mrk (s := $s_var)
      (i := ($ov_var).setWidth 64) ((1 : BitVec 32).setWidth 8) $hmrk_bd $hm_var
    rw [show (1 : BitVec 32).setWidth 8 = 1#8 from rfl, bv_c0_zext32_64] at hm_a
    have hws_len_a : ($s_var).scratch.work_stk1.length = 2 * ($c_var).max_vars := $hwsl
    have hmcl_ws : (BitVec.ofNat 64 ($s_var).core.min_clr_len).toNat <
        { $s_var with core := { ($s_var).core with
          mrk := ($s_var).core.mrk.set ($ov_var).toNat 1#8 } }.scratch.work_stk1.length := by
      rw [bv64_ofNat_toNat (by omega : ($s_var).core.min_clr_len < 2 ^ 64)]
      dsimp only; rw [hws_len_a]; omega
    ml_ld (load_full_min_clr_len (s := _) hm_a)
    ml_st m_b, hm_b := c0_store_full_work_stk1 (s := _)
      (i := BitVec.ofNat 64 ($s_var).core.min_clr_len) ($ov_var) hmcl_ws hm_a
    rw [bv64_ofNat_toNat (by omega : ($s_var).core.min_clr_len < 2 ^ 64)] at hm_b
    ml_ld (load_full_min_clr_len (s := _) hm_b)
    ml_st m_c, hm_c := c0_store_full_min_clr_len (s := _)
      (BitVec.ofNat 64 ($s_var).core.min_clr_len + 1) hm_b
    ml_lets
    exact $hJ () m_c
      (bumpAna_push_post $ov_var $hinv_var $hov_lt $hmrk0 $hmcl_lt hm_c)))

theorem full_bump_analyzed_m6_wp (Γ : Env)
    (hDrAllow : ∀ a m Q X, m6DrAllowSpec a m Q X → Γ "full_dr_allow_m6" [i64] [.bool] a m Q X)
    (hSortQs : ∀ a m Q X, m6SortAnaQsSpec a m Q X →
      Γ "full_sort_ana_qs_m6" [i64, i64] [] a m Q X)
    (hBump : ∀ a m Q X, fullBumpVarSpec a m Q X → Γ "full_bump_var" [i64, i32] [] a m Q X)
    (hMtf : ∀ a m Q X, fullQueueMtfSpec a m Q X → Γ "full_queue_mtf" [i64, i32] [] a m Q X)
    (hDecay : ∀ a m Q X, fullBumpDecaySpec a m Q X → Γ "full_bump_decay" [i64] [] a m Q X) :
    ∀ a m Q X, Full.fullBumpAnalyzedSpec a m Q X →
      Func.wp Γ full_bump_analyzed_m6_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hcov0, hm, hQ⟩
  have hmax : c.max_vars < 2 * dimacsBound := c.hmaxv
  have haca : c.arena_cap < 2 * dimacsBound := c.harena
  unfold dimacsBound at hmax haca
  have hcv_le := hlen.core_ok.cur_vars_le
  unfold Func.wp full_bump_analyzed_m6_body; dsimp only [full_bump_analyzed_m6_body]
  ml_ld (load_full_probing hm); ml_lets; ml_jnz
  refine ⟨fun _ => by
    ml_lets; rw [wp]
    exact hQ s.core.mrk s.core.min_clr_len s.scratch m hlen hcov0 ⟨rfl, rfl⟩ rfl hm, fun _ => ?_⟩
  ml_ld (load_full_work_stk1_ptr hm); ml_ld (load_full_level_ptr hm)
  ml_ld (load_full_reason_ptr hm); ml_ld (load_full_tmp_lits_ptr hm)
  ml_ld (load_full_arena_ptr hm); ml_ld (load_full_flags_ptr hm)
  ml_ld (load_full_mark_ptr hm); ml_ld (load_full_cur_vars hm)
  ml_ld (load_full_min_clr_len hm); ml_lets
  let saved := s.core.min_clr_len
  let lim := BitVec.ofNat 64 saved * 10#64
  have hmcl_cv := hcov0.1
  have hlim_eq : lim.toNat = saved * 10 := by
    have hs32 : saved < 2 ^ 30 := by omega
    dsimp only [lim]
    rw [BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : saved < 2 ^ 64),
      show (10#64).toNat = 10 from rfl, Nat.mod_eq_of_lt (by omega)]
  refine wp_join_group (ts := [])
    (fun _ m2 => ∃ s2 : FullState, BumpAnaInv c s s2 saved ∧ (FullMem c s2 ⋆ R) m2)
    (fun Jallow _ m2 ⟨s2, hinv2, hm2⟩ => ?_) (fun Jallow hJallow => ?_)
  · rw [Blocks.get_here]; ml_lets
    have hinv2_pk := hinv2
    rcases hinv2 with ⟨hlen2, hcore2, hscr2, _, hcov2, _, _⟩
    have hcv2 : s2.core.cur_vars = s.core.cur_vars := by rw [hcore2]
    have hmcl2 : s2.core.min_clr_len ≤ s.core.cur_vars := by rw [← hcv2]; exact hcov2.1
    have hwsl2 := hlen2.scratch_ok.work_stk1_len
    have hfll2 := hlen2.core_ok.flags_len
    let cnt := s2.core.min_clr_len
    ml_ld (load_full_min_clr_len (s := s2) hm2); ml_lets
    refine wp_join_group (ts := [])
      (fun _ m3 => ∃ ws3 : List (BitVec 32), ws3.length = 2 * c.max_vars ∧
        FullAnaMarksCov c { s2 with scratch := { s2.scratch with work_stk1 := ws3 } } ∧
        (FullMem c { s2 with scratch := { s2.scratch with work_stk1 := ws3 } } ⋆ R) m3)
      (fun Jsort _ m3 ⟨ws3, hws3_len, hcov3, hm3⟩ => ?_) (fun Jsort hJsort => ?_)
    · rw [Blocks.get_here]; ml_lets
      let s3 : FullState := { s2 with scratch := { s2.scratch with work_stk1 := ws3 } }
      have hlen3 : s3.LengthsOk c :=
        ⟨hlen2.core_ok, { hlen2.scratch_ok with work_stk1_len := hws3_len }⟩
      refine wp_loop_inv
        (fun (k, ()) m4 => k.toNat ≤ cnt ∧ ∃ s4 : FullState,
          s4.LengthsOk c ∧
          s4.core = { s.core with mrk := s2.core.mrk, min_clr_len := cnt } ∧
          s4.scratch.work_stk1 = ws3 ∧ s4.scratch.work_stk2 = s.scratch.work_stk2 ∧
          s4.scratch.last_learned = s.scratch.last_learned ∧
          s4.scratch.extend_len = s.scratch.extend_len ∧
          (FullMem c s4 ⋆ R) m4)
        (fun (k, ()) _ => cnt - k.toNat) (fun Jk hJk => ?_)
        (fun Jk (k, ()) m4 ⟨hk_le, s4, hlen4, hcore4, hws4, hws24, hll4, hel4, hm4⟩ hJk => ?_)
      · ml_lets
        exact hJk (0#64, ()) m3 ⟨by simp, s3, hlen3, hcore2, rfl,
          by dsimp only [s3]; rw [hscr2], by dsimp only [s3]; rw [hscr2],
          by dsimp only [s3]; rw [hscr2], hm3⟩
      · rw [Blocks.get_here]; ml_lets; ml_jnz; refine ⟨fun hklt => ?_, fun _ => ?_⟩
        · have hk_lt : k.toNat < cnt := by
            have h1 := bv64_ult_toNat hklt
            rwa [bv64_ofNat_toNat (by omega : cnt < 2 ^ 64)] at h1
          have hk_ws : k.toNat < s4.scratch.work_stk1.length := by
            rw [hlen4.scratch_ok.work_stk1_len]; omega
          ml_ld (c0_load_full_work_stk1 (s := s4) (i := k) hk_ws hm4); ml_lets
          let bv := s4.scratch.work_stk1[k.toNat]'hk_ws
          have hbv_lt : bv.toNat < s.core.cur_vars → bv.toNat < s4.core.flags.length := fun h =>
            by rw [hlen4.core_ok.flags_len]; omega
          refine wp_join_group (ts := [])
            (fun _ m5 => ∃ s5 : FullState,
              s5.LengthsOk c ∧
              s5.core = { s.core with mrk := s2.core.mrk, min_clr_len := cnt } ∧
              s5.scratch.work_stk1 = ws3 ∧ s5.scratch.work_stk2 = s.scratch.work_stk2 ∧
              s5.scratch.last_learned = s.scratch.last_learned ∧
              s5.scratch.extend_len = s.scratch.extend_len ∧
              (FullMem c s5 ⋆ R) m5)
            (fun Jw _ m5 ⟨s5, hs5, hc5, hws5, hws25, hll5, hel5, hm5⟩ => ?_)
            (fun Jw hJw => ?_)
          · rw [Blocks.get_here]; ml_lets
            exact hJk (k + 1#64, ()) m5 (by dsimp only; bv_omega)
              ⟨by bv_omega, s5, hs5, hc5, hws5, hws25, hll5, hel5, hm5⟩
          · ml_lets; ml_jnz; refine ⟨fun hbv_ok => ?_, fun _ => ?_⟩
            · have hbv_cv : bv.toNat < s.core.cur_vars := by
                have hk_ws3 : k.toNat < ws3.length := by rwa [← hws4]
                have h1 := (hcov3.2.2.1 k.toNat hk_lt).1
                dsimp only at h1
                rw [List.getElem?_eq_getElem hk_ws3, Option.getD_some, hcv2] at h1
                have h4e : bv = ws3[k.toNat]'hk_ws3 := by dsimp only [bv]; simp only [hws4]
                rwa [h4e]
              have hfl_ok : (bv.setWidth 64).toNat < s4.core.flags.length := by
                rw [bv_c0_zext32_64]; exact hbv_lt hbv_cv
              ml_ld (c0_load_full_flags (s := s4) (i := bv.setWidth 64) hfl_ok hm4)
              ml_lets; ml_jnz; refine ⟨fun _ => ?_, fun _ => ?_⟩
              · ml_lets; apply wp_call_of_spec; apply hBump
                refine ⟨c, s4, R, rfl, hlen4, hm4, fun ⟨⟩ s5 m5 hcore5 hs5 hp5 hm5 => ?_⟩
                dsimp only [fullSafetySlice_mem, fullSafetySlice_coreProj,
                  fullSafetySlice_safe] at hcore5 hs5 hp5 hm5
                have heq5 := @fullCoreState_agrees_with_scratch c s4 s5 hcore5
                refine wp_join_group (ts := [])
                  (fun _ m6 => ∃ s6 : FullState,
                    s6.LengthsOk c ∧
                    s6.core = { s.core with mrk := s2.core.mrk, min_clr_len := cnt } ∧
                    s6.scratch.work_stk1 = ws3 ∧ s6.scratch.work_stk2 = s.scratch.work_stk2 ∧
                    s6.scratch.last_learned = s.scratch.last_learned ∧
                    s6.scratch.extend_len = s.scratch.extend_len ∧
                    (FullMem c s6 ⋆ R) m6)
                  (fun _ _ m6 ⟨s6, hs6, hc6, hws6, hws26, hll6, hel6, hm6⟩ => by
                    rw [Blocks.get_here]; ml_lets
                    exact hJw () m6 ⟨s6, hs6, hc6, hws6, hws26, hll6, hel6, hm6⟩)
                  (fun Jmtf hJmtf => ?_)
                ml_ld (load_full_stable (s := s5) hm5); ml_lets; ml_jnz
                refine ⟨fun _ => ?_, fun _ => ?_⟩
                · ml_lets; apply wp_call_of_spec; apply hMtf
                  refine ⟨c, s5, R, rfl, hs5, hm5, fun ⟨⟩ s6 m6 hcore6 hs6 hp6 hm6 => ?_⟩
                  dsimp only [fullSafetySlice_mem, fullSafetySlice_coreProj,
                    fullSafetySlice_safe] at hcore6 hs6 hp6 hm6
                  have heq6 := @fullCoreState_agrees_with_scratch c s5 s6 hcore6
                  exact hJmtf () m6 ⟨s6, hs6, by rw [heq6, heq5, hcore4],
                    by rw [hp6.2.1, hp5.2.1, hws4], by rw [hp6.2.2.1, hp5.2.2.1, hws24],
                    by rw [hp6.1.1, hp5.1.1, hll4], by rw [hp6.1.2, hp5.1.2, hel4], hm6⟩
                · exact hJmtf () m5 ⟨s5, hs5, by rw [heq5, hcore4], by rw [hp5.2.1, hws4],
                    by rw [hp5.2.2.1, hws24], by rw [hp5.1.1, hll4], by rw [hp5.1.2, hel4], hm5⟩
              · exact hJw _ _ ⟨s4, hlen4, hcore4, hws4, hws24, hll4, hel4, hm4⟩
            · exact hJw _ _ ⟨s4, hlen4, hcore4, hws4, hws24, hll4, hel4, hm4⟩
        · ml_lets; apply wp_call_of_spec; apply hDecay
          refine ⟨c, s4, R, rfl, hlen4, hm4, fun ⟨⟩ s5 m5 hcore5 hs5 hp5 hm5 => ?_⟩
          dsimp only [fullSafetySlice_mem, fullSafetySlice_coreProj,
            fullSafetySlice_safe] at hcore5 hs5 hp5 hm5
          have heq5 := @fullCoreState_agrees_with_scratch c s4 s5 hcore5
          have hcore5' : s5.core = { s.core with mrk := s2.core.mrk, min_clr_len := cnt } := by
            rw [heq5, hcore4]
          have hws5 : s5.scratch.work_stk1 = ws3 := by rw [hp5.2.1, hws4]
          have heq_st : FullState.mk
              { s.core with mrk := s5.core.mrk, min_clr_len := s5.core.min_clr_len }
              s5.scratch = s5 := by
            cases s5; dsimp only at hcore5' ⊢; congr 1; rw [hcore5']
          refine hQ s5.core.mrk s5.core.min_clr_len s5.scratch m5 (by rw [heq_st]; exact hs5) ?_
            ⟨by rw [hp5.1.1, hll4], by rw [hp5.1.2, hel4]⟩ (by rw [hp5.2.2.1, hws24])
            (by rw [heq_st]; exact hm5)
          rw [heq_st]; unfold Full.FullAnaMarksCov at hcov3 ⊢
          rw [hws5, hcore5', ← hcore2]; exact hcov3
    · ml_ld (load_full_stable (s := s2) hm2); ml_lets; ml_jnz
      refine ⟨fun _ => ?_, fun _ => hJsort _ _ ⟨s2.scratch.work_stk1, hwsl2, hcov2, hm2⟩⟩
      ml_lets; ml_jnz
      refine ⟨fun _ => ?_, fun _ => hJsort _ _ ⟨s2.scratch.work_stk1, hwsl2, hcov2, hm2⟩⟩
      ml_lets; apply wp_call_of_spec; apply hSortQs
      refine ⟨c, s2, R, rfl, hlen2,
        by rw [Arg.val_var, bv64_ofNat_toNat (by omega), hcv2]; exact hmcl2,
        fun k hk => ?_, hm2, ?_⟩
      · rw [Arg.val_var, bv64_ofNat_toNat (by omega)] at hk
        exact (hcov2.2.2.1 k hk).1
      · intro ws3 m3 hl3 hp3 hsuf3 _ hm3
        rw [Arg.val_var, bv64_ofNat_toNat (by omega)] at hp3 hsuf3
        exact hJsort _ _ ⟨ws3, hl3, anaMarksCov_perm hlen2 hcov2 hl3 hp3 hsuf3, hm3⟩
  · have htl_le0 := hlen.core_ok.tmp_len_le
    ml_lets; apply wp_call_of_spec; apply hDrAllow
    refine m6DrAllowSpec_of hlen hm fun r_dr => ?_
    ml_lets; ml_jnz
    refine ⟨fun _ => ?_, fun _ => by
      ml_lets; exact hJallow () m ⟨s, bumpAnaInv_init hlen hcov0, hm⟩⟩
    let tlen := min s.core.tmp_len s.core.cur_vars
    have htlen_le_tl : tlen ≤ s.core.tmp_len := Nat.min_le_left _ _
    have htlen_le_cv : tlen ≤ s.core.cur_vars := Nat.min_le_right _ _
    ml_ld (load_full_tmp_len hm); ml_lets
    refine wp_join_group (ts := [i64])
      (fun (tlv, ()) m1 => tlv.toNat = tlen ∧ m = m1)
      (fun Jtl (tlv, ()) m1 ⟨htlv, hm1⟩ => ?_) (fun Jtl hJtl => ?_)
    · rcases hm1 with rfl; rw [Blocks.get_here]; ml_lets
      refine wp_loop_inv
        (fun (i, ()) m1 => i.toNat ≤ tlen ∧ ∃ s1 : FullState,
          BumpAnaInv c s s1 saved ∧ (FullMem c s1 ⋆ R) m1)
        (fun (i, ()) _ => tlen - i.toNat) (fun Jloop hLoop => ?_)
        (fun Jloop (i, ()) m1 ⟨hi_le, s1, hinv1, hm1⟩ hLoop => ?_)
      · ml_lets; exact hLoop (0#64, ()) m ⟨by simp, s, bumpAnaInv_init hlen hcov0, hm⟩
      · have hinv1_pk := hinv1
        rcases hinv1 with ⟨hlen1, hcore1, hscr1, _, hcov1, _, _⟩
        have hcveq : s1.core.cur_vars = s.core.cur_vars := by rw [hcore1]
        have hmcl1 : s1.core.min_clr_len ≤ s.core.cur_vars := by rw [← hcveq]; exact hcov1.1
        have hteq : s1.core.tmp_len = s.core.tmp_len := by rw [hcore1]
        have hareq : s1.core.arena_len = s.core.arena_len := by rw [hcore1]
        have harl1 := hlen1.core_ok.arena_len_arr
        have hale1 := hlen1.core_ok.arena_len_le
        have htll1 := hlen1.core_ok.tmp_len_arr
        have htl_le1 := hlen1.core_ok.tmp_len_le
        have hrsnl1 := hlen1.core_ok.rsns_len
        have hlvll1 := hlen1.core_ok.lvl_len
        have hmrl1 := hlen1.core_ok.mrk_len
        have hwsl1 := hlen1.scratch_ok.work_stk1_len
        clear hcore1 hscr1 hcov1
        refine wp_join_group (ts := [])
          (fun _ m2 => ∃ s2 : FullState, BumpAnaInv c s s2 saved ∧ (FullMem c s2 ⋆ R) m2)
          (fun Jrb _ m2 ⟨s2, hinv2, hm2⟩ => ?_) (fun Jrb hJrb => ?_)
        · rw [Blocks.get_here]; ml_lets
          refine wp_join_group (ts := [])
            (fun _ m3 => ∃ s3 : FullState, BumpAnaInv c s s3 saved ∧ (FullMem c s3 ⋆ R) m3)
            (fun _ _ m3 ⟨s3, hinv3, hm3⟩ => by
              rw [Blocks.get_here]; ml_lets; exact hJallow () m3 ⟨s3, hinv3, hm3⟩)
            (fun JrbOut hJrbOut => ?_)
          ml_ld (load_full_min_clr_len (s := s2) hm2); ml_lets; ml_jnz
          refine ⟨fun _ => ?_, fun _ => hJrbOut () m2 ⟨s2, hinv2, hm2⟩⟩
          ml_lets
          refine wp_loop_inv
            (fun _ m3 => ∃ s3 : FullState, BumpAnaInv c s s3 saved ∧ (FullMem c s3 ⋆ R) m3)
            (fun _ m3 => ((loadVal m3 i64 (c.hdr + 272)).getD 0#64).toNat - saved)
            (fun Jw hJw => by ml_lets; exact hJw () m2 ⟨s2, hinv2, hm2⟩)
            (fun Jw () m3 ⟨s3, hinv3, hm3⟩ hJw => ?_)
          have hinv3_pk := hinv3
          rcases hinv3 with ⟨hlen3, hcore3, _, _, hcov3, _, _⟩
          have hcveq3 : s3.core.cur_vars = s.core.cur_vars := by rw [hcore3]
          have hmcl3 : s3.core.min_clr_len ≤ s.core.cur_vars := by
            rw [← hcveq3]; exact hcov3.1
          have hwsl3 := hlen3.scratch_ok.work_stk1_len
          have hmrl3 := hlen3.core_ok.mrk_len
          have hload3 : (loadVal m3 i64 (c.hdr + 272)).getD 0#64 =
              BitVec.ofNat 64 s3.core.min_clr_len := by
            rw [FullArenaTactics.load_full_min_clr_len hm3]; rfl
          rw [Blocks.get_here]; ml_ld (load_full_min_clr_len (s := s3) hm3); ml_lets; ml_jnz
          refine ⟨fun hsav_b => ?_, fun _ => hJrbOut () m3 ⟨s3, hinv3_pk, hm3⟩⟩
          have hsav_lt : saved < s3.core.min_clr_len := by
            have h1 := bv64_ult_toNat hsav_b
            rwa [bv64_ofNat_toNat (by omega), bv64_ofNat_toNat (by omega)] at h1
          obtain ⟨hrv_lt, hinv4⟩ := bumpAnaInv_rollback hinv3_pk hsav_lt
          ml_ld (load_full_min_clr_len (s := s3) hm3)
          ml_st m3a, hm3a := c0_store_full_min_clr_len (s := s3)
            (BitVec.ofNat 64 s3.core.min_clr_len - 1) hm3
          have hsub : (BitVec.ofNat 64 s3.core.min_clr_len - 1).toNat =
              s3.core.min_clr_len - 1 := by bv_omega
          rw [hsub] at hm3a
          let s3a : FullState :=
            { s3 with core := { s3.core with min_clr_len := s3.core.min_clr_len - 1 } }
          have hm3a' : (FullMem c s3a ⋆ R) m3a := hm3a
          have hws_idx :
              (BitVec.ofNat 64 (s3.core.min_clr_len - 1)).toNat < s3a.scratch.work_stk1.length := by
            rw [bv64_ofNat_toNat (by omega)]; dsimp only [s3a]; rw [hwsl3]; omega
          ml_ld (load_full_min_clr_len (s := s3a) hm3a')
          ml_ld (c0_load_full_work_stk1 (s := s3a)
            (i := BitVec.ofNat 64 (s3.core.min_clr_len - 1)) hws_idx hm3a')
          ml_lets
          refine wp_join_group (ts := [])
            (fun _ m4 => ∃ s4 : FullState, BumpAnaInv c s s4 saved ∧
              ((loadVal m4 i64 (c.hdr + 272)).getD 0#64).toNat - saved <
                ((loadVal m3 i64 (c.hdr + 272)).getD 0#64).toNat - saved ∧
              (FullMem c s4 ⋆ R) m4)
            (fun _ _ m4 ⟨s4, hinv4', hdec, hm4⟩ => by
              rw [Blocks.get_here]; ml_lets; exact hJw () m4 hdec ⟨s4, hinv4', hm4⟩)
            (fun Jstep hJstep => ?_)
          ml_lets; ml_jnz; refine ⟨fun hrv_b => ?_, fun hrv_no => ?_⟩
          · let rv32 := s3a.scratch.work_stk1[(BitVec.ofNat 64
                (s3.core.min_clr_len - 1)).toNat]'hws_idx
            have hrv_lt' : rv32.toNat < s3.core.cur_vars := by
              rw [hcveq3]; dsimp only [rv32, s3a]
              have hidx_eq : (BitVec.ofNat 64 (s3.core.min_clr_len - 1)).toNat =
                  s3.core.min_clr_len - 1 := bv64_ofNat_toNat (by omega)
              simpa only [hidx_eq, List.getElem?_eq_getElem (by rw [hwsl3]; omega :
                s3.core.min_clr_len - 1 < s3.scratch.work_stk1.length), Option.getD_some]
                using hrv_lt
            have hmrk_bd : (rv32.setWidth 64).toNat < s3a.core.mrk.length := by
              rw [bv_c0_zext32_64]; dsimp only [s3a]; rw [hmrl3]; omega
            ml_st m4, hm4 := c0_store_full_mrk (s := s3a)
              (i := rv32.setWidth 64) ((0 : BitVec 32).setWidth 8) hmrk_bd hm3a'
            rw [show (0 : BitVec 32).setWidth 8 = 0#8 from rfl, bv_c0_zext32_64] at hm4
            have hws_lt3 : s3.core.min_clr_len - 1 < s3.scratch.work_stk1.length := by
              rw [hwsl3]; omega
            have hrveq : (s3.scratch.work_stk1[s3.core.min_clr_len - 1]?.getD 0#32).toNat =
                rv32.toNat := by
              simp only [rv32, s3a, bv64_ofNat_toNat (by omega : s3.core.min_clr_len - 1 < 2 ^ 64)]
              rw [List.getElem?_eq_getElem hws_lt3, Option.getD_some]
            let s4 : FullState :=
              { core :=
                  { s3.core with
                    mrk := s3.core.mrk.set rv32.toNat 0#8
                    min_clr_len := s3.core.min_clr_len - 1 }
                scratch := s3.scratch }
            have hm4' : (FullMem c s4 ⋆ R) m4 := hm4
            have hinv4' : BumpAnaInv c s s4 saved := by
              simpa only [s4, hrveq] using hinv4
            have hdec : ((loadVal m4 i64 (c.hdr + 272)).getD 0#64).toNat - saved <
                ((loadVal m3 i64 (c.hdr + 272)).getD 0#64).toNat - saved := by
              rw [FullArenaTactics.load_full_min_clr_len hm4', hload3]
              dsimp only [Option.getD_some, s4]
              rw [bv64_ofNat_toNat (by omega), bv64_ofNat_toNat (by omega)]; omega
            ml_lets; exact hJstep () m4 ⟨s4, hinv4', hdec, hm4'⟩
          · exfalso
            have hnot := bv64_not_ult_toNat hrv_no
            simp only [bv64_ofNat_toNat (by omega : s.core.cur_vars < 2 ^ 64), bv_c0_zext32_64,
              bv64_ofNat_toNat (by omega : s3.core.min_clr_len - 1 < 2 ^ 64), s3a] at hnot
            have : (s3.scratch.work_stk1[s3.core.min_clr_len - 1]?.getD 0#32).toNat =
                (s3.scratch.work_stk1[s3.core.min_clr_len - 1]'(by rw [hwsl3]; omega)).toNat := by
              rw [List.getElem?_eq_getElem (by rw [hwsl3]; omega), Option.getD_some]
            omega
        · ml_lets; ml_jnz; refine ⟨fun hilt => ?_, fun _ => hJrb () m1 ⟨s1, hinv1_pk, hm1⟩⟩
          ml_ld (load_full_min_clr_len (s := s1) hm1); ml_lets; ml_jnz
          refine ⟨fun _ => ?_, fun _ => hJrb () m1 ⟨s1, hinv1_pk, hm1⟩⟩
          have hi_lt : i.toNat < tlen := by
            have h1 := bv64_ult_toNat hilt
            rwa [htlv] at h1
          have hi_tmp : i.toNat < s1.core.tmp.length := by rw [htll1]; omega
          ml_ld (c0_load_full_tmp (s := s1) (i := i) hi_tmp hm1); ml_lets
          refine wp_join_group (ts := [i32]) (fun (rsn, ()) m1' => m1' = m1)
            (fun Jr (rsn, ()) m1' hm1' => ?_) (fun Jr hJr => ?_)
          · subst m1'; rw [Blocks.get_here]; ml_lets
            refine wp_join_group (ts := [])
              (fun _ m2 => ∃ s2 : FullState, BumpAnaInv c s s2 saved ∧ (FullMem c s2 ⋆ R) m2)
              (fun Jstep _ m2 ⟨s2, hinv2, hm2⟩ => ?_) (fun Jstep hJstep => ?_)
            · rw [Blocks.get_here]; ml_lets
              exact hLoop (i + 1#64, ()) m2 (by dsimp only; bv_omega)
                ⟨by bv_omega, s2, hinv2, hm2⟩
            · refine wp_join_group (ts := []) (fun _ m' => m' = m1)
                (fun Jelse () m' hm' => ?_) (fun Jelse hJelse => ?_)
              · subst m'; rw [Blocks.get_here]; ml_lets
                refine wp_join_group (ts := [])
                  (fun _ m2 => ∃ s2 : FullState,
                    BumpAnaInv c s s2 saved ∧ (FullMem c s2 ⋆ R) m2)
                  (fun Js () m2 ⟨s2, hinv2, hm2⟩ => by
                    rw [Blocks.get_here]; ml_lets; exact hJstep () m2 ⟨s2, hinv2, hm2⟩)
                  (fun Js hJs => ?_)
                ml_lets; ml_jnz
                refine ⟨fun _ => ?_, fun _ => hJs () m1 ⟨s1, hinv1_pk, hm1⟩⟩
                ml_ld (load_full_arena_len (s := s1) hm1); ml_lets; ml_jnz
                refine ⟨fun hrsn3_le => ?_, fun _ => hJs () m1 ⟨s1, hinv1_pk, hm1⟩⟩
                have hrsn3 : rsn.toNat + 3 ≤ s1.core.arena_len := by
                  have h1 := bv64_ule_toNat hrsn3_le
                  rw [bv64_ofNat_toNat (by omega : s1.core.arena_len < 2 ^ 64)] at h1
                  revert h1; bv_omega
                have hrsn2_eq : (rsn.setWidth 64 + 2#64).toNat = rsn.toNat + 2 := by bv_omega
                have hrsn2_lt : (rsn.setWidth 64 + 2#64).toNat < s1.core.arena.length := by
                  rw [hrsn2_eq, harl1]; omega
                let sz := s1.core.arena[(rsn.setWidth 64 + 2#64).toNat]'hrsn2_lt
                ml_ld (c0_load_full_arena (s := s1) (i := rsn.setWidth 64 + 2#64) hrsn2_lt hm1)
                ml_lets
                refine wp_join_group (ts := [])
                  (fun _ m2 => ∃ s2 : FullState,
                    BumpAnaInv c s s2 saved ∧ (FullMem c s2 ⋆ R) m2)
                  (fun _ () m2 ⟨s2, hinv2, hm2⟩ => by
                    rw [Blocks.get_here]; ml_lets; exact hJs () m2 ⟨s2, hinv2, hm2⟩)
                  (fun Jsz hJsz => ?_)
                ml_lets; ml_jnz
                refine ⟨fun _ => ?_, fun _ => hJsz () m1 ⟨s1, hinv1_pk, hm1⟩⟩
                ml_ld (load_full_arena_len (s := s1) hm1); ml_lets; ml_jnz
                refine ⟨fun hrsn_sz_le => ?_, fun _ => hJsz () m1 ⟨s1, hinv1_pk, hm1⟩⟩
                have hrsn_sz : rsn.toNat + 3 + sz.toNat ≤ s1.core.arena_len := by
                  have hsz_lt := sz.isLt
                  have h1 := bv64_ule_toNat hrsn_sz_le
                  rw [bv64_ofNat_toNat (by omega : s1.core.arena_len < 2 ^ 64)] at h1
                  revert h1; dsimp only [sz]; bv_omega
                refine wp_loop_inv (ts := [i32])
                  (fun (j, ()) m2 => j.toNat ≤ sz.toNat ∧ ∃ s2 : FullState,
                    BumpAnaInv c s s2 saved ∧ (FullMem c s2 ⋆ R) m2)
                  (fun (j, ()) _ => sz.toNat - j.toNat) (fun Jj hJj => ?_)
                  (fun Jj (j, ()) m2 ⟨hjle, s2, hinv2, hm2⟩ hJj => ?_)
                · ml_lets; exact hJj (0#32, ()) m1 ⟨by simp, s1, hinv1_pk, hm1⟩
                · have hinv2_pk := hinv2
                  rcases hinv2 with ⟨hlen2, hcore2, hscr2, hsav2, hcov2, hmrk_p2, hana_p2⟩
                  have hcveq2 : s2.core.cur_vars = s.core.cur_vars := by rw [hcore2]
                  have hmcl2 : s2.core.min_clr_len ≤ s.core.cur_vars := by
                    rw [← hcveq2]; exact hcov2.1
                  have har2_eq : s2.core.arena_len = s1.core.arena_len := by rw [hcore2, hareq]
                  have harl2 := hlen2.core_ok.arena_len_arr
                  have hale2 := hlen2.core_ok.arena_len_le
                  have hlvll2 := hlen2.core_ok.lvl_len
                  have hmrl2 := hlen2.core_ok.mrk_len
                  have hwsl2 := hlen2.scratch_ok.work_stk1_len
                  clear hcore2 hscr2 hsav2 hcov2 hmrk_p2 hana_p2
                  rw [Blocks.get_here]; ml_lets; ml_jnz
                  refine ⟨fun hjlt => ?_, fun _ => hJsz () m2 ⟨s2, hinv2_pk, hm2⟩⟩
                  ml_ld (load_full_min_clr_len (s := s2) hm2); ml_lets; ml_jnz
                  refine ⟨fun _ => ?_, fun _ => hJsz () m2 ⟨s2, hinv2_pk, hm2⟩⟩
                  have hj_lt : j.toNat < sz.toNat := bv32_ult_toNat hjlt
                  have har_li : (rsn.setWidth 64 + 3#64 + j.setWidth 64).toNat <
                      s2.core.arena.length := by
                    have : (rsn.setWidth 64 + 3#64 + j.setWidth 64).toNat =
                        rsn.toNat + 3 + j.toNat := by bv_omega
                    rw [this, harl2]; omega
                  ml_ld (c0_load_full_arena (s := s2) (i := rsn.setWidth 64 + 3#64 + j.setWidth 64)
                    har_li hm2); ml_lets
                  let ov32 :=
                    (s2.core.arena[(rsn.setWidth 64 + 3#64 +
                      j.setWidth 64).toNat]'har_li) >>> (1 : Nat)
                  have hj1 : (j + 1#32).toNat = j.toNat + 1 := by
                    have hsz_lt := sz.isLt; bv_omega
                  refine wp_join_group (ts := [])
                    (fun _ m3 => ∃ s3 : FullState,
                      BumpAnaInv c s s3 saved ∧ (FullMem c s3 ⋆ R) m3)
                    (fun _ () m3 ⟨s3, hinv3, hm3⟩ => by
                      rw [Blocks.get_here]; ml_lets
                      exact hJj (j + 1#32, ()) m3 (by dsimp only; rw [hj1]; omega)
                        ⟨by rw [hj1]; omega, s3, hinv3, hm3⟩)
                    (fun Jj_step hJj_step => ?_)
                  ml_lets; ml_jnz
                  refine ⟨fun hov => ?_, fun _ => hJj_step () m2 ⟨s2, hinv2_pk, hm2⟩⟩
                  have hov_lt : ov32.toNat < s.core.cur_vars := by
                    have h1 := bv64_ult_toNat hov
                    rwa [bv64_ofNat_toNat (by omega : s.core.cur_vars < 2 ^ 64),
                      bv_c0_zext32_64] at h1
                  have hlvl_bd : (ov32.setWidth 64).toNat < s2.core.lvl.length := by
                    rw [bv_c0_zext32_64, hlvll2]; omega
                  have hmrk_bd : (ov32.setWidth 64).toNat < s2.core.mrk.length := by
                    rw [bv_c0_zext32_64, hmrl2]; omega
                  ml_ld (c0_load_full_lvl (s := s2) (i := ov32.setWidth 64) hlvl_bd hm2)
                  ml_lets; ml_jnz
                  refine ⟨fun _ => ?_, fun _ => hJj_step () m2 ⟨s2, hinv2_pk, hm2⟩⟩
                  ml_ld (c0_load_full_mrk (s := s2) (i := ov32.setWidth 64) hmrk_bd hm2)
                  ml_lets; ml_jnz
                  refine ⟨fun hmrk_eq => ?_, fun _ => hJj_step () m2 ⟨s2, hinv2_pk, hm2⟩⟩
                  have hmrk0 : s2.core.mrk[ov32.toNat]?.getD 0#8 = 0#8 := by
                    rw [List.getElem?_eq_getElem (by rw [hmrl2]; omega), Option.getD_some]
                    exact bv8_zext32_beq_zero hmrk_eq
                  ml_ld (load_full_min_clr_len (s := s2) hm2)
                  ml_lets; ml_jnz
                  refine ⟨fun hmcl => ?_, fun _ => hJj_step () m2 ⟨s2, hinv2_pk, hm2⟩⟩
                  have hmcl_lt : s2.core.min_clr_len < s.core.cur_vars := by
                    have h1 := bv64_ult_toNat hmcl
                    rwa [bv64_ofNat_toNat (by omega : s2.core.min_clr_len < 2 ^ 64),
                      bv64_ofNat_toNat (by omega : s.core.cur_vars < 2 ^ 64)] at h1
                  ml_bump_push c s2 hinv2_pk hm2 ov32 hov_lt hmrk0 hmcl_lt hmrk_bd hwsl2 hJj_step
              · ml_lets; ml_jnz; refine ⟨fun _ => ?_, fun _ => hJelse () m1 rfl⟩
                ml_lets; ml_jnz; refine ⟨fun _ => ?_, fun _ => hJelse () m1 rfl⟩
                refine wp_join_group (ts := [])
                  (fun _ m2 => ∃ s2 : FullState,
                    BumpAnaInv c s s2 saved ∧ (FullMem c s2 ⋆ R) m2)
                  (fun _ () m2 ⟨s2, hinv2, hm2⟩ => by
                    rw [Blocks.get_here]; ml_lets; exact hJstep () m2 ⟨s2, hinv2, hm2⟩)
                  (fun Jbin hJbin => ?_)
                let ov32 := (rsn &&& 0x7FFFFFFF#32) >>> (1 : Nat)
                ml_lets; ml_jnz
                refine ⟨fun hov => ?_, fun _ => hJbin () m1 ⟨s1, hinv1_pk, hm1⟩⟩
                have hov_lt : ov32.toNat < s.core.cur_vars := by
                  have h1 := bv64_ult_toNat hov
                  rwa [bv64_ofNat_toNat (by omega : s.core.cur_vars < 2 ^ 64),
                    bv_c0_zext32_64] at h1
                have hov_lvl : (ov32.setWidth 64).toNat < s1.core.lvl.length := by
                  rw [bv_c0_zext32_64, hlvll1]; omega
                have hov_mrk : (ov32.setWidth 64).toNat < s1.core.mrk.length := by
                  rw [bv_c0_zext32_64, hmrl1]; omega
                ml_ld (c0_load_full_lvl (s := s1) (i := ov32.setWidth 64) hov_lvl hm1)
                ml_lets; ml_jnz
                refine ⟨fun _ => ?_, fun _ => hJbin () m1 ⟨s1, hinv1_pk, hm1⟩⟩
                ml_ld (c0_load_full_mrk (s := s1) (i := ov32.setWidth 64) hov_mrk hm1)
                ml_lets; ml_jnz
                refine ⟨fun hmrk_eq => ?_, fun _ => hJbin () m1 ⟨s1, hinv1_pk, hm1⟩⟩
                have hmrk0 : s1.core.mrk[ov32.toNat]?.getD 0#8 = 0#8 := by
                  rw [List.getElem?_eq_getElem (by rw [hmrl1]; omega), Option.getD_some]
                  exact bv8_zext32_beq_zero hmrk_eq
                ml_ld (load_full_min_clr_len (s := s1) hm1)
                ml_lets; ml_jnz
                refine ⟨fun hmcl => ?_, fun _ => hJbin () m1 ⟨s1, hinv1_pk, hm1⟩⟩
                have hmcl_lt : s1.core.min_clr_len < s.core.cur_vars := by
                  have h1 := bv64_ult_toNat hmcl
                  rwa [bv64_ofNat_toNat (by omega : s1.core.min_clr_len < 2 ^ 64),
                    bv64_ofNat_toNat (by omega : s.core.cur_vars < 2 ^ 64)] at h1
                ml_bump_push c s1 hinv1_pk hm1 ov32 hov_lt hmrk0 hmcl_lt hov_mrk hwsl1 hJbin
          · ml_lets; ml_jnz
            refine ⟨fun huv => ?_, fun _ => by ml_lets; exact hJr (0xFFFFFFFF#32, ()) m1 rfl⟩
            have huv_rsn : ((s1.core.tmp[i.toNat]'hi_tmp >>> (1 : Nat)).setWidth 64).toNat <
                s1.core.rsns.length := by
              have h1 := bv64_ult_toNat huv
              rw [bv64_ofNat_toNat (by omega : s.core.cur_vars < 2 ^ 64)] at h1
              rw [hrsnl1]; omega
            ml_ld (c0_load_full_rsns (s := s1)
              (i := (s1.core.tmp[i.toNat]'hi_tmp >>> (1 : Nat)).setWidth 64) huv_rsn hm1)
            ml_lets; exact hJr (_, ()) m1 rfl
    · ml_lets; ml_jnz
      · refine ⟨fun hlt => ?_, fun hle => ?_⟩
        · have h1 := bv64_ult_toNat hlt
          rw [bv64_ofNat_toNat (by omega), bv64_ofNat_toNat (by omega)] at h1
          ml_lets; exact hJtl (_, ()) m
            ⟨by rw [Arg.val_var, bv64_ofNat_toNat (by omega)]
                exact (Nat.min_eq_right (le_of_lt h1)).symm, rfl⟩
        · have h1 := bv64_not_ult_toNat hle
          rw [bv64_ofNat_toNat (by omega), bv64_ofNat_toNat (by omega)] at h1
          ml_lets; exact hJtl (_, ()) m
            ⟨by rw [Arg.val_var, bv64_ofNat_toNat (by omega)]
                exact (Nat.min_eq_left h1).symm, rfl⟩

/-! ## 5. `full_restore_bump_ana_m6` `Func.wp` proof -/

theorem full_restore_bump_ana_m6_wp (Γ : Env)
    (hBumpAna : ∀ a m Q X, Full.fullBumpAnalyzedSpec a m Q X →
      Γ "full_bump_analyzed_m6" [i64] [] a m Q X)
    (hClearAna : ∀ a m Q X, Full.fullClearAnaSpec a m Q X →
      Γ "full_clear_ana" [i64] [] a m Q X) :
    ∀ a m Q X, m6RestoreBumpAnaSpec a m Q X →
      Func.wp Γ full_restore_bump_ana_m6_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hmrk0, hm, hQ⟩
  have hmax : c.max_vars < 2 * dimacsBound := c.hmaxv
  unfold dimacsBound at hmax
  have hcv_le := hlen.core_ok.cur_vars_le
  have hmrl := hlen.core_ok.mrk_len
  have hwsl := hlen.scratch_ok.work_stk1_len
  have htll := hlen.core_ok.tmp_len_arr
  have hlvll := hlen.core_ok.lvl_len
  c0_hsteps_nogrp
  · exact hQ s.core.mrk s.core.min_clr_len s.scratch m hlen hmrk0
      (fun h0 => absurd h0 hc) (fun _ => rfl) ⟨rfl, rfl⟩ rfl hm
  · have hprob0 : s.core.probing = 0#64 := hc
    let ana_n := min s.scratch.res_sz.toNat s.core.cur_vars
    have han_le : ana_n ≤ s.core.cur_vars := Nat.min_le_right _ _
    let CovInv : Nat → FullState → Prop := fun w s1 =>
      s1.LengthsOk c ∧
      s1.core = { s.core with mrk := s1.core.mrk } ∧
      s1.scratch = { s.scratch with work_stk1 := s1.scratch.work_stk1 } ∧
      w ≤ s.core.cur_vars ∧
      ((s1.scratch.work_stk1.take w).map BitVec.toNat).Nodup ∧
      (∀ i < w, (s1.scratch.work_stk1[i]?.getD 0#32).toNat < s.core.cur_vars ∧
        s1.core.mrk[(s1.scratch.work_stk1[i]?.getD 0#32).toNat]?.getD 0#8 ≠ 0#8) ∧
      (∀ v < c.max_vars, s1.core.mrk[v]?.getD 0#8 ≠ 0#8 →
        ∃ i < w, (s1.scratch.work_stk1[i]?.getD 0#32).toNat = v)
    refine wp_join_group (ts := [i64])
      (fun (anv, ()) m1 => anv.toNat = ana_n ∧ m = m1)
      (fun Jan (anv, ()) m1 ⟨han_eq, hm1⟩ => ?_) (fun Jan hJan => ?_)
    · rcases hm1 with rfl; rw [Blocks.get_here]; dsimp only
      c0_hsteps_nogrp
      refine wp_loop_inv (ts := [i64, i64])
        (fun (w, k, ()) m1 => w.toNat ≤ k.toNat ∧ k.toNat ≤ ana_n ∧ ∃ s1 : FullState,
          CovInv w.toNat s1 ∧ (FullMem c s1 ⋆ R) m1)
        (fun (_, k, ()) _ => ana_n - k.toNat) (fun J1 hJ1 => ?_)
        (fun J1 (w, k, ()) m1 ⟨hwk, hkn, s1, hci1, hm1⟩ hJ1 => ?_)
      · c0_hsteps
        refine hJ1 (0#64, 0#64, ()) m ⟨by simp, by simp, s, ⟨hlen, rfl, rfl, Nat.zero_le _,
          by simp, fun _ hi => absurd hi (Nat.not_lt_zero _),
          fun v hv hnz => absurd (hmrk0 v hv) hnz⟩, hm⟩
      · have hci1_pk := hci1
        rcases hci1 with ⟨hlen1, hcore1, hscr1, hw_cv, hnd1, hel1, hcv1⟩
        have hmrl1 := hlen1.core_ok.mrk_len
        have hwsl1 := hlen1.scratch_ok.work_stk1_len
        c0_hsteps_nogrp
        · have hk_lt : k.toNat < ana_n := by c0_bound
          have hk_ws : k.toNat < s1.scratch.work_stk1.length := by rw [hwsl1]; omega
          let av := s1.scratch.work_stk1[k.toNat]'hk_ws
          refine wp_join_group (ts := [i64])
            (fun (w1, ()) m1' => w1.toNat ≤ k.toNat + 1 ∧ k.toNat + 1 ≤ ana_n ∧
              ∃ s1' : FullState, CovInv w1.toNat s1' ∧ (FullMem c s1' ⋆ R) m1')
            (fun Jk1 (w1, ()) m1' ⟨hwk1, hk1n, s1', hci1', hm1'⟩ => by
              c0_hsteps
              exact hJ1 (w1, k + 1#64, ()) m1' (by dsimp only; bv_omega)
                ⟨by bv_omega, by bv_omega, s1', hci1', hm1'⟩)
            (fun Jk1 hJk1 => ?_)
          c0_hsteps_nogrp
          · have hav_lt : av.toNat < s.core.cur_vars := by dsimp only [av]; c0_bound
            have hmrk_av : s1.core.mrk[av.toNat]?.getD 0#8 = 0#8 := by
              rw [List.getElem?_eq_getElem (by rw [hmrl1]; omega), Option.getD_some]
              simpa only [av] using hc
            have hw_lt_cv : w.toNat < s.core.cur_vars := by omega
            let s2 : FullState :=
              { core := { s1.core with mrk := s1.core.mrk.set av.toNat 1#8 }
                scratch := { s1.scratch with work_stk1 := s1.scratch.work_stk1.set w.toNat av } }
            have hm2' : (FullMem c s2 ⋆ R) m := by
              simpa only [s2, av, bv_c0_zext32_64] using hm
            have hci2 : CovInv (w + 1#64).toNat s2 := by
              have hw1 : (w + 1#64).toNat = w.toNat + 1 := by bv_omega
              have hws_len : w.toNat < s1.scratch.work_stk1.length := by rw [hwsl1]; omega
              rw [hw1]
              refine ⟨⟨{ hlen1.core_ok with mrk_len := by simp [s2, hmrl1] },
                  { hlen1.scratch_ok with work_stk1_len := by simp [s2, hwsl1] }⟩,
                by dsimp only [s2]; rw [hcore1], by dsimp only [s2]; rw [hscr1], by omega, ?_,
                fun i hi => ?_, fun v hv hnz => ?_⟩
              · exact nodup_map_take_append hws_len hnd1 fun j hj he =>
                  (hel1 j hj).2 (by rw [he]; exact hmrk_av)
              · rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hlt | rfl
                · rw [List.getElem?_set_ne (by omega)]
                  have hne : (s1.scratch.work_stk1[i]?.getD 0#32).toNat ≠ av.toNat := fun he =>
                    (hel1 i hlt).2 (he ▸ hmrk_av)
                  exact ⟨(hel1 i hlt).1,
                    by rw [List.getElem?_set_ne (Ne.symm hne)]; exact (hel1 i hlt).2⟩
                · rw [List.getElem?_set_self hws_len, Option.getD_some,
                    List.getElem?_set_self (by rw [hmrl1]; omega), Option.getD_some]
                  exact ⟨hav_lt, by decide⟩
              · by_cases hveq : v = av.toNat
                · subst v; refine ⟨w.toNat, by omega, ?_⟩
                  dsimp only [s2]; rw [List.getElem?_set_self hws_len, Option.getD_some]
                · have hnz1 : s1.core.mrk[v]?.getD 0#8 ≠ 0#8 := by
                    dsimp only [s2] at hnz; rwa [List.getElem?_set_ne (Ne.symm hveq)] at hnz
                  obtain ⟨i, hi, hieq⟩ := hcv1 v hv hnz1
                  exact ⟨i, by omega, by
                    dsimp only [s2]; rw [List.getElem?_set_ne (by omega)]; exact hieq⟩
            exact hJk1 (w + 1#64, ()) m ⟨by bv_omega, by omega, s2, hci2, hm2'⟩
          · exact hJk1 (w, ()) m1 ⟨by omega, by omega, s1, hci1_pk, hm1⟩
          · exact hJk1 (w, ()) m1 ⟨by omega, by omega, s1, hci1_pk, hm1⟩
        · c0_hsteps_nogrp
          refine wp_join_group (ts := [i64])
            (fun (w2, ()) m2 => w2.toNat ≤ s.core.cur_vars ∧
              ∃ s2 : FullState, CovInv w2.toNat s2 ∧ (FullMem c s2 ⋆ R) m2)
            (fun Jtmp (w2, ()) m2 ⟨hw2_cv, s2, hci2, hm2⟩ => ?_)
            (fun Jtmp hJtmp => ?_)
          · rw [Blocks.get_here]; dsimp only
            have hci2_pk := hci2
            rcases hci2 with ⟨hlen2, hcore2, hscr2, _, hnd2, hel2, hcv2⟩
            let s3 : FullState :=
              { core := { s2.core with min_clr_len := w2.toNat }, scratch := s2.scratch }
            have hlen3 : s3.LengthsOk c :=
              ⟨{ hlen2.core_ok with
                  min_clr_len_le := by dsimp only [s3]; omega },
                hlen2.scratch_ok⟩
            have hcov3 : FullAnaMarksCov c s3 :=
              ⟨by dsimp only [s3]; rw [hcore2]; exact hw2_cv, hnd2,
                fun i hi => by dsimp only [s3]; rw [hcore2]; exact hel2 i hi,
                fun v hv hnz => by dsimp only [s3] at hnz ⊢; exact hcv2 v hv hnz⟩
            have hcore3_mrk :
                s3.core = { s.core with mrk := s3.core.mrk, min_clr_len := w2.toNat } :=
              by dsimp only [s3]; rw [hcore2]
            c0_hsteps_nogrp
            have hm3 : (FullMem c s3 ⋆ R) m := by
              simpa only [s3, bv64_ofNat_toNat (by omega : w2.toNat < 2 ^ 64)] using hm
            refine wp_join_group (ts := []) (fun _ m_end => Q () m_end)
              (fun _ _ m_end hq => by c0_hsteps; exact hq) (fun Jend hJend => ?_)
            c0_hsteps_nogrp
            · c0_call hBumpAna
              refine ⟨c, s3, R, rfl, hlen3, hcov3, hm3,
                fun mrk4 mcl4 sc4 m4 hlen4 hcov4 hpres4 hws24 hm4 => ?_⟩
              dsimp only at hlen4 hcov4 hpres4 hws24 hm4
              let s4 : FullState :=
                { core := { s3.core with mrk := mrk4, min_clr_len := mcl4 }, scratch := sc4 }
              c0_call hClearAna
              refine ⟨c, s4, R, rfl, hlen4, hm4, fun mrk5 m5 hml5 _ _ hclr5 hm5 => ?_⟩
              have hmrk5 : ∀ v < c.max_vars, mrk5[v]?.getD 0#8 = 0#8 := hclr5 hcov4
              let s5 : FullState :=
                { s4 with core := { s4.core with mrk := mrk5, min_clr_len := 0 } }
              have hcore5 : s5.core = { s.core with mrk := mrk5, min_clr_len := 0 } := by
                dsimp only [s5, s4]; rw [hcore3_mrk]
              have hlen5 : s5.LengthsOk c :=
                ⟨{ hlen4.core_ok with
                    mrk_len := hml5
                    min_clr_len_le := by dsimp only [s5]; omega },
                  hlen4.scratch_ok⟩
              have hpres5 : FullExtScratchPres s s5 :=
                ⟨by dsimp only [s5]; rw [hpres4.1]; dsimp only [s3]; rw [hscr2],
                 by dsimp only [s5]; rw [hpres4.2]; dsimp only [s3]; rw [hscr2]⟩
              have hws25 : s5.scratch.work_stk2 = s.scratch.work_stk2 := by
                dsimp only [s5]; rw [hws24]; dsimp only [s3]; rw [hscr2]
              let s5_0 : FullState :=
                FullState.mk { s.core with mrk := mrk5, min_clr_len := 0 } sc4
              have hs5_eq : s5_0 = s5 :=
                congrArg (FullState.mk · sc4) hcore5.symm
              have hlen5_0 : s5_0.LengthsOk c := by rw [hs5_eq]; exact hlen5
              have hpres5_0 : FullExtScratchPres s s5_0 := by rw [hs5_eq]; exact hpres5
              have hm5_0 : (FullMem c s5_0 ⋆ R) m5 := by rw [hs5_eq]; exact hm5
              exact hJend () m5 (hQ mrk5 0 sc4 m5 hlen5_0
                hmrk5 (fun _ => rfl) (fun hne => absurd hprob0 hne)
                hpres5_0 hws25 hm5_0)
            · have hw2_0 : w2.toNat = 0 := by c0_bound
              have hmrk3 : ∀ v < c.max_vars, s3.core.mrk[v]?.getD 0#8 = 0#8 := by
                intro v hv
                exact Classical.byContradiction fun hnz => by
                  obtain ⟨i, hi, _⟩ := hcov3.2.2.2 v hv hnz
                  dsimp only [s3] at hi; omega
              have hcore3_0 : s3.core = { s.core with mrk := s3.core.mrk, min_clr_len := 0 } := by
                rw [← hw2_0]; exact hcore3_mrk
              let s3_0 : FullState :=
                FullState.mk { s.core with mrk := s3.core.mrk, min_clr_len := 0 } s3.scratch
              have hs3_eq : s3_0 = s3 :=
                congrArg (FullState.mk · s3.scratch) hcore3_0.symm
              have hlen3_0 : s3_0.LengthsOk c := by rw [hs3_eq]; exact hlen3
              have hm3_0 : (FullMem c s3_0 ⋆ R) m := by rw [hs3_eq]; exact hm3
              have hpres3_0 : FullExtScratchPres s s3_0 :=
                ⟨by dsimp only [s3_0, s3]; rw [hscr2], by dsimp only [s3_0, s3]; rw [hscr2]⟩
              have hws23_0 : s3_0.scratch.work_stk2 = s.scratch.work_stk2 := by
                dsimp only [s3_0, s3]; rw [hscr2]
              exact hJend () m (hQ s3.core.mrk 0 s3.scratch m hlen3_0 hmrk3 (fun _ => rfl)
                (fun hne => absurd hprob0 hne) hpres3_0 hws23_0 hm3_0)
          · c0_hsteps_nogrp
            · have htl_le1 := hlen1.core_ok.tmp_len_le
              have hcv_le1 := hlen1.core_ok.cur_vars_le
              have htlen_cv : s.core.tmp_len ≤ s.core.cur_vars := by
                have h1 : s1.core.tmp_len ≤ s.core.cur_vars := by c0_bound
                rwa [hcore1] at h1
              refine wp_loop_inv (ts := [i64, i64])
                (fun (w2, ti, ()) m2 => w2.toNat ≤ s.core.cur_vars ∧ ti.toNat ≤ s.core.tmp_len ∧
                  ∃ s2 : FullState, CovInv w2.toNat s2 ∧ (FullMem c s2 ⋆ R) m2)
                (fun (_, ti, ()) _ => s.core.tmp_len - ti.toNat)
                (fun J2 hJ2 => hJ2 (w, 0#64, ()) m1 ⟨hw_cv, by simp, s1, hci1_pk, hm1⟩)
                (fun J2 (w2, ti, ()) m2 ⟨hw2_cv, hti_le, s2, hci2, hm2⟩ hJ2 => ?_)
              have hci2_pk := hci2
              rcases hci2 with ⟨hlen2, hcore2, hscr2, _, hnd2, hel2, hcv2⟩
              have hmrl2 := hlen2.core_ok.mrk_len
              have hwsl2 := hlen2.scratch_ok.work_stk1_len
              have htll2 := hlen2.core_ok.tmp_len_arr
              have htl_le2 := hlen2.core_ok.tmp_len_le
              have hlvll2 := hlen2.core_ok.lvl_len
              c0_hsteps_nogrp
              · have hti_lt : ti.toNat < s.core.tmp_len := by
                  have h1 : ti.toNat < s1.core.tmp_len := by c0_bound
                  rwa [hcore1] at h1
                have hti_tmp : ti.toNat < s2.core.tmp.length := by
                  rw [htll2]; have := htl_le2; rw [hcore2] at this; omega
                let tv := (s2.core.tmp[ti.toNat]'hti_tmp) >>> (1 : Nat)
                refine wp_join_group (ts := [i64])
                  (fun (w3, ()) m3 => w3.toNat ≤ s.core.cur_vars ∧
                    ∃ s3 : FullState, CovInv w3.toNat s3 ∧ (FullMem c s3 ⋆ R) m3)
                  (fun Jt1 (w3, ()) m3 ⟨hw3_cv, s3, hci3, hm3⟩ => by
                    c0_hsteps
                    exact hJ2 (w3, ti + 1#64, ()) m3 (by dsimp only; bv_omega)
                      ⟨hw3_cv, by bv_omega, s3, hci3, hm3⟩)
                  (fun Jt1 hJt1 => ?_)
                c0_hsteps_nogrp
                · have htv_lt : tv.toNat < s.core.cur_vars := by dsimp only [tv]; c0_bound
                  have hmrk_tv : s2.core.mrk[tv.toNat]?.getD 0#8 = 0#8 := by
                    have htv_to : tv.toNat = (s2.core.tmp[ti.toNat]'hti_tmp).toNat / 2 := by
                      dsimp only [tv]
                      rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.pow_one]
                    rw [List.getElem?_eq_getElem (by rw [hmrl2]; omega), Option.getD_some]
                    have hc_mrk :
                        s2.core.mrk[(s2.core.tmp[ti.toNat]'hti_tmp).toNat / 2]'(by
                          rw [← htv_to, hmrl2]; omega) = 0#8 := by
                      assumption
                    simpa only [← htv_to] using hc_mrk
                  have hw2_lt_cv : w2.toNat < s.core.cur_vars := by c0_bound
                  let s3 : FullState :=
                    { core := { s2.core with mrk := s2.core.mrk.set tv.toNat 1#8 }
                      scratch := { s2.scratch with
                        work_stk1 := s2.scratch.work_stk1.set w2.toNat tv } }
                  have hm3' : (FullMem c s3 ⋆ R) m := by
                    simpa only [s3, tv, bv_c0_zext32_64] using hm
                  have hci3 : CovInv (w2 + 1#64).toNat s3 := by
                    have hw1 : (w2 + 1#64).toNat = w2.toNat + 1 := by bv_omega
                    have hws_len : w2.toNat < s2.scratch.work_stk1.length := by rw [hwsl2]; omega
                    rw [hw1]
                    refine ⟨⟨{ hlen2.core_ok with mrk_len := by simp [s3, hmrl2] },
                        { hlen2.scratch_ok with work_stk1_len := by simp [s3, hwsl2] }⟩,
                      by dsimp only [s3]; rw [hcore2], by dsimp only [s3]; rw [hscr2], by omega, ?_,
                      fun i hi => ?_, fun v hv hnz => ?_⟩
                    · exact nodup_map_take_append hws_len hnd2 fun j hj he =>
                        (hel2 j hj).2 (by rw [he]; exact hmrk_tv)
                    · rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hlt | rfl
                      · rw [List.getElem?_set_ne (by omega)]
                        have hne : (s2.scratch.work_stk1[i]?.getD 0#32).toNat ≠ tv.toNat :=
                          fun he => (hel2 i hlt).2 (he ▸ hmrk_tv)
                        exact ⟨(hel2 i hlt).1,
                          by rw [List.getElem?_set_ne (Ne.symm hne)]; exact (hel2 i hlt).2⟩
                      · rw [List.getElem?_set_self hws_len, Option.getD_some,
                          List.getElem?_set_self (by rw [hmrl2]; omega), Option.getD_some]
                        exact ⟨htv_lt, by decide⟩
                    · by_cases hveq : v = tv.toNat
                      · subst v; refine ⟨w2.toNat, by omega, ?_⟩
                        dsimp only [s3]; rw [List.getElem?_set_self hws_len, Option.getD_some]
                      · have hnz2 : s2.core.mrk[v]?.getD 0#8 ≠ 0#8 := by
                          dsimp only [s3] at hnz; rwa [List.getElem?_set_ne (Ne.symm hveq)] at hnz
                        obtain ⟨i, hi, hieq⟩ := hcv2 v hv hnz2
                        exact ⟨i, by omega, by
                          dsimp only [s3]; rw [List.getElem?_set_ne (by omega)]; exact hieq⟩
                  exact hJt1 (w2 + 1#64, ()) m ⟨by bv_omega, s3, hci3, hm3'⟩
                · exact hJt1 (w2, ()) m2 ⟨hw2_cv, s2, hci2_pk, hm2⟩
                · exact hJt1 (w2, ()) m2 ⟨hw2_cv, s2, hci2_pk, hm2⟩
                · exact hJt1 (w2, ()) m2 ⟨hw2_cv, s2, hci2_pk, hm2⟩
                · exact hJt1 (w2, ()) m2 ⟨hw2_cv, s2, hci2_pk, hm2⟩
              · exact hJtmp (w2, ()) m2 ⟨hw2_cv, s2, hci2_pk, hm2⟩
            · exact hJtmp (w, ()) m1 ⟨hw_cv, s1, hci1_pk, hm1⟩
    · c0_hsteps
      · have hgt : s.core.cur_vars < s.scratch.res_sz.toNat := by c0_bound
        exact hJan (_, ()) m
          ⟨by rw [bv64_ofNat_toNat (by omega)]; exact (Nat.min_eq_right (le_of_lt hgt)).symm, rfl⟩
      · have hle : s.scratch.res_sz.toNat ≤ s.core.cur_vars := by c0_bound
        exact hJan (_, ()) m ⟨(Nat.min_eq_left hle).symm, rfl⟩
