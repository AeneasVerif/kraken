module

public import LeanQbe.T.Examples.Kissat.FullDefSweepLemmas1
public import LeanQbe.T.Examples.Kissat.FullBveVarLemmas1
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat `D-Full` Gate Mining & Dense Congruence `Func.wp` Proofs (`Part 2`)

Proves parametric `(Γ : Env)` `Func.wp` contracts for `4` definition-mining and
ticks-bounded congruence functions in `FullDefSweep`:
1. `full_bve_mark_and_wp`
2. `full_bve_gates_wp`
3. `full_cong_extract_wp`
4. `full_congruence_dense_wp`
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullDefSweep

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open Kraken.Bedrock2.Test
open FullCongSpecs FullCongHelpers
open scoped FullArenaTactics FullCongTactics FullDefSweepTactics

/-! ## 1. Pure Helpers for `mark_and`, `find_definition`, and `bve_gates` -/

private theorem fullLitMark_eq_of_zero_ext {lm0 lm : List (BitVec 8)} {n : Nat}
    (h0 : lm0.length = n) (h1 : lm.length = n)
    (hz0 : ∀ l < n, lm0[l]?.getD 0#8 = 0#8)
    (hz1 : ∀ l < n, lm[l]? = some 0#8) : lm = lm0 := by
  apply List.ext_getElem (by omega)
  intro l hl1 hl2
  have ha := hz1 l (by omega)
  have hb := hz0 l (by omega)
  rw [List.getElem?_eq_getElem hl2, Option.getD_some] at hb
  rw [List.getElem?_eq_getElem hl1] at ha
  exact (Option.some.inj ha).trans hb.symm

private theorem litMark_set_agree_out {lm0 : List (BitVec 8)} {ar : List (BitVec 32)}
    {cr i n : Nat} {v : BitVec 8}
    (hagree : ∀ l < n, (∀ j < i, (ar[cr + 3 + j]?.getD 0#32).toNat ^^^ 1 ≠ l) →
      lm0[l]? = some 0#8)
    (hi : cr + 3 + i < ar.length) :
    let idx := ((ar[cr + 3 + i]'hi ^^^ 1#32)).toNat
    ∀ l < n, (∀ j < i + 1, (ar[cr + 3 + j]?.getD 0#32).toNat ^^^ 1 ≠ l) →
      (lm0.set idx v)[l]? = some 0#8 := by
  intro idx l hl hnone
  have hne : idx ≠ l := by
    have h0 := hnone i (Nat.lt_succ_self i)
    rw [List.getElem?_eq_getElem hi, Option.getD_some] at h0
    exact h0
  rw [List.getElem?_set_ne hne]
  exact hagree l hl fun j hj => hnone j (Nat.lt_succ_of_lt hj)

private theorem litMark_clear_cov {lm : List (BitVec 8)} {ar : List (BitVec 32)}
    {cr sz i n : Nat} (hi_lt : cr + 3 + i < ar.length)
    (hidx_lt : ((ar[cr + 3 + i]'hi_lt ^^^ 1#32)).toNat < n)
    (hml : lm.length = n)
    (hcov : ∀ l < n,
      ((∃ j < i, (ar[cr + 3 + j]?.getD 0#32).toNat ^^^ 1 = l) ∨
       (∀ j < sz, (ar[cr + 3 + j]?.getD 0#32).toNat ^^^ 1 ≠ l)) → lm[l]? = some 0#8) :
    let idx := ((ar[cr + 3 + i]'hi_lt ^^^ 1#32)).toNat
    ∀ l < n,
      ((∃ j < i + 1, (ar[cr + 3 + j]?.getD 0#32).toNat ^^^ 1 = l) ∨
       (∀ j < sz, (ar[cr + 3 + j]?.getD 0#32).toNat ^^^ 1 ≠ l)) →
      (lm.set idx 0#8)[l]? = some 0#8 := by
  intro idx l hl hc
  by_cases heq : l = idx
  · subst heq; rw [List.getElem?_set_self (by omega)]
  · rw [List.getElem?_set_ne (Ne.symm heq)]
    refine hcov l hl ?_
    rcases hc with ⟨j, hj, hjl⟩ | hnone
    · left
      have hji : j ≠ i := by
        rintro rfl; apply heq; rw [← hjl, List.getElem?_eq_getElem hi_lt, Option.getD_some]; rfl
      exact ⟨j, by omega, hjl⟩
    · exact Or.inr hnone

private theorem nodup_of_map_div2 {xs : List Nat} (h : (xs.map (· / 2)).Nodup) : xs.Nodup := by
  induction xs with
  | nil => exact List.nodup_nil
  | cons x xs ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at h ⊢
    exact ⟨fun hx => h.1 ⟨x, hx, rfl⟩, ih h.2⟩

theorem nat_xor1_cancel (x : Nat) : (x ^^^ 1) ^^^ 1 = x := by
  rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

private theorem countP_inc_unique {xs : List Nat} (hnd : xs.Nodup) {x : Nat} (hx : x ∈ xs)
    (p q : Nat → Bool) (hpx : p x = false) (hqx : q x = true)
    (hother : ∀ y ∈ xs, y ≠ x → q y = p y) :
    xs.countP q = xs.countP p + 1 := by
  induction xs with
  | nil => cases hx
  | cons a xs ih =>
    rw [List.nodup_cons] at hnd
    cases hx with
    | head =>
      have hcongr : xs.countP q = xs.countP p := by
        refine List.countP_congr fun y hy => ?_
        have hne : y ≠ x := fun h => hnd.1 (h ▸ hy)
        rw [hother y (List.mem_cons_of_mem _ hy) hne]
      simp [hpx, hqx, hcongr]
    | tail _ hmem =>
      have ha : a ≠ x := fun h => hnd.1 (h ▸ hmem)
      have heqa : q a = p a := hother a (List.mem_cons_self ..) ha
      have ih' := ih hnd.2 hmem fun y hy hne => hother y (List.mem_cons_of_mem _ hy) hne
      cases hpa : p a <;> simp [heqa, hpa, ih'] <;> omega

private theorem forall_of_length_le_countP {α : Type} {xs : List α} {p : α → Bool}
    (h : xs.length ≤ xs.countP p) : ∀ x ∈ xs, p x = true := by
  induction xs with
  | nil => intro x hx; cases hx
  | cons a xs ih =>
    simp only [List.length_cons, List.countP_cons] at h
    have hle := List.countP_le_length (l := xs) (p := p)
    cases hpa : p a with
    | false => simp [hpa] at h; omega
    | true =>
      simp only [hpa, ↓reduceIte] at h
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hmem
      · exact hpa
      · exact ih (by omega) x hmem

theorem bv64_mask_split_32 (x : BitVec 64) :
    (x.setWidth 32).setWidth 64 ||| (((x >>> 32).setWidth 32).setWidth 64 <<< 32) = x := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, hi, decide_true, Bool.true_and]
  by_cases h32 : i < 32
  · simp [h32]
  · have hlt : i - 32 < 32 := by omega
    have hlt64 : i - 32 < 64 := by omega
    have hm : ¬ (i < 32) := h32
    simp [hm, hlt, hlt64, show 32 + (i - 32) = i by omega]

private theorem bv64_shl_shr_hi (m : BitVec 64) {j nn : Nat}
    (_hj : j < nn) (_hnn : nn ≤ 64) (hm : m >>> j = 0#64) :
    (m ||| (1#64 <<< j)) >>> (j + 1) = 0#64 := by
  apply BitVec.eq_of_getLsbD_eq; intro k _
  have hm_bit := congrArg (fun v => v.getLsbD (k + 1)) hm
  simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_zero] at hm_bit
  simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_one, BitVec.getLsbD_zero]
  have hneq : ¬ (j + (k + 1) < j) := by omega
  simp [show j + 1 + k = j + (k + 1) by omega, hm_bit, hneq]

private theorem bv64_shl_testBit_self {k : Nat} (hk : k < 64) :
    (((1#64 : BitVec 64) <<< k) >>> k) &&& 1#64 ≠ 0#64 := by
  have hk0 : ((((1#64 : BitVec 64) <<< k) >>> k) &&& 1#64).getLsbD 0 = true := by
    simp [hk]
  intro h; rw [h] at hk0; simp at hk0

theorem bv64_or_shl_testBit_self (m : BitVec 64) {k : Nat} (hk : k < 64) :
    (((m ||| (1#64 <<< k)) >>> k) &&& 1#64) ≠ 0#64 := by
  have hk0 : ((((m ||| (1#64 <<< k)) >>> k) &&& 1#64)).getLsbD 0 = true := by
    simp [hk]
  intro h; rw [h] at hk0; simp at hk0

private theorem bv64_shl_testBit_ne {i k : Nat} (hne : k ≠ i) :
    (((1#64 : BitVec 64) <<< i) >>> k) &&& 1#64 = 0#64 := by
  apply BitVec.eq_of_getLsbD_eq; intro b _
  cases b with
  | zero =>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft,
      BitVec.getLsbD_one, BitVec.getLsbD_zero, Nat.add_zero]
    by_cases hk : k < 64
    · by_cases hlt : k < i
      · simp [hk, hlt]
      · simp [hk, show ¬ (k < i) by omega, show k - i ≠ 0 by omega]
    · simp [hk]
  | succ _ => simp [BitVec.getLsbD_and, BitVec.getLsbD_one]

theorem bv64_or_bit_pres_other {m : BitVec 64} {j k : Nat} (hk : k < 64)
    (hprev : (m >>> k) &&& 1#64 ≠ 0#64) :
    ((m ||| (1#64 <<< j)) >>> k) &&& 1#64 ≠ 0#64 := by
  intro h; apply hprev
  apply BitVec.eq_of_getLsbD_eq; intro b _
  have h2 := congrArg (·.getLsbD b) h
  cases b with
  | zero =>
    simp [hk] at h2 ⊢
    exact h2.1
  | succ _ => simp [BitVec.getLsbD_and, BitVec.getLsbD_one]

private theorem bv64_shr_zero_imp_le {m : BitVec 64} {a b : Nat} (hab : a ≤ b)
    (ha : m >>> a = 0#64) : m >>> b = 0#64 := by
  apply BitVec.eq_of_getLsbD_eq; intro k _
  have hm := congrArg (fun v => v.getLsbD (k + (b - a))) ha
  simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_zero] at hm ⊢
  rwa [show a + (k + (b - a)) = b + k by omega] at hm

theorem maskedOccRestCls_mem {s : FullState} {except off cnt : Nat} {mask : BitVec 64}
    {k : Nat} (hk : k < cnt) (hbit : (mask >>> k) &&& 1#64 ≠ 0#64) :
    bveOccRestLits s except (s.scratch.scratch_buf[off + k]?.getD 0#32) ∈
      maskedOccRestCls s except off cnt mask := by
  unfold maskedOccRestCls
  rw [List.mem_filterMap]
  refine ⟨k, List.mem_range.mpr hk, ?_⟩
  simp [hbit]

private theorem unsat_of_filter_res {s : FullState} {v_lit : BitVec 32} {cr n_off nn : Nat}
    {nmask : BitVec 64}
    (hcov : ∀ l ∈ (fullArenaClauseLits s cr).filter (· != v_lit.toNat),
      ∃ k < nn, ((nmask >>> k) &&& 1#64 ≠ 0#64) ∧
        bveOccRestLits s (v_lit.toNat ^^^ 1) (s.scratch.scratch_buf[n_off + k]?.getD 0#32) =
          [l ^^^ 1]) :
    (cnfOfClauses ([(fullArenaClauseLits s cr).filter (· != v_lit.toNat)] ++
      maskedOccRestCls s (v_lit.toNat ^^^ 1) n_off nn nmask)).Unsat := by
  rw [CNF.unsat_iff_not_sat]; intro α hSat
  have hMain := (cnf_sat_cnfOfClauses_iff α _).mp hSat _ (List.mem_cons_self ..)
  rw [clause_sat_cnfClause_iff] at hMain
  obtain ⟨l, hl, hsat_l⟩ := hMain
  obtain ⟨k, hk, hbit, heq⟩ := hcov l hl
  have hmem := maskedOccRestCls_mem (s := s) (except := v_lit.toNat ^^^ 1) (off := n_off)
    (cnt := nn) hk hbit
  rw [heq] at hmem
  have hNeg := (cnf_sat_cnfOfClauses_iff α _).mp hSat [l ^^^ 1] (List.mem_append_right _ hmem)
  rw [clause_sat_cnfClause_iff] at hNeg
  obtain ⟨l', hl', hsat_neg⟩ := hNeg
  rcases List.mem_singleton.mp hl' with rfl
  simp only [litVar, litSign] at hsat_l hsat_neg
  have hln := litNeg_eq l
  have hdv : (l ^^^ 1) / 2 = l / 2 := litVar_litNeg l
  have hmod : (l ^^^ 1) % 2 ≠ l % 2 := by
    rcases Nat.mod_two_eq_zero_or_one l with hm | hm
    · have : l ^^^ 1 = l + 1 := by simpa [litNeg, hm] using hln
      omega
    · have : l ^^^ 1 = l - 1 := by simpa [litNeg, hm] using hln
      omega
  rw [hdv] at hsat_neg
  rcases Nat.mod_two_eq_zero_or_one l with h | h <;> cases ha : α (l / 2) <;>
    simp [h, ha] at hsat_l hsat_neg <;> omega

theorem bv32_shr1_toNat (x : BitVec 32) : (x >>> (1 : Nat)).toNat = x.toNat / 2 := by
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem bv32_lit_shl_or (v l : BitVec 32) (hv : v.toNat < 2 ^ 30) :
    ((v <<< (1 : Nat)) ||| (l &&& 1#32)).toNat = 2 * v.toNat + l.toNat % 2 := by
  have h1 : (l &&& 1#32).toNat = l.toNat % 2 := by
    rw [BitVec.toNat_and, show (1#32 : BitVec 32).toNat = 1 from rfl, Nat.and_one_is_mod]
  exact (FullSweepFwdHelpers.bv32_shl1_or_pol v (l &&& 1#32) (by omega) (by omega)).trans
    (by rw [h1])

private theorem filterMap_single_bit {α : Type} {f : Nat → α} {i : Nat} (hi : i < 64) :
    ∀ m ≤ 64,
      (List.range m).filterMap (fun k =>
        if (((1#64 : BitVec 64) <<< i) >>> k) &&& 1#64 ≠ 0#64 then some (f k) else none) =
      if i < m then [f i] else []
  | 0, _ => by simp
  | m + 1, hm => by
    have ih := filterMap_single_bit (f := f) hi m (by omega)
    rw [List.range_succ, List.filterMap_append, ih]
    by_cases hmi : m = i
    · subst hmi
      have hs := bv64_shl_testBit_self hi
      simp [hs]
    · have hz := bv64_shl_testBit_ne hmi
      simp only [List.filterMap_cons, hz, ne_eq, not_true_eq_false, ↓reduceIte, List.filterMap_nil,
        List.append_nil]
      split <;> split <;> first | rfl | omega

theorem maskedOccRestCls_single_bit {s : FullState} {except off n i : Nat}
    (hi : i < n) (hn : n ≤ 64) :
    maskedOccRestCls s except off n (1#64 <<< i) =
      [bveOccRestLits s except (s.scratch.scratch_buf[off + i]?.getD 0#32)] := by
  unfold maskedOccRestCls
  have h := filterMap_single_bit
    (f := fun k => bveOccRestLits s except (s.scratch.scratch_buf[off + k]?.getD 0#32))
    (by omega : i < 64) n hn
  simpa [hi] using h

theorem fullDefGateUnsat_of_unsat {s : FullState} {v : Nat} {pmask nmask : BitVec 64}
    {np nn : Nat}
    (hpm : np ≤ 64 → pmask >>> np = 0#64)
    (hnm : nn ≤ 64 → nmask >>> nn = 0#64)
    (hu : (cnfOfClauses (level0ForcedUnits s ++
      maskedOccRestCls s (2 * v) 0 np pmask ++
      maskedOccRestCls s (2 * v + 1) 64 nn nmask)).Unsat) :
    FullDefGateUnsat s v pmask nmask np nn := by
  rintro ⟨hnp, hnn, _⟩
  exact ⟨hpm hnp, hnm hnn, hu⟩

theorem unsat_of_subclauses {cs1 cs2 : List (List Nat)}
    (hsub : ∀ cl ∈ cs1, cl ∈ cs2) (hu : (cnfOfClauses cs1).Unsat) :
    (cnfOfClauses cs2).Unsat := by
  rw [CNF.unsat_iff_not_sat] at hu ⊢
  intro α hSat; apply hu α
  rw [cnf_sat_cnfOfClauses_iff]; intro cl hcl
  exact (cnf_sat_cnfOfClauses_iff α _).mp hSat cl (hsub cl hcl)

theorem range_filterMap_congr {α : Type} {n : Nat} {f g : Nat → Option α}
    (h : ∀ i < n, f i = g i) : (List.range n).filterMap f = (List.range n).filterMap g := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [List.range_succ, List.filterMap_append, List.filterMap_append,
      ih (fun i hi => h i (Nat.lt_succ_of_lt hi))]
    congr 1; simp only [List.filterMap_cons, List.filterMap_nil, h k (Nat.lt_succ_self k)]

theorem maskedOccRestCls_congr {s1 s2 : FullState} {except off cnt : Nat}
    {mask : BitVec 64} (har : s2.core.arena = s1.core.arena)
    (hbd : off + cnt ≤ 128)
    (hscr : ∀ i < 128, s2.scratch.scratch_buf[i]? = s1.scratch.scratch_buf[i]?) :
    maskedOccRestCls s2 except off cnt mask = maskedOccRestCls s1 except off cnt mask := by
  unfold maskedOccRestCls; apply range_filterMap_congr; intro i hi
  split
  · congr 1
    simp only [bveOccRestLits, fullArenaClauseLits, fullArenaClauseLitsCore,
      fullArenaClauseSizeCore, har, hscr (off + i) (by omega)]
  · rfl

theorem fullDefGateUnsat_congr {s1 s2 : FullState} {v : Nat} {pmask nmask : BitVec 64}
    {np nn : Nat} (hcv : s2.core.cur_vars = s1.core.cur_vars)
    (hvals : s2.core.vals = s1.core.vals) (har : s2.core.arena = s1.core.arena)
    (hscr : ∀ i < 128, s2.scratch.scratch_buf[i]? = s1.scratch.scratch_buf[i]?)
    (h : FullDefGateUnsat s2 v pmask nmask np nn) :
    FullDefGateUnsat s1 v pmask nmask np nn := by
  intro hp
  have ⟨h1, h2, h3⟩ := h hp
  have huf : level0ForcedUnits s2 = level0ForcedUnits s1 := by
    unfold level0ForcedUnits; rw [hcv, hvals]
  have hm1 := maskedOccRestCls_congr (s1 := s1) (s2 := s2) (except := 2 * v)
    (off := 0) (cnt := np) (mask := pmask) har (by omega) hscr
  have hm2 := maskedOccRestCls_congr (s1 := s1) (s2 := s2) (except := 2 * v + 1)
    (off := 64) (cnt := nn) (mask := nmask) har (by omega) hscr
  rw [huf, hm1, hm2] at h3
  exact ⟨h1, h2, h3⟩

theorem fullBveEntryOkW_congr {F_cur : List (List Nat)} {s1 s2 : FullState} {l : Nat}
    {w : BitVec 32} (hcv : s2.core.cur_vars = s1.core.cur_vars)
    (_hvals : s2.core.vals = s1.core.vals) (har : s2.core.arena = s1.core.arena)
    (hal : s2.core.arena_len = s1.core.arena_len) :
    FullBveEntryOkW F_cur s1 l w ↔ FullBveEntryOkW F_cur s2 l w := by
  unfold FullDefSweep.FullBveEntryOkW Full.FullBveEntryOkW
    fullArenaClauseRefs fullArenaClauseRefsCore
    fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore
  rw [hcv, har, hal]

theorem unsat_of_unit_pair {l : Nat} : (cnfOfClauses [[l], [l ^^^ 1]]).Unsat := by
  rw [CNF.unsat_iff_not_sat]; intro α hSat
  have h1 := (cnf_sat_cnfOfClauses_iff α _).mp hSat [l] List.mem_cons_self
  have h2 := (cnf_sat_cnfOfClauses_iff α _).mp hSat [l ^^^ 1]
    (List.mem_cons_of_mem _ List.mem_cons_self)
  rw [clause_sat_cnfClause_iff] at h1 h2
  obtain ⟨l1, hl1, hs1⟩ := h1
  obtain ⟨l2, hl2, hs2⟩ := h2
  rcases List.mem_singleton.mp hl1 with rfl
  rcases List.mem_singleton.mp hl2 with rfl
  have hxor_if : l1 ^^^ 1 = if l1 % 2 = 0 then l1 + 1 else l1 - 1 := by
    apply Nat.eq_of_testBit_eq; intro k
    cases k with
    | zero =>
      rw [Nat.testBit_xor, Nat.testBit_zero, Nat.testBit_zero]
      rcases Nat.mod_two_eq_zero_or_one l1 with h | h
      · simp [h, show (l1 + 1) % 2 = 1 by omega]
      · simp [h, show (l1 - 1) % 2 = 0 by omega]
    | succ k =>
      rw [Nat.testBit_xor, Nat.testBit_succ, show (1 : Nat).testBit (k + 1) = false by
        rw [Nat.testBit_succ]; simp]
      rcases Nat.mod_two_eq_zero_or_one l1 with h | h
      · simp [h, Nat.testBit_succ, show (l1 + 1) / 2 = l1 / 2 by omega]
      · simp [h, Nat.testBit_succ, show (l1 - 1) / 2 = l1 / 2 by omega]
  have hev := evalLitVal_litNeg α l1
  rw [litNeg_eq, ← hxor_if] at hev
  dsimp only [evalLitVal] at hev
  rw [hs1, hs2] at hev
  cases hbs1 : litSign l1 <;> cases hbs2 : litSign (l1 ^^^ 1) <;> simp_all

theorem list_set_eq_self_of_getElem? {α : Type} {xs : List α} {i : Nat} {v : α}
    (h : xs[i]? = some v) : xs.set i v = xs := by
  have hi : i < xs.length := (List.getElem?_eq_some_iff.mp h).1
  have hv : xs[i]'hi = v := (List.getElem?_eq_some_iff.mp h).2
  apply List.ext_getElem (by simp)
  intro j hj1 _
  by_cases hji : j = i
  · subst hji; rw [List.getElem_set_self (by simpa using hj1), ← hv]
  · rw [List.getElem_set_ne (Ne.symm hji)]

/-! ## 2. `full_bve_mark_and_wp` (`FullDefSweep` #1) -/

/-- **`full_bve_mark_and`**: marks complements of non-`v_lit` literals in clause `cr`, detects
matched unit opposites in `scr[n_off ..< n_off + nn)` using duplicate-literal guard `lm[ot] == 2`,
clears all marks, and writes the `nmask` bitmask into `scr[130..131]` on success. -/
theorem full_bve_mark_and_wp (Γ : Env) :
    ∀ args m Q X, fullBveMarkAndDefSpec args m Q X →
      Func.wp Γ full_bve_mark_and_body args m Q X := by
  rintro ⟨h, v_lit, cr, n_off, nn, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, s, R, rfl, hdw, h132, href, hgarb, hn_bd, hn_ok, hm, hQ⟩
  have hmv := c.hmaxv; have harc := c.harena; have hsc := c.hscr
  unfold dimacsBound at hmv harc hsc
  have hcl := hdw.1.core_ok; have hsl := hdw.1.scratch_ok; have hw := hdw.2.1
  have hlm_clr := hdw.2.2.1; have hnd := hdw.2.2.2.1
  have hcv := hcl.cur_vars_le; have harl := hcl.arena_len_arr; have harle := hcl.arena_len_le
  have hlml := hcl.lit_mark_len; have hscrl := hsl.scratch_buf_len
  have hwf := hw.arena.refs_wf cr.toNat href
  have hcr2_nat : (cr.setWidth 64 + 2).toNat = cr.toNat + 2 := by bv_omega
  have hcr2_lt : (cr.setWidth 64 + 2).toNat < s.core.arena.length := by bv_omega
  let sz := s.core.arena[cr.toNat + 2]'(by omega)
  have hsz_eq : s.core.arena[(cr.setWidth 64 + 2).toNat]'hcr2_lt = sz := by
    simp only [sz, hcr2_nat]
  have hsz_nat : sz.toNat = fullArenaClauseSizeCore s.core cr.toNat := by
    unfold fullArenaClauseSizeCore sz
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
  have hcr_sz_bd : cr.toNat + 3 + sz.toNat ≤ s.core.arena_len := by
    have : fullArenaClauseSize s cr.toNat = sz.toNat := by
      unfold fullArenaClauseSize; exact hsz_nat.symm
    omega
  have hsz_le_cv : sz.toNat ≤ s.core.cur_vars := by
    rw [hsz_nat]
    exact fullArenaClauseSize_le_cur_vars hdw.1 hw hnd href hgarb
  have hcl_nodup : (fullArenaClauseLits s cr.toNat).Nodup :=
    nodup_of_map_div2 (hnd cr.toNat href hgarb)
  have hlits_lt : ∀ l ∈ fullArenaClauseLits s cr.toNat, l < 2 * c.max_vars := fun l hl =>
    Nat.lt_of_lt_of_le (hw.arena.lits_lt cr.toNat href hgarb l hl) (by omega)
  have hlit_lt_at : ∀ j < sz.toNat,
      (s.core.arena[cr.toNat + 3 + j]?.getD 0#32).toNat < 2 * c.max_vars := fun j hj => by
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
    apply hlits_lt
    unfold fullArenaClauseLits
    rw [mem_fullArenaClauseLitsCore_iff (by omega)]
    exact ⟨j, by rw [← hsz_nat]; exact hj, rfl⟩
  let rest := (fullArenaClauseLits s cr.toNat).filter (· != v_lit.toNat)
  have hrest_nodup : rest.Nodup := hcl_nodup.filter _
  unfold Func.wp full_bve_mark_and_body
  ds_steps
  simp only [hsz_eq]
  refine wp_loop_inv (ts := [i32, i32])
    (fun (need, i, _) m1 =>
      i.toNat ≤ sz.toNat ∧
      need.toNat =
        (((fullArenaClauseLits s cr.toNat).take i.toNat).filter (· != v_lit.toNat)).length ∧
      ∃ lm1 : List (BitVec 8), lm1.length = 2 * c.max_vars ∧
      (∀ l < 2 * c.max_vars,
        (lm1[l]? = some 1#8 ↔
          (l ^^^ 1) ∈ ((fullArenaClauseLits s cr.toNat).take i.toNat).filter (· != v_lit.toNat)) ∧
        ((l ^^^ 1) ∉ ((fullArenaClauseLits s cr.toNat).take i.toNat).filter (· != v_lit.toNat) →
          lm1[l]? = some 0#8)) ∧
      (FullMem c { s with core := { s.core with lit_mark := lm1 } } ⋆ R) m1)
    (fun (_, i, _) _ => sz.toNat - i.toNat)
    ?_ ?_
  · intro J1 hJ1; ds_steps
    refine hJ1 (0#32, 0#32, ()) m
      ⟨Nat.zero_le _, by simp, s.core.lit_mark, hlml, fun l hl => ?_, hm⟩
    have h0 := hlm_clr.2 l hl
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at h0
    rw [List.getElem?_eq_getElem (by omega), h0]
    exact ⟨⟨fun h => absurd h (by decide), fun h => by simp at h⟩, fun _ => rfl⟩
  · rintro J1 ⟨need, i, ⟨⟩⟩ m1 ⟨hi_le, hneed_eq, lm1, hlm1_len, hlm1_spec, hm1⟩ ih1
    ds_split
    · have hi_lt : i.toNat < sz.toNat := by bv_omega
      have har_nat : (cr.setWidth 64 + 3#64 + i.setWidth 64).toNat = cr.toNat + 3 + i.toNat := by
        bv_omega
      have har_idx : (cr.setWidth 64 + 3#64 + i.setWidth 64).toNat < s.core.arena.length := by
        omega
      let l_bv := s.core.arena[(cr.setWidth 64 + 3#64 + i.setWidth 64).toNat]'har_idx
      have hl_ar : l_bv.toNat < 2 * c.max_vars := by
        have := hlit_lt_at i.toNat hi_lt
        rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at this
        simpa [l_bv, har_nat] using this
      have hidx_lt : (l_bv ^^^ 1#32).toNat < lm1.length := by
        rw [hlm1_len]; exact bv32_xor1_lt_even hl_ar
      have hidx64_lt : (BitVec.setWidth 64 (l_bv ^^^ 1#32)).toNat < lm1.length := by
        rw [bv_c0_zext32_64]; exact hidx_lt
      have hcl_take : (fullArenaClauseLits s cr.toNat).take (i.toNat + 1) =
          (fullArenaClauseLits s cr.toNat).take i.toNat ++ [l_bv.toNat] := by
        unfold fullArenaClauseLits fullArenaClauseLitsCore
        rw [← hsz_nat, ← List.map_take, ← List.map_take, List.take_take, List.take_take]
        have hmin1 : min (i.toNat + 1) sz.toNat = i.toNat + 1 := by omega
        have hmin2 : min i.toNat sz.toNat = i.toNat := by omega
        rw [hmin1, hmin2, List.take_succ_eq_append_getElem (by simp [List.length_drop]; omega)]
        simp only [List.map_append, List.map_cons, List.map_nil, List.getElem_drop, l_bv, har_nat]
      have hlen_full : (fullArenaClauseLits s cr.toNat).length = sz.toNat := by
        unfold fullArenaClauseLits fullArenaClauseLitsCore
        simp [← hsz_nat]; exact Nat.min_eq_left (by omega)
      have hl_not_mem : l_bv.toNat ∉ (fullArenaClauseLits s cr.toNat).take i.toNat := by
        have hlen_l : ((fullArenaClauseLits s cr.toNat).take i.toNat).length = i.toNat := by
          rw [List.length_take, hlen_full]; exact Nat.min_eq_left (by omega)
        intro hm
        obtain ⟨j, hj, hje⟩ := List.mem_iff_getElem.mp hm
        rw [hlen_l] at hj
        have ht := List.getElem_take (xs := fullArenaClauseLits s cr.toNat) (i := j) (j := i.toNat)
          (h := by rw [List.length_take, hlen_full, Nat.min_eq_left (by omega)]; exact hj)
        rw [hje] at ht
        have heq_l :
            (fullArenaClauseLits s cr.toNat)[i.toNat]'(by rw [hlen_full]; exact hi_lt) =
              l_bv.toNat := by
          unfold fullArenaClauseLits fullArenaClauseLitsCore
          simp [List.getElem_drop, l_bv, har_nat]
        have hne := (List.pairwise_iff_getElem.mp hcl_nodup) j i.toNat
          (by rw [hlen_full]; omega) (by rw [hlen_full]; exact hi_lt) hj
        exact absurd (ht.symm.trans heq_l.symm) hne
      (try change wp _ _ _ _ _); (repeat ds_strip); c0_steps
      · -- `l_bv ≠ v_lit`
        have hl_ne : l_bv.toNat ≠ v_lit.toNat := fun h => by
          apply absurd (BitVec.eq_of_toNat_eq h)
          simpa [l_bv] using hc
        have htake_len :
            (((fullArenaClauseLits s cr.toNat).take (i.toNat + 1)).filter
              (· != v_lit.toNat)).length =
            (((fullArenaClauseLits s cr.toNat).take i.toNat).filter (· != v_lit.toNat)).length +
              1 := by
          rw [hcl_take, List.filter_append, List.length_append]
          simp [hl_ne]
        have hneed_lt : need.toNat < sz.toNat := by
          have h1 :
              (((fullArenaClauseLits s cr.toNat).take i.toNat).filter
                (· != v_lit.toNat)).length ≤ i.toNat :=
            Nat.le_trans (List.length_filter_le ..) (List.length_take_le ..)
          omega
        have hi1 : (i + 1#32).toNat = i.toNat + 1 := by bv_omega
        have hneed1 : (need + 1#32).toNat = need.toNat + 1 := by bv_omega
        have hm_upd :
            (FullMem c
              { s with core := { s.core with lit_mark := lm1.set (l_bv ^^^ 1#32).toNat 1#8 } } ⋆
              R) m := by
          rw [bv_c0_zext32_64] at hm; exact hm
        refine ih1 (need + 1#32, i + 1#32, ()) m (by bv_omega)
          ⟨by omega, by rw [hi1, hneed1, htake_len, hneed_eq],
            lm1.set (l_bv ^^^ 1#32).toNat 1#8, by simp [hlm1_len], fun l hl => ?_, hm_upd⟩
        have hxor_eq : (l_bv ^^^ 1#32).toNat = l_bv.toNat ^^^ 1 := rfl
        have hf_eq :
            ((fullArenaClauseLits s cr.toNat).take (i.toNat + 1)).filter (· != v_lit.toNat) =
            ((fullArenaClauseLits s cr.toNat).take i.toNat).filter (· != v_lit.toNat) ++
              [l_bv.toNat] := by
          rw [hcl_take, List.filter_append]; simp [hl_ne]
        rw [hi1, hf_eq]
        by_cases hl_target : l = (l_bv ^^^ 1#32).toNat
        · subst hl_target
          have hinv : ((l_bv ^^^ 1#32).toNat ^^^ 1) = l_bv.toNat := by
            rw [hxor_eq]; exact nat_xor1_cancel _
          rw [List.getElem?_set_self (by omega), hinv]
          exact ⟨⟨fun _ => List.mem_append_right _ (List.mem_singleton.mpr rfl), fun _ => rfl⟩,
            fun hn => absurd (List.mem_append_right _ (List.mem_singleton.mpr rfl)) hn⟩
        · rw [List.getElem?_set_ne (Ne.symm hl_target)]
          have hnot_l : l ^^^ 1 ≠ l_bv.toNat := fun he => hl_target (by
            rw [hxor_eq, ← he, nat_xor1_cancel])
          simpa [List.mem_append, List.mem_singleton, hnot_l] using hlm1_spec l hl
      · -- `l_bv = v_lit`
        have hl_eq : l_bv.toNat = v_lit.toNat :=
          congrArg BitVec.toNat (by simpa [l_bv] using hc : l_bv = v_lit)
        have hi1 : (i + 1#32).toNat = i.toNat + 1 := by bv_omega
        have hf_eq :
            ((fullArenaClauseLits s cr.toNat).take (i.toNat + 1)).filter (· != v_lit.toNat) =
            ((fullArenaClauseLits s cr.toNat).take i.toNat).filter (· != v_lit.toNat) := by
          rw [hcl_take, List.filter_append]; simp [hl_eq]
        refine ih1 (need, i + 1#32, ()) m1 (by bv_omega)
          ⟨by omega, by rw [hi1, hf_eq]; exact hneed_eq, lm1, hlm1_len,
            fun l hl => by rw [hi1, hf_eq]; exact hlm1_spec l hl, hm1⟩
    · -- exit Loop 1: `i = sz`
      have hi_eq : i.toNat = sz.toNat := by bv_omega
      have htake_all : (fullArenaClauseLits s cr.toNat).take i.toNat =
          fullArenaClauseLits s cr.toNat := by
        rw [hi_eq]; apply List.take_of_length_le
        unfold fullArenaClauseLits fullArenaClauseLitsCore; simp [← hsz_nat]
        exact Nat.min_le_left ..
      rw [htake_all] at hneed_eq hlm1_spec
      change need.toNat = rest.length at hneed_eq
      ds_steps
      refine wp_loop_inv (ts := [i32, i64, i32])
        (fun (matched, nmask, j, _) m2 =>
          j.toNat ≤ nn.toNat ∧ (nn.toNat ≤ 64 → (nmask >>> j.toNat) = 0#64) ∧
          ∃ lm2 : List (BitVec 8), lm2.length = 2 * c.max_vars ∧
          matched.toNat = rest.countP (fun l => lm2[l ^^^ 1]?.getD 0#8 == 2#8) ∧
          (∀ l < 2 * c.max_vars,
            ((l ^^^ 1) ∉ rest → lm2[l]? = some 0#8) ∧
            ((l ^^^ 1) ∈ rest → lm2[l]? = some 1#8 ∨ lm2[l]? = some 2#8) ∧
            (lm2[l]? = some 2#8 → nn.toNat ≤ 64 →
              ∃ k < j.toNat, ((nmask >>> k) &&& 1#64 ≠ 0#64) ∧
                bveOccRestLits s (v_lit.toNat ^^^ 1)
                  (s.scratch.scratch_buf[n_off.toNat + k]?.getD 0#32) = [l])) ∧
          (FullMem c { s with core := { s.core with lit_mark := lm2 } } ⋆ R) m2)
        (fun (_, _, j, _) _ => nn.toNat - j.toNat)
        ?_ ?_
      · intro J2 hJ2; ds_steps
        refine hJ2 (0#32, 0#64, 0#32, ()) m1 ⟨Nat.zero_le _, fun _ => rfl, lm1, hlm1_len, ?_,
          fun l hl => ?_, hm1⟩
        · rw [show (0#32 : BitVec 32).toNat = 0 from rfl]
          symm; rw [List.countP_eq_zero]; intro l hl
          have hl_ar : l < 2 * c.max_vars := hlits_lt l (List.mem_filter.mp hl).1
          have h1 := (hlm1_spec (l ^^^ 1) (bv32_xor1_lt_even hl_ar)).1.mpr
            (by rw [nat_xor1_cancel]; exact hl)
          rw [h1]; decide
        · refine ⟨(hlm1_spec l hl).2, fun hm => Or.inl ((hlm1_spec l hl).1.mpr hm),
            fun h2 => absurd h2 (by
              by_cases hm : (l ^^^ 1) ∈ rest
              · rw [(hlm1_spec l hl).1.mpr hm]; decide
              · rw [(hlm1_spec l hl).2 hm]; decide)⟩
      · rintro J2 ⟨matched, nmask, j, ⟨⟩⟩ m2 ⟨hj_le, hnmask_hi, lm2, hlm2_len, hmatch_eq,
          hlm2_spec, hm2⟩ ih2
        have hmatched_le : matched.toNat ≤ c.max_vars := by
          rw [hmatch_eq]
          have h1 := List.countP_le_length (l := rest)
            (p := fun l => lm2[l ^^^ 1]?.getD 0#8 == 2#8)
          have h2 : rest.length ≤ sz.toNat := by
            refine Nat.le_trans (List.length_filter_le ..) ?_
            unfold fullArenaClauseLits fullArenaClauseLitsCore; simp [← hsz_nat]
            exact Nat.min_le_left ..
          omega
        clear hc; ds_split
        · have hj_lt : j.toNat < nn.toNat := by bv_omega
          have hj1 : (j + 1#32).toNat = j.toNat + 1 := by bv_omega
          have hno_nat : (n_off + j).toNat = n_off.toNat + j.toNat := by bv_omega
          have hscr_idx : (n_off + j).toNat < s.scratch.scratch_buf.length := by bv_omega
          have hscr64 : ((n_off + j).setWidth 64).toNat = n_off.toNat + j.toNat := by bv_omega
          let w := s.scratch.scratch_buf[n_off.toNat + j.toNat]'(by omega)
          have hw_get : s.scratch.scratch_buf[n_off.toNat + j.toNat]?.getD 0#32 = w := by
            rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
          ds_to_group
          let Loop2Step (matched' : BitVec 32) (nmask' : BitVec 64) (mj : Mem 64) : Prop :=
            matched'.toNat ≤ c.max_vars ∧
            (nn.toNat ≤ 64 → (nmask' >>> (j.toNat + 1)) = 0#64) ∧
            ∃ lm2' : List (BitVec 8), lm2'.length = 2 * c.max_vars ∧
            matched'.toNat = rest.countP (fun l => lm2'[l ^^^ 1]?.getD 0#8 == 2#8) ∧
            (∀ l < 2 * c.max_vars,
              ((l ^^^ 1) ∉ rest → lm2'[l]? = some 0#8) ∧
              ((l ^^^ 1) ∈ rest → lm2'[l]? = some 1#8 ∨ lm2'[l]? = some 2#8) ∧
              (lm2'[l]? = some 2#8 → nn.toNat ≤ 64 →
                ∃ k < j.toNat + 1, ((nmask' >>> k) &&& 1#64 ≠ 0#64) ∧
                  bveOccRestLits s (v_lit.toNat ^^^ 1)
                    (s.scratch.scratch_buf[n_off.toNat + k]?.getD 0#32) = [l])) ∧
            (FullMem c { s with core := { s.core with lit_mark := lm2' } } ⋆ R) mj
          refine wp_join_group (ts := [i32, i64])
            (fun (matched', nmask', _) mj => Loop2Step matched' nmask' mj)
            ?_ ?_
          · rintro _ ⟨matched', nmask', ⟨⟩⟩ mj ⟨hm_le, hnm, lm2', hll, hm_eq, hsp, hm'⟩
            ds_steps
            exact ih2 (matched', nmask', j + 1#32, ()) mj (by bv_omega)
              ⟨by omega, by rw [hj1]; exact hnm, lm2', hll, hm_eq,
                by rw [hj1]; exact hsp, hm'⟩
          · intro Jw hJw
            have hkeep : Loop2Step matched nmask m2 :=
              ⟨hmatched_le, fun hnn => bv64_shr_zero_imp_le (by omega) (hnmask_hi hnn),
                lm2, hlm2_len, hmatch_eq, fun l hl =>
                  ⟨(hlm2_spec l hl).1, (hlm2_spec l hl).2.1, fun h2 hnn =>
                    let ⟨k, hk_lt, hk_b, hk_e⟩ := (hlm2_spec l hl).2.2 h2 hnn
                    ⟨k, by omega, hk_b, hk_e⟩⟩, hm2⟩
            clear hc; ds_split
            · -- binary entry: `(w & 0x80000000#32) ≠ 0#32`
              have hbin : (w &&& 0x80000000#32) ≠ 0#32 := by
                simpa [w, hno_nat, hscr64, LeanQbe.T.lift2, LeanQbe.T.Arg.val] using hc
              have hok_j := hn_ok j.toNat hj_lt
              unfold FullBveEntryOkW Full.FullBveEntryOkW at hok_j
              rw [hw_get, ite_eq_left hbin] at hok_j
              let ot := w &&& 0x7FFFFFFF#32
              have hot_lt : ot.toNat < 2 * c.max_vars := Nat.lt_of_lt_of_le hok_j.1 (by omega)
              have hot_lm : ot.toNat < lm2.length := by omega
              have hot64_lm : (ot.setWidth 64).toNat < lm2.length := by
                rw [bv_c0_zext32_64]; exact hot_lm
              have hot64_lm_raw :
                  (BitVec.setWidth 64
                    (s.scratch.scratch_buf[(BitVec.setWidth 64 (n_off + j)).toNat]'(by
                        rw [hscr64, ← hno_nat]; exact hscr_idx) &&&
                      0x7FFFFFFF#32)).toNat < lm2.length := by
                simpa [w, ot, hscr64] using hot64_lm
              have hrest_ot : bveOccRestLits s (v_lit.toNat ^^^ 1)
                  (s.scratch.scratch_buf[n_off.toNat + j.toNat]?.getD 0#32) = [ot.toNat] := by
                unfold bveOccRestLits; rw [hw_get, ite_eq_left hbin]
              ds_to_group
              refine wp_join_group (ts := [i32, i64])
                (fun (matched', nmask', _) mj => Loop2Step matched' nmask' mj)
                (fun _ ⟨m', nm', ⟨⟩⟩ mj h => by ds_steps; exact hJw (m', nm', ()) mj h) ?_
              intro Jw1 hJw1
              dsimp only [LeanQbe.T.lift2, LeanQbe.T.Arg.val]
              have hno64_eq : ((n_off + j).setWidth 64).toNat = n_off.toNat + j.toNat := hscr64
              clear hc; ds_split
              · -- `lm2[ot] == 1#8`
                have hot_eq1 : lm2[ot.toNat]? = some 1#8 := by
                  have hnat := congrArg BitVec.toNat hc
                  have hmod32 : (n_off.toNat + j.toNat) % 2 ^ 32 = n_off.toNat + j.toNat := by omega
                  simp only [BitVec.toNat_setWidth, hmod32,
                    show (BitVec.ofNat 32 1).toNat = 1 from rfl] at hnat
                  have hlt8 := (lm2[ot.toNat]'hot_lm).isLt
                  have hbv : lm2[ot.toNat]'hot_lm = 1#8 := by
                    apply BitVec.eq_of_toNat_eq
                    change (lm2[ot.toNat]'hot_lm).toNat = 1
                    rw [← Nat.mod_eq_of_lt (by omega : (lm2[ot.toNat]'hot_lm).toNat < 2 ^ 32)]
                    simpa [w, ot] using hnat
                  rw [List.getElem?_eq_getElem hot_lm, hbv]
                have hot_in : (ot.toNat ^^^ 1) ∈ rest := Classical.byContradiction fun hnot => by
                  have hz := (hlm2_spec ot.toNat hot_lt).1 hnot
                  rw [hot_eq1] at hz; cases hz
                have hot_xor_lt : (ot.toNat ^^^ 1) < 2 * c.max_vars := bv32_xor1_lt_even hot_lt
                let lm2' := lm2.set ot.toNat 2#8
                have hcnt_eq : rest.countP (fun l => lm2'[l ^^^ 1]?.getD 0#8 == 2#8) =
                    matched.toNat + 1 := by
                  rw [hmatch_eq]
                  refine countP_inc_unique hrest_nodup hot_in
                    (fun l => lm2[l ^^^ 1]?.getD 0#8 == 2#8)
                    (fun l => lm2'[l ^^^ 1]?.getD 0#8 == 2#8) ?_ ?_ ?_
                  · rw [nat_xor1_cancel, hot_eq1]; rfl
                  · simp only [lm2', nat_xor1_cancel, List.getElem?_set_self hot_lm]; rfl
                  · intro y _ hne
                    have hne' : y ^^^ 1 ≠ ot.toNat := fun h => hne (by
                      rw [← h, nat_xor1_cancel])
                    simp [lm2', List.getElem?_set_ne (Ne.symm hne')]
                have hmatched_lt : matched.toNat < c.max_vars := by
                  have h1 : rest.countP (fun l => lm2'[l ^^^ 1]?.getD 0#8 == 2#8) ≤ rest.length :=
                    List.countP_le_length
                  have h2 : rest.length ≤ sz.toNat := by
                    refine Nat.le_trans (List.length_filter_le ..) ?_
                    unfold fullArenaClauseLits fullArenaClauseLitsCore; simp [← hsz_nat]
                    exact Nat.min_le_left ..
                  omega
                ds_csteps!
                have hm1_nat : (matched + 1#32).toNat = matched.toNat + 1 := by bv_omega
                let nmask' := nmask ||| (1#64 <<< ((j.setWidth 64).toNat % 64))
                have hj64_mod : (hnn : nn.toNat ≤ 64) →
                    (j.setWidth 64).toNat % 64 = j.toNat := fun hnn => by bv_omega
                have hnmask_eq : (hnn : nn.toNat ≤ 64) →
                    nmask' = nmask ||| (1#64 <<< j.toNat) := fun hnn => by
                  dsimp only [nmask']; rw [hj64_mod hnn]
                have hm_upd2 :
                    (FullMem c { s with core := { s.core with lit_mark := lm2' } } ⋆ R) m := by
                  have heq :
                      (BitVec.setWidth 64
                        (s.scratch.scratch_buf[(BitVec.setWidth 64 (n_off + j)).toNat]'(by
                            rw [hscr64, ← hno_nat]; exact hscr_idx) &&&
                          0x7FFFFFFF#32)).toNat = ot.toNat := by
                    simp only [bv_c0_zext32_64, ot, w, hscr64]
                  dsimp only [lm2']; rwa [← heq]
                refine hJw1 (matched + 1#32, nmask', ()) m
                  ⟨by rw [hm1_nat]; omega, fun hnn => by
                    rw [hnmask_eq hnn]; exact bv64_shl_shr_hi nmask hj_lt hnn (hnmask_hi hnn),
                    lm2', by simp [lm2', hlm2_len], by rw [hm1_nat, hcnt_eq],
                    fun l hl => ?_, hm_upd2⟩
                by_cases hlot : l = ot.toNat
                · subst hlot
                  refine ⟨fun hnot => absurd hot_in hnot,
                    fun _ => Or.inr (List.getElem?_set_self hot_lm), fun _ hnn => ?_⟩
                  refine ⟨j.toNat, by omega, ?_, hrest_ot⟩
                  rw [hnmask_eq hnn]; exact bv64_or_shl_testBit_self nmask (by omega)
                · simp only [lm2', List.getElem?_set_ne (Ne.symm hlot)]
                  refine ⟨(hlm2_spec l hl).1, (hlm2_spec l hl).2.1, fun h2 hnn => ?_⟩
                  obtain ⟨k, hk_lt, hk_bit, hk_eq⟩ := (hlm2_spec l hl).2.2 h2 hnn
                  refine ⟨k, by omega, ?_, hk_eq⟩
                  rw [hnmask_eq hnn]
                  exact bv64_or_bit_pres_other (j := j.toNat) (by omega) hk_bit
              · ds_to_group
                refine wp_join_group (ts := [i64])
                  (fun (nmask', _) mj => Loop2Step matched nmask' mj)
                  (fun _ ⟨nm', ⟨⟩⟩ mj h => by ds_steps; exact hJw1 (matched, nm', ()) mj h) ?_
                intro Jw2 hJw2
                dsimp only [LeanQbe.T.lift2, LeanQbe.T.Arg.val]
                clear hc; ds_split
                · -- `lm2[ot] == 2#8`
                  ds_steps
                  have hj64_mod : (hnn : nn.toNat ≤ 64) →
                      (j.setWidth 64).toNat % 64 = j.toNat := fun hnn => by bv_omega
                  let nmask' := nmask ||| (1#64 <<< ((j.setWidth 64).toNat % 64))
                  have hnmask_eq : (hnn : nn.toNat ≤ 64) →
                      nmask' = nmask ||| (1#64 <<< j.toNat) := fun hnn => by
                    dsimp only [nmask']; rw [hj64_mod hnn]
                  refine hJw2 (nmask', ()) m2
                    ⟨hmatched_le, fun hnn => by
                      rw [hnmask_eq hnn]; exact bv64_shl_shr_hi nmask hj_lt hnn (hnmask_hi hnn),
                      lm2, hlm2_len, hmatch_eq, fun l hl => ?_, hm2⟩
                  refine ⟨(hlm2_spec l hl).1, (hlm2_spec l hl).2.1, fun h2 hnn => ?_⟩
                  obtain ⟨k, hk_lt, hk_bit, hk_eq⟩ := (hlm2_spec l hl).2.2 h2 hnn
                  refine ⟨k, by omega, ?_, hk_eq⟩
                  rw [hnmask_eq hnn]
                  exact bv64_or_bit_pres_other (j := j.toNat) (by omega) hk_bit
                · -- `lm2[ot] ∉ {1#8, 2#8}`
                  ds_steps
                  exact hJw2 (nmask, ()) m2 hkeep
            · -- non-binary entry
              ds_steps
              exact hJw (matched, nmask, ()) m2 hkeep
        · -- Exit Loop 2 (`j = nn`): run Loop 3 to clear `lm2` back to `s.core.lit_mark`
          have hj_eq : j.toNat = nn.toNat := by bv_omega
          rw [hj_eq] at hnmask_hi
          ds_steps
          refine wp_loop_inv (ts := [i32])
            (fun (i3, _) m3 =>
              i3.toNat ≤ sz.toNat ∧
              ∃ lm3 : List (BitVec 8), lm3.length = 2 * c.max_vars ∧
              (∀ l < 2 * c.max_vars,
                ((∃ k < i3.toNat,
                    (s.core.arena[cr.toNat + 3 + k]?.getD 0#32).toNat ^^^ 1 = l) ∨
                 (∀ k < sz.toNat,
                    (s.core.arena[cr.toNat + 3 + k]?.getD 0#32).toNat ^^^ 1 ≠ l)) →
                lm3[l]? = some 0#8) ∧
              (FullMem c { s with core := { s.core with lit_mark := lm3 } } ⋆ R) m3)
            (fun (i3, _) _ => sz.toNat - i3.toNat)
            ?_ ?_
          · intro J3 hJ3; ds_steps
            refine hJ3 (0#32, ()) m2 ⟨Nat.zero_le _, lm2, hlm2_len, fun l hl hc => ?_, hm2⟩
            rcases hc with ⟨k, hk, _⟩ | hnone
            · simp at hk
            · refine (hlm2_spec l hl).1 fun hmem => ?_
              have hmem2 := (List.mem_filter.mp hmem).1
              unfold fullArenaClauseLits at hmem2
              obtain ⟨k, hk, heq_k⟩ := (mem_fullArenaClauseLitsCore_iff (by omega)).mp hmem2
              rw [← hsz_nat] at hk
              exact hnone k hk (by
                rw [List.getElem?_eq_getElem (by omega), Option.getD_some, heq_k]
                exact nat_xor1_cancel l)
          · rintro J3 ⟨i3, ⟨⟩⟩ m3 ⟨hi3_le, lm3, hlm3_len, hlm3_cov, hm3⟩ ih3
            clear hc; ds_split
            · have hi3_lt : i3.toNat < sz.toNat := by bv_omega
              have har_nat : (cr.setWidth 64 + 3 + i3.setWidth 64).toNat =
                  cr.toNat + 3 + i3.toNat := by bv_omega
              have har_idx : (cr.setWidth 64 + 3 + i3.setWidth 64).toNat <
                  s.core.arena.length := by omega
              have hl_ar : (s.core.arena[(cr.setWidth 64 + 3 +
                  i3.setWidth 64).toNat]'har_idx).toNat < 2 * c.max_vars := by
                have h1 := hlit_lt_at i3.toNat hi3_lt
                rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at h1
                rw [list_getElem_congr har_nat har_idx (by omega)]; exact h1
              have hidx_lt : (s.core.arena[(cr.setWidth 64 + 3 +
                  i3.setWidth 64).toNat]'har_idx ^^^ 1).toNat < lm3.length := by
                rw [hlm3_len]; exact bv32_xor1_lt_even hl_ar
              ds_steps
              dsimp only [LeanQbe.T.lift2, LeanQbe.T.Arg.val] at hm
              have hi_ar2 : cr.toNat + 3 + i3.toNat < s.core.arena.length := by omega
              have hidx2_lt : (s.core.arena[cr.toNat + 3 + i3.toNat]'hi_ar2 ^^^ 1#32).toNat <
                  2 * c.max_vars := by
                have heqv : s.core.arena[cr.toNat + 3 + i3.toNat]'hi_ar2 =
                    s.core.arena[(cr.setWidth 64 + 3 + i3.setWidth 64).toNat]'har_idx := by
                  exact (list_getElem_congr har_nat har_idx (by omega)).symm
                rw [heqv]; exact bv32_xor1_lt_even hl_ar
              have hidx_eq :
                  ((s.core.arena[(cr.setWidth 64 + 3 + i3.setWidth 64).toNat]'har_idx ^^^
                    1).setWidth 64).toNat =
                  (s.core.arena[cr.toNat + 3 + i3.toNat]'hi_ar2 ^^^ 1#32).toNat := by
                simp only [bv_c0_zext32_64, har_nat]; rfl
              have hcov' := litMark_clear_cov hi_ar2 hidx2_lt hlm3_len hlm3_cov
              refine ih3 (i3 + 1#32, ()) _ (by bv_omega)
                ⟨by bv_omega, lm3.set _ 0#8, by simp [hlm3_len], fun l hl hc => ?_, hm⟩
              rw [show (i3 + 1#32).toNat = i3.toNat + 1 from by bv_omega] at hc
              rw [hidx_eq]; exact hcov' l hl hc
            · have hi3_eq : i3.toNat = sz.toNat := by bv_omega
              have heq_lm : lm3 = s.core.lit_mark := by
                refine fullLitMark_eq_of_zero_ext hlml hlm3_len hlm_clr.2 fun l hl => ?_
                apply hlm3_cov l hl
                by_cases hex : ∃ k < sz.toNat,
                    (s.core.arena[cr.toNat + 3 + k]?.getD 0#32).toNat ^^^ 1 = l
                · exact Or.inl (hi3_eq ▸ hex)
                · exact Or.inr fun k hk heq => hex ⟨k, hk, heq⟩
              subst heq_lm
              clear hc; ds_split
              · -- `matched ≥ need`: store `scr[130], scr[131]` and return `true`
                have hge_nat : rest.length ≤ matched.toNat := by
                  rw [← hneed_eq]; bv_omega
                have h130 : 520 / 4 < s.scratch.scratch_buf.length := by omega
                have h131 : 524 / 4 < s.scratch.scratch_buf.length := by omega
                ds_csteps!
                let scr' := (s.scratch.scratch_buf.set (520 / 4) (nmask.setWidth 32)).set
                  (524 / 4) ((nmask >>> 32).setWidth 32)
                have hscrl' : scr'.length = c.scratch_cap := by simp [scr', hscrl]
                have hdw' : FullDenseInvW c F0 F_cur
                    { s with
                      core := { s.core with lit_mark := s.core.lit_mark }
                      scratch := { s.scratch with scratch_buf := scr' } } :=
                  FullDenseInvW.with_litMark_scr hdw hlml hscrl' hdw.2.2.1
                have hnmask_rec :
                    (scr'[130]?.getD 0#32).setWidth 64 |||
                      ((scr'[131]?.getD 0#32).setWidth 64 <<< 32) = nmask := by
                  have h130e : scr'[130]? = some (nmask.setWidth 32) := by
                    simp only [scr', show 520 / 4 = 130 from rfl, show 524 / 4 = 131 from rfl]
                    rw [List.getElem?_set_ne (by decide), List.getElem?_set_self (by omega)]
                  have h131e : scr'[131]? = some ((nmask >>> 32).setWidth 32) := by
                    simp only [scr', show 520 / 4 = 130 from rfl, show 524 / 4 = 131 from rfl]
                    rw [List.getElem?_set_self (by simp [hscrl]; omega)]
                  rw [h130e, h131e, Option.getD_some, Option.getD_some]
                  exact bv64_mask_split_32 nmask
                refine hQ true s.core.lit_mark scr' _ hdw'
                  (fun k _ hk1 hk2 => by
                    simp only [scr', show 520 / 4 = 130 from rfl, show 524 / 4 = 131 from rfl]
                    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)])
                  (fun h => Bool.noConfusion h)
                  (fun _ hnn => ?_) hm
                rw [hnmask_rec]; refine ⟨hnmask_hi hnn, unsat_of_filter_res fun l hl => ?_⟩
                have hl_ar : l < 2 * c.max_vars := hlits_lt l (List.mem_filter.mp hl).1
                have hcnt_le : rest.length ≤
                    rest.countP (fun l => lm2[l ^^^ 1]?.getD 0#8 == 2#8) :=
                  hmatch_eq ▸ hge_nat
                have hp2 := forall_of_length_le_countP hcnt_le l hl
                have hm2_l : lm2[l ^^^ 1]? = some 2#8 := by
                  have hlt_x : l ^^^ 1 < lm2.length := by
                    rw [hlm2_len]; exact bv32_xor1_lt_even hl_ar
                  rw [List.getElem?_eq_getElem hlt_x, Option.getD_some] at hp2
                  rw [List.getElem?_eq_getElem hlt_x, beq_iff_eq.mp hp2]
                obtain ⟨k, hk_lt, hk_bit, hk_eq⟩ :=
                  (hlm2_spec (l ^^^ 1) (bv32_xor1_lt_even hl_ar)).2.2 hm2_l hnn
                exact ⟨k, hj_eq ▸ hk_lt, hk_bit, hk_eq⟩
              · -- `matched < need`: return `false`, state unchanged
                ds_steps
                exact hQ false s.core.lit_mark s.scratch.scratch_buf m3 hdw
                  (fun _ _ _ _ => rfl) (fun _ => ⟨rfl, rfl⟩)
                  (fun h => Bool.noConfusion h) hm3

/-! ## 3. `full_bve_gates_wp` (`FullDefSweep` #3) -/

/-- **`full_bve_gates`**: checks binary complement pairs and one-sided AND gates in
`P × N`, falling back to `full_find_definition`, and guaranteeing `FullDefGateUnsat` on exit. -/
theorem full_bve_gates_wp (Γ : Env)
    (hMark : ∀ args m Q X, fullBveMarkAndDefSpec args m Q X →
      Γ "full_bve_mark_and" [i64, i32, i32, i32, i32] [.bool] args m Q X)
    (hFindDef : ∀ args m Q X, fullFindDefinitionSpec args m Q X →
      Γ "full_find_definition" [i64, i32, i32, i32] [] args m Q X) :
    ∀ args m Q X, fullBveGatesDefSpec args m Q X →
      Func.wp Γ full_bve_gates_body args m Q X := by
  rintro ⟨h, v, np, nn, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, s, R, rfl, hdw, h132, htmk0, hv_lt, hnp64, hnn64, hpos, hneg, hm, hQ⟩
  have hmv := c.hmaxv; have hsc := c.hscr; unfold dimacsBound at hmv hsc
  have hcl := hdw.1.core_ok; have hsl := hdw.1.scratch_ok; have hw := hdw.2.1
  have hcv := hcl.cur_vars_le; have hlml := hcl.lit_mark_len; have hscrl := hsl.scratch_buf_len
  have h128 : 512 / 4 < s.scratch.scratch_buf.length := by omega
  have h129 : 516 / 4 < s.scratch.scratch_buf.length := by omega
  have h130 : 520 / 4 < s.scratch.scratch_buf.length := by omega
  have h131 : 524 / 4 < s.scratch.scratch_buf.length := by omega
  have hpl_n : (v <<< 1#32).toNat = 2 * v.toNat := by
    rw [show (v <<< 1#32 : BitVec 32) = v <<< (1 : Nat) from rfl,
      FullDefSweepTactics.bv32_shl1_nat]
    omega
  have hnl_n : ((v <<< 1#32) ^^^ 1#32).toNat = 2 * v.toNat + 1 := by
    rw [bv32_xor1_eq_litNeg, hpl_n, litNeg_eq]; simp [show (2 * v.toNat) % 2 = 0 by omega]
  unfold Func.wp full_bve_gates_body
  ds_csteps!
  let scr0 := (((s.scratch.scratch_buf.set 128 0#32).set 129 0#32).set 130 0#32).set 131 0#32
  have hscr0_eq :
      ((((s.scratch.scratch_buf.set (512 / 4) 0#32).set (516 / 4) 0#32).set
        (520 / 4) 0#32).set (524 / 4) 0#32) = scr0 := rfl
  have hscr0_l : scr0.length = c.scratch_cap := by simp [scr0, hscrl]
  have hscr0_out : ∀ k < c.scratch_cap,
      k < 128 ∨ (132 ≤ k ∧ (k < 256 ∨ c.scratch_cap < 10240)) →
      scr0[k]? = s.scratch.scratch_buf[k]? := fun k _ hk => by
    simp only [scr0]
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
  have hscr0_128 : scr0[128]? = some 0#32 ∧ scr0[129]? = some 0#32 ∧
      scr0[130]? = some 0#32 ∧ scr0[131]? = some 0#32 := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [scr0]; rw [List.getElem?_set_ne (by decide), List.getElem?_set_ne (by decide),
        List.getElem?_set_ne (by decide), List.getElem?_set_self (by omega)]
    · simp only [scr0]; rw [List.getElem?_set_ne (by decide), List.getElem?_set_ne (by decide),
        List.getElem?_set_self (by simp [hscrl]; omega)]
    · simp only [scr0]; rw [List.getElem?_set_ne (by decide),
        List.getElem?_set_self (by simp [hscrl]; omega)]
    · simp only [scr0]; rw [List.getElem?_set_self (by simp [hscrl]; omega)]
  have hdw0 : FullDenseInvW c F0 F_cur
      { s with
        core := { s.core with lit_mark := s.core.lit_mark }
        scratch := { s.scratch with scratch_buf := scr0 } } :=
    FullDenseInvW.with_litMark_scr hdw hlml hscr0_l hdw.2.2.1
  have hm0 : (FullMem c { s with
      core := { s.core with lit_mark := s.core.lit_mark }
      scratch := { s.scratch with scratch_buf := scr0 } } ⋆ R) m := by
    simpa [hscr0_eq] using hm
  refine wp_loop_inv (ts := [i32])
    (fun (i, _) mi =>
      i.toNat ≤ np.toNat ∧
      ∃ (lm' : List (BitVec 8)) (scr' : List (BitVec 32)),
        let si : FullState :=
          { s with
            core := { s.core with lit_mark := lm' }
            scratch := { s.scratch with scratch_buf := scr' } }
        FullDenseInvW c F0 F_cur si ∧
        (∀ k < c.scratch_cap, k < 128 ∨ (132 ≤ k ∧ (k < 256 ∨ c.scratch_cap < 10240)) →
          scr'[k]? = s.scratch.scratch_buf[k]?) ∧
        scr'[128]? = some 0#32 ∧ scr'[129]? = some 0#32 ∧
        scr'[130]? = some 0#32 ∧ scr'[131]? = some 0#32 ∧
        (FullMem c si ⋆ R) mi)
    (fun (i, _) _ => np.toNat - i.toNat)
    ?_ ?_
  · intro J1 hJ1; ds_steps
    exact hJ1 (0#32, ()) m ⟨Nat.zero_le _, s.core.lit_mark, scr0, hdw0, hscr0_out,
      hscr0_128.1, hscr0_128.2.1, hscr0_128.2.2.1, hscr0_128.2.2.2, hm0⟩
  · clear m hm hm0 h128 h129 h130 h131 scr0 hscr0_eq hscr0_l hscr0_out hscr0_128 hdw0 hlml
    rintro J1 ⟨i, ⟨⟩⟩ ml ⟨hi_le, lm', scr', hdw', hout', h128', h129', h130', h131', hm'⟩ ih1
    let si : FullState :=
      { s with
        core := { s.core with lit_mark := lm' }
        scratch := { s.scratch with scratch_buf := scr' } }
    have hscrl' : scr'.length = c.scratch_cap := hdw'.1.scratch_ok.scratch_buf_len
    have hlml' : lm'.length = 2 * c.max_vars := hdw'.1.core_ok.lit_mark_len
    fc_split_fast
    · have hi_lt : i.toNat < np.toNat := by
        simp only [BitVec.ult, decide_eq_true_eq] at hc; exact hc
      clear hc
      have hi_scr : i.toNat < scr'.length := by omega
      have hwp_eq : scr'[i.toNat]? = s.scratch.scratch_buf[i.toNat]? :=
        hout' i.toNat (by omega) (Or.inl (by omega))
      have hwp_get : scr'[i.toNat]'hi_scr = s.scratch.scratch_buf[i.toNat]?.getD 0#32 :=
        Option.some.inj (by
          rw [← List.getElem?_eq_getElem hi_scr, hwp_eq,
            List.getElem?_eq_getElem (by omega : i.toNat < s.scratch.scratch_buf.length)]; rfl)
      have hwp_z : scr'[(i.setWidth 64).toNat]'(by rw [bv_c0_zext32_64]; exact hi_scr) =
          s.scratch.scratch_buf[i.toNat]?.getD 0#32 := by
        rw [list_getElem_congr (bv_c0_zext32_64 i) _ hi_scr]; exact hwp_get
      fc_split_fast
      · -- `(wp & PW_BIN_FLAG) != 0`: inner scan `while (j < nn)`
        have hwp_bin : (s.scratch.scratch_buf[i.toNat]?.getD 0#32 &&& 0x80000000#32) ≠ 0#32 := by
          have h := bne_iff_ne.mp hc
          change (scr'[(i.setWidth 64).toNat]'_ &&& 0x80000000#32) ≠ 0#32 at h
          rwa [← hwp_z]
        clear hc
        refine wp_loop_inv (ts := [i32])
          (fun (j, _) mj => j.toNat ≤ nn.toNat ∧ mj = ml)
          (fun (j, _) _ => nn.toNat - j.toNat)
          ?_ ?_
        · intro J2 hJ2; ds_steps; exact hJ2 (0#32, ()) ml ⟨Nat.zero_le _, rfl⟩
        · rintro J2 ⟨j, ⟨⟩⟩ mj ⟨hj_le, rfl⟩ ih2
          have h128_l : 512 / 4 < scr'.length := by omega
          have h129_l : 516 / 4 < scr'.length := by omega
          have h130_l : 520 / 4 < scr'.length := by omega
          have h131_l : 524 / 4 < scr'.length := by omega
          fc_split_fast
          · have hj_lt : j.toNat < nn.toNat := by
              simp only [BitVec.ult, decide_eq_true_eq] at hc; exact hc
            clear hc
            fc_split_fast
            · have hwn_bin_hc := bne_iff_ne.mp hc; clear hc
              fc_split_fast
              · -- Binary pair match found: store `pm = 1 <<< i`, `nm = 1 <<< j` and return
                have hot_hc := beq_iff_eq.mp hc; clear hc
                have hj64_n : (64#32 + j).toNat = 64 + j.toNat := by bv_omega
                have hj_scr : (64 + j.toNat) < scr'.length := by omega
                have hwn_eq : scr'[64 + j.toNat]? = s.scratch.scratch_buf[64 + j.toNat]? :=
                  hout' (64 + j.toNat) (by omega) (Or.inl (by omega))
                have hwn_z : scr'[((64#32 + j).setWidth 64).toNat]'
                    (by rw [bv_c0_zext32_64, hj64_n]; exact hj_scr) =
                    s.scratch.scratch_buf[64 + j.toNat]?.getD 0#32 := by
                  rw [list_getElem_congr (by rw [bv_c0_zext32_64, hj64_n]) _ hj_scr,
                    ← Option.getD_some (a := scr'[64 + j.toNat]'_) (b := 0#32),
                    ← List.getElem?_eq_getElem hj_scr, hwn_eq]
                have hwn_bin :
                    (s.scratch.scratch_buf[64 + j.toNat]?.getD 0#32 &&& 0x80000000#32) ≠
                      0#32 := by
                  change (scr'[((64#32 + j).setWidth 64).toNat]'_ &&& 0x80000000#32) ≠ 0#32
                    at hwn_bin_hc
                  rwa [← hwn_z]
                have hot_eq : (s.scratch.scratch_buf[64 + j.toNat]?.getD 0#32 &&& 0x7FFFFFFF#32) =
                    (s.scratch.scratch_buf[i.toNat]?.getD 0#32 &&& 0x7FFFFFFF#32) ^^^ 1#32 := by
                  change (scr'[((64#32 + j).setWidth 64).toNat]'_ &&& 0x7FFFFFFF#32) =
                    (scr'[(i.setWidth 64).toNat]'_ &&& 0x7FFFFFFF#32) ^^^ 1#32 at hot_hc
                  rwa [← hwn_z, ← hwp_z]
                ds_csteps!
                have hi_mod : (i.setWidth 64).toNat % 64 = i.toNat := by bv_omega
                have hj_mod : (j.setWidth 64).toNat % 64 = j.toNat := by bv_omega
                let pm : BitVec 64 := 1#64 <<< ((i.setWidth 64).toNat % 64)
                let nm : BitVec 64 := 1#64 <<< ((j.setWidth 64).toNat % 64)
                let scr_f : List (BitVec 32) :=
                  (((scr'.set (512 / 4) (pm.setWidth 32)).set (516 / 4)
                    ((pm >>> 32).setWidth 32)).set (520 / 4) (nm.setWidth 32)).set (524 / 4)
                    ((nm >>> 32).setWidth 32)
                have hscr_f_len : scr_f.length = c.scratch_cap := by simp [scr_f, hscrl']
                have h8 : scr_f[128]? = some (pm.setWidth 32) := by
                  simp only [scr_f, show 512 / 4 = 128 from rfl, show 516 / 4 = 129 from rfl,
                    show 520 / 4 = 130 from rfl, show 524 / 4 = 131 from rfl]
                  rw [List.getElem?_set_ne (by decide), List.getElem?_set_ne (by decide),
                    List.getElem?_set_ne (by decide), List.getElem?_set_self (by omega)]
                have h9 : scr_f[129]? = some ((pm >>> 32).setWidth 32) := by
                  simp only [scr_f, show 512 / 4 = 128 from rfl, show 516 / 4 = 129 from rfl,
                    show 520 / 4 = 130 from rfl, show 524 / 4 = 131 from rfl]
                  rw [List.getElem?_set_ne (by decide), List.getElem?_set_ne (by decide),
                    List.getElem?_set_self (by simp [hscrl']; omega)]
                have ha : scr_f[130]? = some (nm.setWidth 32) := by
                  simp only [scr_f, show 512 / 4 = 128 from rfl, show 516 / 4 = 129 from rfl,
                    show 520 / 4 = 130 from rfl, show 524 / 4 = 131 from rfl]
                  rw [List.getElem?_set_ne (by decide),
                    List.getElem?_set_self (by simp [hscrl']; omega)]
                have hb : scr_f[131]? = some ((nm >>> 32).setWidth 32) := by
                  simp only [scr_f, show 512 / 4 = 128 from rfl, show 516 / 4 = 129 from rfl,
                    show 520 / 4 = 130 from rfl, show 524 / 4 = 131 from rfl]
                  rw [List.getElem?_set_self (by simp [hscrl']; omega)]
                have hout_f : ∀ k < c.scratch_cap, k ≠ 128 → k ≠ 129 → k ≠ 130 → k ≠ 131 →
                    scr_f[k]? = scr'[k]? := fun k hk1 h1 h2 h3 h4 => by
                  simp only [scr_f, show 512 / 4 = 128 from rfl, show 516 / 4 = 129 from rfl,
                    show 520 / 4 = 130 from rfl, show 524 / 4 = 131 from rfl]
                  rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
                    List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
                have hdw_f : FullDenseInvW c F0 F_cur
                    { s with
                      core := { s.core with lit_mark := lm' }
                      scratch := { s.scratch with scratch_buf := scr_f } } :=
                  FullDenseInvW.with_litMark_scr hdw' hlml' hscr_f_len hdw'.2.2.1
                have hpm_rec : (scr_f[128]?.getD 0#32).setWidth 64 |||
                    ((scr_f[129]?.getD 0#32).setWidth 64 <<< 32) = 1#64 <<< i.toNat := by
                  rw [h8, h9, Option.getD_some, Option.getD_some, bv64_mask_split_32]
                  dsimp only [pm]; rw [hi_mod]
                have hnm_rec : (scr_f[130]?.getD 0#32).setWidth 64 |||
                    ((scr_f[131]?.getD 0#32).setWidth 64 <<< 32) = 1#64 <<< j.toNat := by
                  rw [ha, hb, Option.getD_some, Option.getD_some, bv64_mask_split_32]
                  dsimp only [nm]; rw [hj_mod]
                refine hQ _ _ hdw_f htmk0 rfl rfl rfl rfl (le_refl _) (fun k hk1 hk2 => ?_) ?_
                  (by assumption)
                · have hne : k ≠ 128 ∧ k ≠ 129 ∧ k ≠ 130 ∧ k ≠ 131 := by omega
                  exact (hout_f k hk1 hne.1 hne.2.1 hne.2.2.1 hne.2.2.2).trans (hout' k hk1 hk2)
                · rw [hpm_rec, hnm_rec]
                  refine fullDefGateUnsat_of_unsat
                    (fun _ => by apply BitVec.eq_of_getLsbD_eq; intro b _; simp; omega)
                    (fun _ => by apply BitVec.eq_of_getLsbD_eq; intro b _; simp; omega) ?_
                  rw [maskedOccRestCls_single_bit hi_lt hnp64,
                    maskedOccRestCls_single_bit hj_lt hnn64]
                  let ot := (s.scratch.scratch_buf[i.toNat]?.getD 0#32 &&& 0x7FFFFFFF#32).toNat
                  have hbp : bveOccRestLits s (2 * v.toNat)
                      (s.scratch.scratch_buf[i.toNat]?.getD 0#32) = [ot] := by
                    simp [bveOccRestLits, hwp_bin, ot]
                  have hbn : bveOccRestLits s (2 * v.toNat + 1)
                      (s.scratch.scratch_buf[64 + j.toNat]?.getD 0#32) = [ot ^^^ 1] := by
                    simp [bveOccRestLits, hwn_bin, hot_eq, ot, BitVec.toNat_xor]
                  refine unsat_of_subclauses (cs1 := [[ot], [ot ^^^ 1]]) (fun cl hcl => ?_)
                    unsat_of_unit_pair
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at hcl
                  rcases hcl with rfl | rfl
                  · exact List.mem_append_left _ (List.mem_append_right _ (by simp [hbp]))
                  · exact List.mem_append_right _ (by simp [hbn])
              · ds_steps; exact ih2 (j + 1#32, ()) _ (by bv_omega) ⟨by bv_omega, rfl⟩
            · ds_steps; exact ih2 (j + 1#32, ()) _ (by bv_omega) ⟨by bv_omega, rfl⟩
          · ds_steps; exact ih1 (i + 1#32, ()) _ (by bv_omega) ⟨by bv_omega, lm', scr', hdw', hout',
              h128', h129', h130', h131', hm'⟩
      · -- `(wp & PW_BIN_FLAG) == 0`: call `full_bve_mark_and`
        have hnot_bin :
            ¬ (s.scratch.scratch_buf[i.toNat]?.getD 0#32 &&& 0x80000000#32) ≠ 0#32 := by
          have h := bne_eq_false_iff_eq.mp hc
          change (scr'[(i.setWidth 64).toNat]'_ &&& 0x80000000#32) = 0#32 at h
          rw [← hwp_z]; exact fun hne => hne h
        clear hc
        have hpos_i := hpos i.toNat hi_lt
        unfold FullDefSweep.FullBveEntryOkW Full.FullBveEntryOkW at hpos_i
        rw [ite_eq_right hnot_bin] at hpos_i
        ds_steps; c0_call hMark
        refine ⟨c, F0, F_cur, si, R, rfl, hdw', h132, ?_, ?_, by bv_omega, ?_, hm',
          fun ok lm'' scr'' m'' hdw'' hout'' hok_f hok_t hm'' => ?_⟩
        · unfold fullArenaClauseRefs fullArenaClauseRefsCore; rw [hwp_z]; exact hpos_i.1
        · unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore; rw [hwp_z]
          exact hpos_i.2
        · intro j hj
          have hwn_eq : scr'[64 + j]? = s.scratch.scratch_buf[64 + j]? :=
            hout' (64 + j) (by omega) (Or.inl (by omega))
          have hneg_j := (fullBveEntryOkW_congr (s1 := s) (s2 := si) rfl rfl rfl rfl).mp (hneg j hj)
          first
          | rw [hpl_n]
          | rw [show (v <<< (1 : BitVec 32)) = v <<< 1#32 from rfl, hpl_n]
          | rw [show (v <<< (1 : Nat)).toNat = 2 * v.toNat by
              rw [FullDefSweepTactics.bv32_shl1_nat]; omega]
          rw [(FullSweepVarHelpers.nat_2x_xor1 v.toNat).1]
          dsimp only [si]; rw [show (64 : BitVec 32).toNat = 64 from rfl, hwn_eq]
          exact hneg_j
        · have hscrl'' : scr''.length = c.scratch_cap := hdw''.1.scratch_ok.scratch_buf_len
          have hlml'' : lm''.length = 2 * c.max_vars := hdw''.1.core_ok.lit_mark_len
          fc_split_fast
          · -- `ok = true`: store `pm = 1 <<< i` in `scr''[128..129]` and return
            have hok_true := hc; clear hc
            have h128_l : 512 / 4 < scr''.length := by omega
            have h129_l : 516 / 4 < scr''.length := by omega
            ds_csteps!
            have hi_mod : (i.setWidth 64).toNat % 64 = i.toNat := by bv_omega
            let pm : BitVec 64 := 1#64 <<< ((i.setWidth 64).toNat % 64)
            let scr_f : List (BitVec 32) :=
              (scr''.set (512 / 4) (pm.setWidth 32)).set (516 / 4) ((pm >>> 32).setWidth 32)
            have hscr_f_len : scr_f.length = c.scratch_cap := by simp [scr_f, hscrl'']
            have h8 : scr_f[128]? = some (pm.setWidth 32) := by
              simp only [scr_f, show 512 / 4 = 128 from rfl, show 516 / 4 = 129 from rfl]
              rw [List.getElem?_set_ne (by decide), List.getElem?_set_self (by omega)]
            have h9 : scr_f[129]? = some ((pm >>> 32).setWidth 32) := by
              simp only [scr_f, show 512 / 4 = 128 from rfl, show 516 / 4 = 129 from rfl]
              rw [List.getElem?_set_self (by simp [hscrl'']; omega)]
            have ha : scr_f[130]? = scr''[130]? := by
              simp only [scr_f, show 512 / 4 = 128 from rfl, show 516 / 4 = 129 from rfl]
              rw [List.getElem?_set_ne (by decide), List.getElem?_set_ne (by decide)]
            have hb : scr_f[131]? = scr''[131]? := by
              simp only [scr_f, show 512 / 4 = 128 from rfl, show 516 / 4 = 129 from rfl]
              rw [List.getElem?_set_ne (by decide), List.getElem?_set_ne (by decide)]
            have hout_f : ∀ k < c.scratch_cap, k ≠ 128 → k ≠ 129 → scr_f[k]? = scr''[k]? :=
              fun k hk1 h1 h2 => by
                simp only [scr_f, show 512 / 4 = 128 from rfl, show 516 / 4 = 129 from rfl]
                rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
            have hdw_f : FullDenseInvW c F0 F_cur
                { s with
                  core := { s.core with lit_mark := lm'' }
                  scratch := { s.scratch with scratch_buf := scr_f } } :=
              FullDenseInvW.with_litMark_scr hdw'' hlml'' hscr_f_len hdw''.2.2.1
            have hpm_rec : (scr_f[128]?.getD 0#32).setWidth 64 |||
                ((scr_f[129]?.getD 0#32).setWidth 64 <<< 32) = 1#64 <<< i.toNat := by
              rw [h8, h9, Option.getD_some, Option.getD_some, bv64_mask_split_32]
              dsimp only [pm]; rw [hi_mod]
            let nm := (scr''[130]?.getD 0#32).setWidth 64 |||
              ((scr''[131]?.getD 0#32).setWidth 64 <<< 32)
            have hnm_rec : (scr_f[130]?.getD 0#32).setWidth 64 |||
                ((scr_f[131]?.getD 0#32).setWidth 64 <<< 32) = nm := by rw [ha, hb]
            obtain ⟨hnm_hi, hunsat⟩ := hok_t hok_true hnn64
            refine hQ _ _ hdw_f htmk0 rfl rfl rfl rfl (le_refl _) (fun k hk1 hk2 => ?_) ?_
              (by assumption)
            · have hne : k ≠ 128 ∧ k ≠ 129 := by omega
              exact (hout_f k hk1 hne.1 hne.2).trans
                ((hout'' k hk1 (by omega) (by omega)).trans (hout' k hk1 hk2))
            · rw [hpm_rec, hnm_rec]
              refine fullDefGateUnsat_of_unsat
                (fun _ => by apply BitVec.eq_of_getLsbD_eq; intro b _; simp; omega)
                (fun _ => hnm_hi) ?_
              have hsub_cls : ∀ cl ∈
                  [(fullArenaClauseLits si
                    (scr'[(i.setWidth 64).toNat]'(by
                      rw [bv_c0_zext32_64]; exact hi_scr)).toNat).filter
                    (· != (v <<< 1#32).toNat)] ++
                  maskedOccRestCls si ((v <<< 1#32).toNat ^^^ 1) 64 nn.toNat nm,
                  cl ∈ level0ForcedUnits s ++
                    maskedOccRestCls s (2 * v.toNat) 0 np.toNat (1#64 <<< i.toNat) ++
                    maskedOccRestCls s (2 * v.toNat + 1) 64 nn.toNat nm := by
                intro cl hcl
                rw [List.mem_append] at hcl
                rcases hcl with hcl1 | hcl2
                · rw [List.mem_singleton] at hcl1; subst cl
                  refine List.mem_append_left _ (List.mem_append_right _ ?_)
                  rw [maskedOccRestCls_single_bit hi_lt hnp64, List.mem_singleton]
                  rw [hwp_z, hpl_n]
                  dsimp only [si]
                  simp [bveOccRestLits, hnot_bin, fullArenaClauseLits,
                    fullArenaClauseLitsCore, fullArenaClauseSizeCore]
                · refine List.mem_append_right _ ?_
                  have hcongr := maskedOccRestCls_congr (s1 := s) (s2 := si)
                    (except := 2 * v.toNat + 1) (off := 64) (cnt := nn.toNat) (mask := nm)
                    rfl (by omega) (fun k hk => hout' k (by omega) (Or.inl hk))
                  rw [hpl_n, (FullSweepVarHelpers.nat_2x_xor1 v.toNat).1] at hcl2
                  simpa only [hcongr] using hcl2
              exact unsat_of_subclauses hsub_cls hunsat
          · -- `ok = false`: `128..131` preserved (`0`), continue `i + 1`
            have ⟨h130_p, h131_p⟩ := hok_f hc; clear hc
            ds_steps
            exact ih1 (i + 1#32, ()) m'' (by bv_omega)
              ⟨by bv_omega, lm'', scr'', hdw'',
               fun k hk1 hk2 => (hout'' k hk1 (by omega) (by omega)).trans (hout' k hk1 hk2),
               (hout'' 128 (by omega) (by decide) (by decide)).trans h128',
               (hout'' 129 (by omega) (by decide) (by decide)).trans h129',
               h130_p.trans h130', h131_p.trans h131', hm''⟩
    · -- Exit Loop 1 (`i = np`): run Loop 2 (`while (j < nn)`) then fallback `full_find_definition`
      clear hc
      refine wp_loop_inv (ts := [i32])
        (fun (j, _) mj =>
          j.toNat ≤ nn.toNat ∧
          ∃ (lmj : List (BitVec 8)) (scrj : List (BitVec 32)),
            let sj : FullState :=
              { s with
                core := { s.core with lit_mark := lmj }
                scratch := { s.scratch with scratch_buf := scrj } }
            FullDenseInvW c F0 F_cur sj ∧
            (∀ k < c.scratch_cap, k < 128 ∨ (132 ≤ k ∧ (k < 256 ∨ c.scratch_cap < 10240)) →
              scrj[k]? = s.scratch.scratch_buf[k]?) ∧
            scrj[128]? = some 0#32 ∧ scrj[129]? = some 0#32 ∧
            scrj[130]? = some 0#32 ∧ scrj[131]? = some 0#32 ∧
            (FullMem c sj ⋆ R) mj)
        (fun (j, _) _ => nn.toNat - j.toNat)
        ?_ ?_
      · intro J2 hJ2; ds_steps
        exact hJ2 (0#32, ()) ml ⟨Nat.zero_le _, lm', scr', hdw', hout',
          h128', h129', h130', h131', hm'⟩
      · clear hscrl' hlml' si lm' scr' hdw' hout' h128' h129' h130' h131' hm' ih1
        rintro J2 ⟨j, ⟨⟩⟩ mj ⟨hj_le, lmj, scrj, hdwj, houtj, h128j, h129j, h130j, h131j, hmj⟩ ih2
        let sj : FullState :=
          { s with
            core := { s.core with lit_mark := lmj }
            scratch := { s.scratch with scratch_buf := scrj } }
        have hscrlj : scrj.length = c.scratch_cap := hdwj.1.scratch_ok.scratch_buf_len
        have hlmlj : lmj.length = 2 * c.max_vars := hdwj.1.core_ok.lit_mark_len
        fc_split_fast
        · -- `j < nn`: `(wn & PW_BIN_FLAG) == 0 && full_bve_mark_and(...)`
          have hj_lt : j.toNat < nn.toNat := by
            simp only [BitVec.ult, decide_eq_true_eq] at hc; exact hc
          clear hc
          have hj64_n : ((64 : BitVec 32) + j).toNat = 64 + j.toNat := by bv_omega
          have hj_scr : (64 + j.toNat) < scrj.length := by omega
          have hwn_eq : scrj[64 + j.toNat]? = s.scratch.scratch_buf[64 + j.toNat]? :=
            houtj (64 + j.toNat) (by omega) (Or.inl (by omega))
          have hwn_z : scrj[(((64 : BitVec 32) + j).setWidth 64).toNat]'
              (by rw [bv_c0_zext32_64, hj64_n]; exact hj_scr) =
              s.scratch.scratch_buf[64 + j.toNat]?.getD 0#32 := by
            rw [list_getElem_congr (by rw [bv_c0_zext32_64, hj64_n]) _ hj_scr,
              ← Option.getD_some (a := scrj[64 + j.toNat]'_) (b := 0#32),
              ← List.getElem?_eq_getElem hj_scr, hwn_eq]
          fc_split_fast
          · -- `(wn & PW_BIN_FLAG) == 0`
            have hnot_bin :
                ¬ (s.scratch.scratch_buf[64 + j.toNat]?.getD 0#32 &&& 0x80000000#32) ≠ 0#32 := by
              have h := beq_iff_eq.mp hc
              change (scrj[(((64 : BitVec 32) + j).setWidth 64).toNat]'_ &&& 0x80000000#32) =
                0#32 at h
              rw [← hwn_z]; exact fun hne => hne h
            clear hc
            have hneg_j := hneg j.toNat hj_lt
            unfold FullDefSweep.FullBveEntryOkW Full.FullBveEntryOkW at hneg_j
            rw [ite_eq_right hnot_bin] at hneg_j
            ds_steps; c0_call hMark
            refine ⟨c, F0, F_cur, sj, R, rfl, hdwj, h132, ?_, ?_, by bv_omega, ?_, hmj,
              fun ok lm'' scr'' m'' hdw'' hout'' hok_f hok_t hm'' => ?_⟩
            · unfold fullArenaClauseRefs fullArenaClauseRefsCore
              rw [hwn_z]; exact hneg_j.1
            · unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore
              rw [hwn_z]; exact hneg_j.2
            · intro k hk
              have hwp_eq : scrj[k]? = s.scratch.scratch_buf[k]? :=
                houtj k (by omega) (Or.inl (by omega))
              have hpos_k := (fullBveEntryOkW_congr (s1 := s) (s2 := sj) rfl rfl rfl rfl).mp
                (hpos k hk)
              have hxor_e : ((v <<< 1 ^^^ 1 : BitVec 32)).toNat ^^^ 1 = 2 * v.toNat := by
                rw [show (v <<< 1 ^^^ 1 : BitVec 32) = (v <<< 1#32) ^^^ 1#32 from rfl, hnl_n]
                exact (FullSweepVarHelpers.nat_2x_xor1 v.toNat).2
              rw [hxor_e]; dsimp only [sj]; rw [show (0 : BitVec 32).toNat = 0 from rfl,
                Nat.zero_add, hwp_eq]
              exact hpos_k
            · have hscrl'' : scr''.length = c.scratch_cap := hdw''.1.scratch_ok.scratch_buf_len
              have hlml'' : lm''.length = 2 * c.max_vars := hdw''.1.core_ok.lit_mark_len
              fc_split_fast
              · -- `ok = true`: `pm` from `scr''[130..131]` -> `128..129`, `1 <<< j` -> `130..131`
                have hok_true := hc; clear hc
                have h128_l : 512 / 4 < scr''.length := by omega
                have h129_l : 516 / 4 < scr''.length := by omega
                have h130_l : 520 / 4 < scr''.length := by omega
                have h131_l : 524 / 4 < scr''.length := by omega
                ds_csteps!
                have hj_mod : (j.setWidth 64).toNat % 64 = j.toNat := by bv_omega
                let pm := (scr''[130]?.getD 0#32).setWidth 64 |||
                  ((scr''[131]?.getD 0#32).setWidth 64 <<< 32)
                let pm_c := (scr''[520 / 4]'(by omega)).setWidth 64 |||
                  ((scr''[524 / 4]'(by omega)).setWidth 64 <<< 32)
                have hpm_eq : pm = pm_c := by
                  simp only [pm, pm_c,
                    List.getElem?_eq_getElem (by omega : 130 < scr''.length),
                    List.getElem?_eq_getElem (by omega : 131 < scr''.length),
                    Option.getD_some, show 520 / 4 = 130 from rfl, show 524 / 4 = 131 from rfl]
                let nm : BitVec 64 := 1#64 <<< ((j.setWidth 64).toNat % 64)
                let scr_f : List (BitVec 32) :=
                  (((scr''.set (512 / 4) (pm_c.setWidth 32)).set (516 / 4)
                    ((pm_c >>> 32).setWidth 32)).set (520 / 4) (nm.setWidth 32)).set (524 / 4)
                    ((nm >>> 32).setWidth 32)
                have hscr_f_len : scr_f.length = c.scratch_cap := by simp [scr_f, hscrl'']
                have h8 : scr_f[128]? = some (pm.setWidth 32) := by
                  simp only [scr_f, show 512 / 4 = 128 from rfl, show 516 / 4 = 129 from rfl,
                    show 520 / 4 = 130 from rfl, show 524 / 4 = 131 from rfl]
                  rw [List.getElem?_set_ne (by decide), List.getElem?_set_ne (by decide),
                    List.getElem?_set_ne (by decide), List.getElem?_set_self (by omega), hpm_eq]
                have h9 : scr_f[129]? = some ((pm >>> 32).setWidth 32) := by
                  simp only [scr_f, show 512 / 4 = 128 from rfl, show 516 / 4 = 129 from rfl,
                    show 520 / 4 = 130 from rfl, show 524 / 4 = 131 from rfl]
                  rw [List.getElem?_set_ne (by decide), List.getElem?_set_ne (by decide),
                    List.getElem?_set_self (by simp [hscrl'']; omega), hpm_eq]
                have ha : scr_f[130]? = some (nm.setWidth 32) := by
                  simp only [scr_f, show 512 / 4 = 128 from rfl, show 516 / 4 = 129 from rfl,
                    show 520 / 4 = 130 from rfl, show 524 / 4 = 131 from rfl]
                  rw [List.getElem?_set_ne (by decide),
                    List.getElem?_set_self (by simp [hscrl'']; omega)]
                have hb : scr_f[131]? = some ((nm >>> 32).setWidth 32) := by
                  simp only [scr_f, show 512 / 4 = 128 from rfl, show 516 / 4 = 129 from rfl,
                    show 520 / 4 = 130 from rfl, show 524 / 4 = 131 from rfl]
                  rw [List.getElem?_set_self (by simp [hscrl'']; omega)]
                have hout_f : ∀ k < c.scratch_cap, k ≠ 128 → k ≠ 129 → k ≠ 130 → k ≠ 131 →
                    scr_f[k]? = scr''[k]? := fun k hk1 h1 h2 h3 h4 => by
                  simp only [scr_f, show 512 / 4 = 128 from rfl, show 516 / 4 = 129 from rfl,
                    show 520 / 4 = 130 from rfl, show 524 / 4 = 131 from rfl]
                  rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
                    List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
                have hdw_f : FullDenseInvW c F0 F_cur
                    { s with
                      core := { s.core with lit_mark := lm'' }
                      scratch := { s.scratch with scratch_buf := scr_f } } :=
                  FullDenseInvW.with_litMark_scr hdw'' hlml'' hscr_f_len hdw''.2.2.1
                have hpm_rec : (scr_f[128]?.getD 0#32).setWidth 64 |||
                    ((scr_f[129]?.getD 0#32).setWidth 64 <<< 32) = pm := by
                  rw [h8, h9, Option.getD_some, Option.getD_some, bv64_mask_split_32]
                have hnm_rec : (scr_f[130]?.getD 0#32).setWidth 64 |||
                    ((scr_f[131]?.getD 0#32).setWidth 64 <<< 32) = 1#64 <<< j.toNat := by
                  rw [ha, hb, Option.getD_some, Option.getD_some, bv64_mask_split_32]
                  dsimp only [nm]; rw [hj_mod]
                obtain ⟨hpm_hi, hunsat⟩ := hok_t hok_true hnp64
                refine hQ _ _ hdw_f htmk0 rfl rfl rfl rfl (le_refl _) (fun k hk1 hk2 => ?_) ?_
                  (by assumption)
                · have hne : k ≠ 128 ∧ k ≠ 129 ∧ k ≠ 130 ∧ k ≠ 131 := by omega
                  exact (hout_f k hk1 hne.1 hne.2.1 hne.2.2.1 hne.2.2.2).trans
                    ((hout'' k hk1 (by omega) (by omega)).trans (houtj k hk1 hk2))
                · rw [hpm_rec, hnm_rec]
                  refine fullDefGateUnsat_of_unsat (fun _ => hpm_hi)
                    (fun _ => by apply BitVec.eq_of_getLsbD_eq; intro b _; simp; omega) ?_
                  have hsub_cls : ∀ cl ∈ [(fullArenaClauseLits sj
                      (scrj[(((64 : BitVec 32) + j).setWidth 64).toNat]'
                        (by rw [bv_c0_zext32_64, hj64_n]; exact hj_scr)).toNat).filter
                        (· != ((v <<< 1#32) ^^^ 1#32).toNat)] ++
                      maskedOccRestCls sj (((v <<< 1#32) ^^^ 1#32).toNat ^^^ 1) 0 np.toNat pm,
                      cl ∈ level0ForcedUnits s ++
                        maskedOccRestCls s (2 * v.toNat) 0 np.toNat pm ++
                        maskedOccRestCls s (2 * v.toNat + 1) 64 nn.toNat (1#64 <<< j.toNat) := by
                    intro cl hcl
                    rw [List.mem_append] at hcl
                    rcases hcl with hcl1 | hcl2
                    · rw [List.mem_singleton] at hcl1; subst cl
                      refine List.mem_append_right _ ?_
                      rw [maskedOccRestCls_single_bit hj_lt hnn64, List.mem_singleton]
                      rw [hwn_z, hnl_n]
                      dsimp only [sj]
                      simp [bveOccRestLits, hnot_bin, fullArenaClauseLits,
                        fullArenaClauseLitsCore, fullArenaClauseSizeCore]
                    · refine List.mem_append_left _ (List.mem_append_right _ ?_)
                      have hcongr := maskedOccRestCls_congr (s1 := s) (s2 := sj)
                        (except := 2 * v.toNat) (off := 0) (cnt := np.toNat) (mask := pm)
                        rfl (by omega) (fun k hk => houtj k (by omega) (Or.inl hk))
                      rw [hnl_n, (FullSweepVarHelpers.nat_2x_xor1 v.toNat).2] at hcl2
                      simpa only [hcongr] using hcl2
                  exact unsat_of_subclauses hsub_cls hunsat
              · -- `ok = false`: continue `j + 1`
                have ⟨h130_p, h131_p⟩ := hok_f hc; clear hc
                ds_steps
                exact ih2 (j + 1#32, ()) m'' (by bv_omega)
                  ⟨by bv_omega, lm'', scr'', hdw'',
                   fun k hk1 hk2 => (hout'' k hk1 (by omega) (by omega)).trans (houtj k hk1 hk2),
                   (hout'' 128 (by omega) (by decide) (by decide)).trans h128j,
                   (hout'' 129 (by omega) (by decide) (by decide)).trans h129j,
                   h130_p.trans h130j, h131_p.trans h131j, hm''⟩
          · -- `(wn & PW_BIN_FLAG) != 0`: skip `mark_and` and continue `j + 1`
            clear hc; ds_steps
            exact ih2 (j + 1#32, ()) mj (by bv_omega) ⟨by bv_omega, lmj, scrj, hdwj, houtj,
              h128j, h129j, h130j, h131j, hmj⟩
        · -- Exit Loop 2 (`j = nn`): tail-call `full_find_definition(h, v, np, nn)`
          clear hc; ds_steps; c0_call hFindDef
          refine ⟨c, F0, F_cur, sj, R, rfl, hdwj, h132, htmk0.congr rfl rfl, hv_lt, hnp64, hnn64,
            fun k hk => by
              have hwp_eq : scrj[k]? = s.scratch.scratch_buf[k]? :=
                houtj k (by omega) (Or.inl (by omega))
              have hpos_k := (fullBveEntryOkW_congr (s1 := s) (s2 := sj) rfl rfl rfl rfl).mp
                (hpos k hk)
              dsimp only [sj]; rw [hwp_eq]; exact hpos_k,
            fun k hk => by
              have hwn_eq : scrj[64 + k]? = s.scratch.scratch_buf[64 + k]? :=
                houtj (64 + k) (by omega) (Or.inl (by omega))
              have hneg_k := (fullBveEntryOkW_congr (s1 := s) (s2 := sj) rfl rfl rfl rfl).mp
                (hneg k hk)
              dsimp only [sj]; rw [hwn_eq]; exact hneg_k,
            hmj,
            fun s' m' hdw' htmk' hcv' hvals' har' harl' hfl' hout_fd hres hm' => ?_⟩
          refine hQ s' m' hdw' htmk' hcv' hvals' har' harl' hfl' (fun k hk1 hk2 => ?_) ?_ hm'
          · exact (hout_fd k hk1 hk2).trans (houtj k hk1 hk2)
          · rcases hres with hpres | huns
            · have hp0 : (s'.scratch.scratch_buf[128]?.getD 0#32).setWidth 64 |||
                  ((s'.scratch.scratch_buf[129]?.getD 0#32).setWidth 64 <<< 32) = 0#64 := by
                rw [hpres 128 (by simp), hpres 129 (by simp), h128j, h129j]; decide
              have hn0 : (s'.scratch.scratch_buf[130]?.getD 0#32).setWidth 64 |||
                  ((s'.scratch.scratch_buf[131]?.getD 0#32).setWidth 64 <<< 32) = 0#64 := by
                rw [hpres 130 (by simp), hpres 131 (by simp), h130j, h131j]; decide
              rw [hp0, hn0]; exact fullDefGateUnsat_zero s v.toNat np.toNat nn.toNat
            · exact fullDefGateUnsat_congr (s1 := s) (s2 := sj) rfl rfl rfl
                (fun k hk => houtj k (by omega) (Or.inl hk)) huns

/-! ## 4. `full_cong_extract_wp` (`FullDefSweep` #4) -/

/-- **`full_cong_extract`**: ticks-bounded version of `Full.full_cong_extract`, extracting AND,
XOR, and ITE gates into `scratch_buf[0 ..< ret)` with `ret ≤ g_cap` and `GateSeqOk`. -/
theorem full_cong_extract_wp (Γ : Env)
    (hNext : ∀ args m Q X, FullCongSpecs.fullArenaNextSpec args m Q X →
      Γ "full_arena_next" [i64, i32] [i32] args m Q X)
    (hHasBin : ∀ args m Q X, FullCongSpecs.fullHasBinSpec args m Q X →
      Γ "full_has_bin" [i64, i32, i32] [.bool] args m Q X)
    (hTryXorIte : ∀ args m Q X, FullCongSpecs.fullCongTryXorIteSpec args m Q X →
      Γ "full_cong_try_xor_ite" [i64, i32, i32, i32, i64, i64] [i64] args m Q X) :
    ∀ args m Q X, fullCongExtractTickSpec args m Q X →
      Func.wp Γ full_cong_extract_body args m Q X := by
  rintro ⟨h, g_cap, _tick_lim, ⟨⟩⟩ m0 Q X
    ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hnd, hcl0, hgc_le, hm0, hQ⟩
  have hac := c.harena; have hsc := c.hscr; have hmx := c.hmaxv
  unfold dimacsBound at hac hsc hmx; have hcl := hlen.core_ok; have hsl := hlen.scratch_ok
  have harl := hcl.arena_len_arr; have hale := hcl.arena_len_le; have hscrl := hsl.scratch_buf_len
  fc_steps; refine wp_loop_inv
    (fun (p, g_len, _ticks, ()) ml => ∃ scr : List (BitVec 32),
      scr.length = c.scratch_cap ∧
      p.toNat ≤ s.core.arena_len ∧
      (p.toNat = s.core.arena_len ∨ p.toNat ∈ fullArenaClauseRefs s) ∧
      g_len.toNat ≤ g_cap.toNat ∧
      GateSeqOk F_cur s.core.cur_vars scr g_len.toNat 0 ∧
      (FullMem c { s with scratch := { s.scratch with scratch_buf := scr } } ⋆ R) ml)
    (fun (p, _, _, ()) _ => s.core.arena_len - p.toNat)
    (fun J hJ => by
      fc_let
      refine hJ (0#64, 0#64, 0#64, ()) m0 ⟨s.scratch.scratch_buf, hscrl, Nat.zero_le _, ?_,
        Nat.zero_le _, .done, hm0⟩
      rcases Nat.eq_zero_or_pos s.core.arena_len with hz | hpos
      · exact Or.inl hz.symm
      · exact Or.inr (fullArenaClauseRefs_zero_mem hw hpos))
    (fun J (p, g_len, ticks, ()) ml ⟨scr, hscrl_c, hp_le, hp_mem, hgl_le, hseq_c, hml⟩ ih => ?_)
  let sc : FullState := { s with scratch := { s.scratch with scratch_buf := scr } }
  have hlen_c : sc.LengthsOk c :=
    ⟨hlen.core_ok, { hlen.scratch_ok with scratch_buf_len := hscrl_c }⟩
  have hq_out : Q (g_len, ()) ml := hQ g_len scr ml hscrl_c hgl_le hseq_c hml; fc_split_fast
  · have hp_lt : p.toNat < s.core.arena_len := by
      simp only [BitVec.ult, decide_eq_true_eq] at hc; bv_omega
    fc_split_fast
    · have hgl16 : g_len.toNat + 16 ≤ g_cap.toNat := by
        simp only [BitVec.ule, decide_eq_true_eq] at hc; bv_omega
      fc_split_fast
      · have hp_ref : p.toNat ∈ fullArenaClauseRefs s := hp_mem.resolve_left (by omega)
        have hp_wf := hw.arena.refs_wf p.toNat hp_ref
        have hp2_n : (p + 2).toNat = p.toNat + 2 :=
          show (p.toNat + 2) % 2 ^ 64 = p.toNat + 2 from Nat.mod_eq_of_lt (by omega)
        have hp_arr : p.toNat < s.core.arena.length := by omega
        have hp2_arr : (p + 2).toNat < s.core.arena.length := by omega
        fc_steps; c0_call hNext; refine ⟨c, sc, R, rfl, hlen_c, hml, ?_⟩
        have hp_tr : (p.setWidth 32).toNat = p.toNat := by
          rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
        have hnp_bd := fullArenaNextOff_bounds (ar := s.core.arena) (alen := s.core.arena_len)
          (cref := p.toNat) hp_wf.1
        let np_bv := (BitVec.ofNat 32 (fullArenaNextOff s.core.arena s.core.arena_len
          (p.setWidth 32).toNat)).setWidth 64
        have hnp_n : np_bv.toNat = fullArenaNextOff s.core.arena s.core.arena_len p.toNat := by
          dsimp only [np_bv]; rw [hp_tr, bv_zext32_toNat, bv32_ofNat_toNat (by omega)]
        have hnp_mem : np_bv.toNat = s.core.arena_len ∨
            np_bv.toNat ∈ fullArenaClauseRefs s := by
          rw [hnp_n]; exact fullArenaClauseRefs_next_or_end hw hp_ref
        fc_to_group; refine wp_join_group (ts := [i64, i64])
          (fun (g_len_n, _ticks_n, ()) mn => ∃ scr_n : List (BitVec 32),
            scr_n.length = c.scratch_cap ∧ g_len_n.toNat ≤ g_cap.toNat ∧
            GateSeqOk F_cur s.core.cur_vars scr_n g_len_n.toNat 0 ∧
            (FullMem c { s with scratch := { s.scratch with scratch_buf := scr_n } } ⋆ R) mn)
          ?_ ?_
        · rintro _ ⟨g_len_n, ticks_n, ⟨⟩⟩ mn ⟨scr_n, hscrl_n, hgl_n, hseq_n, hmn⟩
          fc_let; exact ih (np_bv, g_len_n, ticks_n, ()) mn (by dsimp only; omega)
            ⟨scr_n, hscrl_n, by omega, hnp_mem, hgl_n, hseq_n, hmn⟩
        · intro Jnp hJnp
          have hjnp0 : Jnp (g_len, ticks + 1#64, ()) ml :=
            hJnp (g_len, ticks + 1#64, ()) ml ⟨scr, hscrl_c, hgl_le, hseq_c, hml⟩
          fc_split_fast
          · have hng_red := beq_iff_eq.mp hc; clear hc; fc_split_fast
            · have hsz3_bv : 3 ≤ (s.core.arena[(p + 2).toNat]'hp2_arr).toNat := by
                simp only [BitVec.ule, decide_eq_true_eq] at hc; exact hc
              clear hc; fc_split_fast
              · have hsz8_bv : (s.core.arena[(p + 2).toNat]'hp2_arr).toNat ≤ 8 := by
                  simp only [BitVec.ule, decide_eq_true_eq] at hc; exact hc
                clear hc
                have hng : fullArenaClauseGarb s p.toNat = false := by
                  unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore
                  rw [List.getElem?_eq_getElem hp_arr, Option.getD_some]
                  exact garb_false_of_and_480000 hng_red
                let sz_bv := s.core.arena[(p + 2).toNat]'hp2_arr
                have hsz_bv_p2 : sz_bv = s.core.arena[p.toNat + 2]'(by omega) :=
                  list_getElem_congr hp2_n hp2_arr (by omega)
                have hsz_eq : sz_bv.toNat = fullArenaClauseSizeCore s.core p.toNat := by
                  unfold fullArenaClauseSizeCore
                  rw [hsz_bv_p2, List.getElem?_eq_getElem (by omega), Option.getD_some]
                have hsz3 : 3 ≤ sz_bv.toNat := hsz3_bv; have hsz8 : sz_bv.toNat ≤ 8 := hsz8_bv
                have har_bd : p.toNat + 3 + sz_bv.toNat ≤ s.core.arena.length := by omega
                fc_to_group
                refine wp_loop_break_group (brkTs := [i64, i32]) (lpTs := [i32])
                  (fun (g_len1, _, ()) mb => ∃ scr1 : List (BitVec 32),
                    scr1.length = c.scratch_cap ∧ g_len1.toNat ≤ g_cap.toNat ∧
                    GateSeqOk F_cur s.core.cur_vars scr1 g_len1.toNat 0 ∧
                    (FullMem c { s with scratch := { s.scratch with scratch_buf := scr1 } } ⋆ R)
                      mb)
                  (fun rem (i, ()) mi =>
                    mi = ml ∧ i.toNat ≤ sz_bv.toNat ∧ rem = sz_bv.toNat - i.toNat)
                  ?_ ?_ ?_
                · rintro _ ⟨g_len1, _, ⟨⟩⟩ mb ⟨scr1, hscrl1, hgl1_le, hseq1, hmb⟩
                  let sc1 : FullState :=
                    { s with scratch := { s.scratch with scratch_buf := scr1 } }
                  have hlen1 : sc1.LengthsOk c :=
                    ⟨hlen.core_ok, { hlen.scratch_ok with scratch_buf_len := hscrl1 }⟩
                  have hjnp1 : Jnp (g_len1, ticks + 1#64, ()) mb :=
                    hJnp (g_len1, ticks + 1#64, ()) mb ⟨scr1, hscrl1, hgl1_le, hseq1, hmb⟩
                  fc_to_group
                  refine wp_join_group (ts := [i64, i64]) (fun args mj => Jnp args mj)
                    (fun _ args mj h => by fc_let; exact h) ?_
                  intro J3 hJ3
                  have hj3_keep : J3 (g_len1, ticks + 1#64, ()) mb :=
                    hJ3 (g_len1, ticks + 1#64, ()) mb hjnp1
                  fc_split_fast
                  · have hsz_eq3 := beq_iff_eq.mp hc; clear hc; fc_split_fast
                    · have h14_le : g_len1.toNat + 14 ≤ g_cap.toNat := by
                        simp only [BitVec.ule, decide_eq_true_eq] at hc; bv_omega
                      have hsz3_n : fullArenaClauseSizeCore s.core p.toNat = 3 := by
                        rw [← hsz_eq]; exact congrArg BitVec.toNat hsz_eq3
                      have hp3_n : (p + 3).toNat = p.toNat + 3 :=
                        show (p.toNat + 3) % 2 ^ 64 = p.toNat + 3 from Nat.mod_eq_of_lt (by omega)
                      have hp4_n : (p + 4).toNat = p.toNat + 4 :=
                        show (p.toNat + 4) % 2 ^ 64 = p.toNat + 4 from Nat.mod_eq_of_lt (by omega)
                      have hp5_n : (p + 5).toNat = p.toNat + 5 :=
                        show (p.toNat + 5) % 2 ^ 64 = p.toNat + 5 from Nat.mod_eq_of_lt (by omega)
                      have hlits3 := arena_clause3_lits (k := s.core) (cr := p.toNat) hsz3_n
                        (by omega)
                      have hcl3 := hw.arena.entails p.toNat hp_ref hng
                      have hnd3 := hnd p.toNat hp_ref hng
                      have hlt3 := hw.arena.lits_lt p.toNat hp_ref hng
                      unfold fullArenaClauseLits at hnd3; rw [hlits3] at hcl3 hnd3 hlt3
                      simp only [List.map_cons, List.map_nil, List.nodup_cons, List.mem_cons,
                        List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true] at hnd3
                      have hl3 : s.core.arena[(p + 3).toNat]'(by omega) =
                          s.core.arena[p.toNat + 3]'(by omega) :=
                        list_getElem_congr hp3_n (by omega) (by omega)
                      have hl4 : s.core.arena[(p + 4).toNat]'(by omega) =
                          s.core.arena[p.toNat + 4]'(by omega) :=
                        list_getElem_congr hp4_n (by omega) (by omega)
                      have hl5 : s.core.arena[(p + 5).toNat]'(by omega) =
                          s.core.arena[p.toNat + 5]'(by omega) :=
                        list_getElem_congr hp5_n (by omega) (by omega)
                      fc_steps; c0_call hTryXorIte
                      refine ⟨c, F0, F_cur, sc1, R, rfl, hlen1, hw, hnd, hcl0,
                        by rw [hl3]; exact hlt3 _ (by simp),
                        by rw [hl4]; exact hlt3 _ (by simp),
                        by rw [hl5]; exact hlt3 _ (by simp),
                        by rw [hl3, hl4]; exact hnd3.1.1,
                        by rw [hl3, hl5]; exact hnd3.1.2,
                        by rw [hl4, hl5]; exact hnd3.2.1,
                        by rw [hl3, hl4, hl5]; exact hcl3,
                        by omega, hgc_le, hseq1, hmb,
                        fun ret scr2 m2 hlen2 _ hret_le _ hseq2 hm2 => ?_⟩
                      fc_let
                      exact hJ3 (ret, ticks + 1#64 + 4#64, ()) m2
                        (hJnp (ret, ticks + 1#64 + 4#64, ()) m2
                          ⟨scr2, hlen2, hret_le, hseq2, hm2⟩)
                    · fc_let; exact hj3_keep
                  · fc_let; exact hj3_keep
                · rintro B L rem ⟨i, ⟨⟩⟩ mi hB hL ⟨hmi, hi_le, rfl⟩
                  subst mi; fc_split_fast
                  · have hi_lt : i.toNat < sz_bv.toNat := by
                      simp only [BitVec.ult, decide_eq_true_eq] at hc; exact hc
                    have hp3i_n : (p + 3 + i.setWidth 64).toNat = p.toNat + 3 + i.toNat :=
                      bv64_add_zext32 (k := 3) (by omega)
                    have hp3i_arr : (p + 3 + i.setWidth 64).toNat < s.core.arena.length := by
                      omega
                    let lhs := s.core.arena[(p + 3 + i.setWidth 64).toNat]'hp3i_arr
                    have hlhs_eq : s.core.arena[(p + 3 + i.setWidth 64).toNat]'hp3i_arr =
                        s.core.arena[p.toNat + 3 + i.toNat]?.getD 0#32 := by
                      rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
                      exact list_getElem_congr hp3i_n hp3i_arr (by omega)
                    fc_to_group
                    refine wp_loop_break_group (brkTs := [.bool, i32]) (lpTs := [i32])
                      (fun (ok, _, ()) mb2 => mb2 = ml ∧
                        (ok = true → ∀ k < sz_bv.toNat, k ≠ i.toNat →
                          (cnfOfClauses F_cur).EntailsClause (cnfClause
                            [litNeg (s.core.arena[p.toNat + 3 + i.toNat]?.getD 0#32).toNat,
                             litNeg (s.core.arena[p.toNat + 3 + k]?.getD 0#32).toNat])))
                      (fun rem2 (j, ()) mj => mj = ml ∧ j.toNat ≤ sz_bv.toNat ∧
                        rem2 = sz_bv.toNat - j.toNat ∧
                        ∀ k < j.toNat, k ≠ i.toNat →
                          (cnfOfClauses F_cur).EntailsClause (cnfClause
                            [litNeg (s.core.arena[p.toNat + 3 + i.toNat]?.getD 0#32).toNat,
                             litNeg (s.core.arena[p.toNat + 3 + k]?.getD 0#32).toNat]))
                      ?_ ?_ ?_
                    · rintro _ ⟨ok, _, ⟨⟩⟩ mb2 ⟨hmb2, hok⟩
                      subst mb2; fc_split_fast
                      · have hbins := hok hc
                        clear hc hok hL hNext hHasBin hTryXorIte hQ ih hJnp hjnp0 hq_out
                        have hi32 : i32.bytes = 4 := rfl
                        have hg1 : (g_len + 1).toNat = g_len.toNat + 1 :=
                          show (g_len.toNat + 1) % 2 ^ 64 = g_len.toNat + 1 from
                            Nat.mod_eq_of_lt (by omega)
                        have hszm1 : (sz_bv - 1#32).toNat = sz_bv.toNat - 1 := by bv_omega
                        have hgl_next : (g_len + 2#64 + (sz_bv - 1#32).setWidth 64).toNat =
                            g_len.toNat + 2 + (sz_bv.toNat - 1) := by
                          rw [bv64_add_zext32 (k := 2) (by omega), hszm1]
                        have hfs := focus_full_scratch_buf hml; clear hml
                        generalize hR_scr : FullScrBufRest c sc ⋆ R = R_scr at hfs
                        have hg0_lt : g_len.toNat < scr.length := by omega
                        have hg1_lt : (g_len + 1).toNat < scr.length := by omega
                        fc_steps; let scr_h0 := scr.set g_len.toNat lhs
                        let scr_h1 := scr_h0.set (g_len.toNat + 1) (sz_bv - 1#32)
                        have hm_h1 : (array (t := i32) c.pScratchBuf scr_h1 ⋆ R_scr) m := by
                          rw [hg1] at hm; exact hm
                        have hm_h1_full : (FullMem c { s with scratch :=
                            { s.scratch with scratch_buf := scr_h1 } } ⋆ R) m := by
                          subst hR_scr; exact unfocus_full_scratch_buf hm_h1
                        let ScrWOk (n : Nat) (scrw : List (BitVec 32)) (mj : Mem 64) : Prop :=
                          scrw.length = c.scratch_cap ∧
                          (∀ idx < g_len.toNat, scrw[idx]? = scr[idx]?) ∧
                          scrw[g_len.toNat]? = some lhs ∧
                          scrw[g_len.toNat + 1]? = some (sz_bv - 1#32) ∧
                          (∀ k < n, k ≠ i.toNat →
                            scrw[g_len.toNat + 2 + (if k < i.toNat then k else k - 1)]? =
                              some ((s.core.arena[p.toNat + 3 + k]?.getD 0#32) ^^^ 1#32)) ∧
                          (FullMem c { s with scratch :=
                            { s.scratch with scratch_buf := scrw } } ⋆ R) mj
                        clear hm hm_h1; refine wp_loop_inv
                          (fun (j2, rk, ()) mj2 => ∃ scrw : List (BitVec 32),
                            j2.toNat ≤ sz_bv.toNat ∧
                            rk.toNat = (if j2.toNat ≤ i.toNat then j2.toNat else j2.toNat - 1) ∧
                            ScrWOk j2.toNat scrw mj2)
                          (fun (j2, _, ()) _ => sz_bv.toNat - j2.toNat)
                          (fun Jw hJw => by
                            fc_let; refine hJw (0#32, 0#32, ()) m
                              ⟨scr_h1, Nat.zero_le _, by simp,
                               by simp [scr_h1, scr_h0, hscrl_c],
                               fun idx hi => by
                                 simp only [scr_h1, scr_h0]
                                 repeat rw [List.getElem?_set_ne (by omega)],
                               by simp only [scr_h1, scr_h0]
                                  rw [List.getElem?_set_ne (by omega),
                                    List.getElem?_set_self (by omega)],
                               by simp only [scr_h1, scr_h0]
                                  rw [List.getElem?_set_self (by simp [hscrl_c]; omega)],
                               fun _ hk => by simp at hk, hm_h1_full⟩)
                          (fun Jw (j2, rk, ()) mj2
                            ⟨scrw, hj2_le, hrk_eq, hscrlw, hprefw, hw0, hw1, hwrhs, hmj2⟩ ihw =>
                            ?_)
                        fc_split_fast
                        · have hj2_lt : j2.toNat < sz_bv.toNat := by
                            simp only [BitVec.ult, decide_eq_true_eq] at hc; exact hc
                          have hj21 : (j2 + 1#32).toNat = j2.toNat + 1 :=
                            show (j2.toNat + 1) % 2 ^ 32 = j2.toNat + 1 from
                              Nat.mod_eq_of_lt (by omega)
                          fc_to_group; refine wp_join_group (ts := [i32])
                            (fun (rk', ()) mj2' => ∃ scrw' : List (BitVec 32),
                              rk'.toNat = (if j2.toNat + 1 ≤ i.toNat then j2.toNat + 1
                                else j2.toNat) ∧ ScrWOk (j2.toNat + 1) scrw' mj2')
                            (fun _ ⟨rk', ⟨⟩⟩ mj2' ⟨scrw', h2, h1, h3, h4, h5, h6, h7⟩ => by
                              fc_let; exact ihw (j2 + 1#32, rk', ()) mj2' (by dsimp only; omega)
                                ⟨scrw', by omega, by rw [hj21]; exact h2, h1, h3, h4, h5,
                                 by rw [hj21]; exact h6, h7⟩) ?_
                          intro Jif hJif; fc_split_fast
                          · have hj2i : j2.toNat ≠ i.toNat := fun h =>
                              (bne_iff_ne.mp hc) (BitVec.eq_of_toNat_eq h)
                            have hrk_pos_eq : rk.toNat =
                                (if j2.toNat < i.toNat then j2.toNat else j2.toNat - 1) := by
                              rw [hrk_eq]; split <;> split <;> omega
                            have hrk_lt8 : rk.toNat < sz_bv.toNat - 1 := by
                              rw [hrk_pos_eq]; split <;> omega
                            have hp3j_n : (p + 3 + j2.setWidth 64).toNat =
                                p.toNat + 3 + j2.toNat :=
                              bv64_add_zext32 (k := 3) (by omega)
                            have hp3j_arr : (p + 3 + j2.setWidth 64).toNat <
                                s.core.arena.length := by omega
                            have hdst_n : (g_len + 2 + rk.setWidth 64).toNat =
                                g_len.toNat + 2 + rk.toNat := bv64_add_zext32 (k := 2) (by omega)
                            have hdst_lt : (g_len + 2 + rk.setWidth 64).toNat < scrw.length := by
                              omega
                            have hrk1 : (rk + 1#32).toNat = rk.toNat + 1 :=
                              show (rk.toNat + 1) % 2 ^ 32 = rk.toNat + 1 from
                                Nat.mod_eq_of_lt (by omega)
                            fc_let; fc_step; have hfs_w := focus_full_scratch_buf hmj2; clear hmj2
                            generalize hR_w : FullScrBufRest c { s with scratch :=
                              { s.scratch with scratch_buf := scrw } } ⋆ R = R_w at hfs_w
                            fc_steps; subst hR_w
                            let val_j :=
                              (s.core.arena[(p + 3 + j2.setWidth 64).toNat]'hp3j_arr) ^^^ 1#32
                            have hval_j : val_j =
                                (s.core.arena[p.toNat + 3 + j2.toNat]?.getD 0#32) ^^^ 1#32 := by
                              dsimp only [val_j]; congr 1
                              rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
                              exact list_getElem_congr hp3j_n hp3j_arr (by omega)
                            let scrw' := scrw.set (g_len.toNat + 2 + rk.toNat) val_j
                            have hm_w' : (FullMem c { s with scratch :=
                                { s.scratch with scratch_buf := scrw' } } ⋆ R) m := by
                              rw [hdst_n] at hm; exact unfocus_full_scratch_buf hm
                            refine hJif (rk + 1#32, ()) m
                              ⟨scrw', by rw [hrk1, hrk_eq]; split <;> split <;> omega,
                               by rw [List.length_set]; exact hscrlw,
                               fun idx hi => by
                                 rw [List.getElem?_set_ne (by omega)]; exact hprefw idx hi,
                               by rw [List.getElem?_set_ne (by omega)]; exact hw0,
                               by rw [List.getElem?_set_ne (by omega)]; exact hw1,
                               fun k hk hkne => ?_, hm_w'⟩
                            by_cases hkj : k = j2.toNat
                            · subst hkj; rw [← hrk_pos_eq]
                              simp only [scrw']; rw [List.getElem?_set_self (by omega), hval_j]
                            · have hne_slot : (if k < i.toNat then k else k - 1) ≠ rk.toNat := by
                                rw [hrk_pos_eq]; split <;> split <;> omega
                              simp only [scrw']; rw [List.getElem?_set_ne (by omega)]
                              exact hwrhs k (by omega) hkne
                          · have hj2i : j2.toNat = i.toNat :=
                              congrArg BitVec.toNat (by simpa using hc : j2 = i)
                            fc_let; exact hJif (rk, ()) mj2
                              ⟨scrw, by rw [hrk_eq]; split <;> split <;> omega,
                               hscrlw, hprefw, hw0, hw1, fun k hk hkne => hwrhs k (by omega) hkne,
                               hmj2⟩
                        · have hj2_e : j2.toNat = sz_bv.toNat := by
                            simp only [BitVec.ult, decide_eq_false_iff_not] at hc
                            change ¬j2.toNat < sz_bv.toNat at hc; omega
                          rw [hj2_e] at hwrhs
                          have hsz_bv_eq : sz_bv - 1#32 = BitVec.ofNat 32 (sz_bv.toNat - 1) := by
                            apply BitVec.eq_of_toNat_eq; rw [hszm1, bv32_ofNat_toNat (by omega)]
                          have hgat := FullCongHelpers.andGate_of_emitted hlen hw hnd hp_ref hng
                            hsz_eq.symm hsz3 hsz8 hi_lt hbins hscrlw (by omega) (hlhs_eq ▸ hw0)
                            (hsz_bv_eq ▸ hw1) hwrhs
                          have hseq_new : GateSeqOk F_cur s.core.cur_vars scrw
                              (g_len + 2#64 + (sz_bv - 1#32).setWidth 64).toNat 0 := by
                            rw [hgl_next]; refine gateSeqOk_append (by omega) hprefw ?_ hseq_c
                            refine .step hgat ?_
                            have hmword_ar : ((sz_bv - 1#32) &&& 0xFF#32).toNat =
                                sz_bv.toNat - 1 := by
                              rw [BitVec.toNat_and, hszm1,
                                show (0xFF#32 : BitVec 32).toNat = 255 from rfl]
                              simpa [Nat.mod_eq_of_lt (show sz_bv.toNat - 1 < 256 by omega)] using
                                Nat.and_two_pow_sub_one_eq_mod (sz_bv.toNat - 1) 8
                            simpa [hw1, hmword_ar] using GateSeqOk.done
                          fc_let; exact hB (g_len + 2#64 + (sz_bv - 1#32).setWidth 64, i, ()) mj2
                            ⟨scrw, hscrlw, by omega, hseq_new, hmj2⟩
                      · have hi1 : (i + 1#32).toNat = i.toNat + 1 :=
                          show (i.toNat + 1) % 2 ^ 32 = i.toNat + 1 from
                            Nat.mod_eq_of_lt (by omega)
                        fc_let; exact hL (sz_bv.toNat - (i + 1#32).toNat) (i + 1#32, ()) ml
                          (by omega) ⟨rfl, by omega, rfl⟩
                    · rintro B2 L2 rem2 ⟨j, ⟨⟩⟩ mj hB2 hL2 ⟨hmj, hj_le, rfl, hseen⟩
                      subst mj; fc_split_fast
                      · have hj_lt : j.toNat < sz_bv.toNat := by
                          simp only [BitVec.ult, decide_eq_true_eq] at hc; exact hc
                        have hj1 : (j + 1#32).toNat = j.toNat + 1 :=
                          show (j.toNat + 1) % 2 ^ 32 = j.toNat + 1 from
                            Nat.mod_eq_of_lt (by omega)
                        fc_to_group; refine wp_join_group (ts := [])
                          (fun () m_j => m_j = ml ∧
                            ∀ k < (j + 1#32).toNat, k ≠ i.toNat →
                              (cnfOfClauses F_cur).EntailsClause (cnfClause
                                [litNeg (s.core.arena[p.toNat + 3 + i.toNat]?.getD 0#32).toNat,
                                 litNeg (s.core.arena[p.toNat + 3 + k]?.getD 0#32).toNat]))
                          ?_ ?_
                        · rintro _ ⟨⟩ m_j ⟨hmj', hseen'⟩; subst m_j; fc_let
                          exact hL2 (sz_bv.toNat - (j + 1#32).toNat) (j + 1#32, ()) ml (by omega)
                            ⟨rfl, by omega, rfl, hseen'⟩
                        · intro Jj hJj
                          fc_let; refine ⟨fun hne => ?_, fun heq => ?_⟩
                          · have hji : j.toNat ≠ i.toNat := fun h =>
                              (bne_iff_ne.mp hne) (BitVec.eq_of_toNat_eq h)
                            have hp3j_n : (p + 3 + j.setWidth 64).toNat =
                                p.toNat + 3 + j.toNat :=
                              bv64_add_zext32 (k := 3) (by omega)
                            have hp3j_arr : (p + 3 + j.setWidth 64).toNat <
                                s.core.arena.length := by omega
                            fc_steps; c0_call hHasBin
                            refine ⟨c, F0, F_cur, sc, R, rfl, hlen_c, hw, hml, fun hb hhb => ?_⟩
                            fc_let; refine ⟨fun hbt => ?_, fun _ => ?_⟩
                            · have hnew : (cnfOfClauses F_cur).EntailsClause (cnfClause
                                  [litNeg (s.core.arena[p.toNat + 3 + i.toNat]?.getD 0#32).toNat,
                                   litNeg (s.core.arena[p.toNat + 3 + j.toNat]?.getD 0#32).toNat])
                                  := by
                                have h := (hhb hbt).2.2.2.2
                                have hget_j :
                                    s.core.arena[(p + 3 + j.setWidth 64).toNat]'hp3j_arr =
                                    s.core.arena[p.toNat + 3 + j.toNat]?.getD 0#32 := by
                                  rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
                                  exact list_getElem_congr hp3j_n hp3j_arr (by omega)
                                simpa only [bv32_xor1_litNeg, hlhs_eq, hget_j] using h
                              fc_let
                              exact hJj () ml ⟨rfl, fun k hk hkne => by
                                rw [hj1] at hk
                                by_cases hkj : k = j.toNat
                                · subst hkj; exact hnew
                                · exact hseen k (by omega) hkne⟩
                            · fc_let; exact hB2 (false, j, ()) ml ⟨rfl, fun h => by cases h⟩
                          · have hji : j.toNat = i.toNat := by
                              have : j = i := by simpa using heq
                              exact congrArg BitVec.toNat this
                            fc_let; exact hJj () ml ⟨rfl, fun k hk hkne => hseen k (by omega) hkne⟩
                      · have hj_e : j.toNat = sz_bv.toNat := by
                          simp only [BitVec.ult, decide_eq_false_iff_not] at hc
                          change ¬j.toNat < sz_bv.toNat at hc; omega
                        rw [hj_e] at hseen; fc_let; exact hB2 (true, j, ()) ml ⟨rfl, fun _ => hseen⟩
                    · intro _ L2 _ hL2; fc_let
                      exact hL2 (sz_bv.toNat - 0) (0#32, ()) ml
                        ⟨rfl, Nat.zero_le _, rfl, fun _ h => by simp at h⟩
                  · fc_let; exact hB (g_len, i, ()) ml ⟨scr, hscrl_c, hgl_le, hseq_c, hml⟩
                · intro _ L _ hL; fc_let
                  exact hL (sz_bv.toNat - 0) (0#32, ()) ml ⟨rfl, Nat.zero_le _, rfl⟩
              · fc_let; exact hjnp0
            · fc_let; exact hjnp0
          · fc_let; exact hjnp0
      · fc_let; exact hq_out
    · fc_let; exact hq_out
  · fc_let; exact hq_out

/-! ## 5. `full_congruence_dense_wp` (`FullDefSweep` #5) -/

/-- **`full_congruence_dense`**: runs ticks-bounded gate extraction and `6`-pass union-find
congruence hashing directly inside dense mode (`FullDenseInv → FullDenseInv` or
`20#64 → F0.Unsat`). -/
theorem full_congruence_dense_wp (Γ : Env)
    (hExtract : ∀ args m Q X, fullCongExtractTickSpec args m Q X →
      Γ "full_cong_extract" [i64, i64, i64] [i64] args m Q X)
    (hHashStep : ∀ args m Q X, FullCongSpecs.fullCongHashStepSpec args m Q X →
      Γ "full_cong_hash_step" [i64, i64, i64, i64] [.bool] args m Q X) :
    ∀ args m Q X, fullCongruenceDenseSpec args m Q X →
      Func.wp Γ full_congruence_dense_body args m Q X := by
  rintro ⟨h, tick_lim, ⟨⟩⟩ m0 Q X ⟨c, F0, s, R, rfl, hd0, hm0, hQ⟩
  have hsc := c.hscr; have hmx := c.hmaxv; unfold dimacsBound at hsc hmx
  fc_split
  · fc_steps
    exact hQ 1#64 s m0 hd0 rfl (Or.inl rfl) (fun h => absurd h (by decide)) hm0
  · have h_ge256 := hc; clear hc
    fc_split
    · fc_steps
      exact hQ 1#64 s m0 hd0 rfl (Or.inl rfl) (fun h => absurd h (by decide)) hm0
    · have h256 : 256 ≤ c.scratch_cap := by bv_omega
      obtain ⟨hcore0, hmk0, hnd0, hext0, hcl0, hdm0⟩ := hd0
      obtain ⟨F_cur, hw0⟩ := hcore0.witness
      have hlen0 := hcore0.lengths; have hcv_le := hlen0.core_ok.cur_vars_le
      have hrl0 := hlen0.core_ok.repr_len
      fc_steps
      refine wp_loop_inv
        (fun (ht_sz, ()) mht => mht = m0 ∧
          64 ≤ ht_sz.toNat ∧ ht_sz.toNat ≤ 8192 ∧ ht_sz.toNat ≤ c.scratch_cap)
        (fun (ht_sz, ()) _ => 8192 - ht_sz.toNat)
        (fun Jht hJht => by
          fc_steps
          exact hJht (64#64, ()) m0
            ⟨rfl, by decide, by decide, show 64 ≤ c.scratch_cap by omega⟩)
        (fun Jht (ht_sz, ()) mht ⟨hmht, hht64, hht_le8, hht_sc⟩ ih_ht => ?_)
      subst mht; fc_to_group; refine wp_join_group (ts := []) (fun () me => me = m0) ?_ ?_
      · rintro _ ⟨⟩ me hme; subst me
        have hht_off : (BitVec.ofNat 64 c.scratch_cap - ht_sz).toNat =
            c.scratch_cap - ht_sz.toNat := by bv_omega
        fc_steps; c0_call hExtract
        refine ⟨c, F0, F_cur, s, R, rfl, hlen0, hw0, hnd0, hcl0, by omega, hm0,
          fun g_len scr1 m1 hscrl1 hgl_le hseq1 hm1 => ?_⟩
        let s1 : FullState := { s with scratch := { s.scratch with scratch_buf := scr1 } }
        have hlen1 : s1.LengthsOk c :=
          ⟨hlen0.core_ok, { hlen0.scratch_ok with scratch_buf_len := hscrl1 }⟩
        have hd1 : FullDenseInv c F0 s1 := ⟨⟨hlen1, F_cur, hw0⟩, hmk0, hnd0, hext0, hcl0, hdm0⟩
        fc_split
        · fc_steps
          exact hQ 1#64 s1 m1 hd1 rfl (Or.inl rfl) (fun h => absurd h (by decide)) hm1
        · have hnlits : (BitVec.ofNat 64 s.core.cur_vars <<< (1 : Nat)).toNat =
              2 * s.core.cur_vars := by
            rw [bv64_shl1_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
          fc_steps; refine wp_loop_inv
            (fun (i, ()) mi => ∃ repri : List (BitVec 32),
              repri.length = 2 * c.max_vars ∧ i.toNat ≤ 2 * s.core.cur_vars ∧
              (∀ k < i.toNat, repri[k]? = some (BitVec.ofNat 32 k)) ∧
              (FullMem c { s1 with core := { s1.core with repr := repri } } ⋆ R) mi)
            (fun (i, ()) _ => 2 * s.core.cur_vars - i.toNat)
            (fun Ji hJi => by
              fc_steps
              exact hJi (0#64, ()) m1 ⟨s.core.repr, hrl0, Nat.zero_le _,
                fun _ h => by simp at h, hm1⟩)
            (fun Ji (i, ()) mi ⟨repri, hrli, hi_le, hinit, hmi⟩ ihi => ?_)
          fc_split
          · have hi_lt : i.toNat < 2 * s.core.cur_vars := by bv_omega
            have hi1_n : (i + 1#64).toNat = i.toNat + 1 :=
              show (i.toNat + 1) % 2 ^ 64 = i.toNat + 1 from Nat.mod_eq_of_lt (by omega)
            have hi_tr : i.setWidth 32 = BitVec.ofNat 32 i.toNat := by
              apply BitVec.eq_of_toNat_eq
              rw [BitVec.toNat_setWidth, bv32_ofNat_toNat (by omega), Nat.mod_eq_of_lt (by omega)]
            fc_steps; let repri' := repri.set i.toNat (i.setWidth 32)
            exact ihi (i + 1#64, ()) m (by dsimp only; omega)
              ⟨repri', by simp [repri', hrli], by omega, fun k hk => by
                rw [hi1_n] at hk
                by_cases hki : k = i.toNat
                · subst hki; rw [List.getElem?_set_self (by omega), hi_tr]
                · rw [List.getElem?_set_ne (Ne.symm hki)]; exact hinit k (by omega),
               hm⟩
          · have hi_eq : i.toNat = 2 * s.core.cur_vars := by bv_omega
            rw [hi_eq] at hinit
            have hrepr2 : CongReprInv F_cur (2 * s.core.cur_vars) repri := by
              refine ⟨⟨by omega, fun l hl => ?_⟩, fun l hl => ?_⟩
              · rw [hinit l hl, Option.getD_some, bv32_ofNat_toNat (by omega)]; exact Nat.le_refl _
              · rw [hinit l hl, Option.getD_some, bv32_ofNat_toNat (by omega)]
                exact LitEquiv.refl _ _
            let s2 : FullState := { s1 with core := { s1.core with repr := repri } }
            have hlen2 : s2.LengthsOk c :=
              ⟨{ hlen1.core_ok with repr_len := hrli }, hlen1.scratch_ok⟩
            have hw2 : FullWitnessInv c F0 F_cur s2.core := fullWitnessInv_with_repr hw0 repri
            fc_to_group; refine wp_loop_break_group (brkTs := [i64]) (lpTs := [i64])
              (fun (_, ()) mb => ∃ sf : FullState, FullDenseInv c F0 sf ∧
                sf.core.fuel = s.core.fuel ∧ (FullMem c sf ⋆ R) mb)
              (fun remp (pass, ()) mp => ∃ sp : FullState,
                pass.toNat ≤ 6 ∧ remp = 6 - pass.toNat ∧
                sp.LengthsOk c ∧ FullWitnessInv c F0 F_cur sp.core ∧
                FullLitMarksClear c sp ∧ FullArenaVarsNodup sp ∧ FullExtScratchOk c sp ∧
                sp.core.cur_level = 0 ∧ sp.core.dense_mode ≠ 0#64 ∧
                sp.core.cur_vars = s.core.cur_vars ∧
                sp.core.fuel = s.core.fuel ∧
                CongReprInv F_cur (2 * sp.core.cur_vars) sp.core.repr ∧
                GateSeqOk F_cur sp.core.cur_vars sp.scratch.scratch_buf g_len.toNat 0 ∧
                (FullMem c sp ⋆ R) mp)
              ?_ ?_ ?_
            · rintro _ ⟨_, ⟨⟩⟩ mb ⟨sf, hdf, hflf, hmb⟩
              fc_to_group; refine wp_join_group (ts := [i64])
                (fun (r, ()) mf => mf = mb ∧ (r = 1#64 ∨ r = 20#64) ∧ (r = 20#64 → F0.Unsat))
                (fun _ ⟨r, ⟨⟩⟩ mf ⟨hmf, hdom, hu⟩ => by
                  subst hmf; fc_steps; exact hQ r sf mf hdf hflf hdom hu hmb)
                ?_
              intro Jret hJret; fc_split
              · have hinc : sf.core.inconsistent ≠ 0#64 := by grind
                fc_steps
                exact hJret (20#64, ()) mb ⟨rfl, Or.inr rfl, fun _ => hdf.inconsistent_unsat hinc⟩
              · fc_steps
                exact hJret (1#64, ()) mb ⟨rfl, Or.inl rfl, fun h => absurd h (by decide)⟩
            · rintro Bp Lp remp ⟨pass, ⟨⟩⟩ mp hBp hLp
                ⟨sp, hpass_le, rfl, hlen_p, hw_p, hmk_p, hnd_p, hext_p, hcl_p, hdm_p,
                 hcv_p, hfl_p, hrepr_p, hseq_p, hmp⟩
              fc_split
              · have hpass_lt : pass.toNat < 6 := by bv_omega
                fc_split
                · have hpass1 : (pass + 1#64).toNat = pass.toNat + 1 :=
                    show (pass.toNat + 1) % 2 ^ 64 = pass.toNat + 1 from
                      Nat.mod_eq_of_lt (by omega)
                  fc_steps; c0_call hHashStep
                  refine ⟨c, F0, F_cur, sp, R, rfl, hlen_p, hw_p, hmk_p, hnd_p, hext_p, hcl_p,
                    hdm_p, hrepr_p, by omega, by omega, by omega, hseq_p, hmp,
                    fun ch sp' mp' hlen_p' hw_p' hmk_p' hnd_p' hext_p' hcl_p' hdm_p' hcv_p' hfl_p'
                      _ _ hrepr_p' hpref_p' hmp' => ?_⟩
                  fc_split
                  · fc_steps
                    exact hLp (6 - (pass + 1#64).toNat) (pass + 1#64, ()) mp' (by omega)
                      ⟨sp', by omega, rfl, hlen_p', hw_p', hmk_p', hnd_p', hext_p', hcl_p', hdm_p',
                       hcv_p'.trans hcv_p, hfl_p'.trans hfl_p, hrepr_p',
                       hcv_p' ▸ gateSeqOk_congr hpref_p' hseq_p, hmp'⟩
                  · fc_steps
                    exact hBp (pass, ()) mp' ⟨sp', ⟨⟨hlen_p', ⟨F_cur, hw_p'⟩⟩, hmk_p', hnd_p',
                      hext_p', hcl_p', hdm_p'⟩, hfl_p'.trans hfl_p, hmp'⟩
                · fc_steps
                  exact hBp (pass, ()) mp ⟨sp, ⟨⟨hlen_p, ⟨F_cur, hw_p⟩⟩, hmk_p, hnd_p, hext_p,
                    hcl_p, hdm_p⟩, hfl_p, hmp⟩
              · fc_steps
                exact hBp (pass, ()) mp ⟨sp, ⟨⟨hlen_p, ⟨F_cur, hw_p⟩⟩, hmk_p, hnd_p, hext_p,
                  hcl_p, hdm_p⟩, hfl_p, hmp⟩
            · intro _ Lp _ hLp; fc_steps
              exact hLp 6 (0#64, ()) mi ⟨s2, Nat.zero_le _, rfl, hlen2, hw2, hmk0, hnd0, hext0,
                hcl0, hdm0, rfl, rfl, hrepr2, hseq1, hmi⟩
      · intro Jht_exit hJht_exit
        fc_split
        · have h4_n : ht_sz.toNat * 4 < c.scratch_cap := by bv_omega
          fc_split
          · have h4096_n : ht_sz.toNat < 4096 := by bv_omega
            have hshl1 : (ht_sz <<< (1 : Nat)).toNat = 2 * ht_sz.toNat := by
              rw [bv64_shl1_toNat]; omega
            fc_steps; exact ih_ht (ht_sz <<< (1 : Nat), ()) m0 (by dsimp only; omega)
              ⟨rfl, by omega, by omega, by omega⟩
          · fc_steps; exact hJht_exit () m0 rfl
        · fc_steps; exact hJht_exit () m0 rfl

end LeanQbe.T.Examples.Kissat.FullDefSweep
