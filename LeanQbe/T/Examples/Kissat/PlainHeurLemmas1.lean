module

public import LeanQbe.T.Examples.Kissat.PlainSpec
import LeanQbe.T.Logic.C0Step

/-!
# Kissat `D-Plain` Arithmetic, Arena, and Watch-Stack Proofs — Part 1 (`Wave 2b`)

Proves parametric `(Γ : Env)` `Func.wp` contracts for the first 5 `Plain1` helpers matching
`plainSpecTable` rows (`PlainSpec.lean:832-836`):
1. `plain_isqrt` (`plainIsqrtSpec`, `plain_isqrt_wp`)
2. `plain_ilog10` (`plainIlog10Spec`, `plain_ilog10_wp`)
3. `plain_arena_next` (`plainArenaNextSpec`, `plain_arena_next_wp`)
4. `plain_alloc_cl` (`plainAllocClSpec`, `plain_alloc_cl_wp`)
5. `plain_wstack_defrag` (`plainWstackDefragSpec`, `plain_wstack_defrag_wp`)
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Plain

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.C0Step
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open Kraken.Bedrock2.Test

/-! ## 0. Scoped tactics and helper lemmas (`PlainHeurTactics`) -/

namespace PlainHeurTactics

attribute [scoped bv_c0] List.length_set

@[scoped c0_load] theorem load_arena_heap0 {c : PlainCfg} {s : PlainState} {R : Mem 64 → Prop}
    {m : Mem 64} (hi : 0 < s.heur.heap.length) (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i32 c.pHeap = some s.heur.heap[0] := by simpa using load_arena_heap (i := 0) hi hm

@[scoped c0_load] theorem load_arena_heap_zero {c : PlainCfg} {s : PlainState} {R : Mem 64 → Prop}
    {m : Mem 64} (hi : 0 < s.heur.heap.length) (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i32 (c.pHeap + 0#64) = some s.heur.heap[0] := load_arena_heap (i := 0) hi hm

@[scoped c0_store] theorem store_arena_heap0 {c : PlainCfg} {s : PlainState} {R : Mem 64 → Prop}
    {m : Mem 64} (v : BitVec 32) (hi : 0 < s.heur.heap.length) (hm : (PlainMem c s ⋆ R) m) :
    storeOk m i32 c.pHeap ∧
      (PlainMem c { s with heur := { s.heur with heap := s.heur.heap.set 0 v } } ⋆ R)
        (storeMem m i32 c.pHeap v) := by simpa using store_arena_heap (i := 0) v hi hm

@[scoped c0_store] theorem store_arena_heap_zero {c : PlainCfg} {s : PlainState} {R : Mem 64 → Prop}
    {m : Mem 64} (v : BitVec 32) (hi : 0 < s.heur.heap.length) (hm : (PlainMem c s ⋆ R) m) :
    storeOk m i32 (c.pHeap + 0#64) ∧
      (PlainMem c { s with heur := { s.heur with heap := s.heur.heap.set 0 v } } ⋆ R)
        (storeMem m i32 (c.pHeap + 0#64) v) := store_arena_heap (i := 0) v hi hm

@[scoped c0_load] theorem load_arena_wstk0 {c : PlainCfg} {s : PlainState} {R : Mem 64 → Prop}
    {m : Mem 64} (hi : 0 < s.wstk.length) (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i32 c.pWstk = some s.wstk[0] := by simpa using load_arena_wstk (i := 0) hi hm

@[scoped c0_load] theorem load_arena_wstk_zero {c : PlainCfg} {s : PlainState} {R : Mem 64 → Prop}
    {m : Mem 64} (hi : 0 < s.wstk.length) (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i32 (c.pWstk + 0#64) = some s.wstk[0] := load_arena_wstk (i := 0) hi hm

@[scoped c0_store] theorem store_arena_wstk0 {c : PlainCfg} {s : PlainState} {R : Mem 64 → Prop}
    {m : Mem 64} (v : BitVec 32) (hi : 0 < s.wstk.length) (hm : (PlainMem c s ⋆ R) m) :
    storeOk m i32 c.pWstk ∧
      (PlainMem c { s with wstk := s.wstk.set 0 v } ⋆ R) (storeMem m i32 c.pWstk v) := by
  simpa using store_arena_wstk (i := 0) v hi hm

@[scoped c0_store] theorem store_arena_wstk_zero {c : PlainCfg} {s : PlainState} {R : Mem 64 → Prop}
    {m : Mem 64} (v : BitVec 32) (hi : 0 < s.wstk.length) (hm : (PlainMem c s ⋆ R) m) :
    storeOk m i32 (c.pWstk + 0#64) ∧
      (PlainMem c { s with wstk := s.wstk.set 0 v } ⋆ R) (storeMem m i32 (c.pWstk + 0#64) v) :=
  store_arena_wstk (i := 0) v hi hm

@[scoped c0_load] theorem load_arena_wsort0 {c : PlainCfg} {s : PlainState} {R : Mem 64 → Prop}
    {m : Mem 64} (hi : 0 < s.heur.wsort.length) (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i32 c.pWsort = some s.heur.wsort[0] := by simpa using load_arena_wsort (i := 0) hi hm

@[scoped c0_load] theorem load_arena_wsort_zero {c : PlainCfg} {s : PlainState} {R : Mem 64 → Prop}
    {m : Mem 64} (hi : 0 < s.heur.wsort.length) (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i32 (c.pWsort + 0#64) = some s.heur.wsort[0] := load_arena_wsort (i := 0) hi hm

@[scoped c0_store] theorem store_arena_wsort0 {c : PlainCfg} {s : PlainState} {R : Mem 64 → Prop}
    {m : Mem 64} (v : BitVec 32) (hi : 0 < s.heur.wsort.length) (hm : (PlainMem c s ⋆ R) m) :
    storeOk m i32 c.pWsort ∧
      (PlainMem c { s with heur := { s.heur with wsort := s.heur.wsort.set 0 v } } ⋆ R)
        (storeMem m i32 c.pWsort v) := by simpa using store_arena_wsort (i := 0) v hi hm

@[scoped c0_store] theorem store_arena_wsort_zero {c : PlainCfg} {s : PlainState}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32) (hi : 0 < s.heur.wsort.length)
    (hm : (PlainMem c s ⋆ R) m) :
    storeOk m i32 (c.pWsort + 0#64) ∧
      (PlainMem c { s with heur := { s.heur with wsort := s.heur.wsort.set 0 v } } ⋆ R)
        (storeMem m i32 (c.pWsort + 0#64) v) := store_arena_wsort (i := 0) v hi hm

open Lean Elab Tactic in
/-- Step all goals like `c0_steps`, stopping at `Expr.group` instead of inlining join points. -/
scoped elab "c0_to_group" : tactic => do
  let rec go (fuel : Nat) : TacticM Unit := do
    if fuel = 0 then return
    let mut out : Array MVarId := #[]
    for g in ← getUnsolvedGoals do
      if ← g.isAssigned then continue
      setGoals [g]
      let ty ← Lean.instantiateMVars (← g.getType)
      if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 &&
          ((ty.getArg! 4).headBeta).isAppOf ``LeanQbe.T.Expr.group then
        out := out.push g
      else if ← LeanQbe.T.C0Step.stepOnce then
        go (fuel - 1); out := out ++ (← getUnsolvedGoals)
      else out := out.push g
    setGoals out.toList
  go 500

open Lean Elab Tactic in
/-- Step straight-line ops on the main goal until the next `Expr.jnz`, then split it once. -/
scoped elab "c0_split" : tactic => do
  let rec go (fuel : Nat) : TacticM Unit := do
    if fuel = 0 then return
    let ty ← Lean.instantiateMVars (← (← getMainGoal).getType)
    if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 &&
        ((ty.getArg! 4).headBeta).isAppOf ``LeanQbe.T.Expr.jnz then
      let _ ← LeanQbe.T.C0Step.stepOnce; return
    if ← LeanQbe.T.C0Step.stepOnce then go (fuel - 1)
  go 100

end PlainHeurTactics

open scoped PlainHeurTactics

/-! ## 1. `plain_isqrt` and `plain_ilog10` -/

private theorem pow4_lt_2_64 {k : Nat} (hk : k ≤ 31) : 4 ^ k < 2 ^ 64 :=
  Nat.lt_of_le_of_lt (Nat.pow_le_pow_right (by omega) hk) (by decide)

private theorem pow4_shr2 {k : Nat} (hk : 1 ≤ k) (h4k : 4 ^ k < 2 ^ 64) :
    BitVec.ofNat 64 (4 ^ k) >>> (2 : Nat) = BitVec.ofNat 64 (4 ^ (k - 1)) := by
  rw [bv_shr_ofNat h4k (by omega)]; congr 1
  rw [Nat.shiftRight_eq_div_pow, show 2 ^ 2 = 4 by decide]
  conv => lhs; rw [show k = (k - 1) + 1 by omega, Nat.pow_succ]
  exact Nat.mul_div_cancel _ (by omega)

private theorem isqrt_step_bound {q e x0 : Nat} (he : 1 ≤ e) (he32 : e ≤ 32)
    (hle : q * q * 4 ^ e ≤ x0) (hx : x0 < 2 ^ 64) : q * 4 ^ e + 4 ^ (e - 1) < 2 ^ 64 := by
  have h4 : 4 ^ e = 4 * 4 ^ (e - 1) := by
    conv => lhs; rw [show e = (e - 1) + 1 by omega, Nat.pow_succ]; rw [Nat.mul_comm]
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · have := pow4_lt_2_64 (k := e - 1) (by omega); omega
  · rcases Nat.eq_or_lt_of_le hq with rfl | hq2
    · have hlt : 4 ^ e < 2 ^ 64 := by simp only [Nat.one_mul] at hle; omega
      have he31 : e ≤ 31 := Classical.byContradiction fun h =>
        absurd (show 4 ^ 32 < 2 ^ 64 by rw [show 32 = e by omega]; exact hlt) (by decide)
      have h1 : 4 ^ (e - 1) ≤ 4 ^ 30 := Nat.pow_le_pow_right (by omega) (by omega)
      have h2 : 5 * 4 ^ 30 < 2 ^ 64 := by decide
      simp only [Nat.one_mul]; omega
    · have hq4 : 2 * (q * 4 ^ e) ≤ q * q * 4 ^ e := by
        simpa [Nat.mul_assoc] using Nat.mul_le_mul_right (4 ^ e) (Nat.mul_le_mul_right q hq2)
      have h4_le : 4 * 4 ^ (e - 1) ≤ q * q * 4 ^ e := by
        have h1 := Nat.mul_le_mul_right (4 ^ e) (Nat.mul_pos hq hq)
        simp only [Nat.one_mul] at h1; omega
      omega

private theorem isqrt_sq_odd (q a : Nat) :
    (2 * q + 1) * (2 * q + 1) * a = q * q * (4 * a) + (q * (4 * a) + a) := by grind

private theorem isqrt_sq_even (q a : Nat) : (2 * q) * (2 * q) * a = q * q * (4 * a) := by grind

private theorem isqrt_sq_succ_odd (q a : Nat) :
    (2 * q + 1 + 1) * (2 * q + 1 + 1) * a = (q + 1) * (q + 1) * (4 * a) := by grind

theorem plain_isqrt_wp (Γ : Env) :
    ∀ a m Q X, plainIsqrtSpec a m Q X → Func.wp Γ plain_isqrt_body a m Q X := by
  rintro ⟨x, ⟨⟩⟩ m Q X hQ
  c0_steps
  · have hx1 : x.toNat ≤ 1 := by c0_bound
    exact hQ x (by rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hx1 with h | h <;> simp [h])
      (fun _ => rfl) (fun h => by omega)
  obtain hx2 : 2 ≤ x.toNat := by c0_bound
  obtain hxlt : x.toNat < 2 ^ 64 := x.isLt
  refine wp_loop_inv
    (fun (bit, ()) m1 => m1 = m ∧ ∃ k ≤ 31, bit = BitVec.ofNat 64 (4 ^ k) ∧ x.toNat < 4 ^ (k + 1))
    (fun (bit, ()) _ => bit.toNat) (fun J hJ => ?_)
    (fun J (bit, ()) m1 ⟨rfl, k, hk, hbit, hxk⟩ hJ => ?_)
  · c0_steps; refine hJ _ _ ⟨rfl, 31, by omega, by decide, ?_⟩
    have : 4 ^ 32 = 2 ^ 64 := by decide
    omega
  · subst hbit; c0_steps
    · have hkpos : 1 ≤ k := Classical.byContradiction fun h0 => by
        have hk0 : k = 0 := by omega
        subst hk0; simp at hc; omega
      have h4k := pow4_lt_2_64 hk; have h4k' := pow4_lt_2_64 (k := k - 1) (by omega)
      have hlt_bit : (BitVec.ofNat 64 (4 ^ (k - 1))).toNat < (BitVec.ofNat 64 (4 ^ k)).toNat := by
        rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h4k', Nat.mod_eq_of_lt h4k]
        exact Nat.pow_lt_pow_right (by omega) (by omega)
      rw [pow4_shr2 hkpos h4k]
      exact hJ _ _ hlt_bit ⟨rfl, k - 1, by omega, rfl, by
        rw [show (k - 1) + 1 = k by omega]; rw [Nat.mod_eq_of_lt h4k] at hc; exact hc⟩
    · refine wp_loop_inv
        (fun (rem, r, bit, ()) m2 => m2 = m1 ∧ ∃ e q : Nat, e ≤ 32 ∧
          bit = (if e = 0 then 0#64 else BitVec.ofNat 64 (4 ^ (e - 1))) ∧
          r = BitVec.ofNat 64 (q * 4 ^ e) ∧ q * q * 4 ^ e + rem.toNat = x.toNat ∧
          x.toNat < (q + 1) * (q + 1) * 4 ^ e)
        (fun (_, _, bit, ()) _ => bit.toNat) (fun J2 hJ2 => ?_)
        (fun J2 (rem, r, bit, ()) m2 ⟨rfl, e, q, he32, hbit2, hr, hsum, hub⟩ hJ2 => ?_)
      · c0_steps
        exact hJ2 _ _ ⟨rfl, k + 1, 0, by omega, by simp, by simp, by simp, by simpa using hxk⟩
      · obtain hstep_prep : bit ≠ 0#64 →
            1 ≤ e ∧ bit = BitVec.ofNat 64 (4 ^ (e - 1)) ∧ 4 ^ e = 4 * 4 ^ (e - 1) ∧
            q * 4 ^ e + 4 ^ (e - 1) < 2 ^ 64 ∧
            r + bit = BitVec.ofNat 64 (q * 4 ^ e + 4 ^ (e - 1)) ∧
            r >>> (1 : Nat) = BitVec.ofNat 64 (2 * q * 4 ^ (e - 1)) ∧
            bit >>> (2 : Nat) = (if e - 1 = 0 then 0#64 else BitVec.ofNat 64 (4 ^ (e - 1 - 1))) ∧
            (bit >>> (2 : Nat)).toNat < bit.toNat := by
          intro hne0
          have hepos : 1 ≤ e := Classical.byContradiction fun h0 => by
            have he0 : e = 0 := by omega
            simp [he0] at hbit2; exact hne0 hbit2
          have hbit_eq : bit = BitVec.ofNat 64 (4 ^ (e - 1)) := by
            rw [hbit2]; simp [show e ≠ 0 by omega]
          have h4e1 := pow4_lt_2_64 (k := e - 1) (by omega)
          have h4e : 4 ^ e = 4 * 4 ^ (e - 1) := by
            conv => lhs; rw [show e = (e - 1) + 1 by omega, Nat.pow_succ]; rw [Nat.mul_comm]
          have hrb_lt := isqrt_step_bound (q := q) hepos he32 (by omega) hxlt
          have hr_shr : r >>> (1 : Nat) = BitVec.ofNat 64 (2 * q * 4 ^ (e - 1)) := by
            rw [hr, bv_shr_one (by omega)]; congr 1
            rw [show q * 4 ^ e = (2 * q * 4 ^ (e - 1)) * 2 by
              rw [h4e, show (4 : Nat) = 2 * 2 from rfl]; ac_rfl, Nat.mul_div_cancel _ (by omega)]
          have hbit_next : bit >>> (2 : Nat) =
              if e - 1 = 0 then 0#64 else BitVec.ofNat 64 (4 ^ (e - 1 - 1)) := by
            rw [hbit_eq]; by_cases he1 : e - 1 = 0
            · simp only [he1, ↓reduceIte, Nat.pow_zero]; decide
            · simp only [he1, ↓reduceIte]; exact pow4_shr2 (by omega) h4e1
          have hbit_dec : (bit >>> (2 : Nat)).toNat < bit.toNat := by
            rw [hbit_next, hbit_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h4e1]; split
            · simpa using Nat.pow_pos (a := 4) (n := e - 1) (by omega)
            · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (pow4_lt_2_64 (by omega))]
              exact Nat.pow_lt_pow_right (by omega) (by omega)
          exact ⟨hepos, hbit_eq, h4e, hrb_lt, by rw [hr, hbit_eq, bv_add_ofNat],
            hr_shr, hbit_next, hbit_dec⟩
        obtain hdone_prep : bit = 0#64 →
            r.toNat = q ∧ 1 ≤ q ∧ q * q ≤ x.toNat ∧ x.toNat < (q + 1) * (q + 1) := by
          intro hbz
          have he0 : e = 0 := Classical.byContradiction fun hne => by
            rw [hbz] at hbit2; simp only [hne, ↓reduceIte] at hbit2
            have h1 := congrArg BitVec.toNat hbit2
            rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
              Nat.mod_eq_of_lt (pow4_lt_2_64 (by omega))] at h1
            have := Nat.pow_pos (a := 4) (n := e - 1) (by omega); omega
          subst he0; simp only [Nat.pow_zero, Nat.mul_one] at hr hsum hub
          have hqpos : 1 ≤ q := Classical.byContradiction fun h0 => by
            have : q = 0 := by omega
            subst this; omega
          have hqlt : q < 2 ^ 64 := by have := Nat.le_mul_self q; omega
          exact ⟨by rw [hr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hqlt], hqpos, by omega, hub⟩
        c0_steps
        · obtain ⟨_, hbit_eq, h4e, hrb_lt, hrb_eq, hr_shr, hbit_next, hbit_dec⟩ :=
            hstep_prep (by assumption)
          have h1 : (r + bit).toNat = q * 4 ^ e + 4 ^ (e - 1) := by
            rw [hrb_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hrb_lt]
          have hge : q * 4 ^ e + 4 ^ (e - 1) ≤ rem.toNat := by rw [BitVec.toNat_add] at h1; omega
          have hsub : (rem - (r + bit)).toNat = rem.toNat - (q * 4 ^ e + 4 ^ (e - 1)) := by
            rw [hrb_eq, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hrb_lt]
            have := rem.isLt; omega
          exact hJ2 _ _ hbit_dec ⟨rfl, e - 1, 2 * q + 1, by omega, hbit_next,
            by rw [hr_shr, hbit_eq, bv_add_ofNat]; congr 1; rw [Nat.add_mul, Nat.one_mul],
            by rw [hsub, isqrt_sq_odd]; rw [h4e] at hsum hge ⊢; omega,
            by rw [isqrt_sq_succ_odd, ← h4e]; exact hub⟩
        · obtain ⟨_, _, h4e, hrb_lt, hrb_eq, hr_shr, hbit_next, hbit_dec⟩ :=
            hstep_prep (by assumption)
          have h1 : (r + bit).toNat = q * 4 ^ e + 4 ^ (e - 1) := by
            rw [hrb_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hrb_lt]
          have hlt : rem.toNat < q * 4 ^ e + 4 ^ (e - 1) := by rw [BitVec.toNat_add] at h1; omega
          exact hJ2 _ _ hbit_dec ⟨rfl, e - 1, 2 * q, by omega, hbit_next, hr_shr,
            by rw [isqrt_sq_even, ← h4e]; exact hsum, by rw [isqrt_sq_odd, ← h4e]; omega⟩
        · obtain ⟨hr_toNat, hqpos, hsq, hub0⟩ := hdone_prep (by assumption)
          exact hQ r (by rw [hr_toNat]; exact hsq) (fun h => by omega)
            (fun _ => ⟨by rw [hr_toNat]; exact hqpos, by rw [hr_toNat]; exact hub0⟩)

theorem plain_ilog10_wp (Γ : Env) :
    ∀ a m Q X, plainIlog10Spec a m Q X → Func.wp Γ plain_ilog10_body a m Q X := by
  rintro ⟨x, ⟨⟩⟩ m Q X hQ
  c0_steps
  refine wp_loop_inv
    (fun (r, _, ()) m1 => m1 = m ∧ 1 ≤ r.toNat ∧ r.toNat ≤ 19)
    (fun (r, _, ()) _ => 19 - r.toNat)
    (fun J hJ => ?_) (fun J (r, p, ()) m1 ⟨rfl, h1, h19⟩ hJ => ?_)
  · c0_steps; exact hJ _ _ ⟨rfl, by decide, by decide⟩
  · c0_steps
    · exact hJ _ _ (by c0_bound) ⟨rfl, by c0_bound, by c0_bound⟩
    · exact hQ r h1 h19
    · exact hQ r h1 h19

/-! ## 2. `plain_arena_next` and `plain_alloc_cl` -/

theorem plain_arena_next_wp (Γ : Env) :
    ∀ a m Q X, plainArenaNextSpec a m Q X → Func.wp Γ plain_arena_next_body a m Q X := by
  rintro ⟨h, cref, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  obtain har_len := hlen.arena_len_arr; obtain hale := hlen.arena_len_le
  obtain hcap : c.arena_cap < 2 * 2 ^ 28 := c.harena
  obtain hcref32 : cref.toNat < 2 ^ 32 := cref.isLt
  obtain hidx0 : cref.toNat % 2 ^ 64 = cref.toNat := Nat.mod_eq_of_lt (by omega)
  obtain hidx2 : (cref.toNat + 2) % 2 ^ 64 = cref.toNat + 2 := Nat.mod_eq_of_lt (by omega)
  obtain h2_64 : (2 : BitVec 64).toNat = 2 := rfl
  obtain h3_64 : (3 : BitVec 64).toNat = 3 := rfl
  obtain htrunc_al : BitVec.setWidth 32 (BitVec.ofNat 64 s.arena_len) =
      BitVec.ofNat 32 s.arena_len :=
    BitVec.eq_of_toNat_eq (by simp [Nat.mod_eq_of_lt (by omega : s.arena_len < 2 ^ 32)])
  c0_steps
  · have hgt : cref.toNat + 3 > s.arena_len := by c0_bound
    rw [htrunc_al]; simpa [arenaNextOff, hgt] using hQ
  · rename_i hle3_bv
    have hle3 : cref.toNat + 3 ≤ s.arena_len := by
      simp only [h3_64, Nat.reducePow] at hle3_bv; omega
    have hcref2_lt : cref.toNat + 2 < s.arena.length := by omega
    have hsz32 := (s.arena[cref.toNat + 2]'hcref2_lt).isLt
    have hgtp : cref.toNat + 3 + (s.arena[cref.toNat + 2]'hcref2_lt).toNat > s.arena_len := by
      simp only [h2_64, h3_64, hidx2] at hc; omega
    rw [htrunc_al]
    simpa [arenaNextOff, show ¬ (cref.toNat + 3 > s.arena_len) by omega,
      List.getElem?_eq_getElem hcref2_lt, hgtp] using hQ
  · obtain hle3 : cref.toNat + 3 ≤ s.arena_len := by simp only [h3_64, Nat.reducePow] at *; omega
    obtain hcref_lt : cref.toNat < s.arena.length := by omega
    obtain hcref2_lt : cref.toNat + 2 < s.arena.length := by omega
    obtain hsz32 := (s.arena[cref.toNat + 2]'hcref2_lt).isLt
    obtain hshrk : s.arena[cref.toNat]'hcref_lt &&& 0x00800000#32 ≠ 0#32 := by
      simpa [hidx0] using hc
    obtain hlep : cref.toNat + 3 + (s.arena[cref.toNat + 2]'hcref2_lt).toNat ≤ s.arena_len := by
      simp only [h2_64, h3_64, hidx2] at *; omega
    let p0 := cref.toNat + 3 + (s.arena[cref.toNat + 2]'hcref2_lt).toNat
    have hp0_bv : (cref.setWidth 64 + 3 +
        (s.arena[(cref.setWidth 64 + 2).toNat]'(by c0_bound)).setWidth 64) =
        BitVec.ofNat 64 p0 := by
      have hsub : (cref.setWidth 64 + 2).toNat = cref.toNat + 2 := by c0_bound
      apply BitVec.eq_of_toNat_eq; simp only [hsub]; c0_bound
    have hnext_eq : arenaNextOff s.arena s.arena_len cref.toNat =
        arenaSkipShrk s.arena s.arena_len p0 (s.arena_len - p0) := by
      unfold arenaNextOff
      simp only [show ¬ (cref.toNat + 3 > s.arena_len) by omega, ↓reduceIte,
        List.getElem?_eq_getElem hcref_lt, List.getElem?_eq_getElem hcref2_lt, Option.getD_some,
        show ¬ (cref.toNat + 3 + (s.arena[cref.toNat + 2]'hcref2_lt).toNat > s.arena_len) by omega,
        hshrk, ne_eq, not_false_eq_true]; rfl
    refine wp_loop_inv
      (fun (p, ()) m1 => m1 = m ∧ p.toNat ≤ s.arena_len ∧
        arenaSkipShrk s.arena s.arena_len p.toNat (s.arena_len - p.toNat) =
          arenaSkipShrk s.arena s.arena_len p0 (s.arena_len - p0))
      (fun (p, ()) _ => s.arena_len - p.toNat)
      (fun J hLoop => ?_) (fun J (p, ()) m1 ⟨rfl, hple, hskip⟩ hLoop => ?_)
    · c0_steps; exact hLoop _ _ ⟨rfl, by rw [hp0_bv]; c0_bound, by
        rw [hp0_bv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : p0 < 2 ^ 64)]⟩
    · c0_steps
      · have hplt : p.toNat < s.arena_len := by c0_bound
        have hpar : p.toNat < s.arena.length := by omega
        have hne : s.arena[p.toNat]'hpar ≠ 0xFFFFFFFF#32 := hc
        have hstep : arenaSkipShrk s.arena s.arena_len (p.toNat + 1)
            (s.arena_len - (p.toNat + 1)) =
            arenaSkipShrk s.arena s.arena_len p.toNat (s.arena_len - p.toNat) := by
          conv => rhs; rw [show s.arena_len - p.toNat = (s.arena_len - (p.toNat + 1)) + 1 by omega]
                  unfold arenaSkipShrk
          simp only [hplt, ↓reduceIte, List.getElem?_eq_getElem hpar, Option.getD_some,
            hne, ne_eq, not_false_eq_true]
        refine hLoop _ _ (by c0_bound) ⟨rfl, by c0_bound, ?_⟩
        rw [show (p + 1).toNat = p.toNat + 1 by c0_bound, hstep, hskip]
      · have hplt : p.toNat < s.arena_len := by c0_bound
        have hpar : p.toNat < s.arena.length := by omega
        have heq_ff : s.arena[p.toNat]'hpar = 0xFFFFFFFF#32 := by assumption
        rw [hnext_eq, ← hskip,
          show s.arena_len - p.toNat = (s.arena_len - (p.toNat + 1)) + 1 by omega] at hQ
        simp only [arenaSkipShrk, hplt, ↓reduceIte, List.getElem?_eq_getElem hpar,
          Option.getD_some, heq_ff] at hQ
        rw [show (p + 1).setWidth 32 = BitVec.ofNat 32 (p.toNat + 1) from
          BitVec.eq_of_toNat_eq (by c0_bound)]; exact hQ
      · have hpeq : p.toNat = s.arena_len := by c0_bound
        rw [hnext_eq, ← hskip, hpeq, Nat.sub_self] at hQ
        simp only [arenaSkipShrk, Nat.min_self] at hQ
        rw [show p.setWidth 32 = BitVec.ofNat 32 s.arena_len from
          BitVec.eq_of_toNat_eq (by c0_bound)]; exact hQ
  · have hle3 : cref.toNat + 3 ≤ s.arena_len := by simp only [h3_64, Nat.reducePow] at *; omega
    have hcref_lt : cref.toNat < s.arena.length := by omega
    have hcref2_lt : cref.toNat + 2 < s.arena.length := by omega
    have hsz32 := (s.arena[cref.toNat + 2]'hcref2_lt).isLt
    have hshrk : s.arena[cref.toNat]'hcref_lt &&& 0x00800000#32 = 0#32 := by simpa [hidx0] using hc
    have hlep : cref.toNat + 3 + (s.arena[cref.toNat + 2]'hcref2_lt).toNat ≤ s.arena_len := by
      simp only [h2_64, h3_64, hidx2] at *; omega
    have hfin : arenaNextOff s.arena s.arena_len cref.toNat =
        cref.toNat + 3 + (s.arena[cref.toNat + 2]'hcref2_lt).toNat := by
      unfold arenaNextOff
      simp only [show ¬ (cref.toNat + 3 > s.arena_len) by omega, ↓reduceIte,
        List.getElem?_eq_getElem hcref_lt, List.getElem?_eq_getElem hcref2_lt, Option.getD_some,
        show ¬ (cref.toNat + 3 + (s.arena[cref.toNat + 2]'hcref2_lt).toNat > s.arena_len) by omega,
        hshrk, ne_eq, not_true_eq_false]
    rw [hfin] at hQ
    have hsub : (cref.setWidth 64 + 2).toNat = cref.toNat + 2 := by c0_bound
    rw [show (cref.setWidth 64 + 3 +
        (s.arena[(cref.setWidth 64 + 2).toNat]'(by c0_bound)).setWidth 64).setWidth 32 =
        BitVec.ofNat 32 (cref.toNat + 3 + (s.arena[cref.toNat + 2]'hcref2_lt).toNat) from
      BitVec.eq_of_toNat_eq (by simp only [hsub]; c0_bound)]
    exact hQ

private theorem bv32_and_two_pow_eq_zero {g : BitVec 32} {k : Nat}
    (hg : g.toNat < 2 ^ 19) (hk : 19 ≤ k) (hk32 : k < 32) :
    g &&& BitVec.ofNat 32 (2 ^ k) = 0#32 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_zero]
  by_cases hik : i = k
  · subst hik; rw [BitVec.getLsbD_eq_getElem hi, BitVec.getElem_eq_testBit_toNat,
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hg (Nat.pow_le_pow_right (by omega) hk))]; simp
  · rw [BitVec.getLsbD_eq_getElem hi (x := BitVec.ofNat 32 (2 ^ k)),
      BitVec.getElem_eq_testBit_toNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by omega) hk32), Nat.testBit_two_pow]
    simp [Ne.symm hik]

private theorem alloc_hdr_bits (g : BitVec 32) (red : Bool) (hg : g.toNat ≤ 0x7FFFF) :
    let w := g ||| (if red then 0x00400000#32 else 0#32)
    (w &&& 0x00800000#32) = 0#32 ∧ (w &&& 0x00080000#32) = 0#32 ∧
    ((w &&& 0x00400000#32) ≠ 0#32 ↔ red = true) := by
  intro w; have hg' : g.toNat < 2 ^ 19 := Nat.lt_of_le_of_lt hg (by decide)
  have h1 := bv32_and_two_pow_eq_zero (k := 23) hg' (by omega) (by omega)
  have h2 := bv32_and_two_pow_eq_zero (k := 19) hg' (by omega) (by omega)
  have h3 := bv32_and_two_pow_eq_zero (k := 22) hg' (by omega) (by omega)
  cases red
  · simp [w, h1, h2, h3]
  · refine ⟨?_, ?_, ?_⟩
    · apply BitVec.eq_of_getElem_eq; intro i hi
      have := congrArg (fun x => x[i]'hi) h1
      have := congrArg (fun x => x[i]'hi) (by decide : (0x00400000#32 &&& 0x00800000#32) = 0#32)
      simp only [w, ↓reduceIte, BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_zero] at *
      grind
    · apply BitVec.eq_of_getElem_eq; intro i hi
      have := congrArg (fun x => x[i]'hi) h2
      have := congrArg (fun x => x[i]'hi) (by decide : (0x00400000#32 &&& 0x00080000#32) = 0#32)
      simp only [w, ↓reduceIte, BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_zero] at *
      grind
    · simp only [w, ↓reduceIte, iff_true]; intro h0
      have hb := congrArg (fun x => x.getLsbD 22) h0; simp at hb

theorem plain_alloc_cl_wp (Γ : Env) :
    ∀ a m Q X, plainAllocClSpec a m Q X → Func.wp Γ plain_alloc_cl_body a m Q X := by
  rintro ⟨h, sz, glue, red, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  obtain har_len := hlen.arena_len_arr
  obtain hale := hlen.arena_len_le
  obtain hcap : c.arena_cap < 2 * 2 ^ 28 := c.harena
  c0_steps
  · have hlt : c.arena_cap - s.arena_len < 3 + sz.toNat := by c0_bound
    simp only [hlt, ↓reduceIte] at hQ
    exact hQ
  all_goals
    have hsz32 : sz.toNat < 2 ^ 32 := sz.isLt
    have hge : ¬ (c.arena_cap - s.arena_len < 3 + sz.toNat) := by c0_bound
    simp only [hge, ↓reduceIte] at hQ
    have hfit : s.arena_len + 3 + sz.toNat ≤ c.arena_cap := by omega
    have hne_al : (BitVec.ofNat 64 s.arena_len + (3 + sz.setWidth 64)).toNat =
        s.arena_len + 3 + sz.toNat := by c0_bound
    have h1_eq : (BitVec.ofNat 64 s.arena_len + 1).toNat = s.arena_len + 1 := by c0_bound
    have h2_eq : (BitVec.ofNat 64 s.arena_len + 2).toNat = s.arena_len + 2 := by c0_bound
    have h0_eq : (BitVec.ofNat 64 s.arena_len).toNat = s.arena_len := by c0_bound
    rw [hne_al, h0_eq, h1_eq, h2_eq] at hm
    refine hQ _ _ { hlen with arena_len_arr := by simp [har_len], arena_len_le := hfit }
      (fun k hk => by
        rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
          List.getElem?_set_ne (by omega)]) ?_ ?_ ?_ ?_ hm
    · rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
        List.getElem?_set_self (by omega), Option.getD_some]
      first
      | exact (alloc_hdr_bits 0x7FFFF#32 true (by decide)).1
      | exact (alloc_hdr_bits 0x7FFFF#32 false (by decide)).1
      | exact (alloc_hdr_bits glue true (by c0_bound)).1
      | exact (alloc_hdr_bits glue false (by c0_bound)).1
    · rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
        List.getElem?_set_self (by omega), Option.getD_some]
      first
      | exact (alloc_hdr_bits 0x7FFFF#32 true (by decide)).2.1
      | exact (alloc_hdr_bits 0x7FFFF#32 false (by decide)).2.1
      | exact (alloc_hdr_bits glue true (by c0_bound)).2.1
      | exact (alloc_hdr_bits glue false (by c0_bound)).2.1
    · rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
        List.getElem?_set_self (by omega), Option.getD_some]
      first
      | (subst hc; exact (alloc_hdr_bits 0x7FFFF#32 true (by decide)).2.2)
      | (subst hc; exact (alloc_hdr_bits 0x7FFFF#32 false (by decide)).2.2)
      | (subst hc; exact (alloc_hdr_bits glue true (by c0_bound)).2.2)
      | (subst hc; exact (alloc_hdr_bits glue false (by c0_bound)).2.2)
    · rw [List.getElem?_set_self (by simp [har_len]; omega), Option.getD_some]

/-! ## 4. Pure heapsort & watch-stack compaction helpers -/

private def wsVal (ws : List (BitVec 32)) (i : Nat) : Nat :=
  (ws[i]?.getD 0#32).toNat

private def WsCovers (ws : List (BitVec 32)) (n nlits : Nat) (sz : Nat → Nat) : Prop :=
  (∀ i < n, wsVal ws i < nlits ∧ 0 < sz (wsVal ws i)) ∧
  (∀ i < n, ∀ j < n, i ≠ j → wsVal ws i ≠ wsVal ws j) ∧
  (∀ l < nlits, 0 < sz l → ∃ i < n, wsVal ws i = l)

private def MaxHeapExcept (key : Nat → Nat) (ws : List (BitVec 32))
    (lo hi hole : Nat) : Prop :=
  ∀ p, lo ≤ p → p ≠ hole →
    (2 * p + 1 < hi → key (wsVal ws (2 * p + 1)) ≤ key (wsVal ws p)) ∧
    (2 * p + 2 < hi → key (wsVal ws (2 * p + 2)) ≤ key (wsVal ws p))

private def HoleParentOk (key : Nat → Nat) (ws : List (BitVec 32))
    (lo hi root : Nat) : Prop :=
  0 < root → lo ≤ (root - 1) / 2 →
    (2 * root + 1 < hi → key (wsVal ws (2 * root + 1)) ≤ key (wsVal ws ((root - 1) / 2))) ∧
    (2 * root + 2 < hi → key (wsVal ws (2 * root + 2)) ≤ key (wsVal ws ((root - 1) / 2)))

private def SortedRange (key : Nat → Nat) (ws : List (BitVec 32)) (lo hi : Nat) : Prop :=
  ∀ i j, lo ≤ i → i ≤ j → j < hi → key (wsVal ws i) ≤ key (wsVal ws j)

private def SplitLe (key : Nat → Nat) (ws : List (BitVec 32)) (mid hi : Nat) : Prop :=
  ∀ i < mid, ∀ j, mid ≤ j → j < hi → key (wsVal ws i) ≤ key (wsVal ws j)

private def swapIdx (i j k : Nat) : Nat :=
  if k = i then j else if k = j then i else k

private theorem swapIdx_invol (i j k : Nat) : swapIdx i j (swapIdx i j k) = k := by
  unfold swapIdx; grind

private theorem wsVal_swap {ws : List (BitVec 32)} {i j : Nat}
    (hi : i < ws.length) (hj : j < ws.length) (k : Nat) :
    wsVal ((ws.set i (ws[j]'hj)).set j (ws[i]'hi)) k = wsVal ws (swapIdx i j k) := by
  unfold wsVal swapIdx
  by_cases hkj : k = j
  · subst hkj; rw [List.getElem?_set_self (by simp; omega)]
    by_cases hki : k = i <;> simp [hki, List.getElem?_eq_getElem hi]
  · rw [List.getElem?_set_ne (by omega)]
    by_cases hki : k = i
    · subst hki; rw [List.getElem?_set_self (by omega)]; simp [List.getElem?_eq_getElem hj]
    · rw [List.getElem?_set_ne (by omega)]; simp [hki, hkj]

private theorem wsCovers_swap {ws : List (BitVec 32)} {n nlits i j : Nat} {sz : Nat → Nat}
    (hc : WsCovers ws n nlits sz) (hi : i < n) (hj : j < n) (hn : n ≤ ws.length) :
    WsCovers ((ws.set i (ws[j]'(by omega))).set j (ws[i]'(by omega))) n nlits sz := by
  obtain ⟨hb, hnd, hcov⟩ := hc
  have hlt : ∀ k < n, swapIdx i j k < n := fun k hk => by unfold swapIdx; grind
  refine ⟨fun k hk => by rw [wsVal_swap (by omega) (by omega)]; exact hb _ (hlt k hk),
    fun a ha b hb' hab => by
      rw [wsVal_swap (by omega) (by omega), wsVal_swap (by omega) (by omega)]
      refine hnd _ (hlt a ha) _ (hlt b hb') fun heq => hab ?_
      simpa [swapIdx_invol] using congrArg (swapIdx i j) heq,
    fun l hl hsz => by
      obtain ⟨k, hk, hkl⟩ := hcov l hl hsz
      exact ⟨swapIdx i j k, hlt k hk, by
        rw [wsVal_swap (by omega) (by omega), swapIdx_invol]; exact hkl⟩⟩

private theorem maxHeap_sift_step {key : Nat → Nat} {ws : List (BitVec 32)}
    {lo hi root child : Nat} (hlo : lo ≤ root) (hchi : child < hi) (hhi : hi ≤ ws.length)
    (hch : child = 2 * root + 1 ∨ child = 2 * root + 2)
    (hmax : MaxHeapExcept key ws lo hi root) (hpar : HoleParentOk key ws lo hi root)
    (hlt : key (wsVal ws root) < key (wsVal ws child))
    (hsib : (2 * root + 1 < hi → key (wsVal ws (2 * root + 1)) ≤ key (wsVal ws child)) ∧
            (2 * root + 2 < hi → key (wsVal ws (2 * root + 2)) ≤ key (wsVal ws child))) :
    let ws' := (ws.set root (ws[child]'(by omega))).set child (ws[root]'(by omega))
    MaxHeapExcept key ws' lo hi child ∧ HoleParentOk key ws' lo hi child := by
  intro ws'; have hsw := wsVal_swap (ws := ws) (i := root) (j := child) (by omega) (by omega)
  refine ⟨fun p hp hpc => ?_, fun _ _ => ?_⟩
  · have hstep : ∀ c, (c = 2 * p + 1 ∨ c = 2 * p + 2) → c < hi →
        key (wsVal ws' c) ≤ key (wsVal ws' p) := by
      intro c hc hci; rw [hsw c, hsw p]
      by_cases hpr : p = root
      · rcases hpr with rfl; rw [show swapIdx p child p = child by unfold swapIdx; simp]
        by_cases hcc : c = child
        · rcases hcc with rfl; rw [show swapIdx p c c = p by unfold swapIdx; grind]; omega
        · rw [show swapIdx p child c = c by unfold swapIdx; grind]
          rcases hc with rfl | rfl; exact hsib.1 hci; exact hsib.2 hci
      · rw [show swapIdx root child p = p by unfold swapIdx; grind]
        by_cases hcr : c = root
        · subst hcr
          have hproot : p = (c - 1) / 2 := by omega
          subst hproot
          rw [show swapIdx c child c = child by unfold swapIdx; simp]
          rcases hch with rfl | rfl; exact (hpar (by omega) hp).1 hchi
          exact (hpar (by omega) hp).2 hchi
        · rw [show swapIdx root child c = c by unfold swapIdx; grind]
          rcases hc with rfl | rfl; exact (hmax p hp hpr).1 hci; exact (hmax p hp hpr).2 hci
    exact ⟨hstep _ (Or.inl rfl), hstep _ (Or.inr rfl)⟩
  · rw [show (child - 1) / 2 = root by omega, hsw root,
      show swapIdx root child root = child by unfold swapIdx; simp]
    exact ⟨fun h1 => by rw [hsw, show swapIdx root child (2 * child + 1) = 2 * child + 1 by
        unfold swapIdx; grind]; exact (hmax child (by omega) (by omega)).1 h1,
      fun h2 => by rw [hsw, show swapIdx root child (2 * child + 2) = 2 * child + 2 by
        unfold swapIdx; grind]; exact (hmax child (by omega) (by omega)).2 h2⟩

private theorem maxHeap_sift_done {key : Nat → Nat} {ws : List (BitVec 32)}
    {lo hi root : Nat} (hmax : MaxHeapExcept key ws lo hi root)
    (h1 : 2 * root + 1 < hi → key (wsVal ws (2 * root + 1)) ≤ key (wsVal ws root))
    (h2 : 2 * root + 2 < hi → key (wsVal ws (2 * root + 2)) ≤ key (wsVal ws root)) :
    MaxHeapExcept key ws lo hi hi := fun p hp _ =>
  if hpr : p = root then hpr ▸ ⟨h1, h2⟩ else hmax p hp hpr

private theorem maxHeap_root_ge {key : Nat → Nat} {ws : List (BitVec 32)} {hi : Nat}
    (hmax : MaxHeapExcept key ws 0 hi hi) :
    ∀ i < hi, key (wsVal ws i) ≤ key (wsVal ws 0) := by
  intro i; induction i using Nat.strongRecOn with
  | ind i ih =>
    intro hilt; rcases Nat.eq_zero_or_pos i with rfl | hpos
    · exact Nat.le_refl _
    · have hrec := ih _ (show (i - 1) / 2 < i by omega) (by omega)
      have hstep := hmax ((i - 1) / 2) (by omega) (by omega)
      by_cases hodd : i = 2 * ((i - 1) / 2) + 1
      · have := hstep.1 (by omega); rw [← hodd] at this; omega
      · have := hstep.2 (by omega); rw [← show i = 2 * ((i - 1) / 2) + 2 by omega] at this; omega

private theorem extract_swap_step {key : Nat → Nat} {ws : List (BitVec 32)} {e n : Nat}
    (hmax : MaxHeapExcept key ws 0 (e + 1) (e + 1))
    (hsp : SplitLe key ws (e + 1) n) (hsrt : SortedRange key ws (e + 1) n)
    (he : 0 < e) (hen : e < n) (hn : n ≤ ws.length) :
    let ws' := (ws.set 0 (ws[e]'(by omega))).set e (ws[0]'(by omega))
    MaxHeapExcept key ws' 0 e 0 ∧ HoleParentOk key ws' 0 e 0 ∧
      SplitLe key ws' e n ∧ SortedRange key ws' e n := by
  intro ws'; have hsw := wsVal_swap (ws := ws) (i := 0) (j := e) (by omega) (by omega)
  have hroot := maxHeap_root_ge hmax
  have hfix : ∀ k, 0 < k → k < e → swapIdx 0 e k = k := fun k _ _ => by unfold swapIdx; grind
  refine ⟨fun p _ hp0 => ⟨fun h1 => ?_, fun h2 => ?_⟩, fun h0 => by omega,
    fun i hi j hj1 hj2 => ?_, fun i j hi1 hij hj2 => ?_⟩
  · rw [hsw, hsw, hfix _ (by omega) h1, hfix _ (by omega) (by omega)]
    exact (hmax p (by omega) (by omega)).1 (by omega)
  · rw [hsw, hsw, hfix _ (by omega) h2, hfix _ (by omega) (by omega)]
    exact (hmax p (by omega) (by omega)).2 (by omega)
  · rw [hsw i, hsw j]; have hisw : swapIdx 0 e i < e + 1 := by unfold swapIdx; grind
    by_cases hje : j = e
    · subst hje; rw [show swapIdx 0 j j = 0 by unfold swapIdx; grind]; exact hroot _ hisw
    · rw [show swapIdx 0 e j = j by unfold swapIdx; grind]; exact hsp _ hisw _ (by omega) hj2
  · rw [hsw i, hsw j]
    by_cases hie : i = e
    · subst hie; rw [show swapIdx 0 i i = 0 by unfold swapIdx; grind]
      by_cases hje : j = i
      · subst hje; rw [show swapIdx 0 j j = 0 by unfold swapIdx; grind]; exact Nat.le_refl _
      · rw [show swapIdx 0 i j = j by unfold swapIdx; grind]
        exact hsp 0 (by omega) j (by omega) hj2
    · rw [show swapIdx 0 e i = i by unfold swapIdx; grind,
        show swapIdx 0 e j = j by unfold swapIdx; grind]
      exact hsrt i j (by omega) hij hj2

private theorem split_sorted_swap_lt {key : Nat → Nat} {ws : List (BitVec 32)} {e n i j : Nat}
    (hsp : SplitLe key ws e n) (hsrt : SortedRange key ws e n)
    (hi : i < e) (hj : j < e) (hen : e ≤ n) (hn : n ≤ ws.length) :
    let ws' := (ws.set i (ws[j]'(by omega))).set j (ws[i]'(by omega))
    SplitLe key ws' e n ∧ SortedRange key ws' e n := by
  intro ws'; have hsw := wsVal_swap (ws := ws) (i := i) (j := j) (by omega) (by omega)
  have hge : ∀ k, e ≤ k → swapIdx i j k = k := fun k _ => by unfold swapIdx; grind
  have hlt : ∀ k < e, swapIdx i j k < e := fun k _ => by unfold swapIdx; grind
  exact ⟨fun a ha b hb1 hb2 => by rw [hsw a, hsw b, hge b hb1]; exact hsp _ (hlt a ha) b hb1 hb2,
    fun a b ha hab hb => by rw [hsw a, hsw b, hge a ha, hge b (by omega)]; exact hsrt a b ha hab hb⟩

private theorem defrag_sorted_gap {c : PlainCfg} {s : PlainState} {ws : List (BitVec 32)} {n : Nat}
    (hlay : WatchStackLayout c s) (hcov : WsCovers ws n (2 * c.mv) (watchSize s))
    (hsrt : SortedRange (watchOff s) ws 0 n) {i j : Nat} (hij : i < j) (hjn : j < n) :
    watchOff s (wsVal ws i) + watchSize s (wsVal ws i) ≤ watchOff s (wsVal ws j) := by
  have hi := hcov.1 i (by omega); have hj := hcov.1 j hjn
  have hle := hsrt i j (by omega) (by omega) hjn
  rcases hlay.disjoint _ _ hi.1 hj.1 (hcov.2.1 i (by omega) j hjn (by omega)) hi.2 hj.2 with h | h
  · exact h
  · omega

private theorem wvec_set_even_eq {wvec : List (BitVec 32)} {l : Nat} {v : BitVec 32}
    (hl : 2 * l < wvec.length) (j : Nat) :
    (wvec.set (2 * l) v)[2 * j + 1]? = wvec[2 * j + 1]? ∧
    (j ≠ l → (wvec.set (2 * l) v)[2 * j]? = wvec[2 * j]?) ∧
    (wvec.set (2 * l) v)[2 * l]? = some v :=
  ⟨List.getElem?_set_ne (by omega), fun _ => List.getElem?_set_ne (by omega),
   List.getElem?_set_self hl⟩

private theorem defrag_finalize {c : PlainCfg} {s : PlainState}
    {wvecC wstkC wsort2 : List (BitVec 32)} {n p : Nat} (hlay : WatchStackLayout c s)
    (hcov : WsCovers wsort2 n (2 * c.mv) (watchSize s)) (_hp1 : 1 ≤ p)
    (hsz : ∀ l < 2 * c.mv, (wvecC[2 * l + 1]?.getD 0#32).toNat = watchSize s l)
    (hzero : ∀ l < 2 * c.mv, watchSize s l = 0 → (wvecC[2 * l]?.getD 0#32).toNat = 0)
    (hdone : ∀ j < n, let l := wsVal wsort2 j; let off := (wvecC[2 * l]?.getD 0#32).toNat;
      1 ≤ off ∧ off + watchSize s l ≤ p ∧
      ∀ k < watchSize s l, wstkC[off + k]? = s.wstk[watchOff s l + k]?)
    (hdisj : ∀ a < n, ∀ b < n, a ≠ b →
      let la := wsVal wsort2 a; let lb := wsVal wsort2 b;
      (wvecC[2 * la]?.getD 0#32).toNat + watchSize s la ≤ (wvecC[2 * lb]?.getD 0#32).toNat ∨
      (wvecC[2 * lb]?.getD 0#32).toNat + watchSize s lb ≤ (wvecC[2 * la]?.getD 0#32).toNat) :
    let s' : PlainState :=
      { s with wvec := wvecC, wstk := wstkC, wlen := p, wusable := 0#64,
               heur := { s.heur with wsort := wsort2 } }
    WatchStackLayout c s' ∧
      ∀ l < 2 * c.mv, watchSize s' l = watchSize s l ∧
        ∀ k < watchSize s l, s'.wstk[watchOff s' l + k]? = s.wstk[watchOff s l + k]? := by
  intro s'
  have hsz' : ∀ l < 2 * c.mv, watchSize s' l = watchSize s l := hsz
  refine ⟨⟨fun l hl => ?_, fun l hl hp => ?_, fun l1 l2 h1 h2 hne hp1 hp2 => ?_,
    fun l hl k hk => ?_⟩, fun l hl => ⟨hsz' l hl, fun k hk => ?_⟩⟩
  · rw [hsz' l hl]; rcases Nat.eq_zero_or_pos (watchSize s l) with hz | hp
    · change (wvecC[2 * l]?.getD 0#32).toNat + _ ≤ p; rw [hz, hzero l hl hz]; omega
    · obtain ⟨j, hj, rfl⟩ := hcov.2.2 l hl hp; exact (hdone j hj).2.1
  · rw [hsz' l hl] at hp; obtain ⟨j, hj, rfl⟩ := hcov.2.2 l hl hp; exact (hdone j hj).1
  · rw [hsz' l1 h1] at hp1 ⊢; rw [hsz' l2 h2] at hp2 ⊢
    obtain ⟨a, ha, rfl⟩ := hcov.2.2 l1 h1 hp1; obtain ⟨b, hb, rfl⟩ := hcov.2.2 l2 h2 hp2
    exact hdisj a ha b hb fun hab => hne (by rw [hab])
  · rw [hsz' l hl] at hk; obtain ⟨j, hj, rfl⟩ := hcov.2.2 l hl (by omega)
    change wstkC[(wvecC[2 * wsVal wsort2 j]?.getD 0#32).toNat + k]? ≠ _
    rw [(hdone j hj).2.2 k hk]; exact hlay.no_sentinel _ hl k hk
  · obtain ⟨j, hj, rfl⟩ := hcov.2.2 l hl (by omega); exact (hdone j hj).2.2 k hk

/-! ## 5. `plain_wstack_defrag` -/

private theorem list_getElem_toNat_eq {xs : List (BitVec 32)} {i j : Nat}
    (hi : i < xs.length) (hij : i = j) : (xs[i]'hi).toNat = (xs[j]?.getD 0#32).toNat := by
  subst hij; rw [List.getElem?_eq_getElem hi, Option.getD_some]

private theorem ws_idx_shl1 {s : PlainState} {ws : List (BitVec 32)} {mv n idx k : Nat}
    (hmv : mv < 2 ^ 28) (hcov : WsCovers ws n (2 * mv) (watchSize s))
    (hidx : idx < ws.length) (hik : idx = k) (hkn : k < n) :
    ((ws[idx]'hidx).setWidth 64 <<< (1 : Nat)).toNat = 2 * wsVal ws k ∧
    2 * wsVal ws k < 4 * mv := by
  have h1 : (ws[idx]'hidx).toNat = wsVal ws k := list_getElem_toNat_eq hidx hik
  have h2 : wsVal ws k < 2 * mv := (hcov.1 k hkn).1
  refine ⟨?_, by omega⟩
  rw [BitVec.toNat_shiftLeft, zext_toNat _ (by decide), h1]; simp [Nat.shiftLeft_eq]; omega

private theorem ws_idx_off {c : PlainCfg} {s : PlainState} {ws wvec1 : List (BitVec 32)}
    {n idx k : Nat} (hcov : WsCovers ws n (2 * c.mv) (watchSize s))
    (hoff1 : ∀ j < 2 * c.mv, 0 < watchSize s j → wvec1[2 * j]? = s.wvec[2 * j]?)
    (hidx : idx < wvec1.length) (hkn : k < n) (hidx_eq : idx = 2 * wsVal ws k) :
    (wvec1[idx]'hidx).toNat = watchOff s (wsVal ws k) := by
  rw [list_getElem_toNat_eq hidx hidx_eq]
  have h := hcov.1 k hkn
  unfold watchOff; rw [hoff1 _ h.1 h.2]

private abbrev qOp1 {t r : Ty} (code : OpCode [t] [r]) (a : Arg Val t) : Op Val [r] :=
  { sig := [t], code := code, args := (a, ()) }

private abbrev qOp2 {t r : Ty} (code : OpCode [t, t] [r]) (a b : Arg Val t) : Op Val [r] :=
  { sig := [t, t], code := code, args := (a, b, ()) }

private abbrev dIdx4 (base idx : Val i64) (k : Val i64 → Expr Val Cont []) : Expr Val Cont [] :=
  Expr.let_ (qOp2 (.mul i64) (Arg.var idx) (Arg.imm 4)) fun p1 =>
  Expr.let_ (qOp2 (.add i64) (Arg.var base) (Arg.var p1.fst)) fun p2 => k p2.fst

private abbrev dWsOff (pWvec pWsort idx : Val i64) (k : Val i32 → Val i32 → Expr Val Cont []) :
    Expr Val Cont [] :=
  dIdx4 pWsort idx fun a1 => Expr.load i32 (Arg.var a1) fun ld =>
  Expr.let_ (qOp1 (.zext 32 64) (Arg.var ld)) fun p1 =>
  Expr.let_ (qOp1 (.sext 32 64) (Arg.imm 1)) fun p2 =>
  Expr.let_ (qOp2 (.shl i64) (Arg.var p1.fst) (Arg.var p2.fst)) fun p3 =>
  dIdx4 pWvec p3.fst fun a2 => Expr.load i32 (Arg.var a2) fun ld_o => k ld ld_o

/-- Shared inner `while (true)` sift-down `Expr` emitted in build-heap and extract-max. -/
private abbrev defragSiftExpr (pWvec pWsort lim : Val i64) (Jbrk : Cont [i64])
    (root0 : Arg Val i64) : Expr Val Cont [] :=
  Expr.group (sig := [[i64]]) (fun Js_1 => Blocks.cons (fun (p : Tup Val [i64]) =>
    Expr.jnz (Arg.imm true)
      (Expr.let_ (qOp1 (.sext 32 64) (Arg.imm 1)) fun p_1 =>
       Expr.let_ (qOp2 (.shl i64) (Arg.var p.fst) (Arg.var p_1.fst)) fun p_2 =>
       Expr.let_ (qOp2 (.add i64) (Arg.var p_2.fst) (Arg.imm 1)) fun p_3 =>
       Expr.let_ (qOp2 (.cmp .uge i64 .bool rfl) (Arg.var p_3.fst) (Arg.var lim)) fun p_4 =>
       Expr.jnz (Arg.var p_4.fst) (Expr.jump Jbrk (Arg.var p.fst, ()))
         (dWsOff pWvec pWsort p_3.fst fun _ ld_co =>
          Expr.group (sig := [[i64, i32]]) (fun _Js_2 => Blocks.cons
            (fun (p_12 : Tup Val [i64, i32]) =>
              dWsOff pWvec pWsort p.fst fun ld_rl ld_ro =>
              Expr.let_ (qOp2 (.cmp .uge i32 .bool rfl) (Arg.var ld_ro) (Arg.var p_12.snd.fst))
                fun p_20 =>
              Expr.jnz (Arg.var p_20.fst) (Expr.jump Jbrk (Arg.var p.fst, ()))
                (dIdx4 pWsort p.fst fun p_22 =>
                 dIdx4 pWsort p_12.fst fun p_24 =>
                 Expr.load i32 (Arg.var p_24) fun ld_wc =>
                 Expr.store (t := i32) (Arg.var ld_wc) (Arg.var p_22)
                   (dIdx4 pWsort p_12.fst fun p_26 =>
                    Expr.store (t := i32) (Arg.var ld_rl) (Arg.var p_26)
                      (Expr.jump Js_1.fst (Arg.var p_12.fst, ()))))) Blocks.nil)
            fun Js =>
            Expr.let_ (qOp2 (.add i64) (Arg.var p_3.fst) (Arg.imm 1)) fun p_27 =>
            Expr.let_ (qOp2 (.cmp .ult i64 .bool rfl) (Arg.var p_27.fst) (Arg.var lim)) fun p_28 =>
            Expr.jnz (Arg.var p_28.fst)
              (Expr.let_ (qOp2 (.add i64) (Arg.var p_3.fst) (Arg.imm 1)) fun p_29 =>
               dWsOff pWvec pWsort p_29.fst fun _ ld_so =>
               Expr.group (sig := [[i64, i32]]) (fun _Js_3 => Blocks.cons
                 (fun (p_39 : Tup Val [i64, i32]) =>
                   Expr.jump Js.fst (Arg.var p_39.fst, Arg.var p_39.snd.fst, ())) Blocks.nil)
                 fun Js_in =>
               Expr.let_ (qOp2 (.cmp .ugt i32 .bool rfl) (Arg.var ld_so) (Arg.var ld_co))
                 fun p_37 =>
               Expr.jnz (Arg.var p_37.fst)
                 (Expr.let_ (qOp2 (.add i64) (Arg.var p_3.fst) (Arg.imm 1)) fun p_38 =>
                  Expr.jump Js_in.fst (Arg.var p_38.fst, Arg.var ld_so, ()))
                 (Expr.jump Js_in.fst (Arg.var p_3.fst, Arg.var ld_co, ())))
              (Expr.jump Js.fst (Arg.var p_3.fst, Arg.var ld_co, ()))))
      (Expr.jump Jbrk (Arg.var p.fst, ()))) Blocks.nil)
    fun Js => Expr.jump Js.fst (root0, ())

private theorem defrag_sift_wp {Γ : Env} {Q : Post []} {X : XPost} {c : PlainCfg}
    {s : PlainState} {R : Mem 64 → Prop} {wvec1 ws0 : List (BitVec 32)}
    {n lim : Val i64} {root0 : Arg Val i64} {lo : Nat} {Jbrk : Cont [i64]}
    {P : List (BitVec 32) → Prop} {m0 : Mem 64}
    (hmv : c.mv < 2 ^ 28) (hn_le : n.toNat ≤ 2 * c.mv) (hlim_le : lim.toNat ≤ n.toNat)
    (hlo_le : lo ≤ root0.val.toNat) (hrt0 : root0.val.toNat < lim.toNat)
    (hwv1 : wvec1.length = 4 * c.mv) (hws0 : ws0.length = 2 * c.mv)
    (hoff1 : ∀ j < 2 * c.mv, 0 < watchSize s j → wvec1[2 * j]? = s.wvec[2 * j]?)
    (hcov0 : WsCovers ws0 n.toNat (2 * c.mv) (watchSize s))
    (hmax0 : MaxHeapExcept (watchOff s) ws0 lo lim.toNat root0.val.toNat)
    (hpar0 : HoleParentOk (watchOff s) ws0 lo lim.toNat root0.val.toNat)
    (hP0 : P ws0)
    (hP_sw : ∀ ws i j, i < lim.toNat → j < lim.toNat →
      ∀ (hil : i < ws.length) (hjl : j < ws.length),
      P ws → P ((ws.set i (ws[j]'hjl)).set j (ws[i]'hil)))
    (hm0 : (PlainMem c { s with wvec := wvec1, heur := { s.heur with wsort := ws0 } } ⋆ R) m0)
    (hBrk : ∀ root ws m1, ws.length = 2 * c.mv → WsCovers ws n.toNat (2 * c.mv) (watchSize s) →
      MaxHeapExcept (watchOff s) ws lo lim.toNat lim.toNat → P ws →
      (PlainMem c { s with wvec := wvec1, heur := { s.heur with wsort := ws } } ⋆ R) m1 →
      Jbrk (root, ()) m1) :
    wp Γ Q X (defragSiftExpr c.pWvec c.pWsort lim Jbrk root0) m0 := by
  dsimp only [defragSiftExpr, dIdx4, dWsOff]
  refine wp_loop_inv
    (fun (root, ()) mS =>
      lo ≤ root.toNat ∧ root.toNat < lim.toNat ∧ ∃ wsS : List (BitVec 32),
        wsS.length = 2 * c.mv ∧ WsCovers wsS n.toNat (2 * c.mv) (watchSize s) ∧
        MaxHeapExcept (watchOff s) wsS lo lim.toNat root.toNat ∧
        HoleParentOk (watchOff s) wsS lo lim.toNat root.toNat ∧ P wsS ∧
        (PlainMem c { s with wvec := wvec1, heur := { s.heur with wsort := wsS } } ⋆ R) mS)
    (fun (root, ()) _ => lim.toNat - root.toNat)
    (fun JS hLoopS => ?_) ?_
  · c0_steps
    exact hLoopS (root0.val, ()) m0 ⟨hlo_le, hrt0, ws0, hws0, hcov0, hmax0, hpar0, hP0, hm0⟩
  · rintro JS ⟨root, ⟨⟩⟩ mS ⟨hloS, hrt_lt, wsS, hwsS, hcovS, hmaxS, hparS, hPS, hmS⟩ hLoopS
    clear hm0 ws0 hws0 hcov0 hmax0 hpar0 hP0 hlo_le hrt0
    obtain hch_eq : ((root <<< (1 : Nat)) + 1).toNat = 2 * root.toNat + 1 := by
      have hsh : (root <<< (1 : Nat)).toNat = 2 * root.toNat := by
        rw [BitVec.toNat_shiftLeft]; simp [Nat.shiftLeft_eq]; omega
      rw [BitVec.toNat_add, hsh]; simp; omega
    c0_step; c0_step
    · clear hc
      c0_split
      · obtain hge : lim.toNat ≤ 2 * root.toNat + 1 := by
          have : lim.toNat ≤ ((root <<< (1 : Nat)) + 1).toNat := by c0_bound
          omega
        c0_steps
        exact hBrk root wsS mS hwsS hcovS
          (maxHeap_sift_done hmaxS (fun h => by omega) (fun h => by omega)) hPS hmS
      · obtain hch_lt : 2 * root.toNat + 1 < lim.toNat := by
          have : ¬ (lim.toNat ≤ ((root <<< (1 : Nat)) + 1).toNat) := by c0_bound
          omega
        obtain ⟨hcl2, hcl2_b⟩ := ws_idx_shl1 (s := s) hmv hcovS (by omega) hch_eq (by omega)
        obtain hcl2_lt : ((wsS[((root <<< (1 : Nat)) + 1).toNat]'(by omega)).setWidth 64
            <<< (1 : Nat)).toNat < wvec1.length := by omega
        clear hc
        c0_to_group
        refine wp_join_group
          (fun (ch, co, ()) mJ =>
            (ch.toNat = 2 * root.toNat + 1 ∨ ch.toNat = 2 * root.toNat + 2) ∧
            ch.toNat < lim.toNat ∧ co.toNat = watchOff s (wsVal wsS ch.toNat) ∧
            (2 * root.toNat + 1 < lim.toNat →
              watchOff s (wsVal wsS (2 * root.toNat + 1)) ≤ co.toNat) ∧
            (2 * root.toNat + 2 < lim.toNat →
              watchOff s (wsVal wsS (2 * root.toNat + 2)) ≤ co.toNat) ∧ mS = mJ) ?_ ?_
        · rintro _ ⟨ch, co, ⟨⟩⟩ mJ ⟨hch_or, hch_lim, hco_eq, hsib1, hsib2, hmJ⟩
          rcases hmJ with rfl
          clear hcl2 hcl2_b hcl2_lt hch_lt hch_eq
          obtain ⟨hrl2, hrl2_b⟩ :=
            ws_idx_shl1 (s := s) (k := root.toNat) hmv hcovS (by omega) rfl (by omega)
          obtain hrl2_lt : ((wsS[root.toNat]'(by omega)).setWidth 64 <<< (1 : Nat)).toNat <
              wvec1.length := by omega
          obtain hrl_off := ws_idx_off hcovS hoff1 hrl2_lt (by omega) hrl2
          c0_steps
          · have hge : co.toNat ≤ watchOff s (wsVal wsS root.toNat) := by
              have : co.toNat ≤ (wvec1[((wsS[root.toNat]'(by omega)).setWidth 64
                  <<< (1 : Nat)).toNat]'hrl2_lt).toNat := by c0_bound
              omega
            exact hBrk root wsS mS hwsS hcovS
              (maxHeap_sift_done hmaxS (fun h => Nat.le_trans (hsib1 h) hge)
                (fun h => Nat.le_trans (hsib2 h) hge)) hPS hmS
          · have hlt : watchOff s (wsVal wsS root.toNat) < watchOff s (wsVal wsS ch.toNat) := by
              have : ¬ (co.toNat ≤ (wvec1[((wsS[root.toNat]'(by omega)).setWidth 64
                  <<< (1 : Nat)).toNat]'hrl2_lt).toNat) := by c0_bound
              omega
            have hstep := maxHeap_sift_step hloS hch_lim (by omega) hch_or hmaxS hparS hlt
              ⟨fun h => by rw [← hco_eq]; exact hsib1 h,
               fun h => by rw [← hco_eq]; exact hsib2 h⟩
            exact hLoopS _ _ (by dsimp only; omega)
              ⟨by omega, hch_lim, _, by rw [List.length_set, List.length_set, hwsS],
               wsCovers_swap hcovS (by omega) (by omega) (by omega),
               hstep.1, hstep.2, hP_sw wsS root.toNat ch.toNat hrt_lt hch_lim (by omega)
                 (by omega) hPS, hm⟩
        · intro Jc hJc
          clear hLoopS hBrk hP_sw hmaxS hparS hPS
          obtain hco1 := ws_idx_off hcovS hoff1 hcl2_lt (by omega) hcl2
          c0_split
          · obtain hsp_eq : (((root <<< (1 : Nat)) + 1) + 1).toNat = 2 * root.toNat + 2 := by
              rw [BitVec.toNat_add, hch_eq]; simp; omega
            obtain hsp_lt : 2 * root.toNat + 2 < lim.toNat := by
              have : (((root <<< (1 : Nat)) + 1) + 1).toNat < lim.toNat := by c0_bound
              omega
            obtain ⟨hsl2, hsl2_b⟩ := ws_idx_shl1 (s := s) hmv hcovS (by omega) hsp_eq (by omega)
            obtain hsl2_lt : ((wsS[(((root <<< (1 : Nat)) + 1) + 1).toNat]'(by omega)).setWidth 64
                <<< (1 : Nat)).toNat < wvec1.length := by omega
            obtain hso := ws_idx_off hcovS hoff1 hsl2_lt (by omega) hsl2
            clear hc
            c0_steps
            · refine hJc _ _ ⟨Or.inr hsp_eq, by omega,
                hso.trans (congrArg (fun k => watchOff s (wsVal wsS k)) hsp_eq.symm),
                fun _ => by
                  have : (wvec1[((wsS[((root <<< (1 : Nat)) + 1).toNat]'(by omega)).setWidth 64
                      <<< (1 : Nat)).toNat]'hcl2_lt).toNat <
                    (wvec1[((wsS[(((root <<< (1 : Nat)) + 1) + 1).toNat]'(by omega)).setWidth 64
                      <<< (1 : Nat)).toNat]'hsl2_lt).toNat := by c0_bound
                  omega,
                fun _ => by omega, rfl⟩
            · refine hJc _ _ ⟨Or.inl hch_eq, by omega,
                hco1.trans (congrArg (fun k => watchOff s (wsVal wsS k)) hch_eq.symm),
                fun _ => by omega,
                fun _ => by
                  have : ¬ ((wvec1[((wsS[((root <<< (1 : Nat)) + 1).toNat]'(by omega)).setWidth 64
                      <<< (1 : Nat)).toNat]'hcl2_lt).toNat <
                    (wvec1[((wsS[(((root <<< (1 : Nat)) + 1) + 1).toNat]'(by omega)).setWidth 64
                      <<< (1 : Nat)).toNat]'hsl2_lt).toNat) := by c0_bound
                  omega, rfl⟩
          · obtain hsp_ge : lim.toNat ≤ 2 * root.toNat + 2 := by
              have h1 : ¬ ((((root <<< (1 : Nat)) + 1) + 1).toNat < lim.toNat) := by c0_bound
              have h2 : (((root <<< (1 : Nat)) + 1) + 1).toNat = 2 * root.toNat + 2 := by
                rw [BitVec.toNat_add, hch_eq]; simp; omega
              omega
            c0_steps
            exact hJc _ _ ⟨Or.inl hch_eq, by omega,
              hco1.trans (congrArg (fun k => watchOff s (wsVal wsS k)) hch_eq.symm),
              fun _ => by omega, fun h => by omega, rfl⟩
    · cases hc

theorem plain_wstack_defrag_wp (Γ : Env) :
    ∀ a m Q X, plainWstackDefragSpec a m Q X → Func.wp Γ plain_wstack_defrag_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hlay, hm, hQ⟩
  obtain hmv : c.mv < 2 ^ 28 := c.hmv
  obtain hwcap : c.wcap < 2 * 2 ^ 28 := c.hwcap
  obtain hwle := hlen.wlen_le
  obtain hwvl := hlen.wvec_len
  obtain hwsl := hlen.wstk_len_arr
  obtain hok := hlen.heur_ok
  obtain hwsrt_l := hok.wsort_len
  c0_to_group
  · -- `wlen <= 1`: zero `wusable` and return
    refine hQ s.wvec s.wstk s.wlen s.heur.wsort _
      { hlen with wlen_le := hwle } (hlay.with_wstk rfl rfl rfl) id
      (fun _ _ => ⟨rfl, fun _ _ => rfl⟩) hm
  · -- `wlen > 1`
    obtain hwlen_gt1 : 1 < s.wlen := by c0_bound
    obtain hwsl_pos : 0 < s.wstk.length := by omega
    obtain hnlits : (BitVec.ofNat 64 c.mv <<< (1 : Nat)).toNat = 2 * c.mv := by
      rw [BitVec.toNat_shiftLeft, bv64_ofNat_toNat (by omega)]
      simp [Nat.shiftLeft_eq]; omega
    clear hc
    -- Loop 1: collect non-empty watch lists into `ws[0 ..< n]`
    refine wp_loop_inv
      (fun (n, l, ()) m1 =>
        l.toNat ≤ 2 * c.mv ∧ n.toNat ≤ l.toNat ∧
        ∃ (wvec1 wsort1 : List (BitVec 32)),
          wvec1.length = 4 * c.mv ∧ wsort1.length = 2 * c.mv ∧
          (∀ j < 2 * c.mv, wvec1[2 * j + 1]? = s.wvec[2 * j + 1]?) ∧
          (∀ j < 2 * c.mv, 0 < watchSize s j → wvec1[2 * j]? = s.wvec[2 * j]?) ∧
          (∀ j < l.toNat, watchSize s j = 0 → wvec1[2 * j]? = some 0#32) ∧
          WsCovers wsort1 n.toNat l.toNat (watchSize s) ∧
          (PlainMem c { s with wvec := wvec1, heur := { s.heur with wsort := wsort1 } } ⋆ R) m1)
      (fun (_, l, ()) _ => 2 * c.mv - l.toNat)
      (fun J hLoop => ?_) ?_
    · c0_steps
      refine hLoop _ _ ⟨by simp, by simp, s.wvec, s.heur.wsort, hwvl, hwsrt_l,
        fun _ _ => rfl, fun _ _ _ => rfl, fun _ hj => by simp at hj,
        ⟨fun _ hi => by simp at hi, fun _ hi => by simp at hi, fun _ hl => by simp at hl⟩, hm⟩
    · rintro J ⟨n, l, ⟨⟩⟩ m1 ⟨hl_le, hn_le, wvec1, wsort1, hwv1, hws1,
        hsz1, hoff1, hzero1, hcov1, hm1⟩ hLoop
      clear hm
      c0_to_group
      · -- Loop 1 body (`l < 2 * c.mv`)
        obtain hl_lt : l.toNat < 2 * c.mv := by
          have : l.toNat < (BitVec.ofNat 64 c.mv <<< (1 : Nat)).toNat := by c0_bound
          omega
        obtain hl2 : (l <<< (1 : Nat)).toNat = 2 * l.toNat := by
          rw [BitVec.toNat_shiftLeft]; simp [Nat.shiftLeft_eq]; omega
        obtain hl2p1 : ((l <<< (1 : Nat)) + 1).toNat = 2 * l.toNat + 1 := by
          rw [BitVec.toNat_add, hl2]; simp; omega
        obtain hl2_lt : (l <<< (1 : Nat)).toNat < wvec1.length := by omega
        obtain hl2p1_lt : ((l <<< (1 : Nat)) + 1).toNat < wvec1.length := by omega
        obtain hsz_eq : (wvec1[((l <<< (1 : Nat)) + 1).toNat]'hl2p1_lt).toNat =
            watchSize s l.toNat := by
          unfold watchSize
          have h1 := hsz1 l.toNat hl_lt
          rw [← h1]
          have h2 : wvec1[((l <<< (1 : Nat)) + 1).toNat]'hl2p1_lt =
              wvec1[2 * l.toNat + 1]'(by omega) := by
            congr 1
          rw [h2, List.getElem?_eq_getElem (by omega), Option.getD_some]
        c0_steps
        · have hsz0 : watchSize s l.toNat = 0 := by
            have hget : wvec1[(l <<< (1 : Nat) + 1).toNat]'hl2p1_lt =
                wvec1[((l <<< (1 : Nat)).toNat + (1 : Val i64).toNat) % 2 ^ 64]'(by
                  rw [← BitVec.toNat_add]; exact hl2p1_lt) := by congr 1
            rw [← hsz_eq, hget, hc]; rfl
          have hset := wvec_set_even_eq (wvec := wvec1) (l := l.toNat) (v := 0#32) (by omega)
          have hlp1 : (l + 1).toNat = l.toNat + 1 := by bv_omega
          refine hLoop _ _ (by dsimp only; omega)
            ⟨by omega, by omega, _, wsort1, by rw [List.length_set, hwv1], hws1,
             fun j hj => by rw [hl2]; exact (hset j).1.trans (hsz1 j hj),
             fun j hj hp => by
               rw [hl2]; exact ((hset j).2.1 fun heq => by subst heq; omega).trans (hoff1 j hj hp),
             fun j hj hzj => by
               rw [hl2]; by_cases hjl : j = l.toNat
               · subst hjl; exact (hset l.toNat).2.2
               · exact ((hset j).2.1 hjl).trans (hzero1 j (by omega) hzj),
             ⟨fun i hi => ⟨by have := (hcov1.1 i hi).1; omega, (hcov1.1 i hi).2⟩, hcov1.2.1,
              fun j hj hzj => hcov1.2.2 j
                (if hjl : j = l.toNat then by subst hjl; omega else by omega) hzj⟩,
             hm⟩
        · have hszp : 0 < watchSize s l.toNat := by
            have hget : wvec1[(l <<< (1 : Nat) + 1).toNat]'hl2p1_lt =
                wvec1[((l <<< (1 : Nat)).toNat + (1 : Val i64).toNat) % 2 ^ 64]'(by
                  rw [← BitVec.toNat_add]; exact hl2p1_lt) := by congr 1
            rw [← hsz_eq, hget]
            exact Nat.pos_of_ne_zero fun h0 => hc (BitVec.eq_of_toNat_eq (by simpa using h0))
          have hlp1 : (l + 1).toNat = l.toNat + 1 := by bv_omega
          have hnp1 : (n + 1).toNat = n.toNat + 1 := by bv_omega
          have htr : (l.setWidth 32).toNat = l.toNat := by
            rw [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by omega)
          have hws_at : ∀ k, wsVal (wsort1.set n.toNat (l.setWidth 32)) k =
              if k = n.toNat then l.toNat else wsVal wsort1 k := fun k => by
            unfold wsVal; by_cases hk : k = n.toNat
            · subst hk; rw [List.getElem?_set_self (by omega), Option.getD_some, htr]; simp
            · rw [List.getElem?_set_ne (by omega)]; simp [hk]
          refine hLoop _ _ (by dsimp only; omega)
            ⟨by omega, by omega, wvec1, _, hwv1, by rw [List.length_set, hws1], hsz1, hoff1,
             fun j hj hzj => hzero1 j
               (if hjl : j = l.toNat then by subst hjl; omega else by omega) hzj,
             ⟨fun i hi => by
                rw [hws_at]; split
                · exact ⟨by omega, hszp⟩
                · have := hcov1.1 i (by omega); exact ⟨by omega, this.2⟩,
              fun a ha b hb hab => by
                rw [hws_at, hws_at]; split <;> split
                · omega
                · have := (hcov1.1 b (by omega)).1; omega
                · have := (hcov1.1 a (by omega)).1; omega
                · exact hcov1.2.1 a (by omega) b (by omega) hab,
              fun j hj hzj => by
                by_cases hjl : j = l.toNat
                · subst hjl; exact ⟨n.toNat, by omega, by rw [hws_at]; simp⟩
                · obtain ⟨i, hi, hij⟩ := hcov1.2.2 j (by omega) hzj
                  exact ⟨i, by omega, by rw [hws_at]; simp [show i ≠ n.toNat by omega]; exact hij⟩⟩,
             hm⟩
      · -- Loop 1 exit (`l == 2 * c.mv`) & `n == 0`: reset `wstk[0] = 0; wlen = 1; wusable = 0`
        obtain hl_eq : l.toNat = 2 * c.mv := by
          have : ¬ (l.toNat < (BitVec.ofNat 64 c.mv <<< (1 : Nat)).toNat) := by c0_bound
          omega
        rw [hl_eq] at hzero1 hcov1 hn_le
        have hn0 : n.toNat = 0 := by rw [hc]; rfl
        have hfin := defrag_finalize (c := c) (s := s) (wvecC := wvec1)
          (wstkC := s.wstk.set 0 0#32) (wsort2 := wsort1) (n := 0) (p := 1) hlay
          (by simpa [hn0] using hcov1) (by omega)
          (fun j hj => by have := hsz1 j hj; unfold watchSize; rw [this])
          (fun j hj hz => by rw [hzero1 j hj hz]; rfl)
          (fun _ h0 => by omega) (fun _ h0 => by omega)
        refine hQ wvec1 (s.wstk.set 0 0#32) 1 wsort1 _
          ({ hlen with
             wvec_len := hwv1,
             wstk_len_arr := by simp [hwsl],
             wlen_le := by dsimp only; omega,
             heur_ok := { hok with wsort_len := hws1 } })
          hfin.1 (fun _ => by omega) hfin.2 hm
      · -- Loop 1 exit (`l == 2 * c.mv`) & `n > 0`: heapsort if `n > 1`, then compact!
        obtain hl_eq : l.toNat = 2 * c.mv := by
          have : ¬ (l.toNat < (BitVec.ofNat 64 c.mv <<< (1 : Nat)).toNat) := by c0_bound
          omega
        rw [hl_eq] at hzero1 hcov1 hn_le
        obtain hn_pos : 0 < n.toNat :=
          Nat.pos_of_ne_zero fun h0 => hc (BitVec.eq_of_toNat_eq (by simpa using h0))
        rename_i hc_ge; clear hc_ge hc hLoop J l hl_le hl_eq
        -- Join after `if (n > 1)` heapsort block
        refine wp_join_group
            (fun _ m2 => ∃ wsort2 : List (BitVec 32), wsort2.length = 2 * c.mv ∧
              WsCovers wsort2 n.toNat (2 * c.mv) (watchSize s) ∧
              SortedRange (watchOff s) wsort2 0 n.toNat ∧
              (PlainMem c
                { s with wvec := wvec1, heur := { s.heur with wsort := wsort2 } } ⋆ R) m2) ?_ ?_
        · -- Compaction phase (`p = 1`, `i = 0 ..< n`)
          rintro _ _ m2 ⟨wsort2, hws2, hcov2, hsrt2, hm2⟩
          clear hm1 wsort1 hws1 hcov1
          c0_to_group
          refine wp_loop_inv
            (fun (p, i, ()) mC =>
              1 ≤ p.toNat ∧ p.toNat ≤ s.wlen ∧ i.toNat ≤ n.toNat ∧
              (i.toNat < n.toNat → p.toNat ≤ watchOff s (wsVal wsort2 i.toNat)) ∧
              ∃ (wvecC wstkC : List (BitVec 32)),
                wvecC.length = 4 * c.mv ∧ wstkC.length = c.wcap ∧
                (∀ j < 2 * c.mv, (wvecC[2 * j + 1]?.getD 0#32).toNat = watchSize s j) ∧
                (∀ j < 2 * c.mv, watchSize s j = 0 → (wvecC[2 * j]?.getD 0#32).toNat = 0) ∧
                (∀ j < i.toNat, let l := wsVal wsort2 j; let off := (wvecC[2 * l]?.getD 0#32).toNat;
                  1 ≤ off ∧ off + watchSize s l ≤ p.toNat ∧
                  ∀ k < watchSize s l, wstkC[off + k]? = s.wstk[watchOff s l + k]?) ∧
                (∀ a < i.toNat, ∀ b < i.toNat, a ≠ b →
                  let la := wsVal wsort2 a; let lb := wsVal wsort2 b;
                  (wvecC[2 * la]?.getD 0#32).toNat + watchSize s la ≤
                    (wvecC[2 * lb]?.getD 0#32).toNat ∨
                  (wvecC[2 * lb]?.getD 0#32).toNat + watchSize s lb ≤
                    (wvecC[2 * la]?.getD 0#32).toNat) ∧
                (∀ j, i.toNat ≤ j → j < n.toNat → let l := wsVal wsort2 j;
                  (wvecC[2 * l]?.getD 0#32).toNat = watchOff s l ∧
                  ∀ k < watchSize s l, wstkC[watchOff s l + k]? = s.wstk[watchOff s l + k]?) ∧
                (PlainMem c
                  { s with wvec := wvecC, wstk := wstkC,
                           heur := { s.heur with wsort := wsort2 } } ⋆ R) mC)
            (fun (_, i, ()) _ => n.toNat - i.toNat)
            (fun J hLoop => ?_) ?_
          · c0_steps
            refine hLoop _ _ ⟨by simp, by simp; omega, by simp, fun h0 => ?_,
              wvec1, s.wstk, hwv1, hwsl,
              fun j hj => by unfold watchSize; rw [hsz1 j hj],
              fun j hj hz => by rw [hzero1 j hj hz]; rfl,
              fun _ hj => by simp at hj, fun _ ha => by simp at ha,
              fun j _ hjn => ⟨by
                have := hcov2.1 j hjn; unfold watchOff; rw [hoff1 _ this.1 this.2],
                fun _ _ => rfl⟩,
              hm2⟩
            have := hcov2.1 0 (by simpa using h0)
            simpa using hlay.pos_off _ this.1 this.2
          · rintro J ⟨p, i, ⟨⟩⟩ mC ⟨hp1, hple, hile, hp_off, wvecC, wstkC,
              hwvC, hwsC, hszC, hzeroC, hdoneC, hdisjC, hremC, hmC⟩ hLoop
            clear hm2
            c0_split
            · -- Compaction loop body (`i < n`)
              obtain hi_lt : i.toNat < n.toNat := by c0_bound
              obtain hlit_info := hcov2.1 i.toNat hi_lt
              obtain hlit_eq : (wsort2[i.toNat]'(by omega)).toNat = wsVal wsort2 i.toNat := by
                unfold wsVal; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
              obtain hlit_mv : (wsort2[i.toNat]'(by omega)).toNat < 2 * c.mv := by
                rw [hlit_eq]; exact hlit_info.1
              obtain hlit2 : ((wsort2[i.toNat]'(by omega)).setWidth 64 <<< (1 : Nat)).toNat =
                  2 * wsVal wsort2 i.toNat := by
                rw [BitVec.toNat_shiftLeft, zext_toNat _ (by decide), hlit_eq]
                simp [Nat.shiftLeft_eq]; omega
              obtain hlit2p1 :
                  (((wsort2[i.toNat]'(by omega)).setWidth 64 <<< (1 : Nat)) + 1).toNat =
                  2 * wsVal wsort2 i.toNat + 1 := by
                rw [BitVec.toNat_add, hlit2]; simp; omega
              obtain hlit2_lt :
                  ((wsort2[i.toNat]'(by omega)).setWidth 64 <<< (1 : Nat)).toNat <
                  wvecC.length := by omega
              obtain hlit2p1_lt :
                  (((wsort2[i.toNat]'(by omega)).setWidth 64 <<< (1 : Nat)) + 1).toNat <
                  wvecC.length := by omega
              obtain hoff_i :
                  (wvecC[((wsort2[i.toNat]'(by omega)).setWidth 64 <<< (1 : Nat)).toNat]'
                    hlit2_lt).toNat = watchOff s (wsVal wsort2 i.toNat) := by
                rw [list_getElem_toNat_eq hlit2_lt hlit2]
                exact (hremC i.toNat (by omega) hi_lt).1
              obtain hsz_i :
                  (wvecC[(((wsort2[i.toNat]'(by omega)).setWidth 64 <<< (1 : Nat)) + 1).toNat]'
                    hlit2p1_lt).toNat = watchSize s (wsVal wsort2 i.toNat) := by
                rw [list_getElem_toNat_eq hlit2p1_lt hlit2p1]
                exact hszC (wsVal wsort2 i.toNat) hlit_info.1
              obtain hp_le_off : p.toNat ≤ watchOff s (wsVal wsort2 i.toNat) := hp_off hi_lt
              obtain hoff_sz_le :
                  watchOff s (wsVal wsort2 i.toNat) + watchSize s (wsVal wsort2 i.toNat) ≤
                  s.wlen := hlay.bounds _ hlit_info.1
              rename_i hci; clear hci
              c0_to_group
              -- Join after `if (off != p) { copy; wvec[2*lit] = p; }`
              refine wp_join_group
                (fun _ mD => ∃ (wvecD wstkD : List (BitVec 32)),
                  wvecD.length = 4 * c.mv ∧ wstkD.length = c.wcap ∧
                  (∀ j < 2 * c.mv, (wvecD[2 * j + 1]?.getD 0#32).toNat = watchSize s j) ∧
                  (∀ j < 2 * c.mv, watchSize s j = 0 → (wvecD[2 * j]?.getD 0#32).toNat = 0) ∧
                  (∀ j < i.toNat + 1, let l := wsVal wsort2 j;
                    let off := (wvecD[2 * l]?.getD 0#32).toNat;
                    1 ≤ off ∧ off + watchSize s l ≤ p.toNat + watchSize s (wsVal wsort2 i.toNat) ∧
                    ∀ k < watchSize s l, wstkD[off + k]? = s.wstk[watchOff s l + k]?) ∧
                  (∀ a < i.toNat + 1, ∀ b < i.toNat + 1, a ≠ b →
                    let la := wsVal wsort2 a; let lb := wsVal wsort2 b;
                    (wvecD[2 * la]?.getD 0#32).toNat + watchSize s la ≤
                      (wvecD[2 * lb]?.getD 0#32).toNat ∨
                    (wvecD[2 * lb]?.getD 0#32).toNat + watchSize s lb ≤
                      (wvecD[2 * la]?.getD 0#32).toNat) ∧
                  (∀ j, i.toNat + 1 ≤ j → j < n.toNat → let l := wsVal wsort2 j;
                    (wvecD[2 * l]?.getD 0#32).toNat = watchOff s l ∧
                    ∀ k < watchSize s l, wstkD[watchOff s l + k]? = s.wstk[watchOff s l + k]?) ∧
                  (PlainMem c
                    { s with wvec := wvecD, wstk := wstkD,
                             heur := { s.heur with wsort := wsort2 } } ⋆ R) mD) ?_ ?_
              · rintro _ _ mD ⟨wvecD, wstkD, hwvD, hwsD, hszD, hzeroD,
                  hdoneD, hdisjD, hremD, hmD⟩
                clear hmC hszC hzeroC hdoneC hdisjC hremC
                c0_steps
                have hp_next : (p + BitVec.setWidth 64
                    (wvecC[(((wsort2[i.toNat]'(by omega)).setWidth 64 <<< (1 : Nat)) + 1).toNat]'
                      hlit2p1_lt)).toNat = p.toNat + watchSize s (wsVal wsort2 i.toNat) := by
                  rw [BitVec.toNat_add, zext_toNat _ (by decide), hsz_i]; omega
                have hi_next : (i + 1).toNat = i.toNat + 1 := by bv_omega
                refine hLoop _ _ (by dsimp only; omega)
                  ⟨by omega, by omega, by omega, fun hlt => ?_,
                    wvecD, wstkD, hwvD, hwsD, hszD, hzeroD,
                    by rw [hi_next, hp_next]; exact hdoneD,
                    by rw [hi_next]; exact hdisjD,
                    by rw [hi_next]; exact hremD, hmD⟩
                rw [hp_next]
                have hgap := defrag_sorted_gap hlay hcov2 hsrt2 (i := i.toNat) (j := (i + 1).toNat)
                  (by omega) hlt
                omega
              · intro JD hJD
                clear hLoop hQ hlen hok hsz1 hoff1 hzero1 hwv1 hwsl hwvl hwsrt_l hwlen_gt1 hwsl_pos
                  hnlits
                c0_to_group
                · -- `off != p` (so `p < off`): copy loop + update `wvec[2*lit] = p`
                  obtain hp_lt_off : p.toNat < watchOff s (wsVal wsort2 i.toNat) := by
                    have hne : p.toNat ≠ watchOff s (wsVal wsort2 i.toNat) := fun heq =>
                      hc (BitVec.eq_of_toNat_eq (by
                        rw [zext_toNat _ (by decide), hoff_i]; exact heq.symm))
                    omega
                  clear hc
                  refine wp_loop_inv
                    (fun (k, ()) mK =>
                      k.toNat ≤ watchSize s (wsVal wsort2 i.toNat) ∧
                      ∃ wstkK : List (BitVec 32), wstkK.length = c.wcap ∧
                        (∀ idx < p.toNat, wstkK[idx]? = wstkC[idx]?) ∧
                        (∀ idx, p.toNat + watchSize s (wsVal wsort2 i.toNat) ≤ idx →
                          wstkK[idx]? = wstkC[idx]?) ∧
                        (∀ r < k.toNat, wstkK[p.toNat + r]? =
                          s.wstk[watchOff s (wsVal wsort2 i.toNat) + r]?) ∧
                        (∀ r, k.toNat ≤ r → r < watchSize s (wsVal wsort2 i.toNat) →
                          wstkK[watchOff s (wsVal wsort2 i.toNat) + r]? =
                          s.wstk[watchOff s (wsVal wsort2 i.toNat) + r]?) ∧
                        (PlainMem c
                          { s with wvec := wvecC, wstk := wstkK,
                                   heur := { s.heur with wsort := wsort2 } } ⋆ R) mK)
                    (fun (k, ()) _ => watchSize s (wsVal wsort2 i.toNat) - k.toNat)
                    (fun JK hLoopK => ?_) ?_
                  · c0_steps
                    exact hLoopK _ _ ⟨by simp, wstkC, hwsC, fun _ _ => rfl, fun _ _ => rfl,
                      fun _ hr => by simp at hr,
                      fun r _ hr => (hremC i.toNat (by omega) hi_lt).2 r hr, hmC⟩
                  · rintro JK ⟨k, ⟨⟩⟩ mK ⟨hk_le, wstkK, hwsK, hpreK, hpostK,
                      hcopK, hsrcK, hmK⟩ hLoopK
                    clear hmC
                    c0_steps
                    · -- copy step `k < sz`
                      have hsz_hc : (wvecC[((BitVec.setWidth 64 (wsort2[i.toNat]'(by omega)) <<<
                          (1 : Nat)).toNat + (1 : Val i64).toNat) % 2 ^ 64]'(by
                          rw [← BitVec.toNat_add]; exact hlit2p1_lt)).toNat =
                          watchSize s (wsVal wsort2 i.toNat) := by
                        rw [list_getElem_toNat_eq _ (by rw [← BitVec.toNat_add, hlit2p1])]
                        exact hszC (wsVal wsort2 i.toNat) hlit_info.1
                      have hk_lt : k.toNat < watchSize s (wsVal wsort2 i.toNat) := by
                        have : k.toNat < (wvecC[((BitVec.setWidth 64 (wsort2[i.toNat]'(by omega))
                            <<< (1 : Nat)).toNat + (1 : Val i64).toNat) % 2 ^ 64]'(by
                            rw [← BitVec.toNat_add]; exact hlit2p1_lt)).toNat := by c0_bound
                        omega
                      have hkp1 : (k + 1).toNat = k.toNat + 1 := by bv_omega
                      have hpk : (p + k).toNat = p.toNat + k.toNat := by bv_omega
                      have hok_eq : (BitVec.setWidth 64
                          (wvecC[((wsort2[i.toNat]'(by omega)).setWidth 64 <<< (1 : Nat)).toNat]'
                            hlit2_lt) + k).toNat =
                          watchOff s (wsVal wsort2 i.toNat) + k.toNat := by
                        rw [BitVec.toNat_add, zext_toNat _ (by decide), hoff_i]; omega
                      refine hLoopK _ _ (by dsimp only; omega)
                        ⟨by omega, _, by rw [List.length_set, hwsK], ?_, ?_, ?_, ?_, hm⟩
                      · intro idx hidx
                        rw [List.getElem?_set_ne (by omega)]; exact hpreK idx hidx
                      · intro idx hidx
                        rw [List.getElem?_set_ne (by omega)]; exact hpostK idx hidx
                      · intro r hr
                        by_cases hrk : r = k.toNat
                        · subst hrk
                          rw [hpk, List.getElem?_set_self (by omega),
                            ← List.getElem?_eq_getElem (by omega), hok_eq]
                          exact hsrcK k.toNat (by omega) hk_lt
                        · rw [List.getElem?_set_ne (by omega)]; exact hcopK r (by omega)
                      · intro r hr1 hr2
                        rw [List.getElem?_set_ne (by omega)]; exact hsrcK r (by omega) hr2
                    · -- copy loop done (`k == sz`): update `wvec[2*lit] = p`
                      have hsz_hc : (wvecC[((BitVec.setWidth 64 (wsort2[i.toNat]'(by omega)) <<<
                          (1 : Nat)).toNat + (1 : Val i64).toNat) % 2 ^ 64]'(by
                          rw [← BitVec.toNat_add]; exact hlit2p1_lt)).toNat =
                          watchSize s (wsVal wsort2 i.toNat) := by
                        rw [list_getElem_toNat_eq _ (by rw [← BitVec.toNat_add, hlit2p1])]
                        exact hszC (wsVal wsort2 i.toNat) hlit_info.1
                      have hk_eq : k.toNat = watchSize s (wsVal wsort2 i.toNat) := by
                        have : ¬ (k.toNat < (wvecC[((BitVec.setWidth 64 (wsort2[i.toNat]'(by omega))
                            <<< (1 : Nat)).toNat + (1 : Val i64).toNat) % 2 ^ 64]'(by
                            rw [← BitVec.toNat_add]; exact hlit2p1_lt)).toNat) := by c0_bound
                        omega
                      have hp32 : (p.setWidth 32).toNat = p.toNat := by
                        rw [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by omega)
                      have hset := wvec_set_even_eq (wvec := wvecC) (l := wsVal wsort2 i.toNat)
                        (v := p.setWidth 32) (by omega)
                      refine hJD _ _ ⟨_, wstkK, by rw [List.length_set, hwvC], hwsK,
                        ?_, ?_, ?_, ?_, ?_, hm⟩
                      · intro j hj; rw [hlit2, (hset j).1]; exact hszC j hj
                      · intro j hj hzj; rw [hlit2]
                        have hne : j ≠ wsVal wsort2 i.toNat := fun heq => by
                          subst heq; have := hlit_info.2; omega
                        rw [(hset j).2.1 hne]; exact hzeroC j hj hzj
                      · intro j hj; dsimp only
                        by_cases hji : j = i.toNat
                        · subst hji
                          rw [hlit2, (hset (wsVal wsort2 i.toNat)).2.2, Option.getD_some, hp32]
                          exact ⟨hp1, by omega, fun r hr => hcopK r (by omega)⟩
                        · have hne : wsVal wsort2 j ≠ wsVal wsort2 i.toNat :=
                            hcov2.2.1 j (by omega) i.toNat hi_lt hji
                          rw [hlit2, (hset _).2.1 hne]
                          have hd := hdoneC j (by omega)
                          refine ⟨hd.1, by omega, fun r hr => ?_⟩
                          rw [hpreK _ (by omega)]; exact hd.2.2 r hr
                      · intro a ha b hb hab; dsimp only
                        by_cases hai : a = i.toNat
                        · subst hai
                          have hne : wsVal wsort2 b ≠ wsVal wsort2 i.toNat :=
                            hcov2.2.1 b (by omega) i.toNat hi_lt (by omega)
                          rw [hlit2, (hset (wsVal wsort2 i.toNat)).2.2, (hset _).2.1 hne,
                            Option.getD_some, hp32]
                          exact Or.inr (hdoneC b (by omega)).2.1
                        · by_cases hbi : b = i.toNat
                          · subst hbi
                            have hne : wsVal wsort2 a ≠ wsVal wsort2 i.toNat :=
                              hcov2.2.1 a (by omega) i.toNat hi_lt (by omega)
                            rw [hlit2, (hset (wsVal wsort2 i.toNat)).2.2, (hset _).2.1 hne,
                              Option.getD_some, hp32]
                            exact Or.inl (hdoneC a (by omega)).2.1
                          · have hna := hcov2.2.1 a (by omega) i.toNat hi_lt hai
                            have hnb := hcov2.2.1 b (by omega) i.toNat hi_lt hbi
                            rw [hlit2, (hset _).2.1 hna, (hset _).2.1 hnb]
                            exact hdisjC a (by omega) b (by omega) hab
                      · intro j hj1 hj2; dsimp only
                        have hne : wsVal wsort2 j ≠ wsVal wsort2 i.toNat :=
                          hcov2.2.1 j hj2 i.toNat hi_lt (by omega)
                        rw [hlit2, (hset _).2.1 hne]
                        have hgap := defrag_sorted_gap hlay hcov2 hsrt2 (i := i.toNat) (j := j)
                          (by omega) hj2
                        have hr := hremC j (by omega) hj2
                        refine ⟨hr.1, fun r hr' => ?_⟩
                        rw [hpostK _ (by omega)]; exact hr.2 r hr'
                · -- `off == p`: already in place!
                  have hoff_eq_p : watchOff s (wsVal wsort2 i.toNat) = p.toNat := by
                    have := congrArg BitVec.toNat hc
                    rw [zext_toNat _ (by decide), hoff_i] at this; exact this
                  refine hJD _ _ ⟨wvecC, wstkC, hwvC, hwsC, hszC, hzeroC, ?_, ?_, ?_, hmC⟩
                  · intro j hj; dsimp only
                    by_cases hji : j = i.toNat
                    · subst hji
                      have hr := hremC i.toNat (by omega) hi_lt
                      rw [hr.1, hoff_eq_p]
                      refine ⟨hp1, by omega, fun r hr' => ?_⟩
                      rw [← hoff_eq_p]; exact hr.2 r hr'
                    · have hd := hdoneC j (by omega)
                      exact ⟨hd.1, by omega, hd.2.2⟩
                  · intro a ha b hb hab; dsimp only
                    by_cases hai : a = i.toNat
                    · subst hai
                      rw [(hremC i.toNat (by omega) hi_lt).1, hoff_eq_p]
                      exact Or.inr (hdoneC b (by omega)).2.1
                    · by_cases hbi : b = i.toNat
                      · subst hbi
                        rw [(hremC i.toNat (by omega) hi_lt).1, hoff_eq_p]
                        exact Or.inl (hdoneC a (by omega)).2.1
                      · exact hdisjC a (by omega) b (by omega) hab
                  · intro j hj1 hj2; exact hremC j (by omega) hj2
            · -- Compaction loop exit (`i == n`): store `wlen = p; wusable = 0`
              obtain hi_eq : i.toNat = n.toNat := by
                have : ¬ (i.toNat < n.toNat) := by c0_bound
                omega
              c0_steps
              rw [hi_eq] at hdoneC hdisjC
              have hfin := defrag_finalize hlay hcov2 hp1 hszC hzeroC hdoneC hdisjC
              refine hQ wvecC wstkC p.toNat wsort2 _
                ({ hlen with
                   wvec_len := hwvC,
                   wstk_len_arr := hwsC,
                   wlen_le := by dsimp only; omega,
                   heur_ok := { hok with wsort_len := hws2 } })
                hfin.1 (fun _ => hp1) hfin.2 hm
        · -- `if (n > 1)` heapsort block (both branches jump to `J_sort`)
          intro JS hJS
          clear hQ hlen hlay hok hsz1 hzero1 hwsl hwvl hwle hwcap hwsrt_l hwlen_gt1 hwsl_pos hnlits
          c0_to_group
          · -- `n > 1`: Build-heap + Extract-max
            obtain hn_gt1 : 1 < n.toNat := by c0_bound
            clear hc
            -- Phase 3a: Build-heap (`start` from `n >>> 1` down to `0`)
            refine wp_loop_inv
              (fun (st, ()) mB => st.toNat ≤ n.toNat ∧ ∃ wsB : List (BitVec 32),
                wsB.length = 2 * c.mv ∧ WsCovers wsB n.toNat (2 * c.mv) (watchSize s) ∧
                MaxHeapExcept (watchOff s) wsB st.toNat n.toNat n.toNat ∧
                (PlainMem c
                  { s with wvec := wvec1, heur := { s.heur with wsort := wsB } } ⋆ R) mB)
              (fun (st, ()) _ => st.toNat)
              (fun JB hLoopB => ?_) ?_
            · c0_steps
              have hshr : (n >>> (1 : Nat)).toNat = n.toNat / 2 := by
                rw [BitVec.toNat_ushiftRight]; simp [Nat.shiftRight_eq_div_pow]
              refine hLoopB _ _ ⟨by omega, wsort1, hws1, hcov1, fun p hp _ =>
                ⟨fun h1 => by omega, fun h2 => by omega⟩, hm1⟩
            · rintro JB ⟨st, ⟨⟩⟩ mB ⟨hst_le, wsB, hwsB, hcovB, hmaxB, hmB⟩ hLoopB
              clear hm1
              c0_to_group
              · -- Build-heap body (`st > 0`): sift down `root = st - 1`
                obtain hst_pos : 0 < st.toNat := by c0_bound
                obtain hstm1 : (st - 1).toNat = st.toNat - 1 := by bv_omega
                clear hc
                c0_step
                exact defrag_sift_wp (lo := st.toNat - 1) (root0 := Arg.var (st - 1))
                  (P := fun _ => True) hmv hn_le (Nat.le_refl _)
                  (by dsimp only [Arg.val]; omega) (by dsimp only [Arg.val]; omega)
                  hwv1 hwsB hoff1 hcovB
                  (fun p hp hne => if hpn : p < n.toNat then
                      hmaxB p (by dsimp only [Arg.val] at hne; omega) (by omega)
                    else ⟨fun h => by omega, fun h => by omega⟩)
                  (fun hpos hp => by dsimp only [Arg.val] at hpos hp; rw [hstm1] at hpos hp; omega)
                  trivial
                  (fun _ _ _ _ _ _ _ _ => trivial) hmB
                  (fun root ws m1 hws hcov hmax _ hm1 => hJ (root, ()) m1 (by
                    c0_steps
                    refine hLoopB _ _ (by dsimp only; omega) ⟨by omega, ws, hws, hcov, ?_, hm1⟩
                    rw [hstm1]; exact hmax))
              · -- Build-heap done (`st == 0`): Phase 3b Extract-max (`end` from `n - 1` to `0`)
                have hst0 : st.toNat = 0 := by
                  have : ¬ (0 < st.toNat) := by c0_bound
                  omega
                rw [hst0] at hmaxB
                clear hc hLoopB JB st hst_le hst0 wsort1 hws1 hcov1
                refine wp_loop_inv
                  (fun (e, ()) mE => e.toNat < n.toNat ∧ ∃ wsE : List (BitVec 32),
                    wsE.length = 2 * c.mv ∧ WsCovers wsE n.toNat (2 * c.mv) (watchSize s) ∧
                    MaxHeapExcept (watchOff s) wsE 0 (e.toNat + 1) (e.toNat + 1) ∧
                    SplitLe (watchOff s) wsE (e.toNat + 1) n.toNat ∧
                    SortedRange (watchOff s) wsE (e.toNat + 1) n.toNat ∧
                    (PlainMem c
                      { s with wvec := wvec1, heur := { s.heur with wsort := wsE } } ⋆ R) mE)
                  (fun (e, ()) _ => e.toNat)
                  (fun JE hLoopE => ?_) ?_
                · c0_steps
                  have hnm1 : (n - 1).toNat = n.toNat - 1 := by bv_omega
                  have hnm1p1 : (n - 1).toNat + 1 = n.toNat := by omega
                  refine hLoopE _ _ ⟨by omega, wsB, hwsB, hcovB,
                    by rw [hnm1p1]; exact hmaxB,
                    fun _ _ _ h1 h2 => by omega, fun _ _ h1 _ h2 => by omega, hmB⟩
                · rintro JE ⟨e, ⟨⟩⟩ mE ⟨he_lt, wsE, hwsE, hcovE, hmaxE, hspE, hsrtE, hmE⟩ hLoopE
                  clear hmB wsB hwsB hcovB hmaxB
                  c0_to_group
                  · -- Extract-max body (`e > 0`): swap `ws[0]` and `ws[e]`, sift `0` in `[0, e)`
                    obtain he_pos : 0 < e.toNat := by c0_bound
                    obtain hem1 : (e - 1).toNat = e.toNat - 1 := by bv_omega
                    obtain h0_lt : 0 < wsE.length := by omega
                    rename_i hc_e
                    c0_step
                    have hsw_ex := extract_swap_step hmaxE hspE hsrtE he_pos he_lt (by omega)
                    have hsw_cov := wsCovers_swap hcovE (i := 0) (j := e.toNat) (by omega)
                      he_lt (by omega)
                    exact defrag_sift_wp (lo := 0) (root0 := Arg.imm 0)
                      (P := fun ws => ws.length = 2 * c.mv ∧
                        SplitLe (watchOff s) ws e.toNat n.toNat ∧
                        SortedRange (watchOff s) ws e.toNat n.toNat)
                      hmv hn_le (by omega) (Nat.zero_le _)
                      (by dsimp only [Arg.val]; simpa using he_pos)
                      hwv1 (by rw [List.length_set, List.length_set, hwsE]) hoff1 hsw_cov
                      hsw_ex.1 hsw_ex.2.1
                      ⟨by rw [List.length_set, List.length_set, hwsE],
                        hsw_ex.2.2.1, hsw_ex.2.2.2⟩
                      (fun ws i j hi hj hil hjl hP =>
                        ⟨by rw [List.length_set, List.length_set, hP.1],
                         split_sorted_swap_lt hP.2.1 hP.2.2 hi hj (by omega) (by omega)⟩)
                      hm
                      (fun root ws m1 hws hcov hmax hP hm1 => hJ (root, ()) m1 (by
                        c0_steps
                        have hep : (e - 1).toNat + 1 = e.toNat := by omega
                        refine hLoopE _ _ (by dsimp only; omega)
                          ⟨by omega, ws, hws, hcov, by rw [hep]; exact hmax,
                           by rw [hep]; exact hP.2.1, by rw [hep]; exact hP.2.2, hm1⟩))
                  · -- Extract-max done (`e == 0`) -> jump `hJS`!
                    have he0 : e.toNat = 0 := by
                      have : ¬ (0 < e.toNat) := by c0_bound
                      omega
                    rw [he0] at hspE hsrtE
                    refine hJS _ _ ⟨wsE, hwsE, hcovE, fun i j _ hij hj => ?_, hmE⟩
                    rcases Nat.eq_zero_or_pos i with rfl | hip
                    · rcases Nat.eq_zero_or_pos j with rfl | hjp
                      · exact Nat.le_refl _
                      · exact hspE 0 (by omega) j (by omega) hj
                    · exact hsrtE i j (by omega) hij hj
          · -- `n <= 1`: trivially sorted!
            have hn1 : n.toNat ≤ 1 := by c0_bound
            refine hJS _ _ ⟨wsort1, hws1, hcov1, fun i j _ hij hj => ?_, hm1⟩
            have heq : i = j := by omega
            subst heq; exact Nat.le_refl _

end LeanQbe.T.Examples.Kissat.Plain
