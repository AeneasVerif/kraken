/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Kitten.State
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts3

/-!
# Shared Sweep State Predicates & Pure Helpers (`Kissat.Proof.Sweep.State`)

Defines the sweep-specific semantic and structural predicates used by `Proof.Sweep.Spec` and
`Proof.Sweep.Wp*`:
- `ConeModelSet`, `M6SweepConeOk`
- `M6PhtOk`, `M6PartitionOk`
- `M6TmkZero`, `M6EqBufOk`
- `k6PutHdr25` (`k[25]` PRNG word update) plus pure `K6Inv`/`K6TailEq`/`K6HwmClean` lemmas.

Zero legacy `Full*` imports; zero `@[expose]` on theorems, lemmas, or sections.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Sweep

open Std Std.Sat Kraken.Bedrock2.Test
open LeanQbe.T
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Kitten

/-! ## 1. Sweep Cone, PHT, Marking, & Equivalence-Buffer Predicates -/

/-- Cone projection of global models of `F_cur` onto local variables `0 ..< nv` via `work_stk1`.
-/
@[expose] def ConeModelSet (F_cur : List (List Nat)) (cone_v : List (BitVec 32)) (nv : Nat)
    (β : Nat → Bool) : Prop :=
  ∃ α, (cnfOfClauses F_cur).Sat α ∧ ∀ i < nv, β i = α (cone_v[i]?.getD 0#32).toNat

/-- Probing Hash Table (PHT) linked-bucket structural invariant over `scratch_buf`. -/
@[expose] def M6PhtOk (nv : Nat) (scr : List (BitVec 32)) : Prop :=
  (∀ b < k6PhtSz,
    let h := scr[k6PhtHead + b]?.getD 0xFFFFFFFF#32
    h = 0xFFFFFFFF#32 ∨ h.toNat < nv) ∧
  (∀ i < nv,
    let nx := scr[k6PhtNext + i]?.getD 0xFFFFFFFF#32
    nx = 0xFFFFFFFF#32 ∨ nx.toNat < i)

/-- Equivalence-class candidate partition invariant over `pht_next` and `shrink_stk` (`heads`). -/
@[expose] def M6PartitionOk (nv ncls : Nat) (scr heads : List (BitVec 32)) : Prop :=
  ncls ≤ heads.length ∧
  (∀ i < nv,
    let nx := scr[k6PhtNext + i]?.getD 0xFFFFFFFF#32
    nx = 0xFFFFFFFF#32 ∨ nx.toNat < i) ∧
  (∀ ci < ncls, (heads[ci]?.getD 0xFFFFFFFF#32).toNat < nv)

/-- `tarjan_mark` cleared to `0` across all active variables `[0 ..< cur_vars)`. -/
@[expose] def M6TmkZero (s : FullState) : Prop :=
  ∀ v < s.core.cur_vars, s.scratch.tarjan_mark[v]?.getD 0#32 = 0#32

/-- Semantic invariant for the extracted local Kitten sub-problem on `nv` variables. -/
@[expose] def M6SweepConeOk (F_cur : List (List Nat)) (s : FullState) (nv : Nat) : Prop :=
  1 ≤ nv ∧ nv ≤ k6MaxV s.scratch.scratch_buf.length ∧ nv ≤ s.core.cur_vars ∧
  (∀ i < nv, (s.scratch.work_stk1[i]?.getD 0#32).toNat < s.core.cur_vars) ∧
  K6ScratchInv (ConeModelSet F_cur s.scratch.work_stk1 nv) s.scratch.scratch_buf ∧
  ∃ hge hlt,
    (k6StateOfScratch (k6LayoutOfCap s.scratch.scratch_buf.length hge hlt)
      s.scratch.scratch_buf).nv = BitVec.ofNat 32 nv

/-- Proven literal-equivalence pairs in `work_stk2[0 ..< 2 * neq)`. -/
@[expose] def M6EqBufOk (F_cur : List (List Nat)) (s : FullState) (neq : Nat) : Prop :=
  neq ≤ s.core.cur_vars ∧
  ∀ i < neq,
    let la := (s.scratch.work_stk2[2 * i]?.getD 0#32).toNat
    let lc := (s.scratch.work_stk2[2 * i + 1]?.getD 0#32).toNat
    la < 2 * s.core.cur_vars ∧ lc < 2 * s.core.cur_vars ∧
    LitEquiv (cnfOfClauses F_cur) la lc

/-- Isolated xorshift32 PRNG word `k[25]` (`hdrTail[0]`) inside `K6State`. -/
@[expose] def k6PutHdr25 (ks : K6State) (v : BitVec 32) : K6State :=
  { ks with hdrTail := ks.hdrTail.set 0 v }

/-! ## 2. Pure Bridge & Preservation Lemmas -/

theorem m6_coneModelSet_unsat_of_empty {F_cur : List (List Nat)} {cone_v : List (BitVec 32)}
    {nv : Nat} (h : ∀ β, ¬ ConeModelSet F_cur cone_v nv β) : (cnfOfClauses F_cur).Unsat := by
  intro α
  exact Bool.eq_false_iff.mpr fun hsat =>
    h (fun i => α (cone_v[i]?.getD 0#32).toNat) ⟨α, hsat, fun _ _ => rfl⟩

theorem m6SweepConeOk_to_k6Inv {F_cur : List (List Nat)} {s : FullState} {nv : Nat}
    {L : K6Layout} (hLscr : L.scrLen = s.scratch.scratch_buf.length)
    (hLmv : L.maxV = k6MaxV s.scratch.scratch_buf.length)
    (hm6 : M6SweepConeOk F_cur s nv) :
    let ks := k6StateOfScratch L s.scratch.scratch_buf
    K6Inv L (ConeModelSet F_cur s.scratch.work_stk1 nv) ks ∧
      ks.nv = BitVec.ofNat 32 nv ∧ ks.nv.toNat = nv := by
  rcases hm6 with ⟨h1, hle_mv, hle_cv, hws, ⟨hge, hlt, hki⟩, hge2, hlt2, hnv⟩
  have hL : L = k6LayoutOfCap s.scratch.scratch_buf.length hge hlt :=
    K6Layout.eq_of_scrLen_maxV (by rw [hLscr, k6LayoutOfCap_scrLen]) (by rw [hLmv]; rfl)
  have hL2 : L = k6LayoutOfCap s.scratch.scratch_buf.length hge2 hlt2 :=
    K6Layout.eq_of_scrLen_maxV (by rw [hLscr, k6LayoutOfCap_scrLen]) (by rw [hLmv]; rfl)
  have hnv' : (k6StateOfScratch L s.scratch.scratch_buf).nv = BitVec.ofNat 32 nv := by
    rw [hL2]; exact hnv
  have hnv_lt : nv < 2 ^ 32 := by
    have := L.hmaxV.2; omega
  refine ⟨?_, hnv', by rw [hnv', BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnv_lt]⟩
  subst hL; exact hki

theorem m6TmkZero_congr {s s' : FullState} (h : M6TmkZero s)
    (hcv : s'.core.cur_vars = s.core.cur_vars)
    (htmk : s'.scratch.tarjan_mark = s.scratch.tarjan_mark) : M6TmkZero s' := fun v hv => by
  rw [htmk]; exact h v (hcv ▸ hv)

theorem m6EqBufOk_mono {F_cur : List (List Nat)} {s s' : FullState} {neq : Nat}
    (h : M6EqBufOk F_cur s neq) (hcv : s'.core.cur_vars = s.core.cur_vars)
    (hws2 : s'.scratch.work_stk2 = s.scratch.work_stk2) : M6EqBufOk F_cur s' neq := by
  refine ⟨hcv ▸ h.1, fun i hi => ?_⟩
  have hi' := h.2 i hi
  rw [hws2, hcv]; exact hi'

theorem k6PutHdr25_shapes {L : K6Layout} {ks : K6State} (h : ks.ShapesOk L) (v : BitVec 32) :
    (k6PutHdr25 ks v).ShapesOk L :=
  { h with hdrTail_len := by simp [k6PutHdr25, h.hdrTail_len] }

theorem k6PutHdr25_tailEq {L : K6Layout} {ks : K6State} (v : BitVec 32) :
    K6TailEq L ks (k6PutHdr25 ks v) :=
  ⟨rfl, fun _ _ _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

theorem k6HwmClean_putHdr25 {L : K6Layout} {hw : BitVec 32} {ks : K6State} (v : BitVec 32)
    (h : K6HwmClean L hw ks) : K6HwmClean L hw (k6PutHdr25 ks v) :=
  h

end LeanQbe.T.Examples.Kissat.Proof.Sweep
