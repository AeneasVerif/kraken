/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S4EVSIDSReorder
public import LeanQbe.T.Examples.Kissat.FullSpec
public import LeanQbe.T.Examples.Kissat.FullM6MinShrinkProof1
import LeanQbe.T.AbiLemmas
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Examples.Kissat.SolverArena
import LeanQbe.T.Logic.Bytes
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.Cells
import LeanQbe.T.Logic.ControlComb
import LeanQbe.T.Logic.MemLemmas
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Fidelity Step 13 S4-A Proofs — Part 0 (`FullFidelityStep13S4EVSIDSReorderProof0`)

UNSAT-only `Func.wp` proofs (`public section`, `0` `@[expose]` on theorems/lemmas, `0` `import all`,
`XPost`-polymorphic) for the first `4` S4-A functions:
1. `full_rescale_m6_step13_wp` (`Full.fullRescaleSpec`, `f64u_div` + `f64u_mul`).
2. `full_bump_var_step13_wp` (`Full.fullBumpVarSpec`, `f64u_add` + `full_heap_up` + `full_rescale`).
3. `full_bump_decay_step13_wp` (`Full.fullBumpDecaySpec`, `f64u_mul` + `full_rescale`).
4. `full_sort_ana_qs_m6_step13_wp` (`s13SortAnaQsSpec`, `PERF-R3` insertion + LSD radix +
   heapsort fallback).

Also exports shared `f64uPure1Spec` / `f64uPure2Spec` and `array32 <-> array64` aliasing helpers
reused by `FullFidelityStep13S4EVSIDSReorderProof2`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep13S4

open Std Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM6MinShrink
open Kraken.Bedrock2.Test

/-! ## 1. Shared Step-13 `f64u_*` Callee Specs & `s13SortAnaQsSpec` -/

/-- Shared frozen pure 1-arg `f64u_*` callee spec (`0` heap accesses). -/
def f64uPure1Spec : Spec [i64] [i64] := fun _ m Q _ =>
  ∀ r : BitVec 64, Q (r, ()) m

/-- Shared frozen pure 2-arg `f64u_*` callee spec (`0` heap accesses). -/
def f64uPure2Spec : Spec [i64, i64] [i64] := fun _ m Q _ =>
  ∀ r : BitVec 64, Q (r, ()) m

theorem f64uPure1Spec_monoX {xs : Tup Val [i64]} {m : Mem 64} {Q : Post [i64]} {X X' : XPost}
    (h : f64uPure1Spec xs m Q X) : f64uPure1Spec xs m Q X' := h

theorem f64uPure2Spec_monoX {xs : Tup Val [i64, i64]} {m : Mem 64} {Q : Post [i64]} {X X' : XPost}
    (h : f64uPure2Spec xs m Q X) : f64uPure2Spec xs m Q X' := h

theorem f64uPure1Spec_of {a : BitVec 64} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (hQ : ∀ r : BitVec 64, Q (r, ()) m) : f64uPure1Spec (a, ()) m Q X := hQ

theorem f64uPure2Spec_of {a b : BitVec 64} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (hQ : ∀ r : BitVec 64, Q (r, ()) m) : f64uPure2Spec (a, b, ()) m Q X := hQ

/-- Transparent Step-13 mirror of `m6AnaSiftSpec` (since `FullM6MinShrinkProof1.m6AnaSiftSpec`
lacks an exported `_of` introducer across `module` boundaries). -/
def s13AnaSiftSpec : Spec [i64, i64, i64, i64, i64] [] :=
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

theorem s13AnaSiftSpec_monoX {xs : Tup Val [i64, i64, i64, i64, i64]} {m : Mem 64}
    {Q : Post []} {X X' : XPost} (h : s13AnaSiftSpec xs m Q X) : s13AnaSiftSpec xs m Q X' := by
  rcases xs with ⟨_, _, _, _, _, ⟨⟩⟩; exact h

theorem s13AnaSiftSpec_of {qs_ptr ana_ptr cv start n : BitVec 64}
    {qs ana : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64} {Q : Post []} {X : XPost}
    (hcv_qs : cv.toNat ≤ qs.length) (hst_n : start.toNat ≤ n.toNat)
    (hn_ana : n.toNat ≤ ana.length) (hn62 : n.toNat < 2 ^ 62)
    (hcov : ∀ k < n.toNat, (ana[k]?.getD 0#32).toNat < cv.toNat)
    (hm : (array (t := i32) qs_ptr qs ⋆ array (t := i32) ana_ptr ana ⋆ R) m)
    (hQ : ∀ ana' m',
      ana'.length = ana.length → (ana'.take n.toNat).Perm (ana.take n.toNat) →
      (∀ k, n.toNat ≤ k → ana'[k]? = ana[k]?) →
      (∀ k < n.toNat, (ana'[k]?.getD 0#32).toNat < cv.toNat) →
      (array (t := i32) qs_ptr qs ⋆ array (t := i32) ana_ptr ana' ⋆ R) m' → Q () m') :
    s13AnaSiftSpec (qs_ptr, ana_ptr, cv, start, n, ()) m Q X :=
  ⟨qs, ana, R, hcv_qs, hst_n, hn_ana, hn62, hcov, hm, hQ⟩

theorem s13AnaSiftSpec_elim {qs_ptr ana_ptr cv start n : BitVec 64} {m : Mem 64}
    {Q : Post []} {X : XPost} (hs : s13AnaSiftSpec (qs_ptr, ana_ptr, cv, start, n, ()) m Q X) :
    ∃ (qs ana : List (BitVec 32)) (R : Mem 64 → Prop),
      cv.toNat ≤ qs.length ∧ start.toNat ≤ n.toNat ∧ n.toNat ≤ ana.length ∧
      n.toNat < 2 ^ 62 ∧
      (∀ k < n.toNat, (ana[k]?.getD 0#32).toNat < cv.toNat) ∧
      (array (t := i32) qs_ptr qs ⋆ array (t := i32) ana_ptr ana ⋆ R) m ∧
      ∀ ana' m',
        ana'.length = ana.length → (ana'.take n.toNat).Perm (ana.take n.toNat) →
        (∀ k, n.toNat ≤ k → ana'[k]? = ana[k]?) →
        (∀ k < n.toNat, (ana'[k]?.getD 0#32).toNat < cv.toNat) →
        (array (t := i32) qs_ptr qs ⋆ array (t := i32) ana_ptr ana' ⋆ R) m' → Q () m' :=
  hs

/-- Step-13 `PERF-R3` `full_sort_ana_qs_m6` spec (`work_stk1` permutation + valid vars `< cur_vars`,
allowing scratch writes into `s.core.repr`, `s.scratch.wsort`, `s.scratch.scratch_buf`). -/
def s13SortAnaQsSpec : Spec [i64, i64] [] := fun (h, n, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ n.toNat ≤ s.core.cur_vars ∧
    (∀ k < n.toNat, (s.scratch.work_stk1[k]?.getD 0#32).toNat < s.core.cur_vars) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ ws1' repr' wsort' sbuf' m',
      ws1'.length = 2 * c.max_vars →
      repr'.length = 2 * c.max_vars →
      wsort'.length = 2 * c.max_vars →
      sbuf'.length = c.scratch_cap →
      (ws1'.take n.toNat).Perm (s.scratch.work_stk1.take n.toNat) →
      (∀ k, n.toNat ≤ k → ws1'[k]? = s.scratch.work_stk1[k]?) →
      (∀ k < n.toNat, (ws1'[k]?.getD 0#32).toNat < s.core.cur_vars) →
      (FullMem c { core := { s.core with repr := repr' }
                   scratch := { s.scratch with
                     work_stk1 := ws1', wsort := wsort', scratch_buf := sbuf' } } ⋆ R) m' →
      Q () m'

theorem s13SortAnaQsSpec_monoX {xs : Tup Val [i64, i64]} {m : Mem 64} {Q : Post []} {X X' : XPost}
    (h : s13SortAnaQsSpec xs m Q X) : s13SortAnaQsSpec xs m Q X' := by
  rcases xs with ⟨_, _, ⟨⟩⟩; exact h

theorem s13SortAnaQsSpec_of {c : FullCfg} {s : FullState} {n : BitVec 64} {R : Mem 64 → Prop}
    {m : Mem 64} {Q : Post []} {X : XPost} (hlen : s.LengthsOk c)
    (hn : n.toNat ≤ s.core.cur_vars)
    (hlt : ∀ k < n.toNat, (s.scratch.work_stk1[k]?.getD 0#32).toNat < s.core.cur_vars)
    (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ ws1' repr' wsort' sbuf' m',
      ws1'.length = 2 * c.max_vars →
      repr'.length = 2 * c.max_vars →
      wsort'.length = 2 * c.max_vars →
      sbuf'.length = c.scratch_cap →
      (ws1'.take n.toNat).Perm (s.scratch.work_stk1.take n.toNat) →
      (∀ k, n.toNat ≤ k → ws1'[k]? = s.scratch.work_stk1[k]?) →
      (∀ k < n.toNat, (ws1'[k]?.getD 0#32).toNat < s.core.cur_vars) →
      (FullMem c { core := { s.core with repr := repr' }
                   scratch := { s.scratch with
                     work_stk1 := ws1', wsort := wsort', scratch_buf := sbuf' } } ⋆ R) m' →
      Q () m') :
    s13SortAnaQsSpec (c.hdr, n, ()) m Q X :=
  ⟨c, s, R, rfl, hlen, hn, hlt, hm, hQ⟩

theorem s13SortAnaQsSpec_elim {h n : BitVec 64} {m : Mem 64} {Q : Post []} {X : XPost}
    (hs : s13SortAnaQsSpec (h, n, ()) m Q X) :
    ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ n.toNat ≤ s.core.cur_vars ∧
      (∀ k < n.toNat, (s.scratch.work_stk1[k]?.getD 0#32).toNat < s.core.cur_vars) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ ws1' repr' wsort' sbuf' m',
        ws1'.length = 2 * c.max_vars → repr'.length = 2 * c.max_vars →
        wsort'.length = 2 * c.max_vars → sbuf'.length = c.scratch_cap →
        (ws1'.take n.toNat).Perm (s.scratch.work_stk1.take n.toNat) →
        (∀ k, n.toNat ≤ k → ws1'[k]? = s.scratch.work_stk1[k]?) →
        (∀ k < n.toNat, (ws1'[k]?.getD 0#32).toNat < s.core.cur_vars) →
        (FullMem c { core := { s.core with repr := repr' }
                     scratch := { s.scratch with
                       work_stk1 := ws1', wsort := wsort', scratch_buf := sbuf' } } ⋆ R) m' →
        Q () m' :=
  hs

/-! ## 2. Shared `array32 <-> array64` Aliasing Helpers -/

/-- Pack adjacent `u32` pairs into little-endian `u64` words. -/
def s13PackPairs64 : List (BitVec 32) → List (BitVec 64)
  | [] => []
  | lo :: hi :: rest => ((hi.setWidth 64 <<< 32) ||| lo.setWidth 64) :: s13PackPairs64 rest
  | [_] => []

/-- Unpack `u64` words back into little-endian `u32` pairs. -/
def s13UnpackPairs32 : List (BitVec 64) → List (BitVec 32)
  | [] => []
  | w :: rest => w.setWidth 32 :: (w >>> 32).setWidth 32 :: s13UnpackPairs32 rest

theorem s13PackPairs64_length : ∀ xs : List (BitVec 32),
    (s13PackPairs64 xs).length = xs.length / 2
  | [] => rfl
  | [_] => by simp [s13PackPairs64]
  | _ :: _ :: rest => by
    simp only [s13PackPairs64, List.length_cons, s13PackPairs64_length rest]; omega

theorem s13UnpackPairs32_length (ys : List (BitVec 64)) :
    (s13UnpackPairs32 ys).length = 2 * ys.length := by
  induction ys with
  | nil => rfl
  | cons _ _ ih => simp only [s13UnpackPairs32, List.length_cons, ih]; omega

private theorem s13_toBytes_8_split (w : BitVec 64) :
    Int.toBytes 8 (w.toNat : Int) =
      Int.toBytes 4 ((w.setWidth 32).toNat : Int) ++
        Int.toBytes 4 (((w >>> 32).setWidth 32).toNat : Int) := by
  have hw0 : ((w.setWidth 32).toNat : Int) = (w.toNat : Int) % (2 : Int) ^ (8 * 4) := by
    simp only [BitVec.toNat_setWidth]; omega
  have hw1 : (((w >>> 32).setWidth 32).toNat : Int) =
      ((w.toNat : Int) / (2 : Int) ^ 32) % (2 : Int) ^ (8 * 4) := by
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; omega
  rw [hw0, hw1, Int.toBytes_emod (n := 4) (x := (w.toNat : Int)),
    Int.toBytes_emod (n := 4) (x := (w.toNat : Int) / (2 : Int) ^ 32)]
  have hd : ∀ (k : Int), (((k / 256) / 256) / 256) / 256 = k / (2 : Int) ^ 32 := fun k => by omega
  simp only [Int.toBytes, Int.take, List.cons_append, List.nil_append, hd]

private theorem s13_cell_i32_eq_int4 (a : BitVec 64) (v : BitVec 32) :
    cell (t := i32) a v = int4 a (v.setWidth 64) := by
  unfold cell int4
  simp only [Ty.bytes, Ty.size, toBits, BitVec.setWidth_eq]
  congr 2
  rw [← Int.toBytes_emod, ← Int.toBytes_emod (x := ((v.setWidth 64).toNat : Int))]
  congr 1; dsimp only [Int.take]
  simp only [Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMul, BitVec.toInt_eq_msb_cond,
    BitVec.toNat_setWidth]
  have hlt : 0 ≤ (v.toNat : Int) ∧ (v.toNat : Int) < (2 ^ 32 : Int) :=
    ⟨Int.natCast_nonneg _, by exact_mod_cast v.isLt⟩
  have hlt64 : v.toNat < 2 ^ 64 := Nat.lt_trans v.isLt (by decide)
  rw [Nat.mod_eq_of_lt hlt64]
  cases v.msb
  · simp
  · simp only [↓reduceIte, Int.natCast_pow, Int.cast_ofNat_Int]; omega

private theorem s13_cell64_eq_cell_i32_pair (a w : BitVec 64) :
    cell64 a w =
      (cell (t := i32) a (w.setWidth 32) ⋆ cell (t := i32) (a + 4) ((w >>> 32).setWidth 32)) := by
  rw [cell64_eq_word8, word8_eq_int4_sep, s13_cell_i32_eq_int4, s13_cell_i32_eq_int4,
    int4_setWidth32, int4_setWidth32]
  have hdrop : (Int.toBytes 8 (w.toNat : Int)).drop 4 =
      Int.toBytes 4 ((w >>> 32).toNat : Int) := by
    have h1 : (((w >>> 32).setWidth 32).toNat : Int) =
        ((w >>> 32).toNat : Int) % (2 : Int) ^ (8 * 4) := by
      simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; omega
    rw [s13_toBytes_8_split, List.drop_left' (by simp [Int.toBytes_length]), h1, Int.toBytes_emod]
  unfold int4; rw [hdrop]

private theorem s13_pack_pair_word (lo hi : BitVec 32) :
    let w : BitVec 64 := (hi.setWidth 64 <<< 32) ||| lo.setWidth 64
    w.setWidth 32 = lo ∧ (w >>> 32).setWidth 32 = hi := by
  dsimp only; constructor
  · apply BitVec.eq_of_getElem_eq; intro k hk; simp
  · apply BitVec.eq_of_getElem_eq; intro k hk
    have hk64 : k < 64 := by omega
    have h32 : 32 + k < 64 := by omega
    have hnot : ¬(32 + k < 32) := by omega
    simp [BitVec.getElem_setWidth, BitVec.getElem_ushiftRight, BitVec.getElem_or,
      BitVec.getElem_shiftLeft, BitVec.getLsbD_eq_getElem, hk, hk64, h32, hnot]

theorem s13_array_i32_eq_array64_pack (a : BitVec 64) (xs : List (BitVec 32))
    (heven : xs.length % 2 = 0) :
    array (t := i32) a xs = array64 a (s13PackPairs64 xs) := by
  match xs with
  | [] => rfl
  | [_] => simp at heven
  | lo :: hi :: rest =>
    have hrest : rest.length % 2 = 0 := by simp at heven; omega
    have hlo : (((hi.setWidth 64 <<< 32) ||| lo.setWidth 64).setWidth 32) = lo :=
      (s13_pack_pair_word lo hi).1
    have hhi : ((((hi.setWidth 64 <<< 32) ||| lo.setWidth 64) >>> 32).setWidth 32) = hi :=
      (s13_pack_pair_word lo hi).2
    have hstep : a + BitVec.ofNat 64 (Ty.bytes i32) + BitVec.ofNat 64 (Ty.bytes i32) = a + 8 := by
      change a + 4#64 + 4#64 = a + 8#64; bv_omega
    have h4 : a + BitVec.ofNat 64 (Ty.bytes i32) = a + 4 := by
      change a + 4#64 = a + 4; rfl
    rw [array_cons, array_cons, s13PackPairs64, array64_cons,
      s13_cell64_eq_cell_i32_pair, hlo, hhi, ← h4, hstep,
      s13_array_i32_eq_array64_pack (a + 8) rest hrest, sep_assoc]

theorem s13_array64_eq_array_i32_unpack (a : BitVec 64) (ys : List (BitVec 64)) :
    array64 a ys = array (t := i32) a (s13UnpackPairs32 ys) := by
  induction ys generalizing a with
  | nil => rfl
  | cons w rest ih =>
    have hstep : a + BitVec.ofNat 64 (Ty.bytes i32) + BitVec.ofNat 64 (Ty.bytes i32) = a + 8 := by
      change a + 4#64 + 4#64 = a + 8#64; bv_omega
    have h4 : a + BitVec.ofNat 64 (Ty.bytes i32) = a + 4 := by
      change a + 4#64 = a + 4; rfl
    rw [array64_cons, s13_cell64_eq_cell_i32_pair, s13UnpackPairs32, array_cons, array_cons,
      ← h4, hstep, ih (a + 8), sep_assoc]

theorem s13_array_i32_append (a : BitVec 64) (xs ys : List (BitVec 32)) :
    array (t := i32) a (xs ++ ys) =
      (array (t := i32) a xs ⋆ array (t := i32) (a + BitVec.ofNat 64 (4 * xs.length)) ys) := by
  induction xs generalizing a with
  | nil =>
    simp only [List.nil_append, List.length_nil, Nat.mul_zero, BitVec.add_zero]
    rw [array_nil, emp_sep]
  | cons x rest ih =>
    have h4 : BitVec.ofNat 64 (Ty.bytes i32) = 4#64 := rfl
    have hstep : a + 4#64 + BitVec.ofNat 64 (4 * rest.length) =
        a + BitVec.ofNat 64 (4 * (rest.length + 1)) := by
      rw [BitVec.add_assoc]; congr 1
      apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]; omega
    rw [List.cons_append, array_cons, array_cons, List.length_cons,
      ih (a + BitVec.ofNat 64 (Ty.bytes i32)), h4, hstep, sep_assoc]

/-! ## 3. `full_rescale_m6`, `full_bump_var`, `full_bump_decay` (`Full.*` Exact Specs) -/

section EvsidsProofs

open scoped FullArenaTactics

private theorem s13_probePres_refl (s : FullState) : FullProbeScratchPres s s :=
  ⟨⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem s13_probePres_trans {s1 s2 s3 : FullState}
    (h12 : FullProbeScratchPres s1 s2) (h23 : FullProbeScratchPres s2 s3) :
    FullProbeScratchPres s1 s3 :=
  ⟨⟨h23.1.1.trans h12.1.1, h23.1.2.trans h12.1.2⟩,
    h23.2.1.trans h12.2.1, h23.2.2.1.trans h12.2.2.1, h23.2.2.2.1.trans h12.2.2.2.1,
    h23.2.2.2.2.1.trans h12.2.2.2.2.1, h23.2.2.2.2.2.1.trans h12.2.2.2.2.2.1,
    h23.2.2.2.2.2.2.1.trans h12.2.2.2.2.2.2.1, h23.2.2.2.2.2.2.2.trans h12.2.2.2.2.2.2.2⟩

private theorem s13_hlen_upd_score {c : FullCfg} {s : FullState}
    (hlen : s.LengthsOk c) (sc' : List (BitVec 64)) (hs : sc'.length = c.max_vars) :
    ({ core := s.core, scratch := { s.scratch with score := sc' } } : FullState).LengthsOk c :=
  hlen.with_scratch { hlen.scratch_ok with score_len := hs }

/-- Step-13 `full_rescale_m6` (`f64u_div` + `f64u_mul`) satisfies exact `Full.fullRescaleSpec`. -/
theorem full_rescale_m6_step13_wp (Γ : Env)
    (hDiv : ∀ a m Q X, f64uPure2Spec a m Q X → Γ "f64u_div" [i64, i64] [i64] a m Q X)
    (hMul : ∀ a m Q X, f64uPure2Spec a m Q X → Γ "f64u_mul" [i64, i64] [i64] a m Q X) :
    ∀ a m Q X, fullRescaleSpec a m Q X → Func.wp Γ full_rescale_m6_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  dsimp only [fullSafetySlice] at hm hlen hQ
  have hmx : c.max_vars < 2 * dimacsBound := c.hmaxv
  unfold dimacsBound at hmx
  have hcv_le := hlen.core_ok.cur_vars_le
  have hsl := hlen.scratch_ok.score_len
  have hcv64 : (BitVec.ofNat 64 s.core.cur_vars).toNat = s.core.cur_vars :=
    bv64_ofNat_toNat (by omega)
  unfold Func.wp full_rescale_m6_body
  c0_hsteps_nogrp
  refine wp_loop_inv
    (fun (mx, mi, ()) m1 => mi.toNat ≤ s.core.cur_vars ∧ m1 = m)
    (fun (_, mi, ()) _ => s.core.cur_vars - mi.toNat)
    (fun J1 hJ1 => by c0_hsteps; exact hJ1 (0#64, 0#64, ()) m ⟨Nat.zero_le _, rfl⟩)
    (fun J1 (mx, mi, ()) m1 ⟨hmi_le, hm1⟩ hJ1 => ?_)
  · rcases hm1.symm with rfl; rw [Blocks.get_here]; dsimp only
    c0_hsteps_nogrp
    · have hmi_lt : mi.toNat < s.core.cur_vars := by
        have h1 : mi.toNat < (BitVec.ofNat 64 s.core.cur_vars).toNat := by c0_bound
        omega
      have hmip1 : (mi + 1).toNat = mi.toNat + 1 := by bv_omega
      have hmi_sc : mi.toNat < s.scratch.score.length := by rw [hsl]; omega
      c0_hsteps
      · exact hJ1 (_, mi + 1, ()) m (by dsimp only; omega) ⟨by omega, rfl⟩
      · exact hJ1 (_, mi + 1, ()) m (by dsimp only; omega) ⟨by omega, rfl⟩
    · refine wp_join_group (ts := [i64]) (fun _ m2 => m2 = m)
        (fun _ _ m2 hm2 => ?_) (fun Jmx hJmx => by c0_hsteps; all_goals exact hJmx _ m rfl)
      rcases hm2.symm with rfl; rw [Blocks.get_here]
      c0_hsteps_nogrp
      c0_call hDiv; intro factor
      c0_hsteps_nogrp
      refine wp_loop_safety_slice_pure (fullSafetySlice c) s R
        (fun s1 (v, ()) => v.toNat ≤ s.core.cur_vars ∧ FullProbeScratchPres s s1)
        (fun (v, ()) => s.core.cur_vars - v.toNat)
        (fun J2 hJ2 => by
          c0_hsteps; exact hJ2 s (0#64, ()) m hm rfl hlen ⟨Nat.zero_le _, s13_probePres_refl s⟩)
        (fun J2 s1 (v, ()) m2 hcore1 hlen1 ⟨hv1, hpres1⟩ hm2 hJ2 => ?_)
      rw [Blocks.get_here]; dsimp only [fullSafetySlice] at *
      have hceq1 : s1.core = s.core := hcore1
      have hsl1 := hlen1.scratch_ok.score_len
      c0_hsteps_nogrp
      · have hv_lt : v.toNat < s.core.cur_vars := by
          have h1 : v.toNat < (BitVec.ofNat 64 s.core.cur_vars).toNat := by
            rw [hceq1] at *; c0_bound
          omega
        have hvp1 : (v + 1).toNat = v.toNat + 1 := by bv_omega
        have hv_sc : v.toNat < s1.scratch.score.length := by rw [hsl1]; omega
        c0_hsteps_nogrp
        c0_call hMul; intro nsc
        c0_hsteps
        exact hJ2 _ (v + 1, ()) m hm (by dsimp only; omega) rfl
          (s13_hlen_upd_score hlen1 _ (by simp [hsl1])) ⟨by dsimp only; omega, hpres1⟩
      · c0_call hMul; intro ninc
        c0_hsteps
        let sf : FullState := { core := s1.core, scratch := { s1.scratch with scinc := ninc } }
        exact hQ () sf m hcore1 (hlen1.with_scratch { hlen1.scratch_ok with }) hpres1 hm

/-- Step-13 `full_bump_var` (`f64u_add`) satisfies exact `Full.fullBumpVarSpec`. -/
theorem full_bump_var_step13_wp (Γ : Env)
    (hAdd : ∀ a m Q X, f64uPure2Spec a m Q X → Γ "f64u_add" [i64, i64] [i64] a m Q X)
    (hUp : ∀ a m Q X, fullHeapUpSpec a m Q X → Γ "full_heap_up" [i64, i32] [] a m Q X)
    (hRes : ∀ a m Q X, fullRescaleSpec a m Q X → Γ "full_rescale" [i64] [] a m Q X) :
    ∀ a m Q X, fullBumpVarSpec a m Q X → Func.wp Γ full_bump_var_body a m Q X := by
  rintro ⟨h, v, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  dsimp only [fullSafetySlice] at hm hlen hQ
  have hmx : c.max_vars < 2 * dimacsBound := c.hmaxv
  unfold dimacsBound at hmx
  have hcv_le := hlen.core_ok.cur_vars_le
  have hsl := hlen.scratch_ok.score_len
  unfold Func.wp full_bump_var_body
  c0_hsteps_nogrp
  · exact hQ () s m rfl hlen (s13_probePres_refl s) hm
  · have hv_lt : (BitVec.setWidth 64 v).toNat < s.core.cur_vars := by
      have h1 : (BitVec.setWidth 64 v).toNat < (BitVec.ofNat 64 s.core.cur_vars).toNat := by
        c0_bound
      rwa [bv64_ofNat_toNat (by omega)] at h1
    have hv_sc : (BitVec.setWidth 64 v).toNat < s.scratch.score.length := by rw [hsl]; omega
    c0_hsteps_nogrp
    c0_call hAdd; intro nsc
    c0_hsteps_nogrp
    let s0 : FullState :=
      { core := s.core, scratch := { s.scratch with
          score := s.scratch.score.set (BitVec.setWidth 64 v).toNat nsc } }
    have hlen0 : s0.LengthsOk c := s13_hlen_upd_score hlen _ (by simp [hsl])
    refine wp_join_group (ts := [])
      (fun () m1 => ∃ s1 : FullState, PreservesCoreSlice FullState.core s s1 ∧
        s1.LengthsOk c ∧ FullProbeScratchPres s s1 ∧ (FullMem c s1 ⋆ R) m1)
      (fun _ () m1 ⟨s1, hcore1, hlen1, hpres1, hm1⟩ => ?_)
      (fun Jup hJup => ?_)
    · rw [Blocks.get_here]
      c0_hsteps
      · c0_call hRes
        refine ⟨c, s1, R, rfl, hlen1, hm1, fun () s2 m2 hcore2 hlen2 hpres2 hm2 => ?_⟩
        dsimp only [fullSafetySlice] at hm2 hlen2 hcore2
        c0_hsteps
        exact hQ () s2 m2 (hcore1.trans hcore2) hlen2 (s13_probePres_trans hpres1 hpres2) hm2
      · exact hQ () s1 m1 hcore1 hlen1 hpres1 hm1
    · c0_hsteps_nogrp
      · c0_call hUp
        refine ⟨c, s0, R, rfl, hlen0, by assumption, fun () s1 m1 hcore1 hlen1 hpres1 hm1 => ?_⟩
        dsimp only [fullSafetySlice] at hm1 hlen1 hcore1
        c0_hsteps
        exact hJup () m1 ⟨s1, hcore1, hlen1, hpres1.1, hm1⟩
      · exact hJup () _ ⟨s0, rfl, hlen0, s13_probePres_refl s, by assumption⟩

/-- Step-13 `full_bump_decay` (`f64u_mul`) satisfies exact `Full.fullBumpDecaySpec`. -/
theorem full_bump_decay_step13_wp (Γ : Env)
    (hMul : ∀ a m Q X, f64uPure2Spec a m Q X → Γ "f64u_mul" [i64, i64] [i64] a m Q X)
    (hRes : ∀ a m Q X, fullRescaleSpec a m Q X → Γ "full_rescale" [i64] [] a m Q X) :
    ∀ a m Q X, fullBumpDecaySpec a m Q X → Func.wp Γ full_bump_decay_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  dsimp only [fullSafetySlice] at hm hlen hQ
  unfold Func.wp full_bump_decay_body
  c0_hsteps_nogrp
  c0_call hMul; intro ninc
  c0_hsteps
  · let s0 : FullState := { core := s.core, scratch := { s.scratch with scinc := ninc } }
    have hlen0 : s0.LengthsOk c := hlen.with_scratch { hlen.scratch_ok with }
    c0_call hRes
    refine ⟨c, s0, R, rfl, hlen0, hm, fun () s1 m1 hcore1 hlen1 hpres1 hm1 => ?_⟩
    dsimp only [fullSafetySlice] at hm1 hlen1 hcore1
    c0_hsteps
    exact hQ () s1 m1 hcore1 hlen1 hpres1 hm1
  · let s0 : FullState := { core := s.core, scratch := { s.scratch with scinc := ninc } }
    exact hQ () s0 m rfl (hlen.with_scratch { hlen.scratch_ok with })
      ⟨⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hm

end EvsidsProofs

/-! ## 4. `full_sort_ana_qs_m6` (`s13SortAnaQsSpec`, `PERF-R3` Insertion + LSD Radix + Heapsort) -/

section SortAnaProof

open scoped FullArenaTactics

def sortAnaRestSans5 (c : FullCfg) (s : FullState) : Mem 64 → Prop :=
  dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
  array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆
  FullCoreByteArrs c s.core ⋆ FullCoreU32A c s.core ⋆
  array (t := i32) c.pFrameTrail s.core.frame_trail ⋆
  array (t := i32) c.pFrameDec s.core.frame_dec ⋆
  array (t := i32) c.pWvec s.core.wvec ⋆
  array (t := i32) c.pMinStk s.core.min_stk ⋆
  FullCoreDynArrs c s.core ⋆
  FullScrByteArrs c s.scratch ⋆
  array (t := i32) c.pHeap s.scratch.heap ⋆ array (t := i32) c.pPos s.scratch.pos ⋆
  array (t := i32) c.pShrinkStk s.scratch.shrink_stk ⋆
  array (t := i32) c.pQPrev s.scratch.q_prev ⋆ array (t := i32) c.pQNext s.scratch.q_next ⋆
  array (t := i32) c.pWorkStk2 s.scratch.work_stk2 ⋆
  array (t := i32) c.pTarjanMark s.scratch.tarjan_mark ⋆
  array (t := i32) c.pTarjanReach s.scratch.tarjan_reach ⋆
  FullScrMetaArrs c s.scratch ⋆
  array (t := i32) c.pDelayed s.scratch.delayed ⋆
  array (t := i32) c.pRedRefs s.scratch.red_refs ⋆
  array (t := i32) c.pExtendStk s.scratch.extend_stk ⋆
  c.pad

theorem fullMem_to_sortAna5 {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (FullMem c s ⋆ R) m) :
    (array (t := i32) c.pQStamp s.scratch.q_stamp ⋆
      array (t := i32) c.pWorkStk1 s.scratch.work_stk1 ⋆
      array (t := i32) c.pRepr s.core.repr ⋆
      array (t := i32) c.pWsort s.scratch.wsort ⋆
      array (t := i32) c.pScratchBuf s.scratch.scratch_buf ⋆
      (sortAnaRestSans5 c s ⋆ R)) m := by
  unfold FullMem FullCoreArrays FullCoreU32B FullScratchArrays FullScrU32A FullScrWksArrs
    FullScrDynArrs at hm
  unfold sortAnaRestSans5
  exact sep_ac hm

theorem fullMem_of_sortAna5 {c : FullCfg} {s : FullState}
    {ws1' repr' wsort' sbuf' : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (array (t := i32) c.pQStamp s.scratch.q_stamp ⋆
      array (t := i32) c.pWorkStk1 ws1' ⋆
      array (t := i32) c.pRepr repr' ⋆
      array (t := i32) c.pWsort wsort' ⋆
      array (t := i32) c.pScratchBuf sbuf' ⋆
      (sortAnaRestSans5 c s ⋆ R)) m) :
    (FullMem c { core := { s.core with repr := repr' }
                 scratch := { s.scratch with
                   work_stk1 := ws1', wsort := wsort', scratch_buf := sbuf' } } ⋆ R) m := by
  unfold FullMem FullCoreArrays FullCoreU32B FullScratchArrays FullScrU32A FullScrWksArrs
    FullScrDynArrs
  unfold sortAnaRestSans5 at hm
  exact sep_ac hm

theorem s13_take_set_lt {α : Type} (xs : List α) {n i : Nat} (v : α) (hi : i < n) :
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

theorem s13_count_set_eq {α : Type} [DecidableEq α] (l : List α) (i : Nat) (v x : α)
    (hi : i < l.length) :
    (l.set i v).count x + (if l[i] == x then 1 else 0) =
      l.count x + (if v == x then 1 else 0) := by
  induction l generalizing i with
  | nil => simp at hi
  | cons a rest ih =>
    cases i with
    | zero => simp [List.count_cons]; omega
    | succ i' =>
      simp only [List.set_cons_succ, List.count_cons, List.getElem_cons_succ]
      have := ih i' (by simp at hi; omega)
      omega

theorem s13_swap_perm {α : Type} [DecidableEq α] {xs : List α} {i j : Nat}
    (hi : i < xs.length) (hj : j < xs.length) :
    ((xs.set i (xs[j]'hj)).set j (xs[i]'hi)).Perm xs := by
  by_cases hij : i = j
  · subst hij; rw [List.set_getElem_self hi, List.set_getElem_self hi]
  · rw [List.perm_iff_count]; intro x
    have h1 := s13_count_set_eq xs i (xs[j]'hj) x hi
    have h2 := s13_count_set_eq (xs.set i (xs[j]'hj)) j (xs[i]'hi) x
      (by rw [List.length_set]; exact hj)
    rw [List.getElem_set_ne hij] at h2; omega

theorem s13_ins_shift_perm {xs : List (BitVec 64)} {n j : Nat} {x : BitVec 64}
    (hj1 : 1 ≤ j) (hjn : j < n) (hn : n ≤ xs.length) :
    (((xs.set j (xs[j - 1]'(by omega))).set (j - 1) x).take n).Perm
      ((xs.set j x).take n) := by
  rw [s13_take_set_lt _ _ (by omega : j - 1 < n), s13_take_set_lt _ _ hjn,
    s13_take_set_lt _ _ hjn, List.perm_iff_count]
  intro y
  have hl : (xs.take n).length = n := by simp; omega
  have h1 := s13_count_set_eq (xs.take n) j (xs[j - 1]'(by omega)) y (by omega)
  have h2 := s13_count_set_eq ((xs.take n).set j (xs[j - 1]'(by omega))) (j - 1) x y
    (by simp; omega)
  have h3 := s13_count_set_eq (xs.take n) j x y (by omega)
  rw [List.getElem_set_ne (by omega : j ≠ j - 1), List.getElem_take] at h2
  omega

theorem s13_pack_word_lo (q a : BitVec 32) :
    (((q.setWidth 64 <<< 32) ||| a.setWidth 64).setWidth 32) = a :=
  (s13_pack_pair_word a q).1

theorem s13_take_map_eq_of_eq {rk : List (BitVec 64)} {ana : List (BitVec 32)} {n : Nat}
    (hrk : n ≤ rk.length) (hana : n ≤ ana.length)
    (heq : ∀ k (hk : k < n), (rk[k]'(by omega)).setWidth 32 = ana[k]'(by omega)) :
    (rk.take n).map (BitVec.setWidth 32) = ana.take n := by
  apply List.ext_getElem (by simp; omega)
  intro k hk1 hk2
  have hkn : k < n := by simp at hk2; omega
  simp only [List.getElem_map, List.getElem_take]
  exact heq k hkn

theorem s13_lt_cv_of_perm {ws1 ws0 : List (BitVec 32)} {n cv : Nat}
    (hl1 : n ≤ ws1.length) (hl0 : n ≤ ws0.length)
    (hperm : (ws1.take n).Perm (ws0.take n))
    (hlt0 : ∀ k < n, (ws0[k]?.getD 0#32).toNat < cv) :
    ∀ k < n, (ws1[k]?.getD 0#32).toNat < cv := by
  intro k hk
  have hmem : ws1[k]'(by omega) ∈ ws1.take n := by
    rw [List.mem_iff_getElem]
    exact ⟨k, by simp; omega, by simp⟩
  have hmem0 := hperm.subset hmem
  rw [List.mem_iff_getElem] at hmem0
  rcases hmem0 with ⟨j, hj, hjeq⟩
  simp only [List.length_take, List.getElem_take] at hj hjeq
  have hltj := hlt0 j (by omega)
  rw [List.getElem?_eq_getElem (by omega : j < ws0.length), Option.getD_some] at hltj
  rw [List.getElem?_eq_getElem (by omega : k < ws1.length), Option.getD_some, ← hjeq]
  exact hltj

theorem s13_swap_take_perm {xs : List (BitVec 32)} {n i j : Nat}
    (hi : i < n) (hj : j < n) (hn : n ≤ xs.length) :
    let xs' := (xs.set i (xs[j]'(by omega))).set j (xs[i]'(by omega))
    xs'.length = xs.length ∧ (xs'.take n).Perm (xs.take n) ∧
    (∀ k, n ≤ k → xs'[k]? = xs[k]?) := by
  intro xs'
  refine ⟨by simp [xs'], ?_, fun k hk => ?_⟩
  · have hi_t : i < (xs.take n).length := by simp; omega
    have hj_t : j < (xs.take n).length := by simp; omega
    have hsw : xs'.take n =
        (((xs.take n).set i ((xs.take n)[j]'hj_t)).set j ((xs.take n)[i]'hi_t)) := by
      dsimp only [xs']
      rw [s13_take_set_lt _ _ hj, s13_take_set_lt _ _ hi]
      simp [List.getElem_take]
    rw [hsw]; exact s13_swap_perm hi_t hj_t
  · dsimp only [xs']; rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]

theorem s13_list_take_split_eq {α : Type} {xs ys : List α} {m n : Nat}
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

theorem s13_perm_take_lift {xs ys : List (BitVec 32)} {m n : Nat}
    (hmn : m ≤ n) (hn : n ≤ xs.length) (hl : ys.length = xs.length)
    (hperm : (ys.take m).Perm (xs.take m)) (hsuf : ∀ k, m ≤ k → ys[k]? = xs[k]?) :
    (ys.take n).Perm (xs.take n) := by
  rw [s13_list_take_split_eq hmn hn hl.symm (fun k h1 _ => hsuf k h1),
    s13_list_take_split_eq hmn hn rfl (fun _ _ _ => rfl)]
  exact hperm.append_right _

/-! ### 4a. LSD Radix Sort Permutation Lemmas (`flatMap` Bucket Count Invariant) -/

def rdxBkt (shift : Nat) (w : BitVec 64) : Nat :=
  ((w >>> shift) &&& 255#64).toNat

theorem rdxBkt_eq (shift : Nat) (w : BitVec 64) :
    rdxBkt shift w = ((w >>> shift) &&& 255#64).toNat := by unfold rdxBkt; rfl

theorem rdxBkt_lt (shift : Nat) (w : BitVec 64) : rdxBkt shift w < 256 := by
  unfold rdxBkt
  rw [BitVec.toNat_and]
  exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

def rdxSeen (shift : Nat) (xs : List (BitVec 64)) (i b : Nat) : Nat :=
  ((xs.take i).filter (fun w => rdxBkt shift w == b)).length

theorem rdxSeen_zero (shift : Nat) (xs : List (BitVec 64)) (b : Nat) :
    rdxSeen shift xs 0 b = 0 := by unfold rdxSeen; rfl

theorem rdxSeen_le (shift : Nat) (xs : List (BitVec 64)) (i b : Nat) :
    rdxSeen shift xs i b ≤ i := by
  unfold rdxSeen
  exact Nat.le_trans (List.length_filter_le ..) (by simp; omega)

theorem rdxSeen_succ (shift : Nat) (xs : List (BitVec 64)) {i : Nat}
    (hi : i < xs.length) (b : Nat) :
    rdxSeen shift xs (i + 1) b =
      rdxSeen shift xs i b + (if rdxBkt shift (xs[i]'hi) = b then 1 else 0) := by
  unfold rdxSeen
  rw [List.take_succ_eq_append_getElem hi, List.filter_append, List.length_append]
  simp only [List.filter_cons, List.filter_nil, beq_iff_eq]
  split <;> simp

theorem rdxSeen_mono (shift : Nat) (xs : List (BitVec 64)) {i j : Nat}
    (hij : i ≤ j) (hj : j ≤ xs.length) (b : Nat) :
    rdxSeen shift xs i b ≤ rdxSeen shift xs j b := by
  induction j with
  | zero =>
    have h0 : i = 0 := by omega
    rw [h0]; exact Nat.le_refl _
  | succ j' ih =>
    by_cases h : i ≤ j'
    · have h1 := ih h (by omega)
      rw [rdxSeen_succ shift xs (by omega)]
      omega
    · have h1 : i = j' + 1 := by omega
      rw [h1]; exact Nat.le_refl _

def rdxStart (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | b + 1 => rdxStart f b + f b

theorem rdxStart_zero (f : Nat → Nat) : rdxStart f 0 = 0 := by unfold rdxStart; rfl

theorem rdxStart_succ (f : Nat → Nat) (b : Nat) :
    rdxStart f (b + 1) = rdxStart f b + f b := by rw [rdxStart]

theorem rdxStart_mono (f : Nat → Nat) {a b : Nat} (hab : a ≤ b) :
    rdxStart f a ≤ rdxStart f b := by
  induction b with
  | zero =>
    have h0 : a = 0 := by omega
    rw [h0]; exact Nat.le_refl _
  | succ b' ih =>
    by_cases h : a ≤ b'
    · have := ih h; simp only [rdxStart]; omega
    · have h1 : a = b' + 1 := by omega
      rw [h1]; exact Nat.le_refl _

theorem rdxStart_sum_all (shift : Nat) (xs : List (BitVec 64)) (n : Nat)
    (hn : n ≤ xs.length) :
    rdxStart (fun b => rdxSeen shift xs n b) 256 = n := by
  have hgen : ∀ k, k ≤ n →
      rdxStart (fun b => rdxSeen shift xs k b) 256 = k := by
    intro k hk
    induction k with
    | zero =>
      have h0 : ∀ m, rdxStart (fun b => rdxSeen shift xs 0 b) m = 0 := by
        intro m; induction m with
        | zero => rfl
        | succ m' ih => rw [rdxStart, ih, rdxSeen_zero]
      exact h0 256
    | succ k' ih =>
      have hstep : ∀ m, rdxStart (fun b => rdxSeen shift xs (k' + 1) b) m =
          rdxStart (fun b => rdxSeen shift xs k' b) m +
            (if rdxBkt shift (xs[k']'(by omega)) < m then 1 else 0) := by
        intro m; induction m with
        | zero => simp [rdxStart]
        | succ m' ihm =>
          rw [rdxStart, rdxStart, ihm, rdxSeen_succ shift xs (by omega : k' < xs.length)]
          split <;> split <;> split <;> omega
      rw [hstep 256, ih (by omega), ite_eq_left (rdxBkt_lt shift _)]
  exact hgen n (Nat.le_refl _)

theorem rdx_slice_set_ne {α : Type} (xs : List α) {p s len : Nat} (v : α)
    (hdisj : p < s ∨ s + len ≤ p) :
    ((xs.set p v).drop s).take len = (xs.drop s).take len := by
  apply List.ext_getElem (by simp)
  intro k hk1 hk2
  simp only [List.length_take, List.length_drop, List.length_set] at hk1 hk2
  have hk_lt : k < len := by omega
  simp only [List.getElem_take, List.getElem_drop]
  exact List.getElem_set_ne (by omega : p ≠ s + k) _

theorem rdx_slice_set_append {α : Type} (xs : List α) {s len : Nat} (v : α)
    (hfit : s + len < xs.length) :
    ((xs.set (s + len) v).drop s).take (len + 1) =
      (xs.drop s).take len ++ [v] := by
  apply List.ext_getElem (by simp; omega)
  intro k hk1 hk2
  simp only [List.length_take, List.length_drop, List.length_set, List.length_append,
    List.length_singleton] at hk1 hk2
  have hlt : ((xs.drop s).take len).length = len := by simp; omega
  by_cases hkl : k < len
  · rw [List.getElem_take, List.getElem_drop, List.getElem_set_ne (by omega),
      List.getElem_append_left (by omega), List.getElem_take, List.getElem_drop]
  · have hke : k = len := by omega
    subst hke
    rw [List.getElem_take, List.getElem_drop, List.getElem_set_self,
      List.getElem_append_right (by omega)]
    simp [hlt]

theorem rdx_flatMap_range_full {α : Type} (f : Nat → Nat) (xs : List α) :
    ∀ m, rdxStart f m ≤ xs.length →
      ((List.range m).flatMap fun b => (xs.drop (rdxStart f b)).take (f b)) =
        xs.take (rdxStart f m) := by
  intro m hm
  induction m with
  | zero => simp [rdxStart]
  | succ m' ih =>
    have hle : rdxStart f m' ≤ xs.length := by simp only [rdxStart] at hm; omega
    rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, ih hle]
    apply List.ext_getElem (by simp [rdxStart] at hm ⊢; omega)
    intro k hk1 hk2
    simp only [List.length_append, List.length_take, List.length_drop] at hk1 hk2
    have hlt : (xs.take (rdxStart f m')).length = rdxStart f m' := by simp; omega
    by_cases hk : k < rdxStart f m'
    · rw [List.getElem_append_left (by omega), List.getElem_take, List.getElem_take]
    · rw [List.getElem_append_right (by omega), List.getElem_take, List.getElem_drop,
        List.getElem_take]
      congr 1; omega

theorem rdx_flatMap_count_step (shift : Nat) (s_arr d_arr : List (BitVec 64))
    {n i : Nat} (hn : n ≤ s_arr.length) (hd : n ≤ d_arr.length) (hi : i < n)
    (y : BitVec 64) :
    let tot := fun b => rdxSeen shift s_arr n b
    let x := s_arr[i]'(by omega)
    let bv := rdxBkt shift x
    let p := rdxStart tot bv + rdxSeen shift s_arr i bv
    let d' := d_arr.set p x
    ((List.range 256).flatMap fun b =>
        (d'.drop (rdxStart tot b)).take (rdxSeen shift s_arr (i + 1) b)).count y =
      ((List.range 256).flatMap fun b =>
        (d_arr.drop (rdxStart tot b)).take (rdxSeen shift s_arr i b)).count y +
        (if x == y then 1 else 0) := by
  intro tot x bv p d'
  have hbv_lt : bv < 256 := rdxBkt_lt shift x
  have hseen_lt : rdxSeen shift s_arr i bv < tot bv := by
    have h1 := rdxSeen_succ shift s_arr (by omega : i < s_arr.length) bv
    have h2 := rdxSeen_mono shift s_arr (by omega : i + 1 ≤ n) hn bv
    have : rdxBkt shift (s_arr[i]'(by omega)) = bv := rfl
    rw [ite_eq_left this] at h1; dsimp only [tot]; omega
  have hp_lt_next : p < rdxStart tot (bv + 1) := by simp only [rdxStart, p]; omega
  have hp_lt_n : p < n := by
    have hle := rdxStart_mono tot (by omega : bv + 1 ≤ 256)
    rw [rdxStart_sum_all shift s_arr n hn] at hle; omega
  have hgen : ∀ m, m ≤ 256 →
      ((List.range m).flatMap fun b =>
          (d'.drop (rdxStart tot b)).take (rdxSeen shift s_arr (i + 1) b)).count y =
        ((List.range m).flatMap fun b =>
          (d_arr.drop (rdxStart tot b)).take (rdxSeen shift s_arr i b)).count y +
          (if bv < m then (if x == y then 1 else 0) else 0) := by
    intro m hm
    induction m with
    | zero => simp
    | succ m' ih =>
      rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
        List.append_nil, List.count_append,
        List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        List.count_append, ih (by omega)]
      by_cases hbm : bv = m'
      · subst hbm
        have hsucc : rdxSeen shift s_arr (i + 1) bv = rdxSeen shift s_arr i bv + 1 := by
          rw [rdxSeen_succ shift s_arr (by omega : i < s_arr.length) bv, ite_eq_left rfl]
        rw [hsucc, rdx_slice_set_append d_arr x (by dsimp only [p] at hp_lt_n; omega),
          List.count_append, List.count_singleton]
        simp only [Nat.lt_irrefl, ↓reduceIte, Nat.lt_succ_self]; omega
      · have hsucc : rdxSeen shift s_arr (i + 1) m' = rdxSeen shift s_arr i m' := by
          rw [rdxSeen_succ shift s_arr (by omega : i < s_arr.length) m', ite_eq_right hbm,
            Nat.add_zero]
        have hdisj : p < rdxStart tot m' ∨ rdxStart tot m' + rdxSeen shift s_arr i m' ≤ p := by
          by_cases hlt : bv < m'
          · left; have := rdxStart_mono tot (by omega : bv + 1 ≤ m'); omega
          · right
            have hle1 := rdxStart_mono tot (by omega : m' + 1 ≤ bv)
            have hle2 := rdxSeen_mono shift s_arr (by omega : i ≤ n) hn m'
            simp only [rdxStart] at hle1; dsimp only [p, tot] at *; omega
        rw [hsucc, rdx_slice_set_ne d_arr x hdisj]
        have hiff : (bv < m' + 1) ↔ (bv < m') := by omega
        by_cases hlt : bv < m'
        · simp [hlt, hiff.mpr hlt]; omega
        · simp [hlt, mt hiff.mp hlt]
  have h256 := hgen 256 (Nat.le_refl _)
  simpa [hbv_lt] using h256

theorem s13_radix_pass_perm (shift : Nat) (s_arr d_arr : List (BitVec 64)) {n : Nat}
    (hn : n ≤ s_arr.length) (hd : n ≤ d_arr.length)
    (hcnt : ∀ y, ((List.range 256).flatMap fun b =>
        (d_arr.drop (rdxStart (fun b => rdxSeen shift s_arr n b) b)).take
          (rdxSeen shift s_arr n b)).count y = (s_arr.take n).count y) :
    (d_arr.take n).Perm (s_arr.take n) := by
  rw [List.perm_iff_count]; intro y
  have hfull := rdx_flatMap_range_full (fun b => rdxSeen shift s_arr n b) d_arr 256
    (by rw [rdxStart_sum_all shift s_arr n hn]; exact hd)
  rw [rdxStart_sum_all shift s_arr n hn] at hfull
  rw [← hfull]; exact hcnt y

end SortAnaProof

end LeanQbe.T.Examples.Kissat.FullFidelityStep13S4
