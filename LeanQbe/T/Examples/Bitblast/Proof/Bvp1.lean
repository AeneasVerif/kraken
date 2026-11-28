/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Bitblast.Ref.BVProg
public import LeanQbe.T.Examples.Bitblast.Src.Header

/-!
# Pure `BVP1` Bytecode Model, `RadixTree` & `ValidBVP1 -> BVProg.parse` (`Bitblast.Proof.Bvp1`)

Pure mathematical layer (zero `Mem` / separation logic) bridging the C0 word-indexed `BVP1`
validator (`Src/Validate.lean`) and evaluator (`Src/Driver.lean`) to `Bitblast.Ref.BVProg`:
- `u32At`, `cwordsOff`, `nodesOff`, `align8`, `countAtoms`, `validNodeAt`, `ValidBVP1`
- `radixTree_get?_insert_same` / `radixTree_get?_insert_ne` (`idx < 2^32`)
- `validBVP1_parse`: every validated byte stream parses via `BVProg.parse` to a unique
  `BVLogicalExpr` with exact `vars`/`cwords`/`nodes` lookup equations
- `atomAssign` & `atomAssign_eq`, `readConstNatAux_getLsbD`, `bvExpr_var_getLsbD`
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Bitblast.Proof

open Std.Tactic.BVDecide
open LeanQbe.T.Examples.Bitblast.Ref
open LeanQbe.T.Examples.Bitblast.Ref.BVProg
open LeanQbe.T.Examples.Bitblast.Src

public section

/-! ## 1. Pure Word Accessors, Offsets, and Atom Prefix Sums -/

/-- Little-endian 32-bit unsigned word at 4-byte index `idx` of `bs`. -/
@[expose] def u32At (bs : List UInt8) (idx : Nat) : Nat :=
  u32OfBytesLE (bs.getD (4 * idx) 0) (bs.getD (4 * idx + 1) 0)
    (bs.getD (4 * idx + 2) 0) (bs.getD (4 * idx + 3) 0)

/-- Word offset of the constant pool (`8 + 2 * n_vars`). -/
@[expose] def cwordsOff (n_vars : Nat) : Nat :=
  8 + 2 * n_vars

/-- Word offset of the node table (`8 + 2 * n_vars + n_cwords`). -/
@[expose] def nodesOff (n_vars n_cwords : Nat) : Nat :=
  8 + 2 * n_vars + n_cwords

/-- Round `n` up to a multiple of `8` (`(n + 7) & ~7`). -/
@[expose] def align8 (n : Nat) : Nat :=
  ((n + 7) / 8) * 8

/-- Exact pure mirror of `bv_count_atoms(prog_ptr, n)` returning `0` on overflow or `1 + ∑ vw`. -/
@[expose] def countAtoms (bs : List UInt8) : Nat → Nat
  | 0 => 1
  | k + 1 =>
    let prev := countAtoms bs k
    let vw := u32At bs (8 + 2 * k + 1)
    if prev == 0 || vw ≥ bvDimacsBound || prev > bvDimacsBound - 1 - vw then 0
    else prev + vw

/-- Exact pure mirror of `bv_validate_node(prog_ptr, nodes_w, n_vars, n_cwords, i)`. -/
@[expose] def validNodeAt (bs : List UInt8) (n_vars n_cwords i : Nat) : Bool :=
  let nw0 := nodesOff n_vars n_cwords
  let base := nw0 + 5 * i
  let op := u32At bs base
  let w := u32At bs (base + 1)
  let a := u32At bs (base + 2)
  let b := u32At bs (base + 3)
  let c := u32At bs (base + 4)
  if op ≥ 32 then false
  else if op == opVar then
    if a ≥ n_vars then false
    else u32At bs (8 + 2 * a + 1) == w
  else if op == opConst then
    let nw := (w + 31) / 32
    if nw > 0 then decide (a ≤ n_cwords ∧ nw ≤ n_cwords - a)
    else true
  else if op == opExtract then
    if b ≥ i then false
    else decide (u32At bs (nw0 + 5 * b) < opEq)
  else if op ≤ opUmod then
    if a ≥ i || b ≥ i then false
    else
      let ab := nw0 + 5 * a
      let bb := nw0 + 5 * b
      decide (u32At bs ab < opEq ∧ u32At bs bb < opEq ∧
        u32At bs (ab + 1) = w ∧ u32At bs (bb + 1) = w)
  else if op ≤ opCpop then
    if a ≥ i then false
    else
      let ab := nw0 + 5 * a
      decide (u32At bs ab < opEq ∧ u32At bs (ab + 1) = w)
  else if op == opAppend then
    if a ≥ i || b ≥ i then false
    else
      let ab := nw0 + 5 * a
      let bb := nw0 + 5 * b
      decide (u32At bs ab < opEq ∧ u32At bs bb < opEq ∧
        u32At bs (ab + 1) + u32At bs (bb + 1) = w)
  else if op == opReplicate then
    if a ≥ i then false
    else
      let ab := nw0 + 5 * a
      decide (u32At bs ab < opEq ∧ u32At bs (ab + 1) * b = w)
  else if op ≤ opAshr then
    if a ≥ i || b ≥ i then false
    else
      let ab := nw0 + 5 * a
      let bb := nw0 + 5 * b
      decide (u32At bs ab < opEq ∧ u32At bs bb < opEq ∧ u32At bs (ab + 1) = w)
  else if w ≠ 1 then false
  else if op ≤ opUlt then
    if a ≥ i || b ≥ i then false
    else
      let ab := nw0 + 5 * a
      let bb := nw0 + 5 * b
      decide (u32At bs ab < opEq ∧ u32At bs bb < opEq ∧
        u32At bs (ab + 1) = u32At bs (bb + 1))
  else if op == opGetLsbD then
    if a ≥ i then false
    else decide (u32At bs (nw0 + 5 * a) < opEq)
  else if op == opBConst then
    decide (a < 2)
  else if op == opBNot then
    if a ≥ i then false
    else decide (u32At bs (nw0 + 5 * a) ≥ opEq)
  else if op ≤ opGateOr then
    if a ≥ i || b ≥ i then false
    else decide (u32At bs (nw0 + 5 * a) ≥ opEq ∧ u32At bs (nw0 + 5 * b) ≥ opEq)
  else
    if a ≥ i || b ≥ i || c ≥ i then false
    else decide (u32At bs (nw0 + 5 * a) ≥ opEq ∧ u32At bs (nw0 + 5 * b) ≥ opEq ∧
      u32At bs (nw0 + 5 * c) ≥ opEq)

/-- Complete structural validity predicate matching `bv_validate` on raw bytes `bs`. -/
structure ValidBVP1 (bs : List UInt8) : Prop where
  len_ge : 32 ≤ bs.length
  len_mod4 : bs.length % 4 = 0
  magic_eq : u32At bs 0 = bvMagic
  ver_eq : u32At bs 1 = bvVersion
  nodes_pos : 0 < u32At bs 3
  root_lt : u32At bs 5 < u32At bs 3
  total_len : 4 * (8 + 2 * u32At bs 2 + u32At bs 4 + 5 * u32At bs 3) = bs.length
  atoms_ok : countAtoms bs (u32At bs 2) ≠ 0
  nodes_ok : ∀ i < u32At bs 3, validNodeAt bs (u32At bs 2) (u32At bs 4) i = true
  root_bool : opEq ≤ u32At bs (nodesOff (u32At bs 2) (u32At bs 4) + 5 * u32At bs 5)

/-- Decoded `BVP1` tables linked to `bs` via `BVProg.parse`. -/
structure ParsedBVP1 (bs : List UInt8) (vars : BinTree VarEntry) (cwords : BinTree Nat)
    (nodes : BinTree ProgNode) (prog : BVLogicalExpr) : Prop where
  valid : ValidBVP1 bs
  parse_eq : BVProg.parse bs = some prog
  vars_get : ∀ k < u32At bs 2,
    vars.get? k = some ⟨u32At bs (8 + 2 * k), u32At bs (8 + 2 * k + 1)⟩
  cwords_get : ∀ j < u32At bs 4,
    cwords.get? j = some (u32At bs (cwordsOff (u32At bs 2) + j))
  nodes_step : ∀ i < u32At bs 3,
    let nw0 := nodesOff (u32At bs 2) (u32At bs 4)
    let base := nw0 + 5 * i
    ∃ nd : ProgNode,
      nodes.get? i = some nd ∧
      decodeNode vars cwords nodes (u32At bs base) (u32At bs (base + 1))
        (u32At bs (base + 2)) (u32At bs (base + 3)) (u32At bs (base + 4)) = some nd ∧
      (u32At bs base < opEq → ∃ e, nd = .bv (u32At bs (base + 1)) e) ∧
      (opEq ≤ u32At bs base → ∃ e, nd = .bool e)
  root_get : nodes.get? (u32At bs 5) = some (.bool prog)

/-- Induced AIG atom assignment `1..num_atoms -> Bool` from `BVExpr.Assignment`. -/
def atomAssignAux (bs : List UInt8) (assign : BVExpr.Assignment) : Nat → Nat → Bool
  | 0, _ => false
  | k + 1, a =>
    let base := countAtoms bs k
    let vw := u32At bs (8 + 2 * k + 1)
    if base ≤ a && a < base + vw then
      (assign.get (u32At bs (8 + 2 * k))).bv.getLsbD (a - base)
    else
      atomAssignAux bs assign k a

/-- Induced AIG atom assignment over all `n_vars = u32At bs 2` variables in `bs`. -/
@[expose] def atomAssign (bs : List UInt8) (assign : BVExpr.Assignment) (a : Nat) : Bool :=
  atomAssignAux bs assign (u32At bs 2) a

end

/-! ## 2. Basic Word, `countAtoms`, and `atomAssign` Lemmas -/

public section

theorem u32At_lt (bs : List UInt8) (idx : Nat) : u32At bs idx < u32Bound := by
  unfold u32At u32OfBytesLE u32Bound
  have h0 := (bs.getD (4 * idx) 0).toNat_lt
  have h1 := (bs.getD (4 * idx + 1) 0).toNat_lt
  have h2 := (bs.getD (4 * idx + 2) 0).toNat_lt
  have h3 := (bs.getD (4 * idx + 3) 0).toNat_lt
  omega

theorem isU32_u32At (bs : List UInt8) (idx : Nat) : isU32 (u32At bs idx) = true := by
  unfold isU32
  exact Nat.blt_eq.mpr (u32At_lt bs idx)

theorem countAtoms_lt (bs : List UInt8) (n : Nat) : countAtoms bs n < bvDimacsBound := by
  induction n with
  | zero => unfold countAtoms bvDimacsBound; decide
  | succ k ih =>
    unfold countAtoms
    dsimp only
    split
    · unfold bvDimacsBound; decide
    · rename_i h
      simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, not_or] at h
      unfold bvDimacsBound at *
      omega

theorem countAtoms_prev_ne_zero {bs : List UInt8} {k : Nat}
    (h : countAtoms bs (k + 1) ≠ 0) :
    countAtoms bs k ≠ 0 ∧
    u32At bs (8 + 2 * k + 1) < bvDimacsBound ∧
    countAtoms bs (k + 1) = countAtoms bs k + u32At bs (8 + 2 * k + 1) := by
  have hdef : countAtoms bs (k + 1) =
      if (countAtoms bs k == 0 || decide (u32At bs (8 + 2 * k + 1) ≥ bvDimacsBound) ||
          decide (countAtoms bs k > bvDimacsBound - 1 - u32At bs (8 + 2 * k + 1))) = true then 0
      else countAtoms bs k + u32At bs (8 + 2 * k + 1) := rfl
  rw [hdef] at h ⊢
  by_cases hc :
      (countAtoms bs k == 0 || decide (u32At bs (8 + 2 * k + 1) ≥ bvDimacsBound) ||
        decide (countAtoms bs k > bvDimacsBound - 1 - u32At bs (8 + 2 * k + 1))) = true
  · simp only [hc, ite_true] at h; exact absurd rfl h
  · simp only [hc, Bool.false_eq_true, ite_false]
    simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, not_or] at hc
    rcases hc with ⟨⟨h1, h2⟩, h3⟩
    unfold bvDimacsBound at *
    exact ⟨h1, by omega, trivial⟩

theorem countAtoms_mono_ne_zero {bs : List UInt8} {n k : Nat} (hle : k ≤ n)
    (hn : countAtoms bs n ≠ 0) :
    countAtoms bs k ≠ 0 ∧ countAtoms bs k ≤ countAtoms bs n := by
  induction n with
  | zero =>
    have hk : k = 0 := by omega
    subst hk
    exact ⟨hn, Nat.le_refl _⟩
  | succ m ih =>
    by_cases hkm : k = m + 1
    · subst hkm; exact ⟨hn, Nat.le_refl _⟩
    · have ⟨hm_ne, _, hm_eq⟩ := countAtoms_prev_ne_zero hn
      have ⟨hk_ne, hk_le⟩ := ih (by omega) hm_ne
      exact ⟨hk_ne, by omega⟩

theorem countAtoms_pos_of_ne_zero {bs : List UInt8} {n : Nat}
    (hn : countAtoms bs n ≠ 0) : 1 ≤ countAtoms bs n := by
  have ⟨_, hle⟩ := countAtoms_mono_ne_zero (Nat.zero_le n) hn
  simpa [countAtoms] using hle

theorem atomAssignAux_eq {bs : List UInt8} {assign : BVExpr.Assignment} {n k j : Nat}
    (hn : countAtoms bs n ≠ 0) (hk : k < n) (hj : j < u32At bs (8 + 2 * k + 1)) :
    atomAssignAux bs assign n (countAtoms bs k + j) =
      (assign.get (u32At bs (8 + 2 * k))).bv.getLsbD j := by
  induction n with
  | zero => omega
  | succ m ih =>
    have ⟨hm_ne, _, _⟩ := countAtoms_prev_ne_zero hn
    unfold atomAssignAux
    dsimp only
    by_cases hkm : k = m
    · subst hkm
      have h1 : countAtoms bs k ≤ countAtoms bs k + j := Nat.le_add_right _ _
      have h2 : countAtoms bs k + j < countAtoms bs k + u32At bs (8 + 2 * k + 1) := by omega
      simp [h1, h2]
    · have hk_lt : k < m := by omega
      have ⟨hk1_ne, hk1_le⟩ := countAtoms_mono_ne_zero (k := k + 1) (n := m) (by omega) hm_ne
      have ⟨_, _, hk1_eq⟩ := countAtoms_prev_ne_zero hk1_ne
      have hnot : ¬ (countAtoms bs m ≤ countAtoms bs k + j) := by omega
      simp only [decide_eq_false hnot, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      exact ih hm_ne hk_lt

theorem atomAssign_eq {bs : List UInt8} {assign : BVExpr.Assignment} {k j : Nat}
    (hn : countAtoms bs (u32At bs 2) ≠ 0) (hk : k < u32At bs 2)
    (hj : j < u32At bs (8 + 2 * k + 1)) :
    atomAssign bs assign (countAtoms bs k + j) =
      (assign.get (u32At bs (8 + 2 * k))).bv.getLsbD j :=
  atomAssignAux_eq hn hk hj

theorem bvExpr_var_getLsbD {w : Nat} (bvIdx : Nat) (assign : BVExpr.Assignment)
    {j : Nat} (hj : j < w) :
    ((BVExpr.var bvIdx : BVExpr w).eval assign).getLsbD j =
      (assign.get bvIdx).bv.getLsbD j := by
  simp only [BVExpr.eval]
  split
  · next heq => cases heq; rfl
  · simp [BitVec.truncate, hj]

/-! ## 3. `RadixTree` Lookup-After-Insert Lemmas (`idx < 2^32`) -/

private theorem nat_beq_false {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  cases hc : Nat.beq a b
  · rfl
  · exact absurd (Nat.beq_eq.mp hc) h

private theorem radix_blt0 : Nat.blt 0 2 = true := rfl
private theorem radix_blt1 : Nat.blt 1 2 = true := rfl
private theorem radix_blt2 : Nat.blt 2 2 = false := rfl
private theorem radix_blt3 : Nat.blt 3 2 = false := rfl
private theorem radix_beq00 : Nat.beq 0 0 = true := rfl
private theorem radix_beq10 : Nat.beq 1 0 = false := rfl
private theorem radix_beq22 : Nat.beq 2 2 = true := rfl
private theorem radix_beq32 : Nat.beq 3 2 = false := rfl

private theorem radix_getAux_empty {α : Type} (fuel idx : Nat) :
    RadixTree.getAux (α := α) fuel .empty idx = none := by
  cases fuel <;> rfl

private theorem radix_getAux_insertAux_same {α : Type} :
    ∀ (fuel : Nat) (t : RadixTree α) (idx : Nat) (x : α),
      idx < 4 ^ fuel →
      RadixTree.getAux fuel (RadixTree.insertAux fuel t idx x) idx = some x
  | 0, .empty, _, _, _ => rfl
  | 0, .node _ _ _ _ _, _, _, _ => rfl
  | fuel + 1, t, idx, x, hlt => by
    have hpow : 4 ^ (fuel + 1) = 4 ^ fuel * 4 := Nat.pow_succ 4 fuel
    cases t with
    | empty =>
      by_cases h0 : idx = 0
      · subst h0; rfl
      · have hq : idx / 4 < 4 ^ fuel := by omega
        have hrem : idx % 4 = 0 ∨ idx % 4 = 1 ∨ idx % 4 = 2 ∨ idx % 4 = 3 := by omega
        have hne0 := nat_beq_false h0
        rcases hrem with hr | hr | hr | hr <;>
          (unfold RadixTree.insertAux
           simp only [hne0, hr, radix_blt0, radix_blt1, radix_blt2, radix_blt3,
             radix_beq00, radix_beq10, radix_beq22, radix_beq32]
           unfold RadixTree.getAux
           simp only [hne0, hr, radix_blt0, radix_blt1, radix_blt2, radix_blt3,
             radix_beq00, radix_beq10, radix_beq22, radix_beq32]
           exact radix_getAux_insertAux_same fuel .empty (idx / 4) x hq)
    | node v c0 c1 c2 c3 =>
      by_cases h0 : idx = 0
      · subst h0; rfl
      · have hq : idx / 4 < 4 ^ fuel := by omega
        have hrem : idx % 4 = 0 ∨ idx % 4 = 1 ∨ idx % 4 = 2 ∨ idx % 4 = 3 := by omega
        have hne0 := nat_beq_false h0
        rcases hrem with hr | hr | hr | hr
        · unfold RadixTree.insertAux
          simp only [hne0, hr, radix_blt0, radix_beq00]
          unfold RadixTree.getAux; simp only [hne0, hr, radix_blt0, radix_beq00]
          exact radix_getAux_insertAux_same fuel c0 (idx / 4) x hq
        · unfold RadixTree.insertAux
          simp only [hne0, hr, radix_blt1, radix_beq10]
          unfold RadixTree.getAux; simp only [hne0, hr, radix_blt1, radix_beq10]
          exact radix_getAux_insertAux_same fuel c1 (idx / 4) x hq
        · unfold RadixTree.insertAux
          simp only [hne0, hr, radix_blt2, radix_beq22]
          unfold RadixTree.getAux; simp only [hne0, hr, radix_blt2, radix_beq22]
          exact radix_getAux_insertAux_same fuel c2 (idx / 4) x hq
        · unfold RadixTree.insertAux
          simp only [hne0, hr, radix_blt3, radix_beq32]
          unfold RadixTree.getAux; simp only [hne0, hr, radix_blt3, radix_beq32]
          exact radix_getAux_insertAux_same fuel c3 (idx / 4) x hq

private theorem radix_getAux_insertAux_ne {α : Type} :
    ∀ (fuel : Nat) (t : RadixTree α) (i j : Nat) (x : α),
      i < 4 ^ fuel → j < 4 ^ fuel → i ≠ j →
      RadixTree.getAux fuel (RadixTree.insertAux fuel t i x) j = RadixTree.getAux fuel t j
  | 0, _, i, j, _, hi, hj, hne => by simp at hi hj; omega
  | fuel + 1, t, i, j, x, hi, hj, hne => by
    have hpow : 4 ^ (fuel + 1) = 4 ^ fuel * 4 := Nat.pow_succ 4 fuel
    cases t with
    | empty =>
      rw [radix_getAux_empty]
      by_cases hi0 : i = 0
      · subst hi0
        have hbj := nat_beq_false (show j ≠ 0 from fun h => hne h.symm)
        unfold RadixTree.insertAux; dsimp only
        unfold RadixTree.getAux; simp only [hbj]
        have hrj : j % 4 = 0 ∨ j % 4 = 1 ∨ j % 4 = 2 ∨ j % 4 = 3 := by omega
        rcases hrj with hr | hr | hr | hr <;>
          (simp only [hr, radix_blt0, radix_blt1, radix_blt2, radix_blt3,
             radix_beq00, radix_beq10, radix_beq22, radix_beq32]
           exact radix_getAux_empty fuel (j / 4))
      · have hbi := nat_beq_false hi0
        by_cases hj0 : j = 0
        · subst hj0
          have hri : i % 4 = 0 ∨ i % 4 = 1 ∨ i % 4 = 2 ∨ i % 4 = 3 := by omega
          rcases hri with hr | hr | hr | hr <;>
            (unfold RadixTree.insertAux
             simp only [hbi, hr, radix_blt0, radix_blt1, radix_blt2, radix_blt3,
               radix_beq00, radix_beq10, radix_beq22, radix_beq32]
             rfl)
        · have hbj := nat_beq_false hj0
          have hiq : i / 4 < 4 ^ fuel := by omega
          have hjq : j / 4 < 4 ^ fuel := by omega
          have hri : i % 4 = 0 ∨ i % 4 = 1 ∨ i % 4 = 2 ∨ i % 4 = 3 := by omega
          have hrj : j % 4 = 0 ∨ j % 4 = 1 ∨ j % 4 = 2 ∨ j % 4 = 3 := by omega
          rcases hri with h1 | h1 | h1 | h1 <;> rcases hrj with h2 | h2 | h2 | h2 <;>
            (unfold RadixTree.insertAux
             simp only [hbi, h1, radix_blt0, radix_blt1, radix_blt2, radix_blt3,
               radix_beq00, radix_beq10, radix_beq22, radix_beq32]
             unfold RadixTree.getAux
             simp only [hbj, h2, radix_blt0, radix_blt1, radix_blt2, radix_blt3,
               radix_beq00, radix_beq10, radix_beq22, radix_beq32])
          all_goals
            first
            | exact radix_getAux_empty fuel (j / 4)
            | (rw [radix_getAux_insertAux_ne fuel .empty (i / 4) (j / 4) x hiq hjq (by omega)]
               exact radix_getAux_empty fuel (j / 4))
    | node v c0 c1 c2 c3 =>
      by_cases hi0 : i = 0
      · subst hi0
        have hbj := nat_beq_false (show j ≠ 0 from fun h => hne h.symm)
        unfold RadixTree.insertAux; dsimp only
        conv => lhs; unfold RadixTree.getAux
        conv => rhs; unfold RadixTree.getAux
        simp only [hbj]
      · have hbi := nat_beq_false hi0
        by_cases hj0 : j = 0
        · subst hj0
          have hri : i % 4 = 0 ∨ i % 4 = 1 ∨ i % 4 = 2 ∨ i % 4 = 3 := by omega
          rcases hri with hr | hr | hr | hr <;>
            (unfold RadixTree.insertAux
             simp only [hbi, hr, radix_blt0, radix_blt1, radix_blt2, radix_blt3,
               radix_beq00, radix_beq10, radix_beq22, radix_beq32]
             rfl)
        · have hbj := nat_beq_false hj0
          have hiq : i / 4 < 4 ^ fuel := by omega
          have hjq : j / 4 < 4 ^ fuel := by omega
          have hri : i % 4 = 0 ∨ i % 4 = 1 ∨ i % 4 = 2 ∨ i % 4 = 3 := by omega
          have hrj : j % 4 = 0 ∨ j % 4 = 1 ∨ j % 4 = 2 ∨ j % 4 = 3 := by omega
          rcases hri with h1 | h1 | h1 | h1 <;> rcases hrj with h2 | h2 | h2 | h2 <;>
            (unfold RadixTree.insertAux
             simp only [hbi, h1, radix_blt0, radix_blt1, radix_blt2, radix_blt3,
               radix_beq00, radix_beq10, radix_beq22, radix_beq32]
             conv => lhs; unfold RadixTree.getAux
             conv => rhs; unfold RadixTree.getAux
             simp only [hbj, h2, radix_blt0, radix_blt1, radix_blt2, radix_blt3,
               radix_beq00, radix_beq10, radix_beq22, radix_beq32])
          all_goals
            first
            | rfl
            | exact radix_getAux_insertAux_ne fuel _ (i / 4) (j / 4) x hiq hjq (by omega)

theorem radixTree_get?_insert_same {α : Type} (t : RadixTree α) {idx : Nat} (x : α)
    (h : idx < u32Bound) : (t.insert idx x).get? idx = some x :=
  radix_getAux_insertAux_same 16 t idx x (by simpa [u32Bound] using h)

theorem radixTree_get?_insert_ne {α : Type} (t : RadixTree α) {i j : Nat} (x : α)
    (hi : i < u32Bound) (hj : j < u32Bound) (hne : i ≠ j) :
    (t.insert i x).get? j = t.get? j :=
  radix_getAux_insertAux_ne 16 t i j x
    (by simpa [u32Bound] using hi) (by simpa [u32Bound] using hj) hne

/-! ## 4. `bytesToWordsLE` and `readConstNatAux` Bit Extraction -/

theorem bytesToWordsLE_of_mod4 (bs : List UInt8) (hmod : bs.length % 4 = 0) :
    ∃ ws : List Nat,
      bytesToWordsLE bs = some ws ∧
      ws.length = bs.length / 4 ∧
      ∀ i < ws.length, ws[i]! = u32At bs i := by
  have haux : ∀ n (l : List UInt8), l.length = 4 * n →
      ∃ ws : List Nat,
        bytesToWordsLE l = some ws ∧
        ws.length = n ∧
        ∀ i < n, ws[i]! = u32At l i := by
    intro n
    induction n with
    | zero =>
      intro l hl
      cases l with
      | nil => exact ⟨[], rfl, rfl, fun i hi => by omega⟩
      | cons _ _ => simp at hl
    | succ n ih =>
      intro l hl
      rcases l with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, rest⟩⟩⟩⟩
      · simp at hl
      · simp at hl; omega
      · simp at hl; omega
      · simp at hl; omega
      · have hrl : rest.length = 4 * n := by simp at hl; omega
        obtain ⟨ws, hbw, hwlen, hget⟩ := ih rest hrl
        refine ⟨u32OfBytesLE b0 b1 b2 b3 :: ws, ?_, by simp [hwlen], ?_⟩
        · simp [bytesToWordsLE, hbw]
        · intro i hi
          cases i with
          | zero => simp [u32At]
          | succ j =>
            have hj : j < n := by omega
            simp only [List.getElem!_cons_succ, hget j hj]
            unfold u32At
            have h4 : ∀ k, (b0 :: b1 :: b2 :: b3 :: rest).getD (4 * (j + 1) + k) 0 =
                rest.getD (4 * j + k) 0 := by
              intro k
              rw [show 4 * (j + 1) + k = 4 * j + k + 4 by omega]; rfl
            have h40 : (b0 :: b1 :: b2 :: b3 :: rest).getD (4 * (j + 1)) 0 =
                rest.getD (4 * j) 0 := by simpa using h4 0
            rw [h40, h4 1, h4 2, h4 3]
  obtain ⟨ws, hbw, hwlen, hget⟩ := haux (bs.length / 4) bs (by omega)
  exact ⟨ws, hbw, hwlen, fun i hi => hget i (by omega)⟩

theorem readConstNatAux_of_cwords {cwords : BinTree Nat} {f : Nat → Nat} {base : Nat} :
    ∀ nw acc,
      (∀ k < nw, cwords.get? (base + k) = some (f k)) →
      ∃ val : Nat,
        readConstNatAux cwords base nw acc = some val ∧
        (∀ j < nw * 32, (∀ k < nw, f k < u32Bound) →
          val.testBit j = (f (j / 32)).testBit (j % 32)) := by
  intro nw
  induction nw with
  | zero =>
    intro acc _
    exact ⟨acc, rfl, fun j hj _ => by omega⟩
  | succ nw ih =>
    intro acc hget
    have htop := hget nw (Nat.lt_succ_self nw)
    obtain ⟨val, hrec, hbits⟩ := ih (acc * u32Bound + f nw)
      (fun k hk => hget k (Nat.lt_succ_of_lt hk))
    refine ⟨val, ?_, ?_⟩
    · simp only [readConstNatAux, htop, hrec]
    · intro j hj hlt
      by_cases hlow : j < nw * 32
      · exact hbits j hlow (fun k hk => hlt k (Nat.lt_succ_of_lt hk))
      · have hval_div : ∀ (m : Nat) (a0 : Nat) (v : Nat),
            (∀ k < m, cwords.get? (base + k) = some (f k)) →
            (∀ k < m, f k < u32Bound) →
            readConstNatAux cwords base m a0 = some v →
            v / (2 ^ (32 * m)) = a0 := by
          intro m
          induction m with
          | zero =>
            intro a0 v _ _ hr
            simp only [readConstNatAux, Option.some.injEq] at hr
            subst hr; simp
          | succ m ihm =>
            intro a0 v hg hl hr
            have hm := hg m (Nat.lt_succ_self m)
            simp only [readConstNatAux, hm] at hr
            have hrec_div := ihm (a0 * u32Bound + f m) v
              (fun k hk => hg k (Nat.lt_succ_of_lt hk))
              (fun k hk => hl k (Nat.lt_succ_of_lt hk)) hr
            have hfm : f m < 2 ^ 32 := hl m (Nat.lt_succ_self m)
            have hpow : 2 ^ (32 * (m + 1)) = 2 ^ (32 * m) * 2 ^ 32 := by
              rw [Nat.mul_add, Nat.mul_one, Nat.pow_add]
            rw [hpow, ← Nat.div_div_eq_div_mul, hrec_div]
            unfold u32Bound
            rw [show (4294967296 : Nat) = 2 ^ 32 from rfl, Nat.mul_comm a0 (2 ^ 32),
              Nat.mul_add_div (by decide : 0 < 2 ^ 32), Nat.div_eq_of_lt hfm, Nat.add_zero]
        have hdiv := hval_div nw (acc * u32Bound + f nw) val
          (fun k hk => hget k (Nat.lt_succ_of_lt hk))
          (fun k hk => hlt k (Nat.lt_succ_of_lt hk)) hrec
        have hj_div : j / 32 = nw := by omega
        have hj_eq : j = 32 * nw + j % 32 := by omega
        have hmod_lt : j % 32 < 32 := Nat.mod_lt j (by decide)
        rw [hj_div, Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq]
        conv => lhs; rw [hj_eq]
        rw [Nat.pow_add, ← Nat.div_div_eq_div_mul, hdiv]
        rw [show (u32Bound : Nat) = 2 ^ 32 from rfl]
        have hq : 2 ^ 32 = 2 ^ (j % 32) * 2 ^ (32 - j % 32) := by
          rw [← Nat.pow_add, Nat.add_sub_of_le (by omega)]
        have hmul' : acc * 2 ^ 32 + f nw = f nw + 2 ^ (j % 32) * (acc * 2 ^ (32 - j % 32)) := by
          rw [hq, Nat.add_comm]; congr 1; rw [Nat.mul_left_comm]
        have hq_even : ∃ q', 2 ^ (32 - j % 32) = 2 * q' :=
          ⟨2 ^ (31 - j % 32), by
            rw [show 32 - j % 32 = (31 - j % 32) + 1 by omega, Nat.pow_succ, Nat.mul_comm]⟩
        rw [hmul', Nat.add_mul_div_left _ _ (Nat.two_pow_pos _)]
        obtain ⟨q', hq'⟩ := hq_even
        rw [hq']
        have hmod2 : (f nw / 2 ^ (j % 32) + acc * (2 * q')) % 2 =
            (f nw / 2 ^ (j % 32)) % 2 := by
          rw [Nat.mul_left_comm, Nat.add_mul_mod_self_left]
        rw [hmod2]

theorem readConstNatAux_getLsbD {cwords : BinTree Nat} {f : Nat → Nat} {base w val : Nat}
    (hget : ∀ k < (w + 31) / 32, cwords.get? (base + k) = some (f k))
    (hlt : ∀ k < (w + 31) / 32, f k < u32Bound)
    (hr : readConstNatAux cwords base ((w + 31) / 32) 0 = some val)
    {j : Nat} (hj : j < w) :
    (BitVec.ofNat w val).getLsbD j = (f (j / 32)).testBit (j % 32) := by
  have ⟨val', hr', hbits⟩ :=
    readConstNatAux_of_cwords (cwords := cwords) (f := f) (base := base) ((w + 31) / 32) 0 hget
  rw [hr'] at hr
  injection hr with heq
  subst heq
  rw [BitVec.getLsbD_ofNat, decide_eq_true hj, Bool.true_and]
  exact hbits j (by omega) hlt

/-! ## 5. `ValidBVP1 -> ParsedBVP1` (`validBVP1_parse`) -/

private theorem parseVars_drop (bs : List UInt8) (ws : List Nat)
    (hws : ∀ i < ws.length, ws[i]! = u32At bs i) :
    ∀ n (idx : Nat) (acc : BinTree VarEntry),
      8 + 2 * idx + 2 * n ≤ ws.length →
      idx + n < u32Bound →
      (∀ k < idx, acc.get? k = some ⟨u32At bs (8 + 2 * k), u32At bs (8 + 2 * k + 1)⟩) →
      ∃ vars : BinTree VarEntry,
        parseVars n idx acc (ws.drop (8 + 2 * idx)) =
          some (vars, ws.drop (8 + 2 * (idx + n))) ∧
        ∀ k < idx + n, vars.get? k = some ⟨u32At bs (8 + 2 * k), u32At bs (8 + 2 * k + 1)⟩ := by
  intro n
  induction n with
  | zero =>
    intro idx acc _ _ hacc
    exact ⟨acc, by simp [parseVars], by simpa using hacc⟩
  | succ n ih =>
    intro idx acc hlen hlt hacc
    have h0 : 8 + 2 * idx < ws.length := by omega
    have h1 : 8 + 2 * idx + 1 < ws.length := by omega
    have hdrop : ws.drop (8 + 2 * idx) =
        ws[8 + 2 * idx]! :: ws[8 + 2 * idx + 1]! :: ws.drop (8 + 2 * (idx + 1)) := by
      rw [List.drop_eq_getElem_cons h0, List.drop_eq_getElem_cons h1]
      simp [getElem!_pos, h0, h1, show 8 + 2 * idx + 1 + 1 = 8 + 2 * (idx + 1) by omega]
    rw [hdrop, hws _ h0, hws _ h1]
    unfold parseVars
    rw [isU32_u32At, isU32_u32At]
    simp only [Bool.and_self]
    have hacc' : ∀ k < idx + 1,
        (acc.insert idx ⟨u32At bs (8 + 2 * idx), u32At bs (8 + 2 * idx + 1)⟩).get? k =
          some ⟨u32At bs (8 + 2 * k), u32At bs (8 + 2 * k + 1)⟩ := by
      intro k hk
      by_cases hke : k = idx
      · subst hke; exact radixTree_get?_insert_same acc _ (by omega)
      · rw [radixTree_get?_insert_ne acc _ (by omega) (by omega) (Ne.symm hke)]
        exact hacc k (by omega)
    obtain ⟨vars, hp, hget⟩ := ih (idx + 1) _ (by omega) (by omega) hacc'
    exact ⟨vars, by simpa [Nat.add_assoc, Nat.add_comm 1 n] using hp, fun k hk => hget k (by omega)⟩

private theorem parseCwords_drop (bs : List UInt8) (ws : List Nat) (nv : Nat)
    (hws : ∀ i < ws.length, ws[i]! = u32At bs i) :
    ∀ n (idx : Nat) (acc : BinTree Nat),
      cwordsOff nv + idx + n ≤ ws.length →
      idx + n < u32Bound →
      (∀ j < idx, acc.get? j = some (u32At bs (cwordsOff nv + j))) →
      ∃ cwords : BinTree Nat,
        parseCwords n idx acc (ws.drop (cwordsOff nv + idx)) =
          some (cwords, ws.drop (cwordsOff nv + (idx + n))) ∧
        ∀ j < idx + n, cwords.get? j = some (u32At bs (cwordsOff nv + j)) := by
  intro n
  induction n with
  | zero =>
    intro idx acc _ _ hacc
    exact ⟨acc, by simp [parseCwords], by simpa using hacc⟩
  | succ n ih =>
    intro idx acc hlen hlt hacc
    have h0 : cwordsOff nv + idx < ws.length := by omega
    have hdrop : ws.drop (cwordsOff nv + idx) =
        ws[cwordsOff nv + idx]! :: ws.drop (cwordsOff nv + (idx + 1)) := by
      rw [List.drop_eq_getElem_cons h0]
      simp [getElem!_pos, h0, Nat.add_assoc]
    rw [hdrop, hws _ h0]
    unfold parseCwords
    rw [isU32_u32At]
    have hacc' : ∀ j < idx + 1,
        (acc.insert idx (u32At bs (cwordsOff nv + idx))).get? j =
          some (u32At bs (cwordsOff nv + j)) := by
      intro j hj
      by_cases hje : j = idx
      · subst hje; exact radixTree_get?_insert_same acc _ (by omega)
      · rw [radixTree_get?_insert_ne acc _ (by omega) (by omega) (Ne.symm hje)]
        exact hacc j (by omega)
    obtain ⟨cwords, hp, hget⟩ := ih (idx + 1) _ (by omega) (by omega) hacc'
    exact ⟨cwords, by simpa [Nat.add_assoc, Nat.add_comm 1 n] using hp,
      fun j hj => hget j (by omega)⟩

private theorem nat_blt_eq_decide (a b : Nat) : Nat.blt a b = decide (a < b) := by
  cases h : Nat.blt a b
  · have hnot : ¬ a < b := fun hlt => by rw [Nat.blt_eq.mpr hlt] at h; cases h
    simp [hnot]
  · simp [Nat.blt_eq.mp h]

/-- Unified `validNodeAt -> decodeNode` + child-bounds theorem (one 14-branch pass). -/
private theorem decodeNode_of_validNodeAt {bs : List UInt8}
    {vars : BinTree VarEntry} {cwords : BinTree Nat} {nodes : BinTree ProgNode}
    {nv nc i : Nat}
    (hvars : ∀ k < nv, vars.get? k = some ⟨u32At bs (8 + 2 * k), u32At bs (8 + 2 * k + 1)⟩)
    (hcw : ∀ j < nc, cwords.get? j = some (u32At bs (cwordsOff nv + j)))
    (hnodes : ∀ j < i, ∃ nd : ProgNode, nodes.get? j = some nd ∧
      (u32At bs (nodesOff nv nc + 5 * j) < opEq →
        ∃ e, nd = .bv (u32At bs (nodesOff nv nc + 5 * j + 1)) e) ∧
      (opEq ≤ u32At bs (nodesOff nv nc + 5 * j) → ∃ e, nd = .bool e))
    (hval : validNodeAt bs nv nc i = true) :
    let base := nodesOff nv nc + 5 * i
    ∃ nd : ProgNode,
      (∀ n' : BinTree ProgNode, (∀ k < i, n'.get? k = nodes.get? k) →
        decodeNode vars cwords n' (u32At bs base) (u32At bs (base + 1))
          (u32At bs (base + 2)) (u32At bs (base + 3)) (u32At bs (base + 4)) = some nd) ∧
      (u32At bs base < opEq → ∃ e, nd = .bv (u32At bs (base + 1)) e) ∧
      (opEq ≤ u32At bs base → ∃ e, nd = .bool e) := by
  intro base
  have hgetBv : ∀ idx < i, u32At bs (nodesOff nv nc + 5 * idx) < opEq →
      ∃ e, nodes.get? idx = some (.bv (u32At bs (nodesOff nv nc + 5 * idx + 1)) e) := by
    intro idx hidx hop
    obtain ⟨nd, hg, hbv, _⟩ := hnodes idx hidx
    obtain ⟨e, rfl⟩ := hbv hop
    exact ⟨e, hg⟩
  have hgetBool : ∀ idx < i, opEq ≤ u32At bs (nodesOff nv nc + 5 * idx) →
      ∃ e, nodes.get? idx = some (.bool e) := by
    intro idx hidx hop
    obtain ⟨nd, hg, _, hbo⟩ := hnodes idx hidx
    obtain ⟨e, rfl⟩ := hbo hop
    exact ⟨e, hg⟩
  unfold validNodeAt at hval
  dsimp only [opVar, opConst, opExtract, opUmod, opCpop, opAppend, opReplicate, opAshr,
    opUlt, opGetLsbD, opBConst, opBNot, opGateOr, opEq] at hval
  let op := u32At bs base
  let w := u32At bs (base + 1)
  let a := u32At bs (base + 2)
  let b := u32At bs (base + 3)
  let c := u32At bs (base + 4)
  change (if op ≥ 32 then false
    else if op == 0 then if a ≥ nv then false else u32At bs (8 + 2 * a + 1) == w
    else if op == 1 then
      if (w + 31) / 32 > 0 then decide (a ≤ nc ∧ (w + 31) / 32 ≤ nc - a) else true
    else if op == 2 then if b ≥ i then false else decide (u32At bs (nodesOff nv nc + 5 * b) < 22)
    else if op ≤ 9 then if a ≥ i || b ≥ i then false else
      decide (u32At bs (nodesOff nv nc + 5 * a) < 22 ∧ u32At bs (nodesOff nv nc + 5 * b) < 22 ∧
        u32At bs (nodesOff nv nc + 5 * a + 1) = w ∧ u32At bs (nodesOff nv nc + 5 * b + 1) = w)
    else if op ≤ 16 then if a ≥ i then false else
      decide (u32At bs (nodesOff nv nc + 5 * a) < 22 ∧ u32At bs (nodesOff nv nc + 5 * a + 1) = w)
    else if op == 17 then if a ≥ i || b ≥ i then false else
      decide (u32At bs (nodesOff nv nc + 5 * a) < 22 ∧ u32At bs (nodesOff nv nc + 5 * b) < 22 ∧
        u32At bs (nodesOff nv nc + 5 * a + 1) + u32At bs (nodesOff nv nc + 5 * b + 1) = w)
    else if op == 18 then if a ≥ i then false else
      decide (u32At bs (nodesOff nv nc + 5 * a) < 22 ∧
        u32At bs (nodesOff nv nc + 5 * a + 1) * b = w)
    else if op ≤ 21 then if a ≥ i || b ≥ i then false else
      decide (u32At bs (nodesOff nv nc + 5 * a) < 22 ∧ u32At bs (nodesOff nv nc + 5 * b) < 22 ∧
        u32At bs (nodesOff nv nc + 5 * a + 1) = w)
    else if w ≠ 1 then false
    else if op ≤ 23 then if a ≥ i || b ≥ i then false else
      decide (u32At bs (nodesOff nv nc + 5 * a) < 22 ∧ u32At bs (nodesOff nv nc + 5 * b) < 22 ∧
        u32At bs (nodesOff nv nc + 5 * a + 1) = u32At bs (nodesOff nv nc + 5 * b + 1))
    else if op == 24 then if a ≥ i then false else decide (u32At bs (nodesOff nv nc + 5 * a) < 22)
    else if op == 25 then decide (a < 2)
    else if op == 26 then if a ≥ i then false else decide (u32At bs (nodesOff nv nc + 5 * a) ≥ 22)
    else if op ≤ 30 then if a ≥ i || b ≥ i then false else
      decide (u32At bs (nodesOff nv nc + 5 * a) ≥ 22 ∧ u32At bs (nodesOff nv nc + 5 * b) ≥ 22)
    else if a ≥ i || b ≥ i || c ≥ i then false else
      decide (u32At bs (nodesOff nv nc + 5 * a) ≥ 22 ∧ u32At bs (nodesOff nv nc + 5 * b) ≥ 22 ∧
        u32At bs (nodesOff nv nc + 5 * c) ≥ 22)) = true at hval
  by_cases hop32 : op ≥ 32
  · simp only [hop32, ite_true] at hval; cases hval
  simp only [hop32, ite_false] at hval
  by_cases h0 : (op == 0) = true
  · -- op = 0 (VAR)
    simp only [h0, ite_true] at hval; have hop0 : op = 0 := beq_iff_eq.mp h0
    by_cases ha : a ≥ nv
    · simp only [ha, ite_true] at hval; cases hval
    simp only [ha, ite_false] at hval
    have hvw : u32At bs (8 + 2 * a + 1) = w := beq_iff_eq.mp hval
    refine ⟨.bv w (.var (u32At bs (8 + 2 * a))), fun n' _ => ?_,
      fun _ => ⟨_, rfl⟩, fun hge => by unfold opEq at hge; omega⟩
    show decodeNode vars cwords n' op w a b c = _
    simp [decodeNode, nat_blt_eq_decide, hop0, hvars a (by omega), hvw]
  simp only [h0, Bool.false_eq_true, ite_false] at hval
  by_cases h1 : (op == 1) = true
  · -- op = 1 (CONST)
    simp only [h1, ite_true] at hval; have hop1 : op = 1 := beq_iff_eq.mp h1
    have hcw_ok : ∀ k < (w + 31) / 32,
        cwords.get? (a + k) = some (u32At bs (cwordsOff nv + (a + k))) := by
      intro k hk
      have hpos : (w + 31) / 32 > 0 := by omega
      simp only [hpos, ite_true, decide_eq_true_eq] at hval
      exact hcw (a + k) (by omega)
    obtain ⟨val, hval_eq, _⟩ :=
      readConstNatAux_of_cwords (cwords := cwords) (f := fun k => u32At bs (cwordsOff nv + (a + k)))
        (base := a) ((w + 31) / 32) 0 hcw_ok
    refine ⟨.bv w (.const (BitVec.ofNat w val)), fun n' _ => ?_,
      fun _ => ⟨_, rfl⟩, fun hge => by unfold opEq at hge; omega⟩
    show decodeNode vars cwords n' op w a b c = _
    simp [decodeNode, nat_blt_eq_decide, hop1, hval_eq]
  simp only [h1, Bool.false_eq_true, ite_false] at hval
  by_cases h2 : (op == 2) = true
  · -- op = 2 (EXTRACT)
    simp only [h2, ite_true] at hval; have hop2 : op = 2 := beq_iff_eq.mp h2
    by_cases hb : b ≥ i
    · simp only [hb, ite_true] at hval; cases hval
    simp only [hb, ite_false, decide_eq_true_eq] at hval
    obtain ⟨eb, hgb⟩ := hgetBv b (by omega) hval
    refine ⟨.bv w (.extract a w eb), fun n' hag => ?_,
      fun _ => ⟨_, rfl⟩, fun hge => by unfold opEq at hge; omega⟩
    show decodeNode vars cwords n' op w a b c = _
    simp [decodeNode, nat_blt_eq_decide, hop2, hag b (by omega), hgb]
  simp only [h2, Bool.false_eq_true, ite_false] at hval
  by_cases hle9 : op ≤ 9
  · -- ops 3..9 (BVBinOp)
    simp only [hle9, ite_true] at hval
    by_cases hab : (a ≥ i || b ≥ i) = true
    · simp only [hab, ite_true] at hval; cases hval
    simp only [hab, Bool.false_eq_true, ite_false, decide_eq_true_eq] at hval
    simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at hab
    obtain ⟨ea, hga⟩ := hgetBv a (by omega) hval.1
    obtain ⟨eb, hgb⟩ := hgetBv b (by omega) hval.2.1
    let bop : BVBinOp :=
      if op == 3 then .and else if op == 4 then .or else if op == 5 then .xor
      else if op == 6 then .add else if op == 7 then .mul else if op == 8 then .udiv else .umod
    have hop_c : op = 3 ∨ op = 4 ∨ op = 5 ∨ op = 6 ∨ op = 7 ∨ op = 8 ∨ op = 9 := by
      simp only [beq_iff_eq] at h0 h1 h2; omega
    refine ⟨.bv w (.bin (hval.2.2.1 ▸ ea) bop (hval.2.2.2 ▸ eb)), fun n' hag => ?_,
      fun _ => ⟨_, rfl⟩, fun hge => by unfold opEq at hge; omega⟩
    show decodeNode vars cwords n' op w a b c = _
    rcases hop_c with h | h | h | h | h | h | h <;>
      simp [decodeNode, mkBvBin, bop, nat_blt_eq_decide, h, hag a (by omega), hag b (by omega),
        hga, hgb, hval.2.2.1, hval.2.2.2]
  simp only [hle9, ite_false] at hval
  by_cases hle16 : op ≤ 16
  · -- ops 10..16 (BVUnOp)
    simp only [hle16, ite_true] at hval
    by_cases ha : a ≥ i
    · simp only [ha, ite_true] at hval; cases hval
    simp only [ha, ite_false, decide_eq_true_eq] at hval
    obtain ⟨ea, hga⟩ := hgetBv a (by omega) hval.1
    let uop : BVUnOp :=
      if op == 10 then .not else if op == 11 then .rotateLeft b
      else if op == 12 then .rotateRight b else if op == 13 then .arithShiftRightConst b
      else if op == 14 then .reverse else if op == 15 then .clz else .cpop
    have hop_c : op = 10 ∨ op = 11 ∨ op = 12 ∨ op = 13 ∨ op = 14 ∨ op = 15 ∨ op = 16 := by omega
    refine ⟨.bv w (.un uop (hval.2 ▸ ea)), fun n' hag => ?_,
      fun _ => ⟨_, rfl⟩, fun hge => by unfold opEq at hge; omega⟩
    show decodeNode vars cwords n' op w a b c = _
    rcases hop_c with h | h | h | h | h | h | h <;>
      simp [decodeNode, mkBvUn, uop, nat_blt_eq_decide, h, hag a (by omega), hga, hval.2]
  simp only [hle16, ite_false] at hval
  by_cases h17 : (op == 17) = true
  · -- op = 17 (APPEND)
    simp only [h17, ite_true] at hval; have hop17 : op = 17 := beq_iff_eq.mp h17
    by_cases hab : (a ≥ i || b ≥ i) = true
    · simp only [hab, ite_true] at hval; cases hval
    simp only [hab, Bool.false_eq_true, ite_false, decide_eq_true_eq] at hval
    simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at hab
    obtain ⟨ea, hga⟩ := hgetBv a (by omega) hval.1
    obtain ⟨eb, hgb⟩ := hgetBv b (by omega) hval.2.1
    have hw : w = u32At bs (nodesOff nv nc + 5 * a + 1) + u32At bs (nodesOff nv nc + 5 * b + 1) :=
      hval.2.2.symm
    refine ⟨.bv w (.append ea eb hw), fun n' hag => ?_,
      fun _ => ⟨_, rfl⟩, fun hge => by unfold opEq at hge; omega⟩
    show decodeNode vars cwords n' op w a b c = _
    simp [decodeNode, nat_blt_eq_decide, hop17, hag a (by omega), hag b (by omega), hga, hgb, hw]
  simp only [h17, Bool.false_eq_true, ite_false] at hval
  by_cases h18 : (op == 18) = true
  · -- op = 18 (REPLICATE)
    simp only [h18, ite_true] at hval; have hop18 : op = 18 := beq_iff_eq.mp h18
    by_cases ha : a ≥ i
    · simp only [ha, ite_true] at hval; cases hval
    simp only [ha, ite_false, decide_eq_true_eq] at hval
    obtain ⟨ea, hga⟩ := hgetBv a (by omega) hval.1
    have hw : w = u32At bs (nodesOff nv nc + 5 * a + 1) * b := hval.2.symm
    refine ⟨.bv w (.replicate b ea hw), fun n' hag => ?_,
      fun _ => ⟨_, rfl⟩, fun hge => by unfold opEq at hge; omega⟩
    show decodeNode vars cwords n' op w a b c = _
    simp [decodeNode, nat_blt_eq_decide, hop18, hag a (by omega), hga, hw]
  simp only [h18, Bool.false_eq_true, ite_false] at hval
  by_cases hle21 : op ≤ 21
  · -- ops 19..21 (shifts)
    simp only [hle21, ite_true] at hval
    by_cases hab : (a ≥ i || b ≥ i) = true
    · simp only [hab, ite_true] at hval; cases hval
    simp only [hab, Bool.false_eq_true, ite_false, decide_eq_true_eq] at hval
    simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at hab
    obtain ⟨ea, hga⟩ := hgetBv a (by omega) hval.1
    obtain ⟨eb, hgb⟩ := hgetBv b (by omega) hval.2.1
    have hop_c : op = 19 ∨ op = 20 ∨ op = 21 := by
      simp only [beq_iff_eq] at h17 h18; omega
    rcases hop_c with h | h | h
    · refine ⟨.bv w (.shiftLeft (hval.2.2 ▸ ea) eb), fun n' hag => ?_,
        fun _ => ⟨_, rfl⟩, fun hge => by unfold opEq at hge; omega⟩
      show decodeNode vars cwords n' op w a b c = _
      simp [decodeNode, nat_blt_eq_decide, h, hag a (by omega), hag b (by omega),
        hga, hgb, hval.2.2]
    · refine ⟨.bv w (.shiftRight (hval.2.2 ▸ ea) eb), fun n' hag => ?_,
        fun _ => ⟨_, rfl⟩, fun hge => by unfold opEq at hge; omega⟩
      show decodeNode vars cwords n' op w a b c = _
      simp [decodeNode, nat_blt_eq_decide, h, hag a (by omega), hag b (by omega),
        hga, hgb, hval.2.2]
    · refine ⟨.bv w (.arithShiftRight (hval.2.2 ▸ ea) eb), fun n' hag => ?_,
        fun _ => ⟨_, rfl⟩, fun hge => by unfold opEq at hge; omega⟩
      show decodeNode vars cwords n' op w a b c = _
      simp [decodeNode, nat_blt_eq_decide, h, hag a (by omega), hag b (by omega),
        hga, hgb, hval.2.2]
  simp only [hle21, ite_false] at hval
  have hw1 : w = 1 := by
    by_cases h : w = 1
    · exact h
    · simp only [h, ne_eq, not_false_eq_true, ite_true] at hval; cases hval
  simp only [hw1, ne_eq, not_true_eq_false, ite_false] at hval
  by_cases hle23 : op ≤ 23
  · -- ops 22..23 (EQ / ULT)
    simp only [hle23, ite_true] at hval
    by_cases hab : (a ≥ i || b ≥ i) = true
    · simp only [hab, ite_true] at hval; cases hval
    simp only [hab, Bool.false_eq_true, ite_false, decide_eq_true_eq] at hval
    simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at hab
    obtain ⟨ea, hga⟩ := hgetBv a (by omega) hval.1
    obtain ⟨eb, hgb⟩ := hgetBv b (by omega) hval.2.1
    have hweq : u32At bs (nodesOff nv nc + 5 * b + 1) = u32At bs (nodesOff nv nc + 5 * a + 1) :=
      hval.2.2.symm
    have hop_c : op = 22 ∨ op = 23 := by omega
    rcases hop_c with h | h
    · refine ⟨.bool (.literal (.bin ea .eq (hweq ▸ eb))), fun n' hag => ?_,
        fun hlt => by unfold opEq at hlt; omega, fun _ => ⟨_, rfl⟩⟩
      show decodeNode vars cwords n' op w a b c = _
      simp [decodeNode, mkPredBin, nat_blt_eq_decide, h, hw1, hag a (by omega), hag b (by omega),
        hga, hgb, hweq]
    · refine ⟨.bool (.literal (.bin ea .ult (hweq ▸ eb))), fun n' hag => ?_,
        fun hlt => by unfold opEq at hlt; omega, fun _ => ⟨_, rfl⟩⟩
      show decodeNode vars cwords n' op w a b c = _
      simp [decodeNode, mkPredBin, nat_blt_eq_decide, h, hw1, hag a (by omega), hag b (by omega),
        hga, hgb, hweq]
  simp only [hle23, ite_false] at hval
  by_cases h24 : (op == 24) = true
  · -- op = 24 (GETLSBD)
    simp only [h24, ite_true] at hval; have hop24 : op = 24 := beq_iff_eq.mp h24
    by_cases ha : a ≥ i
    · simp only [ha, ite_true] at hval; cases hval
    simp only [ha, ite_false, decide_eq_true_eq] at hval
    obtain ⟨ea, hga⟩ := hgetBv a (by omega) hval
    refine ⟨.bool (.literal (.getLsbD ea b)), fun n' hag => ?_,
      fun hlt => by unfold opEq at hlt; omega, fun _ => ⟨_, rfl⟩⟩
    show decodeNode vars cwords n' op w a b c = _
    simp [decodeNode, nat_blt_eq_decide, hop24, hw1, hag a (by omega), hga]
  simp only [h24, Bool.false_eq_true, ite_false] at hval
  by_cases h25 : (op == 25) = true
  · -- op = 25 (BCONST)
    simp only [h25, ite_true, decide_eq_true_eq] at hval
    have hop25 : op = 25 := beq_iff_eq.mp h25
    refine ⟨.bool (.const (Nat.beq a 1)), fun n' _ => ?_,
      fun hlt => by unfold opEq at hlt; omega, fun _ => ⟨_, rfl⟩⟩
    show decodeNode vars cwords n' op w a b c = _
    simp [decodeNode, nat_blt_eq_decide, hop25, hw1, hval]
  simp only [h25, Bool.false_eq_true, ite_false] at hval
  by_cases h26 : (op == 26) = true
  · -- op = 26 (BNOT)
    simp only [h26, ite_true] at hval; have hop26 : op = 26 := beq_iff_eq.mp h26
    by_cases ha : a ≥ i
    · simp only [ha, ite_true] at hval; cases hval
    simp only [ha, ite_false, decide_eq_true_eq] at hval
    obtain ⟨ea, hga⟩ := hgetBool a (by omega) hval
    refine ⟨.bool (.not ea), fun n' hag => ?_,
      fun hlt => by unfold opEq at hlt; omega, fun _ => ⟨_, rfl⟩⟩
    show decodeNode vars cwords n' op w a b c = _
    simp [decodeNode, nat_blt_eq_decide, hop26, hw1, hag a (by omega), hga]
  simp only [h26, Bool.false_eq_true, ite_false] at hval
  by_cases hle30 : op ≤ 30
  · -- ops 27..30 (gates)
    simp only [hle30, ite_true] at hval
    by_cases hab : (a ≥ i || b ≥ i) = true
    · simp only [hab, ite_true] at hval; cases hval
    simp only [hab, Bool.false_eq_true, ite_false, decide_eq_true_eq] at hval
    simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at hab
    obtain ⟨ea, hga⟩ := hgetBool a (by omega) hval.1
    obtain ⟨eb, hgb⟩ := hgetBool b (by omega) hval.2
    let g : Gate :=
      if op == 27 then .and else if op == 28 then .xor else if op == 29 then .beq else .or
    have hop_c : op = 27 ∨ op = 28 ∨ op = 29 ∨ op = 30 := by
      simp only [beq_iff_eq] at h24 h25 h26; omega
    refine ⟨.bool (.gate g ea eb), fun n' hag => ?_,
      fun hlt => by unfold opEq at hlt; omega, fun _ => ⟨_, rfl⟩⟩
    show decodeNode vars cwords n' op w a b c = _
    rcases hop_c with h | h | h | h <;>
      simp [decodeNode, mkGateNode, g, nat_blt_eq_decide, h, hw1, hag a (by omega),
        hag b (by omega), hga, hgb]
  · -- op = 31 (ITE)
    simp only [hle30, ite_false] at hval
    have hop31 : op = 31 := by omega
    by_cases habc : (a ≥ i || b ≥ i || c ≥ i) = true
    · simp only [habc, ite_true] at hval; cases hval
    simp only [habc, Bool.false_eq_true, ite_false, decide_eq_true_eq] at hval
    simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at habc
    obtain ⟨ea, hga⟩ := hgetBool a (by omega) hval.1
    obtain ⟨eb, hgb⟩ := hgetBool b (by omega) hval.2.1
    obtain ⟨ec, hgc⟩ := hgetBool c (by omega) hval.2.2
    refine ⟨.bool (.ite ea eb ec), fun n' hag => ?_,
      fun hlt => by unfold opEq at hlt; omega, fun _ => ⟨_, rfl⟩⟩
    show decodeNode vars cwords n' op w a b c = _
    simp [decodeNode, nat_blt_eq_decide, hop31, hw1, hag a (by omega), hag b (by omega),
      hag c (by omega), hga, hgb, hgc]

private theorem parseNodes_drop (bs : List UInt8) (ws : List Nat) (nv nc : Nat)
    (vars : BinTree VarEntry) (cwords : BinTree Nat)
    (hws : ∀ i < ws.length, ws[i]! = u32At bs i)
    (hvars : ∀ k < nv, vars.get? k = some ⟨u32At bs (8 + 2 * k), u32At bs (8 + 2 * k + 1)⟩)
    (hcw : ∀ j < nc, cwords.get? j = some (u32At bs (cwordsOff nv + j))) :
    ∀ n (idx : Nat) (acc : BinTree ProgNode),
      nodesOff nv nc + 5 * idx + 5 * n ≤ ws.length →
      idx + n < u32Bound →
      (∀ i < idx + n, validNodeAt bs nv nc i = true) →
      (∀ j < idx,
        let base := nodesOff nv nc + 5 * j
        ∃ nd : ProgNode,
          acc.get? j = some nd ∧
          (∀ n' : BinTree ProgNode, (∀ k < j, n'.get? k = acc.get? k) →
            decodeNode vars cwords n' (u32At bs base) (u32At bs (base + 1))
              (u32At bs (base + 2)) (u32At bs (base + 3)) (u32At bs (base + 4)) = some nd) ∧
          (u32At bs base < opEq → ∃ e, nd = .bv (u32At bs (base + 1)) e) ∧
          (opEq ≤ u32At bs base → ∃ e, nd = .bool e)) →
      ∃ nodes : BinTree ProgNode,
        parseNodes vars cwords n idx acc (ws.drop (nodesOff nv nc + 5 * idx)) =
          some (nodes, ws.drop (nodesOff nv nc + 5 * (idx + n))) ∧
        ∀ j < idx + n,
          let base := nodesOff nv nc + 5 * j
          ∃ nd : ProgNode,
            nodes.get? j = some nd ∧
            decodeNode vars cwords nodes (u32At bs base) (u32At bs (base + 1))
              (u32At bs (base + 2)) (u32At bs (base + 3)) (u32At bs (base + 4)) = some nd ∧
            (u32At bs base < opEq → ∃ e, nd = .bv (u32At bs (base + 1)) e) ∧
            (opEq ≤ u32At bs base → ∃ e, nd = .bool e) := by
  intro n
  induction n with
  | zero =>
    intro idx acc _ _ _ hacc
    refine ⟨acc, by simp [parseNodes], fun j hj => ?_⟩
    obtain ⟨nd, hg, hd, hbv, hbo⟩ := hacc j (by omega)
    exact ⟨nd, hg, hd acc (fun _ _ => rfl), hbv, hbo⟩
  | succ n ih =>
    intro idx acc hlen hlt hvals hacc
    have h0 : nodesOff nv nc + 5 * idx < ws.length := by omega
    have h1 : nodesOff nv nc + 5 * idx + 1 < ws.length := by omega
    have h2 : nodesOff nv nc + 5 * idx + 2 < ws.length := by omega
    have h3 : nodesOff nv nc + 5 * idx + 3 < ws.length := by omega
    have h4 : nodesOff nv nc + 5 * idx + 4 < ws.length := by omega
    have hdrop : ws.drop (nodesOff nv nc + 5 * idx) =
        ws[nodesOff nv nc + 5 * idx]! :: ws[nodesOff nv nc + 5 * idx + 1]! ::
        ws[nodesOff nv nc + 5 * idx + 2]! :: ws[nodesOff nv nc + 5 * idx + 3]! ::
        ws[nodesOff nv nc + 5 * idx + 4]! :: ws.drop (nodesOff nv nc + 5 * (idx + 1)) := by
      rw [List.drop_eq_getElem_cons h0, List.drop_eq_getElem_cons h1,
        List.drop_eq_getElem_cons h2, List.drop_eq_getElem_cons h3, List.drop_eq_getElem_cons h4]
      simp [getElem!_pos, h0, h1, h2, h3, h4,
        show nodesOff nv nc + 5 * idx + 1 + 1 + 1 + 1 + 1 =
          nodesOff nv nc + 5 * (idx + 1) by omega]
    rw [hdrop, hws _ h0, hws _ h1, hws _ h2, hws _ h3, hws _ h4]
    have hprev : ∀ j < idx, ∃ nd : ProgNode, acc.get? j = some nd ∧
        (u32At bs (nodesOff nv nc + 5 * j) < opEq →
          ∃ e, nd = .bv (u32At bs (nodesOff nv nc + 5 * j + 1)) e) ∧
        (opEq ≤ u32At bs (nodesOff nv nc + 5 * j) → ∃ e, nd = .bool e) := by
      intro j hj
      obtain ⟨nd, hg, _, hbv, hbo⟩ := hacc j hj
      exact ⟨nd, hg, hbv, hbo⟩
    obtain ⟨nd, hdec, hbv, hbo⟩ :=
      decodeNode_of_validNodeAt hvars hcw hprev (hvals idx (by omega))
    unfold parseNodes
    rw [isU32_u32At, isU32_u32At, isU32_u32At, isU32_u32At, isU32_u32At]
    simp only [Bool.and_self, hdec acc (fun _ _ => rfl)]
    let acc' := acc.insert idx nd
    have hagree : ∀ k < idx, acc'.get? k = acc.get? k := fun k hk =>
      radixTree_get?_insert_ne acc nd (by omega) (by omega) (by omega)
    have hacc' : ∀ j < idx + 1,
        let base := nodesOff nv nc + 5 * j
        ∃ nd' : ProgNode,
          acc'.get? j = some nd' ∧
          (∀ n' : BinTree ProgNode, (∀ k < j, n'.get? k = acc'.get? k) →
            decodeNode vars cwords n' (u32At bs base) (u32At bs (base + 1))
              (u32At bs (base + 2)) (u32At bs (base + 3)) (u32At bs (base + 4)) = some nd') ∧
          (u32At bs base < opEq → ∃ e, nd' = .bv (u32At bs (base + 1)) e) ∧
          (opEq ≤ u32At bs base → ∃ e, nd' = .bool e) := by
      intro j hj
      by_cases hje : j = idx
      · subst hje
        refine ⟨nd, radixTree_get?_insert_same acc nd (by omega), fun n' hn' => ?_, hbv, hbo⟩
        exact hdec n' (fun k hk => (hn' k hk).trans (hagree k hk))
      · have hltj : j < idx := by omega
        obtain ⟨nd0, hg0, hd0, hbv0, hbo0⟩ := hacc j hltj
        refine ⟨nd0, by rw [hagree j hltj]; exact hg0, fun n' hn' => ?_, hbv0, hbo0⟩
        exact hd0 n' (fun k hk => (hn' k hk).trans (hagree k (by omega)))
    obtain ⟨nodes, hp, hget⟩ := ih (idx + 1) acc' (by omega) (by omega)
      (fun i hi => hvals i (by omega)) hacc'
    exact ⟨nodes, by simpa [Nat.add_assoc, Nat.add_comm 1 n] using hp,
      fun j hj => hget j (by omega)⟩

/-- Main pure validation-to-parsing soundness theorem:
every `ValidBVP1 bs` byte stream parses via `BVProg.parse bs = some prog` with exact decoded
`vars`, `cwords`, `nodes` tables matching `u32At bs`. -/
theorem validBVP1_parse {bs : List UInt8} (hv : ValidBVP1 bs) :
    ∃ (vars : BinTree VarEntry) (cwords : BinTree Nat) (nodes : BinTree ProgNode)
      (prog : BVLogicalExpr), ParsedBVP1 bs vars cwords nodes prog := by
  obtain ⟨ws, hbw, hwlen, hws⟩ := bytesToWordsLE_of_mod4 bs hv.len_mod4
  have htot := hv.total_len
  let nv := u32At bs 2
  let nn := u32At bs 3
  let nc := u32At bs 4
  let rt := u32At bs 5
  have hws_len : ws.length = 8 + 2 * nv + nc + 5 * nn := by omega
  have hcons : ws = ws[0]! :: ws[1]! :: ws[2]! :: ws[3]! :: ws[4]! :: ws[5]! :: ws[6]! ::
      ws[7]! :: ws.drop 8 := by
    have hd : ∀ k (hk : k < ws.length), ws.drop k = ws[k]! :: ws.drop (k + 1) := by
      intro k hk; rw [List.drop_eq_getElem_cons hk]; simp [getElem!_pos, hk]
    have h0 := hd 0 (by omega)
    have h1 := hd 1 (by omega)
    have h2 := hd 2 (by omega)
    have h3 := hd 3 (by omega)
    have h4 := hd 4 (by omega)
    have h5 := hd 5 (by omega)
    have h6 := hd 6 (by omega)
    have h7 := hd 7 (by omega)
    rw [List.drop_zero] at h0
    conv => lhs; rw [h0, h1, h2, h3, h4, h5, h6, h7]
  obtain ⟨vars, hpv, hvars⟩ := parseVars_drop bs ws hws nv 0 .empty
    (by omega) (by simpa [nv] using u32At_lt bs 2) (fun k hk => by omega)
  obtain ⟨cwords, hpc, hcws⟩ := parseCwords_drop bs ws nv hws nc 0 .empty
    (by unfold cwordsOff; omega) (by simpa [nc] using u32At_lt bs 4) (fun j hj => by omega)
  have hvars' : ∀ k < nv, vars.get? k = some ⟨u32At bs (8 + 2 * k), u32At bs (8 + 2 * k + 1)⟩ :=
    fun k hk => hvars k (by omega)
  have hcws' : ∀ j < nc, cwords.get? j = some (u32At bs (cwordsOff nv + j)) :=
    fun j hj => hcws j (by omega)
  obtain ⟨nodes, hpn, hnodes⟩ :=
    parseNodes_drop bs ws nv nc vars cwords hws hvars' hcws' nn 0 .empty
      (by unfold nodesOff; omega) (by simpa [nn] using u32At_lt bs 3)
      (fun i hi => hv.nodes_ok i (by simpa [nn] using hi)) (fun j hj => by omega)
  obtain ⟨nd_rt, hrt_get, _, _, hrt_bool⟩ := hnodes rt (by simpa [nn, rt] using hv.root_lt)
  obtain ⟨prog, rfl⟩ := hrt_bool hv.root_bool
  have hparse : BVProg.parse bs = some prog := by
    unfold BVProg.parse
    rw [hbw]
    dsimp only
    rw [hcons]
    unfold BVProg.parseWords
    dsimp only
    rw [hws 0 (by omega), hws 1 (by omega), hws 2 (by omega), hws 3 (by omega),
      hws 4 (by omega), hws 5 (by omega), hws 6 (by omega), hws 7 (by omega)]
    rw [isU32_u32At, isU32_u32At, isU32_u32At, isU32_u32At, isU32_u32At, isU32_u32At,
      isU32_u32At, isU32_u32At]
    have hmag : Nat.beq (u32At bs 0) bvpMagic = true := by
      simp [hv.magic_eq, bvMagic, bvpMagic]
    have hver : Nat.beq (u32At bs 1) bvpVersion = true := by
      simp [hv.ver_eq, bvVersion, bvpVersion]
    have hnp : Nat.blt 0 (u32At bs 3) = true := Nat.blt_eq.mpr hv.nodes_pos
    have hrl : Nat.blt (u32At bs 5) (u32At bs 3) = true := Nat.blt_eq.mpr hv.root_lt
    simp only [hmag, hver, hnp, hrl, Bool.and_self]
    have hpv' : parseVars nv 0 .empty (ws.drop 8) = some (vars, ws.drop (cwordsOff nv)) := by
      simpa [cwordsOff] using hpv
    have hpc' : parseCwords nc 0 .empty (ws.drop (cwordsOff nv)) =
        some (cwords, ws.drop (nodesOff nv nc)) := by
      simpa [cwordsOff, nodesOff] using hpc
    have hpn' : parseNodes vars cwords nn 0 .empty (ws.drop (nodesOff nv nc)) =
        some (nodes, []) := by
      have hemp : ws.drop (nodesOff nv nc + 5 * (0 + nn)) = [] := by
        rw [List.drop_eq_nil_iff]; unfold nodesOff; omega
      rw [hemp] at hpn
      simpa using hpn
    change (match parseVars nv 0 .empty (ws.drop 8) with
      | some (vars, rest1) =>
        match parseCwords nc 0 .empty rest1 with
        | some (cwords, rest2) =>
          match parseNodes vars cwords nn 0 .empty rest2 with
          | some (nodes, []) =>
            match nodes.get? rt with
            | some (.bool e) => some e
            | _ => none
          | _ => none
        | none => none
      | none => none) = some prog
    simp only [hpv', hpc', hpn', hrt_get]
  exact ⟨vars, cwords, nodes, prog, hv, hparse, hvars', hcws',
    fun i hi => by simpa [nv, nn, nc] using hnodes i (by simpa [nn] using hi), hrt_get⟩

end

end LeanQbe.T.Examples.Bitblast.Proof
