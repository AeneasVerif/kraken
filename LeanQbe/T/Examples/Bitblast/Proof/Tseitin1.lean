/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Bitblast.Proof.Tseitin0
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import LeanQbe.T.Logic.ProofKit
import LeanQbe.T.Logic.MemLemmas
import LeanQbe.T.Logic.Bytes

/-!
# DIMACS Writer Helpers, AST Definitions, and Base WP Lemmas (`Bitblast.Proof.Tseitin1`)

Proves pure `Ref.Tseitin` / DIMACS / COI memory helpers, defines the C0 AST decomposition
and `CoiCtx` bundle for `bv_dimacs_write_body`, and proves `wp_root0Body` and call wrappers
used by `Bitblast.Proof.Tseitin`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Bitblast.Proof

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.ProofUtil LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofKit
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Bitblast.Src LeanQbe.T.Examples.Bitblast.Src.Tseitin
open LeanQbe.T.Examples.Bitblast.Ref LeanQbe.T.Examples.Bitblast.Ref.Tseitin

/-! ## 1. Pure `Ref.Tseitin`, DIMACS, and Memory Helpers -/

public section

theorem bv64_add_ofNat_toNat {a : BitVec 64} {n : Nat} (h : a.toNat + n < 2 ^ 64) :
    (a + BitVec.ofNat 64 n).toNat = a.toNat + n := by
  have := a.isLt
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : n < 2 ^ 64),
    Nat.mod_eq_of_lt h]

theorem litToDimacs_neg_out {n : Nat} (hn : n < 2 ^ 31) :
    litToDimacs (UInt32.ofBitVec ((BitVec.ofNat 32 n <<< (1 : BitVec 32)) ||| 1#32)) =
      (n + 1, false) := by
  unfold litToDimacs
  have hor : ((BitVec.ofNat 32 n <<< (1 : BitVec 32)) ||| 1#32).toNat = 2 * n + 1 := by
    rw [show BitVec.ofNat 32 n <<< (1 : BitVec 32) = BitVec.ofNat 32 n <<< 1 from rfl,
      bv_c0_toNat_shl1_or_one_of_le _ (by decide), BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : n < 2 ^ 32), Nat.mod_eq_of_lt (by omega : 2 * n + 1 < 2 ^ 32)]
  have h1 :
      (UInt32.ofBitVec ((BitVec.ofNat 32 n <<< (1 : BitVec 32)) ||| 1#32) >>> 1).toNat = n := by
    change (((BitVec.ofNat 32 n <<< (1 : BitVec 32)) ||| 1#32) >>> 1).toNat = n
    rw [BitVec.toNat_ushiftRight, hor, Nat.shiftRight_eq_div_pow, Nat.pow_one]; omega
  have h2 :
      (UInt32.ofBitVec ((BitVec.ofNat 32 n <<< (1 : BitVec 32)) ||| 1#32) &&& 1 == 0) = false := by
    rw [beq_eq_false_iff_ne]; intro hz
    have hbv := congrArg BitVec.toNat (congrArg UInt32.toBitVec hz)
    change (((BitVec.ofNat 32 n <<< (1 : BitVec 32)) ||| 1#32) &&& 1#32).toNat = 0 at hbv
    rw [bv_c0_toNat_and_one_32, hor] at hbv; omega
  rw [h1, h2]

theorem litToDimacs_pos_out {n : Nat} (hn : n < 2 ^ 31) :
    litToDimacs (UInt32.ofBitVec (BitVec.ofNat 32 n <<< (1 : BitVec 32))) = (n + 1, true) := by
  unfold litToDimacs
  have hshl : (BitVec.ofNat 32 n <<< (1 : BitVec 32)).toNat = 2 * n := by
    rw [show BitVec.ofNat 32 n <<< (1 : BitVec 32) = BitVec.ofNat 32 n <<< 1 from rfl,
      bv_c0_toNat_shiftLeft_nat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : n < 2 ^ 32),
      Nat.pow_one, Nat.mul_comm, Nat.mod_eq_of_lt (by omega : 2 * n < 2 ^ 32)]
  have h1 : (UInt32.ofBitVec (BitVec.ofNat 32 n <<< (1 : BitVec 32)) >>> 1).toNat = n := by
    change ((BitVec.ofNat 32 n <<< (1 : BitVec 32)) >>> 1).toNat = n
    rw [BitVec.toNat_ushiftRight, hshl, Nat.shiftRight_eq_div_pow, Nat.pow_one]; omega
  have h2 : (UInt32.ofBitVec (BitVec.ofNat 32 n <<< (1 : BitVec 32)) &&& 1 == 0) = true := by
    rw [beq_iff_eq]; apply UInt32.eq_of_toBitVec_eq; apply BitVec.eq_of_toNat_eq
    change ((BitVec.ofNat 32 n <<< (1 : BitVec 32)) &&& 1#32).toNat = 0
    rw [bv_c0_toNat_and_one_32, hshl]; omega
  rw [h1, h2]

theorem litToDimacs_xor1 (l : BitVec 32) :
    litToDimacs (UInt32.ofBitVec (l ^^^ 1#32)) =
      ((litToDimacs (UInt32.ofBitVec l)).1, !(litToDimacs (UInt32.ofBitVec l)).2) := by
  unfold litToDimacs
  have hsr : (l ^^^ 1#32) >>> (1 : BitVec 32) = l >>> (1 : BitVec 32) := by
    apply BitVec.eq_of_getLsbD_eq; intro i; simp [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_xor]
  have h1 : (UInt32.ofBitVec (l ^^^ 1#32) >>> 1).toNat = (UInt32.ofBitVec l >>> 1).toNat := by
    change ((l ^^^ 1#32) >>> (1 : BitVec 32)).toNat = (l >>> (1 : BitVec 32)).toNat; rw [hsr]
  have heqb : ∀ x : BitVec 32, ((UInt32.ofBitVec x &&& 1) == 0) = ((x &&& 1#32) == 0#32) := by
    intro x; by_cases hx : x &&& 1#32 = 0#32
    · have : UInt32.ofBitVec x &&& 1 = 0 := UInt32.eq_of_toBitVec_eq hx; simp [hx, this]
    · have hne : UInt32.ofBitVec x &&& 1 ≠ 0 := fun h => hx (congrArg UInt32.toBitVec h)
      rw [beq_eq_false_iff_ne.mpr hne]; exact (beq_eq_false_iff_ne.mpr hx).symm
  have hd : ((l ^^^ 1#32) &&& 1#32 == 0#32) = !((l &&& 1#32) == 0#32) := by
    have hxor : (l ^^^ 1#32) &&& 1#32 = (l &&& 1#32) ^^^ 1#32 := by
      apply BitVec.eq_of_getLsbD_eq; intro i
      simp [BitVec.getLsbD_and, BitVec.getLsbD_xor, Bool.and_xor_distrib_right]
    rw [hxor]; have ha : (l &&& 1#32).toNat ≤ 1 := by rw [bv_c0_toNat_and_one_32]; omega
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp ha with h | h
    · rw [BitVec.eq_of_toNat_eq (by simpa using h : (l &&& 1#32).toNat = (0#32).toNat)]; decide
    · rw [BitVec.eq_of_toNat_eq (by simpa using h : (l &&& 1#32).toNat = (1#32).toNat)]; decide
  rw [h1, heqb (l ^^^ 1#32), heqb l, hd]

@[expose] def clauseMaxVar (m : Nat) (cl : Std.Sat.CNF.Clause Nat) : Nat :=
  List.foldl (fun m' l => max m' l.1) m cl.literals

theorem foldl_max_init {α : Type} (f : α → Nat) (xs : List α) (m0 : Nat) :
    List.foldl (fun m x => max m (f x)) m0 xs =
      max m0 (List.foldl (fun m x => max m (f x)) 0 xs) := by
  induction xs generalizing m0 with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, Nat.zero_max]; rw [ih (max m0 (f x)), ih (f x)]; omega

theorem foldl_clauseMaxVar_init (cs : List (Std.Sat.CNF.Clause Nat)) (m0 : Nat) :
    List.foldl clauseMaxVar m0 cs = max m0 (List.foldl clauseMaxVar 0 cs) := by
  induction cs generalizing m0 with
  | nil => simp
  | cons cl cs ih =>
    have hc : clauseMaxVar m0 cl = max m0 (clauseMaxVar 0 cl) := by
      unfold clauseMaxVar; exact foldl_max_init (fun l => l.1) cl.literals m0
    simp only [List.foldl_cons]; rw [hc, ih (max m0 (clauseMaxVar 0 cl)), ih (clauseMaxVar 0 cl)]
    omega

theorem cnfMaxVar_eq_foldl (cnf : Std.Sat.CNF Nat) :
    cnfMaxVar cnf = List.foldl clauseMaxVar 0 cnf.clauses.toList := by
  unfold cnfMaxVar clauseMaxVar; rw [← Array.foldl_toList]

theorem clauses_foldl_add (init : Std.Sat.CNF Nat) (cs : List (Std.Sat.CNF.Clause Nat)) :
    (List.foldl Std.Sat.CNF.add init cs).clauses.toList = init.clauses.toList ++ cs := by
  induction cs generalizing init <;> simp [Std.Sat.CNF.add, List.append_assoc, *]

theorem cnfMaxVar_root0 (g : Aig) (marks : Array Bool) :
    cnfMaxVar (tseitin g marks (UInt32.ofBitVec 0#32)) = 0 := by
  have hroot : (UInt32.ofBitVec 0#32 == 0) = true := rfl
  simp only [tseitin, hroot, ↓reduceIte, cnfMaxVar_eq_foldl, Std.Sat.CNF.add, Std.Sat.CNF.empty,
    Array.toList_push, List.nil_append, List.foldl_cons, List.foldl_nil, clauseMaxVar,
    Std.Sat.CNF.Clause.literals_empty]

theorem encodeDimacs_root0 (g : Aig) (marks : Array Bool) :
    encodeDimacs (tseitin g marks (UInt32.ofBitVec 0#32)) =
      dimacsHeaderPrefix ++ natToBytes 0 ++ [asciiSpace] ++ natToBytes 1 ++
        [asciiNewline, asciiZero, asciiNewline] := by
  have hroot : (UInt32.ofBitVec 0#32 == 0) = true := rfl
  have hmax := cnfMaxVar_root0 g marks
  simp only [tseitin, hroot, ↓reduceIte] at hmax ⊢; rw [encodeDimacs, hmax]
  simp [Std.Sat.CNF.add, Std.Sat.CNF.empty, encodeDimacsClause, Std.Sat.CNF.Clause.literals_empty,
    List.append_assoc]

@[expose] def prefixClauses (g : Aig) (marks : Array Bool) (k : Nat) :
    List (Std.Sat.CNF.Clause Nat) :=
  (List.range k).flatMap fun i => if h : i < g.nodes.size then
    if marks.getD (g.A + 1 + i) false = true then
      gateClauses g i h else [] else []

theorem prefixClauses_succ (g : Aig) (marks : Array Bool) {k : Nat}
    (hk : k < g.nodes.size) :
    prefixClauses g marks (k + 1) = prefixClauses g marks k ++
      if marks.getD (g.A + 1 + k) false = true then
        gateClauses g k hk else [] := by
  unfold prefixClauses; rw [List.range_succ, List.flatMap_append]; simp [hk]

@[expose] def pass1Mv (g : Aig) (marks : Array Bool) (root : BitVec 32) (k : Nat) : Nat :=
  List.foldl clauseMaxVar ((root >>> 1).toNat + 1) (prefixClauses g marks k)
@[expose] def pass1Nc (g : Aig) (marks : Array Bool) (k : Nat) : Nat :=
  1 + (prefixClauses g marks k).length
@[expose] def pass1Bytes (g : Aig) (marks : Array Bool) (k : Nat) : List UInt8 :=
  (prefixClauses g marks k).flatMap encodeDimacsClause
@[expose] def pass1BodyBytes (g : Aig) (marks : Array Bool) (root : BitVec 32) (k : Nat) : Nat :=
  (encodeDimacsClause (Std.Sat.CNF.Clause.ofLiterals [litToDimacs (UInt32.ofBitVec root)])).length +
    (pass1Bytes g marks k).length

theorem encodeDimacsClause_ofLiterals (xs : List (Std.Sat.Literal Nat)) :
    encodeDimacsClause (Std.Sat.CNF.Clause.ofLiterals xs) =
      xs.flatMap encodeDimacsLit ++ [asciiZero, asciiNewline] := by
  unfold encodeDimacsClause; rw [Std.Sat.CNF.Clause.literals_ofLiterals]

theorem andClauses_flatMap_eq (outNode : Nat) (l1 l2 : UInt32) :
    (andClauses outNode l1 l2).flatMap encodeDimacsClause =
      (encodeDimacsLit (outNode + 1, false) ++ encodeDimacsLit (litToDimacs l1) ++
        [asciiZero, asciiNewline]) ++
      ((encodeDimacsLit (outNode + 1, false) ++ encodeDimacsLit (litToDimacs l2) ++
        [asciiZero, asciiNewline]) ++
      (encodeDimacsLit (outNode + 1, true) ++
        encodeDimacsLit (litToDimacs (UInt32.ofBitVec (l1.toBitVec ^^^ 1#32))) ++
        encodeDimacsLit (litToDimacs (UInt32.ofBitVec (l2.toBitVec ^^^ 1#32))) ++
        [asciiZero, asciiNewline])) := by
  have hx1 := litToDimacs_xor1 l1.toBitVec; have hx2 := litToDimacs_xor1 l2.toBitVec
  simp only [UInt32.ofBitVec_toBitVec] at hx1 hx2
  simp only [andClauses, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    encodeDimacsClause_ofLiterals, ← hx1, ← hx2, List.append_assoc]

theorem iteClauses_flatMap_eq (outNode : Nat) (c t f : UInt32) :
    (iteClauses outNode c t f).flatMap encodeDimacsClause =
      (encodeDimacsLit (litToDimacs (UInt32.ofBitVec (c.toBitVec ^^^ 1#32))) ++
        encodeDimacsLit (litToDimacs (UInt32.ofBitVec (t.toBitVec ^^^ 1#32))) ++
        encodeDimacsLit (outNode + 1, true) ++ [asciiZero, asciiNewline]) ++
      ((encodeDimacsLit (litToDimacs (UInt32.ofBitVec (c.toBitVec ^^^ 1#32))) ++
        encodeDimacsLit (litToDimacs t) ++
        encodeDimacsLit (outNode + 1, false) ++ [asciiZero, asciiNewline]) ++
      ((encodeDimacsLit (litToDimacs c) ++
        encodeDimacsLit (litToDimacs (UInt32.ofBitVec (f.toBitVec ^^^ 1#32))) ++
        encodeDimacsLit (outNode + 1, true) ++ [asciiZero, asciiNewline]) ++
      (encodeDimacsLit (litToDimacs c) ++
        encodeDimacsLit (litToDimacs f) ++
        encodeDimacsLit (outNode + 1, false) ++ [asciiZero, asciiNewline]))) := by
  have hxc := litToDimacs_xor1 c.toBitVec
  have hxt := litToDimacs_xor1 t.toBitVec
  have hxf := litToDimacs_xor1 f.toBitVec
  simp only [UInt32.ofBitVec_toBitVec] at hxc hxt hxf
  simp only [iteClauses, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    encodeDimacsClause_ofLiterals, ← hxc, ← hxt, ← hxf, List.append_assoc]

private theorem lit_pair_len (x : UInt32) :
    (encodeDimacsLit (litToDimacs x)).length +
      (encodeDimacsLit (litToDimacs (UInt32.ofBitVec (x.toBitVec ^^^ 1#32)))).length =
      2 * (natToBytes ((x >>> 1).toNat + 1)).length + 3 := by
  have h1 := encodeDimacsLit_length_bv x.toBitVec
  have h2 := encodeDimacsLit_length_bv (x.toBitVec ^^^ 1#32)
  simp only [UInt32.ofBitVec_toBitVec] at h1
  have hshr : ((x.toBitVec ^^^ 1#32) >>> 1).toNat = (x.toBitVec >>> 1).toNat :=
    bv_c0_toNat_xor_one_ushiftRight_32 x.toBitVec
  have ha1 : (x.toBitVec &&& 1#32).toNat = x.toBitVec.toNat % 2 :=
    bv_c0_toNat_and_one_32 x.toBitVec
  have ha2 : ((x.toBitVec ^^^ 1#32) &&& 1#32).toNat = (x.toBitVec ^^^ 1#32).toNat % 2 :=
    bv_c0_toNat_and_one_32 (x.toBitVec ^^^ 1#32)
  have hpar : (x.toBitVec &&& 1#32).toNat + ((x.toBitVec ^^^ 1#32) &&& 1#32).toNat = 1 := by
    have hxor : (x.toBitVec ^^^ 1#32) &&& 1#32 = (x.toBitVec &&& 1#32) ^^^ 1#32 := by
      apply BitVec.eq_of_getLsbD_eq; intro i
      simp [BitVec.getLsbD_and, BitVec.getLsbD_xor, Bool.and_xor_distrib_right]
    rw [hxor]
    have hle : (x.toBitVec &&& 1#32).toNat ≤ 1 := by omega
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle with hz | ho
    · have : x.toBitVec &&& 1#32 = 0#32 := BitVec.eq_of_toNat_eq (by simpa using hz)
      rw [this]; decide
    · have : x.toBitVec &&& 1#32 = 1#32 := BitVec.eq_of_toNat_eq (by simpa using ho)
      rw [this]; decide
  have hxshr : (x.toBitVec >>> 1).toNat = (x >>> 1).toNat := rfl
  rw [h1, h2, hshr, hxshr]; omega

theorem pass1_zero (g : Aig) (marks : Array Bool) (root : BitVec 32) :
    pass1Mv g marks root 0 = (root >>> 1).toNat + 1 ∧ pass1Nc g marks 0 = 1 ∧
      pass1Bytes g marks 0 = [] ∧ pass1BodyBytes g marks root 0 =
        (encodeDimacsLit (litToDimacs (UInt32.ofBitVec root))).length + 2 := by
  have hz : prefixClauses g marks 0 = [] := by simp [prefixClauses]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [pass1Mv, pass1Nc, pass1Bytes, pass1BodyBytes, hz, encodeDimacsClause_ofLiterals]

theorem pass1_succ_false (g : Aig) (marks : Array Bool) (root : BitVec 32) {k : Nat}
    (hk : k < g.nodes.size) (hf : marks.getD (g.A + 1 + k) false = false) :
    pass1Mv g marks root (k + 1) = pass1Mv g marks root k ∧
      pass1Nc g marks (k + 1) = pass1Nc g marks k ∧
      pass1Bytes g marks (k + 1) = pass1Bytes g marks k ∧
      pass1BodyBytes g marks root (k + 1) = pass1BodyBytes g marks root k := by
  have hp := prefixClauses_succ g marks hk
  simp only [hf, Bool.false_eq_true, ↓reduceIte, List.append_nil] at hp
  simp [pass1Mv, pass1Nc, pass1Bytes, pass1BodyBytes, hp]

theorem pass1_succ_true_and (g : Aig) (marks : Array Bool) (root : BitVec 32) {k : Nat}
    (hk : k < g.nodes.size) (ht : marks.getD (g.A + 1 + k) false = true)
    (hd : detectIte g k hk = none) :
    pass1Mv g marks root (k + 1) = max (max (max (pass1Mv g marks root k) (g.A + 1 + k + 1))
        (((g.nodes[k]'hk).1 >>> 1).toNat + 1)) (((g.nodes[k]'hk).2 >>> 1).toNat + 1) ∧
      pass1Nc g marks (k + 1) = pass1Nc g marks k + 3 ∧
      pass1Bytes g marks (k + 1) = pass1Bytes g marks k ++
        (andClauses (g.A + 1 + k) (g.nodes[k]'hk).1 (g.nodes[k]'hk).2).flatMap
          encodeDimacsClause ∧
      pass1BodyBytes g marks root (k + 1) = pass1BodyBytes g marks root k +
        ((natToBytes (g.A + 1 + k + 1)).length + 11 +
          (encodeDimacsLit (litToDimacs (g.nodes[k]'hk).1)).length +
          (encodeDimacsLit (litToDimacs (g.nodes[k]'hk).2)).length +
          (encodeDimacsLit (litToDimacs (UInt32.ofBitVec
            ((g.nodes[k]'hk).1.toBitVec ^^^ 1#32)))).length +
          (encodeDimacsLit (litToDimacs (UInt32.ofBitVec
            ((g.nodes[k]'hk).2.toBitVec ^^^ 1#32)))).length +
          2 * (natToBytes (g.A + 1 + k + 1)).length) := by
  have hp := prefixClauses_succ g marks hk
  simp only [ht, ↓reduceIte, gateClauses, hd] at hp
  have hbs : pass1Bytes g marks (k + 1) = pass1Bytes g marks k ++
      (andClauses (g.A + 1 + k) (g.nodes[k]'hk).1 (g.nodes[k]'hk).2).flatMap
        encodeDimacsClause := by unfold pass1Bytes; rw [hp, List.flatMap_append]
  have hlen : ((andClauses (g.A + 1 + k) (g.nodes[k]'hk).1 (g.nodes[k]'hk).2).flatMap
      encodeDimacsClause).length = (natToBytes (g.A + 1 + k + 1)).length + 11 +
        (encodeDimacsLit (litToDimacs (g.nodes[k]'hk).1)).length +
        (encodeDimacsLit (litToDimacs (g.nodes[k]'hk).2)).length +
        (encodeDimacsLit (litToDimacs (UInt32.ofBitVec
          ((g.nodes[k]'hk).1.toBitVec ^^^ 1#32)))).length +
        (encodeDimacsLit (litToDimacs (UInt32.ofBitVec
          ((g.nodes[k]'hk).2.toBitVec ^^^ 1#32)))).length +
        2 * (natToBytes (g.A + 1 + k + 1)).length := by
    rw [andClauses_flatMap_eq]; simp only [List.length_append, List.length_cons, List.length_nil]
    have hl1 : (encodeDimacsLit (g.A + 1 + k + 1, false)).length =
        (natToBytes (g.A + 1 + k + 1)).length + 2 := by
      simp [encodeDimacsLit, asciiMinus, asciiSpace]
    have hl2 : (encodeDimacsLit (g.A + 1 + k + 1, true)).length =
        (natToBytes (g.A + 1 + k + 1)).length + 1 := by simp [encodeDimacsLit, asciiSpace]
    rw [hl1, hl2]; omega
  refine ⟨?_, by unfold pass1Nc; rw [hp, List.length_append]; simp [andClauses, Nat.add_assoc],
    hbs, by unfold pass1BodyBytes; rw [hbs, List.length_append, hlen]; omega⟩
  unfold pass1Mv; rw [hp, List.foldl_append]
  simp only [andClauses, List.foldl_cons, List.foldl_nil, clauseMaxVar,
    Std.Sat.CNF.Clause.literals_ofLiterals]
  have hl1 : (litToDimacs (g.nodes[k]'hk).1).1 = ((g.nodes[k]'hk).1 >>> 1).toNat + 1 := rfl
  have hl2 : (litToDimacs (g.nodes[k]'hk).2).1 = ((g.nodes[k]'hk).2 >>> 1).toNat + 1 := rfl
  rw [hl1, hl2]
  change max (max (max (max (max (max (max (List.foldl clauseMaxVar _ (prefixClauses g marks k))
    (g.A + 1 + k + 1)) (((g.nodes[k]'hk).1 >>> 1).toNat + 1)) (g.A + 1 + k + 1))
    (((g.nodes[k]'hk).2 >>> 1).toNat + 1)) (g.A + 1 + k + 1))
    (((g.nodes[k]'hk).1 >>> 1).toNat + 1)) (((g.nodes[k]'hk).2 >>> 1).toNat + 1) = _; omega

theorem pass1_succ_true_ite (g : Aig) (marks : Array Bool) (root : BitVec 32) {k : Nat}
    (hk : k < g.nodes.size) (ht : marks.getD (g.A + 1 + k) false = true) {c t f : UInt32}
    (hd : detectIte g k hk = some (c, t, f)) :
    pass1Mv g marks root (k + 1) = max (max (max (max (pass1Mv g marks root k)
        (g.A + 1 + k + 1)) ((c >>> 1).toNat + 1)) ((t >>> 1).toNat + 1)) ((f >>> 1).toNat + 1) ∧
      pass1Nc g marks (k + 1) = pass1Nc g marks k + 4 ∧
      pass1Bytes g marks (k + 1) = pass1Bytes g marks k ++
        (iteClauses (g.A + 1 + k) c t f).flatMap encodeDimacsClause ∧
      pass1BodyBytes g marks root (k + 1) = pass1BodyBytes g marks root k +
        (4 * (natToBytes (g.A + 1 + k + 1)).length + 4 * (natToBytes ((c >>> 1).toNat + 1)).length +
          2 * (natToBytes ((t >>> 1).toNat + 1)).length +
          2 * (natToBytes ((f >>> 1).toNat + 1)).length + 26) := by
  have hp := prefixClauses_succ g marks hk
  simp only [ht, ↓reduceIte, gateClauses, hd] at hp
  have hbs : pass1Bytes g marks (k + 1) = pass1Bytes g marks k ++
      (iteClauses (g.A + 1 + k) c t f).flatMap encodeDimacsClause := by
    unfold pass1Bytes; rw [hp, List.flatMap_append]
  have hlen : ((iteClauses (g.A + 1 + k) c t f).flatMap encodeDimacsClause).length =
      4 * (natToBytes (g.A + 1 + k + 1)).length + 4 * (natToBytes ((c >>> 1).toNat + 1)).length +
        2 * (natToBytes ((t >>> 1).toNat + 1)).length +
        2 * (natToBytes ((f >>> 1).toNat + 1)).length + 26 := by
    rw [iteClauses_flatMap_eq]; simp only [List.length_append, List.length_cons, List.length_nil]
    have hl1 : (encodeDimacsLit (g.A + 1 + k + 1, false)).length =
        (natToBytes (g.A + 1 + k + 1)).length + 2 := by
      simp [encodeDimacsLit, asciiMinus, asciiSpace]
    have hl2 : (encodeDimacsLit (g.A + 1 + k + 1, true)).length =
        (natToBytes (g.A + 1 + k + 1)).length + 1 := by simp [encodeDimacsLit, asciiSpace]
    have hpc := lit_pair_len c; have hpt := lit_pair_len t; have hpf := lit_pair_len f
    rw [hl1, hl2]; omega
  refine ⟨?_, by unfold pass1Nc; rw [hp, List.length_append]; simp [iteClauses, Nat.add_assoc],
    hbs, by unfold pass1BodyBytes; rw [hbs, List.length_append, hlen]; omega⟩
  unfold pass1Mv; rw [hp, List.foldl_append]
  simp only [iteClauses, List.foldl_cons, List.foldl_nil, clauseMaxVar,
    Std.Sat.CNF.Clause.literals_ofLiterals]
  have hlc : (litToDimacs c).1 = (c >>> 1).toNat + 1 := rfl
  have hlt : (litToDimacs t).1 = (t >>> 1).toNat + 1 := rfl
  have hlf : (litToDimacs f).1 = (f >>> 1).toNat + 1 := rfl
  rw [hlc, hlt, hlf]
  change max (max (max (max (max (max (max (max (max (max (max (max
    (List.foldl clauseMaxVar _ (prefixClauses g marks k))
    ((c >>> 1).toNat + 1)) ((t >>> 1).toNat + 1)) (g.A + 1 + k + 1))
    ((c >>> 1).toNat + 1)) ((t >>> 1).toNat + 1)) (g.A + 1 + k + 1))
    ((c >>> 1).toNat + 1)) ((f >>> 1).toNat + 1)) (g.A + 1 + k + 1))
    ((c >>> 1).toNat + 1)) ((f >>> 1).toNat + 1)) (g.A + 1 + k + 1) = _
  have hdup (x u v w : Nat) :
      max (max (max (max (max (max x u) v) w) u) v) w = max (max (max x u) v) w := by
    have h1 : max (max (max (max x u) v) w) u = max (max (max x u) v) w := by omega
    have h2 : max (max (max (max x u) v) w) v = max (max (max x u) v) w := by omega
    rw [h1, h2]; omega
  rw [hdup, hdup]
  have hdrop (x u v w z : Nat) :
      max (max (max (max (max (max x u) v) w) u) z) w = max (max (max (max x w) u) v) z := by
    have h1 : max (max (max (max x u) v) w) u = max (max (max x u) v) w := by omega
    have h2 : max (max (max x u) v) w = max (max (max x w) u) v := by omega
    rw [h1, h2]; omega
  exact hdrop _ _ _ _ _

theorem pass1Bytes_len_mono {g : Aig} (marks : Array Bool) {root : BitVec 32}
    {k1 k2 : Nat} (hle : k1 ≤ k2) (hk2 : k2 ≤ g.nodes.size) :
    (pass1Bytes g marks k1).length ≤ (pass1Bytes g marks k2).length := by
  have hb : ∀ {a b : Nat}, a ≤ b → b ≤ g.nodes.size →
      pass1BodyBytes g marks root a ≤ pass1BodyBytes g marks root b := by
    intro a b hab hb_sz; induction b with
    | zero => simp [show a = 0 by omega]
    | succ k ih =>
      by_cases hlt : a ≤ k
      · have hs : pass1BodyBytes g marks root k ≤ pass1BodyBytes g marks root (k + 1) := by
          by_cases hm : marks.getD (g.A + 1 + k) false = true
          · cases hd : detectIte g k (by omega) with
            | none =>
              have ⟨_, _, _, h⟩ := pass1_succ_true_and g marks root (by omega) hm hd; omega
            | some ctf =>
              rcases ctf with ⟨c, t, f⟩
              have ⟨_, _, _, h⟩ := pass1_succ_true_ite g marks root (by omega) hm hd; omega
          · have ⟨_, _, _, h⟩ := pass1_succ_false g marks root (by omega)
              (Bool.eq_false_iff.mpr hm); omega
        exact Nat.le_trans (ih hlt (by omega)) hs
      · simp [show a = k + 1 by omega]
  have hm := hb hle hk2; unfold pass1BodyBytes at hm; omega

theorem pass1_end_eq (g : Aig) (marks : Array Bool) (root : BitVec 32)
    (hroot : root ≠ 0#32) :
    let cnf := tseitin g marks (UInt32.ofBitVec root)
    pass1Mv g marks root g.nodes.size = cnfMaxVar cnf ∧
      pass1Nc g marks g.nodes.size = cnf.clauses.size ∧
      8 + (natToBytes (pass1Mv g marks root g.nodes.size)).length +
          (natToBytes (pass1Nc g marks g.nodes.size)).length +
          pass1BodyBytes g marks root g.nodes.size = (encodeDimacs cnf).length ∧
      encodeDimacs cnf = dimacsHeaderPrefix ++ natToBytes (cnfMaxVar cnf) ++ [asciiSpace] ++
        natToBytes cnf.clauses.size ++ [asciiNewline] ++ pass1Bytes g marks g.nodes.size ++
        encodeDimacsClause
          (Std.Sat.CNF.Clause.ofLiterals [litToDimacs (UInt32.ofBitVec root)]) := by
  dsimp only
  have hne : (UInt32.ofBitVec root == 0) = false :=
    beq_eq_false_iff_ne.mpr fun hz => hroot (congrArg UInt32.toBitVec hz)
  have hclauses : (tseitin g marks (UInt32.ofBitVec root)).clauses.toList =
      tseitinClauses g marks ++
        [Std.Sat.CNF.Clause.ofLiterals [litToDimacs (UInt32.ofBitVec root)]] := by
    simp only [tseitin, hne, Bool.false_eq_true, ↓reduceIte, Std.Sat.CNF.add, Array.toList_push,
      clauses_foldl_add, Std.Sat.CNF.empty, List.nil_append]
  have hmv : pass1Mv g marks root g.nodes.size =
      cnfMaxVar (tseitin g marks (UInt32.ofBitVec root)) := by
    rw [cnfMaxVar_eq_foldl, hclauses, List.foldl_append, foldl_clauseMaxVar_init]
    simp only [List.foldl_cons, List.foldl_nil, clauseMaxVar,
      Std.Sat.CNF.Clause.literals_ofLiterals, Nat.zero_max]
    unfold pass1Mv; change List.foldl clauseMaxVar _ (tseitinClauses g marks) = _
    rw [foldl_clauseMaxVar_init]
    have hl1 : (litToDimacs (UInt32.ofBitVec root)).1 = (root >>> 1).toNat + 1 := rfl
    rw [hl1]; omega
  have hnc : pass1Nc g marks g.nodes.size =
      (tseitin g marks (UInt32.ofBitVec root)).clauses.size := by
    rw [← Array.length_toList (xs := (tseitin g marks (UInt32.ofBitVec root)).clauses),
      hclauses, List.length_append, List.length_singleton, Nat.add_comm]; rfl
  have henc : encodeDimacs (tseitin g marks (UInt32.ofBitVec root)) =
      dimacsHeaderPrefix ++ natToBytes (cnfMaxVar (tseitin g marks (UInt32.ofBitVec root))) ++
        [asciiSpace] ++ natToBytes (tseitin g marks (UInt32.ofBitVec root)).clauses.size ++
        [asciiNewline] ++ pass1Bytes g marks g.nodes.size ++
        encodeDimacsClause
          (Std.Sat.CNF.Clause.ofLiterals [litToDimacs (UInt32.ofBitVec root)]) := by
    unfold encodeDimacs pass1Bytes
    change _ = _ ++ _ ++ _ ++ _ ++ _ ++ (tseitinClauses g marks).flatMap encodeDimacsClause ++ _
    rw [hclauses, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    simp only [List.append_assoc]
  refine ⟨hmv, hnc, ?_, henc⟩
  rw [henc, hmv, hnc]; unfold pass1BodyBytes; simp [dimacsHeaderPrefix, List.length_append]; omega

theorem pass1BodyBytes_lt_pow64 {g : Aig} {marks : Array Bool} {root : BitVec 32}
    (hbd : g.A + 1 + g.nodes.size < bvDimacsBound) {k : Nat} :
    pass1BodyBytes g marks root k ≤ 14 + 40 * pass1Nc g marks k := by
  induction k with
  | zero => have hz := pass1_zero g marks root; have := encodeDimacsLit_length_le_bv root; omega
  | succ k ih =>
    by_cases hlt : k < g.nodes.size
    · by_cases hm : marks.getD (g.A + 1 + k) false = true
      · cases hd : detectIte g k hlt with
        | none =>
          have ⟨_, hnc, _, hbb⟩ := pass1_succ_true_and g marks root hlt hm hd
          have h0 := natToBytes_length_le_10
            (by unfold bvDimacsBound at hbd; omega : g.A + 1 + k + 1 < 2 ^ 32)
          have h1 := encodeDimacsLit_length_le_bv (g.nodes[k]'hlt).1.toBitVec
          have h2 := encodeDimacsLit_length_le_bv (g.nodes[k]'hlt).2.toBitVec
          have h3 := encodeDimacsLit_length_le_bv ((g.nodes[k]'hlt).1.toBitVec ^^^ 1#32)
          have h4 := encodeDimacsLit_length_le_bv ((g.nodes[k]'hlt).2.toBitVec ^^^ 1#32)
          simp only [UInt32.ofBitVec_toBitVec] at h1 h2; omega
        | some ctf =>
          rcases ctf with ⟨c, t, f⟩
          have ⟨_, hnc, _, hbb⟩ := pass1_succ_true_ite g marks root hlt hm hd
          have h0 := natToBytes_length_le_10
            (by unfold bvDimacsBound at hbd; omega : g.A + 1 + k + 1 < 2 ^ 32)
          have hc := natToBytes_length_le_10 (n := (c >>> 1).toNat + 1) (by
            have := c.toBitVec.isLt
            have : (c >>> 1).toNat = c.toBitVec.toNat / 2 := by
              change (c.toBitVec >>> (1 : Nat)).toNat = _
              rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.pow_one]
            omega)
          have ht := natToBytes_length_le_10 (n := (t >>> 1).toNat + 1) (by
            have := t.toBitVec.isLt
            have : (t >>> 1).toNat = t.toBitVec.toNat / 2 := by
              change (t.toBitVec >>> (1 : Nat)).toNat = _
              rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.pow_one]
            omega)
          have hf := natToBytes_length_le_10 (n := (f >>> 1).toNat + 1) (by
            have := f.toBitVec.isLt
            have : (f >>> 1).toNat = f.toBitVec.toNat / 2 := by
              change (f.toBitVec >>> (1 : Nat)).toNat = _
              rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.pow_one]
            omega)
          omega
      · have ⟨_, hnc, _, hbb⟩ := pass1_succ_false g marks root hlt (Bool.eq_false_iff.mpr hm); omega
    · have hp : prefixClauses g marks (k + 1) = prefixClauses g marks k := by
        unfold prefixClauses; rw [List.range_succ, List.flatMap_append]; simp [hlt]
      simp only [pass1BodyBytes, pass1Nc, pass1Bytes, hp] at ih ⊢; exact ih

theorem region_join_sub {a b : BitVec 64} {n : Nat}
    (hle : a.toNat ≤ b.toNat) (hb : b.toNat + n ≤ 2 ^ 64) :
    region a (b.toNat - a.toNat) ⋆ region b n = region a (b.toNat - a.toNat + n) := by
  have hptr : a + BitVec.ofNat 64 (b.toNat - a.toNat) = b :=
    BitVec.eq_of_toNat_eq (by rw [bv64_add_ofNat_toNat (by omega)]; omega)
  have := region_merge_eq (a := a) (n1 := b.toNat - a.toNat) (n2 := n) rfl (by omega)
  rwa [hptr] at this

theorem bvCoiTail_to_prefixRegion {workBase aigPtr marksPtr dimacsStart : BitVec 64}
    {avail : Nat} {hdr : BVHdrState} {aigUsed : List (BitVec 64)} {marks : List UInt8}
    {dbsLen : Nat} {R : Mem 64 → Prop} {m : Mem 64} (hfit : workBase.toNat + avail < 2 ^ 64)
    (hm_ge : marksPtr.toNat + marks.length ≤ dimacsStart.toNat)
    (hd_end : dimacsStart.toNat + dbsLen = workBase.toNat + avail)
    (hm : (bvCoiMem workBase aigPtr marksPtr avail hdr aigUsed marks ⋆ R) m) :
    (region dimacsStart dbsLen ⋆ (bvHdrMem workBase hdr ⋆
        region (workBase + 128#64) (aigPtr.toNat - (workBase.toNat + 128)) ⋆
        array64 aigPtr aigUsed ⋆ bytes marksPtr marks ⋆
        region (marksPtr + BitVec.ofNat 64 marks.length)
          (dimacsStart.toNat - (marksPtr.toNat + marks.length)) ⋆ R)) m := by
  unfold bvCoiMem at hm
  have hptr_eq := bv64_add_ofNat_toNat (a := marksPtr) (n := marks.length) (by omega)
  have hj := region_join_sub (a := marksPtr + BitVec.ofNat 64 marks.length) (b := dimacsStart)
    (n := dbsLen) (by omega) (by omega)
  rw [hptr_eq, show dimacsStart.toNat - (marksPtr.toNat + marks.length) + dbsLen =
    workBase.toNat + avail - (marksPtr.toNat + marks.length) by omega] at hj
  rw [← hj] at hm; exact sep_ac hm

theorem bvCoiMem_to_dimacsSep {workBase aigPtr marksPtr dimacsStart : BitVec 64}
    {avail : Nat} {hdr' : BVHdrState} {aigUsed : List (BitVec 64)} {marks dbs : List UInt8}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hfit : workBase.toNat + avail < 2 ^ 64) (haig_ge : workBase.toNat + 128 ≤ aigPtr.toNat)
    (hmptr : marksPtr = aigPtr + BitVec.ofNat 64 (8 * aigUsed.length))
    (haig_end : aigPtr.toNat + 8 * aigUsed.length ≤ workBase.toNat + avail)
    (hm_ge : marksPtr.toNat + marks.length ≤ dimacsStart.toNat)
    (hd_end : dimacsStart.toNat + dbs.length = workBase.toNat + avail)
    (hm : (bvHdrMem workBase hdr' ⋆
      region (workBase + 128#64) (aigPtr.toNat - (workBase.toNat + 128)) ⋆
      array64 aigPtr aigUsed ⋆ bytes marksPtr marks ⋆
      region (marksPtr + BitVec.ofNat 64 marks.length)
        (dimacsStart.toNat - (marksPtr.toNat + marks.length)) ⋆
      bytes dimacsStart dbs ⋆ R) m) :
    (bvHdrMem workBase hdr' ⋆
      region (workBase + 128#64) (dimacsStart.toNat - (workBase.toNat + 128)) ⋆
      bytes dimacsStart dbs ⋆ R) m := by
  have hmptr_nat : marksPtr.toNat = aigPtr.toNat + 8 * aigUsed.length := by
    rw [hmptr, bv64_add_ofNat_toNat (by omega)]
  have h128_nat : (workBase + 128#64).toNat = workBase.toNat + 128 :=
    bv64_add_ofNat_toNat (n := 128) (by omega)
  let F := region (workBase + 128#64) (aigPtr.toNat - (workBase.toNat + 128)) ⋆
    bvHdrMem workBase hdr' ⋆ bytes dimacsStart dbs ⋆ R
  have hm2 : (bytes marksPtr marks ⋆ (region aigPtr (8 * aigUsed.length) ⋆
      region (marksPtr + BitVec.ofNat 64 marks.length)
        (dimacsStart.toNat - (marksPtr.toNat + marks.length)) ⋆ F)) m :=
    sep_ac (sep_mono (P' := region aigPtr (8 * aigUsed.length))
      (fun _ h => array64_to_region (by omega) h)
      (by dsimp only [F]; exact sep_ac hm :
        (array64 aigPtr aigUsed ⋆ (bytes marksPtr marks ⋆ region (marksPtr + BitVec.ofNat 64
          marks.length) (dimacsStart.toNat - (marksPtr.toNat + marks.length)) ⋆ F)) m))
  have hm3 : ((region marksPtr marks.length ⋆ region (marksPtr + BitVec.ofNat 64 marks.length)
        (dimacsStart.toNat - (marksPtr.toNat + marks.length))) ⋆
      (region aigPtr (8 * aigUsed.length) ⋆ F)) m :=
    sep_ac (sep_mono (P' := region marksPtr marks.length) (fun _ h => bytes_to_region h) hm2)
  rw [region_merge_eq (a := marksPtr) (n1 := marks.length)
    (n2 := dimacsStart.toNat - (marksPtr.toNat + marks.length))
    (n := dimacsStart.toNat - marksPtr.toNat) (by omega) (by omega)] at hm3
  have hra := region_join_sub (a := aigPtr) (b := marksPtr)
    (n := dimacsStart.toNat - marksPtr.toNat) (by omega) (by omega)
  rw [show marksPtr.toNat - aigPtr.toNat + (dimacsStart.toNat - marksPtr.toNat) =
      dimacsStart.toNat - aigPtr.toNat by omega,
    show marksPtr.toNat - aigPtr.toNat = 8 * aigUsed.length by omega] at hra
  have hm4 : ((region aigPtr (8 * aigUsed.length) ⋆
      region marksPtr (dimacsStart.toNat - marksPtr.toNat)) ⋆ F) m := sep_ac hm3
  rw [hra] at hm4
  have hrw := region_join_sub (a := workBase + 128#64) (b := aigPtr)
    (n := dimacsStart.toNat - aigPtr.toNat) (by omega) (by omega)
  rw [h128_nat, show aigPtr.toNat - (workBase.toNat + 128) + (dimacsStart.toNat - aigPtr.toNat) =
    dimacsStart.toNat - (workBase.toNat + 128) by omega] at hrw
  have hm5 : ((region (workBase + 128#64) (aigPtr.toNat - (workBase.toNat + 128)) ⋆
      region aigPtr (dimacsStart.toNat - aigPtr.toNat)) ⋆
      (bvHdrMem workBase hdr' ⋆ bytes dimacsStart dbs ⋆ R)) m := by
    dsimp only [F] at hm4; exact sep_ac hm4
  rw [hrw] at hm5; exact sep_ac hm5

end

/-! ## 2. AST Decomposition -/

public section

@[expose] def oomRet {V L} (h : V i64) : Expr V L [Ty.bool] :=
  Expr.let_ ⟨OpCode.add i64, (Arg.var h, Arg.imm 120#64, ())⟩ fun p1 =>
  Expr.store (t := i32) (Arg.imm 1#32) (Arg.var p1.1) (
  Expr.let_ ⟨OpCode.add i64, (Arg.var h, Arg.imm 72#64, ())⟩ fun p2 =>
  Expr.store (t := i64) (Arg.imm 0#64) (Arg.var p2.1) (
  Expr.let_ ⟨OpCode.add i64, (Arg.var h, Arg.imm 124#64, ())⟩ fun p3 =>
  Expr.store (t := i32) (Arg.imm 0#32) (Arg.var p3.1)
    (Expr.ret (Arg.imm (t := Ty.bool) false, ()))))

@[expose] def root0Body {V L} (h : V i64) : Expr V L [Ty.bool] :=
  Expr.load i64 (Arg.var h) fun wb =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var wb, Arg.imm 128#64, ())⟩ fun floor0 =>
  Expr.group (sig := [[]]) (fun _ => Blocks.cons (fun _ => oomRet h) Blocks.nil) fun Js =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var h, Arg.imm 8#64, ())⟩ fun p =>
  Expr.load i64 (Arg.var p.1) fun we1 =>
  Expr.let_ ⟨OpCode.cmp CmpOp.ult i64 Ty.bool rfl, (Arg.var we1, Arg.var floor0.1, ())⟩ fun c1 =>
  Expr.jnz (Arg.var c1.1) (Expr.jump Js.1 ()) (
  Expr.let_ ⟨OpCode.add i64, (Arg.var h, Arg.imm 8#64, ())⟩ fun p =>
  Expr.load i64 (Arg.var p.1) fun we2 =>
  Expr.let_ ⟨OpCode.sub i64, (Arg.var we2, Arg.var floor0.1, ())⟩ fun rem =>
  Expr.let_ ⟨OpCode.cmp CmpOp.ugt i64 Ty.bool rfl, (Arg.imm 12#64, Arg.var rem.1, ())⟩ fun c2 =>
  Expr.jnz (Arg.var c2.1) (Expr.jump Js.1 ()) (
  Expr.let_ ⟨OpCode.add i64, (Arg.var h, Arg.imm 8#64, ())⟩ fun p =>
  Expr.load i64 (Arg.var p.1) fun we3 =>
  Expr.let_ ⟨OpCode.sub i64, (Arg.var we3, Arg.imm 12#64, ())⟩ fun start0 =>
  Expr.call (as := [i64, i32, i32]) (bs := [i64]) "bv_write_dimacs_hdr"
    (Arg.var start0.1, Arg.imm 0#32, Arg.imm 1#32, ()) fun p10 =>
  Expr.call (as := [i64]) (bs := [i64]) "bv_write_clause_end" (Arg.var p10.1, ()) fun _ =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var h, Arg.imm 72#64, ())⟩ fun p1 =>
  Expr.store (t := i64) (Arg.var start0.1) (Arg.var p1.1) (
  Expr.let_ ⟨OpCode.add i64, (Arg.var h, Arg.imm 124#64, ())⟩ fun p2 =>
  Expr.store (t := i32) (Arg.imm 12#32) (Arg.var p2.1)
    (Expr.ret (Arg.imm (t := Ty.bool) true, ())))))

@[expose] def maxUpdate {V L} (a b : V i32) (k : V i32 → Expr V L [Ty.bool]) :
    Expr V L [Ty.bool] :=
  Expr.group (sig := [[i32]]) (fun _ => Blocks.cons (fun p => k p.1) Blocks.nil) fun Js =>
  Expr.let_ ⟨OpCode.cmp CmpOp.ugt i32 Ty.bool rfl, (Arg.var a, Arg.var b, ())⟩ fun c =>
  Expr.jnz (Arg.var c.1) (Expr.jump Js.1 (Arg.var a, ())) (Expr.jump Js.1 (Arg.var b, ()))

@[expose] def pass1GateStep {V L} (h aigPtr : V i64) (A mv nc : V i32) (bb : V i64) (g idx : V i32)
    (aigWord : V i64) (onDone : V i32 → V i32 → V i64 → V i32 → Expr V L [Ty.bool]) :
    Expr V L [Ty.bool] :=
  Expr.let_ ⟨OpCode.and i64, (Arg.var aigWord, Arg.imm 4294967295#64, ())⟩ fun p27 =>
  Expr.let_ ⟨OpCode.trunc 64 32, (Arg.var p27.1, ())⟩ fun lhs =>
  Expr.let_ ⟨OpCode.sext 32 64, (Arg.imm 32#32, ())⟩ fun s32 =>
  Expr.let_ ⟨OpCode.lshr i64, (Arg.var aigWord, Arg.var s32.1, ())⟩ fun p30 =>
  Expr.let_ ⟨OpCode.trunc 64 32, (Arg.var p30.1, ())⟩ fun rhs =>
  detectIteExpr aigPtr A lhs.1 rhs.1 fun det =>
  let isIte := det.1; let ic := det.2.1; let it := det.2.2.1; let if_ := det.2.2.2.1
  Expr.let_ ⟨OpCode.add i32, (Arg.var idx, Arg.imm 1#32, ())⟩ fun gv =>
  maxUpdate gv.1 mv fun mv1 =>
  Expr.group (sig := [[i32, i32, i64]])
    (fun _ => Blocks.cons (fun st' => onDone st'.1 st'.2.1 st'.2.2.1 g) Blocks.nil) fun JsB =>
  Expr.let_ ⟨OpCode.cmp CmpOp.ne i32 Ty.bool rfl, (Arg.var isIte, Arg.imm 0#32, ())⟩ fun cIte =>
  Expr.jnz (Arg.var cIte.1)
    (Expr.let_ ⟨OpCode.lshr i32, (Arg.var ic, Arg.imm 1#32, ())⟩ fun c1 =>
    Expr.let_ ⟨OpCode.add i32, (Arg.var c1.1, Arg.imm 1#32, ())⟩ fun cv =>
    Expr.let_ ⟨OpCode.lshr i32, (Arg.var it, Arg.imm 1#32, ())⟩ fun t1 =>
    Expr.let_ ⟨OpCode.add i32, (Arg.var t1.1, Arg.imm 1#32, ())⟩ fun tv =>
    Expr.let_ ⟨OpCode.lshr i32, (Arg.var if_, Arg.imm 1#32, ())⟩ fun f1 =>
    Expr.let_ ⟨OpCode.add i32, (Arg.var f1.1, Arg.imm 1#32, ())⟩ fun fv =>
    maxUpdate cv.1 mv1 fun mv2 => maxUpdate tv.1 mv2 fun mv3 => maxUpdate fv.1 mv3 fun mv4 =>
    Expr.group (sig := [[]]) (fun _ => Blocks.cons (fun _ => oomRet h) Blocks.nil) fun Js4 =>
    Expr.let_ ⟨OpCode.zext 32 64, (Arg.var mv4, ())⟩ fun p =>
    Expr.let_ ⟨OpCode.cmp CmpOp.uge i64 Ty.bool rfl,
      (Arg.var p.1, Arg.imm 268435456#64, ())⟩ fun o1 =>
    Expr.jnz (Arg.var o1.1) (Expr.jump Js4.1 ()) (
    Expr.let_ ⟨OpCode.zext 32 64, (Arg.var nc, ())⟩ fun p =>
    Expr.let_ ⟨OpCode.sub i64, (Arg.imm 268435456#64, Arg.imm 4#64, ())⟩ fun p40 =>
    Expr.let_ ⟨OpCode.cmp CmpOp.uge i64 Ty.bool rfl, (Arg.var p.1, Arg.var p40.1, ())⟩ fun o2 =>
    Expr.jnz (Arg.var o2.1) (Expr.jump Js4.1 ()) (
    Expr.let_ ⟨OpCode.add i32, (Arg.var nc, Arg.imm 4#32, ())⟩ fun nc1 =>
    Expr.call (as := [i32]) (bs := [i64]) "bv_dec_len" (Arg.var gv.1, ()) fun do1 =>
    Expr.let_ ⟨OpCode.sext 32 64, (Arg.imm 2#32, ())⟩ fun s2a =>
    Expr.let_ ⟨OpCode.shl i64, (Arg.var do1.1, Arg.var s2a.1, ())⟩ fun do4 =>
    Expr.let_ ⟨OpCode.add i64, (Arg.var bb, Arg.var do4.1, ())⟩ fun bb1 =>
    Expr.call (as := [i32]) (bs := [i64]) "bv_dec_len" (Arg.var cv.1, ()) fun dc1 =>
    Expr.let_ ⟨OpCode.sext 32 64, (Arg.imm 2#32, ())⟩ fun s2b =>
    Expr.let_ ⟨OpCode.shl i64, (Arg.var dc1.1, Arg.var s2b.1, ())⟩ fun dc4 =>
    Expr.let_ ⟨OpCode.add i64, (Arg.var bb1.1, Arg.var dc4.1, ())⟩ fun bb2 =>
    Expr.call (as := [i32]) (bs := [i64]) "bv_dec_len" (Arg.var tv.1, ()) fun dt1 =>
    Expr.let_ ⟨OpCode.sext 32 64, (Arg.imm 1#32, ())⟩ fun s1a =>
    Expr.let_ ⟨OpCode.shl i64, (Arg.var dt1.1, Arg.var s1a.1, ())⟩ fun dt2 =>
    Expr.let_ ⟨OpCode.add i64, (Arg.var bb2.1, Arg.var dt2.1, ())⟩ fun bb3 =>
    Expr.call (as := [i32]) (bs := [i64]) "bv_dec_len" (Arg.var fv.1, ()) fun df1 =>
    Expr.let_ ⟨OpCode.sext 32 64, (Arg.imm 1#32, ())⟩ fun s1b =>
    Expr.let_ ⟨OpCode.shl i64, (Arg.var df1.1, Arg.var s1b.1, ())⟩ fun df2 =>
    Expr.let_ ⟨OpCode.add i64, (Arg.var bb3.1, Arg.var df2.1, ())⟩ fun bb4 =>
    Expr.let_ ⟨OpCode.add i64, (Arg.var bb4.1, Arg.imm 26#64, ())⟩ fun bb5 =>
    Expr.jump JsB.1 (Arg.var mv4, Arg.var nc1.1, Arg.var bb5.1, ()))))
    (Expr.let_ ⟨OpCode.lshr i32, (Arg.var lhs.1, Arg.imm 1#32, ())⟩ fun p33 =>
    Expr.let_ ⟨OpCode.add i32, (Arg.var p33.1, Arg.imm 1#32, ())⟩ fun lv =>
    Expr.let_ ⟨OpCode.lshr i32, (Arg.var rhs.1, Arg.imm 1#32, ())⟩ fun p35 =>
    Expr.let_ ⟨OpCode.add i32, (Arg.var p35.1, Arg.imm 1#32, ())⟩ fun rv =>
    maxUpdate lv.1 mv1 fun mv2 => maxUpdate rv.1 mv2 fun mv3 =>
    Expr.group (sig := [[]]) (fun _ => Blocks.cons (fun _ => oomRet h) Blocks.nil) fun Js4 =>
    Expr.let_ ⟨OpCode.zext 32 64, (Arg.var mv3, ())⟩ fun p =>
    Expr.let_ ⟨OpCode.cmp CmpOp.uge i64 Ty.bool rfl,
      (Arg.var p.1, Arg.imm 268435456#64, ())⟩ fun c1 =>
    Expr.jnz (Arg.var c1.1) (Expr.jump Js4.1 ()) (
    Expr.let_ ⟨OpCode.zext 32 64, (Arg.var nc, ())⟩ fun p =>
    Expr.let_ ⟨OpCode.sub i64, (Arg.imm 268435456#64, Arg.imm 3#64, ())⟩ fun p40 =>
    Expr.let_ ⟨OpCode.cmp CmpOp.uge i64 Ty.bool rfl, (Arg.var p.1, Arg.var p40.1, ())⟩ fun c2 =>
    Expr.jnz (Arg.var c2.1) (Expr.jump Js4.1 ()) (
    Expr.let_ ⟨OpCode.add i32, (Arg.var nc, Arg.imm 3#32, ())⟩ fun nc1 =>
    Expr.call (as := [i32]) (bs := [i64]) "bv_dec_len" (Arg.var gv.1, ()) fun dl =>
    Expr.let_ ⟨OpCode.add i64, (Arg.var dl.1, Arg.imm 2#64, ())⟩ fun p42 =>
    Expr.call (as := [i32]) (bs := [i64]) "bv_lit_bytes" (Arg.var lhs.1, ()) fun bl =>
    Expr.let_ ⟨OpCode.add i64, (Arg.var p42.1, Arg.var bl.1, ())⟩ fun p44 =>
    Expr.let_ ⟨OpCode.add i64, (Arg.var p44.1, Arg.imm 2#64, ())⟩ fun p45 =>
    Expr.let_ ⟨OpCode.add i64, (Arg.var bb, Arg.var p45.1, ())⟩ fun bb1 =>
    Expr.let_ ⟨OpCode.add i64, (Arg.var dl.1, Arg.imm 2#64, ())⟩ fun p47 =>
    Expr.call (as := [i32]) (bs := [i64]) "bv_lit_bytes" (Arg.var rhs.1, ()) fun br =>
    Expr.let_ ⟨OpCode.add i64, (Arg.var p47.1, Arg.var br.1, ())⟩ fun p49 =>
    Expr.let_ ⟨OpCode.add i64, (Arg.var p49.1, Arg.imm 2#64, ())⟩ fun p50 =>
    Expr.let_ ⟨OpCode.add i64, (Arg.var bb1.1, Arg.var p50.1, ())⟩ fun bb2 =>
    Expr.let_ ⟨OpCode.add i64, (Arg.var dl.1, Arg.imm 1#64, ())⟩ fun p52 =>
    Expr.let_ ⟨OpCode.xor i32, (Arg.var lhs.1, Arg.imm 1#32, ())⟩ fun nl =>
    Expr.call (as := [i32]) (bs := [i64]) "bv_lit_bytes" (Arg.var nl.1, ()) fun bnl =>
    Expr.let_ ⟨OpCode.add i64, (Arg.var p52.1, Arg.var bnl.1, ())⟩ fun p55 =>
    Expr.let_ ⟨OpCode.xor i32, (Arg.var rhs.1, Arg.imm 1#32, ())⟩ fun nr =>
    Expr.call (as := [i32]) (bs := [i64]) "bv_lit_bytes" (Arg.var nr.1, ()) fun bnr =>
    Expr.let_ ⟨OpCode.add i64, (Arg.var p55.1, Arg.var bnr.1, ())⟩ fun p58 =>
    Expr.let_ ⟨OpCode.add i64, (Arg.var p58.1, Arg.imm 2#64, ())⟩ fun p59 =>
    Expr.let_ ⟨OpCode.add i64, (Arg.var bb2.1, Arg.var p59.1, ())⟩ fun bb3 =>
    Expr.jump JsB.1 (Arg.var mv3, Arg.var nc1.1, Arg.var bb3.1, ()))))

@[expose] def pass2GateStep {V L} (aigPtr : V i64) (A g : V i32) (p : V i64) (aigWord : V i64)
    (onDone : V i64 → Expr V L [Ty.bool]) : Expr V L [Ty.bool] :=
  Expr.let_ ⟨OpCode.and i64, (Arg.var aigWord, Arg.imm 4294967295#64, ())⟩ fun p27 =>
  Expr.let_ ⟨OpCode.trunc 64 32, (Arg.var p27.1, ())⟩ fun lhs =>
  Expr.let_ ⟨OpCode.sext 32 64, (Arg.imm 32#32, ())⟩ fun s32 =>
  Expr.let_ ⟨OpCode.lshr i64, (Arg.var aigWord, Arg.var s32.1, ())⟩ fun p40 =>
  Expr.let_ ⟨OpCode.trunc 64 32, (Arg.var p40.1, ())⟩ fun rhs =>
  detectIteExpr aigPtr A lhs.1 rhs.1 fun det =>
  let isIte := det.1; let ic := det.2.1; let it := det.2.2.1; let if_ := det.2.2.2.1
  Expr.let_ ⟨OpCode.shl i32, (Arg.var g, Arg.imm 1#32, ())⟩ fun out0 =>
  Expr.let_ ⟨OpCode.or i32, (Arg.var out0.1, Arg.imm 1#32, ())⟩ fun out1 =>
  Expr.group (sig := [[i64]])
    (fun _ => Blocks.cons (fun np => onDone np.1) Blocks.nil) fun JsB =>
  Expr.let_ ⟨OpCode.cmp CmpOp.ne i32 Ty.bool rfl, (Arg.var isIte, Arg.imm 0#32, ())⟩ fun cIte =>
  Expr.jnz (Arg.var cIte.1)
    (Expr.let_ ⟨OpCode.xor i32, (Arg.var ic, Arg.imm 1#32, ())⟩ fun nc =>
    Expr.let_ ⟨OpCode.xor i32, (Arg.var it, Arg.imm 1#32, ())⟩ fun nt =>
    Expr.let_ ⟨OpCode.xor i32, (Arg.var if_, Arg.imm 1#32, ())⟩ fun nf =>
    Expr.call (as := [i64, i32]) (bs := [i64]) "bv_write_lit"
      (Arg.var p, Arg.var nc.1, ()) fun p1 =>
    Expr.call (as := [i64, i32]) (bs := [i64]) "bv_write_lit"
      (Arg.var p1.1, Arg.var nt.1, ()) fun p2 =>
    Expr.call (as := [i64, i32]) (bs := [i64]) "bv_write_lit"
      (Arg.var p2.1, Arg.var out0.1, ()) fun p3 =>
    Expr.call (as := [i64]) (bs := [i64]) "bv_write_clause_end" (Arg.var p3.1, ()) fun p4 =>
    Expr.call (as := [i64, i32]) (bs := [i64]) "bv_write_lit"
      (Arg.var p4.1, Arg.var nc.1, ()) fun p5 =>
    Expr.call (as := [i64, i32]) (bs := [i64]) "bv_write_lit"
      (Arg.var p5.1, Arg.var it, ()) fun p6 =>
    Expr.call (as := [i64, i32]) (bs := [i64]) "bv_write_lit"
      (Arg.var p6.1, Arg.var out1.1, ()) fun p7 =>
    Expr.call (as := [i64]) (bs := [i64]) "bv_write_clause_end" (Arg.var p7.1, ()) fun p8 =>
    Expr.call (as := [i64, i32]) (bs := [i64]) "bv_write_lit"
      (Arg.var p8.1, Arg.var ic, ()) fun p9 =>
    Expr.call (as := [i64, i32]) (bs := [i64]) "bv_write_lit"
      (Arg.var p9.1, Arg.var nf.1, ()) fun p10 =>
    Expr.call (as := [i64, i32]) (bs := [i64]) "bv_write_lit"
      (Arg.var p10.1, Arg.var out0.1, ()) fun p11 =>
    Expr.call (as := [i64]) (bs := [i64]) "bv_write_clause_end" (Arg.var p11.1, ()) fun p12 =>
    Expr.call (as := [i64, i32]) (bs := [i64]) "bv_write_lit"
      (Arg.var p12.1, Arg.var ic, ()) fun p13 =>
    Expr.call (as := [i64, i32]) (bs := [i64]) "bv_write_lit"
      (Arg.var p13.1, Arg.var if_, ()) fun p14 =>
    Expr.call (as := [i64, i32]) (bs := [i64]) "bv_write_lit"
      (Arg.var p14.1, Arg.var out1.1, ()) fun p15 =>
    Expr.call (as := [i64]) (bs := [i64]) "bv_write_clause_end" (Arg.var p15.1, ()) fun p16 =>
    Expr.jump JsB.1 (Arg.var p16.1, ()))
    (Expr.call (as := [i64, i32]) (bs := [i64]) "bv_write_lit"
      (Arg.var p, Arg.var out1.1, ()) fun p1 =>
    Expr.call (as := [i64, i32]) (bs := [i64]) "bv_write_lit"
      (Arg.var p1.1, Arg.var lhs.1, ()) fun p2 =>
    Expr.call (as := [i64]) (bs := [i64]) "bv_write_clause_end" (Arg.var p2.1, ()) fun p3 =>
    Expr.call (as := [i64, i32]) (bs := [i64]) "bv_write_lit"
      (Arg.var p3.1, Arg.var out1.1, ()) fun p4 =>
    Expr.call (as := [i64, i32]) (bs := [i64]) "bv_write_lit"
      (Arg.var p4.1, Arg.var rhs.1, ()) fun p5 =>
    Expr.call (as := [i64]) (bs := [i64]) "bv_write_clause_end" (Arg.var p5.1, ()) fun p6 =>
    Expr.call (as := [i64, i32]) (bs := [i64]) "bv_write_lit"
      (Arg.var p6.1, Arg.var out0.1, ()) fun p7 =>
    Expr.let_ ⟨OpCode.xor i32, (Arg.var lhs.1, Arg.imm 1#32, ())⟩ fun nl =>
    Expr.call (as := [i64, i32]) (bs := [i64]) "bv_write_lit"
      (Arg.var p7.1, Arg.var nl.1, ()) fun p8 =>
    Expr.let_ ⟨OpCode.xor i32, (Arg.var rhs.1, Arg.imm 1#32, ())⟩ fun nr =>
    Expr.call (as := [i64, i32]) (bs := [i64]) "bv_write_lit"
      (Arg.var p8.1, Arg.var nr.1, ()) fun p9 =>
    Expr.call (as := [i64]) (bs := [i64]) "bv_write_clause_end" (Arg.var p9.1, ()) fun p10 =>
    Expr.jump JsB.1 (Arg.var p10.1, ()))

@[expose] def pass2Expr {V L} (A aigLen : V i32) (marksPtr aigPtr : V i64)
    (initG : V i32) (initP : V i64) (kDone : V i64 → Expr V L [Ty.bool]) : Expr V L [Ty.bool] :=
  Expr.group (sig := [[i32, i64]]) (fun Js => Blocks.cons (fun st =>
    let g := st.1; let curP := st.2.1
    Expr.let_ ⟨OpCode.cmp CmpOp.ult i32 Ty.bool rfl, (Arg.var g, Arg.var aigLen, ())⟩ fun c =>
    Expr.jnz (Arg.var c.1)
      (Expr.group (sig := [[i64]]) (fun _ => Blocks.cons (fun np =>
        Expr.let_ ⟨OpCode.add i32, (Arg.var g, Arg.imm 1#32, ())⟩ fun g1 =>
        Expr.jump Js.1 (Arg.var g1.1, Arg.var np.1, ())) Blocks.nil) fun Js1 =>
      Expr.let_ ⟨OpCode.zext 32 64, (Arg.var g, ())⟩ fun g64 =>
      Expr.let_ ⟨OpCode.add i64, (Arg.var marksPtr, Arg.var g64.1, ())⟩ fun mp =>
      Expr.load i8 (Arg.var mp.1) fun mv =>
      Expr.let_ ⟨OpCode.trunc 32 8, (Arg.imm 0#32, ())⟩ fun z8 =>
      Expr.let_ ⟨OpCode.zext 8 32, (Arg.var mv, ())⟩ fun mv32 =>
      Expr.let_ ⟨OpCode.zext 8 32, (Arg.var z8.1, ())⟩ fun z32 =>
      Expr.let_ ⟨OpCode.cmp CmpOp.ne i32 Ty.bool rfl,
        (Arg.var mv32.1, Arg.var z32.1, ())⟩ fun nz =>
      Expr.jnz (Arg.var nz.1)
        (Expr.let_ ⟨OpCode.zext 32 64, (Arg.var g, ())⟩ fun g64' =>
        Expr.let_ ⟨OpCode.mul i64, (Arg.var g64'.1, Arg.imm 8#64, ())⟩ fun off =>
        Expr.let_ ⟨OpCode.add i64, (Arg.var aigPtr, Arg.var off.1, ())⟩ fun ap =>
        Expr.load i64 (Arg.var ap.1) fun aw =>
        pass2GateStep aigPtr A g curP aw fun np => Expr.jump Js1.1 (Arg.var np, ()))
        (Expr.jump Js1.1 (Arg.var curP, ())))
      (kDone curP)) Blocks.nil) (fun Js => Expr.jump Js.1 (Arg.var initG, Arg.var initP, ()))

@[expose] def pass1Expr {V L} (h : V i64) (A aigLen : V i32) (marksPtr aigPtr : V i64)
    (mv0 : V i32) (bb0 : V i64) (g0 : V i32)
    (kExit : V i32 → V i32 → V i64 → Expr V L [Ty.bool]) : Expr V L [Ty.bool] :=
  Expr.group (sig := [[i32, i32, i64, i32]]) (fun Js => Blocks.cons (fun st =>
    let mv := st.1; let nc := st.2.1; let bb := st.2.2.1; let g := st.2.2.2.1
    Expr.let_ ⟨OpCode.cmp CmpOp.ult i32 Ty.bool rfl, (Arg.var g, Arg.var aigLen, ())⟩ fun c =>
    Expr.jnz (Arg.var c.1)
      (Expr.group (sig := [[i32, i32, i64]]) (fun _ => Blocks.cons (fun st' =>
        Expr.let_ ⟨OpCode.add i32, (Arg.var g, Arg.imm 1#32, ())⟩ fun g1 =>
        Expr.jump Js.1 (Arg.var st'.1, Arg.var st'.2.1, Arg.var st'.2.2.1,
          Arg.var g1.1, ())) Blocks.nil) fun Js1 =>
      Expr.let_ ⟨OpCode.zext 32 64, (Arg.var g, ())⟩ fun g64 =>
      Expr.let_ ⟨OpCode.add i64, (Arg.var marksPtr, Arg.var g64.1, ())⟩ fun mp =>
      Expr.load i8 (Arg.var mp.1) fun mvByte =>
      Expr.let_ ⟨OpCode.trunc 32 8, (Arg.imm 0#32, ())⟩ fun z8 =>
      Expr.let_ ⟨OpCode.zext 8 32, (Arg.var mvByte, ())⟩ fun mv32 =>
      Expr.let_ ⟨OpCode.zext 8 32, (Arg.var z8.1, ())⟩ fun z32 =>
      Expr.let_ ⟨OpCode.cmp CmpOp.ne i32 Ty.bool rfl,
        (Arg.var mv32.1, Arg.var z32.1, ())⟩ fun nz =>
      Expr.jnz (Arg.var nz.1)
        (Expr.let_ ⟨OpCode.zext 32 64, (Arg.var g, ())⟩ fun g64' =>
        Expr.let_ ⟨OpCode.mul i64, (Arg.var g64'.1, Arg.imm 8#64, ())⟩ fun off =>
        Expr.let_ ⟨OpCode.add i64, (Arg.var aigPtr, Arg.var off.1, ())⟩ fun ap =>
        Expr.load i64 (Arg.var ap.1) fun aw =>
        pass1GateStep h aigPtr A mv nc bb g g aw fun mv' nc' bb' _ =>
          Expr.jump Js1.1 (Arg.var mv', Arg.var nc', Arg.var bb', ()))
        (Expr.jump Js1.1 (Arg.var mv, Arg.var nc, Arg.var bb, ())))
      (kExit mv nc bb)) Blocks.nil)
    (fun Js => Expr.jump Js.1 (Arg.var mv0, Arg.imm 1#32, Arg.var bb0, Arg.var g0, ()))

@[expose] def postPass1Expr {V L} (h : V i64) (root len A : V i32) (marksPtr aigPtr : V i64)
    (mv nc : V i32) (bb : V i64) : Expr V L [Ty.bool] :=
  Expr.call (as := [i32]) (bs := [i64]) "bv_dec_len" (Arg.var mv, ()) fun dmv =>
  Expr.let_ ⟨OpCode.add i64, (Arg.imm 8#64, Arg.var dmv.1, ())⟩ fun t1 =>
  Expr.call (as := [i32]) (bs := [i64]) "bv_dec_len" (Arg.var nc, ()) fun dnc =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var t1.1, Arg.var dnc.1, ())⟩ fun hdrBytes =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var hdrBytes.1, Arg.var bb, ())⟩ fun tot =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var h, Arg.imm 64#64, ())⟩ fun p =>
  Expr.load i64 (Arg.var p.1) fun mp =>
  Expr.let_ ⟨OpCode.zext 32 64, (Arg.var len, ())⟩ fun len64 =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var mp, Arg.var len64.1, ())⟩ fun floorPtr =>
  Expr.group (sig := [[]]) (fun _ => Blocks.cons (fun _ => oomRet h) Blocks.nil) fun Js =>
  Expr.let_ ⟨OpCode.cmp CmpOp.ugt i64 Ty.bool rfl,
    (Arg.var tot.1, Arg.imm 4294967295#64, ())⟩ fun c1 =>
  Expr.jnz (Arg.var c1.1) (Expr.jump Js.1 ()) (
  Expr.let_ ⟨OpCode.add i64, (Arg.var h, Arg.imm 8#64, ())⟩ fun p =>
  Expr.load i64 (Arg.var p.1) fun we1 =>
  Expr.let_ ⟨OpCode.cmp CmpOp.ult i64 Ty.bool rfl,
    (Arg.var we1, Arg.var floorPtr.1, ())⟩ fun c2 =>
  Expr.jnz (Arg.var c2.1) (Expr.jump Js.1 ()) (
  Expr.let_ ⟨OpCode.add i64, (Arg.var h, Arg.imm 8#64, ())⟩ fun p =>
  Expr.load i64 (Arg.var p.1) fun we2 =>
  Expr.let_ ⟨OpCode.sub i64, (Arg.var we2, Arg.var floorPtr.1, ())⟩ fun rem =>
  Expr.let_ ⟨OpCode.cmp CmpOp.ugt i64 Ty.bool rfl, (Arg.var tot.1, Arg.var rem.1, ())⟩ fun c3 =>
  Expr.jnz (Arg.var c3.1) (Expr.jump Js.1 ()) (
  Expr.let_ ⟨OpCode.add i64, (Arg.var h, Arg.imm 8#64, ())⟩ fun p =>
  Expr.load i64 (Arg.var p.1) fun we3 =>
  Expr.let_ ⟨OpCode.sub i64, (Arg.var we3, Arg.var tot.1, ())⟩ fun start =>
  Expr.call (as := [i64, i32, i32]) (bs := [i64]) "bv_write_dimacs_hdr"
    (Arg.var start.1, Arg.var mv, Arg.var nc, ()) fun p0 =>
  Expr.let_ ⟨OpCode.add i32, (Arg.var A, Arg.imm 1#32, ())⟩ fun g0 =>
  pass2Expr A len marksPtr aigPtr g0.1 p0.1 fun pAfter =>
  Expr.call (as := [i64, i32]) (bs := [i64]) "bv_write_lit"
    (Arg.var pAfter, Arg.var root, ()) fun pRoot =>
  Expr.call (as := [i64]) (bs := [i64]) "bv_write_clause_end" (Arg.var pRoot.1, ()) fun _ =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var h, Arg.imm 72#64, ())⟩ fun p1 =>
  Expr.store (t := i64) (Arg.var start.1) (Arg.var p1.1) (
  Expr.let_ ⟨OpCode.trunc 64 32, (Arg.var tot.1, ())⟩ fun tot32 =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var h, Arg.imm 124#64, ())⟩ fun p2 =>
  Expr.store (t := i32) (Arg.var tot32.1) (Arg.var p2.1)
    (Expr.ret (Arg.imm (t := Ty.bool) true, ()))))))

@[expose] def topBody {V L} (h : V i64) (root : V i32) : Expr V L [Ty.bool] :=
  Expr.let_ ⟨OpCode.cmp CmpOp.eq i32 Ty.bool rfl, (Arg.var root, Arg.imm 0#32, ())⟩ fun c0 =>
  Expr.jnz (Arg.var c0.1) (root0Body h) (
  Expr.let_ ⟨OpCode.add i64, (Arg.var h, Arg.imm 100#64, ())⟩ fun p =>
  Expr.load i32 (Arg.var p.1) fun len =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var h, Arg.imm 96#64, ())⟩ fun p =>
  Expr.load i32 (Arg.var p.1) fun A =>
  Expr.group (sig := [[]]) (fun _ => Blocks.cons (fun _ => oomRet h) Blocks.nil) fun Js =>
  Expr.let_ ⟨OpCode.cmp CmpOp.ule i32 Ty.bool rfl, (Arg.var len, Arg.var A, ())⟩ fun c1 =>
  Expr.jnz (Arg.var c1.1) (Expr.jump Js.1 ()) (
  Expr.let_ ⟨OpCode.add i64, (Arg.var h, Arg.imm 64#64, ())⟩ fun p =>
  Expr.load i64 (Arg.var p.1) fun mp1 =>
  Expr.let_ ⟨OpCode.cmp CmpOp.eq i64 Ty.bool rfl, (Arg.var mp1, Arg.imm 0#64, ())⟩ fun c2 =>
  Expr.jnz (Arg.var c2.1) (Expr.jump Js.1 ()) (
  Expr.let_ ⟨OpCode.add i64, (Arg.var h, Arg.imm 64#64, ())⟩ fun p =>
  Expr.load i64 (Arg.var p.1) fun marksPtr =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var h, Arg.imm 24#64, ())⟩ fun p =>
  Expr.load i64 (Arg.var p.1) fun aigPtr =>
  Expr.let_ ⟨OpCode.lshr i32, (Arg.var root, Arg.imm 1#32, ())⟩ fun r1 =>
  Expr.let_ ⟨OpCode.add i32, (Arg.var r1.1, Arg.imm 1#32, ())⟩ fun mv0 =>
  Expr.let_ ⟨OpCode.zext 32 64, (Arg.var mv0.1, ())⟩ fun mv64 =>
  Expr.let_ ⟨OpCode.cmp CmpOp.uge i64 Ty.bool rfl,
    (Arg.var mv64.1, Arg.imm 268435456#64, ())⟩ fun c3 =>
  Expr.jnz (Arg.var c3.1) (oomRet h)
    (Expr.call (as := [i32]) (bs := [i64]) "bv_lit_bytes" (Arg.var root, ()) fun br =>
    Expr.let_ ⟨OpCode.add i64, (Arg.var br.1, Arg.imm 2#64, ())⟩ fun bb0 =>
    Expr.let_ ⟨OpCode.add i32, (Arg.var A, Arg.imm 1#32, ())⟩ fun g0 =>
    pass1Expr h A len marksPtr aigPtr mv0.1 bb0.1 g0.1
      (postPass1Expr h root len A marksPtr aigPtr)))))

theorem bv_dimacs_write_eq_topBody (V : Ty → Type) (L : List Ty → Type)
    (h : V i64) (root : V i32) :
    (bv_dimacs_write_body V L (h, root, ()) : Expr V L [Ty.bool]) = topBody h root := rfl

/-! ## 3. Context Bundle and Base WP Helpers (`wp_root0Body`, Call Wrappers) -/

structure CoiCtx where
  workBase : BitVec 64
  aigPtr : BitVec 64
  marksPtr : BitVec 64
  avail : Nat
  hdr : BVHdrState
  g : Aig
  aigUsed : List (BitVec 64)
  marks : List UInt8
  fit : workBase.toNat + avail < 2 ^ 64
  wb : hdr.work_base = workBase
  we : hdr.work_end = workBase + BitVec.ofNat 64 avail
  aig_hdr : hdr.aig_ptr = aigPtr
  marks_hdr : hdr.marks_ptr = marksPtr
  aig_ge : workBase.toNat + 128 ≤ aigPtr.toNat
  marks_eq : marksPtr = aigPtr + BitVec.ofNat 64 (8 * aigUsed.length)
  aig_end : aigPtr.toNat + 8 * aigUsed.length + marks.length ≤ workBase.toNat + avail
  wf : g.Wf
  num_atoms : hdr.num_atoms.toNat = g.A
  aig_len : hdr.aig_len.toNat = g.A + 1 + g.nodes.size
  bd : hdr.aig_len.toNat < bvDimacsBound
  aig_w : AigWordsMatch g aigUsed
  aig_l : aigUsed.length = hdr.aig_len.toNat
  marks_l : marks.length = hdr.aig_len.toNat
  marks_ne : marksPtr ≠ 0#64

theorem CoiCtx.mptr_nat (c : CoiCtx) :
    c.marksPtr.toNat = c.aigPtr.toNat + 8 * c.aigUsed.length := by
  have := c.fit; have := c.aig_end; rw [c.marks_eq, bv64_add_ofNat_toNat (by omega)]
theorem CoiCtx.marks_ub (c : CoiCtx) :
    c.marksPtr.toNat + c.marks.length ≤ c.workBase.toNat + c.avail := by
  rw [c.mptr_nat]; exact c.aig_end
theorem CoiCtx.we_nat (c : CoiCtx) : c.hdr.work_end.toNat = c.workBase.toNat + c.avail := by
  have := c.fit; rw [c.we, bv64_add_ofNat_toNat (by omega)]
theorem CoiCtx.add128_nat (c : CoiCtx) :
    (c.workBase + 128#64).toNat = c.workBase.toNat + 128 := by
  have := c.fit; have := c.aig_ge; exact bv64_add_ofNat_toNat (n := 128) (by omega)
theorem CoiCtx.fl_nat (c : CoiCtx) :
    (c.hdr.marks_ptr + c.hdr.aig_len.setWidth 64).toNat = c.marksPtr.toNat + c.marks.length := by
  have := c.fit; have := c.marks_ub; have := c.hdr.aig_len.isLt; have := c.marks_l
  rw [c.marks_hdr, BitVec.toNat_add, BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt (by omega : c.hdr.aig_len.toNat < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : c.marksPtr.toNat + c.hdr.aig_len.toNat < 2 ^ 64), c.marks_l]
theorem CoiCtx.bd_nat (c : CoiCtx) : c.g.A + 1 + c.g.nodes.size < bvDimacsBound := by
  rw [← c.aig_len]; exact c.bd
theorem CoiCtx.g0_bv (c : CoiCtx) :
    c.hdr.num_atoms + 1#32 = BitVec.ofNat 32 (c.g.A + 1) := by
  apply BitVec.eq_of_toNat_eq; have := c.bd; have := c.aig_len; unfold bvDimacsBound at this
  rw [BitVec.toNat_add, c.num_atoms, show (1#32 : BitVec 32).toNat = 1 from rfl,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
theorem CoiCtx.hdrRegion (c : CoiCtx) {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (bvCoiMem c.workBase c.aigPtr c.marksPtr c.avail c.hdr c.aigUsed c.marks ⋆ R) m) :
    (bvHdrMem c.workBase c.hdr ⋆ region (c.workBase + 128#64) (c.avail - 128) ⋆ R) m :=
  sep_ac (sep_mono (P' := bvHdrMem c.workBase c.hdr ⋆ region (c.workBase + 128#64) (c.avail - 128))
    (fun _ hc => bvCoiMem_to_hdrRegion c.fit c.aig_ge c.marks_eq c.marks_ub
      (by have := c.aig_ge; have := c.aig_end; omega) hc) hm)

abbrev coiCoreMem (c : CoiCtx) (hdr : BVHdrState) (endNat : Nat) : Mem 64 → Prop :=
  bvHdrMem c.workBase hdr ⋆ region (c.workBase + 128#64)
    (c.aigPtr.toNat - (c.workBase.toNat + 128)) ⋆ array64 c.aigPtr c.aigUsed ⋆
    bytes c.marksPtr c.marks ⋆ region (c.marksPtr + BitVec.ofNat 64 c.marks.length)
    (endNat - (c.marksPtr.toNat + c.marks.length))
abbrev coiRestMem (c : CoiCtx) (hdr : BVHdrState) (endNat : Nat) : Mem 64 → Prop :=
  bvHdrMem c.workBase hdr ⋆ region (c.workBase + 128#64)
    (c.aigPtr.toNat - (c.workBase.toNat + 128)) ⋆ region (c.marksPtr + BitVec.ofNat 64
    c.marks.length) (endNat - (c.marksPtr.toNat + c.marks.length))
abbrev tseitinCnf (c : CoiCtx) (root : BitVec 32) : Std.Sat.CNF Nat :=
  tseitin c.g (marksToBool c.marks) (UInt32.ofBitVec root)
abbrev p1Bytes (c : CoiCtx) (k : Nat) : List UInt8 :=
  pass1Bytes c.g (marksToBool c.marks) k
abbrev bufAt (base : BitVec 64) (bs : List UInt8) (rem : Nat) (R : Mem 64 → Prop)
    (m : Mem 64) : Prop :=
  (region (base + BitVec.ofNat 64 bs.length) rem ⋆ (bytes base bs ⋆ R)) m
abbrev HypDecLen (Γ : Env) :=
  ∀ xs m Q X, bvDecLenSpec xs m Q X → Γ "bv_dec_len" [i32] [i64] xs m Q X
abbrev HypLitBytes (Γ : Env) :=
  ∀ xs m Q X, bvLitBytesSpec xs m Q X → Γ "bv_lit_bytes" [i32] [i64] xs m Q X
abbrev HypWriteLit (Γ : Env) :=
  ∀ xs m Q X, bvWriteLitSpec xs m Q X → Γ "bv_write_lit" [i64, i32] [i64] xs m Q X
abbrev HypWriteHdr (Γ : Env) :=
  ∀ xs m Q X, bvWriteDimacsHdrSpec xs m Q X → Γ "bv_write_dimacs_hdr" [i64, i32, i32] [i64] xs m Q X
abbrev HypWriteEnd (Γ : Env) :=
  ∀ xs m Q X, bvWriteClauseEndSpec xs m Q X → Γ "bv_write_clause_end" [i64] [i64] xs m Q X
abbrev HypOom (c : CoiCtx) (R : Mem 64 → Prop) (Q : Post [Ty.bool]) : Prop :=
  ∀ (hdr' : BVHdrState) (m' : Mem 64),
    (bvHdrMem c.workBase hdr' ⋆ region (c.workBase + 128#64) (c.avail - 128) ⋆ R) m' →
    Q (false, PUnit.unit) m'

theorem bv64_tot_toNat {a b : Nat} {bb : BitVec 64} (hbd : 8 + a + b + bb.toNat < 2 ^ 64) :
    (8#64 + BitVec.ofNat 64 a + BitVec.ofNat 64 b + bb).toNat = 8 + a + b + bb.toNat := by
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : 8 < 2 ^ 64), Nat.mod_eq_of_lt (by omega : a < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : 8 + a < 2 ^ 64), Nat.mod_eq_of_lt (by omega : b < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : 8 + a + b < 2 ^ 64), Nat.mod_eq_of_lt hbd]

theorem bufAt_rem {base : BitVec 64} {pref : List UInt8} {r1 r2 : Nat}
    {R : Mem 64 → Prop} {m : Mem 64} (h : r1 = r2) (hm : bufAt base pref r1 R m) :
    bufAt base pref r2 R m := h ▸ hm

theorem buf_append_step {base : BitVec 64} {pref bs : List UInt8} {rem : Nat}
    {R : Mem 64 → Prop} {m' : Mem 64}
    (hfit : base.toNat + (pref.length + bs.length + rem) < 2 ^ 64)
    (hm' : (bytes (base + BitVec.ofNat 64 pref.length) bs ⋆
      region (base + BitVec.ofNat 64 pref.length + BitVec.ofNat 64 bs.length) rem ⋆
      bytes base pref ⋆ R) m') :
    bufAt base (pref ++ bs) rem R m' := by
  have hl : (pref ++ bs).length = pref.length + bs.length := List.length_append
  have ha : (region (base + BitVec.ofNat 64 pref.length + BitVec.ofNat 64 bs.length) rem ⋆
      ((bytes base pref ⋆ bytes (base + BitVec.ofNat 64 pref.length) bs) ⋆ R)) m' := sep_ac hm'
  rwa [ptr_add_ofNat, ← hl, bytes_append_merge (by omega)] at ha

abbrev DimacsPost (c : CoiCtx) (root : BitVec 32) (R : Mem 64 → Prop)
    (Q : Post [Ty.bool]) : Prop :=
  ∀ (ret : Bool) (hdr' : BVHdrState) (m' : Mem 64),
    (ret = true → ValidDimacsCnf (tseitinCnf c root) ∧
      hdr'.dimacs_start.toNat + (encodeDimacs (tseitinCnf c root)).length =
        c.workBase.toNat + c.avail ∧
      hdr'.dimacs_len.toNat = (encodeDimacs (tseitinCnf c root)).length ∧
      c.workBase.toNat + 128 ≤ hdr'.dimacs_start.toNat ∧
      (bvHdrMem c.workBase hdr' ⋆ region (c.workBase + 128#64)
        (hdr'.dimacs_start.toNat - (c.workBase.toNat + 128)) ⋆
        bytes hdr'.dimacs_start (encodeDimacs (tseitinCnf c root)) ⋆ R) m' →
      Q (true, PUnit.unit) m') ∧
    (ret = false → (bvHdrMem c.workBase hdr' ⋆ region (c.workBase + 128#64) (c.avail - 128) ⋆
      R) m' → Q (false, PUnit.unit) m')

theorem wp_coiOomRet (Γ : Env) (Q : Post [Ty.bool]) (X : XPost) (c : CoiCtx)
    (R : Mem 64 → Prop) (m : Mem 64)
    (hm : (bvCoiMem c.workBase c.aigPtr c.marksPtr c.avail c.hdr c.aigUsed c.marks ⋆ R) m)
    (hQ : HypOom c R Q) : wp Γ Q X (oomRet c.workBase) m := by
  have hh := c.hdrRegion hm; clear hm; unfold oomRet; c0_hsteps!; exact hQ _ m (sep_ac hm)

theorem wp_decLen_call (Γ : Env) (hDecLen : HypDecLen Γ) {Q : Post [Ty.bool]} {X : XPost}
    (v : Val i32) (m : Mem 64) (k : Tup Val [i64] → Expr Val Cont [Ty.bool])
    (hk : wp Γ Q X (k (BitVec.ofNat 64 (natToBytes v.toNat).length, ())) m) :
    wp Γ Q X (Expr.call (as := [i32]) (bs := [i64]) "bv_dec_len" (Arg.var v, ()) k) m := by
  c0_call hDecLen; unfold bvDecLenSpec; exact hk

theorem wp_litBytes_call (Γ : Env) (hLitBytes : HypLitBytes Γ)
    {Q : Post [Ty.bool]} {X : XPost} (v : Val i32) (m : Mem 64)
    (k : Tup Val [i64] → Expr Val Cont [Ty.bool])
    (hk : wp Γ Q X
      (k (BitVec.ofNat 64 (encodeDimacsLit (litToDimacs (UInt32.ofBitVec v))).length, ())) m) :
    wp Γ Q X (Expr.call (as := [i32]) (bs := [i64]) "bv_lit_bytes" (Arg.var v, ()) k) m := by
  c0_call hLitBytes; unfold bvLitBytesSpec; exact hk

theorem wp_root0Body (Γ : Env) (hWriteHdr : HypWriteHdr Γ) (hWriteEnd : HypWriteEnd Γ)
    (Q : Post [Ty.bool]) (X : XPost) (c : CoiCtx) (R : Mem 64 → Prop) (m : Mem 64)
    (hm : (bvCoiMem c.workBase c.aigPtr c.marksPtr c.avail c.hdr c.aigUsed c.marks ⋆ R) m)
    (hQ : DimacsPost c 0#32 R Q) : wp Γ Q X (root0Body c.workBase) m := by
  have hm_hdr := c.hdrRegion hm
  have hfl0 : (c.hdr.work_base + 128#64).toNat = c.workBase.toNat + 128 := by
    rw [c.wb]; exact c.add128_nat
  have hwe := c.we_nat; have h128 := c.add128_nat; have hfit := c.fit
  unfold root0Body; c0_hsteps_nogrp
  refine wp_join0 (fun ml => ml = m) (fun _ _ hml => hml ▸ wp_coiOomRet Γ Q X c R m hm
    (fun hdr' m' => (hQ false hdr' m').2 rfl)) fun _ hJ => ?_
  clear hm; c0_hsteps_nogrp
  · exact hJ m rfl
  · exact hJ m rfl
  · rename_i hc1; clear hc1
    have h128_le : c.workBase.toNat + 128 ≤ c.workBase.toNat + c.avail := by
      have := c.aig_ge; have := c.aig_end; omega
    rw [c.wb, hwe, Nat.mod_eq_of_lt (by omega : c.workBase.toNat + 128 < 2 ^ 64),
      Nat.mod_eq_of_lt (by decide : 12 < 2 ^ 64),
      show 2 ^ 64 - (c.workBase.toNat + 128) + (c.workBase.toNat + c.avail) =
        2 ^ 64 + (c.avail - 128) by omega,
      Nat.add_mod_left, Nat.mod_eq_of_lt (by omega : c.avail - 128 < 2 ^ 64)] at hc
    have hrem : 12 ≤ c.avail - 128 := Nat.le_of_not_lt hc
    have hst : (c.hdr.work_end - 12#64).toNat = c.workBase.toNat + c.avail - 12 := by
      rw [bv64_sub_toNat (by rw [hwe, show (12#64 : BitVec 64).toNat = 12 from rfl]; omega),
        hwe, show (12#64 : BitVec 64).toNat = 12 from rfl]
    have h128_ptr : (c.workBase + 128#64) + BitVec.ofNat 64 (c.avail - 128 - 12) =
        c.hdr.work_end - 12#64 := BitVec.eq_of_toNat_eq
      (by rw [bv64_add_ofNat_toNat (by rw [h128]; omega), h128, hst]; omega)
    have hsp := region_merge_eq (a := c.workBase + 128#64) (n1 := c.avail - 128 - 12) (n2 := 12)
      (n := c.avail - 128) (by omega) (by omega)
    rw [h128_ptr] at hsp
    have hm0 : (region (c.hdr.work_end - 12#64) 12 ⋆ (bvHdrMem c.workBase c.hdr ⋆
        region (c.workBase + 128#64) (c.avail - 128 - 12) ⋆ R)) m := by
      rw [← hsp] at hm_hdr; exact sep_ac hm_hdr
    let h0bs := dimacsHeaderPrefix ++ natToBytes (0#32).toNat ++ [asciiSpace] ++
      natToBytes (1#32).toNat ++ [asciiNewline]
    have hhl : h0bs.length = 10 := by decide
    have h10_pt : (c.hdr.work_end - 12#64 + BitVec.ofNat 64 h0bs.length).toNat =
        c.workBase.toNat + c.avail - 2 := by
      rw [bv64_add_ofNat_toNat (by rw [hst, hhl]; omega), hst, hhl]; omega
    have hsp_hdr : region (c.hdr.work_end - 12#64) 12 = (region (c.hdr.work_end - 12#64)
        h0bs.length ⋆ region (c.hdr.work_end - 12#64 + BitVec.ofNat 64 h0bs.length) 2) :=
      (region_merge_eq (n := 12) (by rw [hhl]) (by decide)).symm
    rw [hsp_hdr] at hm0; c0_hsteps_nogrp; c0_call hWriteHdr
    refine ⟨region (c.hdr.work_end - 12#64 + BitVec.ofNat 64 h0bs.length) 2 ⋆
        bvHdrMem c.workBase c.hdr ⋆ region (c.workBase + 128#64) (c.avail - 128 - 12) ⋆ R,
      by dsimp only [h0bs] at hhl ⊢; rw [hst, hhl]; omega, sep_ac hm0, fun m1 hm1 => ?_⟩
    dsimp only [h0bs] at h10_pt
    simp only [show (0#32 : BitVec 32).toNat = 0 from rfl,
      show (1#32 : BitVec 32).toNat = 1 from rfl] at h10_pt
    c0_call hWriteEnd
    refine ⟨bvHdrMem c.workBase c.hdr ⋆ region (c.workBase + 128#64) (c.avail - 128 - 12) ⋆
        bytes (c.hdr.work_end - 12#64) h0bs ⋆ R,
      by rw [h10_pt]; omega, sep_ac hm1, fun m2 hm2 => ?_⟩
    c0_hsteps!
    have hmrg : bytes (c.hdr.work_end - 12#64) (encodeDimacs (tseitinCnf c 0#32)) =
        (bytes (c.hdr.work_end - 12#64) h0bs ⋆ bytes (c.hdr.work_end - 12#64 +
          BitVec.ofNat 64 h0bs.length) [asciiZero, asciiNewline]) := by
      rw [encodeDimacs_root0, bytes_append_merge (by rw [hhl]; decide)]
      dsimp only [h0bs]; simp only [show (0#32 : BitVec 32).toNat = 0 from rfl,
        show (1#32 : BitVec 32).toNat = 1 from rfl, List.append_assoc]; rfl
    let hdr' : BVHdrState :=
      { c.hdr with dimacs_start := c.hdr.work_end - 12#64, dimacs_len := 12#32 }
    have hm2' : (bvHdrMem c.workBase hdr' ⋆
        region (c.workBase + 128#64) ((c.hdr.work_end - 12#64).toNat - (c.workBase.toNat + 128)) ⋆
        bytes (c.hdr.work_end - 12#64) (encodeDimacs (tseitinCnf c 0#32)) ⋆ R) m := by
      rw [hmrg, show (c.hdr.work_end - 12#64).toNat - (c.workBase.toNat + 128) =
        c.avail - 128 - 12 by rw [hst]; omega]; dsimp only [hdr']; exact sep_ac hm
    have henc_l : (encodeDimacs (tseitinCnf c 0#32)).length = 12 := by
      rw [encodeDimacs_root0]; decide
    refine (hQ true _ m).1 rfl ⟨validDimacs_tseitin_of_counts (marksToBool c.marks)
      (by rw [cnfMaxVar_root0]; decide)
      (by simp [tseitin, Std.Sat.CNF.add, Std.Sat.CNF.empty]; decide),
      by rw [hst, henc_l]; omega, by rw [henc_l]; rfl, by rw [hst]; omega, hm2'⟩

end

end LeanQbe.T.Examples.Bitblast.Proof
