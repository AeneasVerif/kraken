module

public import Kraken.Bedrock2.Test.LratTrimSpec
public import Kraken.Bedrock2.Notation
import Std.Tactic.BVDecide
meta import Std.Tactic.BVDecide.Reflect
import all Std.Sat.CNF.Entails

@[expose] public section

open Std Std.ExtHashMap Std.Sat
open Std.Tactic.BVDecide.LRAT.Internal
open Kraken.Bedrock2.Notation

namespace Kraken.Bedrock2.Test

attribute [local simp] ExtHashMap.get?_eq_getElem? ExtHashMap.getElem?_insert interpOp1 interpBinop

/-! ## 1. Pure SAT Resolution Metatheory (`MarksWF`, `marksCount`, `MarksSat`, `MarksEntailed`) -/

/-- Encode a Boolean polarity as a mark byte in `marks_begin`: `1` for `true`, `-1` for `false`. -/
def encodePol (pol : Bool) : BitVec 64 :=
  if pol then 1 else -1

@[simp] theorem encodePol_true : encodePol true = 1 := rfl
@[simp] theorem encodePol_false : encodePol false = -1 := rfl

theorem isInt8_encodePol (pol : Bool) : IsInt8 (encodePol pol) := by
  cases pol <;> decide

theorem encodePol_ne_zero (pol : Bool) : encodePol pol ≠ 0 := by
  cases pol <;> decide

theorem encodePol_beq_zero (pol : Bool) : (encodePol pol != 0) = true := by
  cases pol <;> rfl

@[simp] theorem encodePol_inj {p1 p2 : Bool} : encodePol p1 = encodePol p2 ↔ p1 = p2 := by
  cases p1 <;> cases p2 <;> decide

theorem encodePol_not_ne (pol : Bool) : encodePol (!pol) ≠ encodePol pol := by
  cases pol <;> decide

theorem bvSignByte_eq_encodePol (lit : BitVec 64) :
    bvSignByte lit = encodePol (toLiteral lit).2 := by
  have h : ∀ b : Bool, (if b = true then (-1 : BitVec 64) else 1) = encodePol (!b) := by decide
  exact (bvSignByte_eq).trans (h (lit.slt 0))

theorem evalAssignedLit_encodePol_eq (pol : Bool) (lit : BitVec 64) :
    evalAssignedLit (encodePol pol) lit = if pol == (toLiteral lit).2 then 1 else -1 := by
  have h : ∀ p b : Bool, (if b = true then -encodePol p else encodePol p) =
      if p == !b then (1 : BitVec 64) else -1 := by decide
  exact h pol (lit.slt 0)

/-- Well-formedness of the `marks` byte array at `marks_begin`:
every entry is `0` (unmarked), `1` (`true`), or `-1` (`false`). -/
def MarksWF (marks : List (BitVec 64)) : Prop :=
  ∀ idx, idx < marks.length →
    marks[idx]? = some 0 ∨ ∃ pol, marks[idx]? = some (encodePol pol)

theorem MarksWF.isInt8 {marks : List (BitVec 64)} (hwf : MarksWF marks)
    {idx : Nat} (hlt : idx < marks.length) : IsInt8 marks[idx] := by
  have h := hwf idx hlt
  rw [List.getElem?_eq_getElem hlt] at h
  rcases h with h0 | ⟨pol, hpol⟩
  · rw [Option.some.inj h0]; exact isInt8_zero
  · rw [Option.some.inj hpol]; exact isInt8_encodePol pol

/-- Number of non-zero marks in `marks`, tracked by `resolvent_size`. -/
def marksCount (marks : List (BitVec 64)) : Nat :=
  marks.countP (· != 0)

/-- An assignment `a : Nat → Bool` satisfies the resolvent represented by `marks` iff some
variable `idx` has `marks[idx] = encodePol (a idx)`. -/
def MarksSat (a : Nat → Bool) (marks : List (BitVec 64)) : Prop :=
  ∃ idx pol, idx < marks.length ∧
    marks[idx]? = some (encodePol pol) ∧ a idx = pol

/-- A CNF formula `f` entails the resolvent represented by `marks`. -/
def MarksEntailed (f : CNF Nat) (marks : List (BitVec 64)) : Prop :=
  ∀ a, f.Sat a → MarksSat a marks

/-- A clause is non-tautological if no variable occurs with both polarities. -/
def ClauseNonTautological (c : CNF.Clause Nat) : Prop :=
  ∀ atom, ¬((atom, true) ∈ c.literals ∧ (atom, false) ∈ c.literals)

theorem ClauseNonTautological.eq_of_mem {c : CNF.Clause Nat} (hc : ClauseNonTautological c)
    {atom : Nat} {p1 p2 : Bool} (h1 : (atom, p1) ∈ c.literals) (h2 : (atom, p2) ∈ c.literals) :
    p1 = p2 := by
  cases p1 <;> cases p2
  · rfl
  · exact False.elim (hc atom ⟨h2, h1⟩)
  · exact False.elim (hc atom ⟨h1, h2⟩)
  · rfl

theorem marksWF_replicate (n : Nat) : MarksWF (List.replicate n 0) := by
  intro idx hidx
  rw [List.length_replicate] at hidx
  exact Or.inl (by simp [hidx])

theorem marksWF_set_encodePol {marks : List (BitVec 64)} (hwf : MarksWF marks)
    {idx : Nat} (hlt : idx < marks.length) (pol : Bool) :
    MarksWF (marks.set idx (encodePol pol)) := by
  intro j hj
  rw [List.length_set] at hj
  by_cases hji : idx = j
  · subst hji
    exact Or.inr ⟨pol, by simp [List.getElem?_set_self hlt]⟩
  · rw [List.getElem?_set_ne hji]
    exact hwf j hj

theorem marksWF_set_zero {marks : List (BitVec 64)} (hwf : MarksWF marks)
    {idx : Nat} (hlt : idx < marks.length) :
    MarksWF (marks.set idx 0) := by
  intro j hj
  rw [List.length_set] at hj
  by_cases hji : idx = j
  · subst hji
    exact Or.inl (by simp [List.getElem?_set_self hlt])
  · rw [List.getElem?_set_ne hji]
    exact hwf j hj

@[simp] theorem marksCount_nil : marksCount [] = 0 := rfl

@[simp] theorem marksCount_cons (b : BitVec 64) (bs : List (BitVec 64)) :
    marksCount (b :: bs) = (if b != 0 then 1 else 0) + marksCount bs := by
  simp [marksCount, List.countP_cons, Nat.add_comm]

theorem marksCount_le_length (marks : List (BitVec 64)) :
    marksCount marks ≤ marks.length := by
  exact List.countP_le_length

theorem marksCount_replicate_zero (n : Nat) : marksCount (List.replicate n 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, marksCount_cons, ih]
    rfl

theorem eq_replicate_zero_of_marksCount_eq_zero {marks : List (BitVec 64)}
    (h : marksCount marks = 0) : marks = List.replicate marks.length 0 := by
  induction marks with
  | nil => rfl
  | cons b bs ih =>
    rw [marksCount_cons] at h
    by_cases hb : b = 0
    · subst hb
      have h0 : ((0 : BitVec 64) != 0) = false := rfl
      rw [h0] at h
      simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add] at h
      rw [List.length_cons, List.replicate_succ, ← ih h]
    · have hbt : (b != 0) = true := bne_iff_ne.mpr hb
      rw [hbt] at h
      simp only [↓reduceIte] at h
      omega

theorem not_marksSat_of_marksCount_eq_zero {marks : List (BitVec 64)}
    (h : marksCount marks = 0) (a : Nat → Bool) : ¬MarksSat a marks := by
  rintro ⟨idx, pol, hlt, hget, _⟩
  have hrep := eq_replicate_zero_of_marksCount_eq_zero h
  have h0 : marks[idx]? = some 0 := by
    rw [hrep]
    simp [hlt]
  rw [h0] at hget
  exact encodePol_ne_zero pol (Option.some.inj hget).symm

theorem marksCount_set_of_eq_zero {marks : List (BitVec 64)} {idx : Nat} {b : BitVec 64}
    (hget : marks[idx]? = some 0) (hb : b ≠ 0) :
    marksCount (marks.set idx b) = marksCount marks + 1 := by
  induction marks generalizing idx with
  | nil => simp at hget
  | cons x xs ih =>
    cases idx with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hget
      subst hget
      have hbt : (b != 0) = true := bne_iff_ne.mpr hb
      have h0 : ((0 : BitVec 64) != 0) = false := rfl
      simp only [List.set_cons_zero, marksCount_cons, hbt, h0, Bool.false_eq_true, ↓reduceIte]
      omega
    | succ i =>
      simp only [List.getElem?_cons_succ] at hget
      simp [List.set_cons_succ, marksCount_cons, ih hget, Nat.add_assoc]

theorem marksCount_set_zero_of_ne_zero {marks : List (BitVec 64)} {idx : Nat} {b : BitVec 64}
    (hget : marks[idx]? = some b) (hb : b ≠ 0) :
    marksCount (marks.set idx 0) + 1 = marksCount marks := by
  induction marks generalizing idx with
  | nil => simp at hget
  | cons x xs ih =>
    cases idx with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hget
      subst hget
      have hbt : (x != 0) = true := bne_iff_ne.mpr hb
      have h0 : ((0 : BitVec 64) != 0) = false := rfl
      simp only [List.set_cons_zero, marksCount_cons, hbt, h0, Bool.false_eq_true, ↓reduceIte]
      omega
    | succ i =>
      simp only [List.getElem?_cons_succ] at hget
      have := ih hget
      simp only [List.set_cons_succ, marksCount_cons]
      omega

theorem ofNat_add_one (n : Nat) :
    BitVec.ofNat 64 n + 1 = BitVec.ofNat 64 (n + 1) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add]

theorem ofNat_sub_one_of_succ {n n' : Nat} (h : n' + 1 = n) :
    BitVec.ofNat 64 n - 1 = BitVec.ofNat 64 n' := by
  subst h
  rw [← ofNat_add_one]
  bv_decide

/-- Soundness of the first antecedent (`first = 1`) in `br_check_clause_strictly_by_resolution`:
if `unit = 0`, every literal of `c` is marked in `marks` with its polarity, so `Clause.Sat a c → MarksSat a marks`. -/
theorem marksSat_of_first_antecedent {a : Nat → Bool} {c : CNF.Clause Nat} {marks : List (BitVec 64)}
    (hcov : ∀ atom pol, (atom, pol) ∈ c.literals →
      atom < marks.length ∧ marks[atom]? = some (encodePol pol))
    (hsat : c.Sat a) : MarksSat a marks := by
  rcases CNF.Clause.sat_iff_exists_mem_eq.mp hsat with ⟨⟨atom, pol⟩, hmem, ha⟩
  rw [← CNF.Clause.mem_literals_iff] at hmem
  obtain ⟨hlt, hmark⟩ := hcov atom pol hmem
  exact ⟨atom, pol, hlt, hmark, ha⟩

/-- Soundness of binary resolution (`first = 0`) in `br_check_clause_strictly_by_resolution`:
resolving `marks₀` with a non-tautological clause `c` on pivot `(u_atom, u_pol)` preserves `MarksSat a`. -/
theorem marksSat_of_resolve_antecedent {a : Nat → Bool} {c : CNF.Clause Nat}
    {marks₀ marks : List (BitVec 64)} {u_atom : Nat} {u_pol : Bool}
    (hc : ClauseNonTautological c)
    (hlen : marks.length = marks₀.length)
    (hpres : ∀ idx, idx < marks.length → marks₀[idx]? ≠ some 0 → marks[idx]? = marks₀[idx]?)
    (horig : ∀ idx pol, idx < marks.length → marks[idx]? = some (encodePol pol) →
      marks₀[idx]? = some (encodePol pol) ∨ (idx, pol) ∈ c.literals)
    (hcov : ∀ atom pol, (atom, pol) ∈ c.literals →
      atom < marks.length ∧
      (marks[atom]? = some (encodePol pol) ∨
       ((atom, pol) = (u_atom, u_pol) ∧ marks[atom]? = some (encodePol (!pol)))))
    (hunit_mem : (u_atom, u_pol) ∈ c.literals)
    (hunit_mark : marks[u_atom]? = some (encodePol (!u_pol)))
    (hsat₀ : MarksSat a marks₀)
    (hsatc : c.Sat a) :
    MarksSat a (marks.set u_atom 0) := by
  have hu_lt : u_atom < marks.length := (hcov u_atom u_pol hunit_mem).1
  by_cases ha_u : a u_atom = u_pol
  · rcases hsat₀ with ⟨idx, pol, hlt₀, hget₀, ha_idx⟩
    have hlt : idx < marks.length := hlen.symm ▸ hlt₀
    have hne : u_atom ≠ idx := by
      rintro rfl
      have horig_u := horig u_atom (!u_pol) hu_lt hunit_mark
      rcases horig_u with hm0 | hmem_neg
      · rw [hm0] at hget₀
        have hpol : (!u_pol) = pol := encodePol_inj.mp (Option.some.inj hget₀)
        subst hpol
        rw [ha_u] at ha_idx
        cases u_pol <;> contradiction
      · exact absurd (hc.eq_of_mem hunit_mem hmem_neg) (by cases u_pol <;> decide)
    refine ⟨idx, pol, by simp [hlt], ?_, ha_idx⟩
    rw [List.getElem?_set_ne hne, hpres idx hlt]
    · exact hget₀
    · rw [hget₀]
      intro hcontra
      exact encodePol_ne_zero pol (Option.some.inj hcontra)
  · rcases CNF.Clause.sat_iff_exists_mem_eq.mp hsatc with ⟨⟨atom, pol⟩, hmem, ha_atom⟩
    rw [← CNF.Clause.mem_literals_iff] at hmem
    simp only at ha_atom
    have hne_lit : (atom, pol) ≠ (u_atom, u_pol) := by
      rintro ⟨rfl, rfl⟩
      exact ha_u ha_atom
    have hne_atom : atom ≠ u_atom := by
      rintro rfl
      exact hne_lit (Prod.ext rfl (hc.eq_of_mem hmem hunit_mem))
    obtain ⟨hlt, hmark | ⟨heq, _⟩⟩ := hcov atom pol hmem
    · refine ⟨atom, pol, by simp [hlt], ?_, ha_atom⟩
      rw [List.getElem?_set_ne hne_atom.symm]
      exact hmark
    · exact absurd heq hne_lit

/-- Soundness of one step of Loop 3 (`while lit` on `literals`):
if `marks[atom] = encodePol pol` for `(atom, pol) ∈ c`, clearing `marks[atom]` to `0`
preserves `MarksSat a marks ∨ c.Sat a`. -/
theorem marksSat_clear_step {a : Nat → Bool} {c : CNF.Clause Nat} {marks : List (BitVec 64)}
    {atom : Nat} {pol : Bool}
    (hmem : (atom, pol) ∈ c.literals)
    (hmark : marks[atom]? = some (encodePol pol))
    (hsat : MarksSat a marks) :
    MarksSat a (marks.set atom 0) ∨ c.Sat a := by
  rcases hsat with ⟨idx, pol', hlt, hget, ha_idx⟩
  by_cases hji : atom = idx
  · subst hji
    rw [hmark] at hget
    have hpol : pol = pol' := encodePol_inj.mp (Option.some.inj hget)
    subst hpol
    exact Or.inr (CNF.Clause.sat_of_mem_of_eq (CNF.Clause.mem_literals_iff.mp hmem) ha_idx)
  · refine Or.inl ⟨idx, pol', by simp [hlt], ?_, ha_idx⟩
    rw [List.getElem?_set_ne hji]
    exact hget

/-! ## 2. Bedrock2 Expression & Memory Evaluation Lemmas -/

theorem eval_bvAbs_lit {m : Mem 64} {l : Locals 64} {v : BitVec 64}
    (hl : l["lit"]? = some v) :
    (bedrock2_expr:(lit .< 0 ? -lit : lit)).eval m l = some (bvAbs v) := by
  simp only [Expr.eval, ExtHashMap.get?_eq_getElem?, hl, bind, Option.bind, pure,
    interpBinop, interpOp1, bvAbs]
  change (if (if v.slt 0 = true then 1#64 else 0#64) = 0#64 then some v else some (-v)) = _
  cases v.slt 0 <;> rfl

theorem eval_bvAbs_unit {m : Mem 64} {l : Locals 64} {v : BitVec 64}
    (hl : l["unit"]? = some v) :
    (bedrock2_expr:(unit .< 0 ? -unit : unit)).eval m l = some (bvAbs v) := by
  simp only [Expr.eval, ExtHashMap.get?_eq_getElem?, hl, bind, Option.bind, pure,
    interpBinop, interpOp1, bvAbs]
  change (if (if v.slt 0 = true then 1#64 else 0#64) = 0#64 then some v else some (-v)) = _
  cases v.slt 0 <;> rfl

theorem eval_bvSignByte_lit {m : Mem 64} {l : Locals 64} {v : BitVec 64}
    (hl : l["lit"]? = some v) :
    (bedrock2_expr:((lit .>> 63) | 1)).eval m l = some (bvSignByte v) := by
  simp only [Expr.eval, ExtHashMap.get?_eq_getElem?, hl, bind, Option.bind, pure, interpBinop]
  have hs : shamt (BitVec.ofInt 64 63) = 63 := by decide
  rw [hs]
  rfl

theorem bvAbs_eq_ofNat_toLiteral_fst (v : BitVec 64) :
    bvAbs v = BitVec.ofNat 64 (toLiteral v).1 := by
  simp [toLiteral]

theorem zeroTermInts_sub_step {p : BitVec 64} {x : BitVec 64} {xs : List (BitVec 64)}
    {R : Mem 64 → Prop} (h : ∃ R', R = (ZeroTermInts p (x :: xs) ⋆ R')) :
    ∃ R', R = (ZeroTermInts (p + 4) xs ⋆ R') := by
  obtain ⟨R', rfl⟩ := h
  exact ⟨int4 p x ⋆ R', by rw [zeroTermInts_cons, sep_comm (int4 p x), sep_assoc]⟩

theorem eval_load4_zeroTermInts_head {m : Mem 64} {l : Locals 64} {ea : Expr}
    {p : BitVec 64} {xs : List (BitVec 64)} {R : Mem 64 → Prop}
    (ha : ea.eval m l = some p)
    (hsep : m =⋆ ZeroTermInts p xs ⋆ R)
    (h32 : ∀ x ∈ xs, IsInt32 x) :
    (Expr.op .srs (.op .slu (.load .four ea) (.literal 32)) (.literal 32)).eval m l =
      some ((xs ++ [0])[0]'(by simp)) := by
  cases xs with
  | nil =>
    simpa using eval_load4_zeroTermInts_end (xs := []) (by simpa using ha) hsep
  | cons x xs =>
    rw [zeroTermInts_cons, sep_assoc] at hsep
    exact eval_load4_sext ha hsep (h32 x List.mem_cons_self)

theorem eval_load4_zeroTermInts_head_of_sub {m : Mem 64} {l : Locals 64} {ea : Expr}
    {p : BitVec 64} {xs : List (BitVec 64)} {P R : Mem 64 → Prop}
    (ha : ea.eval m l = some p)
    (hsep : m =⋆ P ⋆ R)
    (hsub : ∃ R', R = (ZeroTermInts p xs ⋆ R'))
    (h32 : ∀ x ∈ xs, IsInt32 x) :
    (Expr.op .srs (.op .slu (.load .four ea) (.literal 32)) (.literal 32)).eval m l =
      some ((xs ++ [0])[0]'(by simp)) := by
  obtain ⟨R', rfl⟩ := hsub
  rw [← sep_assoc, sep_comm P, sep_assoc] at hsep
  exact eval_load4_zeroTermInts_head ha hsep h32

/-- Helper for evaluating `if lit .< 0 { mark = -mark }` on `mark = v`. -/
theorem exec_cond_neg_mark {e : Env} {B : Nat} {t : Trace 64} {m : Mem 64} {l : Locals 64}
    {post : Trace 64 → Mem 64 → Locals 64 → Prop} {lit v : BitVec 64}
    (hlit : l["lit"]? = some lit) (hmark : l["mark"]? = some v)
    (hpost : ∀ l', l'["mark"]? = some (evalAssignedLit v lit) →
      (∀ k, k ≠ "mark" → l'[k]? = l[k]?) → post t m l') :
    Exec lratFailExt e B (bedrock2_cmd:(if lit .< 0 { mark = -mark })) t m l post := by
  have hev : (bedrock2_expr:(lit .< 0)).eval m l = some (if lit.slt 0 then 1 else 0) := by
    simp [Expr.eval, hlit]
  refine Exec.cond_cps hev (fun hnz => ?_) (fun hz => ?_)
  · have hslt : lit.slt 0 = true := by revert hnz; cases lit.slt 0 <;> decide
    refine Exec.set_cps (v := -v) (by simp [Expr.eval, hmark]) (hpost (l.insert "mark" (-v)) ?_ ?_)
    · simp only [Locals.getElem?_insert, ↓reduceIte, evalAssignedLit, hslt]
    · intro k hk; simp [Ne.symm hk]
  · have hslt : lit.slt 0 = false := by revert hz; cases lit.slt 0 <;> decide
    refine .skip _ _ _ _ _ (hpost l ?_ (fun _ _ => rfl))
    simp only [hmark, evalAssignedLit, hslt, Bool.false_eq_true, ↓reduceIte]

/-! ## 3. Loop 1 (`while aid` forward scan of `antecedents`) -/

/-- Specification of Loop 1 in `br_check_clause_strictly_by_resolution`:
scans `ants ++ [0]` starting at `a_ptr`, verifying every `aid ∈ ants` has `aid.slt 0 = false`
(or calling `lrat_fail`), and advances `a` to `a_ptr + 4 * ants.length`. -/
theorem strict_loop1_ok {e : Env} {B : Nat} {t : Trace 64} {m : Mem 64} {l : Locals 64}
    {id_val a_ptr : BitVec 64} {ants : List (BitVec 64)} {R : Mem 64 → Prop}
    {post : Trace 64 → Mem 64 → Locals 64 → Prop}
    (hid : l["id"]? = some id_val)
    (ha : l["a"]? = some a_ptr)
    (haid : l["aid"]? = some ((ants ++ [0])[0]'(by simp)))
    (hants : ∀ x ∈ ants, IsInt32 x ∧ x ≠ 0)
    (hmem : m =⋆ ZeroTermInts a_ptr ants ⋆ R)
    (hpost : (∀ x ∈ ants, x.slt 0 = false) →
      ∀ l', l'["a"]? = some (a_ptr + BitVec.ofNat 64 (4 * ants.length)) →
        l'["aid"]? = some 0 →
        (∀ k, k ≠ "a" → k ≠ "aid" → l'[k]? = l[k]?) →
        post t m l') :
    Exec lratFailExt e B (bedrock2_cmd:(
      while aid {
        if aid .< 0 {
          interact lrat_fail(1, id, aid, 0, 0)
        };
        a = a + 4;
        aid = (load4(a) << 32) .>> 32
      }
    )) t m l post := by
  induction ants generalizing a_ptr l R with
  | nil =>
    simp only [List.nil_append, List.getElem_singleton] at haid
    refine .while_false _ _ _ _ _ _ _ _ (by simp [Expr.eval, haid]) rfl ?_
    refine hpost (by intro _ h; cases h) l ?_ haid (fun _ _ _ => rfl)
    simp [ha]
  | cons x xs ih =>
    simp only [List.cons_append, List.getElem_cons_zero] at haid
    obtain ⟨hx32, hxne⟩ := hants x List.mem_cons_self
    refine Exec.while_true_cps (by simp [Expr.eval, haid]) hxne ?_
    refine Exec.seq_cps ?_
    have hev_cond : (bedrock2_expr:(aid .< 0)).eval m l = some (if x.slt 0 then 1 else 0) := by
      simp [Expr.eval, haid]
    refine Exec.cond_cps hev_cond (fun hnz => ?_) (fun hz => ?_)
    · exact exec_lrat_fail (args := [1, id_val, x, 0, 0]) (by simp [evalArgs, Expr.eval, hid, haid])
    · have hxslt : x.slt 0 = false := by revert hz; cases x.slt 0 <;> decide
      refine .skip _ _ _ _ _ ?_
      refine Exec.seq_cps (Exec.set_cps (v := a_ptr + 4) (by simp [Expr.eval, ha]) ?_)
      let l1 := l.insert "a" (a_ptr + 4)
      have hmem_xs : m =⋆ ZeroTermInts (a_ptr + 4) xs ⋆ (int4 a_ptr x ⋆ R) := by
        rw [zeroTermInts_cons, sep_comm (int4 a_ptr x), sep_assoc] at hmem
        exact hmem
      have hload_next : (bedrock2_expr:((load4(a) << 32) .>> 32)).eval m l1 =
          some ((xs ++ [0])[0]'(by simp)) := by
        refine eval_load4_zeroTermInts_head (by simp [l1, Expr.eval]) hmem_xs
          (fun y hy => (hants y (List.mem_cons_of_mem x hy)).1)
      refine Exec.set_cps hload_next ?_
      let l2 := l1.insert "aid" ((xs ++ [0])[0]'(by simp))
      refine ih (a_ptr := a_ptr + 4) (l := l2) (R := int4 a_ptr x ⋆ R)
        (by simp [l2, l1, hid])
        (by simp [l2, l1])
        (by simp [l2])
        (fun y hy => hants y (List.mem_cons_of_mem x hy))
        hmem_xs
        (fun hxs l' ha' haid' hrest => ?_)
      refine hpost ?_ l' ?_ haid' (fun k hka hkaid => ?_)
      · intro y hy
        rcases List.mem_cons.mp hy with rfl | hy'
        · exact hxslt
        · exact hxs y hy'
      · have hadd : a_ptr + 4 + BitVec.ofNat 64 (4 * xs.length) =
            a_ptr + BitVec.ofNat 64 (4 * (x :: xs).length) := by
          apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]; omega
        rw [← hadd]
        exact ha'
      · rw [hrest k hka hkaid]
        simp [l2, l1, Ne.symm hka, Ne.symm hkaid]

/-! ## 4. Loop 3 (`while lit` on `literals` + `if resolvent_size`) -/

/-- Specification of Loop 3 in `br_check_clause_strictly_by_resolution`:
scans `rem ++ [0]` starting at `l_ptr`, verifying every literal `lit ∈ rem` is marked in `marks`
with matching polarity, clearing its mark to `0`, and decrementing `resolvent_size`. -/
theorem strict_loop3_ok {e : Env} {B : Nat} {t : Trace 64} {m : Mem 64} {l : Locals 64}
    {max_var : Nat} {id_val marks_begin l_ptr : BitVec 64}
    {marks₀ marks rem : List (BitVec 64)} {c : CNF.Clause Nat} {R : Mem 64 → Prop}
    {post : Trace 64 → Mem 64 → Locals 64 → Prop}
    (hid : l["id"]? = some id_val)
    (hmb : l["marks_begin"]? = some marks_begin)
    (hrs : l["resolvent_size"]? = some (BitVec.ofNat 64 (marksCount marks)))
    (hl : l["l"]? = some l_ptr)
    (hlit : l["lit"]? = some ((rem ++ [0])[0]'(by simp)))
    (hwf : MarksWF marks)
    (hlen : max_var < marks.length)
    (hrem : ∀ x ∈ rem, IsValidLit max_var x ∧ toLiteral x ∈ c.literals)
    (hsat : ∀ a, MarksSat a marks₀ → MarksSat a marks ∨ c.Sat a)
    (hmem : m =⋆ byte1Array marks_begin marks ⋆ R)
    (hsub : ∃ R', R = (ZeroTermInts l_ptr rem ⋆ R'))
    (hpost : ∀ m' l' (marks' : List (BitVec 64)),
      marks'.length = marks.length →
      MarksWF marks' →
      l'["id"]? = some id_val →
      l'["resolvent_size"]? = some (BitVec.ofNat 64 (marksCount marks')) →
      (∀ a, MarksSat a marks₀ → MarksSat a marks' ∨ c.Sat a) →
      (m' =⋆ byte1Array marks_begin marks' ⋆ R) →
      post t m' l') :
    Exec lratFailExt e B (bedrock2_cmd:(
      while lit {
        idx = lit .< 0 ? -lit : lit;
        m = marks_begin + idx;
        mark = (load1(m) << 56) .>> 56;
        if mark == 0 {
          interact lrat_fail(6, id, lit, 0, 0)
        };
        if lit .< 0 {
          mark = -mark
        };
        if mark .< 0 {
          interact lrat_fail(7, id, lit, 0, 0)
        };
        store1(m, 0);
        resolvent_size = resolvent_size - 1;
        l = l + 4;
        lit = (load4(l) << 32) .>> 32
      }
    )) t m l post := by
  induction rem generalizing m l l_ptr marks with
  | nil =>
    simp only [List.nil_append, List.getElem_singleton] at hlit
    refine .while_false _ _ _ _ _ _ _ _ (by simp [Expr.eval, hlit]) rfl ?_
    exact hpost m l marks rfl hwf hid hrs hsat hmem
  | cons x xs ih =>
    simp only [List.cons_append, List.getElem_cons_zero] at hlit
    obtain ⟨hx_valid, hx_mem⟩ := hrem x List.mem_cons_self
    obtain ⟨hx32, hxne, hxle, _⟩ := hx_valid
    have hatom_lt : (toLiteral x).1 < marks.length := Nat.lt_of_le_of_lt hxle hlen
    refine Exec.while_true_cps (by simp [Expr.eval, hlit]) hxne ?_
    -- idx = lit .< 0 ? -lit : lit
    refine Exec.seq_cps (Exec.set_cps (eval_bvAbs_lit hlit) ?_)
    -- m = marks_begin + idx
    refine Exec.seq_cps (Exec.set_cps (v := marks_begin + BitVec.ofNat 64 (toLiteral x).1)
      (by simp [Expr.eval, hmb, ← bvAbs_eq_ofNat_toLiteral_fst]) ?_)
    -- mark = (load1(m) << 56) .>> 56
    refine Exec.seq_cps (Exec.set_cps
      (eval_load1_byte1Array_elem hatom_lt (by simp [Expr.eval]) hmem (hwf.isInt8 hatom_lt)) ?_)
    -- if mark == 0 { interact lrat_fail(6, id, lit, 0, 0) }
    refine Exec.seq_cps ?_
    refine Exec.cond_cps (v := if marks[(toLiteral x).1] = 0 then 1 else 0)
      (by simp [Expr.eval]) (fun hnz => ?_) (fun hz => ?_)
    · exact exec_lrat_fail (args := [6, id_val, x, 0, 0])
        (by simp [evalArgs, Expr.eval, hid, hlit])
    · have hm_ne0 : marks[(toLiteral x).1] ≠ 0 := by
        intro h0; simp [h0] at hz
      have hm_get : marks[(toLiteral x).1]? = some marks[(toLiteral x).1] :=
        List.getElem?_eq_getElem hatom_lt
      rcases hwf (toLiteral x).1 hatom_lt with h0 | ⟨mpol, hmpol⟩
      · exact absurd (Option.some.inj (hm_get.symm.trans h0)) hm_ne0
      · have hmark_eq : marks[(toLiteral x).1] = encodePol mpol :=
          Option.some.inj (hm_get.symm.trans hmpol)
        refine .skip _ _ _ _ _ ?_
        -- if lit .< 0 { mark = -mark }
        refine Exec.seq_cps (exec_cond_neg_mark (lit := x) (v := encodePol mpol)
          (by simp [hlit]) (by simp [hmark_eq]) fun l4 hl4_mark hl4_rest => ?_)
        -- if mark .< 0 { interact lrat_fail(7, id, lit, 0, 0) }
        refine Exec.seq_cps ?_
        refine Exec.cond_cps (v := if (evalAssignedLit (encodePol mpol) x).slt 0 then 1 else 0)
          (by simp [Expr.eval, hl4_mark]) (fun hnz => ?_) (fun hz => ?_)
        · exact exec_lrat_fail (args := [7, id_val, x, 0, 0])
            (by simp [evalArgs, Expr.eval, hl4_rest "id" (by decide),
              hl4_rest "lit" (by decide), hid, hlit])
        · have hpol_eq : mpol = (toLiteral x).2 := by
            by_cases hpeq : mpol = (toLiteral x).2
            · exact hpeq
            · have hbeq : (mpol == (toLiteral x).2) = false := beq_false_of_ne hpeq
              rw [evalAssignedLit_encodePol_eq, hbeq] at hz
              exact absurd hz (by decide)
          subst hpol_eq
          refine .skip _ _ _ _ _ ?_
          -- store1(m, 0)
          refine Exec.seq_cps (store_byte1Array_elem hatom_lt
            (by simp [Expr.eval, hl4_rest "m" (by decide)])
            (v := 0) (by simp [Expr.eval]) hmem fun m' hm' => ?_)
          -- resolvent_size = resolvent_size - 1
          have hcnt : marksCount (marks.set (toLiteral x).1 0) + 1 = marksCount marks :=
            marksCount_set_zero_of_ne_zero hmpol (encodePol_ne_zero _)
          have hrs_sub : BitVec.ofNat 64 (marksCount marks) - 1 =
              BitVec.ofNat 64 (marksCount (marks.set (toLiteral x).1 0)) :=
            ofNat_sub_one_of_succ hcnt
          refine Exec.seq_cps (Exec.set_cps
            (v := BitVec.ofNat 64 (marksCount (marks.set (toLiteral x).1 0)))
            (by simp [Expr.eval, hl4_rest "resolvent_size" (by decide), hrs]; exact hrs_sub) ?_)
          -- l = l + 4
          refine Exec.seq_cps (Exec.set_cps (v := l_ptr + 4)
            (by simp [Expr.eval, hl4_rest "l" (by decide), hl]) ?_)
          -- lit = (load4(l) << 32) .>> 32
          have hsub_xs := zeroTermInts_sub_step hsub
          refine Exec.set_cps
            (eval_load4_zeroTermInts_head_of_sub (by simp [Expr.eval]) hm' hsub_xs
              (fun y hy => (hrem y (List.mem_cons_of_mem x hy)).1.1)) ?_
          refine ih
            (by simp [hl4_rest "id" (by decide), hid])
            (by simp [hl4_rest "marks_begin" (by decide), hmb])
            (by simp)
            (by simp)
            (by simp)
            (marksWF_set_zero hwf hatom_lt)
            (by simp [hlen])
            (fun y hy => hrem y (List.mem_cons_of_mem x hy))
            (fun a hsa => (hsat a hsa).elim
              (fun hms => marksSat_clear_step hx_mem hmpol hms) Or.inr)
            hm'
            hsub_xs
            (fun m'' l'' marks'' hlen'' hwf'' hid'' hrs'' hsat'' hm'' =>
              hpost m'' l'' marks'' (by simpa using hlen'') hwf'' hid'' hrs'' hsat'' hm'')

/-! ## 5. Inner Loop Invariant & Pure Step Lemmas for Loop 2 -/

/-- Pure invariant of the inner `while lit` loop of Loop 2 in `br_check_clause_strictly_by_resolution`. -/
structure InnerInv (max_var : Nat) (marks₀ : List (BitVec 64)) (seen : List (Literal Nat))
    (marks : List (BitVec 64)) (unit_val : BitVec 64) : Prop where
  wf : MarksWF marks
  len_eq : marks.length = marks₀.length
  pres : ∀ idx, idx < marks.length → marks₀[idx]? ≠ some 0 → marks[idx]? = marks₀[idx]?
  orig : ∀ idx pol, idx < marks.length → marks[idx]? = some (encodePol pol) →
    marks₀[idx]? = some (encodePol pol) ∨ (idx, pol) ∈ seen
  seen_pos : ∀ atom pol, (atom, pol) ∈ seen → 0 < atom
  cov : ∀ atom pol, (atom, pol) ∈ seen →
    atom < marks.length ∧
    (marks[atom]? = some (encodePol pol) ∨
     (toLiteral unit_val = (atom, pol) ∧ marks[atom]? = some (encodePol (!pol))))
  unit_spec : unit_val = 0 ∨
    (IsValidLit max_var unit_val ∧ toLiteral unit_val ∈ seen ∧
     marks[(toLiteral unit_val).1]? = some (encodePol (!(toLiteral unit_val).2)))

theorem InnerInv.init {max_var : Nat} {marks₀ : List (BitVec 64)} (hwf : MarksWF marks₀) :
    InnerInv max_var marks₀ [] marks₀ 0 where
  wf := hwf
  len_eq := rfl
  pres := fun _ _ _ => rfl
  orig := fun _ _ _ h => Or.inl h
  seen_pos := by intro _ _ h; cases h
  cov := by intro _ _ h; cases h
  unit_spec := Or.inl rfl

theorem InnerInv.step_mark_zero {max_var : Nat} {marks₀ : List (BitVec 64)}
    {seen : List (Literal Nat)} {marks : List (BitVec 64)} {unit_val x : BitVec 64}
    (hinv : InnerInv max_var marks₀ seen marks unit_val)
    (hx : IsValidLit max_var x)
    (hatom_lt : (toLiteral x).1 < marks.length)
    (hm0 : marks[(toLiteral x).1]? = some 0) :
    InnerInv max_var marks₀ (seen ++ [toLiteral x])
      (marks.set (toLiteral x).1 (encodePol (toLiteral x).2)) unit_val where
  wf := marksWF_set_encodePol hinv.wf hatom_lt (toLiteral x).2
  len_eq := by simp [hinv.len_eq]
  pres := by
    intro idx hlt hne0
    rw [List.length_set] at hlt
    have hprev := hinv.pres idx hlt hne0
    have hne : (toLiteral x).1 ≠ idx := by
      rintro rfl
      exact hne0 (hprev.symm.trans hm0)
    rw [List.getElem?_set_ne hne, hprev]
  orig := by
    intro idx pol hlt hget
    rw [List.length_set] at hlt
    by_cases hji : (toLiteral x).1 = idx
    · subst hji
      rw [List.getElem?_set_self hatom_lt] at hget
      have hpol : (toLiteral x).2 = pol := encodePol_inj.mp (Option.some.inj hget)
      subst hpol
      exact Or.inr (List.mem_append_right _ (by simp))
    · rw [List.getElem?_set_ne hji] at hget
      rcases hinv.orig idx pol hlt hget with hm | hmem
      · exact Or.inl hm
      · exact Or.inr (List.mem_append_left _ hmem)
  seen_pos := by
    intro atom pol hmem
    rcases List.mem_append.mp hmem with hmem | hmem
    · exact hinv.seen_pos atom pol hmem
    · simp only [List.mem_singleton] at hmem
      have : (toLiteral x).1 = atom := congrArg Prod.fst hmem.symm
      rw [← this]
      exact bvAbs_pos hx
  cov := by
    intro atom pol hmem
    rw [List.length_set]
    rcases List.mem_append.mp hmem with hmem | hmem
    · obtain ⟨hlt, hmark | ⟨hu, hmark⟩⟩ := hinv.cov atom pol hmem
      · have hne : (toLiteral x).1 ≠ atom := by
          rintro rfl
          rw [hm0] at hmark
          exact encodePol_ne_zero pol (Option.some.inj hmark).symm
        exact ⟨hlt, Or.inl (by rw [List.getElem?_set_ne hne]; exact hmark)⟩
      · have hne : (toLiteral x).1 ≠ atom := by
          rintro rfl
          rw [hm0] at hmark
          exact encodePol_ne_zero (!pol) (Option.some.inj hmark).symm
        exact ⟨hlt, Or.inr ⟨hu, by rw [List.getElem?_set_ne hne]; exact hmark⟩⟩
    · simp only [List.mem_singleton] at hmem
      have hatom : (toLiteral x).1 = atom := congrArg Prod.fst hmem.symm
      have hpol : (toLiteral x).2 = pol := congrArg Prod.snd hmem.symm
      subst hatom hpol
      exact ⟨hatom_lt, Or.inl (List.getElem?_set_self hatom_lt)⟩
  unit_spec := by
    rcases hinv.unit_spec with rfl | ⟨hu_val, hu_mem, hu_mark⟩
    · exact Or.inl rfl
    · refine Or.inr ⟨hu_val, List.mem_append_left _ hu_mem, ?_⟩
      have hne : (toLiteral x).1 ≠ (toLiteral unit_val).1 := by
        intro heq
        rw [← heq, hm0] at hu_mark
        exact encodePol_ne_zero (!(toLiteral unit_val).2) (Option.some.inj hu_mark).symm
      rw [List.getElem?_set_ne hne]
      exact hu_mark

theorem InnerInv.step_mark_same {max_var : Nat} {marks₀ : List (BitVec 64)}
    {seen : List (Literal Nat)} {marks : List (BitVec 64)} {unit_val x : BitVec 64}
    (hinv : InnerInv max_var marks₀ seen marks unit_val)
    (hx : IsValidLit max_var x)
    (hatom_lt : (toLiteral x).1 < marks.length)
    (hm : marks[(toLiteral x).1]? = some (encodePol (toLiteral x).2)) :
    InnerInv max_var marks₀ (seen ++ [toLiteral x]) marks unit_val where
  wf := hinv.wf
  len_eq := hinv.len_eq
  pres := hinv.pres
  orig := fun idx pol hlt hget =>
    (hinv.orig idx pol hlt hget).elim Or.inl (fun h => Or.inr (List.mem_append_left _ h))
  seen_pos := by
    intro atom pol hmem
    rcases List.mem_append.mp hmem with hmem | hmem
    · exact hinv.seen_pos atom pol hmem
    · simp only [List.mem_singleton] at hmem
      have : (toLiteral x).1 = atom := congrArg Prod.fst hmem.symm
      rw [← this]
      exact bvAbs_pos hx
  cov := by
    intro atom pol hmem
    rcases List.mem_append.mp hmem with hmem | hmem
    · exact hinv.cov atom pol hmem
    · simp only [List.mem_singleton] at hmem
      have hatom : (toLiteral x).1 = atom := congrArg Prod.fst hmem.symm
      have hpol : (toLiteral x).2 = pol := congrArg Prod.snd hmem.symm
      subst hatom hpol
      exact ⟨hatom_lt, Or.inl hm⟩
  unit_spec :=
    hinv.unit_spec.elim Or.inl (fun ⟨h1, h2, h3⟩ => Or.inr ⟨h1, List.mem_append_left _ h2, h3⟩)

theorem InnerInv.step_mark_opp {max_var : Nat} {marks₀ : List (BitVec 64)}
    {seen : List (Literal Nat)} {marks : List (BitVec 64)} {x : BitVec 64}
    (hinv : InnerInv max_var marks₀ seen marks 0)
    (hx : IsValidLit max_var x)
    (hatom_lt : (toLiteral x).1 < marks.length)
    (hm : marks[(toLiteral x).1]? = some (encodePol (!(toLiteral x).2))) :
    InnerInv max_var marks₀ (seen ++ [toLiteral x]) marks x where
  wf := hinv.wf
  len_eq := hinv.len_eq
  pres := hinv.pres
  orig := fun idx pol hlt hget =>
    (hinv.orig idx pol hlt hget).elim Or.inl (fun h => Or.inr (List.mem_append_left _ h))
  seen_pos := by
    intro atom pol hmem
    rcases List.mem_append.mp hmem with hmem | hmem
    · exact hinv.seen_pos atom pol hmem
    · simp only [List.mem_singleton] at hmem
      have : (toLiteral x).1 = atom := congrArg Prod.fst hmem.symm
      rw [← this]
      exact bvAbs_pos hx
  cov := by
    intro atom pol hmem
    rcases List.mem_append.mp hmem with hmem | hmem
    · obtain ⟨hlt, hmark | ⟨hu0, _⟩⟩ := hinv.cov atom pol hmem
      · exact ⟨hlt, Or.inl hmark⟩
      · have hpos := hinv.seen_pos atom pol hmem
        have h0 : (toLiteral 0).1 = 0 := by decide
        have : 0 = atom := h0.symm.trans (congrArg Prod.fst hu0)
        omega
    · simp only [List.mem_singleton] at hmem
      have hatom : (toLiteral x).1 = atom := congrArg Prod.fst hmem.symm
      have hpol : (toLiteral x).2 = pol := congrArg Prod.snd hmem.symm
      subst hatom hpol
      exact ⟨hatom_lt, Or.inr ⟨rfl, hm⟩⟩
  unit_spec := Or.inr ⟨hx, List.mem_append_right _ (by simp), hm⟩

theorem InnerInv.finish_first {max_var : Nat} {marks₀ marks : List (BitVec 64)}
    {c : CNF.Clause Nat} (hinv : InnerInv max_var marks₀ c.literals marks 0)
    {a : Nat → Bool} (hsat : c.Sat a) : MarksSat a marks := by
  refine marksSat_of_first_antecedent (fun atom pol hmem => ?_) hsat
  obtain ⟨hlt, hmark | ⟨hu0, _⟩⟩ := hinv.cov atom pol hmem
  · exact ⟨hlt, hmark⟩
  · have hpos := hinv.seen_pos atom pol hmem
    have h0 : (toLiteral 0).1 = 0 := by decide
    have : 0 = atom := h0.symm.trans (congrArg Prod.fst hu0)
    omega

theorem InnerInv.finish_resolve {max_var : Nat} {marks₀ marks : List (BitVec 64)}
    {c : CNF.Clause Nat} {unit_val : BitVec 64}
    (hinv : InnerInv max_var marks₀ c.literals marks unit_val)
    (hc : ClauseNonTautological c) (hunit_ne : unit_val ≠ 0)
    {a : Nat → Bool} (hsat₀ : MarksSat a marks₀) (hsatc : c.Sat a) :
    MarksSat a (marks.set (toLiteral unit_val).1 0) := by
  rcases hinv.unit_spec with rfl | ⟨_, hu_mem, hu_mark⟩
  · exact absurd rfl hunit_ne
  · refine marksSat_of_resolve_antecedent hc hinv.len_eq hinv.pres hinv.orig
      (fun atom pol hmem => ?_) hu_mem hu_mark hsat₀ hsatc
    obtain ⟨hlt, hmark | ⟨hu, hmark⟩⟩ := hinv.cov atom pol hmem
    · exact ⟨hlt, Or.inl hmark⟩
    · exact ⟨hlt, Or.inr ⟨hu.symm, hmark⟩⟩

/-! ## 6. Loop 2 Inner (`while lit` on `als`) -/

/-- Helper for failure branches in Loop 2 that execute `store8(st + 144, stat_resolved); interact lrat_fail(...)`. -/
theorem exec_store8_stat_and_fail {e : Env} {B : Nat} {t : Trace 64} {m : Mem 64} {l : Locals 64}
    {st stat_val : BitVec 64} {arges : List Expr} {args : List (BitVec 64)}
    {P R : Mem 64 → Prop} {post : Trace 64 → Mem 64 → Locals 64 → Prop}
    (hst : l["st"]? = some st)
    (hstat : l["stat_resolved"]? = some stat_val)
    (hmem : m =⋆ P ⋆ R)
    (hsub_st : ∃ v0 R', R = (word8 (st + 144) v0 ⋆ R'))
    (hargs : ∀ m', evalArgs m' l arges = some args) :
    Exec lratFailExt e B
      (.seq (bedrock2_cmd:(store8(st + 144, stat_resolved))) (.interact [] "lrat_fail" arges))
      t m l post := by
  obtain ⟨v0, R', rfl⟩ := hsub_st
  rw [← sep_assoc, sep_comm P, sep_assoc] at hmem
  exact Exec.seq_cps (store_word8 (by simp [Expr.eval, hst]) (v := stat_val) (by simp [Expr.eval, hstat]) hmem
    fun m' _ => exec_lrat_fail (hargs m'))

/-- Specification of the inner `while lit` loop of Loop 2 in `br_check_clause_strictly_by_resolution`:
scans `rem ++ [0]` starting at `l_ptr`, marking unmarked literals in `marks_begin`,
recording any opposite-polarity literal in `unit` (or failing if a second one is found),
and preserving `InnerInv`. -/
theorem strict_inner_loop_ok {e : Env} {B : Nat} {t : Trace 64} {m : Mem 64} {l : Locals 64}
    {max_var : Nat} {st id_val aid_val marks_begin stat_val unit_val l_ptr : BitVec 64}
    {marks₀ marks rem : List (BitVec 64)} {seen : List (Literal Nat)} {R : Mem 64 → Prop}
    {post : Trace 64 → Mem 64 → Locals 64 → Prop}
    (hst : l["st"]? = some st)
    (hid : l["id"]? = some id_val)
    (haid : l["aid"]? = some aid_val)
    (hmb : l["marks_begin"]? = some marks_begin)
    (hstat : l["stat_resolved"]? = some stat_val)
    (hrs : l["resolvent_size"]? = some (BitVec.ofNat 64 (marksCount marks)))
    (hunit : l["unit"]? = some unit_val)
    (hl : l["l"]? = some l_ptr)
    (hlit : l["lit"]? = some ((rem ++ [0])[0]'(by simp)))
    (hinv : InnerInv max_var marks₀ seen marks unit_val)
    (hlen : max_var < marks.length)
    (hrem : ∀ x ∈ rem, IsValidLit max_var x)
    (hmem : m =⋆ byte1Array marks_begin marks ⋆ R)
    (hsub : ∃ R', R = (ZeroTermInts l_ptr rem ⋆ R'))
    (hsub_st : ∃ v0 R', R = (word8 (st + 144) v0 ⋆ R'))
    (hpost : ∀ m' l' (marks' : List (BitVec 64)) (unit_val' : BitVec 64),
      InnerInv max_var marks₀ (seen ++ rem.map toLiteral) marks' unit_val' →
      l'["resolvent_size"]? = some (BitVec.ofNat 64 (marksCount marks')) →
      l'["unit"]? = some unit_val' →
      (∀ k, k ≠ "idx" → k ≠ "m" → k ≠ "mark" → k ≠ "resolvent_size" →
        k ≠ "unit" → k ≠ "l" → k ≠ "lit" → l'[k]? = l[k]?) →
      (m' =⋆ byte1Array marks_begin marks' ⋆ R) →
      post t m' l') :
    Exec lratFailExt e B (bedrock2_cmd:(
      while lit {
        idx = lit .< 0 ? -lit : lit;
        m = marks_begin + idx;
        mark = (load1(m) << 56) .>> 56;
        if mark == 0 {
          store1(m, (lit .>> 63) | 1);
          resolvent_size = resolvent_size + 1
        } else {
          if lit .< 0 {
            mark = -mark
          };
          if (0 .< mark) == 0 {
            if unit {
              store8(st + 144, stat_resolved);
              interact lrat_fail(4, id, unit, lit, aid)
            };
            unit = lit
          }
        };
        l = l + 4;
        lit = (load4(l) << 32) .>> 32
      }
    )) t m l post := by
  induction rem generalizing m l l_ptr marks seen unit_val with
  | nil =>
    simp only [List.nil_append, List.getElem_singleton] at hlit
    refine .while_false _ _ _ _ _ _ _ _ (by simp [Expr.eval, hlit]) rfl ?_
    simpa using hpost m l marks unit_val (by simpa using hinv) hrs hunit
      (fun _ _ _ _ _ _ _ _ => rfl) hmem
  | cons x xs ih =>
    simp only [List.cons_append, List.getElem_cons_zero] at hlit
    have hx_valid : IsValidLit max_var x := hrem x List.mem_cons_self
    obtain ⟨hx32, hxne, hxle, _⟩ := hrem x List.mem_cons_self
    have hatom_lt : (toLiteral x).1 < marks.length := Nat.lt_of_le_of_lt hxle hlen
    have hsub_xs := zeroTermInts_sub_step hsub
    refine Exec.while_true_cps (by simp [Expr.eval, hlit]) hxne ?_
    -- idx = lit .< 0 ? -lit : lit
    refine Exec.seq_cps (Exec.set_cps (eval_bvAbs_lit hlit) ?_)
    -- m = marks_begin + idx
    refine Exec.seq_cps (Exec.set_cps (v := marks_begin + BitVec.ofNat 64 (toLiteral x).1)
      (by simp [Expr.eval, hmb, ← bvAbs_eq_ofNat_toLiteral_fst]) ?_)
    -- mark = (load1(m) << 56) .>> 56
    refine Exec.seq_cps (Exec.set_cps
      (eval_load1_byte1Array_elem hatom_lt (by simp [Expr.eval]) hmem (hinv.wf.isInt8 hatom_lt)) ?_)
    -- if mark == 0 { ... } else { ... }
    refine Exec.seq_cps ?_
    refine Exec.cond_cps (v := if marks[(toLiteral x).1] = 0 then 1 else 0)
      (by simp [Expr.eval]) (fun hnz => ?_) (fun hz => ?_)
    · -- Branch 1: mark == 0
      have hm_eq0 : marks[(toLiteral x).1] = 0 := by simpa using hnz
      have hm_get0 : marks[(toLiteral x).1]? = some 0 := by
        rw [List.getElem?_eq_getElem hatom_lt, hm_eq0]
      -- store1(m, (lit .>> 63) | 1)
      refine Exec.seq_cps (store_byte1Array_elem hatom_lt (by simp [Expr.eval])
        (v := encodePol (toLiteral x).2)
        (by rw [← bvSignByte_eq_encodePol]; exact eval_bvSignByte_lit (by simp [hlit]))
        hmem fun m' hm' => ?_)
      -- resolvent_size = resolvent_size + 1
      have hcnt : marksCount (marks.set (toLiteral x).1 (encodePol (toLiteral x).2)) =
          marksCount marks + 1 :=
        marksCount_set_of_eq_zero hm_get0 (encodePol_ne_zero _)
      have hrs_add : BitVec.ofNat 64 (marksCount marks) + 1 =
          BitVec.ofNat 64 (marksCount (marks.set (toLiteral x).1 (encodePol (toLiteral x).2))) := by
        rw [ofNat_add_one, hcnt]
      refine Exec.set_cps
        (v := BitVec.ofNat 64 (marksCount (marks.set (toLiteral x).1 (encodePol (toLiteral x).2))))
        (by simp [Expr.eval, hrs]; exact hrs_add) ?_
      -- l = l + 4
      refine Exec.seq_cps (Exec.set_cps (v := l_ptr + 4) (by simp [Expr.eval, hl]) ?_)
      -- lit = (load4(l) << 32) .>> 32
      refine Exec.set_cps
        (eval_load4_zeroTermInts_head_of_sub (by simp [Expr.eval]) hm' hsub_xs
          (fun y hy => (hrem y (List.mem_cons_of_mem x hy)).1)) ?_
      refine ih
        (by simp [hst]) (by simp [hid]) (by simp [haid]) (by simp [hmb]) (by simp [hstat])
        (by simp) (by simp [hunit]) (by simp) (by simp)
        (hinv.step_mark_zero hx_valid hatom_lt hm_get0)
        (by simp [hlen])
        (fun y hy => hrem y (List.mem_cons_of_mem x hy))
        hm' hsub_xs
        (fun m'' l'' marks'' unit_val'' hinv'' hrs'' hunit'' hrest'' hm'' =>
          hpost m'' l'' marks'' unit_val'' (by simpa using hinv'') hrs'' hunit''
            (fun k hk1 hk2 hk3 hk4 hk5 hk6 hk7 => by
              rw [hrest'' k hk1 hk2 hk3 hk4 hk5 hk6 hk7]
              simp [Ne.symm hk1, Ne.symm hk2, Ne.symm hk3, Ne.symm hk4, Ne.symm hk6, Ne.symm hk7])
            hm'')
    · -- Branch 2: mark != 0
      have hm_ne0 : marks[(toLiteral x).1] ≠ 0 := by intro h0; simp [h0] at hz
      have hm_get : marks[(toLiteral x).1]? = some marks[(toLiteral x).1] :=
        List.getElem?_eq_getElem hatom_lt
      rcases hinv.wf (toLiteral x).1 hatom_lt with h0 | ⟨mpol, hmpol⟩
      · exact absurd (Option.some.inj (hm_get.symm.trans h0)) hm_ne0
      · have hmark_eq : marks[(toLiteral x).1] = encodePol mpol :=
          Option.some.inj (hm_get.symm.trans hmpol)
        -- if lit .< 0 { mark = -mark }
        refine Exec.seq_cps (exec_cond_neg_mark (lit := x) (v := encodePol mpol)
          (by simp [hlit]) (by simp [hmark_eq]) fun l4 hl4_mark hl4_rest => ?_)
        -- if (0 .< mark) == 0 { ... }
        refine Exec.cond_cps
          (v := if (if (0#64).slt (evalAssignedLit (encodePol mpol) x) then (1 : BitVec 64) else 0) = 0 then 1 else 0)
          (by simp [Expr.eval, hl4_mark]) (fun hnz_opp => ?_) (fun hz_same => ?_)
        · -- Subbranch 2a: (0 .< mark) == 0, so mpol = !(toLiteral x).2
          have hpol_opp : mpol = !(toLiteral x).2 := by
            by_cases hpeq : mpol = (toLiteral x).2
            · have hbeq : (mpol == (toLiteral x).2) = true := beq_iff_eq.mpr hpeq
              rw [evalAssignedLit_encodePol_eq, hbeq] at hnz_opp
              exact absurd hnz_opp (by decide)
            · cases mpol <;> cases h : (toLiteral x).2 <;> simp_all
          subst hpol_opp
          -- if unit { store8(st + 144, stat_resolved); interact lrat_fail(4, id, unit, lit, aid) }
          refine Exec.seq_cps ?_
          refine Exec.cond_cps (v := unit_val)
            (by simp [Expr.eval, hl4_rest "unit" (by decide), hunit])
            (fun hunit_nz => ?_) (fun hunit_z => ?_)
          · exact exec_store8_stat_and_fail (st := st) (stat_val := stat_val)
              (args := [4#64, id_val, unit_val, x, aid_val])
              (by simp [hl4_rest "st" (by decide), hst])
              (by simp [hl4_rest "stat_resolved" (by decide), hstat])
              hmem hsub_st
              (fun _ => by simp [evalArgs, Expr.eval, hl4_rest "id" (by decide),
                hl4_rest "unit" (by decide), hl4_rest "lit" (by decide),
                hl4_rest "aid" (by decide), hid, hunit, hlit, haid])
          · subst hunit_z
            refine .skip _ _ _ _ _ ?_
            -- unit = lit
            refine Exec.set_cps (v := x) (by simp [Expr.eval, hl4_rest "lit" (by decide), hlit]) ?_
            -- l = l + 4
            refine Exec.seq_cps (Exec.set_cps (v := l_ptr + 4)
              (by simp [Expr.eval, hl4_rest "l" (by decide), hl]) ?_)
            -- lit = (load4(l) << 32) .>> 32
            refine Exec.set_cps
              (eval_load4_zeroTermInts_head_of_sub (by simp [Expr.eval]) hmem hsub_xs
                (fun y hy => (hrem y (List.mem_cons_of_mem x hy)).1)) ?_
            refine ih
              (by simp [hl4_rest "st" (by decide), hst])
              (by simp [hl4_rest "id" (by decide), hid])
              (by simp [hl4_rest "aid" (by decide), haid])
              (by simp [hl4_rest "marks_begin" (by decide), hmb])
              (by simp [hl4_rest "stat_resolved" (by decide), hstat])
              (by simp [hl4_rest "resolvent_size" (by decide), hrs])
              (by simp) (by simp) (by simp)
              (hinv.step_mark_opp hx_valid hatom_lt hmpol)
              hlen
              (fun y hy => hrem y (List.mem_cons_of_mem x hy))
              hmem hsub_xs
              (fun m'' l'' marks'' unit_val'' hinv'' hrs'' hunit'' hrest'' hm'' =>
                hpost m'' l'' marks'' unit_val'' (by simpa using hinv'') hrs'' hunit''
                  (fun k hk1 hk2 hk3 hk4 hk5 hk6 hk7 => by
                    rw [hrest'' k hk1 hk2 hk3 hk4 hk5 hk6 hk7]
                    simp [Ne.symm hk5, Ne.symm hk6, Ne.symm hk7, hl4_rest k hk3,
                      Ne.symm hk1, Ne.symm hk2, Ne.symm hk3])
                  hm'')
        · -- Subbranch 2b: (0 .< mark) != 0, so mpol = (toLiteral x).2
          have hpol_same : mpol = (toLiteral x).2 := by
            by_cases hpeq : mpol = (toLiteral x).2
            · exact hpeq
            · have hbeq : (mpol == (toLiteral x).2) = false := beq_false_of_ne hpeq
              rw [evalAssignedLit_encodePol_eq, hbeq] at hz_same
              exact absurd hz_same (by decide)
          subst hpol_same
          refine .skip _ _ _ _ _ ?_
          -- l = l + 4
          refine Exec.seq_cps (Exec.set_cps (v := l_ptr + 4)
            (by simp [Expr.eval, hl4_rest "l" (by decide), hl]) ?_)
          -- lit = (load4(l) << 32) .>> 32
          refine Exec.set_cps
            (eval_load4_zeroTermInts_head_of_sub (by simp [Expr.eval]) hmem hsub_xs
              (fun y hy => (hrem y (List.mem_cons_of_mem x hy)).1)) ?_
          refine ih
            (by simp [hl4_rest "st" (by decide), hst])
            (by simp [hl4_rest "id" (by decide), hid])
            (by simp [hl4_rest "aid" (by decide), haid])
            (by simp [hl4_rest "marks_begin" (by decide), hmb])
            (by simp [hl4_rest "stat_resolved" (by decide), hstat])
            (by simp [hl4_rest "resolvent_size" (by decide), hrs])
            (by simp [hl4_rest "unit" (by decide), hunit])
            (by simp) (by simp)
            (hinv.step_mark_same hx_valid hatom_lt hmpol)
            hlen
            (fun y hy => hrem y (List.mem_cons_of_mem x hy))
            hmem hsub_xs
            (fun m'' l'' marks'' unit_val'' hinv'' hrs'' hunit'' hrest'' hm'' =>
              hpost m'' l'' marks'' unit_val'' (by simpa using hinv'') hrs'' hunit''
                (fun k hk1 hk2 hk3 hk4 hk5 hk6 hk7 => by
                  rw [hrest'' k hk1 hk2 hk3 hk4 hk5 hk6 hk7]
                  simp [Ne.symm hk6, Ne.symm hk7, hl4_rest k hk3, Ne.symm hk1, Ne.symm hk2, Ne.symm hk3])
                hm'')

/-! ## 7. Loop 2 Outer (`while (a == antecedents) == 0`) -/

/-- An antecedent ID `aid` points via `literals_begin + (aid <<< 3)` to a 0-terminated array of
valid literals `clits` in the read-only frame `R` whose clause is non-tautological and entailed by `f`. -/
def ValidAntecedent (max_var : Nat) (f : CNF Nat) (literals_begin : BitVec 64)
    (R : Mem 64 → Prop) (aid : BitVec 64) : Prop :=
  ∃ (als : BitVec 64) (clits : List (BitVec 64)),
    (∃ R', R = (word8 (literals_begin + (aid <<< 3)) als ⋆ R')) ∧
    (∃ R', R = (ZeroTermInts als clits ⋆ R')) ∧
    (∀ x ∈ clits, IsValidLit max_var x) ∧
    ClauseNonTautological (toClause clits) ∧
    CNF.EntailsClause f (toClause clits)

theorem ValidAntecedent.mono {max_var : Nat} {f : CNF Nat} {literals_begin : BitVec 64}
    {R1 R2 : Mem 64 → Prop} {aid : BitVec 64}
    (h : ValidAntecedent max_var f literals_begin R1 aid)
    (hsub : ∃ R', R2 = (R1 ⋆ R')) :
    ValidAntecedent max_var f literals_begin R2 aid := by
  obtain ⟨R', rfl⟩ := hsub
  obtain ⟨als, clits, ⟨Ra, hRa⟩, ⟨Rc, hRc⟩, hvalid, hnontaut, hent⟩ := h
  exact ⟨als, clits, ⟨Ra ⋆ R', by rw [hRa, sep_assoc]⟩, ⟨Rc ⋆ R', by rw [hRc, sep_assoc]⟩,
    hvalid, hnontaut, hent⟩

theorem bitVec_ofNat_eight_mul_toNat (aid : BitVec 64) :
    BitVec.ofNat 64 (8 * aid.toNat) = aid <<< 3 := by
  have h : BitVec.ofNat 64 (8 * aid.toNat) = 8#64 * aid := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_mul]
  rw [h]
  bv_decide

theorem ClauseTable.validAntecedent {max_var : Nat} {f : CNF Nat} {literals_begin : BitVec 64}
    {lit_ptrs : List (BitVec 64)} {clauses : Array (Option (CNF.Clause Nat))}
    {P_ro R : Mem 64 → Prop} {aid : BitVec 64}
    (hct : ClauseTable max_var literals_begin lit_ptrs clauses P_ro)
    (hsub : ∃ R_other, R = (P_ro ⋆ R_other))
    (haid : aid.toNat < lit_ptrs.length)
    (hpos : 0 < aid.toNat)
    (hne : lit_ptrs[aid.toNat] ≠ 0)
    (hcl : ∀ c, clauses[aid.toNat - 1]? = some (some c) →
      ClauseNonTautological c ∧ CNF.EntailsClause f c) :
    ValidAntecedent max_var f literals_begin R aid := by
  obtain ⟨R_other, rfl⟩ := hsub
  obtain ⟨R1, hP1⟩ := hct.1
  obtain ⟨clits, R2, hP2, hvalid, hcl_eq⟩ := hct.2 aid.toNat haid hpos hne
  obtain ⟨hnontaut, hent⟩ := hcl (toClause clits) hcl_eq
  refine ⟨lit_ptrs[aid.toNat], clits, ?_, ⟨R2 ⋆ R_other, by rw [hP2, sep_assoc]⟩,
    hvalid, hnontaut, hent⟩
  have hfocus := word8Array_focus literals_begin lit_ptrs haid
  rw [bitVec_ofNat_eight_mul_toNat] at hfocus
  exact ⟨(word8Array literals_begin (lit_ptrs.take aid.toNat) ⋆
      word8Array (literals_begin + (aid <<< 3) + 8) (lit_ptrs.drop (aid.toNat + 1))) ⋆ (R1 ⋆ R_other),
    by rw [hP1, hfocus, sep_assoc, sep_assoc]⟩

@[simp] theorem shamt_three_64 : shamt (3#64) = 3 := by decide

theorem eval_load8_of_sub {m : Mem 64} {l : Locals 64} {ea : Expr}
    {addr val : BitVec 64} {P R : Mem 64 → Prop}
    (ha : ea.eval m l = some addr)
    (hmem : m =⋆ P ⋆ R)
    (hsub : ∃ R', R = (word8 addr val ⋆ R')) :
    (Expr.load .eight ea).eval m l = some val := by
  obtain ⟨R', rfl⟩ := hsub
  rw [← sep_assoc, sep_comm P, sep_assoc] at hmem
  simp [Expr.eval, ha, load_word8 hmem]

theorem eval_load4_sext_of_sub {m : Mem 64} {l : Locals 64} {ea : Expr}
    {addr val : BitVec 64} {P R : Mem 64 → Prop}
    (ha : ea.eval m l = some addr)
    (hmem : m =⋆ P ⋆ R)
    (hsub : ∃ R', R = (int4 addr val ⋆ R'))
    (hv : IsInt32 val) :
    (Expr.op .srs (.op .slu (.load .four ea) (.literal 32)) (.literal 32)).eval m l = some val := by
  obtain ⟨R', rfl⟩ := hsub
  rw [← sep_assoc, sep_comm P, sep_assoc] at hmem
  exact eval_load4_sext ha hmem hv

theorem int4Array_sub_snoc {ant_ptr aid : BitVec 64} {init : List (BitVec 64)} {R : Mem 64 → Prop}
    (hsub : ∃ R', R = (int4Array ant_ptr (init ++ [aid]) ⋆ R')) :
    (∃ R', R = (int4Array ant_ptr init ⋆ R')) ∧
    (∃ R', R = (int4 (ant_ptr + BitVec.ofNat 64 (4 * init.length)) aid ⋆ R')) := by
  obtain ⟨R', rfl⟩ := hsub
  rw [int4Array_append, int4Array_cons, int4Array_nil, sep_emp]
  refine ⟨⟨int4 (ant_ptr + BitVec.ofNat 64 (4 * init.length)) aid ⋆ R', by rw [sep_assoc]⟩,
    ⟨int4Array ant_ptr init ⋆ R', by rw [sep_comm (int4Array ant_ptr init), sep_assoc]⟩⟩

theorem four_mul_length_append_singleton_ne_zero {aid : BitVec 64} {init : List (BitVec 64)}
    (hbound : 4 * (init ++ [aid]).length < 2 ^ 64) :
    BitVec.ofNat 64 (4 * (init.length + 1)) ≠ 0#64 := by
  intro h0
  have htoNat : (BitVec.ofNat 64 (4 * (init.length + 1))).toNat = 0 := congrArg BitVec.toNat h0
  simp only [List.length_append, List.length_singleton] at hbound
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hbound] at htoNat
  omega

theorem eval_outer_cond_true {m : Mem 64} {l : Locals 64} {ant_ptr aid : BitVec 64}
    {init : List (BitVec 64)}
    (ha : l["a"]? = some (ant_ptr + BitVec.ofNat 64 (4 * (init ++ [aid]).length)))
    (hant : l["antecedents"]? = some ant_ptr)
    (hbound : 4 * (init ++ [aid]).length < 2 ^ 64) :
    (bedrock2_expr:((a == antecedents) == 0)).eval m l = some 1 := by
  have hne := four_mul_length_append_singleton_ne_zero hbound
  simp [Expr.eval, ha, hant, hne]

theorem add_four_mul_succ_sub_four (ant_ptr : BitVec 64) (n : Nat) :
    ant_ptr + BitVec.ofNat 64 (4 * (n + 1)) - 4#64 =
      ant_ptr + BitVec.ofNat 64 (4 * n) := by
  have h : BitVec.ofNat 64 (4 * (n + 1)) = BitVec.ofNat 64 (4 * n) + 4#64 := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_add, Nat.mul_add]
  have hsub : ∀ a d : BitVec 64, a + (d + 4#64) - 4#64 = a + d := by bv_decide
  rw [h, hsub]

theorem list_reverseRecOn {α : Type _} {motive : List α → Prop} (xs : List α)
    (nil : motive [])
    (append_singleton : ∀ (init : List α) (a : α), motive init → motive (init ++ [a])) :
    motive xs := by
  rw [← List.reverse_reverse xs]
  induction xs.reverse with
  | nil => exact nil
  | cons a as ih =>
    rw [List.reverse_cons]
    exact append_singleton as.reverse a ih

theorem add_one_add_ofNat_length (stat_val aid : BitVec 64) (init : List (BitVec 64)) :
    stat_val + 1 + BitVec.ofNat 64 init.length =
      stat_val + BitVec.ofNat 64 (init ++ [aid]).length := by
  have h : BitVec.ofNat 64 (init ++ [aid]).length = 1 + BitVec.ofNat 64 init.length := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_add, Nat.add_comm]
  rw [h, BitVec.add_assoc]

/-- Specification of Loop 2 (`while (a == antecedents) == 0`) in
`br_check_clause_strictly_by_resolution`: scans `pref` in reverse order, resolving each
antecedent clause against `marks_begin` and preserving `MarksEntailed f marks`. -/
theorem strict_outer_loop_ok {e : Env} {B : Nat} {t : Trace 64} {m : Mem 64} {l : Locals 64}
    {max_var : Nat} {f : CNF Nat}
    {st id_val ant_ptr literals_begin marks_begin stat_val first_val : BitVec 64}
    {pref marks : List (BitVec 64)} {R : Mem 64 → Prop}
    {post : Trace 64 → Mem 64 → Locals 64 → Prop}
    (hst : l["st"]? = some st)
    (hid : l["id"]? = some id_val)
    (hant : l["antecedents"]? = some ant_ptr)
    (hlb : l["literals_begin"]? = some literals_begin)
    (hmb : l["marks_begin"]? = some marks_begin)
    (ha : l["a"]? = some (ant_ptr + BitVec.ofNat 64 (4 * pref.length)))
    (hstat : l["stat_resolved"]? = some stat_val)
    (hrs : l["resolvent_size"]? = some (BitVec.ofNat 64 (marksCount marks)))
    (hfirst : l["first"]? = some first_val)
    (hwf : MarksWF marks)
    (hlen : max_var < marks.length)
    (hbound : 4 * pref.length < 2 ^ 64)
    (hpref : ∀ aid ∈ pref, IsInt32 aid ∧ aid ≠ 0 ∧ aid.slt 0 = false ∧
      ValidAntecedent max_var f literals_begin R aid)
    (hent_init : first_val = 0 → MarksEntailed f marks)
    (hmem : m =⋆ byte1Array marks_begin marks ⋆ R)
    (hsub_ant : ∃ R', R = (int4Array ant_ptr pref ⋆ R'))
    (hsub_st : ∃ v0 R', R = (word8 (st + 144) v0 ⋆ R'))
    (hpost : ∀ m' l' (marks' : List (BitVec 64)) (first_val' : BitVec 64),
      marks'.length = marks.length →
      MarksWF marks' →
      (first_val' = 0 → MarksEntailed f marks') →
      l'["st"]? = some st →
      l'["id"]? = some id_val →
      l'["marks_begin"]? = some marks_begin →
      l'["literals"]? = l["literals"]? →
      l'["stat_resolved"]? = some (stat_val + BitVec.ofNat 64 pref.length) →
      l'["resolvent_size"]? = some (BitVec.ofNat 64 (marksCount marks')) →
      l'["first"]? = some first_val' →
      (m' =⋆ byte1Array marks_begin marks' ⋆ R) →
      post t m' l') :
    Exec lratFailExt e B (bedrock2_cmd:(
      while (a == antecedents) == 0 {
        a = a - 4;
        aid = (load4(a) << 32) .>> 32;
        als = load8(literals_begin + (aid << 3));
        stat_resolved = stat_resolved + 1;
        unit = 0;
        l = als;
        lit = (load4(l) << 32) .>> 32;
        while lit {
          idx = lit .< 0 ? -lit : lit;
          m = marks_begin + idx;
          mark = (load1(m) << 56) .>> 56;
          if mark == 0 {
            store1(m, (lit .>> 63) | 1);
            resolvent_size = resolvent_size + 1
          } else {
            if lit .< 0 {
              mark = -mark
            };
            if (0 .< mark) == 0 {
              if unit {
                store8(st + 144, stat_resolved);
                interact lrat_fail(4, id, unit, lit, aid)
              };
              unit = lit
            }
          };
          l = l + 4;
          lit = (load4(l) << 32) .>> 32
        };
        if first {
          if unit {
            store8(st + 144, stat_resolved);
            interact lrat_fail(4, id, -unit, unit, aid)
          };
          first = 0
        } else {
          if unit == 0 {
            store8(st + 144, stat_resolved);
            interact lrat_fail(5, id, aid, 0, 0)
          } else {
            resolvent_size = resolvent_size - 1;
            idx = unit .< 0 ? -unit : unit;
            m = marks_begin + idx;
            store1(m, 0)
          }
        }
      }
    )) t m l post := by
  induction pref using list_reverseRecOn generalizing m l marks stat_val first_val with
  | nil =>
    simp only [List.length_nil, Nat.mul_zero, BitVec.add_zero] at ha
    refine .while_false _ _ _ _ _ _ _ _ (by simp [Expr.eval, ha, hant]) rfl ?_
    exact hpost m l marks first_val rfl hwf hent_init hst hid hmb rfl (by simpa using hstat)
      hrs hfirst hmem
  | append_singleton init aid ih =>
    obtain ⟨haid32, _, _, als, clits, hsub_als, hsub_clits, hclits_valid, hclits_nontaut, hclits_ent⟩ :=
      hpref aid (by simp)
    obtain ⟨hsub_init, hsub_aid⟩ := int4Array_sub_snoc hsub_ant
    have hbound_init : 4 * init.length < 2 ^ 64 := by
      simp only [List.length_append, List.length_singleton] at hbound; omega
    refine Exec.while_true_cps (eval_outer_cond_true ha hant hbound) (by decide) ?_
    -- a = a - 4
    refine Exec.seq_cps (Exec.set_cps (v := ant_ptr + BitVec.ofNat 64 (4 * init.length))
      (by simp [Expr.eval, ha, add_four_mul_succ_sub_four]) ?_)
    -- aid = (load4(a) << 32) .>> 32
    refine Exec.seq_cps (Exec.set_cps
      (eval_load4_sext_of_sub (by simp [Expr.eval]) hmem hsub_aid haid32) ?_)
    -- als = load8(literals_begin + (aid << 3))
    refine Exec.seq_cps (Exec.set_cps
      (eval_load8_of_sub (by simp [Expr.eval, hlb]) hmem hsub_als) ?_)
    -- stat_resolved = stat_resolved + 1
    refine Exec.seq_cps (Exec.set_cps (v := stat_val + 1) (by simp [Expr.eval, hstat]) ?_)
    -- unit = 0
    refine Exec.seq_cps (Exec.set_cps (v := 0) (by simp [Expr.eval]) ?_)
    -- l = als
    refine Exec.seq_cps (Exec.set_cps (v := als) (by simp [Expr.eval]) ?_)
    -- lit = (load4(l) << 32) .>> 32
    refine Exec.seq_cps (Exec.set_cps
      (eval_load4_zeroTermInts_head_of_sub (by simp [Expr.eval]) hmem hsub_clits
        (fun x hx => (hclits_valid x hx).1)) ?_)
    -- while lit { ... }
    refine Exec.seq_cps (strict_inner_loop_ok (id_val := id_val) (aid_val := aid) (stat_val := stat_val + 1)
      (by simp [hst]) (by simp [hid]) (by simp) (by simp [hmb]) (by simp)
      (by simp [hrs]) (by simp) (by simp) (by simp)
      (InnerInv.init hwf) hlen hclits_valid hmem hsub_clits hsub_st
      fun m1 l1 marks1 unit_val1 hinv1 hrs1 hunit1 hrest1 hm1 => ?_)
    have hl1 (k : String) (hk : (k != "idx" && k != "m" && k != "mark" &&
        k != "resolvent_size" && k != "unit" && k != "l" && k != "lit") = true) :
        l1[k]? = (((((((l.insert "a" (ant_ptr + BitVec.ofNat 64 (4 * init.length))).insert "aid" aid).insert
          "als" als).insert "stat_resolved" (stat_val + 1)).insert "unit" 0).insert
          "l" als).insert "lit" ((clits ++ [0])[0]'(by simp)))[k]? := by
      simp only [Bool.and_eq_true, bne_iff_ne] at hk
      exact hrest1 k hk.1.1.1.1.1.1 hk.1.1.1.1.1.2 hk.1.1.1.1.2 hk.1.1.1.2 hk.1.1.2 hk.1.2 hk.2
    -- if first { ... } else { ... }
    refine Exec.cond_cps (v := first_val)
      (by simp [Expr.eval, hl1 "first" (by decide), hfirst])
      (fun hfirst_nz => ?_) (fun hfirst_z => ?_)
    · -- Branch 1: first != 0
      refine Exec.seq_cps ?_
      refine Exec.cond_cps (v := unit_val1)
        (by simp [Expr.eval, hunit1]) (fun hunit_nz => ?_) (fun hunit_z => ?_)
      · exact exec_store8_stat_and_fail (st := st) (stat_val := stat_val + 1)
          (args := [4#64, id_val, -unit_val1, unit_val1, aid])
          (by simp [hl1 "st" (by decide), hst])
          (by simp [hl1 "stat_resolved" (by decide)])
          hm1 hsub_st
          (fun _ => by simp [evalArgs, Expr.eval, hl1 "id" (by decide),
            hunit1, hl1 "aid" (by decide), hid])
      · subst hunit_z
        refine .skip _ _ _ _ _ ?_
        -- first = 0
        refine Exec.set_cps (v := 0) (by simp [Expr.eval]) ?_
        have hinv1_cl : InnerInv max_var marks (toClause clits).literals marks1 0 := by
          simpa using hinv1
        refine ih (stat_val := stat_val + 1) (first_val := 0)
          (by simp [hl1 "st" (by decide), hst])
          (by simp [hl1 "id" (by decide), hid])
          (by simp [hl1 "antecedents" (by decide), hant])
          (by simp [hl1 "literals_begin" (by decide), hlb])
          (by simp [hl1 "marks_begin" (by decide), hmb])
          (by simp [hl1 "a" (by decide)])
          (by simp [hl1 "stat_resolved" (by decide)])
          (by simp [hrs1])
          (by simp)
          hinv1.wf
          (by rw [hinv1.len_eq]; exact hlen)
          hbound_init
          (fun x hx => hpref x (List.mem_append_left _ hx))
          (fun _ a hfa => hinv1_cl.finish_first (hclits_ent a hfa))
          hm1
          hsub_init
          (fun m' l' marks' first_val' hlen' hwf' hent' hst' hid' hmb' hlit' hstat' hrs' hfirst' hm' =>
            hpost m' l' marks' first_val' (hlen'.trans hinv1.len_eq) hwf' hent' hst' hid' hmb'
              (by rw [hlit']; simp [hl1 "literals" (by decide)])
              (by rw [hstat', add_one_add_ofNat_length])
              hrs' hfirst' hm')
    · -- Branch 2: first == 0
      have hent : MarksEntailed f marks := hent_init hfirst_z
      refine Exec.cond_cps (v := if unit_val1 = 0 then 1 else 0)
        (by simp [Expr.eval, hunit1]) (fun hunit_eq0 => ?_) (fun hunit_ne0 => ?_)
      · exact exec_store8_stat_and_fail (st := st) (stat_val := stat_val + 1)
          (args := [5#64, id_val, aid, 0, 0])
          (by simp [hl1 "st" (by decide), hst])
          (by simp [hl1 "stat_resolved" (by decide)])
          hm1 hsub_st
          (fun _ => by simp [evalArgs, Expr.eval, hl1 "id" (by decide),
            hl1 "aid" (by decide), hid])
      · have hu_ne : unit_val1 ≠ 0 := by intro h0; simp [h0] at hunit_ne0
        have hinv1_cl : InnerInv max_var marks (toClause clits).literals marks1 unit_val1 := by
          simpa using hinv1
        rcases hinv1_cl.unit_spec with rfl | ⟨hu_valid, _, hu_mark⟩
        · exact absurd rfl hu_ne
        · have hu_lt : (toLiteral unit_val1).1 < marks1.length := by
            rw [hinv1.len_eq]; exact Nat.lt_of_le_of_lt hu_valid.2.2.1 hlen
          have hcnt : marksCount (marks1.set (toLiteral unit_val1).1 0) + 1 = marksCount marks1 :=
            marksCount_set_zero_of_ne_zero hu_mark (encodePol_ne_zero _)
          have hrs_sub : BitVec.ofNat 64 (marksCount marks1) - 1 =
              BitVec.ofNat 64 (marksCount (marks1.set (toLiteral unit_val1).1 0)) :=
            ofNat_sub_one_of_succ hcnt
          -- resolvent_size = resolvent_size - 1
          refine Exec.seq_cps (Exec.set_cps
            (v := BitVec.ofNat 64 (marksCount (marks1.set (toLiteral unit_val1).1 0)))
            (by simp [Expr.eval, hrs1]; exact hrs_sub) ?_)
          -- idx = unit .< 0 ? -unit : unit
          refine Exec.seq_cps (Exec.set_cps
            (eval_bvAbs_unit (v := unit_val1) (by simp [hunit1])) ?_)
          -- m = marks_begin + idx
          refine Exec.seq_cps (Exec.set_cps
            (v := marks_begin + BitVec.ofNat 64 (toLiteral unit_val1).1)
            (by simp [Expr.eval, hl1 "marks_begin" (by decide), hmb, ← bvAbs_eq_ofNat_toLiteral_fst]) ?_)
          -- store1(m, 0)
          refine store_byte1Array_elem hu_lt (by simp [Expr.eval])
            (v := 0) (by simp [Expr.eval]) hm1 fun m2 hm2 => ?_
          refine ih (stat_val := stat_val + 1) (first_val := first_val)
            (by simp [hl1 "st" (by decide), hst])
            (by simp [hl1 "id" (by decide), hid])
            (by simp [hl1 "antecedents" (by decide), hant])
            (by simp [hl1 "literals_begin" (by decide), hlb])
            (by simp [hl1 "marks_begin" (by decide), hmb])
            (by simp [hl1 "a" (by decide)])
            (by simp [hl1 "stat_resolved" (by decide)])
            (by simp)
            (by simp [hl1 "first" (by decide), hfirst])
            (marksWF_set_zero hinv1.wf hu_lt)
            (by simp [hinv1.len_eq, hlen])
            hbound_init
            (fun x hx => hpref x (List.mem_append_left _ hx))
            (fun _ a hfa => hinv1_cl.finish_resolve hclits_nontaut hu_ne (hent a hfa) (hclits_ent a hfa))
            hm2
            hsub_init
            (fun m' l' marks' first_val' hlen' hwf' hent' hst' hid' hmb' hlit' hstat' hrs' hfirst' hm' =>
              hpost m' l' marks' first_val'
                (by simpa [hinv1.len_eq] using hlen')
                hwf' hent' hst' hid' hmb'
                (by rw [hlit']; simp [hl1 "literals" (by decide)])
                (by rw [hstat', add_one_add_ofNat_length])
                hrs' hfirst' hm')

/-! ## 8. Top-Level Specification of `br_check_clause_strictly_by_resolution` -/

theorem kernelState_sub_literals_begin (st : BitVec 64) (k : KernelFields) (R_other : Mem 64 → Prop) :
    ∃ R', (kernelState st k ⋆ R_other) = (word8 (st + 16) k.literals_begin ⋆ R') := by
  refine ⟨(word8Array st (k.toList.take 2) ⋆ word8Array (st + 16 + 8) (k.toList.drop 3)) ⋆ R_other, ?_⟩
  have h := word8Array_focus st k.toList (i := 2) (by simp [KernelFields.toList])
  change (word8Array st k.toList ⋆ R_other) = _
  rw [h, sep_assoc]
  rfl

theorem kernelState_sub_marks_begin (st : BitVec 64) (k : KernelFields) (R_other : Mem 64 → Prop) :
    ∃ R', (kernelState st k ⋆ R_other) = (word8 (st + 32) k.marks_begin ⋆ R') := by
  refine ⟨(word8Array st (k.toList.take 4) ⋆ word8Array (st + 32 + 8) (k.toList.drop 5)) ⋆ R_other, ?_⟩
  have h := word8Array_focus st k.toList (i := 4) (by simp [KernelFields.toList])
  change (word8Array st k.toList ⋆ R_other) = _
  rw [h, sep_assoc]
  rfl

theorem kernelState_sub_stat_resolved_val (st : BitVec 64) (k : KernelFields) (R_other : Mem 64 → Prop) :
    ∃ R', (kernelState st k ⋆ R_other) = (word8 (st + 144) k.stat_resolved ⋆ R') := by
  refine ⟨(word8Array st (k.toList.take 18) ⋆ word8Array (st + 144 + 8) (k.toList.drop 19)) ⋆ R_other, ?_⟩
  have h := word8Array_focus st k.toList (i := 18) (by simp [KernelFields.toList])
  change (word8Array st k.toList ⋆ R_other) = _
  rw [h, sep_assoc]
  rfl

theorem kernelState_sub_stat_resolved (st : BitVec 64) (k : KernelFields) (R_other : Mem 64 → Prop) :
    ∃ v0 R', (kernelState st k ⋆ R_other) = (word8 (st + 144) v0 ⋆ R') :=
  ⟨k.stat_resolved, kernelState_sub_stat_resolved_val st k R_other⟩

theorem kernelState_store_stat_resolved_in_frame {e : Env} {B : Nat} {ea ev : Expr}
    {t : Trace 64} {m : Mem 64} {l : Locals 64}
    {post : Trace 64 → Mem 64 → Locals 64 → Prop}
    {st v : BitVec 64} {k : KernelFields} {P R_ro : Mem 64 → Prop}
    (ha : ea.eval m l = some (st + 144))
    (hv : ev.eval m l = some v)
    (hmem : m =⋆ P ⋆ (kernelState st k ⋆ R_ro))
    (hpost : ∀ m', (m' =⋆ P ⋆ (kernelState st { k with stat_resolved := v } ⋆ R_ro)) → post t m' l) :
    Exec lratFailExt e B (.store .eight ea ev) t m l post := by
  rw [← sep_assoc, sep_comm P, sep_assoc] at hmem
  exact store_word8Array_elem (xs := k.toList) (i := 18) (by simp [KernelFields.toList]) ha hv hmem fun m' hm' => by
    rw [← sep_assoc, sep_comm (word8Array st (k.toList.set 18 v)), sep_assoc] at hm'
    exact hpost m' hm'

/-- Full specification of the body of `br_check_clause_strictly_by_resolution`:
starting with `marks_begin` holding `n` zero bytes (`max_var < n < 2 ^ 64`),
verifies that all `ants` are non-negative, resolves their clauses in reverse order,
checks that `clause_lits` matches the resulting resolvent, restores `marks_begin` to `n`
zero bytes, updates `k.stat_resolved` by `ants.length`, and establishes
`CNF.EntailsClause f (toClause clause_lits)`. -/
theorem br_check_clause_strictly_by_resolution_body_ok {e : Env} {B : Nat}
    {t : Trace 64} {m : Mem 64} {l : Locals 64}
    {max_var n : Nat} {f : CNF Nat}
    {st id_val lits_ptr ant_ptr : BitVec 64} {k : KernelFields}
    {clause_lits ants : List (BitVec 64)} {R_ro : Mem 64 → Prop}
    {post : Trace 64 → Mem 64 → Locals 64 → Prop}
    (hst : l["st"]? = some st)
    (hid : l["id"]? = some id_val)
    (hlits : l["literals"]? = some lits_ptr)
    (hant : l["antecedents"]? = some ant_ptr)
    (hlen : max_var < n)
    (hn_bound : n < 2 ^ 64)
    (hants_bound : 4 * ants.length < 2 ^ 64)
    (hants_int : ∀ x ∈ ants, IsInt32 x ∧ x ≠ 0)
    (hants_valid : ∀ aid ∈ ants, aid.slt 0 = false →
      ValidAntecedent max_var f k.literals_begin R_ro aid)
    (hclause_valid : ∀ x ∈ clause_lits, IsValidLit max_var x)
    (hmem : m =⋆ byte1Array k.marks_begin (List.replicate n 0) ⋆ (kernelState st k ⋆ R_ro))
    (hsub_ants : ∃ R', R_ro = (ZeroTermInts ant_ptr ants ⋆ R'))
    (hsub_lits : ∃ R', R_ro = (ZeroTermInts lits_ptr clause_lits ⋆ R'))
    (hpost : CNF.EntailsClause f (toClause clause_lits) →
      ∀ m' l',
        (m' =⋆ byte1Array k.marks_begin (List.replicate n 0) ⋆
          (kernelState st { k with stat_resolved := k.stat_resolved + BitVec.ofNat 64 ants.length } ⋆ R_ro)) →
        post t m' l') :
    Exec lratFailExt e B br_check_clause_strictly_by_resolution.2.body t m l post := by
  have hmem_ants : ∃ R_rest, (m =⋆ ZeroTermInts ant_ptr ants ⋆ R_rest) := by
    obtain ⟨R', hR⟩ := hsub_ants
    refine ⟨byte1Array k.marks_begin (List.replicate n 0) ⋆ kernelState st k ⋆ R', ?_⟩
    rw [hR, ← sep_assoc, ← sep_assoc,
      sep_comm (byte1Array k.marks_begin (List.replicate n 0) ⋆ kernelState st k), sep_assoc] at hmem
    exact hmem
  obtain ⟨R_ants_rest, hmem_ants⟩ := hmem_ants
  -- a = antecedents
  refine Exec.seq_cps (Exec.set_cps (v := ant_ptr) (by simp [Expr.eval, hant]) ?_)
  -- aid = (load4(a) << 32) .>> 32
  refine Exec.seq_cps (Exec.set_cps
    (eval_load4_zeroTermInts_head (by simp [Expr.eval]) hmem_ants (fun x hx => (hants_int x hx).1)) ?_)
  -- Loop 1: while aid { ... }
  refine Exec.seq_cps (strict_loop1_ok (id_val := id_val)
    (by simp [hid]) (by simp) (by simp) hants_int hmem_ants
    fun hants_pos l1 ha1 haid1 hrest1 => ?_)
  have hl1 (key : String) (hk : (key != "a" && key != "aid") = true) :
      l1[key]? = l[key]? := by
    simp only [Bool.and_eq_true, bne_iff_ne] at hk
    rw [hrest1 key hk.1 hk.2]
    simp [Ne.symm hk.1, Ne.symm hk.2]
  -- literals_begin = load8(st + 16)
  refine Exec.seq_cps (Exec.set_cps
    (eval_load8_of_sub (by simp [Expr.eval, hl1 "st" (by decide), hst]) hmem
      (kernelState_sub_literals_begin st k R_ro)) ?_)
  -- marks_begin = load8(st + 32)
  refine Exec.seq_cps (Exec.set_cps
    (eval_load8_of_sub (by simp [Expr.eval, hl1 "st" (by decide), hst]) hmem
      (kernelState_sub_marks_begin st k R_ro)) ?_)
  -- stat_resolved = load8(st + 144)
  refine Exec.seq_cps (Exec.set_cps
    (eval_load8_of_sub (by simp [Expr.eval, hl1 "st" (by decide), hst]) hmem
      (kernelState_sub_stat_resolved_val st k R_ro)) ?_)
  -- resolvent_size = 0
  refine Exec.seq_cps (Exec.set_cps (v := BitVec.ofNat 64 (marksCount (List.replicate n 0)))
    (by rw [marksCount_replicate_zero]; rfl) ?_)
  -- first = 1
  refine Exec.seq_cps (Exec.set_cps (v := 1) (by simp [Expr.eval]) ?_)
  -- Prepare Loop 2 outer hypotheses
  have hsub_ant_arr : ∃ R', (kernelState st k ⋆ R_ro) = (int4Array ant_ptr ants ⋆ R') := by
    obtain ⟨R', hR⟩ := hsub_ants
    refine ⟨int4 (ant_ptr + BitVec.ofNat 64 (4 * ants.length)) 0 ⋆ (kernelState st k ⋆ R'), ?_⟩
    rw [hR, zeroTermInts_eq_append, ← sep_assoc, sep_comm (kernelState st k), sep_assoc, sep_assoc]
  have hpref_valid : ∀ aid ∈ ants, IsInt32 aid ∧ aid ≠ 0 ∧ aid.slt 0 = false ∧
      ValidAntecedent max_var f k.literals_begin (kernelState st k ⋆ R_ro) aid := by
    intro aid haid
    exact ⟨(hants_int aid haid).1, (hants_int aid haid).2, hants_pos aid haid,
      (hants_valid aid haid (hants_pos aid haid)).mono
        ⟨kernelState st k, by rw [sep_comm]⟩⟩
  -- Loop 2 outer: while (a == antecedents) == 0 { ... }
  refine Exec.seq_cps (strict_outer_loop_ok (id_val := id_val) (stat_val := k.stat_resolved) (first_val := 1)
    (by simp [hl1 "st" (by decide), hst])
    (by simp [hl1 "id" (by decide), hid])
    (by simp [hl1 "antecedents" (by decide), hant])
    (by simp) (by simp)
    (by simp [ha1])
    (by simp) (by simp) (by simp)
    (marksWF_replicate n)
    (by simp [hlen])
    hants_bound
    hpref_valid
    (fun h10 => absurd h10 (by decide))
    hmem
    hsub_ant_arr
    (kernelState_sub_stat_resolved st k R_ro)
    fun m1 l2 marks1 first_val1 hlen1 hwf1 hent1 hst2 hid2 hmb2 hlit2 hstat2 hrs2 hfirst2 hm1 => ?_)
  simp only [List.length_replicate] at hlen1
  have hlits2 : l2["literals"]? = some lits_ptr := by
    rw [hlit2]; simp [hl1 "literals" (by decide), hlits]
  -- store8(st + 144, stat_resolved)
  refine Exec.seq_cps (kernelState_store_stat_resolved_in_frame
    (v := k.stat_resolved + BitVec.ofNat 64 ants.length)
    (by simp [Expr.eval, hst2]) (by simp [Expr.eval, hstat2]) hm1 fun m2 hm2 => ?_)
  -- if first { interact lrat_fail(3, id, 0, 0, 0) }
  refine Exec.seq_cps ?_
  refine Exec.cond_cps (v := first_val1)
    (by simp [Expr.eval, hfirst2]) (fun hfirst_nz => ?_) (fun hfirst_z => ?_)
  · exact exec_lrat_fail (args := [3, id_val, 0, 0, 0])
      (by simp [evalArgs, Expr.eval, hid2])
  · have hent_marks1 : MarksEntailed f marks1 := hent1 hfirst_z
    refine .skip _ _ _ _ _ ?_
    -- l = literals
    refine Exec.seq_cps (Exec.set_cps (v := lits_ptr) (by simp [Expr.eval, hlits2]) ?_)
    -- lit = (load4(l) << 32) .>> 32
    have hsub_lits_after : ∃ R',
        (kernelState st { k with stat_resolved := k.stat_resolved + BitVec.ofNat 64 ants.length } ⋆ R_ro) =
          (ZeroTermInts lits_ptr clause_lits ⋆ R') := by
      obtain ⟨R', hR⟩ := hsub_lits
      refine ⟨kernelState st { k with stat_resolved := k.stat_resolved + BitVec.ofNat 64 ants.length } ⋆ R', ?_⟩
      rw [hR, ← sep_assoc,
        sep_comm (kernelState st { k with stat_resolved := k.stat_resolved + BitVec.ofNat 64 ants.length }),
        sep_assoc]
    refine Exec.seq_cps (Exec.set_cps
      (eval_load4_zeroTermInts_head_of_sub (by simp [Expr.eval]) hm2 hsub_lits_after
        (fun x hx => (hclause_valid x hx).1)) ?_)
    -- Loop 3: while lit { ... }
    refine Exec.seq_cps (strict_loop3_ok (id_val := id_val) (c := toClause clause_lits) (marks₀ := marks1)
      (by simp [hid2]) (by simp [hmb2]) (by simp [hrs2]) (by simp) (by simp)
      hwf1 (by omega)
      (fun x hx => ⟨hclause_valid x hx, by simp [List.mem_map_of_mem hx]⟩)
      (fun a hsa => Or.inl hsa)
      hm2 hsub_lits_after
      fun m3 l3 marks2 hlen2 hwf2 hid3 hrs3 hsat3 hm3 => ?_)
    -- if resolvent_size { interact lrat_fail(8, id, resolvent_size, 0, 0) }
    refine Exec.cond_cps (v := BitVec.ofNat 64 (marksCount marks2))
      (by simp [Expr.eval, hrs3]) (fun hnz => ?_) (fun hz => ?_)
    · exact exec_lrat_fail (args := [8, id_val, BitVec.ofNat 64 (marksCount marks2), 0, 0])
        (by simp [evalArgs, Expr.eval, hid3, hrs3])
    · refine .skip _ _ _ _ _ ?_
      have hlen2_n : marks2.length = n := hlen2.trans hlen1
      have hcnt_le : marksCount marks2 ≤ n := hlen2_n ▸ marksCount_le_length marks2
      have hcnt0 : marksCount marks2 = 0 := by
        have htoNat := congrArg BitVec.toNat hz
        simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hcnt_le hn_bound)] at htoNat
        exact htoNat
      have hmarks2_eq : marks2 = List.replicate n 0 := by
        rw [← hlen2_n]
        exact eq_replicate_zero_of_marksCount_eq_zero hcnt0
      rw [hmarks2_eq] at hm3
      have hent_clause : CNF.EntailsClause f (toClause clause_lits) := by
        intro a hfa
        rcases hsat3 a (hent_marks1 a hfa) with hms | hcsat
        · exact False.elim (not_marksSat_of_marksCount_eq_zero hcnt0 a hms)
        · exact hcsat
      exact hpost hent_clause m3 l3 hm3

/-- `call`-level specification of `br_check_clause_strictly_by_resolution` matching
`LratTrimCheckProof.lean`: establishes `CNF.EntailsClause f (toClause clause_lits)`,
restores `marks_begin` to `n` zero bytes, and increments `k.stat_resolved` by `ants.length`. -/
theorem call_br_check_clause_strictly_by_resolution {e : Env} {B : Nat}
    {t : Trace 64} {m : Mem 64}
    {max_var n : Nat} {f : CNF Nat}
    {st id_val lits_ptr ant_ptr : BitVec 64} {k : KernelFields}
    {clause_lits ants : List (BitVec 64)} {R_ro : Mem 64 → Prop}
    {post : Trace 64 → Mem 64 → List (BitVec 64) → Prop}
    (hfn : e.lookup br_check_clause_strictly_by_resolution.1 = some br_check_clause_strictly_by_resolution.2)
    (hlen : max_var < n)
    (hn_bound : n < 2 ^ 64)
    (hants_bound : 4 * ants.length < 2 ^ 64)
    (hants_int : ∀ x ∈ ants, IsInt32 x ∧ x ≠ 0)
    (hants_valid : ∀ aid ∈ ants, aid.slt 0 = false →
      ValidAntecedent max_var f k.literals_begin R_ro aid)
    (hclause_valid : ∀ x ∈ clause_lits, IsValidLit max_var x)
    (hmem : m =⋆ byte1Array k.marks_begin (List.replicate n 0) ⋆ (kernelState st k ⋆ R_ro))
    (hsub_ants : ∃ R', R_ro = (ZeroTermInts ant_ptr ants ⋆ R'))
    (hsub_lits : ∃ R', R_ro = (ZeroTermInts lits_ptr clause_lits ⋆ R'))
    (hpost : CNF.EntailsClause f (toClause clause_lits) →
      ∀ m',
        (m' =⋆ byte1Array k.marks_begin (List.replicate n 0) ⋆
          (kernelState st { k with stat_resolved := k.stat_resolved + BitVec.ofNat 64 ants.length } ⋆ R_ro)) →
        post t m' []) :
    call lratFailExt e B br_check_clause_strictly_by_resolution.1 t m
      [st, id_val, lits_ptr, ant_ptr] post := by
  refine call.of_body hfn rfl ?_
  exact br_check_clause_strictly_by_resolution_body_ok (id_val := id_val)
    (by simp [br_check_clause_strictly_by_resolution, insertMany_cons, insertMany_nil])
    (by simp [br_check_clause_strictly_by_resolution, insertMany_cons, insertMany_nil])
    (by simp [br_check_clause_strictly_by_resolution, insertMany_cons, insertMany_nil])
    (by simp [br_check_clause_strictly_by_resolution, insertMany_cons, insertMany_nil])
    hlen hn_bound hants_bound hants_int hants_valid hclause_valid hmem hsub_ants hsub_lits
    (fun hent m' _ hm' => ⟨[], rfl, hpost hent m' hm'⟩)

/-- `Exec.call` specification of `br_check_clause_strictly_by_resolution(st, id, literals, antecedents)`. -/
theorem br_check_clause_strictly_by_resolution_call_ok {e : Env} {B : Nat}
    {t : Trace 64} {m : Mem 64} {l : Locals 64}
    {est eid elits eants : Expr}
    {max_var n : Nat} {f : CNF Nat}
    {st id_val lits_ptr ant_ptr : BitVec 64} {k : KernelFields}
    {clause_lits ants : List (BitVec 64)} {R_ro : Mem 64 → Prop}
    {post : Trace 64 → Mem 64 → Locals 64 → Prop}
    (hf : e.lookup br_check_clause_strictly_by_resolution.1 = some br_check_clause_strictly_by_resolution.2)
    (hest : est.eval m l = some st)
    (heid : eid.eval m l = some id_val)
    (helits : elits.eval m l = some lits_ptr)
    (heants : eants.eval m l = some ant_ptr)
    (hlen : max_var < n)
    (hn_bound : n < 2 ^ 64)
    (hants_bound : 4 * ants.length < 2 ^ 64)
    (hants_int : ∀ x ∈ ants, IsInt32 x ∧ x ≠ 0)
    (hants_valid : ∀ aid ∈ ants, aid.slt 0 = false →
      ValidAntecedent max_var f k.literals_begin R_ro aid)
    (hclause_valid : ∀ x ∈ clause_lits, IsValidLit max_var x)
    (hmem : m =⋆ byte1Array k.marks_begin (List.replicate n 0) ⋆ (kernelState st k ⋆ R_ro))
    (hsub_ants : ∃ R', R_ro = (ZeroTermInts ant_ptr ants ⋆ R'))
    (hsub_lits : ∃ R', R_ro = (ZeroTermInts lits_ptr clause_lits ⋆ R'))
    (hpost : CNF.EntailsClause f (toClause clause_lits) →
      ∀ m',
        (m' =⋆ byte1Array k.marks_begin (List.replicate n 0) ⋆
          (kernelState st { k with stat_resolved := k.stat_resolved + BitVec.ofNat 64 ants.length } ⋆ R_ro)) →
        post t m' l) :
    Exec lratFailExt e B
      (.call [] br_check_clause_strictly_by_resolution.1 [est, eid, elits, eants]) t m l post := by
  refine Exec.call_cps (args := [st, id_val, lits_ptr, ant_ptr])
    (by simp [evalArgs, hest, heid, helits, heants])
    (call_br_check_clause_strictly_by_resolution hf hlen hn_bound hants_bound hants_int
      hants_valid hclause_valid hmem hsub_ants hsub_lits fun hent m' hm' => ?_)
  exact ⟨l, putManyZip_nil l, hpost hent m' hm'⟩

end Kraken.Bedrock2.Test
