module

public import Kraken.Bedrock2.Test.LratTrimSpec
import Kraken.Bedrock2.Notation
import all Kraken.Separation
import Std.Tactic.BVDecide
meta import Std.Tactic.BVDecide.Reflect
import all Std.Tactic.BVDecide.LRAT.Internal.Assignment
import all Std.Tactic.BVDecide.LRAT.Internal.Basic
import all Std.Tactic.BVDecide.LRAT.Internal.Rup

@[expose] public section

open Std Std.ExtHashMap Std.Sat
open Std.Tactic.BVDecide.LRAT
open Std.Tactic.BVDecide.LRAT.Internal

namespace Kraken.Bedrock2.Test

/-! ## 0. Private Tactical Helpers -/

@[simp] private theorem shamt_3 : shamt 3#64 = 3 := by decide
@[simp] private theorem shamt_63 : shamt 63#64 = 63 := by decide

@[simp] private theorem ite_one_zero_ne_zero (c : Bool) :
    ((if c then 1#64 else 0#64) ≠ (0 : BitVec 64)) ↔ c = true := by cases c <;> decide

@[simp] private theorem ite_one_zero_eq_zero (c : Bool) :
    ((if c then 1#64 else 0#64) = (0 : BitVec 64)) ↔ c = false := by cases c <;> decide

@[simp] private theorem ite_zero_one_ne_zero (c : Bool) :
    ((if c then 0#64 else 1#64) ≠ (0 : BitVec 64)) ↔ c = false := by cases c <;> decide

@[simp] private theorem ite_zero_one_eq_zero (c : Bool) :
    ((if c then 0#64 else 1#64) = (0 : BitVec 64)) ↔ c = true := by cases c <;> decide

@[simp] private theorem ite_zero_one_ne_zero_prop (P : Prop) [Decidable P] :
    ((if P then 0#64 else 1#64) ≠ (0 : BitVec 64)) ↔ ¬ P := by by_cases P <;> simp

@[simp] private theorem ite_zero_one_eq_zero_prop (P : Prop) [Decidable P] :
    ((if P then 0#64 else 1#64) = (0 : BitVec 64)) ↔ P := by by_cases P <;> simp

@[simp] private theorem ite_one_zero_ne_zero_prop (P : Prop) [Decidable P] :
    ((if P then 1#64 else 0#64) ≠ (0 : BitVec 64)) ↔ P := by by_cases P <;> simp

@[simp] private theorem ite_one_zero_eq_zero_prop (P : Prop) [Decidable P] :
    ((if P then 1#64 else 0#64) = (0 : BitVec 64)) ↔ ¬ P := by by_cases P <;> simp

private theorem sep_cast {P Q : Mem 64 → Prop} {m : Mem 64} (h : m =⋆ P) (heq : P = Q) : m =⋆ Q :=
  heq ▸ h

private theorem sep_1_to_front {A B C : Mem 64 → Prop} : ((A ⋆ B) ⋆ C) = (A ⋆ (B ⋆ C)) := by ac_rfl
private theorem sep_2_to_front {A B C : Mem 64 → Prop} : ((A ⋆ B) ⋆ C) = (B ⋆ (A ⋆ C)) := by ac_rfl
private theorem sep_3_to_front {A B C D : Mem 64 → Prop} :
    ((A ⋆ B) ⋆ (C ⋆ D)) = (C ⋆ ((A ⋆ B) ⋆ D)) := by ac_rfl
private theorem sep_4_to_front {A B C D E : Mem 64 → Prop} :
    ((A ⋆ B) ⋆ (C ⋆ (D ⋆ E))) = (D ⋆ ((A ⋆ B) ⋆ (C ⋆ E))) := by ac_rfl
private theorem sep_last4_to_front {A B C D : Mem 64 → Prop} :
    ((A ⋆ B) ⋆ (C ⋆ D)) = (D ⋆ ((A ⋆ B) ⋆ C)) := by ac_rfl
private theorem sep_2nd_to_front {A B C : Mem 64 → Prop} : (A ⋆ (B ⋆ C)) = (B ⋆ (A ⋆ C)) := by ac_rfl

private theorem exec_if_cps {e : Env} {B : Nat} {t : Trace 64} {m : Mem 64} {l : Locals 64}
    {ec : Expr} {c1 c2 : Cmd} {post : Trace 64 → Mem 64 → Locals 64 → Prop} {v : BitVec 64}
    (hv : ec.eval m l = some v)
    (ht : v ≠ 0 → Exec lratFailExt e B c1 t m l (fun t' m' l' => Exec lratFailExt e B c2 t' m' l' post))
    (hf : v = 0 → Exec lratFailExt e B c2 t m l post) :
    Exec lratFailExt e B (.seq (.cond ec c1 .skip) c2) t m l post :=
  Exec.seq_cps (Exec.cond_cps hv ht (fun hz => .skip _ _ _ _ _ (hf hz)))

private theorem local_pres {l l' : Locals 64} {k : String} {v : BitVec 64}
    (h1 : l'[k]? = l[k]?) (h2 : l[k]? = some v) : l'[k]? = some v :=
  h1.trans h2

/-! ## 1. Pure RUP Metatheory Bridge Lemmas -/

/-- If a clause contains both `(atom, pol)` and `(atom, !pol)`, it is a tautology and entailed by any formula. -/
theorem entailsClause_of_tautology {f : CNF Nat} {clause : CNF.Clause Nat}
    (h : ∃ atom pol, (atom, pol) ∈ clause ∧ (atom, !pol) ∈ clause) :
    CNF.EntailsClause f clause :=
  let ⟨_, _, h1, h2⟩ := h
  CNF.entails_clause_of_forall_sat (CNF.Clause.sat_of_mem_of_mem_neg h1 h2)

/-- An assignment `assign` whose assigned literals are exact negations of `clause` satisfies
`CNF.IsNegationOf assign.toCNF clause`. -/
theorem isNegationOf_of_iff_falsified {clause : CNF.Clause Nat} {assign : Assignment}
    (h : ∀ lit : Literal Nat, lit ∈ clause ↔ assign.get? lit.1 = some !lit.2) :
    CNF.IsNegationOf assign.toCNF clause := by
  rw [CNF.isNegationOf_def]
  intro a
  simp only [Assignment.sat_toCNF_iff, CNF.Clause.not_sat_iff_forall_mem_ne]
  constructor
  · intro ha lit hmem
    have := ha lit.1 (!lit.2) ((h lit).mp hmem)
    grind
  · intro hne atom pol hget
    simpa using hne (atom, !pol) ((h (atom, !pol)).mpr (by simpa using hget))

/-- If `assign` falsifies iff `lit ∈ clause` and `f ++ assign.toCNF` is unsatisfiable, then `f` entails `clause`. -/
theorem entailsClause_of_unsat_of_iff_falsified {f : CNF Nat} {clause : CNF.Clause Nat}
    {assign : Assignment}
    (h1 : ∀ lit : Literal Nat, lit ∈ clause ↔ assign.get? lit.1 = some !lit.2)
    (h2 : CNF.Unsat (f ++ assign.toCNF)) :
    CNF.EntailsClause f clause :=
  CNF.entails_clause_of_unsat_of_isNegationOf (isNegationOf_of_iff_falsified h1) h2

/-- Conflict step in RUP unit propagation: if `c ∈ f` has all literals falsified by `curAssign`,
and `f ++ initAssign.toCNF` entails `f ++ curAssign.toCNF`, then `f ++ initAssign.toCNF` is unsatisfiable. -/
theorem unsat_of_all_falsified {f : CNF Nat} {initAssign curAssign : Assignment}
    {c : CNF.Clause Nat} (hc : c ∈ f)
    (hent : CNF.Entails (f ++ initAssign.toCNF) (f ++ curAssign.toCNF))
    (hall : ∀ lit ∈ c, curAssign.get? lit.1 = some !lit.2) :
    CNF.Unsat (f ++ initAssign.toCNF) :=
  CNF.unsat_of_entails_unsat
    (CNF.unsat_iff_not_sat.mpr fun _ hsat => by
      rw [CNF.sat_append] at hsat
      exact Assignment.not_sat_of_forall_falsified hsat.2 hall (CNF.sat_of_mem hsat.1 hc))
    hent

/-- Unit propagation step in RUP: if `c ∈ f` has all literals except `unit` falsified by `curAssign`,
then `f ++ initAssign.toCNF` entails `f ++ (curAssign.insert unit.1 unit.2).toCNF`. -/
theorem entails_insert_of_unit_prop {f : CNF Nat} {initAssign curAssign : Assignment}
    {c : CNF.Clause Nat} {unit : Literal Nat} (hc : c ∈ f)
    (hent : CNF.Entails (f ++ initAssign.toCNF) (f ++ curAssign.toCNF))
    (hall : ∀ lit ∈ c, lit = unit ∨ curAssign.get? lit.1 = some !lit.2) :
    CNF.Entails (f ++ initAssign.toCNF) (f ++ (curAssign.insert unit.1 unit.2).toCNF) := by
  refine CNF.entails_trans hent (CNF.entails_append_of_entails CNF.append_entails_left ?_)
  refine CNF.entails_trans (h2 := Assignment.toCNF_add_entails_toCNF_insert) ?_
  rw [CNF.entails_add_iff]
  refine ⟨CNF.append_entails_right, CNF.entails_clause_def.mpr fun _ ha => ?_⟩
  rw [CNF.sat_append] at ha
  rw [CNF.Clause.sat_unit_iff]
  exact Assignment.unit_propagation ha.2 (CNF.sat_of_mem ha.1 hc) hall

/-- Lookup in `State.formula` at `aid - 1` yields membership in `s.toCNF`. -/
theorem mem_toCNF_of_formula_getElem? {s : State} {aid : Nat} {c : CNF.Clause Nat}
    (hget : s.formula[aid - 1]? = some (some c)) :
    c ∈ s.toCNF :=
  State.mem_toCNF_of_eq_some (idx := aid) (by simp [State.get?, Array.getD_eq_getD_getElem?, hget])

/-! ## 2. Signed BitVec & Expression Evaluation Helpers -/

theorem isValidLit_neg {max_var : Nat} {lit : BitVec 64} (h : IsValidLit max_var lit) :
    IsValidLit max_var (-lit) := by
  obtain ⟨h32, hne, hle, hmax⟩ := h
  have hnotmin : lit ≠ 0xffffffff80000000#64 := by
    rintro rfl; simp [bvAbs] at hle; omega
  refine ⟨?_, ?_, (bvAbs_neg ⟨h32, hne, hle, hmax⟩) ▸ hle, hmax⟩ <;>
    · unfold IsInt32 at *; revert h32 hne hnotmin; bv_decide

theorem ofNat_bvAbs_toNat (lit : BitVec 64) :
    BitVec.ofNat 64 (bvAbs lit).toNat = bvAbs lit :=
  BitVec.eq_of_toNat_eq (by simp)

theorem eval_ite_abs {m : Mem 64} {l : Locals 64} {vname : String} {lit : BitVec 64}
    (hl : l[vname]? = some lit) :
    (Expr.ite (.op .lts (.var vname) (.literal 0))
      (.op .sub (.literal 0) (.var vname)) (.var vname)).eval m l = some (bvAbs lit) := by
  simp [Expr.eval, hl, interpBinop, bvAbs]
  cases lit.slt 0 <;> rfl

theorem eval_sign_byte_expr {m : Mem 64} {l : Locals 64} {e : Expr} {lit : BitVec 64}
    (he : e.eval m l = some lit) :
    (Expr.op .or (.op .srs e (.literal 63)) (.literal 1)).eval m l = some (bvSignByte lit) := by
  simp [Expr.eval, he, interpBinop, bvSignByte]

theorem eval_neg_var {m : Mem 64} {l : Locals 64} {vname : String} {lit : BitVec 64}
    (hl : l[vname]? = some lit) :
    (Expr.op .sub (.literal 0) (.var vname)).eval m l = some (-lit) := by
  simp [Expr.eval, hl, interpBinop]

/-! ## 3. Step Lemmas for Inline Helpers (`inline_assigned_literal`, `inline_assign_literal`, `flush_prop_state`) -/

theorem exec_inline_assigned_literal {e : Env} {B : Nat} {t : Trace 64} {m : Mem 64} {l : Locals 64}
    {post : Trace 64 → Mem 64 → Locals 64 → Prop}
    {max_var : Nat} {values_begin lit : BitVec 64} {assign : Assignment} {R : Mem 64 → Prop}
    (hlit_var : l["lit"]? = some lit)
    (hvb_var : l["values_begin"]? = some values_begin)
    (hlit : IsValidLit max_var lit)
    (hsep : m =⋆ byte1Array values_begin (assignBytes max_var assign) ⋆ R)
    (hpost : post t m ((l.insert "idx" (bvAbs lit)).insert "val"
      (evalAssignedLit (assignByte assign (toLiteral lit).1) lit))) :
    Exec lratFailExt e B inline_assigned_literal t m l post := by
  unfold inline_assigned_literal
  refine Exec.seq_cps (Exec.set_cps (eval_ite_abs hlit_var) ?_)
  have hi : (toLiteral lit).1 < (assignBytes max_var assign).length := by
    simp [toLiteral]; have := hlit.2.2.1; omega
  have h8 : IsInt8 (assignBytes max_var assign)[(toLiteral lit).1] := by
    rw [getElem_assignBytes max_var assign (by simpa using hi)]
    exact isInt8_assignByte assign (toLiteral lit).1
  have hload := eval_load1_byte1Array_elem hi
    (ea := .op .add (.var "values_begin") (.var "idx"))
    (l := l.insert "idx" (bvAbs lit))
    (by simp [Expr.eval, hvb_var, interpBinop, toLiteral]) hsep h8
  simp only [getElem_assignBytes max_var assign (by simpa using hi)] at hload
  refine Exec.seq_cps (Exec.set_cps hload ?_)
  refine Exec.cond_cps (by simp [Expr.eval, hlit_var, interpBinop]; rfl) (fun hnz => ?_) (fun hz => ?_)
  · simp only [ite_one_zero_ne_zero] at hnz
    refine Exec.set_cps (by simp [Expr.eval, interpOp1]; rfl) ?_
    have hins : (((l.insert "idx" (bvAbs lit)).insert "val"
        (assignByte assign (toLiteral lit).1)).insert "val"
        (-(assignByte assign (toLiteral lit).1))) =
        (l.insert "idx" (bvAbs lit)).insert "val"
          (evalAssignedLit (assignByte assign (toLiteral lit).1) lit) :=
      ExtHashMap.ext_getElem? fun _ => by simp [evalAssignedLit, hnz]; split <;> rfl
    rwa [hins]
  · simp only [ite_one_zero_eq_zero] at hz
    exact Exec.skip _ _ _ _ _ (by simpa [evalAssignedLit, hz] using hpost)

theorem exec_inline_assign_literal {e : Env} {B : Nat} {t : Trace 64} {m : Mem 64} {l : Locals 64}
    {post : Trace 64 → Mem 64 → Locals 64 → Prop}
    {elit eval_expr : Expr} {max_var : Nat}
    {values_begin trail_begin trail_end stat_lit_assigned wlit : BitVec 64}
    {assign : Assignment} {trail : List (BitVec 64)} {t0 : BitVec 64} {trail_free : List (BitVec 64)}
    {R : Mem 64 → Prop}
    (hvb : l["values_begin"]? = some values_begin)
    (hidx : l["idx"]? = some (bvAbs wlit))
    (hte : l["trail_end"]? = some trail_end)
    (hstat : l["stat_lit_assigned"]? = some stat_lit_assigned)
    (hwlit : IsValidLit max_var wlit)
    (heval_val : eval_expr.eval m l = some (bvSignByte wlit))
    (heval_lit : ∀ m', elit.eval m' l = some wlit)
    (hte_eq : trail_end = trail_begin + BitVec.ofNat 64 (4 * trail.length))
    (hcov : TrailCoversAssign max_var assign trail)
    (hsep : m =⋆ (byte1Array values_begin (assignBytes max_var assign) ⋆
      int4Array trail_begin (trail ++ t0 :: trail_free)) ⋆ R)
    (hpost : ∀ m',
      trail_end + 4 = trail_begin + BitVec.ofNat 64 (4 * (trail ++ [wlit]).length) →
      TrailCoversAssign max_var (assign.insert (toLiteral wlit).1 (toLiteral wlit).2) (trail ++ [wlit]) →
      (m' =⋆ (byte1Array values_begin
          (assignBytes max_var (assign.insert (toLiteral wlit).1 (toLiteral wlit).2)) ⋆
        int4Array trail_begin ((trail ++ [wlit]) ++ trail_free)) ⋆ R) →
      post t m' ((l.insert "trail_end" (trail_end + 4)).insert "stat_lit_assigned" (stat_lit_assigned + 1))) :
    Exec lratFailExt e B (inline_assign_literal elit eval_expr) t m l post := by
  unfold inline_assign_literal
  have hi : (toLiteral wlit).1 < (assignBytes max_var assign).length := by
    simp [toLiteral]; have := hwlit.2.2.1; omega
  refine Exec.seq_cps (store_byte1Array_elem hi
    (by simp [Expr.eval, hvb, hidx, interpBinop, toLiteral]) heval_val (sep_1_to_front ▸ hsep)
    fun m1 hm1 => ?_)
  rw [assignBytes_set_insert max_var assign hwlit] at hm1
  refine Exec.seq_cps (store_int4Array_elem (i := trail.length) (by simp)
    (by simp [Expr.eval, hte, hte_eq]) (heval_lit m1) (sep_2nd_to_front ▸ hm1)
    fun m2 hm2 => ?_)
  have hset_trail : (trail ++ t0 :: trail_free).set trail.length wlit = (trail ++ [wlit]) ++ trail_free := by
    simp [List.set_append_right]
  rw [hset_trail] at hm2
  refine Exec.seq_cps (Exec.set_cps (by simp [Expr.eval, hte, interpBinop]; rfl) ?_)
  refine Exec.set_cps (by simp [Expr.eval, hstat, interpBinop]; rfl) ?_
  have hte_next : trail_end + 4 = trail_begin + BitVec.ofNat 64 (4 * (trail ++ [wlit]).length) := by
    rw [hte_eq, List.length_append, List.length_singleton]
    exact BitVec.eq_of_toNat_eq (by simp [BitVec.toNat_add]; omega)
  exact hpost m2 hte_next (trailCoversAssign_insert wlit hcov) (sep_cast hm2 (by ac_rfl))

theorem exec_flush_prop_state {e : Env} {B : Nat} {t : Trace 64} {m : Mem 64} {l : Locals 64}
    {post : Trace 64 → Mem 64 → Locals 64 → Prop}
    {st trail_end stat_resolved stat_lit_assigned : BitVec 64}
    {k : KernelFields} {R : Mem 64 → Prop}
    (hst : l["st"]? = some st)
    (hte : l["trail_end"]? = some trail_end)
    (hsr : l["stat_resolved"]? = some stat_resolved)
    (hsla : l["stat_lit_assigned"]? = some stat_lit_assigned)
    (hsep : m =⋆ kernelState st k ⋆ R)
    (hpost : ∀ m',
      (m' =⋆ kernelState st
        { k with trail_end := trail_end, stat_resolved := stat_resolved, stat_lit_assigned := stat_lit_assigned } ⋆ R) →
      post t m' l) :
    Exec lratFailExt e B flush_prop_state t m l post := by
  unfold flush_prop_state kernelState at *
  refine Exec.seq_cps (store_word8Array_elem (i := 6) (by simp [KernelFields.toList])
    (by simp [Expr.eval, hst, interpBinop]) hte hsep fun m1 hm1 => ?_)
  refine Exec.seq_cps (store_word8Array_elem (i := 18) (by simp [KernelFields.toList])
    (by simp [Expr.eval, hst, interpBinop]) hsr hm1 fun m2 hm2 => ?_)
  refine store_word8Array_elem (i := 19) (by simp [KernelFields.toList])
    (by simp [Expr.eval, hst, interpBinop]) hsla hm2 fun m3 hm3 => ?_
  exact hpost m3 hm3

theorem exec_flush_and_fail {e : Env} {B : Nat} {t : Trace 64} {m : Mem 64} {l : Locals 64}
    {post : Trace 64 → Mem 64 → Locals 64 → Prop}
    {arges : List Expr} {args : List (BitVec 64)}
    {st trail_end stat_resolved stat_lit_assigned : BitVec 64}
    {k : KernelFields} {R : Mem 64 → Prop}
    (hst : l["st"]? = some st)
    (hte : l["trail_end"]? = some trail_end)
    (hsr : l["stat_resolved"]? = some stat_resolved)
    (hsla : l["stat_lit_assigned"]? = some stat_lit_assigned)
    (hsep : m =⋆ kernelState st k ⋆ R)
    (ha : ∀ m', evalArgs m' l arges = some args) :
    Exec lratFailExt e B (.seq flush_prop_state (.interact [] "lrat_fail" arges)) t m l post :=
  Exec.seq_cps (exec_flush_prop_state hst hte hsr hsla hsep fun m' _ => exec_lrat_fail (ha m'))

/-! ## 4. Zero-Terminated Array Access (`zeroTermGet`) & `inline_backtrack` (Loop 3) -/

/-- Element at index `i` of a 0-terminated array `xs ++ [0]`, for `i ≤ xs.length`. -/
def zeroTermGet (xs : List (BitVec 64)) (i : Nat) : BitVec 64 :=
  if h : i < xs.length then xs[i] else 0

theorem eval_load4_zeroTermGet {m : Mem 64} {l : Locals 64} {ea : Expr}
    {p : BitVec 64} {xs : List (BitVec 64)} {i : Nat} {R : Mem 64 → Prop}
    (hi : i ≤ xs.length)
    (ha : ea.eval m l = some (p + BitVec.ofNat 64 (4 * i)))
    (hsep : m =⋆ ZeroTermInts p xs ⋆ R)
    (h32 : ∀ x ∈ xs, IsInt32 x) :
    (Expr.op .srs (.op .slu (.load .four ea) (.literal 32)) (.literal 32)).eval m l =
      some (zeroTermGet xs i) := by
  unfold zeroTermGet; split
  · exact eval_load4_zeroTermInts_elem ‹_› ha hsep (h32 _ (List.getElem_mem ‹_›))
  · obtain rfl : i = xs.length := by omega
    exact eval_load4_zeroTermInts_end ha hsep

theorem zeroTermGet_ne_zero_iff {xs : List (BitVec 64)} {i : Nat}
    (_hi : i ≤ xs.length) (hne0 : ∀ x ∈ xs, x ≠ 0) :
    zeroTermGet xs i ≠ 0 ↔ i < xs.length := by
  unfold zeroTermGet; split <;> simp_all

theorem zeroTermGet_eq_zero_iff {xs : List (BitVec 64)} {i : Nat}
    (hi : i ≤ xs.length) (hne0 : ∀ x ∈ xs, x ≠ 0) :
    zeroTermGet xs i = 0 ↔ i = xs.length := by
  unfold zeroTermGet; split <;> simp_all <;> omega

theorem ptr_step_4 (p : BitVec 64) (i : Nat) :
    p + BitVec.ofNat 64 (4 * i) + 4#64 = p + BitVec.ofNat 64 (4 * (i + 1)) :=
  BitVec.eq_of_toNat_eq (by simp [BitVec.toNat_add]; omega)

theorem clearTrailBytes_append (bs : List (BitVec 64)) (t1 t2 : List (BitVec 64)) :
    clearTrailBytes bs (t1 ++ t2) = clearTrailBytes (clearTrailBytes bs t1) t2 :=
  List.foldl_append

theorem clearTrailBytes_take_succ (bs : List (BitVec 64)) (trail : List (BitVec 64))
    {i : Nat} (hi : i < trail.length) :
    (clearTrailBytes bs (trail.take i)).set (bvAbs trail[i]).toNat 0 =
      clearTrailBytes bs (trail.take (i + 1)) := by
  rw [List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some,
    clearTrailBytes_append, clearTrailBytes_cons, clearTrailBytes_nil]

theorem exec_inline_backtrack {e : Env} {B : Nat} {t : Trace 64} {m : Mem 64} {l : Locals 64}
    {post : Trace 64 → Mem 64 → Locals 64 → Prop}
    {max_var : Nat} {values_begin trail_begin trail_end : BitVec 64}
    {assign : Assignment} {trail trail_free : List (BitVec 64)} {R : Mem 64 → Prop}
    (hvb : l["values_begin"]? = some values_begin)
    (htb : l["trail_begin"]? = some trail_begin)
    (hte : l["trail_end"]? = some trail_end)
    (hte_eq : trail_end = trail_begin + BitVec.ofNat 64 (4 * trail.length))
    (htrail_valid : ∀ tlit ∈ trail, IsValidLit max_var tlit)
    (htrail_len : 4 * trail.length < 2 ^ 64)
    (hcov : TrailCoversAssign max_var assign trail)
    (hsep : m =⋆ (byte1Array values_begin (assignBytes max_var assign) ⋆
      int4Array trail_begin (trail ++ trail_free)) ⋆ R)
    (hpost : ∀ m' l',
      l'["trail_end"]? = some trail_begin →
      (∀ k, k ≠ "t" → k ≠ "tlit" → k ≠ "tidx" → k ≠ "trail_end" → l'[k]? = l[k]?) →
      (m' =⋆ (byte1Array values_begin (assignBytes max_var Assignment.empty) ⋆
        int4Array trail_begin (trail ++ trail_free)) ⋆ R) →
      post t m' l') :
    Exec lratFailExt e B inline_backtrack t m l post := by
  unfold inline_backtrack
  refine Exec.seq_cps (Exec.set_cps (v := trail_begin) (by simp [Expr.eval, htb]) ?_)
  let bs0 := assignBytes max_var assign
  let inv (rem : Nat) (t' : Trace 64) (m' : Mem 64) (l' : Locals 64) : Prop :=
    ∃ i : Nat,
      i ≤ trail.length ∧
      rem = trail.length - i ∧
      t' = t ∧
      l'["t"]? = some (trail_begin + BitVec.ofNat 64 (4 * i)) ∧
      (∀ k, k ≠ "t" → k ≠ "tlit" → k ≠ "tidx" → l'[k]? = l[k]?) ∧
      (m' =⋆ (byte1Array values_begin (clearTrailBytes bs0 (trail.take i)) ⋆
        int4Array trail_begin (trail ++ trail_free)) ⋆ R)
  refine Exec.seq_cps (Exec.while_wf (Measure := Nat) Nat.lt_wfRel.wf inv trail.length ?_ ?_)
  · refine ⟨0, Nat.zero_le _, by omega, rfl, by simp, fun _ h1 _ _ => by simp [h1.symm], by simpa [bs0] using hsep⟩
  · rintro rem t' m' l' ⟨i, hi, rfl, rfl, ht_var, hlocals, hm'⟩
    have hte' := local_pres (hlocals _ (by decide) (by decide) (by decide)) hte
    have htb' := local_pres (hlocals _ (by decide) (by decide) (by decide)) htb
    have hvb' := local_pres (hlocals _ (by decide) (by decide) (by decide)) hvb
    let t_val := trail_begin + BitVec.ofNat 64 (4 * i)
    refine ⟨_, by simp [Expr.eval, ht_var, hte', interpBinop] <;> rfl, fun hnz => ?_, fun hz => ?_⟩
    · simp only [ite_zero_one_ne_zero_prop] at hnz
      have hlt : i < trail.length := by
        rcases Nat.eq_or_lt_of_le hi with rfl | hlt
        · exact absurd hte_eq.symm hnz
        · exact hlt
      have hvalid_i := htrail_valid trail[i] (List.getElem_mem hlt)
      have hget_i : (trail ++ trail_free)[i]'(by simp; omega) = trail[i] := List.getElem_append_left hlt
      have hload_tlit := eval_load4_int4Array_elem (ea := .var "t") (by simp; omega) ht_var
        (sep_2_to_front ▸ hm') (by rw [hget_i]; exact hvalid_i.1)
      rw [hget_i] at hload_tlit
      refine Exec.seq_cps (Exec.set_cps (v := trail[i]) hload_tlit ?_)
      refine Exec.seq_cps (Exec.set_cps (eval_ite_abs (vname := "tlit") (lit := trail[i]) (by simp)) ?_)
      have hidx_lt : (bvAbs trail[i]).toNat < (clearTrailBytes bs0 (trail.take i)).length := by
        simp [bs0]; have := hvalid_i.2.2.1; omega
      refine Exec.seq_cps (store_byte1Array_elem (v := 0) hidx_lt
        (by simp [Expr.eval, hvb', interpBinop]) rfl (sep_1_to_front ▸ hm') fun m1 hm1 => ?_)
      rw [clearTrailBytes_take_succ bs0 trail hlt] at hm1
      refine Exec.set_cps (v := t_val + 4) (by simp [Expr.eval, ht_var, interpBinop, t_val]) ?_
      refine ⟨trail.length - (i + 1), ⟨i + 1, Nat.succ_le_of_lt hlt, rfl, rfl, ?_,
        fun _ h1 h2 h3 => by simp [h1.symm, h2.symm, h3.symm, hlocals _ h1 h2 h3], sep_cast hm1 (by ac_rfl)⟩, by dsimp only [WellFoundedRelation.rel]; omega⟩
      simp [t_val, ptr_step_4]
    · simp only [ite_zero_one_eq_zero_prop] at hz
      have hi_eq : i = trail.length := by
        rw [hte_eq] at hz
        have hnat := congrArg BitVec.toNat (congrArg (· - trail_begin) hz)
        simp [BitVec.add_comm trail_begin, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega : 4 * i < 2 ^ 64), Nat.mod_eq_of_lt htrail_len] at hnat
        omega
      subst hi_eq
      rw [List.take_length, clearTrailBytes_assignBytes hcov] at hm'
      refine Exec.set_cps (v := trail_begin) (by simp [Expr.eval, htb']) ?_
      exact hpost m' (l'.insert "trail_end" trail_begin) (by simp)
        (fun _ h1 h2 h3 h4 => by simp [h4.symm, hlocals _ h1 h2 h3]) hm'

/-! ## 5. Phase 1 Loop (`while lit` on `literals` —Negating Clause Literals) -/

theorem evalAssignedLit_cases {max_var : Nat} (assign : Assignment) {lit : BitVec 64}
    (hlit : IsValidLit max_var lit) :
    let v := evalAssignedLit (assignByte assign (toLiteral lit).1) lit
    (v.slt 0 = true → assign.get? (toLiteral lit).1 = some !(toLiteral lit).2) ∧
    (v.slt 0 = false ∧ (0#64).slt v = true → assign.get? (toLiteral lit).1 = some (toLiteral lit).2) ∧
    (v.slt 0 = false ∧ (0#64).slt v = false → assign.get? (toLiteral lit).1 = none ∧ v = 0) := by
  have hpos := bvAbs_pos hlit
  dsimp only
  simp only [assignByte, toLiteral, Nat.ne_of_gt hpos, ↓reduceIte, evalAssignedLit]
  rcases assign.get? (bvAbs lit).toNat with _ | (_ | _) <;>
    cases lit.slt 0 <;> simp <;> decide

theorem phase1_step_already_falsified {lits : List (BitVec 64)} {i : Nat} {assign : Assignment}
    (hlt : i < lits.length)
    (hinv : ∀ x : Literal Nat, x ∈ (lits.take i).map toLiteral ↔ assign.get? x.1 = some !x.2)
    (hfals : assign.get? (toLiteral lits[i]).1 = some !(toLiteral lits[i]).2) :
    ∀ x : Literal Nat, x ∈ (lits.take (i + 1)).map toLiteral ↔ assign.get? x.1 = some !x.2 := by
  intro x
  simp only [List.take_add_one, List.getElem?_eq_getElem hlt, Option.toList_some,
    List.map_append, List.map_singleton, List.mem_append, List.mem_singleton, hinv x]
  grind

theorem phase1_step_tautology {lits : List (BitVec 64)} {i : Nat} {assign : Assignment}
    (hlt : i < lits.length)
    (hinv : ∀ x : Literal Nat, x ∈ (lits.take i).map toLiteral ↔ assign.get? x.1 = some !x.2)
    (hsat : assign.get? (toLiteral lits[i]).1 = some (toLiteral lits[i]).2) :
    ∃ atom pol, (atom, pol) ∈ toClause lits ∧ (atom, !pol) ∈ toClause lits := by
  have h1 : toLiteral lits[i] ∈ toClause lits := by
    rw [← CNF.Clause.mem_literals_iff, literals_toClause]
    exact List.mem_map_of_mem (List.getElem_mem hlt)
  have h2_pre : ((toLiteral lits[i]).1, !(toLiteral lits[i]).2) ∈ (lits.take i).map toLiteral := by
    rw [hinv]; simpa using hsat
  rcases List.mem_map.mp h2_pre with ⟨y, hy_take, hy_eq⟩
  refine ⟨_, _, h1, ?_⟩
  rw [← CNF.Clause.mem_literals_iff, literals_toClause]
  exact List.mem_map.mpr ⟨y, List.mem_of_mem_take hy_take, by rw [hy_eq]; simp [toLiteral]⟩

theorem phase1_step_insert {max_var : Nat} {lits : List (BitVec 64)} {i : Nat} {assign : Assignment}
    (hlt : i < lits.length) (hlit : IsValidLit max_var lits[i])
    (hinv : ∀ x : Literal Nat, x ∈ (lits.take i).map toLiteral ↔ assign.get? x.1 = some !x.2)
    (hun : assign.get? (toLiteral lits[i]).1 = none) :
    ∀ x : Literal Nat,
      x ∈ (lits.take (i + 1)).map toLiteral ↔
        (assign.insert (toLiteral (-lits[i])).1 (toLiteral (-lits[i])).2).get? x.1 = some !x.2 := by
  intro x
  rw [toLiteral_neg hlit, List.take_add_one, List.getElem?_eq_getElem hlt, Option.toList_some,
    List.map_append, List.map_singleton, List.mem_append, List.mem_singleton]
  by_cases h_atom : (toLiteral lits[i]).1 = x.1
  · rw [Assignment.get?_insert_of_eq h_atom]
    have hnot_in : x ∉ (lits.take i).map toLiteral := by
      intro hmem; have := (hinv x).mp hmem; rw [← h_atom, hun] at this; contradiction
    rcases x with ⟨xa, xp⟩
    simp only [hnot_in, false_or, Option.some.injEq]
    constructor <;> grind
  · rw [Assignment.get?_insert_of_ne h_atom, ← hinv x]
    have : x ≠ toLiteral lits[i] := fun heq => h_atom (congrArg Prod.fst heq).symm
    simp [this]

theorem exec_advance_zeroTerm {e : Env} {B : Nat} {t : Trace 64} {m : Mem 64} {l : Locals 64}
    {post : Trace 64 → Mem 64 → Locals 64 → Prop}
    {pvar xvar : String} {p : BitVec 64} {xs : List (BitVec 64)} {i : Nat} {R : Mem 64 → Prop}
    (hlt : i < xs.length)
    (hpvar : l[pvar]? = some (p + BitVec.ofNat 64 (4 * i)))
    (hsep : m =⋆ ZeroTermInts p xs ⋆ R)
    (h32 : ∀ x ∈ xs, IsInt32 x)
    (hpost : post t m
      ((l.insert pvar (p + BitVec.ofNat 64 (4 * (i + 1)))).insert xvar (zeroTermGet xs (i + 1)))) :
    Exec lratFailExt e B
      (.seq (.set pvar (.op .add (.var pvar) (.literal 4)))
        (.set xvar (.op .srs (.op .slu (.load .four (.var pvar)) (.literal 32)) (.literal 32))))
      t m l post := by
  refine Exec.seq_cps (Exec.set_cps (by simp [Expr.eval, hpvar, interpBinop, ptr_step_4]; rfl) ?_)
  exact Exec.set_cps (eval_load4_zeroTermGet (Nat.succ_le_of_lt hlt) (by simp [Expr.eval]) hsep h32) hpost

def rup_phase1_loop : Cmd := bedrock2_cmd:(
  while lit {
    %❰inline_assigned_literal❱;
    if val .< 0 {
      l = l + 4;
      lit = (load4(l) << 32) .>> 32
    } else {
      if 0 .< val {
        checked = 1;
        lit = 0
      } else {
        %❰inline_assign_literal bedrock2_expr:(-lit) bedrock2_expr:(((-lit) .>> 63) | 1)❱;
        l = l + 4;
        lit = (load4(l) << 32) .>> 32
      }
    }
  }
)

theorem exec_rup_phase1_loop {e : Env} {B : Nat} {t : Trace 64} {m : Mem 64} {l : Locals 64}
    {post : Trace 64 → Mem 64 → Locals 64 → Prop}
    {max_var reserve : Nat} {literals values_begin trail_begin stat_lit_assigned0 : BitVec 64}
    {lits trail_free0 : List (BitVec 64)} {R : Mem 64 → Prop}
    (hl_var : l["l"]? = some literals)
    (hlit_var : l["lit"]? = some (zeroTermGet lits 0))
    (hchk_var : l["checked"]? = some 0)
    (hvb_var : l["values_begin"]? = some values_begin)
    (hte_var : l["trail_end"]? = some trail_begin)
    (hsla_var : l["stat_lit_assigned"]? = some stat_lit_assigned0)
    (hlits_valid : ∀ x ∈ lits, IsValidLit max_var x)
    (htrail_cap : reserve + lits.length ≤ trail_free0.length)
    (hsep : m =⋆ (byte1Array values_begin (assignBytes max_var Assignment.empty) ⋆
        int4Array trail_begin trail_free0) ⋆ (ZeroTermInts literals lits ⋆ R))
    (hpost : ∀ m' l' (checked trail_end stat_lit_assigned : BitVec 64)
        (assign : Assignment) (trail trail_free : List (BitVec 64)),
      l'["checked"]? = some checked →
      l'["trail_end"]? = some trail_end →
      l'["stat_lit_assigned"]? = some stat_lit_assigned →
      (∀ k, k ≠ "l" → k ≠ "lit" → k ≠ "idx" → k ≠ "val" →
            k ≠ "checked" → k ≠ "trail_end" → k ≠ "stat_lit_assigned" → l'[k]? = l[k]?) →
      trail_end = trail_begin + BitVec.ofNat 64 (4 * trail.length) →
      TrailCoversAssign max_var assign trail →
      (∀ tlit ∈ trail, IsValidLit max_var tlit) →
      trail.length + trail_free.length = trail_free0.length →
      reserve ≤ trail_free.length →
      (m' =⋆ (byte1Array values_begin (assignBytes max_var assign) ⋆
          int4Array trail_begin (trail ++ trail_free)) ⋆ (ZeroTermInts literals lits ⋆ R)) →
      ((checked = 0 ∧ ∀ x : Literal Nat, x ∈ toClause lits ↔ assign.get? x.1 = some !x.2) ∨
       (checked = 1 ∧ ∃ atom pol, (atom, pol) ∈ toClause lits ∧ (atom, !pol) ∈ toClause lits)) →
      post t m' l') :
    Exec lratFailExt e B rup_phase1_loop t m l post := by
  unfold rup_phase1_loop
  have h32 : ∀ x ∈ lits, IsInt32 x := fun x hx => (hlits_valid x hx).1
  have hne0 : ∀ x ∈ lits, x ≠ 0 := fun x hx => (hlits_valid x hx).2.1
  let inv (rem : Nat) (t' : Trace 64) (m' : Mem 64) (l' : Locals 64) : Prop :=
    ∃ (checked trail_end stat_lit_assigned : BitVec 64)
      (assign : Assignment) (trail trail_free : List (BitVec 64)),
      t' = t ∧
      l'["checked"]? = some checked ∧
      l'["trail_end"]? = some trail_end ∧
      l'["stat_lit_assigned"]? = some stat_lit_assigned ∧
      (∀ k, k ≠ "l" → k ≠ "lit" → k ≠ "idx" → k ≠ "val" →
            k ≠ "checked" → k ≠ "trail_end" → k ≠ "stat_lit_assigned" → l'[k]? = l[k]?) ∧
      trail_end = trail_begin + BitVec.ofNat 64 (4 * trail.length) ∧
      TrailCoversAssign max_var assign trail ∧
      (∀ tlit ∈ trail, IsValidLit max_var tlit) ∧
      trail.length + trail_free.length = trail_free0.length ∧
      (m' =⋆ (byte1Array values_begin (assignBytes max_var assign) ⋆
          int4Array trail_begin (trail ++ trail_free)) ⋆ (ZeroTermInts literals lits ⋆ R)) ∧
      ((checked = 0 ∧ ∃ i : Nat,
          i ≤ lits.length ∧
          rem = lits.length + 1 - i ∧
          reserve + (lits.length - i) ≤ trail_free.length ∧
          l'["l"]? = some (literals + BitVec.ofNat 64 (4 * i)) ∧
          l'["lit"]? = some (zeroTermGet lits i) ∧
          (∀ x : Literal Nat, x ∈ (lits.take i).map toLiteral ↔ assign.get? x.1 = some !x.2)) ∨
       (checked = 1 ∧ rem = 0 ∧ reserve ≤ trail_free.length ∧ l'["lit"]? = some 0 ∧
          ∃ atom pol, (atom, pol) ∈ toClause lits ∧ (atom, !pol) ∈ toClause lits))
  refine Exec.while_wf (Measure := Nat) Nat.lt_wfRel.wf inv (lits.length + 1) ?_ ?_
  · refine ⟨0, trail_begin, stat_lit_assigned0, Assignment.empty, [], trail_free0,
      rfl, hchk_var, hte_var, hsla_var, fun _ _ _ _ _ _ _ _ => rfl,
      by simp, trailCoversAssign_empty max_var, by simp, by simp, by simpa using hsep,
      Or.inl ⟨rfl, 0, Nat.zero_le _, by omega, by omega, by simpa using hl_var, hlit_var, by simp⟩⟩
  · rintro rem t' m' l' ⟨checked, trail_end, stat_lit_assigned, assign, trail, trail_free,
      rfl, hchk, hte, hsla, hlocals, hte_eq, hcov, htrail_valid, hlen_sum, hm', hstate⟩
    have hvb := local_pres (hlocals _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) hvb_var
    rcases hstate with ⟨rfl, i, hi, rfl, hcap_i, hl_ptr, hlit_cur, hinv_i⟩ | ⟨rfl, rfl, hcap_chk, hlit_zero, htaut⟩
    · refine ⟨zeroTermGet lits i, by simp [Expr.eval, hlit_cur], fun hnz => ?_, fun hz => ?_⟩
      · have hlt : i < lits.length := (zeroTermGet_ne_zero_iff hi hne0).mp hnz
        simp only [zeroTermGet, hlt, ↓reduceDIte] at hlit_cur
        have hlit_valid := hlits_valid lits[i] (List.getElem_mem hlt)
        refine Exec.seq_cps (exec_inline_assigned_literal hlit_cur hvb hlit_valid (sep_1_to_front ▸ hm') ?_)
        let v := evalAssignedLit (assignByte assign (toLiteral lits[i]).1) lits[i]
        have hcases := evalAssignedLit_cases assign hlit_valid
        refine Exec.cond_cps (by simp [Expr.eval, interpBinop]; rfl) (fun hnz1 => ?_) (fun hz1 => ?_)
        · simp only [ite_one_zero_ne_zero] at hnz1
          refine exec_advance_zeroTerm hlt (by simp [hl_ptr]) (sep_3_to_front ▸ hm') h32 ?_
          refine ⟨lits.length + 1 - (i + 1), ⟨0, trail_end, stat_lit_assigned, assign, trail, trail_free,
            rfl, by simp [hchk], by simp [hte], by simp [hsla],
            fun _ h1 h2 h3 h4 h5 h6 h7 => by simp [h1.symm, h2.symm, h3.symm, h4.symm, hlocals _ h1 h2 h3 h4 h5 h6 h7],
            hte_eq, hcov, htrail_valid, hlen_sum, hm',
            Or.inl ⟨rfl, i + 1, Nat.succ_le_of_lt hlt, rfl, by omega, by simp, by simp,
              phase1_step_already_falsified hlt hinv_i (hcases.1 hnz1)⟩⟩, by dsimp only [WellFoundedRelation.rel]; omega⟩
        · simp only [ite_one_zero_eq_zero] at hz1
          refine Exec.cond_cps (by simp [Expr.eval, interpBinop] <;> rfl) (fun hnz2 => ?_) (fun hz2 => ?_)
          · simp only [ite_one_zero_ne_zero] at hnz2
            refine Exec.seq_cps (Exec.set_cps (v := 1) rfl ?_)
            refine Exec.set_cps (v := 0) rfl ?_
            refine ⟨0, ⟨1, trail_end, stat_lit_assigned, assign, trail, trail_free,
              rfl, by simp, by simp [hte], by simp [hsla],
              fun _ h1 h2 h3 h4 h5 h6 h7 => by simp [h2.symm, h3.symm, h4.symm, h5.symm, hlocals _ h1 h2 h3 h4 h5 h6 h7],
              hte_eq, hcov, htrail_valid, hlen_sum, hm',
              Or.inr ⟨rfl, rfl, by omega, by simp, phase1_step_tautology hlt hinv_i (hcases.2.1 ⟨hz1, hnz2⟩)⟩⟩,
              by dsimp only [WellFoundedRelation.rel]; omega⟩
          · simp only [ite_one_zero_eq_zero] at hz2
            have hun : assign.get? (toLiteral lits[i]).1 = none := (hcases.2.2 ⟨hz1, hz2⟩).1
            rcases trail_free with _ | ⟨t0, tf'⟩
            · simp at hcap_i; omega
            · have hwlit := isValidLit_neg hlit_valid
              have hlit1 : ∀ m'', (Expr.op .sub (.literal 0) (.var "lit")).eval m''
                  ((l'.insert "idx" (bvAbs lits[i])).insert "val" v) = some (-lits[i]) :=
                fun _ => eval_neg_var (by simp [hlit_cur])
              refine Exec.seq_cps (exec_inline_assign_literal (stat_lit_assigned := stat_lit_assigned)
                (by simp [hvb]) (by simp [bvAbs_neg hlit_valid])
                (by simp [hte]) (by simp [hsla]) hwlit (eval_sign_byte_expr (hlit1 m')) hlit1
                hte_eq hcov hm' fun m1 hte_next hcov_next hm1 => ?_)
              refine exec_advance_zeroTerm hlt (by simp [hl_ptr]) (sep_3_to_front ▸ hm1) h32 ?_
              refine ⟨lits.length + 1 - (i + 1), ⟨0, trail_end + 4, stat_lit_assigned + 1,
                assign.insert (toLiteral (-lits[i])).1 (toLiteral (-lits[i])).2,
                trail ++ [-lits[i]], tf',
                rfl, by simp [hchk], by simp, by simp,
                fun _ h1 h2 h3 h4 h5 h6 h7 => by simp [h1.symm, h2.symm, h3.symm, h4.symm, h6.symm, h7.symm, hlocals _ h1 h2 h3 h4 h5 h6 h7],
                hte_next, hcov_next, fun tlit htlit => by rcases List.mem_append.mp htlit with h | h <;> simp_all,
                by simp at hlen_sum ⊢; omega, hm1,
                Or.inl ⟨rfl, i + 1, Nat.succ_le_of_lt hlt, rfl, by simp at hcap_i; omega,
                  by simp, by simp, phase1_step_insert hlt hlit_valid hinv_i hun⟩⟩, by dsimp only [WellFoundedRelation.rel]; omega⟩
      · obtain rfl : i = lits.length := (zeroTermGet_eq_zero_iff hi hne0).mp hz
        rw [List.take_length] at hinv_i
        exact hpost m' l' 0 trail_end stat_lit_assigned assign trail trail_free
          hchk hte hsla hlocals hte_eq hcov htrail_valid hlen_sum (by omega) hm'
          (Or.inl ⟨rfl, fun x => by rw [← CNF.Clause.mem_literals_iff, literals_toClause, hinv_i x]⟩)
    · exact ⟨0, by simp [Expr.eval, hlit_zero], fun hnz => absurd rfl hnz, fun _ =>
        hpost m' l' 1 trail_end stat_lit_assigned assign trail trail_free
          hchk hte hsla hlocals hte_eq hcov htrail_valid hlen_sum hcap_chk hm' (Or.inr ⟨rfl, htaut⟩)⟩

/-! ## 6. Loop 2: Antecedent Propagation (`while aid` and `while lit` on `als`) -/

theorem sep_pull_3rd (A B C D : Mem 64 → Prop) :
    (A ⋆ (B ⋆ (C ⋆ D))) = (C ⋆ (A ⋆ (B ⋆ D))) := by
  ac_rfl

theorem sep_pull_4th (A B C D E : Mem 64 → Prop) :
    (A ⋆ (B ⋆ (C ⋆ (D ⋆ E)))) = (D ⋆ (A ⋆ (B ⋆ (C ⋆ E)))) := by
  ac_rfl

theorem phase2_inner_falsified_unit0 {clits : List (BitVec 64)} {curAssign : Assignment} {i : Nat}
    (hlt : i < clits.length)
    (hinv : ∀ x : Literal Nat, x ∈ (clits.take i).map toLiteral → curAssign.get? x.1 = some !x.2)
    (hfals : curAssign.get? (toLiteral clits[i]).1 = some !(toLiteral clits[i]).2) :
    ∀ x : Literal Nat, x ∈ (clits.take (i + 1)).map toLiteral → curAssign.get? x.1 = some !x.2 := by
  simp only [List.take_add_one, List.getElem?_eq_getElem hlt, Option.toList_some,
    List.map_append, List.map_singleton, List.mem_append, List.mem_singleton]
  grind

theorem phase2_inner_falsified_unit_ne0 {max_var : Nat} {clits : List (BitVec 64)}
    {curAssign assign : Assignment} {unit : BitVec 64} {i : Nat}
    (hlt : i < clits.length)
    (hlit : IsValidLit max_var clits[i])
    (hunit_sat : assign.get? (toLiteral unit).1 = some (toLiteral unit).2)
    (hrel : (curAssign.get? (toLiteral unit).1 = none ∧
              assign = curAssign.insert (toLiteral unit).1 (toLiteral unit).2) ∨
            assign = curAssign)
    (hinv : ∀ x : Literal Nat, x ∈ (clits.take i).map toLiteral →
      x = toLiteral unit ∨ curAssign.get? x.1 = some !x.2)
    (hfals : assign.get? (toLiteral clits[i]).1 = some !(toLiteral clits[i]).2)
    (hne_neg : unit ≠ -clits[i]) :
    ∀ x : Literal Nat, x ∈ (clits.take (i + 1)).map toLiteral →
      x = toLiteral unit ∨ curAssign.get? x.1 = some !x.2 := by
  have hatom_ne : (toLiteral clits[i]).1 ≠ (toLiteral unit).1 := by
    intro heq
    rw [heq, hunit_sat] at hfals
    exact hne_neg (toLiteral_inj.mp (by rw [toLiteral_neg hlit]; exact Prod.ext heq.symm (Option.some.inj hfals)))
  have hfals_cur : curAssign.get? (toLiteral clits[i]).1 = some !(toLiteral clits[i]).2 := by
    rcases hrel with ⟨_, rfl⟩ | rfl
    · rwa [Assignment.get?_insert_of_ne (Ne.symm hatom_ne)] at hfals
    · exact hfals
  simp only [List.take_add_one, List.getElem?_eq_getElem hlt, Option.toList_some,
    List.map_append, List.map_singleton, List.mem_append, List.mem_singleton]
  grind

theorem phase2_inner_new_unit {clits : List (BitVec 64)} {curAssign : Assignment} {i : Nat}
    (hlt : i < clits.length)
    (hinv : ∀ x : Literal Nat, x ∈ (clits.take i).map toLiteral → curAssign.get? x.1 = some !x.2) :
    ∀ x : Literal Nat, x ∈ (clits.take (i + 1)).map toLiteral →
      x = toLiteral clits[i] ∨ curAssign.get? x.1 = some !x.2 := by
  simp only [List.take_add_one, List.getElem?_eq_getElem hlt, Option.toList_some,
    List.map_append, List.map_singleton, List.mem_append, List.mem_singleton]
  grind

theorem phase2_inner_dup_unit {clits : List (BitVec 64)} {curAssign : Assignment}
    {unit : BitVec 64} {i : Nat}
    (hlt : i < clits.length)
    (heq : unit = clits[i])
    (hinv : ∀ x : Literal Nat, x ∈ (clits.take i).map toLiteral →
      x = toLiteral unit ∨ curAssign.get? x.1 = some !x.2) :
    ∀ x : Literal Nat, x ∈ (clits.take (i + 1)).map toLiteral →
      x = toLiteral unit ∨ curAssign.get? x.1 = some !x.2 := by
  simp only [List.take_add_one, List.getElem?_eq_getElem hlt, Option.toList_some,
    List.map_append, List.map_singleton, List.mem_append, List.mem_singleton]
  grind

/-- The Phase 2 inner `while lit` loop of `br_check_clause_non_strictly_by_propagation`. -/
def rup_phase2_inner_loop : Cmd := bedrock2_cmd:(
  while lit {
    %❰inline_assigned_literal❱;
    if val .< 0 {
      if unit == -lit {
        %❰flush_prop_state❱;
        interact lrat_fail(2, id, aid, 0, 0)
      }
    } else {
      if unit {
        if (unit == lit) == 0 {
          %❰flush_prop_state❱;
          interact lrat_fail(2, id, aid, 0, 0)
        }
      };
      unit = lit;
      if val == 0 {
        %❰inline_assign_literal bedrock2_expr:(lit) bedrock2_expr:((lit .>> 63) | 1)❱
      }
    };
    l = l + 4;
    lit = (load4(l) << 32) .>> 32
  }
)

theorem exec_rup_phase2_inner_loop {e : Env} {B : Nat} {t : Trace 64} {m : Mem 64} {l : Locals 64}
    {post : Trace 64 → Mem 64 → Locals 64 → Prop}
    {max_var reserve : Nat}
    {st id aid values_begin trail_begin trail_end0 stat_resolved stat_lit_assigned0 als : BitVec 64}
    {k : KernelFields} {clits : List (BitVec 64)}
    {initAssign curAssign : Assignment} {curTrail curTrailFree : List (BitVec 64)}
    {f : CNF Nat} {R : Mem 64 → Prop}
    (hclits_valid : ∀ x ∈ clits, IsValidLit max_var x)
    (hcl_mem : toClause clits ∈ f)
    (hent : CNF.Entails (f ++ initAssign.toCNF) (f ++ curAssign.toCNF))
    (hcap : reserve + 1 ≤ curTrailFree.length)
    (hst_var : l["st"]? = some st)
    (hid_var : l["id"]? = some id)
    (haid_var : l["aid"]? = some aid)
    (hvb_var : l["values_begin"]? = some values_begin)
    (hte_var : l["trail_end"]? = some trail_end0)
    (hsr_var : l["stat_resolved"]? = some stat_resolved)
    (hsla_var : l["stat_lit_assigned"]? = some stat_lit_assigned0)
    (hunit_var : l["unit"]? = some 0)
    (hl_var : l["l"]? = some als)
    (hlit_var : l["lit"]? = some (zeroTermGet clits 0))
    (hte_eq0 : trail_end0 = trail_begin + BitVec.ofNat 64 (4 * curTrail.length))
    (hcov0 : TrailCoversAssign max_var curAssign curTrail)
    (htrail_valid0 : ∀ tlit ∈ curTrail, IsValidLit max_var tlit)
    (hsep : m =⋆ (byte1Array values_begin (assignBytes max_var curAssign) ⋆
        int4Array trail_begin (curTrail ++ curTrailFree)) ⋆
      (ZeroTermInts als clits ⋆ (kernelState st k ⋆ R)))
    (hpost : ∀ m' l' (unit trail_end stat_lit_assigned : BitVec 64)
        (assign : Assignment) (trail trail_free : List (BitVec 64)),
      l'["unit"]? = some unit →
      l'["trail_end"]? = some trail_end →
      l'["stat_lit_assigned"]? = some stat_lit_assigned →
      (∀ vname, vname ≠ "l" → vname ≠ "lit" → vname ≠ "idx" → vname ≠ "val" →
                vname ≠ "unit" → vname ≠ "trail_end" → vname ≠ "stat_lit_assigned" →
                l'[vname]? = l[vname]?) →
      trail_end = trail_begin + BitVec.ofNat 64 (4 * trail.length) →
      TrailCoversAssign max_var assign trail →
      (∀ tlit ∈ trail, IsValidLit max_var tlit) →
      trail.length + trail_free.length = curTrail.length + curTrailFree.length →
      (m' =⋆ (byte1Array values_begin (assignBytes max_var assign) ⋆
          int4Array trail_begin (trail ++ trail_free)) ⋆
        (ZeroTermInts als clits ⋆ (kernelState st k ⋆ R))) →
      ((unit = 0 ∧ reserve + 1 ≤ trail_free.length ∧ CNF.Unsat (f ++ initAssign.toCNF)) ∨
       (unit ≠ 0 ∧ reserve ≤ trail_free.length ∧
        CNF.Entails (f ++ initAssign.toCNF) (f ++ assign.toCNF))) →
      post t m' l') :
    Exec lratFailExt e B rup_phase2_inner_loop t m l post := by
  unfold rup_phase2_inner_loop
  have h32 : ∀ x ∈ clits, IsInt32 x := fun x hx => (hclits_valid x hx).1
  have hne0 : ∀ x ∈ clits, x ≠ 0 := fun x hx => (hclits_valid x hx).2.1
  let inv (rem : Nat) (t' : Trace 64) (m' : Mem 64) (l' : Locals 64) : Prop :=
    ∃ (i : Nat) (unit trail_end stat_lit_assigned : BitVec 64)
      (assign : Assignment) (trail trail_free : List (BitVec 64)),
      i ≤ clits.length ∧
      rem = clits.length - i ∧
      t' = t ∧
      l'["l"]? = some (als + BitVec.ofNat 64 (4 * i)) ∧
      l'["lit"]? = some (zeroTermGet clits i) ∧
      l'["unit"]? = some unit ∧
      l'["trail_end"]? = some trail_end ∧
      l'["stat_lit_assigned"]? = some stat_lit_assigned ∧
      (∀ vname, vname ≠ "l" → vname ≠ "lit" → vname ≠ "idx" → vname ≠ "val" →
                vname ≠ "unit" → vname ≠ "trail_end" → vname ≠ "stat_lit_assigned" →
                l'[vname]? = l[vname]?) ∧
      trail_end = trail_begin + BitVec.ofNat 64 (4 * trail.length) ∧
      TrailCoversAssign max_var assign trail ∧
      (∀ tlit ∈ trail, IsValidLit max_var tlit) ∧
      trail.length + trail_free.length = curTrail.length + curTrailFree.length ∧
      (m' =⋆ (byte1Array values_begin (assignBytes max_var assign) ⋆
          int4Array trail_begin (trail ++ trail_free)) ⋆
        (ZeroTermInts als clits ⋆ (kernelState st k ⋆ R))) ∧
      ((unit = 0 ∧ assign = curAssign ∧ reserve + 1 ≤ trail_free.length ∧
          ∀ x : Literal Nat, x ∈ (clits.take i).map toLiteral → curAssign.get? x.1 = some !x.2) ∨
       (unit ≠ 0 ∧ IsValidLit max_var unit ∧
          assign.get? (toLiteral unit).1 = some (toLiteral unit).2 ∧
          reserve ≤ trail_free.length ∧
          ((curAssign.get? (toLiteral unit).1 = none ∧
            assign = curAssign.insert (toLiteral unit).1 (toLiteral unit).2) ∨
           assign = curAssign) ∧
          ∀ x : Literal Nat, x ∈ (clits.take i).map toLiteral →
            x = toLiteral unit ∨ curAssign.get? x.1 = some !x.2))
  refine Exec.while_wf (Measure := Nat) Nat.lt_wfRel.wf inv clits.length ?_ ?_
  · refine ⟨0, 0, trail_end0, stat_lit_assigned0, curAssign, curTrail, curTrailFree,
      Nat.zero_le _, by omega, rfl, by simpa using hl_var, hlit_var, hunit_var, hte_var, hsla_var,
      fun _ _ _ _ _ _ _ _ => rfl, hte_eq0, hcov0, htrail_valid0, rfl, hsep,
      Or.inl ⟨rfl, rfl, hcap, by simp⟩⟩
  · rintro rem t' m' l' ⟨i, unit, trail_end, stat_lit_assigned, assign, trail, trail_free,
      hi, rfl, rfl, hl_ptr, hlit_cur, hunit_cur, hte, hsla, hlocals, hte_eq, hcov, htrail_valid,
      hlen_sum, hm', hstate⟩
    have hst := local_pres (hlocals _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) hst_var
    have hid := local_pres (hlocals _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) hid_var
    have haid := local_pres (hlocals _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) haid_var
    have hvb := local_pres (hlocals _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) hvb_var
    have hsr := local_pres (hlocals _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) hsr_var
    refine ⟨zeroTermGet clits i, by simp [Expr.eval, hlit_cur], fun hnz => ?_, fun hz => ?_⟩
    · have hlt : i < clits.length := (zeroTermGet_ne_zero_iff hi hne0).mp hnz
      simp only [zeroTermGet, hlt, ↓reduceDIte] at hlit_cur
      have hlit_valid := hclits_valid clits[i] (List.getElem_mem hlt)
      refine Exec.seq_cps (exec_inline_assigned_literal hlit_cur hvb hlit_valid (sep_1_to_front ▸ hm') ?_)
      let v := evalAssignedLit (assignByte assign (toLiteral clits[i]).1) clits[i]
      let l1 := (l'.insert "idx" (bvAbs clits[i])).insert "val" v
      have hcases := evalAssignedLit_cases assign hlit_valid
      refine Exec.seq_cps ?_
      refine Exec.cond_cps (by simp [Expr.eval, interpBinop] <;> rfl) (fun hnz1 => ?_) (fun hz1 => ?_)
      · simp only [ite_one_zero_ne_zero] at hnz1
        have hfals := hcases.1 hnz1
        refine Exec.cond_cps (by simp [Expr.eval, hunit_cur, hlit_cur, interpBinop, interpOp1] <;> rfl) (fun _ => ?_) (fun hz_neg => ?_)
        · refine exec_flush_and_fail (args := [2, id, aid, 0, 0])
            (by simp [hst] <;> rfl) (by simp [hte] <;> rfl) (by simp [hsr] <;> rfl) (by simp [hsla] <;> rfl) (sep_4_to_front ▸ hm')
            (fun _ => by simp [evalArgs, Expr.eval, hid, haid])
        · simp only [ite_one_zero_eq_zero_prop] at hz_neg
          refine .skip _ _ _ _ _ ?_
          refine exec_advance_zeroTerm hlt (by simp [hl_ptr]) (sep_3_to_front ▸ hm') h32 ?_
          refine ⟨clits.length - (i + 1), ⟨i + 1, unit, trail_end, stat_lit_assigned, assign, trail, trail_free,
            Nat.succ_le_of_lt hlt, rfl, rfl, by simp, by simp, by simp [hunit_cur],
            by simp [hte], by simp [hsla],
            fun _ h1 h2 h3 h4 h5 h6 h7 => by simp [h1.symm, h2.symm, h3.symm, h4.symm, hlocals _ h1 h2 h3 h4 h5 h6 h7],
            hte_eq, hcov, htrail_valid, hlen_sum, hm', ?_⟩, by dsimp only [WellFoundedRelation.rel]; omega⟩
          rcases hstate with ⟨rfl, rfl, hcap_i, hinv_i⟩ | ⟨hunit_nz, hunit_val, hunit_sat, hcap_i, hrel, hinv_i⟩
          · exact Or.inl ⟨rfl, rfl, hcap_i, phase2_inner_falsified_unit0 hlt hinv_i hfals⟩
          · exact Or.inr ⟨hunit_nz, hunit_val, hunit_sat, hcap_i, hrel,
              phase2_inner_falsified_unit_ne0 hlt hlit_valid hunit_sat hrel hinv_i hfals hz_neg⟩
      · simp only [ite_one_zero_eq_zero] at hz1
        rcases hstate with ⟨rfl, rfl, hcap_i, hinv_i⟩ | ⟨hunit_nz, hunit_val, hunit_sat, hcap_i, hrel, hinv_i⟩
        · refine exec_if_cps (v := _) ?_ (fun hnz_u => absurd rfl hnz_u) (fun _ => ?_)
          · simp [Expr.eval, hunit_cur]
          refine Exec.seq_cps (Exec.set_cps (v := clits[i]) (by simp [Expr.eval, hlit_cur]) ?_)
          let l2 := l1.insert "unit" clits[i]
          refine Exec.cond_cps (by simp [Expr.eval, interpBinop] <;> rfl) (fun hnz_v0 => ?_) (fun hz_v0 => ?_)
          · simp only [ite_one_zero_ne_zero_prop] at hnz_v0
            have hun : assign.get? (toLiteral clits[i]).1 = none :=
              (hcases.2.2 ⟨hz1, by rw [hnz_v0]; decide⟩).1
            rcases trail_free with _ | ⟨t0, tf'⟩
            · simp at hcap_i
            · have hlit2 : ∀ m'', (Expr.var "lit").eval m'' l2 = some clits[i] :=
                fun _ => by dsimp [l2, l1]; simp [Expr.eval, hlit_cur]
              refine exec_inline_assign_literal (stat_lit_assigned := stat_lit_assigned)
                (by simp [hvb]) (by simp)
                (by simp [hte]) (by simp [hsla]) hlit_valid
                (eval_sign_byte_expr (hlit2 m')) hlit2 hte_eq hcov hm'
                fun m1 hte_next hcov_next hm1 => ?_
              refine exec_advance_zeroTerm hlt (by simp [hl_ptr]) (sep_3_to_front ▸ hm1) h32 ?_
              refine ⟨clits.length - (i + 1), ⟨i + 1, clits[i], trail_end + 4, stat_lit_assigned + 1,
                assign.insert (toLiteral clits[i]).1 (toLiteral clits[i]).2, trail ++ [clits[i]], tf',
                Nat.succ_le_of_lt hlt, rfl, rfl, by simp, by simp, by simp, by simp, by simp,
                fun _ h1 h2 h3 h4 h5 h6 h7 => by simp [h1.symm, h2.symm, h3.symm, h4.symm, h5.symm, h6.symm, h7.symm, hlocals _ h1 h2 h3 h4 h5 h6 h7], hte_next, hcov_next,
                fun tlit htlit => by rcases List.mem_append.mp htlit with h | h <;> simp_all,
                by simp at hlen_sum ⊢; omega, hm1,
                Or.inr ⟨hlit_valid.2.1, hlit_valid, Assignment.get?_insert_of_eq rfl,
                  by simp at hcap_i; omega, Or.inl ⟨hun, rfl⟩, phase2_inner_new_unit hlt hinv_i⟩⟩, by dsimp only [WellFoundedRelation.rel]; omega⟩
          · simp only [ite_one_zero_eq_zero_prop] at hz_v0
            have hv_pos : (0#64).slt v = true := by
              cases hp : (0#64).slt v
              · exact absurd (hcases.2.2 ⟨hz1, hp⟩).2 hz_v0
              · rfl
            refine .skip _ _ _ _ _ ?_
            refine exec_advance_zeroTerm hlt (by simp [hl_ptr]) (sep_3_to_front ▸ hm') h32 ?_
            refine ⟨clits.length - (i + 1), ⟨i + 1, clits[i], trail_end, stat_lit_assigned, assign, trail, trail_free,
              Nat.succ_le_of_lt hlt, rfl, rfl, by simp, by simp, by simp, by simp [hte], by simp [hsla],
              fun _ h1 h2 h3 h4 h5 h6 h7 => by simp [h1.symm, h2.symm, h3.symm, h4.symm, h5.symm, hlocals _ h1 h2 h3 h4 h5 h6 h7], hte_eq, hcov, htrail_valid, hlen_sum, hm',
              Or.inr ⟨hlit_valid.2.1, hlit_valid, hcases.2.1 ⟨hz1, hv_pos⟩, by omega, Or.inr rfl,
                phase2_inner_new_unit hlt hinv_i⟩⟩, by dsimp only [WellFoundedRelation.rel]; omega⟩
        · refine exec_if_cps (v := _) ?_ (fun _ => ?_) (fun hz_u => absurd hz_u hunit_nz)
          · simp [Expr.eval, hunit_cur]
          refine Exec.cond_cps (by simp [Expr.eval, hunit_cur, hlit_cur, interpBinop] <;> rfl) (fun _ => ?_) (fun hz_eq => ?_)
          · refine exec_flush_and_fail (args := [2, id, aid, 0, 0])
              (by simp [hst] <;> rfl) (by simp [hte] <;> rfl) (by simp [hsr] <;> rfl) (by simp [hsla] <;> rfl) (sep_4_to_front ▸ hm')
              (fun _ => by simp [evalArgs, Expr.eval, hid, haid])
          · have hz_eq' : unit = clits[i] := by
              by_cases h : unit = clits[i]
              · exact h
              · simp [h] at hz_eq
            refine .skip _ _ _ _ _ ?_
            refine Exec.seq_cps (Exec.set_cps (v := clits[i]) (by simp [Expr.eval, hlit_cur]) ?_)
            let l2 := l1.insert "unit" clits[i]
            refine Exec.cond_cps (by simp [Expr.eval, interpBinop] <;> rfl) (fun hnz_v0 => ?_) (fun _ => ?_)
            · simp only [ite_one_zero_ne_zero_prop] at hnz_v0
              have hun : assign.get? (toLiteral clits[i]).1 = none :=
                (hcases.2.2 ⟨hz1, by rw [hnz_v0]; decide⟩).1
              rw [← hz_eq', hunit_sat] at hun
              nomatch hun
            · refine .skip _ _ _ _ _ ?_
              refine exec_advance_zeroTerm hlt (by simp [hl_ptr]) (sep_3_to_front ▸ hm') h32 ?_
              refine ⟨clits.length - (i + 1), ⟨i + 1, clits[i], trail_end, stat_lit_assigned, assign, trail, trail_free,
                Nat.succ_le_of_lt hlt, rfl, rfl, by simp, by simp, by simp, by simp [hte], by simp [hsla],
                fun _ h1 h2 h3 h4 h5 h6 h7 => by simp [h1.symm, h2.symm, h3.symm, h4.symm, h5.symm, hlocals _ h1 h2 h3 h4 h5 h6 h7], hte_eq, hcov, htrail_valid, hlen_sum, hm',
                Or.inr ⟨hlit_valid.2.1, hlit_valid, by rwa [← hz_eq'], hcap_i,
                  by rwa [← hz_eq'], by rw [← hz_eq']; exact phase2_inner_dup_unit hlt hz_eq' hinv_i⟩⟩, by dsimp only [WellFoundedRelation.rel]; omega⟩
    · obtain rfl : i = clits.length := (zeroTermGet_eq_zero_iff hi hne0).mp hz
      rw [List.take_length] at hstate
      rcases hstate with ⟨rfl, rfl, hcap_i, hinv_all⟩ | ⟨hunit_nz, _, _, hcap_i, hrel, hinv_unit⟩
      · have hunsat := unsat_of_all_falsified hcl_mem hent fun x hx => by
          rw [← CNF.Clause.mem_literals_iff, literals_toClause] at hx; exact hinv_all x hx
        exact hpost m' l' 0 trail_end stat_lit_assigned assign trail trail_free
          hunit_cur hte hsla hlocals hte_eq hcov htrail_valid hlen_sum hm' (Or.inl ⟨rfl, hcap_i, hunsat⟩)
      · have hunit_cl : ∀ x ∈ toClause clits, x = toLiteral unit ∨ curAssign.get? x.1 = some !x.2 := fun x hx => by
          rw [← CNF.Clause.mem_literals_iff, literals_toClause] at hx; exact hinv_unit x hx
        have hent' : CNF.Entails (f ++ initAssign.toCNF) (f ++ assign.toCNF) := by
          rcases hrel with ⟨_, rfl⟩ | rfl
          · exact entails_insert_of_unit_prop hcl_mem hent hunit_cl
          · exact hent
        exact hpost m' l' unit trail_end stat_lit_assigned assign trail trail_free
          hunit_cur hte hsla hlocals hte_eq hcov htrail_valid hlen_sum hm' (Or.inr ⟨hunit_nz, hcap_i, hent'⟩)

@[simp] theorem shamt_3_mul_8 (aid : BitVec 64) :
    aid <<< shamt 3#64 = BitVec.ofNat 64 (8 * aid.toNat) := by
  rw [shamt_3, show BitVec.ofNat 64 (8 * aid.toNat) = 8#64 * aid from
    BitVec.eq_of_toNat_eq (by simp [BitVec.toNat_mul])]
  bv_decide

/-- The Phase 2 outer `while aid` loop of `br_check_clause_non_strictly_by_propagation`. -/
def rup_phase2_outer_loop : Cmd := bedrock2_cmd:(
  while aid {
    if aid .< 0 {
      %❰flush_prop_state❱;
      interact lrat_fail(1, id, aid, 0, 0)
    };
    als = load8(literals_begin + (aid << 3));
    stat_resolved = stat_resolved + 1;
    unit = 0;
    l = als;
    lit = (load4(l) << 32) .>> 32;
    %❰rup_phase2_inner_loop❱;
    if unit == 0 {
      checked = 1;
      aid = 0
    } else {
      a = a + 4;
      aid = (load4(a) << 32) .>> 32
    }
  }
)

private theorem bv64_slu3 (x : BitVec 64) : x <<< 3 = BitVec.ofNat 64 (8 * x.toNat) := by
  rw [BitVec.ofNat_mul, BitVec.ofNat_toNat]; bv_decide

theorem exec_rup_phase2_outer_loop {e : Env} {B : Nat} {t : Trace 64} {m : Mem 64} {l : Locals 64}
    {post : Trace 64 → Mem 64 → Locals 64 → Prop}
    {max_var : Nat}
    {st id literals_begin values_begin trail_begin trail_end0 stat_resolved0 stat_lit_assigned0 antecedents : BitVec 64}
    {k : KernelFields} {lit_ptrs aids : List (BitVec 64)}
    {s : State} {initAssign assign0 : Assignment} {trail0 trail_free0 : List (BitVec 64)}
    {P_ro : Mem 64 → Prop}
    (hct : ClauseTable max_var literals_begin lit_ptrs s.formula P_ro)
    (haids_ro : ∃ R_aids, P_ro = (ZeroTermInts antecedents aids ⋆ R_aids))
    (haids_valid : ∀ aid ∈ aids, IsInt32 aid ∧ aid ≠ 0 ∧
      (aid.slt 0 = false → ∃ h : aid.toNat < lit_ptrs.length, lit_ptrs[aid.toNat] ≠ 0))
    (hcap0 : aids.length ≤ trail_free0.length)
    (hent0 : CNF.Entails (s.toCNF ++ initAssign.toCNF) (s.toCNF ++ assign0.toCNF))
    (hst_var : l["st"]? = some st)
    (hid_var : l["id"]? = some id)
    (hlb_var : l["literals_begin"]? = some literals_begin)
    (hvb_var : l["values_begin"]? = some values_begin)
    (htb_var : l["trail_begin"]? = some trail_begin)
    (hte_var : l["trail_end"]? = some trail_end0)
    (hsr_var : l["stat_resolved"]? = some stat_resolved0)
    (hsla_var : l["stat_lit_assigned"]? = some stat_lit_assigned0)
    (hchk_var : l["checked"]? = some 0)
    (ha_var : l["a"]? = some antecedents)
    (haid_var : l["aid"]? = some (zeroTermGet aids 0))
    (hte_eq0 : trail_end0 = trail_begin + BitVec.ofNat 64 (4 * trail0.length))
    (hcov0 : TrailCoversAssign max_var assign0 trail0)
    (htrail_valid0 : ∀ tlit ∈ trail0, IsValidLit max_var tlit)
    (hsep : m =⋆ (byte1Array values_begin (assignBytes max_var assign0) ⋆
        int4Array trail_begin (trail0 ++ trail_free0)) ⋆
      (kernelState st k ⋆ P_ro))
    (hpost : ∀ m' l' (checked trail_end stat_resolved stat_lit_assigned : BitVec 64)
        (assign : Assignment) (trail trail_free : List (BitVec 64)),
      l'["st"]? = some st →
      l'["id"]? = some id →
      l'["values_begin"]? = some values_begin →
      l'["trail_begin"]? = some trail_begin →
      l'["checked"]? = some checked →
      l'["trail_end"]? = some trail_end →
      l'["stat_resolved"]? = some stat_resolved →
      l'["stat_lit_assigned"]? = some stat_lit_assigned →
      trail_end = trail_begin + BitVec.ofNat 64 (4 * trail.length) →
      TrailCoversAssign max_var assign trail →
      (∀ tlit ∈ trail, IsValidLit max_var tlit) →
      trail.length + trail_free.length = trail0.length + trail_free0.length →
      (m' =⋆ (byte1Array values_begin (assignBytes max_var assign) ⋆
          int4Array trail_begin (trail ++ trail_free)) ⋆
        (kernelState st k ⋆ P_ro)) →
      (checked = 0 ∨ (checked = 1 ∧ CNF.Unsat (s.toCNF ++ initAssign.toCNF))) →
      post t m' l') :
    Exec lratFailExt e B rup_phase2_outer_loop t m l post := by
  unfold rup_phase2_outer_loop
  obtain ⟨R_aids, hP_aids⟩ := haids_ro
  have haids_32 : ∀ x ∈ aids, IsInt32 x := fun x hx => (haids_valid x hx).1
  have haids_ne0 : ∀ x ∈ aids, x ≠ 0 := fun x hx => (haids_valid x hx).2.1
  let inv (rem : Nat) (t' : Trace 64) (m' : Mem 64) (l' : Locals 64) : Prop :=
    ∃ (checked trail_end stat_resolved stat_lit_assigned : BitVec 64)
      (assign : Assignment) (trail trail_free : List (BitVec 64)),
      t' = t ∧
      l'["st"]? = some st ∧
      l'["id"]? = some id ∧
      l'["literals_begin"]? = some literals_begin ∧
      l'["values_begin"]? = some values_begin ∧
      l'["trail_begin"]? = some trail_begin ∧
      l'["checked"]? = some checked ∧
      l'["trail_end"]? = some trail_end ∧
      l'["stat_resolved"]? = some stat_resolved ∧
      l'["stat_lit_assigned"]? = some stat_lit_assigned ∧
      trail_end = trail_begin + BitVec.ofNat 64 (4 * trail.length) ∧
      TrailCoversAssign max_var assign trail ∧
      (∀ tlit ∈ trail, IsValidLit max_var tlit) ∧
      trail.length + trail_free.length = trail0.length + trail_free0.length ∧
      (m' =⋆ (byte1Array values_begin (assignBytes max_var assign) ⋆
          int4Array trail_begin (trail ++ trail_free)) ⋆
        (kernelState st k ⋆ P_ro)) ∧
      ((checked = 0 ∧ ∃ j : Nat,
          j ≤ aids.length ∧
          rem = aids.length + 1 - j ∧
          aids.length - j ≤ trail_free.length ∧
          l'["a"]? = some (antecedents + BitVec.ofNat 64 (4 * j)) ∧
          l'["aid"]? = some (zeroTermGet aids j) ∧
          CNF.Entails (s.toCNF ++ initAssign.toCNF) (s.toCNF ++ assign.toCNF)) ∨
       (checked = 1 ∧ rem = 0 ∧ l'["aid"]? = some 0 ∧
          CNF.Unsat (s.toCNF ++ initAssign.toCNF)))
  refine Exec.while_wf (Measure := Nat) Nat.lt_wfRel.wf inv (aids.length + 1) ?_ ?_
  · refine ⟨0, trail_end0, stat_resolved0, stat_lit_assigned0, assign0, trail0, trail_free0,
      rfl, hst_var, hid_var, hlb_var, hvb_var, htb_var, hchk_var, hte_var, hsr_var, hsla_var,
      hte_eq0, hcov0, htrail_valid0, rfl, hsep,
      Or.inl ⟨rfl, 0, Nat.zero_le _, by omega, by omega, by simpa using ha_var, haid_var, hent0⟩⟩
  · rintro rem t' m' l' ⟨checked, trail_end, stat_resolved, stat_lit_assigned, assign, trail, trail_free,
      rfl, hst, hid, hlb, hvb, htb, hchk, hte, hsr, hsla, hte_eq, hcov, htrail_valid, hlen_sum, hm', hstate⟩
    rcases hstate with ⟨rfl, j, hj, rfl, hcap_j, ha_ptr, haid_cur, hent_j⟩ | ⟨rfl, rfl, haid_zero, hunsat⟩
    · refine ⟨zeroTermGet aids j, by simp [Expr.eval, haid_cur], fun hnz => ?_, fun hz => ?_⟩
      · have hlt : j < aids.length := (zeroTermGet_ne_zero_iff hj haids_ne0).mp hnz
        simp only [zeroTermGet, hlt, ↓reduceDIte] at haid_cur
        have haid_val := haids_valid aids[j] (List.getElem_mem hlt)
        refine Exec.seq_cps ?_
        refine Exec.cond_cps (by simp [Expr.eval, haid_cur, interpBinop] <;> rfl)
          (fun _ => ?_) (fun hz_neg => .skip _ _ _ _ _ ?_)
        · refine exec_flush_and_fail (args := [1, id, aids[j], 0, 0])
            hst hte hsr hsla (sep_3_to_front ▸ hm') (fun _ => by simp [evalArgs, Expr.eval, hid, haid_cur])
        · simp only [ite_one_zero_eq_zero] at hz_neg
          obtain ⟨haid_lt_ptrs, hptr_ne0⟩ := haid_val.2.2 hz_neg
          have haid_pos : 0 < aids[j].toNat :=
            Nat.pos_of_ne_zero (fun h0 => haid_val.2.1 (BitVec.eq_of_toNat_eq h0))
          have hals_eval := hct.eval_load_ptr
            (ea := .op .add (.var "literals_begin") (.op .slu (.var "aid") (.literal 3))) (l := l')
            (sep_last4_to_front ▸ hm') haid_lt_ptrs
            (by simp [Expr.eval, hlb, haid_cur, interpBinop, bv64_slu3])
          refine Exec.seq_cps (Exec.set_cps hals_eval ?_)
          refine Exec.seq_cps (Exec.set_cps (v := stat_resolved + 1) (by simp [Expr.eval, hsr, interpBinop]) ?_)
          refine Exec.seq_cps (Exec.set_cps (v := 0) rfl ?_)
          refine Exec.seq_cps (Exec.set_cps (v := lit_ptrs[aids[j].toNat]) (by simp [Expr.eval]) ?_)
          obtain ⟨clits, R1, hP, hclits_valid, hcl_lookup⟩ := hct.2 aids[j].toNat haid_lt_ptrs haid_pos hptr_ne0
          have hm_inner : m' =⋆ (byte1Array values_begin (assignBytes max_var assign) ⋆
              int4Array trail_begin (trail ++ trail_free)) ⋆
            (ZeroTermInts lit_ptrs[aids[j].toNat] clits ⋆ (kernelState st k ⋆ R1)) := by
            have h := hm'; rw [hP] at h; exact sep_cast h (by ac_rfl)
          refine Exec.seq_cps (Exec.set_cps
            (eval_load4_zeroTermGet (Nat.zero_le _) (by simp [Expr.eval])
              (sep_3_to_front ▸ hm_inner) (fun x hx => (hclits_valid x hx).1)) ?_)
          refine Exec.seq_cps (exec_rup_phase2_inner_loop (reserve := aids.length - (j + 1))
            (id := id) (aid := aids[j]) (stat_resolved := stat_resolved + 1) (stat_lit_assigned0 := stat_lit_assigned)
            hclits_valid (mem_toCNF_of_formula_getElem? hcl_lookup) hent_j (by omega)
            (by simp [hst]) (by simp [hid]) (by simp [haid_cur]) (by simp [hvb]) (by simp [hte]) (by simp)
            (by simp [hsla]) (by simp) (by simp) (by simp) hte_eq hcov htrail_valid hm_inner ?_)
          intro m_mid l_mid unit trail_end' stat_lit_assigned' assign' trail' trail_free'
            hunit_mid hte_mid hsla_mid hlocals_mid hte_eq' hcov' htrail_valid' hlen_sum' hm_mid hres_mid
          have hm_restored : m_mid =⋆ (byte1Array values_begin (assignBytes max_var assign') ⋆
              int4Array trail_begin (trail' ++ trail_free')) ⋆ (kernelState st k ⋆ P_ro) := by
            have h := sep_cast hm_mid (by ac_rfl : _ = ((byte1Array values_begin (assignBytes max_var assign') ⋆
              int4Array trail_begin (trail' ++ trail_free')) ⋆ (kernelState st k ⋆ (ZeroTermInts lit_ptrs[aids[j].toNat] clits ⋆ R1))))
            rwa [← hP] at h
          have hst_mid : l_mid["st"]? = some st := local_pres (hlocals_mid "st" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by simp [hst])
          have hid_mid : l_mid["id"]? = some id := local_pres (hlocals_mid "id" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by simp [hid])
          have hlb_mid : l_mid["literals_begin"]? = some literals_begin := local_pres (hlocals_mid "literals_begin" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by simp [hlb])
          have hvb_mid : l_mid["values_begin"]? = some values_begin := local_pres (hlocals_mid "values_begin" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by simp [hvb])
          have htb_mid : l_mid["trail_begin"]? = some trail_begin := local_pres (hlocals_mid "trail_begin" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by simp [htb])
          have hchk_mid : l_mid["checked"]? = some 0 := local_pres (hlocals_mid "checked" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by simp [hchk])
          have hsr_mid : l_mid["stat_resolved"]? = some (stat_resolved + 1) := local_pres (hlocals_mid "stat_resolved" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by simp)
          have ha_mid : l_mid["a"]? = some (antecedents + BitVec.ofNat 64 (4 * j)) := local_pres (hlocals_mid "a" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by simp [ha_ptr])
          refine Exec.cond_cps (by simp [Expr.eval, hunit_mid, interpBinop] <;> rfl) (fun hnz_u0 => ?_) (fun hz_u0 => ?_)
          · simp only [ite_one_zero_ne_zero_prop] at hnz_u0
            rcases hres_mid with ⟨_, _, hunsat⟩ | ⟨hunit_nz, _, _⟩
            · refine Exec.seq_cps (Exec.set_cps (v := 1) rfl ?_)
              refine Exec.set_cps (v := 0) rfl ?_
              exact ⟨0, ⟨1, trail_end', stat_resolved + 1, stat_lit_assigned', assign', trail', trail_free',
                rfl, by simp [hst_mid], by simp [hid_mid], by simp [hlb_mid], by simp [hvb_mid],
                by simp [htb_mid], by simp, by simp [hte_mid], by simp [hsr_mid], by simp [hsla_mid],
                hte_eq', hcov', htrail_valid', hlen_sum'.trans hlen_sum, hm_restored,
                Or.inr ⟨rfl, rfl, by simp, hunsat⟩⟩, by dsimp only [WellFoundedRelation.rel]; omega⟩
            · exact absurd hnz_u0 hunit_nz
          · simp only [ite_one_zero_eq_zero_prop] at hz_u0
            rcases hres_mid with ⟨hu0, _, _⟩ | ⟨_, hcap_next, hent_next⟩
            · exact absurd hu0 hz_u0
            · have hm_aids : m_mid =⋆ ZeroTermInts antecedents aids ⋆
                  ((byte1Array values_begin (assignBytes max_var assign') ⋆
                    int4Array trail_begin (trail' ++ trail_free')) ⋆ (kernelState st k ⋆ R_aids)) := by
                have h := hm_restored; rw [hP_aids] at h; exact sep_cast h (by ac_rfl)
              refine exec_advance_zeroTerm hlt ha_mid hm_aids haids_32 ?_
              exact ⟨_, ⟨0, trail_end', stat_resolved + 1, stat_lit_assigned', assign', trail', trail_free',
                rfl, by simp [hst_mid], by simp [hid_mid], by simp [hlb_mid], by simp [hvb_mid],
                by simp [htb_mid], by simp [hchk_mid], by simp [hte_mid], by simp [hsr_mid],
                by simp [hsla_mid], hte_eq', hcov', htrail_valid', hlen_sum'.trans hlen_sum, hm_restored,
                Or.inl ⟨rfl, j + 1, Nat.succ_le_of_lt hlt, rfl, hcap_next, by simp, by simp, hent_next⟩⟩, by dsimp only [WellFoundedRelation.rel]; omega⟩
      · exact hpost m' l' 0 trail_end stat_resolved stat_lit_assigned assign trail trail_free
          hst hid hvb htb hchk hte hsr hsla hte_eq hcov htrail_valid hlen_sum hm' (Or.inl rfl)
    · exact ⟨0, by simp [Expr.eval, haid_zero], fun hnz => absurd rfl hnz, fun _ =>
        hpost m' l' 1 trail_end stat_resolved stat_lit_assigned assign trail trail_free
          hst hid hvb htb hchk hte hsr hsla hte_eq hcov htrail_valid hlen_sum hm' (Or.inr ⟨rfl, hunsat⟩)⟩

/-! ## 7. Main Theorem: `br_check_clause_non_strictly_by_propagation` -/

theorem eval_load_kernelField {m : Mem 64} {l : Locals 64} {ea : Expr}
    {st : BitVec 64} {k : KernelFields} {R : Mem 64 → Prop}
    (i : Nat) (hi : i < 20)
    (ha : ea.eval m l = some (st + BitVec.ofNat 64 (8 * i)))
    (hsep : m =⋆ kernelState st k ⋆ R) :
    (Expr.load .eight ea).eval m l = some (k.toList[i]'(by simpa [KernelFields.toList] using hi)) :=
  eval_load_word8Array_elem (by simpa [KernelFields.toList] using hi) ha hsep

private theorem eval_load_st {m : Mem 64} {l : Locals 64} {st : BitVec 64} {k : KernelFields}
    {R : Mem 64 → Prop} (i : Nat) (hi : i < 20) (off : Int)
    (hoff : BitVec.ofInt 64 off = BitVec.ofNat 64 (8 * i)) (hst : l["st"]? = some st)
    (hsep : m =⋆ kernelState st k ⋆ R) :
    (Expr.load .eight (.op .add (.var "st") (.literal off))).eval m l =
      some (k.toList[i]'(by simpa [KernelFields.toList] using hi)) :=
  eval_load_kernelField i hi (by simp [Expr.eval, hst, interpBinop, hoff]) hsep

theorem exec_backtrack_and_flush {e : Env} {B : Nat} {t : Trace 64} {m : Mem 64} {l : Locals 64}
    {post : Trace 64 → Mem 64 → Locals 64 → Prop}
    {max_var : Nat} {st trail_end stat_resolved stat_lit_assigned : BitVec 64}
    {k : KernelFields} {assign : Assignment} {trail trail_free : List (BitVec 64)}
    {P_ro : Mem 64 → Prop}
    (hst : l["st"]? = some st)
    (hvb : l["values_begin"]? = some k.values_begin)
    (htb : l["trail_begin"]? = some k.trail_begin)
    (hte : l["trail_end"]? = some trail_end)
    (hsr : l["stat_resolved"]? = some stat_resolved)
    (hsla : l["stat_lit_assigned"]? = some stat_lit_assigned)
    (hte_eq : trail_end = k.trail_begin + BitVec.ofNat 64 (4 * trail.length))
    (htrail_len : 4 * trail.length < 2 ^ 64)
    (hcov : TrailCoversAssign max_var assign trail)
    (htrail_valid : ∀ tlit ∈ trail, IsValidLit max_var tlit)
    (hsep : m =⋆ (byte1Array k.values_begin (assignBytes max_var assign) ⋆
        int4Array k.trail_begin (trail ++ trail_free)) ⋆
      (kernelState st k ⋆ P_ro))
    (hpost : ∀ m' l',
      (m' =⋆ (byte1Array k.values_begin (assignBytes max_var Assignment.empty) ⋆
          int4Array k.trail_begin (trail ++ trail_free)) ⋆
        (kernelState st
          { k with
            trail_end := k.trail_begin
            stat_resolved := stat_resolved
            stat_lit_assigned := stat_lit_assigned } ⋆ P_ro)) →
      post t m' l') :
    Exec lratFailExt e B (.seq inline_backtrack flush_prop_state) t m l post := by
  refine Exec.seq_cps (exec_inline_backtrack hvb htb hte hte_eq htrail_valid htrail_len hcov hsep
    fun m1 l1 hte1 hlocals1 hm1 => ?_)
  have hst1 := local_pres (hlocals1 _ (by decide) (by decide) (by decide) (by decide)) hst
  have hsr1 := local_pres (hlocals1 _ (by decide) (by decide) (by decide) (by decide)) hsr
  have hsla1 := local_pres (hlocals1 _ (by decide) (by decide) (by decide) (by decide)) hsla
  exact exec_flush_prop_state hst1 hte1 hsr1 hsla1 (sep_3_to_front ▸ hm1)
    fun m2 hm2 => hpost m2 l1 (sep_cast hm2 (by ac_rfl))

/-- Complete `Exec` specification for `br_check_clause_non_strictly_by_propagation.2.body`:
Starting with all variables unassigned (`Assignment.empty`) and empty trail (`k.trail_end = k.trail_begin`),
if `br_check_clause_non_strictly_by_propagation` completes without calling `lrat_fail`, then:
1. `CNF.EntailsClause s.toCNF (toClause lits)` holds, and
2. `values_begin` is restored to `assignBytes max_var Assignment.empty` and `k.trail_end` is restored to `k.trail_begin`. -/
theorem exec_br_check_clause_non_strictly_by_propagation
    {e : Env} {B : Nat} {t : Trace 64} {m : Mem 64} {l : Locals 64}
    {post : Trace 64 → Mem 64 → Locals 64 → Prop}
    {max_var : Nat} {st id literals antecedents : BitVec 64}
    {k : KernelFields} {lits aids lit_ptrs trail_free0 : List (BitVec 64)}
    {s : State} {P_ro : Mem 64 → Prop}
    (hk_trail : k.trail_end = k.trail_begin)
    (hct : ClauseTable max_var k.literals_begin lit_ptrs s.formula P_ro)
    (hlits_ro : ∃ R_lits, P_ro = (ZeroTermInts literals lits ⋆ R_lits))
    (haids_ro : ∃ R_aids, P_ro = (ZeroTermInts antecedents aids ⋆ R_aids))
    (hlits_valid : ∀ x ∈ lits, IsValidLit max_var x)
    (haids_valid : ∀ aid ∈ aids, IsInt32 aid ∧ aid ≠ 0 ∧
      (aid.slt 0 = false → ∃ h : aid.toNat < lit_ptrs.length, lit_ptrs[aid.toNat] ≠ 0))
    (hcap : lits.length + aids.length ≤ trail_free0.length)
    (htrail_len : 4 * trail_free0.length < 2 ^ 64)
    (hst_var : l["st"]? = some st)
    (hid_var : l["id"]? = some id)
    (hlits_var : l["literals"]? = some literals)
    (hante_var : l["antecedents"]? = some antecedents)
    (hsep : m =⋆ (byte1Array k.values_begin (assignBytes max_var Assignment.empty) ⋆
        int4Array k.trail_begin trail_free0) ⋆
      (kernelState st k ⋆ P_ro))
    (hpost : ∀ m' l' (stat_resolved stat_lit_assigned : BitVec 64)
        (trail_all : List (BitVec 64)),
      trail_all.length = trail_free0.length →
      (m' =⋆ (byte1Array k.values_begin (assignBytes max_var Assignment.empty) ⋆
          int4Array k.trail_begin trail_all) ⋆
        (kernelState st
          { k with
            trail_end := k.trail_begin
            stat_resolved := stat_resolved
            stat_lit_assigned := stat_lit_assigned } ⋆ P_ro)) →
      CNF.EntailsClause s.toCNF (toClause lits) →
      post t m' l') :
    Exec lratFailExt e B br_check_clause_non_strictly_by_propagation.2.body t m l post := by
  dsimp only [br_check_clause_non_strictly_by_propagation, Func.body]
  have hm_ks := sep_cast hsep (by ac_rfl : _ = kernelState st k ⋆
    ((byte1Array k.values_begin (assignBytes max_var Assignment.empty) ⋆ int4Array k.trail_begin trail_free0) ⋆ P_ro))
  refine Exec.seq_cps (Exec.set_cps (by simpa [KernelFields.toList] using eval_load_st 2 (by decide) 16 rfl hst_var hm_ks) ?_)
  refine Exec.seq_cps (Exec.set_cps (by simpa [KernelFields.toList] using eval_load_st 3 (by decide) 24 rfl (by simp [hst_var]) hm_ks) ?_)
  refine Exec.seq_cps (Exec.set_cps (by simpa [KernelFields.toList] using eval_load_st 5 (by decide) 40 rfl (by simp [hst_var]) hm_ks) ?_)
  refine Exec.seq_cps (Exec.set_cps (v := k.trail_begin)
    (by rw [← hk_trail]; simpa [KernelFields.toList] using eval_load_st 6 (by decide) 48 rfl (by simp [hst_var]) hm_ks) ?_)
  have h18 : (Expr.load .eight (.op .add (.var "st") (.literal 144))).eval m l = some k.stat_resolved := by
    simpa [KernelFields.toList] using eval_load_st 18 (by decide) 144 rfl (by simp [hst_var]) hm_ks
  simp [Expr.eval, interpBinop] at h18
  refine Exec.seq_cps (Exec.set_cps (v := k.stat_resolved + 1)
    (by simp [Expr.eval, h18, interpBinop]) ?_)
  refine Exec.seq_cps (Exec.set_cps (by simpa [KernelFields.toList] using eval_load_st 19 (by decide) 152 rfl (by simp [hst_var]) hm_ks) ?_)
  refine Exec.seq_cps (Exec.set_cps (v := 0) rfl ?_)
  refine Exec.seq_cps (Exec.set_cps (v := literals) (by simp [Expr.eval, hlits_var]) ?_)
  obtain ⟨R_lits, hP_lits⟩ := hlits_ro
  have hm_p1 : m =⋆ (byte1Array k.values_begin (assignBytes max_var Assignment.empty) ⋆
      int4Array k.trail_begin trail_free0) ⋆ (ZeroTermInts literals lits ⋆ (kernelState st k ⋆ R_lits)) := by
    have h := hsep; rw [hP_lits] at h; exact sep_cast h (by ac_rfl)
  refine Exec.seq_cps (Exec.set_cps (eval_load4_zeroTermGet (Nat.zero_le _) (by simp [Expr.eval])
    (sep_3_to_front ▸ hm_p1) (fun x hx => (hlits_valid x hx).1)) ?_)
  refine Exec.seq_cps (exec_rup_phase1_loop (reserve := aids.length) (stat_lit_assigned0 := k.stat_lit_assigned)
    (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) hlits_valid (by omega) hm_p1 ?_)
  intro m1 l1 checked1 trail_end1 stat_lit_assigned1 assign1 trail1 trail_free1
    hchk1 hte1 hsla1 hlocals1 hte_eq1 hcov1 htrail_valid1 hlen_sum1 hcap1 hm1 hres1
  have hm1_restored : m1 =⋆ (byte1Array k.values_begin (assignBytes max_var assign1) ⋆
      int4Array k.trail_begin (trail1 ++ trail_free1)) ⋆ (kernelState st k ⋆ P_ro) := by
    have h := sep_cast hm1 (by ac_rfl : _ = ((byte1Array k.values_begin (assignBytes max_var assign1) ⋆
      int4Array k.trail_begin (trail1 ++ trail_free1)) ⋆ (kernelState st k ⋆ (ZeroTermInts literals lits ⋆ R_lits))))
    rwa [← hP_lits] at h
  have hst1 : l1["st"]? = some st := local_pres (hlocals1 "st" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by simp [hst_var])
  have hid1 : l1["id"]? = some id := local_pres (hlocals1 "id" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by simp [hid_var])
  have hante1 : l1["antecedents"]? = some antecedents := local_pres (hlocals1 "antecedents" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by simp [hante_var])
  have hlb1 : l1["literals_begin"]? = some k.literals_begin := local_pres (hlocals1 "literals_begin" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by simp)
  have hvb1 : l1["values_begin"]? = some k.values_begin := local_pres (hlocals1 "values_begin" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by simp)
  have htb1 : l1["trail_begin"]? = some k.trail_begin := local_pres (hlocals1 "trail_begin" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by simp)
  have hsr1 : l1["stat_resolved"]? = some (k.stat_resolved + 1) := local_pres (hlocals1 "stat_resolved" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by simp)
  rcases hres1 with ⟨rfl, hiff_fals⟩ | ⟨rfl, htaut⟩
  · refine Exec.seq_cps (Exec.cond_cps (v := 1) (by simp [Expr.eval, hchk1, interpBinop] <;> rfl)
      (fun _ => ?_) (fun hz => absurd hz (by decide)))
    refine Exec.seq_cps (Exec.set_cps (v := antecedents) (by simp [Expr.eval, hante1]) ?_)
    obtain ⟨R_aids, hP_aids⟩ := haids_ro
    have hm1_aids_front : m1 =⋆ ZeroTermInts antecedents aids ⋆
        ((byte1Array k.values_begin (assignBytes max_var assign1) ⋆
          int4Array k.trail_begin (trail1 ++ trail_free1)) ⋆ (kernelState st k ⋆ R_aids)) := by
      have h := hm1_restored; rw [hP_aids] at h; exact sep_cast h (by ac_rfl)
    refine Exec.seq_cps (Exec.set_cps (eval_load4_zeroTermGet (Nat.zero_le _) (by simp [Expr.eval])
      hm1_aids_front (fun x hx => (haids_valid x hx).1)) ?_)
    refine exec_rup_phase2_outer_loop (id := id) (initAssign := assign1)
      (stat_resolved0 := k.stat_resolved + 1) (stat_lit_assigned0 := stat_lit_assigned1)
      hct ⟨R_aids, hP_aids⟩ haids_valid hcap1 (CNF.entails_refl _)
      (by simp [hst1]) (by simp [hid1]) (by simp [hlb1]) (by simp [hvb1]) (by simp [htb1])
      (by simp [hte1]) (by simp [hsr1]) (by simp [hsla1]) (by simp [hchk1]) (by simp) (by simp)
      hte_eq1 hcov1 htrail_valid1 hm1_restored ?_
    intro m2 l2 checked2 trail_end2 stat_resolved2 stat_lit_assigned2 assign2 trail2 trail_free2
      hst2 hid2 hvb2 htb2 hchk2 hte2 hsr2 hsla2 hte_eq2 hcov2 htrail_valid2 hlen_sum2 hm2 hres2
    rcases hres2 with rfl | ⟨rfl, hunsat⟩
    · refine Exec.seq_cps (Exec.cond_cps (v := 1) (by simp [Expr.eval, hchk2, interpBinop] <;> rfl)
        (fun _ => ?_) (fun hz => absurd hz (by decide)))
      exact exec_flush_and_fail (args := [3, id, 0, 0, 0]) hst2 hte2 hsr2 hsla2 (sep_3_to_front ▸ hm2)
        (fun _ => by simp [evalArgs, Expr.eval, hid2])
    · refine Exec.seq_cps (Exec.cond_cps (v := 0) (by simp [Expr.eval, hchk2, interpBinop] <;> rfl)
        (fun hnz => absurd rfl hnz) (fun _ => .skip _ _ _ _ _ ?_))
      exact exec_backtrack_and_flush hst2 hvb2 htb2 hte2 hsr2 hsla2 hte_eq2 (by omega) hcov2 htrail_valid2 hm2
        fun m3 l3 hm3 => hpost m3 l3 stat_resolved2 stat_lit_assigned2 (trail2 ++ trail_free2)
          (by rw [List.length_append, hlen_sum2, hlen_sum1]) hm3
          (entailsClause_of_unsat_of_iff_falsified hiff_fals hunsat)
  · refine Exec.seq_cps (Exec.cond_cps (v := 0) (by simp [Expr.eval, hchk1, interpBinop] <;> rfl)
      (fun hnz => absurd rfl hnz) (fun _ => .skip _ _ _ _ _ ?_))
    refine Exec.seq_cps (Exec.cond_cps (v := 0) (by simp [Expr.eval, hchk1, interpBinop] <;> rfl)
      (fun hnz => absurd rfl hnz) (fun _ => .skip _ _ _ _ _ ?_))
    exact exec_backtrack_and_flush hst1 hvb1 htb1 hte1 hsr1 hsla1 hte_eq1 (by omega) hcov1 htrail_valid1
      hm1_restored fun m3 l3 hm3 => hpost m3 l3 (k.stat_resolved + 1) stat_lit_assigned1 (trail1 ++ trail_free1)
        (by rw [List.length_append, hlen_sum1]) hm3 (entailsClause_of_tautology htaut)

/-- Top-level `call` specification for `br_check_clause_non_strictly_by_propagation`:
Establishes `CNF.EntailsClause s.toCNF (toClause lits)` and restores `values_begin` to
`assignBytes max_var Assignment.empty` and `k.trail_end` to `k.trail_begin`. -/
theorem br_check_clause_non_strictly_by_propagation_ok
    {e : Env} {B : Nat} {t : Trace 64} {m : Mem 64}
    {post : Trace 64 → Mem 64 → List (BitVec 64) → Prop}
    {max_var : Nat} {st id literals antecedents : BitVec 64}
    {k : KernelFields} {lits aids lit_ptrs trail_free0 : List (BitVec 64)}
    {s : State} {P_ro : Mem 64 → Prop}
    (hfn : e.lookup br_check_clause_non_strictly_by_propagation.1 =
      some br_check_clause_non_strictly_by_propagation.2)
    (hk_trail : k.trail_end = k.trail_begin)
    (hct : ClauseTable max_var k.literals_begin lit_ptrs s.formula P_ro)
    (hlits_ro : ∃ R_lits, P_ro = (ZeroTermInts literals lits ⋆ R_lits))
    (haids_ro : ∃ R_aids, P_ro = (ZeroTermInts antecedents aids ⋆ R_aids))
    (hlits_valid : ∀ x ∈ lits, IsValidLit max_var x)
    (haids_valid : ∀ aid ∈ aids, IsInt32 aid ∧ aid ≠ 0 ∧
      (aid.slt 0 = false → ∃ h : aid.toNat < lit_ptrs.length, lit_ptrs[aid.toNat] ≠ 0))
    (hcap : lits.length + aids.length ≤ trail_free0.length)
    (htrail_len : 4 * trail_free0.length < 2 ^ 64)
    (hsep : m =⋆ (byte1Array k.values_begin (assignBytes max_var Assignment.empty) ⋆
        int4Array k.trail_begin trail_free0) ⋆
      (kernelState st k ⋆ P_ro))
    (hpost : ∀ m' (stat_resolved stat_lit_assigned : BitVec 64)
        (trail_all : List (BitVec 64)),
      trail_all.length = trail_free0.length →
      (m' =⋆ (byte1Array k.values_begin (assignBytes max_var Assignment.empty) ⋆
          int4Array k.trail_begin trail_all) ⋆
        (kernelState st
          { k with
            trail_end := k.trail_begin
            stat_resolved := stat_resolved
            stat_lit_assigned := stat_lit_assigned } ⋆ P_ro)) →
      CNF.EntailsClause s.toCNF (toClause lits) →
      post t m' []) :
    call lratFailExt e B br_check_clause_non_strictly_by_propagation.1 t m
      [st, id, literals, antecedents] post := by
  let l₀ : Locals 64 :=
    insertMany ∅ (br_check_clause_non_strictly_by_propagation.2.params.zip [st, id, literals, antecedents])
  refine call.of_body hfn rfl ?_
  change Exec lratFailExt e B br_check_clause_non_strictly_by_propagation.2.body t m l₀
    (fun t' m' l' => ∃ rets, getMany l' [] = some rets ∧ post t' m' rets)
  exact exec_br_check_clause_non_strictly_by_propagation
    (st := st) (id := id) (literals := literals) (antecedents := antecedents)
    hk_trail hct hlits_ro haids_ro hlits_valid haids_valid hcap htrail_len
    (by simp [l₀, br_check_clause_non_strictly_by_propagation, insertMany_cons, insertMany_nil])
    (by simp [l₀, br_check_clause_non_strictly_by_propagation, insertMany_cons, insertMany_nil])
    (by simp [l₀, br_check_clause_non_strictly_by_propagation, insertMany_cons, insertMany_nil])
    (by simp [l₀, br_check_clause_non_strictly_by_propagation, insertMany_cons, insertMany_nil])
    hsep (fun m' _ sr sla trail_all hlen hm' hent => ⟨[], rfl, hpost m' sr sla trail_all hlen hm' hent⟩)

end Kraken.Bedrock2.Test
