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

/-! ## 1. Pure RUP Metatheory Bridge Lemmas -/

/-- If a clause contains both `(atom, pol)` and `(atom, !pol)`, it is a tautology and entailed by any formula. -/
theorem entailsClause_of_tautology {f : CNF Nat} {clause : CNF.Clause Nat}
    (h : ∃ atom pol, (atom, pol) ∈ clause ∧ (atom, !pol) ∈ clause) :
    CNF.EntailsClause f clause := by
  rcases h with ⟨atom, pol, h1, h2⟩
  exact CNF.entails_clause_of_forall_sat (CNF.Clause.sat_of_mem_of_mem_neg h1 h2)

/-- An assignment `assign` whose assigned literals are exact negations of `clause` satisfies
`CNF.IsNegationOf assign.toCNF clause`. -/
theorem isNegationOf_of_iff_falsified {clause : CNF.Clause Nat} {assign : Assignment}
    (h : ∀ lit : Literal Nat, lit ∈ clause ↔ assign.get? lit.1 = some !lit.2) :
    CNF.IsNegationOf assign.toCNF clause := by
  rw [CNF.isNegationOf_def]
  intro a
  rw [Assignment.sat_toCNF_iff, CNF.Clause.not_sat_iff_forall_mem_ne]
  constructor
  · intro h1 lit hlit
    have hget := (h lit).mp hlit
    have ha := h1 lit.1 (!lit.2) hget
    simp [ha]
  · intro h1 atom pol hget
    have hmem := (h (atom, !pol)).mpr (by simpa using hget)
    have hne := h1 (atom, !pol) hmem
    simpa using hne

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
    CNF.Unsat (f ++ initAssign.toCNF) := by
  refine CNF.unsat_of_entails_unsat ?_ hent
  rw [CNF.unsat_iff_not_sat]
  intro a hsat
  rw [CNF.sat_append] at hsat
  exact Assignment.not_sat_of_forall_falsified hsat.2 hall (CNF.sat_of_mem hsat.1 hc)

/-- Unit propagation step in RUP: if `c ∈ f` has all literals except `unit` falsified by `curAssign`,
then `f ++ initAssign.toCNF` entails `f ++ (curAssign.insert unit.1 unit.2).toCNF`. -/
theorem entails_insert_of_unit_prop {f : CNF Nat} {initAssign curAssign : Assignment}
    {c : CNF.Clause Nat} {unit : Literal Nat} (hc : c ∈ f)
    (hent : CNF.Entails (f ++ initAssign.toCNF) (f ++ curAssign.toCNF))
    (hall : ∀ lit ∈ c, lit = unit ∨ curAssign.get? lit.1 = some !lit.2) :
    CNF.Entails (f ++ initAssign.toCNF) (f ++ (curAssign.insert unit.1 unit.2).toCNF) := by
  apply CNF.entails_trans hent
  apply CNF.entails_append_of_entails CNF.append_entails_left
  apply CNF.entails_trans (h2 := Assignment.toCNF_add_entails_toCNF_insert)
  rw [CNF.entails_add_iff]
  refine ⟨CNF.append_entails_right, ?_⟩
  rw [CNF.entails_clause_def]
  intro a ha
  rw [CNF.sat_append] at ha
  rw [CNF.Clause.sat_unit_iff]
  exact Assignment.unit_propagation ha.2 (CNF.sat_of_mem ha.1 hc) hall

/-- Lookup in `State.formula` at `aid - 1` yields membership in `s.toCNF`. -/
theorem mem_toCNF_of_formula_getElem? {s : State} {aid : Nat} {c : CNF.Clause Nat}
    (hget : s.formula[aid - 1]? = some (some c)) :
    c ∈ s.toCNF := by
  apply State.mem_toCNF_of_eq_some (idx := aid)
  rw [State.get?, Array.getD_eq_getD_getElem?, hget]
  rfl

/-! ## 2. Signed BitVec & Expression Evaluation Helpers -/

theorem isValidLit_neg {max_var : Nat} {lit : BitVec 64} (h : IsValidLit max_var lit) :
    IsValidLit max_var (-lit) := by
  obtain ⟨h32, hne, hle, hmax⟩ := h
  have hnotmin : lit ≠ 0xffffffff80000000#64 := by
    rintro rfl
    have : (bvAbs 0xffffffff80000000#64).toNat = 2 ^ 31 := by decide
    omega
  refine ⟨?_, ?_, ?_, hmax⟩
  · unfold IsInt32 at h32 ⊢
    revert h32 hne hnotmin; bv_decide
  · revert h32 hne hnotmin; bv_decide
  · rw [bvAbs_neg ⟨h32, hne, hle, hmax⟩]
    exact hle

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
  have hs : shamt 63#64 = 63 := by decide
  rw [hs]

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
  refine Exec.seq_cps (Exec.set_cps (v := bvAbs lit) (eval_ite_abs hlit_var) ?_)
  let l1 : Locals 64 := l.insert "idx" (bvAbs lit)
  have hi : (toLiteral lit).1 < (assignBytes max_var assign).length := by
    simp [toLiteral]; have := hlit.2.2.1; omega
  have ha : (Expr.op .add (.var "values_begin") (.var "idx")).eval m l1 =
      some (values_begin + BitVec.ofNat 64 (toLiteral lit).1) := by
    have h1 : l1["values_begin"]? = some values_begin := by simp [l1, hvb_var]
    have h2 : l1["idx"]? = some (bvAbs lit) := by simp [l1]
    simp [Expr.eval, h1, h2, interpBinop, toLiteral]
  have h8 : IsInt8 (assignBytes max_var assign)[(toLiteral lit).1] := by
    rw [getElem_assignBytes max_var assign (by simpa using hi)]
    exact isInt8_assignByte assign (toLiteral lit).1
  have hload := eval_load1_byte1Array_elem hi ha hsep h8
  rw [getElem_assignBytes max_var assign (by simpa using hi)] at hload
  let b := assignByte assign (toLiteral lit).1
  refine Exec.seq_cps (Exec.set_cps (v := b) hload ?_)
  let l2 : Locals 64 := l1.insert "val" b
  have hcond : (Expr.op .lts (.var "lit") (.literal 0)).eval m l2 =
      some (if lit.slt 0 then 1 else 0) := by
    simp [l2, l1, Expr.eval, hlit_var, interpBinop]
  refine Exec.cond_cps hcond (fun hnz => ?_) (fun hz => ?_)
  · have hslt : lit.slt 0#64 = true := by cases h : lit.slt 0#64 <;> simp_all
    refine Exec.set_cps (v := -b) (by simp [Expr.eval, interpOp1]) ?_
    have hins : l2.insert "val" (-b) = l1.insert "val" (evalAssignedLit b lit) := by
      apply ExtHashMap.ext_getElem?; intro k
      by_cases hk : "val" = k <;> simp [hk, l2, evalAssignedLit, hslt]
    rw [hins]
    exact hpost
  · have hslt : lit.slt 0#64 = false := by cases h : lit.slt 0#64 <;> simp_all
    refine Exec.skip _ _ _ _ _ ?_
    have hval : evalAssignedLit b lit = b := by simp [evalAssignedLit, hslt]
    simpa [l2, l1, b, hval] using hpost

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
  have ha1 : (Expr.op .add (.var "values_begin") (.var "idx")).eval m l =
      some (values_begin + BitVec.ofNat 64 (toLiteral wlit).1) := by
    simp [Expr.eval, hvb, hidx, interpBinop, toLiteral]
  rw [sep_assoc] at hsep
  refine Exec.seq_cps (store_byte1Array_elem hi ha1 heval_val hsep fun m1 hm1 => ?_)
  rw [assignBytes_set_insert max_var assign hwlit, sep_comm_l] at hm1
  have hti : trail.length < (trail ++ t0 :: trail_free).length := by simp
  have ha2 : (Expr.var "trail_end").eval m1 l =
      some (trail_begin + BitVec.ofNat 64 (4 * trail.length)) := by
    simp [Expr.eval, hte, hte_eq]
  refine Exec.seq_cps (store_int4Array_elem hti ha2 (heval_lit m1) hm1 fun m2 hm2 => ?_)
  have hset_trail : (trail ++ t0 :: trail_free).set trail.length wlit = (trail ++ [wlit]) ++ trail_free := by
    rw [List.set_append_right _ _ (Nat.le_refl _), Nat.sub_self, List.set_cons_zero, List.append_assoc]
    rfl
  rw [hset_trail, sep_comm_l, ← sep_assoc] at hm2
  refine Exec.seq_cps (Exec.set_cps (v := trail_end + 4)
    (by simp [Expr.eval, hte, interpBinop]) ?_)
  refine Exec.set_cps (v := stat_lit_assigned + 1)
    (by simp [Expr.eval, hstat, interpBinop]) ?_
  have hte_next : trail_end + 4 = trail_begin + BitVec.ofNat 64 (4 * (trail ++ [wlit]).length) := by
    rw [hte_eq, List.length_append, List.length_singleton]
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_add]
    omega
  exact hpost m2 hte_next (trailCoversAssign_insert wlit hcov) hm2

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
  unfold flush_prop_state
  unfold kernelState at hsep
  have hi6 : 6 < k.toList.length := by simp [KernelFields.toList]
  have ha6 : (Expr.op .add (.var "st") (.literal 48)).eval m l = some (st + BitVec.ofNat 64 (8 * 6)) := by
    simp [Expr.eval, hst, interpBinop]
  refine Exec.seq_cps (store_word8Array_elem hi6 ha6 hte hsep fun m1 hm1 => ?_)
  have hi18 : 18 < (k.toList.set 6 trail_end).length := by simp [KernelFields.toList]
  have ha18 : (Expr.op .add (.var "st") (.literal 144)).eval m1 l = some (st + BitVec.ofNat 64 (8 * 18)) := by
    simp [Expr.eval, hst, interpBinop]
  refine Exec.seq_cps (store_word8Array_elem hi18 ha18 hsr hm1 fun m2 hm2 => ?_)
  have hi19 : 19 < ((k.toList.set 6 trail_end).set 18 stat_resolved).length := by simp [KernelFields.toList]
  have ha19 : (Expr.op .add (.var "st") (.literal 152)).eval m2 l = some (st + BitVec.ofNat 64 (8 * 19)) := by
    simp [Expr.eval, hst, interpBinop]
  refine store_word8Array_elem hi19 ha19 hsla hm2 fun m3 hm3 => ?_
  have hlist : ((k.toList.set 6 trail_end).set 18 stat_resolved).set 19 stat_lit_assigned =
      ({ k with trail_end := trail_end, stat_resolved := stat_resolved, stat_lit_assigned := stat_lit_assigned } : KernelFields).toList := rfl
  rw [hlist] at hm3
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
  unfold zeroTermGet
  split
  · next hlt =>
    exact eval_load4_zeroTermInts_elem hlt ha hsep (h32 xs[i] (List.getElem_mem hlt))
  · next hge =>
    have heq : i = xs.length := by omega
    subst heq
    exact eval_load4_zeroTermInts_end ha hsep

theorem zeroTermGet_ne_zero_iff {xs : List (BitVec 64)} {i : Nat}
    (_hi : i ≤ xs.length) (hne0 : ∀ x ∈ xs, x ≠ 0) :
    zeroTermGet xs i ≠ 0 ↔ i < xs.length := by
  unfold zeroTermGet
  split
  · next hlt =>
    have hne : xs[i] ≠ 0 := hne0 xs[i] (List.getElem_mem hlt)
    exact ⟨fun _ => hlt, fun _ => hne⟩
  · next hge =>
    simp [hge]

theorem zeroTermGet_eq_zero_iff {xs : List (BitVec 64)} {i : Nat}
    (hi : i ≤ xs.length) (hne0 : ∀ x ∈ xs, x ≠ 0) :
    zeroTermGet xs i = 0 ↔ i = xs.length := by
  unfold zeroTermGet
  split
  · next hlt =>
    have hne : xs[i] ≠ 0 := hne0 xs[i] (List.getElem_mem hlt)
    exact ⟨fun h => False.elim (hne h), fun _ => by omega⟩
  · next hge =>
    exact ⟨fun _ => by omega, fun _ => rfl⟩

theorem ptr_step_4 (p : BitVec 64) (i : Nat) :
    p + BitVec.ofNat 64 (4 * i) + 4#64 = p + BitVec.ofNat 64 (4 * (i + 1)) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add]
  omega

theorem clearTrailBytes_append (bs : List (BitVec 64)) (t1 t2 : List (BitVec 64)) :
    clearTrailBytes bs (t1 ++ t2) = clearTrailBytes (clearTrailBytes bs t1) t2 := by
  unfold clearTrailBytes
  exact List.foldl_append

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
  · refine ⟨0, Nat.zero_le _, by omega, rfl, by simp, fun k hkt _ _ => by simp [hkt.symm], ?_⟩
    simpa [bs0] using hsep
  · rintro rem t' m' l' ⟨i, hi, rfl, rfl, ht_var, hlocals, hm'⟩
    have hte' : l'["trail_end"]? = some trail_end := by
      rw [hlocals "trail_end" (by decide) (by decide) (by decide), hte]
    have htb' : l'["trail_begin"]? = some trail_begin := by
      rw [hlocals "trail_begin" (by decide) (by decide) (by decide), htb]
    have hvb' : l'["values_begin"]? = some values_begin := by
      rw [hlocals "values_begin" (by decide) (by decide) (by decide), hvb]
    let t_val := trail_begin + BitVec.ofNat 64 (4 * i)
    let cond_val : BitVec 64 := if (if t_val == trail_end then 1#64 else 0#64) == 0#64 then 1#64 else 0#64
    refine ⟨cond_val, ?_, fun hnz => ?_, fun hz => ?_⟩
    · simp [Expr.eval, ht_var, hte', interpBinop, t_val, cond_val]
    · have hne_ptr : t_val ≠ trail_end := by
        intro heq; apply hnz; simp [cond_val, heq]
      have hlt : i < trail.length := by
        rcases Nat.eq_or_lt_of_le hi with rfl | hlt
        · exact False.elim (hne_ptr hte_eq.symm)
        · exact hlt
      have hti : i < (trail ++ trail_free).length := by simp; omega
      have hm_trail : m' =⋆ int4Array trail_begin (trail ++ trail_free) ⋆
          (byte1Array values_begin (clearTrailBytes bs0 (trail.take i)) ⋆ R) := by
        rw [sep_assoc, sep_comm_l] at hm'; exact hm'
      have hvalid_i : IsValidLit max_var trail[i] := htrail_valid trail[i] (List.getElem_mem hlt)
      have hget_i : (trail ++ trail_free)[i] = trail[i] := List.getElem_append_left hlt
      have h32_i : IsInt32 (trail ++ trail_free)[i] := by rw [hget_i]; exact hvalid_i.1
      have hload_tlit := eval_load4_int4Array_elem (ea := .var "t") hti ht_var hm_trail h32_i
      rw [hget_i] at hload_tlit
      refine Exec.seq_cps (Exec.set_cps (v := trail[i]) hload_tlit ?_)
      let l1 := l'.insert "tlit" trail[i]
      have htlit_var : l1["tlit"]? = some trail[i] := by simp [l1]
      refine Exec.seq_cps (Exec.set_cps (v := bvAbs trail[i]) (eval_ite_abs htlit_var) ?_)
      let l2 := l1.insert "tidx" (bvAbs trail[i])
      have hidx_lt : (bvAbs trail[i]).toNat < (clearTrailBytes bs0 (trail.take i)).length := by
        simp [bs0]; have := hvalid_i.2.2.1; omega
      have ha_store : (Expr.op .add (.var "values_begin") (.var "tidx")).eval m' l2 =
          some (values_begin + BitVec.ofNat 64 (bvAbs trail[i]).toNat) := by
        have h1 : l2["values_begin"]? = some values_begin := by simp [l2, l1, hvb']
        have h2 : l2["tidx"]? = some (bvAbs trail[i]) := by simp [l2]
        simp [Expr.eval, h1, h2, interpBinop]
      have hm_bs : m' =⋆ byte1Array values_begin (clearTrailBytes bs0 (trail.take i)) ⋆
          (int4Array trail_begin (trail ++ trail_free) ⋆ R) := by
        rw [sep_assoc] at hm'; exact hm'
      refine Exec.seq_cps (store_byte1Array_elem (v := 0) hidx_lt ha_store rfl hm_bs fun m1 hm1 => ?_)
      rw [clearTrailBytes_take_succ bs0 trail hlt, ← sep_assoc] at hm1
      refine Exec.set_cps (v := t_val + 4) (by simp [Expr.eval, ht_var, interpBinop, t_val]) ?_
      refine ⟨trail.length - (i + 1), ⟨i + 1, Nat.succ_le_of_lt hlt, rfl, rfl, ?_, ?_, hm1⟩,
        show trail.length - (i + 1) < trail.length - i by omega⟩
      · simp [t_val]
        exact ptr_step_4 trail_begin i
      · intro k hkt hktlit hktidx
        simp [Ne.symm hkt, Ne.symm hktlit, Ne.symm hktidx, hlocals k hkt hktlit hktidx]
    · have heq_ptr : t_val = trail_end := by
        by_cases h : t_val = trail_end
        · exact h
        · exfalso; revert hz; simp [cond_val, h]
      have hi_eq : i = trail.length := by
        rw [hte_eq] at heq_ptr
        have hsub : BitVec.ofNat 64 (4 * i) = BitVec.ofNat 64 (4 * trail.length) := by
          have := congrArg (fun x => x - trail_begin) heq_ptr
          simpa [t_val, BitVec.add_comm trail_begin, BitVec.add_sub_cancel] using this
        have hnat := congrArg BitVec.toNat hsub
        simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 4 * i < 2 ^ 64),
          Nat.mod_eq_of_lt htrail_len] at hnat
        omega
      subst hi_eq
      rw [List.take_length, clearTrailBytes_assignBytes hcov] at hm'
      refine Exec.set_cps (v := trail_begin) (by simp [Expr.eval, htb']) ?_
      refine hpost m' (l'.insert "trail_end" trail_begin) (by simp) (fun k hkt hktlit hktidx hkte => ?_) hm'
      simp [Ne.symm hkte, hlocals k hkt hktlit hktidx]

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
  cases assign.get? (bvAbs lit).toNat with
  | none =>
    cases lit.slt 0 <;> decide
  | some pol =>
    cases pol <;> cases lit.slt 0 <;> decide

theorem phase1_step_already_falsified {lits : List (BitVec 64)} {i : Nat} {assign : Assignment}
    (hlt : i < lits.length)
    (hinv : ∀ x : Literal Nat, x ∈ (lits.take i).map toLiteral ↔ assign.get? x.1 = some !x.2)
    (hfals : assign.get? (toLiteral lits[i]).1 = some !(toLiteral lits[i]).2) :
    ∀ x : Literal Nat, x ∈ (lits.take (i + 1)).map toLiteral ↔ assign.get? x.1 = some !x.2 := by
  intro x
  rw [List.take_add_one, List.getElem?_eq_getElem hlt, Option.toList_some,
    List.map_append, List.map_singleton, List.mem_append, List.mem_singleton, hinv x]
  constructor
  · rintro (h | rfl)
    · exact h
    · exact hfals
  · intro h
    exact Or.inl h

theorem phase1_step_tautology {lits : List (BitVec 64)} {i : Nat} {assign : Assignment}
    (hlt : i < lits.length)
    (hinv : ∀ x : Literal Nat, x ∈ (lits.take i).map toLiteral ↔ assign.get? x.1 = some !x.2)
    (hsat : assign.get? (toLiteral lits[i]).1 = some (toLiteral lits[i]).2) :
    ∃ atom pol, (atom, pol) ∈ toClause lits ∧ (atom, !pol) ∈ toClause lits := by
  let lit := toLiteral lits[i]
  have h1 : lit ∈ toClause lits := by
    rw [ ← CNF.Clause.mem_literals_iff, literals_toClause]
    exact List.mem_map_of_mem (List.getElem_mem hlt)
  have h2_pre : (lit.1, !lit.2) ∈ (lits.take i).map toLiteral := by
    rw [hinv (lit.1, !lit.2)]
    simpa [lit] using hsat
  rcases List.mem_map.mp h2_pre with ⟨y, hy_take, hy_eq⟩
  have h2 : (lit.1, !lit.2) ∈ toClause lits := by
    rw [← CNF.Clause.mem_literals_iff, literals_toClause, ← hy_eq]
    exact List.mem_map_of_mem (List.mem_of_mem_take hy_take)
  exact ⟨lit.1, lit.2, h1, h2⟩

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
      intro hmem
      have hget := (hinv x).mp hmem
      rw [← h_atom, hun] at hget
      contradiction
    simp only [hnot_in, false_or, Option.some.injEq]
    rcases x with ⟨xa, xp⟩
    dsimp only at h_atom ⊢
    constructor
    · rintro ⟨_, rfl⟩; rfl
    · intro hp
      have hp' : (toLiteral lits[i]).2 = xp := Bool.not_inj hp
      exact Prod.ext h_atom.symm hp'.symm
  · rw [Assignment.get?_insert_of_ne h_atom, ← hinv x]
    have hne_lit : x ≠ toLiteral lits[i] := fun heq => h_atom (congrArg Prod.fst heq).symm
    simp [hne_lit]

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
  have heval_p : (Expr.op .add (.var pvar) (.literal 4)).eval m l =
      some (p + BitVec.ofNat 64 (4 * (i + 1))) := by
    simp [Expr.eval, hpvar, interpBinop, ptr_step_4]
  refine Exec.seq_cps (Exec.set_cps (v := p + BitVec.ofNat 64 (4 * (i + 1))) heval_p ?_)
  let l1 := l.insert pvar (p + BitVec.ofNat 64 (4 * (i + 1)))
  have hpvar1 : (Expr.var pvar).eval m l1 = some (p + BitVec.ofNat 64 (4 * (i + 1))) := by
    simp [l1, Expr.eval]
  have hload := eval_load4_zeroTermGet (Nat.succ_le_of_lt hlt) hpvar1 hsep h32
  exact Exec.set_cps (v := zeroTermGet xs (i + 1)) hload hpost

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
      Or.inl ⟨rfl, 0, Nat.zero_le _, by omega, by omega, by simpa using hl_var, hlit_var, ?_⟩⟩
    intro x; simp
  · rintro rem t' m' l' ⟨checked, trail_end, stat_lit_assigned, assign, trail, trail_free,
      rfl, hchk, hte, hsla, hlocals, hte_eq, hcov, htrail_valid, hlen_sum, hm', hstate⟩
    have hvb : l'["values_begin"]? = some values_begin := by
      rw [hlocals "values_begin" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hvb_var]
    rcases hstate with ⟨rfl, i, hi, rfl, hcap_i, hl_ptr, hlit_cur, hinv_i⟩ | ⟨rfl, rfl, hcap_chk, hlit_zero, htaut⟩
    · refine ⟨zeroTermGet lits i, by simp [Expr.eval, hlit_cur], fun hnz => ?_, fun hz => ?_⟩
      · have hlt : i < lits.length := (zeroTermGet_ne_zero_iff hi hne0).mp hnz
        have hlit_eq : zeroTermGet lits i = lits[i] := by simp [zeroTermGet, hlt]
        rw [hlit_eq] at hlit_cur
        have hlit_valid : IsValidLit max_var lits[i] := hlits_valid lits[i] (List.getElem_mem hlt)
        have hm_bs : m' =⋆ byte1Array values_begin (assignBytes max_var assign) ⋆
            (int4Array trail_begin (trail ++ trail_free) ⋆ (ZeroTermInts literals lits ⋆ R)) := by
          rw [sep_assoc] at hm'; exact hm'
        refine Exec.seq_cps (exec_inline_assigned_literal hlit_cur hvb hlit_valid hm_bs ?_)
        let v := evalAssignedLit (assignByte assign (toLiteral lits[i]).1) lits[i]
        let l1 := (l'.insert "idx" (bvAbs lits[i])).insert "val" v
        have hcases := evalAssignedLit_cases assign hlit_valid
        have hcond1 : (Expr.op .lts (.var "val") (.literal 0)).eval m' l1 =
            some (if v.slt 0 then 1 else 0) := by
          simp [l1, Expr.eval, interpBinop]
        refine Exec.cond_cps hcond1 (fun hnz1 => ?_) (fun hz1 => ?_)
        · have hv_slt : v.slt 0 = true := by cases h : v.slt 0 <;> simp_all
          have hfals : assign.get? (toLiteral lits[i]).1 = some !(toLiteral lits[i]).2 :=
            hcases.1 hv_slt
          have hl1_ptr : l1["l"]? = some (literals + BitVec.ofNat 64 (4 * i)) := by
            simp [l1, hl_ptr]
          have hm_z : m' =⋆ ZeroTermInts literals lits ⋆
              ((byte1Array values_begin (assignBytes max_var assign) ⋆
                int4Array trail_begin (trail ++ trail_free)) ⋆ R) := by
            rw [sep_comm_l] at hm'; exact hm'
          refine exec_advance_zeroTerm hlt hl1_ptr hm_z h32 ?_
          refine ⟨lits.length + 1 - (i + 1),
            ⟨0, trail_end, stat_lit_assigned, assign, trail, trail_free,
              rfl, by simp [hchk], by simp [hte], by simp [hsla], ?_,
              hte_eq, hcov, htrail_valid, hlen_sum, hm',
              Or.inl ⟨rfl, i + 1, Nat.succ_le_of_lt hlt, rfl, by omega, by simp, by simp,
                phase1_step_already_falsified hlt hinv_i hfals⟩⟩,
            show lits.length + 1 - (i + 1) < lits.length + 1 - i by omega⟩
          intro k hkl hklit hkidx hkval hkchk hkte hksla
          simp [Ne.symm hkl, Ne.symm hklit, Ne.symm hkidx, Ne.symm hkval,
            hlocals k hkl hklit hkidx hkval hkchk hkte hksla]
        · have hv_not_slt : v.slt 0 = false := by cases h : v.slt 0 <;> simp_all
          have hcond2 : (Expr.op .lts (.literal 0) (.var "val")).eval m' l1 =
              some (if (0#64).slt v then 1 else 0) := by
            simp [l1, Expr.eval, interpBinop]
          refine Exec.cond_cps hcond2 (fun hnz2 => ?_) (fun hz2 => ?_)
          · have hv_pos : (0#64).slt v = true := by cases h : (0#64).slt v <;> simp_all
            have hsat : assign.get? (toLiteral lits[i]).1 = some (toLiteral lits[i]).2 :=
              hcases.2.1 ⟨hv_not_slt, hv_pos⟩
            refine Exec.seq_cps (Exec.set_cps (v := 1) rfl ?_)
            refine Exec.set_cps (v := 0) rfl ?_
            refine ⟨0, ⟨1, trail_end, stat_lit_assigned, assign, trail, trail_free,
              rfl, by simp, by simp [hte], by simp [hsla], ?_,
              hte_eq, hcov, htrail_valid, hlen_sum, hm',
              Or.inr ⟨rfl, rfl, by omega, by simp, phase1_step_tautology hlt hinv_i hsat⟩⟩,
              show 0 < lits.length + 1 - i by omega⟩
            intro k hkl hklit hkidx hkval hkchk hkte hksla
            simp [Ne.symm hklit, Ne.symm hkchk, Ne.symm hkidx, Ne.symm hkval,
              hlocals k hkl hklit hkidx hkval hkchk hkte hksla]
          · have hv_not_pos : (0#64).slt v = false := by cases h : (0#64).slt v <;> simp_all
            have hun : assign.get? (toLiteral lits[i]).1 = none :=
              (hcases.2.2 ⟨hv_not_slt, hv_not_pos⟩).1
            have htf_pos : 0 < trail_free.length := by omega
            rcases trail_free with _ | ⟨t0, tf'⟩
            · simp at htf_pos
            · have hwlit : IsValidLit max_var (-lits[i]) := isValidLit_neg hlit_valid
              have hvb1 : l1["values_begin"]? = some values_begin := by simp [l1, hvb]
              have hidx1 : l1["idx"]? = some (bvAbs (-lits[i])) := by
                simp [l1, bvAbs_neg hlit_valid]
              have hte1 : l1["trail_end"]? = some trail_end := by simp [l1, hte]
              have hsla1 : l1["stat_lit_assigned"]? = some stat_lit_assigned := by simp [l1, hsla]
              have hlit1 : ∀ m'', (Expr.op .sub (.literal 0) (.var "lit")).eval m'' l1 = some (-lits[i]) := by
                intro m''; exact eval_neg_var (by simp [l1, hlit_cur])
              have hval1 : (Expr.op .or (.op .srs (.op .sub (.literal 0) (.var "lit")) (.literal 63)) (.literal 1)).eval m' l1 =
                  some (bvSignByte (-lits[i])) :=
                eval_sign_byte_expr (hlit1 m')
              refine Exec.seq_cps (exec_inline_assign_literal hvb1 hidx1 hte1 hsla1 hwlit hval1 hlit1
                hte_eq hcov hm' fun m1 hte_next hcov_next hm1 => ?_)
              let l2 := (l1.insert "trail_end" (trail_end + 4)).insert "stat_lit_assigned" (stat_lit_assigned + 1)
              have hl2_ptr : l2["l"]? = some (literals + BitVec.ofNat 64 (4 * i)) := by
                simp [l2, l1, hl_ptr]
              have hm1_z : m1 =⋆ ZeroTermInts literals lits ⋆
                  ((byte1Array values_begin (assignBytes max_var (assign.insert (toLiteral (-lits[i])).1 (toLiteral (-lits[i])).2)) ⋆
                    int4Array trail_begin ((trail ++ [-lits[i]]) ++ tf')) ⋆ R) := by
                rw [sep_comm_l] at hm1; exact hm1
              refine exec_advance_zeroTerm hlt hl2_ptr hm1_z h32 ?_
              refine ⟨lits.length + 1 - (i + 1),
                ⟨0, trail_end + 4, stat_lit_assigned + 1,
                  assign.insert (toLiteral (-lits[i])).1 (toLiteral (-lits[i])).2,
                  trail ++ [-lits[i]], tf',
                  rfl, by simp [hchk], by simp, by simp, ?_,
                  hte_next, hcov_next, ?_, by simp at hlen_sum ⊢; omega, hm1,
                  Or.inl ⟨rfl, i + 1, Nat.succ_le_of_lt hlt, rfl, by simp at hcap_i; omega,
                    by simp, by simp, phase1_step_insert hlt hlit_valid hinv_i hun⟩⟩,
                show lits.length + 1 - (i + 1) < lits.length + 1 - i by omega⟩
              · intro k hkl hklit hkidx hkval hkchk hkte hksla
                simp [Ne.symm hkl, Ne.symm hklit, Ne.symm hkidx, Ne.symm hkval,
                  Ne.symm hkte, Ne.symm hksla, hlocals k hkl hklit hkidx hkval hkchk hkte hksla]
              · intro tlit htlit
                rcases List.mem_append.mp htlit with htlit | htlit
                · exact htrail_valid tlit htlit
                · rw [List.mem_singleton.mp htlit]; exact hwlit
      · have hi_eq : i = lits.length := (zeroTermGet_eq_zero_iff hi hne0).mp hz
        subst hi_eq
        rw [List.take_length] at hinv_i
        have hinv_clause : ∀ x : Literal Nat, x ∈ toClause lits ↔ assign.get? x.1 = some !x.2 := by
          intro x
          rw [← CNF.Clause.mem_literals_iff, literals_toClause, hinv_i x]
        exact hpost m' l' 0 trail_end stat_lit_assigned assign trail trail_free
          hchk hte hsla hlocals hte_eq hcov htrail_valid hlen_sum (by omega) hm' (Or.inl ⟨rfl, hinv_clause⟩)
    · refine ⟨0, by simp [Expr.eval, hlit_zero], fun hnz => False.elim (hnz rfl), fun _ => ?_⟩
      exact hpost m' l' 1 trail_end stat_lit_assigned assign trail trail_free
        hchk hte hsla hlocals hte_eq hcov htrail_valid hlen_sum hcap_chk hm' (Or.inr ⟨rfl, htaut⟩)

/-! ## 6. Loop 2: Antecedent Propagation (`while aid` and `while lit` on `als`) -/

theorem sep_pull_3rd (A B C D : Mem 64 → Prop) :
    (A ⋆ (B ⋆ (C ⋆ D))) = (C ⋆ (A ⋆ (B ⋆ D))) := by
  rw [sep_comm_l B C D, sep_comm_l A C (B ⋆ D)]

theorem sep_pull_4th (A B C D E : Mem 64 → Prop) :
    (A ⋆ (B ⋆ (C ⋆ (D ⋆ E)))) = (D ⋆ (A ⋆ (B ⋆ (C ⋆ E)))) := by
  rw [sep_pull_3rd B C D E, sep_comm_l A D]

theorem phase2_inner_falsified_unit0 {clits : List (BitVec 64)} {curAssign : Assignment} {i : Nat}
    (hlt : i < clits.length)
    (hinv : ∀ x : Literal Nat, x ∈ (clits.take i).map toLiteral → curAssign.get? x.1 = some !x.2)
    (hfals : curAssign.get? (toLiteral clits[i]).1 = some !(toLiteral clits[i]).2) :
    ∀ x : Literal Nat, x ∈ (clits.take (i + 1)).map toLiteral → curAssign.get? x.1 = some !x.2 := by
  rw [List.take_add_one, List.getElem?_eq_getElem hlt, Option.toList_some, List.map_append, List.map_singleton]
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact hinv x hx
  · rw [List.mem_singleton.mp hx]
    exact hfals

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
    rw [heq] at hfals
    rw [hunit_sat] at hfals
    have hpol : (toLiteral unit).2 = !(toLiteral clits[i]).2 := Option.some.inj hfals
    have htolit : toLiteral unit = toLiteral (-clits[i]) := by
      rw [toLiteral_neg hlit]
      exact Prod.ext heq.symm hpol
    exact hne_neg (toLiteral_inj.mp htolit)
  have hfals_cur : curAssign.get? (toLiteral clits[i]).1 = some !(toLiteral clits[i]).2 := by
    rcases hrel with ⟨_, rfl⟩ | rfl
    · rw [Assignment.get?_insert_of_ne (Ne.symm hatom_ne)] at hfals
      exact hfals
    · exact hfals
  rw [List.take_add_one, List.getElem?_eq_getElem hlt, Option.toList_some, List.map_append, List.map_singleton]
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact hinv x hx
  · rw [List.mem_singleton.mp hx]
    exact Or.inr hfals_cur

theorem phase2_inner_new_unit {clits : List (BitVec 64)} {curAssign : Assignment} {i : Nat}
    (hlt : i < clits.length)
    (hinv : ∀ x : Literal Nat, x ∈ (clits.take i).map toLiteral → curAssign.get? x.1 = some !x.2) :
    ∀ x : Literal Nat, x ∈ (clits.take (i + 1)).map toLiteral →
      x = toLiteral clits[i] ∨ curAssign.get? x.1 = some !x.2 := by
  rw [List.take_add_one, List.getElem?_eq_getElem hlt, Option.toList_some, List.map_append, List.map_singleton]
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact Or.inr (hinv x hx)
  · exact Or.inl (List.mem_singleton.mp hx)

theorem phase2_inner_dup_unit {clits : List (BitVec 64)} {curAssign : Assignment}
    {unit : BitVec 64} {i : Nat}
    (hlt : i < clits.length)
    (heq : unit = clits[i])
    (hinv : ∀ x : Literal Nat, x ∈ (clits.take i).map toLiteral →
      x = toLiteral unit ∨ curAssign.get? x.1 = some !x.2) :
    ∀ x : Literal Nat, x ∈ (clits.take (i + 1)).map toLiteral →
      x = toLiteral unit ∨ curAssign.get? x.1 = some !x.2 := by
  rw [List.take_add_one, List.getElem?_eq_getElem hlt, Option.toList_some, List.map_append, List.map_singleton]
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact hinv x hx
  · rw [List.mem_singleton.mp hx, ← heq]
    exact Or.inl rfl

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
    have hst : l'["st"]? = some st := by
      rw [hlocals "st" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hst_var]
    have hid : l'["id"]? = some id := by
      rw [hlocals "id" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hid_var]
    have haid : l'["aid"]? = some aid := by
      rw [hlocals "aid" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), haid_var]
    have hvb : l'["values_begin"]? = some values_begin := by
      rw [hlocals "values_begin" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hvb_var]
    have hsr : l'["stat_resolved"]? = some stat_resolved := by
      rw [hlocals "stat_resolved" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hsr_var]
    refine ⟨zeroTermGet clits i, by simp [Expr.eval, hlit_cur], fun hnz => ?_, fun hz => ?_⟩
    · have hlt : i < clits.length := (zeroTermGet_ne_zero_iff hi hne0).mp hnz
      have hlit_eq : zeroTermGet clits i = clits[i] := by simp [zeroTermGet, hlt]
      rw [hlit_eq] at hlit_cur
      have hlit_valid : IsValidLit max_var clits[i] := hclits_valid clits[i] (List.getElem_mem hlt)
      have hm_bs : m' =⋆ byte1Array values_begin (assignBytes max_var assign) ⋆
          (int4Array trail_begin (trail ++ trail_free) ⋆ (ZeroTermInts als clits ⋆ (kernelState st k ⋆ R))) := by
        rw [sep_assoc] at hm'; exact hm'
      refine Exec.seq_cps (exec_inline_assigned_literal hlit_cur hvb hlit_valid hm_bs ?_)
      let v := evalAssignedLit (assignByte assign (toLiteral clits[i]).1) clits[i]
      let l1 := (l'.insert "idx" (bvAbs clits[i])).insert "val" v
      have hcases := evalAssignedLit_cases assign hlit_valid
      have hm_ks : m' =⋆ kernelState st k ⋆
          ((byte1Array values_begin (assignBytes max_var assign) ⋆ int4Array trail_begin (trail ++ trail_free)) ⋆
           (ZeroTermInts als clits ⋆ R)) := by
        rw [sep_pull_3rd] at hm'; exact hm'
      have hcond1 : (Expr.op .lts (.var "val") (.literal 0)).eval m' l1 =
          some (if v.slt 0 then 1 else 0) := by
        simp [l1, Expr.eval, interpBinop]
      refine Exec.seq_cps (c1 := .cond _ _ _) ?_
      refine Exec.cond_cps hcond1 (fun hnz1 => ?_) (fun hz1 => ?_)
      · have hv_slt : v.slt 0 = true := by cases h : v.slt 0 <;> simp_all
        have hfals : assign.get? (toLiteral clits[i]).1 = some !(toLiteral clits[i]).2 :=
          hcases.1 hv_slt
        have hcond_neg : (Expr.op .eq (.var "unit") (.op .sub (.literal 0) (.var "lit"))).eval m' l1 =
            some (if unit = -clits[i] then 1 else 0) := by
          simp [l1, Expr.eval, hunit_cur, hlit_cur, interpBinop]
        refine Exec.cond_cps hcond_neg (fun hnz_neg => ?_) (fun hz_neg => ?_)
        · refine exec_flush_and_fail (trail_end := trail_end) (stat_resolved := stat_resolved)
            (stat_lit_assigned := stat_lit_assigned) (args := [2, id, aid, 0, 0])
            (by simp [hst]) (by simp [hte]) (by simp [hsr]) (by simp [hsla]) hm_ks (fun m'' => ?_)
          simp [evalArgs, Expr.eval, hid, haid]
        · have hne_neg : unit ≠ -clits[i] := by split at hz_neg <;> simp_all
          refine .skip _ _ _ _ _ ?_
          have hl1_ptr : l1["l"]? = some (als + BitVec.ofNat 64 (4 * i)) := by simp [l1, hl_ptr]
          have hm_z : m' =⋆ ZeroTermInts als clits ⋆
              ((byte1Array values_begin (assignBytes max_var assign) ⋆
                int4Array trail_begin (trail ++ trail_free)) ⋆ (kernelState st k ⋆ R)) := by
            rw [sep_comm_l] at hm'; exact hm'
          refine exec_advance_zeroTerm hlt hl1_ptr hm_z h32 ?_
          refine ⟨clits.length - (i + 1),
            ⟨i + 1, unit, trail_end, stat_lit_assigned, assign, trail, trail_free,
              Nat.succ_le_of_lt hlt, rfl, rfl, by simp, by simp, by simp [hunit_cur],
              by simp [hte], by simp [hsla], ?_, hte_eq, hcov, htrail_valid, hlen_sum, hm', ?_⟩,
            show clits.length - (i + 1) < clits.length - i by omega⟩
          · intro vname hkl hklit hkidx hkval hkunit hkte hksla
            simp [Ne.symm hkl, Ne.symm hklit, Ne.symm hkidx, Ne.symm hkval,
              hlocals vname hkl hklit hkidx hkval hkunit hkte hksla]
          · rcases hstate with ⟨rfl, hassign_eq, hcap_i, hinv_i⟩ | ⟨hunit_nz, hunit_val, hunit_sat, hcap_i, hrel, hinv_i⟩
            · subst hassign_eq
              exact Or.inl ⟨rfl, rfl, hcap_i, phase2_inner_falsified_unit0 hlt hinv_i hfals⟩
            · exact Or.inr ⟨hunit_nz, hunit_val, hunit_sat, hcap_i, hrel,
                phase2_inner_falsified_unit_ne0 hlt hlit_valid hunit_sat hrel hinv_i hfals hne_neg⟩
      · have hv_not_slt : v.slt 0 = false := by cases h : v.slt 0 <;> simp_all
        rcases hstate with ⟨rfl, hassign_eq, hcap_i, hinv_i⟩ | ⟨hunit_nz, hunit_val, hunit_sat, hcap_i, hrel, hinv_i⟩
        · -- Case unit = 0
          subst hassign_eq
          have hcond_unit0 : (Expr.var "unit").eval m' l1 = some 0 := by
            simp [l1, Expr.eval, hunit_cur]
          refine Exec.seq_cps (Exec.cond_cps hcond_unit0 (fun hnz_u => False.elim (hnz_u rfl)) (fun _ => .skip _ _ _ _ _ ?_))
          refine Exec.seq_cps (Exec.set_cps (v := clits[i]) (by simp [Expr.eval, hlit_cur]) ?_)
          let l2 := l1.insert "unit" clits[i]
          have hcond_val0 : (Expr.op .eq (.var "val") (.literal 0)).eval m' l2 =
              some (if v = 0 then 1 else 0) := by
            simp [l2, l1, Expr.eval, interpBinop]
          refine Exec.cond_cps hcond_val0 (fun hnz_v0 => ?_) (fun hz_v0 => ?_)
          · have hv0 : v = 0 := by split at hnz_v0 <;> simp_all
            have hv_not_pos : (0#64).slt v = false := by rw [hv0]; decide
            have hun : assign.get? (toLiteral clits[i]).1 = none :=
              (hcases.2.2 ⟨hv_not_slt, hv_not_pos⟩).1
            have htf_pos : 0 < trail_free.length := by omega
            rcases trail_free with _ | ⟨t0, tf'⟩
            · simp at htf_pos
            · have hvb2 : l2["values_begin"]? = some values_begin := by simp [l2, l1, hvb]
              have hidx2 : l2["idx"]? = some (bvAbs clits[i]) := by simp [l2, l1]
              have hte2 : l2["trail_end"]? = some trail_end := by simp [l2, l1, hte]
              have hsla2 : l2["stat_lit_assigned"]? = some stat_lit_assigned := by simp [l2, l1, hsla]
              have hlit2 : ∀ m'', (Expr.var "lit").eval m'' l2 = some clits[i] := by
                intro m''; simp [l2, l1, Expr.eval, hlit_cur]
              have hval2 : (Expr.op .or (.op .srs (.var "lit") (.literal 63)) (.literal 1)).eval m' l2 =
                  some (bvSignByte clits[i]) :=
                eval_sign_byte_expr (hlit2 m')
              refine exec_inline_assign_literal hvb2 hidx2 hte2 hsla2 hlit_valid hval2 hlit2
                hte_eq hcov hm' (fun m1 hte_next hcov_next hm1 => ?_)
              let l3 := (l2.insert "trail_end" (trail_end + 4)).insert "stat_lit_assigned" (stat_lit_assigned + 1)
              have hl3_ptr : l3["l"]? = some (als + BitVec.ofNat 64 (4 * i)) := by simp [l3, l2, l1, hl_ptr]
              have hm1_z : m1 =⋆ ZeroTermInts als clits ⋆
                  ((byte1Array values_begin (assignBytes max_var (assign.insert (toLiteral clits[i]).1 (toLiteral clits[i]).2)) ⋆
                    int4Array trail_begin ((trail ++ [clits[i]]) ++ tf')) ⋆ (kernelState st k ⋆ R)) := by
                rw [sep_comm_l] at hm1; exact hm1
              refine exec_advance_zeroTerm hlt hl3_ptr hm1_z h32 ?_
              refine ⟨clits.length - (i + 1),
                ⟨i + 1, clits[i], trail_end + 4, stat_lit_assigned + 1,
                  assign.insert (toLiteral clits[i]).1 (toLiteral clits[i]).2,
                  trail ++ [clits[i]], tf',
                  Nat.succ_le_of_lt hlt, rfl, rfl, by simp, by simp, by simp,
                  by simp, by simp, ?_, hte_next, hcov_next, ?_,
                  by simp at hlen_sum ⊢; omega, hm1,
                  Or.inr ⟨hlit_valid.2.1, hlit_valid, Assignment.get?_insert_of_eq rfl,
                    by simp at hcap_i; omega, Or.inl ⟨hun, rfl⟩,
                    phase2_inner_new_unit hlt hinv_i⟩⟩,
                show clits.length - (i + 1) < clits.length - i by omega⟩
              · intro vname hkl hklit hkidx hkval hkunit hkte hksla
                simp [Ne.symm hkl, Ne.symm hklit, Ne.symm hkidx, Ne.symm hkval,
                  Ne.symm hkunit, Ne.symm hkte, Ne.symm hksla,
                  hlocals vname hkl hklit hkidx hkval hkunit hkte hksla]
              · intro tlit htlit
                rcases List.mem_append.mp htlit with htlit | htlit
                · exact htrail_valid tlit htlit
                · rw [List.mem_singleton.mp htlit]; exact hlit_valid
          · have hv_ne0 : v ≠ 0 := by split at hz_v0 <;> simp_all
            have hv_pos : (0#64).slt v = true := by
              cases hp : (0#64).slt v
              · exact False.elim (hv_ne0 (hcases.2.2 ⟨hv_not_slt, hp⟩).2)
              · rfl
            have hsat : assign.get? (toLiteral clits[i]).1 = some (toLiteral clits[i]).2 :=
              hcases.2.1 ⟨hv_not_slt, hv_pos⟩
            refine .skip _ _ _ _ _ ?_
            have hl2_ptr : l2["l"]? = some (als + BitVec.ofNat 64 (4 * i)) := by simp [l2, l1, hl_ptr]
            have hm_z : m' =⋆ ZeroTermInts als clits ⋆
                ((byte1Array values_begin (assignBytes max_var assign) ⋆
                  int4Array trail_begin (trail ++ trail_free)) ⋆ (kernelState st k ⋆ R)) := by
              rw [sep_comm_l] at hm'; exact hm'
            refine exec_advance_zeroTerm hlt hl2_ptr hm_z h32 ?_
            refine ⟨clits.length - (i + 1),
              ⟨i + 1, clits[i], trail_end, stat_lit_assigned, assign, trail, trail_free,
                Nat.succ_le_of_lt hlt, rfl, rfl, by simp, by simp, by simp,
                by simp [hte], by simp [hsla], ?_, hte_eq, hcov, htrail_valid,
                hlen_sum, hm',
                Or.inr ⟨hlit_valid.2.1, hlit_valid, hsat, by omega, Or.inr rfl,
                  phase2_inner_new_unit hlt hinv_i⟩⟩,
              show clits.length - (i + 1) < clits.length - i by omega⟩
            intro vname hkl hklit hkidx hkval hkunit hkte hksla
            simp [Ne.symm hkl, Ne.symm hklit, Ne.symm hkidx, Ne.symm hkval, Ne.symm hkunit,
              hlocals vname hkl hklit hkidx hkval hkunit hkte hksla]
        · -- Case unit ≠ 0
          have hcond_unit_nz : (Expr.var "unit").eval m' l1 = some unit := by
            simp [l1, Expr.eval, hunit_cur]
          refine Exec.seq_cps (Exec.cond_cps hcond_unit_nz (fun _ => ?_) (fun hz_u => False.elim (hunit_nz hz_u)))
          have hcond_eq : (Expr.op .eq (.op .eq (.var "unit") (.var "lit")) (.literal 0)).eval m' l1 =
              some (if unit = clits[i] then 0 else 1) := by
            simp [l1, Expr.eval, hunit_cur, hlit_cur, interpBinop]
          refine Exec.cond_cps hcond_eq (fun hnz_eq => ?_) (fun hz_eq => ?_)
          · refine exec_flush_and_fail (trail_end := trail_end) (stat_resolved := stat_resolved)
              (stat_lit_assigned := stat_lit_assigned) (args := [2, id, aid, 0, 0])
              (by simp [hst]) (by simp [hte]) (by simp [hsr]) (by simp [hsla]) hm_ks (fun m'' => ?_)
            simp [evalArgs, Expr.eval, hid, haid]
          · have heq_unit : unit = clits[i] := by split at hz_eq <;> simp_all
            refine .skip _ _ _ _ _ ?_
            refine Exec.seq_cps (Exec.set_cps (v := clits[i]) (by simp [Expr.eval, hlit_cur]) ?_)
            let l2 := l1.insert "unit" clits[i]
            have hcond_val0 : (Expr.op .eq (.var "val") (.literal 0)).eval m' l2 =
                some (if v = 0 then 1 else 0) := by
              simp [l2, l1, Expr.eval, interpBinop]
            refine Exec.cond_cps hcond_val0 (fun hnz_v0 => ?_) (fun _ => ?_)
            · have hv0 : v = 0 := by split at hnz_v0 <;> simp_all
              have hv_not_pos : (0#64).slt v = false := by rw [hv0]; decide
              have hun : assign.get? (toLiteral clits[i]).1 = none :=
                (hcases.2.2 ⟨hv_not_slt, hv_not_pos⟩).1
              rw [← heq_unit, hunit_sat] at hun
              nomatch hun
            · refine .skip _ _ _ _ _ ?_
              have hl2_ptr : l2["l"]? = some (als + BitVec.ofNat 64 (4 * i)) := by simp [l2, l1, hl_ptr]
              have hm_z : m' =⋆ ZeroTermInts als clits ⋆
                  ((byte1Array values_begin (assignBytes max_var assign) ⋆
                    int4Array trail_begin (trail ++ trail_free)) ⋆ (kernelState st k ⋆ R)) := by
                rw [sep_comm_l] at hm'; exact hm'
              refine exec_advance_zeroTerm hlt hl2_ptr hm_z h32 ?_
              refine ⟨clits.length - (i + 1),
                ⟨i + 1, clits[i], trail_end, stat_lit_assigned, assign, trail, trail_free,
                  Nat.succ_le_of_lt hlt, rfl, rfl, by simp, by simp, by simp,
                  by simp [hte], by simp [hsla], ?_, hte_eq, hcov, htrail_valid,
                  hlen_sum, hm',
                  Or.inr ⟨hlit_valid.2.1, hlit_valid, by rwa [← heq_unit], hcap_i,
                    by rwa [← heq_unit], by rw [← heq_unit]; exact phase2_inner_dup_unit hlt heq_unit hinv_i⟩⟩,
                show clits.length - (i + 1) < clits.length - i by omega⟩
              intro vname hkl hklit hkidx hkval hkunit hkte hksla
              simp [Ne.symm hkl, Ne.symm hklit, Ne.symm hkidx, Ne.symm hkval, Ne.symm hkunit,
                hlocals vname hkl hklit hkidx hkval hkunit hkte hksla]
    · have hi_eq : i = clits.length := (zeroTermGet_eq_zero_iff hi hne0).mp hz
      subst hi_eq
      rw [List.take_length] at hstate
      rcases hstate with ⟨rfl, hassign_eq, hcap_i, hinv_all⟩ | ⟨hunit_nz, _, _, hcap_i, hrel, hinv_unit⟩
      · subst hassign_eq
        have hall_cl : ∀ x : Literal Nat, x ∈ toClause clits → assign.get? x.1 = some !x.2 := by
          intro x hx
          rw [← CNF.Clause.mem_literals_iff, literals_toClause] at hx
          exact hinv_all x hx
        have hunsat : CNF.Unsat (f ++ initAssign.toCNF) := unsat_of_all_falsified hcl_mem hent hall_cl
        exact hpost m' l' 0 trail_end stat_lit_assigned assign trail trail_free
          hunit_cur hte hsla hlocals hte_eq hcov htrail_valid hlen_sum hm'
          (Or.inl ⟨rfl, hcap_i, hunsat⟩)
      · have hunit_cl : ∀ x : Literal Nat, x ∈ toClause clits →
            x = toLiteral unit ∨ curAssign.get? x.1 = some !x.2 := by
          intro x hx
          rw [← CNF.Clause.mem_literals_iff, literals_toClause] at hx
          exact hinv_unit x hx
        have hent' : CNF.Entails (f ++ initAssign.toCNF) (f ++ assign.toCNF) := by
          rcases hrel with ⟨_, rfl⟩ | rfl
          · exact entails_insert_of_unit_prop hcl_mem hent hunit_cl
          · exact hent
        exact hpost m' l' unit trail_end stat_lit_assigned assign trail trail_free
          hunit_cur hte hsla hlocals hte_eq hcov htrail_valid hlen_sum hm'
          (Or.inr ⟨hunit_nz, hcap_i, hent'⟩)

@[simp] theorem shamt_3_mul_8 (aid : BitVec 64) :
    aid <<< shamt 3#64 = BitVec.ofNat 64 (8 * aid.toNat) := by
  have h1 : shamt 3#64 = 3 := by decide
  have h2 : BitVec.ofNat 64 (8 * aid.toNat) = 8#64 * aid := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_mul]
  rw [h1, h2]
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
        have haid_eq : zeroTermGet aids j = aids[j] := by simp [zeroTermGet, hlt]
        rw [haid_eq] at haid_cur
        have haid_mem : aids[j] ∈ aids := List.getElem_mem hlt
        have haid_val := haids_valid aids[j] haid_mem
        have hm_ks : m' =⋆ kernelState st k ⋆
            ((byte1Array values_begin (assignBytes max_var assign) ⋆ int4Array trail_begin (trail ++ trail_free)) ⋆ P_ro) := by
          rw [sep_comm_l] at hm'; exact hm'
        have hcond_neg : (Expr.op .lts (.var "aid") (.literal 0)).eval m' l' =
            some (if aids[j].slt 0 then 1 else 0) := by
          simp [Expr.eval, haid_cur, interpBinop]
        refine Exec.seq_cps (c1 := .cond _ _ .skip) ?_
        refine Exec.cond_cps hcond_neg (fun hnz_neg => ?_) (fun hz_neg => ?_)
        · refine exec_flush_and_fail (trail_end := trail_end) (stat_resolved := stat_resolved)
            (stat_lit_assigned := stat_lit_assigned) (args := [1, id, aids[j], 0, 0])
            hst hte hsr hsla hm_ks (fun m'' => ?_)
          simp [evalArgs, Expr.eval, hid, haid_cur]
        · have hnot_slt : aids[j].slt 0 = false := by cases h : aids[j].slt 0 <;> simp_all
          refine .skip _ _ _ _ _ ?_
          obtain ⟨haid_lt_ptrs, hptr_ne0⟩ := haid_val.2.2 hnot_slt
          have haid_pos : 0 < aids[j].toNat :=
            Nat.pos_of_ne_zero (fun h0 => haid_val.2.1 (BitVec.eq_of_toNat_eq h0))
          have hm_pro : m' =⋆ P_ro ⋆
              ((byte1Array values_begin (assignBytes max_var assign) ⋆ int4Array trail_begin (trail ++ trail_free)) ⋆
               kernelState st k) := by
            have h := hm'
            rw [sep_comm (kernelState st k) P_ro, sep_comm_l] at h
            exact h
          have hals_eval : (Expr.load .eight (.op .add (.var "literals_begin") (.op .slu (.var "aid") (.literal 3)))).eval m' l' =
              some lit_ptrs[aids[j].toNat] := by
            refine hct.eval_load_ptr hm_pro haid_lt_ptrs ?_
            simp [Expr.eval, hlb, haid_cur, interpBinop]
          refine Exec.seq_cps (Exec.set_cps hals_eval ?_)
          refine Exec.seq_cps (Exec.set_cps (v := stat_resolved + 1) (by simp [Expr.eval, hsr, interpBinop]) ?_)
          refine Exec.seq_cps (Exec.set_cps (v := 0) rfl ?_)
          refine Exec.seq_cps (Exec.set_cps (v := lit_ptrs[aids[j].toNat]) (by simp [Expr.eval]) ?_)
          let l1 := (((l'.insert "als" lit_ptrs[aids[j].toNat]).insert "stat_resolved" (stat_resolved + 1)).insert "unit" 0).insert "l" lit_ptrs[aids[j].toNat]
          obtain ⟨clits, R1, hP, hclits_valid, hcl_lookup⟩ :=
            hct.2 aids[j].toNat haid_lt_ptrs haid_pos hptr_ne0
          have hcl_mem : toClause clits ∈ s.toCNF := mem_toCNF_of_formula_getElem? hcl_lookup
          have hm_inner : m' =⋆ (byte1Array values_begin (assignBytes max_var assign) ⋆
              int4Array trail_begin (trail ++ trail_free)) ⋆
            (ZeroTermInts lit_ptrs[aids[j].toNat] clits ⋆ (kernelState st k ⋆ R1)) := by
            have h := hm'
            rw [hP, sep_comm_l (kernelState st k) (ZeroTermInts lit_ptrs[aids[j].toNat] clits) R1] at h
            exact h
          have hm_clits_front : m' =⋆ ZeroTermInts lit_ptrs[aids[j].toNat] clits ⋆
              ((byte1Array values_begin (assignBytes max_var assign) ⋆ int4Array trail_begin (trail ++ trail_free)) ⋆
               (kernelState st k ⋆ R1)) := by
            rw [sep_comm_l] at hm_inner; exact hm_inner
          have hlit0_eval : (Expr.op .srs (.op .slu (.load .four (.var "l")) (.literal 32)) (.literal 32)).eval m' l1 =
              some (zeroTermGet clits 0) := by
            refine eval_load4_zeroTermGet (Nat.zero_le _) ?_ hm_clits_front (fun x hx => (hclits_valid x hx).1)
            simp [l1, Expr.eval]
          refine Exec.seq_cps (Exec.set_cps hlit0_eval ?_)
          let l2 := l1.insert "lit" (zeroTermGet clits 0)
          have hcap_inner : (aids.length - (j + 1)) + 1 ≤ trail_free.length := by omega
          refine Exec.seq_cps (exec_rup_phase2_inner_loop (reserve := aids.length - (j + 1))
            (id := id) (aid := aids[j]) (stat_resolved := stat_resolved + 1)
            (stat_lit_assigned0 := stat_lit_assigned)
            hclits_valid hcl_mem hent_j hcap_inner
            (by simp [hst]) (by simp [hid]) (by simp [haid_cur])
            (by simp [hvb]) (by simp [hte]) (by simp)
            (by simp [hsla]) (by simp) (by simp) (by simp)
            hte_eq hcov htrail_valid hm_inner ?_)
          intro m_mid l_mid unit trail_end' stat_lit_assigned' assign' trail' trail_free'
            hunit_mid hte_mid hsla_mid hlocals_mid hte_eq' hcov' htrail_valid' hlen_sum' hm_mid hres_mid
          have hm_restored : m_mid =⋆ (byte1Array values_begin (assignBytes max_var assign') ⋆
              int4Array trail_begin (trail' ++ trail_free')) ⋆
            (kernelState st k ⋆ P_ro) := by
            have h := hm_mid
            rw [sep_comm_l (ZeroTermInts lit_ptrs[aids[j].toNat] clits) (kernelState st k) R1, ← hP] at h
            exact h
          have hst_mid : l_mid["st"]? = some st := by
            rw [hlocals_mid "st" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
            simp [hst]
          have hid_mid : l_mid["id"]? = some id := by
            rw [hlocals_mid "id" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
            simp [hid]
          have hlb_mid : l_mid["literals_begin"]? = some literals_begin := by
            rw [hlocals_mid "literals_begin" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
            simp [hlb]
          have hvb_mid : l_mid["values_begin"]? = some values_begin := by
            rw [hlocals_mid "values_begin" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
            simp [hvb]
          have htb_mid : l_mid["trail_begin"]? = some trail_begin := by
            rw [hlocals_mid "trail_begin" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
            simp [htb]
          have hchk_mid : l_mid["checked"]? = some 0 := by
            rw [hlocals_mid "checked" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
            simp [hchk]
          have hsr_mid : l_mid["stat_resolved"]? = some (stat_resolved + 1) := by
            rw [hlocals_mid "stat_resolved" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
            simp
          have ha_mid : l_mid["a"]? = some (antecedents + BitVec.ofNat 64 (4 * j)) := by
            rw [hlocals_mid "a" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
            simp [ha_ptr]
          have hcond_u0 : (Expr.op .eq (.var "unit") (.literal 0)).eval m_mid l_mid =
              some (if unit = 0 then 1 else 0) := by
            simp [Expr.eval, hunit_mid, interpBinop]
          refine Exec.cond_cps hcond_u0 (fun hnz_u0 => ?_) (fun hz_u0 => ?_)
          · have hu0 : unit = 0 := by split at hnz_u0 <;> simp_all
            rcases hres_mid with ⟨_, _, hunsat⟩ | ⟨hunit_nz, _, _⟩
            · refine Exec.seq_cps (Exec.set_cps (v := 1) rfl ?_)
              refine Exec.set_cps (v := 0) rfl ?_
              refine ⟨0, ⟨1, trail_end', stat_resolved + 1, stat_lit_assigned', assign', trail', trail_free',
                rfl, by simp [hst_mid], by simp [hid_mid], by simp [hlb_mid], by simp [hvb_mid],
                by simp [htb_mid], by simp, by simp [hte_mid], by simp [hsr_mid], by simp [hsla_mid],
                hte_eq', hcov', htrail_valid', hlen_sum'.trans hlen_sum, hm_restored,
                Or.inr ⟨rfl, rfl, by simp, hunsat⟩⟩,
                show 0 < aids.length + 1 - j by omega⟩
            · exact False.elim (hunit_nz hu0)
          · have hu_ne0 : unit ≠ 0 := by split at hz_u0 <;> simp_all
            rcases hres_mid with ⟨hu0, _, _⟩ | ⟨_, hcap_next, hent_next⟩
            · exact False.elim (hu_ne0 hu0)
            · have hm_aids : m_mid =⋆ ZeroTermInts antecedents aids ⋆
                  ((byte1Array values_begin (assignBytes max_var assign') ⋆
                    int4Array trail_begin (trail' ++ trail_free')) ⋆
                   (kernelState st k ⋆ R_aids)) := by
                have h := hm_restored
                rw [hP_aids, sep_pull_3rd] at h
                exact h
              refine exec_advance_zeroTerm hlt ha_mid hm_aids haids_32 ?_
              refine ⟨aids.length + 1 - (j + 1),
                ⟨0, trail_end', stat_resolved + 1, stat_lit_assigned', assign', trail', trail_free',
                  rfl, by simp [hst_mid], by simp [hid_mid], by simp [hlb_mid], by simp [hvb_mid],
                  by simp [htb_mid], by simp [hchk_mid], by simp [hte_mid], by simp [hsr_mid],
                  by simp [hsla_mid], hte_eq', hcov', htrail_valid', hlen_sum'.trans hlen_sum,
                  hm_restored,
                  Or.inl ⟨rfl, j + 1, Nat.succ_le_of_lt hlt, rfl, hcap_next, by simp, by simp, hent_next⟩⟩,
                show aids.length + 1 - (j + 1) < aids.length + 1 - j by omega⟩
      · exact hpost m' l' 0 trail_end stat_resolved stat_lit_assigned assign trail trail_free
          hst hid hvb htb hchk hte hsr hsla hte_eq hcov htrail_valid hlen_sum hm' (Or.inl rfl)
    · refine ⟨0, by simp [Expr.eval, haid_zero], fun hnz => False.elim (hnz rfl), fun _ => ?_⟩
      exact hpost m' l' 1 trail_end stat_resolved stat_lit_assigned assign trail trail_free
        hst hid hvb htb hchk hte hsr hsla hte_eq hcov htrail_valid hlen_sum hm' (Or.inr ⟨rfl, hunsat⟩)

/-! ## 7. Main Theorem: `br_check_clause_non_strictly_by_propagation` -/

theorem eval_load_kernelField {m : Mem 64} {l : Locals 64} {ea : Expr}
    {st : BitVec 64} {k : KernelFields} {R : Mem 64 → Prop}
    (i : Nat) (hi : i < 20)
    (ha : ea.eval m l = some (st + BitVec.ofNat 64 (8 * i)))
    (hsep : m =⋆ kernelState st k ⋆ R) :
    (Expr.load .eight ea).eval m l = some (k.toList[i]'(by simpa [KernelFields.toList] using hi)) :=
  eval_load_word8Array_elem (by simpa [KernelFields.toList] using hi) ha hsep

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
  have hst1 : l1["st"]? = some st := by
    rw [hlocals1 "st" (by decide) (by decide) (by decide) (by decide), hst]
  have hsr1 : l1["stat_resolved"]? = some stat_resolved := by
    rw [hlocals1 "stat_resolved" (by decide) (by decide) (by decide) (by decide), hsr]
  have hsla1 : l1["stat_lit_assigned"]? = some stat_lit_assigned := by
    rw [hlocals1 "stat_lit_assigned" (by decide) (by decide) (by decide) (by decide), hsla]
  have hm1_ks : m1 =⋆ kernelState st k ⋆
      ((byte1Array k.values_begin (assignBytes max_var Assignment.empty) ⋆
        int4Array k.trail_begin (trail ++ trail_free)) ⋆ P_ro) := by
    rw [sep_comm_l] at hm1; exact hm1
  refine exec_flush_prop_state hst1 hte1 hsr1 hsla1 hm1_ks fun m2 hm2 => ?_
  rw [sep_comm_l] at hm2
  exact hpost m2 l1 hm2

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
  have hm_ks : m =⋆ kernelState st k ⋆
      ((byte1Array k.values_begin (assignBytes max_var Assignment.empty) ⋆
        int4Array k.trail_begin trail_free0) ⋆ P_ro) := by
    rw [sep_comm_l] at hsep; exact hsep
  -- 1. literals_begin = load8(st + 16)
  have hload_lb : (Expr.load .eight (.op .add (.var "st") (.literal 16))).eval m l = some k.literals_begin :=
    eval_load_kernelField 2 (by decide) (by simp [Expr.eval, hst_var, interpBinop]) hm_ks
  refine Exec.seq_cps (Exec.set_cps hload_lb ?_)
  -- 2. values_begin = load8(st + 24)
  have hload_vb : (Expr.load .eight (.op .add (.var "st") (.literal 24))).eval m (l.insert "literals_begin" k.literals_begin) = some k.values_begin :=
    eval_load_kernelField 3 (by decide) (by simp [Expr.eval, hst_var, interpBinop]) hm_ks
  refine Exec.seq_cps (Exec.set_cps hload_vb ?_)
  -- 3. trail_begin = load8(st + 40)
  have hload_tb : (Expr.load .eight (.op .add (.var "st") (.literal 40))).eval m
      ((l.insert "literals_begin" k.literals_begin).insert "values_begin" k.values_begin) = some k.trail_begin :=
    eval_load_kernelField 5 (by decide) (by simp [Expr.eval, hst_var, interpBinop]) hm_ks
  refine Exec.seq_cps (Exec.set_cps hload_tb ?_)
  -- 4. trail_end = load8(st + 48)
  have hload_te : (Expr.load .eight (.op .add (.var "st") (.literal 48))).eval m
      (((l.insert "literals_begin" k.literals_begin).insert "values_begin" k.values_begin).insert "trail_begin" k.trail_begin) = some k.trail_begin := by
    rw [← hk_trail]
    exact eval_load_kernelField 6 (by decide) (by simp [Expr.eval, hst_var, interpBinop]) hm_ks
  refine Exec.seq_cps (Exec.set_cps hload_te ?_)
  -- 5. stat_resolved = load8(st + 144) + 1
  have hload_sr : (Expr.op .add (.load .eight (.op .add (.var "st") (.literal 144))) (.literal 1)).eval m
      ((((l.insert "literals_begin" k.literals_begin).insert "values_begin" k.values_begin).insert "trail_begin" k.trail_begin).insert "trail_end" k.trail_begin) =
      some (k.stat_resolved + 1) := by
    have h18 := eval_load_kernelField 18 (by decide)
      (l := ((((l.insert "literals_begin" k.literals_begin).insert "values_begin" k.values_begin).insert "trail_begin" k.trail_begin).insert "trail_end" k.trail_begin))
      (ea := .op .add (.var "st") (.literal 144))
      (by simp [Expr.eval, hst_var, interpBinop]) hm_ks
    rw [Expr.eval, h18]; rfl
  refine Exec.seq_cps (Exec.set_cps hload_sr ?_)
  -- 6. stat_lit_assigned = load8(st + 152)
  have hload_sla : (Expr.load .eight (.op .add (.var "st") (.literal 152))).eval m
      (((((l.insert "literals_begin" k.literals_begin).insert "values_begin" k.values_begin).insert "trail_begin" k.trail_begin).insert "trail_end" k.trail_begin).insert "stat_resolved" (k.stat_resolved + 1)) =
      some k.stat_lit_assigned :=
    eval_load_kernelField 19 (by decide) (by simp [Expr.eval, hst_var, interpBinop]) hm_ks
  refine Exec.seq_cps (Exec.set_cps hload_sla ?_)
  -- 7. checked = 0; l = literals
  refine Exec.seq_cps (Exec.set_cps (v := 0) rfl ?_)
  refine Exec.seq_cps (Exec.set_cps (v := literals) (by simp [Expr.eval, hlits_var]) ?_)
  -- 8. lit = (load4(l) << 32) .>> 32
  obtain ⟨R_lits, hP_lits⟩ := hlits_ro
  have hm_lits_front : m =⋆ ZeroTermInts literals lits ⋆
      ((byte1Array k.values_begin (assignBytes max_var Assignment.empty) ⋆
        int4Array k.trail_begin trail_free0) ⋆ (kernelState st k ⋆ R_lits)) := by
    have h := hsep
    rw [hP_lits, sep_pull_3rd] at h
    exact h
  have hload_lit0 : (Expr.op .srs (.op .slu (.load .four (.var "l")) (.literal 32)) (.literal 32)).eval m
      ((((((((l.insert "literals_begin" k.literals_begin).insert "values_begin" k.values_begin).insert "trail_begin" k.trail_begin).insert "trail_end" k.trail_begin).insert "stat_resolved" (k.stat_resolved + 1)).insert "stat_lit_assigned" k.stat_lit_assigned).insert "checked" 0).insert "l" literals) =
      some (zeroTermGet lits 0) :=
    eval_load4_zeroTermGet (Nat.zero_le _) (by simp [Expr.eval]) hm_lits_front (fun x hx => (hlits_valid x hx).1)
  refine Exec.seq_cps (Exec.set_cps hload_lit0 ?_)
  -- 9. Phase 1 loop
  have hm_p1 : m =⋆ (byte1Array k.values_begin (assignBytes max_var Assignment.empty) ⋆
      int4Array k.trail_begin trail_free0) ⋆
    (ZeroTermInts literals lits ⋆ (kernelState st k ⋆ R_lits)) := by
    have h := hsep
    rw [hP_lits, sep_comm_l (kernelState st k)] at h
    exact h
  have hcap_p1 : aids.length + lits.length ≤ trail_free0.length := by omega
  refine Exec.seq_cps (exec_rup_phase1_loop (reserve := aids.length)
    (stat_lit_assigned0 := k.stat_lit_assigned)
    (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
    hlits_valid hcap_p1 hm_p1 ?_)
  intro m1 l1 checked1 trail_end1 stat_lit_assigned1 assign1 trail1 trail_free1
    hchk1 hte1 hsla1 hlocals1 hte_eq1 hcov1 htrail_valid1 hlen_sum1 hcap1 hm1 hres1
  have hm1_restored : m1 =⋆ (byte1Array k.values_begin (assignBytes max_var assign1) ⋆
      int4Array k.trail_begin (trail1 ++ trail_free1)) ⋆
    (kernelState st k ⋆ P_ro) := by
    have h := hm1
    rw [sep_comm_l (ZeroTermInts literals lits) (kernelState st k) R_lits, ← hP_lits] at h
    exact h
  have hst1 : l1["st"]? = some st := by
    rw [hlocals1 "st" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    simp [hst_var]
  have hid1 : l1["id"]? = some id := by
    rw [hlocals1 "id" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    simp [hid_var]
  have hante1 : l1["antecedents"]? = some antecedents := by
    rw [hlocals1 "antecedents" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    simp [hante_var]
  have hlb1 : l1["literals_begin"]? = some k.literals_begin := by
    rw [hlocals1 "literals_begin" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    simp
  have hvb1 : l1["values_begin"]? = some k.values_begin := by
    rw [hlocals1 "values_begin" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    simp
  have htb1 : l1["trail_begin"]? = some k.trail_begin := by
    rw [hlocals1 "trail_begin" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    simp
  have hsr1 : l1["stat_resolved"]? = some (k.stat_resolved + 1) := by
    rw [hlocals1 "stat_resolved" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    simp
  rcases hres1 with ⟨rfl, hiff_fals⟩ | ⟨rfl, htaut⟩
  · -- Case checked1 = 0: enter Phase 2
    have hcond_p2 : (Expr.op .eq (.var "checked") (.literal 0)).eval m1 l1 = some 1 := by
      simp [Expr.eval, hchk1, interpBinop]
    refine Exec.seq_cps (Exec.cond_cps hcond_p2 (fun _ => ?_) (fun hz => absurd hz (by decide)))
    refine Exec.seq_cps (Exec.set_cps (v := antecedents) (by simp [Expr.eval, hante1]) ?_)
    obtain ⟨R_aids, hP_aids⟩ := haids_ro
    have hm1_aids_front : m1 =⋆ ZeroTermInts antecedents aids ⋆
        ((byte1Array k.values_begin (assignBytes max_var assign1) ⋆
          int4Array k.trail_begin (trail1 ++ trail_free1)) ⋆ (kernelState st k ⋆ R_aids)) := by
      have h := hm1_restored
      rw [hP_aids, sep_pull_3rd] at h
      exact h
    have hload_aid0 : (Expr.op .srs (.op .slu (.load .four (.var "a")) (.literal 32)) (.literal 32)).eval m1
        (l1.insert "a" antecedents) = some (zeroTermGet aids 0) :=
      eval_load4_zeroTermGet (Nat.zero_le _) (by simp [Expr.eval]) hm1_aids_front (fun x hx => (haids_valid x hx).1)
    refine Exec.seq_cps (Exec.set_cps hload_aid0 ?_)
    refine exec_rup_phase2_outer_loop (id := id) (initAssign := assign1)
      (stat_resolved0 := k.stat_resolved + 1) (stat_lit_assigned0 := stat_lit_assigned1)
      hct ⟨R_aids, hP_aids⟩ haids_valid hcap1 (CNF.entails_refl (s.toCNF ++ assign1.toCNF))
      (by simp [hst1]) (by simp [hid1]) (by simp [hlb1]) (by simp [hvb1]) (by simp [htb1])
      (by simp [hte1]) (by simp [hsr1]) (by simp [hsla1]) (by simp [hchk1]) (by simp) (by simp)
      hte_eq1 hcov1 htrail_valid1 hm1_restored ?_
    intro m2 l2 checked2 trail_end2 stat_resolved2 stat_lit_assigned2 assign2 trail2 trail_free2
      hst2 hid2 hvb2 htb2 hchk2 hte2 hsr2 hsla2 hte_eq2 hcov2 htrail_valid2 hlen_sum2 hm2 hres2
    rcases hres2 with rfl | ⟨rfl, hunsat⟩
    · -- checked2 = 0: hits `if checked == 0 { flush_prop_state; interact lrat_fail(3, id, 0, 0, 0) }`
      have hcond_fail : (Expr.op .eq (.var "checked") (.literal 0)).eval m2 l2 = some 1 := by
        simp [Expr.eval, hchk2, interpBinop]
      have hm2_ks : m2 =⋆ kernelState st k ⋆
          ((byte1Array k.values_begin (assignBytes max_var assign2) ⋆
            int4Array k.trail_begin (trail2 ++ trail_free2)) ⋆ P_ro) := by
        rw [sep_comm_l] at hm2; exact hm2
      refine Exec.seq_cps (Exec.cond_cps hcond_fail (fun _ => ?_) (fun hz => absurd hz (by decide)))
      refine exec_flush_and_fail (trail_end := trail_end2) (stat_resolved := stat_resolved2)
        (stat_lit_assigned := stat_lit_assigned2) (args := [3, id, 0, 0, 0])
        hst2 hte2 hsr2 hsla2 hm2_ks (fun m'' => ?_)
      simp [evalArgs, Expr.eval, hid2]
    · -- checked2 = 1: RUP conflict reached!
      have hent_cl : CNF.EntailsClause s.toCNF (toClause lits) :=
        entailsClause_of_unsat_of_iff_falsified hiff_fals hunsat
      have hcond_ok : (Expr.op .eq (.var "checked") (.literal 0)).eval m2 l2 = some 0 := by
        simp [Expr.eval, hchk2, interpBinop]
      refine Exec.seq_cps (Exec.cond_cps hcond_ok (fun hnz => False.elim (hnz rfl)) (fun _ => .skip _ _ _ _ _ ?_))
      refine exec_backtrack_and_flush hst2 hvb2 htb2 hte2 hsr2 hsla2 hte_eq2 (by omega) hcov2 htrail_valid2 hm2
        fun m3 l3 hm3 => ?_
      exact hpost m3 l3 stat_resolved2 stat_lit_assigned2 (trail2 ++ trail_free2)
        (by rw [List.length_append, hlen_sum2, hlen_sum1]) hm3 hent_cl
  · -- Case checked1 = 1: tautology in Phase 1!
    have hent_cl : CNF.EntailsClause s.toCNF (toClause lits) :=
      entailsClause_of_tautology htaut
    have hcond_p2 : (Expr.op .eq (.var "checked") (.literal 0)).eval m1 l1 = some 0 := by
      simp [Expr.eval, hchk1, interpBinop]
    refine Exec.seq_cps (Exec.cond_cps hcond_p2 (fun hnz => False.elim (hnz rfl)) (fun _ => .skip _ _ _ _ _ ?_))
    refine Exec.seq_cps (Exec.cond_cps hcond_p2 (fun hnz => False.elim (hnz rfl)) (fun _ => .skip _ _ _ _ _ ?_))
    refine exec_backtrack_and_flush hst1 hvb1 htb1 hte1 hsr1 hsla1 hte_eq1 (by omega) hcov1 htrail_valid1 hm1_restored
      fun m3 l3 hm3 => ?_
    exact hpost m3 l3 (k.stat_resolved + 1) stat_lit_assigned1 (trail1 ++ trail_free1)
      (by rw [List.length_append, hlen_sum1]) hm3 hent_cl

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
  have hst : l₀["st"]? = some st := by
    simp [l₀, br_check_clause_non_strictly_by_propagation, insertMany_cons, insertMany_nil]
  have hid : l₀["id"]? = some id := by
    simp [l₀, br_check_clause_non_strictly_by_propagation, insertMany_cons, insertMany_nil]
  have hlits : l₀["literals"]? = some literals := by
    simp [l₀, br_check_clause_non_strictly_by_propagation, insertMany_cons, insertMany_nil]
  have hante : l₀["antecedents"]? = some antecedents := by
    simp [l₀, br_check_clause_non_strictly_by_propagation, insertMany_cons, insertMany_nil]
  exact exec_br_check_clause_non_strictly_by_propagation
    hk_trail hct hlits_ro haids_ro hlits_valid haids_valid hcap htrail_len
    hst hid hlits hante hsep
    (fun m' _ sr sla trail_all hlen hm' hent => ⟨[], rfl, hpost m' sr sla trail_all hlen hm' hent⟩)

end Kraken.Bedrock2.Test
