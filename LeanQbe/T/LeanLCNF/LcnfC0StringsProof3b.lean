module

public import LeanQbe.T.LeanLCNF.LcnfC0StringsProof3a

/-!
# LeanLCNF R2b Proof Part 3b (`LcnfC0StringsProof3b`)

Per-function weakest-precondition proofs for `lcnf_array_mk`, `lcnf_array_to_list`, and
`lcnf_array_replicate` against `lcnfArrayMkSpec`, `lcnfArrayToListSpec`, and
`lcnfArrayReplicateSpec`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.LeanLCNF

open Kraken LeanQbe.T

/-! ## 1. Shared Heap, RC, List, and Array Helpers -/

private theorem bv64_listConsHeader_eq : (72620647070564353 : BitVec 64) = listConsHeaderWord := by
  decide

private theorem bv64_toNat_ofNat_lt {n : Nat} (hn : n < 2 ^ 64) :
    (BitVec.ofNat 64 n).toNat = n := by
  simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]

private theorem bv64_mul8_ofNat (k : Nat) :
    (8 : BitVec 64) * BitVec.ofNat 64 k = BitVec.ofNat 64 (8 * k) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.mul_mod]

private theorem bv64_add16_assoc (a : BitVec 64) : (a + 8#64) + 8#64 = a + 16#64 := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.add_mod]
  omega

private theorem list_drop_pred_cons {α : Type _} (xs : List α) {k : Nat}
    (hk0 : 0 < k) (hk : k ≤ xs.length) :
    xs.drop (k - 1) = xs[k - 1] :: xs.drop k := by
  have hk' : k - 1 < xs.length := by omega
  have heq : xs.drop (k - 1) = xs[k - 1] :: xs.drop (k - 1 + 1) :=
    List.drop_eq_getElem_cons hk'
  have h1 : k - 1 + 1 = k := by omega
  rwa [h1] at heq

private theorem list_replicate_snoc {α : Type _} (n : Nat) (x : α) :
    List.replicate n x ++ [x] = List.replicate (n + 1) x := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, ih]

private theorem list_pairwise_ne_getElem {α : Type _} :
    ∀ {xs : List α}, xs.Pairwise (· ≠ ·) → ∀ {i j : Nat}
      (hi : i < xs.length) (hj : j < xs.length), i ≠ j → xs[i] ≠ xs[j]
  | _ :: _xs, .cons hhd _, 0, _j + 1, _, hj, _ => fun hEq =>
    hhd _ (List.getElem_mem (Nat.lt_of_succ_lt_succ hj)) hEq
  | _ :: _xs, .cons hhd _, _i + 1, 0, hi, _, _ => fun hEq =>
    hhd _ (List.getElem_mem (Nat.lt_of_succ_lt_succ hi)) hEq.symm
  | _ :: _xs, .cons _ htl, _i + 1, _j + 1, hi, hj, hij =>
    list_pairwise_ne_getElem htl (Nat.lt_of_succ_lt_succ hi) (Nat.lt_of_succ_lt_succ hj)
      (fun h => hij (congrArg Nat.succ h))

private theorem lcnfHeap_focus_obj {objs : List LcnfObj} {o : LcnfObj} (ho : o ∈ objs) :
    ∃ i, ∃ (hi : i < objs.length), objs[i] = o ∧
      lcnfHeap objs = lcnfObjMem o ⋆ (lcnfHeap (objs.take i) ⋆ lcnfHeap (objs.drop (i + 1))) := by
  obtain ⟨i, hi, heq⟩ := List.mem_iff_getElem.mp ho
  have hf := lcnfHeap_focus objs hi
  rw [heq] at hf
  exact ⟨i, hi, heq, hf⟩

private theorem lcnfHeap_set_focus {objs : List LcnfObj} {o' : LcnfObj} {i : Nat}
    (hi : i < objs.length) {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (lcnfObjMem o' ⋆ (lcnfHeap (objs.take i) ⋆ lcnfHeap (objs.drop (i + 1))) ⋆ R) m) :
    (lcnfHeap (objs.set i o') ⋆ R) m := by
  rw [lcnfHeap_set objs hi o']
  exact hm

private theorem list_map_addr_eq_set {objs : List LcnfObj}
    (hnodup : (objs.map LcnfObj.addr).Nodup) {i : Nat} (hi : i < objs.length)
    (p : LcnfObj → Prop) [DecidablePred p] (f : LcnfObj → LcnfObj)
    (hp : p objs[i]) :
    objs.map (fun o => if o.addr = objs[i].addr ∧ p o then f o else o) =
      objs.set i (f objs[i]) := by
  apply List.ext_getElem
  · simp
  · intro j hj1 hj2
    have hj : j < objs.length := by simp at hj1; exact hj1
    simp only [List.getElem_map, List.getElem_set]
    by_cases hij : i = j
    · subst hij
      simp [hp]
    · have hne : objs[j].addr ≠ objs[i].addr := by
        have h := list_pairwise_ne_getElem hnodup
          (i := j) (j := i) (by simp; exact hj) (by simp; exact hi) (Ne.symm hij)
        simpa [List.getElem_map] using h
      rw [ite_eq_right (by simp [hne]), ite_eq_right hij]

private theorem bv32_toNat_of_nonneg (x : BitVec 32) (h : 0 ≤ x.toInt) :
    x.toNat < 2147483648 ∧ x.toInt = ↑x.toNat := by
  rw [BitVec.toInt_eq_toNat_cond] at h ⊢
  by_cases hlt : 2 * x.toNat < 2 ^ 32
  · rw [ite_eq_left hlt]
    exact ⟨by omega, rfl⟩
  · rw [ite_eq_right hlt] at h
    have hbd : x.toNat < 2 ^ 32 := x.isLt
    omega

private theorem bv32_nonneg_of_toNat_lt (x : BitVec 32) (hlt : x.toNat < 2147483648) :
    0 ≤ x.toInt := by
  rw [BitVec.toInt_eq_toNat_cond, ite_eq_left (by omega)]
  omega

private theorem incRcVal_nonneg (rc : BitVec 32) (h : 0 ≤ rc.toInt) :
    0 ≤ (incRcVal rc).toInt := by
  unfold incRcVal
  by_cases hlt : 0 < rc.toInt ∧ rc.toInt < 2147483647
  · rw [ite_eq_left hlt]
    have ⟨_, hto⟩ := bv32_toNat_of_nonneg rc h
    apply bv32_nonneg_of_toNat_lt
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  · rw [ite_eq_right hlt]
    exact h

private theorem lcnfObj_withRc_wf {o : LcnfObj} (hwf : o.Wf) {rc' : BitVec 32}
    (hrc : 0 ≤ rc'.toInt) : (o.withRc rc').Wf := by
  rcases hwf with ⟨h1, h2, _, h4, h5, h6, h7, h8, h9, h10⟩
  simp only [LcnfObj.Wf, LcnfObj.withRc, LcnfObj.totalBytes] at h7 h8 h9 h10 ⊢
  exact ⟨h1, h2, hrc, h4, h5, h6, h7, h8, h9, h10⟩

private theorem incObjList_wf (v : BitVec 64) {objs : List LcnfObj}
    (hwf : ∀ o ∈ objs, o.Wf) : ∀ o ∈ incObjList v objs, o.Wf := by
  unfold incObjList
  by_cases hv : v = 0#64 ∨ v &&& 1#64 ≠ 0#64
  · rw [ite_eq_left hv]; exact hwf
  · rw [ite_eq_right hv]
    intro o ho
    rw [List.mem_map] at ho
    rcases ho with ⟨x, hx, rfl⟩
    by_cases ha : x.addr = v
    · rw [ite_eq_left ha]
      exact lcnfObj_withRc_wf (hwf x hx) (incRcVal_nonneg x.rc (hwf x hx).2.2.1)
    · rw [ite_eq_right ha]
      exact hwf x hx

private theorem incElemsList_wf (xs : List (BitVec 64)) {objs : List LcnfObj}
    (hwf : ∀ o ∈ objs, o.Wf) : ∀ o ∈ incElemsList xs objs, o.Wf := by
  induction xs generalizing objs with
  | nil => rw [incElemsList.eq_1]; exact hwf
  | cons x xs ih =>
    rw [incElemsList.eq_2]
    exact ih (incObjList_wf x hwf)

private theorem incElemsList_append (xs ys : List (BitVec 64)) (objs : List LcnfObj) :
    incElemsList (xs ++ ys) objs = incElemsList ys (incElemsList xs objs) := by
  induction xs generalizing objs with
  | nil => simp [incElemsList.eq_1]
  | cons x xs ih => simp [incElemsList.eq_2, ih]

private theorem incObjList_exists_withRc (v : BitVec 64) {objs : List LcnfObj} {o : LcnfObj}
    (ho : o ∈ objs) (hrc : 0 ≤ o.rc.toInt) :
    ∃ rc', o.withRc rc' ∈ incObjList v objs ∧ 0 ≤ rc'.toInt := by
  unfold incObjList
  by_cases hv : v = 0#64 ∨ v &&& 1#64 ≠ 0#64
  · rw [ite_eq_left hv]
    refine ⟨o.rc, ?_, hrc⟩
    have : o.withRc o.rc = o := by cases o; rfl
    rw [this]; exact ho
  · rw [ite_eq_right hv]
    by_cases ha : o.addr = v
    · refine ⟨incRcVal o.rc, ?_, incRcVal_nonneg o.rc hrc⟩
      rw [List.mem_map]
      exact ⟨o, ho, by simp [ha]⟩
    · refine ⟨o.rc, ?_, hrc⟩
      have heq : o.withRc o.rc = o := by cases o; rfl
      rw [heq, List.mem_map]
      exact ⟨o, ho, by simp [ha]⟩

private theorem incElemsList_exists_withRc (xs : List (BitVec 64)) {objs : List LcnfObj}
    {o : LcnfObj} (ho : o ∈ objs) (hrc : 0 ≤ o.rc.toInt) :
    ∃ rc', o.withRc rc' ∈ incElemsList xs objs ∧ 0 ≤ rc'.toInt := by
  induction xs generalizing objs o with
  | nil =>
    rw [incElemsList.eq_1]
    exact ⟨o.rc, by cases o; exact ho, hrc⟩
  | cons x xs ih =>
    rw [incElemsList.eq_2]
    obtain ⟨rc1, ho1, hrc1⟩ := incObjList_exists_withRc x ho hrc
    obtain ⟨rc2, ho2, hrc2⟩ := ih ho1 hrc1
    refine ⟨rc2, ?_, hrc2⟩
    simpa [LcnfObj.withRc] using ho2

private theorem incObjList_has_addr (w v : BitVec 64) {objs : List LcnfObj}
    (hv : v = 0#64 ∨ v &&& 1#64 ≠ 0#64 ∨ ∃ o ∈ objs, o.addr = v) :
    v = 0#64 ∨ v &&& 1#64 ≠ 0#64 ∨ ∃ o ∈ incObjList w objs, o.addr = v := by
  rcases hv with rfl | hodd | ⟨o, ho, hoa⟩
  · exact Or.inl rfl
  · exact Or.inr (Or.inl hodd)
  · unfold incObjList
    by_cases hw : w = 0#64 ∨ w &&& 1#64 ≠ 0#64
    · rw [ite_eq_left hw]; exact Or.inr (Or.inr ⟨o, ho, hoa⟩)
    · rw [ite_eq_right hw]
      refine Or.inr (Or.inr ⟨if o.addr = w then o.withRc (incRcVal o.rc) else o, ?_, ?_⟩)
      · rw [List.mem_map]; exact ⟨o, ho, rfl⟩
      · by_cases ha : o.addr = w
        · rw [ite_eq_left ha]; simpa [LcnfObj.withRc] using hoa
        · rw [ite_eq_right ha]; exact hoa

private theorem listConsCanon_withRc {o : LcnfObj} (hc : ListConsCanon o) {rc' : BitVec 32}
    (hrc : 0 ≤ rc'.toInt) : ListConsCanon (o.withRc rc') := by
  rcases hc with ⟨h1, h2, _, h4, h5, h6, h7, h8⟩
  exact ⟨h1, h2, hrc, h4, h5, h6, h7, h8⟩

private theorem isListInHeap_incObjList (w : BitVec 64) {objs : List LcnfObj}
    {p : BitVec 64} {xs : List (BitVec 64)} (h : IsListInHeap objs p xs) :
    IsListInHeap (incObjList w objs) p xs := by
  induction h with
  | nil => exact .nil
  | cons hmem ha hcan hf heven _ ih =>
    obtain ⟨rc', hmem', hrc'⟩ := incObjList_exists_withRc w hmem hcan.2.2.1
    exact .cons hmem' (by simpa [LcnfObj.withRc] using ha)
      (listConsCanon_withRc hcan hrc') (by simpa [LcnfObj.withRc] using hf) heven ih

private theorem wp_call_r2b_inc_obj {rs : List Ty} {Q : Post rs} {X : XPost}
    (v : BitVec 64) {objs : List LcnfObj} (hwf : ∀ o ∈ objs, o.Wf)
    (hv : v = 0#64 ∨ v &&& 1#64 ≠ 0#64 ∨ ∃ o ∈ objs, o.addr = v)
    {R : Mem 64 → Prop} {m : Mem 64} {k : Tup Val [] → Expr Val Cont rs}
    (hm : (lcnfHeap objs ⋆ R) m)
    (hcont : ∀ m', (lcnfHeap (incObjList v objs) ⋆ R) m' → wp rtR2bEnv Q X (k ()) m') :
    wp rtR2bEnv Q X (@Expr.call Val Cont rs "r2b_inc_obj" [i64] [] (Arg.var v, ()) k) m := by
  apply @wp_call_of_spec _ _ _ _ _ _ [i64] []
  apply rtR2bEnv_r2b_inc_obj
  dsimp only [r2IncObjSpec, vals, Arg.val_var]
  by_cases himm : v = 0#64 ∨ v &&& 1#64 ≠ 0#64
  · rw [ite_eq_left himm]
    have hinc : incObjList v objs = objs := by simp [incObjList, himm]
    refine hcont m ?_
    rw [hinc]
    exact hm
  · rw [ite_eq_right himm]
    have hex : ∃ o ∈ objs, o.addr = v := by
      rcases hv with h0 | hodd | hex
      · exact absurd (Or.inl h0) himm
      · exact absurd (Or.inr hodd) himm
      · exact hex
    rcases hex with ⟨o, ho, hoa⟩
    have hnodup : (objs.map LcnfObj.addr).Nodup := lcnfHeap_nodup_addrs hm
    obtain ⟨i, hi, heq, hheap⟩ := lcnfHeap_focus_obj ho
    have hm' : (lcnfObjMem o ⋆
        (lcnfHeap (objs.take i) ⋆ lcnfHeap (objs.drop (i + 1)) ⋆ R)) m := by
      rw [hheap] at hm
      exact sep_cast hm (by ac_rfl)
    refine ⟨o, lcnfHeap (objs.take i) ⋆ lcnfHeap (objs.drop (i + 1)) ⋆ R,
      hoa, hwf o ho, hm', fun m' hm'' => ?_⟩
    have hm1 : (lcnfHeap (objs.set i (o.withRc (incRcVal o.rc))) ⋆ R) m' :=
      lcnfHeap_set_focus hi (sep_cast hm'' (by ac_rfl))
    have hinc : incObjList v objs = objs.set i (o.withRc (incRcVal o.rc)) := by
      have hsub := list_map_addr_eq_set hnodup hi (fun _ => True)
        (fun x => x.withRc (incRcVal x.rc)) trivial
      unfold incObjList
      rw [ite_eq_right himm, ← hoa, ← heq]
      simpa using hsub
    exact hcont m' (hinc ▸ hm1)

private theorem wp_call_r2b_dec_obj {rs : List Ty} {Q : Post rs} {X : XPost}
    (rt o : BitVec 64) {st : RtC0State} {objs : List LcnfObj}
    (hwf : ∀ x ∈ objs, x.Wf)
    (hpre : ¬ (o = 0#64 ∨ o &&& 1#64 ≠ 0#64) →
      ∃ obj ∈ objs, obj.addr = o ∧
        (obj.rc = 1#32 → objs.length ≤ st.workCap ∧ lcnfHeapClosed objs ∧ RcSound o objs))
    {R : Mem 64 → Prop} {m : Mem 64} {k : Tup Val [] → Expr Val Cont rs}
    (hm : (rtC0Inv rt st ⋆ lcnfHeap objs ⋆ R) m)
    (hcont : ∀ st' objs' m', st'.PreservesMeta st → st'.rem = st.rem →
      DecObjRel o objs objs' → (rtC0Inv rt st' ⋆ lcnfHeap objs' ⋆ R) m' →
      wp rtR2bEnv Q X (k ()) m') :
    wp rtR2bEnv Q X (@Expr.call Val Cont rs "r2b_dec_obj" [i64, i64] []
      (Arg.var rt, Arg.var o, ()) k) m := by
  apply @wp_call_of_spec _ _ _ _ _ _ [i64, i64] []
  apply rtR2bEnv_r2b_dec_obj
  dsimp only [r2DecObjSpec, vals, Arg.val_var]
  by_cases himm : o = 0#64 ∨ o &&& 1#64 ≠ 0#64
  · rw [ite_eq_left himm]
    exact hcont st objs m (RtC0State.PreservesMeta.refl st) rfl (by simp [DecObjRel, himm]) hm
  · rw [ite_eq_right himm]
    exact ⟨st, objs, R, hpre himm, hwf, hm, fun st' objs' m' hpr hrem hdec hm' =>
      hcont st' objs' m' hpr hrem hdec hm'⟩

private theorem store_array64_snoc_step {arr : BitVec 64} {len : Nat}
    {filled : List (BitVec 64)} (v : BitVec 64) {R : Mem 64 → Prop} {m : Mem 64}
    (hlt : filled.length < len) (hle : 8 * (len - filled.length) ≤ 2 ^ 64)
    (hm : (array64 (arr + 24#64) filled ⋆
      region ((arr + 24#64) + BitVec.ofNat 64 (8 * filled.length)) (8 * (len - filled.length)) ⋆
      R) m) :
    let p := (arr + 24#64) + BitVec.ofNat 64 (8 * filled.length)
    storeOk m i64 p ∧
      (array64 (arr + 24#64) (filled ++ [v]) ⋆
        region ((arr + 24#64) + BitVec.ofNat 64 (8 * (filled ++ [v]).length))
          (8 * (len - (filled ++ [v]).length)) ⋆
        R) (storeMem m i64 p v) := by
  have hmReg : (region ((arr + 24#64) + BitVec.ofNat 64 (8 * filled.length))
      (8 * (len - filled.length)) ⋆ (array64 (arr + 24#64) filled ⋆ R)) m :=
    sep_cast hm (by ac_rfl)
  obtain ⟨w, hmCell⟩ := region_pop_cell64 (by omega) hle hmReg
  have hmCell' : (cell64 ((arr + 24#64) + BitVec.ofNat 64 (8 * filled.length)) w ⋆
      (region (((arr + 24#64) + BitVec.ofNat 64 (8 * filled.length)) + 8#64)
        (8 * (len - filled.length) - 8) ⋆ array64 (arr + 24#64) filled ⋆ R)) m :=
    sep_cast hmCell (by ac_rfl)
  obtain ⟨hstOk, hmStored⟩ := r2_c0_store_cell64 v hmCell'
  refine ⟨hstOk, ?_⟩
  have h1 : (array64 (arr + 24#64) (filled ++ [v]) ⋆
      region (((arr + 24#64) + BitVec.ofNat 64 (8 * filled.length)) + 8#64)
        (8 * (len - filled.length) - 8) ⋆ R) (storeMem m i64
          ((arr + 24#64) + BitVec.ofNat 64 (8 * filled.length)) v) := by
    rw [array64_append (arr + 24#64) filled [v], array64_cons, array64_nil,
      Std.ExtHashMap.sep_emp]
    exact sep_cast hmStored (by ac_rfl)
  have hptr : ((arr + 24#64) + BitVec.ofNat 64 (8 * filled.length)) + 8#64 =
      (arr + 24#64) + BitVec.ofNat 64 (8 * (filled ++ [v]).length) := by
    rw [BitVec.add_assoc]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mul_add]
  have hrem : 8 * (len - filled.length) - 8 = 8 * (len - (filled ++ [v]).length) := by
    simp; omega
  rw [hptr, hrem] at h1
  exact h1

private theorem mkArrObj_mem_of_filled {arr : BitVec 64} {len : Nat}
    {elems : List (BitVec 64)} {R : Mem 64 → Prop} {m : Mem 64}
    (hlen : elems.length = len)
    (hm : (cell64 arr arrHeaderWord ⋆ cell64 (arr + 8#64) (BitVec.ofNat 64 len) ⋆
      cell64 (arr + 16#64) (BitVec.ofNat 64 len) ⋆ array64 (arr + 24#64) elems ⋆
      region ((arr + 24#64) + BitVec.ofNat 64 (8 * elems.length)) (8 * (len - elems.length)) ⋆
      R) m) :
    (lcnfObjMem (mkArrObj arr (1#32) len elems) ⋆ R) m := by
  have hmem := hm
  have hzero : 8 * (len - elems.length) = 0 := by omega
  rw [hzero, region_zero, Std.ExtHashMap.sep_emp] at hmem
  rw [lcnfObjMem_array_eq (o := mkArrObj arr (1#32) len elems) rfl]
  simp only [mkArrObj, hlen]
  have hzero2 : 8 * (len - len) = 0 := by omega
  rw [hzero2, region_zero, Std.ExtHashMap.sep_emp]
  have hhdr : (mkArrObj arr (1#32) len elems).header = arrHeaderWord :=
    mkArrObj_header arr len elems
  simp only [mkArrObj] at hhdr
  rw [hhdr]
  exact hmem

private theorem lcnfObjHeader_and_mask (o : LcnfObj) :
    (o.header &&& 4294967295#64) = BitVec.ofNat 64 o.rc.toNat := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [LcnfObj.header, BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_ofNat]
  have hmask : Nat.testBit 4294967295 i = decide (i < 32) := by
    have hpow : (4294967295 : Nat) = 2 ^ 32 - 1 := rfl
    rw [hpow, Nat.testBit_two_pow_sub_one]
  rw [hmask]
  by_cases hi32 : i < 32
  · have hi48 : i < 48 := by omega
    have hi56 : i < 56 := by omega
    simp [hi32, hi48, hi56, hi]
  · have hlt : o.rc.toNat < 2 ^ 32 := o.rc.isLt
    have htb : Nat.testBit o.rc.toNat i = false := Nat.testBit_lt_two_pow (by
      calc o.rc.toNat < 2 ^ 32 := hlt
        _ ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) (by omega))
    simp [hi32, htb]

private theorem lcnfObjHeader_add_nat (o : LcnfObj) (hwf : o.Wf) (d : Nat)
    (hle : o.rc.toNat + d ≤ 2147483647) :
    o.header + BitVec.ofNat 64 d = (o.withRc (o.rc + BitVec.ofNat 32 d)).header ∧
      0 ≤ (o.rc + BitVec.ofNat 32 d).toInt := by
  induction d generalizing o with
  | zero =>
    have hz64 : BitVec.ofNat 64 0 = 0#64 := rfl
    have hz32 : BitVec.ofNat 32 0 = 0#32 := rfl
    rw [hz64, hz32, BitVec.add_zero, BitVec.add_zero]
    have heq : o.withRc o.rc = o := by cases o; rfl
    rw [heq]
    exact ⟨rfl, hwf.2.2.1⟩
  | succ d ih =>
    obtain ⟨hd, hnonneg⟩ := ih o hwf (by omega)
    let o1 := o.withRc (o.rc + BitVec.ofNat 32 d)
    have ho1Wf : o1.Wf := lcnfObj_withRc_wf hwf hnonneg
    have ho1RcLt : o1.rc.toNat < 2147483647 := by
      have ⟨hrcLt, _⟩ := bv32_toNat_of_nonneg o.rc hwf.2.2.1
      simp only [o1, LcnfObj.withRc, BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    have ho1IntLt : o1.rc.toInt < 2147483647 := by
      rw [(bv32_toNat_of_nonneg o1.rc hnonneg).2]
      exact Int.ofNat_lt.mpr ho1RcLt
    have hadd1 := lcnfObjHeader_add1 o1 ho1Wf ho1IntLt
    have hsucc64 : BitVec.ofNat 64 (d + 1) = BitVec.ofNat 64 d + 1#64 := by
      apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]
    have hsucc32 : BitVec.ofNat 32 (d + 1) = BitVec.ofNat 32 d + 1#32 := by
      apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]
    have hdrEq : o.header + BitVec.ofNat 64 (d + 1) =
        (o.withRc (o.rc + BitVec.ofNat 32 (d + 1))).header := by
      rw [hsucc64, ← BitVec.add_assoc, hd]
      change o1.header + 1#64 = _
      rw [hadd1, hsucc32, ← BitVec.add_assoc]
      rfl
    have hnonneg' : 0 ≤ (o.rc + BitVec.ofNat 32 (d + 1)).toInt := by
      have heq32 : o.rc + BitVec.ofNat 32 (d + 1) = o1.rc + 1#32 := by
        rw [hsucc32, ← BitVec.add_assoc]; rfl
      rw [heq32]
      apply bv32_nonneg_of_toNat_lt
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    exact ⟨hdrEq, hnonneg'⟩

private theorem addRcObjList_of_rc_zero {objs : List LcnfObj}
    (hnodup : (objs.map LcnfObj.addr).Nodup) {v : BitVec 64} {o : LcnfObj}
    (ho : o ∈ objs) (hoa : o.addr = v) (hrc0 : o.rc = 0#32) (d : Nat) :
    addRcObjList v d objs = objs := by
  unfold addRcObjList
  apply List.ext_getElem
  · simp
  · intro j hj1 hj2
    have hj : j < objs.length := hj2
    simp only [List.getElem_map]
    by_cases hc : objs[j].addr = v ∧ objs[j].rc ≠ 0#32
    · obtain ⟨i, hi, heq⟩ := List.mem_iff_getElem.mp ho
      have hij : j = i := by
        by_cases hijEq : j = i
        · exact hijEq
        · have hdiff := list_pairwise_ne_getElem hnodup
            (i := j) (j := i) (by simp; exact hj) (by simp; exact hi) hijEq
          simp only [List.getElem_map] at hdiff
          exact absurd (hc.1.trans (heq ▸ hoa).symm) hdiff
      have hrc : objs[j].rc = 0#32 := by cases hij; rw [heq, hrc0]
      exact absurd hrc hc.2
    · rw [ite_eq_right hc]

private theorem addRcObjList_eq_set {objs : List LcnfObj}
    (hnodup : (objs.map LcnfObj.addr).Nodup) {i : Nat} (hi : i < objs.length)
    (hrc : objs[i].rc ≠ 0#32) (d : Nat) :
    addRcObjList objs[i].addr d objs =
      objs.set i (objs[i].withRc (objs[i].rc + BitVec.ofNat 32 d)) :=
  list_map_addr_eq_set hnodup hi (fun o => o.rc ≠ 0#32)
    (fun o => o.withRc (o.rc + BitVec.ofNat 32 d)) hrc

/-! ## 2. `lcnf_array_mk` WP Proof -/

theorem lcnf_array_mk_wp (xs : Tup Val [i64, i64]) (m : Mem 64)
    (Q : Post [i64]) (X : XPost) :
    lcnfArrayMkSpec xs m Q X → Func.wp rtR2bEnv lcnf_array_mk_body xs m Q X := by
  rcases xs with ⟨rt, list, ⟨⟩⟩
  intro ⟨st, elems, objs, R, hlist, hwf, helemv, hm0, hspec⟩
  unfold lcnf_array_mk_body Func.wp
  refine wp_loop_group
    (Inv := fun remLen xs1 m1 =>
      ∃ n cur remElems, xs1 = (n, cur, ()) ∧
        n = BitVec.ofNat 64 (elems.length - remElems.length) ∧
        remElems.length ≤ elems.length ∧
        elems.length - remElems.length ≤ arrMaxCap ∧
        remElems.length = remLen ∧
        IsListInHeap objs cur remElems ∧
        m1 = m)
    ?_ ?_
  · intro J remLen xs1 m1 hJ hInv
    rcases hInv with ⟨n, cur, remElems, rfl, rfl, hleLen, hkCap, hrem, hcur, hmEq1⟩
    rw [hmEq1]
    c0_steps
    · have heven : cur &&& 1#64 = 0#64 := by assumption
      have hcap : (33554428#64).toNat ≤
          (BitVec.ofNat 64 (elems.length - remElems.length)).toNat := by assumption
      obtain ⟨hd, tl, nxt, node, hremEq, _, _, _, _, _⟩ :=
        (isListInHeap_and1 hcur).1 heven
      have hkVal : (BitVec.ofNat 64 (elems.length - remElems.length)).toNat =
          elems.length - remElems.length :=
        bv64_toNat_ofNat_lt (by simp only [arrMaxCap] at hkCap; omega)
      have hlenGt : arrMaxCap < elems.length := by
        have h1 : 33554428 ≤ (BitVec.ofNat 64 (elems.length - remElems.length)).toNat := hcap
        rw [hkVal] at h1
        have hpos : 0 < remElems.length := by rw [hremEq]; simp
        simp only [arrMaxCap]; omega
      rw [ite_eq_left hlenGt] at hspec
      exact hspec
    · have heven : cur &&& 1#64 = 0#64 := by assumption
      have hnotCap : ¬ ((33554428#64).toNat ≤
          (BitVec.ofNat 64 (elems.length - remElems.length)).toNat) := by assumption
      obtain ⟨hd, tl, nxt, node, hremEq, hmem, haddr, hcan, hf, hnext⟩ :=
        (isListInHeap_and1 hcur).1 heven
      have hkVal : (BitVec.ofNat 64 (elems.length - remElems.length)).toNat =
          elems.length - remElems.length :=
        bv64_toNat_ofNat_lt (by simp only [arrMaxCap] at hkCap; omega)
      have hkLt : elems.length - remElems.length < arrMaxCap := by
        have hnot : ¬ (33554428 ≤ (BitVec.ofNat 64 (elems.length - remElems.length)).toNat) :=
          hnotCap
        rw [hkVal] at hnot
        simp only [arrMaxCap]; omega
      obtain ⟨iNode, hiNode, heqNode, hfocusNode⟩ := lcnfHeap_focus_obj hmem
      obtain ⟨hd0, tl0, hf0, hmemNode⟩ := lcnfObjMem_listCons_eq hcan
      rw [hf] at hf0
      simp only [List.cons.injEq, and_true] at hf0
      obtain ⟨rfl, rfl⟩ := hf0
      have hmemLoad : (cell64 node.addr node.header ⋆ cell64 (node.addr + 8#64) hd ⋆
          cell64 (node.addr + 16#64) nxt ⋆
          (lcnfHeap (objs.take iNode) ⋆ lcnfHeap (objs.drop (iNode + 1)) ⋆
            rtC0Inv rt st ⋆ R)) m := by
        have hm0' : (lcnfObjMem node ⋆ (lcnfHeap (objs.take iNode) ⋆
            lcnfHeap (objs.drop (iNode + 1)) ⋆ rtC0Inv rt st ⋆ R)) m := by
          rw [hfocusNode] at hm0
          exact sep_cast hm0 (by ac_rfl)
        rw [hmemNode] at hm0'
        exact sep_cast hm0' (by ac_rfl)
      rw [haddr] at hmemLoad
      have hld16 := r2b_c0_load_cell64_raw16 hmemLoad
      apply wp_load_of (v := nxt) (by simpa [Arg.val_var, lift2] using hld16)
      c0_steps
      apply hJ tl.length (BitVec.ofNat 64 (elems.length - remElems.length) + 1#64, nxt, ()) m
      · rw [← hrem, hremEq]; simp
      · have htlLe : tl.length ≤ elems.length := by rw [hremEq] at hleLen; simp at hleLen; omega
        have hsub : elems.length - tl.length = (elems.length - remElems.length) + 1 := by
          rw [hremEq] at hleLen ⊢; simp at hleLen ⊢; omega
        refine ⟨_, nxt, tl, rfl, ?_, htlLe, by simp only [arrMaxCap] at hkLt ⊢; omega,
          rfl, hnext, rfl⟩
        rw [hsub]
        have hkLt1 : elems.length - remElems.length + 1 < 2 ^ 64 := by
          simp only [arrMaxCap] at hkLt; omega
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
          Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hkLt1]
    · have hodd : ¬ (cur &&& 1#64 = 0#64) := by assumption
      obtain ⟨rfl, hnil⟩ := (isListInHeap_and1 hcur).2 hodd
      rw [hnil] at hleLen hkCap ⊢
      simp only [List.length_nil, Nat.sub_zero] at hkCap
      have hnotGt : ¬ arrMaxCap < elems.length := by omega
      rw [ite_eq_right hnotGt] at hspec
      rcases hspec with ⟨hclosedSpec, hfreeSpec, hpostSpec⟩
      apply wp_call_of_spec
      apply rtR2bEnv_r2b_alloc_array
      dsimp only [r2bAllocArraySpec, vals, Arg.val_var]
      simp only [List.length_nil, Nat.sub_zero]
      have hcapCheck : (BitVec.ofNat 64 elems.length).toNat ≤
            (BitVec.ofNat 64 elems.length).toNat ∧
          (BitVec.ofNat 64 elems.length).toNat ≤ arrMaxCap := by
        rw [bv64_toNat_ofNat_lt (by simp only [arrMaxCap] at hkCap; omega)]
        exact ⟨Nat.le_refl _, hkCap⟩
      rw [ite_eq_left hcapCheck]
      rw [bv64_toNat_ofNat_lt (by simp only [arrMaxCap] at hkCap; omega)]
      refine ⟨st, lcnfHeap objs ⋆ R, hfreeSpec, sep_cast hm0 (by ac_rfl),
        fun arr st1 m1 ha0 ha8 hpr1 hrem1 _ hm1 => ?_⟩
      c0_steps
      refine wp_loop_group
        (Inv := fun remLen2 xs2 m2 =>
          ∃ cur2 i2 filled remElems2 st2 objs2,
            xs2 = (cur2, i2, ()) ∧
            elems = filled ++ remElems2 ∧
            i2 = BitVec.ofNat 64 filled.length ∧
            remElems2.length = remLen2 ∧
            st2.PreservesMeta st1 ∧ st2.rem ≤ st1.rem ∧
            objs2 = incElemsList filled objs ∧
            IsListInHeap objs2 cur2 remElems2 ∧
            (∀ o ∈ objs2, o.Wf) ∧
            (∀ v ∈ elems, v = 0#64 ∨ v &&& 1#64 ≠ 0#64 ∨ ∃ o ∈ objs2, o.addr = v) ∧
            (rtC0Inv rt st2 ⋆ cell64 arr arrHeaderWord ⋆
              cell64 (arr + 8#64) (BitVec.ofNat 64 elems.length) ⋆
              cell64 (arr + 16#64) (BitVec.ofNat 64 elems.length) ⋆
              array64 (arr + 24#64) filled ⋆
              region ((arr + 24#64) + BitVec.ofNat 64 (8 * filled.length))
                (8 * (elems.length - filled.length)) ⋆
              lcnfHeap objs2 ⋆ R) m2)
        ?_ ?_
      · intro J2 remLen2 xs2 m2 hJ2 hInv2
        rcases hInv2 with ⟨cur2, i2, filled, remElems2, st2, objs2,
          rfl, hsplit, rfl, hrem2, hpr2, hremLe2, rfl, hlist2, hwf2, hev2, hm2⟩
        c0_steps
        · have heven2 : cur2 &&& 1#64 = 0#64 := by assumption
          obtain ⟨hd, tl, nxt, node2, hremEq2, hmem2, haddr2, hcan2, hf2, hnext2⟩ :=
            (isListInHeap_and1 hlist2).1 heven2
          obtain ⟨iN2, hiN2, heqN2, hfocusN2⟩ := lcnfHeap_focus_obj hmem2
          obtain ⟨hd0, tl0, hf0, hmemN2⟩ := lcnfObjMem_listCons_eq hcan2
          rw [hf2] at hf0
          simp only [List.cons.injEq, and_true] at hf0
          obtain ⟨rfl, rfl⟩ := hf0
          have hmLoadHd : (cell64 node2.addr node2.header ⋆ cell64 (node2.addr + 8#64) hd ⋆
              cell64 (node2.addr + 16#64) nxt ⋆
              (lcnfHeap ((incElemsList filled objs).take iN2) ⋆
                lcnfHeap ((incElemsList filled objs).drop (iN2 + 1)) ⋆
                rtC0Inv rt st2 ⋆ cell64 arr arrHeaderWord ⋆
                cell64 (arr + 8#64) (BitVec.ofNat 64 elems.length) ⋆
                cell64 (arr + 16#64) (BitVec.ofNat 64 elems.length) ⋆
                array64 (arr + 24#64) filled ⋆
                region ((arr + 24#64) + BitVec.ofNat 64 (8 * filled.length))
                  (8 * (elems.length - filled.length)) ⋆ R)) m2 := by
            have hm2' : (lcnfObjMem node2 ⋆ (lcnfHeap ((incElemsList filled objs).take iN2) ⋆
                lcnfHeap ((incElemsList filled objs).drop (iN2 + 1)) ⋆ rtC0Inv rt st2 ⋆
                cell64 arr arrHeaderWord ⋆ cell64 (arr + 8#64) (BitVec.ofNat 64 elems.length) ⋆
                cell64 (arr + 16#64) (BitVec.ofNat 64 elems.length) ⋆
                array64 (arr + 24#64) filled ⋆
                region ((arr + 24#64) + BitVec.ofNat 64 (8 * filled.length))
                  (8 * (elems.length - filled.length)) ⋆ R)) m2 := by
              rw [hfocusN2] at hm2
              exact sep_cast hm2 (by ac_rfl)
            rw [hmemN2] at hm2'
            exact sep_cast hm2' (by ac_rfl)
          rw [haddr2] at hmLoadHd
          have hld8 := r2b_c0_load_cell64_raw8 hmLoadHd
          apply wp_load_of (v := hd) (by simpa [Arg.val_var, lift2] using hld8)
          c0_steps
          have hhdMem : hd ∈ elems := by rw [hsplit, hremEq2]; simp
          have hmIncPre : (lcnfHeap (incElemsList filled objs) ⋆
              (rtC0Inv rt st2 ⋆ cell64 arr arrHeaderWord ⋆
                cell64 (arr + 8#64) (BitVec.ofNat 64 elems.length) ⋆
                cell64 (arr + 16#64) (BitVec.ofNat 64 elems.length) ⋆
                array64 (arr + 24#64) filled ⋆
                region ((arr + 24#64) + BitVec.ofNat 64 (8 * filled.length))
                  (8 * (elems.length - filled.length)) ⋆ R)) m2 :=
            sep_cast hm2 (by ac_rfl)
          refine wp_call_r2b_inc_obj hd hwf2 (hev2 hd hhdMem) hmIncPre fun m3 hm3 => ?_
          c0_steps
          have hltLen : filled.length < elems.length := by
            have : elems.length = filled.length + remElems2.length := by rw [hsplit]; simp
            rw [hremEq2] at this; simp at this; omega
          have hleCap : 8 * (elems.length - filled.length) ≤ 2 ^ 64 := by
            simp only [arrMaxCap] at hkCap; omega
          have hmArr3 : (array64 (arr + 24#64) filled ⋆
              region ((arr + 24#64) + BitVec.ofNat 64 (8 * filled.length))
                (8 * (elems.length - filled.length)) ⋆
              (rtC0Inv rt st2 ⋆ cell64 arr arrHeaderWord ⋆
                cell64 (arr + 8#64) (BitVec.ofNat 64 elems.length) ⋆
                cell64 (arr + 16#64) (BitVec.ofNat 64 elems.length) ⋆
                lcnfHeap (incObjList hd (incElemsList filled objs)) ⋆ R)) m3 :=
            sep_cast hm3 (by ac_rfl)
          obtain ⟨hstOk, hmStored⟩ := store_array64_snoc_step hd hltLen hleCap hmArr3
          have hptrEq : arr + 24 + 8 * BitVec.ofNat 64 filled.length =
              (arr + 24#64) + BitVec.ofNat 64 (8 * filled.length) := by
            apply BitVec.eq_of_toNat_eq
            simp [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.mul_mod]
          rw [← hptrEq] at hstOk hmStored
          rw [wp_store]
          simp only [Arg.val_var]
          refine ⟨hstOk, ?_⟩
          c0_steps
          let objs3 := incObjList hd (incElemsList filled objs)
          have hlist3 : IsListInHeap objs3 cur2 (hd :: tl) :=
            hremEq2 ▸ isListInHeap_incObjList hd hlist2
          have ⟨hd', tl', nxt', node3, hremEq3, hmem3, haddr3, hcan3, hf3, hnext3⟩ :=
            (isListInHeap_and1 hlist3).1 heven2
          obtain ⟨_, htlEq⟩ := List.cons.inj hremEq3
          subst htlEq
          obtain ⟨iN3, hiN3, heqN3, hfocusN3⟩ := lcnfHeap_focus_obj hmem3
          obtain ⟨hd0', tl0', hf0', hmemN3⟩ := lcnfObjMem_listCons_eq hcan3
          rw [hf3] at hf0'
          simp only [List.cons.injEq, and_true] at hf0'
          obtain ⟨rfl, rfl⟩ := hf0'
          have hm3' : (lcnfHeap objs3 ⋆
              (rtC0Inv rt st2 ⋆ cell64 arr arrHeaderWord ⋆
                cell64 (arr + 8#64) (BitVec.ofNat 64 elems.length) ⋆
                cell64 (arr + 16#64) (BitVec.ofNat 64 elems.length) ⋆
                array64 (arr + 24#64) (filled ++ [hd]) ⋆
                region ((arr + 24#64) + BitVec.ofNat 64 (8 * (filled ++ [hd]).length))
                  (8 * (elems.length - (filled ++ [hd]).length)) ⋆ R))
              (storeMem m3 i64 (arr + 24 + 8 * BitVec.ofNat 64 filled.length) hd) :=
            sep_cast hmStored (by ac_rfl)
          rw [hfocusN3, hmemN3] at hm3'
          have hmLoadNxt : (cell64 node3.addr node3.header ⋆ cell64 (node3.addr + 8#64) hd' ⋆
              cell64 (node3.addr + 16#64) nxt' ⋆
              (lcnfHeap (objs3.take iN3) ⋆ lcnfHeap (objs3.drop (iN3 + 1)) ⋆
                rtC0Inv rt st2 ⋆ cell64 arr arrHeaderWord ⋆
                cell64 (arr + 8#64) (BitVec.ofNat 64 elems.length) ⋆
                cell64 (arr + 16#64) (BitVec.ofNat 64 elems.length) ⋆
                array64 (arr + 24#64) (filled ++ [hd]) ⋆
                region ((arr + 24#64) + BitVec.ofNat 64 (8 * (filled ++ [hd]).length))
                  (8 * (elems.length - (filled ++ [hd]).length)) ⋆ R))
              (storeMem m3 i64 (arr + 24 + 8 * BitVec.ofNat 64 filled.length) hd) :=
            sep_cast hm3' (by ac_rfl)
          rw [haddr3] at hmLoadNxt
          have hld16' := r2b_c0_load_cell64_raw16 hmLoadNxt
          apply wp_load_of (v := nxt') (by simpa [Arg.val_var, lift2] using hld16')
          c0_steps
          apply hJ2 tl.length
            (nxt', BitVec.ofNat 64 filled.length + 1, ())
            (storeMem m3 i64 (arr + 24 + 8 * BitVec.ofNat 64 filled.length) hd)
          · rw [← hrem2, hremEq2]; simp
          · have hsplit' : elems = (filled ++ [hd]) ++ tl := by rw [hsplit, hremEq2]; simp
            have hi' : BitVec.ofNat 64 filled.length + (1 : BitVec 64) =
                BitVec.ofNat 64 (filled ++ [hd]).length := by
              apply BitVec.eq_of_toNat_eq
              simp [BitVec.toNat_add, BitVec.toNat_ofNat]
            have hobjs' : objs3 = incElemsList (filled ++ [hd]) objs := by
              change incObjList hd (incElemsList filled objs) = incElemsList (filled ++ [hd]) objs
              rw [incElemsList_append, incElemsList.eq_2, incElemsList.eq_1]
            refine ⟨nxt', BitVec.ofNat 64 filled.length + 1, filled ++ [hd], tl, st2, objs3,
              rfl, hsplit', hi', rfl, hpr2, hremLe2, hobjs', hnext3,
              incObjList_wf hd hwf2, fun v hv => incObjList_has_addr hd v (hev2 v hv), ?_⟩
            exact sep_cast hmStored (by ac_rfl)
        · have hodd2 : ¬ (cur2 &&& 1#64 = 0#64) := by assumption
          obtain ⟨rfl, rfl⟩ := (isListInHeap_and1 hlist2).2 hodd2
          simp only [List.append_nil] at hsplit
          rw [← hsplit] at hwf2 hm2
          have hmArrObj : (rtC0Inv rt st2 ⋆ lcnfHeap (incElemsList elems objs) ⋆
              (lcnfObjMem (mkArrObj arr (1#32) elems.length elems) ⋆ R)) m2 := by
            have hm' : (cell64 arr arrHeaderWord ⋆
                cell64 (arr + 8#64) (BitVec.ofNat 64 elems.length) ⋆
                cell64 (arr + 16#64) (BitVec.ofNat 64 elems.length) ⋆
                array64 (arr + 24#64) elems ⋆
                region ((arr + 24#64) + BitVec.ofNat 64 (8 * elems.length))
                  (8 * (elems.length - elems.length)) ⋆
                (rtC0Inv rt st2 ⋆ lcnfHeap (incElemsList elems objs) ⋆ R)) m2 :=
              sep_cast hm2 (by ac_rfl)
            have hm'' := mkArrObj_mem_of_filled rfl hm'
            exact sep_cast hm'' (by ac_rfl)
          refine wp_call_r2b_dec_obj rt list hwf2
            (fun hn => by
              have hne1 : list ≠ 1#64 := fun h1 => hn (Or.inr (h1 ▸ bv64_one_and1_ne_zero))
              obtain ⟨o, ho, hoa, hcls⟩ := hclosedSpec hne1
              refine ⟨o, ho, hoa, fun hrc1 => ?_⟩
              have ⟨hwc, hlc, hrs⟩ := hcls hrc1
              have hst1wc : st1.workCap = st.workCap :=
                RtC0State.workCap_eq_of_preservesMeta hpr1
              have hst2wc : st2.workCap = st1.workCap :=
                RtC0State.workCap_eq_of_preservesMeta hpr2
              rw [hst2wc, hst1wc]
              exact ⟨hwc, hlc, hrs⟩)
            hmArrObj fun st' objs' m' hpr' hrem' hdec' hm' => ?_
          c0_steps
          have hcanon : ArrCanon (mkArrObj arr (1#32) elems.length elems) :=
            mkArrObj_canon ha0 ha8 (by decide) (Nat.le_refl _) hkCap
          exact hpostSpec arr st' objs' m' ha0 ha8
            (RtC0State.PreservesMeta.trans (RtC0State.PreservesMeta.trans hpr1 hpr2) hpr')
            (Nat.le_trans (Nat.le_of_eq hrem') (Nat.le_trans hremLe2 hrem1))
            hcanon hdec' (sep_cast hm' (by ac_rfl))
      · intro J2 hJ2
        c0_steps
        refine hJ2 elems.length (list, 0#64, ()) m1 ⟨list, 0#64, [], elems, st1, objs, rfl, rfl,
          rfl, rfl, RtC0State.PreservesMeta.refl st1, Nat.le_refl _,
          (incElemsList.eq_1 objs).symm, hlist, hwf, helemv, ?_⟩
        rw [List.length_nil, Nat.sub_zero]
        exact sep_cast hm1 (by ac_rfl)
  · intro J hJ
    c0_steps
    exact hJ elems.length (0#64, list, ()) m ⟨0#64, list, elems, rfl, by simp, Nat.le_refl _,
      by simp, rfl, hlist, rfl⟩

/-! ## 3. `lcnf_array_to_list` WP Proof -/

theorem lcnf_array_to_list_wp (xs : Tup Val [i64, i64]) (m : Mem 64)
    (Q : Post [i64]) (X : XPost) :
    lcnfArrayToListSpec xs m Q X → Func.wp rtR2bEnv lcnf_array_to_list_body xs m Q X := by
  rcases xs with ⟨rt, arr, ⟨⟩⟩
  intro ⟨st, arrObj, objs, R, harrMem, harrAddr, harrCan, hwf, helemv,
    hclosedSpec, hremArr, hm0, hpostSpec⟩
  unfold lcnf_array_to_list_body Func.wp
  c0_steps
  let n := arrObj.fields.length
  have hnCap : n ≤ arrMaxCap := Nat.le_trans harrCan.2.2.2.2.2.2.1 harrCan.2.2.2.2.2.2.2
  have hnLt64 : n < 2 ^ 64 := by simp only [arrMaxCap] at hnCap; omega
  obtain ⟨iArr, hiArr, heqArr, hfocusArr⟩ := lcnfHeap_focus_obj harrMem
  have hmemArrLd : (lcnfObjMem arrObj ⋆
      (lcnfHeap (objs.take iArr) ⋆ lcnfHeap (objs.drop (iArr + 1)) ⋆ rtC0Inv rt st ⋆ R)) m := by
    rw [hfocusArr] at hm0
    exact sep_cast hm0 (by ac_rfl)
  rw [lcnfObjMem_array_eq harrCan.2.2.2.2.2.1] at hmemArrLd
  have hmemSz : (cell64 arrObj.addr arrObj.header ⋆
      cell64 (arrObj.addr + 8#64) (BitVec.ofNat 64 n) ⋆
      cell64 (arrObj.addr + 16#64) (BitVec.ofNat 64 arrObj.cap) ⋆
      (array64 (arrObj.addr + 24#64) arrObj.fields ⋆
        region (arrObj.addr + BitVec.ofNat 64 (24 + 8 * n)) (8 * (arrObj.cap - n)) ⋆
        lcnfHeap (objs.take iArr) ⋆ lcnfHeap (objs.drop (iArr + 1)) ⋆
        rtC0Inv rt st ⋆ R)) m :=
    sep_cast hmemArrLd (by ac_rfl)
  rw [harrAddr] at hmemSz
  have hldN := r2b_c0_load_cell64_raw8 hmemSz
  apply wp_load_of (v := BitVec.ofNat 64 n) (by simpa [Arg.val_var, lift2] using hldN)
  c0_steps
  refine wp_loop_group
    (Inv := fun k xs1 m1 =>
      ∃ res i1 resObjs st1 objs1,
        xs1 = (res, i1, ()) ∧
        k ≤ n ∧
        i1 = BitVec.ofNat 64 k ∧
        st1.PreservesMeta st ∧ st1.rem ≤ st.rem ∧
        st.rem - 24 * (n - k) ≤ st1.rem ∧
        ExclListMem res (arrObj.fields.drop k) resObjs ∧
        objs1 = incElemsList (arrObj.fields.drop k).reverse objs ∧
        (∀ o ∈ objs1, o.Wf) ∧
        (∀ v ∈ arrObj.fields, v = 0#64 ∨ v &&& 1#64 ≠ 0#64 ∨ ∃ o ∈ objs1, o.addr = v) ∧
        (rtC0Inv rt st1 ⋆ lcnfHeap resObjs ⋆ lcnfHeap objs1 ⋆ R) m1)
    ?_ ?_
  · intro J k xs1 m1 hJ hInv
    rcases hInv with ⟨res, i1, resObjs, st1, objs1, rfl, hkLe, rfl, hpr1, hremLe1, hremLo1,
      hresMem, rfl, hwf1, hev1, hm1⟩
    c0_steps
    · have hpos : (0#64).toNat < (BitVec.ofNat 64 k).toNat := by assumption
      have hkLt64 : k < 2 ^ 64 := Nat.lt_of_le_of_lt hkLe hnLt64
      have hkVal : (BitVec.ofNat 64 k).toNat = k := bv64_toNat_ofNat_lt hkLt64
      have hkPos : 0 < k := by
        have hlt : 0 < (BitVec.ofNat 64 k).toNat := hpos
        rw [hkVal] at hlt
        exact hlt
      let k' := k - 1
      have hk'Val : BitVec.ofNat 64 k - 1#64 = BitVec.ofNat 64 k' := by
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_sub, bv64_toNat_ofNat_lt hkLt64,
          show (1#64).toNat = 1 from rfl, bv64_toNat_ofNat_lt (by omega)]
        have hwrap : 2 ^ 64 - 1 + k = 2 ^ 64 + (k - 1) := by omega
        rw [hwrap, Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_mod,
          Nat.mod_eq_of_lt (by omega)]
      obtain ⟨rcA, hmemA, hrcA⟩ := incElemsList_exists_withRc
        (arrObj.fields.drop k).reverse harrMem harrCan.2.2.1
      obtain ⟨iA, hiA, heqA, hfocusA⟩ := lcnfHeap_focus_obj hmemA
      have hmArrA : (lcnfObjMem (arrObj.withRc rcA) ⋆
          (lcnfHeap ((incElemsList (arrObj.fields.drop k).reverse objs).take iA) ⋆
            lcnfHeap ((incElemsList (arrObj.fields.drop k).reverse objs).drop (iA + 1)) ⋆
            rtC0Inv rt st1 ⋆ lcnfHeap resObjs ⋆ R)) m1 := by
        rw [hfocusA] at hm1
        exact sep_cast hm1 (by ac_rfl)
      rw [lcnfObjMem_array_eq (o := arrObj.withRc rcA) harrCan.2.2.2.2.2.1] at hmArrA
      simp only [LcnfObj.withRc] at hmArrA
      rw [harrAddr] at hmArrA
      have hmArrFields : (array64 (arr + 24#64) arrObj.fields ⋆
          (cell64 arr (arrObj.withRc rcA).header ⋆
            cell64 (arr + 8#64) (BitVec.ofNat 64 n) ⋆
            cell64 (arr + 16#64) (BitVec.ofNat 64 arrObj.cap) ⋆
            region (arr + BitVec.ofNat 64 (24 + 8 * n)) (8 * (arrObj.cap - n)) ⋆
            lcnfHeap ((incElemsList (arrObj.fields.drop k).reverse objs).take iA) ⋆
            lcnfHeap ((incElemsList (arrObj.fields.drop k).reverse objs).drop (iA + 1)) ⋆
            rtC0Inv rt st1 ⋆ lcnfHeap resObjs ⋆ R)) m1 :=
        sep_cast hmArrA (by ac_rfl)
      have hk'Lt : (BitVec.ofNat 64 k - 1#64).toNat < arrObj.fields.length := by
        rw [hk'Val, bv64_toNat_ofNat_lt (by omega)]
        change k - 1 < n; omega
      have hldElem := r2_c0_load_array64_add24_mul8 hmArrFields hk'Lt
      have hk'Idx : (BitVec.ofNat 64 k - 1#64).toNat = k' := by
        rw [hk'Val, bv64_toNat_ofNat_lt (by omega)]
      have hk'In : k' < arrObj.fields.length := by change k - 1 < n; omega
      let v := arrObj.fields[k']
      have hvEq : arrObj.fields[(BitVec.ofNat 64 k - 1#64).toNat]'hk'Lt = v := by
        simp only [hk'Idx]; rfl
      rw [hvEq] at hldElem
      have hptrElem : arr + 24 + 8 * (BitVec.ofNat 64 k - 1) =
          arr + 24#64 + 8#64 * (BitVec.ofNat 64 k - 1#64) := by rfl
      apply wp_load_of (v := v) (by simpa [Arg.val_var, lift2, hptrElem] using hldElem)
      c0_steps
      have hvMem : v ∈ arrObj.fields := List.getElem_mem hk'In
      have hmIncPre : (lcnfHeap (incElemsList (arrObj.fields.drop k).reverse objs) ⋆
          (rtC0Inv rt st1 ⋆ lcnfHeap resObjs ⋆ R)) m1 := sep_cast hm1 (by ac_rfl)
      refine wp_call_r2b_inc_obj v hwf1 (hev1 v hvMem) hmIncPre fun m2 hm2 => ?_
      c0_steps
      let objs2 := incObjList v (incElemsList (arrObj.fields.drop k).reverse objs)
      apply wp_call_of_spec
      apply rtR2bEnv_lcnf_alloc
      dsimp only [lcnfAllocRemSpec, vals, Arg.val_var, Arg.val_imm]
      have hsz24 : (24 : BitVec 64).toNat ≤ 268435448 := by decide
      have halign24 : rtMinObjBytes ≤ align8 (24 : BitVec 64).toNat ∧
          align8 (24 : BitVec 64).toNat < rtMaxObjBytes := by
        decide
      have hrem24 : 24 ≤ st1.rem := by
        have hstep : 24 * (n - k) + 24 ≤ 24 * n := by
          have : n - k + 1 ≤ n := by omega
          omega
        omega
      have halEq24 : align8 (24 : BitVec 64).toNat = 24 := by decide
      rw [halEq24]
      refine ⟨st1, lcnfHeap resObjs ⋆ lcnfHeap objs2 ⋆ R, hsz24, halign24.1, halign24.2,
        Or.inr hrem24, sep_cast hm2 (by ac_rfl),
        fun node st2 m3 hnode0 hnode8 hpr2 hremLe2 hremLo2 hm3 => ?_⟩
      have hmPop0 : (region node 24 ⋆
          (rtC0Inv rt st2 ⋆ lcnfHeap resObjs ⋆ lcnfHeap objs2 ⋆ R)) m3 :=
        sep_cast hm3 (by ac_rfl)
      obtain ⟨w0, hmC0⟩ := region_pop_cell64 (by decide) (by decide) hmPop0
      have hmPop1 : (region (node + 8#64) 16 ⋆ (cell64 node w0 ⋆ rtC0Inv rt st2 ⋆
          lcnfHeap resObjs ⋆ lcnfHeap objs2 ⋆ R)) m3 := sep_cast hmC0 (by ac_rfl)
      obtain ⟨w1, hmC1⟩ := region_pop_cell64 (by decide) (by decide) hmPop1
      have hmPop2 : (region ((node + 8#64) + 8#64) 8 ⋆ (cell64 node w0 ⋆ cell64 (node + 8#64) w1 ⋆
          rtC0Inv rt st2 ⋆ lcnfHeap resObjs ⋆ lcnfHeap objs2 ⋆ R)) m3 := sep_cast hmC1 (by ac_rfl)
      obtain ⟨w2, hmC2⟩ := region_pop_cell64 (by decide) (by decide) hmPop2
      rw [bv64_add16_assoc, show 8 - 8 = 0 from rfl, region_zero, Std.ExtHashMap.sep_emp] at hmC2
      have hmPre0 : (cell64 node w0 ⋆ (cell64 (node + 8#64) w1 ⋆ cell64 (node + 16#64) w2 ⋆
          rtC0Inv rt st2 ⋆ lcnfHeap resObjs ⋆ lcnfHeap objs2 ⋆ R)) m3 :=
        sep_cast hmC2 (by ac_rfl)
      obtain ⟨hstOk0, hm4⟩ := r2_c0_store_cell64 (72620647070564353 : BitVec 64) hmPre0
      rw [wp_store]
      simp only [Arg.val_var, Arg.val_imm] at hstOk0 hm4 ⊢
      refine ⟨hstOk0, ?_⟩
      c0_steps
      have hmPre1 : (cell64 (node + 8#64) w1 ⋆ (cell64 node (72620647070564353 : BitVec 64) ⋆
          cell64 (node + 16#64) w2 ⋆ rtC0Inv rt st2 ⋆ lcnfHeap resObjs ⋆ lcnfHeap objs2 ⋆ R))
          (storeMem m3 i64 node 72620647070564353) :=
        sep_cast hm4 (by ac_rfl)
      obtain ⟨hstOk1, hm5⟩ := r2_c0_store_cell64 v hmPre1
      rw [wp_store]
      simp only [Arg.val_var] at hstOk1 hm5 ⊢
      refine ⟨hstOk1, ?_⟩
      c0_steps
      have hmPre2 : (cell64 (node + 16#64) w2 ⋆ (cell64 node (72620647070564353 : BitVec 64) ⋆
          cell64 (node + 8#64) v ⋆ rtC0Inv rt st2 ⋆ lcnfHeap resObjs ⋆ lcnfHeap objs2 ⋆ R))
          (storeMem (storeMem m3 i64 node 72620647070564353) i64 (node + 8) v) :=
        sep_cast hm5 (by ac_rfl)
      obtain ⟨hstOk2, hm6⟩ := r2_c0_store_cell64 res hmPre2
      rw [wp_store]
      simp only [Arg.val_var] at hstOk2 hm6 ⊢
      refine ⟨hstOk2, ?_⟩
      c0_steps
      have hmNodeCells : (cell64 node listConsHeaderWord ⋆ cell64 (node + 8#64) v ⋆
          cell64 (node + 16#64) res ⋆
          (rtC0Inv rt st2 ⋆ lcnfHeap resObjs ⋆ lcnfHeap objs2 ⋆ R))
          (storeMem (storeMem (storeMem m3 i64 node 72620647070564353) i64 (node + 8) v)
            i64 (node + 16) res) := by
        rw [← bv64_listConsHeader_eq]
        exact sep_cast hm6 (by ac_rfl)
      have hmCons := mkListConsObj_mem hnode0 hnode8 hmNodeCells
      apply hJ k' (node, BitVec.ofNat 64 k - 1#64, ())
        (storeMem (storeMem (storeMem m3 i64 node 72620647070564353) i64 (node + 8) v)
          i64 (node + 16) res)
        (by change k - 1 < k; omega)
      have hdropEq : arrObj.fields.drop k' = v :: arrObj.fields.drop k :=
        list_drop_pred_cons arrObj.fields hkPos hkLe
      have hremStep : st.rem - 24 * (n - k') ≤ st2.rem := by
        have h24 : 24 * (n - k') = 24 * (n - k) + 24 := by change 24 * (n - (k - 1)) = _; omega
        omega
      have hobjsEq : objs2 = incElemsList (arrObj.fields.drop k').reverse objs := by
        rw [hdropEq, List.reverse_cons, incElemsList_append, incElemsList.eq_2, incElemsList.eq_1]
      refine ⟨node, BitVec.ofNat 64 k - 1#64, mkListConsObj node (1#32) v res :: resObjs,
        st2, objs2, rfl, by change k - 1 ≤ n; omega, hk'Val,
        RtC0State.PreservesMeta.trans hpr1 hpr2, Nat.le_trans hremLe2 hremLe1, hremStep,
        hdropEq ▸ ExclListMem.cons rfl hnode0 hnode8 hresMem,
        hobjsEq, incObjList_wf v hwf1, fun w hw => incObjList_has_addr v w (hev1 w hw), ?_⟩
      simp only [lcnfHeap]
      exact sep_cast hmCons (by ac_rfl)
    · have hnotPos : ¬ ((0#64).toNat < (BitVec.ofNat 64 k).toNat) := by assumption
      have hkVal : (BitVec.ofNat 64 k).toNat = k := bv64_toNat_ofNat_lt (by omega)
      have hk0 : k = 0 := by
        have hnot : ¬ (0 < (BitVec.ofNat 64 k).toNat) := hnotPos
        rw [hkVal] at hnot
        omega
      subst hk0
      simp only [List.drop_zero] at hresMem hwf1
      have hmDecPre : (rtC0Inv rt st1 ⋆ lcnfHeap (incElemsList arrObj.fields.reverse objs) ⋆
          (lcnfHeap resObjs ⋆ R)) m1 := by
        simp only [List.drop_zero] at hm1
        exact sep_cast hm1 (by ac_rfl)
      refine wp_call_r2b_dec_obj rt arr hwf1
        (fun _ => by
          obtain ⟨o, ho, hoa, hcls⟩ := hclosedSpec
          refine ⟨o, ho, hoa, fun hrc1 => ?_⟩
          have ⟨hwc, hlc, hrs⟩ := hcls hrc1
          have hst1wc : st1.workCap = st.workCap :=
            RtC0State.workCap_eq_of_preservesMeta hpr1
          rw [hst1wc]
          exact ⟨hwc, hlc, hrs⟩)
        hmDecPre fun st' objs' m' hpr' hrem' hdec' hm' => ?_
      c0_steps
      exact hpostSpec res st' resObjs objs' m' (RtC0State.PreservesMeta.trans hpr1 hpr')
        (Nat.le_trans (Nat.le_of_eq hrem') hremLe1) hresMem hdec' (sep_cast hm' (by ac_rfl))
  · intro J hJ
    c0_steps
    refine hJ n (1#64, BitVec.ofNat 64 n, ()) m ⟨1#64, BitVec.ofNat 64 n, [], st, objs, rfl,
      Nat.le_refl _, rfl, RtC0State.PreservesMeta.refl st, Nat.le_refl _, by simp, ?_, ?_,
      hwf, helemv, ?_⟩
    · rw [List.drop_length]; exact ExclListMem.nil
    · rw [List.drop_length, List.reverse_nil, incElemsList.eq_1]
    · simp only [lcnfHeap, Std.ExtHashMap.sep_emp]
      exact hm0

/-! ## 4. `lcnf_array_replicate` WP Proof -/

private theorem array_replicate_fill_wp {Q : Post [i64]} {X : XPost}
    {arr v cntBv : BitVec 64} {R' : Mem 64 → Prop} {mJ : Mem 64} {hc}
    (hregLe : 8 * cntBv.toNat ≤ 2 ^ 64)
    (hmJ : (cell64 arr arrHeaderWord ⋆ cell64 (arr + 8#64) cntBv ⋆
      cell64 (arr + 16#64) cntBv ⋆ region (arr + 24#64) (8 * cntBv.toNat) ⋆ R') mJ)
    (hdone : ∀ mF,
      (lcnfObjMem (mkArrObj arr (1#32) cntBv.toNat (List.replicate cntBv.toNat v)) ⋆ R') mF →
      Q (arr, ()) mF) :
    wp rtR2bEnv Q X
      (Expr.group
        (fun (Js : Tup Cont [[i64]]) =>
          Blocks.cons
            (fun (p : Tup Val [i64]) =>
              Expr.let_
                { sig := [i64, i64], code := OpCode.cmp CmpOp.ult i64 Ty.bool hc,
                  args := (Arg.var p.fst, Arg.var cntBv, ()) }
                fun p_1 =>
                Expr.jnz (Arg.var p_1.fst)
                  (Expr.let_
                    { sig := [i64, i64], code := OpCode.add i64,
                      args := (Arg.var arr, Arg.imm 24, ()) }
                    fun p_2 =>
                    Expr.let_
                      { sig := [i64, i64], code := OpCode.mul i64,
                        args := (Arg.imm 8, Arg.var p.fst, ()) }
                      fun p_3 =>
                      Expr.let_
                        { sig := [i64, i64], code := OpCode.add i64,
                          args := (Arg.var p_2.fst, Arg.var p_3.fst, ()) }
                        fun p_4 =>
                        Expr.store (Arg.var (t := i64) v) (Arg.var p_4.fst)
                          (Expr.let_
                            { sig := [i64, i64], code := OpCode.add i64,
                              args := (Arg.var p.fst, Arg.imm 1, ()) }
                            fun p => Expr.jump Js.fst (Arg.var p.fst, ())))
                  (Expr.ret (Arg.var arr, ())))
            Blocks.nil)
        fun Js => Expr.jump Js.fst (Arg.imm 0, ()))
      mJ := by
  have hcntLt : cntBv.toNat < 2 ^ 64 := cntBv.isLt
  refine wp_loop_group
    (Inv := fun remCnt xsL mL =>
      ∃ filled,
        xsL = (BitVec.ofNat 64 filled.length, ()) ∧
        filled = List.replicate filled.length v ∧
        filled.length ≤ cntBv.toNat ∧
        remCnt = cntBv.toNat - filled.length ∧
        (cell64 arr arrHeaderWord ⋆ cell64 (arr + 8#64) cntBv ⋆
          cell64 (arr + 16#64) cntBv ⋆ array64 (arr + 24#64) filled ⋆
          region ((arr + 24#64) + BitVec.ofNat 64 (8 * filled.length))
            (8 * (cntBv.toNat - filled.length)) ⋆ R') mL)
    ?_ ?_
  · intro Jfill remCnt xsL mL hJfill hInvL
    rcases hInvL with ⟨filled, rfl, hrepl, hleL, rfl, hmL⟩
    c0_steps
    · have hlt : (BitVec.ofNat 64 filled.length).toNat < cntBv.toNat := by assumption
      have hltNat : filled.length < cntBv.toNat := by
        have h1 : (BitVec.ofNat 64 filled.length).toNat < cntBv.toNat := hlt
        rw [bv64_toNat_ofNat_lt (by omega)] at h1
        exact h1
      have hleReg : 8 * (cntBv.toNat - filled.length) ≤ 2 ^ 64 := by omega
      obtain ⟨hstOk, hmStored⟩ := store_array64_snoc_step
        (arr := arr) (len := cntBv.toNat) (filled := filled)
        (R := cell64 arr arrHeaderWord ⋆ cell64 (arr + 8#64) cntBv ⋆
          cell64 (arr + 16#64) cntBv ⋆ R')
        v hltNat hleReg (sep_cast hmL (by ac_rfl) :
          (array64 (arr + 24#64) filled ⋆
            region ((arr + 24#64) + BitVec.ofNat 64 (8 * filled.length))
              (8 * (cntBv.toNat - filled.length)) ⋆
            (cell64 arr arrHeaderWord ⋆ cell64 (arr + 8#64) cntBv ⋆
              cell64 (arr + 16#64) cntBv ⋆ R')) mL)
      have hptrEq : arr + 24 + 8 * BitVec.ofNat 64 filled.length =
          (arr + 24#64) + BitVec.ofNat 64 (8 * filled.length) := by
        apply BitVec.eq_of_toNat_eq
        simp [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.mul_mod]
      rw [← hptrEq] at hstOk hmStored
      rw [wp_store]
      simp only [Arg.val_var]
      refine ⟨hstOk, ?_⟩
      c0_steps
      apply hJfill (cntBv.toNat - (filled ++ [v]).length)
        (BitVec.ofNat 64 filled.length + 1, ())
        (storeMem mL i64 (arr + 24 + 8 * BitVec.ofNat 64 filled.length) v)
      · simp; omega
      · refine ⟨filled ++ [v], ?_, ?_, by simp; omega, rfl, sep_cast hmStored (by ac_rfl)⟩
        · apply congrArg (·, ())
          apply BitVec.eq_of_toNat_eq
          simp [BitVec.toNat_add, BitVec.toNat_ofNat]
        · rw [List.length_append, List.length_singleton, ← list_replicate_snoc, ← hrepl]
    · have hnotLt : ¬ ((BitVec.ofNat 64 filled.length).toNat < cntBv.toNat) := by assumption
      have hlenEq : filled.length = cntBv.toNat := by
        have hnot : ¬ ((BitVec.ofNat 64 filled.length).toNat < cntBv.toNat) := hnotLt
        rw [bv64_toNat_ofNat_lt (by omega)] at hnot
        omega
      have hfilledEq : filled = List.replicate cntBv.toNat v := by rw [hrepl, hlenEq]
      have hmArrDone : (cell64 arr arrHeaderWord ⋆
          cell64 (arr + 8#64) (BitVec.ofNat 64 cntBv.toNat) ⋆
          cell64 (arr + 16#64) (BitVec.ofNat 64 cntBv.toNat) ⋆
          array64 (arr + 24#64) (List.replicate cntBv.toNat v) ⋆
          region ((arr + 24#64) + BitVec.ofNat 64 (8 * (List.replicate cntBv.toNat v).length))
            (8 * (cntBv.toNat - (List.replicate cntBv.toNat v).length)) ⋆ R') mL := by
        have hbvCnt : BitVec.ofNat 64 cntBv.toNat = cntBv := by
          apply BitVec.eq_of_toNat_eq
          simp
        rw [← hfilledEq, hbvCnt]
        exact sep_cast hmL (by ac_rfl)
      exact hdone mL (mkArrObj_mem_of_filled (List.length_replicate) hmArrDone)
  · intro Jfill hJfill
    c0_steps
    have hz64 : BitVec.ofNat 64 0 = 0#64 := rfl
    exact hJfill cntBv.toNat (0#64, ()) mJ ⟨[], rfl, rfl, Nat.zero_le _, rfl, by
      rw [List.length_nil, Nat.mul_zero, hz64, BitVec.add_zero, Nat.sub_zero, array64_nil]
      have h0 : (Std.ExtHashMap.emp ⋆ (cell64 arr arrHeaderWord ⋆
          cell64 (arr + 8#64) cntBv ⋆ cell64 (arr + 16#64) cntBv ⋆
          region (arr + 24#64) (8 * cntBv.toNat) ⋆ R')) mJ := by
        rw [Std.ExtHashMap.emp_sep]; exact hmJ
      exact sep_cast h0 (by ac_rfl)⟩

private theorem bv64_sub1_toNat {cntBv : BitVec 64} (hcnt : 1 ≤ cntBv.toNat) :
    (cntBv - 1#64).toNat = cntBv.toNat - 1 := by
  rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by simpa using hcnt))]
  rfl

private theorem bv64_slack_toNat {rc : BitVec 32} (hrc : rc.toNat < 2147483648) :
    (2147483647#64 - BitVec.ofNat 64 rc.toNat).toNat = 2147483647 - rc.toNat := by
  have hle : BitVec.ofNat 64 rc.toNat ≤ 2147483647#64 := by
    rw [BitVec.le_def, bv64_toNat_ofNat_lt (by omega)]
    change rc.toNat ≤ (2147483647#64).toNat
    have hmax : (2147483647#64).toNat = 2147483647 := rfl
    omega
  rw [BitVec.toNat_sub_of_le hle, show (2147483647#64).toNat = 2147483647 from rfl,
    bv64_toNat_ofNat_lt (by omega)]

theorem lcnf_array_replicate_wp (xs : Tup Val [i64, i64, i64]) (m : Mem 64)
    (Q : Post [i64]) (X : XPost) :
    lcnfArrayReplicateSpec xs m Q X → Func.wp rtR2bEnv lcnf_array_replicate_body xs m Q X := by
  rcases xs with ⟨rt, n, v, ⟨⟩⟩
  intro hspec
  unfold lcnfArrayReplicateSpec at hspec
  dsimp only at hspec
  unfold lcnf_array_replicate_body Func.wp
  c0_steps
  · have hn0 : n &&& 1#64 = 0#64 := by assumption
    rw [ite_eq_left (Or.inl hn0)] at hspec
    exact hspec
  · have hbig : (33554428#64).toNat < (n >>> (1 : Nat)).toNat := by assumption
    have hbigNat : arrMaxCap < (n >>> (1 : Nat)).toNat := by
      have h33 : (33554428#64).toNat = 33554428 := rfl
      rw [h33] at hbig
      exact hbig
    rw [ite_eq_left (Or.inr hbigNat)] at hspec
    exact hspec
  · have hn0 : ¬ (n &&& 1#64 = 0#64) := by assumption
    let cntBv : BitVec 64 := n >>> (1 : Nat)
    let cnt : Nat := cntBv.toNat
    have hnotBig : ¬ (33554428 < cnt) := by
      have h1 : ¬ ((33554428#64).toNat < (n >>> (1 : Nat)).toNat) := by assumption
      simpa [cnt, cntBv, BitVec.toNat_ofNat] using h1
    have hleCap : cnt ≤ arrMaxCap := by simp only [arrMaxCap]; omega
    have hbadFalse : ¬ (n &&& 1#64 = 0#64 ∨ arrMaxCap < cnt) := by
      intro h
      rcases h with h0 | hgt
      · exact hn0 h0
      · simp only [arrMaxCap] at hleCap hgt; omega
    rw [show (n >>> 1).toNat = cnt from rfl] at hspec
    rw [ite_eq_right hbadFalse] at hspec
    rcases hspec with ⟨st, objs, R, hfree, hwf, h0pre, hgtpre, hm0, hpostSpec⟩
    have hcntLt : cnt < 2 ^ 64 := cntBv.isLt
    have hregLe : 8 * cnt ≤ 2 ^ 64 := by simp only [arrMaxCap] at hleCap; omega
    have hcanon : ∀ arr : BitVec 64, arr ≠ 0#64 → arr.toNat % 8 = 0 →
        ArrCanon (mkArrObj arr (1#32) cnt (List.replicate cnt v)) :=
      fun arr ha0 ha8 => mkArrObj_canon ha0 ha8 (by decide) (by simp) hleCap
    apply wp_call_of_spec
    apply rtR2bEnv_r2b_alloc_array
    dsimp only [r2bAllocArraySpec, vals, Arg.val_var]
    rw [show (n >>> 1).toNat = cnt from rfl]
    rw [ite_eq_left ⟨Nat.le_refl _, hleCap⟩]
    refine ⟨st, lcnfHeap objs ⋆ R, hfree, sep_cast hm0 (by ac_rfl),
      fun arr st1 m1 ha0 ha8 hpr1 hrem1 _ hm1 => ?_⟩
    change (rtC0Inv rt st1 ⋆ cell64 arr arrHeaderWord ⋆ cell64 (arr + 8#64) cntBv ⋆
      cell64 (arr + 16#64) cntBv ⋆ region (arr + 24#64) (8 * cnt) ⋆
      (lcnfHeap objs ⋆ R)) m1 at hm1
    c0_step
    c0_step
    · have hzeroBv : cntBv = 0#64 := by assumption
      have hcnt0 : cnt = 0 := by simp [cnt, hzeroBv]
      have hmArr0 : (rtC0Inv rt st1 ⋆ lcnfHeap objs ⋆
          (lcnfObjMem (mkArrObj arr (1#32) cnt (List.replicate cnt v)) ⋆ R)) m1 := by
        have hm1' : (cell64 arr arrHeaderWord ⋆ cell64 (arr + 8#64) (BitVec.ofNat 64 cnt) ⋆
            cell64 (arr + 16#64) (BitVec.ofNat 64 cnt) ⋆
            array64 (arr + 24#64) (List.replicate cnt v) ⋆
            region ((arr + 24#64) + BitVec.ofNat 64 (8 * (List.replicate cnt v).length))
              (8 * (cnt - (List.replicate cnt v).length)) ⋆
            (rtC0Inv rt st1 ⋆ lcnfHeap objs ⋆ R)) m1 := by
          rw [hcnt0, List.replicate_zero, array64_nil]
          have h0z : 8 * (0 - ([] : List (BitVec 64)).length) = 0 := rfl
          rw [h0z, region_zero]
          rw [show 8 * cnt = 0 by omega, region_zero, Std.ExtHashMap.sep_emp] at hm1
          rw [hzeroBv] at hm1
          have hE1 : (Std.ExtHashMap.emp ⋆ Std.ExtHashMap.emp ⋆
              (cell64 arr arrHeaderWord ⋆ cell64 (arr + 8#64) 0#64 ⋆
                cell64 (arr + 16#64) 0#64 ⋆ rtC0Inv rt st1 ⋆ lcnfHeap objs ⋆ R)) m1 := by
            rw [Std.ExtHashMap.emp_sep, Std.ExtHashMap.emp_sep]
            exact sep_cast hm1 (by ac_rfl)
          exact sep_cast hE1 (by ac_rfl)
        have hmObj := mkArrObj_mem_of_filled (List.length_replicate) hm1'
        exact sep_cast hmObj (by ac_rfl)
      c0_steps
      refine wp_call_r2b_dec_obj rt v hwf
        (fun himm => by
          have hv0 : v ≠ 0#64 := fun h => himm (Or.inl h)
          have hve : v &&& 1#64 = 0#64 := Classical.byContradiction fun hne => himm (Or.inr hne)
          obtain ⟨o, ho, hoa, hcls⟩ := h0pre ⟨hcnt0, hv0, hve⟩
          refine ⟨o, ho, hoa, fun hrc1 => ?_⟩
          have ⟨hwc, hlc, hrs⟩ := hcls hrc1
          rw [RtC0State.workCap_eq_of_preservesMeta hpr1]
          exact ⟨hwc, hlc, hrs⟩)
        hmArr0 fun st' objs' m' hpr' hrem' hdec' hm' => ?_
      c0_steps
      exact hpostSpec arr st' objs' m' ha0 ha8 (RtC0State.PreservesMeta.trans hpr1 hpr')
        (Nat.le_trans (Nat.le_of_eq hrem') hrem1) (hcanon arr ha0 ha8)
        (fun _ => hdec') (fun h1 => by omega) (fun hgt => by omega) (sep_cast hm' (by ac_rfl))
    · have hnzBv : cntBv ≠ 0#64 := by assumption
      have hcntPos : 1 ≤ cnt := Nat.pos_of_ne_zero fun h0 =>
        hnzBv (BitVec.eq_of_toNat_eq h0)
      let P_repl : Tup Val [] → Mem 64 → Prop := fun _ mJ =>
        ∃ stJ objsJ,
          stJ.PreservesMeta st ∧ stJ.rem ≤ st.rem ∧
          (cnt = 1 → objsJ = objs) ∧
          (1 < cnt →
            if v = 0#64 ∨ v &&& 1#64 ≠ 0#64 then objsJ = objs
            else ∃ o, o ∈ objs ∧ o.addr = v ∧
              if o.rc = 0#32 ∨ o.rc.toNat + (cnt - 1) ≤ 2147483647
              then objsJ = addRcObjList v (cnt - 1) objs
              else MarkPersistRel v objs objsJ) ∧
          (rtC0Inv rt stJ ⋆ cell64 arr arrHeaderWord ⋆ cell64 (arr + 8#64) cntBv ⋆
            cell64 (arr + 16#64) cntBv ⋆ region (arr + 24#64) (8 * cnt) ⋆
            lcnfHeap objsJ ⋆ R) mJ
      refine wp_join_group P_repl ?_ ?_
      · intro Jouter xs0 mJ hP
        rcases xs0 with ⟨⟩
        rcases hP with ⟨stJ, objsJ, hprJ, hremJ, h1J, hgtJ, hmJ⟩
        c0_steps
        exact array_replicate_fill_wp
          (R' := rtC0Inv rt stJ ⋆ lcnfHeap objsJ ⋆ R)
          hregLe (sep_cast hmJ (by ac_rfl)) fun mF hmF =>
          hpostSpec arr stJ objsJ mF ha0 ha8 hprJ hremJ (hcanon arr ha0 ha8)
            (fun h0 => by omega) h1J hgtJ (sep_cast hmF (by ac_rfl))
      · intro Jouter hJouter
        c0_steps
        · have hcntGt1 : 1 < cnt := by
            have hgt1 : (1#64).toNat < (n >>> (1 : Nat)).toNat := by assumption
            simpa [cnt, cntBv, BitVec.toNat_ofNat] using hgt1
          have hvNe0 : v ≠ 0#64 := by assumption
          have hve : v &&& 1#64 = 0#64 := by assumption
          obtain ⟨o, ho, hoa, hclsO⟩ := hgtpre ⟨hcntGt1, hvNe0, hve⟩
          have hnodup : (objs.map LcnfObj.addr).Nodup := lcnfHeap_nodup_addrs
            (sep_cast hm1 (by ac_rfl) : (lcnfHeap objs ⋆ (rtC0Inv rt st1 ⋆
              cell64 arr arrHeaderWord ⋆ cell64 (arr + 8#64) cntBv ⋆
              cell64 (arr + 16#64) cntBv ⋆ region (arr + 24#64) (8 * cnt) ⋆ R)) m1)
          obtain ⟨iO, hiO, heqO, hfocusO⟩ := lcnfHeap_focus_obj ho
          have hmLdHdr : (lcnfObjMem o ⋆ (lcnfHeap (objs.take iO) ⋆
              lcnfHeap (objs.drop (iO + 1)) ⋆ rtC0Inv rt st1 ⋆
              cell64 arr arrHeaderWord ⋆ cell64 (arr + 8#64) cntBv ⋆
              cell64 (arr + 16#64) cntBv ⋆ region (arr + 24#64) (8 * cnt) ⋆ R)) m1 := by
            rw [hfocusO] at hm1
            exact sep_cast hm1 (by ac_rfl)
          have hldHdr := r2_lcnfObjMem_load_header hmLdHdr
          rw [hoa] at hldHdr
          apply wp_load_of (v := o.header) (by simpa [Arg.val_var, lift2] using hldHdr)
          c0_step; c0_step
          rw [wp_jnz]
          dsimp only [Arg.val_var]
          refine ⟨fun hrcNe0B => ?_, fun hrcIs0B => ?_⟩
          · c0_step
            rw [wp_jnz]
            dsimp only [Arg.val_var]
            refine ⟨?_, ?_⟩
            · intro hule
              rw [BitVec.ule, decide_eq_true_eq] at hule
              have hrcNe0 : (o.header &&& 4294967295#64) ≠ 0#64 := by
                simpa [bne_iff_ne] using hrcNe0B
              rw [lcnfObjHeader_and_mask] at hrcNe0
              have hoRcNe : o.rc ≠ 0#32 := fun h0 => hrcNe0 (by simp [h0])
              have hoWf := hwf o ho
              have hoRcLt : o.rc.toNat < 2147483648 :=
                (bv32_toNat_of_nonneg o.rc hoWf.2.2.1).1
              have hmask : (4294967295 : BitVec 64) = 4294967295#64 := rfl
              have h1k : (1 : BitVec 64) = 1#64 := rfl
              have hmaxk : (2147483647 : BitVec 64) = 2147483647#64 := rfl
              have hcntEq : n >>> (1 : Nat) = cntBv := rfl
              rw [hmask, h1k, hmaxk, hcntEq, lcnfObjHeader_and_mask] at hule
              have hdeltaVal := bv64_sub1_toNat hcntPos
              have hslackVal := bv64_slack_toNat hoRcLt
              have hleAdd : o.rc.toNat + (cnt - 1) ≤ 2147483647 := by
                rw [hdeltaVal, hslackVal] at hule; omega
              obtain ⟨hstOk, hmSt1⟩ := lcnfObjMem_store_rc
                (o.rc + BitVec.ofNat 32 (cnt - 1)) hmLdHdr
              obtain ⟨hdrEq, _⟩ := lcnfObjHeader_add_nat o hoWf (cnt - 1) hleAdd
              have hdeltaBv : cntBv - 1#64 = BitVec.ofNat 64 (cnt - 1) := by
                apply BitVec.eq_of_toNat_eq
                rw [hdeltaVal, bv64_toNat_ofNat_lt (by omega)]
              have hvalEq : o.header + (cntBv - 1#64) =
                  (o.withRc (o.rc + BitVec.ofNat 32 (cnt - 1))).header := by
                rw [hdeltaBv]; exact hdrEq
              c0_let_simp
              rw [wp_store]
              simp only [Arg.val_var]
              rw [hoa] at hstOk
              refine ⟨hstOk, ?_⟩
              change wp rtR2bEnv Q X _ (storeMem m1 i64 v (o.header + (cntBv - 1#64)))
              rw [hvalEq]
              repeat c0_step
              have hmSt1' : (lcnfObjMem (o.withRc (o.rc + BitVec.ofNat 32 (cnt - 1))) ⋆
                  (lcnfHeap (objs.take iO) ⋆ lcnfHeap (objs.drop (iO + 1)) ⋆ rtC0Inv rt st1 ⋆
                    cell64 arr arrHeaderWord ⋆ cell64 (arr + 8#64) cntBv ⋆
                    cell64 (arr + 16#64) cntBv ⋆ region (arr + 24#64) (8 * cnt) ⋆ R))
                  (storeMem m1 i64 v (o.withRc (o.rc + BitVec.ofNat 32 (cnt - 1))).header) := by
                rw [← hoa]; exact hmSt1
              have hmHeapSet : (lcnfHeap (objs.set iO
                  (o.withRc (o.rc + BitVec.ofNat 32 (cnt - 1)))) ⋆
                  (rtC0Inv rt st1 ⋆ cell64 arr arrHeaderWord ⋆
                    cell64 (arr + 8#64) cntBv ⋆ cell64 (arr + 16#64) cntBv ⋆
                    region (arr + 24#64) (8 * cnt) ⋆ R))
                  (storeMem m1 i64 v (o.withRc (o.rc + BitVec.ofNat 32 (cnt - 1))).header) := by
                apply lcnfHeap_set_focus hiO
                exact sep_cast hmSt1' (by ac_rfl)
              have haddEq := addRcObjList_eq_set hnodup hiO (heqO ▸ hoRcNe) (cnt - 1)
              rw [heqO, hoa] at haddEq
              rw [← haddEq] at hmHeapSet
              refine hJouter () _ ⟨st1, addRcObjList v (cnt - 1) objs, hpr1, hrem1,
                fun h1 => by omega, fun _ => ?_, sep_cast hmHeapSet (by ac_rfl)⟩
              rw [ite_eq_right (by simp [hvNe0, hve])]
              exact ⟨o, ho, hoa, by rw [ite_eq_left (Or.inr hleAdd)]⟩
            · intro huleFalse
              rw [BitVec.ule, decide_eq_false_iff_not] at huleFalse
              have hrcNe0 : (o.header &&& 4294967295#64) ≠ 0#64 := by
                simpa [bne_iff_ne] using hrcNe0B
              rw [lcnfObjHeader_and_mask] at hrcNe0
              have hoRcNe : o.rc ≠ 0#32 := fun h0 => hrcNe0 (by simp [h0])
              have hoWf := hwf o ho
              have hoRcLt : o.rc.toNat < 2147483648 :=
                (bv32_toNat_of_nonneg o.rc hoWf.2.2.1).1
              have hmask : (4294967295 : BitVec 64) = 4294967295#64 := rfl
              have h1k : (1 : BitVec 64) = 1#64 := rfl
              have hmaxk : (2147483647 : BitVec 64) = 2147483647#64 := rfl
              have hcntEq : n >>> (1 : Nat) = cntBv := rfl
              rw [hmask, h1k, hmaxk, hcntEq, lcnfObjHeader_and_mask] at huleFalse
              have hdeltaVal := bv64_sub1_toNat hcntPos
              have hslackVal := bv64_slack_toNat hoRcLt
              have hgtOverflow : 2147483647 - o.rc.toNat < cnt - 1 := by
                rw [hdeltaVal, hslackVal] at huleFalse; omega
              obtain ⟨hlenWc, hlc⟩ := hclsO ⟨hoRcNe, hgtOverflow⟩
              rw [← RtC0State.workCap_eq_of_preservesMeta hpr1] at hlenWc
              apply wp_call_of_spec
              apply rtR2bEnv_lcnf_mark_persistent
              dsimp only [lcnfMarkPersistentSpec, vals, Arg.val_var]
              rw [ite_eq_right (by simp [hve])]
              refine ⟨st1, objs, cell64 arr arrHeaderWord ⋆
                  cell64 (arr + 8#64) cntBv ⋆ cell64 (arr + 16#64) cntBv ⋆
                  region (arr + 24#64) (8 * cnt) ⋆ R,
                hlenWc, sep_cast hm1 (by ac_rfl), ⟨o, ho, hoa⟩, hwf, hlc,
                fun st2 objs2 m2 hpr2 hrem2 hmark hm2 => ?_⟩
              repeat c0_step
              refine hJouter () _ ⟨st2, objs2, RtC0State.PreservesMeta.trans hpr1 hpr2,
                Nat.le_trans (Nat.le_of_eq hrem2) hrem1, fun h1 => by omega,
                fun _ => ?_, sep_cast hm2 (by ac_rfl)⟩
              rw [ite_eq_right (by simp [hvNe0, hve])]
              exact ⟨o, ho, hoa, by
                rw [ite_eq_right (fun hc => by
                  rcases hc with h0 | hle
                  · exact hoRcNe h0
                  · omega)]
                exact hmark⟩
          · c0_steps
            have hrcIs0 : (o.header &&& 4294967295#64) = 0#64 := by
              have h1 : (o.header &&& 4294967295#64 != 0#64) = false := by
                simpa using hrcIs0B
              simpa [bne_iff_ne] using h1
            rw [lcnfObjHeader_and_mask] at hrcIs0
            have hoWf := hwf o ho
            have hoRcLt : o.rc.toNat < 2147483648 :=
              (bv32_toNat_of_nonneg o.rc hoWf.2.2.1).1
            have hoRc0 : o.rc = 0#32 := by
              apply BitVec.eq_of_toNat_eq
              have h1 : (BitVec.ofNat 64 o.rc.toNat).toNat = 0 := by rw [hrcIs0]; rfl
              rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h1
              exact h1
            have hadd0 := addRcObjList_of_rc_zero hnodup ho hoa hoRc0 (cnt - 1)
            refine hJouter () _ ⟨st1, objs, hpr1, hrem1, fun h1 => by omega, fun _ => ?_,
              sep_cast hm1 (by ac_rfl)⟩
            rw [ite_eq_right (by simp [hvNe0, hve])]
            refine ⟨o, ho, hoa, ?_⟩
            rw [ite_eq_left (Or.inl hoRc0)]
            exact hadd0.symm
        · have hoddV : ¬ (v &&& 1#64 = 0#64) := by assumption
          have hcntGt1 : 1 < cnt := by
            simpa [cnt, cntBv, BitVec.toNat_ofNat] using
              (by assumption : (1#64).toNat < (n >>> (1 : Nat)).toNat)
          refine hJouter () _ ⟨st1, objs, hpr1, hrem1, fun h1 => by omega,
            fun _ => by rw [ite_eq_left (Or.inr hoddV)], sep_cast hm1 (by ac_rfl)⟩
        · have hv0 : v = 0#64 := by assumption
          have hcntGt1 : 1 < cnt := by
            simpa [cnt, cntBv, BitVec.toNat_ofNat] using
              (by assumption : (1#64).toNat < (n >>> (1 : Nat)).toNat)
          refine hJouter () _ ⟨st1, objs, hpr1, hrem1, fun h1 => by omega,
            fun _ => by simp [hv0], sep_cast hm1 (by ac_rfl)⟩
        · have hnotGt1 : ¬ ((1#64).toNat < (n >>> (1 : Nat)).toNat) := by assumption
          have hcnt1 : cnt = 1 := by
            have hnot : ¬ (1 < cnt) := by simpa [cnt, cntBv, BitVec.toNat_ofNat] using hnotGt1
            omega
          exact hJouter () _ ⟨st1, objs, hpr1, hrem1, fun _ => rfl, fun hgt => by omega,
            sep_cast hm1 (by ac_rfl)⟩

end LeanQbe.T.LeanLCNF
