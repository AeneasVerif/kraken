module

public import LeanQbe.T.LeanLCNF.LcnfC0ContainersProof1
import all Kraken.Separation

/-!
# Soundness Proofs for `LcnfC0Containers`, Part 3: `Array` (`tag 246`)

Proves `Func.wp` contracts against `rtR2Env` for all `Array` runtime helpers and primitives:
- `r2_alloc_array` (`r2_alloc_array_wp`)
- `r2_ensure_excl_array` (`r2_ensure_excl_array_wp`)
- `lcnf_array_mk_empty` (`lcnf_array_mk_empty_wp`)
- `lcnf_array_get` (`lcnf_array_get_wp`)
- `lcnf_array_set` (`lcnf_array_set_wp`)
- `lcnf_array_push` (`lcnf_array_push_wp`)
- `lcnf_array_pop` (`lcnf_array_pop_wp`)
- `lcnf_array_swap` (`lcnf_array_swap_wp`)
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.LeanLCNF

open Std.ExtHashMap

/-! ## 1. `Array` Memory, Layout, and Child-RC Helper Lemmas -/

private theorem arr_align8_allocBytes (n : Nat) : align8 (arrAllocBytes n) = arrAllocBytes n := by
  unfold arrAllocBytes align8
  omega

private theorem arr_allocBytes_fit {cap : BitVec 64} (h : cap.toNat ≤ arrMaxCap) :
    ((24 : BitVec 64) + 8#64 * cap).toNat = arrAllocBytes cap.toNat ∧
      arrAllocBytes cap.toNat ≤ 268435448 := by
  unfold arrMaxCap at h
  unfold arrAllocBytes
  have hlt : 24 + 8 * cap.toNat ≤ 268435448 := by omega
  have hbv : ((24 : BitVec 64) + 8#64 * cap).toNat = 24 + 8 * cap.toNat := by
    rw [BitVec.toNat_add, BitVec.toNat_mul]
    have h24 : (24 : BitVec 64).toNat = 24 := rfl
    have h8 : (8#64 : BitVec 64).toNat = 8 := rfl
    rw [h24, h8]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  exact ⟨hbv, hlt⟩

private theorem mkArrObj_totalBytes (p : BitVec 64) (rc : BitVec 32) {cap : Nat}
    (elems : List (BitVec 64)) : (mkArrObj p rc cap elems).totalBytes = arrAllocBytes cap := by
  unfold LcnfObj.totalBytes mkArrObj arrAllocBytes
  simp [arrayTag]

private theorem lcnfObjMem_array_elim {o : LcnfObj} (h : ArrCanon o) {R : Mem 64 → Prop}
    {m : Mem 64} (hm : (lcnfObjMem o ⋆ R) m) :
    (cell64 o.addr o.header ⋆
      cell64 (o.addr + 8#64) (BitVec.ofNat 64 o.fields.length) ⋆
      cell64 (o.addr + 16#64) (BitVec.ofNat 64 o.cap) ⋆
      array64 (o.addr + 24#64) o.fields ⋆
      region (o.addr + BitVec.ofNat 64 (24 + 8 * o.fields.length))
        (8 * (o.cap - o.fields.length)) ⋆ R) m := by
  rw [lcnfObjMem_array_eq h.2.2.2.2.2.1] at hm
  exact sep_cast hm (by ac_rfl)

private theorem mkArrObj_mem_of_parts {p : BitVec 64} {rc : BitVec 32} {cap : Nat}
    {elems : List (BitVec 64)} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (cell64 p (mkArrObj p rc cap elems).header ⋆
        cell64 (p + 8#64) (BitVec.ofNat 64 elems.length) ⋆
        cell64 (p + 16#64) (BitVec.ofNat 64 cap) ⋆
        array64 (p + 24#64) elems ⋆
        region (p + BitVec.ofNat 64 (24 + 8 * elems.length)) (8 * (cap - elems.length)) ⋆ R) m) :
    (lcnfObjMem (mkArrObj p rc cap elems) ⋆ R) m := by
  have htag : (mkArrObj p rc cap elems).tag = arrayTag := rfl
  rw [lcnfObjMem_array_eq htag]
  exact sep_cast hm (by ac_rfl)

private theorem arr_load_sz_mid {o : LcnfObj} (h : ArrCanon o) {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (lcnfObjMem o ⋆ R) m) :
    loadVal m i64 (o.addr + 8#64) = some (BitVec.ofNat 64 o.fields.length) := by
  have hs := lcnfObjMem_array_elim h hm
  have hs' : (cell64 (o.addr + 8#64) (BitVec.ofNat 64 o.fields.length) ⋆
      (cell64 o.addr o.header ⋆ cell64 (o.addr + 16#64) (BitVec.ofNat 64 o.cap) ⋆
        array64 (o.addr + 24#64) o.fields ⋆
        region (o.addr + BitVec.ofNat 64 (24 + 8 * o.fields.length))
          (8 * (o.cap - o.fields.length)) ⋆ R)) m := sep_cast hs (by ac_rfl)
  exact r2_c0_load_cell64_add8 hs'

private theorem arr_load_cap_mid {o : LcnfObj} (h : ArrCanon o) {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (lcnfObjMem o ⋆ R) m) :
    loadVal m i64 (o.addr + 16#64) = some (BitVec.ofNat 64 o.cap) := by
  have hs := lcnfObjMem_array_elim h hm
  have hs' : (cell64 (o.addr + 16#64) (BitVec.ofNat 64 o.cap) ⋆
      (cell64 o.addr o.header ⋆ cell64 (o.addr + 8#64) (BitVec.ofNat 64 o.fields.length) ⋆
        array64 (o.addr + 24#64) o.fields ⋆
        region (o.addr + BitVec.ofNat 64 (24 + 8 * o.fields.length))
          (8 * (o.cap - o.fields.length)) ⋆ R)) m := sep_cast hs (by ac_rfl)
  exact r2_c0_load_cell64_add16 hs'

private theorem arr_load_elem_mid {o : LcnfObj} {i : BitVec 64} (h : ArrCanon o)
    (hi : i.toNat < o.fields.length) {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (lcnfObjMem o ⋆ R) m) :
    loadVal m i64 (o.addr + 24#64 + 8#64 * i) = some o.fields[i.toNat] := by
  have hs := lcnfObjMem_array_elim h hm
  have hs' : (array64 (o.addr + 24#64) o.fields ⋆
      (cell64 o.addr o.header ⋆ cell64 (o.addr + 8#64) (BitVec.ofNat 64 o.fields.length) ⋆
        cell64 (o.addr + 16#64) (BitVec.ofNat 64 o.cap) ⋆
        region (o.addr + BitVec.ofNat 64 (24 + 8 * o.fields.length))
          (8 * (o.cap - o.fields.length)) ⋆ R)) m := sep_cast hs (by ac_rfl)
  exact r2_c0_load_array64_add24_mul8 hs' hi

private theorem arr_rc_of_mask_eq1 {o : LcnfObj} (hwf : o.Wf)
    (hm : o.header &&& 4294967295#64 = 1#64) : o.rc = 1#32 := by
  have hrc := LcnfObj.header_rc o hwf.2.2.2.1 hwf.2.2.2.2.1 hwf.2.2.2.2.2.1
  rw [hm] at hrc
  have h1 := congrArg BitVec.toNat hrc
  have h1l : (1#64 : BitVec 64).toNat = 1 := rfl
  rw [h1l, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans o.rc.isLt (by decide))] at h1
  exact BitVec.eq_of_toNat_eq (by simp [← h1])

private theorem arr_rc_ne1_of_mask {o : LcnfObj} (hwf : o.Wf)
    (hm : o.header &&& 4294967295#64 ≠ 1#64) : o.rc ≠ 1#32 :=
  fun h1 => hm (by
    rw [LcnfObj.header_rc o hwf.2.2.2.1 hwf.2.2.2.2.1 hwf.2.2.2.2.2.1, h1]
    rfl)

private theorem ptr_add_24_mul8 (p : BitVec 64) (n : Nat) :
    p + 24#64 + BitVec.ofNat 64 (8 * n) = p + BitVec.ofNat 64 (24 + 8 * n) := by
  rw [BitVec.add_assoc]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add, BitVec.toNat_ofNat]

private theorem region_split_cell64 {a : BitVec 64} {n : Nat} (hn : 8 ≤ n) (hfit : n ≤ 2 ^ 64)
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (region a n ⋆ R) m) :
    ∃ w, (cell64 a w ⋆ region (a + 8#64) (n - 8) ⋆ R) m := by
  have hsplit : region a n = region a 8 ⋆ region (a + 8#64) (n - 8) := by
    have hs := @region_split a 8 (n - 8) (by omega)
    rw [show 8 + (n - 8) = n by omega] at hs
    exact hs
  rw [hsplit] at hm
  have hm' : (region a 8 ⋆ (region (a + 8#64) (n - 8) ⋆ R)) m := sep_cast hm (by ac_rfl)
  obtain ⟨m1, m2, hu, hd, hr1, hr2⟩ := hm'
  obtain ⟨w, hw⟩ := region_to_cell64 hr1
  have hres : (cell64 a w ⋆ (region (a + 8#64) (n - 8) ⋆ R)) m := ⟨m1, m2, hu, hd, hw, hr2⟩
  exact ⟨w, sep_cast hres (by ac_rfl)⟩

private theorem cell64_merge_region {a v : BitVec 64} {n : Nat} (hfit : 8 + n ≤ 2 ^ 64)
    {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (cell64 a v ⋆ region (a + 8#64) n ⋆ R) m) :
    (region a (8 + n) ⋆ R) m := by
  have hm' : (cell64 a v ⋆ (region (a + 8#64) n ⋆ R)) m := sep_cast hm (by ac_rfl)
  obtain ⟨m1, m2, hu, hd, hcell, hrest⟩ := hm'
  have hr : (region a 8 ⋆ (region (a + 8#64) n ⋆ R)) m :=
    ⟨m1, m2, hu, hd, cell64_to_region hcell, hrest⟩
  have hr' : ((region a 8 ⋆ region (a + 8#64) n) ⋆ R) m := sep_cast hr (by ac_rfl)
  rw [← @region_split a 8 n hfit] at hr'
  exact hr'

private theorem lcnfHeap_insertIdx {xs : List LcnfObj} {k : Nat} (hk : k ≤ xs.length)
    (x : LcnfObj) :
    lcnfHeap (xs.insertIdx k x) = lcnfObjMem x ⋆ lcnfHeap xs := by
  induction k generalizing xs with
  | zero => simp [List.insertIdx, lcnfHeap]
  | succ k ih =>
    cases xs with
    | nil => simp at hk
    | cons y ys =>
      simp only [List.length_cons, Nat.succ_le_succ_iff] at hk
      simp only [List.insertIdx_succ_cons, lcnfHeap, ih hk]
      ac_rfl

private theorem mem_of_mem_eraseIdx_arr {α : Type _} {xs : List α} {i : Nat} {a : α}
    (h : a ∈ xs.eraseIdx i) : a ∈ xs := by
  rw [List.eraseIdx_eq_take_drop_succ] at h
  rcases List.mem_append.mp h with ht | hd
  · exact List.mem_of_mem_take ht
  · exact List.mem_of_mem_drop hd

private theorem eraseIdx_set_eq_self {α : Type _} (xs : List α) {j : Nat} (a : α) :
    (xs.set j a).eraseIdx j = xs.eraseIdx j := by
  induction xs generalizing j with
  | nil => simp
  | cons x xs ih =>
    cases j with
    | zero => simp
    | succ j => simp [List.set, List.eraseIdx_cons_succ, ih]

private theorem mem_eraseIdx_of_addr_ne {objs : List LcnfObj} {k : Nat} (hk : k < objs.length)
    {y : LcnfObj} (hy : y ∈ objs) (hne : y.addr ≠ objs[k].addr) :
    y ∈ objs.eraseIdx k := by
  obtain ⟨jy, hjyLen, hjyEq⟩ := List.getElem_of_mem hy
  have hneIdx : jy ≠ k := fun h => hne (by subst h; rw [← hjyEq])
  have hmem : y ∈ objs.take k ++ objs.drop (k + 1) := by
    rcases Nat.lt_trichotomy jy k with hlt | heq | hgt
    · exact List.mem_append_left _ (by
        rw [← hjyEq]; exact List.mem_take_iff_getElem.mpr ⟨jy, by omega, rfl⟩)
    · exact absurd heq hneIdx
    · exact List.mem_append_right _ (by
        rw [← hjyEq, List.mem_drop_iff_getElem]
        exact ⟨jy - (k + 1), by omega, by congr 1; omega⟩)
  simpa [List.eraseIdx_eq_take_drop_succ] using hmem

private theorem list_set_eq_map_of_nodup {objs : List LcnfObj}
    (hnodup : (objs.map LcnfObj.addr).Nodup) {j : Nat} (hj : j < objs.length)
    (fn : LcnfObj → LcnfObj) :
    objs.set j (fn objs[j]) =
      objs.map (fun o => if o.addr = objs[j].addr then fn o else o) := by
  apply List.ext_getElem
  · simp
  · intro i hi1 hi2
    have hi : i < objs.length := by simpa using hi1
    simp only [List.getElem_set, List.getElem_map]
    split
    · rename_i heq
      subst heq
      simp
    · rename_i hne
      have had : objs[i].addr ≠ objs[j].addr := by
        intro heqa
        have hi' : i < (objs.map LcnfObj.addr).length := by simp [hi]
        have hj' : j < (objs.map LcnfObj.addr).length := by simp [hj]
        have heq := (hnodup.getElem_inj (i := i) (j := j) (hi := hi') (hj := hj')).mp
          (by rw [List.getElem_map, List.getElem_map]; exact heqa)
        exact hne heq.symm
      simp [had]

private theorem ArrCanon.cap_lt_64 {o : LcnfObj} (h : ArrCanon o) : o.cap < 2 ^ 64 := by
  have := h.2.2.2.2.2.2.2; unfold arrMaxCap at this; omega

private theorem ArrCanon.len_lt_64 {o : LcnfObj} (h : ArrCanon o) :
    o.fields.length < 2 ^ 64 := by
  have := h.2.2.2.2.2.2.1; have := h.cap_lt_64; omega

private theorem arr_wf_rc_bounds {o : LcnfObj} (hwf : o.Wf) (hrc : 0 < o.rc.toInt) :
    1 ≤ o.rc.toNat ∧ o.rc.toNat < 2147483648 := by
  have h1 := hwf.2.2.1
  rw [BitVec.toInt_eq_toNat_cond] at hrc h1
  split at hrc <;> omega

private theorem withRc_self (o : LcnfObj) : o.withRc o.rc = o := by
  cases o; rfl

private theorem incChildrenObjs_nil (childObjs : List LcnfObj)
    (hwf : ∀ y ∈ childObjs, y.Wf) :
    incChildrenObjs [] childObjs = childObjs := by
  unfold incChildrenObjs
  induction childObjs with
  | nil => rfl
  | cons y ys ih =>
    simp only [List.map_cons]
    congr 1
    · by_cases hpos : 0 < y.rc.toInt
      · simp only [hpos, ↓reduceIte, List.count_nil, Nat.add_zero]
        have hlt31 : y.rc.toNat < 2147483648 := by
          have h0 := (hwf y (List.mem_cons_self ..)).2.2.1
          rw [BitVec.toInt_eq_toNat_cond] at hpos h0
          split at hpos <;> omega
        have hbv : BitVec.ofNat 32 y.rc.toNat = y.rc := by
          apply BitVec.eq_of_toNat_eq
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        rw [hbv, withRc_self]
      · simp only [hpos, ↓reduceIte]
    · exact ih (fun z hz => hwf z (List.mem_cons_of_mem y hz))

private theorem arrObj_wf_decNonExclRc {o : LcnfObj} (hwf : o.Wf) (hne1 : o.rc ≠ 1#32) :
    (o.withRc (decNonExclRc o.rc)).Wf := by
  rcases hwf with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, htag⟩
  by_cases hgt : (1 : Int) < o.rc.toInt
  · simp only [decNonExclRc, hgt, ↓reduceIte]
    have hnat := arr_wf_rc_bounds ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, htag⟩ (by omega)
    have hge2 : 2 ≤ o.rc.toNat := by
      have hne1n : o.rc.toNat ≠ 1 := fun h => hne1 (BitVec.eq_of_toNat_eq (by simpa using h))
      omega
    have hsub : (o.rc - 1#32).toNat = o.rc.toNat - 1 := by
      rw [BitVec.toNat_sub_of_le (by show 1 ≤ o.rc.toNat; omega)]
      rfl
    have hint : (o.rc - 1#32).toInt = (o.rc.toNat - 1 : Int) := by
      rw [BitVec.toInt_eq_toNat_cond, hsub]; split <;> omega
    refine ⟨h1, h2, ?_, h4, h5, h6, h7, h8, h9, ?_⟩
    · simp [LcnfObj.withRc, hint]; omega
    · dsimp only [LcnfObj.withRc]; exact htag
  · simp only [decNonExclRc, hgt, ↓reduceIte]
    have h0 : o.rc.toInt = 0 := by
      by_cases h1eq : o.rc.toInt = 1
      · exfalso
        rw [BitVec.toInt_eq_toNat_cond] at h1eq
        have hrcNat1 : o.rc.toNat = 1 := by split at h1eq <;> omega
        exact hne1 (BitVec.eq_of_toNat_eq (by simpa using hrcNat1))
      · omega
    refine ⟨h1, h2, ?_, h4, h5, h6, h7, h8, h9, ?_⟩
    · dsimp only [LcnfObj.withRc]; exact h3
    · dsimp only [LcnfObj.withRc]; exact htag

private theorem count_take_le {α : Type _} [BEq α] (a : α) (xs : List α) (i : Nat) :
    List.count a (xs.take i) ≤ List.count a xs := by
  have hsp : xs.take i ++ xs.drop i = xs := List.take_append_drop i xs
  have hcnt := congrArg (List.count a) hsp
  rw [List.count_append] at hcnt
  omega

private theorem count_take_succ_eq {α : Type _} [BEq α] [LawfulBEq α] (a : α) (xs : List α)
    {i : Nat} (hi : i < xs.length) :
    List.count a (xs.take (i + 1)) =
      List.count a (xs.take i) + if xs[i] == a then 1 else 0 := by
  rw [List.take_succ_eq_append_getElem hi, List.count_append, List.count_singleton]

private theorem incChildrenObjs_wf {fields : List (BitVec 64)} {childObjs : List LcnfObj}
    (hwf : ∀ y ∈ childObjs, y.Wf)
    (hbound : ∀ y ∈ childObjs, 0 < y.rc.toInt →
      y.rc.toInt + (List.count y.addr fields : Int) < 2147483648)
    (i : Nat) :
    ∀ z ∈ incChildrenObjs (fields.take i) childObjs, z.Wf := by
  intro z hz
  simp only [incChildrenObjs, List.mem_map] at hz
  rcases hz with ⟨y, hy, rfl⟩
  have hyWf := hwf y hy
  by_cases hpos : 0 < y.rc.toInt
  · simp only [hpos, ↓reduceIte]
    have hb := hbound y hy hpos
    have hc := count_take_le y.addr fields i
    have hnat := arr_wf_rc_bounds hyWf hpos
    have hyInt : y.rc.toInt = (y.rc.toNat : Int) := by
      rw [BitVec.toInt_eq_toNat_cond]; split <;> omega
    have hsumLt : y.rc.toNat + List.count y.addr (fields.take i) < 2147483648 := by omega
    have hbv : (BitVec.ofNat 32 (y.rc.toNat + List.count y.addr (fields.take i))).toInt =
        (y.rc.toNat + List.count y.addr (fields.take i) : Int) := by
      rw [BitVec.toInt_eq_toNat_cond, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      split <;> omega
    rcases hyWf with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, htag⟩
    refine ⟨h1, h2, ?_, h4, h5, h6, h7, h8, h9, ?_⟩
    · dsimp only [LcnfObj.withRc]; omega
    · dsimp only [LcnfObj.withRc]; exact htag
  · simp only [hpos, ↓reduceIte]; exact hyWf

private theorem incChildrenObjs_step_skip {fields : List (BitVec 64)}
    {childObjs : List LcnfObj} (hwf : ∀ y ∈ childObjs, y.Wf) {i : Nat} (hi : i < fields.length)
    (hskip : fields[i] = 0#64 ∨ (fields[i] &&& 1#64) ≠ 0#64) :
    incChildrenObjs (fields.take (i + 1)) childObjs =
      incChildrenObjs (fields.take i) childObjs := by
  unfold incChildrenObjs
  apply List.map_congr_left
  intro y hy
  have hyWf := hwf y hy
  have hne : fields[i] ≠ y.addr := by
    intro heq
    rw [heq] at hskip
    rcases hskip with h0 | h1
    · exact hyWf.1 h0
    · exact h1 (bv64_and1_zero_of_mod8 hyWf.2.1)
  have hbeq : (fields[i] == y.addr) = false := beq_false_of_ne hne
  rw [count_take_succ_eq y.addr fields hi, hbeq]
  simp

private theorem incChildrenObjs_step_hit {fields : List (BitVec 64)} {childObjs : List LcnfObj}
    (hwf : ∀ y ∈ childObjs, y.Wf)
    (hnodup : (childObjs.map LcnfObj.addr).Nodup)
    (hbound : ∀ y ∈ childObjs, 0 < y.rc.toInt →
      y.rc.toInt + (List.count y.addr fields : Int) < 2147483648)
    {i j : Nat} (hi : i < fields.length) (hj : j < childObjs.length)
    (haddr : childObjs[j].addr = fields[i]) :
    let cur := incChildrenObjs (fields.take i) childObjs
    have hjCur : j < cur.length := by simpa [cur, incChildrenObjs] using hj
    cur.set j (cur[j].withRc (incRcVal cur[j].rc)) =
      incChildrenObjs (fields.take (i + 1)) childObjs := by
  intro cur hjCur
  apply List.ext_getElem
  · simp [cur, incChildrenObjs]
  · intro m hm1 hm2
    have hm : m < childObjs.length := by simpa [cur, incChildrenObjs] using hm1
    simp only [cur, List.getElem_set, incChildrenObjs, List.getElem_map]
    split
    · rename_i hmj
      subst hmj
      have hyWf := hwf childObjs[j] (List.getElem_mem hj)
      by_cases hpos : 0 < childObjs[j].rc.toInt
      · have hnat := arr_wf_rc_bounds hyWf hpos
        have hb := hbound childObjs[j] (List.getElem_mem hj) hpos
        have hcnt1 := count_take_succ_eq childObjs[j].addr fields hi
        have hbeq : (fields[i] == childObjs[j].addr) = true := beq_iff_eq.mpr haddr.symm
        rw [hbeq] at hcnt1
        have hcle := count_take_le childObjs[j].addr fields (i + 1)
        have hyInt : childObjs[j].rc.toInt = (childObjs[j].rc.toNat : Int) := by
          rw [BitVec.toInt_eq_toNat_cond]; split <;> omega
        have hlt231 : childObjs[j].rc.toNat + List.count childObjs[j].addr (fields.take (i + 1)) <
            2147483648 := by omega
        have hprevLt : childObjs[j].rc.toNat + List.count childObjs[j].addr (fields.take i) <
            2147483647 := by simp at hcnt1; omega
        simp only [hpos, ↓reduceIte, hcnt1]
        have hbvPos : 0 < (BitVec.ofNat 32
            (childObjs[j].rc.toNat + List.count childObjs[j].addr (fields.take i))).toInt := by
          rw [BitVec.toInt_eq_toNat_cond, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
          split <;> omega
        have hbvLt : (BitVec.ofNat 32
            (childObjs[j].rc.toNat + List.count childObjs[j].addr (fields.take i))).toInt <
            2147483647 := by
          rw [BitVec.toInt_eq_toNat_cond, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
          split <;> omega
        dsimp only [incRcVal, LcnfObj.withRc]
        rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨hbvPos, hbvLt⟩)]
        congr 1
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
        have hmA : childObjs[j].rc.toNat +
            List.count childObjs[j].addr (fields.take i) < 2 ^ 32 := by omega
        have hmB : (1 : Nat) < 2 ^ 32 := by decide
        have hmC : (childObjs[j].rc.toNat +
            List.count childObjs[j].addr (fields.take i)) + 1 < 2 ^ 32 := by omega
        have hmD : childObjs[j].rc.toNat +
            (List.count childObjs[j].addr (fields.take i) + 1) < 2 ^ 32 := by omega
        rw [Nat.mod_eq_of_lt hmA, Nat.mod_eq_of_lt hmB,
          Nat.mod_eq_of_lt hmC, Nat.mod_eq_of_lt hmD]
        omega
      · have h0 : childObjs[j].rc.toInt = 0 := by have := hyWf.2.2.1; omega
        have hrc0 : childObjs[j].rc = 0#32 := by
          apply BitVec.eq_of_toNat_eq
          have hlt32 := childObjs[j].rc.isLt
          rw [BitVec.toInt_eq_toNat_cond] at h0
          split at h0 <;> simp at * <;> omega
        simp only [hpos, false_and, ↓reduceIte, incRcVal, withRc_self]
    · rename_i hne
      have had : childObjs[m].addr ≠ childObjs[j].addr := by
        intro heqa
        have hm' : m < (childObjs.map LcnfObj.addr).length := by simp [hm]
        have hj' : j < (childObjs.map LcnfObj.addr).length := by simp [hj]
        have heq := (hnodup.getElem_inj (i := m) (j := j) (hi := hm') (hj := hj')).mp
          (by rw [List.getElem_map, List.getElem_map]; exact heqa)
        exact hne heq.symm
      have hne2 : fields[i] ≠ childObjs[m].addr := by rw [← haddr]; exact had.symm
      have hbeq : (fields[i] == childObjs[m].addr) = false := beq_false_of_ne hne2
      rw [count_take_succ_eq childObjs[m].addr fields hi, hbeq]
      simp

private theorem incChildrenObjs_rc_ne_one {fields : List (BitVec 64)} {childObjs : List LcnfObj}
    (hwf : ∀ y ∈ childObjs, y.Wf)
    (hbound : ∀ y ∈ childObjs, 0 < y.rc.toInt →
      y.rc.toInt + (List.count y.addr fields : Int) < 2147483648)
    {v : BitVec 64} (hvMem : v ∈ fields) {z : LcnfObj}
    (hzMem : z ∈ incChildrenObjs fields childObjs) (hzAddr : z.addr = v) : z.rc ≠ 1#32 := by
  simp only [incChildrenObjs, List.mem_map] at hzMem
  rcases hzMem with ⟨y, hy, rfl⟩
  have hyWf := hwf y hy
  by_cases hpos : 0 < y.rc.toInt
  · simp only [hpos, ↓reduceIte, LcnfObj.withRc] at hzAddr ⊢
    have hnat := arr_wf_rc_bounds hyWf hpos
    have hb := hbound y hy hpos
    have hyInt : y.rc.toInt = (y.rc.toNat : Int) := by
      rw [BitVec.toInt_eq_toNat_cond]; split <;> omega
    have hcntPos : 1 ≤ List.count y.addr fields :=
      Nat.succ_le_of_lt (List.count_pos_iff.mpr (hzAddr ▸ hvMem))
    have hlt231 : y.rc.toNat + List.count y.addr fields < 2147483648 := by omega
    intro h1
    have h1n := congrArg BitVec.toNat h1
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h1n
    have h1r : (1#32 : BitVec 32).toNat = 1 := rfl
    omega
  · simp only [hpos, ↓reduceIte]
    intro h1
    have h0 : y.rc.toInt = 0 := by have := hyWf.2.2.1; omega
    rw [h1] at h0; revert h0; decide

private theorem arr_cow_closed_bound {arrObj : LcnfObj} {objs : List LcnfObj} {k : Nat}
    (hk : k < objs.length) (hobj : objs[k] = arrObj) (hcanon : ArrCanon arrObj)
    (hnotSelf : ¬ arrObj.addr ∈ arrObj.fields) (hclosed : lcnfHeapClosed objs) :
    ∀ f ∈ arrObj.fields, (f &&& 1#64) = 0#64 → ∃ y ∈ objs.eraseIdx k, y.addr = f := by
  intro f hfMem hf0
  have hcf : f ∈ arrObj.childFields := by
    simp only [LcnfObj.childFields, hcanon.2.2.2.2.2.1]
    simp [hfMem]
  obtain ⟨y, hyMem, hyAddr⟩ := hclosed arrObj (hobj ▸ List.getElem_mem hk) f hcf hf0
  have hne : y.addr ≠ objs[k].addr := by
    intro heq
    have had : arrObj.addr = f := by rw [← hobj, ← heq, hyAddr]
    exact hnotSelf (had ▸ hfMem)
  exact ⟨y, mem_eraseIdx_of_addr_ne hk hyMem hne, hyAddr⟩

/-! ## 2. `r2_alloc_array` & `r2_ensure_excl_array` WP Proofs -/

theorem r2_alloc_array_wp :
    ∀ xs m Q X, r2AllocArraySpec xs m Q X → Func.wp rtR2Env r2_alloc_array_body xs m Q X := by
  intro ⟨rt, size, cap, ⟨⟩⟩ m Q X hSpec
  dsimp only [Func.wp, r2_alloc_array_body, r2AllocArraySpec] at hSpec ⊢
  change LeanQbe.T.wp _ _ _ _ _
  by_cases hvalid : size.toNat ≤ cap.toNat ∧ cap.toNat ≤ arrMaxCap
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hvalid)] at hSpec
    rcases hSpec with ⟨st, R, hav, hm, hk⟩
    have hcapMax : cap.toNat ≤ 33554428 := by unfold arrMaxCap at hvalid; exact hvalid.2
    obtain ⟨hszEq, hszLe⟩ := arr_allocBytes_fit hvalid.2
    have hid : align8 (arrAllocBytes cap.toNat) = arrAllocBytes cap.toNat :=
      arr_align8_allocBytes cap.toNat
    r2_steps
    r2_call rtR2Env_lcnf_alloc
    dsimp only [lcnfAllocRemSpec, vals, Tup.map, Arg.val]
    have hszEq' : ((24 : BitVec 64) + 8 * cap).toNat = arrAllocBytes cap.toNat := hszEq
    rw [hszEq']
    refine ⟨st, R, hszLe, ?_, ?_, ?_, hm, ?_⟩
    · rw [hid]; unfold rtMinObjBytes arrAllocBytes; omega
    · rw [hid]; unfold rtMaxObjBytes; omega
    · rwa [hid]
    · intro p st' m1 hp0 hp8 hpr hrem hrem2 hm1
      change LeanQbe.T.wp _ _ _ _ _
      rw [hid] at hm1 hrem2
      have hm1' : (region p (arrAllocBytes cap.toNat) ⋆ (rtC0Inv rt st' ⋆ R)) m1 :=
        sep_cast hm1 (by ac_rfl)
      have hge24 : 24 ≤ arrAllocBytes cap.toNat := by unfold arrAllocBytes; omega
      have hfit24 : arrAllocBytes cap.toNat ≤ 2 ^ 64 := by omega
      obtain ⟨w0, hp1⟩ := region_split_cell64 (by omega) hfit24 hm1'
      have hp1' : (region (p + 8#64) (arrAllocBytes cap.toNat - 8) ⋆
          (cell64 p w0 ⋆ rtC0Inv rt st' ⋆ R)) m1 := sep_cast hp1 (by ac_rfl)
      obtain ⟨w1, hp2⟩ := region_split_cell64 (by omega) (by omega) hp1'
      have hp2' : (region (p + 16#64) (arrAllocBytes cap.toNat - 16) ⋆
          (cell64 p w0 ⋆ cell64 (p + 8#64) w1 ⋆ rtC0Inv rt st' ⋆ R)) m1 := by
        have ha16 : p + 8#64 + 8#64 = p + 16#64 := by
          apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]
        rw [ha16, show arrAllocBytes cap.toNat - 8 - 8 = arrAllocBytes cap.toNat - 16 by omega]
          at hp2
        exact sep_cast hp2 (by ac_rfl)
      obtain ⟨w2, hp3⟩ := region_split_cell64 (by omega) (by omega) hp2'
      have ha24 : p + 16#64 + 8#64 = p + 24#64 := by
        apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]
      rw [ha24, show arrAllocBytes cap.toNat - 16 - 8 = arrAllocBytes cap.toNat - 24 by omega]
        at hp3
      have hpc : (cell64 p w0 ⋆ (cell64 (p + 8#64) w1 ⋆ cell64 (p + 16#64) w2 ⋆
          region (p + 24#64) (arrAllocBytes cap.toNat - 24) ⋆ rtC0Inv rt st' ⋆ R)) m1 :=
        sep_cast hp3 (by ac_rfl)
      apply wp_store_sep (store_cell64 arrHeaderWord hpc)
      intro m2 hm2
      r2_steps
      have hm2' : (cell64 (p + 8#64) w1 ⋆ (cell64 p arrHeaderWord ⋆
          cell64 (p + 16#64) w2 ⋆ region (p + 24#64) (arrAllocBytes cap.toNat - 24) ⋆
          rtC0Inv rt st' ⋆ R)) m2 := sep_cast hm2 (by ac_rfl)
      apply wp_store_sep (store_cell64 size hm2')
      intro m3 hm3
      r2_steps
      have hm3' : (cell64 (p + 16#64) w2 ⋆ (cell64 p arrHeaderWord ⋆
          cell64 (p + 8#64) size ⋆ region (p + 24#64) (arrAllocBytes cap.toNat - 24) ⋆
          rtC0Inv rt st' ⋆ R)) m3 := sep_cast hm3 (by ac_rfl)
      apply wp_store_sep (store_cell64 cap hm3')
      intro m4 hm4
      r2_steps
      have hremEq : arrAllocBytes cap.toNat - 24 = 8 * cap.toNat := by
        unfold arrAllocBytes; omega
      rw [hremEq] at hm4
      exact hk p st' m4 hp0 hp8 hpr hrem hrem2 (sep_cast hm4 (by ac_rfl))
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hvalid)] at hSpec
    r2_steps <;> first
      | exact hSpec
      | (exfalso
         have h1 : ¬ 33554428 < cap.toNat := by assumption
         have h2 : ¬ cap.toNat < size.toNat := by assumption
         unfold arrMaxCap at hvalid; omega)

private theorem arr_ensure_fast_ok {rt a : BitVec 64} {st : RtC0State} {arrObj : LcnfObj}
    {childObjs : List LcnfObj} {expand : BitVec 64} {R : Mem 64 → Prop} {m : Mem 64}
    {Q : Post [i64]}
    (hcanon : ArrCanon arrObj) (haddr : arrObj.addr = a) (hrc1 : arrObj.rc = 1#32)
    (hfast : expand = 0#64 ∨ arrObj.fields.length < arrObj.cap)
    (hm : (rtC0Inv rt st ⋆ lcnfObjMem arrObj ⋆ lcnfHeap childObjs ⋆ R) m)
    (hPost : ∀ (r : BitVec 64) (st' : RtC0State) (childObjs' : List LcnfObj) (m' : Mem 64),
      r ≠ 0#64 → r.toNat % 8 = 0 → st'.PreservesMeta st → st'.rem ≤ st.rem →
      (arrObj.rc = 1#32 → expand = 0#64 ∨ arrObj.fields.length < arrObj.cap → st' = st) →
      EnsureExclArrayOutcome arrObj expand r childObjs childObjs'
        (mkArrObj r 1#32 (arrEnsureCap arrObj.fields.length arrObj.cap expand) arrObj.fields)
        (if arrObj.rc = 1#32 then emp else lcnfObjMem (arrObj.withRc (decNonExclRc arrObj.rc))) →
      (rtC0Inv rt st' ⋆
        lcnfObjMem (mkArrObj r 1#32 (arrEnsureCap arrObj.fields.length arrObj.cap expand)
          arrObj.fields) ⋆
        (if arrObj.rc = 1#32 then emp else lcnfObjMem (arrObj.withRc (decNonExclRc arrObj.rc))) ⋆
        lcnfHeap childObjs' ⋆ R) m' →
      Q (r, ()) m') :
    Q (a, ()) m := by
  have hcapEq : arrEnsureCap arrObj.fields.length arrObj.cap expand = arrObj.cap := by
    rcases hfast with rfl | hlt
    · simp [arrEnsureCap]
    · by_cases hex : expand = 0#64 <;> simp [arrEnsureCap, hex, hlt]
  have hhEq : (mkArrObj a 1#32 arrObj.cap arrObj.fields).header = arrObj.header := by
    dsimp only [mkArrObj, LcnfObj.header]
    rcases hcanon with ⟨_, _, _, hcs, hot, htag, _⟩
    rw [hcs, hot, htag, hrc1]
  have hcanNew : ArrCanon (mkArrObj a 1#32 arrObj.cap arrObj.fields) :=
    ⟨haddr ▸ hcanon.1, haddr ▸ hcanon.2.1, by dsimp only [mkArrObj]; decide,
      rfl, rfl, rfl, hcanon.2.2.2.2.2.2.1, hcanon.2.2.2.2.2.2.2⟩
  have hm' : (rtC0Inv rt st ⋆
      lcnfObjMem (mkArrObj a 1#32 (arrEnsureCap arrObj.fields.length arrObj.cap expand)
        arrObj.fields) ⋆
      (if arrObj.rc = 1#32 then emp
       else lcnfObjMem (arrObj.withRc (decNonExclRc arrObj.rc))) ⋆
      lcnfHeap childObjs ⋆ R) m := by
    rw [hcapEq, ite_eq_left_of_eq_true _ _ (eq_true hrc1)]
    have hm0 : (lcnfObjMem arrObj ⋆ (rtC0Inv rt st ⋆ lcnfHeap childObjs ⋆ R)) m :=
      sep_cast hm (by ac_rfl)
    have helim := lcnfObjMem_array_elim hcanon hm0
    rw [haddr, ← hhEq] at helim
    have hm1 : (lcnfObjMem (mkArrObj a 1#32 arrObj.cap arrObj.fields) ⋆
        (rtC0Inv rt st ⋆ lcnfHeap childObjs ⋆ R)) m :=
      mkArrObj_mem_of_parts helim
    have hm2 : ((lcnfObjMem (mkArrObj a 1#32 arrObj.cap arrObj.fields) ⋆ emp) ⋆
        (rtC0Inv rt st ⋆ lcnfHeap childObjs ⋆ R)) m := by
      simpa [sep_emp] using hm1
    exact sep_cast hm2 (by ac_rfl)
  have hout : EnsureExclArrayOutcome arrObj expand a childObjs childObjs
      (mkArrObj a 1#32 (arrEnsureCap arrObj.fields.length arrObj.cap expand) arrObj.fields)
      (if arrObj.rc = 1#32 then emp
       else lcnfObjMem (arrObj.withRc (decNonExclRc arrObj.rc))) := by
    dsimp only [EnsureExclArrayOutcome]
    rw [hcapEq]
    refine ⟨rfl, hcanNew, ?_, ?_, ?_, ?_⟩
    · intro hex
      rcases hfast with h0 | hlt
      · exact absurd h0 hex
      · exact hlt
    · intro _ _; exact haddr.symm
    · intro _; refine ⟨rfl, ite_eq_left_of_eq_true _ _ (eq_true hrc1)⟩
    · intro hne; exact absurd hrc1 hne
  exact hPost a st childObjs m (haddr ▸ hcanon.1) (haddr ▸ hcanon.2.1)
    (RtC0State.PreservesMeta.refl st) (Nat.le_refl _) (fun _ _ => rfl) hout hm'

private theorem arrEnsureCap_props {arrObj : LcnfObj} (hcanon : ArrCanon arrObj)
    {expand : BitVec 64}
    (hnotPanic : ¬ (expand ≠ 0#64 ∧ arrObj.cap ≤ arrObj.fields.length ∧
      arrMaxCap ≤ arrObj.cap)) :
    arrObj.fields.length ≤ arrEnsureCap arrObj.fields.length arrObj.cap expand ∧
      arrEnsureCap arrObj.fields.length arrObj.cap expand ≤ arrMaxCap ∧
      (expand ≠ 0#64 →
        arrObj.fields.length < arrEnsureCap arrObj.fields.length arrObj.cap expand) := by
  have hleCap := hcanon.2.2.2.2.2.2.1
  have hmax := hcanon.2.2.2.2.2.2.2
  by_cases hexp : expand = 0#64
  · simp [arrEnsureCap, hexp, hleCap, hmax]
  · by_cases hlt : arrObj.fields.length < arrObj.cap
    · unfold arrMaxCap at hmax ⊢
      have hcap : arrEnsureCap arrObj.fields.length arrObj.cap expand = arrObj.cap := by
        simp [arrEnsureCap, hexp, hlt]
      rw [hcap]
      exact ⟨hleCap, hmax, fun _ => hlt⟩
    · unfold arrMaxCap at hmax hnotPanic
      have hnotge : ¬ (33554428 ≤ arrObj.cap) :=
        fun h => hnotPanic ⟨hexp, Nat.le_of_not_lt hlt, h⟩
      have hltMax : arrObj.cap < arrMaxCap := by unfold arrMaxCap; omega
      by_cases hcap0 : arrObj.cap = 0
      · have hlen0 : arrObj.fields.length = 0 := by omega
        have hcap : arrEnsureCap arrObj.fields.length arrObj.cap expand = 4 := by
          simp [arrEnsureCap, hexp, hcap0, hlen0]
        rw [hcap]
        unfold arrMaxCap
        exact ⟨by omega, by omega, fun _ => by omega⟩
      · have hcap : arrEnsureCap arrObj.fields.length arrObj.cap expand =
            min arrMaxCap (arrObj.cap * 2) := by
          simp [arrEnsureCap, hexp, hlt, hcap0]
        rw [hcap]
        unfold arrMaxCap at hltMax ⊢
        exact ⟨by omega, by omega, fun _ => by omega⟩

private theorem arr_ensure_excl_mk_new {rt r : BitVec 64} {st1 : RtC0State}
    {arrObj : LcnfObj} {newCap : Nat} {chEnd : List LcnfObj}
    {R : Mem 64 → Prop} {mL : Mem 64}
    (hr0 : r ≠ 0#64) (hr8 : r.toNat % 8 = 0)
    (hlenLe : arrObj.fields.length ≤ newCap) (hcapMax : newCap ≤ arrMaxCap)
    (hmLoop : (array64 (r + 24#64) (arrObj.fields.take arrObj.fields.length) ⋆
      region (r + 24#64 + BitVec.ofNat 64 (8 * arrObj.fields.length))
        (8 * (newCap - arrObj.fields.length)) ⋆
      cell64 r arrHeaderWord ⋆
      cell64 (r + 8#64) (BitVec.ofNat 64 arrObj.fields.length) ⋆
      cell64 (r + 16#64) (BitVec.ofNat 64 newCap) ⋆
      rtC0Inv rt st1 ⋆ lcnfObjMem arrObj ⋆ lcnfHeap chEnd ⋆ R) mL) :
    let rObj := mkArrObj r 1#32 newCap arrObj.fields
    ArrCanon rObj ∧
    (lcnfObjMem arrObj ⋆ (rtC0Inv rt st1 ⋆ lcnfObjMem rObj ⋆ lcnfHeap chEnd ⋆ R)) mL := by
  refine ⟨mkArrObj_canon hr0 hr8 (by decide) hlenLe hcapMax, ?_⟩
  rw [List.take_length] at hmLoop
  have hparts : (cell64 r (mkArrObj r 1#32 newCap arrObj.fields).header ⋆
      cell64 (r + 8#64) (BitVec.ofNat 64 arrObj.fields.length) ⋆
      cell64 (r + 16#64) (BitVec.ofNat 64 newCap) ⋆
      array64 (r + 24#64) arrObj.fields ⋆
      region (r + BitVec.ofNat 64 (24 + 8 * arrObj.fields.length))
        (8 * (newCap - arrObj.fields.length)) ⋆
      (rtC0Inv rt st1 ⋆ lcnfObjMem arrObj ⋆ lcnfHeap chEnd ⋆ R)) mL := by
    rw [mkArrObj_header, ← ptr_add_24_mul8]
    exact sep_cast hmLoop (by ac_rfl)
  exact sep_cast (mkArrObj_mem_of_parts hparts) (by ac_rfl)

private theorem arr_ensure_excl_finish {rt r : BitVec 64} {expand : BitVec 64}
    {Q : Post [i64]} {st st1 st3 : RtC0State} {arrObj : LcnfObj} {childObjs : List LcnfObj}
    {R : Mem 64 → Prop} {m3 : Mem 64}
    (hr0 : r ≠ 0#64) (hr8 : r.toNat % 8 = 0)
    (hpr1 : st1.PreservesMeta st) (hpr3 : st3.PreservesMeta st1)
    (hrem1 : st1.rem ≤ st.rem) (hrem3 : st3.rem ≤ st1.rem)
    (hslow : arrObj.rc ≠ 1#32 ∨ expand ≠ 0#64 ∧ arrObj.cap ≤ arrObj.fields.length)
    (hcanon : ArrCanon arrObj)
    (hpanic : ¬ (expand ≠ 0#64 ∧ arrObj.cap ≤ arrObj.fields.length ∧ arrMaxCap ≤ arrObj.cap))
    (hpost : ∀ (r' : BitVec 64) (st' : RtC0State) (childObjs' : List LcnfObj) (m' : Mem 64),
      r' ≠ 0#64 → r'.toNat % 8 = 0 → st'.PreservesMeta st → st'.rem ≤ st.rem →
      (arrObj.rc = 1#32 → expand = 0#64 ∨ arrObj.fields.length < arrObj.cap → st' = st) →
      let rObj := mkArrObj r' 1#32 (arrEnsureCap arrObj.fields.length arrObj.cap expand)
        arrObj.fields
      let oldKeep := if arrObj.rc = 1#32 then emp
        else lcnfObjMem (arrObj.withRc (decNonExclRc arrObj.rc))
      EnsureExclArrayOutcome arrObj expand r' childObjs childObjs' rObj oldKeep →
      (rtC0Inv rt st' ⋆ lcnfObjMem rObj ⋆ oldKeep ⋆ lcnfHeap childObjs' ⋆ R) m' →
      Q (r', ()) m')
    (hm3 : (rtC0Inv rt st3 ⋆
      lcnfObjMem (mkArrObj r 1#32 (arrEnsureCap arrObj.fields.length arrObj.cap expand)
        arrObj.fields) ⋆
      (if arrObj.rc = 1#32 then emp else lcnfObjMem (arrObj.withRc (decNonExclRc arrObj.rc))) ⋆
      lcnfHeap (if arrObj.rc = 1#32 then childObjs
        else incChildrenObjs (arrObj.fields.take arrObj.fields.length) childObjs) ⋆
      R) m3) :
    Q (r, ()) m3 := by
  have hcapProps := arrEnsureCap_props hcanon hpanic
  have hcanNew : ArrCanon (mkArrObj r 1#32
      (arrEnsureCap arrObj.fields.length arrObj.cap expand) arrObj.fields) :=
    mkArrObj_canon hr0 hr8 (by decide) hcapProps.1 hcapProps.2.1
  simp only [List.take_length] at hm3
  have hout : EnsureExclArrayOutcome arrObj expand r childObjs
      (if arrObj.rc = 1#32 then childObjs else incChildrenObjs arrObj.fields childObjs)
      (mkArrObj r 1#32 (arrEnsureCap arrObj.fields.length arrObj.cap expand) arrObj.fields)
      (if arrObj.rc = 1#32 then emp
       else lcnfObjMem (arrObj.withRc (decNonExclRc arrObj.rc))) := by
    refine ⟨rfl, hcanNew, hcapProps.2.2, ?_, ?_, ?_⟩
    · intro hrc1 hfast
      rcases hslow with hne | ⟨hex, hge⟩
      · exact absurd hrc1 hne
      · rcases hfast with rfl | hlt
        · exact absurd rfl hex
        · omega
    · intro hrc1
      exact ⟨ite_eq_left_of_eq_true _ _ (eq_true hrc1),
        ite_eq_left_of_eq_true _ _ (eq_true hrc1)⟩
    · intro hne
      exact ⟨ite_eq_right_of_eq_false _ _ (eq_false hne),
        ite_eq_right_of_eq_false _ _ (eq_false hne)⟩
  refine hpost r st3 _ m3 hr0 hr8 (hpr1.trans hpr3) (by omega) ?_ hout hm3
  intro hrc1 hfast
  rcases hslow with hne | ⟨hex, hge⟩
  · exact absurd hrc1 hne
  · rcases hfast with rfl | hlt
    · exact absurd rfl hex
    · omega

theorem r2_ensure_excl_array_wp :
    ∀ xs m Q X,
      r2EnsureExclArraySpec xs m Q X → Func.wp rtR2Env r2_ensure_excl_array_body xs m Q X := by
  intro ⟨rt, a, expand, ⟨⟩⟩ m Q X
    ⟨st, arrObj, childObjs, R, haddr, hcanon, hwfChild, hm, hchildOk, hPost⟩
  subst haddr
  have hwf := hcanon.wf
  have hlen64 := hcanon.len_lt_64
  have hcap64 := hcanon.cap_lt_64
  have hlenMod : arrObj.fields.length % 2 ^ 64 = arrObj.fields.length := Nat.mod_eq_of_lt hlen64
  have hcapMod : arrObj.cap % 2 ^ 64 = arrObj.cap := Nat.mod_eq_of_lt hcap64
  have hrcEq := LcnfObj.header_rc arrObj hwf.2.2.2.1 hwf.2.2.2.2.1 hwf.2.2.2.2.2.1
  dsimp only [Func.wp, r2_ensure_excl_array_body]
  change LeanQbe.T.wp _ _ _ _ _
  have hmHdr : (lcnfObjMem arrObj ⋆ (rtC0Inv rt st ⋆ lcnfHeap childObjs ⋆ R)) m :=
    sep_cast hm (by ac_rfl)
  apply wp_load_of (r2_lcnfObjMem_load_header hmHdr)
  r2_steps
  apply wp_load_of (arr_load_sz_mid hcanon hmHdr)
  r2_steps
  apply wp_load_of (arr_load_cap_mid hcanon hmHdr)
  apply wp_join_group
    (P := fun _ m' =>
      m' = m ∧ (arrObj.rc ≠ 1#32 ∨ (expand ≠ 0#64 ∧ arrObj.cap ≤ arrObj.fields.length)))
  · intro _ ⟨⟩ m' ⟨hmEq, hslow⟩
    subst hmEq
    change LeanQbe.T.wp _ _ _ _ _
    by_cases hpanic : expand ≠ 0#64 ∧ arrObj.cap ≤ arrObj.fields.length ∧ arrMaxCap ≤ arrObj.cap
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hpanic)] at hPost
      apply wp_join_group (P := fun _ _ => False)
      · intro _ _ _ hFalse; exact hFalse.elim
      · intro _ hJ
        have hcapMax : arrObj.cap = 33554428 := by
          have := hcanon.2.2.2.2.2.2.2; unfold arrMaxCap at *; omega
        have hlenMax : arrObj.fields.length = 33554428 := by
          have := hcanon.2.2.2.2.2.2.1; omega
        r2_steps <;> first
          | exact hPost
          | (exfalso
             simp only [hlenMod, hcapMod, BitVec.toNat_ofNat] at *
             try (have hcap0 : BitVec.ofNat 64 arrObj.cap = 0 := by assumption
                  have := congrArg BitVec.toNat hcap0
                  rw [BitVec.toNat_ofNat, hcapMod] at this
                  omega)
             omega)
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hpanic)] at hPost
      rcases hPost with ⟨hav, hpost⟩
      have hcapProps := arrEnsureCap_props hcanon hpanic
      let newCap := arrEnsureCap arrObj.fields.length arrObj.cap expand
      have hlenLe : arrObj.fields.length ≤ newCap := hcapProps.1
      have hcapMax : newCap ≤ arrMaxCap := hcapProps.2.1
      have hexLt : expand ≠ 0#64 → arrObj.fields.length < newCap := hcapProps.2.2
      have hcap64New : newCap < 2 ^ 64 := by unfold arrMaxCap at hcapMax; omega
      apply wp_join_group
        (P := fun (xs : Tup Val [i64]) m1 => match xs with
          | (nc, PUnit.unit) => m1 = m' ∧ nc = BitVec.ofNat 64 newCap)
      · intro _ ⟨nc, ⟨⟩⟩ m1 ⟨rfl, hnc⟩
        subst hnc
        change LeanQbe.T.wp _ _ _ _ _
        r2_call rtR2Env_r2_alloc_array
        dsimp only [r2AllocArraySpec, vals, Tup.map, Arg.val]
        have hszTo : (BitVec.ofNat 64 arrObj.fields.length).toNat = arrObj.fields.length := by
          rw [BitVec.toNat_ofNat, hlenMod]
        have hncTo : (BitVec.ofNat 64 newCap).toNat = newCap := by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcap64New]
        have hvalidA : (BitVec.ofNat 64 arrObj.fields.length).toNat ≤
              (BitVec.ofNat 64 newCap).toNat ∧
            (BitVec.ofNat 64 newCap).toNat ≤ arrMaxCap := by
          rw [hszTo, hncTo]; exact ⟨hlenLe, hcapMax⟩
        rw [ite_eq_left_of_eq_true _ _ (eq_true hvalidA)]
        refine ⟨st, lcnfObjMem arrObj ⋆ lcnfHeap childObjs ⋆ R, ?_, sep_cast hm (by ac_rfl),
          fun r st1 m1 hr0 hr8 hpr1 hrem1 _ hm1 => ?_⟩
        · rw [hncTo]; exact hav hslow
        · rw [hncTo] at hm1
          change LeanQbe.T.wp _ _ _ _ _
          let n := arrObj.fields.length
          let curChilds : Nat → List LcnfObj := fun i =>
            if arrObj.rc = 1#32 then childObjs else incChildrenObjs (arrObj.fields.take i) childObjs
          apply wp_loop_inv
            (Inv := fun (xs : Tup Val [i64]) mL => match xs with
              | (iv, PUnit.unit) => ∃ i, i ≤ n ∧ iv = BitVec.ofNat 64 i ∧
                (array64 (r + 24#64) (arrObj.fields.take i) ⋆
                  region (r + 24#64 + BitVec.ofNat 64 (8 * i)) (8 * (newCap - i)) ⋆
                  cell64 r arrHeaderWord ⋆
                  cell64 (r + 8#64) (BitVec.ofNat 64 n) ⋆
                  cell64 (r + 16#64) (BitVec.ofNat 64 newCap) ⋆
                  rtC0Inv rt st1 ⋆ lcnfObjMem arrObj ⋆
                  lcnfHeap (curChilds i) ⋆ R) mL)
            (μ := fun (xs : Tup Val [i64]) _ =>
              match xs with | (iv, PUnit.unit) => n - iv.toNat)
          · intro J hJ
            r2_steps
            apply hJ (0#64, ()) m1
            refine ⟨0, Nat.zero_le n, rfl, ?_⟩
            dsimp only [curChilds]
            by_cases hrc1 : arrObj.rc = 1#32
            · simp only [hrc1, ↓reduceIte, List.take_zero, array64_nil, emp_sep, Nat.mul_zero,
                Nat.sub_zero]
              rw [show r + 24#64 + 0#64 = r + 24#64 by simp]
              exact sep_cast hm1 (by ac_rfl)
            · simp only [hrc1, ↓reduceIte, List.take_zero, array64_nil, emp_sep, Nat.mul_zero,
                Nat.sub_zero]
              rw [incChildrenObjs_nil childObjs hwfChild,
                show r + 24#64 + 0#64 = r + 24#64 by simp]
              exact sep_cast hm1 (by ac_rfl)
          · intro _J ⟨iv, ⟨⟩⟩ mL ⟨i, hle, hiv, hmLoop⟩ hRec
            subst hiv
            have hi64 : i < 2 ^ 64 := Nat.lt_of_le_of_lt hle (by omega)
            have hiTo : (BitVec.ofNat 64 i).toNat = i := by
              rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi64]
            r2_steps
            · have hcLt : i % 2 ^ 64 < arrObj.fields.length % 2 ^ 64 := by assumption
              have hlt : i < n := by rwa [Nat.mod_eq_of_lt hi64, hlenMod] at hcLt
              have hmArrMid : (lcnfObjMem arrObj ⋆
                  (array64 (r + 24#64) (arrObj.fields.take i) ⋆
                    region (r + 24#64 + BitVec.ofNat 64 (8 * i)) (8 * (newCap - i)) ⋆
                    cell64 r arrHeaderWord ⋆
                    cell64 (r + 8#64) (BitVec.ofNat 64 n) ⋆
                    cell64 (r + 16#64) (BitVec.ofNat 64 newCap) ⋆
                    rtC0Inv rt st1 ⋆ lcnfHeap (curChilds i) ⋆ R)) mL :=
                sep_cast hmLoop (by ac_rfl)
              have hloadElem := arr_load_elem_mid hcanon (by rw [hiTo]; exact hlt) hmArrMid
              simp only [hiTo] at hloadElem
              let elem := arrObj.fields[i]
              have hmReg : (region (r + 24#64 + BitVec.ofNat 64 (8 * i)) (8 * (newCap - i)) ⋆
                  (array64 (r + 24#64) (arrObj.fields.take i) ⋆
                    cell64 r arrHeaderWord ⋆
                    cell64 (r + 8#64) (BitVec.ofNat 64 n) ⋆
                    cell64 (r + 16#64) (BitVec.ofNat 64 newCap) ⋆
                    rtC0Inv rt st1 ⋆ lcnfObjMem arrObj ⋆
                    lcnfHeap (curChilds i) ⋆ R)) mL := sep_cast hmLoop (by ac_rfl)
              have hn8 : 8 ≤ 8 * (newCap - i) := by omega
              have hfit8 : 8 * (newCap - i) ≤ 2 ^ 64 := by unfold arrMaxCap at hcapMax; omega
              obtain ⟨wSlot, hmSlot0⟩ := region_split_cell64 hn8 hfit8 hmReg
              have hmSlot : (cell64 (r + 24#64 + BitVec.ofNat 64 (8 * i)) wSlot ⋆
                  (region (r + 24#64 + BitVec.ofNat 64 (8 * i) + 8#64) (8 * (newCap - i) - 8) ⋆
                    array64 (r + 24#64) (arrObj.fields.take i) ⋆
                    cell64 r arrHeaderWord ⋆ cell64 (r + 8#64) (BitVec.ofNat 64 n) ⋆
                    cell64 (r + 16#64) (BitVec.ofNat 64 newCap) ⋆
                    rtC0Inv rt st1 ⋆ lcnfObjMem arrObj ⋆ lcnfHeap (curChilds i) ⋆ R)) mL :=
                sep_cast hmSlot0 (by ac_rfl)
              r2_steps
              try rw [bv64_8mul_eq_ofNat, Nat.mod_eq_of_lt hi64]
              apply wp_load_of hloadElem
              apply wp_join_group
                (P := fun (_ : Tup Val []) m3 =>
                  (cell64 (r + 24#64 + BitVec.ofNat 64 (8 * i)) wSlot ⋆
                    (region (r + 24#64 + BitVec.ofNat 64 (8 * i) + 8#64) (8 * (newCap - i) - 8) ⋆
                      array64 (r + 24#64) (arrObj.fields.take i) ⋆
                      cell64 r arrHeaderWord ⋆ cell64 (r + 8#64) (BitVec.ofNat 64 n) ⋆
                      cell64 (r + 16#64) (BitVec.ofNat 64 newCap) ⋆
                      rtC0Inv rt st1 ⋆ lcnfObjMem arrObj ⋆
                      lcnfHeap (curChilds (i + 1)) ⋆ R)) m3)
              · intro _ ⟨⟩ m3 hm3
                have haddrSlot : r + 24#64 + BitVec.ofNat 64 (8 * i) =
                    r + 24#64 + 8#64 * BitVec.ofNat 64 i := by
                  congr 1
                  rw [bv64_8mul_eq_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi64]
                have hm3S : (cell64 (r + 24#64 + 8#64 * BitVec.ofNat 64 i) wSlot ⋆
                    (region (r + 24#64 + BitVec.ofNat 64 (8 * i) + 8#64) (8 * (newCap - i) - 8) ⋆
                      array64 (r + 24#64) (arrObj.fields.take i) ⋆
                      cell64 r arrHeaderWord ⋆ cell64 (r + 8#64) (BitVec.ofNat 64 n) ⋆
                      cell64 (r + 16#64) (BitVec.ofNat 64 newCap) ⋆
                      rtC0Inv rt st1 ⋆ lcnfObjMem arrObj ⋆
                      lcnfHeap (curChilds (i + 1)) ⋆ R)) m3 := by
                  rwa [← haddrSlot]
                obtain ⟨hstOk, hm4⟩ := r2_c0_store_cell64 elem hm3S
                r2_steps
                apply wp_store_sep ⟨hstOk, hm4⟩
                intro m4 hm4'
                rw [← haddrSlot] at hm4'
                r2_steps
                have hbvAdd : BitVec.ofNat 64 i + (1 : BitVec 64) =
                    BitVec.ofNat 64 (i + 1) := by
                  apply BitVec.eq_of_toNat_eq; simp
                rw [hbvAdd]
                apply hRec (BitVec.ofNat 64 (i + 1), ()) m4
                · dsimp only
                  have hi1 : (BitVec.ofNat 64 (i + 1)).toNat = i + 1 := by
                    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
                  rw [hiTo, hi1]; omega
                · refine ⟨i + 1, hlt, rfl, ?_⟩
                  have hlenP : (arrObj.fields.take i).length = i := by
                    simp [List.length_take]; omega
                  have htake : arrObj.fields.take (i + 1) =
                      arrObj.fields.take i ++ [elem] :=
                    List.take_succ_eq_append_getElem hlt
                  rw [htake, array64_append, hlenP]
                  have hs1 : array64 (r + 24#64 + BitVec.ofNat 64 (8 * i)) [elem] =
                      cell64 (r + 24#64 + BitVec.ofNat 64 (8 * i)) elem := by
                    simp [array64, sep_emp]
                  rw [hs1]
                  have hregAddr : r + 24#64 + BitVec.ofNat 64 (8 * (i + 1)) =
                      r + 24#64 + BitVec.ofNat 64 (8 * i) + 8#64 := by
                    apply BitVec.eq_of_toNat_eq
                    rw [BitVec.add_assoc, BitVec.add_assoc]
                    congr 1; apply BitVec.eq_of_toNat_eq
                    simp [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
                  have hregSz : 8 * (newCap - (i + 1)) = 8 * (newCap - i) - 8 := by omega
                  rw [hregAddr, hregSz]
                  exact sep_cast hm4' (by ac_rfl)
              · intro Jinc hJinc
                r2_steps
                · have hrcNe1 := arr_rc_ne1_of_mask hwf (by assumption)
                  rcases hchildOk hrcNe1 with ⟨hclosed, hbound⟩
                  have hcurNe1 : curChilds i = incChildrenObjs (arrObj.fields.take i)
                      childObjs := by simp [curChilds, hrcNe1]
                  have hnextNe1 : curChilds (i + 1) =
                      incChildrenObjs (arrObj.fields.take (i + 1)) childObjs := by
                    simp [curChilds, hrcNe1]
                  r2_call rtR2Env_r2_inc_obj
                  dsimp only [r2IncObjSpec, vals, Tup.map, Arg.val]
                  by_cases hskip : elem = 0#64 ∨ (elem &&& 1#64) ≠ 0#64
                  · rw [ite_eq_left_of_eq_true _ _ (eq_true hskip)]
                    r2_steps
                    apply hJinc
                    rw [hnextNe1, incChildrenObjs_step_skip hwfChild hlt hskip, ← hcurNe1]
                    exact hmSlot
                  · rw [ite_eq_right_of_eq_false _ _ (eq_false hskip)]
                    have he0 : elem ≠ 0#64 := fun h => hskip (Or.inl h)
                    have he1 : (elem &&& 1#64) = 0#64 :=
                      Classical.not_not.mp fun h => hskip (Or.inr h)
                    obtain ⟨y, hyMem, hyAddr⟩ :=
                      hclosed elem (List.getElem_mem hlt) he1
                    obtain ⟨j, hjLen, hjEq⟩ := List.getElem_of_mem hyMem
                    have hcurLen : (incChildrenObjs (arrObj.fields.take i)
                        childObjs).length = childObjs.length := by
                      simp [incChildrenObjs]
                    have hjCur : j < (curChilds i).length := by
                      rw [hcurNe1, hcurLen]; exact hjLen
                    have hjInc : j < (incChildrenObjs (arrObj.fields.take i) childObjs).length :=
                      by rwa [← hcurNe1]
                    have hcurMem : (curChilds i)[j].addr = elem := by
                      simp only [hcurNe1, incChildrenObjs, List.getElem_map]
                      split <;> simp [hjEq, hyAddr, LcnfObj.withRc]
                    have hcurWf : (curChilds i)[j].Wf := by
                      simp only [hcurNe1]
                      exact incChildrenObjs_wf hwfChild hbound i _ (List.getElem_mem hjInc)
                    have hmInc : (lcnfObjMem (curChilds i)[j] ⋆
                        (lcnfHeap ((curChilds i).eraseIdx j) ⋆
                          cell64 (r + 24#64 + BitVec.ofNat 64 (8 * i)) wSlot ⋆
                          region (r + 24#64 + BitVec.ofNat 64 (8 * i) + 8#64)
                            (8 * (newCap - i) - 8) ⋆
                          array64 (r + 24#64) (arrObj.fields.take i) ⋆
                          cell64 r arrHeaderWord ⋆
                          cell64 (r + 8#64) (BitVec.ofNat 64 n) ⋆
                          cell64 (r + 16#64) (BitVec.ofNat 64 newCap) ⋆
                          rtC0Inv rt st1 ⋆ lcnfObjMem arrObj ⋆ R)) mL := by
                      have hf := lcnfHeap_focus (curChilds i) hjCur
                      rw [← lcnfHeap_eraseIdx (curChilds i)] at hf
                      rw [hf] at hmSlot
                      exact sep_cast hmSlot (by ac_rfl)
                    have hnodup : (childObjs.map LcnfObj.addr).Nodup := by
                      have hcf : (lcnfHeap childObjs ⋆
                          (rtC0Inv rt st ⋆ lcnfObjMem arrObj ⋆ R)) _ :=
                        sep_cast hm (by ac_rfl)
                      exact lcnfHeap_nodup_addrs hcf
                    refine ⟨(curChilds i)[j], _, hcurMem, hcurWf, hmInc, fun m3 hm3 => ?_⟩
                    r2_steps
                    apply hJinc
                    have hset : (curChilds i).set j
                        ((curChilds i)[j].withRc (incRcVal (curChilds i)[j].rc)) =
                        curChilds (i + 1) := by
                      simp only [hcurNe1, hnextNe1]
                      exact incChildrenObjs_step_hit hwfChild hnodup hbound hlt hjLen
                        (hjEq ▸ hyAddr)
                    have hm3' : (lcnfHeap ((curChilds i).set j
                          ((curChilds i)[j].withRc (incRcVal (curChilds i)[j].rc))) ⋆
                        (cell64 (r + 24#64 + BitVec.ofNat 64 (8 * i)) wSlot ⋆
                          region (r + 24#64 + BitVec.ofNat 64 (8 * i) + 8#64)
                            (8 * (newCap - i) - 8) ⋆
                          array64 (r + 24#64) (arrObj.fields.take i) ⋆
                          cell64 r arrHeaderWord ⋆
                          cell64 (r + 8#64) (BitVec.ofNat 64 n) ⋆
                          cell64 (r + 16#64) (BitVec.ofNat 64 newCap) ⋆
                          rtC0Inv rt st1 ⋆ lcnfObjMem arrObj ⋆ R)) m3 := by
                      have hfn := lcnfHeap_focus
                        ((curChilds i).set j
                          ((curChilds i)[j].withRc (incRcVal (curChilds i)[j].rc)))
                        (show j < ((curChilds i).set j _).length from by
                          rw [List.length_set]; exact hjCur)
                      rw [← lcnfHeap_eraseIdx _] at hfn
                      rw [List.getElem_set_self, eraseIdx_set_eq_self] at hfn
                      rw [hfn]
                      exact sep_cast hm3 (by ac_rfl)
                    rw [hset] at hm3'
                    exact sep_cast hm3' (by ac_rfl)
                · have hrc1 := arr_rc_of_mask_eq1 hwf (by assumption)
                  r2_steps
                  apply hJinc
                  have hceq : curChilds (i + 1) = curChilds i := by simp [curChilds, hrc1]
                  rw [hceq]
                  exact hmSlot
            all_goals
              have hcGe : ¬ i % 2 ^ 64 < arrObj.fields.length % 2 ^ 64 := by assumption
              have hiEq : i = n := by
                rw [Nat.mod_eq_of_lt hi64, hlenMod] at hcGe
                dsimp only [n] at *; omega
              subst hiEq
              let rObj := mkArrObj r 1#32 newCap arrObj.fields
              obtain ⟨_, hmNew⟩ := arr_ensure_excl_mk_new hr0 hr8 hlenLe hcapMax hmLoop
              first
                | ( have hrc1 := arr_rc_of_mask_eq1 hwf (by assumption)
                    have hand0 : (arrObj.addr &&& 1#64) = 0#64 :=
                      bv64_and1_zero_of_mod8 hcanon.2.1
                    have hnotAnd : ¬ (arrObj.addr &&& 1#64) ≠ 0#64 := by simp [hand0]
                    r2_call rtR2Env_lcnf_free_obj
                    dsimp only [lcnfFreeObjSpec, vals, Tup.map, Arg.val]
                    rw [ite_eq_right_of_eq_false _ _ (eq_false hnotAnd)]
                    obtain ⟨f1, f2, hu, hd, hfree0, hrest⟩ := hmNew
                    have hfreeLay := lcnfObjMem_to_freeObjLayout hwf hfree0
                    have hmFree0 : (freeObjLayout arrObj.addr arrObj.totalBytes arrObj.header ⋆
                        (rtC0Inv rt st1 ⋆ lcnfObjMem rObj ⋆ lcnfHeap (curChilds n) ⋆ R)) mL :=
                      ⟨f1, f2, hu, hd, hfreeLay, hrest⟩
                    have hmFree : (rtC0Inv rt st1 ⋆
                        freeObjLayout arrObj.addr arrObj.totalBytes arrObj.header ⋆
                        (lcnfObjMem rObj ⋆ lcnfHeap (curChilds n) ⋆ R)) mL :=
                      sep_cast hmFree0 (by ac_rfl)
                    refine ⟨st1, arrObj.header, arrObj.totalBytes, _, hcanon.1, hcanon.2.1,
                      hwf.2.2.2.2.2.2.1, hwf.2.2.2.2.2.2.2.1, hwf.2.2.2.2.2.2.2.2.1, hmFree, ?_⟩
                    intro st2 m3 hpr2 hrem2 _ hm3
                    r2_steps
                    refine arr_ensure_excl_finish hr0 hr8 hpr1 hpr2 hrem1 (Nat.le_of_eq hrem2)
                      hslow hcanon hpanic hpost ?_
                    rw [ite_eq_left_of_eq_true _ _ (eq_true hrc1)]
                    exact sep_cast hm3 (by ac_rfl) )
                | ( have hrcNe1 := arr_rc_ne1_of_mask hwf (by assumption)
                    have hgt1 : 1 < arrObj.rc.toNat := by
                      have hc1 : 1 < (arrObj.header &&& 4294967295#64).toNat := by assumption
                      rw [hrcEq, BitVec.toNat_ofNat,
                        Nat.mod_eq_of_lt (Nat.lt_trans arrObj.rc.isLt (by decide))] at hc1
                      exact hc1
                    have hgtInt : 1 < arrObj.rc.toInt := by
                      have hlt231 : arrObj.rc.toNat < 2147483648 := by
                        have hc2 : (arrObj.header &&& 4294967295#64).toNat < 2147483648 :=
                          by assumption
                        rw [hrcEq, BitVec.toNat_ofNat,
                          Nat.mod_eq_of_lt (Nat.lt_trans arrObj.rc.isLt (by decide))] at hc2
                        exact hc2
                      have h0 := hwf.2.2.1
                      rw [BitVec.toInt_eq_toNat_cond] at h0 ⊢; split at h0 <;> omega
                    obtain ⟨hok, hm3⟩ := lcnfObjMem_store_rc (arrObj.rc - 1#32) hmNew
                    rw [← lcnfObjHeader_sub1 arrObj hwf hgt1] at hm3
                    apply wp_store_sep ⟨hok, hm3⟩
                    intro m3 hm3'
                    r2_steps
                    refine arr_ensure_excl_finish hr0 hr8 hpr1 (RtC0State.PreservesMeta.refl st1)
                      hrem1 (Nat.le_refl _) hslow hcanon hpanic hpost ?_
                    rw [ite_eq_right_of_eq_false _ _ (eq_false hrcNe1)]
                    simp only [decNonExclRc, hgtInt, ↓reduceIte]
                    exact sep_cast hm3' (by ac_rfl) )
                | ( exfalso
                    have hnot : ¬ (arrObj.header &&& 4294967295#64).toNat < 2147483648 :=
                      by assumption
                    have h0 := hwf.2.2.1
                    rw [hrcEq, BitVec.toNat_ofNat,
                      Nat.mod_eq_of_lt (Nat.lt_trans arrObj.rc.isLt (by decide))] at hnot
                    rw [BitVec.toInt_eq_toNat_cond] at h0; split at h0 <;> omega )
                | ( have hrcNe1 := arr_rc_ne1_of_mask hwf (by assumption)
                    have hnot : ¬ 1 < (arrObj.header &&& 4294967295#64).toNat := by assumption
                    have h0 := hwf.2.2.1
                    have hlt231 : arrObj.rc.toNat < 2147483648 := by
                      rw [BitVec.toInt_eq_toNat_cond] at h0; split at h0 <;> omega
                    have hrc0Nat : arrObj.rc.toNat = 0 := by
                      rw [hrcEq, BitVec.toNat_ofNat,
                        Nat.mod_eq_of_lt (Nat.lt_trans arrObj.rc.isLt (by decide))] at hnot
                      have hne1 : arrObj.rc.toNat ≠ 1 :=
                        fun h => hrcNe1 (BitVec.eq_of_toNat_eq (by simpa using h))
                      omega
                    have hrc0 : arrObj.rc = 0#32 :=
                      BitVec.eq_of_toNat_eq (by simpa using hrc0Nat)
                    r2_steps
                    refine arr_ensure_excl_finish hr0 hr8 hpr1 (RtC0State.PreservesMeta.refl st1)
                      hrem1 (Nat.le_refl _) hslow hcanon hpanic hpost ?_
                    rw [ite_eq_right_of_eq_false _ _ (eq_false hrcNe1)]
                    have hdec0 : decNonExclRc arrObj.rc = 0#32 := by
                      simp only [decNonExclRc, hrc0]
                      exact ite_eq_right_of_eq_false _ _ (eq_false (by decide))
                    have hwid : arrObj.withRc (decNonExclRc arrObj.rc) = arrObj := by
                      rw [hdec0]
                      cases arrObj with
                      | mk addr rc csSz other tag cap fields limbs mpzMeta scalarData =>
                        dsimp only [LcnfObj.withRc]; subst hrc0; rfl
                    rw [hwid]
                    exact sep_cast hmNew (by ac_rfl) )
      · intro Jnc hJnc
        r2_steps
        · exfalso
          have hne : expand ≠ 0#64 := by assumption
          have hge : 4 ≤ arrObj.fields.length % 2 ^ 64 := by assumption
          have hc0 : BitVec.ofNat 64 arrObj.cap = 0 := by assumption
          have hcap0 : arrObj.cap = 0 := by
            have := congrArg BitVec.toNat hc0
            rw [BitVec.toNat_ofNat, hcapMod] at this; exact this
          have := hcanon.2.2.2.2.2.2.1; omega
        · apply hJnc
          refine ⟨rfl, ?_⟩
          have hne : expand ≠ 0#64 := by assumption
          have hc0 : BitVec.ofNat 64 arrObj.cap = 0 := by assumption
          have hcap0 : arrObj.cap = 0 := by
            have := congrArg BitVec.toNat hc0
            rw [BitVec.toNat_ofNat, hcapMod] at this; exact this
          have hnlt : ¬ arrObj.fields.length < arrObj.cap := by omega
          simp [newCap, arrEnsureCap, hne, hcap0]
        · apply hJnc
          refine ⟨rfl, ?_⟩
          have hne : expand ≠ 0#64 := by assumption
          have hlt : arrObj.fields.length % 2 ^ 64 < arrObj.cap % 2 ^ 64 := by assumption
          rw [hlenMod, hcapMod] at hlt
          simp [newCap, arrEnsureCap, hne, hlt]
        · exfalso
          have hne : expand ≠ 0#64 := by assumption
          have hge : 33554428 ≤ arrObj.cap % 2 ^ 64 := by assumption
          have hnlt : ¬ arrObj.fields.length % 2 ^ 64 < arrObj.cap % 2 ^ 64 := by assumption
          rw [hcapMod] at hge; rw [hlenMod, hcapMod] at hnlt
          unfold arrMaxCap at hpanic; exact hpanic ⟨hne, by omega, hge⟩
        · exfalso
          have hgt : 33554428 < arrObj.fields.length % 2 ^ 64 := by assumption
          rw [hlenMod] at hgt
          have := hcanon.2.2.2.2.2.2.1; have := hcanon.2.2.2.2.2.2.2
          unfold arrMaxCap at *; omega
        · exfalso
          have hne : expand ≠ 0#64 := by assumption
          have hge : 33554428 ≤ arrObj.fields.length % 2 ^ 64 := by assumption
          rw [hlenMod] at hge
          have := hcanon.2.2.2.2.2.2.1; have := hcanon.2.2.2.2.2.2.2
          unfold arrMaxCap at *; apply hpanic; exact ⟨hne, by omega, by omega⟩
        · apply hJnc
          refine ⟨rfl, ?_⟩
          have hne : expand ≠ 0#64 := by assumption
          have hnlt : ¬ arrObj.fields.length % 2 ^ 64 < arrObj.cap % 2 ^ 64 := by assumption
          rw [hlenMod, hcapMod] at hnlt
          have hc0 : BitVec.ofNat 64 arrObj.cap ≠ 0 := by assumption
          have hcapNe0 : arrObj.cap ≠ 0 := fun h0 => hc0 (by simp [h0])
          have hgtMax : 33554428 < arrObj.cap % 2 ^ 64 * BitVec.toNat (2 : BitVec 64) % 2 ^ 64 :=
            by assumption
          have hmul : arrObj.cap % 2 ^ 64 * BitVec.toNat (2 : BitVec 64) % 2 ^ 64 =
              arrObj.cap * 2 := by
            rw [hcapMod]; have h2 : (2#64 : BitVec 64).toNat = 2 := rfl
            rw [show BitVec.toNat (2 : BitVec 64) = 2 from h2, Nat.mod_eq_of_lt
              (by have := hcanon.2.2.2.2.2.2.2; unfold arrMaxCap at *; omega)]
          rw [hmul] at hgtMax
          have hmin : min arrMaxCap (arrObj.cap * 2) = 33554428 := by unfold arrMaxCap; omega
          simp [newCap, arrEnsureCap, hne, hnlt, hcapNe0, hmin]
        · exfalso
          have hge2 : arrObj.cap % 2 ^ 64 * BitVec.toNat (2 : BitVec 64) % 2 ^ 64 ≤
              arrObj.fields.length % 2 ^ 64 := by assumption
          have hc0 : BitVec.ofNat 64 arrObj.cap ≠ 0 := by assumption
          have hcapNe0 : arrObj.cap ≠ 0 := fun h0 => hc0 (by simp [h0])
          have hmul : arrObj.cap % 2 ^ 64 * BitVec.toNat (2 : BitVec 64) % 2 ^ 64 =
              arrObj.cap * 2 := by
            rw [hcapMod]; have h2 : (2#64 : BitVec 64).toNat = 2 := rfl
            rw [show BitVec.toNat (2 : BitVec 64) = 2 from h2, Nat.mod_eq_of_lt
              (by have := hcanon.2.2.2.2.2.2.2; unfold arrMaxCap at *; omega)]
          rw [hmul, hlenMod] at hge2
          have := hcanon.2.2.2.2.2.2.1; omega
        · exfalso
          have hge2 : arrObj.cap % 2 ^ 64 * BitVec.toNat (2 : BitVec 64) % 2 ^ 64 ≤
              arrObj.fields.length % 2 ^ 64 := by assumption
          have hc0 : BitVec.ofNat 64 arrObj.cap ≠ 0 := by assumption
          have hcapNe0 : arrObj.cap ≠ 0 := fun h0 => hc0 (by simp [h0])
          have hmul : arrObj.cap % 2 ^ 64 * BitVec.toNat (2 : BitVec 64) % 2 ^ 64 =
              arrObj.cap * 2 := by
            rw [hcapMod]; have h2 : (2#64 : BitVec 64).toNat = 2 := rfl
            rw [show BitVec.toNat (2 : BitVec 64) = 2 from h2, Nat.mod_eq_of_lt
              (by have := hcanon.2.2.2.2.2.2.2; unfold arrMaxCap at *; omega)]
          rw [hmul, hlenMod] at hge2
          have := hcanon.2.2.2.2.2.2.1; omega
        · apply hJnc
          refine ⟨rfl, ?_⟩
          have hne : expand ≠ 0#64 := by assumption
          have hnlt : ¬ arrObj.fields.length % 2 ^ 64 < arrObj.cap % 2 ^ 64 := by assumption
          rw [hlenMod, hcapMod] at hnlt
          have hc0 : BitVec.ofNat 64 arrObj.cap ≠ 0 := by assumption
          have hcapNe0 : arrObj.cap ≠ 0 := fun h0 => hc0 (by simp [h0])
          have hngt : ¬ 33554428 < arrObj.cap % 2 ^ 64 * BitVec.toNat (2 : BitVec 64) % 2 ^ 64 :=
            by assumption
          have hmul : arrObj.cap % 2 ^ 64 * BitVec.toNat (2 : BitVec 64) % 2 ^ 64 =
              arrObj.cap * 2 := by
            rw [hcapMod]; have h2 : (2#64 : BitVec 64).toNat = 2 := rfl
            rw [show BitVec.toNat (2 : BitVec 64) = 2 from h2, Nat.mod_eq_of_lt
              (by have := hcanon.2.2.2.2.2.2.2; unfold arrMaxCap at *; omega)]
          rw [hmul] at hngt
          have hmin : min arrMaxCap (arrObj.cap * 2) = arrObj.cap * 2 := by unfold arrMaxCap; omega
          simp only [newCap, arrEnsureCap, hne, ↓reduceIte, hnlt, hcapNe0, hmin]
          rw [show (2 : BitVec 64) = BitVec.ofNat 64 2 from rfl, ← BitVec.ofNat_mul]
        · apply hJnc
          refine ⟨rfl, ?_⟩
          have hex : expand = 0#64 := by assumption
          simp [newCap, arrEnsureCap, hex]
  · intro Jouter hJouter
    r2_steps
    · have hrc1 := arr_rc_of_mask_eq1 hwf (by assumption)
      have hex : expand = 0#64 := by assumption
      have hnp : ¬ (expand ≠ 0#64 ∧ arrObj.cap ≤ arrObj.fields.length ∧
          arrMaxCap ≤ arrObj.cap) := by simp [hex]
      rw [ite_eq_right_of_eq_false _ _ (eq_false hnp)] at hPost
      exact arr_ensure_fast_ok hcanon rfl hrc1 (Or.inl hex) hm hPost.2
    · have hrc1 := arr_rc_of_mask_eq1 hwf (by assumption)
      have hlt : arrObj.fields.length % 2 ^ 64 < arrObj.cap % 2 ^ 64 := by assumption
      rw [hlenMod, hcapMod] at hlt
      have hnp : ¬ (expand ≠ 0#64 ∧ arrObj.cap ≤ arrObj.fields.length ∧
          arrMaxCap ≤ arrObj.cap) := by omega
      rw [ite_eq_right_of_eq_false _ _ (eq_false hnp)] at hPost
      exact arr_ensure_fast_ok hcanon rfl hrc1 (Or.inr hlt) hm hPost.2
    · apply hJouter
      refine ⟨rfl, Or.inr ⟨by assumption, ?_⟩⟩
      have hnlt : ¬ arrObj.fields.length % 2 ^ 64 < arrObj.cap % 2 ^ 64 := by assumption
      rw [hlenMod, hcapMod] at hnlt
      omega
    · apply hJouter
      exact ⟨rfl, Or.inl (arr_rc_ne1_of_mask hwf (by assumption))⟩

/-! ## 3. `lcnf_array_mk_empty` & `lcnf_array_get` WP Proofs -/

theorem lcnf_array_mk_empty_wp :
    ∀ xs m Q X,
      lcnfArrayMkEmptySpec xs m Q X → Func.wp rtR2Env lcnf_array_mk_empty_body xs m Q X := by
  intro ⟨rt, cap, ⟨⟩⟩ m Q X hSpec
  dsimp only [Func.wp, lcnf_array_mk_empty_body, lcnfArrayMkEmptySpec] at hSpec ⊢
  change LeanQbe.T.wp _ _ _ _ _
  let c64 : BitVec 64 := if (cap &&& 1#64) ≠ 0#64 then cap >>> 1#64 else 0#64
  apply wp_join_group (P := fun (xs : Tup Val [i64]) m' => match xs with
    | (x, PUnit.unit) => m' = m ∧ x = c64)
  · intro _ ⟨x, ⟨⟩⟩ m' ⟨rfl, hx⟩
    subst hx
    change LeanQbe.T.wp _ _ _ _ _
    have hcEq : c64.toNat = if (cap &&& 1#64) ≠ 0#64 then (cap >>> 1).toNat else 0 := by
      dsimp only [c64]; split <;> simp
    by_cases hvalid : (if (cap &&& 1#64) ≠ 0#64 then (cap >>> 1).toNat else 0) ≤ arrMaxCap
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hvalid)] at hSpec
      rcases hSpec with ⟨st, R, hav, hm, hk⟩
      r2_call rtR2Env_r2_alloc_array
      dsimp only [r2AllocArraySpec, vals, Tup.map, Arg.val]
      have h0c : (0 : BitVec 64).toNat ≤ c64.toNat ∧ c64.toNat ≤ arrMaxCap := by
        rw [hcEq]; exact ⟨Nat.zero_le _, hvalid⟩
      rw [ite_eq_left_of_eq_true _ _ (eq_true h0c)]
      refine ⟨st, R, by rw [hcEq]; exact hav, hm, fun p st' m1 hp0 hp8 hpr hrem _ hm1 => ?_⟩
      r2_steps
      have hmObj : (rtC0Inv rt st' ⋆
          lcnfObjMem (mkArrObj p 1#32 (if (cap &&& 1#64) ≠ 0#64 then (cap >>> 1).toNat else 0) []) ⋆
          R) m1 := by
        have hpParts : (cell64 p (mkArrObj p 1#32
              (if (cap &&& 1#64) ≠ 0#64 then (cap >>> 1).toNat else 0) []).header ⋆
            cell64 (p + 8#64) (BitVec.ofNat 64 ([] : List (BitVec 64)).length) ⋆
            cell64 (p + 16#64) (BitVec.ofNat 64
              (if (cap &&& 1#64) ≠ 0#64 then (cap >>> 1).toNat else 0)) ⋆
            array64 (p + 24#64) [] ⋆
            region (p + BitVec.ofNat 64 (24 + 8 * ([] : List (BitVec 64)).length))
              (8 * ((if (cap &&& 1#64) ≠ 0#64 then (cap >>> 1).toNat else 0) -
                ([] : List (BitVec 64)).length)) ⋆
            (rtC0Inv rt st' ⋆ R)) m1 := by
          rw [mkArrObj_header, List.length_nil, Nat.mul_zero, Nat.add_zero, Nat.sub_zero,
            array64_nil, Std.ExtHashMap.sep_emp]
          rw [← hcEq, BitVec.ofNat_toNat, BitVec.setWidth_eq]
          rw [show (0#64 : BitVec 64) = (0 : BitVec 64) from rfl]
          rw [show (BitVec.ofNat 64 24 : BitVec 64) = 24#64 from rfl]
          exact sep_cast hm1 (by ac_rfl)
        exact sep_cast (mkArrObj_mem_of_parts hpParts) (by ac_rfl)
      have hcan : ArrCanon
          (mkArrObj p 1#32 (if (cap &&& 1#64) ≠ 0#64 then (cap >>> 1).toNat else 0) []) :=
        mkArrObj_canon hp0 hp8 (by decide) (by simp) hvalid
      exact hk p st' m1 hp0 hp8 hpr hrem hcan hmObj
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hvalid)] at hSpec
      r2_call rtR2Env_r2_alloc_array
      dsimp only [r2AllocArraySpec, vals, Tup.map, Arg.val]
      have hnot : ¬ ((0 : BitVec 64).toNat ≤ c64.toNat ∧ c64.toNat ≤ arrMaxCap) := by
        rw [hcEq]; intro ⟨_, hle⟩; exact hvalid hle
      rw [ite_eq_right_of_eq_false _ _ (eq_false hnot)]
      exact hSpec
  · intro J hJ
    r2_steps
    · apply hJ
      refine ⟨rfl, ?_⟩
      dsimp only [c64]
      have hne : (cap &&& 1#64) ≠ 0#64 := by assumption
      simp [hne]
    · apply hJ
      refine ⟨rfl, ?_⟩
      dsimp only [c64]
      have heq : (cap &&& 1#64) = 0#64 := by assumption
      simp [heq]

theorem lcnf_array_get_wp :
    ∀ xs m Q X, lcnfArrayGetSpec xs m Q X → Func.wp rtR2Env lcnf_array_get_body xs m Q X := by
  intro ⟨rt, dv, arr, idx, flags, ⟨⟩⟩ m Q X
    ⟨arrObj, objs, R, harrMem, haddr, hcanon, hwfObjs, hm, hPost⟩
  subst haddr
  have hlen64 := hcanon.len_lt_64
  have hlenMod : arrObj.fields.length % 2 ^ 64 = arrObj.fields.length := Nat.mod_eq_of_lt hlen64
  obtain ⟨k, hkLen, hkEq⟩ := List.getElem_of_mem harrMem
  have hmArr : (lcnfObjMem arrObj ⋆ (lcnfHeap (objs.eraseIdx k) ⋆ R)) m := by
    have hf := lcnfHeap_focus objs hkLen
    rw [hkEq, ← lcnfHeap_eraseIdx objs] at hf
    rw [hf] at hm
    exact sep_cast hm (by ac_rfl)
  dsimp only [Func.wp, lcnf_array_get_body]
  change LeanQbe.T.wp _ _ _ _ _
  r2_steps
  apply wp_load_of (arr_load_sz_mid hcanon hmArr)
  have handleRet : ∀ (ret : BitVec 64) {hcmp},
      (¬ ((flags &&& 1#64) ≠ 0#64) ∧ ret ≠ 0#64 ∧ (ret &&& 1#64) = 0#64 →
        ∃ o ∈ objs, o.addr = ret) →
      ∀ (J : Cont []),
        (∀ m', ((flags &&& 1#64) ≠ 0#64 → m' = m) →
          (lcnfHeap (if (flags &&& 1#64) ≠ 0#64 ∨ ret = 0#64 ∨ (ret &&& 1#64) ≠ 0#64 then objs
            else objs.map (fun o => if o.addr = ret then o.withRc (incRcVal o.rc) else o)) ⋆ R) m' →
          J () m') →
        wp rtR2Env Q X
          (Expr.let_ (Op.mk (OpCode.cmp CmpOp.eq i64 Ty.bool hcmp)
              (Arg.var (flags &&& 1#64), Arg.imm 0, ()))
            fun p => Expr.jnz (Arg.var p.fst)
              (Expr.call "r2_inc_obj" (as := [i64]) (bs := [])
                (Arg.var ret, ()) (fun _ => Expr.jump J ()))
              (Expr.jump J ())) m := by
    intro ret _ hcl J hJret
    r2_steps
    · have hnb : ¬ (flags &&& 1#64) ≠ 0#64 := fun h => h (by assumption)
      r2_call rtR2Env_r2_inc_obj
      dsimp only [r2IncObjSpec, vals, Tup.map, Arg.val]
      by_cases hskip : ret = 0#64 ∨ (ret &&& 1#64) ≠ 0#64
      · rw [ite_eq_left_of_eq_true _ _ (eq_true hskip)]
        r2_steps
        refine hJret m (fun h => absurd h hnb) ?_
        have hor : (flags &&& 1#64) ≠ 0#64 ∨ ret = 0#64 ∨ (ret &&& 1#64) ≠ 0#64 := Or.inr hskip
        rwa [ite_eq_left_of_eq_true _ _ (eq_true hor)]
      · rw [ite_eq_right_of_eq_false _ _ (eq_false hskip)]
        have hr0 : ret ≠ 0#64 := fun h => hskip (Or.inl h)
        have hr1 : (ret &&& 1#64) = 0#64 := Classical.not_not.mp fun h => hskip (Or.inr h)
        obtain ⟨o, hoMem, hoAddr⟩ := hcl ⟨hnb, hr0, hr1⟩
        obtain ⟨jo, hjoLen, hjoEq⟩ := List.getElem_of_mem hoMem
        have hmObj : (lcnfObjMem o ⋆ (lcnfHeap (objs.eraseIdx jo) ⋆ R)) m := by
          have hf := lcnfHeap_focus objs hjoLen
          rw [hjoEq, ← lcnfHeap_eraseIdx objs] at hf
          rw [hf] at hm
          exact sep_cast hm (by ac_rfl)
        refine ⟨o, lcnfHeap (objs.eraseIdx jo) ⋆ R, hoAddr, hwfObjs o hoMem,
          hmObj, fun m' hm' => ?_⟩
        r2_steps
        have hnodup := lcnfHeap_nodup_addrs hm
        refine hJret m' (fun h => absurd h hnb) ?_
        have hnotOr : ¬ ((flags &&& 1#64) ≠ 0#64 ∨ ret = 0#64 ∨ (ret &&& 1#64) ≠ 0#64) := by
          intro h; rcases h with hb | h0 | h1
          · exact hnb hb
          · exact hr0 h0
          · exact hskip (Or.inr h1)
        rw [ite_eq_right_of_eq_false _ _ (eq_false hnotOr)]
        have hsetMap := list_set_eq_map_of_nodup hnodup hjoLen
          (fun obj => obj.withRc (incRcVal obj.rc))
        rw [hjoEq, hoAddr] at hsetMap
        rw [← hsetMap]
        have hf := lcnfHeap_focus (objs.set jo (o.withRc (incRcVal o.rc)))
          (by simp; exact hjoLen)
        rw [← lcnfHeap_eraseIdx _, List.getElem_set_self, eraseIdx_set_eq_self] at hf
        rw [hf]
        exact sep_cast hm' (by ac_rfl)
    · have hb : (flags &&& 1#64) ≠ 0#64 := by assumption
      apply hJret m (fun _ => rfl)
      have hor : (flags &&& 1#64) ≠ 0#64 ∨ ret = 0#64 ∨ (ret &&& 1#64) ≠ 0#64 := Or.inl hb
      rwa [ite_eq_left_of_eq_true _ _ (eq_true hor)]
  by_cases hunb : (flags &&& 2#64) ≠ 0#64
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hunb)] at hPost
    by_cases hoob : arrObj.fields.length ≤ idx.toNat
    · rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨hunb, hoob⟩)] at hPost
      r2_steps <;> first
        | exact hPost
        | (exfalso
           have hlt : idx.toNat < arrObj.fields.length % 2 ^ 64 := by assumption
           rw [hlenMod] at hlt; omega)
    · have hnp : ¬ ((flags &&& 2#64) ≠ 0#64 ∧ arrObj.fields.length ≤ idx.toNat) :=
        fun ⟨_, h⟩ => hoob h
      rw [ite_eq_right_of_eq_false _ _ (eq_false hnp)] at hPost
      have hlt : idx.toNat < arrObj.fields.length := Nat.lt_of_not_le hoob
      rw [dite_eq_left hlt] at hPost
      rcases hPost with ⟨hcl, hk⟩
      r2_steps <;> first
        | (exfalso
           have hge : arrObj.fields.length % 2 ^ 64 ≤ idx.toNat := by assumption
           rw [hlenMod] at hge; omega)
        | {
        apply wp_load_of (arr_load_elem_mid hcanon hlt hmArr)
        apply wp_join_group (P := fun xs m' => xs = () ∧
          ((flags &&& 1#64) ≠ 0#64 → m' = m) ∧
          (lcnfHeap (if (flags &&& 1#64) ≠ 0#64 ∨ arrObj.fields[idx.toNat] = 0#64 ∨
              (arrObj.fields[idx.toNat] &&& 1#64) ≠ 0#64 then objs
            else objs.map (fun o => if o.addr = arrObj.fields[idx.toNat]
              then o.withRc (incRcVal o.rc) else o)) ⋆ R) m')
        · intro _ ⟨⟩ m' ⟨_, hb, hm'⟩
          r2_steps
          exact hk m' hb hm'
        · intro J hJ
          exact handleRet arrObj.fields[idx.toNat] hcl J
            (fun m' hb hm' => hJ () m' ⟨rfl, hb, hm'⟩) }
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hunb)] at hPost
    have hnotUnb : ¬ ((flags &&& 2#64) ≠ 0#64 ∧ arrObj.fields.length ≤ idx.toNat) :=
      fun ⟨h, _⟩ => hunb h
    rw [ite_eq_right_of_eq_false _ _ (eq_false hnotUnb)] at hPost
    have handleDvNeg :
        (flags &&& 1#64) ≠ 0#64 →
        (∀ m', ((flags &&& 1#64) ≠ 0#64 → m' = m) →
          (lcnfHeap (if (flags &&& 1#64) ≠ 0#64 ∨ dv = 0#64 ∨ (dv &&& 1#64) ≠ 0#64 then objs
            else objs.map (fun o => if o.addr = dv then o.withRc (incRcVal o.rc) else o)) ⋆ R) m' →
          Q (dv, ()) m') →
        Q (dv, ()) m := by
      intro hf hkDv
      refine hkDv m (fun _ => rfl) ?_
      rw [ite_eq_left_of_eq_true _ _ (eq_true (Or.inl hf))]
      exact hm
    have handleDvCall :
        ∀ (J : Cont []),
        (∀ (xs : Tup Val []) (m' : Mem 64),
          wp rtR2Env Q X
            ((Blocks.cons (fun p => Expr.ret (Arg.var dv, ())) Blocks.nil).get
              Member.here xs) m' → J xs m') →
        (flags &&& 1#64) = 0#64 →
        (¬ (flags &&& 1#64) ≠ 0#64 ∧ dv ≠ 0#64 ∧ (dv &&& 1#64) = 0#64 →
          ∃ o, o ∈ objs ∧ o.addr = dv) →
        (∀ m', ((flags &&& 1#64) ≠ 0#64 → m' = m) →
          (lcnfHeap (if (flags &&& 1#64) ≠ 0#64 ∨ dv = 0#64 ∨ (dv &&& 1#64) ≠ 0#64 then objs
            else objs.map (fun o => if o.addr = dv then o.withRc (incRcVal o.rc) else o)) ⋆ R) m' →
          Q (dv, ()) m') →
        wp rtR2Env Q X
          (Expr.call "r2_inc_obj" (as := [i64]) (bs := []) (Arg.var dv, ())
            fun _ => Expr.jump J ()) m := by
      intro J hJret hf0 hclDv hkDv
      have hnf : ¬ (flags &&& 1#64) ≠ 0#64 := by simp [hf0]
      r2_call rtR2Env_r2_inc_obj
      dsimp only [r2IncObjSpec, vals, Tup.map, Arg.val]
      by_cases hskip : dv = 0#64 ∨ (dv &&& 1#64) ≠ 0#64
      · rw [ite_eq_left_of_eq_true _ _ (eq_true hskip)]
        r2_steps
        try (apply hJret; r2_steps)
        refine hkDv m (fun h => absurd h hnf) ?_
        rw [ite_eq_left_of_eq_true _ _ (eq_true (Or.inr hskip))]
        exact hm
      · rw [ite_eq_right_of_eq_false _ _ (eq_false hskip)]
        have hdv0 : dv ≠ 0#64 := fun h => hskip (Or.inl h)
        have hdv1 : (dv &&& 1#64) = 0#64 := Classical.not_not.mp fun h => hskip (Or.inr h)
        obtain ⟨o, hoMem, hoAddr⟩ := hclDv ⟨hnf, hdv0, hdv1⟩
        obtain ⟨jo, hjoLen, hjoEq⟩ := List.getElem_of_mem hoMem
        have hmObj : (lcnfObjMem o ⋆ (lcnfHeap (objs.eraseIdx jo) ⋆ R)) m := by
          have hf := lcnfHeap_focus objs hjoLen
          rw [hjoEq, ← lcnfHeap_eraseIdx objs] at hf
          rw [hf] at hm
          exact sep_cast hm (by ac_rfl)
        refine ⟨o, lcnfHeap (objs.eraseIdx jo) ⋆ R, hoAddr, hwfObjs o hoMem,
          hmObj, fun m' hm' => ?_⟩
        r2_steps
        try (apply hJret; r2_steps)
        have hnodup := lcnfHeap_nodup_addrs hm
        refine hkDv m' (fun h => absurd h hnf) ?_
        have hnotOr : ¬ ((flags &&& 1#64) ≠ 0#64 ∨ dv = 0#64 ∨ (dv &&& 1#64) ≠ 0#64) := by
          intro h; rcases h with hb | h0 | h1
          · exact hnf hb
          · exact hdv0 h0
          · exact hskip (Or.inr h1)
        rw [ite_eq_right_of_eq_false _ _ (eq_false hnotOr)]
        have hsetMap := list_set_eq_map_of_nodup hnodup hjoLen
          (fun obj => obj.withRc (incRcVal obj.rc))
        rw [hjoEq, hoAddr] at hsetMap
        rw [← hsetMap]
        have hf := lcnfHeap_focus (objs.set jo (o.withRc (incRcVal o.rc)))
          (show jo < (objs.set jo _).length from by rw [List.length_set]; exact hjoLen)
        rw [← lcnfHeap_eraseIdx _, List.getElem_set_self, eraseIdx_set_eq_self] at hf
        rw [hf]
        exact sep_cast hm' (by ac_rfl)
    by_cases htag : (idx &&& 1#64) ≠ 0#64
    · rw [ite_eq_left_of_eq_true _ _ (eq_true htag)] at hPost
      by_cases hlt : (idx >>> 1).toNat < arrObj.fields.length
      · rw [dite_eq_left hlt] at hPost
        rcases hPost with ⟨hcl, hk⟩
        have hlt2 : (idx >>> 1#64).toNat < arrObj.fields.length := hlt
        r2_steps <;> first
          | (exfalso; exact hunb (by assumption))
          | (exfalso
             have hnlt : ¬ (idx >>> 1).toNat < arrObj.fields.length % 2 ^ 64 := by assumption
             rw [hlenMod] at hnlt; exact hnlt hlt)
          | {
          apply wp_load_of (arr_load_elem_mid hcanon hlt2 hmArr)
          apply wp_join_group (P := fun (xs : Tup Val []) m' => xs = () ∧
            ((flags &&& 1#64) ≠ 0#64 → m' = m) ∧
            (lcnfHeap (if (flags &&& 1#64) ≠ 0#64 ∨ arrObj.fields[(idx >>> 1).toNat] = 0#64 ∨
                (arrObj.fields[(idx >>> 1).toNat] &&& 1#64) ≠ 0#64 then objs
              else objs.map (fun o => if o.addr = arrObj.fields[(idx >>> 1).toNat]
                then o.withRc (incRcVal o.rc) else o)) ⋆ R) m')
          · intro _ ⟨⟩ m' ⟨_, hb, hm'⟩
            r2_steps
            exact hk m' hb hm'
          · intro J hJ
            exact handleRet arrObj.fields[(idx >>> 1).toNat] hcl J
              (fun m' hb hm' => hJ () m' ⟨rfl, hb, hm'⟩) }
      · rw [dite_eq_right hlt] at hPost
        rcases hPost with ⟨hcl, hk⟩
        r2_steps <;> first
          | (exfalso; exact hunb (by assumption))
          | (exfalso
             have hlt2 : (idx >>> 1).toNat < arrObj.fields.length % 2 ^ 64 := by assumption
             rw [hlenMod] at hlt2; exact hlt hlt2)
          | exact handleDvCall _ (by assumption) (by assumption) hcl hk
          | exact handleDvNeg (by assumption) hk
    · rw [ite_eq_right_of_eq_false _ _ (eq_false htag)] at hPost
      rcases hPost with ⟨hcl, hk⟩
      r2_steps <;> first
        | (exfalso; exact hunb (by assumption))
        | exact handleDvCall _ (by assumption) (by assumption) hcl hk
        | exact handleDvNeg (by assumption) hk

/-! ## 4. `lcnf_array_set`, `lcnf_array_push`, `lcnf_array_pop`, `lcnf_array_swap` WP Proofs -/

private theorem arr_r2_dec_in_bounds {rt : BitVec 64} {arrObj : LcnfObj} {objs : List LcnfObj}
    {k : Nat} {st st1 : RtC0State} {rObj : LcnfObj} {mid1 mid2 : List LcnfObj}
    {old : BitVec 64} {R : Mem 64 → Prop} {m : Mem 64}
    (hk : k < objs.length) (hobj : objs[k] = arrObj) (hcanon : ArrCanon arrObj)
    (hnotSelf : ¬ arrObj.addr ∈ arrObj.fields)
    (hwfObjs : ∀ o ∈ objs, o.Wf) (hclosed : lcnfHeapClosed objs)
    (hrc1Ok : arrObj.rc = 1#32 → old ≠ 0#64 → (old &&& 1#64) = 0#64 →
      ∀ o2 ∈ rObj :: objs.eraseIdx k, o2.addr = old → o2.rc = 1#32 →
        (rObj :: objs.eraseIdx k).length ≤ st.workCap ∧
          lcnfHeapClosed (rObj :: objs.eraseIdx k) ∧ RcSound old (rObj :: objs.eraseIdx k))
    (hbound : arrObj.rc ≠ 1#32 → ∀ y ∈ objs.eraseIdx k,
      0 < y.rc.toInt → y.rc.toInt + (List.count y.addr arrObj.fields : Int) < 2147483648)
    (holdMem : old ∈ arrObj.fields) (hcanR : ArrCanon rObj)
    (hpr1 : st1.PreservesMeta st)
    (hm1 : arrObj.rc = 1#32 → mid1 = objs.eraseIdx k)
    (hm2 : arrObj.rc ≠ 1#32 →
      mid1 = (incChildrenObjs arrObj.fields (objs.eraseIdx k)).insertIdx k
        (arrObj.withRc (decNonExclRc arrObj.rc)))
    (hmid2 : mid2 = rObj :: mid1) (_hm : (rtC0Inv rt st1 ⋆ lcnfHeap mid2 ⋆ R) m)
    (hold0 : old ≠ 0#64) (hold1 : (old &&& 1#64) = 0#64) :
    (∀ o ∈ mid2, o.Wf) ∧
      ∃ obj ∈ mid2, obj.addr = old ∧
        (obj.rc = 1#32 → mid2.length ≤ st1.workCap ∧ lcnfHeapClosed mid2 ∧ RcSound old mid2) := by
  have hwfArr := hwfObjs arrObj (hobj ▸ List.getElem_mem hk)
  have hwfMid1 : ∀ o ∈ mid1, o.Wf := by
    intro o ho
    by_cases hrc1 : arrObj.rc = 1#32
    · rw [hm1 hrc1] at ho
      exact hwfObjs o (mem_of_mem_eraseIdx_arr ho)
    · rw [hm2 hrc1] at ho
      rcases (List.mem_insertIdx
        (by simp [incChildrenObjs, List.length_eraseIdx, hk]; omega)).mp ho with rfl | hinc
      · exact arrObj_wf_decNonExclRc hwfArr hrc1
      · have hinc' : o ∈ incChildrenObjs (arrObj.fields.take arrObj.fields.length)
            (objs.eraseIdx k) := by simpa [List.take_length] using hinc
        exact incChildrenObjs_wf
          (fun y hy => hwfObjs y (mem_of_mem_eraseIdx_arr hy))
          (hbound hrc1) arrObj.fields.length o hinc'
  have hwfMid2 : ∀ o ∈ mid2, o.Wf := by
    intro o ho
    rw [hmid2] at ho
    rcases List.mem_cons.mp ho with rfl | hm1'
    · exact hcanR.wf
    · exact hwfMid1 o hm1'
  refine ⟨hwfMid2, ?_⟩
  obtain ⟨y, hyInErase, hyAddr⟩ :=
    arr_cow_closed_bound hk hobj hcanon hnotSelf hclosed old holdMem hold1
  by_cases hrc1 : arrObj.rc = 1#32
  · have hyMid2 : y ∈ mid2 := by rw [hmid2, hm1 hrc1]; exact List.mem_cons_of_mem _ hyInErase
    refine ⟨y, hyMid2, hyAddr, fun hyRc => ?_⟩
    have hwc : st1.workCap = st.workCap := by simp [RtC0State.workCap, hpr1.2.2.2.2.2.1]
    rw [hwc]
    have hyMid2' : y ∈ rObj :: objs.eraseIdx k := List.mem_cons_of_mem _ hyInErase
    have hspec := hrc1Ok hrc1 hold0 hold1 y hyMid2' hyAddr hyRc
    rw [hmid2, hm1 hrc1]
    exact hspec
  · let z := if 0 < y.rc.toInt
      then y.withRc (BitVec.ofNat 32 (y.rc.toNat + List.count y.addr arrObj.fields)) else y
    have hzInc : z ∈ incChildrenObjs arrObj.fields (objs.eraseIdx k) := by
      simp only [incChildrenObjs, List.mem_map]
      exact ⟨y, hyInErase, rfl⟩
    have hzAddr : z.addr = old := by dsimp only [z]; split <;> exact hyAddr
    have hzMid2 : z ∈ mid2 := by
      rw [hmid2, hm2 hrc1]
      exact List.mem_cons_of_mem _
        ((List.mem_insertIdx
          (by simp [incChildrenObjs, List.length_eraseIdx, hk]; omega)).mpr (Or.inr hzInc))
    have hzne1 : z.rc ≠ 1#32 :=
      incChildrenObjs_rc_ne_one (fun o ho => hwfObjs o (mem_of_mem_eraseIdx_arr ho))
        (hbound hrc1) holdMem hzInc hzAddr
    exact ⟨z, hzMid2, hzAddr, fun h1 => absurd h1 hzne1⟩

theorem lcnf_array_set_wp :
    ∀ xs m Q X, lcnfArraySetSpec xs m Q X → Func.wp rtR2Env lcnf_array_set_body xs m Q X := by
  intro ⟨rt, arr, idx, v, unboxed, ⟨⟩⟩ m Q X
    ⟨st, objs, k, hkLen, R, haddr, hcanon, hnotSelf, hwfObjs, hclosed, hm, hPost⟩
  let arrObj := objs[k]
  change arrObj.addr = arr at haddr
  have hlen64 := hcanon.len_lt_64
  have hlenMod : arrObj.fields.length % 2 ^ 64 = arrObj.fields.length := Nat.mod_eq_of_lt hlen64
  have hlenTo : (BitVec.ofNat 64 arrObj.fields.length).toNat = arrObj.fields.length := by
    rw [BitVec.toNat_ofNat, hlenMod]
  have hmArr : (lcnfObjMem arrObj ⋆ (rtC0Inv rt st ⋆ lcnfHeap (objs.eraseIdx k) ⋆ R)) m := by
    have hf := lcnfHeap_focus objs hkLen
    rw [← lcnfHeap_eraseIdx objs] at hf
    rw [hf] at hm
    exact sep_cast hm (by ac_rfl)
  dsimp only [Func.wp, lcnf_array_set_body]
  change LeanQbe.T.wp _ _ _ _ _
  r2_steps
  have hsz := arr_load_sz_mid hcanon hmArr
  rw [haddr] at hsz
  apply wp_load_of hsz
  let iNat :=
    if unboxed ≠ 0#64 then idx.toNat
    else if (idx &&& 1#64) ≠ 0#64 then (idx >>> 1).toNat
    else arrObj.fields.length
  let iBv : BitVec 64 :=
    if unboxed ≠ 0#64 then idx
    else if (idx &&& 1#64) ≠ 0#64 then idx >>> 1#64
    else BitVec.ofNat 64 arrObj.fields.length
  have hiTo : iBv.toNat = iNat := by
    dsimp only [iBv, iNat]
    split
    · rfl
    · split
      · rfl
      · exact hlenTo
  apply wp_join_group (P := fun (xs : Tup Val [i64]) m' => match xs with
    | (iv, PUnit.unit) => m' = m ∧ iv = iBv)
  · intro _ ⟨iv, ⟨⟩⟩ m' ⟨hmEq, hiv⟩
    subst hmEq; subst hiv
    change LeanQbe.T.wp _ _ _ _ _
    by_cases hlt : iNat < arrObj.fields.length
    · rw [dite_eq_left hlt] at hPost
      rcases hPost with ⟨hrcNe1Ok, hrc1Ok, _hvClose, hk⟩
      have hltMod : ¬ arrObj.fields.length % 2 ^ 64 ≤ iBv.toNat := by
        rw [hiTo, hlenMod]; omega
      r2_steps
      · exfalso; exact hltMod (by assumption)
      · r2_call rtR2Env_r2_ensure_excl_array
        dsimp only [r2EnsureExclArraySpec, vals, Tup.map, Arg.val]
        have hnotPanic : ¬ ((0 : BitVec 64) ≠ 0#64 ∧ arrObj.cap ≤ arrObj.fields.length ∧
            arrMaxCap ≤ arrObj.cap) := by simp
        have hcapEq :
            arrEnsureCap arrObj.fields.length arrObj.cap (0 : BitVec 64) = arrObj.cap := by
          simp [arrEnsureCap]
        have hmSplit : (rtC0Inv rt st ⋆ lcnfObjMem arrObj ⋆
            lcnfHeap (objs.eraseIdx k) ⋆ R) m' := sep_cast hmArr (by ac_rfl)
        have hwfEr : ∀ y ∈ objs.eraseIdx k, y.Wf :=
          fun y hy => hwfObjs y (mem_of_mem_eraseIdx_arr hy)
        refine ⟨st, arrObj, objs.eraseIdx k, R, haddr, hcanon, hwfEr, hmSplit, ?_, ?_⟩
        · intro hne
          refine ⟨arr_cow_closed_bound hkLen rfl hcanon hnotSelf hclosed, (hrcNe1Ok hne).2⟩
        · rw [ite_eq_right_of_eq_false _ _ (eq_false hnotPanic), hcapEq]
          refine ⟨fun hneed => ?_, fun r st1 mid0 m1 hr0 hr8 hpr1 hrem1 _ hout hm1 => ?_⟩
          · rcases hneed with hne | ⟨h0, _⟩
            · exact (hrcNe1Ok hne).1
            · exact absurd rfl h0
          · rcases hout with ⟨_, hcanPre, _, haddr1, hrc1Br, hrcNeBr⟩
            change LeanQbe.T.wp _ _ _ _ _
            r2_steps
            let rPre := mkArrObj r 1#32 arrObj.cap arrObj.fields
            let oldKeep := if arrObj.rc = 1#32 then emp
              else lcnfObjMem (arrObj.withRc (decNonExclRc arrObj.rc))
            have hm1Obj : (lcnfObjMem rPre ⋆ (rtC0Inv rt st1 ⋆ oldKeep ⋆
                lcnfHeap mid0 ⋆ R)) m1 := by
              dsimp only [rPre, oldKeep]
              exact sep_cast hm1 (by ac_rfl)
            have hloadOld := arr_load_elem_mid (i := iBv) hcanPre
              (by simp only [mkArrObj]; rw [hiTo]; exact hlt) hm1Obj
            simp only [mkArrObj, hiTo] at hloadOld
            let old := arrObj.fields[iNat]
            r2_steps
            apply wp_load_of hloadOld
            r2_steps
            have hm1S := lcnfObjMem_array_elim hcanPre hm1Obj
            have hmArrPre : (array64 (r + 24#64) arrObj.fields ⋆
                (cell64 r rPre.header ⋆
                  cell64 (r + 8#64) (BitVec.ofNat 64 rPre.fields.length) ⋆
                  cell64 (r + 16#64) (BitVec.ofNat 64 rPre.cap) ⋆
                  region (r + BitVec.ofNat 64 (24 + 8 * rPre.fields.length))
                    (8 * (rPre.cap - rPre.fields.length)) ⋆
                  rtC0Inv rt st1 ⋆ oldKeep ⋆ lcnfHeap mid0 ⋆ R)) m1 := by
              dsimp only [rPre, mkArrObj] at hm1S ⊢
              exact sep_cast hm1S (by ac_rfl)
            obtain ⟨hstOk, hm2⟩ := r2_c0_store_array64_add24_mul8 v hmArrPre
              (by rw [hiTo]; exact hlt)
            apply wp_store_sep ⟨hstOk, hm2⟩
            intro m2 hm2'
            rw [hiTo] at hm2'
            let rObj := mkArrObj r 1#32 arrObj.cap (arrObj.fields.set iNat v)
            have hlenNew : (arrObj.fields.set iNat v).length = arrObj.fields.length := by simp
            have hcanNew : ArrCanon rObj :=
              mkArrObj_canon hr0 hr8 (by decide)
                (by rw [hlenNew]; exact hcanon.2.2.2.2.2.2.1) hcanon.2.2.2.2.2.2.2
            let mid1 := if arrObj.rc = 1#32 then objs.eraseIdx k
              else (incChildrenObjs arrObj.fields (objs.eraseIdx k)).insertIdx k
                (arrObj.withRc (decNonExclRc arrObj.rc))
            let mid2 := rObj :: mid1
            have hm2Heap : (rtC0Inv rt st1 ⋆ lcnfHeap mid2 ⋆ R) m2 := by
              have hmRObj : (lcnfObjMem rObj ⋆
                  (rtC0Inv rt st1 ⋆ oldKeep ⋆ lcnfHeap mid0 ⋆ R)) m2 := by
                have hparts : (cell64 r (mkArrObj r 1#32 arrObj.cap
                      (arrObj.fields.set iNat v)).header ⋆
                    cell64 (r + 8#64) (BitVec.ofNat 64 (arrObj.fields.set iNat v).length) ⋆
                    cell64 (r + 16#64) (BitVec.ofNat 64 arrObj.cap) ⋆
                    array64 (r + 24#64) (arrObj.fields.set iNat v) ⋆
                    region (r + BitVec.ofNat 64 (24 + 8 * (arrObj.fields.set iNat v).length))
                      (8 * (arrObj.cap - (arrObj.fields.set iNat v).length)) ⋆
                    (rtC0Inv rt st1 ⋆ oldKeep ⋆ lcnfHeap mid0 ⋆ R)) m2 := by
                  rw [mkArrObj_header, hlenNew]
                  have hrPreHdr : rPre.header = arrHeaderWord :=
                    mkArrObj_header r arrObj.cap arrObj.fields
                  dsimp only [rPre] at hm2'
                  rw [hrPreHdr] at hm2'
                  exact sep_cast hm2' (by ac_rfl)
                exact mkArrObj_mem_of_parts hparts
              have hmMid1 : (oldKeep ⋆ lcnfHeap mid0) = lcnfHeap mid1 := by
                by_cases hrc1 : arrObj.rc = 1#32
                · have h1 := hrc1Br hrc1
                  dsimp only [oldKeep, mid1]
                  simp only [hrc1, ↓reduceIte, emp_sep, h1.1]
                · have h2 := hrcNeBr hrc1
                  dsimp only [oldKeep, mid1]
                  simp only [hrc1, ↓reduceIte, h2.1]
                  have hlenInc : k ≤ (incChildrenObjs arrObj.fields (objs.eraseIdx k)).length := by
                    simp [incChildrenObjs, List.length_eraseIdx, hkLen]; omega
                  rw [lcnfHeap_insertIdx hlenInc]
              dsimp only [mid2]
              rw [lcnfHeap, ← hmMid1]
              exact sep_cast hmRObj (by ac_rfl)
            r2_call rtR2Env_r2_dec_obj
            dsimp only [r2DecObjSpec, vals, Tup.map, Arg.val]
            by_cases hskip : old = 0#64 ∨ (old &&& 1#64) ≠ 0#64
            · rw [ite_eq_left_of_eq_true _ _ (eq_true hskip)]
              r2_steps
              exact hk r st1 mid2 m2 hr0 hr8 hpr1 hrem1 (fun h1 => haddr ▸ haddr1 h1 (Or.inl rfl))
                rObj mid1 mid2 rfl
                (fun h1 => by
                dsimp only [mid1, arrObj] at *; rw [ite_eq_left_of_eq_true _ _ (eq_true h1)])
                (fun hne => by
                dsimp only [mid1, arrObj] at *; rw [ite_eq_right_of_eq_false _ _ (eq_false hne)])
                rfl (by
                dsimp only [old] at hskip; dsimp only [DecObjRel]
                rw [ite_eq_left_of_eq_true _ _ (eq_true hskip)]) hm2Heap
            · rw [ite_eq_right_of_eq_false _ _ (eq_false hskip)]
              have hold0 : old ≠ 0#64 := fun h => hskip (Or.inl h)
              have hold1 : (old &&& 1#64) = 0#64 := Classical.not_not.mp fun h => hskip (Or.inr h)
              have hrc1OkCast : arrObj.rc = 1#32 → old ≠ 0#64 → (old &&& 1#64) = 0#64 →
                  ∀ o2 ∈ rObj :: objs.eraseIdx k, o2.addr = old → o2.rc = 1#32 →
                    (rObj :: objs.eraseIdx k).length ≤ st.workCap ∧
                      lcnfHeapClosed (rObj :: objs.eraseIdx k) ∧
                      RcSound old (rObj :: objs.eraseIdx k) := by
                intro h1 ho0 ho1
                have hrEq := haddr ▸ haddr1 h1 (Or.inl rfl)
                have hrObjEq : rObj = mkArrObj arr 1#32 arrObj.cap (arrObj.fields.set iNat v) := by
                  dsimp only [rObj]; rw [hrEq]
                rw [hrObjEq]
                exact hrc1Ok h1 ho0 ho1
              obtain ⟨hwfMid2, obj, hobjMem, hobjAddr, hobjRc1⟩ :=
                arr_r2_dec_in_bounds hkLen rfl hcanon hnotSelf hwfObjs hclosed hrc1OkCast
                  (fun hne => (hrcNe1Ok hne).2) (List.getElem_mem hlt) hcanNew hpr1
                  (fun h1 => by
                dsimp only [mid1, arrObj] at *
                rw [ite_eq_left_of_eq_true _ _ (eq_true h1)]) (fun hne => by
                dsimp only [mid1, arrObj] at *
                rw [ite_eq_right_of_eq_false _ _ (eq_false hne)]) rfl
                  hm2Heap hold0 hold1
              refine ⟨st1, mid2, R, ⟨obj, hobjMem, hobjAddr, hobjRc1⟩, hwfMid2, hm2Heap, ?_⟩
              intro st2 objs' m3 hpr2 hrem2 hdec hm3
              r2_steps
              exact hk r st2 objs' m3 hr0 hr8 (hpr1.trans hpr2) (by omega)
                (fun h1 => haddr ▸ haddr1 h1 (Or.inl rfl))
                rObj mid1 mid2 rfl
                (fun h1 => by
                dsimp only [mid1, arrObj] at *; rw [ite_eq_left_of_eq_true _ _ (eq_true h1)])
                (fun hne => by
                dsimp only [mid1, arrObj] at *; rw [ite_eq_right_of_eq_false _ _ (eq_false hne)])
                rfl hdec hm3
    · rw [dite_eq_right hlt] at hPost
      rcases hPost with ⟨hvClose, hk⟩
      have hgeMod : arrObj.fields.length % 2 ^ 64 ≤ iBv.toNat := by rw [hiTo, hlenMod]; omega
      r2_steps
      · r2_call rtR2Env_r2_dec_obj
        dsimp only [r2DecObjSpec, vals, Tup.map, Arg.val]
        by_cases hskip : v = 0#64 ∨ (v &&& 1#64) ≠ 0#64
        · rw [ite_eq_left_of_eq_true _ _ (eq_true hskip)]
          r2_steps
          exact hk st objs m' (RtC0State.PreservesMeta.refl st) rfl
            (by simp [DecObjRel, hskip]) hm
        · rw [ite_eq_right_of_eq_false _ _ (eq_false hskip)]
          have hv0 : v ≠ 0#64 := fun h => hskip (Or.inl h)
          have hv1 : (v &&& 1#64) = 0#64 := Classical.not_not.mp fun h => hskip (Or.inr h)
          obtain ⟨vo, hvoMem, hvoAddr, hvoRc1⟩ := hvClose ⟨hv0, hv1⟩
          refine ⟨st, objs, R, ⟨vo, hvoMem, hvoAddr, fun h1 =>
            ⟨(hvoRc1 h1).1, hclosed, (hvoRc1 h1).2⟩⟩, hwfObjs, hm, ?_⟩
          intro st' objs' m1 hpr hrem hdec hm1
          r2_steps
          exact hk st' objs' m1 hpr hrem hdec hm1
      · exfalso
        exact (by assumption : ¬ arrObj.fields.length % 2 ^ 64 ≤ iBv.toNat) hgeMod
  · intro Jout hJout
    r2_steps
    · apply hJout; refine ⟨rfl, ?_⟩
      have hu : unboxed ≠ 0#64 := fun h => (by assumption : ¬ unboxed = 0) h
      simp [iBv, hu]
    · apply hJout; refine ⟨rfl, ?_⟩
      have hu : (unboxed ≠ 0#64) = False := eq_false (fun h => h (by assumption))
      have hi1 : (idx &&& 1#64) ≠ 0#64 := by assumption
      simp [iBv, hu, hi1]
    · apply hJout; refine ⟨rfl, ?_⟩
      dsimp only [iBv]
      rw [ite_eq_right_of_eq_false _ _ (eq_false fun h => h (by assumption)),
        ite_eq_right_of_eq_false _ _ (eq_false fun h => h (by assumption))]

theorem lcnf_array_push_wp :
    ∀ xs m Q X,
      lcnfArrayPushSpec xs m Q X → Func.wp rtR2Env lcnf_array_push_body xs m Q X := by
  intro ⟨rt, arr, v, ⟨⟩⟩ m Q X
    ⟨st, arrObj, childObjs, R, haddr, hcanon, hwfChild, hm, hchildOk, hPost⟩
  subst haddr
  dsimp only [Func.wp, lcnf_array_push_body]
  change LeanQbe.T.wp _ _ _ _ _
  r2_call rtR2Env_r2_ensure_excl_array
  dsimp only [r2EnsureExclArraySpec, vals, Tup.map, Arg.val]
  refine ⟨st, arrObj, childObjs, R, rfl, hcanon, hwfChild, hm, hchildOk, ?_⟩
  by_cases hpanic : arrObj.cap ≤ arrObj.fields.length ∧ arrMaxCap ≤ arrObj.cap
  · have hpan1 : (1 : BitVec 64) ≠ 0#64 ∧ arrObj.cap ≤ arrObj.fields.length ∧
        arrMaxCap ≤ arrObj.cap := ⟨by decide, hpanic⟩
    rw [ite_eq_left_of_eq_true _ _ (eq_true hpanic)] at hPost
    rw [ite_eq_left_of_eq_true _ _ (eq_true hpan1)]
    exact hPost
  · have hnp1 : ¬ ((1 : BitVec 64) ≠ 0#64 ∧ arrObj.cap ≤ arrObj.fields.length ∧
        arrMaxCap ≤ arrObj.cap) := fun ⟨_, h1, h2⟩ => hpanic ⟨h1, h2⟩
    rw [ite_eq_right_of_eq_false _ _ (eq_false hpanic)] at hPost
    rw [ite_eq_right_of_eq_false _ _ (eq_false hnp1)]
    rcases hPost with ⟨hav, hk⟩
    have h1eq : (1 : BitVec 64) = 1#64 := rfl
    refine ⟨?_, ?_⟩
    · intro hneed
      rcases hneed with hne | ⟨_, hge⟩
      · exact hav (Or.inl hne)
      · exact hav (Or.inr hge)
    · intro r st' childObjs' m1 hr0 hr8 hpr1 hrem1 hfp1 hout hm1
      rw [h1eq] at hout
      rcases hout with ⟨_, hcanPre, hltCap, haddr1, hrc1Br, hrcNeBr⟩
      let newCap := arrEnsureCap arrObj.fields.length arrObj.cap 1#64
      let rPre := mkArrObj r 1#32 newCap arrObj.fields
      let oldKeep := if arrObj.rc = 1#32 then emp
        else lcnfObjMem (arrObj.withRc (decNonExclRc arrObj.rc))
      change LeanQbe.T.wp _ _ _ _ _
      r2_steps
      have hm1Pre : (lcnfObjMem rPre ⋆ (rtC0Inv rt st' ⋆ oldKeep ⋆ lcnfHeap childObjs' ⋆ R)) m1 :=
        by dsimp only [rPre, oldKeep]; exact sep_cast hm1 (by ac_rfl)
      apply wp_load_of (arr_load_sz_mid hcanPre hm1Pre)
      simp only [mkArrObj]
      r2_steps
      have hm1S := lcnfObjMem_array_elim hcanPre hm1Pre
      dsimp only [rPre, mkArrObj] at hm1S
      have hlenCap : arrObj.fields.length < newCap := hltCap (by decide)
      have hcapMax : newCap ≤ arrMaxCap := hcanPre.2.2.2.2.2.2.2
      have hfit8 : 8 * (newCap - arrObj.fields.length) ≤ 2 ^ 64 := by
        unfold arrMaxCap at hcapMax; omega
      have hge8 : 8 ≤ 8 * (newCap - arrObj.fields.length) := by omega
      have hmReg : (region (r + BitVec.ofNat 64 (24 + 8 * arrObj.fields.length))
            (8 * (newCap - arrObj.fields.length)) ⋆
          (cell64 r (mkArrObj r 1#32 newCap arrObj.fields).header ⋆
            cell64 (r + 8#64) (BitVec.ofNat 64 arrObj.fields.length) ⋆
            cell64 (r + 16#64) (BitVec.ofNat 64 newCap) ⋆
            array64 (r + 24#64) arrObj.fields ⋆
            rtC0Inv rt st' ⋆ oldKeep ⋆ lcnfHeap childObjs' ⋆ R)) m1 := sep_cast hm1S (by ac_rfl)
      obtain ⟨wSlot, hmSlot⟩ := region_split_cell64 hge8 hfit8 hmReg
      have hmSlot' : (cell64 (r + BitVec.ofNat 64 (24 + 8 * arrObj.fields.length)) wSlot ⋆
          (region (r + BitVec.ofNat 64 (24 + 8 * arrObj.fields.length) + 8#64)
              (8 * (newCap - arrObj.fields.length) - 8) ⋆
            cell64 r (mkArrObj r 1#32 newCap arrObj.fields).header ⋆
            cell64 (r + 8#64) (BitVec.ofNat 64 arrObj.fields.length) ⋆
            cell64 (r + 16#64) (BitVec.ofNat 64 newCap) ⋆
            array64 (r + 24#64) arrObj.fields ⋆
            rtC0Inv rt st' ⋆ oldKeep ⋆ lcnfHeap childObjs' ⋆ R)) m1 := sep_cast hmSlot (by ac_rfl)
      obtain ⟨hstOk, hm2⟩ := store_cell64 v hmSlot'
      have hlen64 := hcanPre.len_lt_64
      have hlenLt64 : arrObj.fields.length < 2 ^ 64 := by
        simp only [mkArrObj] at hlen64; exact hlen64
      have hslotAddr : r + 24 + 8 * BitVec.ofNat 64 arrObj.fields.length =
          r + BitVec.ofNat 64 (24 + 8 * arrObj.fields.length) := by
        change r + 24#64 + 8#64 * BitVec.ofNat 64 arrObj.fields.length = _
        rw [bv64_8mul_eq_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlenLt64, ptr_add_24_mul8]
      apply wp_store_sep
      · dsimp only [Arg.val]; rw [hslotAddr]; exact ⟨hstOk, hm2⟩
      · intro m2 hm2'
        r2_steps
        have hmAdd8 : (cell64 (r + 8#64) (BitVec.ofNat 64 arrObj.fields.length) ⋆
            (cell64 (r + BitVec.ofNat 64 (24 + 8 * arrObj.fields.length)) v ⋆
              region (r + BitVec.ofNat 64 (24 + 8 * arrObj.fields.length) + 8#64)
                (8 * (newCap - arrObj.fields.length) - 8) ⋆
              cell64 r (mkArrObj r 1#32 newCap arrObj.fields).header ⋆
              cell64 (r + 16#64) (BitVec.ofNat 64 newCap) ⋆
              array64 (r + 24#64) arrObj.fields ⋆
              rtC0Inv rt st' ⋆ oldKeep ⋆ lcnfHeap childObjs' ⋆ R)) m2 :=
          sep_cast hm2' (by ac_rfl)
        obtain ⟨hstOk8, hm3⟩ :=
          r2_c0_store_cell64_add8 (BitVec.ofNat 64 arrObj.fields.length + 1#64) hmAdd8
        apply wp_store_sep ⟨hstOk8, hm3⟩
        intro m3 hm3'
        r2_steps
        let newFields := arrObj.fields ++ [v]
        let rObj := mkArrObj r 1#32 newCap newFields
        have hlenNew : newFields.length = arrObj.fields.length + 1 := by simp [newFields]
        have hcanNew : ArrCanon rObj :=
          mkArrObj_canon hr0 hr8 (by decide) (by rw [hlenNew]; exact hlenCap) hcapMax
        have hm3Obj : (rtC0Inv rt st' ⋆ lcnfObjMem rObj ⋆ oldKeep ⋆
            lcnfHeap childObjs' ⋆ R) m3 := by
          have hbvAdd : BitVec.ofNat 64 arrObj.fields.length + 1#64 =
              BitVec.ofNat 64 newFields.length := by
            rw [hlenNew]; apply BitVec.eq_of_toNat_eq
            simp [BitVec.toNat_add, BitVec.toNat_ofNat]
          have hregAddr : r + BitVec.ofNat 64 (24 + 8 * newFields.length) =
              r + BitVec.ofNat 64 (24 + 8 * arrObj.fields.length) + 8#64 := by
            rw [hlenNew]; apply BitVec.eq_of_toNat_eq
            simp [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
          have hregSz : 8 * (newCap - newFields.length) =
              8 * (newCap - arrObj.fields.length) - 8 := by rw [hlenNew]; omega
          have hparts : (cell64 r rObj.header ⋆
              cell64 (r + 8#64) (BitVec.ofNat 64 newFields.length) ⋆
              cell64 (r + 16#64) (BitVec.ofNat 64 newCap) ⋆
              array64 (r + 24#64) newFields ⋆
              region (r + BitVec.ofNat 64 (24 + 8 * newFields.length))
                (8 * (newCap - newFields.length)) ⋆
              (rtC0Inv rt st' ⋆ oldKeep ⋆ lcnfHeap childObjs' ⋆ R)) m3 := by
            dsimp only [newFields]
            rw [array64_append]
            have hs1 : array64 (r + 24#64 + BitVec.ofNat 64 (8 * arrObj.fields.length)) [v] =
                cell64 (r + BitVec.ofNat 64 (24 + 8 * arrObj.fields.length)) v := by
              rw [ptr_add_24_mul8]; simp [array64, sep_emp]
            rw [hs1, hregAddr, hregSz, ← hbvAdd]
            have hhdr : rObj.header = (mkArrObj r 1#32 newCap arrObj.fields).header := rfl
            rw [hhdr]
            exact sep_cast hm3' (by ac_rfl)
          exact sep_cast (mkArrObj_mem_of_parts hparts) (by ac_rfl)
        exact hk r st' childObjs' m3 hr0 hr8 hpr1 hrem1
          (fun h1 hlt => ⟨haddr1 h1 (Or.inr hlt), hfp1 h1 (Or.inr hlt)⟩)
          hcanNew (fun h1 => (hrc1Br h1).1) (fun hne => (hrcNeBr hne).1) hm3Obj

private theorem arr_dropLast_append_last (xs : List (BitVec 64)) (h : 0 < xs.length) :
    xs.dropLast ++ [xs[xs.length - 1]] = xs := by
  induction xs with
  | nil => simp at h
  | cons x xs ih =>
    cases xs with
    | nil => simp
    | cons y ys =>
      have hlen : 0 < (y :: ys).length := by simp
      simpa [List.dropLast_cons_cons] using ih hlen

theorem lcnf_array_pop_wp :
    ∀ xs m Q X, lcnfArrayPopSpec xs m Q X → Func.wp rtR2Env lcnf_array_pop_body xs m Q X := by
  intro ⟨rt, arr, ⟨⟩⟩ m Q X
    ⟨st, objs, k, hkLen, R, haddr, hcanon, hnotSelf, hwfObjs, hclosed, hm,
      hrcNe1Ok, hrc1Ok, hk⟩
  let arrObj := objs[k]
  change arrObj.addr = arr at haddr
  have hlen64 := hcanon.len_lt_64
  have hlenMod : arrObj.fields.length % 2 ^ 64 = arrObj.fields.length := Nat.mod_eq_of_lt hlen64
  have hmSplit : (rtC0Inv rt st ⋆ lcnfObjMem arrObj ⋆ lcnfHeap (objs.eraseIdx k) ⋆ R) m := by
    have hf := lcnfHeap_focus objs hkLen
    rw [← lcnfHeap_eraseIdx objs] at hf
    rw [hf] at hm
    exact sep_cast hm (by ac_rfl)
  dsimp only [Func.wp, lcnf_array_pop_body]
  change LeanQbe.T.wp _ _ _ _ _
  r2_call rtR2Env_r2_ensure_excl_array
  dsimp only [r2EnsureExclArraySpec, vals, Tup.map, Arg.val]
  have hwfEr : ∀ y ∈ objs.eraseIdx k, y.Wf := fun y hy => hwfObjs y (mem_of_mem_eraseIdx_arr hy)
  refine ⟨st, arrObj, objs.eraseIdx k, R, haddr, hcanon, hwfEr, hmSplit, ?_, ?_⟩
  · intro hne
    exact ⟨arr_cow_closed_bound hkLen rfl hcanon hnotSelf hclosed, (hrcNe1Ok hne).2⟩
  · have hnp0 : ¬ ((0 : BitVec 64) ≠ 0#64 ∧ arrObj.cap ≤ arrObj.fields.length ∧
        arrMaxCap ≤ arrObj.cap) := by simp
    have hcapEq : arrEnsureCap arrObj.fields.length arrObj.cap (0 : BitVec 64) = arrObj.cap := by
      simp [arrEnsureCap]
    rw [ite_eq_right_of_eq_false _ _ (eq_false hnp0), hcapEq]
    refine ⟨fun hneed => ?_, fun r st1 mid0 m1 hr0 hr8 hpr1 hrem1 _hfp1 hout hm1 => ?_⟩
    · rcases hneed with hne | ⟨h0, _⟩
      · exact (hrcNe1Ok hne).1
      · exact absurd rfl h0
    · rcases hout with ⟨_, hcanPre, _, haddr1, hrc1Br, hrcNeBr⟩
      change LeanQbe.T.wp _ _ _ _ _
      r2_steps
      let rPre := mkArrObj r 1#32 arrObj.cap arrObj.fields
      let oldKeep := if arrObj.rc = 1#32 then emp
        else lcnfObjMem (arrObj.withRc (decNonExclRc arrObj.rc))
      have hm1Pre : (lcnfObjMem rPre ⋆ (rtC0Inv rt st1 ⋆ oldKeep ⋆
          lcnfHeap mid0 ⋆ R)) m1 := by
        dsimp only [rPre, oldKeep]; exact sep_cast hm1 (by ac_rfl)
      apply wp_load_of (arr_load_sz_mid hcanPre hm1Pre)
      simp only [mkArrObj]
      let mid1 := if arrObj.rc = 1#32 then objs.eraseIdx k
        else (incChildrenObjs arrObj.fields (objs.eraseIdx k)).insertIdx k
          (arrObj.withRc (decNonExclRc arrObj.rc))
      have hmMid1 : (oldKeep ⋆ lcnfHeap mid0) = lcnfHeap mid1 := by
        by_cases hrc1 : arrObj.rc = 1#32
        · have h1 := hrc1Br hrc1
          dsimp only [oldKeep, mid1]
          simp only [hrc1, ↓reduceIte, emp_sep, h1.1]
        · have h2 := hrcNeBr hrc1
          dsimp only [oldKeep, mid1]
          simp only [hrc1, ↓reduceIte, h2.1]
          have hlenInc : k ≤ (incChildrenObjs arrObj.fields (objs.eraseIdx k)).length := by
            simp [incChildrenObjs, List.length_eraseIdx, hkLen]; omega
          rw [lcnfHeap_insertIdx hlenInc]
      by_cases hpos : 0 < arrObj.fields.length
      · have hne0 : BitVec.ofNat 64 arrObj.fields.length ≠ 0#64 := by
          intro h0
          have h1 := congrArg BitVec.toNat h0
          rw [BitVec.toNat_ofNat, hlenMod] at h1
          have h0n : (0#64 : BitVec 64).toNat = 0 := rfl
          omega
        r2_steps
        let len := arrObj.fields.length
        let old := arrObj.fields[len - 1]
        have hsplit : arrObj.fields = arrObj.fields.dropLast ++ [old] :=
          (arr_dropLast_append_last arrObj.fields hpos).symm
        have hdlLen : arrObj.fields.dropLast.length = len - 1 := by simp [len]
        have hm1S := lcnfObjMem_array_elim hcanPre hm1Pre
        have hhdrEq : (mkArrObj r 1#32 arrObj.cap arrObj.fields).header = arrHeaderWord :=
          mkArrObj_header r arrObj.cap arrObj.fields
        rw [hhdrEq] at hm1S
        simp only [mkArrObj] at hm1S
        rw [hsplit, array64_append, hdlLen] at hm1S
        have hs1 : array64 (r + 24#64 + BitVec.ofNat 64 (8 * (len - 1))) [old] =
            cell64 (r + 24#64 + BitVec.ofNat 64 (8 * (len - 1))) old := by
          simp [array64, sep_emp]
        rw [hs1] at hm1S
        have hlenSplit : (arrObj.fields.dropLast ++ [old]).length = len := by rw [← hsplit]
        rw [hlenSplit] at hm1S
        have hmCell8 : (cell64 (r + 8#64) (BitVec.ofNat 64 len) ⋆
            (cell64 r arrHeaderWord ⋆
              cell64 (r + 16#64) (BitVec.ofNat 64 arrObj.cap) ⋆
              array64 (r + 24#64) arrObj.fields.dropLast ⋆
              cell64 (r + 24#64 + BitVec.ofNat 64 (8 * (len - 1))) old ⋆
              region (r + BitVec.ofNat 64 (24 + 8 * len)) (8 * (arrObj.cap - len)) ⋆
              rtC0Inv rt st1 ⋆ oldKeep ⋆ lcnfHeap mid0 ⋆ R)) m1 := sep_cast hm1S (by ac_rfl)
        have hbvSub : BitVec.ofNat 64 len - 1#64 = BitVec.ofNat 64 (len - 1) := by
          apply BitVec.eq_of_toNat_eq
          have hlenTo : (BitVec.ofNat 64 arrObj.fields.length).toNat = arrObj.fields.length := by
            rw [BitVec.toNat_ofNat, hlenMod]
          have hsub1 : (BitVec.ofNat 64 (arrObj.fields.length - 1)).toNat =
              arrObj.fields.length - 1 := by
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
          dsimp only [len]
          rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hlenTo]; exact hpos),
            hlenTo, hsub1]
          rfl
        obtain ⟨hstOk, hm2⟩ := r2_c0_store_cell64_add8 (BitVec.ofNat 64 len - 1#64) hmCell8
        apply wp_store_sep ⟨hstOk, hm2⟩
        intro m2 hm2'
        rw [hbvSub] at hm2'
        r2_steps
        have hm2Old : (cell64 (r + 24#64 + BitVec.ofNat 64 (8 * (len - 1))) old ⋆
            (cell64 (r + 8#64) (BitVec.ofNat 64 (len - 1)) ⋆
              cell64 r arrHeaderWord ⋆
              cell64 (r + 16#64) (BitVec.ofNat 64 arrObj.cap) ⋆
              array64 (r + 24#64) arrObj.fields.dropLast ⋆
              region (r + BitVec.ofNat 64 (24 + 8 * len)) (8 * (arrObj.cap - len)) ⋆
              rtC0Inv rt st1 ⋆ oldKeep ⋆ lcnfHeap mid0 ⋆ R)) m2 := sep_cast hm2' (by ac_rfl)
        have hmul8 : 8#64 * BitVec.ofNat 64 (len - 1) = BitVec.ofNat 64 (8 * (len - 1)) := by
          rw [bv64_8mul_eq_ofNat, BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt (by dsimp only [len]; omega)]
        have hloadOld : loadVal m2 i64 (r + 24#64 + 8#64 * (BitVec.ofNat 64 len - 1#64)) =
            some old := by
          rw [hbvSub, hmul8]; exact r2_c0_load_cell64 hm2Old
        apply wp_load_of hloadOld
        let rObj := mkArrObj r 1#32 arrObj.cap arrObj.fields.dropLast
        have hcanA : arrObj.fields.length ≤ arrObj.cap ∧ arrObj.cap ≤ arrMaxCap :=
          hcanon.2.2.2.2.2.2
        have hcanNew : ArrCanon rObj :=
          mkArrObj_canon hr0 hr8 (by decide)
            (by rw [hdlLen]; dsimp only [len]; omega)
            hcanA.2
        let mid2 := rObj :: mid1
        have hm2Heap : (rtC0Inv rt st1 ⋆ lcnfHeap mid2 ⋆ R) m2 := by
          have hregAddr : r + BitVec.ofNat 64 (24 + 8 * len) =
              r + 24#64 + BitVec.ofNat 64 (8 * (len - 1)) + 8#64 := by
            apply BitVec.eq_of_toNat_eq
            simp [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
          have hregTail : r + BitVec.ofNat 64 (24 + 8 * arrObj.fields.dropLast.length) =
              r + 24#64 + BitVec.ofNat 64 (8 * (len - 1)) := by
            rw [hdlLen, ptr_add_24_mul8]
          have hmergeReg : (region (r + 24#64 + BitVec.ofNat 64 (8 * (len - 1)))
                (8 * (arrObj.cap - arrObj.fields.dropLast.length)) ⋆
              (cell64 (r + 8#64) (BitVec.ofNat 64 (len - 1)) ⋆
                cell64 r arrHeaderWord ⋆
                cell64 (r + 16#64) (BitVec.ofNat 64 arrObj.cap) ⋆
                array64 (r + 24#64) arrObj.fields.dropLast ⋆
                rtC0Inv rt st1 ⋆ oldKeep ⋆ lcnfHeap mid0 ⋆ R)) m2 := by
            have hszEq : 8 * (arrObj.cap - arrObj.fields.dropLast.length) =
                8 + 8 * (arrObj.cap - len) := by
              rw [hdlLen]; dsimp only [len]; omega
            have hfitM : 8 + 8 * (arrObj.cap - len) ≤ 2 ^ 64 := by
              have := hcanA.2; unfold arrMaxCap at this; omega
            rw [hszEq]
            apply cell64_merge_region hfitM
            rw [← hregAddr]
            exact sep_cast hm2Old (by ac_rfl)
          have hparts : (cell64 r rObj.header ⋆
              cell64 (r + 8#64) (BitVec.ofNat 64 arrObj.fields.dropLast.length) ⋆
              cell64 (r + 16#64) (BitVec.ofNat 64 arrObj.cap) ⋆
              array64 (r + 24#64) arrObj.fields.dropLast ⋆
              region (r + BitVec.ofNat 64 (24 + 8 * arrObj.fields.dropLast.length))
                (8 * (arrObj.cap - arrObj.fields.dropLast.length)) ⋆
              (rtC0Inv rt st1 ⋆ oldKeep ⋆ lcnfHeap mid0 ⋆ R)) m2 := by
            rw [hregTail, hdlLen]
            rw [hdlLen] at hmergeReg
            have hhdr : rObj.header = arrHeaderWord :=
              mkArrObj_header r arrObj.cap arrObj.fields
            rw [hhdr]
            exact sep_cast hmergeReg (by ac_rfl)
          have hmRObj := mkArrObj_mem_of_parts hparts
          dsimp only [mid2]
          rw [lcnfHeap, ← hmMid1]
          exact sep_cast hmRObj (by ac_rfl)
        r2_call rtR2Env_r2_dec_obj
        dsimp only [r2DecObjSpec, vals, Tup.map, Arg.val]
        by_cases hskip : old = 0#64 ∨ (old &&& 1#64) ≠ 0#64
        · rw [ite_eq_left_of_eq_true _ _ (eq_true hskip)]
          r2_steps
          refine hk r st1 mid2 m2 hr0 hr8 hpr1 hrem1
            (fun h1 => haddr ▸ haddr1 h1 (Or.inl rfl))
            rObj mid1 mid2 rfl
            (fun h1 => by simp [mid1, h1, arrObj]) (fun hne => by simp [mid1, hne, arrObj])
            rfl ?_ hm2Heap
          rw [dite_eq_left hpos]
          simp only [DecObjRel]
          rw [ite_eq_left_of_eq_true _ _ (eq_true hskip)]
          exact True.intro
        · rw [ite_eq_right_of_eq_false _ _ (eq_false hskip)]
          have hold0 : old ≠ 0#64 := fun h => hskip (Or.inl h)
          have hold1 : (old &&& 1#64) = 0#64 := Classical.not_not.mp fun h => hskip (Or.inr h)
          have hrc1OkCast : arrObj.rc = 1#32 → old ≠ 0#64 → (old &&& 1#64) = 0#64 →
              ∀ o2 ∈ rObj :: objs.eraseIdx k, o2.addr = old → o2.rc = 1#32 →
                (rObj :: objs.eraseIdx k).length ≤ st.workCap ∧
                  lcnfHeapClosed (rObj :: objs.eraseIdx k) ∧
                  RcSound old (rObj :: objs.eraseIdx k) := by
            intro h1 ho0 ho1
            have hrEq := haddr ▸ haddr1 h1 (Or.inl rfl)
            have hrObjEq : rObj = mkArrObj arr 1#32 arrObj.cap arrObj.fields.dropLast := by
              dsimp only [rObj]; rw [hrEq]
            rw [hrObjEq]
            exact hrc1Ok hpos h1 ho0 ho1
          have hltPos : arrObj.fields.length - 1 < arrObj.fields.length := by omega
          obtain ⟨hwfMid2, obj, hobjMem, hobjAddr, hobjRc1⟩ :=
            arr_r2_dec_in_bounds hkLen rfl hcanon hnotSelf hwfObjs hclosed hrc1OkCast
              (fun hne => (hrcNe1Ok hne).2) (List.getElem_mem hltPos) hcanNew hpr1
              (fun h1 => by simp [mid1, h1, arrObj]) (fun hne => by simp [mid1, hne, arrObj]) rfl
              hm2Heap hold0 hold1
          refine ⟨st1, mid2, R, ⟨obj, hobjMem, hobjAddr, hobjRc1⟩, hwfMid2, hm2Heap, ?_⟩
          intro st2 objs' m3 hpr2 hrem2 hdec hm3
          r2_steps
          refine hk r st2 objs' m3 hr0 hr8 (hpr1.trans hpr2) (by omega)
            (fun h1 => haddr ▸ haddr1 h1 (Or.inl rfl))
            rObj mid1 mid2 rfl
            (fun h1 => by simp [mid1, h1, arrObj]) (fun hne => by simp [mid1, hne, arrObj])
            rfl ?_ hm3
          rw [dite_eq_left hpos]; exact hdec
      · have hlen0 : arrObj.fields.length = 0 := Nat.eq_zero_of_not_pos hpos
        r2_steps
        let rObj := mkArrObj r 1#32 arrObj.cap arrObj.fields.dropLast
        have hdlEq : arrObj.fields.dropLast = arrObj.fields := by
          have he : arrObj.fields = [] := List.eq_nil_of_length_eq_zero hlen0
          simp [he]
        have hobjEq : rObj = rPre := by dsimp only [rObj, rPre]; rw [hdlEq]
        let mid2 := rObj :: mid1
        have hm1Heap : (rtC0Inv rt st1 ⋆ lcnfHeap mid2 ⋆ R) m1 := by
          dsimp only [mid2]; rw [hobjEq, lcnfHeap, ← hmMid1]; exact sep_cast hm1Pre (by ac_rfl)
        refine hk r st1 mid2 m1 hr0 hr8 hpr1 hrem1
          (fun h1 => haddr ▸ haddr1 h1 (Or.inl rfl))
          rObj mid1 mid2 rfl
          (fun h1 => by simp [mid1, h1, arrObj]) (fun hne => by simp [mid1, hne, arrObj])
          rfl ?_ hm1Heap
        rw [dite_eq_right hpos]

theorem lcnf_array_swap_wp :
    ∀ xs m Q X,
      lcnfArraySwapSpec xs m Q X → Func.wp rtR2Env lcnf_array_swap_body xs m Q X := by
  intro ⟨rt, arr, i, j, check_bounds, ⟨⟩⟩ m Q X
    ⟨st, arrObj, childObjs, R, haddr, hcanon, hwfChild, hm, hPost⟩
  subst haddr
  have hlen64 := hcanon.len_lt_64
  have hlenMod : arrObj.fields.length % 2 ^ 64 = arrObj.fields.length := Nat.mod_eq_of_lt hlen64
  dsimp only [Func.wp, lcnf_array_swap_body, lcnfArraySwapSpec] at hPost ⊢
  change LeanQbe.T.wp _ _ _ _ _
  have hmArr : (lcnfObjMem arrObj ⋆ (rtC0Inv rt st ⋆ lcnfHeap childObjs ⋆ R)) m :=
    sep_cast hm (by ac_rfl)
  r2_steps
  apply wp_load_of (arr_load_sz_mid hcanon hmArr)
  let ui := (i >>> 1).toNat
  let uj := (j >>> 1).toNat
  by_cases hi : (i &&& 1#64) ≠ 0#64 ∧ (j &&& 1#64) ≠ 0#64 ∧
      ui < arrObj.fields.length ∧ uj < arrObj.fields.length
  · rw [dite_eq_left hi] at hPost
    rcases hPost with ⟨hchildOk, hk⟩
    rcases hi with ⟨hi1, hj1, hui, huj⟩
    r2_steps <;> first
      | { r2_call rtR2Env_r2_ensure_excl_array
          dsimp only [r2EnsureExclArraySpec, vals, Tup.map, Arg.val]
          have hnp0 : ¬ ((0 : BitVec 64) ≠ 0#64 ∧ arrObj.cap ≤ arrObj.fields.length ∧
              arrMaxCap ≤ arrObj.cap) := by simp
          have hcapEq : arrEnsureCap arrObj.fields.length arrObj.cap (0 : BitVec 64) =
              arrObj.cap := by simp [arrEnsureCap]
          refine ⟨st, arrObj, childObjs, R, rfl, hcanon, hwfChild, hm,
            fun hne => (hchildOk hne).2, ?_⟩
          rw [ite_eq_right_of_eq_false _ _ (eq_false hnp0), hcapEq]
          refine ⟨fun hneed => ?_, fun r st' childObjs' m1 hr0 hr8 hpr1 hrem1 hfp1 hout hm1 => ?_⟩
          · rcases hneed with hne | ⟨h0, _⟩
            · exact (hchildOk hne).1
            · exact absurd rfl h0
          · rcases hout with ⟨_, hcanPre, _, haddr1, hrc1Br, hrcNeBr⟩
            let rPre := mkArrObj r 1#32 arrObj.cap arrObj.fields
            let oldKeep := if arrObj.rc = 1#32 then emp
              else lcnfObjMem (arrObj.withRc (decNonExclRc arrObj.rc))
            change LeanQbe.T.wp _ _ _ _ _
            r2_steps
            have hm1Pre : (lcnfObjMem rPre ⋆ (rtC0Inv rt st' ⋆ oldKeep ⋆
                lcnfHeap childObjs' ⋆ R)) m1 := by
              dsimp only [rPre, oldKeep]; exact sep_cast hm1 (by ac_rfl)
            have hloadI := arr_load_elem_mid hcanPre (by simp [mkArrObj]; exact hui) hm1Pre
            have hloadJ := arr_load_elem_mid hcanPre (by simp [mkArrObj]; exact huj) hm1Pre
            simp only [mkArrObj] at hloadI hloadJ
            apply wp_load_of hloadI
            r2_steps
            apply wp_load_of hloadJ
            r2_steps
            have hm1S := lcnfObjMem_array_elim hcanPre hm1Pre
            dsimp only [rPre, mkArrObj] at hm1S
            have hmArr1 : (array64 (r + 24#64) arrObj.fields ⋆
                (cell64 r rPre.header ⋆
                  cell64 (r + 8#64) (BitVec.ofNat 64 arrObj.fields.length) ⋆
                  cell64 (r + 16#64) (BitVec.ofNat 64 arrObj.cap) ⋆
                  region (r + BitVec.ofNat 64 (24 + 8 * arrObj.fields.length))
                    (8 * (arrObj.cap - arrObj.fields.length)) ⋆
                  rtC0Inv rt st' ⋆ oldKeep ⋆ lcnfHeap childObjs' ⋆ R)) m1 :=
              sep_cast hm1S (by ac_rfl)
            let vi := arrObj.fields[ui]
            let vj := arrObj.fields[uj]
            obtain ⟨hok1, hm2⟩ := r2_c0_store_array64_add24_mul8 vj hmArr1 hui
            apply wp_store_sep ⟨hok1, hm2⟩
            intro m2 hm2'
            r2_steps
            have hlen1 : (arrObj.fields.set ui vj).length = arrObj.fields.length := by simp
            obtain ⟨hok2, hm3⟩ :=
              r2_c0_store_array64_add24_mul8 vi hm2' (by rw [hlen1]; exact huj)
            apply wp_store_sep ⟨hok2, hm3⟩
            intro m3 hm3'
            r2_steps
            let swapped := (arrObj.fields.set ui vj).set uj vi
            let rObj := mkArrObj r 1#32 arrObj.cap swapped
            have hlenSwap : swapped.length = arrObj.fields.length := by simp [swapped]
            have hcanNew : ArrCanon rObj :=
              mkArrObj_canon hr0 hr8 (by decide)
                (by rw [hlenSwap]; exact hcanon.2.2.2.2.2.2.1) hcanon.2.2.2.2.2.2.2
            have hm3Obj : (rtC0Inv rt st' ⋆ lcnfObjMem rObj ⋆ oldKeep ⋆
                lcnfHeap childObjs' ⋆ R) m3 := by
              have hparts : (cell64 r rObj.header ⋆
                  cell64 (r + 8#64) (BitVec.ofNat 64 swapped.length) ⋆
                  cell64 (r + 16#64) (BitVec.ofNat 64 arrObj.cap) ⋆
                  array64 (r + 24#64) swapped ⋆
                  region (r + BitVec.ofNat 64 (24 + 8 * swapped.length))
                    (8 * (arrObj.cap - swapped.length)) ⋆
                  (rtC0Inv rt st' ⋆ oldKeep ⋆ lcnfHeap childObjs' ⋆ R)) m3 := by
                rw [hlenSwap]
                have hhdr : rObj.header = rPre.header := rfl
                rw [hhdr]
                exact sep_cast hm3' (by ac_rfl)
              exact sep_cast (mkArrObj_mem_of_parts hparts) (by ac_rfl)
            exact hk r st' childObjs' m3 hr0 hr8 hpr1 hrem1
              (fun h1 => ⟨haddr1 h1 (Or.inl rfl), hfp1 h1 (Or.inl rfl)⟩)
              hcanNew (fun h1 => (hrc1Br h1).1) (fun hne => (hrcNeBr hne).1) hm3Obj }
      | { exfalso; first
            | exact hi1 (by assumption)
            | exact hj1 (by assumption)
            | (have hn : ¬ ui < arrObj.fields.length % 2 ^ 64 := by assumption
               rw [hlenMod] at hn; exact hn hui)
            | (have hn : ¬ uj < arrObj.fields.length % 2 ^ 64 := by assumption
               rw [hlenMod] at hn; exact hn huj) }
  · rw [dite_eq_right hi] at hPost
    by_cases hcb : check_bounds ≠ 0#64
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hcb)] at hPost
      r2_steps <;> first
        | exact hPost
        | (exfalso; have h0 : check_bounds = 0#64 := by assumption; exact hcb h0)
        | (exfalso
           exact hi ⟨by assumption, by assumption,
             by have hle : ¬ arrObj.fields.length % 2 ^ 64 ≤ (i >>> 1).toNat := by assumption
                rw [hlenMod] at hle; dsimp only [ui]; omega,
             by have hle : ¬ arrObj.fields.length % 2 ^ 64 ≤ (j >>> 1).toNat := by assumption
                rw [hlenMod] at hle; dsimp only [uj]; omega⟩)
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hcb)] at hPost
      r2_steps <;> first
        | exact hPost
        | (exfalso; exact hcb (by assumption))
        | (exfalso
           exact hi ⟨by assumption, by assumption,
             by have hle : ¬ arrObj.fields.length % 2 ^ 64 ≤ (i >>> 1).toNat := by assumption
                rw [hlenMod] at hle; dsimp only [ui]; omega,
             by have hle : ¬ arrObj.fields.length % 2 ^ 64 ≤ (j >>> 1).toNat := by assumption
                rw [hlenMod] at hle; dsimp only [uj]; omega⟩)

end LeanQbe.T.LeanLCNF
