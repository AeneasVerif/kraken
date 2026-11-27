module

public import LeanQbe.T.LeanLCNF.Sem.PerceusCall
public import LeanQbe.T.LeanLCNF.Sem.PerceusPrims
import LeanQbe.T.Logic.ProofKit

namespace LeanQbe.T.LeanLCNF.Sem

open LeanQbe.T.LeanLCNF

/-! ## 1. `maxObjRc`, Metadata, and List Helpers -/

private theorem foldl_max_eq (a : Nat) (xs : List Nat) :
    List.foldl Nat.max a xs = Nat.max a (List.foldl Nat.max 0 xs) := by
  induction xs generalizing a with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, Nat.zero_max]
    rw [ih (a.max x), ih x]
    exact Nat.max_assoc a x _

private theorem maxObjRc_eq_foldl_map (objs : List LcnfObj) :
    maxObjRc objs = List.foldl Nat.max 0 (objs.map (fun o => o.rc.toNat)) := by
  simp only [maxObjRc, List.foldl_map]

private theorem maxObjRc_cons_eq (o : LcnfObj) (objs : List LcnfObj) :
    maxObjRc (o :: objs) = Nat.max o.rc.toNat (maxObjRc objs) := by
  rw [maxObjRc_eq_foldl_map, List.map_cons, List.foldl_cons]
  simp only [Nat.zero_max]
  rw [foldl_max_eq, maxObjRc_eq_foldl_map]

public theorem maxObjRc_eraseIdx_le (objs : List LcnfObj) (idx : Nat) :
    maxObjRc (objs.eraseIdx idx) ≤ maxObjRc objs := by
  induction objs generalizing idx with
  | nil => simp [maxObjRc]
  | cons o os ih =>
    cases idx with
    | zero =>
      simp only [List.eraseIdx_cons_zero, maxObjRc_cons_eq]
      exact Nat.le_max_right _ _
    | succ i =>
      simp only [List.eraseIdx_cons_succ, maxObjRc_cons_eq]
      exact Nat.max_le.mpr ⟨Nat.le_max_left _ _, Nat.le_trans (ih i) (Nat.le_max_right _ _)⟩

public theorem maxObjRc_set_le (objs : List LcnfObj) (idx : Nat) (o' : LcnfObj)
    (hrc : ∀ hidx : idx < objs.length, o'.rc.toNat ≤ objs[idx].rc.toNat) :
    maxObjRc (objs.set idx o') ≤ maxObjRc objs := by
  induction objs generalizing idx with
  | nil => simp [maxObjRc]
  | cons o os ih =>
    cases idx with
    | zero =>
      simp only [List.set_cons_zero, maxObjRc_cons_eq]
      exact Nat.max_le.mpr
        ⟨Nat.le_trans (hrc (Nat.zero_lt_succ _)) (Nat.le_max_left _ _), Nat.le_max_right _ _⟩
    | succ i =>
      simp only [List.set_cons_succ, maxObjRc_cons_eq]
      exact Nat.max_le.mpr
        ⟨Nat.le_max_left _ _,
         Nat.le_trans (ih i fun h => hrc (Nat.succ_lt_succ h)) (Nat.le_max_right _ _)⟩

public theorem maxObjRc_le_of_mem_le {objs objs' : List LcnfObj}
    (hle : ∀ o' ∈ objs', ∃ o ∈ objs, o'.rc.toNat ≤ o.rc.toNat) :
    maxObjRc objs' ≤ maxObjRc objs := by
  induction objs' with
  | nil => simp [maxObjRc]
  | cons y ys ih =>
    rw [maxObjRc_cons_eq]
    obtain ⟨o, ho, hor⟩ := hle y List.mem_cons_self
    exact Nat.max_le.mpr ⟨Nat.le_trans hor (le_maxObjRc_of_mem ho),
      ih (fun z hz => hle z (List.mem_cons_of_mem _ hz))⟩

public theorem maxObjRc_set_inc_lt {objs : List LcnfObj} {idx n rcr : Nat}
    (hidx : idx < objs.length) (hrcr : n ≤ rcr)
    (hbd : Nat.max 1 (maxObjRc objs) + rcr < 2 ^ 31 - 1) :
    Nat.max 1 (maxObjRc (objs.set idx
      (objs[idx].withRc (objs[idx].rc + BitVec.ofNat 32 n)))) +
      (rcr - n) < 2 ^ 31 - 1 := by
  have hold : objs[idx].rc.toNat ≤ Nat.max 1 (maxObjRc objs) :=
    Nat.le_trans (le_maxObjRc_of_mem (List.getElem_mem hidx)) (Nat.le_max_right _ _)
  have hsum_lt : objs[idx].rc.toNat + n < 2 ^ 32 := by omega
  have hrc'_nat : (objs[idx].rc + BitVec.ofNat 32 n).toNat = objs[idx].rc.toNat + n := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : n < 2 ^ 32),
      Nat.mod_eq_of_lt hsum_lt]
  have hmax : ∀ ys : List LcnfObj,
      (∀ o' ∈ ys, o'.rc.toNat ≤ Nat.max 1 (maxObjRc objs) + n) →
      maxObjRc ys ≤ Nat.max 1 (maxObjRc objs) + n := by
    intro ys hys
    induction ys with
    | nil => simp [maxObjRc]
    | cons y ys ih =>
      rw [maxObjRc_cons_eq]
      exact Nat.max_le.mpr ⟨hys y List.mem_cons_self,
        ih (fun z hz => hys z (List.mem_cons_of_mem _ hz))⟩
  have hbound : maxObjRc (objs.set idx
      (objs[idx].withRc (objs[idx].rc + BitVec.ofNat 32 n))) ≤
      Nat.max 1 (maxObjRc objs) + n := by
    refine hmax _ (fun o' ho' => ?_)
    obtain ⟨j, hj, hjeq⟩ := List.mem_iff_getElem.mp ho'
    rw [← hjeq]
    by_cases hij : j = idx
    · subst hij
      simp only [List.getElem_set_self, LcnfObj.withRc]
      rw [hrc'_nat]; omega
    · simp only [List.length_set] at hj
      rw [List.getElem_set_ne (Ne.symm hij)]
      exact Nat.le_trans (le_maxObjRc_of_mem (List.getElem_mem hj))
        (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_add_right _ _))
  have hone : 1 ≤ Nat.max 1 (maxObjRc objs) + n :=
    Nat.le_trans (Nat.le_max_left _ _) (Nat.le_add_right _ _)
  have hmax1 : Nat.max 1 (maxObjRc (objs.set idx
      (objs[idx].withRc (objs[idx].rc + BitVec.ofNat 32 n)))) ≤
      Nat.max 1 (maxObjRc objs) + n :=
    Nat.max_le.mpr ⟨hone, hbound⟩
  exact Nat.lt_of_le_of_lt (Nat.add_le_add_right hmax1 (rcr - n)) (by omega)

public theorem rc_lt_bound_of_toNat {rc : BitVec 32} (h : rc.toNat < 2 ^ 31 - 1) :
    0 ≤ rc.toInt ∧ rc.toInt = ↑rc.toNat := by
  rw [BitVec.toInt_eq_toNat_cond]
  have hlt : 2 * rc.toNat < 2 ^ 32 := by omega
  simp [hlt]

public theorem rc_sub_nat_eq {rc : BitVec 32} (hbd : rc.toNat < 2 ^ 31 - 1) (hgt : 1 < rc.toInt) :
    (rc - 1#32).toNat = rc.toNat - 1 ∧ 0 < (rc - 1#32).toInt ∧
      (rc - 1#32).toNat < 2 ^ 31 - 1 := by
  have ⟨_, hti⟩ := rc_lt_bound_of_toNat hbd
  rw [hti] at hgt
  have h1 : 1 < rc.toNat := by omega
  have hsub : (rc - 1#32).toNat = rc.toNat - 1 := by
    rw [BitVec.toNat_sub]
    simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    have hsub1 : 2 ^ 32 - 1 + rc.toNat = 2 ^ 32 + (rc.toNat - 1) := by omega
    rw [hsub1, Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_mod]
    exact Nat.mod_eq_of_lt (by omega)
  have hlt : (rc - 1#32).toNat < 2 ^ 31 - 1 := by omega
  have ⟨_, hti2⟩ := rc_lt_bound_of_toNat hlt
  have hpos : 0 < (rc - 1#32).toInt := by rw [hti2]; omega
  exact ⟨hsub, hpos, hlt⟩

public theorem rc_add_nat_eq {rc : BitVec 32} {n : Nat} (hbd : rc.toNat + n < 2 ^ 31 - 1) :
    (rc + BitVec.ofNat 32 n).toNat = rc.toNat + n ∧
      (rc + BitVec.ofNat 32 n).toNat < 2 ^ 31 - 1 := by
  have hn : n % 2 ^ 32 = n := Nat.mod_eq_of_lt (by omega)
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, hn, Nat.mod_eq_of_lt (by omega)]
  exact ⟨rfl, hbd⟩

public theorem list_map_addr_set_eq {objs : List LcnfObj} {idx : Nat} (hidx : idx < objs.length)
    {o' : LcnfObj} (haddr : o'.addr = objs[idx].addr) :
    (objs.set idx o').map LcnfObj.addr = objs.map LcnfObj.addr := by
  rw [List.map_set, haddr]
  have hlen : idx < (objs.map LcnfObj.addr).length := by simpa using hidx
  have hget : objs[idx].addr = (objs.map LcnfObj.addr)[idx] := (List.getElem_map _).symm
  rw [hget, List.set_getElem_self]

public theorem list_nodup_eraseIdx {α : Type} {xs : List α} (hnodup : xs.Nodup) (idx : Nat) :
    (xs.eraseIdx idx).Nodup :=
  hnodup.sublist (List.eraseIdx_sublist xs idx)

public theorem list_mem_set_iff {α : Type} {xs : List α} {idx : Nat} (hidx : idx < xs.length)
    {x y : α} : y ∈ xs.set idx x ↔ y = x ∨ ∃ j, ∃ hj : j < xs.length, j ≠ idx ∧ xs[j] = y := by
  induction xs generalizing idx with
  | nil => simp at hidx
  | cons a as ih =>
    cases idx with
    | zero =>
      simp only [List.set_cons_zero, List.mem_cons]
      constructor
      · rintro (rfl | hy)
        · exact Or.inl rfl
        · obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hy
          exact Or.inr ⟨j + 1, Nat.succ_lt_succ hj, by omega, rfl⟩
      · rintro (rfl | ⟨j, hj, hne, rfl⟩)
        · exact Or.inl rfl
        · cases j with
          | zero => exact absurd rfl hne
          | succ k => exact Or.inr (List.getElem_mem _)
    | succ i =>
      simp only [List.set_cons_succ, List.mem_cons]
      have hi : i < as.length := Nat.lt_of_succ_lt_succ hidx
      rw [ih hi]
      constructor
      · rintro (rfl | rfl | ⟨j, hj, hne, rfl⟩)
        · exact Or.inr ⟨0, Nat.zero_lt_succ _, by omega, rfl⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨j + 1, Nat.succ_lt_succ hj, by omega, rfl⟩
      · rintro (rfl | ⟨j, hj, hne, rfl⟩)
        · exact Or.inr (Or.inl rfl)
        · cases j with
          | zero => exact Or.inl rfl
          | succ k => exact Or.inr (Or.inr ⟨k, Nat.lt_of_succ_lt_succ hj, by omega, rfl⟩)

public theorem obj_mem_idx {objs : List LcnfObj} {o : LcnfObj} (ho : o ∈ objs) :
    ∃ idx, ∃ hidx : idx < objs.length, objs[idx] = o :=
  let ⟨idx, hidx, heq⟩ := List.mem_iff_getElem.mp ho
  ⟨idx, hidx, heq⟩

private theorem list_count_set_add {α : Type} [DecidableEq α] (xs : List α) (i : Nat)
    (hi : i < xs.length) (x a : α) :
    List.count a (xs.set i x) + (if a = xs[i] then 1 else 0) =
      List.count a xs + (if a = x then 1 else 0) := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons y ys ih =>
    cases i with
    | zero =>
      simp only [List.set_cons_zero, List.getElem_cons_zero, List.count_cons, beq_iff_eq]
      rw [show (if x = a then (1 : Nat) else 0) = if a = x then 1 else 0 by simp [eq_comm]]
      rw [show (if y = a then (1 : Nat) else 0) = if a = y then 1 else 0 by simp [eq_comm]]
      omega
    | succ k =>
      simp only [List.set_cons_succ, List.getElem_cons_succ, List.count_cons, beq_iff_eq]
      have hk := ih k (Nat.lt_of_succ_lt_succ hi)
      by_cases h1 : y = a <;> simp only [h1, ↓reduceIte, Nat.add_zero]
      · rw [Nat.add_right_comm _ 1, hk, Nat.add_right_comm]
      · exact hk

public theorem nonPersistRefs_set_obj_fields {objs : List LcnfObj} {idx i : Nat}
    (hidx : idx < objs.length) (o' : LcnfObj) (hrc : objs[idx].rc ≠ 0#32) (hrc' : o'.rc ≠ 0#32)
    (oldF newF : BitVec 64) (hch : o'.childFields = objs[idx].childFields.set i newF)
    (hi : i < objs[idx].childFields.length) (hold : objs[idx].childFields[i] = oldF)
    (a : BitVec 64) :
    nonPersistRefs (objs.set idx o') a + (if a = oldF then 1 else 0) =
      nonPersistRefs objs a + (if a = newF then 1 else 0) := by
  have h1 := LeanQbe.T.LeanLCNF.nonPersistRefs_focus (objs.set idx o') (idx := idx)
    (by simp [hidx]) a
  have h2 := LeanQbe.T.LeanLCNF.nonPersistRefs_focus objs (idx := idx) hidx a
  simp only [List.getElem_set_self, List.eraseIdx_set_eq, hrc', ↓reduceIte, hrc] at h1 h2
  rw [hch] at h1
  have hcnt := list_count_set_add objs[idx].childFields i hi newF a
  rw [hold] at hcnt
  omega

/-! ## 2. `ParentChildBacked` and `EntryPres` -/

/-- Every live non-scalar `borrowed` var with `parent? = some p` points either into
`extH ++ ghostH` (via `Backed`) or directly to a child field of `p`. -/
@[expose] public def ParentChildBacked (rf : RcFrame) (objs : List LcnfObj) : Prop :=
  ∀ u ∈ rf.ctx.vars, u.isLive = true → u.noRc = false → u.persistent = false →
    u.borrowed = true → ∀ p, u.parent? = some p → ∀ bv, rf.envH u.id = some (u.ty, .i64 bv) →
      bv &&& 1#64 = 0#64 →
        Backed objs (rf.extH ++ rf.ghostH) bv ∨
          ∃ wp o_p, rf.envH p = some wp ∧ wp.2.toBV64? = some o_p.addr ∧
            o_p ∈ objs ∧ ∃ o_mid ∈ objs,
              NonPersistReach objs o_p.addr o_mid.addr ∧ bv ∈ o_mid.childFields

/-- Preservation relative to function entry frame `(rf0, σ0)`. -/
@[expose] public def EntryPres (rf0 : RcFrame) (σ0 : HState) (rf : RcFrame) (σ : HState) : Prop :=
  HeapStepRel (rf0.extH ++ rf0.ghostH) σ0 σ ∧
  (∀ a, a ∈ rf0.extH ++ rf0.ghostH → IsolatedAddr a rf0 σ0.objs →
    IsolatedAddr a rf σ.objs ∧
    ∀ o ∈ σ0.objs, o.addr = a → ∃ o' ∈ σ.objs, ObjDataEq o o' ∧ o'.rc = 1#32) ∧
  rf.extH = rf0.extH ∧ (∀ a, a ∈ rf0.ghostH → a ∈ rf.ghostH) ∧
  ∀ a, rf0.ghostH.count a ≤ rf.ghostH.count a

public theorem entryPres_refl (rf0 : RcFrame) (σ0 : HState)
    (hclean : ∀ o ∈ σ0.objs, o.Wf) (hnodup : (σ0.objs.map LcnfObj.addr).Nodup) :
    EntryPres rf0 σ0 rf0 σ0 :=
  ⟨heapStepRel_refl (rf0.extH ++ rf0.ghostH) σ0, fun _ _ hiso =>
    ⟨hiso, fun o ho hoa =>
      let ⟨_, ho1, _, hoa1, hrc⟩ := hiso.2.2
      ⟨o, ho, objDataEq_refl o (hclean o ho),
        (obj_eq_of_addr_nodup hnodup ho ho1 (hoa.trans hoa1.symm)) ▸ hrc⟩⟩,
   rfl, fun _ h => h, fun _ => Nat.le_refl _⟩

public theorem entryPres_set_shadowP {rf0 rf : RcFrame} {σ0 σ : HState}
    {envP' : PValEnv} (hep : EntryPres rf0 σ0 rf σ) :
    EntryPres rf0 σ0 { rf with envP := envP' } σ :=
  ⟨hep.1, fun a ha hiso => hep.2.1 a ha hiso, hep.2.2⟩

private theorem nonScalarWords_cons_of_nonSc {p : LcParam} {ps : List LcParam}
    {w : Word} {ws : List Word} (hns : p.ty.isScalar = false) :
    nonScalarWords (p :: ps) (w :: ws) = w :: nonScalarWords ps ws := by
  simp [nonScalarWords, hns]

private theorem nonScalarWords_cons_of_sc {p : LcParam} {ps : List LcParam}
    {w : Word} {ws : List Word} (hs : p.ty.isScalar = true) :
    nonScalarWords (p :: ps) (w :: ws) = nonScalarWords ps ws := by
  simp [nonScalarWords, hs]

private theorem bindParams_mem_info (ps : List LcParam) (ctx : RcCtx)
    (hnd : (ctx.vars.map RcVar.id).Nodup) :
    (∀ v ∈ (ctx.bindParams ps).vars,
      (v ∈ ctx.vars ∧ ∀ p ∈ ps, p.id ≠ v.id) ∨
        ∃ p ∈ ps, v.id = p.id ∧ v.ty = p.ty ∧ v.parent? = none) ∧
    ((ctx.bindParams ps).vars.map RcVar.id).Nodup := by
  induction ps generalizing ctx with
  | nil => exact ⟨fun v hv => Or.inl ⟨hv, fun _ h => nomatch h⟩, hnd⟩
  | cons p ps ih =>
    simp only [RcCtx.bindParams, List.foldl_cons]
    have hstep_nd :
        ((if p.borrow = true then ctx.bindBorrowed p.id p.ty else ctx.bindOwned p.id p.ty).vars.map
          RcVar.id).Nodup := by
      cases p.borrow <;> simp [RcCtx.bindBorrowed, RcCtx.bindOwned] <;> exact RcCtx.put_nodup hnd _
    obtain ⟨ih1, ih2⟩ := ih _ hstep_nd
    refine ⟨fun v hv => ?_, ih2⟩
    rcases ih1 v hv with ⟨hmem, hne⟩ | ⟨q, hqm, hqid, hqty, hqp⟩
    · cases hb : p.borrow with
      | true =>
        simp only [hb, ↓reduceIte, RcCtx.bindBorrowed] at hmem
        rcases (RcCtx.put_mem_iff hnd).mp hmem with rfl | ⟨hm, hne_p⟩
        · exact Or.inr ⟨p, List.mem_cons_self, rfl, rfl, by simp⟩
        · exact Or.inl ⟨hm, fun q hqm => by
            rcases List.mem_cons.mp hqm with rfl | hqs
            · exact hne_p.symm
            · exact hne q hqs⟩
      | false =>
        simp only [hb, Bool.false_eq_true, ↓reduceIte, RcCtx.bindOwned] at hmem
        rcases (RcCtx.put_mem_iff hnd).mp hmem with rfl | ⟨hm, hne_p⟩
        · exact Or.inr ⟨p, List.mem_cons_self, rfl, rfl, rfl⟩
        · exact Or.inl ⟨hm, fun q hqm => by
            rcases List.mem_cons.mp hqm with rfl | hqs
            · exact hne_p.symm
            · exact hne q hqs⟩
    · exact Or.inr ⟨q, List.mem_cons_of_mem _ hqm, hqid, hqty, hqp⟩

private theorem bindAll_eq_of_not_mem (ps : List LcParam) (as : List Word)
    (ρ : HValEnv) {x : Nat} (hne : ∀ q ∈ ps, q.id ≠ x) :
    (ρ.bindAll ps as) x = ρ x := by
  induction ps generalizing as ρ with
  | nil => simp [HValEnv.bindAll]
  | cons p ps ih =>
    cases as with
    | nil => simp [HValEnv.bindAll]
    | cons w ws =>
      simp only [HValEnv.bindAll]
      rw [ih ws _ (fun q hq => hne q (List.mem_cons_of_mem _ hq))]
      simp [HValEnv.set, Ne.symm (hne p List.mem_cons_self)]

private theorem bindAll_nonScalar_mem (ps : List LcParam) (as : List Word)
    (ρ : HValEnv) (hnd : (ps.map (·.id)).Nodup) (hpm : paramsMatch ps as)
    {x : Nat} {ty : LcTy} {w : Word}
    (hp : ∃ p ∈ ps, p.id = x ∧ p.ty = ty ∧ ty.isScalar = false)
    (heq : (ρ.bindAll ps as) x = some (ty, w)) :
    w ∈ nonScalarWords ps as := by
  induction ps generalizing as ρ with
  | nil => obtain ⟨p, hm, _⟩ := hp; nomatch hm
  | cons p ps ih =>
    cases as with
    | nil => simp [paramsMatch] at hpm
    | cons w0 ws =>
      simp only [paramsMatch] at hpm
      simp only [HValEnv.bindAll] at heq
      rw [List.map_cons, List.nodup_cons] at hnd
      have hnd_cons := hnd
      by_cases hmem_tail : ∃ q ∈ ps, q.id = x ∧ q.ty = ty ∧ ty.isScalar = false
      · have hw := ih ws (ρ.set p.id p.ty w0) hnd_cons.2 hpm.2 hmem_tail heq
        cases hsc : p.ty.isScalar
        · rw [nonScalarWords_cons_of_nonSc hsc]; exact List.mem_cons_of_mem _ hw
        · rw [nonScalarWords_cons_of_sc hsc]; exact hw
      · obtain ⟨q, hqm, hqid, hqty, hns⟩ := hp
        rcases List.mem_cons.mp hqm with rfl | hqt
        · have hnot : ∀ r ∈ ps, r.id ≠ q.id := fun r hr heqr =>
            hnd_cons.1 (List.mem_map.mpr ⟨r, hr, heqr⟩)
          rw [← hqid, bindAll_eq_of_not_mem ps ws _ hnot] at heq
          simp only [HValEnv.set, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at heq
          subst hqty; rw [heq.2, nonScalarWords_cons_of_nonSc hns]
          exact List.mem_cons_self
        · exact absurd ⟨q, hqt, hqid, hqty, hns⟩ hmem_tail

public theorem parentChildBacked_init (d : LcDecl) (pvs : List PVal) (as : List Word)
    (extH ghostH : List (BitVec 64)) {σObjs : List LcnfObj} :
    ParentChildBacked (entryRcFrame d pvs as extH ghostH) σObjs := by
  intro u hu _ _ _ _ p hp
  have hmem := (bindParams_mem_info d.params { vars := [], sharedPreds := [] }
    (by simp)).1 u hu
  rcases hmem with ⟨hm, _⟩ | ⟨_, _, _, _, hnone⟩
  · simp at hm
  · rw [hnone] at hp; cases hp

public theorem entryPres_to_callPreserve {d : LcDecl} {pvs : List PVal} {as : List Word}
    {extH ghostH : List (BitVec 64)} {σ0 σ : HState} {rf : RcFrame}
    (hnd : (d.params.map (·.id)).Nodup) (hpm : paramsMatch d.params as)
    (hep : EntryPres (entryRcFrame d pvs as extH ghostH) σ0 rf σ) :
    CallPreserve (nonScalarWords d.params as) (extH ++ ghostH) σ0 σ := by
  refine ⟨hep.1, fun o ho howf hext hrc1 hnp0 hdisj => ?_⟩
  have hiso : IsolatedAddr o.addr (entryRcFrame d pvs as extH ghostH) σ0.objs := by
    refine ⟨fun v hv _ hns w hevh => ?_, hnp0, o, ho, howf, rfl, hrc1⟩
    rcases (bindParams_mem_info d.params { vars := [], sharedPreds := [] }
        (by simp)).1 v hv with ⟨hm, _⟩ | ⟨p, hpm_p, hid, hty, _⟩
    · simp at hm
    · intro hbw
      have hwmem := bindAll_nonScalar_mem d.params as HValEnv.empty hnd hpm
        ⟨p, hpm_p, hid.symm, hty.symm, Bool.eq_false_iff.mpr (by simpa using hns)⟩
        (by simpa [entryRcFrame, hid] using hevh)
      exact hdisj w hwmem hbw
  exact (hep.2.1 o.addr hext hiso).2 o ho rfl

public theorem entryPres_of_live_back {rf0 rf rf' : RcFrame} {σ0 σ : HState}
    (hep : EntryPres rf0 σ0 rf σ)
    (hext : rf'.extH = rf.extH) (hgh : ∀ a, a ∈ rf.ghostH → a ∈ rf'.ghostH)
    (hgh_cnt : ∀ a, rf.ghostH.count a ≤ rf'.ghostH.count a)
    (hlive : ∀ v ∈ rf'.ctx.vars, v.isLive = true → !v.ty.isScalar = true →
      ∃ v0 ∈ rf.ctx.vars, v0.isLive = true ∧ !v0.ty.isScalar = true ∧
        v0.id = v.id ∧ v0.ty = v.ty)
    (henv : ∀ z, rf'.envH z = rf.envH z) :
    EntryPres rf0 σ0 rf' σ := by
  refine ⟨hep.1, fun a ha hiso => ?_, hext.trans hep.2.2.1,
    fun b hb => hgh b (hep.2.2.2.1 b hb),
    fun b => Nat.le_trans (hep.2.2.2.2 b) (hgh_cnt b)⟩
  obtain ⟨⟨hlive0, hnp, o, ho, hwf, hoa, hrc⟩, hop⟩ := hep.2.1 a ha hiso
  refine ⟨⟨fun v hv hvl hvns w hev => ?_, hnp, o, ho, hwf, hoa, hrc⟩, hop⟩
  obtain ⟨v0, hv0m, hv0l, hv0ns, hid, hty⟩ := hlive v hv hvl hvns
  rw [henv, ← hid, ← hty] at hev
  exact hlive0 v0 hv0m hv0l hv0ns w hev

public theorem rcCtx_get?_of_mem {ctx : RcCtx} (hnd : (ctx.vars.map RcVar.id).Nodup)
    {v : RcVar} (hv : v ∈ ctx.vars) : ctx.get? v.id = some v :=
  (RcCtx.mem_get?_iff hnd).mpr hv

public theorem entryPres_consumeVar {rf0 rf : RcFrame} {σ0 σ : HState}
    (hnd : (rf.ctx.vars.map RcVar.id).Nodup) (hclean : CleanVars rf.ctx)
    {x n : Nat} {ctx' : RcCtx} (hc : rf.ctx.consumeVar x n = .ok ctx')
    (hep : EntryPres rf0 σ0 rf σ) :
    EntryPres rf0 σ0 { rf with ctx := ctx' } σ := by
  have hnd' := consumeVar_nodup hnd hc
  refine entryPres_of_live_back hep rfl (fun _ h => h) (fun _ => Nat.le_refl _)
    (fun v hv hvl hvns => ?_) (fun _ => rfl)
  obtain ⟨v0, hv0g, hv0l, _, _, hv0ty, _⟩ :=
    consumeVar_get?_live_back hnd hclean hc v.id (rcCtx_get?_of_mem hnd' hv) hvl
  have hv0m := RcCtx.get?_mem hv0g
  exact ⟨v0, hv0m.1, hv0l, hv0ty ▸ hvns, hv0m.2, hv0ty⟩

public theorem entryPres_applyArgs {rf0 rf : RcFrame} {σ0 σ : HState}
    (hnd : (rf.ctx.vars.map RcVar.id).Nodup) (hclean : CleanVars rf.ctx)
    {as : List LcArg} {bs : List Bool} {ctx' : RcCtx}
    (ha : rf.ctx.applyArgs as bs = .ok ctx')
    (hep : EntryPres rf0 σ0 rf σ) :
    EntryPres rf0 σ0 { rf with ctx := ctx' } σ := by
  have hnd' := applyArgs_nodup hnd ha
  refine entryPres_of_live_back hep rfl (fun _ h => h) (fun _ => Nat.le_refl _)
    (fun v hv hvl hvns => ?_) (fun _ => rfl)
  obtain ⟨v0, hv0g, hv0l, _, _, hv0ty, _⟩ :=
    applyArgs_get?_live_back hnd hclean ha v.id (rcCtx_get?_of_mem hnd' hv) hvl
  have hv0m := RcCtx.get?_mem hv0g
  exact ⟨v0, hv0m.1, hv0l, hv0ty ▸ hvns, hv0m.2, hv0ty⟩

public theorem entryPres_put_same_var {rf0 rf : RcFrame} {σ0 σ : HState}
    (hnd : (rf.ctx.vars.map RcVar.id).Nodup) {v v' : RcVar}
    (hv : v ∈ rf.ctx.vars) (hid : v'.id = v.id) (hty : v'.ty = v.ty)
    (hl : v'.isLive = true → v.isLive = true)
    (hep : EntryPres rf0 σ0 rf σ) :
    EntryPres rf0 σ0 { rf with ctx := rf.ctx.put v' } σ := by
  refine entryPres_of_live_back hep rfl (fun _ h => h) (fun _ => Nat.le_refl _)
    (fun u hu hul huns => ?_) (fun _ => rfl)
  rcases (RcCtx.put_mem_iff hnd).mp hu with rfl | ⟨hm, _⟩
  · exact ⟨v, hv, hl hul, hty ▸ huns, hid.symm, hty.symm⟩
  · exact ⟨u, hm, hul, huns, rfl, rfl⟩

public theorem entryPres_bindNonPtr {rf0 rf : RcFrame} {σ0 σ : HState}
    (hnd : (rf.ctx.vars.map RcVar.id).Nodup) (hwf_all : ∀ o ∈ σ.objs, o.Wf)
    {x : Nat} (_hfr : binderFreshOwned rf.ctx x = true)
    {v : RcVar} (hvid : v.id = x) {pv : PVal} {w : Word}
    (hodd : ¬v.ty.isScalar = true → ∃ bv, w = .i64 bv ∧ bv &&& 1#64 ≠ 0#64)
    (hep : EntryPres rf0 σ0 rf σ) :
    EntryPres rf0 σ0
      { rf with
        ctx := rf.ctx.put v
        envP := rf.envP.set x pv
        envH := rf.envH.set x v.ty w } σ := by
  refine ⟨hep.1, fun a ha hiso => ?_, hep.2.2⟩
  obtain ⟨⟨hlive0, hnp, o, ho, hwf, hoa, hrc⟩, hop⟩ := hep.2.1 a ha hiso
  refine ⟨⟨fun u hu hul huns wu hewu => ?_, hnp, o, ho, hwf, hoa, hrc⟩, hop⟩
  rcases (RcCtx.put_mem_iff hnd).mp hu with rfl | ⟨hm, hne⟩
  · simp only [HValEnv.set, hvid, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hewu
    obtain ⟨bv, rfl, hbv_odd⟩ := hodd (by simpa using huns)
    rw [← hewu.2]
    intro heqa
    simp only [Word.toBV64?, Word.i64, Option.some.injEq] at heqa
    have h0 := obj_addr_and1_zero (hwf_all o ho)
    rw [hoa, ← heqa] at h0
    exact hbv_odd h0
  · simp only [HValEnv.set, show u.id ≠ x by simpa [hvid] using hne, ite_false] at hewu
    exact hlive0 u hm hul huns wu hewu

public theorem entryPres_bindBorrowed {rf0 rf : RcFrame} {σ0 σ : HState}
    (hnd : (rf.ctx.vars.map RcVar.id).Nodup)
    (hhs : HandlesRcSound (frameHandles rf) σ.objs)
    (_hwf_all : ∀ o ∈ σ.objs, o.Wf) (hnodup_o : (σ.objs.map LcnfObj.addr).Nodup)
    {x src : Nat} (_hfr : binderFreshOwned rf.ctx x = true)
    {v : RcVar} (hvid : v.id = x) {pv : PVal} {bv : BitVec 64}
    {v_src : RcVar} (_hgsrc : rf.ctx.get? src = some v_src) (_hns_src : ¬v_src.ty.isScalar = true)
    {bv_src : BitVec 64} (_hesrc : rf.envH src = some (v_src.ty, .i64 bv_src))
    {o_src : LcnfObj} (ho_src : o_src ∈ σ.objs) (_ha_src : o_src.addr = bv_src)
    (hch : bv &&& 1#64 = 0#64 → bv ∈ o_src.childFields)
    (hep : EntryPres rf0 σ0 rf σ) :
    EntryPres rf0 σ0
      { rf with
        ctx := rf.ctx.put v
        envP := rf.envP.set x pv
        envH := rf.envH.set x v.ty (.i64 bv) } σ := by
  refine ⟨hep.1, fun a ha hiso => ?_, hep.2.2⟩
  obtain ⟨⟨hlive0, hnp, o, ho, hwf, hoa, hrc⟩, hop⟩ := hep.2.1 a ha hiso
  refine ⟨⟨fun u hu hul huns wu hewu => ?_, hnp, o, ho, hwf, hoa, hrc⟩, hop⟩
  rcases (RcCtx.put_mem_iff hnd).mp hu with rfl | ⟨hm, hne⟩
  · simp only [HValEnv.set, hvid, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hewu
    rw [← hewu.2]
    intro heqa
    simp only [Word.toBV64?, Word.i64, Option.some.injEq] at heqa
    have hev := obj_addr_and1_zero hwf
    rw [hoa, ← heqa] at hev
    have hmem_ch := hch hev
    by_cases hrc0 : o_src.rc = 0#32
    · obtain ⟨q, hqm, hqa, hqrc⟩ := hhs.1 o_src ho_src hrc0 bv hmem_ch hev
      have hqeq := obj_eq_of_addr_nodup hnodup_o hqm ho (hqa.trans (heqa.trans hoa.symm))
      rw [hqeq, hrc] at hqrc; cases hqrc
    · exact RtProof.nonPersistRefs_eq_zero_imp σ.objs a hnp o_src ho_src hrc0 (heqa ▸ hmem_ch)
  · simp only [HValEnv.set, show u.id ≠ x by simpa [hvid] using hne, ite_false] at hewu
    exact hlive0 u hm hul huns wu hewu

public theorem entryPres_freshAlloc {rf0 rf : RcFrame} {σ0 σ : HState}
    (hnd : (rf.ctx.vars.map RcVar.id).Nodup) (_hwf_all : ∀ o ∈ σ.objs, o.Wf)
    (hclean_st : ∀ o ∈ σ.objs, o.Wf)
    {newObj : LcnfObj} (_hnwf : newObj.Wf) (hnrc : newObj.rc = 1#32)
    (hfresh : ∀ o ∈ σ.objs, o.addr ≠ newObj.addr)
    (hch_nl : ∀ a, a ∈ rf0.extH ++ rf0.ghostH → IsolatedAddr a rf0 σ0.objs →
      ¬ a ∈ newObj.childFields)
    {st' : RtC0State} (hmeta : st'.PreservesMeta σ.st)
    {x : Nat} {v : RcVar} (hvid : v.id = x) {pv : PVal}
    {ghostH' : List (BitVec 64)} (hgh_sub : ∀ a, a ∈ rf.ghostH → a ∈ ghostH')
    (hgh_cnt : ∀ a, rf.ghostH.count a ≤ ghostH'.count a)
    (hep : EntryPres rf0 σ0 rf σ) :
    let σ' : HState :=
      { st := st', objs := newObj :: σ.objs, scr := σ.scr, scrLimbs := σ.scrLimbs }
    let rf' : RcFrame :=
      { ctx := rf.ctx.put v
        envP := rf.envP.set x pv
        envH := rf.envH.set x v.ty (.i64 newObj.addr)
        extH := rf.extH
        ghostH := ghostH' }
    EntryPres rf0 σ0 rf' σ' := by
  intro σ' rf'
  have hpres : HeapStepRel (rf0.extH ++ rf0.ghostH) σ σ' := by
    refine ⟨hmeta, rfl, rfl, ?_, ?_⟩
    · intro o ho howf _
      exact ⟨o, List.mem_cons_of_mem _ ho, objDataEq_refl o howf, fun h => h, fun h => h⟩
    · intro a hb
      exact backed_mono_heap
        (fun o ho howf _ => ⟨o, List.mem_cons_of_mem _ ho, rfl, rfl, rfl⟩)
        (fun _ _ _ _ _ _ _ => trivial) hclean_st (fun r hr => ⟨hr, trivial⟩) trivial hb
  refine ⟨heapStepRel_trans hep.1 hpres, fun a ha hiso => ?_,
    hep.2.2.1, fun b hb => hgh_sub b (hep.2.2.2.1 b hb),
    fun b => Nat.le_trans (hep.2.2.2.2 b) (hgh_cnt b)⟩
  obtain ⟨⟨hlive0, hnp, o, ho, hwf, hoa, hrc⟩, hop⟩ := hep.2.1 a ha hiso
  have hne_new : newObj.addr ≠ a := fun h => hfresh o ho (hoa.trans h.symm)
  have hnp' : nonPersistRefs (newObj :: σ.objs) a = 0 := by
    rw [nonPersistRefs_cons, hnp]
    have hnotin := hch_nl a ha hiso
    have hcnt0 : List.count a newObj.childFields = 0 := List.count_eq_zero.mpr hnotin
    simp [hnrc, hcnt0]
  refine ⟨⟨fun u hu hul huns wu hewu => ?_, hnp', o, List.mem_cons_of_mem _ ho, hwf, hoa, hrc⟩,
    fun o0 ho0 hoa0 => ?_⟩
  · rcases (RcCtx.put_mem_iff hnd).mp hu with rfl | ⟨hm, hne⟩
    · dsimp only [rf'] at hewu
      simp only [HValEnv.set, hvid, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hewu
      rw [← hewu.2]
      intro hbw; simp only [Word.toBV64?, Word.i64, Option.some.injEq] at hbw
      exact hne_new hbw
    · dsimp only [rf'] at hewu
      simp only [HValEnv.set, show u.id ≠ x by simpa [hvid] using hne, ite_false] at hewu
      exact hlive0 u hm hul huns wu hewu
  · obtain ⟨o1, ho1, hdeq1, hrc1⟩ := hop o0 ho0 hoa0
    exact ⟨o1, List.mem_cons_of_mem _ ho1, hdeq1, hrc1⟩

public theorem entryPres_afterCall {rf0 rf : RcFrame} {σ0 σ σ' : HState}
    (hnd : (rf.ctx.vars.map RcVar.id).Nodup) (hclean : CleanVars rf.ctx)
    (hwf_all : ∀ o ∈ σ.objs, o.Wf) (_hwf_all' : ∀ o ∈ σ'.objs, o.Wf)
    {x : Nat} {ty rty : LcTy} {as : List LcArg} {borrows : List Bool} {ctx' : RcCtx}
    (ha : rf.ctx.applyArgs as borrows = .ok ctx')
    (_hfr : binderFreshOwned rf.ctx x = true)
    (hty_sc : ty.isScalar = rty.isScalar)
    {pv : PVal} {rw : Word}
    (hret_odd : ¬rty.isScalar → ¬rty.needsRc → ∃ bv, rw = Word.i64 bv ∧ bv &&& 1#64 ≠ 0#64)
    (hhs_ret : HandlesRcSound
      (retHandles rty rw ++ (localHandles ctx' rf.envH ++ rf.extH) ++ rf.ghostH) σ'.objs)
    (hstep_sub : HeapStepRel (localHandles ctx' rf.envH ++ rf.extH ++ rf.ghostH) σ σ')
    (hisol : IsolPreserve rf σ σ')
    (hep : EntryPres rf0 σ0 rf σ) :
    let rf_post : RcFrame :=
      { ctx := ctx'.bindOwned x ty, envP := rf.envP.set x pv,
        envH := rf.envH.set x ty rw, extH := rf.extH, ghostH := rf.ghostH }
    EntryPres rf0 σ0 rf_post σ' := by
  intro rf_post
  have hsub_ext : ∀ a, a ∈ rf0.extH ++ rf0.ghostH →
      a ∈ localHandles ctx' rf.envH ++ rf.extH ++ rf.ghostH := by
    intro a ha0
    rcases List.mem_append.mp ha0 with h1 | h2
    · exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr (hep.2.2.1 ▸ h1))))
    · exact List.mem_append.mpr (Or.inr (hep.2.2.2.1 a h2))
  have hstep0 : HeapStepRel (rf0.extH ++ rf0.ghostH) σ σ' :=
    heapStepRel_mono_ext hwf_all hsub_ext hstep_sub
  refine ⟨heapStepRel_trans hep.1 hstep0, fun a ha0 hiso0 => ?_, hep.2.2.1, hep.2.2.2⟩
  obtain ⟨hiso_mid, hop_mid⟩ := hep.2.1 a ha0 hiso0
  have ha_rf : a ∈ rf.extH ++ rf.ghostH := by
    rcases List.mem_append.mp ha0 with h1 | h2
    · exact List.mem_append.mpr (Or.inl (hep.2.2.1 ▸ h1))
    · exact List.mem_append.mpr (Or.inr (hep.2.2.2.1 a h2))
  obtain ⟨o', ho', hwf', hoa', hrc', hnp', hdeq_fn⟩ := hisol a ha_rf hiso_mid
  have hnd' := applyArgs_nodup hnd ha
  have hctx_bind : ctx'.bindOwned x ty = ctx'.put
      { id := x, ty := ty, noRc := !ty.needsRc, persistent := false,
        owned := if !ty.needsRc then 0 else 1, borrowed := false,
        parent? := none, excl := false, resetTok := false } := by
    cases hnr : ty.needsRc <;> simp [RcCtx.bindOwned, hnr]
  refine ⟨⟨fun u hu hul huns wu hewu => ?_, hnp', o', ho', hwf', hoa', hrc'⟩,
    fun o0 ho0 hoa0 => ?_⟩
  · dsimp only [rf_post] at hu hewu
    rw [hctx_bind] at hu
    rcases (RcCtx.put_mem_iff hnd').mp hu with rfl | ⟨hm, hne⟩
    · simp only [HValEnv.set, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hewu
      rw [← hewu.2]
      intro heqa
      by_cases hrty_rc : rty.needsRc = true
      · have hnrty_sc : ¬rty.isScalar = true := fun h => by
          rw [← hty_sc] at h; simp [h] at huns
        have hr_mem : a ∈ retHandles rty rw := by
          simp only [retHandles, hrty_rc, Bool.true_and, hnrty_sc, Bool.not_false, ↓reduceIte]
          cases hbv : rw.toBV64? with
          | none => rw [hbv] at heqa; cases heqa
          | some bv =>
            rw [hbv] at heqa; cases heqa
            have hev := obj_addr_and1_zero hwf'
            rw [hoa'] at hev
            simp [hev]
        have hs := hhs_ret.2 o' ho' (by rw [hrc']; decide)
        have hc1 : 1 ≤ List.count a (retHandles rty rw) := List.count_pos_iff.mpr hr_mem
        have hc2 : 1 ≤ List.count a ((localHandles ctx' rf.envH ++ rf.extH) ++ rf.ghostH) := by
          refine List.count_pos_iff.mpr ?_
          rcases List.mem_append.mp ha_rf with h1 | h2
          · exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr h1)))
          · exact List.mem_append.mpr (Or.inr h2)
        have htot : 2 ≤ List.count o'.addr
            (retHandles rty rw ++ (localHandles ctx' rf.envH ++ rf.extH) ++ rf.ghostH) := by
          rw [hoa', List.append_assoc, List.count_append]
          omega
        rw [hrc'] at hs; simp only [BitVec.toNat_ofNat] at hs; omega
      · have hnrty_rc : ¬rty.needsRc = true := hrty_rc
        have hnrty_sc : ¬rty.isScalar = true := fun h => by
          rw [← hty_sc] at h; simp [h] at huns
        obtain ⟨bv, hrweq, hbv_odd⟩ := hret_odd hnrty_sc hnrty_rc
        rw [hrweq] at heqa
        simp only [Word.toBV64?, Word.i64, Option.some.injEq] at heqa
        have hev := obj_addr_and1_zero hwf'
        rw [hoa', ← heqa] at hev
        exact hbv_odd hev
    · simp only [HValEnv.set, hne, ite_false] at hewu
      obtain ⟨v0, hv0g, hv0l, _, _, hv0ty, _⟩ :=
        applyArgs_get?_live_back hnd hclean ha u.id (rcCtx_get?_of_mem hnd' hm) hul
      have hv0m := RcCtx.get?_mem hv0g
      exact hiso_mid.1 v0 hv0m.1 hv0l (hv0ty ▸ huns) wu (hv0m.2 ▸ hv0ty ▸ hewu)
  · obtain ⟨o1, ho1, hdeq1, _⟩ := hop_mid o0 ho0 hoa0
    exact ⟨o', ho', objDataEq_trans hdeq1 (hdeq_fn o1 ho1 (hdeq1.1.trans hoa0)), hrc'⟩

public theorem parentChildBacked_consumeVar {rf : RcFrame} {σ : HState}
    (hnd : (rf.ctx.vars.map RcVar.id).Nodup) (hclean : CleanVars rf.ctx)
    {x n : Nat} {ctx' : RcCtx} (hc : rf.ctx.consumeVar x n = .ok ctx')
    (hpc : ParentChildBacked rf σ.objs) :
    ParentChildBacked { rf with ctx := ctx' } σ.objs := by
  intro u hu hul huno hups hub p hup bv hev hbv0
  have hnd' := consumeVar_nodup hnd hc
  obtain ⟨u0, hg0, hul0, huno0, hups0, hty0, _, hb_back⟩ :=
    consumeVar_get?_live_back hnd hclean hc u.id (rcCtx_get?_of_mem hnd' hu) hul
  obtain ⟨hub0, hup0⟩ := hb_back.1 hub
  exact hpc u0 (RcCtx.get?_mem hg0).1 hul0 (huno0 ▸ huno) (hups0 ▸ hups) hub0 p
    (hup0.trans hup) bv (by simpa [(RcCtx.get?_mem hg0).2, hty0] using hev) hbv0

public theorem parentChildBacked_applyArgs {rf : RcFrame} {σ : HState}
    (hnd : (rf.ctx.vars.map RcVar.id).Nodup) (hclean : CleanVars rf.ctx)
    {as : List LcArg} {bs : List Bool} {ctx' : RcCtx}
    (ha : rf.ctx.applyArgs as bs = .ok ctx')
    (hpc : ParentChildBacked rf σ.objs) :
    ParentChildBacked { rf with ctx := ctx' } σ.objs := by
  intro u hu hul huno hups hub p hup bv hev hbv0
  have hnd' := applyArgs_nodup hnd ha
  obtain ⟨u0, hg0, hul0, huno0, hups0, hty0, _, hb_back⟩ :=
    applyArgs_get?_live_back hnd hclean ha u.id (rcCtx_get?_of_mem hnd' hu) hul
  obtain ⟨hub0, hup0⟩ := hb_back.1 hub
  exact hpc u0 (RcCtx.get?_mem hg0).1 hul0 (huno0 ▸ huno) (hups0 ▸ hups) hub0 p
    (hup0.trans hup) bv (by simpa [(RcCtx.get?_mem hg0).2, hty0] using hev) hbv0

private theorem nonPersistReach_target_nz' {objs : List LcnfObj} {r a : BitVec 64}
    (h : NonPersistReach objs r a) : ∃ t ∈ objs, t.addr = a ∧ t.rc ≠ 0#32 := by
  cases h with
  | refl h1 => exact h1
  | step _ _ _ h1 => exact h1

private theorem nonPersistReach_backed_lift {objs objs' : List LcnfObj}
    {roots : List (BitVec 64)} {r a : BitVec 64}
    (hrop : r ∈ roots)
    (hwf : ∀ o ∈ objs, o.Wf)
    (hpres : ∀ o ∈ objs, o.Wf → Backed objs roots o.addr →
      ∃ o' ∈ objs', ObjDataEq o o' ∧ (o.rc ≠ 0#32 → o'.rc ≠ 0#32))
    (hreach : NonPersistReach objs r a) :
    NonPersistReach objs' r a := by
  induction hreach with
  | refl h1 =>
    obtain ⟨t, ht, hta, htnz⟩ := h1
    have ht_bk : Backed objs roots t.addr :=
      Or.inr ⟨r, hrop, hta ▸ NonPersistReach.refl ⟨t, ht, rfl, htnz⟩⟩
    obtain ⟨t', ht'm, hdeq_t, hrc_t⟩ := hpres t ht (hwf t ht) ht_bk
    exact NonPersistReach.refl ⟨t', ht'm, hdeq_t.1.trans hta, hrc_t htnz⟩
  | @step u_r v_r hprev hchild hev_r hcnz ih =>
    obtain ⟨o_u, hou_m, hou_a, hou_cf⟩ := hchild
    have hu_bk : Backed objs roots o_u.addr :=
      Or.inr ⟨r, hrop, hou_a ▸ hprev⟩
    obtain ⟨o_u', hou'm, hdeq_u, _⟩ := hpres o_u hou_m (hwf o_u hou_m) hu_bk
    obtain ⟨o_v, hov_m, hov_a, hov_nz⟩ := hcnz
    have hv_bk : Backed objs roots o_v.addr :=
      Or.inr ⟨r, hrop, NonPersistReach.step hprev ⟨o_u, hou_m, hou_a, hov_a ▸ hou_cf⟩
        (hov_a ▸ hev_r) ⟨o_v, hov_m, rfl, hov_nz⟩⟩
    obtain ⟨o_v', hov'm, hdeq_v, hrc_v⟩ := hpres o_v hov_m (hwf o_v hov_m) hv_bk
    exact NonPersistReach.step ih ⟨o_u', hou'm, hdeq_u.1.trans hou_a,
      objDataEq_childFields hdeq_u ▸ hou_cf⟩ hev_r
      ⟨o_v', hov'm, hdeq_v.1.trans hov_a, hrc_v hov_nz⟩

public theorem parentChildBacked_bindFreshOwned {rf : RcFrame} {σ σ' : HState}
    (hnd : (rf.ctx.vars.map RcVar.id).Nodup)
    (hclean : CleanVars rf.ctx)
    (hwf_all : ∀ o ∈ σ.objs, o.Wf)
    (hvar : ∀ v ∈ rf.ctx.vars, VarInv v rf σ.objs)
    (hpo : ParentsOwned rf.ctx)
    (hpc : ParentChildBacked rf σ.objs)
    {x : Nat} (hfr : binderFreshOwned rf.ctx x = true)
    {v : RcVar} (hvid : v.id = x) (hnb : v.borrowed = false)
    {pv : PVal} {w : Word} {ghostH' : List (BitVec 64)} {roots : List (BitVec 64)}
    (hroots_par : ∀ pv0 ∈ rf.ctx.vars, pv0.noRc = false →
      pv0.persistent = false → 0 < pv0.owned → ∀ bp, rf.envH pv0.id = some (pv0.ty, .i64 bp) →
        bp &&& 1#64 = 0#64 → bp ∈ roots)
    (hpres : ∀ o ∈ σ.objs, o.Wf → Backed σ.objs roots o.addr →
      ∃ o' ∈ σ'.objs, ObjDataEq o o' ∧ (o.rc ≠ 0#32 → o'.rc ≠ 0#32))
    (hbk_step : ∀ a, Backed σ.objs (rf.extH ++ rf.ghostH) a →
      Backed σ'.objs (rf.extH ++ ghostH') a) :
    ParentChildBacked
      { ctx := rf.ctx.put v, envP := rf.envP.set x pv, envH := rf.envH.set x v.ty w,
        extH := rf.extH, ghostH := ghostH' } σ'.objs := by
  intro u hu hul huno hups hub p hup bv hev hbv0
  rcases (RcCtx.put_mem_iff hnd).mp hu with rfl | ⟨hm, hne⟩
  · rw [hub] at hnb; cases hnb
  · have hne_ux : u.id ≠ x := by simpa [hvid] using hne
    have hne_px : p ≠ x := by
      intro heq; subst heq
      have hf := hfr
      simp only [binderFreshOwned, Bool.and_eq_true, List.all_eq_true, bne_iff_ne] at hf
      exact hf.1.1 u hm (by simp [hup])
    simp only [HValEnv.set, hne_ux, ite_false] at hev
    rcases hpc u hm hul huno hups hub p hup bv hev hbv0 with hbk | ⟨wp, op, hep, hwp, hopm, hch⟩
    · exact Or.inl (hbk_step bv hbk)
    · obtain ⟨pv0, hpvm, hpvid, hp1, hp2, hp3, _⟩ := hpo u hm p hup
      have hpvl : pv0.isLive = true := by simp [RcVar.isLive, hp3]
      obtain ⟨_, w0, _, hw0, _, hnon0⟩ := hvar pv0 hpvm hpvl
      have hp_ns : ¬pv0.ty.isScalar := fun hs => by
        have := (hclean pv0 hpvm).1.2 hs
        rw [this] at hp1; cases hp1
      obtain ⟨bp, hweq0, _⟩ := hnon0 hp_ns
      rw [hpvid, hep] at hw0; cases hw0
      rw [hweq0] at hwp hep
      simp only [Word.toBV64?, Word.i64, Option.some.injEq] at hwp
      have howf := hwf_all op hopm
      have hevb := obj_addr_and1_zero howf
      rw [← hwp] at hevb
      have hrop : op.addr ∈ roots :=
        hwp ▸ hroots_par pv0 hpvm hp1 hp2 hp3 bp (hpvid ▸ hep) hevb
      have hbk_op : Backed σ.objs roots op.addr := by
        by_cases hrc0 : op.rc = 0#32
        · exact Or.inl ⟨op, hopm, rfl, hrc0⟩
        · exact Or.inr ⟨op.addr, hrop, NonPersistReach.refl ⟨op, hopm, rfl, hrc0⟩⟩
      obtain ⟨op', hop'm, hdeq, _⟩ := hpres op hopm howf hbk_op
      obtain ⟨o_mid, hom_m, hreach_mid, hcf_mid⟩ := hch
      have hmid_bk : Backed σ.objs roots o_mid.addr := Or.inr ⟨op.addr, hrop, hreach_mid⟩
      obtain ⟨o_mid', hom'm, hdeq_m, _⟩ := hpres o_mid hom_m (hwf_all o_mid hom_m) hmid_bk
      have hreach' : NonPersistReach σ'.objs op'.addr o_mid'.addr := by
        rw [hdeq.1, hdeq_m.1]
        exact nonPersistReach_backed_lift hrop hwf_all hpres hreach_mid
      refine Or.inr ⟨(pv0.ty, .i64 bp), op', ?_, ?_, hop'm, o_mid', hom'm, hreach', ?_⟩
      · simp only [HValEnv.set, hne_px, ite_false]; exact hep
      · simp [Word.toBV64?, Word.i64, hdeq.1, hwp]
      · rw [objDataEq_childFields hdeq_m]; exact hcf_mid

public theorem parentChildBacked_bindBorrowed {rf : RcFrame} {σ : HState}
    (hnd : (rf.ctx.vars.map RcVar.id).Nodup)
    (hpc : ParentChildBacked rf σ.objs)
    {x : Nat} (hfr : binderFreshOwned rf.ctx x = true)
    {v : RcVar} (hvid : v.id = x) (hpne : v.parent? ≠ some x)
    {pv : PVal} {bv : BitVec 64}
    (hv_ok : ∀ p, v.parent? = some p → bv &&& 1#64 = 0#64 →
      Backed σ.objs (rf.extH ++ rf.ghostH) bv ∨
        ∃ wp o_p, rf.envH p = some wp ∧ wp.2.toBV64? = some o_p.addr ∧
          o_p ∈ σ.objs ∧ ∃ o_mid ∈ σ.objs,
            NonPersistReach σ.objs o_p.addr o_mid.addr ∧ bv ∈ o_mid.childFields) :
    ParentChildBacked
      { rf with
        ctx := rf.ctx.put v
        envP := rf.envP.set x pv
        envH := rf.envH.set x v.ty (.i64 bv) } σ.objs := by
  intro u hu hul huno hups hub p hup bvu hev hbv0
  rcases (RcCtx.put_mem_iff hnd).mp hu with rfl | ⟨hm, hne⟩
  · simp only [HValEnv.set, hvid, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hev
    have hbveq : bvu = bv := by
      have := congrArg (·.toBV64?) hev.2
      simpa [Word.toBV64?, Word.i64] using this.symm
    subst hbveq
    rcases hv_ok p hup hbv0 with hbk | ⟨wp, op, hep, hwp, hopm, hch⟩
    · exact Or.inl hbk
    · have hpx : p ≠ x := fun heq => hpne (heq ▸ hup)
      exact Or.inr ⟨wp, op, by simp [HValEnv.set, hpx, hep], hwp, hopm, hch⟩
  · have hne_ux : u.id ≠ x := by simpa [hvid] using hne
    have hne_px : p ≠ x := by
      intro heq; subst heq
      have hf := hfr
      simp only [binderFreshOwned, Bool.and_eq_true, List.all_eq_true, bne_iff_ne] at hf
      exact hf.1.1 u hm (by simp [hup])
    simp only [HValEnv.set, hne_ux, ite_false] at hev
    rcases hpc u hm hul huno hups hub p hup bvu hev hbv0 with hbk | ⟨wp, op, hep, hwp, hopm, hch⟩
    · exact Or.inl hbk
    · exact Or.inr ⟨wp, op, by simp [HValEnv.set, hne_px, hep], hwp, hopm, hch⟩

public theorem parentChildBacked_markScalarBranch {rf : RcFrame} {σ : HState}
    (hnd : (rf.ctx.vars.map RcVar.id).Nodup) (_hclean : CleanVars rf.ctx)
    (x : Nat) (hpc : ParentChildBacked rf σ.objs) :
    ParentChildBacked { rf with ctx := rf.ctx.markScalarBranch x } σ.objs := by
  intro u hu hul huno hups hub p hup bv hev hbv0
  unfold RcCtx.markScalarBranch at hu
  cases hgx : rf.ctx.get? x with
  | none =>
    rw [hgx] at hu
    exact hpc u hu hul huno hups hub p hup bv hev hbv0
  | some vx =>
    rw [hgx] at hu
    by_cases hty : (vx.ty == .tobject || vx.ty == .tagged) = true
    · simp only [hty, ↓reduceIte] at hu
      obtain ⟨w, hw, hidw, htyw, hnow, hpsw, _, _, _, hbrw⟩ :=
        invalidateChildren_live_back x hu
      rcases (RcCtx.put_mem_iff hnd).mp hw with rfl | ⟨hm0, _⟩
      · simp at hnow; rw [hnow] at huno; cases huno
      · have hm0_l : w.isLive = true := by simp [RcVar.isLive, (hbrw hub).1]
        exact hpc w hm0 hm0_l (hnow ▸ huno) (hpsw ▸ hups) (hbrw hub).1 p
          ((hbrw hub).2.trans hup) bv (by simpa [hidw, htyw] using hev) hbv0
    · simp only [hty, Bool.false_eq_true, ↓reduceIte] at hu
      exact hpc u hu hul huno hups hub p hup bv hev hbv0

public theorem parentChildBacked_markExcl {rf : RcFrame} {σ : HState}
    (hnd : (rf.ctx.vars.map RcVar.id).Nodup) (x : Nat) (hpc : ParentChildBacked rf σ.objs) :
    ParentChildBacked { rf with ctx := rf.ctx.markExcl x } σ.objs := by
  intro u hu hul huno hups hub p hup bv hev hbv0
  unfold RcCtx.markExcl at hu
  cases hgx : rf.ctx.get? x with
  | none =>
    rw [hgx] at hu
    exact hpc u hu hul huno hups hub p hup bv hev hbv0
  | some vx =>
    rw [hgx] at hu
    by_cases hok : (!vx.noRc && !vx.persistent && vx.owned == 1) = true
    · simp only [hok, ↓reduceIte] at hu
      rcases (RcCtx.put_mem_iff hnd).mp hu with rfl | ⟨hm0, _⟩
      · exact hpc vx (RcCtx.get?_mem hgx).1 hul huno hups hub p hup bv hev hbv0
      · exact hpc u hm0 hul huno hups hub p hup bv hev hbv0
    · simp only [hok, Bool.false_eq_true, ↓reduceIte] at hu
      exact hpc u hu hul huno hups hub p hup bv hev hbv0

/-! ## 3. Exclusivity Disjointness Helpers -/

public theorem nonPersistReach_target_nz {objs : List LcnfObj} {r a : BitVec 64}
    (hreach : NonPersistReach objs r a) : ∃ o ∈ objs, o.addr = a ∧ o.rc ≠ 0#32 := by
  induction hreach with
  | refl h => exact h
  | step _ _ _ ht => exact ht

public theorem not_nonPersistReach_of_no_refs {objs : List LcnfObj} {r a : BitVec 64}
    (hnodup : (objs.map LcnfObj.addr).Nodup)
    (hnp : nonPersistRefs objs a = 0) (hne : r ≠ a) :
    ¬ NonPersistReach objs r a := by
  intro hreach
  cases hreach with
  | refl _ => exact hne rfl
  | step hpre hpar _ _ =>
    obtain ⟨op, hop, hoa, hch⟩ := hpar
    obtain ⟨op2, hop2, hoa2, hrc2⟩ := nonPersistReach_target_nz hpre
    have heq := obj_eq_of_addr_nodup hnodup hop hop2 (hoa.trans hoa2.symm)
    rw [← heq] at hrc2
    exact RtProof.nonPersistRefs_eq_zero_imp objs a hnp op hop hrc2 hch

public theorem not_backed_of_excl {objs : List LcnfObj} {roots : List (BitVec 64)}
    {o : LcnfObj} {addr : BitVec 64}
    (hnodup : (objs.map LcnfObj.addr).Nodup)
    (ho : o ∈ objs) (hoa : o.addr = addr) (hrc_nz : o.rc ≠ 0#32)
    (hnp : nonPersistRefs objs addr = 0) (hcnt0 : List.count addr roots = 0) :
    ¬ Backed objs roots addr := by
  rintro (⟨o2, ho2, hoa2, hrc0⟩ | ⟨r, hr, hreach⟩)
  · have := obj_eq_of_addr_nodup hnodup ho ho2 (hoa.trans hoa2.symm)
    rw [← this] at hrc0; exact hrc_nz hrc0
  · have hne : r ≠ addr := fun heq => by
      subst heq
      have hpos := List.count_pos_iff.mpr hr
      omega
    exact not_nonPersistReach_of_no_refs hnodup hnp hne hreach

public theorem excl_disjoint_facts {rt : BitVec 64} {rf : RcFrame} {σ : HState}
    (hinv : RcInv rt rf σ) (hclean : CleanVars rf.ctx)
    (_hpo : ParentsOwned rf.ctx) (hpc : ParentChildBacked rf σ.objs)
    {v : RcVar} (hv : v ∈ rf.ctx.vars) (hvno : v.noRc = false)
    (hvps : v.persistent = false) (hvrt : v.resetTok = false) (hvow : v.owned = 1)
    {addr : BitVec 64} (hve : rf.envH v.id = some (v.ty, .i64 addr))
    {o : LcnfObj} (ho : o ∈ σ.objs) (howf : o.Wf) (hoa : o.addr = addr) (horc : o.rc = 1#32) :
    nonPersistRefs σ.objs addr = 0 ∧
      List.count addr (localHandlesExcept rf.ctx rf.envH v.id ++ rf.extH ++ rf.ghostH) = 0 ∧
      ¬ addr ∈ o.childFields ∧
      (∀ u ∈ rf.ctx.vars, u.id ≠ v.id → u.isLive = true → !u.ty.isScalar = true →
        ∀ bvu, rf.envH u.id = some (u.ty, .i64 bvu) → bvu ≠ addr) ∧
      (∀ q ∈ σ.objs, q.Wf → q.addr ≠ addr →
        ∀ f ∈ q.childFields, f &&& 1#64 = 0#64 → f ≠ addr) ∧
      (∀ a, Backed σ.objs (localHandlesExcept rf.ctx rf.envH v.id ++ rf.extH ++ rf.ghostH) a →
        a ≠ addr) := by
  obtain ⟨hnp, hcnt, hself⟩ :=
    handlesRcSound_excl_unique hinv.2.1 hinv.2.2.1 hv hvno hvps hvrt hvow hve ho howf hoa horc
  have hnodup_o := hinv.1.2
  have hev_addr := obj_addr_and1_zero howf
  rw [hoa] at hev_addr
  have hno_ch : ∀ q ∈ σ.objs, q.Wf → q.addr ≠ addr →
      ∀ f ∈ q.childFields, f &&& 1#64 = 0#64 → f ≠ addr := by
    intro q hq _ _ f hf hfev hfa
    by_cases hrc0 : q.rc = 0#32
    · obtain ⟨o2, ho2, hoa2, hrc2⟩ := hinv.2.2.1.1 q hq hrc0 f hf hfev
      have heq := obj_eq_of_addr_nodup hnodup_o ho ho2 (hoa.trans (hfa.symm.trans hoa2.symm))
      rw [← heq, horc] at hrc2; cases hrc2
    · exact RtProof.nonPersistRefs_eq_zero_imp σ.objs addr hnp q hq hrc0 (hfa ▸ hf)
  have hno_u : ∀ u ∈ rf.ctx.vars, u.id ≠ v.id → u.isLive = true → !u.ty.isScalar = true →
      ∀ bvu, rf.envH u.id = some (u.ty, .i64 bvu) → bvu ≠ addr := by
    intro u hum hne hul huns bvu hevu hbveq
    subst bvu
    obtain ⟨_, wu, _, hwu, hvu_rep, hnonu⟩ := hinv.2.2.2.1 u hum hul
    have hns_u : ¬u.ty.isScalar := fun h => by simp [h] at huns
    obtain ⟨bvu', hwueq, huno_fn, hups_fn, _, hubr_fn⟩ := hnonu hns_u
    have hbv_eq : bvu' = addr := by rw [hwueq, hevu] at hwu; cases hwu; rfl
    subst bvu'
    by_cases huno_b : u.noRc = true
    · exact huno_fn huno_b hev_addr
    · have huno_f : u.noRc = false := Bool.eq_false_iff.mpr huno_b
      by_cases hups_b : u.persistent = true
      · obtain ⟨o2, ho2, hoa2, hrc2⟩ := hups_fn hups_b hev_addr
        have heq := obj_eq_of_addr_nodup hnodup_o ho ho2 (hoa.trans hoa2.symm)
        rw [← heq, horc] at hrc2; cases hrc2
      · have hups_f : u.persistent = false := Bool.eq_false_iff.mpr hups_b
        have hcv_u := hclean u hum
        by_cases hown0 : u.owned = 0
        · have hub_t : u.borrowed = true := by
            have := hul
            simp only [RcVar.isLive, huno_f, hups_f, hown0, hcv_u.2.2.2.2, Bool.false_or,
              Bool.or_false] at this
            exact this
          cases hpar : u.parent? with
          | none =>
            have hbk_ext := (hubr_fn huno_f hups_f hub_t hev_addr).2
            rw [hpar] at hbk_ext
            have hcnt_ext : List.count addr (rf.extH ++ rf.ghostH) = 0 := by
              rw [List.append_assoc, List.count_append] at hcnt
              omega
            exact not_backed_of_excl hnodup_o ho hoa (by rw [horc]; simp) hnp hcnt_ext hbk_ext
          | some p =>
            rcases hpc u hum hul huno_f hups_f hub_t p hpar addr hevu
              hev_addr with hbk_ext | ⟨wp, op, hep, hwp, hopm, o_mid,
                hom_m, hreach_mid, hcf_mid⟩
            · have hcnt_ext : List.count addr (rf.extH ++ rf.ghostH) = 0 := by
                rw [List.append_assoc, List.count_append] at hcnt
                omega
              exact not_backed_of_excl hnodup_o ho hoa (by rw [horc]; simp) hnp hcnt_ext hbk_ext
            · have hmid_nz : o_mid.rc ≠ 0#32 := by
                obtain ⟨t, ht, hta, htnz⟩ := nonPersistReach_target_nz' hreach_mid
                exact (obj_eq_of_addr_nodup hnodup_o hom_m ht hta.symm) ▸ htnz
              exact RtProof.nonPersistRefs_eq_zero_imp σ.objs addr hnp o_mid hom_m hmid_nz hcf_mid
        · have hown_pos : 0 < u.owned := Nat.pos_of_ne_zero hown0
          have hmem_vh : addr ∈ varHandles rf.envH u := by
            simp only [varHandles, huno_f, hups_f, hcv_u.2.2.2.2, beq_false_of_ne hown0,
              Bool.false_or, Bool.false_eq_true, ↓reduceIte, hevu, Word.toBV64?, Word.i64,
              beq_iff_eq.mpr hev_addr]
            exact List.mem_replicate.mpr ⟨hown0, rfl⟩
          have hmem_exc : addr ∈ localHandlesExcept rf.ctx rf.envH v.id := by
            unfold localHandlesExcept
            exact List.mem_flatten.mpr ⟨varHandles rf.envH u,
              List.mem_map.mpr ⟨u, List.mem_filter.mpr ⟨hum, bne_iff_ne.mpr hne⟩, rfl⟩,
              hmem_vh⟩
          have hcnt_pos : 1 ≤ List.count addr
              (localHandlesExcept rf.ctx rf.envH v.id ++ rf.extH ++ rf.ghostH) :=
            List.count_pos_iff.mpr
              (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hmem_exc))))
          omega
  exact ⟨hnp, hcnt, hself, hno_u, hno_ch, fun a hbk heq => by
    subst heq
    exact not_backed_of_excl hnodup_o ho hoa (by rw [horc]; simp) hnp hcnt hbk⟩

@[expose] public def NoRcCorrect (ctx : RcCtx) : Prop :=
  ∀ v ∈ ctx.vars, v.noRc = false → v.ty.needsRc = true

public theorem noRcCorrect_init (ps : List LcParam) :
    NoRcCorrect (({ vars := [], sharedPreds := [] } : RcCtx).bindParams ps) := by
  suffices h : ∀ (ctx : RcCtx), (ctx.vars.map RcVar.id).Nodup → NoRcCorrect ctx →
      NoRcCorrect (ctx.bindParams ps) from
    h _ (by simp) (fun _ hm => nomatch hm)
  intro ctx hnd hnc
  induction ps generalizing ctx with
  | nil => exact hnc
  | cons p ps ih =>
    simp only [RcCtx.bindParams, List.foldl_cons]
    have hnd1 :
        ((if p.borrow = true then ctx.bindBorrowed p.id p.ty
          else ctx.bindOwned p.id p.ty).vars.map RcVar.id).Nodup := by
      cases p.borrow <;> simp [RcCtx.bindBorrowed, RcCtx.bindOwned] <;> exact RcCtx.put_nodup hnd _
    refine ih _ hnd1 (fun v hv hno => ?_)
    cases hb : p.borrow with
    | true =>
      simp only [hb, ↓reduceIte, RcCtx.bindBorrowed] at hv
      rcases (RcCtx.put_mem_iff hnd).mp hv with rfl | ⟨hm, _⟩
      · simp only [Bool.not_eq_false'] at hno; exact hno
      · exact hnc v hm hno
    | false =>
      simp only [hb, Bool.false_eq_true, ↓reduceIte, RcCtx.bindOwned] at hv
      rcases (RcCtx.put_mem_iff hnd).mp hv with rfl | ⟨hm, _⟩
      · simp only [Bool.not_eq_false'] at hno; exact hno
      · exact hnc v hm hno

public theorem noRcCorrect_put {ctx : RcCtx} (hnd : (ctx.vars.map RcVar.id).Nodup)
    (hnc : NoRcCorrect ctx) {v : RcVar} (hv : v.noRc = false → v.ty.needsRc = true) :
    NoRcCorrect (ctx.put v) := by
  intro u hu hno
  rcases (RcCtx.put_mem_iff hnd).mp hu with rfl | ⟨hm, _⟩
  · exact hv hno
  · exact hnc u hm hno

public theorem noRcCorrect_consumeVar {ctx : RcCtx} (hnd : (ctx.vars.map RcVar.id).Nodup)
    (hnc : NoRcCorrect ctx) {x n : Nat} {ctx' : RcCtx}
    (hc : ctx.consumeVar x n = .ok ctx') : NoRcCorrect ctx' := by
  intro v hv hno
  have hg' := rcCtx_get?_of_mem (consumeVar_nodup hnd hc) hv
  have hflg := consumeVar_preserves_flags hnd hc v.id
  rw [hg'] at hflg
  cases hg0 : ctx.get? v.id with
  | none => rw [hg0] at hflg; cases hflg
  | some v0 =>
    rw [hg0] at hflg; simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hflg
    exact hflg.2.2 ▸ hnc v0 (RcCtx.get?_mem hg0).1 (hflg.1 ▸ hno)

public theorem noRcCorrect_consumeArg {ctx : RcCtx} (hnd : (ctx.vars.map RcVar.id).Nodup)
    (hnc : NoRcCorrect ctx) {a : LcArg} {ctx' : RcCtx}
    (hc : ctx.consumeArg a = .ok ctx') : NoRcCorrect ctx' ∧ (ctx'.vars.map RcVar.id).Nodup := by
  cases a with
  | erased => simp [RcCtx.consumeArg, pure, Except.pure] at hc; subst hc; exact ⟨hnc, hnd⟩
  | var x => exact ⟨noRcCorrect_consumeVar hnd hnc hc, consumeVar_nodup hnd hc⟩

public theorem noRcCorrect_applyArgs {ctx : RcCtx} (hnd : (ctx.vars.map RcVar.id).Nodup)
    (hnc : NoRcCorrect ctx) (as : List LcArg) (bs : List Bool) {ctx' : RcCtx}
    (ha : ctx.applyArgs as bs = .ok ctx') : NoRcCorrect ctx' := by
  induction as generalizing ctx bs with
  | nil =>
    cases bs with
    | nil =>
      simp only [RcCtx.applyArgs, pure, Except.pure, Except.ok.injEq] at ha
      subst ha; exact hnc
    | cons _ _ =>
      simp only [RcCtx.applyArgs] at ha; cases ha
  | cons a as ih =>
    cases bs with
    | nil =>
      simp only [RcCtx.applyArgs] at ha; cases ha
    | cons b bs =>
      simp only [RcCtx.applyArgs] at ha
      cases b with
      | true =>
        simp only [↓reduceIte, bind, Except.bind] at ha
        cases hchk : ctx.checkArgLive a with
        | error e => rw [hchk] at ha; cases ha
        | ok _ => rw [hchk] at ha; exact ih hnd hnc bs ha
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte, bind, Except.bind] at ha
        cases hc : ctx.consumeArg a with
        | error e => rw [hc] at ha; cases ha
        | ok ctx1 =>
          rw [hc] at ha
          have ⟨hnc1, hnd1⟩ := noRcCorrect_consumeArg hnd hnc hc
          exact ih hnd1 hnc1 bs ha

public theorem getTypedBV64?_of_varInv {v : RcVar} {rf : RcFrame} {objs : List LcnfObj}
    (hvar : ∀ u ∈ rf.ctx.vars, VarInv u rf objs) (hm : v ∈ rf.ctx.vars) (hl : v.isLive = true)
    (hw64 : v.ty.width = 64) :
    ∃ bv, rf.envH v.id = some (v.ty, .i64 bv) ∧ rf.envH.getTypedBV64? v.id = some (v.ty, bv) := by
  obtain ⟨_, w, _, hw, hrep, hnon⟩ := hvar v hm hl
  by_cases hsc : v.ty.isScalar = true
  · cases hvty : v.ty <;> simp [hvty, LcTy.isScalar, LcTy.width] at hsc hw64
    all_goals
      simp only [ValRep, hvty, LcTy.isScalar, LcTy.width, ↓reduceIte] at hrep
      rcases hrep with ⟨bv, _, rfl⟩ | ⟨cidx, _, _, rfl⟩ | ⟨_, rfl⟩
      all_goals
        rw [hvty] at hw
        exact ⟨_, hw, by simp [HValEnv.getTypedBV64?, hw, Word.toBV64?]⟩
  · obtain ⟨bv, rfl, _⟩ := hnon hsc
    exact ⟨bv, hw, by simp [HValEnv.getTypedBV64?, hw, Word.toBV64?, Word.i64]⟩

@[expose] public def SharedTargetsHeap (rf : RcFrame) : Prop :=
  ∀ p ∈ rf.ctx.sharedPreds, ∀ vx, rf.ctx.get? p.2 = some vx → vx.noRc = false →
    ∃ bv, rf.envH p.2 = some (vx.ty, .i64 bv) ∧ bv &&& 1#64 = 0#64

public theorem sharedTargetsHeap_init (ps : List LcParam) (envP : PValEnv) (envH : HValEnv)
    (extH ghostH : List (BitVec 64)) :
    SharedTargetsHeap
      { ctx := ({ vars := [], sharedPreds := [] } : RcCtx).bindParams ps,
        envP := envP, envH := envH, extH := extH, ghostH := ghostH } := by
  have hsp : ∀ p : Nat × Nat,
      p ∉ (({ vars := [], sharedPreds := [] } : RcCtx).bindParams ps).sharedPreds := by
    suffices h : ∀ (ctx : RcCtx), ctx.sharedPreds = [] →
        (ctx.bindParams ps).sharedPreds = [] from by
      intro p hp; rw [h _ rfl] at hp; cases hp
    intro ctx hc
    induction ps generalizing ctx with
    | nil => exact hc
    | cons p ps ih =>
      simp only [RcCtx.bindParams, List.foldl_cons]
      refine ih _ ?_
      cases p.borrow <;> simp [RcCtx.bindBorrowed, RcCtx.bindOwned, RcCtx.put, hc]
  intro p hp; exact absurd hp (hsp p)

public theorem sharedTargetsHeap_consumeVar {rf : RcFrame}
    (hnd : (rf.ctx.vars.map RcVar.id).Nodup) (hsh : SharedTargetsHeap rf)
    {x n : Nat} {ctx' : RcCtx} (hc : rf.ctx.consumeVar x n = .ok ctx') :
    SharedTargetsHeap { rf with ctx := ctx' } := by
  intro p hp vx hgx hxno
  have hp0 := consumeVar_sharedPreds_sub hc p hp
  have hflg := consumeVar_preserves_flags hnd hc p.2
  rw [hgx] at hflg
  cases hg0 : rf.ctx.get? p.2 with
  | none => rw [hg0] at hflg; cases hflg
  | some v0 =>
    rw [hg0] at hflg; simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hflg
    exact hflg.2.2 ▸ hsh p hp0 v0 hg0 (hflg.1 ▸ hxno)

public theorem sharedTargetsHeap_put_fresh {rf : RcFrame} (hnd : (rf.ctx.vars.map RcVar.id).Nodup)
    (hsh : SharedTargetsHeap rf) {x : Nat} (hfr : binderFreshOwned rf.ctx x = true)
    {v : RcVar} (hvid : v.id = x) {envP' : PValEnv} {w : Word} {ghostH' : List (BitVec 64)}
    (hsp_sub : ∀ p ∈ (rf.ctx.put v).sharedPreds, p ∈ rf.ctx.sharedPreds) :
    SharedTargetsHeap
      { ctx := rf.ctx.put v, envP := envP', envH := rf.envH.set x v.ty w,
        extH := rf.extH, ghostH := ghostH' } := by
  intro p hp vx hgx hxno
  have hp0 := hsp_sub p hp
  have hfr_p : p.1 ≠ x ∧ p.2 ≠ x := by
    have hf := hfr
    simp only [binderFreshOwned, Bool.and_eq_true, List.all_eq_true, bne_iff_ne] at hf
    exact hf.1.2 p hp0
  have hxm := (RcCtx.get?_mem hgx).1
  have hxid := (RcCtx.get?_mem hgx).2
  rcases (RcCtx.put_mem_iff hnd).mp hxm with rfl | ⟨hm0, _⟩
  · exact absurd (hvid.symm.trans hxid) hfr_p.2.symm
  · simp only [HValEnv.set, hfr_p.2, ite_false]
    exact hsh p hp0 vx (by rw [← hxid]; exact rcCtx_get?_of_mem hnd hm0) hxno

public theorem sharedTargetsHeap_put_same {rf : RcFrame} (hnd : (rf.ctx.vars.map RcVar.id).Nodup)
    (hsh : SharedTargetsHeap rf) {v v' : RcVar} (hg : rf.ctx.get? v.id = some v)
    (hid : v'.id = v.id) (hno : v'.noRc = v.noRc) (hty : v'.ty = v.ty) :
    SharedTargetsHeap { rf with ctx := rf.ctx.put v' } := by
  intro p hp vx hgx hxno
  have hp0 : p ∈ rf.ctx.sharedPreds := by simpa [RcCtx.put] using hp
  have hxm := (RcCtx.get?_mem hgx).1
  have hxid := (RcCtx.get?_mem hgx).2
  rcases (RcCtx.put_mem_iff hnd).mp hxm with rfl | ⟨hm0, _⟩
  · have hg' : rf.ctx.get? p.2 = some v := by rw [← hxid, hid]; exact hg
    have := hsh p hp0 v hg' (hno ▸ hxno)
    simpa [hid, hty] using this
  · exact hsh p hp0 vx (by rw [← hxid]; exact rcCtx_get?_of_mem hnd hm0) hxno

end LeanQbe.T.LeanLCNF.Sem