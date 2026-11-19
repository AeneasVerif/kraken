module

public import LeanQbe.T.LegalWpSimdLemmas

/-!
# Legalization scalar widening, `TreeRel` bridges, and `legalOp_wp` helpers (`T5`, Part 3a)
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T

section LegalWp


private theorem opWp_minGe_none_not_mem (n : Nat) : ∀ (ws : List Nat),
    minGe n ws = none → ∀ x ∈ ws, ¬ (n ≤ x)
  | [], _, _, hx => by cases hx
  | a :: ws, h, x, hx => by
    change (match minGe n ws with
      | none => if n ≤ a then some a else none
      | some best =>
          if (decide (n ≤ a) && decide (a < best)) = true then some a else some best) = none at h
    cases hm : minGe n ws with
    | none =>
      rw [hm] at h; dsimp only at h
      split at h
      · cases h
      · rcases List.mem_cons.mp hx with rfl | hmem
        · assumption
        · exact opWp_minGe_none_not_mem n ws hm x hmem
    | some best =>
      rw [hm] at h; dsimp only at h
      split at h <;> cases h

private theorem opWp_minGe_spec (n : Nat) : ∀ (ws : List Nat) (w : Nat),
    minGe n ws = some w → w ∈ ws ∧ n ≤ w ∧ ∀ x ∈ ws, n ≤ x → w ≤ x
  | [], _, h => by simp [minGe] at h
  | a :: ws, w, h => by
    change (match minGe n ws with
      | none => if n ≤ a then some a else none
      | some best =>
          if (decide (n ≤ a) && decide (a < best)) = true then some a else some best) = some w at h
    cases hm : minGe n ws with
    | none =>
      rw [hm] at h; dsimp only at h
      split at h
      · rename_i hna
        cases h
        refine ⟨by simp, hna, ?_⟩
        intro x hx hnx
        rcases List.mem_cons.mp hx with rfl | hmem
        · exact Nat.le_refl _
        · exact False.elim (opWp_minGe_none_not_mem n ws hm x hmem hnx)
      · cases h
    | some best =>
      rw [hm] at h; dsimp only at h
      have ih := opWp_minGe_spec n ws best hm
      split at h
      · rename_i hcond
        cases h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
        refine ⟨by simp, hcond.1, ?_⟩
        intro x hx hnx
        rcases List.mem_cons.mp hx with rfl | hmem
        · exact Nat.le_refl _
        · exact Nat.le_trans (Nat.le_of_lt hcond.2) (ih.2.2 x hmem hnx)
      · rename_i hcond
        cases h
        refine ⟨List.mem_cons_of_mem _ ih.1, ih.2.1, ?_⟩
        intro x hx hnx
        rcases List.mem_cons.mp hx with rfl | hmem
        · simp only [Bool.and_eq_true, decide_eq_true_eq, not_and] at hcond
          exact Nat.le_of_not_lt (hcond hnx)
        · exact ih.2.2 x hmem hnx

private theorem opWp_minGe_some_of_mem {n x : Nat} (ws : List Nat) (hx : x ∈ ws) (hnx : n ≤ x) :
    ∃ w, minGe n ws = some w := by
  induction ws with
  | nil => cases hx
  | cons a ws ih =>
    change ∃ w, (match minGe n ws with
      | none => if n ≤ a then some a else none
      | some best =>
          if (decide (n ≤ a) && decide (a < best)) = true then some a else some best) = some w
    cases hm : minGe n ws with
    | none =>
      rcases List.mem_cons.mp hx with rfl | hmem
      · simp [hnx]
      · exact absurd (ih hmem) (by simp [hm])
    | some best =>
      simp only
      split
      · exact ⟨a, rfl⟩
      · exact ⟨best, rfl⟩

private theorem opWp_minGe_mem {n : Nat} {ws : List Nat} (hn : n ∈ ws) :
    minGe n ws = some n := by
  obtain ⟨w, hw⟩ := opWp_minGe_some_of_mem ws hn (Nat.le_refl n)
  obtain ⟨_, hnw, hmin⟩ := opWp_minGe_spec n ws w hw
  have hwn : w = n := Nat.le_antisymm (hmin n hn (Nat.le_refl n)) hnw
  rw [hw, hwn]

theorem opWp_widen_spec {target : LegalTarget} (hv : target.valid = true) {n : Nat}
    (hs : target.supportsTy (Ty.bits n) = true) :
    let w := target.widenWidth n
    w ∈ target.bitWidths ∧ n ≤ w ∧ 0 < w ∧ w % 8 = 0 ∧ w ≤ 64 ∧ n ≤ 64 ∧
    (∀ u ∈ target.bitWidths, n ≤ u → w ≤ u) := by
  have hs' := hs
  simp only [LegalTarget.supportsTy, Bool.and_eq_true, List.any_eq_true, decide_eq_true_eq] at hs'
  obtain ⟨⟨u, hu, hnu⟩, hn64⟩ := hs'
  obtain ⟨w, hw⟩ := opWp_minGe_some_of_mem target.bitWidths hu hnu
  obtain ⟨hwm, hnw, hmin⟩ := opWp_minGe_spec n target.bitWidths w hw
  have hv' := hv
  simp only [LegalTarget.valid, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hv'
  have hbw := hv'.1.2 w hwm
  simp only [beq_iff_eq] at hbw
  have heq : target.widenWidth n = w := by simp [LegalTarget.widenWidth, hw]
  dsimp only
  rw [heq]
  exact ⟨hwm, hnw, hbw.1.1, hbw.1.2, hbw.2, hn64, hmin⟩

theorem opWp_widen_mono {target : LegalTarget} (hv : target.valid = true) {m n : Nat}
    (hm : target.supportsTy (Ty.bits m) = true) (hn : target.supportsTy (Ty.bits n) = true)
    (hmn : m ≤ n) : target.widenWidth m ≤ target.widenWidth n := by
  have sm := opWp_widen_spec hv hm
  have sn := opWp_widen_spec hv hn
  exact sm.2.2.2.2.2.2 (target.widenWidth n) sn.1 (Nat.le_trans hmn sn.2.1)

theorem opWp_isLegalTy_legalTys {target : LegalTarget} {t : Ty}
    (ht : target.isLegalTy t = true) : target.legalTys t = [t] := by
  cases t with
  | bool => rfl
  | bits n =>
    have hn : n ∈ target.bitWidths := by simpa [LegalTarget.isLegalTy] using ht
    simp [LegalTarget.legalTys, LegalTarget.widenWidth, opWp_minGe_mem hn]
  | float f => rfl
  | pair a b =>
    have hkp : target.keepsPacked (a.pair b) = true := ht
    simp [LegalTarget.legalTys, hkp]

private theorem opWp_tupAppend_vals {ts₁ ts₂ : List Ty}
    (xs₁ : Tup (Arg Val) ts₁) (xs₂ : Tup (Arg Val) ts₂) :
    valsTup (tupAppend xs₁ xs₂) = tupAppend (valsTup xs₁) (valsTup xs₂) := by
  induction ts₁ with
  | nil => cases xs₁; rfl
  | cons a ts ih =>
    rcases xs₁ with ⟨x, xs⟩
    change (x.val, valsTup (tupAppend xs xs₂)) = (x.val, tupAppend (valsTup xs) (valsTup xs₂))
    rw [ih]

private theorem opWp_tupSplit_tupAppend {α : Type} {f : α → Type} {ts₁ ts₂ : List α}
    (xs₁ : Tup f ts₁) (xs₂ : Tup f ts₂) :
    tupSplit (tupAppend xs₁ xs₂) = (xs₁, xs₂) := by
  induction ts₁ with
  | nil => cases xs₁; rfl
  | cons a ts ih =>
    rcases xs₁ with ⟨x, xs⟩
    change (match tupSplit (tupAppend xs xs₂) with | (l, r) => ((x, l), r)) = ((x, xs), xs₂)
    rw [ih]

private theorem opWp_valsTup_tupSplit {ts₁ ts₂ : List Ty} (z : Tup (Arg Val) (ts₁ ++ ts₂)) :
    valsTup (tupSplit z).1 = (tupSplit (valsTup z)).1 ∧
    valsTup (tupSplit z).2 = (tupSplit (valsTup z)).2 := by
  induction ts₁ with
  | nil => exact ⟨rfl, rfl⟩
  | cons a ts ih =>
    rcases z with ⟨x, rest⟩
    have hrest := ih rest
    refine ⟨?_, hrest.2⟩
    change (x.val, valsTup (tupSplit rest).1) = (x.val, (tupSplit (valsTup rest)).1)
    rw [hrest.1]

theorem opWp_valsTup_encodeImm (target : LegalTarget) (t : Ty) (v : Val t) :
    valsTup (encodeImm (V := Val) target t v) = encodeVal target t v := by
  induction t with
  | bool => rfl
  | bits n => rfl
  | float f => rfl
  | pair a b iha ihb =>
    unfold encodeImm
    dsimp only
    by_cases h : target.keepsPacked (a.pair b) = true
    · simp only [h, ↓reduceDIte]
      have hlt : target.legalTys (a.pair b) = [a.pair b] := by
        simp [LegalTarget.legalTys, h]
      rw [encodeVal_self target (show target.isLegalTy (a.pair b) = true from h)]
      unfold tupToPacked
      have hm : ∀ (ls : List Ty) (hl : ls = [a.pair b]),
          valsTup (cast (congrArg (Tup (Arg Val)) hl.symm) (Arg.imm (V := Val) v, ())) =
            cast (congrArg (Tup Val) hl.symm) (v, ()) := by
        intro ls hl; subst hl; rfl
      exact hm (target.legalTys (a.pair b)) hlt
    · have hf : target.keepsPacked (a.pair b) = false := Bool.eq_false_iff.mpr h
      simp only [hf, Bool.false_eq_true, ↓reduceDIte]
      have hlt : target.legalTys (a.pair b) = target.legalTys a ++ target.legalTys b := by
        simp [LegalTarget.legalTys, hf]
      have hm : ∀ (ls : List Ty) (hl : ls = target.legalTys a ++ target.legalTys b)
          (xs : Tup (Arg Val) (target.legalTys a ++ target.legalTys b)),
          valsTup (cast (congrArg (Tup (Arg Val)) hl.symm) xs) =
            cast (congrArg (Tup Val) hl.symm) (valsTup xs) := by
        intro ls hl xs; subst hl; rfl
      unfold tupToSplit
      rw [hm (target.legalTys (a.pair b)) hlt, opWp_tupAppend_vals, iha v.1, ihb v.2]
      simp [encodeVal, hf]

theorem opWp_valsTup_tupToPacked {target : LegalTarget} {a b : Ty}
    (h : target.keepsPacked (a.pair b) = true) (xs : Tup (Arg Val) [a.pair b]) :
    valsTup (tupToPacked h xs) = encodeVal target (a.pair b) xs.1.val := by
  have hlt : target.legalTys (a.pair b) = [a.pair b] := by
    simp [LegalTarget.legalTys, h]
  rw [encodeVal_self target (show target.isLegalTy (a.pair b) = true from h)]
  unfold tupToPacked
  have hm : ∀ (ls : List Ty) (hl : ls = [a.pair b]) (xs : Tup (Arg Val) [a.pair b]),
      valsTup (cast (congrArg (Tup (Arg Val)) hl.symm) xs) =
        cast (congrArg (Tup Val) hl.symm) (xs.1.val, ()) := by
    intro ls hl ⟨x, ⟨⟩⟩; subst hl; rfl
  exact hm (target.legalTys (a.pair b)) hlt xs

theorem opWp_packedToTup_fst {target : LegalTarget} {a b : Ty}
    (h : target.keepsPacked (a.pair b) = true)
    (lp : Tup (Arg Val) (target.legalTys (a.pair b))) (v : Val (a.pair b))
    (hval : valsTup lp = encodeVal target (a.pair b) v) :
    (packedToTup h lp).fst.val = v := by
  have hlt : target.legalTys (a.pair b) = [a.pair b] := by
    simp [LegalTarget.legalTys, h]
  rw [encodeVal_self target (show target.isLegalTy (a.pair b) = true from h)] at hval
  unfold packedToTup
  have hm : ∀ (ls : List Ty) (hl : ls = [a.pair b]) (lp : Tup (Arg Val) ls)
      (hval : valsTup lp = cast (congrArg (Tup Val) hl.symm) (v, ())),
      (cast (congrArg (Tup (Arg Val)) hl) lp).fst.val = v := by
    intro ls hl lp hval; subst hl; exact (Prod.mk.inj hval).1
  exact hm (target.legalTys (a.pair b)) hlt lp hval

theorem opWp_valsTup_tupToSplit {target : LegalTarget} {a b : Ty}
    (hf : target.keepsPacked (a.pair b) = false)
    (la : Tup (Arg Val) (target.legalTys a)) (lb : Tup (Arg Val) (target.legalTys b))
    {xa : Val a} {xb : Val b}
    (ha : valsTup la = encodeVal target a xa) (hb : valsTup lb = encodeVal target b xb) :
    valsTup (tupToSplit hf (tupAppend la lb)) = encodeVal target (a.pair b) (xa, xb) := by
  have hlt : target.legalTys (a.pair b) = target.legalTys a ++ target.legalTys b := by
    simp [LegalTarget.legalTys, hf]
  unfold tupToSplit
  have hm : ∀ (ls : List Ty) (hl : ls = target.legalTys a ++ target.legalTys b)
      (xs : Tup (Arg Val) (target.legalTys a ++ target.legalTys b)),
      valsTup (cast (congrArg (Tup (Arg Val)) hl.symm) xs) =
        cast (congrArg (Tup Val) hl.symm) (valsTup xs) := by
    intro ls hl xs; subst hl; rfl
  rw [hm (target.legalTys (a.pair b)) hlt, opWp_tupAppend_vals, ha, hb]
  simp [encodeVal, hf]

theorem opWp_valsTup_splitToTup {target : LegalTarget} {a b : Ty}
    (hf : target.keepsPacked (a.pair b) = false)
    (lp : Tup (Arg Val) (target.legalTys (a.pair b))) (v : Val (a.pair b))
    (hval : valsTup lp = encodeVal target (a.pair b) v) :
    valsTup (tupSplit (splitToTup hf lp)).1 = encodeVal target a v.1 ∧
    valsTup (tupSplit (splitToTup hf lp)).2 = encodeVal target b v.2 := by
  have hlt : target.legalTys (a.pair b) = target.legalTys a ++ target.legalTys b := by
    simp [LegalTarget.legalTys, hf]
  have henc : encodeVal target (a.pair b) v =
      cast (congrArg (Tup Val) hlt.symm)
        (tupAppend (encodeVal target a v.1) (encodeVal target b v.2)) := by
    simp [encodeVal, hf]
  rw [henc] at hval
  unfold splitToTup
  have hm : ∀ (ls : List Ty) (hl : ls = target.legalTys a ++ target.legalTys b)
    (lp : Tup (Arg Val) ls)
      (hval : valsTup lp = cast (congrArg (Tup Val) hl.symm)
        (tupAppend (encodeVal target a v.1) (encodeVal target b v.2))),
      valsTup (cast (congrArg (Tup (Arg Val)) hl) lp) =
        tupAppend (encodeVal target a v.1) (encodeVal target b v.2) := by
    intro ls hl lp hval; subst hl; exact hval
  have happ := hm (target.legalTys (a.pair b)) hlt lp hval
  have hsp := opWp_valsTup_tupSplit (cast (congrArg (Tup (Arg Val)) hlt) lp)
  rw [happ, opWp_tupSplit_tupAppend] at hsp
  exact hsp

theorem opWp_cast_isLegal_in {target : LegalTarget} {t : Ty} (ht : target.isLegalTy t = true)
    (hlt : target.legalTys t = [t]) (la : Tup (Arg Val) (target.legalTys t)) (x : Val t)
    (hx : valsTup la = encodeVal target t x) :
    (cast (congrArg (Tup (Arg Val)) hlt) la).fst.val = x := by
  rw [encodeVal_self target ht] at hx
  have hm : ∀ (ls : List Ty) (hl : ls = [t]) (la : Tup (Arg Val) ls)
      (hx : valsTup la = cast (congrArg (Tup Val) hl.symm) (x, ())),
      (cast (congrArg (Tup (Arg Val)) hl) la).fst.val = x := by
    intro ls hl la hx; subst hl; exact (Prod.mk.inj hx).1
  exact hm (target.legalTys t) hlt la hx

theorem opWp_cast_isLegal_out {target : LegalTarget} {t : Ty} (ht : target.isLegalTy t = true)
    (hlt : target.legalTys t = [t]) (r : Arg Val t) :
    valsTup (cast (congrArg (Tup (Arg Val)) hlt.symm) (r, ())) = encodeVal target t r.val := by
  rw [encodeVal_self target ht]
  have hm : ∀ (ls : List Ty) (hl : ls = [t]),
      valsTup (cast (congrArg (Tup (Arg Val)) hl.symm) (r, ())) =
        cast (congrArg (Tup Val) hl.symm) (r.val, ()) := by
    intro ls hl; subst hl; rfl
  exact hm (target.legalTys t) hlt

/-! #### TreeRel1 / TreeRel2 / TreeRel3 bridges -/

theorem opWp_floatResultWp_mono (f : Fmt) (r : Float.Model.UnpackedFloat)
    {p q : BitVec f.width → Prop} (hpq : ∀ x, p x → q x)
    (h : floatResultWp f r p) : floatResultWp f r q := by
  unfold floatResultWp at h ⊢
  split at h <;> rename_i hnan <;> simp only [hnan, ↓reduceIte]
  · exact fun x hx => hpq x (h x hx)
  · exact hpq _ h

theorem treeRel1_mono' {onB : Bool → (Bool → Prop) → Prop}
    {onBi : (n : Nat) → BitVec n → (BitVec n → Prop) → Prop}
    {onF : (fmt : Fmt) → BitVec fmt.width → (BitVec fmt.width → Prop) → Prop}
    {t : Ty} {x : Val t} {p q : Val t → Prop}
    (h : TreeRel1 onB onBi onF t x p) (hpq : ∀ r, p r → q r)
    (honB : ∀ a p q, (∀ r, p r → q r) → onB a p → onB a q)
    (honBi : ∀ n a p q, (∀ r, p r → q r) → onBi n a p → onBi n a q)
    (honF : ∀ fmt a p q, (∀ r, p r → q r) → onF fmt a p → onF fmt a q) :
    TreeRel1 onB onBi onF t x q :=
  TreeRel1.mono honB honBi honF hpq h

theorem treeRel2_mono' {onB : Bool → Bool → (Bool → Prop) → Prop}
    {onBi : (n : Nat) → BitVec n → BitVec n → (BitVec n → Prop) → Prop}
    {onF : (fmt : Fmt) → BitVec fmt.width → BitVec fmt.width → (BitVec fmt.width → Prop) → Prop}
    {t : Ty} {x y : Val t} {p q : Val t → Prop}
    (h : TreeRel2 onB onBi onF t x y p) (hpq : ∀ r, p r → q r)
    (honB : ∀ a b p q, (∀ r, p r → q r) → onB a b p → onB a b q)
    (honBi : ∀ n a b p q, (∀ r, p r → q r) → onBi n a b p → onBi n a b q)
    (honF : ∀ fmt a b p q, (∀ r, p r → q r) → onF fmt a b p → onF fmt a b q) :
    TreeRel2 onB onBi onF t x y q :=
  TreeRel2.mono honB honBi honF hpq h

theorem treeRel3_mono' {onB : Bool → Bool → Bool → (Bool → Prop) → Prop}
    {onBi : (n : Nat) → BitVec n → BitVec n → BitVec n → (BitVec n → Prop) → Prop}
    {onF : (fmt : Fmt) → BitVec fmt.width → BitVec fmt.width → BitVec fmt.width →
      (BitVec fmt.width → Prop) → Prop}
    {t : Ty} {x y z : Val t} {p q : Val t → Prop}
    (h : TreeRel3 onB onBi onF t x y z p) (hpq : ∀ r, p r → q r)
    (honB : ∀ a b c p q, (∀ r, p r → q r) → onB a b c p → onB a b c q)
    (honBi : ∀ n a b c p q, (∀ r, p r → q r) → onBi n a b c p → onBi n a b c q)
    (honF : ∀ fmt a b c p q, (∀ r, p r → q r) → onF fmt a b c p → onF fmt a b c q) :
    TreeRel3 onB onBi onF t x y z q :=
  TreeRel3.mono honB honBi honF hpq h

theorem opWp_treeRel1_lift1 (f : {n : Nat} → BitVec n → BitVec n) (g : Bool → Bool)
    (onF : (fmt : Fmt) → BitVec fmt.width → (BitVec fmt.width → Prop) → Prop)
    (honF : ∀ fmt (x : BitVec fmt.width) (p : BitVec fmt.width → Prop), p (f x) → onF fmt x p) :
    ∀ (t : Ty) (x : Val t) (p : Val t → Prop),
      p (lift1 f g t x) → TreeRel1 (fun a q => q (g a)) (fun _ a q => q (f a)) onF t x p
  | .bool, _, _, hp => hp
  | .bits _, _, _, hp => hp
  | .float fmt, x, p, hp => honF fmt x p hp
  | .pair a b, x, _p, hp =>
    opWp_treeRel1_lift1 f g onF honF a x.1 _ (opWp_treeRel1_lift1 f g onF honF b x.2 _ hp)

theorem opWp_treeRel1_lift1_noFloat (f : {n : Nat} → BitVec n → BitVec n) (g : Bool → Bool) :
    ∀ (t : Ty), t.hasFloat = false → ∀ (x : Val t) (p : Val t → Prop),
      p (lift1 f g t x) →
        TreeRel1 (fun a q => q (g a)) (fun _ a q => q (f a)) (fun _ _ _ => False) t x p
  | .bool, _, _, _, hp => hp
  | .bits _, _, _, _, hp => hp
  | .float _, hf, _, _, _ => by cases hf
  | .pair a b, hf, x, p, hp => by
    have hfab : a.hasFloat = false ∧ b.hasFloat = false := by
      simpa [Ty.hasFloat, Bool.or_eq_false_iff] using hf
    exact opWp_treeRel1_lift1_noFloat f g a hfab.1 x.1 _
      (opWp_treeRel1_lift1_noFloat f g b hfab.2 x.2 _ hp)

theorem opWp_lift1_of_treeRel1 (f : {n : Nat} → BitVec n → BitVec n) (g : Bool → Bool)
    (onF : (fmt : Fmt) → BitVec fmt.width → (BitVec fmt.width → Prop) → Prop)
    (honF : ∀ fmt (x : BitVec fmt.width) (p : BitVec fmt.width → Prop), onF fmt x p → p (f x))
    (honF_mono : ∀ fmt x p q, (∀ r, p r → q r) → onF fmt x p → onF fmt x q) :
    ∀ (t : Ty) (x : Val t) (p : Val t → Prop),
      TreeRel1 (fun a q => q (g a)) (fun _ a q => q (f a)) onF t x p → p (lift1 f g t x)
  | .bool, _, _, h => h
  | .bits _, _, _, h => h
  | .float fmt, x, p, h => honF fmt x p h
  | .pair a b, x, p, h =>
    have hb : ∀ (r1 : Val a),
      TreeRel1 (fun a q => q (g a)) (fun _ a q => q (f a)) onF b x.2 (fun r2 => p (r1, r2)) →
        p (r1, lift1 f g b x.2) :=
      fun r1 hr1 => opWp_lift1_of_treeRel1 f g onF honF honF_mono b x.2 (fun r2 => p (r1, r2)) hr1
    have h' : TreeRel1 (fun a q => q (g a)) (fun _ a q => q (f a)) onF a x.1
        (fun r1 =>
          TreeRel1 (fun a q => q (g a)) (fun _ a q => q (f a)) onF b x.2 (fun r2 => p (r1, r2))) :=
          h
    have ha := treeRel1_mono' h' hb (fun _ _ _ hpq h => hpq _ h) (fun _ _ _ _ hpq h => hpq _ h)
      honF_mono
    opWp_lift1_of_treeRel1 f g onF honF honF_mono a x.1 (fun r1 => p (r1, lift1 f g b x.2)) ha

theorem opWp_treeRel2_lift2 (f : {n : Nat} → BitVec n → BitVec n → BitVec n)
  (g : Bool → Bool → Bool)
    (onF : (fmt : Fmt) → BitVec fmt.width → BitVec fmt.width → (BitVec fmt.width → Prop) → Prop)
    (honF : ∀ fmt (x y : BitVec fmt.width) (p : BitVec fmt.width → Prop), p (f x y) → onF fmt x y p)
      :
    ∀ (t : Ty) (x y : Val t) (p : Val t → Prop),
      p (lift2 f g t x y) → TreeRel2 (fun a b q => q (g a b)) (fun _ a b q => q (f a b)) onF t x y p
  | .bool, _, _, _, hp => hp
  | .bits _, _, _, _, hp => hp
  | .float fmt, x, y, p, hp => honF fmt x y p hp
  | .pair a b, x, y, _p, hp =>
    opWp_treeRel2_lift2 f g onF honF a x.1 y.1 _ (opWp_treeRel2_lift2 f g onF honF b x.2 y.2 _ hp)

theorem opWp_treeRel2_lift2_noFloat (f : {n : Nat} → BitVec n → BitVec n → BitVec n)
  (g : Bool → Bool → Bool) :
    ∀ (t : Ty), t.hasFloat = false → ∀ (x y : Val t) (p : Val t → Prop),
      p (lift2 f g t x y) →
        TreeRel2 (fun a b q => q (g a b)) (fun _ a b q => q (f a b)) (fun _ _ _ _ => False) t x y p
  | .bool, _, _, _, _, hp => hp
  | .bits _, _, _, _, _, hp => hp
  | .float _, hf, _, _, _, _ => by cases hf
  | .pair a b, hf, x, y, p, hp => by
    have hfab : a.hasFloat = false ∧ b.hasFloat = false := by
      simpa [Ty.hasFloat, Bool.or_eq_false_iff] using hf
    exact opWp_treeRel2_lift2_noFloat f g a hfab.1 x.1 y.1 _
      (opWp_treeRel2_lift2_noFloat f g b hfab.2 x.2 y.2 _ hp)

theorem opWp_lift2_of_treeRel2 (f : {n : Nat} → BitVec n → BitVec n → BitVec n)
  (g : Bool → Bool → Bool)
    (onF : (fmt : Fmt) → BitVec fmt.width → BitVec fmt.width → (BitVec fmt.width → Prop) → Prop)
    (honF : ∀ fmt (x y : BitVec fmt.width) (p : BitVec fmt.width → Prop), onF fmt x y p → p (f x y))
    (honF_mono : ∀ fmt x y p q, (∀ r, p r → q r) → onF fmt x y p → onF fmt x y q) :
    ∀ (t : Ty) (x y : Val t) (p : Val t → Prop),
      TreeRel2 (fun a b q => q (g a b)) (fun _ a b q => q (f a b)) onF t x y p → p (lift2 f g t x y)
  | .bool, _, _, _, h => h
  | .bits _, _, _, _, h => h
  | .float fmt, x, y, p, h => honF fmt x y p h
  | .pair a b, x, y, p, h =>
    have hb : ∀ (r1 : Val a),
        TreeRel2 (fun a b q => q (g a b)) (fun _ a b q => q (f a b)) onF b x.2 y.2
          (fun r2 => p (r1, r2)) →
        p (r1, lift2 f g b x.2 y.2) :=
      fun r1 hr1 =>
        opWp_lift2_of_treeRel2 f g onF honF honF_mono b x.2 y.2 (fun r2 => p (r1, r2)) hr1
    have h' : TreeRel2 (fun a b q => q (g a b)) (fun _ a b q => q (f a b)) onF a x.1 y.1
        (fun r1 =>
          TreeRel2 (fun a b q => q (g a b)) (fun _ a b q => q (f a b)) onF b x.2 y.2
          (fun r2 => p (r1, r2))) := h
    have ha := treeRel2_mono' h' hb (fun _ _ _ _ hpq h => hpq _ h) (fun _ _ _ _ _ hpq h => hpq _ h)
      honF_mono
    opWp_lift2_of_treeRel2 f g onF honF honF_mono a x.1 y.1 (fun r1 => p (r1, lift2 f g b x.2 y.2))
      ha

theorem opWp_treeRel3_lift3 (f : {n : Nat} → BitVec n → BitVec n → BitVec n → BitVec n)
    (g : Bool → Bool → Bool → Bool) :
    ∀ (t : Ty) (x y z : Val t) (p : Val t → Prop),
      p (lift3 f g t x y z) →
      TreeRel3 (fun a b c q => q (g a b c)) (fun _ a b c q => q (f a b c))
        (fun _ a b c q => q (f a b c)) t x y z p
  | .bool, _, _, _, _, hp => hp
  | .bits _, _, _, _, _, hp => hp
  | .float _, _, _, _, _, hp => hp
  | .pair a b, x, y, z, _p, hp =>
    opWp_treeRel3_lift3 f g a x.1 y.1 z.1 _ (opWp_treeRel3_lift3 f g b x.2 y.2 z.2 _ hp)

theorem opWp_lift3_of_treeRel3 (f : {n : Nat} → BitVec n → BitVec n → BitVec n → BitVec n)
    (g : Bool → Bool → Bool → Bool) :
    ∀ (t : Ty) (x y z : Val t) (p : Val t → Prop),
      TreeRel3 (fun a b c q => q (g a b c)) (fun _ a b c q => q (f a b c))
        (fun _ a b c q => q (f a b c)) t x y z p →
      p (lift3 f g t x y z)
  | .bool, _, _, _, _, h => h
  | .bits _, _, _, _, _, h => h
  | .float _, _, _, _, _, h => h
  | .pair a b, x, y, z, p, h =>
    have hb : ∀ (r1 : Val a),
        TreeRel3 (fun a b c q => q (g a b c)) (fun _ a b c q => q (f a b c))
          (fun _ a b c q => q (f a b c))
          b x.2 y.2 z.2 (fun r2 => p (r1, r2)) → p (r1, lift3 f g b x.2 y.2 z.2) :=
      fun r1 hr1 => opWp_lift3_of_treeRel3 f g b x.2 y.2 z.2 (fun r2 => p (r1, r2)) hr1
    have h' : TreeRel3 (fun a b c q => q (g a b c)) (fun _ a b c q => q (f a b c))
      (fun _ a b c q => q (f a b c)) a x.1 y.1 z.1
        (fun r1 =>
          TreeRel3 (fun a b c q => q (g a b c)) (fun _ a b c q => q (f a b c))
          (fun _ a b c q => q (f a b c)) b x.2 y.2 z.2 (fun r2 => p (r1, r2))) := h
    have ha := treeRel3_mono' h' hb (fun _ _ _ _ _ hpq h => hpq _ h)
      (fun _ _ _ _ _ _ hpq h => hpq _ h) (fun _ _ _ _ _ _ hpq h => hpq _ h)
    opWp_lift3_of_treeRel3 f g a x.1 y.1 z.1 (fun r1 => p (r1, lift3 f g b x.2 y.2 z.2)) ha

theorem opWp_liftFloatRel1_mono
    (op : Float.Model.Format → Float.Model.UnpackedFloat → Float.Model.UnpackedFloat) :
    ∀ (t : Ty) (_x : Val t) {p q : Val t → Prop}, (∀ r, p r → q r) →
      liftFloatRel1 op t _x p → liftFloatRel1 op t _x q
  | .bool, _, _, _, _, h => False.elim h
  | .bits _, _, _, _, _, h => False.elim h
  | .float fmt, _, _, _, hpq, h => opWp_floatResultWp_mono fmt _ hpq h
  | .pair a b, x, _, _, hpq, h =>
    opWp_liftFloatRel1_mono op a x.1 (fun r1 hr1 =>
      opWp_liftFloatRel1_mono op b x.2 (fun r2 => hpq (r1, r2)) hr1) h

theorem opWp_liftFloatRel2_mono
    (op : Float.Model.Format → Float.Model.UnpackedFloat → Float.Model.UnpackedFloat →
      Float.Model.UnpackedFloat) :
    ∀ (t : Ty) (_x _y : Val t) {p q : Val t → Prop}, (∀ r, p r → q r) →
      liftFloatRel2 op t _x _y p → liftFloatRel2 op t _x _y q
  | .bool, _, _, _, _, _, h => False.elim h
  | .bits _, _, _, _, _, _, h => False.elim h
  | .float fmt, _, _, _, _, hpq, h => opWp_floatResultWp_mono fmt _ hpq h
  | .pair a b, x, y, _, _, hpq, h =>
    opWp_liftFloatRel2_mono op a x.1 y.1 (fun r1 hr1 =>
      opWp_liftFloatRel2_mono op b x.2 y.2 (fun r2 => hpq (r1, r2)) hr1) h

theorem opWp_liftFloatRel3_mono
    (op : Float.Model.Format → Float.Model.UnpackedFloat → Float.Model.UnpackedFloat →
      Float.Model.UnpackedFloat → Float.Model.UnpackedFloat) :
    ∀ (t : Ty) (_x _y _z : Val t) {p q : Val t → Prop}, (∀ r, p r → q r) →
      liftFloatRel3 op t _x _y _z p → liftFloatRel3 op t _x _y _z q
  | .bool, _, _, _, _, _, _, h => False.elim h
  | .bits _, _, _, _, _, _, _, h => False.elim h
  | .float fmt, _, _, _, _, _, hpq, h => opWp_floatResultWp_mono fmt _ hpq h
  | .pair a b, x, y, z, _, _, hpq, h =>
    opWp_liftFloatRel3_mono op a x.1 y.1 z.1 (fun r1 hr1 =>
      opWp_liftFloatRel3_mono op b x.2 y.2 z.2 (fun r2 => hpq (r1, r2)) hr1) h

theorem opWp_treeRel1_float1
    (op : Float.Model.Format → Float.Model.UnpackedFloat → Float.Model.UnpackedFloat) :
    ∀ (t : Ty), t.isFloatTree = true → ∀ (x : Val t) (p : Val t → Prop),
      liftFloatRel1 op t x p →
      TreeRel1 (fun _ _ => False) (fun _ _ _ => False)
        (fun fmt a q => floatResultWp fmt (op fmt.format (unpackFloat fmt a)) q) t x p
  | .bool, ht, _, _, _ => by cases ht
  | .bits _, ht, _, _, _ => by cases ht
  | .float _, _, _, _, h => h
  | .pair a b, ht, x, p, h => by
    have hft : a.isFloatTree = true ∧ b.isFloatTree = true := by
      simpa [Ty.isFloatTree, Bool.and_eq_true] using ht
    exact opWp_treeRel1_float1 op a hft.1 x.1 _
      (opWp_liftFloatRel1_mono op a x.1 (fun r1 hr1 => opWp_treeRel1_float1 op b hft.2 x.2 _ hr1) h)

private theorem opWp_float1_of_treeRel1
    (op : Float.Model.Format → Float.Model.UnpackedFloat → Float.Model.UnpackedFloat) :
    ∀ (t : Ty) (x : Val t) (p : Val t → Prop),
      TreeRel1 (fun _ _ => False) (fun _ _ _ => False)
        (fun fmt a q => floatResultWp fmt (op fmt.format (unpackFloat fmt a)) q) t x p →
      liftFloatRel1 op t x p
  | .bool, _, _, h => False.elim h
  | .bits _, _, _, h => False.elim h
  | .float _, _, _, h => h
  | .pair a b, x, p, h =>
    have h' : TreeRel1 (fun _ _ => False) (fun _ _ _ => False)
        (fun fmt a q => floatResultWp fmt (op fmt.format (unpackFloat fmt a)) q) a x.1
        (fun r1 => TreeRel1 (fun _ _ => False) (fun _ _ _ => False)
          (fun fmt a q => floatResultWp fmt (op fmt.format (unpackFloat fmt a)) q) b x.2
            (fun r2 => p (r1, r2))) := h
    have ha := treeRel1_mono' h'
      (fun r1 hr1 => opWp_float1_of_treeRel1 op b x.2 (fun r2 => p (r1, r2)) hr1)
      (fun _ _ _ _ h => False.elim h) (fun _ _ _ _ _ h => False.elim h)
      (fun fmt _ _ _ hpq hf => opWp_floatResultWp_mono fmt _ hpq hf)
    opWp_float1_of_treeRel1 op a x.1 _ ha

theorem opWp_treeRel2_float2
    (op : Float.Model.Format → Float.Model.UnpackedFloat → Float.Model.UnpackedFloat →
      Float.Model.UnpackedFloat) :
    ∀ (t : Ty), t.isFloatTree = true → ∀ (x y : Val t) (p : Val t → Prop),
      liftFloatRel2 op t x y p →
      TreeRel2 (fun _ _ _ => False) (fun _ _ _ _ => False)
        (fun fmt a b q =>
          floatResultWp fmt (op fmt.format (unpackFloat fmt a) (unpackFloat fmt b)) q) t x y p
  | .bool, ht, _, _, _, _ => by cases ht
  | .bits _, ht, _, _, _, _ => by cases ht
  | .float _, _, _, _, _, h => h
  | .pair a b, ht, x, y, p, h => by
    have hft : a.isFloatTree = true ∧ b.isFloatTree = true := by
      simpa [Ty.isFloatTree, Bool.and_eq_true] using ht
    exact opWp_treeRel2_float2 op a hft.1 x.1 y.1 _
      (opWp_liftFloatRel2_mono op a x.1 y.1
        (fun r1 hr1 => opWp_treeRel2_float2 op b hft.2 x.2 y.2 _ hr1) h)

private theorem opWp_float2_of_treeRel2
    (op : Float.Model.Format → Float.Model.UnpackedFloat → Float.Model.UnpackedFloat →
      Float.Model.UnpackedFloat) :
    ∀ (t : Ty) (x y : Val t) (p : Val t → Prop),
      TreeRel2 (fun _ _ _ => False) (fun _ _ _ _ => False)
        (fun fmt a b q =>
          floatResultWp fmt (op fmt.format (unpackFloat fmt a) (unpackFloat fmt b)) q) t x y p →
      liftFloatRel2 op t x y p
  | .bool, _, _, _, h => False.elim h
  | .bits _, _, _, _, h => False.elim h
  | .float _, _, _, _, h => h
  | .pair a b, x, y, p, h =>
    have h' : TreeRel2 (fun _ _ _ => False) (fun _ _ _ _ => False)
        (fun fmt a b q =>
          floatResultWp fmt (op fmt.format (unpackFloat fmt a) (unpackFloat fmt b)) q) a x.1 y.1
        (fun r1 => TreeRel2 (fun _ _ _ => False) (fun _ _ _ _ => False)
          (fun fmt a b q =>
            floatResultWp fmt (op fmt.format (unpackFloat fmt a) (unpackFloat fmt b)) q) b x.2 y.2
            (fun r2 => p (r1, r2))) := h
    have ha := treeRel2_mono' h'
      (fun r1 hr1 => opWp_float2_of_treeRel2 op b x.2 y.2 (fun r2 => p (r1, r2)) hr1)
      (fun _ _ _ _ _ h => False.elim h) (fun _ _ _ _ _ _ h => False.elim h)
      (fun fmt _ _ _ _ hpq hf => opWp_floatResultWp_mono fmt _ hpq hf)
    opWp_float2_of_treeRel2 op a x.1 y.1 _ ha

theorem opWp_treeRel3_float3
    (op : Float.Model.Format → Float.Model.UnpackedFloat → Float.Model.UnpackedFloat →
      Float.Model.UnpackedFloat → Float.Model.UnpackedFloat) :
    ∀ (t : Ty), t.isFloatTree = true → ∀ (x y z : Val t) (p : Val t → Prop),
      liftFloatRel3 op t x y z p →
      TreeRel3 (fun _ _ _ _ => False) (fun _ _ _ _ _ => False)
        (fun fmt a b c q =>
          floatResultWp fmt
          (op fmt.format (unpackFloat fmt a) (unpackFloat fmt b) (unpackFloat fmt c)) q)
        t x y z p
  | .bool, ht, _, _, _, _, _ => by cases ht
  | .bits _, ht, _, _, _, _, _ => by cases ht
  | .float _, _, _, _, _, _, h => h
  | .pair a b, ht, x, y, z, p, h => by
    have hft : a.isFloatTree = true ∧ b.isFloatTree = true := by
      simpa [Ty.isFloatTree, Bool.and_eq_true] using ht
    exact opWp_treeRel3_float3 op a hft.1 x.1 y.1 z.1 _
      (opWp_liftFloatRel3_mono op a x.1 y.1 z.1
        (fun r1 hr1 => opWp_treeRel3_float3 op b hft.2 x.2 y.2 z.2 _ hr1) h)

private theorem opWp_float3_of_treeRel3
    (op : Float.Model.Format → Float.Model.UnpackedFloat → Float.Model.UnpackedFloat →
      Float.Model.UnpackedFloat → Float.Model.UnpackedFloat) :
    ∀ (t : Ty) (x y z : Val t) (p : Val t → Prop),
      TreeRel3 (fun _ _ _ _ => False) (fun _ _ _ _ _ => False)
        (fun fmt a b c q =>
          floatResultWp fmt
          (op fmt.format (unpackFloat fmt a) (unpackFloat fmt b) (unpackFloat fmt c)) q)
        t x y z p →
      liftFloatRel3 op t x y z p
  | .bool, _, _, _, _, h => False.elim h
  | .bits _, _, _, _, _, h => False.elim h
  | .float _, _, _, _, _, h => h
  | .pair a b, x, y, z, p, h =>
    have h' : TreeRel3 (fun _ _ _ _ => False) (fun _ _ _ _ _ => False)
        (fun fmt a b c q =>
          floatResultWp fmt
          (op fmt.format (unpackFloat fmt a) (unpackFloat fmt b) (unpackFloat fmt c)) q) a x.1 y.1
          z.1
        (fun r1 => TreeRel3 (fun _ _ _ _ => False) (fun _ _ _ _ _ => False)
          (fun fmt a b c q =>
            floatResultWp fmt
            (op fmt.format (unpackFloat fmt a) (unpackFloat fmt b) (unpackFloat fmt c)) q) b x.2 y.2
            z.2 (fun r2 => p (r1, r2))) := h
    have ha := treeRel3_mono' h'
      (fun r1 hr1 => opWp_float3_of_treeRel3 op b x.2 y.2 z.2 (fun r2 => p (r1, r2)) hr1)
      (fun _ _ _ _ _ _ h => False.elim h) (fun _ _ _ _ _ _ _ h => False.elim h)
      (fun fmt _ _ _ _ _ hpq hf => opWp_floatResultWp_mono fmt _ hpq hf)
    opWp_float3_of_treeRel3 op a x.1 y.1 z.1 _ ha

theorem opWp_treeRel1_lift1_float (f : {n : Nat} → BitVec n → BitVec n) :
    ∀ (t : Ty), t.isFloatTree = true → ∀ (x : Val t) (p : Val t → Prop),
      p (lift1 f id t x) →
        TreeRel1 (fun _ _ => False) (fun _ _ _ => False) (fun _ a q => q (f a)) t x p
  | .bool, ht, _, _, _ => by cases ht
  | .bits _, ht, _, _, _ => by cases ht
  | .float _, _, _, _, hp => hp
  | .pair a b, ht, x, p, hp => by
    have hft : a.isFloatTree = true ∧ b.isFloatTree = true := by
      simpa [Ty.isFloatTree, Bool.and_eq_true] using ht
    exact opWp_treeRel1_lift1_float f a hft.1 x.1 _
      (opWp_treeRel1_lift1_float f b hft.2 x.2 _ hp)

theorem opWp_lift1_float_of_treeRel1 (f : {n : Nat} → BitVec n → BitVec n) :
    ∀ (t : Ty) (x : Val t) (p : Val t → Prop),
      TreeRel1 (fun _ _ => False) (fun _ _ _ => False) (fun _ a q => q (f a)) t x p →
      t.isFloatTree = true ∧ p (lift1 f id t x)
  | .bool, _, _, h => False.elim h
  | .bits _, _, _, h => False.elim h
  | .float _, _, _, h => ⟨rfl, h⟩
  | .pair a b, x, p, h => by
    have hb : ∀ (r1 : Val a),
        TreeRel1 (fun _ _ => False) (fun _ _ _ => False) (fun _ c q => q (f c)) b x.2
          (fun r2 => p (r1, r2)) →
        b.isFloatTree = true ∧ p (r1, lift1 f id b x.2) :=
      fun r1 hr1 => opWp_lift1_float_of_treeRel1 f b x.2 (fun r2 => p (r1, r2)) hr1
    have h' : TreeRel1 (fun _ _ => False) (fun _ _ _ => False) (fun _ c q => q (f c)) a x.1
        (fun r1 =>
          TreeRel1 (fun _ _ => False) (fun _ _ _ => False) (fun _ c q => q (f c)) b x.2
          (fun r2 => p (r1, r2))) := h
    have ha := treeRel1_mono' h' hb (fun _ _ _ _ h => False.elim h)
      (fun _ _ _ _ _ h => False.elim h)
      (fun _ _ _ _ hpq h => hpq _ h)
    have ha' :=
      opWp_lift1_float_of_treeRel1 f a x.1
      (fun r1 => b.isFloatTree = true ∧ p (r1, lift1 f id b x.2)) ha
    exact ⟨by simp [Ty.isFloatTree, ha'.1, ha'.2.1], ha'.2.2⟩

/-! #### Uniform shift expansion lemmas (`rotl` and `shl` -> `rotr`) -/

private theorem opWp_rotl_eq_rotr {w : Nat} (hw : 0 < w) (x : BitVec w) {s : Nat}
    (hs0 : s ≠ 0) (hsw : s < w) :
    x.rotateRight ((BitVec.ofNat w (w - s)).toNat % w) = x.rotateLeft s := by
  have hwnat : w < 2 ^ w := Nat.lt_two_pow_self
  have hws2 : w - s < 2 ^ w := Nat.lt_trans (Nat.sub_lt hw (Nat.pos_of_ne_zero hs0)) hwnat
  have hmod1 : (BitVec.ofNat w (w - s)).toNat % w = w - s := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hws2,
      Nat.mod_eq_of_lt (Nat.sub_lt hw (Nat.pos_of_ne_zero hs0))]
  rw [hmod1]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_rotateRight, BitVec.getLsbD_rotateLeft]
  have hms : s % w = s := Nat.mod_eq_of_lt hsw
  have hmws : (w - s) % w = w - s := Nat.mod_eq_of_lt (by omega)
  rw [hms, hmws]
  have hsub : w - (w - s) = s := by omega
  rw [hsub]

private theorem opWp_shl_eq_rotr_and {w : Nat} (hw : 0 < w) (x : BitVec w) {s : Nat}
    (hs0 : s ≠ 0) (hsw : s < w) :
    x.rotateRight ((BitVec.ofNat w (w - s)).toNat % w) &&& (BitVec.allOnes w <<< s) = x <<< s := by
  rw [opWp_rotl_eq_rotr hw x hs0 hsw]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only
    [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_rotateLeft,
    BitVec.getLsbD_allOnes]
  rw [Nat.mod_eq_of_lt hsw]
  by_cases his : i < s
  · simp [his]
  · have hiw : i - s < w := by omega
    simp [his, hi, hiw]

theorem opWp_rotl_uniformShift :
    ∀ (u : Ty) (c : Val u) (w s : Nat),
      uniformShiftLeaf? u c = some (w, s) →
      ∀ (x : Val u),
        u.hasFloat = false ∧
        (if (s == 0) = true then
          x = lift2 (fun {n} a b => a.rotateLeft (b.toNat % n)) (fun a _ => a) u x c
        else
          lift2 (fun {n} a b => a.rotateRight (b.toNat % n)) (fun a _ => a) u x
            (splatBits w (BitVec.ofNat w (w - s)) u) =
          lift2 (fun {n} a b => a.rotateLeft (b.toNat % n)) (fun a _ => a) u x c)
  | .bool, c, _, _, h, _ => by simp [uniformShiftLeaf?] at h
  | .float _, c, _, _, h, _ => by simp [uniformShiftLeaf?] at h
  | .bits n, c, w, s, h, x => by
    simp only [uniformShiftLeaf?] at h
    split at h
    · cases h
    · rename_i hne0
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      have hw : 0 < n := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hne0
      have hsw : c.toNat % n < n := Nat.mod_lt _ hw
      refine ⟨rfl, ?_⟩
      simp only [lift2, splatBits, ↓reduceDIte]
      split
      · rename_i hs0
        have hs0' : c.toNat % n = 0 := by simpa using hs0
        rw [hs0']; apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [hi]
      · rename_i hs0
        have hs0' : c.toNat % n ≠ 0 := by simpa using hs0
        exact opWp_rotl_eq_rotr hw x hs0' hsw
  | .pair a b, c, w, s, h, x => by
    simp only [uniformShiftLeaf?] at h
    cases ha : uniformShiftLeaf? a c.1 with
    | none => simp [ha] at h
    | some p =>
      cases hb : uniformShiftLeaf? b c.2 with
      | none => simp [ha, hb] at h
      | some q =>
        simp only [ha, hb] at h
        dsimp only [bind, Option.bind] at h
        split at h <;> simp at h
        rename_i hcond
        simp only [Bool.and_eq_true, beq_iff_eq] at hcond
        rcases h with ⟨rfl, rfl⟩
        have iha := opWp_rotl_uniformShift a c.1 p.1 p.2 ha x.1
        have ihb := opWp_rotl_uniformShift b c.2 q.1 q.2 (by rw [hb]) x.2
        refine ⟨by simp [Ty.hasFloat, iha.1, ihb.1], ?_⟩
        dsimp only [lift2, lift2._f, splatBits, splatBits._f]
        by_cases hs0 : (p.2 == 0) = true
        · have hq0 : (q.2 == 0) = true := by simpa [← hcond.2] using hs0
          simp only [hs0, hq0, ↓reduceIte] at iha ihb ⊢
          exact Prod.ext iha.2 ihb.2
        · have hsf : (p.2 == 0) = false := Bool.eq_false_iff.mpr hs0
          have hqf : (q.2 == 0) = false := by simpa [← hcond.2] using hsf
          simp only [hsf, hqf, Bool.false_eq_true, ↓reduceIte] at iha ihb ⊢
          rw [← hcond.1, ← hcond.2] at ihb
          exact Prod.ext iha.2 ihb.2

theorem opWp_shl_uniformShift :
    ∀ (u : Ty) (c : Val u) (w s : Nat),
      uniformShiftLeaf? u c = some (w, s) →
      ∀ (x : Val u),
        u.hasFloat = false ∧
        (if (s == 0) = true then
          x = lift2 (fun {n} a b => a <<< (b.toNat % n)) (fun a _ => a) u x c
        else
          lift2 (fun {_n} a b => a &&& b) (fun a b => a && b) u
            (lift2 (fun {n} a b => a.rotateRight (b.toNat % n)) (fun a _ => a) u x
              (splatBits w (BitVec.ofNat w (w - s)) u))
            (splatBits w (BitVec.allOnes w <<< s) u) =
          lift2 (fun {n} a b => a <<< (b.toNat % n)) (fun a _ => a) u x c)
  | .bool, c, _, _, h, _ => by simp [uniformShiftLeaf?] at h
  | .float _, c, _, _, h, _ => by simp [uniformShiftLeaf?] at h
  | .bits n, c, w, s, h, x => by
    simp only [uniformShiftLeaf?] at h
    split at h
    · cases h
    · rename_i hne0
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      have hw : 0 < n := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hne0
      have hsw : c.toNat % n < n := Nat.mod_lt _ hw
      refine ⟨rfl, ?_⟩
      simp only [lift2, splatBits, ↓reduceDIte]
      split
      · rename_i hs0
        have hs0' : c.toNat % n = 0 := by simpa using hs0
        rw [hs0']; exact (BitVec.shiftLeft_zero x).symm
      · rename_i hs0
        have hs0' : c.toNat % n ≠ 0 := by simpa using hs0
        exact opWp_shl_eq_rotr_and hw x hs0' hsw
  | .pair a b, c, w, s, h, x => by
    simp only [uniformShiftLeaf?] at h
    cases ha : uniformShiftLeaf? a c.1 with
    | none => simp [ha] at h
    | some p =>
      cases hb : uniformShiftLeaf? b c.2 with
      | none => simp [ha, hb] at h
      | some q =>
        simp only [ha, hb] at h
        dsimp only [bind, Option.bind] at h
        split at h <;> simp at h
        rename_i hcond
        simp only [Bool.and_eq_true, beq_iff_eq] at hcond
        rcases h with ⟨rfl, rfl⟩
        have iha := opWp_shl_uniformShift a c.1 p.1 p.2 ha x.1
        have ihb := opWp_shl_uniformShift b c.2 q.1 q.2 (by rw [hb]) x.2
        refine ⟨by simp [Ty.hasFloat, iha.1, ihb.1], ?_⟩
        dsimp only [lift2, lift2._f, splatBits, splatBits._f]
        by_cases hs0 : (p.2 == 0) = true
        · have hq0 : (q.2 == 0) = true := by simpa [← hcond.2] using hs0
          simp only [hs0, hq0, ↓reduceIte] at iha ihb ⊢
          exact Prod.ext iha.2 ihb.2
        · have hsf : (p.2 == 0) = false := Bool.eq_false_iff.mpr hs0
          have hqf : (q.2 == 0) = false := by simpa [← hcond.2] using hsf
          simp only [hsf, hqf, Bool.false_eq_true, ↓reduceIte] at iha ihb ⊢
          rw [← hcond.1, ← hcond.2] at ihb
          exact Prod.ext iha.2 ihb.2


end LegalWp

end LeanQbe.T
