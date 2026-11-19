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
      | some best => if (decide (n ≤ a) && decide (a < best)) = true then some a else some best) = none at h
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
      | some best => if (decide (n ≤ a) && decide (a < best)) = true then some a else some best) = some w at h
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
      | some best => if (decide (n ≤ a) && decide (a < best)) = true then some a else some best) = some w
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
      cast (congrArg (Tup Val) hlt.symm) (tupAppend (encodeVal target a v.1) (encodeVal target b v.2)) := by
    simp [encodeVal, hf]
  rw [henc] at hval
  unfold splitToTup
  have hm : ∀ (ls : List Ty) (hl : ls = target.legalTys a ++ target.legalTys b) (lp : Tup (Arg Val) ls)
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

private theorem treeRel1_mono' {onB : Bool → (Bool → Prop) → Prop}
    {onBi : (n : Nat) → BitVec n → (BitVec n → Prop) → Prop}
    {onF : (fmt : Fmt) → BitVec fmt.width → (BitVec fmt.width → Prop) → Prop}
    {t : Ty} {x : Val t} {p q : Val t → Prop}
    (h : TreeRel1 onB onBi onF t x p) (hpq : ∀ r, p r → q r)
    (honB : ∀ a p q, (∀ r, p r → q r) → onB a p → onB a q)
    (honBi : ∀ n a p q, (∀ r, p r → q r) → onBi n a p → onBi n a q)
    (honF : ∀ fmt a p q, (∀ r, p r → q r) → onF fmt a p → onF fmt a q) :
    TreeRel1 onB onBi onF t x q :=
  TreeRel1.mono honB honBi honF hpq h

private theorem treeRel2_mono' {onB : Bool → Bool → (Bool → Prop) → Prop}
    {onBi : (n : Nat) → BitVec n → BitVec n → (BitVec n → Prop) → Prop}
    {onF : (fmt : Fmt) → BitVec fmt.width → BitVec fmt.width → (BitVec fmt.width → Prop) → Prop}
    {t : Ty} {x y : Val t} {p q : Val t → Prop}
    (h : TreeRel2 onB onBi onF t x y p) (hpq : ∀ r, p r → q r)
    (honB : ∀ a b p q, (∀ r, p r → q r) → onB a b p → onB a b q)
    (honBi : ∀ n a b p q, (∀ r, p r → q r) → onBi n a b p → onBi n a b q)
    (honF : ∀ fmt a b p q, (∀ r, p r → q r) → onF fmt a b p → onF fmt a b q) :
    TreeRel2 onB onBi onF t x y q :=
  TreeRel2.mono honB honBi honF hpq h

private theorem treeRel3_mono' {onB : Bool → Bool → Bool → (Bool → Prop) → Prop}
    {onBi : (n : Nat) → BitVec n → BitVec n → BitVec n → (BitVec n → Prop) → Prop}
    {onF : (fmt : Fmt) → BitVec fmt.width → BitVec fmt.width → BitVec fmt.width → (BitVec fmt.width → Prop) → Prop}
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
      p (lift1 f g t x) → TreeRel1 (fun a q => q (g a)) (fun _ a q => q (f a)) (fun _ _ _ => False) t x p
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
    have hb : ∀ (r1 : Val a), TreeRel1 (fun a q => q (g a)) (fun _ a q => q (f a)) onF b x.2 (fun r2 => p (r1, r2)) →
        p (r1, lift1 f g b x.2) :=
      fun r1 hr1 => opWp_lift1_of_treeRel1 f g onF honF honF_mono b x.2 (fun r2 => p (r1, r2)) hr1
    have h' : TreeRel1 (fun a q => q (g a)) (fun _ a q => q (f a)) onF a x.1
        (fun r1 => TreeRel1 (fun a q => q (g a)) (fun _ a q => q (f a)) onF b x.2 (fun r2 => p (r1, r2))) := h
    have ha := treeRel1_mono' h' hb (fun _ _ _ hpq h => hpq _ h) (fun _ _ _ _ hpq h => hpq _ h) honF_mono
    opWp_lift1_of_treeRel1 f g onF honF honF_mono a x.1 (fun r1 => p (r1, lift1 f g b x.2)) ha

private theorem opWp_treeRel2_lift2 (f : {n : Nat} → BitVec n → BitVec n → BitVec n) (g : Bool → Bool → Bool)
    (onF : (fmt : Fmt) → BitVec fmt.width → BitVec fmt.width → (BitVec fmt.width → Prop) → Prop)
    (honF : ∀ fmt (x y : BitVec fmt.width) (p : BitVec fmt.width → Prop), p (f x y) → onF fmt x y p) :
    ∀ (t : Ty) (x y : Val t) (p : Val t → Prop),
      p (lift2 f g t x y) → TreeRel2 (fun a b q => q (g a b)) (fun _ a b q => q (f a b)) onF t x y p
  | .bool, _, _, _, hp => hp
  | .bits _, _, _, _, hp => hp
  | .float fmt, x, y, p, hp => honF fmt x y p hp
  | .pair a b, x, y, _p, hp =>
    opWp_treeRel2_lift2 f g onF honF a x.1 y.1 _ (opWp_treeRel2_lift2 f g onF honF b x.2 y.2 _ hp)

private theorem opWp_treeRel2_lift2_noFloat (f : {n : Nat} → BitVec n → BitVec n → BitVec n) (g : Bool → Bool → Bool) :
    ∀ (t : Ty), t.hasFloat = false → ∀ (x y : Val t) (p : Val t → Prop),
      p (lift2 f g t x y) → TreeRel2 (fun a b q => q (g a b)) (fun _ a b q => q (f a b)) (fun _ _ _ _ => False) t x y p
  | .bool, _, _, _, _, hp => hp
  | .bits _, _, _, _, _, hp => hp
  | .float _, hf, _, _, _, _ => by cases hf
  | .pair a b, hf, x, y, p, hp => by
    have hfab : a.hasFloat = false ∧ b.hasFloat = false := by
      simpa [Ty.hasFloat, Bool.or_eq_false_iff] using hf
    exact opWp_treeRel2_lift2_noFloat f g a hfab.1 x.1 y.1 _
      (opWp_treeRel2_lift2_noFloat f g b hfab.2 x.2 y.2 _ hp)

private theorem opWp_lift2_of_treeRel2 (f : {n : Nat} → BitVec n → BitVec n → BitVec n) (g : Bool → Bool → Bool)
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
        TreeRel2 (fun a b q => q (g a b)) (fun _ a b q => q (f a b)) onF b x.2 y.2 (fun r2 => p (r1, r2)) →
        p (r1, lift2 f g b x.2 y.2) :=
      fun r1 hr1 => opWp_lift2_of_treeRel2 f g onF honF honF_mono b x.2 y.2 (fun r2 => p (r1, r2)) hr1
    have h' : TreeRel2 (fun a b q => q (g a b)) (fun _ a b q => q (f a b)) onF a x.1 y.1
        (fun r1 => TreeRel2 (fun a b q => q (g a b)) (fun _ a b q => q (f a b)) onF b x.2 y.2 (fun r2 => p (r1, r2))) := h
    have ha := treeRel2_mono' h' hb (fun _ _ _ _ hpq h => hpq _ h) (fun _ _ _ _ _ hpq h => hpq _ h) honF_mono
    opWp_lift2_of_treeRel2 f g onF honF honF_mono a x.1 y.1 (fun r1 => p (r1, lift2 f g b x.2 y.2)) ha

theorem opWp_treeRel3_lift3 (f : {n : Nat} → BitVec n → BitVec n → BitVec n → BitVec n)
    (g : Bool → Bool → Bool → Bool) :
    ∀ (t : Ty) (x y z : Val t) (p : Val t → Prop),
      p (lift3 f g t x y z) →
      TreeRel3 (fun a b c q => q (g a b c)) (fun _ a b c q => q (f a b c)) (fun _ a b c q => q (f a b c)) t x y z p
  | .bool, _, _, _, _, hp => hp
  | .bits _, _, _, _, _, hp => hp
  | .float _, _, _, _, _, hp => hp
  | .pair a b, x, y, z, _p, hp =>
    opWp_treeRel3_lift3 f g a x.1 y.1 z.1 _ (opWp_treeRel3_lift3 f g b x.2 y.2 z.2 _ hp)

theorem opWp_lift3_of_treeRel3 (f : {n : Nat} → BitVec n → BitVec n → BitVec n → BitVec n)
    (g : Bool → Bool → Bool → Bool) :
    ∀ (t : Ty) (x y z : Val t) (p : Val t → Prop),
      TreeRel3 (fun a b c q => q (g a b c)) (fun _ a b c q => q (f a b c)) (fun _ a b c q => q (f a b c)) t x y z p →
      p (lift3 f g t x y z)
  | .bool, _, _, _, _, h => h
  | .bits _, _, _, _, _, h => h
  | .float _, _, _, _, _, h => h
  | .pair a b, x, y, z, p, h =>
    have hb : ∀ (r1 : Val a),
        TreeRel3 (fun a b c q => q (g a b c)) (fun _ a b c q => q (f a b c)) (fun _ a b c q => q (f a b c))
          b x.2 y.2 z.2 (fun r2 => p (r1, r2)) → p (r1, lift3 f g b x.2 y.2 z.2) :=
      fun r1 hr1 => opWp_lift3_of_treeRel3 f g b x.2 y.2 z.2 (fun r2 => p (r1, r2)) hr1
    have h' : TreeRel3 (fun a b c q => q (g a b c)) (fun _ a b c q => q (f a b c)) (fun _ a b c q => q (f a b c)) a x.1 y.1 z.1
        (fun r1 => TreeRel3 (fun a b c q => q (g a b c)) (fun _ a b c q => q (f a b c)) (fun _ a b c q => q (f a b c)) b x.2 y.2 z.2 (fun r2 => p (r1, r2))) := h
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

private theorem opWp_liftFloatRel2_mono
    (op : Float.Model.Format → Float.Model.UnpackedFloat → Float.Model.UnpackedFloat → Float.Model.UnpackedFloat) :
    ∀ (t : Ty) (_x _y : Val t) {p q : Val t → Prop}, (∀ r, p r → q r) →
      liftFloatRel2 op t _x _y p → liftFloatRel2 op t _x _y q
  | .bool, _, _, _, _, _, h => False.elim h
  | .bits _, _, _, _, _, _, h => False.elim h
  | .float fmt, _, _, _, _, hpq, h => opWp_floatResultWp_mono fmt _ hpq h
  | .pair a b, x, y, _, _, hpq, h =>
    opWp_liftFloatRel2_mono op a x.1 y.1 (fun r1 hr1 =>
      opWp_liftFloatRel2_mono op b x.2 y.2 (fun r2 => hpq (r1, r2)) hr1) h

theorem opWp_liftFloatRel3_mono
    (op : Float.Model.Format → Float.Model.UnpackedFloat → Float.Model.UnpackedFloat → Float.Model.UnpackedFloat → Float.Model.UnpackedFloat) :
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
          (fun fmt a q => floatResultWp fmt (op fmt.format (unpackFloat fmt a)) q) b x.2 (fun r2 => p (r1, r2))) := h
    have ha := treeRel1_mono' h' (fun r1 hr1 => opWp_float1_of_treeRel1 op b x.2 (fun r2 => p (r1, r2)) hr1)
      (fun _ _ _ _ h => False.elim h) (fun _ _ _ _ _ h => False.elim h)
      (fun fmt _ _ _ hpq hf => opWp_floatResultWp_mono fmt _ hpq hf)
    opWp_float1_of_treeRel1 op a x.1 _ ha

private theorem opWp_treeRel2_float2
    (op : Float.Model.Format → Float.Model.UnpackedFloat → Float.Model.UnpackedFloat → Float.Model.UnpackedFloat) :
    ∀ (t : Ty), t.isFloatTree = true → ∀ (x y : Val t) (p : Val t → Prop),
      liftFloatRel2 op t x y p →
      TreeRel2 (fun _ _ _ => False) (fun _ _ _ _ => False)
        (fun fmt a b q => floatResultWp fmt (op fmt.format (unpackFloat fmt a) (unpackFloat fmt b)) q) t x y p
  | .bool, ht, _, _, _, _ => by cases ht
  | .bits _, ht, _, _, _, _ => by cases ht
  | .float _, _, _, _, _, h => h
  | .pair a b, ht, x, y, p, h => by
    have hft : a.isFloatTree = true ∧ b.isFloatTree = true := by
      simpa [Ty.isFloatTree, Bool.and_eq_true] using ht
    exact opWp_treeRel2_float2 op a hft.1 x.1 y.1 _
      (opWp_liftFloatRel2_mono op a x.1 y.1 (fun r1 hr1 => opWp_treeRel2_float2 op b hft.2 x.2 y.2 _ hr1) h)

private theorem opWp_float2_of_treeRel2
    (op : Float.Model.Format → Float.Model.UnpackedFloat → Float.Model.UnpackedFloat → Float.Model.UnpackedFloat) :
    ∀ (t : Ty) (x y : Val t) (p : Val t → Prop),
      TreeRel2 (fun _ _ _ => False) (fun _ _ _ _ => False)
        (fun fmt a b q => floatResultWp fmt (op fmt.format (unpackFloat fmt a) (unpackFloat fmt b)) q) t x y p →
      liftFloatRel2 op t x y p
  | .bool, _, _, _, h => False.elim h
  | .bits _, _, _, _, h => False.elim h
  | .float _, _, _, _, h => h
  | .pair a b, x, y, p, h =>
    have h' : TreeRel2 (fun _ _ _ => False) (fun _ _ _ _ => False)
        (fun fmt a b q => floatResultWp fmt (op fmt.format (unpackFloat fmt a) (unpackFloat fmt b)) q) a x.1 y.1
        (fun r1 => TreeRel2 (fun _ _ _ => False) (fun _ _ _ _ => False)
          (fun fmt a b q => floatResultWp fmt (op fmt.format (unpackFloat fmt a) (unpackFloat fmt b)) q) b x.2 y.2 (fun r2 => p (r1, r2))) := h
    have ha := treeRel2_mono' h' (fun r1 hr1 => opWp_float2_of_treeRel2 op b x.2 y.2 (fun r2 => p (r1, r2)) hr1)
      (fun _ _ _ _ _ h => False.elim h) (fun _ _ _ _ _ _ h => False.elim h)
      (fun fmt _ _ _ _ hpq hf => opWp_floatResultWp_mono fmt _ hpq hf)
    opWp_float2_of_treeRel2 op a x.1 y.1 _ ha

theorem opWp_treeRel3_float3
    (op : Float.Model.Format → Float.Model.UnpackedFloat → Float.Model.UnpackedFloat → Float.Model.UnpackedFloat → Float.Model.UnpackedFloat) :
    ∀ (t : Ty), t.isFloatTree = true → ∀ (x y z : Val t) (p : Val t → Prop),
      liftFloatRel3 op t x y z p →
      TreeRel3 (fun _ _ _ _ => False) (fun _ _ _ _ _ => False)
        (fun fmt a b c q => floatResultWp fmt (op fmt.format (unpackFloat fmt a) (unpackFloat fmt b) (unpackFloat fmt c)) q)
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
    (op : Float.Model.Format → Float.Model.UnpackedFloat → Float.Model.UnpackedFloat → Float.Model.UnpackedFloat → Float.Model.UnpackedFloat) :
    ∀ (t : Ty) (x y z : Val t) (p : Val t → Prop),
      TreeRel3 (fun _ _ _ _ => False) (fun _ _ _ _ _ => False)
        (fun fmt a b c q => floatResultWp fmt (op fmt.format (unpackFloat fmt a) (unpackFloat fmt b) (unpackFloat fmt c)) q)
        t x y z p →
      liftFloatRel3 op t x y z p
  | .bool, _, _, _, _, h => False.elim h
  | .bits _, _, _, _, _, h => False.elim h
  | .float _, _, _, _, _, h => h
  | .pair a b, x, y, z, p, h =>
    have h' : TreeRel3 (fun _ _ _ _ => False) (fun _ _ _ _ _ => False)
        (fun fmt a b c q => floatResultWp fmt (op fmt.format (unpackFloat fmt a) (unpackFloat fmt b) (unpackFloat fmt c)) q) a x.1 y.1 z.1
        (fun r1 => TreeRel3 (fun _ _ _ _ => False) (fun _ _ _ _ _ => False)
          (fun fmt a b c q => floatResultWp fmt (op fmt.format (unpackFloat fmt a) (unpackFloat fmt b) (unpackFloat fmt c)) q) b x.2 y.2 z.2 (fun r2 => p (r1, r2))) := h
    have ha := treeRel3_mono' h' (fun r1 hr1 => opWp_float3_of_treeRel3 op b x.2 y.2 z.2 (fun r2 => p (r1, r2)) hr1)
      (fun _ _ _ _ _ _ h => False.elim h) (fun _ _ _ _ _ _ _ h => False.elim h)
      (fun fmt _ _ _ _ _ hpq hf => opWp_floatResultWp_mono fmt _ hpq hf)
    opWp_float3_of_treeRel3 op a x.1 y.1 z.1 _ ha

theorem opWp_treeRel1_lift1_float (f : {n : Nat} → BitVec n → BitVec n) :
    ∀ (t : Ty), t.isFloatTree = true → ∀ (x : Val t) (p : Val t → Prop),
      p (lift1 f id t x) → TreeRel1 (fun _ _ => False) (fun _ _ _ => False) (fun _ a q => q (f a)) t x p
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
        TreeRel1 (fun _ _ => False) (fun _ _ _ => False) (fun _ c q => q (f c)) b x.2 (fun r2 => p (r1, r2)) →
        b.isFloatTree = true ∧ p (r1, lift1 f id b x.2) :=
      fun r1 hr1 => opWp_lift1_float_of_treeRel1 f b x.2 (fun r2 => p (r1, r2)) hr1
    have h' : TreeRel1 (fun _ _ => False) (fun _ _ _ => False) (fun _ c q => q (f c)) a x.1
        (fun r1 => TreeRel1 (fun _ _ => False) (fun _ _ _ => False) (fun _ c q => q (f c)) b x.2 (fun r2 => p (r1, r2))) := h
    have ha := treeRel1_mono' h' hb (fun _ _ _ _ h => False.elim h) (fun _ _ _ _ _ h => False.elim h)
      (fun _ _ _ _ hpq h => hpq _ h)
    have ha' := opWp_lift1_float_of_treeRel1 f a x.1 (fun r1 => b.isFloatTree = true ∧ p (r1, lift1 f id b x.2)) ha
    exact ⟨by simp [Ty.isFloatTree, ha'.1, ha'.2.1], ha'.2.2⟩

/-! #### Uniform shift expansion lemmas (`rotl` and `shl` -> `rotr`) -/

private theorem opWp_rotl_eq_rotr {w : Nat} (hw : 0 < w) (x : BitVec w) {s : Nat}
    (hs0 : s ≠ 0) (hsw : s < w) :
    x.rotateRight ((BitVec.ofNat w (w - s)).toNat % w) = x.rotateLeft s := by
  have hwnat : w < 2 ^ w := Nat.lt_two_pow_self
  have hws2 : w - s < 2 ^ w := Nat.lt_trans (Nat.sub_lt hw (Nat.pos_of_ne_zero hs0)) hwnat
  have hmod1 : (BitVec.ofNat w (w - s)).toNat % w = w - s := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hws2, Nat.mod_eq_of_lt (Nat.sub_lt hw (Nat.pos_of_ne_zero hs0))]
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
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_rotateLeft, BitVec.getLsbD_allOnes]
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

/-! #### Bit-width widening identities -/

theorem opWp_setWidth_neg {n w : Nat} (hnw : n ≤ w) (a : BitVec n) :
    BitVec.setWidth n (-(BitVec.setWidth w a)) = -a := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_neg, BitVec.toNat_setWidth, BitVec.toNat_neg]
  have ha : a.toNat < 2 ^ n := a.isLt
  have hp : 2 ^ n ≤ 2 ^ w := Nat.pow_le_pow_right (by omega) hnw
  rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le ha hp)]
  by_cases ha0 : a.toNat = 0
  · simp [ha0]
  · have hpos : 0 < a.toNat := Nat.pos_of_ne_zero ha0
    have hlt1 : 2 ^ w - a.toNat < 2 ^ w := Nat.sub_lt (by omega) hpos
    have hlt2 : 2 ^ n - a.toNat < 2 ^ n := Nat.sub_lt (by omega) hpos
    rw [Nat.mod_eq_of_lt hlt1, Nat.mod_eq_of_lt hlt2]
    have hdvd : 2 ^ n ∣ 2 ^ w := Nat.pow_dvd_pow 2 hnw
    rcases hdvd with ⟨k, hk⟩
    have hk0 : 0 < k := by
      rcases k with _ | k'
      · simp at hk
      · exact Nat.succ_pos k'
    have hdecomp : 2 ^ w - a.toNat = 2 ^ n * (k - 1) + (2 ^ n - a.toNat) := by
      rw [hk, Nat.mul_sub_left_distrib, Nat.mul_one]; omega
    rw [hdecomp, Nat.mul_add_mod, Nat.mod_eq_of_lt hlt2]

theorem opWp_not_setWidth {n w : Nat} (hnw : n ≤ w) (a : BitVec n) :
    BitVec.setWidth n (~~~(BitVec.setWidth w a)) = ~~~a := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [hi, Nat.lt_of_lt_of_le hi hnw]

theorem opWp_ternaryLogic_setWidth {n w : Nat} (hnw : n ≤ w)
    (a b c : BitVec n) (imm : BitVec 8) :
    BitVec.setWidth n (ternaryLogic (BitVec.setWidth w a) (BitVec.setWidth w b) (BitVec.setWidth w c) imm) =
      ternaryLogic a b c imm := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_setWidth, decide_eq_true hi, Bool.true_and]
  have hiw : i < w := Nat.lt_of_lt_of_le hi hnw
  unfold ternaryLogic
  suffices h : ∀ (l : List Nat) (accW : BitVec w) (accN : BitVec n),
      accW.getLsbD i = accN.getLsbD i →
      (l.foldl (fun acc k =>
        if imm.getLsbD k = true then
          acc |||
            (if (k / 4 % 2 == 1) = true then BitVec.setWidth w a else ~~~(BitVec.setWidth w a)) &&&
            (if (k / 2 % 2 == 1) = true then BitVec.setWidth w b else ~~~(BitVec.setWidth w b)) &&&
            (if (k % 2 == 1) = true then BitVec.setWidth w c else ~~~(BitVec.setWidth w c))
        else acc) accW).getLsbD i =
      (l.foldl (fun acc k =>
        if imm.getLsbD k = true then
          acc |||
            (if (k / 4 % 2 == 1) = true then a else ~~~a) &&&
            (if (k / 2 % 2 == 1) = true then b else ~~~b) &&&
            (if (k % 2 == 1) = true then c else ~~~c)
        else acc) accN).getLsbD i from
    h (List.range 8) 0#w 0#n (by simp)
  intro l
  induction l with
  | nil => intro _ _ hacc; exact hacc
  | cons k ks ih =>
    intro accW accN hacc
    dsimp only [List.foldl_cons]
    apply ih
    split
    · simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, hacc]
      have hbit : ∀ (x : BitVec n) (flag : Bool),
          (if flag = true then BitVec.setWidth w x else ~~~(BitVec.setWidth w x)).getLsbD i =
          (if flag = true then x else ~~~x).getLsbD i := by
        intro x flag; cases flag <;> simp [hi, hiw]
      rw [hbit a _, hbit b _, hbit c _]
    · exact hacc

theorem opWp_fshl_widened {n w : Nat} (hn : 0 < n) (hnw : n < w)
    (a b c : BitVec n) :
    BitVec.setWidth n
      ((BitVec.setWidth w a <<< BitVec.ofNat w (c.toNat % n)) |||
       (BitVec.setWidth w b >>> (BitVec.ofNat w n - BitVec.ofNat w (c.toNat % n)))) =
      BitVec.extractLsb' n n ((a ++ b) <<< (c.toNat % n)) := by
  have hsn : c.toNat % n < n := Nat.mod_lt _ hn
  have hnw2 : w < 2 ^ w := Nat.lt_two_pow_self
  have hsn2 : c.toNat % n < 2 ^ w := Nat.lt_trans hsn (Nat.lt_trans hnw hnw2)
  have hn2w : n < 2 ^ w := Nat.lt_trans hnw hnw2
  have hs_val : (BitVec.ofNat w (c.toNat % n)).toNat = c.toNat % n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsn2]
  have hn_val : (BitVec.ofNat w n).toNat = n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn2w]
  have hdiff_val : (BitVec.ofNat w n - BitVec.ofNat w (c.toNat % n)).toNat = n - c.toNat % n := by
    rw [BitVec.toNat_sub, hs_val, hn_val]
    rw [← Nat.sub_add_comm (Nat.le_of_lt hsn2), Nat.add_sub_assoc (Nat.le_of_lt hsn),
      Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
  have hsl_nat : ∀ (x y : BitVec w), x <<< y = x <<< y.toNat := fun _ _ => rfl
  have hsr_nat : ∀ (x y : BitVec w), x >>> y = x >>> y.toNat := fun _ _ => rfl
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [hsl_nat, hsr_nat]
  simp only [BitVec.getLsbD_setWidth, decide_eq_true hi, Bool.true_and,
    BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_extractLsb']
  rw [hs_val, hdiff_val]
  have hiw : i < w := by omega
  have hidw : decide (i < w) = true := decide_eq_true hiw
  rw [BitVec.getLsbD_append]
  have hni_lt : ¬ (n + i < n) := by omega
  by_cases his : i < c.toNat % n
  · have hins : n - c.toNat % n + i < w := by omega
    have hsub : n + i - c.toNat % n < n := by omega
    have hnis2 : ¬ (n + i < c.toNat % n) := by omega
    simp only [decide_eq_true his, Bool.not_true,
      decide_eq_true hins, Bool.true_and, decide_eq_false hnis2, Bool.not_false,
      decide_eq_true (show n + i < n + n by omega)]
    simp [hsub, show n - c.toNat % n + i = n + i - c.toNat % n by omega]
  · have hnis2 : ¬ (n + i < c.toNat % n) := by omega
    have hn_le : ¬ (n + i - c.toNat % n < n) := by omega
    have hb0 : b.getLsbD (n - c.toNat % n + i) = false := BitVec.getLsbD_of_ge b _ (by omega)
    simp only [decide_eq_false his, Bool.not_false, hidw, Bool.true_and,
      decide_eq_true (show i - c.toNat % n < w by omega), hb0, Bool.and_false, Bool.or_false,
      decide_eq_false hnis2, decide_eq_true (show n + i < n + n by omega), hn_le, ↓reduceIte]
    congr 1; omega

theorem opWp_fshr_widened {n w : Nat} (hn : 0 < n) (hnw : n < w)
    (a b c : BitVec n) :
    BitVec.setWidth n
      ((BitVec.setWidth w b >>> BitVec.ofNat w (c.toNat % n)) |||
       (BitVec.setWidth w a <<< (BitVec.ofNat w n - BitVec.ofNat w (c.toNat % n)))) =
      BitVec.extractLsb' 0 n ((a ++ b) >>> (c.toNat % n)) := by
  have hsn : c.toNat % n < n := Nat.mod_lt _ hn
  have hnw2 : w < 2 ^ w := Nat.lt_two_pow_self
  have hsn2 : c.toNat % n < 2 ^ w := Nat.lt_trans hsn (Nat.lt_trans hnw hnw2)
  have hn2w : n < 2 ^ w := Nat.lt_trans hnw hnw2
  have hs_val : (BitVec.ofNat w (c.toNat % n)).toNat = c.toNat % n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsn2]
  have hn_val : (BitVec.ofNat w n).toNat = n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn2w]
  have hdiff_val : (BitVec.ofNat w n - BitVec.ofNat w (c.toNat % n)).toNat = n - c.toNat % n := by
    rw [BitVec.toNat_sub, hs_val, hn_val]
    rw [← Nat.sub_add_comm (Nat.le_of_lt hsn2), Nat.add_sub_assoc (Nat.le_of_lt hsn),
      Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
  have hsl_nat : ∀ (x y : BitVec w), x <<< y = x <<< y.toNat := fun _ _ => rfl
  have hsr_nat : ∀ (x y : BitVec w), x >>> y = x >>> y.toNat := fun _ _ => rfl
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [hsl_nat, hsr_nat]
  simp only [BitVec.getLsbD_setWidth, decide_eq_true hi, Bool.true_and,
    BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_extractLsb', Nat.zero_add]
  rw [hs_val, hdiff_val, BitVec.getLsbD_append]
  by_cases hins : i + c.toNat % n < n
  · have hins_w : c.toNat % n + i < w := by omega
    have hins_n : c.toNat % n + i < n := by omega
    have hlt_ns : i < n - c.toNat % n := by omega
    simp [hlt_ns, hins_w, hins_n]
  · have hb0 : b.getLsbD (c.toNat % n + i) = false := BitVec.getLsbD_of_ge b _ (by omega)
    have hge_ns : ¬ (i < n - c.toNat % n) := by omega
    have hsub_w : i - (n - c.toNat % n) < w := by omega
    have hnot : ¬ (c.toNat % n + i < n) := by omega
    have hiw : i < w := by omega
    simp [hb0, hge_ns, hsub_w, hnot, hiw, show c.toNat % n + i - n = i - (n - c.toNat % n) by omega]

theorem opWp_clz_widened {n w : Nat} (hn : 0 < n) (hnw : n < w) (a : BitVec n) :
    (BitVec.setWidth w a).clz - BitVec.ofNat w (w - n) = BitVec.setWidth w a.clz := by
  have hnw2 : w < 2 ^ w := Nat.lt_two_pow_self
  have hnn2 : n < 2 ^ n := Nat.lt_two_pow_self
  have hp : 2 ^ n ≤ 2 ^ w := Nat.pow_le_pow_right (by omega) (Nat.le_of_lt hnw)
  have hwnsub : (BitVec.ofNat w (w - n)).toNat = w - n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hsw : (BitVec.setWidth w a).toNat = a.toNat := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le a.isLt hp)]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_setWidth, hwnsub, BitVec.toNat_clz, BitVec.toNat_clz]
  by_cases ha0 : a = 0
  · subst ha0
    have hsw0 : BitVec.setWidth w (0 : BitVec n) = (0 : BitVec w) := by apply BitVec.eq_of_toNat_eq; simp
    have h0n : (if (0 : BitVec n) = 0 then n else n - ((0 : BitVec n).toNat.log2 + 1)) = n := rfl
    have h0w : (if BitVec.setWidth w (0 : BitVec n) = 0 then w else w - ((BitVec.setWidth w (0 : BitVec n)).toNat.log2 + 1)) = w := by
      rw [hsw0]; rfl
    change (_ + (if BitVec.setWidth w 0 = 0 then w else w - ((BitVec.setWidth w 0).toNat.log2 + 1))) % 2 ^ w = _
    rw [h0w, h0n, ← Nat.sub_add_comm (show w - n ≤ 2 ^ w by omega), Nat.add_sub_assoc (by omega),
      Nat.add_mod_left, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  · have ha0nat : a.toNat ≠ 0 := fun h => ha0 (BitVec.eq_of_toNat_eq h)
    have hsw_ne : BitVec.setWidth w a ≠ 0 := fun h => ha0nat (by
      have := congrArg BitVec.toNat h; simpa [hsw] using this)
    have hlog : a.toNat.log2 < n := (Nat.log2_lt ha0nat).mpr a.isLt
    simp only [ha0, hsw_ne, ↓reduceIte, hsw]
    have hle1 : a.toNat.log2 + 1 ≤ n := hlog
    have hle2 : w - n ≤ w - (a.toNat.log2 + 1) := by omega
    rw [← Nat.sub_add_comm (show w - n ≤ 2 ^ w by omega), Nat.add_sub_assoc hle2,
      Nat.add_mod_left, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    omega

private theorem opWp_clz_ge_one_of_msb_false {n : Nat} (hn : 0 < n) {x : BitVec n}
    (hx : x.msb = false) : 1 ≤ x.clz.toNat := by
  rw [BitVec.toNat_clz]
  split
  · exact hn
  · rename_i hne
    have hxn0 : x.toNat ≠ 0 := fun h => hne (BitVec.eq_of_toNat_eq h)
    have hlt_pow : x.toNat < 2 ^ (n - 1) := by
      rw [← Nat.not_le]
      intro hge'
      have hxmsb := hx
      rw [BitVec.msb_eq_getLsbD_last] at hxmsb
      have hdiv : x.toNat / 2 ^ (n - 1) = 1 := Nat.div_eq_of_lt_le (by omega) (by
        have hpow2 : (1 + 1) * 2 ^ (n - 1) = 2 ^ n := by
          calc (1 + 1) * 2 ^ (n - 1) = 2 ^ (n - 1) * 2 := by omega
            _ = 2 ^ ((n - 1) + 1) := (Nat.pow_succ 2 (n - 1)).symm
            _ = 2 ^ n := by congr 1; omega
        rw [hpow2]; exact x.isLt)
      have hbit : x.getLsbD (n - 1) = true := by
        rw [BitVec.getLsbD_eq_getElem (by omega), BitVec.getElem_eq_testBit_toNat,
          Nat.testBit_eq_decide_div_mod_eq, hdiv]; rfl
      rw [hbit] at hxmsb; cases hxmsb
    have hlog : x.toNat.log2 < n - 1 := (Nat.log2_lt hxn0).mpr hlt_pow
    omega

theorem opWp_cls_widened {n w : Nat} (hn : 0 < n) (hnw : n < w) (a : BitVec n) :
    (if (BitVec.signExtend w a).msb = true then (~~~BitVec.signExtend w a).clz else (BitVec.signExtend w a).clz) -
      1#w - BitVec.ofNat w (w - n) =
      BitVec.setWidth w ((if a.msb = true then (~~~a).clz else a.clz) - 1#n) := by
  have hnw2 : w < 2 ^ w := Nat.lt_two_pow_self
  have hnn2 : n < 2 ^ n := Nat.lt_two_pow_self
  have hp : 2 ^ n ≤ 2 ^ w := Nat.pow_le_pow_right (by omega) (Nat.le_of_lt hnw)
  have hmsb : (BitVec.signExtend w a).msb = a.msb := by
    rw [BitVec.msb_eq_getLsbD_last, BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_signExtend]
    have h1 : w - 1 < w := by omega
    have h2 : ¬ (w - 1 < n) := by omega
    simp [h1, h2, BitVec.msb_eq_getLsbD_last]
  rw [hmsb]
  let x : BitVec n := if a.msb = true then ~~~a else a
  have hxmsb : x.msb = false := by
    dsimp only [x]; cases ha : a.msb
    · exact ha
    · rw [BitVec.msb_eq_getLsbD_last]; simp only [↓reduceIte, BitVec.getLsbD_not,
        decide_eq_true (show n - 1 < n by omega), Bool.true_and]
      rw [← BitVec.msb_eq_getLsbD_last, ha]; rfl
  have hclz_ge : 1 ≤ x.clz.toNat := opWp_clz_ge_one_of_msb_false hn hxmsb
  have hclz_le : x.clz.toNat ≤ n := by
    rw [BitVec.toNat_clz]; split <;> omega
  have hbody : (if a.msb = true then (~~~BitVec.signExtend w a).clz else (BitVec.signExtend w a).clz) =
      (BitVec.setWidth w x).clz := by
    cases ha : a.msb
    · simp only [ha, Bool.false_eq_true, ↓reduceIte, x, BitVec.signExtend_eq_setWidth_of_msb_false ha]
    · simp only [ha, ↓reduceIte, x]
      congr 1
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      simp only [BitVec.getLsbD_not, BitVec.getLsbD_signExtend, BitVec.getLsbD_setWidth,
        decide_eq_true hi, Bool.true_and, ha]
      by_cases hin : i < n
      · simp [hin]
      · simp [hin]
  have hbody2 : (if a.msb = true then (~~~a).clz else a.clz) = x.clz := by
    cases ha : a.msb <;> simp [x, ha]
  rw [hbody, hbody2]
  change (BitVec.setWidth w x).clz - 1#w - BitVec.ofNat w (w - n) = BitVec.setWidth w (x.clz - 1#n)
  have hclz := congrArg (· - 1#w) (opWp_clz_widened hn hnw x)
  have hassoc : (BitVec.setWidth w x).clz - 1#w - BitVec.ofNat w (w - n) =
      (BitVec.setWidth w x).clz - BitVec.ofNat w (w - n) - 1#w := by
    rw [BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.add_assoc,
      BitVec.add_comm (-1#w), ← BitVec.add_assoc, BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg]
  rw [hassoc, hclz]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_setWidth, BitVec.toNat_setWidth, BitVec.toNat_sub]
  have h1w : (1#w).toNat = 1 := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h1n : (1#n).toNat = 1 := by
    by_cases hn1 : n = 1
    · subst hn1; decide
    · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by
        have : 2 ^ 1 ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) (by omega)
        omega)]
  rw [h1w]
  have hclzw : x.clz.toNat < 2 ^ w := Nat.lt_of_lt_of_le (Nat.lt_of_le_of_lt hclz_le hnn2) hp
  rw [Nat.mod_eq_of_lt hclzw]
  have hsubw : (2 ^ w - 1 + x.clz.toNat) % 2 ^ w = x.clz.toNat - 1 := by
    have h : 2 ^ w - 1 + x.clz.toNat = 2 ^ w + (x.clz.toNat - 1) := by omega
    rw [h, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
  rw [hsubw]
  by_cases hn1 : n = 1
  · subst hn1
    have hx1 : x.clz.toNat = 1 := by omega
    simp [hx1]
  · have h2n : 1 < 2 ^ n := by
      have : 2 ^ 1 ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) (by omega); omega
    rw [h1n]
    have hsubn : (2 ^ n - 1 + x.clz.toNat) % 2 ^ n = x.clz.toNat - 1 := by
      have h : 2 ^ n - 1 + x.clz.toNat = 2 ^ n + (x.clz.toNat - 1) := by omega
      rw [h, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
    rw [hsubn, Nat.mod_eq_of_lt (by omega)]

theorem opWp_rbit_widened {n w : Nat} (_hn : 0 < n) (hnw : n < w) (a : BitVec n) :
    (BitVec.setWidth w a).reverse >>> (w - n) = BitVec.setWidth w a.reverse := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_reverse, BitVec.getLsbD_setWidth]
  by_cases hin : i < n
  · have hsum : w - n + i < w := by omega
    rw [BitVec.getMsbD_eq_getLsbD, decide_eq_true hsum, Bool.true_and, BitVec.getLsbD_setWidth]
    have hidx : w - 1 - (w - n + i) = n - 1 - i := by omega
    rw [hidx, decide_eq_true (by omega), Bool.true_and,
      BitVec.getLsbD_reverse, BitVec.getMsbD_eq_getLsbD, decide_eq_true hi, Bool.true_and,
      decide_eq_true hin, Bool.true_and]
  · have hge : n ≤ i := Nat.le_of_not_lt hin
    have hsum : ¬ (w - n + i < w) := by omega
    simp only [BitVec.getLsbD_reverse, BitVec.getMsbD_eq_getLsbD, decide_eq_true hi,
      decide_eq_false hin, decide_eq_false hsum, Bool.true_and, Bool.false_and]

theorem opWp_ctz_widened {n w : Nat} (hn : 0 < n) (hnw : n < w) (a : BitVec n) :
    ((BitVec.setWidth w a ||| BitVec.ofNat w (2 ^ n)).reverse).clz = BitVec.setWidth w a.reverse.clz := by
  have hnw2 : w < 2 ^ w := Nat.lt_two_pow_self
  have hnn2 : n < 2 ^ n := Nat.lt_two_pow_self
  have hpnw : 2 ^ n < 2 ^ w := Nat.pow_lt_pow_right (by omega) hnw
  let x' : BitVec w := BitVec.setWidth w a ||| BitVec.ofNat w (2 ^ n)
  let r' : BitVec w := x'.reverse
  have hr'_eq : r' = (BitVec.setWidth w (a.reverse ++ 1#1)) <<< (w - 1 - n) := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [r', x', BitVec.getLsbD_reverse, BitVec.getMsbD_eq_getLsbD, decide_eq_true hi, Bool.true_and,
      BitVec.getLsbD_or, BitVec.getLsbD_setWidth, BitVec.getLsbD_shiftLeft]
    by_cases hilt : i < w - 1 - n
    · have hgt : w - 1 - i > n := by omega
      have hnot_lt_n : ¬ (w - 1 - i < n) := by omega
      have hne_n : w - 1 - i ≠ n := by omega
      have hpow_bit : (BitVec.ofNat w (2 ^ n)).getLsbD (w - 1 - i) = false := by
        rw [BitVec.getLsbD_ofNat]
        simp [Ne.symm hne_n]
      simp [hilt, hpow_bit, BitVec.getLsbD_of_ge a _ (Nat.le_of_not_lt hnot_lt_n)]
    · by_cases hieq : i = w - 1 - n
      · subst hieq
        have hwn : w - 1 - (w - 1 - n) = n := by omega
        have hpow_bit : (BitVec.ofNat w (2 ^ n)).getLsbD n = true := by
          rw [BitVec.getLsbD_ofNat]
          simp [hnw]
        have hlt_sub : ¬ (w - 1 - n < w - 1 - n) := Nat.lt_irrefl _
        simp only [hwn, hpow_bit, Bool.or_true, hlt_sub,
          Bool.true_and, Nat.sub_self, decide_eq_true (show 0 < w by omega)]
        rw [BitVec.getLsbD_append]
        simp
      · have hgt : w - 1 - n < i := by omega
        have hlt_n : w - 1 - i < n := by omega
        have hne_n : w - 1 - i ≠ n := by omega
        have hpow_bit : (BitVec.ofNat w (2 ^ n)).getLsbD (w - 1 - i) = false := by
          rw [BitVec.getLsbD_ofNat]
          simp [Ne.symm hne_n]
        have hnot_lt : ¬ (i < w - 1 - n) := by omega
        have hisub_lt : i - (w - 1 - n) < n + 1 := by omega
        have hisub_w : i - (w - 1 - n) < w := by omega
        simp only [hnot_lt, decide_eq_true (show w - 1 - i < w by omega),
          Bool.true_and, hpow_bit, Bool.or_false, decide_eq_true hisub_w]
        rw [BitVec.getLsbD_append]
        have hpos : ¬ (i - (w - 1 - n) < 1) := by omega
        simp only [hpos, ↓reduceIte, BitVec.getLsbD_reverse, BitVec.getMsbD_eq_getLsbD]
        have hlt1 : i - (w - 1 - n) - 1 < n := by omega
        have heq_idx : n - 1 - (i - (w - 1 - n) - 1) = w - 1 - i := by omega
        simp [hlt1, heq_idx]
  have hr'_ne : r' ≠ 0 := by
    intro h0
    have hbit := congrArg (fun z : BitVec w => z.getLsbD (w - 1 - n)) h0
    rw [hr'_eq, BitVec.getLsbD_shiftLeft] at hbit
    have hsub : ¬ (w - 1 - n < w - 1 - n) := Nat.lt_irrefl _
    have hwn : w - 1 - n < w := by omega
    simp only [BitVec.getLsbD_setWidth, hsub, decide_eq_true hwn,
      Bool.true_and, Nat.sub_self, decide_eq_true (show 0 < w by omega)] at hbit
    rw [BitVec.getLsbD_append] at hbit
    simp at hbit
  have hrev_toNat : r'.toNat = (2 * a.reverse.toNat + 1) * 2 ^ (w - 1 - n) := by
    rw [hr'_eq]
    have happ_lt : (a.reverse ++ 1#1).toNat < 2 ^ (n + 1) := (a.reverse ++ 1#1).isLt
    have h2n1 : 2 ^ (n + 1) ≤ 2 ^ w := Nat.pow_le_pow_right (by omega) hnw
    have hsw : (BitVec.setWidth w (a.reverse ++ 1#1)).toNat = (a.reverse ++ 1#1).toNat := by
      rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le happ_lt h2n1)]
    have hprod_lt : (a.reverse ++ 1#1).toNat * 2 ^ (w - 1 - n) < 2 ^ w := by
      have hp1 : 2 ^ (n + 1) * 2 ^ (w - 1 - n) = 2 ^ w := by
        rw [← Nat.pow_add, show n + 1 + (w - 1 - n) = w by omega]
      calc (a.reverse ++ 1#1).toNat * 2 ^ (w - 1 - n)
          < 2 ^ (n + 1) * 2 ^ (w - 1 - n) := Nat.mul_lt_mul_of_pos_right happ_lt (Nat.pow_pos (by omega))
        _ = 2 ^ w := hp1
    have hshift : (BitVec.setWidth w (a.reverse ++ 1#1) <<< (w - 1 - n)).toNat =
        (a.reverse ++ 1#1).toNat * 2 ^ (w - 1 - n) := by
      rw [BitVec.toNat_shiftLeft, hsw, Nat.shiftLeft_eq, Nat.mod_eq_of_lt hprod_lt]
    have happ_val : (a.reverse ++ 1#1).toNat = 2 * a.reverse.toNat + 1 := by
      rw [BitVec.toNat_append]
      change (a.reverse.toNat <<< 1 ||| (1#1).toNat) = 2 * a.reverse.toNat + 1
      have h1 : (1#1).toNat = 1 := rfl
      rw [h1, Nat.shiftLeft_eq, Nat.pow_one]
      have hor : ∀ m, (m * 2) ||| 1 = 2 * m + 1 := by
        intro m; rw [Nat.mul_comm m 2]
        apply Nat.eq_of_testBit_eq; intro k
        cases k with
        | zero => simp [Nat.testBit_zero, Nat.add_mod]
        | succ k' =>
          have h1' : (2 * m).testBit (k' + 1) = m.testBit k' := by
            rw [← Nat.testBit_div_two, show (2 * m) / 2 = m by omega]
          have h2' : (2 * m + 1).testBit (k' + 1) = m.testBit k' := by
            rw [← Nat.testBit_div_two, show (2 * m + 1) / 2 = m by omega]
          have h3' : (1 : Nat).testBit (k' + 1) = false := by
            rw [Nat.testBit, Nat.shiftRight_eq_div_pow,
              Nat.div_eq_of_lt (Nat.one_lt_pow (Nat.succ_ne_zero _) (by omega))]; rfl
          simp [Nat.testBit_or, h1', h2', h3']
      exact hor a.reverse.toNat
    rw [hshift, happ_val]
  have hr'_ne' : ((BitVec.setWidth w a ||| BitVec.ofNat w (2 ^ n)).reverse) ≠ 0 := hr'_ne
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_clz, BitVec.toNat_clz]
  change (if r' = 0 then w else w - (r'.toNat.log2 + 1)) = _
  rw [ite_eq_right (fun h => absurd h hr'_ne)]
  by_cases ha0 : a.reverse = 0
  · simp only [ha0, ↓reduceIte]
    have hrev_0 : (0 : BitVec n).toNat = 0 := rfl
    rw [ha0] at hrev_toNat; simp only [hrev_0, Nat.mul_zero, Nat.zero_add, Nat.one_mul] at hrev_toNat
    have hlog : r'.toNat.log2 = w - 1 - n := by
      rw [hrev_toNat, Nat.log2_two_pow]
    rw [hlog, show w - (w - 1 - n + 1) = n by omega,
      Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hnn2 (Nat.le_of_lt hpnw))]
  · simp only [ha0, ↓reduceIte]
    have ha0nat : a.reverse.toNat ≠ 0 := fun h => ha0 (BitVec.eq_of_toNat_eq h)
    let l := a.reverse.toNat.log2
    have hl_lt : l < n := (Nat.log2_lt ha0nat).mpr a.reverse.isLt
    have hpow_le : 2 ^ l ≤ a.reverse.toNat := (Nat.le_log2 ha0nat).mp (Nat.le_refl l)
    have hpow_lt : a.reverse.toNat < 2 ^ (l + 1) := (Nat.log2_lt ha0nat).mp (Nat.lt_succ_self l)
    have hr0 : r'.toNat ≠ 0 := fun h => hr'_ne (BitVec.eq_of_toNat_eq h)
    have hlog_eq : r'.toNat.log2 = w - n + l := by
      apply Nat.le_antisymm
      · apply Nat.lt_succ_iff.mp
        rw [Nat.log2_lt hr0, hrev_toNat]
        calc (2 * a.reverse.toNat + 1) * 2 ^ (w - 1 - n)
            < (2 * a.reverse.toNat + 2) * 2 ^ (w - 1 - n) := by
              exact Nat.mul_lt_mul_of_pos_right (by omega) (Nat.pow_pos (by omega))
          _ ≤ (2 * 2 ^ (l + 1)) * 2 ^ (w - 1 - n) := by
              apply Nat.mul_le_mul_right; omega
          _ = 2 ^ (w - n + l + 1) := by
              rw [Nat.mul_comm 2 (2 ^ (l + 1)), ← Nat.pow_succ, ← Nat.pow_add]
              congr 1; omega
      · rw [Nat.le_log2 hr0, hrev_toNat]
        have hp : 2 ^ (w - n + l) = (2 * 2 ^ l) * 2 ^ (w - 1 - n) := by
          rw [Nat.mul_comm 2 (2 ^ l), ← Nat.pow_succ, ← Nat.pow_add]
          congr 1; omega
        rw [hp]
        exact Nat.mul_le_mul_right _ (by omega)
    rw [hlog_eq, show w - (w - n + l + 1) = n - (l + 1) by omega,
      Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (by omega) (Nat.le_of_lt hpnw))]

theorem opWp_popcnt_widened {n w : Nat} (hnw : n ≤ w) (a : BitVec n) :
    (BitVec.setWidth w a).cpop = BitVec.setWidth w a.cpop := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_cpop, BitVec.toNat_setWidth, BitVec.toNat_cpop]
  have hrec_eq : ∀ k acc, k ≤ n →
      (BitVec.setWidth w a).cpopNatRec k acc = a.cpopNatRec k acc := by
    intro k
    induction k with
    | zero => intro acc _; rfl
    | succ k' ih =>
      intro acc hk
      change (BitVec.setWidth w a).cpopNatRec k' (acc + ((BitVec.setWidth w a).getLsbD k').toNat) =
        a.cpopNatRec k' (acc + (a.getLsbD k').toNat)
      rw [BitVec.getLsbD_setWidth, decide_eq_true (Nat.lt_of_lt_of_le hk hnw), Bool.true_and, ih _ (Nat.le_of_lt hk)]
  have hrec_hi : ∀ k acc, n ≤ k → k ≤ w →
      (BitVec.setWidth w a).cpopNatRec k acc = (BitVec.setWidth w a).cpopNatRec n acc := by
    intro k
    induction k with
    | zero => intro acc hn0 _; simp [Nat.le_zero.mp hn0]
    | succ k' ih =>
      intro acc hnk hkw
      by_cases hne : n = k' + 1
      · subst hne; rfl
      · have hle : n ≤ k' := by omega
        change (BitVec.setWidth w a).cpopNatRec k' (acc + ((BitVec.setWidth w a).getLsbD k').toNat) = _
        have hzero : (BitVec.setWidth w a).getLsbD k' = false := by
          rw [BitVec.getLsbD_setWidth, Bool.and_eq_false_iff]
          right; exact BitVec.getLsbD_of_ge a k' hle
        rw [hzero]; exact ih acc hle (Nat.le_of_lt hkw)
  have hrec_le : ∀ k acc, a.cpopNatRec k acc ≤ acc + k := by
    intro k; induction k with
    | zero => intro acc; simp [BitVec.cpopNatRec]
    | succ k' ih =>
      intro acc
      change a.cpopNatRec k' (acc + (a.getLsbD k').toNat) ≤ acc + (k' + 1)
      have := ih (acc + (a.getLsbD k').toNat)
      have h1 : (a.getLsbD k').toNat ≤ 1 := by cases a.getLsbD k' <;> simp
      omega
  rw [hrec_hi w 0 hnw (Nat.le_refl w), hrec_eq n 0 (Nat.le_refl n)]
  have hle : a.cpopNatRec n 0 ≤ n := by simpa using hrec_le n 0
  by_cases hn0 : n = 0
  · subst hn0; simp [BitVec.cpopNatRec]
  · have hn2 : n < 2 ^ n := Nat.lt_two_pow_self
    have hp : 2 ^ n ≤ 2 ^ w := Nat.pow_le_pow_right (by omega) hnw
    exact (Nat.mod_eq_of_lt (by omega)).symm

theorem opWp_signExtend_toInt {n w : Nat} (hnw : n ≤ w) (a : BitVec n) :
    (BitVec.signExtend w a).toInt = a.toInt := by
  rw [BitVec.toInt_signExtend, Nat.min_eq_right hnw, ← BitVec.toInt_ofInt (n := n) a.toInt, BitVec.ofInt_toInt]

private theorem opWp_ofInt_toInt_eq_setWidth {n w : Nat} (hnw : n ≤ w) (x : BitVec w) :
    BitVec.ofInt n x.toInt = BitVec.setWidth n x := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofInt, BitVec.toNat_setWidth, BitVec.toInt_eq_toNat_cond]
  have hdvd : ((2 ^ n : Nat) : Int) ∣ ((2 ^ w : Nat) : Int) := Int.ofNat_dvd.mpr (Nat.pow_dvd_pow 2 hnw)
  split
  · rw [← Int.natCast_emod, Int.toNat_natCast]
  · have hmod : ((x.toNat : Int) - ((2 ^ w : Nat) : Int)) % ((2 ^ n : Nat) : Int) =
        (x.toNat : Int) % ((2 ^ n : Nat) : Int) := by
      rw [Int.sub_emod, Int.emod_eq_zero_of_dvd hdvd, Int.sub_zero, Int.emod_emod]
    rw [hmod, ← Int.natCast_emod, Int.toNat_natCast]

private theorem opWp_ofInt_bmod_eq {n w : Nat} (hnw : n ≤ w) (k : Int) :
    BitVec.ofInt n (k.bmod (2 ^ w)) = BitVec.ofInt n k := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofInt, BitVec.toNat_ofInt]
  have hdvd : ((2 ^ n : Nat) : Int) ∣ ((2 ^ w : Nat) : Int) := Int.ofNat_dvd.mpr (Nat.pow_dvd_pow 2 hnw)
  have hmod : (k.bmod (2 ^ w)) % ((2 ^ n : Nat) : Int) = k % ((2 ^ n : Nat) : Int) := by
    unfold Int.bmod; dsimp only
    split
    · exact Int.emod_emod_of_dvd k hdvd
    · rw [Int.sub_emod, Int.emod_eq_zero_of_dvd hdvd, Int.sub_zero, Int.emod_emod,
        Int.emod_emod_of_dvd k hdvd]
  rw [hmod]

theorem opWp_sdiv_widened {n w : Nat} (hnw : n ≤ w) (a b : BitVec n) :
    BitVec.setWidth n (BitVec.sdiv (BitVec.signExtend w a) (BitVec.signExtend w b)) = BitVec.sdiv a b := by
  rw [← opWp_ofInt_toInt_eq_setWidth hnw, BitVec.toInt_sdiv,
    opWp_signExtend_toInt hnw a, opWp_signExtend_toInt hnw b,
    opWp_ofInt_bmod_eq hnw, ← opWp_ofInt_bmod_eq (n := n) (w := n) (Nat.le_refl n),
    ← BitVec.toInt_sdiv, BitVec.ofInt_toInt]

theorem opWp_srem_widened {n w : Nat} (hnw : n ≤ w) (a b : BitVec n) :
    BitVec.setWidth n (BitVec.srem (BitVec.signExtend w a) (BitVec.signExtend w b)) = BitVec.srem a b := by
  rw [← opWp_ofInt_toInt_eq_setWidth hnw, BitVec.toInt_srem,
    opWp_signExtend_toInt hnw a, opWp_signExtend_toInt hnw b,
    ← BitVec.toInt_srem, BitVec.ofInt_toInt]

theorem opWp_sdivDefined_widened {n w : Nat} (hn : 0 < n) (hnw : n < w)
    {a b : BitVec n} (hb : b ≠ 0) :
    sdivDefined (BitVec.signExtend w a) (BitVec.signExtend w b) = true := by
  unfold sdivDefined
  simp only [Bool.and_eq_true, bne_iff_ne, Bool.not_eq_true']
  have hsbn : (BitVec.signExtend w b).toInt = b.toInt := opWp_signExtend_toInt (Nat.le_of_lt hnw) b
  have hbint : b.toInt ≠ 0 := by
    intro h
    apply hb
    have := congrArg (BitVec.ofInt n) h
    simpa [BitVec.ofInt_toInt] using this
  have hsbne : BitVec.signExtend w b ≠ 0 := fun h => hbint (by rw [← hsbn, h]; exact BitVec.toInt_zero)
  refine ⟨hsbne, ?_⟩
  rw [Bool.eq_false_iff]
  intro hboth
  simp only [Bool.and_eq_true, beq_iff_eq] at hboth
  have hsaint : (BitVec.signExtend w a).toInt = (BitVec.intMin w).toInt := by
    rw [hboth.1]
  rw [opWp_signExtend_toInt (Nat.le_of_lt hnw) a, BitVec.toInt_intMin] at hsaint
  have hlt := @BitVec.le_toInt n a
  have hnw2 : w < 2 ^ w := Nat.lt_two_pow_self
  have hpw : 2 ^ (w - 1) < 2 ^ w := Nat.pow_lt_pow_right (by omega) (by omega)
  have hpn : 2 ^ (n - 1) < 2 ^ (w - 1) := Nat.pow_lt_pow_right (by omega) (by omega)
  rw [Nat.mod_eq_of_lt hpw] at hsaint
  rw [show (2 ^ (n - 1) : Int) = ((2 ^ (n - 1) : Nat) : Int) from (Int.natCast_pow 2 (n - 1)).symm] at hlt
  omega

theorem opWp_addc_widened {n w : Nat} (hn : 0 < n) (hnw : n < w) (a b : BitVec n) (c : Bool) :
    let sw := BitVec.setWidth w a + BitVec.setWidth w b + BitVec.ofNat w c.toNat
    BitVec.setWidth n sw = a + b + BitVec.ofNat n c.toNat ∧
    BitVec.ule (1#w <<< n) sw = decide (2 ^ n ≤ a.toNat + b.toNat + c.toNat) := by
  have hp1 : 2 ^ (n + 1) ≤ 2 ^ w := Nat.pow_le_pow_right (by omega) hnw
  have hpn : 2 ^ n < 2 ^ w := Nat.pow_lt_pow_right (by omega) hnw
  have hac : a.toNat < 2 ^ n := a.isLt
  have hbc : b.toNat < 2 ^ n := b.isLt
  have hcc : c.toNat ≤ 1 := by cases c <;> simp
  have hab_lt : a.toNat + b.toNat < 2 ^ w := by omega
  have hsum_lt : a.toNat + b.toNat + c.toNat < 2 ^ w := by
    have : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [Nat.pow_succ, Nat.mul_comm]
    omega
  have hsa : (BitVec.setWidth w a).toNat = a.toNat := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans hac hpn)]
  have hsb : (BitVec.setWidth w b).toNat = b.toNat := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans hbc hpn)]
  have hsc : (BitVec.ofNat w c.toNat).toNat = c.toNat := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hsw_toNat : (BitVec.setWidth w a + BitVec.setWidth w b + BitVec.ofNat w c.toNat).toNat =
      a.toNat + b.toNat + c.toNat := by
    rw [BitVec.toNat_add, BitVec.toNat_add, hsa, hsb, hsc,
      Nat.mod_eq_of_lt hab_lt, Nat.mod_eq_of_lt hsum_lt]
  refine ⟨?_, ?_⟩
  · apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, hsw_toNat, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat]
    have hcmod : c.toNat % 2 ^ n = c.toNat := Nat.mod_eq_of_lt (by
      have : 1 < 2 ^ n := Nat.one_lt_pow (Nat.ne_of_gt hn) (by omega)
      omega)
    rw [hcmod, Nat.mod_add_mod]
  · change decide ((1#w <<< n).toNat ≤ (BitVec.setWidth w a + BitVec.setWidth w b + BitVec.ofNat w c.toNat).toNat) = _
    rw [hsw_toNat, BitVec.toNat_shiftLeft, show (1#w).toNat = 1 by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)],
      Nat.shiftLeft_eq, Nat.one_mul, Nat.mod_eq_of_lt hpn]

theorem opWp_subb_widened {n w : Nat} (hn : 0 < n) (hnw : n < w) (a b : BitVec n) (c : Bool) :
    let dw := BitVec.setWidth w a - BitVec.setWidth w b - BitVec.ofNat w c.toNat
    BitVec.setWidth n dw = a - b - BitVec.ofNat n c.toNat ∧
    decide ((BitVec.setWidth w a).toNat < (BitVec.setWidth w b).toNat + c.toNat) =
      decide (a.toNat < b.toNat + c.toNat) := by
  have hpn : 2 ^ n < 2 ^ w := Nat.pow_lt_pow_right (by omega) hnw
  have hsa : (BitVec.setWidth w a).toNat = a.toNat := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans a.isLt hpn)]
  have hsb : (BitVec.setWidth w b).toNat = b.toNat := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans b.isLt hpn)]
  refine ⟨?_, by rw [hsa, hsb]⟩
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_sub, hsa, hsb,
    BitVec.toNat_sub, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have hcc : c.toNat ≤ 1 := by cases c <;> simp
  have hc_w : c.toNat % 2 ^ w = c.toNat := Nat.mod_eq_of_lt (by omega)
  have hc_n : c.toNat % 2 ^ n = c.toNat := Nat.mod_eq_of_lt (by
    have : 1 < 2 ^ n := Nat.one_lt_pow (Nat.ne_of_gt hn) (by omega)
    omega)
  rw [hc_w, hc_n]
  have hdvd : 2 ^ n ∣ 2 ^ w := Nat.pow_dvd_pow 2 (Nat.le_of_lt hnw)
  rw [Nat.mod_mod_of_dvd _ hdvd]
  have hmod1 : (2 ^ w - c.toNat + (2 ^ w - b.toNat + a.toNat) % 2 ^ w) % 2 ^ n =
      (2 ^ w - c.toNat + (2 ^ w - b.toNat + a.toNat)) % 2 ^ n := by
    rw [Nat.add_mod, Nat.mod_mod_of_dvd _ hdvd, ← Nat.add_mod]
  rw [hmod1]
  have h1 : 2 ^ w - c.toNat + (2 ^ w - b.toNat + a.toNat) =
      (2 ^ w - 2 ^ n) + (2 ^ w - 2 ^ n) + (2 ^ n - c.toNat + (2 ^ n - b.toNat + a.toNat)) := by
    have ha := a.isLt; have hb := b.isLt; omega
  rw [h1]
  rcases hdvd with ⟨k, hk⟩
  have hk0 : 0 < k := by
    rcases k with _ | k'
    · simp at hk
    · exact Nat.succ_pos k'
  have hsub_eq : 2 ^ w - 2 ^ n = 2 ^ n * (k - 1) := by
    rw [hk, Nat.mul_sub_left_distrib, Nat.mul_one]
  rw [hsub_eq, ← Nat.mul_add, Nat.mul_add_mod]
  conv => rhs; rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]

theorem opWp_umulw_widened {n w : Nat} (_hn : 0 < n) (hnw : n < w) (a b : BitVec n) :
    let loW := BitVec.setWidth w a * BitVec.setWidth w b
    let hiW := BitVec.ofNat w ((BitVec.setWidth w a).toNat * (BitVec.setWidth w b).toNat / 2 ^ w)
    BitVec.setWidth n loW = a * b ∧
    BitVec.setWidth n ((loW >>> n) ||| (hiW <<< (w - n))) =
      BitVec.ofNat n (a.toNat * b.toNat / 2 ^ n) := by
  have hpn : 2 ^ n < 2 ^ w := Nat.pow_lt_pow_right (by omega) hnw
  have hsa : (BitVec.setWidth w a).toNat = a.toNat := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans a.isLt hpn)]
  have hsb : (BitVec.setWidth w b).toNat = b.toNat := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans b.isLt hpn)]
  let P := a.toNat * b.toNat
  have hP_lt_2n : P < 2 ^ (n + n) := by
    have : 2 ^ (n + n) = 2 ^ n * 2 ^ n := Nat.pow_add 2 n n
    rw [this]; exact Nat.mul_lt_mul'' a.isLt b.isLt
  have hP_lt_2w : P < 2 ^ (w + w) := Nat.lt_of_lt_of_le hP_lt_2n (Nat.pow_le_pow_right (by omega) (by omega))
  refine ⟨?_, ?_⟩
  · apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.toNat_mul, hsa, hsb, BitVec.toNat_mul]
    exact Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (Nat.le_of_lt hnw))
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [BitVec.getLsbD_setWidth, decide_eq_true hi, Bool.true_and,
      BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft]
    have hlo_eq : BitVec.setWidth w a * BitVec.setWidth w b = BitVec.ofNat w P := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_mul, hsa, hsb, BitVec.toNat_ofNat]
    have hhi_eq : BitVec.ofNat w ((BitVec.setWidth w a).toNat * (BitVec.setWidth w b).toNat / 2 ^ w) =
        BitVec.ofNat w (P / 2 ^ w) := by
      rw [hsa, hsb]
    rw [hlo_eq, hhi_eq]
    have hlo_bit : ∀ j, j < w → (BitVec.ofNat w P).getLsbD j = P.testBit j := by
      intro j hj; rw [BitVec.getLsbD_ofNat, decide_eq_true hj, Bool.true_and]
    have hhi_bit : ∀ j, j < w → (BitVec.ofNat w (P / 2 ^ w)).getLsbD j = P.testBit (w + j) := by
      intro j hj
      rw [BitVec.getLsbD_ofNat, decide_eq_true hj, Bool.true_and,
        ← Nat.shiftRight_eq_div_pow, Nat.testBit_shiftRight, Nat.add_comm w j]
    have hrhs_bit : (BitVec.ofNat n (a.toNat * b.toNat / 2 ^ n)).getLsbD i = P.testBit (n + i) := by
      rw [BitVec.getLsbD_ofNat, decide_eq_true hi, Bool.true_and,
        ← Nat.shiftRight_eq_div_pow, Nat.testBit_shiftRight, Nat.add_comm n i]
    rw [hrhs_bit]
    by_cases hiw : i < w - n
    · have hni : n + i < w := by omega
      have hfalse1 : ¬ (w - n ≤ i) := by omega
      simp [hlo_bit _ hni, hfalse1]
    · have hni_ge : w ≤ n + i := by omega
      have hsub_lt : i - (w - n) < w := by omega
      have hiw_lt : i < w := by omega
      have hl_ge : (BitVec.ofNat w P).getLsbD (n + i) = false := BitVec.getLsbD_of_ge (BitVec.ofNat w P) (n + i) hni_ge
      simp only [hl_ge, Bool.false_or, decide_eq_false hiw, Bool.not_false, decide_eq_true hiw_lt, Bool.true_and,
        hhi_bit _ hsub_lt]
      have hidx : w + (i - (w - n)) = n + i := by omega
      rw [hidx]

private theorem opWp_ofInt_setWidth {m k : Nat} (hmk : m ≤ k) (z : Int) :
    BitVec.setWidth m (BitVec.ofInt k z) = BitVec.ofInt m z := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofInt, BitVec.toNat_ofInt]
  have hdvd : ((2 ^ m : Nat) : Int) ∣ ((2 ^ k : Nat) : Int) := Int.ofNat_dvd.mpr (Nat.pow_dvd_pow 2 hmk)
  have hnonneg1 : (0 : Int) ≤ z % ((2 ^ k : Nat) : Int) :=
    Int.emod_nonneg z (Int.natCast_ne_zero.mpr (Nat.ne_of_gt (Nat.pow_pos (by omega))))
  have hnonneg2 : (0 : Int) ≤ z % ((2 ^ m : Nat) : Int) :=
    Int.emod_nonneg z (Int.natCast_ne_zero.mpr (Nat.ne_of_gt (Nat.pow_pos (by omega))))
  have hmod_int : z % ((2 ^ k : Nat) : Int) % ((2 ^ m : Nat) : Int) = z % ((2 ^ m : Nat) : Int) :=
    Int.emod_emod_of_dvd z hdvd
  have := congrArg Int.toNat hmod_int
  rw [Int.toNat_emod hnonneg1 (Int.natCast_nonneg _)] at this
  exact this

theorem opWp_smulw_widened {n w : Nat} (hn : 0 < n) (hnw : n < w) (a b : BitVec n) :
    let sa := BitVec.signExtend w a
    let sb := BitVec.signExtend w b
    let loW := sa * sb
    let hiW := BitVec.extractLsb' w w (BitVec.ofInt (w + w) (sa.toInt * sb.toInt))
    BitVec.setWidth n loW = a * b ∧
    BitVec.setWidth n ((loW >>> n) ||| (hiW <<< (w - n))) =
      BitVec.extractLsb' n n (BitVec.ofInt (n + n) (a.toInt * b.toInt)) := by
  have hsa : (BitVec.signExtend w a).toInt = a.toInt := opWp_signExtend_toInt (Nat.le_of_lt hnw) a
  have hsb : (BitVec.signExtend w b).toInt = b.toInt := opWp_signExtend_toInt (Nat.le_of_lt hnw) b
  let P : Int := a.toInt * b.toInt
  let vW := BitVec.ofInt (w + w) P
  let vN := BitVec.ofInt (n + n) P
  have hvw_n : BitVec.setWidth (n + n) vW = vN := opWp_ofInt_setWidth (by omega) P
  have hmul_toInt : ∀ (k : Nat) (x y : BitVec k), x * y = BitVec.ofInt k (x.toInt * y.toInt) := by
    intro k x y
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_mul, BitVec.toNat_ofInt]
    have hkx : x.toInt % ((2 ^ k : Nat) : Int) = (x.toNat : Int) % ((2 ^ k : Nat) : Int) := by
      rw [BitVec.toInt_eq_toNat_cond x]
      split <;> simp
    have hky : y.toInt % ((2 ^ k : Nat) : Int) = (y.toNat : Int) % ((2 ^ k : Nat) : Int) := by
      rw [BitVec.toInt_eq_toNat_cond y]
      split <;> simp
    have hmul_mod : (x.toInt * y.toInt) % ((2 ^ k : Nat) : Int) =
        ((x.toNat * y.toNat : Nat) : Int) % ((2 ^ k : Nat) : Int) := by
      rw [Int.mul_emod, hkx, hky, ← Int.mul_emod, Int.natCast_mul]
    rw [hmul_mod, ← Int.natCast_emod, Int.toNat_natCast]
  have hloW_eq : BitVec.signExtend w a * BitVec.signExtend w b = BitVec.setWidth w vW := by
    rw [hmul_toInt, hsa, hsb, opWp_ofInt_setWidth (by omega) P]
  have hloN_eq : a * b = BitVec.setWidth n vN := by
    rw [hmul_toInt, opWp_ofInt_setWidth (by omega) P]
  dsimp only; rw [hsa, hsb]
  refine ⟨?_, ?_⟩
  · rw [hloW_eq, hloN_eq, BitVec.setWidth_setWidth_of_le _ (Nat.le_of_lt hnw),
      ← hvw_n, BitVec.setWidth_setWidth_of_le _ (by omega)]
  · rw [hloW_eq]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_setWidth, decide_eq_true hi, Bool.true_and,
      BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft,
      BitVec.getLsbD_extractLsb']
    have hni2n : n + i < n + n := by omega
    have hv_bit : vW.getLsbD (n + i) = vN.getLsbD (n + i) := by
      rw [← hvw_n, BitVec.getLsbD_setWidth, decide_eq_true hni2n, Bool.true_and]
    rw [← hv_bit]
    by_cases hiw : i < w - n
    · have hni : n + i < w := by omega
      have hfalse1 : ¬ (w - n ≤ i) := by omega
      simp [hni, hfalse1]
    · have hni_ge : ¬ (n + i < w) := by omega
      have hsub_lt : i - (w - n) < w := by omega
      have hiw_lt : i < w := by omega
      simp only [decide_eq_false hni_ge, Bool.false_and, Bool.false_or,
        decide_eq_false hiw, Bool.not_false, Bool.true_and,
        decide_eq_true hiw_lt, decide_eq_true hsub_lt]
      congr 1; omega

theorem opWp_fptoui_widened {n w : Nat} (_hn : 0 < n) (hnw : n ≤ w)
    {z : Int} (hz0 : 0 ≤ z) (hzn : z < 2 ^ n) :
    BitVec.ofInt w z = BitVec.setWidth w (BitVec.ofInt n z) := by
  rw [show (2 ^ n : Int) = ((2 ^ n : Nat) : Int) from (Int.natCast_pow 2 n).symm] at hzn
  have hp : 2 ^ n ≤ 2 ^ w := Nat.pow_le_pow_right (by omega) hnw
  have hzn' : z < ((2 ^ w : Nat) : Int) := by omega
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofInt, BitVec.toNat_setWidth, BitVec.toNat_ofInt]
  have h1 : z % ((2 ^ w : Nat) : Int) = z := Int.emod_eq_of_lt hz0 hzn'
  have h2 : z % ((2 ^ n : Nat) : Int) = z := Int.emod_eq_of_lt hz0 hzn
  have h3 : z.toNat < 2 ^ w := by omega
  rw [h1, h2, Nat.mod_eq_of_lt h3]

theorem opWp_fptosi_widened {n w : Nat} (hnw : n ≤ w) (z : Int) :
    BitVec.setWidth n (BitVec.ofInt w z) = BitVec.ofInt n z :=
  opWp_ofInt_setWidth hnw z

/-! #### `legalOp_wp`: semantic preservation for all 64 `OpCode`s -/

private theorem opWp_exists_isFloatNaN : ∀ (f : Fmt), ∃ (r : BitVec f.width), isFloatNaN f r = true
  | .h => ⟨BitVec.allOnes 16, rfl⟩
  | .s => ⟨BitVec.allOnes 32, rfl⟩
  | .d => ⟨BitVec.allOnes 64, rfl⟩
  | .q => ⟨BitVec.allOnes 128, rfl⟩

private theorem opWp_floatResultWp_implies_nonempty {f : Fmt} {r : Float.Model.UnpackedFloat}
    {p : BitVec f.width → Prop} (h : floatResultWp f r p) : ∃ x, p x := by
  unfold floatResultWp at h
  split at h
  · obtain ⟨x, hx⟩ := opWp_exists_isFloatNaN f
    exact ⟨x, h x hx⟩
  · exact ⟨_, h⟩

theorem opWp_lift1_noFloat_of_treeRel1
    (f : {n : Nat} → BitVec n → BitVec n) (g : Bool → Bool) :
    ∀ (t : Ty) (x : Val t) (p : Val t → Prop),
      TreeRel1 (fun a q => q (g a)) (fun _ a q => q (f a)) (fun _ _ _ => False) t x p →
      t.hasFloat = false ∧ p (lift1 f g t x)
  | .bool, _, _, h => ⟨rfl, h⟩
  | .bits _, _, _, h => ⟨rfl, h⟩
  | .float _, _, _, h => False.elim h
  | .pair a b, x, p, h => by
    have hb : ∀ (r1 : Val a),
        TreeRel1 (fun a q => q (g a)) (fun _ a q => q (f a)) (fun _ _ _ => False) b x.2 (fun r2 => p (r1, r2)) →
        b.hasFloat = false ∧ p (r1, lift1 f g b x.2) :=
      fun r1 hr1 => opWp_lift1_noFloat_of_treeRel1 f g b x.2 (fun r2 => p (r1, r2)) hr1
    have h' : TreeRel1 (fun a q => q (g a)) (fun _ a q => q (f a)) (fun _ _ _ => False) a x.1
        (fun r1 => TreeRel1 (fun a q => q (g a)) (fun _ a q => q (f a)) (fun _ _ _ => False) b x.2 (fun r2 => p (r1, r2))) := h
    have ha := treeRel1_mono' h' hb (fun _ _ _ hpq h => hpq _ h) (fun _ _ _ _ hpq h => hpq _ h)
      (fun _ _ _ _ _ h => False.elim h)
    have ha' := opWp_lift1_noFloat_of_treeRel1 f g a x.1 (fun r1 => b.hasFloat = false ∧ p (r1, lift1 f g b x.2)) ha
    exact ⟨by simp [Ty.hasFloat, ha'.1, ha'.2.1], ha'.2.2⟩

private theorem opWp_lift2_noFloat_of_treeRel2
    (f : {n : Nat} → BitVec n → BitVec n → BitVec n) (g : Bool → Bool → Bool) :
    ∀ (t : Ty) (x y : Val t) (p : Val t → Prop),
      TreeRel2 (fun a b q => q (g a b)) (fun _ a b q => q (f a b)) (fun _ _ _ _ => False) t x y p →
      t.hasFloat = false ∧ p (lift2 f g t x y)
  | .bool, _, _, _, h => ⟨rfl, h⟩
  | .bits _, _, _, _, h => ⟨rfl, h⟩
  | .float _, _, _, _, h => False.elim h
  | .pair a b, x, y, p, h => by
    have hb : ∀ (r1 : Val a),
        TreeRel2 (fun a b q => q (g a b)) (fun _ a b q => q (f a b)) (fun _ _ _ _ => False)
          b x.2 y.2 (fun r2 => p (r1, r2)) →
        b.hasFloat = false ∧ p (r1, lift2 f g b x.2 y.2) :=
      fun r1 hr1 => opWp_lift2_noFloat_of_treeRel2 f g b x.2 y.2 (fun r2 => p (r1, r2)) hr1
    have h' : TreeRel2 (fun a b q => q (g a b)) (fun _ a b q => q (f a b)) (fun _ _ _ _ => False) a x.1 y.1
        (fun r1 => TreeRel2 (fun a b q => q (g a b)) (fun _ a b q => q (f a b)) (fun _ _ _ _ => False) b x.2 y.2 (fun r2 => p (r1, r2))) := h
    have ha := treeRel2_mono' h' hb (fun _ _ _ _ hpq h => hpq _ h) (fun _ _ _ _ _ hpq h => hpq _ h)
      (fun _ _ _ _ _ _ h => False.elim h)
    have ha' := opWp_lift2_noFloat_of_treeRel2 f g a x.1 y.1
      (fun r1 => b.hasFloat = false ∧ p (r1, lift2 f g b x.2 y.2)) ha
    exact ⟨by simp [Ty.hasFloat, ha'.1, ha'.2.1], ha'.2.2⟩

private theorem opWp_liftFloatRel1_const
    (op : Float.Model.Format → Float.Model.UnpackedFloat → Float.Model.UnpackedFloat)
    {C : Prop} : ∀ (t : Ty) (x : Val t) (q : Val t → Prop),
      liftFloatRel1 op t x (fun r => C ∧ q r) → C
  | .bool, _, _, h => False.elim h
  | .bits _, _, _, h => False.elim h
  | .float _, _, _, h => (opWp_floatResultWp_implies_nonempty h).choose_spec.1
  | .pair a b, x, q, h =>
    opWp_liftFloatRel1_const op a x.1 (fun _ => True)
      (opWp_liftFloatRel1_mono op a x.1 (fun r1 hr1 =>
        ⟨opWp_liftFloatRel1_const op b x.2 (fun r2 => q (r1, r2)) hr1, trivial⟩) h)

private theorem opWp_liftFloatRel2_const
    (op : Float.Model.Format → Float.Model.UnpackedFloat → Float.Model.UnpackedFloat → Float.Model.UnpackedFloat)
    {C : Prop} : ∀ (t : Ty) (x y : Val t) (q : Val t → Prop),
      liftFloatRel2 op t x y (fun r => C ∧ q r) → C
  | .bool, _, _, _, h => False.elim h
  | .bits _, _, _, _, h => False.elim h
  | .float _, _, _, _, h => (opWp_floatResultWp_implies_nonempty h).choose_spec.1
  | .pair a b, x, y, q, h =>
    opWp_liftFloatRel2_const op a x.1 y.1 (fun _ => True)
      (opWp_liftFloatRel2_mono op a x.1 y.1 (fun r1 hr1 =>
        ⟨opWp_liftFloatRel2_const op b x.2 y.2 (fun r2 => q (r1, r2)) hr1, trivial⟩) h)

private theorem opWp_liftFloatRel3_const
    (op : Float.Model.Format → Float.Model.UnpackedFloat → Float.Model.UnpackedFloat → Float.Model.UnpackedFloat → Float.Model.UnpackedFloat)
    {C : Prop} : ∀ (t : Ty) (x y z : Val t) (q : Val t → Prop),
      liftFloatRel3 op t x y z (fun r => C ∧ q r) → C
  | .bool, _, _, _, _, h => False.elim h
  | .bits _, _, _, _, _, h => False.elim h
  | .float _, _, _, _, _, h => (opWp_floatResultWp_implies_nonempty h).choose_spec.1
  | .pair a b, x, y, z, q, h =>
    opWp_liftFloatRel3_const op a x.1 y.1 z.1 (fun _ => True)
      (opWp_liftFloatRel3_mono op a x.1 y.1 z.1 (fun r1 hr1 =>
        ⟨opWp_liftFloatRel3_const op b x.2 y.2 z.2 (fun r2 => q (r1, r2)) hr1, trivial⟩) h)

theorem opWp_float1_isFloatTree_of_treeRel1
    (op : Float.Model.Format → Float.Model.UnpackedFloat → Float.Model.UnpackedFloat) :
    ∀ (t : Ty) (x : Val t) (p : Val t → Prop),
      TreeRel1 (fun _ _ => False) (fun _ _ _ => False)
        (fun fmt a q => floatResultWp fmt (op fmt.format (unpackFloat fmt a)) q) t x p →
      t.isFloatTree = true ∧ liftFloatRel1 op t x p
  | .bool, _, _, h => False.elim h
  | .bits _, _, _, h => False.elim h
  | .float _, _, _, h => ⟨rfl, h⟩
  | .pair a b, x, p, h => by
    have hb : ∀ (r1 : Val a),
        TreeRel1 (fun _ _ => False) (fun _ _ _ => False)
          (fun fmt a q => floatResultWp fmt (op fmt.format (unpackFloat fmt a)) q) b x.2 (fun r2 => p (r1, r2)) →
        b.isFloatTree = true ∧ liftFloatRel1 op b x.2 (fun r2 => p (r1, r2)) :=
      fun r1 hr1 => opWp_float1_isFloatTree_of_treeRel1 op b x.2 (fun r2 => p (r1, r2)) hr1
    have h' : TreeRel1 (fun _ _ => False) (fun _ _ _ => False)
        (fun fmt a q => floatResultWp fmt (op fmt.format (unpackFloat fmt a)) q) a x.1
        (fun r1 => TreeRel1 (fun _ _ => False) (fun _ _ _ => False)
          (fun fmt a q => floatResultWp fmt (op fmt.format (unpackFloat fmt a)) q) b x.2 (fun r2 => p (r1, r2))) := h
    have ha := treeRel1_mono' h' hb (fun _ _ _ _ h => False.elim h) (fun _ _ _ _ _ h => False.elim h)
      (fun fmt _ _ _ hpq hf => opWp_floatResultWp_mono fmt _ hpq hf)
    have ha' := opWp_float1_isFloatTree_of_treeRel1 op a x.1
      (fun r1 => b.isFloatTree = true ∧ liftFloatRel1 op b x.2 (fun r2 => p (r1, r2))) ha
    have hbf : b.isFloatTree = true := opWp_liftFloatRel1_const op a x.1 _ ha'.2
    exact ⟨by simp [Ty.isFloatTree, ha'.1, hbf],
      opWp_liftFloatRel1_mono op a x.1 (fun _ hr => hr.2) ha'.2⟩

private theorem opWp_float2_isFloatTree_of_treeRel2
    (op : Float.Model.Format → Float.Model.UnpackedFloat → Float.Model.UnpackedFloat → Float.Model.UnpackedFloat) :
    ∀ (t : Ty) (x y : Val t) (p : Val t → Prop),
      TreeRel2 (fun _ _ _ => False) (fun _ _ _ _ => False)
        (fun fmt a b q => floatResultWp fmt (op fmt.format (unpackFloat fmt a) (unpackFloat fmt b)) q) t x y p →
      t.isFloatTree = true ∧ liftFloatRel2 op t x y p
  | .bool, _, _, _, h => False.elim h
  | .bits _, _, _, _, h => False.elim h
  | .float _, _, _, _, h => ⟨rfl, h⟩
  | .pair a b, x, y, p, h => by
    have hb : ∀ (r1 : Val a),
        TreeRel2 (fun _ _ _ => False) (fun _ _ _ _ => False)
          (fun fmt a b q => floatResultWp fmt (op fmt.format (unpackFloat fmt a) (unpackFloat fmt b)) q)
          b x.2 y.2 (fun r2 => p (r1, r2)) →
        b.isFloatTree = true ∧ liftFloatRel2 op b x.2 y.2 (fun r2 => p (r1, r2)) :=
      fun r1 hr1 => opWp_float2_isFloatTree_of_treeRel2 op b x.2 y.2 (fun r2 => p (r1, r2)) hr1
    have h' : TreeRel2 (fun _ _ _ => False) (fun _ _ _ _ => False)
        (fun fmt a b q => floatResultWp fmt (op fmt.format (unpackFloat fmt a) (unpackFloat fmt b)) q) a x.1 y.1
        (fun r1 => TreeRel2 (fun _ _ _ => False) (fun _ _ _ _ => False)
          (fun fmt a b q => floatResultWp fmt (op fmt.format (unpackFloat fmt a) (unpackFloat fmt b)) q) b x.2 y.2 (fun r2 => p (r1, r2))) := h
    have ha := treeRel2_mono' h' hb (fun _ _ _ _ _ h => False.elim h) (fun _ _ _ _ _ _ h => False.elim h)
      (fun fmt _ _ _ _ hpq hf => opWp_floatResultWp_mono fmt _ hpq hf)
    have ha' := opWp_float2_isFloatTree_of_treeRel2 op a x.1 y.1
      (fun r1 => b.isFloatTree = true ∧ liftFloatRel2 op b x.2 y.2 (fun r2 => p (r1, r2))) ha
    have hbf : b.isFloatTree = true := opWp_liftFloatRel2_const op a x.1 y.1 _ ha'.2
    exact ⟨by simp [Ty.isFloatTree, ha'.1, hbf],
      opWp_liftFloatRel2_mono op a x.1 y.1 (fun _ hr => hr.2) ha'.2⟩

theorem opWp_float3_isFloatTree_of_treeRel3
    (op : Float.Model.Format → Float.Model.UnpackedFloat → Float.Model.UnpackedFloat → Float.Model.UnpackedFloat → Float.Model.UnpackedFloat) :
    ∀ (t : Ty) (x y z : Val t) (p : Val t → Prop),
      TreeRel3 (fun _ _ _ _ => False) (fun _ _ _ _ _ => False)
        (fun fmt a b c q => floatResultWp fmt (op fmt.format (unpackFloat fmt a) (unpackFloat fmt b) (unpackFloat fmt c)) q)
        t x y z p →
      t.isFloatTree = true ∧ liftFloatRel3 op t x y z p
  | .bool, _, _, _, _, h => False.elim h
  | .bits _, _, _, _, _, h => False.elim h
  | .float _, _, _, _, _, h => ⟨rfl, h⟩
  | .pair a b, x, y, z, p, h => by
    have hb : ∀ (r1 : Val a),
        TreeRel3 (fun _ _ _ _ => False) (fun _ _ _ _ _ => False)
          (fun fmt a b c q => floatResultWp fmt (op fmt.format (unpackFloat fmt a) (unpackFloat fmt b) (unpackFloat fmt c)) q)
          b x.2 y.2 z.2 (fun r2 => p (r1, r2)) →
        b.isFloatTree = true ∧ liftFloatRel3 op b x.2 y.2 z.2 (fun r2 => p (r1, r2)) :=
      fun r1 hr1 => opWp_float3_isFloatTree_of_treeRel3 op b x.2 y.2 z.2 (fun r2 => p (r1, r2)) hr1
    have h' : TreeRel3 (fun _ _ _ _ => False) (fun _ _ _ _ _ => False)
        (fun fmt a b c q => floatResultWp fmt (op fmt.format (unpackFloat fmt a) (unpackFloat fmt b) (unpackFloat fmt c)) q) a x.1 y.1 z.1
        (fun r1 => TreeRel3 (fun _ _ _ _ => False) (fun _ _ _ _ _ => False)
          (fun fmt a b c q => floatResultWp fmt (op fmt.format (unpackFloat fmt a) (unpackFloat fmt b) (unpackFloat fmt c)) q) b x.2 y.2 z.2 (fun r2 => p (r1, r2))) := h
    have ha := treeRel3_mono' h' hb (fun _ _ _ _ _ _ h => False.elim h) (fun _ _ _ _ _ _ _ h => False.elim h)
      (fun fmt _ _ _ _ _ hpq hf => opWp_floatResultWp_mono fmt _ hpq hf)
    have ha' := opWp_float3_isFloatTree_of_treeRel3 op a x.1 y.1 z.1
      (fun r1 => b.isFloatTree = true ∧ liftFloatRel3 op b x.2 y.2 z.2 (fun r2 => p (r1, r2))) ha
    have hbf : b.isFloatTree = true := opWp_liftFloatRel3_const op a x.1 y.1 z.1 _ ha'.2
    exact ⟨by simp [Ty.isFloatTree, ha'.1, hbf],
      opWp_liftFloatRel3_mono op a x.1 y.1 z.1 (fun _ hr => hr.2) ha'.2⟩

/-! #### Modular group helpers for `legalOp_wp` -/

theorem op1_wp_eq {a : Ty} {rs : List Ty} (c : OpCode [a] rs) (x : Arg Val a) (P : Tup Val rs → Prop) :
    (op1 c x).wp P = c.wp (x.val, ()) P := rfl

theorem op2_wp_eq {a b : Ty} {rs : List Ty} (c : OpCode [a, b] rs) (x : Arg Val a) (y : Arg Val b) (P : Tup Val rs → Prop) :
    (op2 c x y).wp P = c.wp (x.val, y.val, ()) P := rfl

theorem op3_wp_eq {a b d : Ty} {rs : List Ty} (c : OpCode [a, b, d] rs) (x : Arg Val a) (y : Arg Val b) (z : Arg Val d) (P : Tup Val rs → Prop) :
    (op3 c x y z).wp P = c.wp (x.val, y.val, z.val, ()) P := rfl

theorem legalOp_intBin_wp (target : LegalTarget)
    {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {G : Ctx Val (LVar target Val)} (hG : CGoodWp target G)
    (mkCode : (u : Ty) → OpCode [u, u] [u])
    (f : {n : Nat} → BitVec n → BitVec n → BitVec n)
    (g : Bool → Bool → Bool)
    (hwp : ∀ u x y p, (mkCode u).wp (x, y, ()) p = if u.hasFloat = true then False else p (lift2 f g u x y, ()))
    (hsk : ∀ u, opShiftKind (mkCode u) = none)
    (onBool : {V : Ty → Type} → {L : List Ty → Type} → {outRs : List Ty} →
      Arg V Ty.bool → Arg V Ty.bool → (Arg V Ty.bool → Expr V L outRs) → Expr V L outRs)
    (honBool : ∀ (a' b' : Arg Val Ty.bool) (a b : Bool) (cont : Arg Val Ty.bool → Expr Val Cont rs) (m' : Mem 64),
      a'.val = a → b'.val = b → (∀ r : Arg Val Ty.bool, r.val = g a b → wp Γ Q X (cont r) m') →
      wp Γ Q X (onBool a' b' cont) m')
    (honBits : ∀ n, target.supportsTy (Ty.bits n) = true →
      ∀ (a' b' : Arg Val (Ty.bits (target.widenWidth n))) (a b : BitVec n)
        (cont : Arg Val (Ty.bits (target.widenWidth n)) → Expr Val Cont rs) (m' : Mem 64),
        a'.val = BitVec.setWidth (target.widenWidth n) a →
        b'.val = BitVec.setWidth (target.widenWidth n) b →
        (∀ r : Arg Val (Ty.bits (target.widenWidth n)),
          r.val = BitVec.setWidth (target.widenWidth n) (f a b) → wp Γ Q X (cont r) m') →
        wp Γ Q X (legalBitsArith target n (mkCode (Ty.bits n)) a' b' cont) m')
    {t : Ty} (ht : target.supportsTy t = true)
    {a₁ b₁ : Arg Val t} {a₂ b₂ : Arg (LVar target Val) t}
    (ha : ArgRel G t a₁ a₂) (hb : ArgRel G t b₁ b₂)
    {P : Tup Val [t] → Prop} {k : Tup (LVar target Val) [t] → Expr Val Cont rs} {m : Mem 64}
    (hw : (mkCode t).wp (a₁.val, b₁.val, ()) P)
    (hk : ∀ (r : Tup Val [t]) (lr : Tup (LVar target Val) [t]),
      TRel (fun t x lv => valsTup lv = encodeVal target t x) r lr → P r → wp Γ Q X (k lr) m) :
    wp Γ Q X (if t.hasFloat = true then Expr.hlt else
      legalBinTree target mkCode (fun u unif => target.vecIntOpSupported (mkCode u) u unif)
        onBool (fun n x y cont => legalBitsArith target n (mkCode (Ty.bits n)) x y cont)
        (fun _ _ _ _ => Expr.hlt) (fun _ _ => false) t (legalArg target a₂) (legalArg target b₂) none
        fun r => k (r, ())) m := by
  rw [hwp] at hw
  cases hf : t.hasFloat
  · simp only [hf, Bool.false_eq_true, ↓reduceIte] at hw ⊢
    refine legalBinTree_wp target mkCode
      (fun u unif => target.vecIntOpSupported (mkCode u) u unif)
      onBool (fun n x y cont => legalBitsArith target n (mkCode (Ty.bits n)) x y cont)
      (fun _ _ _ _ => Expr.hlt) (fun _ _ => false)
      (onB := fun a b q => q (g a b)) (onBi := fun _ a b q => q (f a b)) (onF := fun _ _ _ _ => False)
      honBool honBits (fun _ _ _ _ _ _ _ _ _ _ h => False.elim h)
      ?_ (fun u _ _ _ h => by simp [hsk] at h) (fun u _ _ _ h => by simp [hsk] at h)
      (fun _ _ _ _ hpq h => hpq _ h) (fun _ _ _ _ _ hpq h => hpq _ h) (fun _ _ _ _ _ _ h => False.elim h)
      t ht (legalArg target a₂) (legalArg target b₂) none a₁.val b₁.val
      (valsTup_legalArg target hG ha) (valsTup_legalArg target hG hb) (fun _ h => by cases h) (fun r => k (r, ())) m
      (opWp_treeRel2_lift2_noFloat f g t hf _ _ _ fun fres hfres => hk _ _ (TRel.cons hfres TRel.nil) hw)
    intro u _ _ _ _ x y p htr
    have hu := opWp_lift2_noFloat_of_treeRel2 f g u x y p htr
    rw [hwp]; simp [hu.1, hu.2]
  · simp [hf] at hw

theorem legalOp_bitwiseBin_wp (target : LegalTarget)
    {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {G : Ctx Val (LVar target Val)} (hG : CGoodWp target G)
    (mkCode : (u : Ty) → OpCode [u, u] [u])
    (f : {n : Nat} → BitVec n → BitVec n → BitVec n)
    (g : Bool → Bool → Bool)
    (hwp : ∀ u x y p, (mkCode u).wp (x, y, ()) p = p (lift2 f g u x y, ()))
    (hsk : ∀ u, opShiftKind (mkCode u) = none)
    (hcok : ∀ n, match mkCode (Ty.bits n) with
      | OpCode.and (Ty.bits _) => True | OpCode.or (Ty.bits _) => True | OpCode.xor (Ty.bits _) => True
      | _ => False)
    {t : Ty} (ht : target.supportsTy t = true)
    {a₁ b₁ : Arg Val t} {a₂ b₂ : Arg (LVar target Val) t}
    (ha : ArgRel G t a₁ a₂) (hb : ArgRel G t b₁ b₂)
    {P : Tup Val [t] → Prop} {k : Tup (LVar target Val) [t] → Expr Val Cont rs} {m : Mem 64}
    (hw : (mkCode t).wp (a₁.val, b₁.val, ()) P)
    (hk : ∀ (r : Tup Val [t]) (lr : Tup (LVar target Val) [t]),
      TRel (fun t x lv => valsTup lv = encodeVal target t x) r lr → P r → wp Γ Q X (k lr) m) :
    wp Γ Q X (legalBinTree target mkCode (fun u unif => target.vecIntOpSupported (mkCode u) u unif)
      (fun x y cont => Expr.let_ (op2 (mkCode Ty.bool) x y) fun (r, _) => cont (Arg.var r))
      (fun n x y cont => legalBitsArith target n (mkCode (Ty.bits n)) x y cont)
      (legalFloatBit2 target (fun w => mkCode (Ty.bits w)) (fun fmt => mkCode (Ty.float fmt)))
      (fun _ _ => false) t (legalArg target a₂) (legalArg target b₂) none fun r => k (r, ())) m := by
  rw [hwp] at hw
  refine legalBinTree_wp target mkCode
    (fun u unif => target.vecIntOpSupported (mkCode u) u unif)
    (fun x y cont => Expr.let_ (op2 (mkCode Ty.bool) x y) fun (r, _) => cont (Arg.var r))
    (fun n x y cont => legalBitsArith target n (mkCode (Ty.bits n)) x y cont)
    (legalFloatBit2 target (fun w => mkCode (Ty.bits w)) (fun fmt => mkCode (Ty.float fmt)))
    (fun _ _ => false)
    (onB := fun a b q => q (g a b)) (onBi := fun _ a b q => q (f a b)) (onF := fun _ a b q => q (f a b))
    ?_ ?_ ?_ ?_ (fun u _ _ _ h => by simp [hsk] at h) (fun u _ _ _ h => by simp [hsk] at h)
    (fun _ _ _ _ hpq h => hpq _ h) (fun _ _ _ _ _ hpq h => hpq _ h) (fun _ _ _ _ _ hpq h => hpq _ h)
    t ht (legalArg target a₂) (legalArg target b₂) none a₁.val b₁.val
    (valsTup_legalArg target hG ha) (valsTup_legalArg target hG hb) (fun _ h => by cases h) (fun r => k (r, ())) m
    (opWp_treeRel2_lift2 f g (fun _ a b q => q (f a b)) (fun _ _ _ _ h => h) t _ _ _
      fun fres hfres => hk _ _ (TRel.cons hfres TRel.nil) hw)
  · intro a' b' a b cont m' ha' hb' hpre
    rw [wp_let, op2_wp_eq, hwp]; exact hpre _ (by simp [lift2, ha', hb'])
  · intro n hsn a' b' a b cont m' ha' hb' hpre
    refine legalBitsArith_wp target hsn (mkCode (Ty.bits n)) ?_ a' b' a b ha' hb'
      (by dsimp only [Op.wp, vals]; rw [hwp]; simpa [lift2] using hpre)
    have h := hcok n; cases hmc : mkCode (Ty.bits n) <;> simp [hmc] at h <;> exact h
  · intro fmt _ a' b' a b cont m' ha' hb' hpre
    exact legalFloatBit2_wp target (fun w => mkCode (Ty.bits w)) (fun fmt => mkCode (Ty.float fmt))
      fmt f (fun x y post => by simp [hwp, lift2]) (fun x y post => by simp [hwp, lift2])
      a' b' a b ha' hb' hpre
  · intro u _ _ _ _ x y p htr
    rw [hwp]
    exact opWp_lift2_of_treeRel2 f g (fun _ a b q => q (f a b))
      (fun _ _ _ _ h => h) (fun _ _ _ _ _ hpq h => hpq _ h) u x y p htr

theorem legalOp_shiftBin_wp (target : LegalTarget)
    {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {G : Ctx Val (LVar target Val)} (hG : CGoodWp target G)
    (mkCode : (u : Ty) → OpCode [u, u] [u])
    (f : {n : Nat} → BitVec n → BitVec n → BitVec n)
    (hwp : ∀ u x y p, (mkCode u).wp (x, y, ()) p = if u.hasFloat = true then False else p (lift2 f (fun x _ => x) u x y, ()))
    (honBits : ∀ n, target.supportsTy (Ty.bits n) = true →
      ∀ (a' b' : Arg Val (Ty.bits (target.widenWidth n))) (a b : BitVec n)
        (cont : Arg Val (Ty.bits (target.widenWidth n)) → Expr Val Cont rs) (m' : Mem 64),
        a'.val = BitVec.setWidth (target.widenWidth n) a →
        b'.val = BitVec.setWidth (target.widenWidth n) b →
        (∀ r : Arg Val (Ty.bits (target.widenWidth n)),
          r.val = BitVec.setWidth (target.widenWidth n) (f a b) → wp Γ Q X (cont r) m') →
        wp Γ Q X (legalBitsArith target n (mkCode (Ty.bits n)) a' b' cont) m')
    (hrotl : ∀ u c w s, opShiftKind (mkCode u) = some true → uniformShiftLeaf? u c = some (w, s) →
      ∀ x : Val u, u.hasFloat = false ∧
        (if (s == 0) = true then x = lift2 f (fun x _ => x) u x c
         else lift2 (fun {n} a b => a.rotateRight (b.toNat % n)) (fun a _ => a) u x
           (splatBits w (BitVec.ofNat w (w - s)) u) = lift2 f (fun x _ => x) u x c))
    (hshl : ∀ u c w s, opShiftKind (mkCode u) = some false → uniformShiftLeaf? u c = some (w, s) →
      ∀ x : Val u, u.hasFloat = false ∧
        (if (s == 0) = true then x = lift2 f (fun x _ => x) u x c
         else lift2 (fun {_n} a b => a &&& b) (fun a b => a && b) u
           (lift2 (fun {n} a b => a.rotateRight (b.toNat % n)) (fun a _ => a) u x
             (splatBits w (BitVec.ofNat w (w - s)) u))
           (splatBits w (BitVec.allOnes w <<< s) u) = lift2 f (fun x _ => x) u x c))
    {isUnif : (u : Ty) → Arg (LVar target Val) u → Bool}
    {t : Ty} (ht : target.supportsTy t = true)
    {a₁ b₁ : Arg Val t} {a₂ b₂ : Arg (LVar target Val) t}
    (ha : ArgRel G t a₁ a₂) (hb : ArgRel G t b₁ b₂)
    {P : Tup Val [t] → Prop} {k : Tup (LVar target Val) [t] → Expr Val Cont rs} {m : Mem 64}
    (hw : (mkCode t).wp (a₁.val, b₁.val, ()) P)
    (hk : ∀ (r : Tup Val [t]) (lr : Tup (LVar target Val) [t]),
      TRel (fun t x lv => valsTup lv = encodeVal target t x) r lr → P r → wp Γ Q X (k lr) m) :
    wp Γ Q X (if t.hasFloat = true then Expr.hlt else
      legalBinTree target mkCode (fun u unif => target.vecIntOpSupported (mkCode u) u unif)
        (fun x _ cont => cont x) (fun n x y cont => legalBitsArith target n (mkCode (Ty.bits n)) x y cont)
        (fun _ _ _ _ => Expr.hlt)
        isUnif
        t (legalArg target a₂) (legalArg target b₂) (some b₂) fun r => k (r, ())) m := by
  rw [hwp] at hw
  cases hf : t.hasFloat
  · simp only [hf, Bool.false_eq_true, ↓reduceIte] at hw ⊢
    refine legalBinTree_wp target mkCode
      (fun u unif => target.vecIntOpSupported (mkCode u) u unif)
      (fun x _ cont => cont x) (fun n x y cont => legalBitsArith target n (mkCode (Ty.bits n)) x y cont)
      (fun _ _ _ _ => Expr.hlt)
      isUnif
      (onB := fun a _ q => q a) (onBi := fun _ a b q => q (f a b)) (onF := fun _ _ _ _ => False)
      ?_ honBits (fun _ _ _ _ _ _ _ _ _ _ h => False.elim h)
      ?_ ?_ ?_
      (fun _ _ _ _ hpq h => hpq _ h) (fun _ _ _ _ _ hpq h => hpq _ h) (fun _ _ _ _ _ _ h => False.elim h)
      t ht (legalArg target a₂) (legalArg target b₂) (some b₂) a₁.val b₁.val
      (valsTup_legalArg target hG ha) (valsTup_legalArg target hG hb)
      (fun c hc => by
        have hb2 : b₂ = Arg.imm c := Option.some.inj hc
        subst hb2
        cases hb
        rfl)
      (fun r => k (r, ())) m
      (opWp_treeRel2_lift2_noFloat f (fun x _ => x) t hf _ _ _
        fun fres hfres => hk _ _ (TRel.cons hfres TRel.nil) hw)
    · intro a' _ a _ cont m' ha' _ hpre; exact hpre a' ha'
    · intro u _ _ _ _ x y p htr
      have hu := opWp_lift2_noFloat_of_treeRel2 f (fun x _ => x) u x y p htr
      rw [hwp]; simp [hu.1, hu.2]
    · intro u c w s hsk hunif _ x p htr
      have hp := (opWp_lift2_noFloat_of_treeRel2 f (fun x _ => x) u x c p htr).2
      have hrot := hrotl u c w s hsk hunif x
      by_cases hs0 : (s == 0) = true
      · simp only [hs0, ↓reduceIte] at hrot ⊢; rw [hrot.2]; exact hp
      · simp only [hs0, Bool.false_eq_true, ↓reduceIte] at hrot ⊢
        rw [OpCode.wp_rotr]; simp only [hrot.1, Bool.false_eq_true, ↓reduceIte, hrot.2]; exact hp
    · intro u c w s hsk hunif _ x p htr
      have hp := (opWp_lift2_noFloat_of_treeRel2 f (fun x _ => x) u x c p htr).2
      have hsh := hshl u c w s hsk hunif x
      by_cases hs0 : (s == 0) = true
      · simp only [hs0, ↓reduceIte] at hsh ⊢; rw [hsh.2]; exact hp
      · simp only [hs0, Bool.false_eq_true, ↓reduceIte] at hsh ⊢
        rw [OpCode.wp_rotr]; simp only [hsh.1, Bool.false_eq_true, ↓reduceIte]
        rw [OpCode.wp_and, hsh.2]; exact hp
  · simp [hf] at hw

theorem legalOp_floatBin_wp (target : LegalTarget)
    {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {G : Ctx Val (LVar target Val)} (hG : CGoodWp target G)
    (mkCode : (u : Ty) → OpCode [u, u] [u])
    (op : Float.Model.Format → Float.Model.UnpackedFloat → Float.Model.UnpackedFloat → Float.Model.UnpackedFloat)
    (hwp : ∀ u x y p, (mkCode u).wp (x, y, ()) p =
      if (!u.isFloatTree) = true then False else liftFloatRel2 op u x y fun r => p (r, ()))
    (hsk : ∀ u, opShiftKind (mkCode u) = none)
    {t : Ty} (ht : target.supportsTy t = true)
    {a₁ b₁ : Arg Val t} {a₂ b₂ : Arg (LVar target Val) t}
    (ha : ArgRel G t a₁ a₂) (hb : ArgRel G t b₁ b₂)
    {P : Tup Val [t] → Prop} {k : Tup (LVar target Val) [t] → Expr Val Cont rs} {m : Mem 64}
    (hw : (mkCode t).wp (a₁.val, b₁.val, ()) P)
    (hk : ∀ (r : Tup Val [t]) (lr : Tup (LVar target Val) [t]),
      TRel (fun t x lv => valsTup lv = encodeVal target t x) r lr → P r → wp Γ Q X (k lr) m) :
    wp Γ Q X (if (!t.isFloatTree) = true then Expr.hlt else
      legalBinTree target mkCode (fun u _ => target.vecFloatOpSupported (mkCode u) u)
        (fun _ _ _ => Expr.hlt) (fun _ _ _ _ => Expr.hlt)
        (fun fmt x y cont => Expr.let_ (op2 (mkCode (Ty.float fmt)) x y) fun (r, _) => cont (Arg.var r))
        (fun _ _ => false) t (legalArg target a₂) (legalArg target b₂) none fun r => k (r, ())) m := by
  rw [hwp] at hw
  cases hft : t.isFloatTree
  · simp [hft] at hw
  · simp only [hft, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hw ⊢
    refine legalBinTree_wp target mkCode
      (fun u _ => target.vecFloatOpSupported (mkCode u) u)
      (fun _ _ _ => Expr.hlt) (fun _ _ _ _ => Expr.hlt)
      (fun fmt x y cont => Expr.let_ (op2 (mkCode (Ty.float fmt)) x y) fun (r, _) => cont (Arg.var r))
      (fun _ _ => false)
      (onB := fun _ _ _ => False) (onBi := fun _ _ _ _ => False)
      (onF := fun fmt a b q => floatResultWp fmt (op fmt.format (unpackFloat fmt a) (unpackFloat fmt b)) q)
      (fun _ _ _ _ _ _ _ _ h => False.elim h)
      (fun _ _ _ _ _ _ _ _ _ _ h => False.elim h)
      ?_ ?_ (fun u _ _ _ h => by simp [hsk] at h) (fun u _ _ _ h => by simp [hsk] at h)
      (fun _ _ _ _ _ h => False.elim h) (fun _ _ _ _ _ _ h => False.elim h)
      (fun fmt _ _ _ _ hpq h => opWp_floatResultWp_mono fmt _ hpq h)
      t ht (legalArg target a₂) (legalArg target b₂) none a₁.val b₁.val
      (valsTup_legalArg target hG ha) (valsTup_legalArg target hG hb) (fun _ h => by cases h) (fun r => k (r, ())) m ?_
    · intro fmt _ a' b' a b cont m' ha' hb' hpre
      rw [wp_let, op2_wp_eq, hwp]
      simp only [Ty.isFloatTree, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      change floatResultWp fmt (op fmt.format (unpackFloat fmt a'.val) (unpackFloat fmt b'.val))
        (fun r => wp Γ Q X (cont (Arg.var r)) m')
      rw [ha', hb']
      exact opWp_floatResultWp_mono fmt _ (fun res hres => hres (Arg.var res) rfl) hpre
    · intro u _ _ _ _ x y p htr
      have hu := opWp_float2_isFloatTree_of_treeRel2 op u x y p htr
      rw [hwp]; simp [hu.1, hu.2]
    · exact opWp_treeRel2_float2 op t hft a₁.val b₁.val _
        (opWp_liftFloatRel2_mono op t a₁.val b₁.val (fun r hr => fun fres hfres =>
          hk _ _ (TRel.cons hfres TRel.nil) hr) hw)

theorem op1_setWidth_self {op : {k : Nat} → BitVec k → BitVec k} {n w : Nat}
    (h : n = w) {a' : BitVec w} {a : BitVec n} (ha : a' = BitVec.setWidth w a) :
    op a' = BitVec.setWidth w (op a) := by
  subst h; rw [ha, BitVec.setWidth_eq, BitVec.setWidth_eq]

theorem op2_setWidth_self {op : {k : Nat} → BitVec k → BitVec k → BitVec k} {n w : Nat}
    (h : n = w) {a' b' : BitVec w} {a b : BitVec n}
    (ha : a' = BitVec.setWidth w a) (hb : b' = BitVec.setWidth w b) :
    op a' b' = BitVec.setWidth w (op a b) := by
  subst h; rw [ha, hb, BitVec.setWidth_eq, BitVec.setWidth_eq, BitVec.setWidth_eq]

theorem op3_setWidth_self {op : {k : Nat} → BitVec k → BitVec k → BitVec k → BitVec k} {n w : Nat}
    (h : n = w) {a' b' c' : BitVec w} {a b c : BitVec n}
    (ha : a' = BitVec.setWidth w a) (hb : b' = BitVec.setWidth w b) (hc : c' = BitVec.setWidth w c) :
    op a' b' c' = BitVec.setWidth w (op a b c) := by
  subst h; rw [ha, hb, hc, BitVec.setWidth_eq, BitVec.setWidth_eq, BitVec.setWidth_eq, BitVec.setWidth_eq]

theorem op2_pred_self {P : {k : Nat} → BitVec k → BitVec k → Prop} {n w : Nat}
    (h : n = w) {a' b' : BitVec w} {a b : BitVec n}
    (ha : a' = BitVec.setWidth w a) (hb : b' = BitVec.setWidth w b) :
    P a b → P a' b' := by
  subst h; rw [ha, hb, BitVec.setWidth_eq, BitVec.setWidth_eq]; exact id

theorem opWp_words64_two (ws : List (Arg Val i64)) (v : BitVec 128)
    (hbits : ∀ i < 128, words64GetLsb ws i = v.getLsbD i) (hlen : ws.length = 2) :
    (ws.getD 0 (Arg.imm 0#64)).val = BitVec.extractLsb' 0 64 v ∧
    (ws.getD 1 (Arg.imm 0#64)).val = BitVec.extractLsb' 64 64 v := by
  rcases ws with _ | ⟨w0, _ | ⟨w1, _ | _⟩⟩ <;> simp at hlen
  constructor <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi
  · rw [BitVec.getLsbD_extractLsb', decide_eq_true hi, Bool.true_and, Nat.zero_add, ← hbits i (by omega)]
    simp only [words64GetLsb, Nat.div_eq_of_lt hi, Nat.mod_eq_of_lt hi]
  · rw [BitVec.getLsbD_extractLsb', decide_eq_true hi, Bool.true_and, ← hbits (64 + i) (by omega)]
    simp only [words64GetLsb, show (64 + i) / 64 = 1 by omega, show (64 + i) % 64 = i by omega]

theorem dite_true_wp {α : Sort _} {P : α → Prop} {c : Prop} [Decidable c]
    {t : c → α} {e : ¬ c → α} (hc : c) (ht : P (t hc)) : P (dite c t e) := by
  rw [dite_eq_left hc]; exact ht

theorem dite_false_wp {α : Sort _} {P : α → Prop} {c : Prop} [Decidable c]
    {t : c → α} {e : ¬ c → α} (hc : ¬ c) (he : P (e hc)) : P (dite c t e) := by
  rw [dite_eq_right hc]; exact he

def isNatTy (target : LegalTarget) : Ty → Bool
  | .bits n => target.isLegalTy (.bits n) && (target.widenWidth n == n)
  | t => target.isLegalTy t


end LegalWp

end LeanQbe.T
