module

public import LeanQbe.T.Legal
public import LeanQbe.T.LegalEmit
public import LeanQbe.T.WPLemmas
public import LeanQbe.T.FlatLemmas

/-!
# Correctness and legality proofs for `LeanQbe.T.Legal` (`T5`, `G13`)

Proves the three main theorems for `Func.legal` using `Wf.induct`:

* `Func.legal_wf`: well-formedness preservation (`f.Wf → (f.legal target).Wf`).
* `Func.legal_wp` / `Func.legal_spec`: semantic weakest-precondition preservation
  (`Func.wp Γ f xs m Q X → Func.wp (legalEnv target Γ) (f.legal target) (encodeTup target as xs) m
  (legalPost target Q) (legalXPost target X)`).
* `Func.legal_isLegal` (in `LeanQbe.T.LegalCheck3`, split across `LegalCheck1`–`LegalCheck3`):
  computable target legality (`f.Wf → f.supportsSource target = true → (f.legal target).isLegal
  target = true`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T

/-! ## Section 1: Target capability, `minGe` / `widenWidth`, and `chunkBytes` lemmas -/

theorem minGe_mem {n w : Nat} : ∀ {ws : List Nat}, minGe n ws = some w → w ∈ ws
  | [], h => by simp [minGe] at h
  | x :: ws, h => by
    simp only [minGe] at h
    cases hrec : minGe n ws with
    | none =>
      rw [hrec] at h
      by_cases hnx : n ≤ x
      · simp only [hnx, ↓reduceIte, Option.some.injEq] at h
        subst h; exact List.mem_cons_self
      · simp [hnx] at h
    | some best =>
      rw [hrec] at h
      by_cases hc : (n ≤ x && x < best) = true
      · simp only [hc, ↓reduceIte, Option.some.injEq] at h
        subst h; exact List.mem_cons_self
      · simp only [hc, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at h
        subst h; exact List.mem_cons_of_mem _ (minGe_mem hrec)

theorem minGe_le {n w : Nat} : ∀ {ws : List Nat}, minGe n ws = some w → n ≤ w
  | [], h => by simp [minGe] at h
  | x :: ws, h => by
    simp only [minGe] at h
    cases hrec : minGe n ws with
    | none =>
      rw [hrec] at h
      by_cases hnx : n ≤ x
      · simp only [hnx, ↓reduceIte, Option.some.injEq] at h
        subst h; exact hnx
      · simp [hnx] at h
    | some best =>
      rw [hrec] at h
      by_cases hc : (decide (n ≤ x) && decide (x < best)) = true
      · simp only [hc, ↓reduceIte, Option.some.injEq] at h
        subst h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
        exact hc.1
      · simp only [hc, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at h
        subst h; exact minGe_le hrec

private theorem minGe_none_not_le {n : Nat} :
    ∀ {ws : List Nat}, minGe n ws = none → ∀ z ∈ ws, ¬ n ≤ z
  | [], _, _, hz, _ => by cases hz
  | u :: us, h0, z, hz, hnz => by
    simp only [minGe] at h0
    cases hu : minGe n us with
    | none =>
      rw [hu] at h0
      by_cases hnu : n ≤ u
      · simp [hnu] at h0
      · rcases List.mem_cons.1 hz with rfl | hz'
        · exact hnu hnz
        · exact minGe_none_not_le hu z hz' hnz
    | some b =>
      rw [hu] at h0
      by_cases hc : (decide (n ≤ u) && decide (u < b)) = true <;> simp [hc] at h0

theorem minGe_le_of_mem {n w x : Nat} :
    ∀ {ws : List Nat}, x ∈ ws → n ≤ x → minGe n ws = some w → w ≤ x
  | [], hx, _, _ => by cases hx
  | y :: ws, hx, hnx, hw => by
    simp only [minGe] at hw
    cases hrec : minGe n ws with
    | none =>
      rw [hrec] at hw
      rcases List.mem_cons.1 hx with rfl | hx'
      · simp only [hnx, ↓reduceIte, Option.some.injEq] at hw
        subst hw; exact Nat.le_refl _
      · exact absurd hnx (minGe_none_not_le hrec x hx')
    | some best =>
      rw [hrec] at hw
      by_cases hc : (decide (n ≤ y) && decide (y < best)) = true
      · simp only [hc, ↓reduceIte, Option.some.injEq] at hw
        subst hw
        have hlt := of_decide_eq_true (Bool.and_eq_true _ _ |>.mp hc).2
        rcases List.mem_cons.1 hx with rfl | hx'
        · exact Nat.le_refl _
        · exact Nat.le_of_lt (Nat.lt_of_lt_of_le hlt (minGe_le_of_mem hx' hnx hrec))
      · simp only [hc, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hw
        subst hw
        rcases List.mem_cons.1 hx with rfl | hx'
        · exact Nat.le_of_not_lt fun hlt =>
            hc (Bool.and_eq_true _ _ |>.mpr ⟨decide_eq_true hnx, decide_eq_true hlt⟩)
        · exact minGe_le_of_mem hx' hnx hrec

theorem minGe_isSome_of_exists {n : Nat} :
    ∀ {ws : List Nat}, (∃ x ∈ ws, n ≤ x) → (minGe n ws).isSome = true
  | [], ⟨_, hx, _⟩ => by cases hx
  | y :: ws, ⟨x, hx, hnx⟩ => by
    simp only [minGe]
    cases hrec : minGe n ws with
    | none =>
      rcases List.mem_cons.1 hx with rfl | hx'
      · simp [hnx]
      · exact absurd hnx (minGe_none_not_le hrec x hx')
    | some best =>
      by_cases hc : (decide (n ≤ y) && decide (y < best)) = true <;> simp [hc]

theorem widenWidth_mem_of_exists (target : LegalTarget) {n : Nat}
    (h : ∃ w ∈ target.bitWidths, n ≤ w) : target.widenWidth n ∈ target.bitWidths := by
  have hs := minGe_isSome_of_exists h
  rcases Option.isSome_iff_exists.1 hs with ⟨w, hw⟩
  simpa [LegalTarget.widenWidth, hw] using minGe_mem hw

theorem le_widenWidth_of_exists (target : LegalTarget) {n : Nat}
    (h : ∃ w ∈ target.bitWidths, n ≤ w) : n ≤ target.widenWidth n := by
  have hs := minGe_isSome_of_exists h
  rcases Option.isSome_iff_exists.1 hs with ⟨w, hw⟩
  simpa [LegalTarget.widenWidth, hw] using minGe_le hw

theorem widenWidth_eq_self_of_mem (target : LegalTarget) {n : Nat}
    (h : n ∈ target.bitWidths) : target.widenWidth n = n := by
  have hs := minGe_isSome_of_exists ⟨n, h, Nat.le_refl n⟩
  rcases Option.isSome_iff_exists.1 hs with ⟨w, hw⟩
  have h1 := minGe_le hw
  have h2 := minGe_le_of_mem h (Nat.le_refl n) hw
  have heq : w = n := Nat.le_antisymm h2 h1
  simpa [LegalTarget.widenWidth, hw] using heq

theorem widenWidth_mono (target : LegalTarget) {m n : Nat}
    (hmn : m ≤ n) (hn : ∃ w ∈ target.bitWidths, n ≤ w) :
    target.widenWidth m ≤ target.widenWidth n := by
  rcases Option.isSome_iff_exists.1 (minGe_isSome_of_exists hn) with ⟨wn, hwn⟩
  have hwn_mem := minGe_mem hwn
  have hwn_le := minGe_le hwn
  have hm_exists : ∃ w ∈ target.bitWidths, m ≤ w := ⟨wn, hwn_mem, Nat.le_trans hmn hwn_le⟩
  rcases Option.isSome_iff_exists.1 (minGe_isSome_of_exists hm_exists) with ⟨wm, hwm⟩
  have hwm_le := minGe_le_of_mem hwn_mem (Nat.le_trans hmn hwn_le) hwm
  simpa [LegalTarget.widenWidth, hwm, hwn] using hwm_le

theorem valid_mem8 {target : LegalTarget} (hv : target.valid = true) : 8 ∈ target.bitWidths := by
  simp only [LegalTarget.valid, Bool.and_eq_true] at hv
  simpa using hv.1.1.1

theorem valid_mem64 {target : LegalTarget} (hv : target.valid = true) : 64 ∈ target.bitWidths := by
  simp only [LegalTarget.valid, Bool.and_eq_true] at hv
  simpa using hv.1.1.2

theorem valid_bitWidth_spec {target : LegalTarget} (hv : target.valid = true) {w : Nat}
    (hw : w ∈ target.bitWidths) : 0 < w ∧ w % 8 = 0 ∧ w ≤ 64 := by
  simp only [LegalTarget.valid, Bool.and_eq_true, List.all_eq_true] at hv
  have h := hv.1.2 w hw
  simp only [beq_iff_eq, decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem valid_float_spec {target : LegalTarget} (hv : target.valid = true) {f : Fmt}
    (hf : f ∈ target.floatFmts) : f.width ∈ target.bitWidths ∧ f.width ≤ 64 := by
  simp only [LegalTarget.valid, Bool.and_eq_true, List.all_eq_true] at hv
  have h := hv.2 f hf
  simpa [Bool.and_eq_true] using h

theorem valid_widenWidth_64 {target : LegalTarget} (hv : target.valid = true) :
    target.widenWidth 64 = 64 :=
  widenWidth_eq_self_of_mem target (valid_mem64 hv)

theorem supportsTy_bits_iff {target : LegalTarget} {n : Nat} :
    target.supportsTy (.bits n) = true ↔ (∃ w ∈ target.bitWidths, n ≤ w) ∧ n ≤ 64 := by
  simp [LegalTarget.supportsTy, Bool.and_eq_true, List.any_eq_true]

theorem widenWidth_mem_of_supports {target : LegalTarget} {n : Nat}
    (h : target.supportsTy (.bits n) = true) : target.widenWidth n ∈ target.bitWidths :=
  widenWidth_mem_of_exists target (supportsTy_bits_iff.1 h).1

theorem le_widenWidth_of_supports {target : LegalTarget} {n : Nat}
    (h : target.supportsTy (.bits n) = true) : n ≤ target.widenWidth n :=
  le_widenWidth_of_exists target (supportsTy_bits_iff.1 h).1

theorem widenWidth_le_64_of_supports {target : LegalTarget} (hv : target.valid = true) {n : Nat}
    (h : target.supportsTy (.bits n) = true) : target.widenWidth n ≤ 64 :=
  (valid_bitWidth_spec hv (widenWidth_mem_of_supports h)).2.2

theorem isLegalTy_legalTys {target : LegalTarget} (hv : target.valid = true) :
    ∀ {t : Ty}, target.supportsTy t = true → ∀ u ∈ target.legalTys t, target.isLegalTy u = true
  | .bool, _, u, hu => by
    simp only [LegalTarget.legalTys, List.mem_singleton] at hu
    subst hu; rfl
  | .bits n, ht, u, hu => by
    simp only [LegalTarget.legalTys, List.mem_singleton] at hu
    subst hu
    simp only [LegalTarget.isLegalTy, decide_eq_true_eq]
    exact widenWidth_mem_of_supports ht
  | .float f, ht, u, hu => by
    simp only [LegalTarget.legalTys, List.mem_singleton] at hu
    subst hu
    simp only [LegalTarget.supportsTy, Bool.and_eq_true] at ht
    simpa [LegalTarget.isLegalTy] using ht.1
  | .pair a b, ht, u, hu => by
    simp only [LegalTarget.supportsTy, Bool.and_eq_true] at ht
    simp only [LegalTarget.legalTys] at hu
    split at hu
    · next hp =>
      simp only [List.mem_singleton] at hu
      subst hu; exact hp
    · rcases List.mem_append.1 hu with hu' | hu'
      · exact isLegalTy_legalTys hv ht.1 u hu'
      · exact isLegalTy_legalTys hv ht.2 u hu'

theorem isLegalSig_legalSig {target : LegalTarget} (hv : target.valid = true) :
    ∀ {ts : List Ty}, ts.all target.supportsTy = true →
      target.isLegalSig (target.legalSig ts) = true
  | [], _ => rfl
  | t :: ts, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    simp only [LegalTarget.legalSig, LegalTarget.isLegalSig, List.all_append, Bool.and_eq_true]
    exact ⟨List.all_eq_true.2 fun u hu => isLegalTy_legalTys hv h.1 u hu,
      by simpa [LegalTarget.isLegalSig] using isLegalSig_legalSig hv h.2⟩

theorem isLegalTy_leafTys {target : LegalTarget} (hv : target.valid = true) :
    ∀ {t : Ty}, target.supportsTy t = true → ∀ u ∈ target.leafTys t, target.isLegalTy u = true
  | .bool, _, u, hu => by simp only [LegalTarget.leafTys, List.mem_singleton] at hu; subst hu; rfl
  | .bits n, ht, u, hu => by
    simp only [LegalTarget.leafTys, List.mem_singleton] at hu; subst hu
    simpa [LegalTarget.isLegalTy] using widenWidth_mem_of_supports ht
  | .float f, ht, u, hu => by
    simp only [LegalTarget.leafTys, List.mem_singleton] at hu; subst hu
    simp only [LegalTarget.supportsTy, Bool.and_eq_true] at ht
    simpa [LegalTarget.isLegalTy] using ht.1
  | .pair a b, ht, u, hu => by
    simp only [LegalTarget.supportsTy, Bool.and_eq_true] at ht
    rcases List.mem_append.1 (by simpa [LegalTarget.leafTys] using hu) with hu' | hu'
    · exact isLegalTy_leafTys hv ht.1 u hu'
    · exact isLegalTy_leafTys hv ht.2 u hu'

theorem hasLegalLeaves_of_keepsPacked {target : LegalTarget} {a b : Ty}
    (h : target.keepsPacked (.pair a b) = true) : target.hasLegalLeaves (.pair a b) = true := by
  simp only [LegalTarget.keepsPacked, Bool.and_eq_true] at h
  exact h.2

theorem isLegalTy_of_hasLegalLeaves {target : LegalTarget} :
    ∀ {t u : Ty}, target.hasLegalLeaves t = true → u ∈ target.leafTys t → target.isLegalTy u = true
  | .bool, u, _, hu => by simp only [LegalTarget.leafTys, List.mem_singleton] at hu; subst hu; rfl
  | .bits n, u, hl, hu => by
    simp only [LegalTarget.leafTys, List.mem_singleton] at hu; subst hu
    have hmem : n ∈ target.bitWidths := by simpa [LegalTarget.hasLegalLeaves] using hl
    simpa [LegalTarget.isLegalTy, widenWidth_eq_self_of_mem target hmem] using hmem
  | .float f, u, hl, hu => by
    simp only [LegalTarget.leafTys, List.mem_singleton] at hu; subst hu
    simpa [LegalTarget.isLegalTy, LegalTarget.hasLegalLeaves] using hl
  | .pair a b, u, hl, hu => by
    simp only [LegalTarget.hasLegalLeaves, Bool.and_eq_true] at hl
    rcases List.mem_append.1 (by simpa [LegalTarget.leafTys] using hu) with hu' | hu'
    · exact isLegalTy_of_hasLegalLeaves hl.1 hu'
    · exact isLegalTy_of_hasLegalLeaves hl.2 hu'

theorem widenWidth_eq_self_of_hasLegalLeaves {target : LegalTarget} {n : Nat}
    (h : target.hasLegalLeaves (.bits n) = true) : target.widenWidth n = n :=
  widenWidth_eq_self_of_mem target (by simpa [LegalTarget.hasLegalLeaves] using h)

private theorem maxByteChunk_pos_mem :
    ∀ (b : Nat) (ws : List Nat), 0 < maxByteChunk b ws →
      maxByteChunk b ws ≤ b ∧ 8 * maxByteChunk b ws ∈ ws
  | _, [], hw => by simp [maxByteChunk] at hw
  | b, u :: us, hw => by
    simp only [maxByteChunk] at hw
    by_cases hc : (u % 8 == 0 && 0 < u && u / 8 ≤ b && maxByteChunk b us < u / 8) = true
    · simp only [maxByteChunk, hc, ↓reduceIte]
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
      refine ⟨hc.1.2, ?_⟩
      rw [show 8 * (u / 8) = u by omega]
      exact List.mem_cons_self
    · simp only [maxByteChunk, hc, Bool.false_eq_true, ↓reduceIte]
      simp only [hc, Bool.false_eq_true, ↓reduceIte] at hw
      obtain ⟨h1, h2⟩ := maxByteChunk_pos_mem b us hw
      exact ⟨h1, List.mem_cons_of_mem _ h2⟩

theorem maxByteChunk_spec (b : Nat) (hb : 0 < b) :
    ∀ {ws : List Nat}, 8 ∈ ws →
      0 < maxByteChunk b ws ∧ maxByteChunk b ws ≤ b ∧ 8 * maxByteChunk b ws ∈ ws
  | [], h8 => by cases h8
  | w :: ws, h8 => by
    simp only [maxByteChunk]
    rcases List.mem_cons.1 h8 with rfl | h8'
    · have hb1 : 1 ≤ b := hb
      by_cases hm : maxByteChunk b ws < 1
      · have hcond : (8 % 8 == 0 && 0 < 8 && 8 / 8 ≤ b && maxByteChunk b ws < 8 / 8) = true := by
          simp [hb1, hm]
        simp only [hcond, ↓reduceIte]
        refine ⟨by omega, by omega, ?_⟩
        rw [show 8 * (8 / 8) = 8 by omega]
        exact List.mem_cons_self
      · have hbest_pos : 0 < maxByteChunk b ws := by omega
        have hcond : (8 % 8 == 0 && 0 < 8 && 8 / 8 ≤ b && maxByteChunk b ws < 8 / 8) = false := by
          simp [hm]
        simp only [hcond, Bool.false_eq_true, ↓reduceIte]
        obtain ⟨hl, hmem⟩ := maxByteChunk_pos_mem b ws hbest_pos
        exact ⟨hbest_pos, hl, List.mem_cons_of_mem _ hmem⟩
    · obtain ⟨hp, hl, hm⟩ := maxByteChunk_spec b hb h8'
      by_cases hc : (w % 8 == 0 && 0 < w && w / 8 ≤ b && maxByteChunk b ws < w / 8) = true
      · simp only [hc, ↓reduceIte]
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
        refine ⟨by omega, hc.1.2, ?_⟩
        rw [show 8 * (w / 8) = w by omega]
        exact List.mem_cons_self
      · simp only [hc, Bool.false_eq_true, ↓reduceIte]
        exact ⟨hp, hl, List.mem_cons_of_mem _ hm⟩

theorem chunkBytes_pos_mem_sum (ws : List Nat) (h8 : 8 ∈ ws) :
    ∀ b : Nat, (∀ c ∈ chunkBytes ws b, 0 < c ∧ 8 * c ∈ ws) ∧ (chunkBytes ws b).sum = b
  | 0 => by simp [chunkBytes]
  | b' + 1 => by
    obtain ⟨hc_pos, hc_le, hc_mem⟩ := maxByteChunk_spec (b' + 1) (Nat.succ_pos _) h8
    have ih := chunkBytes_pos_mem_sum ws h8 (b' + 1 - maxByteChunk (b' + 1) ws)
    have hcond : (0 < maxByteChunk (b' + 1) ws ∧ maxByteChunk (b' + 1) ws ≤ b' + 1) :=
      ⟨hc_pos, hc_le⟩
    have hdef : chunkBytes ws (b' + 1) =
        maxByteChunk (b' + 1) ws :: chunkBytes ws (b' + 1 - maxByteChunk (b' + 1) ws) := by
      simp [chunkBytes, hcond]
    rw [hdef]
    refine ⟨?_, ?_⟩
    · intro c hc
      rcases List.mem_cons.1 hc with rfl | hc'
      · exact ⟨hc_pos, hc_mem⟩
      · exact ih.1 c hc'
    · simp only [List.sum_cons, ih.2]; omega
termination_by b => b

/-! ## Section 2: Tuple, list relation, encoding, and cast lemmas -/

def leafVals (target : LegalTarget) : (t : Ty) → Val t → Tup Val (target.leafTys t)
  | .bool, b => (b, ())
  | .bits n, x => (x.setWidth (target.widenWidth n), ())
  | .float _, x => (x, ())
  | .pair a b, p => tupAppend (leafVals target a p.1) (leafVals target b p.2)

@[simp] theorem valsTup_nil : valsTup (ts := []) () = () := rfl

@[simp] theorem valsTup_cons {t : Ty} {ts : List Ty} (a : Arg Val t) (as : Tup (Arg Val) ts) :
    valsTup (ts := t :: ts) (a, as) = (a.val, valsTup as) := rfl

@[simp] theorem varsTup_valsTup :
    {ts : List Ty} → (xs : Tup Val ts) → valsTup (varsTup xs) = xs
  | [], () => rfl
  | _ :: _, (_, xs) => by simp [varsTup, varsTup_valsTup xs]

@[simp] theorem tupSplit_tupAppend {α : Type} {f : α → Type} :
    {as bs : List α} → (xs : Tup f as) → (ys : Tup f bs) →
      tupSplit (tupAppend xs ys) = (xs, ys)
  | [], _, (), _ => rfl
  | _ :: _, _, (x, xs), ys => by
    simp [tupAppend, tupSplit, tupSplit_tupAppend xs ys]

@[simp] theorem tupAppend_tupSplit {α : Type} {f : α → Type} :
    {as bs : List α} → (zs : Tup f (as ++ bs)) →
      tupAppend (tupSplit (as := as) (bs := bs) zs).1 (tupSplit (as := as) (bs := bs) zs).2 = zs
  | [], _, _ => rfl
  | _ :: _, _, (x, zs) => by
    simp only [tupSplit, tupAppend]
    exact congrArg (x, ·) (tupAppend_tupSplit zs)

@[simp] theorem valsTup_tupAppend :
    {as bs : List Ty} → (xs : Tup (Arg Val) as) → (ys : Tup (Arg Val) bs) →
      valsTup (tupAppend xs ys) = tupAppend (valsTup xs) (valsTup ys)
  | [], _, (), _ => rfl
  | _ :: _, _, (x, xs), ys => by
    simp only [tupAppend, valsTup_cons]
    exact congrArg (x.val, ·) (valsTup_tupAppend xs ys)

theorem valsTup_cast_eq {as bs : List Ty} (hT : Tup (Arg Val) as = Tup (Arg Val) bs)
    (hV : Tup Val as = Tup Val bs) (h : as = bs) (xs : Tup (Arg Val) as) :
    valsTup (cast hT xs) = cast hV (valsTup xs) := by
  subst h; rfl

theorem TRel_cast_eq {V₁ V₂ : Ty → Type} {R : ∀ t, Arg V₁ t → Arg V₂ t → Prop}
    {as bs : List Ty} (h₁ : Tup (Arg V₁) as = Tup (Arg V₁) bs)
      (h₂ : Tup (Arg V₂) as = Tup (Arg V₂) bs)
    (h : as = bs) {xs₁ : Tup (Arg V₁) as} {xs₂ : Tup (Arg V₂) as} (hr : TRel R xs₁ xs₂) :
    TRel R (cast h₁ xs₁) (cast h₂ xs₂) := by
  subst h; exact hr

theorem TRel_cast {V₁ V₂ : Ty → Type} {R : ∀ t, Arg V₁ t → Arg V₂ t → Prop}
    {as bs : List Ty} (h : as = bs) {xs₁ : Tup (Arg V₁) as} {xs₂ : Tup (Arg V₂) as}
    (hr : TRel R xs₁ xs₂) :
    TRel R (cast (congrArg (Tup (Arg V₁)) h) xs₁) (cast (congrArg (Tup (Arg V₂)) h) xs₂) := by
  subst h; exact hr

theorem TRel.single {V₁ V₂ : Ty → Type} {G : Ctx V₁ V₂} {t : Ty}
    {x₁ : Arg V₁ t} {x₂ : Arg V₂ t} (h : ArgRel G t x₁ x₂) :
    TRel (ArgRel G) (as := [t]) (x₁, PUnit.unit) (x₂, PUnit.unit) :=
  .cons h .nil

theorem TRel_tupAppend {α : Type} {f g : α → Type} {R : ∀ a, f a → g a → Prop} :
    {as bs : List α} → {x₁ : Tup f as} → {x₂ : Tup g as} → {y₁ : Tup f bs} → {y₂ : Tup g bs} →
      TRel R x₁ x₂ → TRel R y₁ y₂ → TRel R (tupAppend x₁ y₁) (tupAppend x₂ y₂)
  | [], _, (), (), _, _, .nil, hy => hy
  | _ :: _, _, (_, _), (_, _), _, _, .cons hx hxs, hy => .cons hx (TRel_tupAppend hxs hy)

theorem TRel_tupSplit {α : Type} {f g : α → Type} {R : ∀ a, f a → g a → Prop} :
    {as bs : List α} → {z₁ : Tup f (as ++ bs)} → {z₂ : Tup g (as ++ bs)} →
      TRel R z₁ z₂ →
      TRel R (tupSplit (as := as) (bs := bs) z₁).1 (tupSplit (as := as) (bs := bs) z₂).1 ∧
      TRel R (tupSplit (as := as) (bs := bs) z₁).2 (tupSplit (as := as) (bs := bs) z₂).2
  | [], _, _, _, hz => ⟨.nil, hz⟩
  | _ :: _, _, (_, _), (_, _), .cons hx hzs =>
    let ⟨h1, h2⟩ := TRel_tupSplit hzs
    ⟨.cons hx h1, h2⟩

theorem TRel_varsTup {V₁ V₂ : Ty → Type} {G : Ctx V₁ V₂} :
    {ts : List Ty} → {xs₁ : Tup V₁ ts} → {xs₂ : Tup V₂ ts} →
      (∀ t i, ⟨t, xs₁.get i, xs₂.get i⟩ ∈ G) →
      TRel (ArgRel G) (varsTup xs₁) (varsTup xs₂)
  | [], (), (), _ => .nil
  | _ :: _, (_, _), (_, _), h =>
    .cons (.var (h _ .here)) (TRel_varsTup (fun t i => h t (.there i)))

theorem TRel_zip_varsTup {V₁ V₂ : Ty → Type} :
    {ts : List Ty} → (xs₁ : Tup V₁ ts) → (xs₂ : Tup V₂ ts) →
      TRel (ArgRel (Tup.zip xs₁ xs₂)) (varsTup xs₁) (varsTup xs₂)
  | [], (), () => .nil
  | _ :: _, (_, _), (_, _) =>
    .cons (.var List.mem_cons_self)
      (TRel_argRel_weaken' (fun _ hm => List.mem_cons_of_mem _ hm) (TRel_zip_varsTup _ _))

@[simp] theorem valsTup_packedToTup {target : LegalTarget} {a b : Ty}
    (h : target.keepsPacked (.pair a b) = true)
    (xs : Tup (Arg Val) (target.legalTys (.pair a b))) :
    valsTup (packedToTup h xs) = cast (by simp [LegalTarget.legalTys, h]) (valsTup xs) :=
  valsTup_cast_eq _ _ (by simp [LegalTarget.legalTys, h]) xs

@[simp] theorem valsTup_tupToPacked {target : LegalTarget} {a b : Ty}
    (h : target.keepsPacked (.pair a b) = true)
    (xs : Tup (Arg Val) [.pair a b]) :
    valsTup (tupToPacked h xs) = cast (by simp [LegalTarget.legalTys, h]) (valsTup xs) :=
  valsTup_cast_eq _ _ (by simp [LegalTarget.legalTys, h]) xs

@[simp] theorem valsTup_splitToTup {target : LegalTarget} {a b : Ty}
    (h : target.keepsPacked (.pair a b) = false)
    (xs : Tup (Arg Val) (target.legalTys (.pair a b))) :
    valsTup (splitToTup h xs) = cast (by simp [LegalTarget.legalTys, h]) (valsTup xs) :=
  valsTup_cast_eq _ _ (by simp [LegalTarget.legalTys, h]) xs

@[simp] theorem valsTup_tupToSplit {target : LegalTarget} {a b : Ty}
    (h : target.keepsPacked (.pair a b) = false)
    (xs : Tup (Arg Val) (target.legalTys a ++ target.legalTys b)) :
    valsTup (tupToSplit h xs) = cast (by simp [LegalTarget.legalTys, h]) (valsTup xs) :=
  valsTup_cast_eq _ _ (by simp [LegalTarget.legalTys, h]) xs

theorem packedToTup_rel {target : LegalTarget} {V₁ V₂ : Ty → Type} {G : Ctx V₁ V₂} {a b : Ty}
    (h : target.keepsPacked (.pair a b) = true)
    {xs₁ : Tup (Arg V₁) (target.legalTys (.pair a b))}
    {xs₂ : Tup (Arg V₂) (target.legalTys (.pair a b))}
    (hr : TRel (ArgRel G) xs₁ xs₂) :
    TRel (ArgRel G) (packedToTup h xs₁) (packedToTup h xs₂) :=
  TRel_cast_eq _ _ (by simp [LegalTarget.legalTys, h]) hr

theorem tupToPacked_rel {target : LegalTarget} {V₁ V₂ : Ty → Type} {G : Ctx V₁ V₂} {a b : Ty}
    (h : target.keepsPacked (.pair a b) = true)
    {xs₁ : Tup (Arg V₁) [.pair a b]} {xs₂ : Tup (Arg V₂) [.pair a b]}
    (hr : TRel (ArgRel G) xs₁ xs₂) :
    TRel (ArgRel G) (tupToPacked h xs₁) (tupToPacked h xs₂) :=
  TRel_cast_eq _ _ (by simp [LegalTarget.legalTys, h]) hr

theorem splitToTup_rel {target : LegalTarget} {V₁ V₂ : Ty → Type} {G : Ctx V₁ V₂} {a b : Ty}
    (h : target.keepsPacked (.pair a b) = false)
    {xs₁ : Tup (Arg V₁) (target.legalTys (.pair a b))}
    {xs₂ : Tup (Arg V₂) (target.legalTys (.pair a b))}
    (hr : TRel (ArgRel G) xs₁ xs₂) :
    TRel (ArgRel G) (splitToTup h xs₁) (splitToTup h xs₂) :=
  TRel_cast_eq _ _ (by simp [LegalTarget.legalTys, h]) hr

theorem tupToSplit_rel {target : LegalTarget} {V₁ V₂ : Ty → Type} {G : Ctx V₁ V₂} {a b : Ty}
    (h : target.keepsPacked (.pair a b) = false)
    {xs₁ : Tup (Arg V₁) (target.legalTys a ++ target.legalTys b)}
    {xs₂ : Tup (Arg V₂) (target.legalTys a ++ target.legalTys b)}
    (hr : TRel (ArgRel G) xs₁ xs₂) :
    TRel (ArgRel G) (tupToSplit h xs₁) (tupToSplit h xs₂) :=
  TRel_cast_eq _ _ (by simp [LegalTarget.legalTys, h]) hr

@[simp] theorem valsTup_encodeImm (target : LegalTarget) :
    (t : Ty) → (c : Val t) → valsTup (encodeImm target t c) = encodeVal target t c
  | .bool, _ => rfl
  | .bits _, _ => rfl
  | .float _, _ => rfl
  | .pair a b, p => by
    by_cases h : target.keepsPacked (.pair a b) = true
    · simp only [encodeImm, encodeVal, h, ↓reduceDIte, valsTup_tupToPacked h]
      rfl
    · have hf : target.keepsPacked (.pair a b) = false := Bool.eq_false_iff.mpr h
      rw [encodeImm, encodeVal, dite_eq_right (fun h' => False.elim (h h')),
        dite_eq_right (fun h' => False.elim (h h')), valsTup_tupToSplit hf]
      congr 1
      rw [valsTup_tupAppend, valsTup_encodeImm target a p.1, valsTup_encodeImm target b p.2]

@[simp] theorem valsTup_leafImm (target : LegalTarget) :
    (t : Ty) → (c : Val t) → valsTup (leafImm target t c) = leafVals target t c
  | .bool, _ => rfl
  | .bits _, _ => rfl
  | .float _, _ => rfl
  | .pair a b, p => by
    rw [leafImm, leafVals]
    change valsTup (tupAppend (leafImm target a p.1) (leafImm target b p.2)) =
           tupAppend (leafVals target a p.1) (leafVals target b p.2)
    rw [valsTup_tupAppend, valsTup_leafImm target a p.1, valsTup_leafImm target b p.2]

theorem encodeImm_rel {V₁ V₂ : Ty → Type} {G : Ctx V₁ V₂} (target : LegalTarget) :
    (t : Ty) → (c : Val t) → TRel (ArgRel G) (encodeImm target t c) (encodeImm target t c)
  | .bool, c => .cons (.imm c) .nil
  | .bits _, _ => .cons (.imm _) .nil
  | .float _, c => .cons (.imm c) .nil
  | .pair a b, p => by
    by_cases h : target.keepsPacked (.pair a b) = true
    · simp only [encodeImm, h, ↓reduceDIte]
      exact tupToPacked_rel h (.cons (.imm p) .nil)
    · rw [encodeImm, dite_eq_right (fun h' => False.elim (h h')),
        encodeImm, dite_eq_right (fun h' => False.elim (h h'))]
      exact tupToSplit_rel (Bool.eq_false_iff.mpr h)
        (TRel_tupAppend (encodeImm_rel target a p.1) (encodeImm_rel target b p.2))

theorem leafImm_rel {V₁ V₂ : Ty → Type} {G : Ctx V₁ V₂} (target : LegalTarget) :
    (t : Ty) → (c : Val t) → TRel (ArgRel G) (leafImm target t c) (leafImm target t c)
  | .bool, c => .cons (.imm c) .nil
  | .bits _, _ => .cons (.imm _) .nil
  | .float _, c => .cons (.imm c) .nil
  | .pair a b, p => TRel_tupAppend (leafImm_rel target a p.1) (leafImm_rel target b p.2)

theorem Member_zip_get {α : Type} {f g : α → Type} :
    {sig : List α} → (xs₁ : Tup f sig) → (xs₂ : Tup g sig) → {ts : α} → (i : Member ts sig) →
      ⟨ts, xs₁.get i, xs₂.get i⟩ ∈ Tup.zip xs₁ xs₂
  | _ :: _, (_, _), (_, _), _, .here => List.mem_cons_self
  | _ :: _, (_, _), (_, _), _, .there i => List.mem_cons_of_mem _ (Member_zip_get _ _ i)

theorem tupLiftMap_get {α β : Type} (g : α → β) (f : β → Type) :
    {sig : List α} → (Js : Tup f (sig.map g)) → {ts : α} → (i : Member ts sig) →
      (tupLiftMap g f Js).get i = Js.get (Member.map g i)
  | _ :: _, (_, _), _, .here => rfl
  | _ :: _, (_, Js'), _, .there i => tupLiftMap_get g f Js' i

theorem castArgBits_rel {V₁ V₂ : Ty → Type} {G : Ctx V₁ V₂} {m n : Nat} (h : m = n)
    {x₁ : Arg V₁ (.bits m)} {x₂ : Arg V₂ (.bits m)} (hr : ArgRel G (.bits m) x₁ x₂) :
    ArgRel G (.bits n) (castArgBits h x₁) (castArgBits h x₂) := by
  subst h; exact hr

/-- Minimal core list pointwise relation (`ListRel`). -/
inductive ListRel {α β : Type} (R : α → β → Prop) : List α → List β → Prop
  | nil : ListRel R [] []
  | cons {a b as bs} : R a b → ListRel R as bs → ListRel R (a :: as) (b :: bs)

theorem ListRel.mono {α β : Type} {R S : α → β → Prop} (h : ∀ a b, R a b → S a b) :
    ∀ {xs : List α} {ys : List β}, ListRel R xs ys → ListRel S xs ys
  | _, _, .nil => .nil
  | _, _, .cons hx hxs => .cons (h _ _ hx) (ListRel.mono h hxs)

theorem ListRel.append {α β : Type} {R : α → β → Prop} :
    ∀ {xs₁ ys₁ : List α} {xs₂ ys₂ : List β},
      ListRel R xs₁ xs₂ → ListRel R ys₁ ys₂ → ListRel R (xs₁ ++ ys₁) (xs₂ ++ ys₂)
  | _, _, _, _, .nil, hy => hy
  | _, _, _, _, .cons hx hxs, hy => .cons hx (ListRel.append hxs hy)

theorem ListRel.getD {α β : Type} {R : α → β → Prop} {d₁ : α} {d₂ : β} (hd : R d₁ d₂) :
    ∀ {xs : List α} {ys : List β}, ListRel R xs ys → ∀ (i : Nat), R (xs.getD i d₁) (ys.getD i d₂)
  | [], [], .nil, _ => hd
  | _ :: _, _ :: _, .cons ha _, 0 => ha
  | _ :: _, _ :: _, .cons _ hs, i + 1 => ListRel.getD hd hs i

theorem ListRel.of_map {α β γ : Type} {R : β → γ → Prop} {f₁ : α → β} {f₂ : α → γ}
    (h : ∀ x, R (f₁ x) (f₂ x)) : ∀ xs : List α, ListRel R (xs.map f₁) (xs.map f₂)
  | [] => .nil
  | x :: xs => .cons (h x) (ListRel.of_map h xs)

theorem listRel_weaken {V₁ V₂ : Ty → Type} {G G' : Ctx V₁ V₂}
    (hG : ∀ p ∈ G, p ∈ G') {t : Ty} {xs₁ : List (Arg V₁ t)} {xs₂ : List (Arg V₂ t)}
    (h : ListRel (ArgRel G t) xs₁ xs₂) : ListRel (ArgRel G' t) xs₁ xs₂ :=
  h.mono fun _ _ ha => ha.weaken hG

/-! ## Section 3: Well-formedness preservation (`Func.legal_wf`) -/

section LegalWf

variable (target : LegalTarget)

/-- `CGood target G LG` holds iff every pair `⟨t, lv₁, lv₂⟩ ∈ LG` has all underlying target
operands `ArgRel G`-related. -/
def CGood {V₁ V₂ : Ty → Type} (G : Ctx V₁ V₂) (LG : Ctx (LVar target V₁) (LVar target V₂)) : Prop :=
  ∀ t lv₁ lv₂, ⟨t, lv₁, lv₂⟩ ∈ LG → TRel (ArgRel G) lv₁ lv₂

/-- `DGood target D LD` holds iff every label pair in `LD` corresponds to a legalized-signature
label pair in `D`. -/
def DGood {L₁ L₂ : List Ty → Type} (D : Ctx L₁ L₂) (LD : Ctx (LLab target L₁) (LLab target L₂)) :
  Prop :=
  ∀ ts l₁ l₂, ⟨ts, l₁, l₂⟩ ∈ LD → ⟨target.legalSig ts, l₁, l₂⟩ ∈ D

theorem CGood.weaken {V₁ V₂ : Ty → Type} {G G' : Ctx V₁ V₂}
    {LG : Ctx (LVar target V₁) (LVar target V₂)}
    (hG : ∀ p ∈ G, p ∈ G') (hc : CGood target G LG) : CGood target G' LG :=
  fun t lv₁ lv₂ hm => TRel_argRel_weaken' hG (hc t lv₁ lv₂ hm)

theorem Tup.zip_tupAppend {α : Type} {f g : α → Type} :
    {as bs : List α} → (x₁ : Tup f as) → (x₂ : Tup g as) → (y₁ : Tup f bs) → (y₂ : Tup g bs) →
      Tup.zip (tupAppend x₁ y₁) (tupAppend x₂ y₂) = Tup.zip x₁ x₂ ++ Tup.zip y₁ y₂
  | [], _, (), (), _, _ => rfl
  | _ :: _, _, (_, _), (_, _), _, _ => by
    simp only [tupAppend, Tup.zip, List.cons_append]
    exact congrArg (_ :: ·) (Tup.zip_tupAppend _ _ _ _)

theorem mem_zip_tupSplit {α : Type} {f g : α → Type} :
    {as bs : List α} → {z₁ : Tup f (as ++ bs)} → {z₂ : Tup g (as ++ bs)} →
      (∀ p ∈ Tup.zip (tupSplit z₁).1 (tupSplit z₂).1, p ∈ Tup.zip z₁ z₂) ∧
      (∀ p ∈ Tup.zip (tupSplit z₁).2 (tupSplit z₂).2, p ∈ Tup.zip z₁ z₂)
  | [], _, _, _ => ⟨(fun _ hp => by cases hp), fun _ hp => hp⟩
  | _ :: as, bs, (_, z₁'), (_, z₂') => by
    have ih := mem_zip_tupSplit (as := as) (bs := bs) (z₁ := z₁') (z₂ := z₂')
    refine ⟨?_, ?_⟩
    · intro p hp
      simp only [tupSplit, Tup.zip] at hp
      rcases List.mem_cons.1 hp with rfl | hp'
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih.1 p hp')
    · intro p hp
      exact List.mem_cons_of_mem _ (ih.2 p hp)

theorem CGood.pushSplit {V₁ V₂ : Ty → Type} {G : Ctx V₁ V₂}
    {LG : Ctx (LVar target V₁) (LVar target V₂)} (hc : CGood target G LG) :
    (ts : List Ty) → (xs₁ : Tup V₁ (target.legalSig ts)) → (xs₂ : Tup V₂ (target.legalSig ts)) →
      CGood target (Tup.zip xs₁ xs₂ ++ G)
        (Tup.zip (splitParams target ts xs₁) (splitParams target ts xs₂) ++ LG)
  | [], (), (), t, lv₁, lv₂, hm =>
    TRel_argRel_weaken' (fun _ hp => List.mem_append_right _ hp) (hc t lv₁ lv₂ hm)
  | _ :: us, xs₁, xs₂, t, lv₁, lv₂, hm => by
    simp only [splitParams, Tup.zip, List.cons_append] at hm
    rcases List.mem_cons.1 hm with hhead | htail
    · cases hhead
      have hzip : TRel (ArgRel (Tup.zip xs₁ xs₂ ++ G))
          (varsTup (tupSplit xs₁).1) (varsTup (tupSplit xs₂).1) :=
        TRel_argRel_weaken'
          (fun p hp => List.mem_append_left G (mem_zip_tupSplit.1 p hp))
          (TRel_zip_varsTup (tupSplit xs₁).1 (tupSplit xs₂).1)
      exact hzip
    · have ih := CGood.pushSplit hc us (tupSplit xs₁).2 (tupSplit xs₂).2 t lv₁ lv₂ htail
      exact TRel_argRel_weaken' (fun p hp => by
        rcases List.mem_append.1 hp with hp' | hp'
        · exact List.mem_append_left G (mem_zip_tupSplit.2 p hp')
        · exact List.mem_append_right _ hp') ih

theorem DGood.weaken {L₁ L₂ : List Ty → Type} {D D' : Ctx L₁ L₂}
    {LD : Ctx (LLab target L₁) (LLab target L₂)}
    (hD : ∀ p ∈ D, p ∈ D') (hd : DGood target D LD) : DGood target D' LD :=
  fun ts l₁ l₂ hm => hD _ (hd ts l₁ l₂ hm)

theorem DGood.pushLiftMap {L₁ L₂ : List Ty → Type} {D : Ctx L₁ L₂}
    {LD : Ctx (LLab target L₁) (LLab target L₂)} (hd : DGood target D LD) :
    {sig : List (List Ty)} → (Js₁ : Tup L₁ (sig.map target.legalSig)) →
    (Js₂ : Tup L₂ (sig.map target.legalSig)) →
      DGood target (Tup.zip Js₁ Js₂ ++ D)
        (Tup.zip (tupLiftMap target.legalSig L₁ Js₁) (tupLiftMap target.legalSig L₂ Js₂) ++ LD)
  | [], (), (), ts, l₁, l₂, hm =>
    List.mem_append_right _ (hd ts l₁ l₂ hm)
  | _ :: _, (_, Js₁'), (_, Js₂'), ts, l₁, l₂, hm => by
    simp only [tupLiftMap, Tup.zip, List.cons_append] at hm
    rcases List.mem_cons.1 hm with hhead | htail
    · cases hhead; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (DGood.pushLiftMap hd Js₁' Js₂' ts l₁ l₂ htail)

theorem legalArg_rel {V₁ V₂ : Ty → Type} {G : Ctx V₁ V₂}
    {LG : Ctx (LVar target V₁) (LVar target V₂)} (hc : CGood target G LG)
    {t : Ty} {a₁ : Arg (LVar target V₁) t} {a₂ : Arg (LVar target V₂) t}
    (ha : ArgRel LG t a₁ a₂) :
    TRel (ArgRel G) (legalArg target a₁) (legalArg target a₂) := by
  cases ha with
  | var hm => exact hc _ _ _ hm
  | imm c => exact encodeImm_rel target t c

theorem joinArgs_rel {V₁ V₂ : Ty → Type} {G : Ctx V₁ V₂}
    {LG : Ctx (LVar target V₁) (LVar target V₂)} (hc : CGood target G LG) :
    {ts : List Ty} → {as₁ : Tup (Arg (LVar target V₁)) ts} → {as₂ : Tup (Arg (LVar target V₂)) ts} →
      TRel (ArgRel LG) as₁ as₂ →
      TRel (ArgRel G) (joinArgs target as₁) (joinArgs target as₂)
  | [], (), (), .nil => .nil
  | _ :: _, (_, _), (_, _), .cons h hs =>
    TRel_tupAppend (legalArg_rel target hc h) (joinArgs_rel hc hs)

theorem Wf.let3 {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} {a b c u : Ty} (code : OpCode [a, b, c] [u])
    {x₁ : Arg V₁ a} {x₂ : Arg V₂ a} {y₁ : Arg V₁ b} {y₂ : Arg V₂ b}
    {z₁ : Arg V₁ c} {z₂ : Arg V₂ c}
    (hx : ArgRel G a x₁ x₂) (hy : ArgRel G b y₁ y₂) (hz : ArgRel G c z₁ z₂)
    {k₁ : Arg V₁ u → Expr V₁ L₁ rs} {k₂ : Arg V₂ u → Expr V₂ L₂ rs}
    (hk : ∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ r₁ r₂, ArgRel G' u r₁ r₂ → Wf G' D (k₁ r₁) (k₂ r₂)) :
    Wf G D (.let_ (op3 code x₁ y₁ z₁) fun r => k₁ (.var r.fst))
           (.let_ (op3 code x₂ y₂ z₂) fun r => k₂ (.var r.fst)) :=
  .let_ (.mk code (.cons hx (.cons hy (.cons hz .nil)))) fun r₁ r₂ =>
    hk (fun _ hp => List.mem_cons_of_mem _ hp) (.var r₁.fst) (.var r₂.fst) (.var List.mem_cons_self)

theorem Wf.let1M {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} {a u : Ty} (code : OpCode [a] [u])
    {x₁ : Arg V₁ a} {x₂ : Arg V₂ a} (hx : ArgRel G a x₁ x₂)
    {k₁ : Arg V₁ u → Expr V₁ L₁ rs} {k₂ : Arg V₂ u → Expr V₂ L₂ rs}
    (hk : ∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂, ArgRel G' u y₁ y₂ → Wf G' D (k₁ y₁) (k₂ y₂)) :
    Wf G D (.let_ (op1 code x₁) fun (r, ()) => k₁ (.var r))
           (.let_ (op1 code x₂) fun (r, ()) => k₂ (.var r)) :=
  .let_ (.mk code (.cons hx .nil)) fun (r₁, ()) (r₂, ()) =>
    hk (fun _ hp => List.mem_cons_of_mem _ hp) (.var r₁) (.var r₂) (.var List.mem_cons_self)

theorem Wf.let2M {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} {a b u : Ty} (code : OpCode [a, b] [u])
    {x₁ : Arg V₁ a} {x₂ : Arg V₂ a} {y₁ : Arg V₁ b} {y₂ : Arg V₂ b}
    (hx : ArgRel G a x₁ x₂) (hy : ArgRel G b y₁ y₂)
    {k₁ : Arg V₁ u → Expr V₁ L₁ rs} {k₂ : Arg V₂ u → Expr V₂ L₂ rs}
    (hk : ∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ r₁ r₂, ArgRel G' u r₁ r₂ → Wf G' D (k₁ r₁) (k₂ r₂)) :
    Wf G D (.let_ (op2 code x₁ y₁) fun (r, ()) => k₁ (.var r))
           (.let_ (op2 code x₂ y₂) fun (r, ()) => k₂ (.var r)) :=
  .let_ (.mk code (.cons hx (.cons hy .nil))) fun (r₁, ()) (r₂, ()) =>
    hk (fun _ hp => List.mem_cons_of_mem _ hp) (.var r₁) (.var r₂) (.var List.mem_cons_self)

theorem Wf.let3M {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} {a b c u : Ty} (code : OpCode [a, b, c] [u])
    {x₁ : Arg V₁ a} {x₂ : Arg V₂ a} {y₁ : Arg V₁ b} {y₂ : Arg V₂ b}
    {z₁ : Arg V₁ c} {z₂ : Arg V₂ c}
    (hx : ArgRel G a x₁ x₂) (hy : ArgRel G b y₁ y₂) (hz : ArgRel G c z₁ z₂)
    {k₁ : Arg V₁ u → Expr V₁ L₁ rs} {k₂ : Arg V₂ u → Expr V₂ L₂ rs}
    (hk : ∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ r₁ r₂, ArgRel G' u r₁ r₂ → Wf G' D (k₁ r₁) (k₂ r₂)) :
    Wf G D (.let_ (op3 code x₁ y₁ z₁) fun (r, ()) => k₁ (.var r))
           (.let_ (op3 code x₂ y₂ z₂) fun (r, ()) => k₂ (.var r)) :=
  .let_ (.mk code (.cons hx (.cons hy (.cons hz .nil)))) fun (r₁, ()) (r₂, ()) =>
    hk (fun _ hp => List.mem_cons_of_mem _ hp) (.var r₁) (.var r₂) (.var List.mem_cons_self)

theorem Wf.load1 {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} (t : Ty)
    {a₁ : Arg V₁ i64} {a₂ : Arg V₂ i64} (ha : ArgRel G i64 a₁ a₂)
    {k₁ : Arg V₁ t → Expr V₁ L₁ rs} {k₂ : Arg V₂ t → Expr V₂ L₂ rs}
    (hk : ∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ v₁ v₂, ArgRel G' t v₁ v₂ → Wf G' D (k₁ v₁) (k₂ v₂)) :
    Wf G D (.load t a₁ fun v => k₁ (.var v)) (.load t a₂ fun v => k₂ (.var v)) :=
  .load t ha fun v₁ v₂ =>
    hk (fun _ hp => List.mem_cons_of_mem _ hp) (.var v₁) (.var v₂) (.var List.mem_cons_self)

theorem emitSextToW_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} (n w : Nat)
    {x₁ : Arg V₁ (.bits w)} {x₂ : Arg V₂ (.bits w)} (hx : ArgRel G (.bits w) x₁ x₂)
    {k₁ : Arg V₁ (.bits w) → Expr V₁ L₁ rs} {k₂ : Arg V₂ (.bits w) → Expr V₂ L₂ rs}
    (hk : ∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂, ArgRel G' (.bits w) y₁ y₂ →
      Wf G' D (k₁ y₁) (k₂ y₂)) :
    Wf G D (emitSextToW n w x₁ k₁) (emitSextToW n w x₂ k₂) :=
  sextToWEmit_eq_emitSextToW n w x₁ k₁ ▸ sextToWEmit_eq_emitSextToW n w x₂ k₂ ▸
    (sextToWEmit n w).run_wf (.cons hx .nil) hk

theorem emitMaskToN_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} (n w : Nat)
    {x₁ : Arg V₁ (.bits w)} {x₂ : Arg V₂ (.bits w)} (hx : ArgRel G (.bits w) x₁ x₂)
    {k₁ : Arg V₁ (.bits w) → Expr V₁ L₁ rs} {k₂ : Arg V₂ (.bits w) → Expr V₂ L₂ rs}
    (hk : ∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂, ArgRel G' (.bits w) y₁ y₂ →
      Wf G' D (k₁ y₁) (k₂ y₂)) :
    Wf G D (emitMaskToN n w x₁ k₁) (emitMaskToN n w x₂ k₂) :=
  maskToNEmit_eq_emitMaskToN n w x₁ k₁ ▸ maskToNEmit_eq_emitMaskToN n w x₂ k₂ ▸
    (maskToNEmit n w).run_wf (.cons hx .nil) hk

theorem emitCountMod_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} (n w : Nat)
    {c₁ : Arg V₁ (.bits w)} {c₂ : Arg V₂ (.bits w)} (hc : ArgRel G (.bits w) c₁ c₂)
    {k₁ : Arg V₁ (.bits w) → Expr V₁ L₁ rs} {k₂ : Arg V₂ (.bits w) → Expr V₂ L₂ rs}
    (hk : ∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂, ArgRel G' (.bits w) y₁ y₂ → Wf G' D (k₁ y₁) (k₂ y₂))
      :
    Wf G D (emitCountMod n w c₁ k₁) (emitCountMod n w c₂ k₂) := by
  cases hc with
  | imm cb => exact hk (fun _ h => h) _ _ (.imm _)
  | var hm => exact Wf.let2 _ (.var hm) (.imm _) hk

theorem unpackToLeaves_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty} :
    ∀ (t : Ty) {G : Ctx V₁ V₂} {D : Ctx L₁ L₂}
      {x₁ : Arg V₁ t} {x₂ : Arg V₂ t}, ArgRel G t x₁ x₂ →
      ∀ {k₁ : Tup (Arg V₁) (target.leafTys t) → Expr V₁ L₁ rs}
        {k₂ : Tup (Arg V₂) (target.leafTys t) → Expr V₂ L₂ rs},
      (∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂, TRel (ArgRel G') y₁ y₂ → Wf G' D (k₁ y₁) (k₂ y₂)) →
      Wf G D (unpackToLeaves target t x₁ k₁) (unpackToLeaves target t x₂ k₂)
  | .bool, _, _, _, _, hx, _, _, hk =>
    hk (fun _ h => h) _ _ (TRel.single hx)
  | .bits n, G, D, x₁, x₂, hx, k₁, k₂, hk => by
    simp only [unpackToLeaves]
    split
    · next h => exact hk (fun _ hp => hp) _ _ (TRel.single (castArgBits_rel h hx))
    · split
      · exact Wf.let1 _ hx fun h1 y₁ y₂ hy =>
          hk h1 _ _ (TRel.single hy)
      · exact hk (fun _ hp => hp) _ _ (TRel.single (ArgRel.imm _))
  | .float _, _, _, _, _, hx, _, _, hk =>
    hk (fun _ h => h) _ _ (TRel.single hx)
  | .pair a b, G, D, x₁, x₂, hx, k₁, k₂, hk => by
    cases hx with
    | imm c => exact hk (fun _ hp => hp) _ _ (leafImm_rel target (.pair a b) c)
    | var hm =>
      simp only [unpackToLeaves]
      refine .let_ (.mk (.unpair a b) (.cons (.var hm) .nil)) fun (va₁, vb₁, ()) (va₂, vb₂, ()) =>
        ?_
      refine unpackToLeaves_wf a (.var List.mem_cons_self) fun hG1 la₁ la₂ hla => ?_
      refine unpackToLeaves_wf b (.var (hG1 _ (List.mem_cons_of_mem _ List.mem_cons_self))) fun hG2
        lb₁ lb₂ hlb => ?_
      exact hk (fun p hp => hG2 _ (hG1 _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hp))))
        _ _ (TRel_tupAppend (TRel_argRel_weaken' hG2 hla) hlb)

theorem unpackToLegal_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty} :
    ∀ (t : Ty) {G : Ctx V₁ V₂} {D : Ctx L₁ L₂}
      {x₁ : Arg V₁ t} {x₂ : Arg V₂ t}, ArgRel G t x₁ x₂ →
      ∀ {k₁ : Tup (Arg V₁) (target.legalTys t) → Expr V₁ L₁ rs}
        {k₂ : Tup (Arg V₂) (target.legalTys t) → Expr V₂ L₂ rs},
      (∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂, TRel (ArgRel G') y₁ y₂ → Wf G' D (k₁ y₁) (k₂ y₂)) →
      Wf G D (unpackToLegal target t x₁ k₁) (unpackToLegal target t x₂ k₂)
  | .bool, _, _, _, _, hx, _, _, hk =>
    hk (fun _ h => h) _ _ (TRel.single hx)
  | .bits n, _, _, _, _, hx, _, _, hk => by
    simp only [unpackToLegal]
    split
    · next h => exact hk (fun _ hp => hp) _ _ (TRel.single (castArgBits_rel h hx))
    · split
      · exact Wf.let1 _ hx fun h1 y₁ y₂ hy =>
          hk h1 _ _ (TRel.single hy)
      · exact hk (fun _ hp => hp) _ _ (TRel.single (ArgRel.imm _))
  | .float _, _, _, _, _, hx, _, _, hk =>
    hk (fun _ h => h) _ _ (TRel.single hx)
  | .pair a b, G, D, x₁, x₂, hx, k₁, k₂, hk => by
    simp only [unpackToLegal]
    split
    · next h => exact hk (fun _ hp => hp) _ _ (tupToPacked_rel h (.cons hx .nil))
    · next h =>
      cases hx with
      | imm c => exact hk (fun _ hp => hp) _ _ (encodeImm_rel target (.pair a b) c)
      | var hm =>
        refine .let_ (.mk (.unpair a b) (.cons (.var hm) .nil)) fun (va₁, vb₁, ()) (va₂, vb₂, ()) =>
          ?_
        refine unpackToLegal_wf a (.var List.mem_cons_self) fun hG1 la₁ la₂ hla => ?_
        refine unpackToLegal_wf b (.var (hG1 _ (List.mem_cons_of_mem _ List.mem_cons_self))) fun hG2
          lb₁ lb₂ hlb => ?_
        exact hk (fun p hp => hG2 _ (hG1 _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hp))))
          _ _ (tupToSplit_rel (Bool.eq_false_iff.mpr h)
            (TRel_tupAppend (TRel_argRel_weaken' hG2 hla) hlb))

theorem packFromLegal_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty} :
    ∀ (t : Ty) {G : Ctx V₁ V₂} {D : Ctx L₁ L₂}
      {xs₁ : Tup (Arg V₁) (target.legalTys t)} {xs₂ : Tup (Arg V₂) (target.legalTys t)},
      TRel (ArgRel G) xs₁ xs₂ →
      ∀ {k₁ : Arg V₁ t → Expr V₁ L₁ rs} {k₂ : Arg V₂ t → Expr V₂ L₂ rs},
      (∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂, ArgRel G' t y₁ y₂ → Wf G' D (k₁ y₁) (k₂ y₂)) →
      Wf G D (packFromLegal target t xs₁ k₁) (packFromLegal target t xs₂ k₂)
  | .bool, _, _, xs₁, xs₂, hxs, _, _, hk => by
    rcases xs₁ with ⟨x₁, ⟨⟩⟩; rcases xs₂ with ⟨x₂, ⟨⟩⟩
    cases hxs with | cons hx _ => exact hk (fun _ h => h) _ _ hx
  | .bits n, _, _, xs₁, xs₂, hxs, _, _, hk => by
    rcases xs₁ with ⟨x₁, ⟨⟩⟩; rcases xs₂ with ⟨x₂, ⟨⟩⟩
    cases hxs with | cons hx _ =>
    simp only [packFromLegal]
    split
    · next h => exact hk (fun _ hp => hp) _ _ (castArgBits_rel h.symm hx)
    · split
      · exact Wf.let1 _ hx hk
      · exact hk (fun _ hp => hp) _ _ (.imm _)
  | .float _, _, _, xs₁, xs₂, hxs, _, _, hk => by
    rcases xs₁ with ⟨x₁, ⟨⟩⟩; rcases xs₂ with ⟨x₂, ⟨⟩⟩
    cases hxs with | cons hx _ => exact hk (fun _ h => h) _ _ hx
  | .pair a b, _, _, xs₁, xs₂, hxs, k₁, k₂, hk => by
    simp only [packFromLegal]
    split
    · next h =>
      obtain ⟨h1, _⟩ := TRel.cons_iff.1 (packedToTup_rel h hxs)
      exact hk (fun _ hp => hp) _ _ h1
    · next h =>
      obtain ⟨h1, h2⟩ := TRel_tupSplit (splitToTup_rel (Bool.eq_false_iff.mpr h) hxs)
      refine packFromLegal_wf a h1 fun hGa va₁ va₂ hva => ?_
      refine packFromLegal_wf b (TRel_argRel_weaken' hGa h2) fun hGb vb₁ vb₂ hvb => ?_
      exact Wf.let2 (.mkpair a b) (hva.weaken hGb) hvb fun hGc p₁ p₂ hp =>
        hk (sub_trans hGa (sub_trans hGb hGc)) p₁ p₂ hp

theorem splitLegalToLeaves_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty} :
    ∀ (t : Ty) {G : Ctx V₁ V₂} {D : Ctx L₁ L₂}
      {xs₁ : Tup (Arg V₁) (target.legalTys t)} {xs₂ : Tup (Arg V₂) (target.legalTys t)},
      TRel (ArgRel G) xs₁ xs₂ →
      ∀ {k₁ : Tup (Arg V₁) (target.leafTys t) → Expr V₁ L₁ rs}
        {k₂ : Tup (Arg V₂) (target.leafTys t) → Expr V₂ L₂ rs},
      (∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂, TRel (ArgRel G') y₁ y₂ → Wf G' D (k₁ y₁) (k₂ y₂)) →
      Wf G D (splitLegalToLeaves target t xs₁ k₁) (splitLegalToLeaves target t xs₂ k₂)
  | .bool, _, _, _, _, hxs, _, _, hk => hk (fun _ h => h) _ _ hxs
  | .bits _, _, _, _, _, hxs, _, _, hk => hk (fun _ h => h) _ _ hxs
  | .float _, _, _, _, _, hxs, _, _, hk => hk (fun _ h => h) _ _ hxs
  | .pair a b, _, _, xs₁, xs₂, hxs, k₁, k₂, hk => by
    simp only [splitLegalToLeaves]
    split
    · next h =>
      obtain ⟨h1, _⟩ := TRel.cons_iff.1 (packedToTup_rel h hxs)
      exact unpackToLeaves_wf target (.pair a b) h1 hk
    · next h =>
      obtain ⟨h1, h2⟩ := TRel_tupSplit (splitToTup_rel (Bool.eq_false_iff.mpr h) hxs)
      refine splitLegalToLeaves_wf a h1 fun hGa fa₁ fa₂ hfa => ?_
      refine splitLegalToLeaves_wf b (TRel_argRel_weaken' hGa h2) fun hGb fb₁ fb₂ hfb => ?_
      exact hk (sub_trans hGa hGb) _ _ (TRel_tupAppend (TRel_argRel_weaken' hGb hfa) hfb)

theorem packLeavesToLegal_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty} :
    ∀ (t : Ty) {G : Ctx V₁ V₂} {D : Ctx L₁ L₂}
      {xs₁ : Tup (Arg V₁) (target.leafTys t)} {xs₂ : Tup (Arg V₂) (target.leafTys t)},
      TRel (ArgRel G) xs₁ xs₂ →
      ∀ {k₁ : Tup (Arg V₁) (target.legalTys t) → Expr V₁ L₁ rs}
        {k₂ : Tup (Arg V₂) (target.legalTys t) → Expr V₂ L₂ rs},
      (∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂, TRel (ArgRel G') y₁ y₂ → Wf G' D (k₁ y₁) (k₂ y₂)) →
      Wf G D (packLeavesToLegal target t xs₁ k₁) (packLeavesToLegal target t xs₂ k₂)
  | .bool, _, _, _, _, hxs, _, _, hk => hk (fun _ h => h) _ _ hxs
  | .bits _, _, _, _, _, hxs, _, _, hk => hk (fun _ h => h) _ _ hxs
  | .float _, _, _, _, _, hxs, _, _, hk => hk (fun _ h => h) _ _ hxs
  | .pair a b, _, _, xs₁, xs₂, hxs, k₁, k₂, hk => by
    simp only [packLeavesToLegal]
    obtain ⟨h1, h2⟩ := TRel_tupSplit hxs
    split
    · next h =>
      refine packLeavesToLegal_wf a h1 fun hGa la₁ la₂ hla => ?_
      refine packLeavesToLegal_wf b (TRel_argRel_weaken' hGa h2) fun hGb lb₁ lb₂ hlb => ?_
      refine packFromLegal_wf target a (TRel_argRel_weaken' hGb hla) fun hGc va₁ va₂ hva => ?_
      refine packFromLegal_wf target b (TRel_argRel_weaken' hGc hlb) fun hGd vb₁ vb₂ hvb => ?_
      exact Wf.let2 (.mkpair a b) (hva.weaken hGd) hvb fun hGe p₁ p₂ hp =>
        hk (sub_trans hGa (sub_trans hGb (sub_trans hGc (sub_trans hGd hGe)))) _ _
          (tupToPacked_rel h (.cons hp .nil))
    · next h =>
      refine packLeavesToLegal_wf a h1 fun hGa la₁ la₂ hla => ?_
      refine packLeavesToLegal_wf b (TRel_argRel_weaken' hGa h2) fun hGb lb₁ lb₂ hlb => ?_
      exact hk (sub_trans hGa hGb) _ _
        (tupToSplit_rel (Bool.eq_false_iff.mpr h)
          (TRel_tupAppend (TRel_argRel_weaken' hGb hla) hlb))

theorem emitTernlogBits_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} (w : Nat)
    {a₁ b₁ c₁ : Arg V₁ (.bits w)} {a₂ b₂ c₂ : Arg V₂ (.bits w)}
    (ha : ArgRel G (.bits w) a₁ a₂) (hb : ArgRel G (.bits w) b₁ b₂) (hc : ArgRel G (.bits w) c₁ c₂)
    (imm : BitVec 8)
    {k₁ : Arg V₁ (.bits w) → Expr V₁ L₁ rs} {k₂ : Arg V₂ (.bits w) → Expr V₂ L₂ rs}
    (hk : ∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂, ArgRel G' (.bits w) y₁ y₂ →
      Wf G' D (k₁ y₁) (k₂ y₂)) :
    Wf G D (emitTernlogBits w a₁ b₁ c₁ imm k₁) (emitTernlogBits w a₂ b₂ c₂ imm k₂) :=
  (ternlogBitsEmit_bundle (.withWidth w) List.mem_cons_self imm).wf_eq
    (.cons ha (.cons hb (.cons hc .nil))) hk
    (ternlogBitsEmit_eq_emitTernlogBits w imm a₁ b₁ c₁ k₁)
    (ternlogBitsEmit_eq_emitTernlogBits w imm a₂ b₂ c₂ k₂)

theorem emitTernlogBool_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂}
    {a₁ b₁ c₁ : Arg V₁ .bool} {a₂ b₂ c₂ : Arg V₂ .bool}
    (ha : ArgRel G .bool a₁ a₂) (hb : ArgRel G .bool b₁ b₂) (hc : ArgRel G .bool c₁ c₂)
    (imm : BitVec 8)
    {k₁ : Arg V₁ .bool → Expr V₁ L₁ rs} {k₂ : Arg V₂ .bool → Expr V₂ L₂ rs}
    (hk : ∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂, ArgRel G' .bool y₁ y₂ → Wf G' D (k₁ y₁) (k₂ y₂)) :
    Wf G D (emitTernlogBool a₁ b₁ c₁ imm k₁) (emitTernlogBool a₂ b₂ c₂ imm k₂) :=
  (ternlogBoolEmit_bundle .aarch64 imm).wf_eq (.cons ha (.cons hb (.cons hc .nil))) hk
    (ternlogBoolEmit_eq_emitTernlogBool imm a₁ b₁ c₁ k₁)
    (ternlogBoolEmit_eq_emitTernlogBool imm a₂ b₂ c₂ k₂)

theorem emitBoolCmp_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} (o : CmpOp)
    {a₁ b₁ : Arg V₁ .bool} {a₂ b₂ : Arg V₂ .bool}
    (ha : ArgRel G .bool a₁ a₂) (hb : ArgRel G .bool b₁ b₂)
    {k₁ : Arg V₁ .bool → Expr V₁ L₁ rs} {k₂ : Arg V₂ .bool → Expr V₂ L₂ rs}
    (hk : ∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂, ArgRel G' .bool y₁ y₂ → Wf G' D (k₁ y₁) (k₂ y₂)) :
    Wf G D (emitBoolCmp o a₁ b₁ k₁) (emitBoolCmp o a₂ b₂ k₂) :=
  (boolCmpEmit_bundle .aarch64 o).wf_eq (.cons ha (.cons hb .nil)) hk
    (boolCmpEmit_eq_emitBoolCmp o a₁ b₁ k₁) (boolCmpEmit_eq_emitBoolCmp o a₂ b₂ k₂)

theorem emitBoolSelect_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂}
    {c₁ a₁ b₁ : Arg V₁ .bool} {c₂ a₂ b₂ : Arg V₂ .bool}
    (hc : ArgRel G .bool c₁ c₂) (ha : ArgRel G .bool a₁ a₂) (hb : ArgRel G .bool b₁ b₂)
    {k₁ : Arg V₁ .bool → Expr V₁ L₁ rs} {k₂ : Arg V₂ .bool → Expr V₂ L₂ rs}
    (hk : ∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂, ArgRel G' .bool y₁ y₂ → Wf G' D (k₁ y₁) (k₂ y₂)) :
    Wf G D (emitBoolSelect c₁ a₁ b₁ k₁) (emitBoolSelect c₂ a₂ b₂ k₂) :=
  (boolSelectEmit_bundle .aarch64).wf_eq (.cons hc (.cons ha (.cons hb .nil))) hk rfl rfl


end LegalWf

end LeanQbe.T
