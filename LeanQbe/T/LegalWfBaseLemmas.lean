module

public import LeanQbe.T.Legal
public import LeanQbe.T.WPLemmas
public import LeanQbe.T.FlatLemmas

/-!
# Correctness and legality proofs for `LeanQbe.T.Legal` (`T5`, `G13`)

Proves the three main theorems for `Func.legal` using `Wf.induct`:

* `Func.legal_wf`: well-formedness preservation (`f.Wf → (f.legal target).Wf`).
* `Func.legal_wp` / `Func.legal_spec`: semantic weakest-precondition preservation
  (`Func.wp Γ f xs m Q X → Func.wp (legalEnv target Γ) (f.legal target) (encodeTup target as xs) m (legalPost target Q) (legalXPost target X)`).
* `Func.legal_isLegal` (in `LeanQbe.T.LegalCheck3`, split across `LegalCheck1`–`LegalCheck3`):
  computable target legality (`f.Wf → f.supportsSource target = true → (f.legal target).isLegal target = true`).
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

def valsTup {ts : List Ty} (xs : Tup (Arg Val) ts) : Tup Val ts :=
  xs.map (fun _ a => a.val)

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
    {as bs : List Ty} (h₁ : Tup (Arg V₁) as = Tup (Arg V₁) bs) (h₂ : Tup (Arg V₂) as = Tup (Arg V₂) bs)
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

theorem TRel_argRel_weaken' {V₁ V₂ : Ty → Type} {G G' : Ctx V₁ V₂}
    (hG : ∀ p ∈ G, p ∈ G') {ts : List Ty} {as₁ : Tup (Arg V₁) ts} {as₂ : Tup (Arg V₂) ts}
    (h : TRel (ArgRel G) as₁ as₂) : TRel (ArgRel G') as₁ as₂ :=
  TRel.argRel_weaken hG h

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
def DGood {L₁ L₂ : List Ty → Type} (D : Ctx L₁ L₂) (LD : Ctx (LLab target L₁) (LLab target L₂)) : Prop :=
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

theorem sub_trans {α : Type} {G₁ G₂ G₃ : List α}
    (h₁ : ∀ p ∈ G₁, p ∈ G₂) (h₂ : ∀ p ∈ G₂, p ∈ G₃) : ∀ p ∈ G₁, p ∈ G₃ :=
  fun p hp => h₂ p (h₁ p hp)

theorem Wf.let1 {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} {a u : Ty} (code : OpCode [a] [u])
    {x₁ : Arg V₁ a} {x₂ : Arg V₂ a} (hx : ArgRel G a x₁ x₂)
    {k₁ : Arg V₁ u → Expr V₁ L₁ rs} {k₂ : Arg V₂ u → Expr V₂ L₂ rs}
    (hk : ∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂, ArgRel G' u y₁ y₂ → Wf G' D (k₁ y₁) (k₂ y₂)) :
    Wf G D (.let_ (op1 code x₁) fun r => k₁ (.var r.fst))
           (.let_ (op1 code x₂) fun r => k₂ (.var r.fst)) :=
  .let_ (.mk code (.cons hx .nil)) fun r₁ r₂ =>
    hk (fun _ hp => List.mem_cons_of_mem _ hp) (.var r₁.fst) (.var r₂.fst) (.var List.mem_cons_self)

theorem Wf.let2 {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} {a b u : Ty} (code : OpCode [a, b] [u])
    {x₁ : Arg V₁ a} {x₂ : Arg V₂ a} {y₁ : Arg V₁ b} {y₂ : Arg V₂ b}
    (hx : ArgRel G a x₁ x₂) (hy : ArgRel G b y₁ y₂)
    {k₁ : Arg V₁ u → Expr V₁ L₁ rs} {k₂ : Arg V₂ u → Expr V₂ L₂ rs}
    (hk : ∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ r₁ r₂, ArgRel G' u r₁ r₂ → Wf G' D (k₁ r₁) (k₂ r₂)) :
    Wf G D (.let_ (op2 code x₁ y₁) fun r => k₁ (.var r.fst))
           (.let_ (op2 code x₂ y₂) fun r => k₂ (.var r.fst)) :=
  .let_ (.mk code (.cons hx (.cons hy .nil))) fun r₁ r₂ =>
    hk (fun _ hp => List.mem_cons_of_mem _ hp) (.var r₁.fst) (.var r₂.fst) (.var List.mem_cons_self)

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
    (hk : ∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂, ArgRel G' (.bits w) y₁ y₂ → Wf G' D (k₁ y₁) (k₂ y₂)) :
    Wf G D (emitSextToW n w x₁ k₁) (emitSextToW n w x₂ k₂) := by
  simp only [emitSextToW]
  split
  · exact hk (fun _ h => h) x₁ x₂ hx
  · exact Wf.let2 _ hx (.imm _) fun h1 s₁ s₂ hs =>
      Wf.let2 _ hs (.imm _) fun h2 r₁ r₂ hr =>
        hk (sub_trans h1 h2) r₁ r₂ hr

theorem emitMaskToN_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} (n w : Nat)
    {x₁ : Arg V₁ (.bits w)} {x₂ : Arg V₂ (.bits w)} (hx : ArgRel G (.bits w) x₁ x₂)
    {k₁ : Arg V₁ (.bits w) → Expr V₁ L₁ rs} {k₂ : Arg V₂ (.bits w) → Expr V₂ L₂ rs}
    (hk : ∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂, ArgRel G' (.bits w) y₁ y₂ → Wf G' D (k₁ y₁) (k₂ y₂)) :
    Wf G D (emitMaskToN n w x₁ k₁) (emitMaskToN n w x₂ k₂) := by
  simp only [emitMaskToN]
  split
  · exact hk (fun _ h => h) _ _ (.imm _)
  · split
    · exact hk (fun _ h => h) x₁ x₂ hx
    · exact Wf.let2 _ hx (.imm _) hk

theorem emitCountMod_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} (n w : Nat)
    {c₁ : Arg V₁ (.bits w)} {c₂ : Arg V₂ (.bits w)} (hc : ArgRel G (.bits w) c₁ c₂)
    {k₁ : Arg V₁ (.bits w) → Expr V₁ L₁ rs} {k₂ : Arg V₂ (.bits w) → Expr V₂ L₂ rs}
    (hk : ∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂, ArgRel G' (.bits w) y₁ y₂ → Wf G' D (k₁ y₁) (k₂ y₂)) :
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
      refine .let_ (.mk (.unpair a b) (.cons (.var hm) .nil)) fun (va₁, vb₁, ()) (va₂, vb₂, ()) => ?_
      refine unpackToLeaves_wf a (.var List.mem_cons_self) fun hG1 la₁ la₂ hla => ?_
      refine unpackToLeaves_wf b (.var (hG1 _ (List.mem_cons_of_mem _ List.mem_cons_self))) fun hG2 lb₁ lb₂ hlb => ?_
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
        refine .let_ (.mk (.unpair a b) (.cons (.var hm) .nil)) fun (va₁, vb₁, ()) (va₂, vb₂, ()) => ?_
        refine unpackToLegal_wf a (.var List.mem_cons_self) fun hG1 la₁ la₂ hla => ?_
        refine unpackToLegal_wf b (.var (hG1 _ (List.mem_cons_of_mem _ List.mem_cons_self))) fun hG2 lb₁ lb₂ hlb => ?_
        exact hk (fun p hp => hG2 _ (hG1 _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hp))))
          _ _ (tupToSplit_rel (Bool.eq_false_iff.mpr h) (TRel_tupAppend (TRel_argRel_weaken' hG2 hla) hlb))

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
        (tupToSplit_rel (Bool.eq_false_iff.mpr h) (TRel_tupAppend (TRel_argRel_weaken' hGb hla) hlb))

private theorem emitTernlogBits_go_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    (w : Nat) (imm : BitVec 8) :
    ∀ (d idx : Nat), 8 - idx ≤ d → ∀ {G : Ctx V₁ V₂} {D : Ctx L₁ L₂}
      {o₁ : Option (Arg V₁ (.bits w))} {o₂ : Option (Arg V₂ (.bits w))}
      {a₁ na₁ b₁ nb₁ c₁ nc₁ : Arg V₁ (.bits w)}
      {a₂ na₂ b₂ nb₂ c₂ nc₂ : Arg V₂ (.bits w)},
      (match o₁, o₂ with
       | none, none => True
       | some u₁, some u₂ => ArgRel G (.bits w) u₁ u₂
       | _, _ => False) →
      ArgRel G (.bits w) a₁ a₂ → ArgRel G (.bits w) b₁ b₂ → ArgRel G (.bits w) c₁ c₂ →
      ArgRel G (.bits w) na₁ na₂ → ArgRel G (.bits w) nb₁ nb₂ → ArgRel G (.bits w) nc₁ nc₂ →
      ∀ {k₁ : Arg V₁ (.bits w) → Expr V₁ L₁ rs} {k₂ : Arg V₂ (.bits w) → Expr V₂ L₂ rs},
      (∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂, ArgRel G' (.bits w) y₁ y₂ → Wf G' D (k₁ y₁) (k₂ y₂)) →
      Wf G D (emitTernlogBits.go w imm k₁ idx o₁ a₁ b₁ c₁ na₁ nb₁ nc₁)
             (emitTernlogBits.go w imm k₂ idx o₂ a₂ b₂ c₂ na₂ nb₂ nc₂)
  | 0, idx, hle, G, D, o₁, o₂, a₁, na₁, b₁, nb₁, c₁, nc₁, a₂, na₂, b₂, nb₂, c₂, nc₂, ho, _, _, _, _, _, _, k₁, k₂, hk => by
    have hge : idx ≥ 8 := by omega
    have hlhs := emitTernlogBits.go.eq_def w imm k₁ idx o₁ a₁ b₁ c₁ na₁ nb₁ nc₁
    have hrhs := emitTernlogBits.go.eq_def w imm k₂ idx o₂ a₂ b₂ c₂ na₂ nb₂ nc₂
    rw [hlhs, hrhs]
    simp only [hge, ↓reduceIte]
    cases o₁ <;> cases o₂ <;> first | exact False.elim ho | exact hk (fun _ p => p) _ _ (.imm _) | exact hk (fun _ p => p) _ _ ho
  | d' + 1, idx, hle, G, D, o₁, o₂, a₁, na₁, b₁, nb₁, c₁, nc₁, a₂, na₂, b₂, nb₂, c₂, nc₂, ho, ha, hb, hc, hna, hnb, hnc, k₁, k₂, hk => by
    have hlhs := emitTernlogBits.go.eq_def w imm k₁ idx o₁ a₁ b₁ c₁ na₁ nb₁ nc₁
    have hrhs := emitTernlogBits.go.eq_def w imm k₂ idx o₂ a₂ b₂ c₂ na₂ nb₂ nc₂
    rw [hlhs, hrhs]
    by_cases hge : idx ≥ 8
    · simp only [hge, ↓reduceIte]
      cases o₁ <;> cases o₂ <;> first | exact False.elim ho | exact hk (fun _ p => p) _ _ (.imm _) | exact hk (fun _ p => p) _ _ ho
    · simp only [hge, ↓reduceIte]
      by_cases hbit : imm.getLsbD idx = true
      · simp only [hbit, ↓reduceIte]
        have hpa : ArgRel G (.bits w) (if idx / 4 % 2 == 1 then a₁ else na₁) (if idx / 4 % 2 == 1 then a₂ else na₂) := by
          split <;> assumption
        have hpb : ArgRel G (.bits w) (if idx / 2 % 2 == 1 then b₁ else nb₁) (if idx / 2 % 2 == 1 then b₂ else nb₂) := by
          split <;> assumption
        have hpc : ArgRel G (.bits w) (if idx % 2 == 1 then c₁ else nc₁) (if idx % 2 == 1 then c₂ else nc₂) := by
          split <;> assumption
        refine .let_ (.mk (.and (.bits w)) (.cons hpa (.cons hpb .nil))) fun t₁ t₂ => ?_
        have h1 : ∀ p ∈ G, p ∈ ⟨.bits w, t₁.fst, t₂.fst⟩ :: G := fun _ hp => List.mem_cons_of_mem _ hp
        have ht : ArgRel (⟨.bits w, t₁.fst, t₂.fst⟩ :: G) (.bits w) (.var t₁.fst) (.var t₂.fst) :=
          .var List.mem_cons_self
        refine .let_ (.mk (.and (.bits w)) (.cons ht (.cons (hpc.weaken h1) .nil))) fun tm₁ tm₂ => ?_
        have h2 : ∀ p ∈ ⟨.bits w, t₁.fst, t₂.fst⟩ :: G,
            p ∈ ⟨.bits w, tm₁.fst, tm₂.fst⟩ :: ⟨.bits w, t₁.fst, t₂.fst⟩ :: G :=
          fun _ hp => List.mem_cons_of_mem _ hp
        have hs := sub_trans h1 h2
        have htm : ArgRel (⟨.bits w, tm₁.fst, tm₂.fst⟩ :: ⟨.bits w, t₁.fst, t₂.fst⟩ :: G) (.bits w)
            (.var tm₁.fst) (.var tm₂.fst) := .var List.mem_cons_self
        cases o₁ <;> cases o₂
        · exact emitTernlogBits_go_wf w imm d' (idx + 1) (by omega) htm (ha.weaken hs) (hb.weaken hs)
            (hc.weaken hs) (hna.weaken hs) (hnb.weaken hs) (hnc.weaken hs)
            fun h3 y₁ y₂ hy => hk (sub_trans hs h3) y₁ y₂ hy
        · exact False.elim ho
        · exact False.elim ho
        · exact Wf.let2 _ (ho.weaken hs) htm fun h3 _ _ hac =>
            have hs2 := sub_trans hs h3
            emitTernlogBits_go_wf w imm d' (idx + 1) (by omega) hac (ha.weaken hs2) (hb.weaken hs2)
              (hc.weaken hs2) (hna.weaken hs2) (hnb.weaken hs2) (hnc.weaken hs2)
              fun h4 y₁ y₂ hy => hk (sub_trans hs2 h4) y₁ y₂ hy
      · simp only [hbit, Bool.false_eq_true, ↓reduceIte]
        exact emitTernlogBits_go_wf w imm d' (idx + 1) (by omega) ho ha hb hc hna hnb hnc hk

theorem emitTernlogBits_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} (w : Nat)
    {a₁ b₁ c₁ : Arg V₁ (.bits w)} {a₂ b₂ c₂ : Arg V₂ (.bits w)}
    (ha : ArgRel G (.bits w) a₁ a₂) (hb : ArgRel G (.bits w) b₁ b₂) (hc : ArgRel G (.bits w) c₁ c₂)
    (imm : BitVec 8)
    {k₁ : Arg V₁ (.bits w) → Expr V₁ L₁ rs} {k₂ : Arg V₂ (.bits w) → Expr V₂ L₂ rs}
    (hk : ∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂, ArgRel G' (.bits w) y₁ y₂ → Wf G' D (k₁ y₁) (k₂ y₂)) :
    Wf G D (emitTernlogBits w a₁ b₁ c₁ imm k₁) (emitTernlogBits w a₂ b₂ c₂ imm k₂) := by
  simp only [emitTernlogBits]
  split
  · exact hk (fun _ h => h) _ _ (.imm _)
  · split
    · exact hk (fun _ h => h) _ _ (.imm _)
    · refine Wf.let1 _ ha fun h1 na₁ na₂ hna =>
        Wf.let1 _ (hb.weaken h1) fun h2 nb₁ nb₂ hnb =>
          Wf.let1 _ (hc.weaken (sub_trans h1 h2)) fun h3 nc₁ nc₂ hnc => ?_
      have hs := sub_trans h1 (sub_trans h2 h3)
      exact emitTernlogBits_go_wf w imm 8 0 (Nat.le_refl _) trivial
        (ha.weaken hs) (hb.weaken hs) (hc.weaken hs)
        (hna.weaken (sub_trans h2 h3)) (hnb.weaken h3) hnc
        fun h4 y₁ y₂ hy => hk (sub_trans hs h4) y₁ y₂ hy

private theorem emitTernlogBool_go_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    (imm : BitVec 8) :
    ∀ (d idx : Nat), 8 - idx ≤ d → ∀ {G : Ctx V₁ V₂} {D : Ctx L₁ L₂}
      {o₁ : Option (Arg V₁ .bool)} {o₂ : Option (Arg V₂ .bool)}
      {a₁ na₁ b₁ nb₁ c₁ nc₁ : Arg V₁ .bool}
      {a₂ na₂ b₂ nb₂ c₂ nc₂ : Arg V₂ .bool},
      (match o₁, o₂ with
       | none, none => True
       | some u₁, some u₂ => ArgRel G .bool u₁ u₂
       | _, _ => False) →
      ArgRel G .bool a₁ a₂ → ArgRel G .bool b₁ b₂ → ArgRel G .bool c₁ c₂ →
      ArgRel G .bool na₁ na₂ → ArgRel G .bool nb₁ nb₂ → ArgRel G .bool nc₁ nc₂ →
      ∀ {k₁ : Arg V₁ .bool → Expr V₁ L₁ rs} {k₂ : Arg V₂ .bool → Expr V₂ L₂ rs},
      (∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂, ArgRel G' .bool y₁ y₂ → Wf G' D (k₁ y₁) (k₂ y₂)) →
      Wf G D (emitTernlogBool.go imm k₁ idx o₁ a₁ b₁ c₁ na₁ nb₁ nc₁)
             (emitTernlogBool.go imm k₂ idx o₂ a₂ b₂ c₂ na₂ nb₂ nc₂)
  | 0, idx, hle, G, D, o₁, o₂, a₁, na₁, b₁, nb₁, c₁, nc₁, a₂, na₂, b₂, nb₂, c₂, nc₂, ho, _, _, _, _, _, _, k₁, k₂, hk => by
    have hge : idx ≥ 8 := by omega
    have hlhs := emitTernlogBool.go.eq_def imm k₁ idx o₁ a₁ b₁ c₁ na₁ nb₁ nc₁
    have hrhs := emitTernlogBool.go.eq_def imm k₂ idx o₂ a₂ b₂ c₂ na₂ nb₂ nc₂
    rw [hlhs, hrhs]
    simp only [hge, ↓reduceIte]
    cases o₁ <;> cases o₂ <;> first | exact False.elim ho | exact hk (fun _ p => p) _ _ (.imm _) | exact hk (fun _ p => p) _ _ ho
  | d' + 1, idx, hle, G, D, o₁, o₂, a₁, na₁, b₁, nb₁, c₁, nc₁, a₂, na₂, b₂, nb₂, c₂, nc₂, ho, ha, hb, hc, hna, hnb, hnc, k₁, k₂, hk => by
    have hlhs := emitTernlogBool.go.eq_def imm k₁ idx o₁ a₁ b₁ c₁ na₁ nb₁ nc₁
    have hrhs := emitTernlogBool.go.eq_def imm k₂ idx o₂ a₂ b₂ c₂ na₂ nb₂ nc₂
    rw [hlhs, hrhs]
    by_cases hge : idx ≥ 8
    · simp only [hge, ↓reduceIte]
      cases o₁ <;> cases o₂ <;> first | exact False.elim ho | exact hk (fun _ p => p) _ _ (.imm _) | exact hk (fun _ p => p) _ _ ho
    · simp only [hge, ↓reduceIte]
      by_cases hbit : imm.getLsbD idx = true
      · simp only [hbit, ↓reduceIte]
        have hpa : ArgRel G .bool (if idx / 4 % 2 == 1 then a₁ else na₁) (if idx / 4 % 2 == 1 then a₂ else na₂) := by
          split <;> assumption
        have hpb : ArgRel G .bool (if idx / 2 % 2 == 1 then b₁ else nb₁) (if idx / 2 % 2 == 1 then b₂ else nb₂) := by
          split <;> assumption
        have hpc : ArgRel G .bool (if idx % 2 == 1 then c₁ else nc₁) (if idx % 2 == 1 then c₂ else nc₂) := by
          split <;> assumption
        refine .let_ (.mk (.and .bool) (.cons hpa (.cons hpb .nil))) fun t₁ t₂ => ?_
        have h1 : ∀ p ∈ G, p ∈ ⟨.bool, t₁.fst, t₂.fst⟩ :: G := fun _ hp => List.mem_cons_of_mem _ hp
        have ht : ArgRel (⟨.bool, t₁.fst, t₂.fst⟩ :: G) .bool (.var t₁.fst) (.var t₂.fst) :=
          .var List.mem_cons_self
        refine .let_ (.mk (.and .bool) (.cons ht (.cons (hpc.weaken h1) .nil))) fun tm₁ tm₂ => ?_
        have h2 : ∀ p ∈ ⟨.bool, t₁.fst, t₂.fst⟩ :: G,
            p ∈ ⟨.bool, tm₁.fst, tm₂.fst⟩ :: ⟨.bool, t₁.fst, t₂.fst⟩ :: G :=
          fun _ hp => List.mem_cons_of_mem _ hp
        have hs := sub_trans h1 h2
        have htm : ArgRel (⟨.bool, tm₁.fst, tm₂.fst⟩ :: ⟨.bool, t₁.fst, t₂.fst⟩ :: G) .bool
            (.var tm₁.fst) (.var tm₂.fst) := .var List.mem_cons_self
        cases o₁ <;> cases o₂
        · exact emitTernlogBool_go_wf imm d' (idx + 1) (by omega) htm (ha.weaken hs) (hb.weaken hs)
            (hc.weaken hs) (hna.weaken hs) (hnb.weaken hs) (hnc.weaken hs)
            fun h3 y₁ y₂ hy => hk (sub_trans hs h3) y₁ y₂ hy
        · exact False.elim ho
        · exact False.elim ho
        · exact Wf.let2 _ (ho.weaken hs) htm fun h3 _ _ hac =>
            have hs2 := sub_trans hs h3
            emitTernlogBool_go_wf imm d' (idx + 1) (by omega) hac (ha.weaken hs2) (hb.weaken hs2)
              (hc.weaken hs2) (hna.weaken hs2) (hnb.weaken hs2) (hnc.weaken hs2)
              fun h4 y₁ y₂ hy => hk (sub_trans hs2 h4) y₁ y₂ hy
      · simp only [hbit, Bool.false_eq_true, ↓reduceIte]
        exact emitTernlogBool_go_wf imm d' (idx + 1) (by omega) ho ha hb hc hna hnb hnc hk

theorem emitTernlogBool_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂}
    {a₁ b₁ c₁ : Arg V₁ .bool} {a₂ b₂ c₂ : Arg V₂ .bool}
    (ha : ArgRel G .bool a₁ a₂) (hb : ArgRel G .bool b₁ b₂) (hc : ArgRel G .bool c₁ c₂)
    (imm : BitVec 8)
    {k₁ : Arg V₁ .bool → Expr V₁ L₁ rs} {k₂ : Arg V₂ .bool → Expr V₂ L₂ rs}
    (hk : ∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂, ArgRel G' .bool y₁ y₂ → Wf G' D (k₁ y₁) (k₂ y₂)) :
    Wf G D (emitTernlogBool a₁ b₁ c₁ imm k₁) (emitTernlogBool a₂ b₂ c₂ imm k₂) := by
  simp only [emitTernlogBool]
  split
  · exact hk (fun _ h => h) _ _ (.imm _)
  · split
    · exact hk (fun _ h => h) _ _ (.imm _)
    · refine Wf.let1 _ ha fun h1 na₁ na₂ hna =>
        Wf.let1 _ (hb.weaken h1) fun h2 nb₁ nb₂ hnb =>
          Wf.let1 _ (hc.weaken (sub_trans h1 h2)) fun h3 nc₁ nc₂ hnc => ?_
      have hs := sub_trans h1 (sub_trans h2 h3)
      exact emitTernlogBool_go_wf imm 8 0 (Nat.le_refl _) trivial
        (ha.weaken hs) (hb.weaken hs) (hc.weaken hs)
        (hna.weaken (sub_trans h2 h3)) (hnb.weaken h3) hnc
        fun h4 y₁ y₂ hy => hk (sub_trans hs h4) y₁ y₂ hy

theorem emitBoolCmp_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} (o : CmpOp)
    {a₁ b₁ : Arg V₁ .bool} {a₂ b₂ : Arg V₂ .bool}
    (ha : ArgRel G .bool a₁ a₂) (hb : ArgRel G .bool b₁ b₂)
    {k₁ : Arg V₁ .bool → Expr V₁ L₁ rs} {k₂ : Arg V₂ .bool → Expr V₂ L₂ rs}
    (hk : ∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂, ArgRel G' .bool y₁ y₂ → Wf G' D (k₁ y₁) (k₂ y₂)) :
    Wf G D (emitBoolCmp o a₁ b₁ k₁) (emitBoolCmp o a₂ b₂ k₂) := by
  cases o <;> simp only [emitBoolCmp]
  · exact Wf.let2 _ ha hb fun h1 x₁ x₂ hx => Wf.let1 _ hx fun h2 r₁ r₂ hr => hk (sub_trans h1 h2) r₁ r₂ hr
  · exact Wf.let2 _ ha hb hk
  all_goals
    first
    | exact Wf.let1 _ ha fun h1 na₁ na₂ hna => Wf.let2 _ hna (hb.weaken h1) fun h2 r₁ r₂ hr => hk (sub_trans h1 h2) r₁ r₂ hr
    | exact Wf.let1 _ hb fun h1 nb₁ nb₂ hnb => Wf.let2 _ (ha.weaken h1) hnb fun h2 r₁ r₂ hr => hk (sub_trans h1 h2) r₁ r₂ hr

theorem emitBoolSelect_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂}
    {c₁ a₁ b₁ : Arg V₁ .bool} {c₂ a₂ b₂ : Arg V₂ .bool}
    (hc : ArgRel G .bool c₁ c₂) (ha : ArgRel G .bool a₁ a₂) (hb : ArgRel G .bool b₁ b₂)
    {k₁ : Arg V₁ .bool → Expr V₁ L₁ rs} {k₂ : Arg V₂ .bool → Expr V₂ L₂ rs}
    (hk : ∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂, ArgRel G' .bool y₁ y₂ → Wf G' D (k₁ y₁) (k₂ y₂)) :
    Wf G D (emitBoolSelect c₁ a₁ b₁ k₁) (emitBoolSelect c₂ a₂ b₂ k₂) :=
  Wf.let2 _ hc ha fun h1 _ _ ht1 =>
    Wf.let1 _ (hc.weaken h1) fun h2 _ _ hnc =>
      Wf.let2 _ hnc (hb.weaken (sub_trans h1 h2)) fun h3 _ _ ht2 =>
        Wf.let2 _ (ht1.weaken (sub_trans h2 h3)) ht2 fun h4 r₁ r₂ hr =>
          hk (sub_trans h1 (sub_trans h2 (sub_trans h3 h4))) r₁ r₂ hr

theorem pushLeafWord64_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} (w : Nat)
    {leaf₁ : Arg V₁ i64} {leaf₂ : Arg V₂ i64} (hl : ArgRel G i64 leaf₁ leaf₂)
    {ws₁ : List (Arg V₁ i64)} {ws₂ : List (Arg V₂ i64)} (hws : ListRel (ArgRel G i64) ws₁ ws₂)
    {acc₁ : Arg V₁ i64} {acc₂ : Arg V₂ i64} (hacc : ArgRel G i64 acc₁ acc₂) (accBits : Nat)
    {k₁ : List (Arg V₁ i64) → Arg V₁ i64 → Nat → Expr V₁ L₁ rs}
    {k₂ : List (Arg V₂ i64) → Arg V₂ i64 → Nat → Expr V₂ L₂ rs}
    (hk : ∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ lws₁ lws₂ a₁ a₂ b,
      ListRel (ArgRel G' i64) lws₁ lws₂ → ArgRel G' i64 a₁ a₂ → Wf G' D (k₁ lws₁ a₁ b) (k₂ lws₂ a₂ b)) :
    Wf G D (pushLeafWord64 w leaf₁ ws₁ acc₁ accBits k₁) (pushLeafWord64 w leaf₂ ws₂ acc₂ accBits k₂) := by
  simp only [pushLeafWord64]
  split
  · exact hk (fun _ h => h) _ _ _ _ _ hws hacc
  · split
    · split
      · exact hk (fun _ h => h) _ _ _ _ _ (hws.append (.cons hl .nil)) (.imm _)
      · exact hk (fun _ h => h) _ _ _ _ _ hws hl
    · refine .let_ (.mk (.shl i64) (.cons hl (.cons (.imm _) .nil))) fun sh₁ sh₂ => ?_
      have h1 : ∀ p ∈ G, p ∈ ⟨i64, sh₁.1, sh₂.1⟩ :: G := fun _ hp => List.mem_cons_of_mem _ hp
      refine .let_ (.mk (.or i64) (.cons (hacc.weaken h1) (.cons (.var List.mem_cons_self) .nil)))
        fun lw₁ lw₂ => ?_
      have h2 : ∀ p ∈ ⟨i64, sh₁.1, sh₂.1⟩ :: G, p ∈ ⟨i64, lw₁.1, lw₂.1⟩ :: ⟨i64, sh₁.1, sh₂.1⟩ :: G :=
        fun _ hp => List.mem_cons_of_mem _ hp
      have hs := sub_trans h1 h2
      have hlw : ArgRel (⟨i64, lw₁.1, lw₂.1⟩ :: ⟨i64, sh₁.1, sh₂.1⟩ :: G) i64 (.var lw₁.1) (.var lw₂.1) :=
        .var List.mem_cons_self
      split
      · exact hk hs _ _ _ _ _ (listRel_weaken hs hws) hlw
      · split
        · exact hk hs _ _ _ _ _ ((listRel_weaken hs hws).append (.cons hlw .nil)) (.imm _)
        · exact Wf.let2 _ (hl.weaken hs) (.imm _) fun h3 hi₁ hi₂ hhi =>
            have hs2 := sub_trans hs h3
            hk hs2 _ _ _ _ _ ((listRel_weaken hs2 hws).append (.cons (hlw.weaken h3) .nil)) hhi

theorem packLeavesToWords64_go_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty} :
    ∀ (u : Ty) {G : Ctx V₁ V₂} {D : Ctx L₁ L₂}
      {xs₁ : Tup (Arg V₁) (target.leafTys u)} {xs₂ : Tup (Arg V₂) (target.leafTys u)},
      TRel (ArgRel G) xs₁ xs₂ →
      ∀ {ws₁ : List (Arg V₁ i64)} {ws₂ : List (Arg V₂ i64)},
      ListRel (ArgRel G i64) ws₁ ws₂ →
      ∀ {acc₁ : Arg V₁ i64} {acc₂ : Arg V₂ i64}, ArgRel G i64 acc₁ acc₂ →
      ∀ (accBits : Nat)
        {k₁ : List (Arg V₁ i64) → Arg V₁ i64 → Nat → Expr V₁ L₁ rs}
        {k₂ : List (Arg V₂ i64) → Arg V₂ i64 → Nat → Expr V₂ L₂ rs},
      (∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ lws₁ lws₂ a₁ a₂ b,
        ListRel (ArgRel G' i64) lws₁ lws₂ → ArgRel G' i64 a₁ a₂ → Wf G' D (k₁ lws₁ a₁ b) (k₂ lws₂ a₂ b)) →
      Wf G D (packLeavesToWords64.go target u xs₁ ws₁ acc₁ accBits k₁)
             (packLeavesToWords64.go target u xs₂ ws₂ acc₂ accBits k₂)
  | .bool, _, _, xs₁, xs₂, hxs, _, _, hws, _, _, hacc, _, _, _, hk => by
    rcases xs₁ with ⟨x₁, ⟨⟩⟩; rcases xs₂ with ⟨x₂, ⟨⟩⟩
    cases hxs with | cons hx _ =>
    exact Wf.let1 _ hx fun h1 w₁ w₂ hw =>
      pushLeafWord64_wf 1 hw (listRel_weaken h1 hws) (hacc.weaken h1) _
        fun h2 lws₁ lws₂ a₁ a₂ b hl ha => hk (sub_trans h1 h2) lws₁ lws₂ a₁ a₂ b hl ha
  | .bits n, _, _, xs₁, xs₂, hxs, _, _, hws, _, _, hacc, _, _, _, hk => by
    rcases xs₁ with ⟨x₁, ⟨⟩⟩; rcases xs₂ with ⟨x₂, ⟨⟩⟩
    cases hxs with | cons hx _ =>
    simp only [packLeavesToWords64.go]
    split
    · exact hk (fun _ h => h) _ _ _ _ _ hws hacc
    · split
      · next h => exact pushLeafWord64_wf (min n 64) (castArgBits_rel h hx) hws hacc _ hk
      · split
        · exact Wf.let1 _ hx fun h1 w₁ w₂ hw =>
            pushLeafWord64_wf n hw (listRel_weaken h1 hws) (hacc.weaken h1) _
              fun h2 lws₁ lws₂ a₁ a₂ b hl ha => hk (sub_trans h1 h2) lws₁ lws₂ a₁ a₂ b hl ha
        · exact Wf.let1 _ hx fun h1 w₁ w₂ hw =>
            pushLeafWord64_wf (min n 64) hw (listRel_weaken h1 hws) (hacc.weaken h1) _
              fun h2 lws₁ lws₂ a₁ a₂ b hl ha => hk (sub_trans h1 h2) lws₁ lws₂ a₁ a₂ b hl ha
  | .float f, G, _, xs₁, xs₂, hxs, _, _, hws, _, _, hacc, _, _, _, hk => by
    rcases xs₁ with ⟨x₁, ⟨⟩⟩; rcases xs₂ with ⟨x₂, ⟨⟩⟩
    cases hxs with | cons hx _ =>
    simp only [packLeavesToWords64.go]
    refine .let_ (.mk (.bitcast (.float f) (.bits f.width) rfl) (.cons hx .nil)) fun bi₁ bi₂ => ?_
    have h1 : ∀ p ∈ G, p ∈ ⟨.bits f.width, bi₁.fst, bi₂.fst⟩ :: G := fun _ hp => List.mem_cons_of_mem _ hp
    have hbi : ArgRel (⟨.bits f.width, bi₁.fst, bi₂.fst⟩ :: G) (.bits f.width) (.var bi₁.fst) (.var bi₂.fst) :=
      .var List.mem_cons_self
    split
    · next h =>
      exact pushLeafWord64_wf 64 (castArgBits_rel h hbi) (listRel_weaken h1 hws) (hacc.weaken h1) _
        fun h2 lws₁ lws₂ a₁ a₂ b hl ha => hk (sub_trans h1 h2) lws₁ lws₂ a₁ a₂ b hl ha
    · split <;> exact Wf.let1 _ hbi fun h2 w₁ w₂ hw =>
        have hs := sub_trans h1 h2
        pushLeafWord64_wf _ hw (listRel_weaken hs hws) (hacc.weaken hs) _
          fun h3 lws₁ lws₂ a₁ a₂ b hl ha => hk (sub_trans hs h3) lws₁ lws₂ a₁ a₂ b hl ha
  | .pair a b, _, _, xs₁, xs₂, hxs, _, _, hws, _, _, hacc, _, _, _, hk => by
    simp only [packLeavesToWords64.go]
    obtain ⟨ha, hb⟩ := TRel_tupSplit hxs
    refine packLeavesToWords64_go_wf a ha hws hacc _ fun h1 ws1' ws2' a1' a2' b1 hws1 hacc1 => ?_
    exact packLeavesToWords64_go_wf b (TRel_argRel_weaken' h1 hb) hws1 hacc1 b1
      fun h2 ws''₁ ws''₂ a''₁ a''₂ b2 hws2 hacc2 =>
        hk (sub_trans h1 h2) ws''₁ ws''₂ a''₁ a''₂ b2 hws2 hacc2

theorem packLeavesToWords64_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} (t : Ty)
    {xs₁ : Tup (Arg V₁) (target.leafTys t)} {xs₂ : Tup (Arg V₂) (target.leafTys t)}
    (hxs : TRel (ArgRel G) xs₁ xs₂)
    {k₁ : List (Arg V₁ i64) → Expr V₁ L₁ rs} {k₂ : List (Arg V₂ i64) → Expr V₂ L₂ rs}
    (hk : ∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ ws₁ ws₂,
      ListRel (ArgRel G' i64) ws₁ ws₂ → Wf G' D (k₁ ws₁) (k₂ ws₂)) :
    Wf G D (packLeavesToWords64 target t xs₁ k₁) (packLeavesToWords64 target t xs₂ k₂) :=
  packLeavesToWords64_go_wf target t hxs .nil (.imm _) 0 fun hG ws₁ ws₂ a₁ a₂ _ hws hacc => by
    split
    · exact hk hG ws₁ ws₂ hws
    · exact hk hG _ _ (hws.append (.cons hacc .nil))

theorem extractBitsFromWords64_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂}
    {ws₁ : List (Arg V₁ i64)} {ws₂ : List (Arg V₂ i64)}
    (hws : ListRel (ArgRel G i64) ws₁ ws₂) (off w : Nat)
    {k₁ : Arg V₁ i64 → Expr V₁ L₁ rs} {k₂ : Arg V₂ i64 → Expr V₂ L₂ rs}
    (hk : ∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂, ArgRel G' i64 y₁ y₂ → Wf G' D (k₁ y₁) (k₂ y₂)) :
    Wf G D (extractBitsFromWords64 ws₁ off w k₁) (extractBitsFromWords64 ws₂ off w k₂) := by
  simp only [extractBitsFromWords64]
  split
  · exact hk (fun _ h => h) _ _ (.imm _)
  · have hw0 := hws.getD (.imm (0#64)) (off / 64)
    have hlo : ∀ {G' : Ctx V₁ V₂} {hG' : ∀ p ∈ G, p ∈ G'} {l₁ : Arg V₁ i64} {l₂ : Arg V₂ i64},
        ArgRel G' i64 l₁ l₂ →
        Wf G' D
          (if off % 64 + w ≤ 64 then emitMaskToN w 64 l₁ k₁
           else
             let w1 := ws₁.getD (off / 64 + 1) (.imm 0#64)
             .let_ (op2 (.shl i64) w1 (.imm (BitVec.ofNat 64 (64 - off % 64)))) fun (hi, ()) =>
             .let_ (op2 (.or i64) l₁ (.var hi)) fun (comb, ()) =>
             emitMaskToN w 64 (.var comb) k₁)
          (if off % 64 + w ≤ 64 then emitMaskToN w 64 l₂ k₂
           else
             let w1 := ws₂.getD (off / 64 + 1) (.imm 0#64)
             .let_ (op2 (.shl i64) w1 (.imm (BitVec.ofNat 64 (64 - off % 64)))) fun (hi, ()) =>
             .let_ (op2 (.or i64) l₂ (.var hi)) fun (comb, ()) =>
             emitMaskToN w 64 (.var comb) k₂) := by
      intro G' hG' l₁ l₂ hl
      split
      · exact emitMaskToN_wf w 64 hl fun h2 y₁ y₂ hy => hk (sub_trans hG' h2) y₁ y₂ hy
      · have hw1 := (hws.getD (.imm (0#64)) (off / 64 + 1)).weaken hG'
        exact Wf.let2 _ hw1 (.imm _) fun h2 hi₁ hi₂ hhi =>
          Wf.let2 _ (hl.weaken h2) hhi fun h3 c₁ c₂ hc =>
            emitMaskToN_wf w 64 hc fun h4 y₁ y₂ hy =>
              hk (sub_trans hG' (sub_trans h2 (sub_trans h3 h4))) y₁ y₂ hy
    by_cases hsh : off % 64 == 0
    · simp only [hsh, ↓reduceIte]; exact hlo (hG' := fun _ h => h) hw0
    · simp only [hsh, Bool.false_eq_true, ↓reduceIte]
      exact Wf.let2 _ hw0 (.imm _) fun h1 r₁ r₂ hr => hlo (hG' := h1) hr

theorem unpackWords64ToLeaves_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty} :
    ∀ (u : Ty) {G : Ctx V₁ V₂} {D : Ctx L₁ L₂}
      {ws₁ : List (Arg V₁ i64)} {ws₂ : List (Arg V₂ i64)},
      ListRel (ArgRel G i64) ws₁ ws₂ → ∀ (off : Nat)
      {k₁ : Tup (Arg V₁) (target.leafTys u) → Expr V₁ L₁ rs}
      {k₂ : Tup (Arg V₂) (target.leafTys u) → Expr V₂ L₂ rs},
      (∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂, TRel (ArgRel G') y₁ y₂ → Wf G' D (k₁ y₁) (k₂ y₂)) →
      Wf G D (unpackWords64ToLeaves target ws₁ off u k₁) (unpackWords64ToLeaves target ws₂ off u k₂)
  | .bool, _, _, ws₁, ws₂, hws, off, k₁, k₂, hk =>
    extractBitsFromWords64_wf hws off 1 fun h1 raw₁ raw₂ hraw =>
      Wf.let2 _ hraw (.imm _) fun h2 b₁ b₂ hb =>
        hk (sub_trans h1 h2) _ _ (TRel.single hb)
  | .bits n, _, _, ws₁, ws₂, hws, off, k₁, k₂, hk => by
    simp only [unpackWords64ToLeaves]
    split
    · exact hk (fun _ h => h) _ _ (TRel.single (ArgRel.imm _))
    · refine extractBitsFromWords64_wf hws off (min n 64) fun h1 raw₁ raw₂ hraw => ?_
      split
      · next h => exact hk h1 _ _ (TRel.single (castArgBits_rel h.symm hraw))
      · split <;> exact Wf.let1 _ hraw fun h2 r₁ r₂ hr =>
          hk (sub_trans h1 h2) _ _ (TRel.single hr)
  | .float f, _, _, ws₁, ws₂, hws, off, k₁, k₂, hk => by
    simp only [unpackWords64ToLeaves]
    refine extractBitsFromWords64_wf hws off (min f.width 64) fun h1 raw₁ raw₂ hraw => ?_
    split
    · exact Wf.let1 _ hraw fun h2 r₁ r₂ hr =>
        hk (sub_trans h1 h2) _ _ (TRel.single hr)
    · split <;> exact Wf.let1 _ hraw fun h2 bi₁ bi₂ hbi =>
        Wf.let1 _ hbi fun h3 r₁ r₂ hr =>
          hk (sub_trans h1 (sub_trans h2 h3)) _ _ (TRel.single hr)
  | .pair a b, _, _, ws₁, ws₂, hws, off, k₁, k₂, hk => by
    simp only [unpackWords64ToLeaves]
    refine unpackWords64ToLeaves_wf a hws off fun h1 fa₁ fa₂ hfa => ?_
    refine unpackWords64ToLeaves_wf b (listRel_weaken h1 hws) (off + a.size) fun h2 fb₁ fb₂ hfb => ?_
    exact hk (sub_trans h1 h2) _ _ (TRel_tupAppend (TRel_argRel_weaken' h2 hfa) hfb)

theorem loadByteChunksToWords64_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {p₁ : Arg V₁ i64} {p₂ : Arg V₂ i64} :
    ∀ (cs : List Nat) {G : Ctx V₁ V₂} {D : Ctx L₁ L₂},
      ArgRel G i64 p₁ p₂ → ∀ (byteOff : Nat)
      {ws₁ : List (Arg V₁ i64)} {ws₂ : List (Arg V₂ i64)},
      ListRel (ArgRel G i64) ws₁ ws₂ →
      ∀ {acc₁ : Arg V₁ i64} {acc₂ : Arg V₂ i64}, ArgRel G i64 acc₁ acc₂ →
      ∀ (accBits : Nat)
        {k₁ : List (Arg V₁ i64) → Expr V₁ L₁ rs} {k₂ : List (Arg V₂ i64) → Expr V₂ L₂ rs},
      (∀ {G'}, (∀ q ∈ G, q ∈ G') → ∀ lws₁ lws₂, ListRel (ArgRel G' i64) lws₁ lws₂ → Wf G' D (k₁ lws₁) (k₂ lws₂)) →
      Wf G D (loadByteChunksToWords64 p₁ byteOff cs ws₁ acc₁ accBits k₁)
             (loadByteChunksToWords64 p₂ byteOff cs ws₂ acc₂ accBits k₂)
  | [], _, _, _, _, _, _, hws, _, _, hacc, _, _, _, hk => by
    simp only [loadByteChunksToWords64]
    split
    · exact hk (fun _ h => h) _ _ hws
    · exact hk (fun _ h => h) _ _ (hws.append (.cons hacc .nil))
  | c :: cs, G, D, hp, byteOff, ws₁, ws₂, hws, acc₁, acc₂, hacc, accBits, k₁, k₂, hk => by
    simp only [loadByteChunksToWords64]
    have hstep : ∀ {G' : Ctx V₁ V₂} {hG' : ∀ q ∈ G, q ∈ G'} {ap₁ : Arg V₁ i64} {ap₂ : Arg V₂ i64},
        ArgRel G' i64 ap₁ ap₂ →
        Wf G' D
          (.load (.bits (8 * c)) ap₁ fun raw =>
            let asWord (cont : Arg V₁ i64 → Expr V₁ L₁ rs) : Expr V₁ L₁ rs :=
              if h : 8 * c = 64 then cont (castArgBits h (.var raw))
              else if 8 * c < 64 then .let_ (op1 (.zext (8 * c) 64) (.var raw)) fun (z, ()) => cont (.var z)
              else .let_ (op1 (.trunc (8 * c) 64) (.var raw)) fun (z, ()) => cont (.var z)
            asWord fun wd =>
              pushLeafWord64 (min (8 * c) 64) wd ws₁ acc₁ accBits fun ws' acc' bits' =>
                loadByteChunksToWords64 p₁ (byteOff + c) cs ws' acc' bits' k₁)
          (.load (.bits (8 * c)) ap₂ fun raw =>
            let asWord (cont : Arg V₂ i64 → Expr V₂ L₂ rs) : Expr V₂ L₂ rs :=
              if h : 8 * c = 64 then cont (castArgBits h (.var raw))
              else if 8 * c < 64 then .let_ (op1 (.zext (8 * c) 64) (.var raw)) fun (z, ()) => cont (.var z)
              else .let_ (op1 (.trunc (8 * c) 64) (.var raw)) fun (z, ()) => cont (.var z)
            asWord fun wd =>
              pushLeafWord64 (min (8 * c) 64) wd ws₂ acc₂ accBits fun ws' acc' bits' =>
                loadByteChunksToWords64 p₂ (byteOff + c) cs ws' acc' bits' k₂) := by
      intro G' hG' ap₁ ap₂ hap
      refine .load (.bits (8 * c)) hap fun raw₁ raw₂ => ?_
      have h1 : ∀ p ∈ G', p ∈ ⟨.bits (8 * c), raw₁, raw₂⟩ :: G' := fun _ hp => List.mem_cons_of_mem _ hp
      have hraw : ArgRel (⟨.bits (8 * c), raw₁, raw₂⟩ :: G') (.bits (8 * c)) (.var raw₁) (.var raw₂) :=
        .var List.mem_cons_self
      have hs1 := sub_trans hG' h1
      split
      · next h64 =>
        exact pushLeafWord64_wf (min (8 * c) 64) (castArgBits_rel h64 hraw)
          (listRel_weaken hs1 hws) (hacc.weaken hs1) accBits
          fun h2 lws₁ lws₂ a₁ a₂ b hlws ha =>
            have hs2 := sub_trans hs1 h2
            loadByteChunksToWords64_wf cs (hp.weaken hs2) (byteOff + c) hlws ha b
              fun h3 rws₁ rws₂ hrws => hk (sub_trans hs2 h3) rws₁ rws₂ hrws
      · split
        · exact Wf.let1 _ hraw fun h2 wd₁ wd₂ hwd =>
            have hs2 := sub_trans hs1 h2
            pushLeafWord64_wf (min (8 * c) 64) hwd (listRel_weaken hs2 hws) (hacc.weaken hs2) accBits
              fun h3 lws₁ lws₂ a₁ a₂ b hlws ha =>
                have hs3 := sub_trans hs2 h3
                loadByteChunksToWords64_wf cs (hp.weaken hs3) (byteOff + c) hlws ha b
                  fun h4 rws₁ rws₂ hrws => hk (sub_trans hs3 h4) rws₁ rws₂ hrws
        · exact Wf.let1 _ hraw fun h2 wd₁ wd₂ hwd =>
            have hs2 := sub_trans hs1 h2
            pushLeafWord64_wf (min (8 * c) 64) hwd (listRel_weaken hs2 hws) (hacc.weaken hs2) accBits
              fun h3 lws₁ lws₂ a₁ a₂ b hlws ha =>
                have hs3 := sub_trans hs2 h3
                loadByteChunksToWords64_wf cs (hp.weaken hs3) (byteOff + c) hlws ha b
                  fun h4 rws₁ rws₂ hrws => hk (sub_trans hs3 h4) rws₁ rws₂ hrws
    by_cases h0 : byteOff == 0
    · simp only [h0, ↓reduceIte]; exact hstep (hG' := fun _ h => h) hp
    · simp only [h0, Bool.false_eq_true, ↓reduceIte]
      exact Wf.let2 _ hp (.imm _) fun h1 ap₁ ap₂ hap => hstep (hG' := h1) hap

theorem storeByteChunksFromWords64_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {p₁ : Arg V₁ i64} {p₂ : Arg V₂ i64} :
    ∀ (cs : List Nat) {G : Ctx V₁ V₂} {D : Ctx L₁ L₂}
      {ws₁ : List (Arg V₁ i64)} {ws₂ : List (Arg V₂ i64)},
      ListRel (ArgRel G i64) ws₁ ws₂ →
      ArgRel G i64 p₁ p₂ → ∀ (byteOff : Nat) {k₁ : Expr V₁ L₁ rs} {k₂ : Expr V₂ L₂ rs},
      (∀ {G'}, (∀ q ∈ G, q ∈ G') → Wf G' D k₁ k₂) →
      Wf G D (storeByteChunksFromWords64 ws₁ p₁ byteOff cs k₁)
             (storeByteChunksFromWords64 ws₂ p₂ byteOff cs k₂)
  | [], _, _, _, _, _, _, _, _, _, hk => hk (fun _ h => h)
  | c :: cs, G, D, ws₁, ws₂, hws, hp, byteOff, k₁, k₂, hk => by
    simp only [storeByteChunksFromWords64]
    refine extractBitsFromWords64_wf hws (8 * byteOff) (min (8 * c) 64) fun h1 raw₁ raw₂ hraw => ?_
    have hvalstep : ∀ {G' : Ctx V₁ V₂} {hG' : ∀ q ∈ G, q ∈ G'} {val₁ : Arg V₁ (.bits (8 * c))} {val₂ : Arg V₂ (.bits (8 * c))},
        ArgRel G' (.bits (8 * c)) val₁ val₂ →
        Wf G' D
          (let emitAddr (cont : Arg V₁ i64 → Expr V₁ L₁ rs) : Expr V₁ L₁ rs :=
             if byteOff == 0 then cont p₁
             else .let_ (op2 (.add i64) p₁ (.imm (BitVec.ofNat 64 byteOff))) fun (ap, ()) => cont (.var ap)
           emitAddr fun ap =>
             .store (t := .bits (8 * c)) val₁ ap (storeByteChunksFromWords64 ws₁ p₁ (byteOff + c) cs k₁))
          (let emitAddr (cont : Arg V₂ i64 → Expr V₂ L₂ rs) : Expr V₂ L₂ rs :=
             if byteOff == 0 then cont p₂
             else .let_ (op2 (.add i64) p₂ (.imm (BitVec.ofNat 64 byteOff))) fun (ap, ()) => cont (.var ap)
           emitAddr fun ap =>
             .store (t := .bits (8 * c)) val₂ ap (storeByteChunksFromWords64 ws₂ p₂ (byteOff + c) cs k₂)) := by
      intro G' hG' val₁ val₂ hval
      by_cases h0 : byteOff == 0
      · simp only [h0, ↓reduceIte]
        exact .store hval (hp.weaken hG')
          (storeByteChunksFromWords64_wf cs (listRel_weaken hG' hws) (hp.weaken hG') (byteOff + c)
            fun h2 => hk (sub_trans hG' h2))
      · simp only [h0, Bool.false_eq_true, ↓reduceIte]
        exact Wf.let2 _ (hp.weaken hG') (.imm _) fun h2 ap₁ ap₂ hap =>
          have hs := sub_trans hG' h2
          .store (hval.weaken h2) hap
            (storeByteChunksFromWords64_wf cs (listRel_weaken hs hws) (hp.weaken hs) (byteOff + c)
              fun h3 => hk (sub_trans hs h3))
    by_cases h64 : 8 * c = 64
    · simp only [h64, ↓reduceDIte]; exact hvalstep (hG' := h1) (castArgBits_rel h64.symm hraw)
    · by_cases hlt : 8 * c < 64
      · simp only [h64, ↓reduceDIte, hlt, ↓reduceIte]
        exact Wf.let1 _ hraw fun h2 val₁ val₂ hval => hvalstep (hG' := sub_trans h1 h2) hval
      · simp only [h64, ↓reduceDIte, hlt, ↓reduceIte]
        exact Wf.let1 _ hraw fun h2 val₁ val₂ hval => hvalstep (hG' := sub_trans h1 h2) hval

private theorem emitLoadBits_step_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    (w byteOff c : Nat) (b : Bool) {G : Ctx V₁ V₂} {D : Ctx L₁ L₂}
    {ap₁ : Arg V₁ i64} {ap₂ : Arg V₂ i64} (hap : ArgRel G i64 ap₁ ap₂)
    {c₁ : Arg V₁ (.bits w) → Expr V₁ L₁ rs} {c₂ : Arg V₂ (.bits w) → Expr V₂ L₂ rs}
    (hc : ∀ {G' : Ctx V₁ V₂}, (∀ q ∈ G, q ∈ G') → ∀ sv₁ sv₂, ArgRel G' (.bits w) sv₁ sv₂ → Wf G' D (c₁ sv₁) (c₂ sv₂)) :
    Wf G D
      (.load (.bits (8 * c)) ap₁ fun raw =>
        if h : 8 * c = w then
          if b then c₁ (castArgBits h (.var raw))
          else .let_ (op2 (.shl (.bits w)) (castArgBits h (.var raw)) (.imm (BitVec.ofNat w (8 * byteOff)))) fun s => c₁ (.var s.fst)
        else if 8 * c < w then
          .let_ (op1 (.zext (8 * c) w) (.var raw)) fun z =>
            if b then c₁ (.var z.fst)
            else .let_ (op2 (.shl (.bits w)) (.var z.fst) (.imm (BitVec.ofNat w (8 * byteOff)))) fun s => c₁ (.var s.fst)
        else
          .let_ (op1 (.trunc (8 * c) w) (.var raw)) fun z =>
            if b then c₁ (.var z.fst)
            else .let_ (op2 (.shl (.bits w)) (.var z.fst) (.imm (BitVec.ofNat w (8 * byteOff)))) fun s => c₁ (.var s.fst))
      (.load (.bits (8 * c)) ap₂ fun raw =>
        if h : 8 * c = w then
          if b then c₂ (castArgBits h (.var raw))
          else .let_ (op2 (.shl (.bits w)) (castArgBits h (.var raw)) (.imm (BitVec.ofNat w (8 * byteOff)))) fun s => c₂ (.var s.fst)
        else if 8 * c < w then
          .let_ (op1 (.zext (8 * c) w) (.var raw)) fun z =>
            if b then c₂ (.var z.fst)
            else .let_ (op2 (.shl (.bits w)) (.var z.fst) (.imm (BitVec.ofNat w (8 * byteOff)))) fun s => c₂ (.var s.fst)
        else
          .let_ (op1 (.trunc (8 * c) w) (.var raw)) fun z =>
            if b then c₂ (.var z.fst)
            else .let_ (op2 (.shl (.bits w)) (.var z.fst) (.imm (BitVec.ofNat w (8 * byteOff)))) fun s => c₂ (.var s.fst)) := by
  refine .load (.bits (8 * c)) hap fun raw₁ raw₂ => ?_
  have h1 : ∀ p ∈ G, p ∈ ⟨.bits (8 * c), raw₁, raw₂⟩ :: G := fun _ hp => List.mem_cons_of_mem _ hp
  have hraw : ArgRel (⟨.bits (8 * c), raw₁, raw₂⟩ :: G) (.bits (8 * c)) (.var raw₁) (.var raw₂) :=
    .var List.mem_cons_self
  have hafterVw : ∀ {G' : Ctx V₁ V₂}, (∀ q ∈ G, q ∈ G') → ∀ {vw₁ vw₂}, ArgRel G' (.bits w) vw₁ vw₂ →
      Wf G' D
        (if b then c₁ vw₁
         else .let_ (op2 (.shl (.bits w)) vw₁ (.imm (BitVec.ofNat w (8 * byteOff)))) fun s => c₁ (.var s.fst))
        (if b then c₂ vw₂
         else .let_ (op2 (.shl (.bits w)) vw₂ (.imm (BitVec.ofNat w (8 * byteOff)))) fun s => c₂ (.var s.fst)) := by
    intro G' hG' vw₁ vw₂ hvw
    cases b
    · exact Wf.let2 _ hvw (.imm _) fun h2 sv₁ sv₂ hsv => hc (sub_trans hG' h2) sv₁ sv₂ hsv
    · exact hc hG' vw₁ vw₂ hvw
  split
  · next heqw => exact hafterVw h1 (castArgBits_rel heqw hraw)
  · split
    · exact Wf.let1 _ hraw fun h2 vw₁ vw₂ hvw => hafterVw (sub_trans h1 h2) hvw
    · exact Wf.let1 _ hraw fun h2 vw₁ vw₂ hvw => hafterVw (sub_trans h1 h2) hvw

theorem emitLoadBits_go_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    (n w : Nat) {p₁ : Arg V₁ i64} {p₂ : Arg V₂ i64} :
    ∀ (byteOff : Nat) (cs : List Nat) {G : Ctx V₁ V₂} {D : Ctx L₁ L₂},
      ArgRel G i64 p₁ p₂ →
      ∀ {acc₁ : Option (Arg V₁ (.bits w))} {acc₂ : Option (Arg V₂ (.bits w))},
      (match acc₁, acc₂ with | none, none => True | some u₁, some u₂ => ArgRel G (.bits w) u₁ u₂ | _, _ => False) →
      ∀ {k₁ : Arg V₁ (.bits w) → Expr V₁ L₁ rs} {k₂ : Arg V₂ (.bits w) → Expr V₂ L₂ rs},
      (∀ {G'}, (∀ q ∈ G, q ∈ G') → ∀ y₁ y₂, ArgRel G' (.bits w) y₁ y₂ → Wf G' D (k₁ y₁) (k₂ y₂)) →
      Wf G D (emitLoadBits.go n w p₁ k₁ byteOff cs acc₁)
             (emitLoadBits.go n w p₂ k₂ byteOff cs acc₂)
  | _, [], _, _, _, o₁, o₂, ho, _, _, hk => by
    simp only [emitLoadBits.go]
    cases o₁ <;> cases o₂ <;> first | exact False.elim ho | exact hk (fun _ h => h) _ _ (.imm _) | exact emitMaskToN_wf n w ho hk
  | byteOff, c :: rest, G, D, hp, o₁, o₂, ho, k₁, k₂, hk => by
    cases o₁ <;> cases o₂
    · simp only [emitLoadBits.go]
      split
      · exact emitLoadBits_step_wf w byteOff c true hp fun hG' sv₁ sv₂ hsv =>
          emitLoadBits_go_wf n w (byteOff + c) rest (hp.weaken hG') (acc₁ := some sv₁) (acc₂ := some sv₂) hsv
            fun h2 y₁ y₂ hy => hk (sub_trans hG' h2) y₁ y₂ hy
      · exact Wf.let2 _ hp (.imm _) fun h1 ap₁ ap₂ hap =>
          emitLoadBits_step_wf w byteOff c false hap fun hG' sv₁ sv₂ hsv =>
            emitLoadBits_go_wf n w (byteOff + c) rest (hp.weaken (sub_trans h1 hG'))
              (acc₁ := some sv₁) (acc₂ := some sv₂) hsv
              fun h2 y₁ y₂ hy => hk (sub_trans h1 (sub_trans hG' h2)) y₁ y₂ hy
    · exact False.elim ho
    · exact False.elim ho
    · simp only [emitLoadBits.go]
      split
      · exact emitLoadBits_step_wf w byteOff c true hp fun hG' sv₁ sv₂ hsv =>
          Wf.let2 _ (ho.weaken hG') hsv fun h2 u₁ u₂ hu =>
            emitLoadBits_go_wf n w (byteOff + c) rest (hp.weaken (sub_trans hG' h2))
              (acc₁ := some u₁) (acc₂ := some u₂) hu
              fun h3 y₁ y₂ hy => hk (sub_trans hG' (sub_trans h2 h3)) y₁ y₂ hy
      · exact Wf.let2 _ hp (.imm _) fun h1 ap₁ ap₂ hap =>
          emitLoadBits_step_wf w byteOff c false hap fun hG' sv₁ sv₂ hsv =>
            Wf.let2 _ (ho.weaken (sub_trans h1 hG')) hsv fun h2 u₁ u₂ hu =>
              emitLoadBits_go_wf n w (byteOff + c) rest (hp.weaken (sub_trans h1 (sub_trans hG' h2)))
                (acc₁ := some u₁) (acc₂ := some u₂) hu
                fun h3 y₁ y₂ hy => hk (sub_trans h1 (sub_trans hG' (sub_trans h2 h3))) y₁ y₂ hy

theorem emitLoadBits_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} (ws : List Nat) (n w : Nat)
    {p₁ : Arg V₁ i64} {p₂ : Arg V₂ i64} (hp : ArgRel G i64 p₁ p₂)
    {k₁ : Arg V₁ (.bits w) → Expr V₁ L₁ rs} {k₂ : Arg V₂ (.bits w) → Expr V₂ L₂ rs}
    (hk : ∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂, ArgRel G' (.bits w) y₁ y₂ → Wf G' D (k₁ y₁) (k₂ y₂)) :
    Wf G D (emitLoadBits ws n w p₁ k₁) (emitLoadBits ws n w p₂ k₂) := by
  simp only [emitLoadBits]
  split
  · exact hk (fun _ h => h) _ _ (.imm _)
  · exact emitLoadBits_go_wf n w 0 (chunkBytes ws ((n + 7) / 8)) hp trivial hk

theorem emitStoreBits_go_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    (w : Nat) {v₁ : Arg V₁ (.bits w)} {v₂ : Arg V₂ (.bits w)} {p₁ : Arg V₁ i64} {p₂ : Arg V₂ i64} :
    ∀ (byteOff : Nat) (cs : List Nat) {G : Ctx V₁ V₂} {D : Ctx L₁ L₂},
      ArgRel G (.bits w) v₁ v₂ → ArgRel G i64 p₁ p₂ →
      {k₁ : Expr V₁ L₁ rs} → {k₂ : Expr V₂ L₂ rs} →
      (∀ {G'}, (∀ q ∈ G, q ∈ G') → Wf G' D k₁ k₂) →
      Wf G D (emitStoreBits.go w v₁ p₁ k₁ byteOff cs) (emitStoreBits.go w v₂ p₂ k₂ byteOff cs)
  | _, [], _, _, _, _, _, _, hk => hk (fun _ h => h)
  | byteOff, c :: rest, G, D, hv, hp, k₁, k₂, hk => by
    simp only [emitStoreBits.go]
    let mkAddrStore {V L} (p : Arg V i64) (v : Arg V (.bits w)) (val : Arg V (.bits (8 * c)))
        (k : Expr V L rs) : Expr V L rs :=
      if byteOff == 0 then .store val p (emitStoreBits.go w v p k (byteOff + c) rest)
      else .let_ (op2 (.add i64) p (.imm (BitVec.ofNat 64 byteOff))) fun (ap, ()) =>
        .store val (.var ap) (emitStoreBits.go w v p k (byteOff + c) rest)
    let mkStoreSv {V L} (p : Arg V i64) (v : Arg V (.bits w)) (k : Expr V L rs)
        (sv : Arg V (.bits w)) : Expr V L rs :=
      if h : 8 * c = w then mkAddrStore p v (castArgBits h.symm sv) k
      else if 8 * c < w then .let_ (op1 (.trunc w (8 * c)) sv) fun (val, ()) => mkAddrStore p v (.var val) k
      else .let_ (op1 (.zext w (8 * c)) sv) fun (val, ()) => mkAddrStore p v (.var val) k
    have hafterSv : ∀ {G' : Ctx V₁ V₂}, (∀ q ∈ G, q ∈ G') → ∀ {sv₁ : Arg V₁ (.bits w)} {sv₂ : Arg V₂ (.bits w)},
        ArgRel G' (.bits w) sv₁ sv₂ → Wf G' D (mkStoreSv p₁ v₁ k₁ sv₁) (mkStoreSv p₂ v₂ k₂ sv₂) := by
      intro G' hG' sv₁ sv₂ hsv
      have hafterVal : ∀ {G'' : Ctx V₁ V₂}, (∀ q ∈ G, q ∈ G'') →
          ∀ {val₁ : Arg V₁ (.bits (8 * c))} {val₂ : Arg V₂ (.bits (8 * c))},
          ArgRel G'' (.bits (8 * c)) val₁ val₂ →
          Wf G'' D (mkAddrStore p₁ v₁ val₁ k₁) (mkAddrStore p₂ v₂ val₂ k₂) := by
        intro G'' hG'' val₁ val₂ hval
        dsimp only [mkAddrStore]
        split
        · exact .store hval (hp.weaken hG'')
            (emitStoreBits_go_wf w (byteOff + c) rest (hv.weaken hG'') (hp.weaken hG'')
              fun h2 => hk (sub_trans hG'' h2))
        · exact Wf.let2 _ (hp.weaken hG'') (.imm _) fun h2 ap₁ ap₂ hap =>
            have hs := sub_trans hG'' h2
            .store (hval.weaken h2) hap
              (emitStoreBits_go_wf w (byteOff + c) rest (hv.weaken hs) (hp.weaken hs)
                fun h3 => hk (sub_trans hs h3))
      dsimp only [mkStoreSv]
      split
      · next heqw => exact hafterVal hG' (castArgBits_rel heqw.symm hsv)
      · split
        · exact Wf.let1 _ hsv fun h2 val₁ val₂ hval => hafterVal (sub_trans hG' h2) hval
        · exact Wf.let1 _ hsv fun h2 val₁ val₂ hval => hafterVal (sub_trans hG' h2) hval
    by_cases h0 : (byteOff == 0) = true
    · have hl := hafterSv (fun _ h => h) hv
      simp only [mkStoreSv, mkAddrStore, h0, ↓reduceIte] at hl ⊢
      exact hl
    · have hl : Wf G D
          (.let_ (op2 (.lshr (.bits w)) v₁ (.imm (BitVec.ofNat w (8 * byteOff)))) fun r =>
            mkStoreSv p₁ v₁ k₁ (.var r.fst))
          (.let_ (op2 (.lshr (.bits w)) v₂ (.imm (BitVec.ofNat w (8 * byteOff)))) fun r =>
            mkStoreSv p₂ v₂ k₂ (.var r.fst)) :=
        Wf.let2 _ hv (.imm _) fun h1 sv₁ sv₂ hsv => hafterSv h1 hsv
      simp only [mkStoreSv, mkAddrStore, h0, Bool.false_eq_true, ↓reduceIte] at hl ⊢
      exact hl

theorem emitStoreBits_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} (ws : List Nat) (n w : Nat)
    {v₁ : Arg V₁ (.bits w)} {v₂ : Arg V₂ (.bits w)} (hv : ArgRel G (.bits w) v₁ v₂)
    {p₁ : Arg V₁ i64} {p₂ : Arg V₂ i64} (hp : ArgRel G i64 p₁ p₂)
    {k₁ : Expr V₁ L₁ rs} {k₂ : Expr V₂ L₂ rs}
    (hk : ∀ {G'}, (∀ q ∈ G, q ∈ G') → Wf G' D k₁ k₂) :
    Wf G D (emitStoreBits ws n w v₁ p₁ k₁) (emitStoreBits ws n w v₂ p₂ k₂) := by
  simp only [emitStoreBits]
  split
  · exact hk (fun _ h => h)
  · exact emitStoreBits_go_wf w 0 (chunkBytes ws ((n + 7) / 8)) hv hp hk

theorem words2ToDwords4_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} {w0₁ w1₁ : Arg V₁ i64} {w0₂ w1₂ : Arg V₂ i64}
    (h0 : ArgRel G i64 w0₁ w0₂) (h1 : ArgRel G i64 w1₁ w1₂)
    {k₁ : Arg V₁ i32 → Arg V₁ i32 → Arg V₁ i32 → Arg V₁ i32 → Expr V₁ L₁ rs}
    {k₂ : Arg V₂ i32 → Arg V₂ i32 → Arg V₂ i32 → Arg V₂ i32 → Expr V₂ L₂ rs}
    (hk : ∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂,
      ArgRel G' i32 a₁ a₂ → ArgRel G' i32 b₁ b₂ → ArgRel G' i32 c₁ c₂ → ArgRel G' i32 d₁ d₂ →
      Wf G' D (k₁ a₁ b₁ c₁ d₁) (k₂ a₂ b₂ c₂ d₂)) :
    Wf G D (words2ToDwords4 w0₁ w1₁ k₁) (words2ToDwords4 w0₂ w1₂ k₂) :=
  Wf.let1 _ h0 fun s1 _ _ hd0 =>
  Wf.let2 _ (h0.weaken s1) (.imm _) fun s2 _ _ hhi0 =>
  Wf.let1 _ hhi0 fun s3 _ _ hd1 =>
  have p3 := sub_trans s1 (sub_trans s2 s3)
  Wf.let1 _ (h1.weaken p3) fun s4 _ _ hd2 =>
  have p4 := sub_trans p3 s4
  Wf.let2 _ (h1.weaken p4) (.imm _) fun s5 _ _ hhi1 =>
  Wf.let1 _ hhi1 fun s6 _ _ hd3 =>
  hk (sub_trans p4 (sub_trans s5 s6)) _ _ _ _ _ _ _ _
    (hd0.weaken (sub_trans s2 (sub_trans s3 (sub_trans s4 (sub_trans s5 s6)))))
    (hd1.weaken (sub_trans s4 (sub_trans s5 s6)))
    (hd2.weaken (sub_trans s5 s6))
    hd3

theorem dwords4ToWords2_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂}
    {d0₁ d1₁ d2₁ d3₁ : Arg V₁ i32} {d0₂ d1₂ d2₂ d3₂ : Arg V₂ i32}
    (h0 : ArgRel G i32 d0₁ d0₂) (h1 : ArgRel G i32 d1₁ d1₂)
    (h2 : ArgRel G i32 d2₁ d2₂) (h3 : ArgRel G i32 d3₁ d3₂)
    {k₁ : Arg V₁ i64 → Arg V₁ i64 → Expr V₁ L₁ rs}
    {k₂ : Arg V₂ i64 → Arg V₂ i64 → Expr V₂ L₂ rs}
    (hk : ∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ w0₁ w1₁ w0₂ w1₂,
      ArgRel G' i64 w0₁ w0₂ → ArgRel G' i64 w1₁ w1₂ → Wf G' D (k₁ w0₁ w1₁) (k₂ w0₂ w1₂)) :
    Wf G D (dwords4ToWords2 d0₁ d1₁ d2₁ d3₁ k₁) (dwords4ToWords2 d0₂ d1₂ d2₂ d3₂ k₂) :=
  Wf.let1 _ h0 fun s1 _z0₁ _z0₂ hz0 =>
  Wf.let1 _ (h1.weaken s1) fun s2 _z1₁ _z1₂ hz1 =>
  Wf.let2 _ hz1 (.imm _) fun s3 _s1₁ _s1₂ hs1 =>
  Wf.let2 _ (hz0.weaken (sub_trans s2 s3)) hs1 fun s4 _w0₁ _w0₂ hw0 =>
  have p4 := sub_trans s1 (sub_trans s2 (sub_trans s3 s4))
  Wf.let1 _ (h2.weaken p4) fun s5 _z2₁ _z2₂ hz2 =>
  Wf.let1 _ (h3.weaken (sub_trans p4 s5)) fun s6 _z3₁ _z3₂ hz3 =>
  Wf.let2 _ hz3 (.imm _) fun s7 _s3₁ _s3₂ hs3 =>
  Wf.let2 _ (hz2.weaken (sub_trans s6 s7)) hs3 fun s8 _w1₁ _w1₂ hw1 =>
  have q4 := sub_trans s5 (sub_trans s6 (sub_trans s7 s8))
  hk (sub_trans p4 q4) _ _ _ _ (hw0.weaken q4) hw1

theorem dwordToBytes4_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} {d₁ : Arg V₁ i32} {d₂ : Arg V₂ i32} (hd : ArgRel G i32 d₁ d₂)
    {k₁ : Arg V₁ i8 → Arg V₁ i8 → Arg V₁ i8 → Arg V₁ i8 → Expr V₁ L₁ rs}
    {k₂ : Arg V₂ i8 → Arg V₂ i8 → Arg V₂ i8 → Arg V₂ i8 → Expr V₂ L₂ rs}
    (hk : ∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ a₁ b₁ c₁ d₁' a₂ b₂ c₂ d₂',
      ArgRel G' i8 a₁ a₂ → ArgRel G' i8 b₁ b₂ → ArgRel G' i8 c₁ c₂ → ArgRel G' i8 d₁' d₂' →
      Wf G' D (k₁ a₁ b₁ c₁ d₁') (k₂ a₂ b₂ c₂ d₂')) :
    Wf G D (dwordToBytes4 d₁ k₁) (dwordToBytes4 d₂ k₂) :=
  Wf.let1 _ hd fun s1 _b0₁ _b0₂ hb0 =>
  Wf.let2 _ (hd.weaken s1) (.imm _) fun s2 _x1₁ _x1₂ hx1 =>
  Wf.let1 _ hx1 fun s3 _b1₁ _b1₂ hb1 =>
  have p3 := sub_trans s1 (sub_trans s2 s3)
  Wf.let2 _ (hd.weaken p3) (.imm _) fun s4 _x2₁ _x2₂ hx2 =>
  Wf.let1 _ hx2 fun s5 _b2₁ _b2₂ hb2 =>
  have p5 := sub_trans p3 (sub_trans s4 s5)
  Wf.let2 _ (hd.weaken p5) (.imm _) fun s6 _x3₁ _x3₂ hx3 =>
  Wf.let1 _ hx3 fun s7 _b3₁ _b3₂ hb3 =>
  have q1 := sub_trans s2 (sub_trans s3 (sub_trans s4 (sub_trans s5 (sub_trans s6 s7))))
  have q3 := sub_trans s4 (sub_trans s5 (sub_trans s6 s7))
  have q5 := sub_trans s6 s7
  hk (sub_trans p5 q5) _ _ _ _ _ _ _ _ (hb0.weaken q1) (hb1.weaken q3) (hb2.weaken q5) hb3

theorem bytes4ToDword_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂}
    {b0₁ b1₁ b2₁ b3₁ : Arg V₁ i8} {b0₂ b1₂ b2₂ b3₂ : Arg V₂ i8}
    (h0 : ArgRel G i8 b0₁ b0₂) (h1 : ArgRel G i8 b1₁ b1₂)
    (h2 : ArgRel G i8 b2₁ b2₂) (h3 : ArgRel G i8 b3₁ b3₂)
    {k₁ : Arg V₁ i32 → Expr V₁ L₁ rs} {k₂ : Arg V₂ i32 → Expr V₂ L₂ rs}
    (hk : ∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ r₁ r₂, ArgRel G' i32 r₁ r₂ → Wf G' D (k₁ r₁) (k₂ r₂)) :
    Wf G D (bytes4ToDword b0₁ b1₁ b2₁ b3₁ k₁) (bytes4ToDword b0₂ b1₂ b2₂ b3₂ k₂) :=
  Wf.let1 _ h0 fun s1 _z0₁ _z0₂ hz0 =>
  Wf.let1 _ (h1.weaken s1) fun s2 _z1₁ _z1₂ hz1 =>
  Wf.let2 _ hz1 (.imm _) fun s3 _sh1₁ _sh1₂ hsh1 =>
  Wf.let2 _ (hz0.weaken (sub_trans s2 s3)) hsh1 fun s4 _o1₁ _o1₂ ho1 =>
  have p4 := sub_trans s1 (sub_trans s2 (sub_trans s3 s4))
  Wf.let1 _ (h2.weaken p4) fun s5 _z2₁ _z2₂ hz2 =>
  Wf.let2 _ hz2 (.imm _) fun s6 _sh2₁ _sh2₂ hsh2 =>
  Wf.let2 _ (ho1.weaken (sub_trans s5 s6)) hsh2 fun s7 _o2₁ _o2₂ ho2 =>
  have p7 := sub_trans p4 (sub_trans s5 (sub_trans s6 s7))
  Wf.let1 _ (h3.weaken p7) fun s8 _z3₁ _z3₂ hz3 =>
  Wf.let2 _ hz3 (.imm _) fun s9 _sh3₁ _sh3₂ hsh3 =>
  Wf.let2 _ (ho2.weaken (sub_trans s8 s9)) hsh3 fun s10 r₁ r₂ hr =>
  hk (sub_trans p7 (sub_trans s8 (sub_trans s9 s10))) r₁ r₂ hr

theorem dwords4ToBytes16_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂}
    {d0₁ d1₁ d2₁ d3₁ : Arg V₁ i32} {d0₂ d1₂ d2₂ d3₂ : Arg V₂ i32}
    (h0 : ArgRel G i32 d0₁ d0₂) (h1 : ArgRel G i32 d1₁ d1₂)
    (h2 : ArgRel G i32 d2₁ d2₂) (h3 : ArgRel G i32 d3₁ d3₂)
    {k₁ : List (Arg V₁ i8) → Expr V₁ L₁ rs} {k₂ : List (Arg V₂ i8) → Expr V₂ L₂ rs}
    (hk : ∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ bs₁ bs₂, ListRel (ArgRel G' i8) bs₁ bs₂ → Wf G' D (k₁ bs₁) (k₂ bs₂)) :
    Wf G D (dwords4ToBytes16 d0₁ d1₁ d2₁ d3₁ k₁) (dwords4ToBytes16 d0₂ d1₂ d2₂ d3₂ k₂) :=
  dwordToBytes4_wf h0 fun hG0 _b0₁ _b1₁ _b2₁ _b3₁ _b0₂ _b1₂ _b2₂ _b3₂ hb0 hb1 hb2 hb3 =>
  dwordToBytes4_wf (h1.weaken hG0) fun hG1 _b4₁ _b5₁ _b6₁ _b7₁ _b4₂ _b5₂ _b6₂ _b7₂ hb4 hb5 hb6 hb7 =>
  have s1 := sub_trans hG0 hG1
  dwordToBytes4_wf (h2.weaken s1) fun hG2 _b8₁ _b9₁ _b10₁ _b11₁ _b8₂ _b9₂ _b10₂ _b11₂ hb8 hb9 hb10 hb11 =>
  have s2 := sub_trans s1 hG2
  dwordToBytes4_wf (h3.weaken s2) fun hG3 _b12₁ _b13₁ _b14₁ _b15₁ _b12₂ _b13₂ _b14₂ _b15₂ hb12 hb13 hb14 hb15 =>
    have hs3 := sub_trans hG1 (sub_trans hG2 hG3)
    have hs2 := sub_trans hG2 hG3
    hk (sub_trans s2 hG3) _ _
      (.cons (hb0.weaken hs3) (.cons (hb1.weaken hs3) (.cons (hb2.weaken hs3) (.cons (hb3.weaken hs3)
      (.cons (hb4.weaken hs2) (.cons (hb5.weaken hs2) (.cons (hb6.weaken hs2) (.cons (hb7.weaken hs2)
      (.cons (hb8.weaken hG3) (.cons (hb9.weaken hG3) (.cons (hb10.weaken hG3) (.cons (hb11.weaken hG3)
      (.cons hb12 (.cons hb13 (.cons hb14 (.cons hb15 .nil))))))))))))))))

theorem bytes16ToDwords4_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂}
    {bs₁ : List (Arg V₁ i8)} {bs₂ : List (Arg V₂ i8)}
    (hbs : ListRel (ArgRel G i8) bs₁ bs₂)
    {k₁ : Arg V₁ i32 → Arg V₁ i32 → Arg V₁ i32 → Arg V₁ i32 → Expr V₁ L₁ rs}
    {k₂ : Arg V₂ i32 → Arg V₂ i32 → Arg V₂ i32 → Arg V₂ i32 → Expr V₂ L₂ rs}
    (hk : ∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂,
      ArgRel G' i32 a₁ a₂ → ArgRel G' i32 b₁ b₂ → ArgRel G' i32 c₁ c₂ → ArgRel G' i32 d₁ d₂ →
      Wf G' D (k₁ a₁ b₁ c₁ d₁) (k₂ a₂ b₂ c₂ d₂)) :
    Wf G D (bytes16ToDwords4 bs₁ k₁) (bytes16ToDwords4 bs₂ k₂) :=
  let himm : ArgRel G i8 (.imm (0#8)) (.imm (0#8)) := .imm _
  bytes4ToDword_wf (hbs.getD himm 0) (hbs.getD himm 1)
    (hbs.getD himm 2) (hbs.getD himm 3) fun hG0 _d0₁ _d0₂ hd0 =>
  bytes4ToDword_wf ((hbs.getD himm 4).weaken hG0) ((hbs.getD himm 5).weaken hG0)
    ((hbs.getD himm 6).weaken hG0) ((hbs.getD himm 7).weaken hG0) fun hG1 _d1₁ _d1₂ hd1 =>
  have s1 := sub_trans hG0 hG1
  bytes4ToDword_wf ((hbs.getD himm 8).weaken s1) ((hbs.getD himm 9).weaken s1)
    ((hbs.getD himm 10).weaken s1) ((hbs.getD himm 11).weaken s1) fun hG2 _d2₁ _d2₂ hd2 =>
  have s2 := sub_trans s1 hG2
  bytes4ToDword_wf ((hbs.getD himm 12).weaken s2) ((hbs.getD himm 13).weaken s2)
    ((hbs.getD himm 14).weaken s2) ((hbs.getD himm 15).weaken s2) fun hG3 _d3₁ _d3₂ hd3 =>
  hk (sub_trans s2 hG3) _ _ _ _ _ _ _ _
    (hd0.weaken (sub_trans hG1 (sub_trans hG2 hG3)))
    (hd1.weaken (sub_trans hG2 hG3))
    (hd2.weaken hG3) hd3

theorem scalarBlendwLane_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} (imm : BitVec 8) (idx : Nat)
    {ai₁ bi₁ : Arg V₁ i32} {ai₂ bi₂ : Arg V₂ i32}
    (hai : ArgRel G i32 ai₁ ai₂) (hbi : ArgRel G i32 bi₁ bi₂)
    {k₁ : Arg V₁ i32 → Expr V₁ L₁ rs} {k₂ : Arg V₂ i32 → Expr V₂ L₂ rs}
    (hk : ∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ r₁ r₂, ArgRel G' i32 r₁ r₂ → Wf G' D (k₁ r₁) (k₂ r₂)) :
    Wf G D (scalarBlendwLane imm idx ai₁ bi₁ k₁) (scalarBlendwLane imm idx ai₂ bi₂ k₂) := by
  cases hlo : imm.getLsbD (2 * idx) <;> cases hhi : imm.getLsbD (2 * idx + 1) <;>
    simp only [scalarBlendwLane, hlo, hhi]
  · exact hk (fun _ p => p) _ _ hai
  · exact Wf.let2 _ hai (.imm _) fun h1 am₁ am₂ ham =>
      Wf.let2 _ (hbi.weaken h1) (.imm _) fun h2 bm₁ bm₂ hbm =>
        Wf.let2 _ (ham.weaken h2) hbm fun h3 r₁ r₂ hr =>
          hk (sub_trans h1 (sub_trans h2 h3)) r₁ r₂ hr
  · exact Wf.let2 _ hai (.imm _) fun h1 am₁ am₂ ham =>
      Wf.let2 _ (hbi.weaken h1) (.imm _) fun h2 bm₁ bm₂ hbm =>
        Wf.let2 _ (ham.weaken h2) hbm fun h3 r₁ r₂ hr =>
          hk (sub_trans h1 (sub_trans h2 h3)) r₁ r₂ hr
  · exact hk (fun _ p => p) _ _ hbi

theorem scalarBlendw128_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} (imm : BitVec 8)
    {a0₁ a1₁ a2₁ a3₁ b0₁ b1₁ b2₁ b3₁ : Arg V₁ i32}
    {a0₂ a1₂ a2₂ a3₂ b0₂ b1₂ b2₂ b3₂ : Arg V₂ i32}
    (ha0 : ArgRel G i32 a0₁ a0₂) (ha1 : ArgRel G i32 a1₁ a1₂)
    (ha2 : ArgRel G i32 a2₁ a2₂) (ha3 : ArgRel G i32 a3₁ a3₂)
    (hb0 : ArgRel G i32 b0₁ b0₂) (hb1 : ArgRel G i32 b1₁ b1₂)
    (hb2 : ArgRel G i32 b2₁ b2₂) (hb3 : ArgRel G i32 b3₁ b3₂)
    {k₁ : Arg V₁ i32 → Arg V₁ i32 → Arg V₁ i32 → Arg V₁ i32 → Expr V₁ L₁ rs}
    {k₂ : Arg V₂ i32 → Arg V₂ i32 → Arg V₂ i32 → Arg V₂ i32 → Expr V₂ L₂ rs}
    (hk : ∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ r0₁ r1₁ r2₁ r3₁ r0₂ r1₂ r2₂ r3₂,
      ArgRel G' i32 r0₁ r0₂ → ArgRel G' i32 r1₁ r1₂ → ArgRel G' i32 r2₁ r2₂ → ArgRel G' i32 r3₁ r3₂ →
      Wf G' D (k₁ r0₁ r1₁ r2₁ r3₁) (k₂ r0₂ r1₂ r2₂ r3₂)) :
    Wf G D (scalarBlendw128 imm a0₁ a1₁ a2₁ a3₁ b0₁ b1₁ b2₁ b3₁ k₁)
           (scalarBlendw128 imm a0₂ a1₂ a2₂ a3₂ b0₂ b1₂ b2₂ b3₂ k₂) :=
  scalarBlendwLane_wf imm 0 ha0 hb0 fun hG0 _r0₁ _r0₂ hr0 =>
  scalarBlendwLane_wf imm 1 (ha1.weaken hG0) (hb1.weaken hG0) fun hG1 _r1₁ _r1₂ hr1 =>
  have s1 := sub_trans hG0 hG1
  scalarBlendwLane_wf imm 2 (ha2.weaken s1) (hb2.weaken s1) fun hG2 _r2₁ _r2₂ hr2 =>
  have s2 := sub_trans s1 hG2
  scalarBlendwLane_wf imm 3 (ha3.weaken s2) (hb3.weaken s2) fun hG3 _r3₁ _r3₂ hr3 =>
  hk (sub_trans s2 hG3) _ _ _ _ _ _ _ _
    (hr0.weaken (sub_trans hG1 (sub_trans hG2 hG3)))
    (hr1.weaken (sub_trans hG2 hG3))
    (hr2.weaken hG3) hr3

theorem scalarAlignr128_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} (imm : BitVec 8)
    {h0₁ h1₁ h2₁ h3₁ l0₁ l1₁ l2₁ l3₁ : Arg V₁ i32}
    {h0₂ h1₂ h2₂ h3₂ l0₂ l1₂ l2₂ l3₂ : Arg V₂ i32}
    (hh0 : ArgRel G i32 h0₁ h0₂) (hh1 : ArgRel G i32 h1₁ h1₂)
    (hh2 : ArgRel G i32 h2₁ h2₂) (hh3 : ArgRel G i32 h3₁ h3₂)
    (hl0 : ArgRel G i32 l0₁ l0₂) (hl1 : ArgRel G i32 l1₁ l1₂)
    (hl2 : ArgRel G i32 l2₁ l2₂) (hl3 : ArgRel G i32 l3₁ l3₂)
    {k₁ : Arg V₁ i32 → Arg V₁ i32 → Arg V₁ i32 → Arg V₁ i32 → Expr V₁ L₁ rs}
    {k₂ : Arg V₂ i32 → Arg V₂ i32 → Arg V₂ i32 → Arg V₂ i32 → Expr V₂ L₂ rs}
    (hk : ∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ r0₁ r1₁ r2₁ r3₁ r0₂ r1₂ r2₂ r3₂,
      ArgRel G' i32 r0₁ r0₂ → ArgRel G' i32 r1₁ r1₂ → ArgRel G' i32 r2₁ r2₂ → ArgRel G' i32 r3₁ r3₂ →
      Wf G' D (k₁ r0₁ r1₁ r2₁ r3₁) (k₂ r0₂ r1₂ r2₂ r3₂)) :
    Wf G D (scalarAlignr128 imm h0₁ h1₁ h2₁ h3₁ l0₁ l1₁ l2₁ l3₁ k₁)
           (scalarAlignr128 imm h0₂ h1₂ h2₂ h3₂ l0₂ l1₂ l2₂ l3₂ k₂) := by
  refine dwords4ToBytes16_wf hl0 hl1 hl2 hl3 fun hG1 lbs₁ lbs₂ hlbs => ?_
  refine dwords4ToBytes16_wf (hh0.weaken hG1) (hh1.weaken hG1) (hh2.weaken hG1) (hh3.weaken hG1)
    fun hG2 hbs₁ hbs₂ hhbs => ?_
  have hout : ListRel (ArgRel _ i8)
      ((List.range 16).map fun i =>
        let j := i + imm.toNat
        if j < 16 then lbs₁.getD j (.imm 0#8)
        else if j < 32 then hbs₁.getD (j - 16) (.imm 0#8) else .imm 0#8)
      ((List.range 16).map fun i =>
        let j := i + imm.toNat
        if j < 16 then lbs₂.getD j (.imm 0#8)
        else if j < 32 then hbs₂.getD (j - 16) (.imm 0#8) else .imm 0#8) :=
    ListRel.of_map (fun i => by
      dsimp only
      split
      · exact (hlbs.getD (.imm (0#8)) (i + imm.toNat)).weaken hG2
      · split
        · exact hhbs.getD (.imm (0#8)) (i + imm.toNat - 16)
        · exact .imm _) (List.range 16)
  exact bytes16ToDwords4_wf hout fun hG3 r0₁ r1₁ r2₁ r3₁ r0₂ r1₂ r2₂ r3₂ hr0 hr1 hr2 hr3 =>
    hk (sub_trans hG1 (sub_trans hG2 hG3)) _ _ _ _ _ _ _ _ hr0 hr1 hr2 hr3

theorem scalarShufb128_mux_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} {idx₁ : Arg V₁ i8} {idx₂ : Arg V₂ i8} (hidx : ArgRel G i8 idx₁ idx₂) :
    ∀ {bs₁ : List (Arg V₁ i8)} {bs₂ : List (Arg V₂ i8)} (_hbs : ListRel (ArgRel G i8) bs₁ bs₂)
      (j : Nat) {k₁ : Arg V₁ i8 → Expr V₁ L₁ rs} {k₂ : Arg V₂ i8 → Expr V₂ L₂ rs},
      (∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂, ArgRel G' i8 y₁ y₂ → Wf G' D (k₁ y₁) (k₂ y₂)) →
      Wf G D (scalarShufb128.muxBytes idx₁ bs₁ j k₁) (scalarShufb128.muxBytes idx₂ bs₂ j k₂)
  | [], [], .nil, _, _, _, hk => hk (fun _ p => p) _ _ (.imm _)
  | [b₁], [b₂], .cons hb .nil, _, _, _, hk => hk (fun _ p => p) b₁ b₂ hb
  | b₁ :: c₁ :: cs₁, b₂ :: c₂ :: cs₂, .cons hb (.cons hc hcs), j, k₁, k₂, hk => by
    simp only [scalarShufb128.muxBytes]
    refine scalarShufb128_mux_wf hidx (.cons hc hcs) (j + 1) fun h1 r₁ r₂ hr => ?_
    exact Wf.let2 _ (hidx.weaken h1) (.imm _) fun h2 eq₁ eq₂ heq =>
      Wf.let3 _ heq (hb.weaken (sub_trans h1 h2)) (hr.weaken h2) fun h3 res₁ res₂ hres =>
        hk (sub_trans h1 (sub_trans h2 h3)) res₁ res₂ hres

theorem scalarShufb128_doBytes_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {abs₁ mbs₁ : List (Arg V₁ i8)} {abs₂ mbs₂ : List (Arg V₂ i8)}
    {k₁ : Arg V₁ i32 → Arg V₁ i32 → Arg V₁ i32 → Arg V₁ i32 → Expr V₁ L₁ rs}
    {k₂ : Arg V₂ i32 → Arg V₂ i32 → Arg V₂ i32 → Arg V₂ i32 → Expr V₂ L₂ rs} :
    ∀ (d i : Nat), 16 - i ≤ d → ∀ {G : Ctx V₁ V₂} {D : Ctx L₁ L₂}
      {acc₁ : List (Arg V₁ i8)} {acc₂ : List (Arg V₂ i8)},
      ListRel (ArgRel G i8) abs₁ abs₂ →
      ListRel (ArgRel G i8) mbs₁ mbs₂ →
      ListRel (ArgRel G i8) acc₁ acc₂ →
      (∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ r0₁ r1₁ r2₁ r3₁ r0₂ r1₂ r2₂ r3₂,
        ArgRel G' i32 r0₁ r0₂ → ArgRel G' i32 r1₁ r1₂ → ArgRel G' i32 r2₁ r2₂ → ArgRel G' i32 r3₁ r3₂ →
        Wf G' D (k₁ r0₁ r1₁ r2₁ r3₁) (k₂ r0₂ r1₂ r2₂ r3₂)) →
      Wf G D (scalarShufb128.doBytes k₁ abs₁ mbs₁ i acc₁)
             (scalarShufb128.doBytes k₂ abs₂ mbs₂ i acc₂)
  | 0, i, hle, G, D, acc₁, acc₂, _, _, hacc, hk => by
    have hge : i ≥ 16 := by omega
    rw [scalarShufb128.doBytes, scalarShufb128.doBytes]
    simp only [hge, ↓reduceIte]
    exact bytes16ToDwords4_wf hacc hk
  | d + 1, i, hle, G, D, acc₁, acc₂, habs, hmbs, hacc, hk => by
    by_cases hge : i ≥ 16
    · rw [scalarShufb128.doBytes, scalarShufb128.doBytes]
      simp only [hge, ↓reduceIte]
      exact bytes16ToDwords4_wf hacc hk
    · rw [scalarShufb128.doBytes, scalarShufb128.doBytes]
      simp only [hge, ↓reduceIte]
      have hmb := hmbs.getD (.imm (0#8)) i
      exact Wf.let2 _ hmb (.imm _) fun h1 neg₁ neg₂ hneg =>
        Wf.let2 _ (hmb.weaken h1) (.imm _) fun h2 idx₁ idx₂ hidx =>
        have s12 := sub_trans h1 h2
        scalarShufb128_mux_wf hidx (listRel_weaken s12 habs) 0 fun h3 sel₁ sel₂ hsel =>
        have s123 := sub_trans s12 h3
        Wf.let3 _ (hneg.weaken (sub_trans h2 h3)) (.imm _) hsel fun h4 res₁ res₂ hres =>
        have s1234 := sub_trans s123 h4
        scalarShufb128_doBytes_wf d (i + 1) (by omega)
          (listRel_weaken s1234 habs) (listRel_weaken s1234 hmbs)
          ((listRel_weaken s1234 hacc).append (.cons hres .nil))
          fun h5 r0₁ r1₁ r2₁ r3₁ r0₂ r1₂ r2₂ r3₂ hr0 hr1 hr2 hr3 =>
            hk (sub_trans s1234 h5) _ _ _ _ _ _ _ _ hr0 hr1 hr2 hr3

theorem scalarShufb128_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂}
    {a0₁ a1₁ a2₁ a3₁ m0₁ m1₁ m2₁ m3₁ : Arg V₁ i32}
    {a0₂ a1₂ a2₂ a3₂ m0₂ m1₂ m2₂ m3₂ : Arg V₂ i32}
    (ha0 : ArgRel G i32 a0₁ a0₂) (ha1 : ArgRel G i32 a1₁ a1₂)
    (ha2 : ArgRel G i32 a2₁ a2₂) (ha3 : ArgRel G i32 a3₁ a3₂)
    (hm0 : ArgRel G i32 m0₁ m0₂) (hm1 : ArgRel G i32 m1₁ m1₂)
    (hm2 : ArgRel G i32 m2₁ m2₂) (hm3 : ArgRel G i32 m3₁ m3₂)
    {k₁ : Arg V₁ i32 → Arg V₁ i32 → Arg V₁ i32 → Arg V₁ i32 → Expr V₁ L₁ rs}
    {k₂ : Arg V₂ i32 → Arg V₂ i32 → Arg V₂ i32 → Arg V₂ i32 → Expr V₂ L₂ rs}
    (hk : ∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ r0₁ r1₁ r2₁ r3₁ r0₂ r1₂ r2₂ r3₂,
      ArgRel G' i32 r0₁ r0₂ → ArgRel G' i32 r1₁ r1₂ → ArgRel G' i32 r2₁ r2₂ → ArgRel G' i32 r3₁ r3₂ →
      Wf G' D (k₁ r0₁ r1₁ r2₁ r3₁) (k₂ r0₂ r1₂ r2₂ r3₂)) :
    Wf G D (scalarShufb128 a0₁ a1₁ a2₁ a3₁ m0₁ m1₁ m2₁ m3₁ k₁)
           (scalarShufb128 a0₂ a1₂ a2₂ a3₂ m0₂ m1₂ m2₂ m3₂ k₂) :=
  dwords4ToBytes16_wf ha0 ha1 ha2 ha3 fun h1 _abs₁ _abs₂ habs =>
  dwords4ToBytes16_wf (hm0.weaken h1) (hm1.weaken h1) (hm2.weaken h1) (hm3.weaken h1)
    fun h2 _mbs₁ _mbs₂ hmbs =>
      scalarShufb128_doBytes_wf 16 0 (Nat.le_refl _) (listRel_weaken h2 habs) hmbs .nil
        fun h3 _r0₁ _r1₁ _r2₁ _r3₁ _r0₂ _r1₂ _r2₂ _r3₂ hr0 hr1 hr2 hr3 =>
          hk (sub_trans h1 (sub_trans h2 h3)) _ _ _ _ _ _ _ _ hr0 hr1 hr2 hr3

section Sha256Wf

theorem emitRotr32_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} {x₁ : Arg V₁ i32} {x₂ : Arg V₂ i32} (hx : ArgRel G i32 x₁ x₂)
    (n : Nat) {k₁ : Arg V₁ i32 → Expr V₁ L₁ rs} {k₂ : Arg V₂ i32 → Expr V₂ L₂ rs}
    (hk : ∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ r₁ r₂, ArgRel G' i32 r₁ r₂ → Wf G' D (k₁ r₁) (k₂ r₂)) :
    Wf G D (emitRotr32 x₁ n k₁) (emitRotr32 x₂ n k₂) :=
  Wf.let2 _ hx (.imm _) hk

theorem emitLshr32_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} {x₁ : Arg V₁ i32} {x₂ : Arg V₂ i32} (hx : ArgRel G i32 x₁ x₂)
    (n : Nat) {k₁ : Arg V₁ i32 → Expr V₁ L₁ rs} {k₂ : Arg V₂ i32 → Expr V₂ L₂ rs}
    (hk : ∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ r₁ r₂, ArgRel G' i32 r₁ r₂ → Wf G' D (k₁ r₁) (k₂ r₂)) :
    Wf G D (emitLshr32 x₁ n k₁) (emitLshr32 x₂ n k₂) :=
  Wf.let2 _ hx (.imm _) hk

theorem emitXor32_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} {a₁ b₁ : Arg V₁ i32} {a₂ b₂ : Arg V₂ i32}
    (ha : ArgRel G i32 a₁ a₂) (hb : ArgRel G i32 b₁ b₂)
    {k₁ : Arg V₁ i32 → Expr V₁ L₁ rs} {k₂ : Arg V₂ i32 → Expr V₂ L₂ rs}
    (hk : ∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ r₁ r₂, ArgRel G' i32 r₁ r₂ → Wf G' D (k₁ r₁) (k₂ r₂)) :
    Wf G D (emitXor32 a₁ b₁ k₁) (emitXor32 a₂ b₂ k₂) :=
  Wf.let2 _ ha hb hk

theorem emitAdd32_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} {a₁ b₁ : Arg V₁ i32} {a₂ b₂ : Arg V₂ i32}
    (ha : ArgRel G i32 a₁ a₂) (hb : ArgRel G i32 b₁ b₂)
    {k₁ : Arg V₁ i32 → Expr V₁ L₁ rs} {k₂ : Arg V₂ i32 → Expr V₂ L₂ rs}
    (hk : ∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ r₁ r₂, ArgRel G' i32 r₁ r₂ → Wf G' D (k₁ r₁) (k₂ r₂)) :
    Wf G D (emitAdd32 a₁ b₁ k₁) (emitAdd32 a₂ b₂ k₂) :=
  Wf.let2 _ ha hb hk

theorem emitAnd32_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} {a₁ b₁ : Arg V₁ i32} {a₂ b₂ : Arg V₂ i32}
    (ha : ArgRel G i32 a₁ a₂) (hb : ArgRel G i32 b₁ b₂)
    {k₁ : Arg V₁ i32 → Expr V₁ L₁ rs} {k₂ : Arg V₂ i32 → Expr V₂ L₂ rs}
    (hk : ∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ r₁ r₂, ArgRel G' i32 r₁ r₂ → Wf G' D (k₁ r₁) (k₂ r₂)) :
    Wf G D (emitAnd32 a₁ b₁ k₁) (emitAnd32 a₂ b₂ k₂) :=
  Wf.let2 _ ha hb hk

theorem emitNot32_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} {a₁ : Arg V₁ i32} {a₂ : Arg V₂ i32} (ha : ArgRel G i32 a₁ a₂)
    {k₁ : Arg V₁ i32 → Expr V₁ L₁ rs} {k₂ : Arg V₂ i32 → Expr V₂ L₂ rs}
    (hk : ∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ r₁ r₂, ArgRel G' i32 r₁ r₂ → Wf G' D (k₁ r₁) (k₂ r₂)) :
    Wf G D (emitNot32 a₁ k₁) (emitNot32 a₂ k₂) :=
  Wf.let1 _ ha hk

theorem emitShaSigma0_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} {x₁ : Arg V₁ i32} {x₂ : Arg V₂ i32} (hx : ArgRel G i32 x₁ x₂)
    {k₁ : Arg V₁ i32 → Expr V₁ L₁ rs} {k₂ : Arg V₂ i32 → Expr V₂ L₂ rs}
    (hk : ∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ r₁ r₂, ArgRel G' i32 r₁ r₂ → Wf G' D (k₁ r₁) (k₂ r₂)) :
    Wf G D (emitShaSigma0 x₁ k₁) (emitShaSigma0 x₂ k₂) :=
  emitRotr32_wf hx 2 fun h0 _r2₁ _r2₂ h2 =>
  emitRotr32_wf (hx.weaken h0) 13 fun h1 _r13₁ _r13₂ h13 =>
  have s1 := sub_trans h0 h1
  emitRotr32_wf (hx.weaken s1) 22 fun h2' _r22₁ _r22₂ h22 =>
  have s2 := sub_trans s1 h2'
  emitXor32_wf (h2.weaken (sub_trans h1 h2')) (h13.weaken h2') fun h3 _t₁ _t₂ ht =>
  emitXor32_wf ht (h22.weaken h3) fun h4 r₁ r₂ hr => hk (sub_trans s2 (sub_trans h3 h4)) r₁ r₂ hr

theorem emitShaSigma1_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} {x₁ : Arg V₁ i32} {x₂ : Arg V₂ i32} (hx : ArgRel G i32 x₁ x₂)
    {k₁ : Arg V₁ i32 → Expr V₁ L₁ rs} {k₂ : Arg V₂ i32 → Expr V₂ L₂ rs}
    (hk : ∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ r₁ r₂, ArgRel G' i32 r₁ r₂ → Wf G' D (k₁ r₁) (k₂ r₂)) :
    Wf G D (emitShaSigma1 x₁ k₁) (emitShaSigma1 x₂ k₂) :=
  emitRotr32_wf hx 6 fun h0 _r6₁ _r6₂ h6 =>
  emitRotr32_wf (hx.weaken h0) 11 fun h1 _r11₁ _r11₂ h11 =>
  have s1 := sub_trans h0 h1
  emitRotr32_wf (hx.weaken s1) 25 fun h2 _r25₁ _r25₂ h25 =>
  have s2 := sub_trans s1 h2
  emitXor32_wf (h6.weaken (sub_trans h1 h2)) (h11.weaken h2) fun h3 _t₁ _t₂ ht =>
  emitXor32_wf ht (h25.weaken h3) fun h4 r₁ r₂ hr => hk (sub_trans s2 (sub_trans h3 h4)) r₁ r₂ hr

theorem emitShaSig0_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} {x₁ : Arg V₁ i32} {x₂ : Arg V₂ i32} (hx : ArgRel G i32 x₁ x₂)
    {k₁ : Arg V₁ i32 → Expr V₁ L₁ rs} {k₂ : Arg V₂ i32 → Expr V₂ L₂ rs}
    (hk : ∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ r₁ r₂, ArgRel G' i32 r₁ r₂ → Wf G' D (k₁ r₁) (k₂ r₂)) :
    Wf G D (emitShaSig0 x₁ k₁) (emitShaSig0 x₂ k₂) :=
  emitRotr32_wf hx 7 fun h0 _r7₁ _r7₂ h7 =>
  emitRotr32_wf (hx.weaken h0) 18 fun h1 _r18₁ _r18₂ h18 =>
  have s1 := sub_trans h0 h1
  emitLshr32_wf (hx.weaken s1) 3 fun h2 _s3₁ _s3₂ hs3 =>
  have s2 := sub_trans s1 h2
  emitXor32_wf (h7.weaken (sub_trans h1 h2)) (h18.weaken h2) fun h3 _t₁ _t₂ ht =>
  emitXor32_wf ht (hs3.weaken h3) fun h4 r₁ r₂ hr => hk (sub_trans s2 (sub_trans h3 h4)) r₁ r₂ hr

theorem emitShaSig1_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} {x₁ : Arg V₁ i32} {x₂ : Arg V₂ i32} (hx : ArgRel G i32 x₁ x₂)
    {k₁ : Arg V₁ i32 → Expr V₁ L₁ rs} {k₂ : Arg V₂ i32 → Expr V₂ L₂ rs}
    (hk : ∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ r₁ r₂, ArgRel G' i32 r₁ r₂ → Wf G' D (k₁ r₁) (k₂ r₂)) :
    Wf G D (emitShaSig1 x₁ k₁) (emitShaSig1 x₂ k₂) :=
  emitRotr32_wf hx 17 fun h0 _r17₁ _r17₂ h17 =>
  emitRotr32_wf (hx.weaken h0) 19 fun h1 _r19₁ _r19₂ h19 =>
  have s1 := sub_trans h0 h1
  emitLshr32_wf (hx.weaken s1) 10 fun h2 _s10₁ _s10₂ hs10 =>
  have s2 := sub_trans s1 h2
  emitXor32_wf (h17.weaken (sub_trans h1 h2)) (h19.weaken h2) fun h3 _t₁ _t₂ ht =>
  emitXor32_wf ht (hs10.weaken h3) fun h4 r₁ r₂ hr => hk (sub_trans s2 (sub_trans h3 h4)) r₁ r₂ hr

theorem emitShaCh_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} {x₁ y₁ z₁ : Arg V₁ i32} {x₂ y₂ z₂ : Arg V₂ i32}
    (hx : ArgRel G i32 x₁ x₂) (hy : ArgRel G i32 y₁ y₂) (hz : ArgRel G i32 z₁ z₂)
    {k₁ : Arg V₁ i32 → Expr V₁ L₁ rs} {k₂ : Arg V₂ i32 → Expr V₂ L₂ rs}
    (hk : ∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ r₁ r₂, ArgRel G' i32 r₁ r₂ → Wf G' D (k₁ r₁) (k₂ r₂)) :
    Wf G D (emitShaCh x₁ y₁ z₁ k₁) (emitShaCh x₂ y₂ z₂ k₂) :=
  emitAnd32_wf hx hy fun h0 _xy₁ _xy₂ hxy =>
  emitNot32_wf (hx.weaken h0) fun h1 _nx₁ _nx₂ hnx =>
  have s1 := sub_trans h0 h1
  emitAnd32_wf hnx (hz.weaken s1) fun h2 _nxz₁ _nxz₂ hnxz =>
  emitXor32_wf (hxy.weaken (sub_trans h1 h2)) hnxz fun h3 r₁ r₂ hr =>
    hk (sub_trans s1 (sub_trans h2 h3)) r₁ r₂ hr

theorem emitShaMaj_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} {x₁ y₁ z₁ : Arg V₁ i32} {x₂ y₂ z₂ : Arg V₂ i32}
    (hx : ArgRel G i32 x₁ x₂) (hy : ArgRel G i32 y₁ y₂) (hz : ArgRel G i32 z₁ z₂)
    {k₁ : Arg V₁ i32 → Expr V₁ L₁ rs} {k₂ : Arg V₂ i32 → Expr V₂ L₂ rs}
    (hk : ∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ r₁ r₂, ArgRel G' i32 r₁ r₂ → Wf G' D (k₁ r₁) (k₂ r₂)) :
    Wf G D (emitShaMaj x₁ y₁ z₁ k₁) (emitShaMaj x₂ y₂ z₂ k₂) :=
  emitAnd32_wf hx hy fun h0 _xy₁ _xy₂ hxy =>
  emitAnd32_wf (hx.weaken h0) (hz.weaken h0) fun h1 _xz₁ _xz₂ hxz =>
  have s1 := sub_trans h0 h1
  emitAnd32_wf (hy.weaken s1) (hz.weaken s1) fun h2 _yz₁ _yz₂ hyz =>
  have s2 := sub_trans s1 h2
  emitXor32_wf (hxy.weaken (sub_trans h1 h2)) (hxz.weaken h2) fun h3 _t₁ _t₂ ht =>
  emitXor32_wf ht (hyz.weaken h3) fun h4 r₁ r₂ hr => hk (sub_trans s2 (sub_trans h3 h4)) r₁ r₂ hr

theorem emitShaRound_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂}
    {a₁ b₁ c₁ d₁ e₁ f₁ g₁ h₁ wk₁ : Arg V₁ i32}
    {a₂ b₂ c₂ d₂ e₂ f₂ g₂ h₂ wk₂ : Arg V₂ i32}
    (ha : ArgRel G i32 a₁ a₂) (hb : ArgRel G i32 b₁ b₂) (hc : ArgRel G i32 c₁ c₂)
    (hd : ArgRel G i32 d₁ d₂) (he : ArgRel G i32 e₁ e₂) (hf : ArgRel G i32 f₁ f₂)
    (hg : ArgRel G i32 g₁ g₂) (hh : ArgRel G i32 h₁ h₂) (hwk : ArgRel G i32 wk₁ wk₂)
    {k₁ : Arg V₁ i32 → Arg V₁ i32 → Arg V₁ i32 → Arg V₁ i32 → Arg V₁ i32 → Arg V₁ i32 → Arg V₁ i32 → Arg V₁ i32 → Expr V₁ L₁ rs}
    {k₂ : Arg V₂ i32 → Arg V₂ i32 → Arg V₂ i32 → Arg V₂ i32 → Arg V₂ i32 → Arg V₂ i32 → Arg V₂ i32 → Arg V₂ i32 → Expr V₂ L₂ rs}
    (hk : ∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ x0₁ x1₁ x2₁ x3₁ x4₁ x5₁ x6₁ x7₁ x0₂ x1₂ x2₂ x3₂ x4₂ x5₂ x6₂ x7₂,
      ArgRel G' i32 x0₁ x0₂ → ArgRel G' i32 x1₁ x1₂ → ArgRel G' i32 x2₁ x2₂ → ArgRel G' i32 x3₁ x3₂ →
      ArgRel G' i32 x4₁ x4₂ → ArgRel G' i32 x5₁ x5₂ → ArgRel G' i32 x6₁ x6₂ → ArgRel G' i32 x7₁ x7₂ →
      Wf G' D (k₁ x0₁ x1₁ x2₁ x3₁ x4₁ x5₁ x6₁ x7₁) (k₂ x0₂ x1₂ x2₂ x3₂ x4₂ x5₂ x6₂ x7₂)) :
    Wf G D (emitShaRound a₁ b₁ c₁ d₁ e₁ f₁ g₁ h₁ wk₁ k₁) (emitShaRound a₂ b₂ c₂ d₂ e₂ f₂ g₂ h₂ wk₂ k₂) :=
  emitShaCh_wf he hf hg fun p0 _ch₁ _ch₂ hch =>
  emitShaSigma1_wf (he.weaken p0) fun p1 _s1₁ _s1₂ hs1 =>
  have q1 := sub_trans p0 p1
  emitAdd32_wf (hch.weaken p1) hs1 fun p2 _t1₁ _t1₂ ht1 =>
  have q2 := sub_trans q1 p2
  emitAdd32_wf ht1 (hwk.weaken q2) fun p3 _t2₁ _t2₂ ht2 =>
  have q3 := sub_trans q2 p3
  emitAdd32_wf ht2 (hh.weaken q3) fun p4 _t₁ _t₂ ht =>
  have q4 := sub_trans q3 p4
  emitShaMaj_wf (ha.weaken q4) (hb.weaken q4) (hc.weaken q4) fun p5 _maj₁ _maj₂ hmaj =>
  have q5 := sub_trans q4 p5
  emitShaSigma0_wf (ha.weaken q5) fun p6 _s0₁ _s0₂ hs0 =>
  have q6 := sub_trans q5 p6
  emitAdd32_wf (ht.weaken (sub_trans p5 p6)) (hmaj.weaken p6) fun p7 _m1₁ _m1₂ hm1 =>
  have q7 := sub_trans q6 p7
  emitAdd32_wf hm1 (hs0.weaken p7) fun p8 _a'₁ _a'₂ ha' =>
  have q8 := sub_trans q7 p8
  emitAdd32_wf (ht.weaken (sub_trans p5 (sub_trans p6 (sub_trans p7 p8)))) (hd.weaken q8) fun p9 _e'₁ _e'₂ he' =>
  have q9 := sub_trans q8 p9
  hk q9 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (ha'.weaken p9) (ha.weaken q9) (hb.weaken q9) (hc.weaken q9)
    he' (he.weaken q9) (hf.weaken q9) (hg.weaken q9)

theorem scalarSha256rnds2_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂}
    {cd0₁ cd1₁ cd2₁ cd3₁ ab0₁ ab1₁ ab2₁ ab3₁ wk0₁ wk1₁ wk2₁ wk3₁ : Arg V₁ i32}
    {cd0₂ cd1₂ cd2₂ cd3₂ ab0₂ ab1₂ ab2₂ ab3₂ wk0₂ wk1₂ wk2₂ wk3₂ : Arg V₂ i32}
    (hcd0 : ArgRel G i32 cd0₁ cd0₂) (hcd1 : ArgRel G i32 cd1₁ cd1₂)
    (hcd2 : ArgRel G i32 cd2₁ cd2₂) (hcd3 : ArgRel G i32 cd3₁ cd3₂)
    (hab0 : ArgRel G i32 ab0₁ ab0₂) (hab1 : ArgRel G i32 ab1₁ ab1₂)
    (hab2 : ArgRel G i32 ab2₁ ab2₂) (hab3 : ArgRel G i32 ab3₁ ab3₂)
    (hwk0 : ArgRel G i32 wk0₁ wk0₂) (hwk1 : ArgRel G i32 wk1₁ wk1₂)
    {k₁ : Arg V₁ i32 → Arg V₁ i32 → Arg V₁ i32 → Arg V₁ i32 → Expr V₁ L₁ rs}
    {k₂ : Arg V₂ i32 → Arg V₂ i32 → Arg V₂ i32 → Arg V₂ i32 → Expr V₂ L₂ rs}
    (hk : ∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ r0₁ r1₁ r2₁ r3₁ r0₂ r1₂ r2₂ r3₂,
      ArgRel G' i32 r0₁ r0₂ → ArgRel G' i32 r1₁ r1₂ → ArgRel G' i32 r2₁ r2₂ → ArgRel G' i32 r3₁ r3₂ →
      Wf G' D (k₁ r0₁ r1₁ r2₁ r3₁) (k₂ r0₂ r1₂ r2₂ r3₂)) :
    Wf G D (scalarSha256rnds2 cd0₁ cd1₁ cd2₁ cd3₁ ab0₁ ab1₁ ab2₁ ab3₁ wk0₁ wk1₁ wk2₁ wk3₁ k₁)
           (scalarSha256rnds2 cd0₂ cd1₂ cd2₂ cd3₂ ab0₂ ab1₂ ab2₂ ab3₂ wk0₂ wk1₂ wk2₂ wk3₂ k₂) :=
  emitShaRound_wf hab3 hab2 hcd3 hcd2 hab1 hab0 hcd1 hcd0 hwk0
    fun p0 _a1₁ _b1₁ _c1₁ _d1₁ _e1₁ _f1₁ _g1₁ _h1₁ _a1₂ _b1₂ _c1₂ _d1₂ _e1₂ _f1₂ _g1₂ _h1₂ ha1 hb1 hc1 hd1 he1 hf1 hg1 hh1 =>
  emitShaRound_wf ha1 hb1 hc1 hd1 he1 hf1 hg1 hh1 (hwk1.weaken p0)
    fun p1 _a2₁ _ _ _ _e2₁ _ _ _ _a2₂ _ _ _ _e2₂ _ _ _ ha2 _ _ _ he2 _ _ _ =>
  hk (sub_trans p0 p1) _ _ _ _ _ _ _ _
    (he1.weaken p1) he2 (ha1.weaken p1) ha2

theorem scalarSha256msg1_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂}
    {a0₁ a1₁ a2₁ a3₁ b0₁ b1₁ b2₁ b3₁ : Arg V₁ i32}
    {a0₂ a1₂ a2₂ a3₂ b0₂ b1₂ b2₂ b3₂ : Arg V₂ i32}
    (ha0 : ArgRel G i32 a0₁ a0₂) (ha1 : ArgRel G i32 a1₁ a1₂)
    (ha2 : ArgRel G i32 a2₁ a2₂) (ha3 : ArgRel G i32 a3₁ a3₂)
    (hb0 : ArgRel G i32 b0₁ b0₂)
    {k₁ : Arg V₁ i32 → Arg V₁ i32 → Arg V₁ i32 → Arg V₁ i32 → Expr V₁ L₁ rs}
    {k₂ : Arg V₂ i32 → Arg V₂ i32 → Arg V₂ i32 → Arg V₂ i32 → Expr V₂ L₂ rs}
    (hk : ∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ r0₁ r1₁ r2₁ r3₁ r0₂ r1₂ r2₂ r3₂,
      ArgRel G' i32 r0₁ r0₂ → ArgRel G' i32 r1₁ r1₂ → ArgRel G' i32 r2₁ r2₂ → ArgRel G' i32 r3₁ r3₂ →
      Wf G' D (k₁ r0₁ r1₁ r2₁ r3₁) (k₂ r0₂ r1₂ r2₂ r3₂)) :
    Wf G D (scalarSha256msg1 a0₁ a1₁ a2₁ a3₁ b0₁ b1₁ b2₁ b3₁ k₁)
           (scalarSha256msg1 a0₂ a1₂ a2₂ a3₂ b0₂ b1₂ b2₂ b3₂ k₂) :=
  emitShaSig0_wf ha1 fun p0 _s0₁ _s0₂ hs0 =>
  emitAdd32_wf (ha0.weaken p0) hs0 fun p1 _r0₁ _r0₂ hr0 =>
  have q1 := sub_trans p0 p1
  emitShaSig0_wf (ha2.weaken q1) fun p2 _s1₁ _s1₂ hs1 =>
  have q2 := sub_trans q1 p2
  emitAdd32_wf (ha1.weaken q2) hs1 fun p3 _r1₁ _r1₂ hr1 =>
  have q3 := sub_trans q2 p3
  emitShaSig0_wf (ha3.weaken q3) fun p4 _s2₁ _s2₂ hs2 =>
  have q4 := sub_trans q3 p4
  emitAdd32_wf (ha2.weaken q4) hs2 fun p5 _r2₁ _r2₂ hr2 =>
  have q5 := sub_trans q4 p5
  emitShaSig0_wf (hb0.weaken q5) fun p6 _s3₁ _s3₂ hs3 =>
  have q6 := sub_trans q5 p6
  emitAdd32_wf (ha3.weaken q6) hs3 fun p7 _r3₁ _r3₂ hr3 =>
  hk (sub_trans q6 p7) _ _ _ _ _ _ _ _
    (hr0.weaken (sub_trans p2 (sub_trans p3 (sub_trans p4 (sub_trans p5 (sub_trans p6 p7))))))
    (hr1.weaken (sub_trans p4 (sub_trans p5 (sub_trans p6 p7))))
    (hr2.weaken (sub_trans p6 p7))
    hr3

theorem scalarSha256msg2_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂}
    {s0₁ s1₁ s2₁ s3₁ w0₁ w1₁ w2₁ w3₁ : Arg V₁ i32}
    {s0₂ s1₂ s2₂ s3₂ w0₂ w1₂ w2₂ w3₂ : Arg V₂ i32}
    (hs0 : ArgRel G i32 s0₁ s0₂) (hs1 : ArgRel G i32 s1₁ s1₂)
    (hs2 : ArgRel G i32 s2₁ s2₂) (hs3 : ArgRel G i32 s3₁ s3₂)
    (hw2 : ArgRel G i32 w2₁ w2₂) (hw3 : ArgRel G i32 w3₁ w3₂)
    {k₁ : Arg V₁ i32 → Arg V₁ i32 → Arg V₁ i32 → Arg V₁ i32 → Expr V₁ L₁ rs}
    {k₂ : Arg V₂ i32 → Arg V₂ i32 → Arg V₂ i32 → Arg V₂ i32 → Expr V₂ L₂ rs}
    (hk : ∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ r0₁ r1₁ r2₁ r3₁ r0₂ r1₂ r2₂ r3₂,
      ArgRel G' i32 r0₁ r0₂ → ArgRel G' i32 r1₁ r1₂ → ArgRel G' i32 r2₁ r2₂ → ArgRel G' i32 r3₁ r3₂ →
      Wf G' D (k₁ r0₁ r1₁ r2₁ r3₁) (k₂ r0₂ r1₂ r2₂ r3₂)) :
    Wf G D (scalarSha256msg2 s0₁ s1₁ s2₁ s3₁ w0₁ w1₁ w2₁ w3₁ k₁)
           (scalarSha256msg2 s0₂ s1₂ s2₂ s3₂ w0₂ w1₂ w2₂ w3₂ k₂) :=
  emitShaSig1_wf hw2 fun p0 _sig2₁ _sig2₂ hsig2 =>
  emitAdd32_wf (hs0.weaken p0) hsig2 fun p1 _w16₁ _w16₂ hw16 =>
  have q1 := sub_trans p0 p1
  emitShaSig1_wf (hw3.weaken q1) fun p2 _sig3₁ _sig3₂ hsig3 =>
  have q2 := sub_trans q1 p2
  emitAdd32_wf (hs1.weaken q2) hsig3 fun p3 _w17₁ _w17₂ hw17 =>
  have q3 := sub_trans q2 p3
  emitShaSig1_wf (hw16.weaken (sub_trans p2 p3)) fun p4 _sig16₁ _sig16₂ hsig16 =>
  have q4 := sub_trans q3 p4
  emitAdd32_wf (hs2.weaken q4) hsig16 fun p5 _w18₁ _w18₂ hw18 =>
  have q5 := sub_trans q4 p5
  emitShaSig1_wf (hw17.weaken (sub_trans p4 p5)) fun p6 _sig17₁ _sig17₂ hsig17 =>
  have q6 := sub_trans q5 p6
  emitAdd32_wf (hs3.weaken q6) hsig17 fun p7 _w19₁ _w19₂ hw19 =>
  hk (sub_trans q6 p7) _ _ _ _ _ _ _ _
    (hw16.weaken (sub_trans p2 (sub_trans p3 (sub_trans p4 (sub_trans p5 (sub_trans p6 p7))))))
    (hw17.weaken (sub_trans p4 (sub_trans p5 (sub_trans p6 p7))))
    (hw18.weaken (sub_trans p6 p7))
    hw19

end Sha256Wf

end LegalWf

end LeanQbe.T
