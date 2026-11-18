module

public import LeanQbe.T.Legal
public import LeanQbe.T.WPLemmas
public import LeanQbe.T.FlatLemmas
import all Kraken.Mem

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

theorem legalUnaryTree_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    (mkCode : (u : Ty) → OpCode [u] [u]) (vecSupported : (u : Ty) → Bool)
    {onBool₁ : Arg V₁ .bool → (Arg V₁ .bool → Expr V₁ L₁ rs) → Expr V₁ L₁ rs}
    {onBool₂ : Arg V₂ .bool → (Arg V₂ .bool → Expr V₂ L₂ rs) → Expr V₂ L₂ rs}
    {onBits₁ : (n : Nat) → Arg V₁ (.bits (target.widenWidth n)) →
      (Arg V₁ (.bits (target.widenWidth n)) → Expr V₁ L₁ rs) → Expr V₁ L₁ rs}
    {onBits₂ : (n : Nat) → Arg V₂ (.bits (target.widenWidth n)) →
      (Arg V₂ (.bits (target.widenWidth n)) → Expr V₂ L₂ rs) → Expr V₂ L₂ rs}
    {onFloat₁ : (f : Fmt) → Arg V₁ (.float f) → (Arg V₁ (.float f) → Expr V₁ L₁ rs) → Expr V₁ L₁ rs}
    {onFloat₂ : (f : Fmt) → Arg V₂ (.float f) → (Arg V₂ (.float f) → Expr V₂ L₂ rs) → Expr V₂ L₂ rs}
    (hb : ∀ {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} {x₁ x₂ cont₁ cont₂}, ArgRel G .bool x₁ x₂ →
      (∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂, ArgRel G' .bool y₁ y₂ → Wf G' D (cont₁ y₁) (cont₂ y₂)) →
      Wf G D (onBool₁ x₁ cont₁) (onBool₂ x₂ cont₂))
    (hn : ∀ (n : Nat) {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} {x₁ x₂ cont₁ cont₂},
      ArgRel G (.bits (target.widenWidth n)) x₁ x₂ →
      (∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂, ArgRel G' (.bits (target.widenWidth n)) y₁ y₂ → Wf G' D (cont₁ y₁) (cont₂ y₂)) →
      Wf G D (onBits₁ n x₁ cont₁) (onBits₂ n x₂ cont₂))
    (hf : ∀ (f : Fmt) {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} {x₁ x₂ cont₁ cont₂},
      ArgRel G (.float f) x₁ x₂ →
      (∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂, ArgRel G' (.float f) y₁ y₂ → Wf G' D (cont₁ y₁) (cont₂ y₂)) →
      Wf G D (onFloat₁ f x₁ cont₁) (onFloat₂ f x₂ cont₂)) :
    ∀ (t : Ty) {G : Ctx V₁ V₂} {D : Ctx L₁ L₂}
      {xs₁ : Tup (Arg V₁) (target.legalTys t)} {xs₂ : Tup (Arg V₂) (target.legalTys t)},
      TRel (ArgRel G) xs₁ xs₂ →
      ∀ {k₁ : Tup (Arg V₁) (target.legalTys t) → Expr V₁ L₁ rs}
        {k₂ : Tup (Arg V₂) (target.legalTys t) → Expr V₂ L₂ rs},
      (∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂, TRel (ArgRel G') y₁ y₂ → Wf G' D (k₁ y₁) (k₂ y₂)) →
      Wf G D (legalUnaryTree target mkCode vecSupported onBool₁ onBits₁ onFloat₁ t xs₁ k₁)
             (legalUnaryTree target mkCode vecSupported onBool₂ onBits₂ onFloat₂ t xs₂ k₂)
  | .bool, _, _, xs₁, xs₂, hxs, _, _, hk => by
    rcases xs₁ with ⟨x₁, ⟨⟩⟩; rcases xs₂ with ⟨x₂, ⟨⟩⟩
    cases hxs with | cons hx _ =>
    exact hb hx fun hG' y₁ y₂ hy => hk hG' _ _ (TRel.single hy)
  | .bits n, _, _, xs₁, xs₂, hxs, _, _, hk => by
    rcases xs₁ with ⟨x₁, ⟨⟩⟩; rcases xs₂ with ⟨x₂, ⟨⟩⟩
    cases hxs with | cons hx _ =>
    exact hn n hx fun hG' y₁ y₂ hy => hk hG' _ _ (TRel.single hy)
  | .float f, _, _, xs₁, xs₂, hxs, _, _, hk => by
    rcases xs₁ with ⟨x₁, ⟨⟩⟩; rcases xs₂ with ⟨x₂, ⟨⟩⟩
    cases hxs with | cons hx _ =>
    exact hf f hx fun hG' y₁ y₂ hy => hk hG' _ _ (TRel.single hy)
  | .pair t1 t2, G, D, xs₁, xs₂, hxs, k₁, k₂, hk => by
    simp only [legalUnaryTree]
    split
    · next h =>
      obtain ⟨h1, _⟩ := TRel.cons_iff.1 (packedToTup_rel h hxs)
      split
      · exact Wf.let1 (mkCode (.pair t1 t2)) h1 fun hG' r₁ r₂ hr =>
          hk hG' _ _ (tupToPacked_rel h (.cons hr .nil))
      · refine splitLegalToLeaves_wf target (.pair t1 t2) hxs fun hG1 fx₁ fx₂ hfx => ?_
        have hgoS : ∀ (u : Ty) {G' : Ctx V₁ V₂} {fxu₁ : Tup (Arg V₁) (target.leafTys u)} {fxu₂ : Tup (Arg V₂) (target.leafTys u)},
            TRel (ArgRel G') fxu₁ fxu₂ →
            ∀ {c₁ : Tup (Arg V₁) (target.leafTys u) → Expr V₁ L₁ rs}
              {c₂ : Tup (Arg V₂) (target.leafTys u) → Expr V₂ L₂ rs},
            (∀ {G''}, (∀ p ∈ G', p ∈ G'') → ∀ y₁ y₂, TRel (ArgRel G'') y₁ y₂ → Wf G'' D (c₁ y₁) (c₂ y₂)) →
            Wf G' D
              (legalUnaryTree.goS target onBool₁ onBits₁ onFloat₁ u fxu₁ c₁)
              (legalUnaryTree.goS target onBool₂ onBits₂ onFloat₂ u fxu₂ c₂) := by
          intro u
          induction u with
          | bool =>
            intro G' (_, ()) (_, ()) hfu c₁ c₂ hc; cases hfu with | cons hu _ =>
              exact hb hu fun hG' y₁ y₂ hy => hc hG' _ _ (TRel.single hy)
          | bits n =>
            intro G' xs1 xs2 hfu c₁ c₂ hc
            rcases xs1 with ⟨u1, ⟨⟩⟩; rcases xs2 with ⟨u2, ⟨⟩⟩
            cases hfu with | cons hu _ =>
              exact hn n hu fun hG' y₁ y₂ hy => hc hG' _ _ (TRel.single hy)
          | float f =>
            intro G' (_, ()) (_, ()) hfu c₁ c₂ hc; cases hfu with | cons hu _ =>
              exact hf f hu fun hG' y₁ y₂ hy => hc hG' _ _ (TRel.single hy)
          | pair u1 u2 ih1 ih2 =>
            intro G' fxu₁ fxu₂ hfu c₁ c₂ hc
            obtain ⟨hu1, hu2⟩ := TRel_tupSplit hfu
            exact ih1 hu1 fun hGa r1₁ r1₂ hr1 =>
              ih2 (TRel_argRel_weaken' hGa hu2) fun hGb r2₁ r2₂ hr2 =>
                hc (sub_trans hGa hGb) _ _ (TRel_tupAppend (TRel_argRel_weaken' hGb hr1) hr2)
        refine hgoS (.pair t1 t2) hfx fun hG2 fr₁ fr₂ hfr =>
          packLeavesToLegal_wf target (.pair t1 t2) hfr fun hG3 y₁ y₂ hy =>
            hk (sub_trans hG1 (sub_trans hG2 hG3)) y₁ y₂ hy
    · next h =>
      obtain ⟨h1, h2⟩ := TRel_tupSplit (splitToTup_rel (Bool.eq_false_iff.mpr h) hxs)
      refine legalUnaryTree_wf mkCode vecSupported hb hn hf t1 h1 fun hG1 r1₁ r1₂ hr1 =>
        legalUnaryTree_wf mkCode vecSupported hb hn hf t2 (TRel_argRel_weaken' hG1 h2) fun hG2 r2₁ r2₂ hr2 =>
          hk (sub_trans hG1 hG2) _ _
            (tupToSplit_rel (Bool.eq_false_iff.mpr h) (TRel_tupAppend (TRel_argRel_weaken' hG2 hr1) hr2))

theorem legalBswapTree_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty} :
    ∀ (t : Ty) {G : Ctx V₁ V₂} {D : Ctx L₁ L₂}
      {xs₁ : Tup (Arg V₁) (target.legalTys t)} {xs₂ : Tup (Arg V₂) (target.legalTys t)},
      TRel (ArgRel G) xs₁ xs₂ →
      ∀ {k₁ : Tup (Arg V₁) (target.legalTys t) → Expr V₁ L₁ rs}
        {k₂ : Tup (Arg V₂) (target.legalTys t) → Expr V₂ L₂ rs},
      (∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂, TRel (ArgRel G') y₁ y₂ → Wf G' D (k₁ y₁) (k₂ y₂)) →
      Wf G D (legalBswapTree target t xs₁ k₁) (legalBswapTree target t xs₂ k₂) := by
  intro t G D xs₁ xs₂ hxs k₁ k₂ hk
  simp only [legalBswapTree]
  split
  · exact .hlt
  · refine legalUnaryTree_wf target .bswap (fun _ => false)
      (fun {_ _ _ _ _ _} _ _ => .hlt)
      ?_
      (fun _ {_ _ _ _ _ _} _ _ => .hlt)
      t hxs hk
    intro n G' D' x₁ x₂ c₁ c₂ hx hc
    split
    · exact hc (fun _ p => p) _ _ (.imm _)
    · split
      · exact hc (fun _ p => p) _ _ hx
      · split
        · exact Wf.let1 _ hx hc
        · split
          · exact Wf.let1 _ hx fun h1 bw₁ bw₂ hbw =>
              Wf.let2 _ hbw (.imm _) fun h2 r₁ r₂ hr =>
                hc (sub_trans h1 h2) r₁ r₂ hr
          · exact .hlt

theorem legalTernaryTree_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    (mkCode : (u : Ty) → OpCode [u, u, u] [u]) (vecSupported : (u : Ty) → Bool)
    {onBool₁ : Arg V₁ .bool → Arg V₁ .bool → Arg V₁ .bool → (Arg V₁ .bool → Expr V₁ L₁ rs) → Expr V₁ L₁ rs}
    {onBool₂ : Arg V₂ .bool → Arg V₂ .bool → Arg V₂ .bool → (Arg V₂ .bool → Expr V₂ L₂ rs) → Expr V₂ L₂ rs}
    {onBits₁ : (n : Nat) → Arg V₁ (.bits (target.widenWidth n)) → Arg V₁ (.bits (target.widenWidth n)) →
      Arg V₁ (.bits (target.widenWidth n)) → (Arg V₁ (.bits (target.widenWidth n)) → Expr V₁ L₁ rs) → Expr V₁ L₁ rs}
    {onBits₂ : (n : Nat) → Arg V₂ (.bits (target.widenWidth n)) → Arg V₂ (.bits (target.widenWidth n)) →
      Arg V₂ (.bits (target.widenWidth n)) → (Arg V₂ (.bits (target.widenWidth n)) → Expr V₂ L₂ rs) → Expr V₂ L₂ rs}
    {onFloat₁ : (f : Fmt) → Arg V₁ (.float f) → Arg V₁ (.float f) → Arg V₁ (.float f) →
      (Arg V₁ (.float f) → Expr V₁ L₁ rs) → Expr V₁ L₁ rs}
    {onFloat₂ : (f : Fmt) → Arg V₂ (.float f) → Arg V₂ (.float f) → Arg V₂ (.float f) →
      (Arg V₂ (.float f) → Expr V₂ L₂ rs) → Expr V₂ L₂ rs}
    (hb : ∀ {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} {a₁ b₁ c₁ a₂ b₂ c₂ cont₁ cont₂},
      ArgRel G .bool a₁ a₂ → ArgRel G .bool b₁ b₂ → ArgRel G .bool c₁ c₂ →
      (∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂, ArgRel G' .bool y₁ y₂ → Wf G' D (cont₁ y₁) (cont₂ y₂)) →
      Wf G D (onBool₁ a₁ b₁ c₁ cont₁) (onBool₂ a₂ b₂ c₂ cont₂))
    (hn : ∀ (n : Nat) {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} {a₁ b₁ c₁ a₂ b₂ c₂ cont₁ cont₂},
      ArgRel G (.bits (target.widenWidth n)) a₁ a₂ → ArgRel G (.bits (target.widenWidth n)) b₁ b₂ →
      ArgRel G (.bits (target.widenWidth n)) c₁ c₂ →
      (∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂, ArgRel G' (.bits (target.widenWidth n)) y₁ y₂ → Wf G' D (cont₁ y₁) (cont₂ y₂)) →
      Wf G D (onBits₁ n a₁ b₁ c₁ cont₁) (onBits₂ n a₂ b₂ c₂ cont₂))
    (hf : ∀ (f : Fmt) {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} {a₁ b₁ c₁ a₂ b₂ c₂ cont₁ cont₂},
      ArgRel G (.float f) a₁ a₂ → ArgRel G (.float f) b₁ b₂ → ArgRel G (.float f) c₁ c₂ →
      (∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂, ArgRel G' (.float f) y₁ y₂ → Wf G' D (cont₁ y₁) (cont₂ y₂)) →
      Wf G D (onFloat₁ f a₁ b₁ c₁ cont₁) (onFloat₂ f a₂ b₂ c₂ cont₂)) :
    ∀ (t : Ty) {G : Ctx V₁ V₂} {D : Ctx L₁ L₂}
      {xs₁ : Tup (Arg V₁) (target.legalTys t)} {xs₂ : Tup (Arg V₂) (target.legalTys t)}
      {ys₁ : Tup (Arg V₁) (target.legalTys t)} {ys₂ : Tup (Arg V₂) (target.legalTys t)}
      {zs₁ : Tup (Arg V₁) (target.legalTys t)} {zs₂ : Tup (Arg V₂) (target.legalTys t)},
      TRel (ArgRel G) xs₁ xs₂ → TRel (ArgRel G) ys₁ ys₂ → TRel (ArgRel G) zs₁ zs₂ →
      ∀ {k₁ : Tup (Arg V₁) (target.legalTys t) → Expr V₁ L₁ rs}
        {k₂ : Tup (Arg V₂) (target.legalTys t) → Expr V₂ L₂ rs},
      (∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂, TRel (ArgRel G') y₁ y₂ → Wf G' D (k₁ y₁) (k₂ y₂)) →
      Wf G D (legalTernaryTree target mkCode vecSupported onBool₁ onBits₁ onFloat₁ t xs₁ ys₁ zs₁ k₁)
             (legalTernaryTree target mkCode vecSupported onBool₂ onBits₂ onFloat₂ t xs₂ ys₂ zs₂ k₂)
  | .bool, _, _, xs₁, xs₂, ys₁, ys₂, zs₁, zs₂, hxs, hys, hzs, _, _, hk => by
    rcases xs₁ with ⟨a₁, ⟨⟩⟩; rcases xs₂ with ⟨a₂, ⟨⟩⟩
    rcases ys₁ with ⟨b₁, ⟨⟩⟩; rcases ys₂ with ⟨b₂, ⟨⟩⟩
    rcases zs₁ with ⟨c₁, ⟨⟩⟩; rcases zs₂ with ⟨c₂, ⟨⟩⟩
    cases hxs with | cons ha _ => cases hys with | cons hb' _ => cases hzs with | cons hc _ =>
    exact hb ha hb' hc fun hG' y₁ y₂ hy => hk hG' _ _ (TRel.single hy)
  | .bits n, _, _, xs₁, xs₂, ys₁, ys₂, zs₁, zs₂, hxs, hys, hzs, _, _, hk => by
    rcases xs₁ with ⟨a₁, ⟨⟩⟩; rcases xs₂ with ⟨a₂, ⟨⟩⟩
    rcases ys₁ with ⟨b₁, ⟨⟩⟩; rcases ys₂ with ⟨b₂, ⟨⟩⟩
    rcases zs₁ with ⟨c₁, ⟨⟩⟩; rcases zs₂ with ⟨c₂, ⟨⟩⟩
    cases hxs with | cons ha _ => cases hys with | cons hb' _ => cases hzs with | cons hc _ =>
    exact hn n ha hb' hc fun hG' y₁ y₂ hy => hk hG' _ _ (TRel.single hy)
  | .float f, _, _, xs₁, xs₂, ys₁, ys₂, zs₁, zs₂, hxs, hys, hzs, _, _, hk => by
    rcases xs₁ with ⟨a₁, ⟨⟩⟩; rcases xs₂ with ⟨a₂, ⟨⟩⟩
    rcases ys₁ with ⟨b₁, ⟨⟩⟩; rcases ys₂ with ⟨b₂, ⟨⟩⟩
    rcases zs₁ with ⟨c₁, ⟨⟩⟩; rcases zs₂ with ⟨c₂, ⟨⟩⟩
    cases hxs with | cons ha _ => cases hys with | cons hb' _ => cases hzs with | cons hc _ =>
    exact hf f ha hb' hc fun hG' y₁ y₂ hy => hk hG' _ _ (TRel.single hy)
  | .pair t1 t2, G, D, xs₁, xs₂, ys₁, ys₂, zs₁, zs₂, hxs, hys, hzs, k₁, k₂, hk => by
    simp only [legalTernaryTree]
    split
    · next h =>
      obtain ⟨hx1, _⟩ := TRel.cons_iff.1 (packedToTup_rel h hxs)
      obtain ⟨hy1, _⟩ := TRel.cons_iff.1 (packedToTup_rel h hys)
      obtain ⟨hz1, _⟩ := TRel.cons_iff.1 (packedToTup_rel h hzs)
      split
      · exact Wf.let3 (mkCode (.pair t1 t2)) hx1 hy1 hz1 fun hG' r₁ r₂ hr =>
          hk hG' _ _ (tupToPacked_rel h (.cons hr .nil))
      · refine splitLegalToLeaves_wf target (.pair t1 t2) hxs fun hG1 fx₁ fx₂ hfx =>
          splitLegalToLeaves_wf target (.pair t1 t2) (TRel_argRel_weaken' hG1 hys) fun hG2 fy₁ fy₂ hfy =>
            splitLegalToLeaves_wf target (.pair t1 t2) (TRel_argRel_weaken' (sub_trans hG1 hG2) hzs) fun hG3 fz₁ fz₂ hfz => ?_
        have hgoS : ∀ (u : Ty) {G' : Ctx V₁ V₂}
            {fxu₁ : Tup (Arg V₁) (target.leafTys u)} {fxu₂ : Tup (Arg V₂) (target.leafTys u)}
            {fyu₁ : Tup (Arg V₁) (target.leafTys u)} {fyu₂ : Tup (Arg V₂) (target.leafTys u)}
            {fzu₁ : Tup (Arg V₁) (target.leafTys u)} {fzu₂ : Tup (Arg V₂) (target.leafTys u)},
            TRel (ArgRel G') fxu₁ fxu₂ → TRel (ArgRel G') fyu₁ fyu₂ → TRel (ArgRel G') fzu₁ fzu₂ →
            ∀ {c₁ : Tup (Arg V₁) (target.leafTys u) → Expr V₁ L₁ rs}
              {c₂ : Tup (Arg V₂) (target.leafTys u) → Expr V₂ L₂ rs},
            (∀ {G''}, (∀ p ∈ G', p ∈ G'') → ∀ y₁ y₂, TRel (ArgRel G'') y₁ y₂ → Wf G'' D (c₁ y₁) (c₂ y₂)) →
            Wf G' D
              (legalTernaryTree.goS target onBool₁ onBits₁ onFloat₁ u fxu₁ fyu₁ fzu₁ c₁)
              (legalTernaryTree.goS target onBool₂ onBits₂ onFloat₂ u fxu₂ fyu₂ fzu₂ c₂) := by
          intro u
          induction u with
          | bool =>
            intro G' (_, ()) (_, ()) (_, ()) (_, ()) (_, ()) (_, ()) hx hy hz c₁ c₂ hc
            cases hx with | cons hx _ => cases hy with | cons hy _ => cases hz with | cons hz _ =>
              exact hb hx hy hz fun hG' y₁ y₂ hr => hc hG' _ _ (TRel.single hr)
          | bits n =>
            intro G' xs1 xs2 ys1 ys2 zs1 zs2 hx hy hz c₁ c₂ hc
            rcases xs1 with ⟨u1, ⟨⟩⟩; rcases xs2 with ⟨u2, ⟨⟩⟩
            rcases ys1 with ⟨v1, ⟨⟩⟩; rcases ys2 with ⟨v2, ⟨⟩⟩
            rcases zs1 with ⟨w1, ⟨⟩⟩; rcases zs2 with ⟨w2, ⟨⟩⟩
            cases hx with | cons hx _ => cases hy with | cons hy _ => cases hz with | cons hz _ =>
              exact hn n hx hy hz fun hG' y₁ y₂ hr => hc hG' _ _ (TRel.single hr)
          | float f =>
            intro G' (_, ()) (_, ()) (_, ()) (_, ()) (_, ()) (_, ()) hx hy hz c₁ c₂ hc
            cases hx with | cons hx _ => cases hy with | cons hy _ => cases hz with | cons hz _ =>
              exact hf f hx hy hz fun hG' y₁ y₂ hr => hc hG' _ _ (TRel.single hr)
          | pair u1 u2 ih1 ih2 =>
            intro G' _ _ _ _ _ _ hx hy hz c₁ c₂ hc
            obtain ⟨hx1, hx2⟩ := TRel_tupSplit hx
            obtain ⟨hy1, hy2⟩ := TRel_tupSplit hy
            obtain ⟨hz1, hz2⟩ := TRel_tupSplit hz
            exact ih1 hx1 hy1 hz1 fun hGa r1₁ r1₂ hr1 =>
              ih2 (TRel_argRel_weaken' hGa hx2) (TRel_argRel_weaken' hGa hy2) (TRel_argRel_weaken' hGa hz2)
                fun hGb r2₁ r2₂ hr2 => hc (sub_trans hGa hGb) _ _
                  (TRel_tupAppend (TRel_argRel_weaken' hGb hr1) hr2)
        refine hgoS (.pair t1 t2) (TRel_argRel_weaken' (sub_trans hG2 hG3) hfx)
          (TRel_argRel_weaken' hG3 hfy) hfz fun hG4 fr₁ fr₂ hfr =>
          packLeavesToLegal_wf target (.pair t1 t2) hfr fun hG5 y₁ y₂ hy =>
            hk (sub_trans hG1 (sub_trans hG2 (sub_trans hG3 (sub_trans hG4 hG5)))) y₁ y₂ hy
    · next h =>
      have hff := Bool.eq_false_iff.mpr h
      obtain ⟨hx1, hx2⟩ := TRel_tupSplit (splitToTup_rel hff hxs)
      obtain ⟨hy1, hy2⟩ := TRel_tupSplit (splitToTup_rel hff hys)
      obtain ⟨hz1, hz2⟩ := TRel_tupSplit (splitToTup_rel hff hzs)
      refine legalTernaryTree_wf mkCode vecSupported hb hn hf t1 hx1 hy1 hz1 fun hG1 r1₁ r1₂ hr1 =>
        legalTernaryTree_wf mkCode vecSupported hb hn hf t2
          (TRel_argRel_weaken' hG1 hx2) (TRel_argRel_weaken' hG1 hy2) (TRel_argRel_weaken' hG1 hz2)
          fun hG2 r2₁ r2₂ hr2 =>
            hk (sub_trans hG1 hG2) _ _ (tupToSplit_rel hff (TRel_tupAppend (TRel_argRel_weaken' hG2 hr1) hr2))

def OptRhsRel {V₁ V₂ : Ty → Type} (LG : Ctx (LVar target V₁) (LVar target V₂)) (t : Ty) :
    Option (Arg (LVar target V₁) t) → Option (Arg (LVar target V₂) t) → Prop
  | none, none => True
  | some r₁, some r₂ => ArgRel LG t r₁ r₂
  | _, _ => False

private theorem checkUniformImmShift_rel {V₁ V₂ : Ty → Type} {G : Ctx V₁ V₂}
    {as bs : List Ty} (u : Ty) (code : OpCode as bs) {x₁ : Arg V₁ u} {x₂ : Arg V₂ u}
    (hx : ArgRel G u x₁ x₂) :
    checkUniformImmShift u code x₁ = checkUniformImmShift u code x₂ := by
  cases hx <;> rfl

theorem legalBinTree_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    (mkCode : (u : Ty) → OpCode [u, u] [u]) (vecSupported : (u : Ty) → Bool → Bool)
    {onBool₁ : Arg V₁ .bool → Arg V₁ .bool → (Arg V₁ .bool → Expr V₁ L₁ rs) → Expr V₁ L₁ rs}
    {onBool₂ : Arg V₂ .bool → Arg V₂ .bool → (Arg V₂ .bool → Expr V₂ L₂ rs) → Expr V₂ L₂ rs}
    {onBits₁ : (n : Nat) → Arg V₁ (.bits (target.widenWidth n)) → Arg V₁ (.bits (target.widenWidth n)) →
      (Arg V₁ (.bits (target.widenWidth n)) → Expr V₁ L₁ rs) → Expr V₁ L₁ rs}
    {onBits₂ : (n : Nat) → Arg V₂ (.bits (target.widenWidth n)) → Arg V₂ (.bits (target.widenWidth n)) →
      (Arg V₂ (.bits (target.widenWidth n)) → Expr V₂ L₂ rs) → Expr V₂ L₂ rs}
    {onFloat₁ : (f : Fmt) → Arg V₁ (.float f) → Arg V₁ (.float f) →
      (Arg V₁ (.float f) → Expr V₁ L₁ rs) → Expr V₁ L₁ rs}
    {onFloat₂ : (f : Fmt) → Arg V₂ (.float f) → Arg V₂ (.float f) →
      (Arg V₂ (.float f) → Expr V₂ L₂ rs) → Expr V₂ L₂ rs}
    (uniformImmRhs₁ : (u : Ty) → Arg (LVar target V₁) u → Bool)
    (uniformImmRhs₂ : (u : Ty) → Arg (LVar target V₂) u → Bool)
    (hunif : ∀ u {LG' : Ctx (LVar target V₁) (LVar target V₂)} {r₁ r₂},
      ArgRel LG' u r₁ r₂ → uniformImmRhs₁ u r₁ = uniformImmRhs₂ u r₂)
    (hb : ∀ {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} {a₁ b₁ a₂ b₂ cont₁ cont₂},
      ArgRel G .bool a₁ a₂ → ArgRel G .bool b₁ b₂ →
      (∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂, ArgRel G' .bool y₁ y₂ → Wf G' D (cont₁ y₁) (cont₂ y₂)) →
      Wf G D (onBool₁ a₁ b₁ cont₁) (onBool₂ a₂ b₂ cont₂))
    (hn : ∀ (n : Nat) {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} {a₁ b₁ a₂ b₂ cont₁ cont₂},
      ArgRel G (.bits (target.widenWidth n)) a₁ a₂ → ArgRel G (.bits (target.widenWidth n)) b₁ b₂ →
      (∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂, ArgRel G' (.bits (target.widenWidth n)) y₁ y₂ → Wf G' D (cont₁ y₁) (cont₂ y₂)) →
      Wf G D (onBits₁ n a₁ b₁ cont₁) (onBits₂ n a₂ b₂ cont₂))
    (hf : ∀ (f : Fmt) {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} {a₁ b₁ a₂ b₂ cont₁ cont₂},
      ArgRel G (.float f) a₁ a₂ → ArgRel G (.float f) b₁ b₂ →
      (∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂, ArgRel G' (.float f) y₁ y₂ → Wf G' D (cont₁ y₁) (cont₂ y₂)) →
      Wf G D (onFloat₁ f a₁ b₁ cont₁) (onFloat₂ f a₂ b₂ cont₂)) :
    ∀ (t : Ty) {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} {LG : Ctx (LVar target V₁) (LVar target V₂)}
      {xs₁ : Tup (Arg V₁) (target.legalTys t)} {xs₂ : Tup (Arg V₂) (target.legalTys t)}
      {ys₁ : Tup (Arg V₁) (target.legalTys t)} {ys₂ : Tup (Arg V₂) (target.legalTys t)}
      {rhs₁ : Option (Arg (LVar target V₁) t)} {rhs₂ : Option (Arg (LVar target V₂) t)},
      TRel (ArgRel G) xs₁ xs₂ → TRel (ArgRel G) ys₁ ys₂ → OptRhsRel target LG t rhs₁ rhs₂ →
      ∀ {k₁ : Tup (Arg V₁) (target.legalTys t) → Expr V₁ L₁ rs}
        {k₂ : Tup (Arg V₂) (target.legalTys t) → Expr V₂ L₂ rs},
      (∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂, TRel (ArgRel G') y₁ y₂ → Wf G' D (k₁ y₁) (k₂ y₂)) →
      Wf G D (legalBinTree target mkCode vecSupported onBool₁ onBits₁ onFloat₁ uniformImmRhs₁ t xs₁ ys₁ rhs₁ k₁)
             (legalBinTree target mkCode vecSupported onBool₂ onBits₂ onFloat₂ uniformImmRhs₂ t xs₂ ys₂ rhs₂ k₂)
  | .bool, _, _, _, xs₁, xs₂, ys₁, ys₂, _, _, hxs, hys, _, _, _, hk => by
    rcases xs₁ with ⟨a₁, ⟨⟩⟩; rcases xs₂ with ⟨a₂, ⟨⟩⟩
    rcases ys₁ with ⟨b₁, ⟨⟩⟩; rcases ys₂ with ⟨b₂, ⟨⟩⟩
    cases hxs with | cons ha _ => cases hys with | cons hb' _ =>
    exact hb ha hb' fun hG' y₁ y₂ hy => hk hG' _ _ (TRel.single hy)
  | .bits n, _, _, _, xs₁, xs₂, ys₁, ys₂, _, _, hxs, hys, _, _, _, hk => by
    rcases xs₁ with ⟨a₁, ⟨⟩⟩; rcases xs₂ with ⟨a₂, ⟨⟩⟩
    rcases ys₁ with ⟨b₁, ⟨⟩⟩; rcases ys₂ with ⟨b₂, ⟨⟩⟩
    cases hxs with | cons ha _ => cases hys with | cons hb' _ =>
    exact hn n ha hb' fun hG' y₁ y₂ hy => hk hG' _ _ (TRel.single hy)
  | .float f, _, _, _, xs₁, xs₂, ys₁, ys₂, _, _, hxs, hys, _, _, _, hk => by
    rcases xs₁ with ⟨a₁, ⟨⟩⟩; rcases xs₂ with ⟨a₂, ⟨⟩⟩
    rcases ys₁ with ⟨b₁, ⟨⟩⟩; rcases ys₂ with ⟨b₂, ⟨⟩⟩
    cases hxs with | cons ha _ => cases hys with | cons hb' _ =>
    exact hf f ha hb' fun hG' y₁ y₂ hy => hk hG' _ _ (TRel.single hy)
  | .pair t1 t2, G, D, LG, xs₁, xs₂, ys₁, ys₂, rhs₁, rhs₂, hxs, hys, hrhs, k₁, k₂, hk => by
    dsimp only [legalBinTree]
    split
    · next h =>
      have hxs' := packedToTup_rel h hxs
      have hys' := packedToTup_rel h hys
      obtain ⟨hx1, _⟩ := TRel.cons_iff.1 hxs'
      obtain ⟨hy1, _⟩ := TRel.cons_iff.1 hys'
      have hscalar :
          Wf G D
            (splitLegalToLeaves target (.pair t1 t2) xs₁ fun fx =>
             splitLegalToLeaves target (.pair t1 t2) ys₁ fun fy =>
             legalBinTree.goS target onBool₁ onBits₁ onFloat₁ (.pair t1 t2) fx fy fun fres =>
               packLeavesToLegal target (.pair t1 t2) fres k₁)
            (splitLegalToLeaves target (.pair t1 t2) xs₂ fun fx =>
             splitLegalToLeaves target (.pair t1 t2) ys₂ fun fy =>
             legalBinTree.goS target onBool₂ onBits₂ onFloat₂ (.pair t1 t2) fx fy fun fres =>
               packLeavesToLegal target (.pair t1 t2) fres k₂) := by
        refine splitLegalToLeaves_wf target (.pair t1 t2) hxs fun hG1 fx₁ fx₂ hfx =>
          splitLegalToLeaves_wf target (.pair t1 t2) (TRel_argRel_weaken' hG1 hys) fun hG2 fy₁ fy₂ hfy => ?_
        have hgoS : ∀ (u : Ty) {G' : Ctx V₁ V₂}
            {fxu₁ : Tup (Arg V₁) (target.leafTys u)} {fxu₂ : Tup (Arg V₂) (target.leafTys u)}
            {fyu₁ : Tup (Arg V₁) (target.leafTys u)} {fyu₂ : Tup (Arg V₂) (target.leafTys u)},
            TRel (ArgRel G') fxu₁ fxu₂ → TRel (ArgRel G') fyu₁ fyu₂ →
            ∀ {c₁ : Tup (Arg V₁) (target.leafTys u) → Expr V₁ L₁ rs}
              {c₂ : Tup (Arg V₂) (target.leafTys u) → Expr V₂ L₂ rs},
            (∀ {G''}, (∀ p ∈ G', p ∈ G'') → ∀ y₁ y₂, TRel (ArgRel G'') y₁ y₂ → Wf G'' D (c₁ y₁) (c₂ y₂)) →
            Wf G' D
              (legalBinTree.goS target onBool₁ onBits₁ onFloat₁ u fxu₁ fyu₁ c₁)
              (legalBinTree.goS target onBool₂ onBits₂ onFloat₂ u fxu₂ fyu₂ c₂) := by
          intro u
          induction u with
          | bool =>
            intro G' (_, ()) (_, ()) (_, ()) (_, ()) hx hy c₁ c₂ hc
            cases hx with | cons hx _ => cases hy with | cons hy _ =>
              exact hb hx hy fun hG' y₁ y₂ hr => hc hG' _ _ (TRel.single hr)
          | bits n =>
            intro G' xs1 xs2 ys1 ys2 hx hy c₁ c₂ hc
            rcases xs1 with ⟨u1, ⟨⟩⟩; rcases xs2 with ⟨u2, ⟨⟩⟩
            rcases ys1 with ⟨v1, ⟨⟩⟩; rcases ys2 with ⟨v2, ⟨⟩⟩
            cases hx with | cons hx _ => cases hy with | cons hy _ =>
              exact hn n hx hy fun hG' y₁ y₂ hr => hc hG' _ _ (TRel.single hr)
          | float f =>
            intro G' (_, ()) (_, ()) (_, ()) (_, ()) hx hy c₁ c₂ hc
            cases hx with | cons hx _ => cases hy with | cons hy _ =>
              exact hf f hx hy fun hG' y₁ y₂ hr => hc hG' _ _ (TRel.single hr)
          | pair u1 u2 ih1 ih2 =>
            intro G' _ _ _ _ hx hy c₁ c₂ hc
            obtain ⟨hx1, hx2⟩ := TRel_tupSplit hx
            obtain ⟨hy1, hy2⟩ := TRel_tupSplit hy
            exact ih1 hx1 hy1 fun hGa r1₁ r1₂ hr1 =>
              ih2 (TRel_argRel_weaken' hGa hx2) (TRel_argRel_weaken' hGa hy2) fun hGb r2₁ r2₂ hr2 =>
                hc (sub_trans hGa hGb) _ _ (TRel_tupAppend (TRel_argRel_weaken' hGb hr1) hr2)
        exact hgoS (.pair t1 t2) (TRel_argRel_weaken' hG2 hfx) hfy fun hG3 fr₁ fr₂ hfr =>
          packLeavesToLegal_wf target (.pair t1 t2) hfr fun hG4 y₁ y₂ hy =>
            hk (sub_trans hG1 (sub_trans hG2 (sub_trans hG3 hG4))) y₁ y₂ hy
      have hyu : checkUniformImmShift (.pair t1 t2) (mkCode (.pair t1 t2)) (packedToTup h ys₁).1 =
          checkUniformImmShift (.pair t1 t2) (mkCode (.pair t1 t2)) (packedToTup h ys₂).1 :=
        checkUniformImmShift_rel (.pair t1 t2) (mkCode (.pair t1 t2)) hy1
      cases rhs₁ with
      | none =>
        cases rhs₂ with
        | some _ => exact False.elim hrhs
        | none =>
          have hu := congrArg (vecSupported (.pair t1 t2)) hyu
          by_cases hvs : vecSupported (.pair t1 t2)
              (checkUniformImmShift (.pair t1 t2) (mkCode (.pair t1 t2)) (packedToTup h ys₁).1) = true
          · have hvs₂ := hu ▸ hvs
            rw [ite_eq_left hvs, ite_eq_left hvs₂]
            exact Wf.let2 (mkCode (.pair t1 t2)) hx1 hy1 fun hG' r₁ r₂ hr =>
              hk hG' _ _ (tupToPacked_rel h (.cons hr .nil))
          · have hvs₂ : ¬ (vecSupported (.pair t1 t2)
                (checkUniformImmShift (.pair t1 t2) (mkCode (.pair t1 t2)) (packedToTup h ys₂).1) = true) := hu ▸ hvs
            rw [ite_eq_right hvs, ite_eq_right hvs₂]
            cases mkCode (.pair t1 t2) <;> (try dsimp only) <;> exact hscalar
      | some r1 =>
        cases rhs₂ with
        | none => exact False.elim hrhs
        | some r2 =>
          have hu := congrArg (vecSupported (.pair t1 t2)) hyu
          by_cases hvs : vecSupported (.pair t1 t2)
              (checkUniformImmShift (.pair t1 t2) (mkCode (.pair t1 t2)) (packedToTup h ys₁).1) = true
          · have hvs₂ := hu ▸ hvs
            rw [ite_eq_left hvs, ite_eq_left hvs₂]
            exact Wf.let2 (mkCode (.pair t1 t2)) hx1 hy1 fun hG' r₁ r₂ hr =>
              hk hG' _ _ (tupToPacked_rel h (.cons hr .nil))
          · have hvs₂ : ¬ (vecSupported (.pair t1 t2)
                (checkUniformImmShift (.pair t1 t2) (mkCode (.pair t1 t2)) (packedToTup h ys₂).1) = true) := hu ▸ hvs
            rw [ite_eq_right hvs, ite_eq_right hvs₂]
            cases hrhs with
            | var _ => cases mkCode (.pair t1 t2) <;> (try dsimp only) <;> exact hscalar
            | imm c =>
              cases mkCode (.pair t1 t2) <;> (try dsimp only [opShiftKind])
              all_goals first
                | exact hscalar
                | (cases uniformShiftLeaf? (.pair t1 t2) c with
                   | none => exact hscalar
                   | some p =>
                     dsimp only
                     by_cases hs0 : (p.2 == 0) = true
                     · rw [ite_eq_left hs0, ite_eq_left hs0]; dsimp only
                       exact hk (fun _ q => q) _ _ (tupToPacked_rel h hxs')
                     · rw [ite_eq_right hs0, ite_eq_right hs0]
                       first
                       | (by_cases hsup : target.vecIntOpSupported (.rotr (.pair t1 t2)) (.pair t1 t2) true = true
                          · rw [ite_eq_left hsup, ite_eq_left hsup]; dsimp only
                            exact Wf.let2 (.rotr (.pair t1 t2)) hx1 (.imm _) fun h1 rt₁ rt₂ hrt =>
                              hk h1 _ _ (tupToPacked_rel h (.cons hrt .nil))
                          · rw [ite_eq_right hsup, ite_eq_right hsup]; dsimp only
                            exact hscalar)
                       | (by_cases hsup : (target.vecIntOpSupported (.rotr (.pair t1 t2)) (.pair t1 t2) true &&
                                          target.vecIntOpSupported (.and (.pair t1 t2)) (.pair t1 t2) false) = true
                          · rw [ite_eq_left hsup, ite_eq_left hsup]; dsimp only
                            exact Wf.let2 (.rotr (.pair t1 t2)) hx1 (.imm _) fun h1 rt₁ rt₂ hrt =>
                              Wf.let2 (.and (.pair t1 t2)) hrt (.imm _) fun h2 r₁ r₂ hr =>
                                hk (sub_trans h1 h2) _ _ (tupToPacked_rel h (.cons hr .nil))
                          · rw [ite_eq_right hsup, ite_eq_right hsup]; dsimp only
                            exact hscalar))
    · next h =>
      have hff := Bool.eq_false_iff.mpr h
      obtain ⟨hx1, hx2⟩ := TRel_tupSplit (splitToTup_rel hff hxs)
      obtain ⟨hy1, hy2⟩ := TRel_tupSplit (splitToTup_rel hff hys)
      exact legalBinTree_wf mkCode vecSupported uniformImmRhs₁ uniformImmRhs₂ hunif hb hn hf
        t1 (LG := LG) hx1 hy1 (rhs₁ := none) (rhs₂ := none) trivial fun hG1 r1₁ r1₂ hr1 =>
        legalBinTree_wf mkCode vecSupported uniformImmRhs₁ uniformImmRhs₂ hunif hb hn hf
          t2 (LG := LG) (TRel_argRel_weaken' hG1 hx2) (TRel_argRel_weaken' hG1 hy2) (rhs₁ := none) (rhs₂ := none) trivial
          fun hG2 r2₁ r2₂ hr2 =>
            hk (sub_trans hG1 hG2) _ _ (tupToSplit_rel hff (TRel_tupAppend (TRel_argRel_weaken' hG2 hr1) hr2))

theorem legalBitsArith_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} (n : Nat) (code : OpCode [.bits n, .bits n] [.bits n])
    {a₁ b₁ : Arg V₁ (.bits (target.widenWidth n))} {a₂ b₂ : Arg V₂ (.bits (target.widenWidth n))}
    (ha : ArgRel G (.bits (target.widenWidth n)) a₁ a₂)
    (hb : ArgRel G (.bits (target.widenWidth n)) b₁ b₂)
    {k₁ : Arg V₁ (.bits (target.widenWidth n)) → Expr V₁ L₁ rs}
    {k₂ : Arg V₂ (.bits (target.widenWidth n)) → Expr V₂ L₂ rs}
    (hk : ∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂,
      ArgRel G' (.bits (target.widenWidth n)) y₁ y₂ → Wf G' D (k₁ y₁) (k₂ y₂)) :
    Wf G D (legalBitsArith target n code a₁ b₁ k₁) (legalBitsArith target n code a₂ b₂ k₂) := by
  simp only [legalBitsArith]
  split
  · exact hk (fun _ p => p) _ _ (.imm _)
  · cases code <;> simp only
    all_goals first
    | exact .hlt
    | exact Wf.let2 _ ha hb fun h1 r₁ r₂ hr =>
        emitMaskToN_wf n (target.widenWidth n) hr fun h2 y₁ y₂ hy => hk (sub_trans h1 h2) y₁ y₂ hy
    | exact Wf.let2 _ ha hb hk
    | (split
       · exact Wf.let2 _ ha hb hk
       · first
         | exact emitCountMod_wf n (target.widenWidth n) hb fun h1 c₁ c₂ hc =>
             Wf.let2 _ (ha.weaken h1) hc fun h2 r₁ r₂ hr =>
               emitMaskToN_wf n (target.widenWidth n) hr fun h3 y₁ y₂ hy =>
                 hk (sub_trans h1 (sub_trans h2 h3)) y₁ y₂ hy
         | exact emitCountMod_wf n (target.widenWidth n) hb fun h1 c₁ c₂ hc =>
             Wf.let2 _ (ha.weaken h1) hc fun h2 r₁ r₂ hr => hk (sub_trans h1 h2) r₁ r₂ hr
         | exact emitCountMod_wf n (target.widenWidth n) hb fun h1 c₁ c₂ hc =>
             emitSextToW_wf n (target.widenWidth n) (ha.weaken h1) fun h2 sa₁ sa₂ hsa =>
               Wf.let2 _ hsa (hc.weaken h2) fun h3 r₁ r₂ hr =>
                 emitMaskToN_wf n (target.widenWidth n) hr fun h4 y₁ y₂ hy =>
                   hk (sub_trans h1 (sub_trans h2 (sub_trans h3 h4))) y₁ y₂ hy
         | exact emitCountMod_wf n (target.widenWidth n) hb fun h1 c₁ c₂ hc =>
             Wf.let2 _ (.imm _) hc fun h2 nc₁ nc₂ hnc =>
               have s12 := sub_trans h1 h2
               Wf.let2 _ (ha.weaken s12) (hc.weaken h2) fun h3 lo₁ lo₂ hlo =>
                 have s123 := sub_trans s12 h3
                 Wf.let2 _ (ha.weaken s123) (hnc.weaken h3) fun h4 hi₁ hi₂ hhi =>
                   Wf.let2 _ (hlo.weaken h4) hhi fun h5 cb₁ cb₂ hcb =>
                     emitMaskToN_wf n (target.widenWidth n) hcb fun h6 y₁ y₂ hy =>
                       hk (sub_trans s123 (sub_trans h4 (sub_trans h5 h6))) y₁ y₂ hy)

theorem legalCmpTree_goMask_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    (o : CmpOp) :
    ∀ (u : Ty) {G : Ctx V₁ V₂} {D : Ctx L₁ L₂}
      {fx₁ : Tup (Arg V₁) (target.leafTys u)} {fx₂ : Tup (Arg V₂) (target.leafTys u)}
      {fy₁ : Tup (Arg V₁) (target.leafTys u)} {fy₂ : Tup (Arg V₂) (target.leafTys u)},
      TRel (ArgRel G) fx₁ fx₂ → TRel (ArgRel G) fy₁ fy₂ →
      ∀ {c₁ : Tup (Arg V₁) (target.leafTys u.mask) → Expr V₁ L₁ rs}
        {c₂ : Tup (Arg V₂) (target.leafTys u.mask) → Expr V₂ L₂ rs},
      (∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂, TRel (ArgRel G') y₁ y₂ → Wf G' D (c₁ y₁) (c₂ y₂)) →
      Wf G D (legalCmpTree.goMask target o u fx₁ fy₁ c₁)
             (legalCmpTree.goMask target o u fx₂ fy₂ c₂)
  | .bool, _, _, fx₁, fx₂, fy₁, fy₂, hfx, hfy, _, _, hc => by
    rcases fx₁ with ⟨a₁, ⟨⟩⟩; rcases fx₂ with ⟨a₂, ⟨⟩⟩
    rcases fy₁ with ⟨b₁, ⟨⟩⟩; rcases fy₂ with ⟨b₂, ⟨⟩⟩
    cases hfx with | cons ha _ => cases hfy with | cons hb _ =>
    simp only [legalCmpTree.goMask]
    split
    · exact Wf.let2 _ ha hb fun h1 r₁ r₂ hr => hc h1 _ _ (TRel.single hr)
    · exact emitBoolCmp_wf o ha hb fun hG' r₁ r₂ hr => hc hG' _ _ (TRel.single hr)
  | .bits n, _, _, fx₁, fx₂, fy₁, fy₂, hfx, hfy, _, _, hc => by
    rcases fx₁ with ⟨a₁, ⟨⟩⟩; rcases fx₂ with ⟨a₂, ⟨⟩⟩
    rcases fy₁ with ⟨b₁, ⟨⟩⟩; rcases fy₂ with ⟨b₂, ⟨⟩⟩
    cases hfx with | cons ha _ => cases hfy with | cons hb _ =>
    simp only [legalCmpTree.goMask]
    split
    · exact hc (fun _ p => p) _ _ (TRel.single (ArgRel.imm _))
    · split
      · exact Wf.let2 _ ha hb fun h1 r₁ r₂ hr => hc h1 _ _ (TRel.single hr)
      · cases o <;> dsimp only
        all_goals first
          | exact Wf.let2 _ ha hb fun h1 r₁ r₂ hr => hc h1 _ _ (TRel.single hr)
          | exact emitSextToW_wf n (target.widenWidth n) ha fun h1 sa₁ sa₂ hsa =>
              emitSextToW_wf n (target.widenWidth n) (hb.weaken h1) fun h2 sb₁ sb₂ hsb =>
                Wf.let2 _ (hsa.weaken h2) hsb fun h3 r₁ r₂ hr =>
                  hc (sub_trans h1 (sub_trans h2 h3)) _ _ (TRel.single hr)
  | .float _, _, _, _, _, _, _, _, _, _, _, _ => .hlt
  | .pair u1 u2, _, _, fx₁, fx₂, fy₁, fy₂, hfx, hfy, c₁, c₂, hc => by
    simp only [legalCmpTree.goMask]
    obtain ⟨hx1, hx2⟩ := TRel_tupSplit hfx
    obtain ⟨hy1, hy2⟩ := TRel_tupSplit hfy
    refine legalCmpTree_goMask_wf o u1 hx1 hy1 fun h1 m1₁ m1₂ hm1 => ?_
    refine legalCmpTree_goMask_wf o u2 (TRel_argRel_weaken' h1 hx2) (TRel_argRel_weaken' h1 hy2)
      fun h2 m2₁ m2₂ hm2 =>
        hc (sub_trans h1 h2) _ _ (TRel_tupAppend (TRel_argRel_weaken' h2 hm1) hm2)

theorem legalCmpTree_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    (o : CmpOp) :
    ∀ (t : Ty) {G : Ctx V₁ V₂} {D : Ctx L₁ L₂}
      {xs₁ : Tup (Arg V₁) (target.legalTys t)} {xs₂ : Tup (Arg V₂) (target.legalTys t)}
      {ys₁ : Tup (Arg V₁) (target.legalTys t)} {ys₂ : Tup (Arg V₂) (target.legalTys t)},
      TRel (ArgRel G) xs₁ xs₂ → TRel (ArgRel G) ys₁ ys₂ →
      ∀ {k₁ : Tup (Arg V₁) (target.legalTys t.mask) → Expr V₁ L₁ rs}
        {k₂ : Tup (Arg V₂) (target.legalTys t.mask) → Expr V₂ L₂ rs},
      (∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂, TRel (ArgRel G') y₁ y₂ → Wf G' D (k₁ y₁) (k₂ y₂)) →
      Wf G D (legalCmpTree target o t xs₁ ys₁ k₁) (legalCmpTree target o t xs₂ ys₂ k₂)
  | .bool, _, _, xs₁, xs₂, ys₁, ys₂, hxs, hys, _, _, hk => by
    rcases xs₁ with ⟨a₁, ⟨⟩⟩; rcases xs₂ with ⟨a₂, ⟨⟩⟩
    rcases ys₁ with ⟨b₁, ⟨⟩⟩; rcases ys₂ with ⟨b₂, ⟨⟩⟩
    cases hxs with | cons ha _ => cases hys with | cons hb _ =>
    simp only [legalCmpTree]
    split
    · exact Wf.let2 _ ha hb fun h1 r₁ r₂ hr => hk h1 _ _ (TRel.single hr)
    · exact emitBoolCmp_wf o ha hb fun hG' r₁ r₂ hr => hk hG' _ _ (TRel.single hr)
  | .bits n, _, _, xs₁, xs₂, ys₁, ys₂, hxs, hys, _, _, hk => by
    rcases xs₁ with ⟨a₁, ⟨⟩⟩; rcases xs₂ with ⟨a₂, ⟨⟩⟩
    rcases ys₁ with ⟨b₁, ⟨⟩⟩; rcases ys₂ with ⟨b₂, ⟨⟩⟩
    cases hxs with | cons ha _ => cases hys with | cons hb _ =>
    simp only [legalCmpTree]
    split
    · exact hk (fun _ p => p) _ _ (TRel.single (ArgRel.imm _))
    · split
      · exact Wf.let2 _ ha hb fun h1 r₁ r₂ hr => hk h1 _ _ (TRel.single hr)
      · cases o <;> dsimp only
        all_goals first
          | exact Wf.let2 _ ha hb fun h1 r₁ r₂ hr => hk h1 _ _ (TRel.single hr)
          | exact emitSextToW_wf n (target.widenWidth n) ha fun h1 sa₁ sa₂ hsa =>
              emitSextToW_wf n (target.widenWidth n) (hb.weaken h1) fun h2 sb₁ sb₂ hsb =>
                Wf.let2 _ (hsa.weaken h2) hsb fun h3 r₁ r₂ hr =>
                  hk (sub_trans h1 (sub_trans h2 h3)) _ _ (TRel.single hr)
  | .float _, _, _, _, _, _, _, _, _, _, _, _ => .hlt
  | .pair t1 t2, _, _, xs₁, xs₂, ys₁, ys₂, hxs, hys, k₁, k₂, hk =>
    splitLegalToLeaves_wf target (.pair t1 t2) hxs fun hG1 fx₁ fx₂ hfx =>
    splitLegalToLeaves_wf target (.pair t1 t2) (TRel_argRel_weaken' hG1 hys) fun hG2 fy₁ fy₂ hfy =>
    legalCmpTree_goMask_wf target o (.pair t1 t2) (TRel_argRel_weaken' hG2 hfx) hfy fun hG3 mr₁ mr₂ hmr =>
    packLeavesToLegal_wf target (Ty.mask (.pair t1 t2)) hmr fun hG4 y₁ y₂ hy =>
      hk (sub_trans hG1 (sub_trans hG2 (sub_trans hG3 hG4))) y₁ y₂ hy

theorem legalSelectTree_goSel_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty} :
    ∀ (u : Ty) {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} {c₁ : Arg V₁ .bool} {c₂ : Arg V₂ .bool}
      {fx₁ : Tup (Arg V₁) (target.leafTys u)} {fx₂ : Tup (Arg V₂) (target.leafTys u)}
      {fy₁ : Tup (Arg V₁) (target.leafTys u)} {fy₂ : Tup (Arg V₂) (target.leafTys u)},
      ArgRel G .bool c₁ c₂ → TRel (ArgRel G) fx₁ fx₂ → TRel (ArgRel G) fy₁ fy₂ →
      ∀ {k₁ : Tup (Arg V₁) (target.leafTys u) → Expr V₁ L₁ rs}
        {k₂ : Tup (Arg V₂) (target.leafTys u) → Expr V₂ L₂ rs},
      (∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂, TRel (ArgRel G') y₁ y₂ → Wf G' D (k₁ y₁) (k₂ y₂)) →
      Wf G D (legalSelectTree.goSel target c₁ u fx₁ fy₁ k₁)
             (legalSelectTree.goSel target c₂ u fx₂ fy₂ k₂)
  | .bool, _, _, _, _, fx₁, fx₂, fy₁, fy₂, hc, hfx, hfy, _, _, hk => by
    rcases fx₁ with ⟨a₁, ⟨⟩⟩; rcases fx₂ with ⟨a₂, ⟨⟩⟩
    rcases fy₁ with ⟨b₁, ⟨⟩⟩; rcases fy₂ with ⟨b₂, ⟨⟩⟩
    cases hfx with | cons ha _ => cases hfy with | cons hb _ =>
    simp only [legalSelectTree.goSel]
    split
    · exact Wf.let3 _ hc ha hb fun h1 r₁ r₂ hr => hk h1 _ _ (TRel.single hr)
    · exact emitBoolSelect_wf hc ha hb fun hG' r₁ r₂ hr => hk hG' _ _ (TRel.single hr)
  | .bits _, _, _, _, _, fx₁, fx₂, fy₁, fy₂, hc, hfx, hfy, _, _, hk => by
    rcases fx₁ with ⟨a₁, ⟨⟩⟩; rcases fx₂ with ⟨a₂, ⟨⟩⟩
    rcases fy₁ with ⟨b₁, ⟨⟩⟩; rcases fy₂ with ⟨b₂, ⟨⟩⟩
    cases hfx with | cons ha _ => cases hfy with | cons hb _ =>
    exact Wf.let3 _ hc ha hb fun h1 r₁ r₂ hr => hk h1 _ _ (TRel.single hr)
  | .float _, _, _, _, _, fx₁, fx₂, fy₁, fy₂, hc, hfx, hfy, _, _, hk => by
    rcases fx₁ with ⟨a₁, ⟨⟩⟩; rcases fx₂ with ⟨a₂, ⟨⟩⟩
    rcases fy₁ with ⟨b₁, ⟨⟩⟩; rcases fy₂ with ⟨b₂, ⟨⟩⟩
    cases hfx with | cons ha _ => cases hfy with | cons hb _ =>
    exact Wf.let3 _ hc ha hb fun h1 r₁ r₂ hr => hk h1 _ _ (TRel.single hr)
  | .pair u1 u2, _, _, c₁, c₂, fx₁, fx₂, fy₁, fy₂, hc, hfx, hfy, k₁, k₂, hk => by
    obtain ⟨hx1, hx2⟩ := TRel_tupSplit hfx
    obtain ⟨hy1, hy2⟩ := TRel_tupSplit hfy
    refine legalSelectTree_goSel_wf u1 hc hx1 hy1 fun hG1 r1₁ r1₂ hr1 => ?_
    refine legalSelectTree_goSel_wf u2 (hc.weaken hG1)
      (TRel_argRel_weaken' hG1 hx2) (TRel_argRel_weaken' hG1 hy2) fun hG2 r2₁ r2₂ hr2 =>
      hk (sub_trans hG1 hG2) _ _ (TRel_tupAppend (TRel_argRel_weaken' hG2 hr1) hr2)

theorem legalSelectTree_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} {c₁ : Arg V₁ .bool} {c₂ : Arg V₂ .bool} (hc : ArgRel G .bool c₁ c₂) :
    ∀ (t : Ty) {xs₁ : Tup (Arg V₁) (target.legalTys t)} {xs₂ : Tup (Arg V₂) (target.legalTys t)}
      {ys₁ : Tup (Arg V₁) (target.legalTys t)} {ys₂ : Tup (Arg V₂) (target.legalTys t)},
      TRel (ArgRel G) xs₁ xs₂ → TRel (ArgRel G) ys₁ ys₂ →
      ∀ {k₁ : Tup (Arg V₁) (target.legalTys t) → Expr V₁ L₁ rs}
        {k₂ : Tup (Arg V₂) (target.legalTys t) → Expr V₂ L₂ rs},
      (∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂, TRel (ArgRel G') y₁ y₂ → Wf G' D (k₁ y₁) (k₂ y₂)) →
      Wf G D (legalSelectTree target c₁ t xs₁ ys₁ k₁) (legalSelectTree target c₂ t xs₂ ys₂ k₂)
  | .bool, xs₁, xs₂, ys₁, ys₂, hxs, hys, _, _, hk => by
    rcases xs₁ with ⟨a₁, ⟨⟩⟩; rcases xs₂ with ⟨a₂, ⟨⟩⟩
    rcases ys₁ with ⟨b₁, ⟨⟩⟩; rcases ys₂ with ⟨b₂, ⟨⟩⟩
    cases hxs with | cons ha _ => cases hys with | cons hb _ =>
    simp only [legalSelectTree]
    split
    · exact Wf.let3 _ hc ha hb fun h1 r₁ r₂ hr => hk h1 _ _ (TRel.single hr)
    · exact emitBoolSelect_wf hc ha hb fun hG' r₁ r₂ hr => hk hG' _ _ (TRel.single hr)
  | .bits _, xs₁, xs₂, ys₁, ys₂, hxs, hys, _, _, hk => by
    rcases xs₁ with ⟨a₁, ⟨⟩⟩; rcases xs₂ with ⟨a₂, ⟨⟩⟩
    rcases ys₁ with ⟨b₁, ⟨⟩⟩; rcases ys₂ with ⟨b₂, ⟨⟩⟩
    cases hxs with | cons ha _ => cases hys with | cons hb _ =>
    exact Wf.let3 _ hc ha hb fun h1 r₁ r₂ hr => hk h1 _ _ (TRel.single hr)
  | .float _, xs₁, xs₂, ys₁, ys₂, hxs, hys, _, _, hk => by
    rcases xs₁ with ⟨a₁, ⟨⟩⟩; rcases xs₂ with ⟨a₂, ⟨⟩⟩
    rcases ys₁ with ⟨b₁, ⟨⟩⟩; rcases ys₂ with ⟨b₂, ⟨⟩⟩
    cases hxs with | cons ha _ => cases hys with | cons hb _ =>
    exact Wf.let3 _ hc ha hb fun h1 r₁ r₂ hr => hk h1 _ _ (TRel.single hr)
  | .pair t1 t2, xs₁, xs₂, ys₁, ys₂, hxs, hys, k₁, k₂, hk =>
    splitLegalToLeaves_wf target (.pair t1 t2) hxs fun hG1 fx₁ fx₂ hfx =>
    splitLegalToLeaves_wf target (.pair t1 t2) (TRel_argRel_weaken' hG1 hys) fun hG2 fy₁ fy₂ hfy =>
    legalSelectTree_goSel_wf target (.pair t1 t2) (hc.weaken (sub_trans hG1 hG2))
      (TRel_argRel_weaken' hG2 hfx) hfy fun hG3 fr₁ fr₂ hfr =>
    packLeavesToLegal_wf target (.pair t1 t2) hfr fun hG4 y₁ y₂ hy =>
      hk (sub_trans hG1 (sub_trans hG2 (sub_trans hG3 hG4))) y₁ y₂ hy

theorem legalBlendTree_goBlend_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty} :
    ∀ (u : Ty) {G : Ctx V₁ V₂} {D : Ctx L₁ L₂}
      {fm₁ : Tup (Arg V₁) (target.leafTys u.mask)} {fm₂ : Tup (Arg V₂) (target.leafTys u.mask)}
      {fx₁ : Tup (Arg V₁) (target.leafTys u)} {fx₂ : Tup (Arg V₂) (target.leafTys u)}
      {fy₁ : Tup (Arg V₁) (target.leafTys u)} {fy₂ : Tup (Arg V₂) (target.leafTys u)},
      TRel (ArgRel G) fm₁ fm₂ → TRel (ArgRel G) fx₁ fx₂ → TRel (ArgRel G) fy₁ fy₂ →
      ∀ {k₁ : Tup (Arg V₁) (target.leafTys u) → Expr V₁ L₁ rs}
        {k₂ : Tup (Arg V₂) (target.leafTys u) → Expr V₂ L₂ rs},
      (∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂, TRel (ArgRel G') y₁ y₂ → Wf G' D (k₁ y₁) (k₂ y₂)) →
      Wf G D (legalBlendTree.goBlend target u fm₁ fx₁ fy₁ k₁)
             (legalBlendTree.goBlend target u fm₂ fx₂ fy₂ k₂)
  | .bool, _, _, fm₁, fm₂, fx₁, fx₂, fy₁, fy₂, hfm, hfx, hfy, _, _, hk => by
    rcases fm₁ with ⟨c₁, ⟨⟩⟩; rcases fm₂ with ⟨c₂, ⟨⟩⟩
    rcases fx₁ with ⟨a₁, ⟨⟩⟩; rcases fx₂ with ⟨a₂, ⟨⟩⟩
    rcases fy₁ with ⟨b₁, ⟨⟩⟩; rcases fy₂ with ⟨b₂, ⟨⟩⟩
    cases hfm with | cons hc _ => cases hfx with | cons ha _ => cases hfy with | cons hb _ =>
    simp only [legalBlendTree.goBlend]
    split
    · exact Wf.let3 _ hc ha hb fun h1 r₁ r₂ hr => hk h1 _ _ (TRel.single hr)
    · exact emitBoolSelect_wf hc ha hb fun hG' r₁ r₂ hr => hk hG' _ _ (TRel.single hr)
  | .bits _, _, _, fm₁, fm₂, fx₁, fx₂, fy₁, fy₂, hfm, hfx, hfy, _, _, hk => by
    rcases fm₁ with ⟨c₁, ⟨⟩⟩; rcases fm₂ with ⟨c₂, ⟨⟩⟩
    rcases fx₁ with ⟨a₁, ⟨⟩⟩; rcases fx₂ with ⟨a₂, ⟨⟩⟩
    rcases fy₁ with ⟨b₁, ⟨⟩⟩; rcases fy₂ with ⟨b₂, ⟨⟩⟩
    cases hfm with | cons hc _ => cases hfx with | cons ha _ => cases hfy with | cons hb _ =>
    exact Wf.let3 _ hc ha hb fun h1 r₁ r₂ hr => hk h1 _ _ (TRel.single hr)
  | .float _, _, _, fm₁, fm₂, fx₁, fx₂, fy₁, fy₂, hfm, hfx, hfy, _, _, hk => by
    rcases fm₁ with ⟨c₁, ⟨⟩⟩; rcases fm₂ with ⟨c₂, ⟨⟩⟩
    rcases fx₁ with ⟨a₁, ⟨⟩⟩; rcases fx₂ with ⟨a₂, ⟨⟩⟩
    rcases fy₁ with ⟨b₁, ⟨⟩⟩; rcases fy₂ with ⟨b₂, ⟨⟩⟩
    cases hfm with | cons hc _ => cases hfx with | cons ha _ => cases hfy with | cons hb _ =>
    exact Wf.let3 _ hc ha hb fun h1 r₁ r₂ hr => hk h1 _ _ (TRel.single hr)
  | .pair u1 u2, _, _, fm₁, fm₂, fx₁, fx₂, fy₁, fy₂, hfm, hfx, hfy, k₁, k₂, hk => by
    obtain ⟨hm1, hm2⟩ := TRel_tupSplit hfm
    obtain ⟨hx1, hx2⟩ := TRel_tupSplit hfx
    obtain ⟨hy1, hy2⟩ := TRel_tupSplit hfy
    refine legalBlendTree_goBlend_wf u1 hm1 hx1 hy1 fun hG1 r1₁ r1₂ hr1 => ?_
    refine legalBlendTree_goBlend_wf u2 (TRel_argRel_weaken' hG1 hm2)
      (TRel_argRel_weaken' hG1 hx2) (TRel_argRel_weaken' hG1 hy2) fun hG2 r2₁ r2₂ hr2 =>
      hk (sub_trans hG1 hG2) _ _ (TRel_tupAppend (TRel_argRel_weaken' hG2 hr1) hr2)

theorem legalBlendTree_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty} :
    ∀ (t : Ty) {G : Ctx V₁ V₂} {D : Ctx L₁ L₂}
      {ms₁ : Tup (Arg V₁) (target.legalTys t.mask)} {ms₂ : Tup (Arg V₂) (target.legalTys t.mask)}
      {xs₁ : Tup (Arg V₁) (target.legalTys t)} {xs₂ : Tup (Arg V₂) (target.legalTys t)}
      {ys₁ : Tup (Arg V₁) (target.legalTys t)} {ys₂ : Tup (Arg V₂) (target.legalTys t)},
      TRel (ArgRel G) ms₁ ms₂ → TRel (ArgRel G) xs₁ xs₂ → TRel (ArgRel G) ys₁ ys₂ →
      ∀ {k₁ : Tup (Arg V₁) (target.legalTys t) → Expr V₁ L₁ rs}
        {k₂ : Tup (Arg V₂) (target.legalTys t) → Expr V₂ L₂ rs},
      (∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂, TRel (ArgRel G') y₁ y₂ → Wf G' D (k₁ y₁) (k₂ y₂)) →
      Wf G D (legalBlendTree target t ms₁ xs₁ ys₁ k₁) (legalBlendTree target t ms₂ xs₂ ys₂ k₂)
  | .bool, _, _, ms₁, ms₂, xs₁, xs₂, ys₁, ys₂, hms, hxs, hys, _, _, hk => by
    rcases ms₁ with ⟨c₁, ⟨⟩⟩; rcases ms₂ with ⟨c₂, ⟨⟩⟩
    rcases xs₁ with ⟨a₁, ⟨⟩⟩; rcases xs₂ with ⟨a₂, ⟨⟩⟩
    rcases ys₁ with ⟨b₁, ⟨⟩⟩; rcases ys₂ with ⟨b₂, ⟨⟩⟩
    cases hms with | cons hc _ => cases hxs with | cons ha _ => cases hys with | cons hb _ =>
    simp only [legalBlendTree]
    split
    · exact Wf.let3 _ hc ha hb fun h1 r₁ r₂ hr => hk h1 _ _ (TRel.single hr)
    · exact emitBoolSelect_wf hc ha hb fun hG' r₁ r₂ hr => hk hG' _ _ (TRel.single hr)
  | .bits _, _, _, ms₁, ms₂, xs₁, xs₂, ys₁, ys₂, hms, hxs, hys, _, _, hk => by
    rcases ms₁ with ⟨c₁, ⟨⟩⟩; rcases ms₂ with ⟨c₂, ⟨⟩⟩
    rcases xs₁ with ⟨a₁, ⟨⟩⟩; rcases xs₂ with ⟨a₂, ⟨⟩⟩
    rcases ys₁ with ⟨b₁, ⟨⟩⟩; rcases ys₂ with ⟨b₂, ⟨⟩⟩
    cases hms with | cons hc _ => cases hxs with | cons ha _ => cases hys with | cons hb _ =>
    exact Wf.let3 _ hc ha hb fun h1 r₁ r₂ hr => hk h1 _ _ (TRel.single hr)
  | .float _, _, _, ms₁, ms₂, xs₁, xs₂, ys₁, ys₂, hms, hxs, hys, _, _, hk => by
    rcases ms₁ with ⟨c₁, ⟨⟩⟩; rcases ms₂ with ⟨c₂, ⟨⟩⟩
    rcases xs₁ with ⟨a₁, ⟨⟩⟩; rcases xs₂ with ⟨a₂, ⟨⟩⟩
    rcases ys₁ with ⟨b₁, ⟨⟩⟩; rcases ys₂ with ⟨b₂, ⟨⟩⟩
    cases hms with | cons hc _ => cases hxs with | cons ha _ => cases hys with | cons hb _ =>
    exact Wf.let3 _ hc ha hb fun h1 r₁ r₂ hr => hk h1 _ _ (TRel.single hr)
  | .pair t1 t2, _, _, ms₁, ms₂, xs₁, xs₂, ys₁, ys₂, hms, hxs, hys, k₁, k₂, hk =>
    splitLegalToLeaves_wf target (Ty.mask (.pair t1 t2)) hms fun hG1 fm₁ fm₂ hfm =>
    splitLegalToLeaves_wf target (.pair t1 t2) (TRel_argRel_weaken' hG1 hxs) fun hG2 fx₁ fx₂ hfx =>
    splitLegalToLeaves_wf target (.pair t1 t2) (TRel_argRel_weaken' (sub_trans hG1 hG2) hys) fun hG3 fy₁ fy₂ hfy =>
    legalBlendTree_goBlend_wf target (.pair t1 t2)
      (TRel_argRel_weaken' (sub_trans hG2 hG3) hfm)
      (TRel_argRel_weaken' hG3 hfx) hfy fun hG4 fr₁ fr₂ hfr =>
    packLeavesToLegal_wf target (.pair t1 t2) hfr fun hG5 y₁ y₂ hy =>
      hk (sub_trans hG1 (sub_trans hG2 (sub_trans hG3 (sub_trans hG4 hG5)))) y₁ y₂ hy

theorem legalFCmpTree_goFCmp_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    (o : FCmpOp) :
    ∀ (u : Ty) {G : Ctx V₁ V₂} {D : Ctx L₁ L₂}
      {fx₁ : Tup (Arg V₁) (target.leafTys u)} {fx₂ : Tup (Arg V₂) (target.leafTys u)}
      {fy₁ : Tup (Arg V₁) (target.leafTys u)} {fy₂ : Tup (Arg V₂) (target.leafTys u)},
      TRel (ArgRel G) fx₁ fx₂ → TRel (ArgRel G) fy₁ fy₂ →
      ∀ {k₁ : Tup (Arg V₁) (target.leafTys u.mask) → Expr V₁ L₁ rs}
        {k₂ : Tup (Arg V₂) (target.leafTys u.mask) → Expr V₂ L₂ rs},
      (∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂, TRel (ArgRel G') y₁ y₂ → Wf G' D (k₁ y₁) (k₂ y₂)) →
      Wf G D (legalFCmpTree.goFCmp target o u fx₁ fy₁ k₁)
             (legalFCmpTree.goFCmp target o u fx₂ fy₂ k₂)
  | .bool, _, _, _, _, _, _, _, _, _, _, _ => .hlt
  | .bits _, _, _, _, _, _, _, _, _, _, _, _ => .hlt
  | .float _, _, _, fx₁, fx₂, fy₁, fy₂, hfx, hfy, _, _, hk => by
    rcases fx₁ with ⟨a₁, ⟨⟩⟩; rcases fx₂ with ⟨a₂, ⟨⟩⟩
    rcases fy₁ with ⟨b₁, ⟨⟩⟩; rcases fy₂ with ⟨b₂, ⟨⟩⟩
    cases hfx with | cons ha _ => cases hfy with | cons hb _ =>
    exact Wf.let2 _ ha hb fun h1 r₁ r₂ hr => hk h1 _ _ (TRel.single hr)
  | .pair u1 u2, _, _, fx₁, fx₂, fy₁, fy₂, hfx, hfy, k₁, k₂, hk => by
    obtain ⟨hx1, hx2⟩ := TRel_tupSplit hfx
    obtain ⟨hy1, hy2⟩ := TRel_tupSplit hfy
    refine legalFCmpTree_goFCmp_wf o u1 hx1 hy1 fun hG1 m1₁ m1₂ hm1 => ?_
    refine legalFCmpTree_goFCmp_wf o u2 (TRel_argRel_weaken' hG1 hx2) (TRel_argRel_weaken' hG1 hy2)
      fun hG2 m2₁ m2₂ hm2 =>
        hk (sub_trans hG1 hG2) _ _ (TRel_tupAppend (TRel_argRel_weaken' hG2 hm1) hm2)

theorem legalFCmpTree_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    (o : FCmpOp) :
    ∀ (t : Ty) {G : Ctx V₁ V₂} {D : Ctx L₁ L₂}
      {xs₁ : Tup (Arg V₁) (target.legalTys t)} {xs₂ : Tup (Arg V₂) (target.legalTys t)}
      {ys₁ : Tup (Arg V₁) (target.legalTys t)} {ys₂ : Tup (Arg V₂) (target.legalTys t)},
      TRel (ArgRel G) xs₁ xs₂ → TRel (ArgRel G) ys₁ ys₂ →
      ∀ {k₁ : Tup (Arg V₁) (target.legalTys t.mask) → Expr V₁ L₁ rs}
        {k₂ : Tup (Arg V₂) (target.legalTys t.mask) → Expr V₂ L₂ rs},
      (∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂, TRel (ArgRel G') y₁ y₂ → Wf G' D (k₁ y₁) (k₂ y₂)) →
      Wf G D (legalFCmpTree target o t xs₁ ys₁ k₁) (legalFCmpTree target o t xs₂ ys₂ k₂)
  | .bool, _, _, _, _, _, _, _, _, _, _, _ => .hlt
  | .bits _, _, _, _, _, _, _, _, _, _, _, _ => .hlt
  | .float _, _, _, fx₁, fx₂, fy₁, fy₂, hfx, hfy, _, _, hk => by
    rcases fx₁ with ⟨a₁, ⟨⟩⟩; rcases fx₂ with ⟨a₂, ⟨⟩⟩
    rcases fy₁ with ⟨b₁, ⟨⟩⟩; rcases fy₂ with ⟨b₂, ⟨⟩⟩
    cases hfx with | cons ha _ => cases hfy with | cons hb _ =>
    exact Wf.let2 _ ha hb fun h1 r₁ r₂ hr => hk h1 _ _ (TRel.single hr)
  | .pair t1 t2, _, _, xs₁, xs₂, ys₁, ys₂, hxs, hys, k₁, k₂, hk =>
    splitLegalToLeaves_wf target (.pair t1 t2) hxs fun hG1 fx₁ fx₂ hfx =>
    splitLegalToLeaves_wf target (.pair t1 t2) (TRel_argRel_weaken' hG1 hys) fun hG2 fy₁ fy₂ hfy =>
    legalFCmpTree_goFCmp_wf target o (.pair t1 t2) (TRel_argRel_weaken' hG2 hfx) hfy fun hG3 mr₁ mr₂ hmr =>
    packLeavesToLegal_wf target (Ty.mask (.pair t1 t2)) hmr fun hG4 y₁ y₂ hy =>
      hk (sub_trans hG1 (sub_trans hG2 (sub_trans hG3 hG4))) y₁ y₂ hy

private theorem legalSimdScalar128_go_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {on128₁ : Arg V₁ i32 → Arg V₁ i32 → Arg V₁ i32 → Arg V₁ i32 →
              Arg V₁ i32 → Arg V₁ i32 → Arg V₁ i32 → Arg V₁ i32 →
              (Arg V₁ i32 → Arg V₁ i32 → Arg V₁ i32 → Arg V₁ i32 → Expr V₁ L₁ rs) → Expr V₁ L₁ rs}
    {on128₂ : Arg V₂ i32 → Arg V₂ i32 → Arg V₂ i32 → Arg V₂ i32 →
              Arg V₂ i32 → Arg V₂ i32 → Arg V₂ i32 → Arg V₂ i32 →
              (Arg V₂ i32 → Arg V₂ i32 → Arg V₂ i32 → Arg V₂ i32 → Expr V₂ L₂ rs) → Expr V₂ L₂ rs}
    (hon : ∀ {G : Ctx V₁ V₂} {D : Ctx L₁ L₂}
      {a0₁ a1₁ a2₁ a3₁ b0₁ b1₁ b2₁ b3₁ : Arg V₁ i32}
      {a0₂ a1₂ a2₂ a3₂ b0₂ b1₂ b2₂ b3₂ : Arg V₂ i32}
      {cont₁ : Arg V₁ i32 → Arg V₁ i32 → Arg V₁ i32 → Arg V₁ i32 → Expr V₁ L₁ rs}
      {cont₂ : Arg V₂ i32 → Arg V₂ i32 → Arg V₂ i32 → Arg V₂ i32 → Expr V₂ L₂ rs},
      ArgRel G i32 a0₁ a0₂ → ArgRel G i32 a1₁ a1₂ → ArgRel G i32 a2₁ a2₂ → ArgRel G i32 a3₁ a3₂ →
      ArgRel G i32 b0₁ b0₂ → ArgRel G i32 b1₁ b1₂ → ArgRel G i32 b2₁ b2₂ → ArgRel G i32 b3₁ b3₂ →
      (∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ r0₁ r1₁ r2₁ r3₁ r0₂ r1₂ r2₂ r3₂,
        ArgRel G' i32 r0₁ r0₂ → ArgRel G' i32 r1₁ r1₂ → ArgRel G' i32 r2₁ r2₂ → ArgRel G' i32 r3₁ r3₂ →
        Wf G' D (cont₁ r0₁ r1₁ r2₁ r3₁) (cont₂ r0₂ r1₂ r2₂ r3₂)) →
      Wf G D (on128₁ a0₁ a1₁ a2₁ a3₁ b0₁ b1₁ b2₁ b3₁ cont₁)
             (on128₂ a0₂ a1₂ a2₂ a3₂ b0₂ b1₂ b2₂ b3₂ cont₂))
    (t : Ty) {G0 : Ctx V₁ V₂} {D : Ctx L₁ L₂}
    {k₁ : Tup (Arg V₁) (target.legalTys t) → Expr V₁ L₁ rs}
    {k₂ : Tup (Arg V₂) (target.legalTys t) → Expr V₂ L₂ rs}
    (hk : ∀ {G'}, (∀ p ∈ G0, p ∈ G') → ∀ y₁ y₂, TRel (ArgRel G') y₁ y₂ → Wf G' D (k₁ y₁) (k₂ y₂)) :
    ∀ (wx'₁ : List (Arg V₁ i64)) {G' : Ctx V₁ V₂} {wx'₂ : List (Arg V₂ i64)}
      {wy'₁ : List (Arg V₁ i64)} {wy'₂ : List (Arg V₂ i64)}
      {acc₁ : List (Arg V₁ i64)} {acc₂ : List (Arg V₂ i64)},
      ListRel (ArgRel G' i64) wx'₁ wx'₂ →
      ListRel (ArgRel G' i64) wy'₁ wy'₂ →
      ListRel (ArgRel G' i64) acc₁ acc₂ →
      (∀ p ∈ G0, p ∈ G') →
      Wf G' D
        (legalSimdScalar128.goWords target on128₁ t k₁ wx'₁ wy'₁ acc₁)
        (legalSimdScalar128.goWords target on128₂ t k₂ wx'₂ wy'₂ acc₂)
  | [], _, _, _, _, _, _, .nil, _, hacc, hsub =>
    unpackWords64ToLeaves_wf target t hacc 0 fun hG5 _ _ hfr =>
      packLeavesToLegal_wf target t hfr fun hG6 y₁ y₂ hy =>
        hk (sub_trans hsub (sub_trans hG5 hG6)) y₁ y₂ hy
  | [_], _, _, _, _, _, _, .cons _ .nil, _, hacc, hsub =>
    unpackWords64ToLeaves_wf target t hacc 0 fun hG5 _ _ hfr =>
      packLeavesToLegal_wf target t hfr fun hG6 y₁ y₂ hy =>
        hk (sub_trans hsub (sub_trans hG5 hG6)) y₁ y₂ hy
  | _ :: _ :: rx₁, _G', _ :: _ :: _rx₂, wy'₁, wy'₂, _acc₁, _acc₂,
      .cons hx0 (.cons hx1 hrest), hwy', hacc, hsub =>
    match wy'₁, wy'₂, hwy' with
    | [], _, .nil =>
      unpackWords64ToLeaves_wf target t hacc 0 fun hG5 _ _ hfr =>
        packLeavesToLegal_wf target t hfr fun hG6 y₁ y₂ hy =>
          hk (sub_trans hsub (sub_trans hG5 hG6)) y₁ y₂ hy
    | [_], _, .cons _ .nil =>
      unpackWords64ToLeaves_wf target t hacc 0 fun hG5 _ _ hfr =>
        packLeavesToLegal_wf target t hfr fun hG6 y₁ y₂ hy =>
          hk (sub_trans hsub (sub_trans hG5 hG6)) y₁ y₂ hy
    | _ :: _ :: _, _ :: _ :: _, .cons hy0 (.cons hy1 hwyrest) =>
      words2ToDwords4_wf hx0 hx1 fun hGa _a0₁ _a1₁ _a2₁ _a3₁ _a0₂ _a1₂ _a2₂ _a3₂ ha0 ha1 ha2 ha3 =>
      words2ToDwords4_wf (hy0.weaken hGa) (hy1.weaken hGa) fun hGb _b0₁ _b1₁ _b2₁ _b3₁ _b0₂ _b1₂ _b2₂ _b3₂ hb0 hb1 hb2 hb3 =>
      hon (ha0.weaken hGb) (ha1.weaken hGb) (ha2.weaken hGb) (ha3.weaken hGb) hb0 hb1 hb2 hb3
        fun hGc _r0₁ _r1₁ _r2₁ _r3₁ _r0₂ _r1₂ _r2₂ _r3₂ hr0 hr1 hr2 hr3 =>
      dwords4ToWords2_wf hr0 hr1 hr2 hr3 fun hGd _w0₁ _w1₁ _w0₂ _w1₂ hw0 hw1 =>
      have hsd := sub_trans hGa (sub_trans hGb (sub_trans hGc hGd))
      legalSimdScalar128_go_wf hon t hk rx₁
        (listRel_weaken hsd hrest) (listRel_weaken hsd hwyrest)
        ((listRel_weaken hsd hacc).append (.cons hw0 (.cons hw1 .nil)))
        (sub_trans hsub hsd)

theorem legalSimdScalar128_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {on128₁ : Arg V₁ i32 → Arg V₁ i32 → Arg V₁ i32 → Arg V₁ i32 →
              Arg V₁ i32 → Arg V₁ i32 → Arg V₁ i32 → Arg V₁ i32 →
              (Arg V₁ i32 → Arg V₁ i32 → Arg V₁ i32 → Arg V₁ i32 → Expr V₁ L₁ rs) → Expr V₁ L₁ rs}
    {on128₂ : Arg V₂ i32 → Arg V₂ i32 → Arg V₂ i32 → Arg V₂ i32 →
              Arg V₂ i32 → Arg V₂ i32 → Arg V₂ i32 → Arg V₂ i32 →
              (Arg V₂ i32 → Arg V₂ i32 → Arg V₂ i32 → Arg V₂ i32 → Expr V₂ L₂ rs) → Expr V₂ L₂ rs}
    (hon : ∀ {G : Ctx V₁ V₂} {D : Ctx L₁ L₂}
      {a0₁ a1₁ a2₁ a3₁ b0₁ b1₁ b2₁ b3₁ : Arg V₁ i32}
      {a0₂ a1₂ a2₂ a3₂ b0₂ b1₂ b2₂ b3₂ : Arg V₂ i32}
      {cont₁ : Arg V₁ i32 → Arg V₁ i32 → Arg V₁ i32 → Arg V₁ i32 → Expr V₁ L₁ rs}
      {cont₂ : Arg V₂ i32 → Arg V₂ i32 → Arg V₂ i32 → Arg V₂ i32 → Expr V₂ L₂ rs},
      ArgRel G i32 a0₁ a0₂ → ArgRel G i32 a1₁ a1₂ → ArgRel G i32 a2₁ a2₂ → ArgRel G i32 a3₁ a3₂ →
      ArgRel G i32 b0₁ b0₂ → ArgRel G i32 b1₁ b1₂ → ArgRel G i32 b2₁ b2₂ → ArgRel G i32 b3₁ b3₂ →
      (∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ r0₁ r1₁ r2₁ r3₁ r0₂ r1₂ r2₂ r3₂,
        ArgRel G' i32 r0₁ r0₂ → ArgRel G' i32 r1₁ r1₂ → ArgRel G' i32 r2₁ r2₂ → ArgRel G' i32 r3₁ r3₂ →
        Wf G' D (cont₁ r0₁ r1₁ r2₁ r3₁) (cont₂ r0₂ r1₂ r2₂ r3₂)) →
      Wf G D (on128₁ a0₁ a1₁ a2₁ a3₁ b0₁ b1₁ b2₁ b3₁ cont₁)
             (on128₂ a0₂ a1₂ a2₂ a3₂ b0₂ b1₂ b2₂ b3₂ cont₂))
    (t : Ty) {G : Ctx V₁ V₂} {D : Ctx L₁ L₂}
    {xs₁ : Tup (Arg V₁) (target.legalTys t)} {xs₂ : Tup (Arg V₂) (target.legalTys t)}
    {ys₁ : Tup (Arg V₁) (target.legalTys t)} {ys₂ : Tup (Arg V₂) (target.legalTys t)}
    (hxs : TRel (ArgRel G) xs₁ xs₂) (hys : TRel (ArgRel G) ys₁ ys₂)
    {k₁ : Tup (Arg V₁) (target.legalTys t) → Expr V₁ L₁ rs}
    {k₂ : Tup (Arg V₂) (target.legalTys t) → Expr V₂ L₂ rs}
    (hk : ∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂, TRel (ArgRel G') y₁ y₂ → Wf G' D (k₁ y₁) (k₂ y₂)) :
    Wf G D (legalSimdScalar128 target on128₁ t xs₁ ys₁ k₁)
           (legalSimdScalar128 target on128₂ t xs₂ ys₂ k₂) := by
  refine splitLegalToLeaves_wf target t hxs fun hG1 fx₁ fx₂ hfx =>
    splitLegalToLeaves_wf target t (TRel_argRel_weaken' hG1 hys) fun hG2 fy₁ fy₂ hfy =>
      packLeavesToWords64_wf target t (TRel_argRel_weaken' hG2 hfx) fun hG3 wx₁ wx₂ hwx =>
        packLeavesToWords64_wf target t (TRel_argRel_weaken' hG3 hfy) fun hG4 wy₁ wy₂ hwy =>
          legalSimdScalar128_go_wf target hon t hk _ (listRel_weaken hG4 hwx) hwy .nil
            (sub_trans hG1 (sub_trans hG2 (sub_trans hG3 hG4)))

theorem legalShufd_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    (imm : BitVec 8) :
    ∀ (t : Ty) {G : Ctx V₁ V₂} {D : Ctx L₁ L₂}
      {xs₁ : Tup (Arg V₁) (target.legalTys t)} {xs₂ : Tup (Arg V₂) (target.legalTys t)},
      TRel (ArgRel G) xs₁ xs₂ →
      ∀ {k₁ : Tup (Arg V₁) (target.legalTys t) → Expr V₁ L₁ rs}
        {k₂ : Tup (Arg V₂) (target.legalTys t) → Expr V₂ L₂ rs},
      (∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂, TRel (ArgRel G') y₁ y₂ → Wf G' D (k₁ y₁) (k₂ y₂)) →
      Wf G D (legalShufd target imm t xs₁ k₁) (legalShufd target imm t xs₂ k₂) := by
  have h128 : ∀ {G : Ctx V₁ V₂} {D : Ctx L₁ L₂}
      {a0₁ a1₁ a2₁ a3₁ b0₁ b1₁ b2₁ b3₁ : Arg V₁ i32}
      {a0₂ a1₂ a2₂ a3₂ b0₂ b1₂ b2₂ b3₂ : Arg V₂ i32}
      {cont₁ : Arg V₁ i32 → Arg V₁ i32 → Arg V₁ i32 → Arg V₁ i32 → Expr V₁ L₁ rs}
      {cont₂ : Arg V₂ i32 → Arg V₂ i32 → Arg V₂ i32 → Arg V₂ i32 → Expr V₂ L₂ rs},
      ArgRel G i32 a0₁ a0₂ → ArgRel G i32 a1₁ a1₂ → ArgRel G i32 a2₁ a2₂ → ArgRel G i32 a3₁ a3₂ →
      ArgRel G i32 b0₁ b0₂ → ArgRel G i32 b1₁ b1₂ → ArgRel G i32 b2₁ b2₂ → ArgRel G i32 b3₁ b3₂ →
      (∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ r0₁ r1₁ r2₁ r3₁ r0₂ r1₂ r2₂ r3₂,
        ArgRel G' i32 r0₁ r0₂ → ArgRel G' i32 r1₁ r1₂ → ArgRel G' i32 r2₁ r2₂ → ArgRel G' i32 r3₁ r3₂ →
        Wf G' D (cont₁ r0₁ r1₁ r2₁ r3₁) (cont₂ r0₂ r1₂ r2₂ r3₂)) →
      Wf G D (let (r0, r1, r2, r3) := scalarShufd128 imm a0₁ a1₁ a2₁ a3₁; cont₁ r0 r1 r2 r3)
             (let (r0, r1, r2, r3) := scalarShufd128 imm a0₂ a1₂ a2₂ a3₂; cont₂ r0 r1 r2 r3) := by
    intro G D a0₁ a1₁ a2₁ a3₁ _ _ _ _ a0₂ a1₂ a2₂ a3₂ _ _ _ _ cont₁ cont₂ ha0 ha1 ha2 ha3 _ _ _ _ hcont
    exact hcont (fun _ p => p) _ _ _ _ _ _ _ _
      (by dsimp only; split <;> assumption)
      (by dsimp only; split <;> assumption)
      (by dsimp only; split <;> assumption)
      (by dsimp only; split <;> assumption)
  intro t G D xs₁ xs₂ hxs k₁ k₂ hk
  induction t generalizing G with
  | bool | bits _ | float _ =>
    simp only [legalShufd]
    split
    · exact .hlt
    · exact legalSimdScalar128_wf target h128 _ hxs hxs hk
  | pair a b iha ihb =>
    simp only [legalShufd]
    split
    · exact .hlt
    · split
      · next h =>
        obtain ⟨hx1, _⟩ := TRel.cons_iff.1 (packedToTup_rel h hxs)
        split
        · exact Wf.let1 (.shufd (.pair a b) imm) hx1 fun hG' r₁ r₂ hr =>
            hk hG' _ _ (tupToPacked_rel h (.cons hr .nil))
        · exact legalSimdScalar128_wf target h128 (.pair a b) hxs hxs hk
      · next h =>
        split
        · have hff := Bool.eq_false_iff.mpr h
          obtain ⟨xa, xb⟩ := TRel_tupSplit (splitToTup_rel hff hxs)
          exact iha xa fun hG1 ra₁ ra₂ hra =>
            ihb (TRel_argRel_weaken' hG1 xb) fun hG2 rb₁ rb₂ hrb =>
              hk (sub_trans hG1 hG2) _ _
                (tupToSplit_rel hff (TRel_tupAppend (TRel_argRel_weaken' hG2 hra) hrb))
        · exact legalSimdScalar128_wf target h128 (.pair a b) hxs hxs hk

theorem legalBlendw_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    (imm : BitVec 8) :
    ∀ (t : Ty) {G : Ctx V₁ V₂} {D : Ctx L₁ L₂}
      {xs₁ : Tup (Arg V₁) (target.legalTys t)} {xs₂ : Tup (Arg V₂) (target.legalTys t)}
      {ys₁ : Tup (Arg V₁) (target.legalTys t)} {ys₂ : Tup (Arg V₂) (target.legalTys t)},
      TRel (ArgRel G) xs₁ xs₂ → TRel (ArgRel G) ys₁ ys₂ →
      ∀ {k₁ : Tup (Arg V₁) (target.legalTys t) → Expr V₁ L₁ rs}
        {k₂ : Tup (Arg V₂) (target.legalTys t) → Expr V₂ L₂ rs},
      (∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂, TRel (ArgRel G') y₁ y₂ → Wf G' D (k₁ y₁) (k₂ y₂)) →
      Wf G D (legalBlendw target imm t xs₁ ys₁ k₁) (legalBlendw target imm t xs₂ ys₂ k₂) := by
  intro t G D xs₁ xs₂ ys₁ ys₂ hxs hys k₁ k₂ hk
  induction t generalizing G with
  | bool | bits _ | float _ =>
    simp only [legalBlendw]
    split
    · exact .hlt
    · exact legalSimdScalar128_wf target (fun ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 cont =>
        scalarBlendw128_wf imm ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 cont) _ hxs hys hk
  | pair a b iha ihb =>
    simp only [legalBlendw]
    split
    · exact .hlt
    · split
      · next h =>
        obtain ⟨hx1, _⟩ := TRel.cons_iff.1 (packedToTup_rel h hxs)
        obtain ⟨hy1, _⟩ := TRel.cons_iff.1 (packedToTup_rel h hys)
        split
        · exact Wf.let2 (.blendw (.pair a b) imm) hx1 hy1 fun hG' r₁ r₂ hr =>
            hk hG' _ _ (tupToPacked_rel h (.cons hr .nil))
        · exact legalSimdScalar128_wf target (fun ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 cont =>
            scalarBlendw128_wf imm ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 cont) (.pair a b) hxs hys hk
      · next h =>
        split
        · have hff := Bool.eq_false_iff.mpr h
          obtain ⟨xa, xb⟩ := TRel_tupSplit (splitToTup_rel hff hxs)
          obtain ⟨ya, yb⟩ := TRel_tupSplit (splitToTup_rel hff hys)
          exact iha xa ya fun hG1 ra₁ ra₂ hra =>
            ihb (TRel_argRel_weaken' hG1 xb) (TRel_argRel_weaken' hG1 yb) fun hG2 rb₁ rb₂ hrb =>
              hk (sub_trans hG1 hG2) _ _
                (tupToSplit_rel hff (TRel_tupAppend (TRel_argRel_weaken' hG2 hra) hrb))
        · exact legalSimdScalar128_wf target (fun ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 cont =>
            scalarBlendw128_wf imm ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 cont) (.pair a b) hxs hys hk

theorem legalAlignr_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    (imm : BitVec 8) :
    ∀ (t : Ty) {G : Ctx V₁ V₂} {D : Ctx L₁ L₂}
      {xs₁ : Tup (Arg V₁) (target.legalTys t)} {xs₂ : Tup (Arg V₂) (target.legalTys t)}
      {ys₁ : Tup (Arg V₁) (target.legalTys t)} {ys₂ : Tup (Arg V₂) (target.legalTys t)},
      TRel (ArgRel G) xs₁ xs₂ → TRel (ArgRel G) ys₁ ys₂ →
      ∀ {k₁ : Tup (Arg V₁) (target.legalTys t) → Expr V₁ L₁ rs}
        {k₂ : Tup (Arg V₂) (target.legalTys t) → Expr V₂ L₂ rs},
      (∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂, TRel (ArgRel G') y₁ y₂ → Wf G' D (k₁ y₁) (k₂ y₂)) →
      Wf G D (legalAlignr target imm t xs₁ ys₁ k₁) (legalAlignr target imm t xs₂ ys₂ k₂) := by
  intro t G D xs₁ xs₂ ys₁ ys₂ hxs hys k₁ k₂ hk
  induction t generalizing G with
  | bool | bits _ | float _ =>
    simp only [legalAlignr]
    split
    · exact .hlt
    · exact legalSimdScalar128_wf target (fun hh0 hh1 hh2 hh3 hl0 hl1 hl2 hl3 cont =>
        scalarAlignr128_wf imm hh0 hh1 hh2 hh3 hl0 hl1 hl2 hl3 cont) _ hxs hys hk
  | pair a b iha ihb =>
    simp only [legalAlignr]
    split
    · exact .hlt
    · split
      · next h =>
        obtain ⟨hx1, _⟩ := TRel.cons_iff.1 (packedToTup_rel h hxs)
        obtain ⟨hy1, _⟩ := TRel.cons_iff.1 (packedToTup_rel h hys)
        split
        · exact Wf.let2 (.alignr (.pair a b) imm) hx1 hy1 fun hG' r₁ r₂ hr =>
            hk hG' _ _ (tupToPacked_rel h (.cons hr .nil))
        · exact legalSimdScalar128_wf target (fun hh0 hh1 hh2 hh3 hl0 hl1 hl2 hl3 cont =>
            scalarAlignr128_wf imm hh0 hh1 hh2 hh3 hl0 hl1 hl2 hl3 cont) (.pair a b) hxs hys hk
      · next h =>
        split
        · have hff := Bool.eq_false_iff.mpr h
          obtain ⟨xa, xb⟩ := TRel_tupSplit (splitToTup_rel hff hxs)
          obtain ⟨ya, yb⟩ := TRel_tupSplit (splitToTup_rel hff hys)
          exact iha xa ya fun hG1 ra₁ ra₂ hra =>
            ihb (TRel_argRel_weaken' hG1 xb) (TRel_argRel_weaken' hG1 yb) fun hG2 rb₁ rb₂ hrb =>
              hk (sub_trans hG1 hG2) _ _
                (tupToSplit_rel hff (TRel_tupAppend (TRel_argRel_weaken' hG2 hra) hrb))
        · exact legalSimdScalar128_wf target (fun hh0 hh1 hh2 hh3 hl0 hl1 hl2 hl3 cont =>
            scalarAlignr128_wf imm hh0 hh1 hh2 hh3 hl0 hl1 hl2 hl3 cont) (.pair a b) hxs hys hk

theorem legalShufb_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty} :
    ∀ (t : Ty) {G : Ctx V₁ V₂} {D : Ctx L₁ L₂}
      {xs₁ : Tup (Arg V₁) (target.legalTys t)} {xs₂ : Tup (Arg V₂) (target.legalTys t)}
      {ys₁ : Tup (Arg V₁) (target.legalTys t)} {ys₂ : Tup (Arg V₂) (target.legalTys t)},
      TRel (ArgRel G) xs₁ xs₂ → TRel (ArgRel G) ys₁ ys₂ →
      ∀ {k₁ : Tup (Arg V₁) (target.legalTys t) → Expr V₁ L₁ rs}
        {k₂ : Tup (Arg V₂) (target.legalTys t) → Expr V₂ L₂ rs},
      (∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂, TRel (ArgRel G') y₁ y₂ → Wf G' D (k₁ y₁) (k₂ y₂)) →
      Wf G D (legalShufb target t xs₁ ys₁ k₁) (legalShufb target t xs₂ ys₂ k₂) := by
  intro t G D xs₁ xs₂ ys₁ ys₂ hxs hys k₁ k₂ hk
  induction t generalizing G with
  | bool | bits _ | float _ =>
    simp only [legalShufb]
    split
    · exact .hlt
    · exact legalSimdScalar128_wf target (fun ha0 ha1 ha2 ha3 hm0 hm1 hm2 hm3 cont =>
        scalarShufb128_wf ha0 ha1 ha2 ha3 hm0 hm1 hm2 hm3 cont) _ hxs hys hk
  | pair a b iha ihb =>
    simp only [legalShufb]
    split
    · exact .hlt
    · split
      · next h =>
        obtain ⟨hx1, _⟩ := TRel.cons_iff.1 (packedToTup_rel h hxs)
        obtain ⟨hy1, _⟩ := TRel.cons_iff.1 (packedToTup_rel h hys)
        split
        · exact Wf.let2 (.shufb (.pair a b)) hx1 hy1 fun hG' r₁ r₂ hr =>
            hk hG' _ _ (tupToPacked_rel h (.cons hr .nil))
        · exact legalSimdScalar128_wf target (fun ha0 ha1 ha2 ha3 hm0 hm1 hm2 hm3 cont =>
            scalarShufb128_wf ha0 ha1 ha2 ha3 hm0 hm1 hm2 hm3 cont) (.pair a b) hxs hys hk
      · next h =>
        split
        · have hff := Bool.eq_false_iff.mpr h
          obtain ⟨xa, xb⟩ := TRel_tupSplit (splitToTup_rel hff hxs)
          obtain ⟨ya, yb⟩ := TRel_tupSplit (splitToTup_rel hff hys)
          exact iha xa ya fun hG1 ra₁ ra₂ hra =>
            ihb (TRel_argRel_weaken' hG1 xb) (TRel_argRel_weaken' hG1 yb) fun hG2 rb₁ rb₂ hrb =>
              hk (sub_trans hG1 hG2) _ _
                (tupToSplit_rel hff (TRel_tupAppend (TRel_argRel_weaken' hG2 hra) hrb))
        · exact legalSimdScalar128_wf target (fun ha0 ha1 ha2 ha3 hm0 hm1 hm2 hm3 cont =>
            scalarShufb128_wf ha0 ha1 ha2 ha3 hm0 hm1 hm2 hm3 cont) (.pair a b) hxs hys hk

theorem legalFloatBit2_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂}
    (mkOp : (w : Nat) → OpCode [.bits w, .bits w] [.bits w])
    (mkFOp : (f : Fmt) → OpCode [.float f, .float f] [.float f])
    (f : Fmt) {x₁ y₁ : Arg V₁ (.float f)} {x₂ y₂ : Arg V₂ (.float f)}
    (hx : ArgRel G (.float f) x₁ x₂) (hy : ArgRel G (.float f) y₁ y₂)
    {k₁ : Arg V₁ (.float f) → Expr V₁ L₁ rs} {k₂ : Arg V₂ (.float f) → Expr V₂ L₂ rs}
    (hk : ∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ r₁ r₂, ArgRel G' (.float f) r₁ r₂ → Wf G' D (k₁ r₁) (k₂ r₂)) :
    Wf G D (legalFloatBit2 target mkOp mkFOp f x₁ y₁ k₁)
           (legalFloatBit2 target mkOp mkFOp f x₂ y₂ k₂) := by
  simp only [legalFloatBit2]
  split
  · exact Wf.let2 (mkFOp f) hx hy hk
  · exact Wf.let1 _ hx fun h1 bx₁ bx₂ hbx =>
      Wf.let1 _ (hy.weaken h1) fun h2 by₁ by₂ hby =>
        Wf.let2 (mkOp f.width) (hbx.weaken h2) hby fun h3 br₁ br₂ hbr =>
          Wf.let1 _ hbr fun h4 r₁ r₂ hr =>
            hk (sub_trans h1 (sub_trans h2 (sub_trans h3 h4))) r₁ r₂ hr

private theorem sha256rnds2_scalar_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂}
    {lc₁ la₁ lw₁ : Tup (Arg V₁) (target.legalTys v4i32)}
    {lc₂ la₂ lw₂ : Tup (Arg V₂) (target.legalTys v4i32)}
    (hlc : TRel (ArgRel G) lc₁ lc₂) (hla : TRel (ArgRel G) la₁ la₂) (hlw : TRel (ArgRel G) lw₁ lw₂)
    {c₁ : Tup (Arg V₁) (target.legalTys v4i32) → Expr V₁ L₁ rs}
    {c₂ : Tup (Arg V₂) (target.legalTys v4i32) → Expr V₂ L₂ rs}
    (hk : ∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂, TRel (ArgRel G') y₁ y₂ → Wf G' D (c₁ y₁) (c₂ y₂)) :
    Wf G D
      (splitLegalToLeaves target v4i32 lc₁ fun fc =>
       splitLegalToLeaves target v4i32 la₁ fun fa =>
       splitLegalToLeaves target v4i32 lw₁ fun fw =>
       packLeavesToWords64 target v4i32 fc fun wc =>
       packLeavesToWords64 target v4i32 fa fun wa =>
       packLeavesToWords64 target v4i32 fw fun ww =>
       words2ToDwords4 (wc.getD 0 (.imm 0#64)) (wc.getD 1 (.imm 0#64)) fun cd0 cd1 cd2 cd3 =>
       words2ToDwords4 (wa.getD 0 (.imm 0#64)) (wa.getD 1 (.imm 0#64)) fun ab0 ab1 ab2 ab3 =>
       words2ToDwords4 (ww.getD 0 (.imm 0#64)) (ww.getD 1 (.imm 0#64)) fun wk0 wk1 wk2 wk3 =>
       scalarSha256rnds2 cd0 cd1 cd2 cd3 ab0 ab1 ab2 ab3 wk0 wk1 wk2 wk3 fun r0 r1 r2 r3 =>
       dwords4ToWords2 r0 r1 r2 r3 fun w0 w1 =>
       unpackWords64ToLeaves target [w0, w1] 0 v4i32 fun fres =>
       packLeavesToLegal target v4i32 fres c₁)
      (splitLegalToLeaves target v4i32 lc₂ fun fc =>
       splitLegalToLeaves target v4i32 la₂ fun fa =>
       splitLegalToLeaves target v4i32 lw₂ fun fw =>
       packLeavesToWords64 target v4i32 fc fun wc =>
       packLeavesToWords64 target v4i32 fa fun wa =>
       packLeavesToWords64 target v4i32 fw fun ww =>
       words2ToDwords4 (wc.getD 0 (.imm 0#64)) (wc.getD 1 (.imm 0#64)) fun cd0 cd1 cd2 cd3 =>
       words2ToDwords4 (wa.getD 0 (.imm 0#64)) (wa.getD 1 (.imm 0#64)) fun ab0 ab1 ab2 ab3 =>
       words2ToDwords4 (ww.getD 0 (.imm 0#64)) (ww.getD 1 (.imm 0#64)) fun wk0 wk1 wk2 wk3 =>
       scalarSha256rnds2 cd0 cd1 cd2 cd3 ab0 ab1 ab2 ab3 wk0 wk1 wk2 wk3 fun r0 r1 r2 r3 =>
       dwords4ToWords2 r0 r1 r2 r3 fun w0 w1 =>
       unpackWords64ToLeaves target [w0, w1] 0 v4i32 fun fres =>
       packLeavesToLegal target v4i32 fres c₂) :=
  splitLegalToLeaves_wf target v4i32 hlc fun p0 _fc₁ _fc₂ hfc =>
  splitLegalToLeaves_wf target v4i32 (TRel_argRel_weaken' p0 hla) fun p1 _fa₁ _fa₂ hfa =>
  splitLegalToLeaves_wf target v4i32 (TRel_argRel_weaken' (sub_trans p0 p1) hlw) fun p2 _fw₁ _fw₂ hfw =>
  packLeavesToWords64_wf target v4i32 (TRel_argRel_weaken' (sub_trans p1 p2) hfc) fun p3 _wc₁ _wc₂ hwc =>
  packLeavesToWords64_wf target v4i32 (TRel_argRel_weaken' (sub_trans p2 p3) hfa) fun p4 _wa₁ _wa₂ hwa =>
  packLeavesToWords64_wf target v4i32 (TRel_argRel_weaken' (sub_trans p3 p4) hfw) fun p5 _ww₁ _ww₂ hww =>
  have q5 := sub_trans p0 (sub_trans p1 (sub_trans p2 (sub_trans p3 (sub_trans p4 p5))))
  words2ToDwords4_wf ((listRel_weaken (sub_trans p4 p5) hwc).getD (ArgRel.imm (G := _) (0#64)) 0)
    ((listRel_weaken (sub_trans p4 p5) hwc).getD (ArgRel.imm (G := _) (0#64)) 1) fun p6 _cd0₁ _cd1₁ _cd2₁ _cd3₁ _cd0₂ _cd1₂ _cd2₂ _cd3₂ hcd0 hcd1 hcd2 hcd3 =>
  words2ToDwords4_wf ((listRel_weaken (sub_trans p5 p6) hwa).getD (ArgRel.imm (G := _) (0#64)) 0)
    ((listRel_weaken (sub_trans p5 p6) hwa).getD (ArgRel.imm (G := _) (0#64)) 1) fun p7 _ab0₁ _ab1₁ _ab2₁ _ab3₁ _ab0₂ _ab1₂ _ab2₂ _ab3₂ hab0 hab1 hab2 hab3 =>
  words2ToDwords4_wf ((listRel_weaken (sub_trans p6 p7) hww).getD (ArgRel.imm (G := _) (0#64)) 0)
    ((listRel_weaken (sub_trans p6 p7) hww).getD (ArgRel.imm (G := _) (0#64)) 1) fun p8 _wk0₁ _wk1₁ _wk2₁ _wk3₁ _wk0₂ _wk1₂ _wk2₂ _wk3₂ hwk0 hwk1 _hwk2 _hwk3 =>
  have q8 := sub_trans q5 (sub_trans p6 (sub_trans p7 p8))
  scalarSha256rnds2_wf (hcd0.weaken (sub_trans p7 p8)) (hcd1.weaken (sub_trans p7 p8))
    (hcd2.weaken (sub_trans p7 p8)) (hcd3.weaken (sub_trans p7 p8))
    (hab0.weaken p8) (hab1.weaken p8) (hab2.weaken p8) (hab3.weaken p8) hwk0 hwk1
    fun p9 _r0₁ _r1₁ _r2₁ _r3₁ _r0₂ _r1₂ _r2₂ _r3₂ hr0 hr1 hr2 hr3 =>
  dwords4ToWords2_wf hr0 hr1 hr2 hr3 fun pa _w0₁ _w1₁ _w0₂ _w1₂ hw0 hw1 =>
  unpackWords64ToLeaves_wf target v4i32 (.cons hw0 (.cons hw1 .nil)) 0 fun pb _fres₁ _fres₂ hfres =>
  packLeavesToLegal_wf target v4i32 hfres fun pc y₁ y₂ hy =>
    hk (sub_trans q8 (sub_trans p9 (sub_trans pa (sub_trans pb pc)))) y₁ y₂ hy

private theorem sha256msg1_scalar_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂}
    {la₁ lb₁ : Tup (Arg V₁) (target.legalTys v4i32)}
    {la₂ lb₂ : Tup (Arg V₂) (target.legalTys v4i32)}
    (hla : TRel (ArgRel G) la₁ la₂) (hlb : TRel (ArgRel G) lb₁ lb₂)
    {c₁ : Tup (Arg V₁) (target.legalTys v4i32) → Expr V₁ L₁ rs}
    {c₂ : Tup (Arg V₂) (target.legalTys v4i32) → Expr V₂ L₂ rs}
    (hk : ∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂, TRel (ArgRel G') y₁ y₂ → Wf G' D (c₁ y₁) (c₂ y₂)) :
    Wf G D
      (splitLegalToLeaves target v4i32 la₁ fun fa =>
       splitLegalToLeaves target v4i32 lb₁ fun fb =>
       packLeavesToWords64 target v4i32 fa fun wa =>
       packLeavesToWords64 target v4i32 fb fun wb =>
       words2ToDwords4 (wa.getD 0 (.imm 0#64)) (wa.getD 1 (.imm 0#64)) fun a0 a1 a2 a3 =>
       words2ToDwords4 (wb.getD 0 (.imm 0#64)) (wb.getD 1 (.imm 0#64)) fun b0 b1 b2 b3 =>
       scalarSha256msg1 a0 a1 a2 a3 b0 b1 b2 b3 fun r0 r1 r2 r3 =>
       dwords4ToWords2 r0 r1 r2 r3 fun w0 w1 =>
       unpackWords64ToLeaves target [w0, w1] 0 v4i32 fun fres =>
       packLeavesToLegal target v4i32 fres c₁)
      (splitLegalToLeaves target v4i32 la₂ fun fa =>
       splitLegalToLeaves target v4i32 lb₂ fun fb =>
       packLeavesToWords64 target v4i32 fa fun wa =>
       packLeavesToWords64 target v4i32 fb fun wb =>
       words2ToDwords4 (wa.getD 0 (.imm 0#64)) (wa.getD 1 (.imm 0#64)) fun a0 a1 a2 a3 =>
       words2ToDwords4 (wb.getD 0 (.imm 0#64)) (wb.getD 1 (.imm 0#64)) fun b0 b1 b2 b3 =>
       scalarSha256msg1 a0 a1 a2 a3 b0 b1 b2 b3 fun r0 r1 r2 r3 =>
       dwords4ToWords2 r0 r1 r2 r3 fun w0 w1 =>
       unpackWords64ToLeaves target [w0, w1] 0 v4i32 fun fres =>
       packLeavesToLegal target v4i32 fres c₂) :=
  splitLegalToLeaves_wf target v4i32 hla fun p0 _fa₁ _fa₂ hfa =>
  splitLegalToLeaves_wf target v4i32 (TRel_argRel_weaken' p0 hlb) fun p1 _fb₁ _fb₂ hfb =>
  packLeavesToWords64_wf target v4i32 (TRel_argRel_weaken' p1 hfa) fun p2 _wa₁ _wa₂ hwa =>
  packLeavesToWords64_wf target v4i32 (TRel_argRel_weaken' p2 hfb) fun p3 _wb₁ _wb₂ hwb =>
  have q3 := sub_trans p0 (sub_trans p1 (sub_trans p2 p3))
  words2ToDwords4_wf ((listRel_weaken p3 hwa).getD (ArgRel.imm (G := _) (0#64)) 0)
    ((listRel_weaken p3 hwa).getD (ArgRel.imm (G := _) (0#64)) 1) fun p4 _a0₁ _a1₁ _a2₁ _a3₁ _a0₂ _a1₂ _a2₂ _a3₂ ha0 ha1 ha2 ha3 =>
  words2ToDwords4_wf ((listRel_weaken p4 hwb).getD (ArgRel.imm (G := _) (0#64)) 0)
    ((listRel_weaken p4 hwb).getD (ArgRel.imm (G := _) (0#64)) 1) fun p5 _b0₁ _b1₁ _b2₁ _b3₁ _b0₂ _b1₂ _b2₂ _b3₂ hb0 _hb1 _hb2 _hb3 =>
  scalarSha256msg1_wf (ha0.weaken p5) (ha1.weaken p5) (ha2.weaken p5) (ha3.weaken p5) hb0
    fun p6 _r0₁ _r1₁ _r2₁ _r3₁ _r0₂ _r1₂ _r2₂ _r3₂ hr0 hr1 hr2 hr3 =>
  dwords4ToWords2_wf hr0 hr1 hr2 hr3 fun p7 _w0₁ _w1₁ _w0₂ _w1₂ hw0 hw1 =>
  unpackWords64ToLeaves_wf target v4i32 (.cons hw0 (.cons hw1 .nil)) 0 fun p8 _fres₁ _fres₂ hfres =>
  packLeavesToLegal_wf target v4i32 hfres fun p9 y₁ y₂ hy =>
    hk (sub_trans q3 (sub_trans p4 (sub_trans p5 (sub_trans p6 (sub_trans p7 (sub_trans p8 p9)))))) y₁ y₂ hy

private theorem sha256msg2_scalar_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂}
    {la₁ lb₁ : Tup (Arg V₁) (target.legalTys v4i32)}
    {la₂ lb₂ : Tup (Arg V₂) (target.legalTys v4i32)}
    (hla : TRel (ArgRel G) la₁ la₂) (hlb : TRel (ArgRel G) lb₁ lb₂)
    {c₁ : Tup (Arg V₁) (target.legalTys v4i32) → Expr V₁ L₁ rs}
    {c₂ : Tup (Arg V₂) (target.legalTys v4i32) → Expr V₂ L₂ rs}
    (hk : ∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂, TRel (ArgRel G') y₁ y₂ → Wf G' D (c₁ y₁) (c₂ y₂)) :
    Wf G D
      (splitLegalToLeaves target v4i32 la₁ fun fa =>
       splitLegalToLeaves target v4i32 lb₁ fun fb =>
       packLeavesToWords64 target v4i32 fa fun wa =>
       packLeavesToWords64 target v4i32 fb fun wb =>
       words2ToDwords4 (wa.getD 0 (.imm 0#64)) (wa.getD 1 (.imm 0#64)) fun s0 s1 s2 s3 =>
       words2ToDwords4 (wb.getD 0 (.imm 0#64)) (wb.getD 1 (.imm 0#64)) fun w0 w1 w2 w3 =>
       scalarSha256msg2 s0 s1 s2 s3 w0 w1 w2 w3 fun r0 r1 r2 r3 =>
       dwords4ToWords2 r0 r1 r2 r3 fun wr0 wr1 =>
       unpackWords64ToLeaves target [wr0, wr1] 0 v4i32 fun fres =>
       packLeavesToLegal target v4i32 fres c₁)
      (splitLegalToLeaves target v4i32 la₂ fun fa =>
       splitLegalToLeaves target v4i32 lb₂ fun fb =>
       packLeavesToWords64 target v4i32 fa fun wa =>
       packLeavesToWords64 target v4i32 fb fun wb =>
       words2ToDwords4 (wa.getD 0 (.imm 0#64)) (wa.getD 1 (.imm 0#64)) fun s0 s1 s2 s3 =>
       words2ToDwords4 (wb.getD 0 (.imm 0#64)) (wb.getD 1 (.imm 0#64)) fun w0 w1 w2 w3 =>
       scalarSha256msg2 s0 s1 s2 s3 w0 w1 w2 w3 fun r0 r1 r2 r3 =>
       dwords4ToWords2 r0 r1 r2 r3 fun wr0 wr1 =>
       unpackWords64ToLeaves target [wr0, wr1] 0 v4i32 fun fres =>
       packLeavesToLegal target v4i32 fres c₂) :=
  splitLegalToLeaves_wf target v4i32 hla fun p0 _fa₁ _fa₂ hfa =>
  splitLegalToLeaves_wf target v4i32 (TRel_argRel_weaken' p0 hlb) fun p1 _fb₁ _fb₂ hfb =>
  packLeavesToWords64_wf target v4i32 (TRel_argRel_weaken' p1 hfa) fun p2 _wa₁ _wa₂ hwa =>
  packLeavesToWords64_wf target v4i32 (TRel_argRel_weaken' p2 hfb) fun p3 _wb₁ _wb₂ hwb =>
  have q3 := sub_trans p0 (sub_trans p1 (sub_trans p2 p3))
  words2ToDwords4_wf ((listRel_weaken p3 hwa).getD (ArgRel.imm (G := _) (0#64)) 0)
    ((listRel_weaken p3 hwa).getD (ArgRel.imm (G := _) (0#64)) 1) fun p4 _s0₁ _s1₁ _s2₁ _s3₁ _s0₂ _s1₂ _s2₂ _s3₂ hs0 hs1 hs2 hs3 =>
  words2ToDwords4_wf ((listRel_weaken p4 hwb).getD (ArgRel.imm (G := _) (0#64)) 0)
    ((listRel_weaken p4 hwb).getD (ArgRel.imm (G := _) (0#64)) 1) fun p5 _w0₁ _w1₁ _w2₁ _w3₁ _w0₂ _w1₂ _w2₂ _w3₂ _hw0 _hw1 hw2 hw3 =>
  scalarSha256msg2_wf (hs0.weaken p5) (hs1.weaken p5) (hs2.weaken p5) (hs3.weaken p5) hw2 hw3
    fun p6 _r0₁ _r1₁ _r2₁ _r3₁ _r0₂ _r1₂ _r2₂ _r3₂ hr0 hr1 hr2 hr3 =>
  dwords4ToWords2_wf hr0 hr1 hr2 hr3 fun p7 _wr0₁ _wr1₁ _wr0₂ _wr1₂ hwr0 hwr1 =>
  unpackWords64ToLeaves_wf target v4i32 (.cons hwr0 (.cons hwr1 .nil)) 0 fun p8 _fres₁ _fres₂ hfres =>
  packLeavesToLegal_wf target v4i32 hfres fun p9 y₁ y₂ hy =>
    hk (sub_trans q3 (sub_trans p4 (sub_trans p5 (sub_trans p6 (sub_trans p7 (sub_trans p8 p9)))))) y₁ y₂ hy

theorem TRel.singleL {V₁ V₂ : Ty → Type} {G : Ctx V₁ V₂} {t : Ty}
    {x₁ : LVar target V₁ t} {x₂ : LVar target V₂ t} (h : TRel (ArgRel G) x₁ x₂) :
    TRel (fun _ a₁ a₂ => TRel (ArgRel G) a₁ a₂) (as := [t]) (x₁, PUnit.unit) (x₂, PUnit.unit) :=
  .cons h .nil

theorem TRel.pairL {V₁ V₂ : Ty → Type} {G : Ctx V₁ V₂} {t u : Ty}
    {x₁ : LVar target V₁ t} {x₂ : LVar target V₂ t}
    {y₁ : LVar target V₁ u} {y₂ : LVar target V₂ u}
    (hx : TRel (ArgRel G) x₁ x₂) (hy : TRel (ArgRel G) y₁ y₂) :
    TRel (fun _ a₁ a₂ => TRel (ArgRel G) a₁ a₂) (as := [t, u])
      (x₁, y₁, PUnit.unit) (x₂, y₂, PUnit.unit) :=
  .cons hx (.cons hy .nil)

private theorem trelBitsImmZero {V₁ V₂ : Ty → Type} {G : Ctx V₁ V₂} (n : Nat) :
    TRel (f := LVar target V₁) (g := LVar target V₂) (fun _ a₁ a₂ => TRel (ArgRel G) a₁ a₂) (as := [Ty.bits n])
      ((Arg.imm (0#(target.widenWidth n)), PUnit.unit), PUnit.unit)
      ((Arg.imm (0#(target.widenWidth n)), PUnit.unit), PUnit.unit) := by
  dsimp only [LVar]
  exact @TRel.singleL target V₁ V₂ G (.bits n) (Arg.imm (0#(target.widenWidth n)), PUnit.unit) _
    (TRel.single (ArgRel.imm _))

private theorem trelSingleBits {V₁ V₂ : Ty → Type} {G : Ctx V₁ V₂} (n : Nat)
    {x₁ : Arg V₁ (.bits (target.widenWidth n))} {x₂ : Arg V₂ (.bits (target.widenWidth n))}
    (h : ArgRel G (.bits (target.widenWidth n)) x₁ x₂) :
    TRel (f := LVar target V₁) (g := LVar target V₂) (fun _ a₁ a₂ => TRel (ArgRel G) a₁ a₂) (as := [Ty.bits n])
      ((x₁, PUnit.unit), PUnit.unit) ((x₂, PUnit.unit), PUnit.unit) := by
  dsimp only [LVar]
  exact @TRel.singleL target V₁ V₂ G (.bits n) (x₁, PUnit.unit) (x₂, PUnit.unit) (TRel.single h)

private theorem trelPairBits {V₁ V₂ : Ty → Type} {G : Ctx V₁ V₂} (n : Nat)
    {x₁ : Arg V₁ (.bits (target.widenWidth n))} {x₂ : Arg V₂ (.bits (target.widenWidth n))}
    {y₁ : Arg V₁ (.bits (target.widenWidth n))} {y₂ : Arg V₂ (.bits (target.widenWidth n))}
    (hx : ArgRel G (.bits (target.widenWidth n)) x₁ x₂)
    (hy : ArgRel G (.bits (target.widenWidth n)) y₁ y₂) :
    TRel (f := LVar target V₁) (g := LVar target V₂) (fun _ a₁ a₂ => TRel (ArgRel G) a₁ a₂) (as := [Ty.bits n, Ty.bits n])
      ((x₁, PUnit.unit), (y₁, PUnit.unit), PUnit.unit)
      ((x₂, PUnit.unit), (y₂, PUnit.unit), PUnit.unit) := by
  dsimp only [LVar]
  exact @TRel.pairL target V₁ V₂ G (.bits n) (.bits n) (x₁, PUnit.unit) (x₂, PUnit.unit)
    (y₁, PUnit.unit) (y₂, PUnit.unit) (TRel.single hx) (TRel.single hy)

private theorem trelPairBitsBool {V₁ V₂ : Ty → Type} {G : Ctx V₁ V₂} (n : Nat)
    {x₁ : Arg V₁ (.bits (target.widenWidth n))} {x₂ : Arg V₂ (.bits (target.widenWidth n))}
    {y₁ : Arg V₁ .bool} {y₂ : Arg V₂ .bool}
    (hx : ArgRel G (.bits (target.widenWidth n)) x₁ x₂)
    (hy : ArgRel G .bool y₁ y₂) :
    TRel (f := LVar target V₁) (g := LVar target V₂) (fun _ a₁ a₂ => TRel (ArgRel G) a₁ a₂) (as := [Ty.bits n, Ty.bool])
      ((x₁, PUnit.unit), (y₁, PUnit.unit), PUnit.unit)
      ((x₂, PUnit.unit), (y₂, PUnit.unit), PUnit.unit) := by
  dsimp only [LVar]
  exact @TRel.pairL target V₁ V₂ G (.bits n) .bool (x₁, PUnit.unit) (x₂, PUnit.unit)
    (y₁, PUnit.unit) (y₂, PUnit.unit) (TRel.single hx) (TRel.single hy)

private theorem legalArg_bits_fst_rel {V₁ V₂ : Ty → Type} {G : Ctx V₁ V₂}
    {LG : Ctx (LVar target V₁) (LVar target V₂)} (hc : CGood target G LG) {n : Nat}
    {a₁ : Arg (LVar target V₁) (.bits n)} {a₂ : Arg (LVar target V₂) (.bits n)}
    (ha : ArgRel LG (.bits n) a₁ a₂) :
    ArgRel G (.bits (target.widenWidth n)) (legalArg target a₁).fst (legalArg target a₂).fst := by
  have r := legalArg_rel target hc ha
  simp only [LegalTarget.legalTys] at r
  exact (TRel.cons_iff.1 r).1

private theorem legalArg_bool_fst_rel {V₁ V₂ : Ty → Type} {G : Ctx V₁ V₂}
    {LG : Ctx (LVar target V₁) (LVar target V₂)} (hc : CGood target G LG)
    {a₁ : Arg (LVar target V₁) .bool} {a₂ : Arg (LVar target V₂) .bool}
    (ha : ArgRel LG .bool a₁ a₂) :
    ArgRel G .bool (legalArg target a₁).fst (legalArg target a₂).fst := by
  have r := legalArg_rel target hc ha
  simp only [LegalTarget.legalTys] at r
  exact (TRel.cons_iff.1 r).1

private theorem legalArg_bits_rel {V₁ V₂ : Ty → Type} {G : Ctx V₁ V₂}
    {LG : Ctx (LVar target V₁) (LVar target V₂)} (hc : CGood target G LG) {n : Nat}
    {a₁ : Arg (LVar target V₁) (.bits n)} {a₂ : Arg (LVar target V₂) (.bits n)}
    (ha : ArgRel LG (.bits n) a₁ a₂)
    {a₁' : Arg V₁ (.bits (target.widenWidth n))} {a₂' : Arg V₂ (.bits (target.widenWidth n))}
    (h₁ : legalArg target a₁ = (a₁', PUnit.unit)) (h₂ : legalArg target a₂ = (a₂', PUnit.unit)) :
    ArgRel G (.bits (target.widenWidth n)) a₁' a₂' := by
  have r := legalArg_rel target hc ha
  rw [h₁, h₂] at r
  simp only [LegalTarget.legalTys] at r
  cases r with | cons h _ => exact h

private theorem legalArg_bool_rel {V₁ V₂ : Ty → Type} {G : Ctx V₁ V₂}
    {LG : Ctx (LVar target V₁) (LVar target V₂)} (hc : CGood target G LG)
    {a₁ : Arg (LVar target V₁) .bool} {a₂ : Arg (LVar target V₂) .bool}
    (ha : ArgRel LG .bool a₁ a₂)
    {a₁' : Arg V₁ .bool} {a₂' : Arg V₂ .bool}
    (h₁ : legalArg target a₁ = (a₁', PUnit.unit)) (h₂ : legalArg target a₂ = (a₂', PUnit.unit)) :
    ArgRel G .bool a₁' a₂' := by
  have r := legalArg_rel target hc ha
  rw [h₁, h₂] at r
  simp only [LegalTarget.legalTys] at r
  cases r with | cons h _ => exact h

private theorem legalArg_float_rel {V₁ V₂ : Ty → Type} {G : Ctx V₁ V₂}
    {LG : Ctx (LVar target V₁) (LVar target V₂)} (hc : CGood target G LG) {f : Fmt}
    {a₁ : Arg (LVar target V₁) (.float f)} {a₂ : Arg (LVar target V₂) (.float f)}
    (ha : ArgRel LG (.float f) a₁ a₂)
    {a₁' : Arg V₁ (.float f)} {a₂' : Arg V₂ (.float f)}
    (h₁ : legalArg target a₁ = (a₁', PUnit.unit)) (h₂ : legalArg target a₂ = (a₂', PUnit.unit)) :
    ArgRel G (.float f) a₁' a₂' := by
  have r := legalArg_rel target hc ha
  rw [h₁, h₂] at r
  simp only [LegalTarget.legalTys] at r
  cases r with | cons h _ => exact h

private theorem opRel_elim {V₁ V₂ : Ty → Type} {G : Ctx V₁ V₂} {rs : List Ty}
    {op₁ : Op V₁ rs} {op₂ : Op V₂ rs} (hop : OpRel G op₁ op₂)
    (P : Op V₁ rs → Op V₂ rs → Prop)
    (h : ∀ {sig} (code : OpCode sig rs) (args₁ : Tup (Arg V₁) sig) (args₂ : Tup (Arg V₂) sig),
      TRel (ArgRel G) args₁ args₂ → P { code := code, args := args₁ } { code := code, args := args₂ }) :
    P op₁ op₂ := by
  cases hop; exact h _ _ _ ‹_›

private def unifShiftRhs (V : Ty → Type) (target : LegalTarget) (u : Ty) (rhs : Arg (LVar target V) u) : Bool :=
  match rhs with
  | .imm c => (uniformShiftLeaf? u c).isSome
  | _ => false

private theorem unifShiftRhs_eq {V₁ V₂ : Ty → Type} (target : LegalTarget) :
    ∀ (u : Ty) {LG : Ctx (LVar target V₁) (LVar target V₂)} {r₁ r₂},
      ArgRel LG u r₁ r₂ → unifShiftRhs V₁ target u r₁ = unifShiftRhs V₂ target u r₂
  | u, _, _, _, h => by cases h <;> rfl

private theorem legalTys_of_isNativeTy (x : Ty)
    (hx : (target.isLegalTy x && match x with | .bits n => target.widenWidth n == n | _ => true) = true) :
    target.legalTys x = [x] := by
  cases x with
  | bool => rfl
  | bits n =>
    simp only [Bool.and_eq_true, beq_iff_eq] at hx
    simp [LegalTarget.legalTys, hx.2]
  | float _ => rfl
  | pair _ _ =>
    simp only [Bool.and_true, LegalTarget.isLegalTy] at hx
    simp [LegalTarget.legalTys, hx]

private theorem TRel_cast_singleton {V₁ V₂ : Ty → Type} {G : Ctx V₁ V₂} {ts : List Ty} {t : Ty}
    (heq : ts = [t]) {xs₁ : Tup (Arg V₁) ts} {xs₂ : Tup (Arg V₂) ts}
    (h : TRel (ArgRel G) xs₁ xs₂) :
    ArgRel G t (cast (by rw [heq]) xs₁ : Tup (Arg V₁) [t]).1
               (cast (by rw [heq]) xs₂ : Tup (Arg V₂) [t]).1 := by
  subst heq; cases h with | cons ha _ => exact ha

private theorem TRel_cast_single_eq {V₁ V₂ : Ty → Type} {G : Ctx V₁ V₂} {u : Ty}
    {ts : List Ty} (heq : [u] = ts) {r₁ : Arg V₁ u} {r₂ : Arg V₂ u}
    (hr : ArgRel G u r₁ r₂) :
    TRel (ArgRel G) (cast (by rw [heq]) (show Tup (Arg V₁) [u] from (r₁, ())) : Tup (Arg V₁) ts)
                    (cast (by rw [heq]) (show Tup (Arg V₂) [u] from (r₂, ())) : Tup (Arg V₂) ts) := by
  subst heq; exact TRel.single hr

theorem legalOp_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {outRs rs' : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} {LG : Ctx (LVar target V₁) (LVar target V₂)}
    (hc : CGood target G LG) {op₁ : Op (LVar target V₁) rs'} {op₂ : Op (LVar target V₂) rs'}
    (hop : OpRel LG op₁ op₂)
    {k₁ : Tup (LVar target V₁) rs' → Expr V₁ L₁ outRs}
    {k₂ : Tup (LVar target V₂) rs' → Expr V₂ L₂ outRs}
    (hk : ∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂,
      TRel (fun _t x₁ x₂ => TRel (ArgRel G') x₁ x₂) y₁ y₂ → Wf G' D (k₁ y₁) (k₂ y₂)) :
    Wf G D (legalOp target op₁ k₁) (legalOp target op₂ k₂) := by
  refine opRel_elim hop (fun o₁ o₂ => Wf G D (legalOp target o₁ k₁) (legalOp target o₂ k₂)) ?_
  intro _sig code args₁ args₂ hargs
  cases code with
  | copy t =>
    rcases hargs with _ | ⟨ha, _⟩
    exact hk (fun _ p => p) _ _ (TRel.singleL target (legalArg_rel target hc ha))
  | add t =>
    rcases hargs with _ | ⟨ha, hargs⟩; rcases hargs with _ | ⟨hb, _⟩
    dsimp only [legalOp]
    split
    · exact .hlt
    · refine legalBinTree_wf target .add (fun u unif => target.vecIntOpSupported (.add u) u unif)
        (fun _ _ => false) (fun _ _ => false) (fun _ {_ _ _} _ => rfl) ?_ ?_ ?_
        t (legalArg_rel target hc ha) (legalArg_rel target hc hb)
        (show OptRhsRel target LG t none none from trivial)
        fun hG' y₁ y₂ hy => hk hG' _ _ (TRel.singleL target hy)
      · intro _ _ _ _ _ _ _ _ h1 h2 c; exact Wf.let2M _ h1 h2 c
      · intro n _ _ _ _ _ _ _ _ h1 h2 c; exact legalBitsArith_wf target n (.add (.bits n)) h1 h2 c
      · intro _ _ _ _ _ _ _ _ _ _ _ _; exact .hlt
  | sub t =>
    rcases hargs with _ | ⟨ha, hargs⟩; rcases hargs with _ | ⟨hb, _⟩
    dsimp only [legalOp]
    split
    · exact .hlt
    · refine legalBinTree_wf target .sub (fun u unif => target.vecIntOpSupported (.sub u) u unif)
        (fun _ _ => false) (fun _ _ => false) (fun _ {_ _ _} _ => rfl) ?_ ?_ ?_
        t (legalArg_rel target hc ha) (legalArg_rel target hc hb)
        (show OptRhsRel target LG t none none from trivial)
        fun hG' y₁ y₂ hy => hk hG' _ _ (TRel.singleL target hy)
      · intro _ _ _ _ _ _ _ _ h1 h2 c; exact Wf.let2M _ h1 h2 c
      · intro n _ _ _ _ _ _ _ _ h1 h2 c; exact legalBitsArith_wf target n (.sub (.bits n)) h1 h2 c
      · intro _ _ _ _ _ _ _ _ _ _ _ _; exact .hlt
  | mul t =>
    rcases hargs with _ | ⟨ha, hargs⟩; rcases hargs with _ | ⟨hb, _⟩
    dsimp only [legalOp]
    split
    · exact .hlt
    · refine legalBinTree_wf target .mul (fun u unif => target.vecIntOpSupported (.mul u) u unif)
        (fun _ _ => false) (fun _ _ => false) (fun _ {_ _ _} _ => rfl) ?_ ?_ ?_
        t (legalArg_rel target hc ha) (legalArg_rel target hc hb)
        (show OptRhsRel target LG t none none from trivial)
        fun hG' y₁ y₂ hy => hk hG' _ _ (TRel.singleL target hy)
      · intro _ _ _ _ _ _ _ _ h1 h2 c; exact Wf.let2M _ h1 h2 c
      · intro n _ _ _ _ _ _ _ _ h1 h2 c; exact legalBitsArith_wf target n (.mul (.bits n)) h1 h2 c
      · intro _ _ _ _ _ _ _ _ _ _ _ _; exact .hlt
  | neg t =>
    rcases hargs with _ | ⟨ha, _⟩
    dsimp only [legalOp]
    split
    · exact .hlt
    · refine legalUnaryTree_wf target .neg (fun u => target.vecIntOpSupported (.neg u) u false)
        (fun {_ _ _ _ _ _} h1 c => c (fun _ p => p) _ _ h1)
        ?_
        (fun _ {_ _ _ _ _ _} _ _ => .hlt)
        t (legalArg_rel target hc ha) fun hG' y₁ y₂ hy => hk hG' _ _ (TRel.singleL target hy)
      intro n G' D' x₁ x₂ cont₁ cont₂ hx hc'
      split
      · exact hc' (fun _ p => p) _ _ (.imm _)
      · exact Wf.let1M _ hx fun h2 r₁ r₂ hr =>
          emitMaskToN_wf n (target.widenWidth n) hr fun h3 y₁ y₂ hy =>
            hc' (sub_trans h2 h3) y₁ y₂ hy
  | and t =>
    rcases hargs with _ | ⟨ha, hargs⟩; rcases hargs with _ | ⟨hb, _⟩
    dsimp only [legalOp]
    refine legalBinTree_wf target .and (fun u unif => target.vecIntOpSupported (.and u) u unif)
      (fun _ _ => false) (fun _ _ => false) (fun _ {_ _ _} _ => rfl) ?_ ?_ ?_
      t (legalArg_rel target hc ha) (legalArg_rel target hc hb)
      (show OptRhsRel target LG t none none from trivial)
      fun hG' y₁ y₂ hy => hk hG' _ _ (TRel.singleL target hy)
    · intro _ _ _ _ _ _ _ _ h1 h2 c; exact Wf.let2M _ h1 h2 c
    · intro n _ _ _ _ _ _ _ _ h1 h2 c; exact legalBitsArith_wf target n (.and (.bits n)) h1 h2 c
    · intro f _ _ _ _ _ _ _ _ h1 h2 c; exact legalFloatBit2_wf target _ _ f h1 h2 c
  | or t =>
    rcases hargs with _ | ⟨ha, hargs⟩; rcases hargs with _ | ⟨hb, _⟩
    dsimp only [legalOp]
    refine legalBinTree_wf target .or (fun u unif => target.vecIntOpSupported (.or u) u unif)
      (fun _ _ => false) (fun _ _ => false) (fun _ {_ _ _} _ => rfl) ?_ ?_ ?_
      t (legalArg_rel target hc ha) (legalArg_rel target hc hb)
      (show OptRhsRel target LG t none none from trivial)
      fun hG' y₁ y₂ hy => hk hG' _ _ (TRel.singleL target hy)
    · intro _ _ _ _ _ _ _ _ h1 h2 c; exact Wf.let2M _ h1 h2 c
    · intro n _ _ _ _ _ _ _ _ h1 h2 c; exact legalBitsArith_wf target n (.or (.bits n)) h1 h2 c
    · intro f _ _ _ _ _ _ _ _ h1 h2 c; exact legalFloatBit2_wf target _ _ f h1 h2 c
  | xor t =>
    rcases hargs with _ | ⟨ha, hargs⟩; rcases hargs with _ | ⟨hb, _⟩
    dsimp only [legalOp]
    refine legalBinTree_wf target .xor (fun u unif => target.vecIntOpSupported (.xor u) u unif)
      (fun _ _ => false) (fun _ _ => false) (fun _ {_ _ _} _ => rfl) ?_ ?_ ?_
      t (legalArg_rel target hc ha) (legalArg_rel target hc hb)
      (show OptRhsRel target LG t none none from trivial)
      fun hG' y₁ y₂ hy => hk hG' _ _ (TRel.singleL target hy)
    · intro _ _ _ _ _ _ _ _ h1 h2 c; exact Wf.let2M _ h1 h2 c
    · intro n _ _ _ _ _ _ _ _ h1 h2 c; exact legalBitsArith_wf target n (.xor (.bits n)) h1 h2 c
    · intro f _ _ _ _ _ _ _ _ h1 h2 c; exact legalFloatBit2_wf target _ _ f h1 h2 c
  | not t =>
    rcases hargs with _ | ⟨ha, _⟩
    refine legalUnaryTree_wf target .not (fun u => target.vecIntOpSupported (.not u) u false)
      (fun {_ _ _ _ _ _} h1 c => Wf.let1M _ h1 c)
      ?_ ?_
      t (legalArg_rel target hc ha) fun hG' y₁ y₂ hy => hk hG' _ _ (TRel.singleL target hy)
    · intro n G' D' x₁ x₂ cont₁ cont₂ hx hc'
      dsimp only; split
      · exact hc' (fun _ p => p) _ _ (.imm _)
      · split
        · exact Wf.let1M _ hx hc'
        · exact Wf.let1M _ hx fun h2 r₁ r₂ hr =>
            emitMaskToN_wf n (target.widenWidth n) hr fun h3 y₁ y₂ hy =>
              hc' (sub_trans h2 h3) y₁ y₂ hy
    · intro f G' D' x₁ x₂ cont₁ cont₂ hx hc'
      dsimp only; split
      · exact Wf.let1M _ hx hc'
      · exact Wf.let1M _ hx fun h2 bx₁ bx₂ hbx =>
          Wf.let1M _ hbx fun h3 br₁ br₂ hbr =>
            Wf.let1M _ hbr fun h4 r₁ r₂ hr =>
              hc' (sub_trans h2 (sub_trans h3 h4)) r₁ r₂ hr
  | ternlog t imm =>
    rcases hargs with _ | ⟨ha, hargs⟩; rcases hargs with _ | ⟨hb, hargs⟩; rcases hargs with _ | ⟨hc', _⟩
    refine legalTernaryTree_wf target (fun u => .ternlog u imm)
      (fun u => target.vecIntOpSupported (.ternlog u imm) u false)
      (fun {_ _ _ _ _ _ _ _ _ _} h1 h2 h3 c => emitTernlogBool_wf h1 h2 h3 imm c)
      ?_ ?_
      t (legalArg_rel target hc ha) (legalArg_rel target hc hb) (legalArg_rel target hc hc')
      fun hG' y₁ y₂ hy => hk hG' _ _ (TRel.singleL target hy)
    · intro n G' D' x₁ x₂ y₁ y₂ z₁ z₂ cont₁ cont₂ hx hy hz hc''
      dsimp only; split
      · exact hc'' (fun _ p => p) _ _ (.imm _)
      · split
        · exact Wf.let3M _ hx hy hz fun h4 r₁ r₂ hr =>
            emitMaskToN_wf n (target.widenWidth n) hr fun h5 y₁ y₂ hy =>
              hc'' (sub_trans h4 h5) y₁ y₂ hy
        · exact emitTernlogBits_wf (target.widenWidth n) hx hy hz imm fun h4 r₁ r₂ hr =>
            emitMaskToN_wf n (target.widenWidth n) hr fun h5 y₁ y₂ hy =>
              hc'' (sub_trans h4 h5) y₁ y₂ hy
    · intro f G' D' x₁ x₂ y₁ y₂ z₁ z₂ cont₁ cont₂ hx hy hz hc''
      dsimp only; split
      · exact Wf.let3M _ hx hy hz hc''
      · cases htern : target.scalarTernlog
        · simp only [Bool.false_eq_true, ↓reduceIte]
          exact Wf.let1 _ hx fun p1 bx₁ bx₂ hbx =>
            Wf.let1 _ (hy.weaken p1) fun p2 by₁ by₂ hby =>
              Wf.let1 _ (hz.weaken (sub_trans p1 p2)) fun p3 bz₁ bz₂ hbz =>
                have q3 := sub_trans p1 (sub_trans p2 p3)
                emitTernlogBits_wf f.width (hbx.weaken (sub_trans p2 p3)) (hby.weaken p3) hbz imm
                  fun p4 br₁ br₂ hbr =>
                    Wf.let1 _ hbr fun p5 r₁ r₂ hr =>
                      hc'' (sub_trans q3 (sub_trans p4 p5)) r₁ r₂ hr
        · simp only [↓reduceIte]
          exact Wf.let1 _ hx fun p1 bx₁ bx₂ hbx =>
            Wf.let1 _ (hy.weaken p1) fun p2 by₁ by₂ hby =>
              Wf.let1 _ (hz.weaken (sub_trans p1 p2)) fun p3 bz₁ bz₂ hbz =>
                have q3 := sub_trans p1 (sub_trans p2 p3)
                Wf.let3 _ (hbx.weaken (sub_trans p2 p3)) (hby.weaken p3) hbz fun p4 br₁ br₂ hbr =>
                  Wf.let1 _ hbr fun p5 r₁ r₂ hr =>
                    hc'' (sub_trans q3 (sub_trans p4 p5)) r₁ r₂ hr
  | shl t =>
    rcases args₁ with ⟨a₁, b₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, b₂, ⟨⟩⟩
    rcases hargs with _ | ⟨ha, hargs⟩; rcases hargs with _ | ⟨hb, _⟩
    dsimp only [legalOp]
    split
    · exact .hlt
    · refine legalBinTree_wf target .shl (fun u unif => target.vecIntOpSupported (.shl u) u unif)
        _ _ ?_ ?_ ?_ ?_
        t (legalArg_rel target hc ha) (legalArg_rel target hc hb)
        (show OptRhsRel target LG t (some b₁) (some b₂) from hb)
        fun hG' y₁ y₂ hy => hk hG' _ _ (TRel.singleL target hy)
      · intro u _ r₁ r₂ hr; cases hr <;> rfl
      · intro _ _ _ _ _ _ _ _ h1 _ c; exact c (fun _ p => p) _ _ h1
      · intro n _ _ _ _ _ _ _ _ h1 h2 c; exact legalBitsArith_wf target n (.shl (.bits n)) h1 h2 c
      · intro _ _ _ _ _ _ _ _ _ _ _ _; exact .hlt
  | lshr t =>
    rcases args₁ with ⟨a₁, b₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, b₂, ⟨⟩⟩
    rcases hargs with _ | ⟨ha, hargs⟩; rcases hargs with _ | ⟨hb, _⟩
    dsimp only [legalOp]
    split
    · exact .hlt
    · refine legalBinTree_wf target .lshr (fun u unif => target.vecIntOpSupported (.lshr u) u unif)
        _ _ ?_ ?_ ?_ ?_
        t (legalArg_rel target hc ha) (legalArg_rel target hc hb)
        (show OptRhsRel target LG t (some b₁) (some b₂) from hb)
        fun hG' y₁ y₂ hy => hk hG' _ _ (TRel.singleL target hy)
      · intro u _ r₁ r₂ hr; cases hr <;> rfl
      · intro _ _ _ _ _ _ _ _ h1 _ c; exact c (fun _ p => p) _ _ h1
      · intro n _ _ _ _ _ _ _ _ h1 h2 c; exact legalBitsArith_wf target n (.lshr (.bits n)) h1 h2 c
      · intro _ _ _ _ _ _ _ _ _ _ _ _; exact .hlt
  | ashr t =>
    rcases args₁ with ⟨a₁, b₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, b₂, ⟨⟩⟩
    rcases hargs with _ | ⟨ha, hargs⟩; rcases hargs with _ | ⟨hb, _⟩
    dsimp only [legalOp]
    split
    · exact .hlt
    · refine legalBinTree_wf target .ashr (fun u unif => target.vecIntOpSupported (.ashr u) u unif)
        _ _ ?_ ?_ ?_ ?_
        t (legalArg_rel target hc ha) (legalArg_rel target hc hb)
        (show OptRhsRel target LG t (some b₁) (some b₂) from hb)
        fun hG' y₁ y₂ hy => hk hG' _ _ (TRel.singleL target hy)
      · intro u _ r₁ r₂ hr; cases hr <;> rfl
      · intro _ _ _ _ _ _ _ _ h1 _ c; exact c (fun _ p => p) _ _ h1
      · intro n _ _ _ _ _ _ _ _ h1 h2 c; exact legalBitsArith_wf target n (.ashr (.bits n)) h1 h2 c
      · intro _ _ _ _ _ _ _ _ _ _ _ _; exact .hlt
  | rotl t =>
    rcases args₁ with ⟨a₁, b₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, b₂, ⟨⟩⟩
    rcases hargs with _ | ⟨ha, hargs⟩; rcases hargs with _ | ⟨hb, _⟩
    dsimp only [legalOp]
    split
    · exact .hlt
    · refine legalBinTree_wf target .rotl (fun u unif => target.vecIntOpSupported (.rotl u) u unif)
        _ _ ?_ ?_ ?_ ?_
        t (legalArg_rel target hc ha) (legalArg_rel target hc hb)
        (show OptRhsRel target LG t (some b₁) (some b₂) from hb)
        fun hG' y₁ y₂ hy => hk hG' _ _ (TRel.singleL target hy)
      · intro u _ r₁ r₂ hr; cases hr <;> rfl
      · intro _ _ _ _ _ _ _ _ h1 _ c; exact c (fun _ p => p) _ _ h1
      · intro n _ _ _ _ _ _ _ _ h1 h2 c; exact legalBitsArith_wf target n (.rotl (.bits n)) h1 h2 c
      · intro _ _ _ _ _ _ _ _ _ _ _ _; exact .hlt
  | rotr t =>
    rcases args₁ with ⟨a₁, b₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, b₂, ⟨⟩⟩
    rcases hargs with _ | ⟨ha, hargs⟩; rcases hargs with _ | ⟨hb, _⟩
    dsimp only [legalOp]
    split
    · exact .hlt
    · refine legalBinTree_wf target .rotr (fun u unif => target.vecIntOpSupported (.rotr u) u unif)
        _ _ ?_ ?_ ?_ ?_
        t (legalArg_rel target hc ha) (legalArg_rel target hc hb)
        (show OptRhsRel target LG t (some b₁) (some b₂) from hb)
        fun hG' y₁ y₂ hy => hk hG' _ _ (TRel.singleL target hy)
      · intro u _ r₁ r₂ hr; cases hr <;> rfl
      · intro _ _ _ _ _ _ _ _ h1 _ c; exact c (fun _ p => p) _ _ h1
      · intro n _ _ _ _ _ _ _ _ h1 h2 c; exact legalBitsArith_wf target n (.rotr (.bits n)) h1 h2 c
      · intro _ _ _ _ _ _ _ _ _ _ _ _; exact .hlt
  | fshl n =>
    rcases args₁ with ⟨a₁, b₁, c₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, b₂, c₂, ⟨⟩⟩
    rcases hargs with _ | ⟨ha, hargs⟩; rcases hargs with _ | ⟨hb, hargs⟩; rcases hargs with _ | ⟨hc', _⟩
    dsimp only [legalOp]
    rcases ha1 : legalArg target a₁ with ⟨a₁', ⟨⟩⟩; rcases ha2 : legalArg target a₂ with ⟨a₂', ⟨⟩⟩
    rcases hb1 : legalArg target b₁ with ⟨b₁', ⟨⟩⟩; rcases hb2 : legalArg target b₂ with ⟨b₂', ⟨⟩⟩
    rcases hc1 : legalArg target c₁ with ⟨c₁', ⟨⟩⟩; rcases hc2 : legalArg target c₂ with ⟨c₂', ⟨⟩⟩
    have ha' := legalArg_bits_rel target hc ha ha1 ha2
    have hb' := legalArg_bits_rel target hc hb hb1 hb2
    have hc'' := legalArg_bits_rel target hc hc' hc1 hc2
    dsimp only
    split
    · exact hk (fun _ p => p) _ _ (trelBitsImmZero target n)
    · split
      · exact Wf.let3M _ ha' hb' hc'' fun h1 r₁ r₂ hr =>
          hk h1 _ _ (TRel.singleL target (TRel.single hr))
      · exact emitCountMod_wf n (target.widenWidth n) hc'' fun p1 cm₁ cm₂ hcm =>
          Wf.let2M _ (.imm _) hcm fun p2 nc₁ nc₂ hnc =>
            have q2 := sub_trans p1 p2
            Wf.let2M _ (ha'.weaken q2) (hcm.weaken p2) fun p3 lo₁ lo₂ hlo =>
              have q3 := sub_trans q2 p3
              Wf.let2M _ (hb'.weaken q3) (hnc.weaken p3) fun p4 hi₁ hi₂ hhi =>
                Wf.let2M _ (hlo.weaken p4) hhi fun p5 cb₁ cb₂ hcb =>
                  emitMaskToN_wf n (target.widenWidth n) hcb fun p6 y₁ y₂ hy =>
                    hk (sub_trans q3 (sub_trans p4 (sub_trans p5 p6))) _ _
                      (TRel.singleL target (TRel.single hy))
  | fshr n =>
    rcases args₁ with ⟨a₁, b₁, c₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, b₂, c₂, ⟨⟩⟩
    rcases hargs with _ | ⟨ha, hargs⟩; rcases hargs with _ | ⟨hb, hargs⟩; rcases hargs with _ | ⟨hc', _⟩
    dsimp only [legalOp]
    rcases ha1 : legalArg target a₁ with ⟨a₁', ⟨⟩⟩; rcases ha2 : legalArg target a₂ with ⟨a₂', ⟨⟩⟩
    rcases hb1 : legalArg target b₁ with ⟨b₁', ⟨⟩⟩; rcases hb2 : legalArg target b₂ with ⟨b₂', ⟨⟩⟩
    rcases hc1 : legalArg target c₁ with ⟨c₁', ⟨⟩⟩; rcases hc2 : legalArg target c₂ with ⟨c₂', ⟨⟩⟩
    have ha' := legalArg_bits_rel target hc ha ha1 ha2
    have hb' := legalArg_bits_rel target hc hb hb1 hb2
    have hc'' := legalArg_bits_rel target hc hc' hc1 hc2
    dsimp only
    split
    · exact hk (fun _ p => p) _ _ (trelBitsImmZero target n)
    · split
      · exact Wf.let3M _ ha' hb' hc'' fun h1 r₁ r₂ hr =>
          hk h1 _ _ (TRel.singleL target (TRel.single hr))
      · exact emitCountMod_wf n (target.widenWidth n) hc'' fun p1 cm₁ cm₂ hcm =>
          Wf.let2M _ (.imm _) hcm fun p2 nc₁ nc₂ hnc =>
            have q2 := sub_trans p1 p2
            Wf.let2M _ (hb'.weaken q2) (hcm.weaken p2) fun p3 lo₁ lo₂ hlo =>
              have q3 := sub_trans q2 p3
              Wf.let2M _ (ha'.weaken q3) (hnc.weaken p3) fun p4 hi₁ hi₂ hhi =>
                Wf.let2M _ (hlo.weaken p4) hhi fun p5 cb₁ cb₂ hcb =>
                  emitMaskToN_wf n (target.widenWidth n) hcb fun p6 y₁ y₂ hy =>
                    hk (sub_trans q3 (sub_trans p4 (sub_trans p5 p6))) _ _
                      (TRel.singleL target (TRel.single hy))
  | bswap t =>
    rcases hargs with _ | ⟨ha, _⟩
    exact legalBswapTree_wf target t (legalArg_rel target hc ha) fun hG' y₁ y₂ hy =>
      hk hG' _ _ (TRel.singleL target hy)
  | clz n =>
    rcases args₁ with ⟨a₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, ⟨⟩⟩
    rcases hargs with _ | ⟨ha, _⟩
    dsimp only [legalOp]
    rcases ha1 : legalArg target a₁ with ⟨a₁', ⟨⟩⟩; rcases ha2 : legalArg target a₂ with ⟨a₂', ⟨⟩⟩
    have ha' := legalArg_bits_rel target hc ha ha1 ha2
    dsimp only
    split
    · exact hk (fun _ p => p) _ _ (trelBitsImmZero target n)
    · split
      · exact Wf.let1M _ ha' fun h1 r₁ r₂ hr =>
          hk h1 _ _ (TRel.singleL target (TRel.single hr))
      · exact Wf.let1M _ ha' fun h1 cw₁ cw₂ hcw =>
          Wf.let2M _ hcw (.imm _) fun h2 r₁ r₂ hr =>
            hk (sub_trans h1 h2) _ _ (TRel.singleL target (TRel.single hr))
  | cls n =>
    rcases args₁ with ⟨a₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, ⟨⟩⟩
    rcases hargs with _ | ⟨ha, _⟩
    dsimp only [legalOp]
    rcases ha1 : legalArg target a₁ with ⟨a₁', ⟨⟩⟩; rcases ha2 : legalArg target a₂ with ⟨a₂', ⟨⟩⟩
    have ha' := legalArg_bits_rel target hc ha ha1 ha2
    dsimp only
    split
    · exact hk (fun _ p => p) _ _ (trelBitsImmZero target n)
    · split
      · exact Wf.let1M _ ha' fun h1 r₁ r₂ hr =>
          hk h1 _ _ (TRel.singleL target (TRel.single hr))
      · exact emitSextToW_wf n (target.widenWidth n) ha' fun h1 sa₁ sa₂ hsa =>
          Wf.let1M _ hsa fun h2 cw₁ cw₂ hcw =>
            Wf.let2M _ hcw (.imm _) fun h3 r₁ r₂ hr =>
              hk (sub_trans h1 (sub_trans h2 h3)) _ _ (TRel.singleL target (TRel.single hr))
  | rbit n =>
    rcases args₁ with ⟨a₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, ⟨⟩⟩
    rcases hargs with _ | ⟨ha, _⟩
    dsimp only [legalOp]
    rcases ha1 : legalArg target a₁ with ⟨a₁', ⟨⟩⟩; rcases ha2 : legalArg target a₂ with ⟨a₂', ⟨⟩⟩
    have ha' := legalArg_bits_rel target hc ha ha1 ha2
    dsimp only
    split
    · exact hk (fun _ p => p) _ _ (trelBitsImmZero target n)
    · split
      · exact Wf.let1M _ ha' fun h1 r₁ r₂ hr =>
          hk h1 _ _ (TRel.singleL target (TRel.single hr))
      · exact Wf.let1M _ ha' fun h1 rw₁ rw₂ hrw =>
          Wf.let2M _ hrw (.imm _) fun h2 r₁ r₂ hr =>
            hk (sub_trans h1 h2) _ _ (TRel.singleL target (TRel.single hr))
  | ctz n =>
    rcases args₁ with ⟨a₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, ⟨⟩⟩
    rcases hargs with _ | ⟨ha, _⟩
    dsimp only [legalOp]
    rcases ha1 : legalArg target a₁ with ⟨a₁', ⟨⟩⟩; rcases ha2 : legalArg target a₂ with ⟨a₂', ⟨⟩⟩
    have ha' := legalArg_bits_rel target hc ha ha1 ha2
    dsimp only
    split
    · exact hk (fun _ p => p) _ _ (trelBitsImmZero target n)
    · split
      · exact Wf.let1M _ ha' fun h1 r₁ r₂ hr =>
          hk h1 _ _ (TRel.singleL target (TRel.single hr))
      · exact Wf.let2M _ ha' (.imm _) fun h1 ao₁ ao₂ hao =>
          Wf.let1M _ hao fun h2 r₁ r₂ hr =>
            hk (sub_trans h1 h2) _ _ (TRel.singleL target (TRel.single hr))
  | popcnt n =>
    rcases args₁ with ⟨a₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, ⟨⟩⟩
    rcases hargs with _ | ⟨ha, _⟩
    dsimp only [legalOp]
    rcases ha1 : legalArg target a₁ with ⟨a₁', ⟨⟩⟩; rcases ha2 : legalArg target a₂ with ⟨a₂', ⟨⟩⟩
    have ha' := legalArg_bits_rel target hc ha ha1 ha2
    dsimp only
    split
    · exact hk (fun _ p => p) _ _ (trelBitsImmZero target n)
    · exact Wf.let1M _ ha' fun h1 r₁ r₂ hr =>
        hk h1 _ _ (TRel.singleL target (TRel.single hr))
  | cmp o t m h =>
    subst h
    rcases hargs with _ | ⟨ha, hargs⟩; rcases hargs with _ | ⟨hb, _⟩
    dsimp only [legalOp]
    split
    · exact .hlt
    · exact legalCmpTree_wf target o t (legalArg_rel target hc ha) (legalArg_rel target hc hb)
        fun hG' y₁ y₂ hy => hk hG' _ _ (TRel.singleL target hy)
  | select t =>
    rcases args₁ with ⟨c₁, a₁, b₁, ⟨⟩⟩; rcases args₂ with ⟨c₂, a₂, b₂, ⟨⟩⟩
    rcases hargs with _ | ⟨hc', hargs⟩; rcases hargs with _ | ⟨ha, hargs⟩; rcases hargs with _ | ⟨hb, _⟩
    dsimp only [legalOp]
    rcases hc1 : legalArg target c₁ with ⟨c₁', ⟨⟩⟩; rcases hc2 : legalArg target c₂ with ⟨c₂', ⟨⟩⟩
    have hc'' := legalArg_bool_rel target hc hc' hc1 hc2
    dsimp only
    exact legalSelectTree_wf target hc'' t (legalArg_rel target hc ha) (legalArg_rel target hc hb)
      fun hG' y₁ y₂ hy => hk hG' _ _ (TRel.singleL target hy)
  | blend t m h =>
    subst h
    rcases hargs with _ | ⟨hc', hargs⟩; rcases hargs with _ | ⟨ha, hargs⟩; rcases hargs with _ | ⟨hb, _⟩
    exact legalBlendTree_wf target t (legalArg_rel target hc hc')
      (legalArg_rel target hc ha) (legalArg_rel target hc hb)
      fun hG' y₁ y₂ hy => hk hG' _ _ (TRel.singleL target hy)
  | zext m n =>
    rcases args₁ with ⟨a₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, ⟨⟩⟩
    rcases hargs with _ | ⟨ha, _⟩
    dsimp only [legalOp]
    rcases ha1 : legalArg target a₁ with ⟨a₁', ⟨⟩⟩; rcases ha2 : legalArg target a₂ with ⟨a₂', ⟨⟩⟩
    have ha' := legalArg_bits_rel target hc ha ha1 ha2
    dsimp only
    split
    · exact .hlt
    · split
      · exact hk (fun _ p => p) _ _ (trelBitsImmZero target n)
      · split
        · next h => exact hk (fun _ p => p) _ _ (trelSingleBits target n (castArgBits_rel h ha'))
        · split
          · exact Wf.let1M _ ha' fun h1 r₁ r₂ hr =>
              hk h1 _ _ (TRel.singleL target (TRel.single hr))
          · exact .hlt
  | sext m n =>
    rcases args₁ with ⟨a₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, ⟨⟩⟩
    rcases hargs with _ | ⟨ha, _⟩
    dsimp only [legalOp]
    rcases ha1 : legalArg target a₁ with ⟨a₁', ⟨⟩⟩; rcases ha2 : legalArg target a₂ with ⟨a₂', ⟨⟩⟩
    have ha' := legalArg_bits_rel target hc ha ha1 ha2
    dsimp only
    split
    · exact .hlt
    · split
      · exact hk (fun _ p => p) _ _ (trelBitsImmZero target n)
      · refine emitSextToW_wf m (target.widenWidth m) ha' fun h1 sx₁ sx₂ hsx => ?_
        by_cases heq : target.widenWidth m = target.widenWidth n
        · simp only [heq, ↓reduceDIte]
          exact emitMaskToN_wf n (target.widenWidth n) (castArgBits_rel heq hsx) fun h2 rm₁ rm₂ hrm =>
            hk (sub_trans h1 h2) _ _ (trelSingleBits target n hrm)
        · by_cases hlt : target.widenWidth m < target.widenWidth n
          · simp only [heq, ↓reduceDIte, hlt, ↓reduceIte]
            exact Wf.let1M _ hsx fun h2 r₁ r₂ hr =>
              emitMaskToN_wf n (target.widenWidth n) hr fun h3 rm₁ rm₂ hrm =>
                hk (sub_trans h1 (sub_trans h2 h3)) _ _ (trelSingleBits target n hrm)
          · simp only [heq, ↓reduceDIte, hlt, ↓reduceIte]; exact .hlt
  | trunc m n =>
    rcases args₁ with ⟨a₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, ⟨⟩⟩
    rcases hargs with _ | ⟨ha, _⟩
    dsimp only [legalOp]
    rcases ha1 : legalArg target a₁ with ⟨a₁', ⟨⟩⟩; rcases ha2 : legalArg target a₂ with ⟨a₂', ⟨⟩⟩
    have ha' := legalArg_bits_rel target hc ha ha1 ha2
    dsimp only
    split
    · exact .hlt
    · split
      · exact hk (fun _ p => p) _ _ (trelBitsImmZero target n)
      · by_cases heq : target.widenWidth n = target.widenWidth m
        · simp only [heq, ↓reduceDIte]
          exact emitMaskToN_wf n (target.widenWidth n) (castArgBits_rel heq.symm ha') fun h1 rm₁ rm₂ hrm =>
            hk h1 _ _ (trelSingleBits target n hrm)
        · by_cases hlt : target.widenWidth n < target.widenWidth m
          · simp only [heq, ↓reduceDIte, hlt, ↓reduceIte]
            exact Wf.let1M _ ha' fun h1 r₁ r₂ hr =>
              emitMaskToN_wf n (target.widenWidth n) hr fun h2 rm₁ rm₂ hrm =>
                hk (sub_trans h1 h2) _ _ (trelSingleBits target n hrm)
          · simp only [heq, ↓reduceDIte, hlt, ↓reduceIte]; exact .hlt
  | ofBool n =>
    rcases args₁ with ⟨c₁, ⟨⟩⟩; rcases args₂ with ⟨c₂, ⟨⟩⟩
    rcases hargs with _ | ⟨hc', _⟩
    dsimp only [legalOp]
    rcases hc1 : legalArg target c₁ with ⟨c₁', ⟨⟩⟩; rcases hc2 : legalArg target c₂ with ⟨c₂', ⟨⟩⟩
    have hc'' := legalArg_bool_rel target hc hc' hc1 hc2
    dsimp only
    split
    · exact hk (fun _ p => p) _ _ (trelBitsImmZero target n)
    · exact Wf.let1M _ hc'' fun h1 r₁ r₂ hr =>
        hk h1 _ _ (TRel.singleL target (TRel.single hr))
  | addc n =>
    rcases args₁ with ⟨a₁, b₁, c₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, b₂, c₂, ⟨⟩⟩
    rcases hargs with _ | ⟨ha, hargs⟩; rcases hargs with _ | ⟨hb, hargs⟩; rcases hargs with _ | ⟨hc', _⟩
    dsimp only [legalOp]
    rcases ha1 : legalArg target a₁ with ⟨a₁', ⟨⟩⟩; rcases ha2 : legalArg target a₂ with ⟨a₂', ⟨⟩⟩
    rcases hb1 : legalArg target b₁ with ⟨b₁', ⟨⟩⟩; rcases hb2 : legalArg target b₂ with ⟨b₂', ⟨⟩⟩
    rcases hc1 : legalArg target c₁ with ⟨c₁', ⟨⟩⟩; rcases hc2 : legalArg target c₂ with ⟨c₂', ⟨⟩⟩
    have ha' := legalArg_bits_rel target hc ha ha1 ha2
    have hb' := legalArg_bits_rel target hc hb hb1 hb2
    have hc'' := legalArg_bool_rel target hc hc' hc1 hc2
    dsimp only
    split
    · exact hk (fun _ p => p) _ _ (trelPairBitsBool target n (ArgRel.imm _) hc'')
    · split
      · refine .let_ (.mk (.addc (target.widenWidth n)) (.cons ha' (.cons hb' (.cons hc'' .nil))))
          fun r₁ r₂ => ?_
        rcases r₁ with ⟨s₁, co₁, ⟨⟩⟩; rcases r₂ with ⟨s₂, co₂, ⟨⟩⟩
        dsimp only [Tup.zip, List.append]
        exact hk (fun _ p => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ p)) _ _
          (trelPairBitsBool target n (.var List.mem_cons_self) (.var (List.mem_cons_of_mem _ List.mem_cons_self)))
      · exact Wf.let1 _ hc'' fun p1 cw₁ cw₂ hcw =>
          Wf.let2 _ (ha'.weaken p1) (hb'.weaken p1) fun p2 ab₁ ab₂ hab =>
            Wf.let2 _ hab (hcw.weaken p2) fun p3 sw₁ sw₂ hsw =>
              emitMaskToN_wf n (target.widenWidth n) hsw fun p4 s₁ s₂ hs =>
                Wf.let2 _ (.imm _) (hsw.weaken p4) fun p5 co₁ co₂ hco =>
                  hk (sub_trans p1 (sub_trans p2 (sub_trans p3 (sub_trans p4 p5)))) _ _
                    (trelPairBitsBool target n (hs.weaken p5) hco)
  | subb n =>
    rcases args₁ with ⟨a₁, b₁, c₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, b₂, c₂, ⟨⟩⟩
    rcases hargs with _ | ⟨ha, hargs⟩; rcases hargs with _ | ⟨hb, hargs⟩; rcases hargs with _ | ⟨hc', _⟩
    dsimp only [legalOp]
    rcases ha1 : legalArg target a₁ with ⟨a₁', ⟨⟩⟩; rcases ha2 : legalArg target a₂ with ⟨a₂', ⟨⟩⟩
    rcases hb1 : legalArg target b₁ with ⟨b₁', ⟨⟩⟩; rcases hb2 : legalArg target b₂ with ⟨b₂', ⟨⟩⟩
    rcases hc1 : legalArg target c₁ with ⟨c₁', ⟨⟩⟩; rcases hc2 : legalArg target c₂ with ⟨c₂', ⟨⟩⟩
    have ha' := legalArg_bits_rel target hc ha ha1 ha2
    have hb' := legalArg_bits_rel target hc hb hb1 hb2
    have hc'' := legalArg_bool_rel target hc hc' hc1 hc2
    dsimp only
    split
    · exact hk (fun _ p => p) _ _ (trelPairBitsBool target n (ArgRel.imm _) hc'')
    · split
      · refine .let_ (.mk (.subb (target.widenWidth n)) (.cons ha' (.cons hb' (.cons hc'' .nil))))
          fun r₁ r₂ => ?_
        rcases r₁ with ⟨d₁, bo₁, ⟨⟩⟩; rcases r₂ with ⟨d₂, bo₂, ⟨⟩⟩
        dsimp only [Tup.zip, List.append]
        exact hk (fun _ p => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ p)) _ _
          (trelPairBitsBool target n (.var List.mem_cons_self) (.var (List.mem_cons_of_mem _ List.mem_cons_self)))
      · refine .let_ (.mk (.subb (target.widenWidth n)) (.cons ha' (.cons hb' (.cons hc'' .nil))))
          fun r₁ r₂ => ?_
        rcases r₁ with ⟨dw₁, bo₁, ⟨⟩⟩; rcases r₂ with ⟨dw₂, bo₂, ⟨⟩⟩
        dsimp only [Tup.zip, List.append]
        exact emitMaskToN_wf n (target.widenWidth n) (.var List.mem_cons_self)
          fun hG1 d₁ d₂ hd =>
            hk (fun _ p => hG1 _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ p))) _ _
              (trelPairBitsBool target n hd (.var (hG1 _ (List.mem_cons_of_mem _ List.mem_cons_self))))
  | umulw n =>
    rcases args₁ with ⟨a₁, b₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, b₂, ⟨⟩⟩
    rcases hargs with _ | ⟨ha, hargs⟩; rcases hargs with _ | ⟨hb, _⟩
    dsimp only [legalOp]
    rcases ha1 : legalArg target a₁ with ⟨a₁', ⟨⟩⟩; rcases ha2 : legalArg target a₂ with ⟨a₂', ⟨⟩⟩
    rcases hb1 : legalArg target b₁ with ⟨b₁', ⟨⟩⟩; rcases hb2 : legalArg target b₂ with ⟨b₂', ⟨⟩⟩
    have ha' := legalArg_bits_rel target hc ha ha1 ha2
    have hb' := legalArg_bits_rel target hc hb hb1 hb2
    dsimp only
    split
    · exact hk (fun _ p => p) _ _ (trelPairBits target n (ArgRel.imm _) (ArgRel.imm _))
    · split
      · refine .let_ (.mk (.umulw (target.widenWidth n)) (.cons ha' (.cons hb' .nil)))
          fun r₁ r₂ => ?_
        rcases r₁ with ⟨lo₁, hi₁, ⟨⟩⟩; rcases r₂ with ⟨lo₂, hi₂, ⟨⟩⟩
        dsimp only [Tup.zip, List.append]
        exact hk (fun _ p => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ p)) _ _
          (trelPairBits target n (.var List.mem_cons_self) (.var (List.mem_cons_of_mem _ List.mem_cons_self)))
      · refine .let_ (.mk (.umulw (target.widenWidth n)) (.cons ha' (.cons hb' .nil)))
          fun r₁ r₂ => ?_
        rcases r₁ with ⟨loW₁, hiW₁, ⟨⟩⟩; rcases r₂ with ⟨loW₂, hiW₂, ⟨⟩⟩
        dsimp only [Tup.zip, List.append]
        refine emitMaskToN_wf n (target.widenWidth n) (.var List.mem_cons_self)
          fun hG1 lo₁ lo₂ hlo => ?_
        have hloW : ArgRel _ (.bits (target.widenWidth n)) (.var loW₁) (.var loW₂) :=
          .var (hG1 _ List.mem_cons_self)
        have hhiW : ArgRel _ (.bits (target.widenWidth n)) (.var hiW₁) (.var hiW₂) :=
          .var (hG1 _ (List.mem_cons_of_mem _ List.mem_cons_self))
        exact Wf.let2M _ hloW (.imm _) fun p1 pv1₁ pv1₂ hp1 =>
          Wf.let2M _ (hhiW.weaken p1) (.imm _) fun p2 pv2₁ pv2₂ hp2 =>
            Wf.let2M _ (hp1.weaken p2) hp2 fun p3 hcb₁ hcb₂ hcb =>
              emitMaskToN_wf n (target.widenWidth n) hcb fun p4 hi₁ hi₂ hhi =>
                have q4 := sub_trans p1 (sub_trans p2 (sub_trans p3 p4))
                hk (fun _ p => q4 _ (hG1 _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ p)))) _ _
                  (trelPairBits target n (hlo.weaken q4) hhi)
  | smulw n =>
    rcases args₁ with ⟨a₁, b₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, b₂, ⟨⟩⟩
    rcases hargs with _ | ⟨ha, hargs⟩; rcases hargs with _ | ⟨hb, _⟩
    dsimp only [legalOp]
    rcases ha1 : legalArg target a₁ with ⟨a₁', ⟨⟩⟩; rcases ha2 : legalArg target a₂ with ⟨a₂', ⟨⟩⟩
    rcases hb1 : legalArg target b₁ with ⟨b₁', ⟨⟩⟩; rcases hb2 : legalArg target b₂ with ⟨b₂', ⟨⟩⟩
    have ha' := legalArg_bits_rel target hc ha ha1 ha2
    have hb' := legalArg_bits_rel target hc hb hb1 hb2
    dsimp only
    split
    · exact hk (fun _ p => p) _ _ (trelPairBits target n (ArgRel.imm _) (ArgRel.imm _))
    · split
      · refine .let_ (.mk (.smulw (target.widenWidth n)) (.cons ha' (.cons hb' .nil)))
          fun r₁ r₂ => ?_
        rcases r₁ with ⟨lo₁, hi₁, ⟨⟩⟩; rcases r₂ with ⟨lo₂, hi₂, ⟨⟩⟩
        dsimp only [Tup.zip, List.append]
        exact hk (fun _ p => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ p)) _ _
          (trelPairBits target n (.var List.mem_cons_self) (.var (List.mem_cons_of_mem _ List.mem_cons_self)))
      · refine emitSextToW_wf n (target.widenWidth n) ha' fun p1 sa₁ sa₂ hsa =>
          emitSextToW_wf n (target.widenWidth n) (hb'.weaken p1) fun p2 sb₁ sb₂ hsb => ?_
        refine .let_ (.mk (.smulw (target.widenWidth n)) (.cons (hsa.weaken p2) (.cons hsb .nil)))
          fun r₁ r₂ => ?_
        rcases r₁ with ⟨loW₁, hiW₁, ⟨⟩⟩; rcases r₂ with ⟨loW₂, hiW₂, ⟨⟩⟩
        dsimp only [Tup.zip, List.append]
        refine emitMaskToN_wf n (target.widenWidth n) (.var List.mem_cons_self)
          fun p3 lo₁ lo₂ hlo => ?_
        have hloW : ArgRel _ (.bits (target.widenWidth n)) (.var loW₁) (.var loW₂) :=
          .var (p3 _ List.mem_cons_self)
        have hhiW : ArgRel _ (.bits (target.widenWidth n)) (.var hiW₁) (.var hiW₂) :=
          .var (p3 _ (List.mem_cons_of_mem _ List.mem_cons_self))
        exact Wf.let2M _ hloW (.imm _) fun p4 pv1₁ pv1₂ hp1 =>
          Wf.let2M _ (hhiW.weaken p4) (.imm _) fun p5 pv2₁ pv2₂ hp2 =>
            Wf.let2M _ (hp1.weaken p5) hp2 fun p6 hcb₁ hcb₂ hcb =>
              emitMaskToN_wf n (target.widenWidth n) hcb fun p7 hi₁ hi₂ hhi =>
                have q7 := sub_trans p4 (sub_trans p5 (sub_trans p6 p7))
                hk (fun _ p => q7 _ (p3 _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (p2 _ (p1 _ p)))))) _ _
                  (trelPairBits target n (hlo.weaken q7) hhi)
  | udiv n =>
    rcases args₁ with ⟨a₁, b₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, b₂, ⟨⟩⟩
    rcases hargs with _ | ⟨ha, hargs⟩; rcases hargs with _ | ⟨hb, _⟩
    dsimp only [legalOp]
    rcases ha1 : legalArg target a₁ with ⟨a₁', ⟨⟩⟩; rcases ha2 : legalArg target a₂ with ⟨a₂', ⟨⟩⟩
    rcases hb1 : legalArg target b₁ with ⟨b₁', ⟨⟩⟩; rcases hb2 : legalArg target b₂ with ⟨b₂', ⟨⟩⟩
    have ha' := legalArg_bits_rel target hc ha ha1 ha2
    have hb' := legalArg_bits_rel target hc hb hb1 hb2
    dsimp only
    split
    · exact .hlt
    · exact Wf.let2M _ ha' hb' fun h1 r₁ r₂ hr =>
        hk h1 _ _ (TRel.singleL target (TRel.single hr))
  | urem n =>
    rcases args₁ with ⟨a₁, b₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, b₂, ⟨⟩⟩
    rcases hargs with _ | ⟨ha, hargs⟩; rcases hargs with _ | ⟨hb, _⟩
    dsimp only [legalOp]
    rcases ha1 : legalArg target a₁ with ⟨a₁', ⟨⟩⟩; rcases ha2 : legalArg target a₂ with ⟨a₂', ⟨⟩⟩
    rcases hb1 : legalArg target b₁ with ⟨b₁', ⟨⟩⟩; rcases hb2 : legalArg target b₂ with ⟨b₂', ⟨⟩⟩
    have ha' := legalArg_bits_rel target hc ha ha1 ha2
    have hb' := legalArg_bits_rel target hc hb hb1 hb2
    dsimp only
    split
    · exact .hlt
    · exact Wf.let2M _ ha' hb' fun h1 r₁ r₂ hr =>
        hk h1 _ _ (TRel.singleL target (TRel.single hr))
  | sdiv n =>
    rcases args₁ with ⟨a₁, b₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, b₂, ⟨⟩⟩
    rcases hargs with _ | ⟨ha, hargs⟩; rcases hargs with _ | ⟨hb, _⟩
    dsimp only [legalOp]
    rcases ha1 : legalArg target a₁ with ⟨a₁', ⟨⟩⟩; rcases ha2 : legalArg target a₂ with ⟨a₂', ⟨⟩⟩
    rcases hb1 : legalArg target b₁ with ⟨b₁', ⟨⟩⟩; rcases hb2 : legalArg target b₂ with ⟨b₂', ⟨⟩⟩
    have ha' := legalArg_bits_rel target hc ha ha1 ha2
    have hb' := legalArg_bits_rel target hc hb hb1 hb2
    dsimp only
    split
    · exact .hlt
    · split
      · exact Wf.let2M _ ha' hb' fun h1 r₁ r₂ hr =>
          hk h1 _ _ (TRel.singleL target (TRel.single hr))
      · exact emitSextToW_wf n (target.widenWidth n) ha' fun h1 sa₁ sa₂ hsa =>
          emitSextToW_wf n (target.widenWidth n) (hb'.weaken h1) fun h2 sb₁ sb₂ hsb =>
            Wf.let2M _ (hsa.weaken h2) hsb fun h3 r₁ r₂ hr =>
              emitMaskToN_wf n (target.widenWidth n) hr fun h4 rm₁ rm₂ hrm =>
                hk (sub_trans h1 (sub_trans h2 (sub_trans h3 h4))) _ _
                  (TRel.singleL target (TRel.single hrm))
  | srem n =>
    rcases args₁ with ⟨a₁, b₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, b₂, ⟨⟩⟩
    rcases hargs with _ | ⟨ha, hargs⟩; rcases hargs with _ | ⟨hb, _⟩
    dsimp only [legalOp]
    rcases ha1 : legalArg target a₁ with ⟨a₁', ⟨⟩⟩; rcases ha2 : legalArg target a₂ with ⟨a₂', ⟨⟩⟩
    rcases hb1 : legalArg target b₁ with ⟨b₁', ⟨⟩⟩; rcases hb2 : legalArg target b₂ with ⟨b₂', ⟨⟩⟩
    have ha' := legalArg_bits_rel target hc ha ha1 ha2
    have hb' := legalArg_bits_rel target hc hb hb1 hb2
    dsimp only
    split
    · exact .hlt
    · split
      · exact Wf.let2M _ ha' hb' fun h1 r₁ r₂ hr =>
          hk h1 _ _ (TRel.singleL target (TRel.single hr))
      · exact emitSextToW_wf n (target.widenWidth n) ha' fun h1 sa₁ sa₂ hsa =>
          emitSextToW_wf n (target.widenWidth n) (hb'.weaken h1) fun h2 sb₁ sb₂ hsb =>
            Wf.let2M _ (hsa.weaken h2) hsb fun h3 r₁ r₂ hr =>
              emitMaskToN_wf n (target.widenWidth n) hr fun h4 rm₁ rm₂ hrm =>
                hk (sub_trans h1 (sub_trans h2 (sub_trans h3 h4))) _ _
                  (TRel.singleL target (TRel.single hrm))
  | udiv0 n =>
    rcases args₁ with ⟨a₁, b₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, b₂, ⟨⟩⟩
    rcases hargs with _ | ⟨ha, hargs⟩; rcases hargs with _ | ⟨hb, _⟩
    dsimp only [legalOp]
    rcases ha1 : legalArg target a₁ with ⟨a₁', ⟨⟩⟩; rcases ha2 : legalArg target a₂ with ⟨a₂', ⟨⟩⟩
    rcases hb1 : legalArg target b₁ with ⟨b₁', ⟨⟩⟩; rcases hb2 : legalArg target b₂ with ⟨b₂', ⟨⟩⟩
    have ha' := legalArg_bits_rel target hc ha ha1 ha2
    have hb' := legalArg_bits_rel target hc hb hb1 hb2
    dsimp only
    split
    · exact hk (fun _ p => p) _ _ (trelBitsImmZero target n)
    · exact Wf.let2M _ ha' hb' fun h1 r₁ r₂ hr =>
        hk h1 _ _ (TRel.singleL target (TRel.single hr))
  | sdiv0 n =>
    rcases args₁ with ⟨a₁, b₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, b₂, ⟨⟩⟩
    rcases hargs with _ | ⟨ha, hargs⟩; rcases hargs with _ | ⟨hb, _⟩
    dsimp only [legalOp]
    rcases ha1 : legalArg target a₁ with ⟨a₁', ⟨⟩⟩; rcases ha2 : legalArg target a₂ with ⟨a₂', ⟨⟩⟩
    rcases hb1 : legalArg target b₁ with ⟨b₁', ⟨⟩⟩; rcases hb2 : legalArg target b₂ with ⟨b₂', ⟨⟩⟩
    have ha' := legalArg_bits_rel target hc ha ha1 ha2
    have hb' := legalArg_bits_rel target hc hb hb1 hb2
    dsimp only
    split
    · exact hk (fun _ p => p) _ _ (trelBitsImmZero target n)
    · split
      · exact Wf.let2M _ ha' hb' fun h1 r₁ r₂ hr =>
          hk h1 _ _ (TRel.singleL target (TRel.single hr))
      · exact emitSextToW_wf n (target.widenWidth n) ha' fun h1 sa₁ sa₂ hsa =>
          emitSextToW_wf n (target.widenWidth n) (hb'.weaken h1) fun h2 sb₁ sb₂ hsb =>
            Wf.let2M _ (hsa.weaken h2) hsb fun h3 r₁ r₂ hr =>
              emitMaskToN_wf n (target.widenWidth n) hr fun h4 rm₁ rm₂ hrm =>
                hk (sub_trans h1 (sub_trans h2 (sub_trans h3 h4))) _ _
                  (TRel.singleL target (TRel.single hrm))
  | mkpair a b =>
    rcases hargs with _ | ⟨ha, hargs⟩; rcases hargs with _ | ⟨hb, _⟩
    have hla := legalArg_rel target hc ha
    have hlb := legalArg_rel target hc hb
    dsimp only [legalOp]
    split
    · next h =>
      exact packFromLegal_wf target a hla fun h1 pa₁ pa₂ hpa =>
        packFromLegal_wf target b (TRel_argRel_weaken' h1 hlb) fun h2 pb₁ pb₂ hpb =>
          Wf.let2M (.mkpair a b) (hpa.weaken h2) hpb fun h3 p₁ p₂ hp =>
            hk (sub_trans h1 (sub_trans h2 h3)) _ _
              (TRel.singleL target (tupToPacked_rel h (TRel.single hp)))
    · next h =>
      exact hk (fun _ q => q) _ _
        (TRel.singleL target (tupToSplit_rel (Bool.eq_false_iff.mpr h) (TRel_tupAppend hla hlb)))
  | unpair a b =>
    rcases hargs with _ | ⟨hp, _⟩
    have hlp := legalArg_rel target hc hp
    dsimp only [legalOp]
    split
    · next h =>
      obtain ⟨h1, _⟩ := TRel.cons_iff.1 (packedToTup_rel h hlp)
      have hunpair : ∀ {px₁ : Arg V₁ (.pair a b)} {px₂ : Arg V₂ (.pair a b)},
          ArgRel G (.pair a b) px₁ px₂ →
          Wf G D
            (match px₁ with
             | .imm c => k₁ (encodeImm target a c.1, encodeImm target b c.2, ())
             | .var v => .let_ (.mk (.unpair a b) (.var v, ())) fun p =>
                 unpackToLegal target a (.var p.1) fun la =>
                   unpackToLegal target b (.var p.2.1) fun lb => k₁ (la, lb, ()))
            (match px₂ with
             | .imm c => k₂ (encodeImm target a c.1, encodeImm target b c.2, ())
             | .var v => .let_ (.mk (.unpair a b) (.var v, ())) fun p =>
                 unpackToLegal target a (.var p.1) fun la =>
                   unpackToLegal target b (.var p.2.1) fun lb => k₂ (la, lb, ())) := by
        intro px₁ px₂ hpx
        cases hpx with
        | imm c =>
          exact hk (fun _ q => q) _ _ (TRel.pairL target (encodeImm_rel target a c.1) (encodeImm_rel target b c.2))
        | var hm =>
          refine .let_ (.mk (.unpair a b) (.cons (.var hm) .nil)) fun p₁ p₂ => ?_
          rcases p₁ with ⟨va₁, vb₁, ⟨⟩⟩; rcases p₂ with ⟨va₂, vb₂, ⟨⟩⟩
          exact unpackToLegal_wf target a (.var List.mem_cons_self) fun h1 la₁ la₂ hla =>
            unpackToLegal_wf target b (.var (h1 _ (List.mem_cons_of_mem _ List.mem_cons_self))) fun h2 lb₁ lb₂ hlb =>
              hk (fun _ q => h2 _ (h1 _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ q))))
                _ _ (TRel.pairL target (TRel_argRel_weaken' h2 hla) hlb)
      exact hunpair h1
    · next h =>
      obtain ⟨hla, hlb⟩ := TRel_tupSplit (splitToTup_rel (Bool.eq_false_iff.mpr h) hlp)
      exact hk (fun _ q => q) _ _ (TRel.pairL target hla hlb)
  | bitcast t u h =>
    rcases hargs with _ | ⟨ha, _⟩
    have hla := legalArg_rel target hc ha
    dsimp only [legalOp]
    split
    · next heq => subst heq; exact hk (fun _ q => q) _ _ (TRel.singleL target hla)
    · have hsplit := splitLegalToLeaves_wf target t hla fun h1 fx₁ fx₂ hfx =>
        packLeavesToWords64_wf target t hfx fun h2 w₁ w₂ hw =>
          unpackWords64ToLeaves_wf target u hw 0 fun h3 fu₁ fu₂ hfu =>
            packLeavesToLegal_wf target u hfu fun h4 y₁ y₂ hy =>
              hk (sub_trans h1 (sub_trans h2 (sub_trans h3 h4))) _ _ (TRel.singleL target hy)
      cases t <;> dsimp only <;> split
      all_goals first
        | exact hsplit
        | (next ht =>
          cases u <;> dsimp only <;> split <;> first
            | exact hsplit
            | contradiction
            | next hu =>
              exact Wf.let1 (.bitcast _ _ h)
                (TRel_cast_singleton (legalTys_of_isNativeTy target _ ht) hla)
                fun h1 r₁ r₂ hr =>
                  hk h1 _ _ (TRel.singleL target
                    (TRel_cast_single_eq (legalTys_of_isNativeTy target _ hu).symm hr)))
  | shufd t imm =>
    rcases hargs with _ | ⟨ha, _⟩
    exact legalShufd_wf target imm t (legalArg_rel target hc ha) fun hG' y₁ y₂ hy =>
      hk hG' _ _ (TRel.singleL target hy)
  | shufb t =>
    rcases hargs with _ | ⟨ha, hargs⟩; rcases hargs with _ | ⟨hm, _⟩
    exact legalShufb_wf target t (legalArg_rel target hc ha) (legalArg_rel target hc hm)
      fun hG' y₁ y₂ hy => hk hG' _ _ (TRel.singleL target hy)
  | alignr t imm =>
    rcases hargs with _ | ⟨hi, hargs⟩; rcases hargs with _ | ⟨lo, _⟩
    exact legalAlignr_wf target imm t (legalArg_rel target hc hi) (legalArg_rel target hc lo)
      fun hG' y₁ y₂ hy => hk hG' _ _ (TRel.singleL target hy)
  | blendw t imm =>
    rcases hargs with _ | ⟨ha, hargs⟩; rcases hargs with _ | ⟨hb, _⟩
    exact legalBlendw_wf target imm t (legalArg_rel target hc ha) (legalArg_rel target hc hb)
      fun hG' y₁ y₂ hy => hk hG' _ _ (TRel.singleL target hy)
  | sha256rnds2 =>
    rcases hargs with _ | ⟨hc', hargs⟩; rcases hargs with _ | ⟨ha, hargs⟩; rcases hargs with _ | ⟨hw, _⟩
    have hlc := legalArg_rel target hc hc'
    have hla := legalArg_rel target hc ha
    have hlw := legalArg_rel target hc hw
    dsimp only [legalOp]
    split
    · next hk_pack =>
      have hl : target.legalTys v4i32 = [v4i32] := by simp [LegalTarget.legalTys, hk_pack]
      split
      · exact Wf.let3 .sha256rnds2 (TRel_cast_singleton hl hlc)
          (TRel_cast_singleton hl hla) (TRel_cast_singleton hl hlw) fun h1 r₁ r₂ hr =>
          hk h1 _ _ (TRel.singleL target (TRel_cast_single_eq hl.symm hr))
      · exact sha256rnds2_scalar_wf target hlc hla hlw fun hG' y₁ y₂ hy => hk hG' _ _ (TRel.singleL target hy)
    · exact sha256rnds2_scalar_wf target hlc hla hlw fun hG' y₁ y₂ hy => hk hG' _ _ (TRel.singleL target hy)
  | sha256msg1 =>
    rcases hargs with _ | ⟨ha, hargs⟩; rcases hargs with _ | ⟨hb, _⟩
    have hla := legalArg_rel target hc ha
    have hlb := legalArg_rel target hc hb
    dsimp only [legalOp]
    split
    · next hk_and =>
      have hkp : target.keepsPacked v4i32 = true := ((Bool.and_eq_true _ _).mp hk_and).1
      have hl : target.legalTys v4i32 = [v4i32] := by simp [LegalTarget.legalTys, hkp]
      exact Wf.let2 .sha256msg1 (TRel_cast_singleton hl hla)
        (TRel_cast_singleton hl hlb) fun h1 r₁ r₂ hr =>
        hk h1 _ _ (TRel.singleL target (TRel_cast_single_eq hl.symm hr))
    · exact sha256msg1_scalar_wf target hla hlb fun hG' y₁ y₂ hy => hk hG' _ _ (TRel.singleL target hy)
  | sha256msg2 =>
    rcases hargs with _ | ⟨ha, hargs⟩; rcases hargs with _ | ⟨hb, _⟩
    have hla := legalArg_rel target hc ha
    have hlb := legalArg_rel target hc hb
    dsimp only [legalOp]
    split
    · next hk_pack =>
      have hl : target.legalTys v4i32 = [v4i32] := by simp [LegalTarget.legalTys, hk_pack]
      split
      · exact Wf.let2 .sha256msg2 (TRel_cast_singleton hl hla)
          (TRel_cast_singleton hl hlb) fun h1 r₁ r₂ hr =>
          hk h1 _ _ (TRel.singleL target (TRel_cast_single_eq hl.symm hr))
      · exact sha256msg2_scalar_wf target hla hlb fun hG' y₁ y₂ hy => hk hG' _ _ (TRel.singleL target hy)
    · exact sha256msg2_scalar_wf target hla hlb fun hG' y₁ y₂ hy => hk hG' _ _ (TRel.singleL target hy)
  | fadd t =>
    rcases hargs with _ | ⟨ha, hargs⟩; rcases hargs with _ | ⟨hb, _⟩
    dsimp only [legalOp]
    split
    · exact .hlt
    · refine legalBinTree_wf target .fadd (fun u _ => target.vecFloatOpSupported (.fadd u) u)
        (fun _ _ => false) (fun _ _ => false) (fun _ {_ _ _} _ => rfl) ?_ ?_ ?_
        t (legalArg_rel target hc ha) (legalArg_rel target hc hb)
        (show OptRhsRel target LG t none none from trivial)
        fun hG' y₁ y₂ hy => hk hG' _ _ (TRel.singleL target hy)
      · intro _ _ _ _ _ _ _ _ _ _ _; exact .hlt
      · intro _ _ _ _ _ _ _ _ _ _ _ _; exact .hlt
      · intro f _ _ _ _ _ _ _ _ h1 h2 c; exact Wf.let2M _ h1 h2 c
  | fsub t =>
    rcases hargs with _ | ⟨ha, hargs⟩; rcases hargs with _ | ⟨hb, _⟩
    dsimp only [legalOp]
    split
    · exact .hlt
    · refine legalBinTree_wf target .fsub (fun u _ => target.vecFloatOpSupported (.fsub u) u)
        (fun _ _ => false) (fun _ _ => false) (fun _ {_ _ _} _ => rfl) ?_ ?_ ?_
        t (legalArg_rel target hc ha) (legalArg_rel target hc hb)
        (show OptRhsRel target LG t none none from trivial)
        fun hG' y₁ y₂ hy => hk hG' _ _ (TRel.singleL target hy)
      · intro _ _ _ _ _ _ _ _ _ _ _; exact .hlt
      · intro _ _ _ _ _ _ _ _ _ _ _ _; exact .hlt
      · intro f _ _ _ _ _ _ _ _ h1 h2 c; exact Wf.let2M _ h1 h2 c
  | fmul t =>
    rcases hargs with _ | ⟨ha, hargs⟩; rcases hargs with _ | ⟨hb, _⟩
    dsimp only [legalOp]
    split
    · exact .hlt
    · refine legalBinTree_wf target .fmul (fun u _ => target.vecFloatOpSupported (.fmul u) u)
        (fun _ _ => false) (fun _ _ => false) (fun _ {_ _ _} _ => rfl) ?_ ?_ ?_
        t (legalArg_rel target hc ha) (legalArg_rel target hc hb)
        (show OptRhsRel target LG t none none from trivial)
        fun hG' y₁ y₂ hy => hk hG' _ _ (TRel.singleL target hy)
      · intro _ _ _ _ _ _ _ _ _ _ _; exact .hlt
      · intro _ _ _ _ _ _ _ _ _ _ _ _; exact .hlt
      · intro f _ _ _ _ _ _ _ _ h1 h2 c; exact Wf.let2M _ h1 h2 c
  | fdiv t =>
    rcases hargs with _ | ⟨ha, hargs⟩; rcases hargs with _ | ⟨hb, _⟩
    dsimp only [legalOp]
    split
    · exact .hlt
    · refine legalBinTree_wf target .fdiv (fun u _ => target.vecFloatOpSupported (.fdiv u) u)
        (fun _ _ => false) (fun _ _ => false) (fun _ {_ _ _} _ => rfl) ?_ ?_ ?_
        t (legalArg_rel target hc ha) (legalArg_rel target hc hb)
        (show OptRhsRel target LG t none none from trivial)
        fun hG' y₁ y₂ hy => hk hG' _ _ (TRel.singleL target hy)
      · intro _ _ _ _ _ _ _ _ _ _ _; exact .hlt
      · intro _ _ _ _ _ _ _ _ _ _ _ _; exact .hlt
      · intro f _ _ _ _ _ _ _ _ h1 h2 c; exact Wf.let2M _ h1 h2 c
  | ffma t =>
    rcases hargs with _ | ⟨ha, hargs⟩; rcases hargs with _ | ⟨hb, hargs⟩; rcases hargs with _ | ⟨hc', _⟩
    dsimp only [legalOp]
    split
    · exact .hlt
    · exact legalTernaryTree_wf target .ffma (fun u => target.vecFloatOpSupported (.ffma u) u)
        (fun {_ _ _ _ _ _ _ _ _ _} _ _ _ _ => .hlt) (fun _ {_ _ _ _ _ _ _ _ _ _} _ _ _ _ => .hlt)
        (fun f {_ _ _ _ _ _ _ _ _ _} h1 h2 h3 c => Wf.let3M _ h1 h2 h3 c)
        t (legalArg_rel target hc ha) (legalArg_rel target hc hb) (legalArg_rel target hc hc')
        fun hG' y₁ y₂ hy => hk hG' _ _ (TRel.singleL target hy)
  | fsqrt t =>
    rcases hargs with _ | ⟨ha, _⟩
    dsimp only [legalOp]
    split
    · exact .hlt
    · exact legalUnaryTree_wf target .fsqrt (fun u => target.vecFloatOpSupported (.fsqrt u) u)
        (fun {_ _ _ _ _ _} _ _ => .hlt) (fun _ {_ _ _ _ _ _} _ _ => .hlt)
        (fun f {_ _ _ _ _ _} h1 c => Wf.let1M _ h1 c)
        t (legalArg_rel target hc ha) fun hG' y₁ y₂ hy => hk hG' _ _ (TRel.singleL target hy)
  | fneg t =>
    rcases hargs with _ | ⟨ha, _⟩
    dsimp only [legalOp]
    split
    · exact .hlt
    · exact legalUnaryTree_wf target .fneg (fun u => target.vecFloatOpSupported (.fneg u) u)
        (fun {_ _ _ _ _ _} _ _ => .hlt) (fun _ {_ _ _ _ _ _} _ _ => .hlt)
        (fun f {_ _ _ _ _ _} h1 c => Wf.let1M _ h1 c)
        t (legalArg_rel target hc ha) fun hG' y₁ y₂ hy => hk hG' _ _ (TRel.singleL target hy)
  | fabs t =>
    rcases hargs with _ | ⟨ha, _⟩
    dsimp only [legalOp]
    split
    · exact .hlt
    · exact legalUnaryTree_wf target .fabs (fun u => target.vecFloatOpSupported (.fabs u) u)
        (fun {_ _ _ _ _ _} _ _ => .hlt) (fun _ {_ _ _ _ _ _} _ _ => .hlt)
        (fun f {_ _ _ _ _ _} h1 c => Wf.let1M _ h1 c)
        t (legalArg_rel target hc ha) fun hG' y₁ y₂ hy => hk hG' _ _ (TRel.singleL target hy)
  | fcmp o t m h =>
    subst h
    rcases hargs with _ | ⟨ha, hargs⟩; rcases hargs with _ | ⟨hb, _⟩
    dsimp only [legalOp]
    split
    · exact .hlt
    · exact legalFCmpTree_wf target o t (legalArg_rel target hc ha) (legalArg_rel target hc hb)
        fun hG' y₁ y₂ hy => hk hG' _ _ (TRel.singleL target hy)
  | fptoui f n =>
    rcases args₁ with ⟨a₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, ⟨⟩⟩
    rcases hargs with _ | ⟨ha, _⟩
    dsimp only [legalOp]
    rcases ha1 : legalArg target a₁ with ⟨a₁', ⟨⟩⟩; rcases ha2 : legalArg target a₂ with ⟨a₂', ⟨⟩⟩
    have ha' := legalArg_float_rel target hc ha ha1 ha2
    dsimp only
    split
    · exact Wf.let1M _ ha' fun h1 _ _ _ =>
        hk h1 _ _ (TRel.singleL target (TRel.single (ArgRel.imm _)))
    · exact Wf.let1M _ ha' fun h1 r₁ r₂ hr =>
        hk h1 _ _ (TRel.singleL target (TRel.single hr))
  | fptosi f n =>
    rcases args₁ with ⟨a₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, ⟨⟩⟩
    rcases hargs with _ | ⟨ha, _⟩
    dsimp only [legalOp]
    rcases ha1 : legalArg target a₁ with ⟨a₁', ⟨⟩⟩; rcases ha2 : legalArg target a₂ with ⟨a₂', ⟨⟩⟩
    have ha' := legalArg_float_rel target hc ha ha1 ha2
    dsimp only
    split
    · exact .hlt
    · split
      · exact Wf.let1M _ ha' fun h1 r₁ r₂ hr =>
          hk h1 _ _ (TRel.singleL target (TRel.single hr))
      · exact Wf.let1M _ ha' fun h1 r₁ r₂ hr =>
          emitMaskToN_wf n (target.widenWidth n) hr fun h2 rm₁ rm₂ hrm =>
            hk (sub_trans h1 h2) _ _ (TRel.singleL target (TRel.single hrm))
  | uitofp n f =>
    rcases args₁ with ⟨a₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, ⟨⟩⟩
    rcases hargs with _ | ⟨ha, _⟩
    dsimp only [legalOp]
    rcases ha1 : legalArg target a₁ with ⟨a₁', ⟨⟩⟩; rcases ha2 : legalArg target a₂ with ⟨a₂', ⟨⟩⟩
    have ha' := legalArg_bits_rel target hc ha ha1 ha2
    dsimp only
    split
    · exact Wf.let1M _ (.imm _) fun h1 r₁ r₂ hr =>
        hk h1 _ _ (TRel.singleL target (TRel.single hr))
    · exact Wf.let1M _ ha' fun h1 r₁ r₂ hr =>
        hk h1 _ _ (TRel.singleL target (TRel.single hr))
  | sitofp n f =>
    rcases args₁ with ⟨a₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, ⟨⟩⟩
    rcases hargs with _ | ⟨ha, _⟩
    dsimp only [legalOp]
    rcases ha1 : legalArg target a₁ with ⟨a₁', ⟨⟩⟩; rcases ha2 : legalArg target a₂ with ⟨a₂', ⟨⟩⟩
    have ha' := legalArg_bits_rel target hc ha ha1 ha2
    dsimp only
    split
    · exact Wf.let1M _ (.imm _) fun h1 r₁ r₂ hr =>
        hk h1 _ _ (TRel.singleL target (TRel.single hr))
    · exact emitSextToW_wf n (target.widenWidth n) ha' fun h1 sa₁ sa₂ hsa =>
        Wf.let1M _ hsa fun h2 r₁ r₂ hr =>
          hk (sub_trans h1 h2) _ _ (TRel.singleL target (TRel.single hr))
  | fcvt f g =>
    rcases args₁ with ⟨a₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, ⟨⟩⟩
    rcases hargs with _ | ⟨ha, _⟩
    dsimp only [legalOp]
    rcases ha1 : legalArg target a₁ with ⟨a₁', ⟨⟩⟩; rcases ha2 : legalArg target a₂ with ⟨a₂', ⟨⟩⟩
    have ha' := legalArg_float_rel target hc ha ha1 ha2
    dsimp only
    exact Wf.let1M _ ha' fun h1 r₁ r₂ hr =>
      hk h1 _ _ (TRel.singleL target (TRel.single hr))

theorem legalLoad_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty} :
    ∀ (t : Ty) {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} {p₁ : Arg V₁ i64} {p₂ : Arg V₂ i64},
      ArgRel G i64 p₁ p₂ →
      ∀ {k₁ : LVar target V₁ t → Expr V₁ L₁ rs} {k₂ : LVar target V₂ t → Expr V₂ L₂ rs},
      (∀ {G'}, (∀ q ∈ G, q ∈ G') → ∀ y₁ y₂, TRel (ArgRel G') y₁ y₂ → Wf G' D (k₁ y₁) (k₂ y₂)) →
      Wf G D (legalLoad target t p₁ k₁) (legalLoad target t p₂ k₂)
  | .bool, _, _, _, _, hp, _, _, hk =>
    Wf.load1 .bool hp fun h1 y₁ y₂ hy =>
      hk h1 _ _ (TRel.single hy)
  | .bits n, _, _, _, _, hp, _, _, hk => by
    simp only [legalLoad]
    split
    · exact Wf.load1 (.bits (target.widenWidth n)) hp fun h1 y₁ y₂ hy =>
        hk h1 _ _ (TRel.single hy)
    · exact emitLoadBits_wf target.bitWidths n (target.widenWidth n) hp fun hG' r₁ r₂ hr =>
        hk hG' _ _ (TRel.single hr)
  | .float f, _, _, _, _, hp, _, _, hk =>
    Wf.load1 (.float f) hp fun h1 y₁ y₂ hy =>
      hk h1 _ _ (TRel.single hy)
  | .pair a b, G, D, p₁, p₂, hp, k₁, k₂, hk => by
    simp only [legalLoad]
    split
    · next h =>
      exact Wf.load1 (.pair a b) hp fun h1 v₁ v₂ hv =>
        hk h1 _ _ (tupToPacked_rel h (.cons hv .nil))
    · next h =>
      split
      · refine legalLoad_wf a hp fun {G1} h1 la₁ la₂ hla => ?_
        have hstep2 : ∀ {G2 : Ctx V₁ V₂} {hG1 : ∀ q ∈ G1, q ∈ G2} {ptr2₁ : Arg V₁ i64} {ptr2₂ : Arg V₂ i64},
            ArgRel G2 i64 ptr2₁ ptr2₂ →
            Wf G2 D
              (legalLoad target b ptr2₁ fun lb => k₁ (tupToSplit (Bool.eq_false_iff.mpr h) (tupAppend la₁ lb)))
              (legalLoad target b ptr2₂ fun lb => k₂ (tupToSplit (Bool.eq_false_iff.mpr h) (tupAppend la₂ lb))) := by
          intro G2 hG1 ptr2₁ ptr2₂ hptr
          exact legalLoad_wf b hptr fun h2 lb₁ lb₂ hlb =>
            hk (sub_trans h1 (sub_trans hG1 h2)) _ _
              (tupToSplit_rel (Bool.eq_false_iff.mpr h)
                (TRel_tupAppend (TRel_argRel_weaken' (sub_trans hG1 h2) hla) hlb))
        by_cases ha0 : a.bytes == 0
        · simp only [ha0, ↓reduceIte]
          exact hstep2 (hG1 := fun _ p => p) (hp.weaken h1)
        · simp only [ha0, Bool.false_eq_true, ↓reduceIte]
          exact Wf.let2 _ (hp.weaken h1) (.imm _) fun h2 p2₁ p2₂ hp2 =>
            hstep2 (hG1 := h2) hp2
      · split
        · exact unpackWords64ToLeaves_wf target (a.pair b) .nil 0 fun h1 fres₁ fres₂ hfres =>
            packLeavesToLegal_wf target (a.pair b) hfres fun h2 res₁ res₂ hres =>
              hk (sub_trans h1 h2) res₁ res₂ hres
        · exact loadByteChunksToWords64_wf (chunkBytes target.bitWidths (Ty.pair a b).bytes) hp 0 .nil (.imm _) 0
            fun h1 ws₁ ws₂ hws =>
              unpackWords64ToLeaves_wf target (a.pair b) hws 0 fun h2 fres₁ fres₂ hfres =>
                packLeavesToLegal_wf target (a.pair b) hfres fun h3 res₁ res₂ hres =>
                  hk (sub_trans h1 (sub_trans h2 h3)) res₁ res₂ hres

theorem legalStore_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty} :
    ∀ (t : Ty) {G : Ctx V₁ V₂} {D : Ctx L₁ L₂}
      {xs₁ : LVar target V₁ t} {xs₂ : LVar target V₂ t} {p₁ : Arg V₁ i64} {p₂ : Arg V₂ i64},
      TRel (ArgRel G) xs₁ xs₂ → ArgRel G i64 p₁ p₂ →
      {k₁ : Expr V₁ L₁ rs} → {k₂ : Expr V₂ L₂ rs} →
      (∀ {G'}, (∀ q ∈ G, q ∈ G') → Wf G' D k₁ k₂) →
      Wf G D (legalStore target t xs₁ p₁ k₁) (legalStore target t xs₂ p₂ k₂)
  | .bool, _, _, xs₁, xs₂, _, _, hxs, hp, _, _, hk => by
    rcases xs₁ with ⟨v₁, ⟨⟩⟩; rcases xs₂ with ⟨v₂, ⟨⟩⟩
    cases hxs with | cons hv _ => exact .store hv hp (hk (fun _ q => q))
  | .bits n, _, _, xs₁, xs₂, _, _, hxs, hp, _, _, hk => by
    rcases xs₁ with ⟨v₁, ⟨⟩⟩; rcases xs₂ with ⟨v₂, ⟨⟩⟩
    cases hxs with | cons hv _ =>
    simp only [legalStore]
    split
    · exact .store hv hp (hk (fun _ q => q))
    · exact emitStoreBits_wf target.bitWidths n (target.widenWidth n) hv hp hk
  | .float _, _, _, xs₁, xs₂, _, _, hxs, hp, _, _, hk => by
    rcases xs₁ with ⟨v₁, ⟨⟩⟩; rcases xs₂ with ⟨v₂, ⟨⟩⟩
    cases hxs with | cons hv _ => exact .store hv hp (hk (fun _ q => q))
  | .pair a b, G, D, xs₁, xs₂, p₁, p₂, hxs, hp, k₁, k₂, hk => by
    simp only [legalStore]
    split
    · next h =>
      obtain ⟨h1, _⟩ := TRel.cons_iff.1 (packedToTup_rel h hxs)
      exact .store h1 hp (hk (fun _ q => q))
    · next h =>
      split
      · obtain ⟨ha, hb⟩ := TRel_tupSplit (splitToTup_rel (Bool.eq_false_iff.mpr h) hxs)
        refine legalStore_wf a ha hp fun hG1 => ?_
        by_cases ha0 : a.bytes == 0
        · simp only [ha0, ↓reduceIte]
          exact legalStore_wf b (TRel_argRel_weaken' hG1 hb) (hp.weaken hG1)
            fun hG2 => hk (sub_trans hG1 hG2)
        · simp only [ha0, Bool.false_eq_true, ↓reduceIte]
          exact Wf.let2 _ (hp.weaken hG1) (.imm _) fun hG2 p2₁ p2₂ hp2 =>
            legalStore_wf b (TRel_argRel_weaken' (sub_trans hG1 hG2) hb) hp2
              fun hG3 => hk (sub_trans hG1 (sub_trans hG2 hG3))
      · split
        · exact hk (fun _ q => q)
        · exact splitLegalToLeaves_wf target (.pair a b) hxs fun hG1 fx₁ fx₂ hfx =>
            packLeavesToWords64_wf target (.pair a b) hfx fun hG2 ws₁ ws₂ hws =>
              storeByteChunksFromWords64_wf (chunkBytes target.bitWidths (Ty.pair a b).bytes) hws
                (hp.weaken (sub_trans hG1 hG2)) 0
                fun hG3 => hk (sub_trans hG1 (sub_trans hG2 hG3))

theorem CGood.cons {V₁ V₂ : Ty → Type} {G : Ctx V₁ V₂}
    {LG : Ctx (LVar target V₁) (LVar target V₂)} (hc : CGood target G LG)
    {t : Ty} {x₁ : LVar target V₁ t} {x₂ : LVar target V₂ t} (hx : TRel (ArgRel G) x₁ x₂) :
    CGood target G (⟨t, x₁, x₂⟩ :: LG) := by
  intro t' lv₁ lv₂ hm
  rcases List.mem_cons.1 hm with hhead | htail
  · cases hhead; exact hx
  · exact hc t' lv₁ lv₂ htail

theorem CGood.pushTRel {V₁ V₂ : Ty → Type} {G : Ctx V₁ V₂}
    {LG : Ctx (LVar target V₁) (LVar target V₂)} (hc : CGood target G LG) :
    {ts : List Ty} → {xs₁ : Tup (LVar target V₁) ts} → {xs₂ : Tup (LVar target V₂) ts} →
      TRel (fun _ x₁ x₂ => TRel (ArgRel G) x₁ x₂) xs₁ xs₂ →
      CGood target G (Tup.zip xs₁ xs₂ ++ LG)
  | [], (), (), .nil => hc
  | _ :: _, (_, _), (_, _), .cons hx hxs =>
    CGood.cons target (CGood.pushTRel hc hxs) hx

theorem legalBlocks_wf_aux {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty} :
    ∀ {sig : List (List Ty)}
      {b₁ : Blocks (LVar target V₁) (LLab target L₁) rs sig}
      {b₂ : Blocks (LVar target V₂) (LLab target L₂) rs sig}
      {G : Ctx V₁ V₂} {D : Ctx L₁ L₂},
      (∀ {ts} (i : Member ts sig) (ys₁ : Tup V₁ (target.legalSig ts)) (ys₂ : Tup V₂ (target.legalSig ts)),
        Wf (ys₁.zip ys₂ ++ G) D
          (legalExpr target (b₁.get i (splitParams target ts ys₁)))
          (legalExpr target (b₂.get i (splitParams target ts ys₂)))) →
      WfB G D (legalBlocks target b₁) (legalBlocks target b₂)
  | [], .nil, .nil, _, _, _ => .nil
  | _ :: _, .cons _ _, .cons _ _, _, _, ih => by
    simp only [legalBlocks]
    exact .cons (fun ys₁ ys₂ => ih .here ys₁ ys₂)
      (legalBlocks_wf_aux fun i ys₁ ys₂ => ih (.there i) ys₁ ys₂)

theorem legalExpr_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {LG : Ctx (LVar target V₁) (LVar target V₂)} {LD : Ctx (LLab target L₁) (LLab target L₂)}
    {e₁ : Expr (LVar target V₁) (LLab target L₁) rs}
    {e₂ : Expr (LVar target V₂) (LLab target L₂) rs}
    (hwf : Wf LG LD e₁ e₂) :
    ∀ {G : Ctx V₁ V₂} {D : Ctx L₁ L₂},
      CGood target G LG → DGood target D LD →
      Wf G D (legalExpr target e₁) (legalExpr target e₂) := by
  refine Wf.induct (motive := fun LG' LD' e₁' e₂' _ =>
    ∀ {G : Ctx V₁ V₂} {D : Ctx L₁ L₂},
      CGood target G LG' → DGood target D LD' →
      Wf G D (legalExpr target e₁') (legalExpr target e₂')) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hwf
  · intro LG LD ts op₁ op₂ k₁ k₂ hop hk ihk G D hc hd
    simp only [legalExpr]
    exact legalOp_wf target hc hop fun hG' y₁ y₂ hy =>
      ihk y₁ y₂ (CGood.pushTRel target (CGood.weaken target hG' hc) hy) hd
  · intro LG LD t a₁ a₂ k₁ k₂ ha hk ihk G D hc hd
    simp only [legalExpr]
    split
    · next h64 =>
      refine legalLoad_wf target t (castArgBits_rel h64 (legalArg_bits_fst_rel target hc ha))
        fun hG' y₁ y₂ hy => ihk y₁ y₂ (CGood.cons target (CGood.weaken target hG' hc) hy) hd
    · exact .hlt
  · intro LG LD t v₁ v₂ a₁ a₂ k₁ k₂ hv ha hk ihk G D hc hd
    simp only [legalExpr]
    split
    · next h64 =>
      exact legalStore_wf target t (legalArg_rel target hc hv)
        (castArgBits_rel h64 (legalArg_bits_fst_rel target hc ha))
        fun hG' => ihk (CGood.weaken target hG' hc) hd
    · exact .hlt
  · intro LG LD f as bs args₁ args₂ k₁ k₂ hargs hk ihk G D hc hd
    simp only [legalExpr]
    exact .call f (joinArgs_rel target hc hargs) fun res₁ res₂ =>
      ihk (splitParams target bs res₁) (splitParams target bs res₂) (CGood.pushSplit target hc bs res₁ res₂) hd
  · intro LG LD c₁ c₂ t₁ t₂ e₁ e₂ hcd ht he iht ihe G D hc hd
    simp only [legalExpr]
    exact .jnz (legalArg_bool_fst_rel target hc hcd) (iht hc hd) (ihe hc hd)
  · intro LG LD ts j₁ j₂ args₁ args₂ hj hargs G D hc hd
    simp only [legalExpr]
    exact .jump (hd ts j₁ j₂ hj) (joinArgs_rel target hc hargs)
  · intro LG LD vs₁ vs₂ hvs G D hc hd
    simp only [legalExpr]
    exact .ret (joinArgs_rel target hc hvs)
  · intro LG LD f as args₁ args₂ hargs G D hc hd
    simp only [legalExpr]
    exact .exit f (joinArgs_rel target hc hargs)
  · intro LG LD G D _ _
    simp only [legalExpr]
    exact .hlt
  · intro LG LD sig b₁ b₂ k₁ k₂ hb hk ihb ihk G D hc hd
    simp only [legalExpr]
    refine .group (fun Js₁ Js₂ => legalBlocks_wf_aux target fun i ys₁ ys₂ =>
      ihb (tupLiftMap target.legalSig _ Js₁) (tupLiftMap target.legalSig _ Js₂) i
        (splitParams target _ ys₁) (splitParams target _ ys₂)
        (CGood.pushSplit target hc _ ys₁ ys₂) (DGood.pushLiftMap target hd Js₁ Js₂)) fun Js₁ Js₂ =>
      ihk (tupLiftMap target.legalSig _ Js₁) (tupLiftMap target.legalSig _ Js₂)
        hc (DGood.pushLiftMap target hd Js₁ Js₂)

end LegalWf

theorem Func.legal_wf (target : LegalTarget) {as rs : List Ty} {f : Func as rs} (hf : f.Wf) :
    (f.legal target).Wf := by
  intro V₁ V₂ L₁ L₂ xs₁ xs₂
  have hc0 : CGood target (Tup.zip xs₁ xs₂) [] := fun _ _ _ hm => by cases hm
  have hc1 := CGood.pushSplit target hc0 as xs₁ xs₂
  have hc : CGood target (Tup.zip xs₁ xs₂)
      (Tup.zip (splitParams target as xs₁) (splitParams target as xs₂)) := by
    intro t lv₁ lv₂ hm
    have hmem : ⟨t, lv₁, lv₂⟩ ∈ Tup.zip (splitParams target as xs₁) (splitParams target as xs₂) ++ [] := by
      simp only [List.append_nil]; exact hm
    exact TRel_argRel_weaken' (fun p hp => by rcases List.mem_append.1 hp with h | h <;> exact h) (hc1 t lv₁ lv₂ hmem)
  have hd : DGood target ([] : Ctx L₁ L₂) ([] : Ctx (LLab target L₁) (LLab target L₂)) :=
    fun _ _ _ hm => by cases hm
  exact legalExpr_wf target (hf (LVar target V₁) (LVar target V₂) (LLab target L₁) (LLab target L₂)
    (splitParams target as xs₁) (splitParams target as xs₂)) hc hd

theorem Fn.legal_wf (target : LegalTarget) {fn : Fn} (hfn : fn.Wf) :
    (fn.legal target).Wf :=
  Func.legal_wf target hfn

/-! ## Section 4: Semantic preservation (`Func.legal_wp` / `Func.legal_spec`) -/

section LegalWp

/-- Lift a source return postcondition `Q : Post rs` to the legalized return tuple. -/
def legalPost (target : LegalTarget) {rs : List Ty} (Q : Post rs) : Post (target.legalSig rs) :=
  fun ys m => ∃ xs : Tup Val rs, encodeTup target rs xs = ys ∧ Q xs m

/-- Lift a source abnormal-exit postcondition `X : XPost` across legalized exit signatures. -/
def legalXPost (target : LegalTarget) (X : XPost) : XPost :=
  fun g cs' ys m => ∃ (cs : List Ty) (hcs : target.legalSig cs = cs') (xs : Tup Val cs),
    cast (congrArg (Tup Val) hcs) (encodeTup target cs xs) = ys ∧ X g cs xs m

/-- Simulation relation between source callee environment `Γsrc` and target environment `Γtgt`. -/
def EnvRefines (target : LegalTarget) (Γsrc Γtgt : Env) : Prop :=
  ∀ f as bs xs m P E,
    Γsrc f as bs xs m P E →
    Γtgt f (target.legalSig as) (target.legalSig bs) (encodeTup target as xs) m
      (legalPost target P) (legalXPost target E)

/-- Canonical legalized environment transforming every source contract via `encodeTup` / `legalPost` /
`legalXPost` (with consequence closure matching `wp_env_mono`). -/
def legalEnv (target : LegalTarget) (Γ : Env) : Env :=
  fun f as' bs' xs' m' Q' X' =>
    ∃ (as bs : List Ty) (has : target.legalSig as = as') (hbs : target.legalSig bs = bs')
      (xs : Tup Val as) (P : Post bs) (E : XPost),
      cast (congrArg (Tup Val) has) (encodeTup target as xs) = xs' ∧
      (∀ r m, legalPost target P r m → Q' (cast (congrArg (Tup Val) hbs) r) m) ∧
      (∀ g cs ys m, legalXPost target E g cs ys m → X' g cs ys m) ∧
      Γ f as bs xs m' P E

theorem envRefines_legalEnv (target : LegalTarget) (Γ : Env) : EnvRefines target Γ (legalEnv target Γ) :=
  fun _ as bs xs _ P E h => ⟨as, bs, rfl, rfl, xs, P, E, rfl, fun _ _ hp => hp, fun _ _ _ _ hx => hx, h⟩

theorem valsTup_eq_vals : ∀ {ts : List Ty} (xs : Tup (Arg Val) ts), valsTup xs = vals xs
  | [], () => rfl
  | _ :: _, (a, as) => congrArg (a.val, ·) (valsTup_eq_vals as)

@[simp] theorem valsTup_single {t : Ty} (a : Arg Val t) :
    valsTup (ts := [t]) (a, ()) = (a.val, ()) := rfl

@[simp] theorem val_castArgBits {m n : Nat} (h : m = n) (x : Arg Val (.bits m)) :
    (castArgBits h x).val = h ▸ x.val := by
  subst h; rfl

@[simp] theorem setWidth_cast_bits {m n k : Nat} (h : m = n) (x : BitVec m) :
    (h ▸ x : BitVec n).setWidth k = x.setWidth k := by
  subst h; rfl

theorem cast_eq_setWidth {m n : Nat} (h : m = n) (x : BitVec m) :
    (h ▸ x : BitVec n) = x.setWidth n := by
  subst h; simp [BitVec.setWidth_eq]

theorem setWidth_eq_cast {m n : Nat} (h : m = n) (x : BitVec m) :
    (x.setWidth n, ()) = cast (by rw [h]) (x, ()) := by
  subst h; simp [BitVec.setWidth_eq]

theorem cast_cast_eq {α β : Type} (h₁ : α = β) (h₂ : β = α) (x : α) :
    cast h₂ (cast h₁ x) = x := by
  subst h₁; rfl

theorem cast_inj {α β : Type} (h : α = β) {x y : α} (heq : cast h x = cast h y) : x = y := by
  subst h; exact heq

@[simp] theorem leafVals_pair (target : LegalTarget) (a b : Ty) (p : Val (.pair a b)) :
    leafVals target (.pair a b) p = tupAppend (leafVals target a p.1) (leafVals target b p.2) := rfl

theorem tupSplit_valsTup {as bs : List Ty} (fx : Tup (Arg Val) (as ++ bs)) :
    tupSplit (valsTup fx) = (valsTup (tupSplit (as := as) (bs := bs) fx).1,
      valsTup (tupSplit (as := as) (bs := bs) fx).2) := by
  have h := congrArg valsTup (tupAppend_tupSplit fx)
  rw [valsTup_tupAppend] at h
  rw [← h, tupSplit_tupAppend]

theorem encodeVal_pair_packed (target : LegalTarget) {a b : Ty}
    (h : target.keepsPacked (.pair a b) = true) (p : Val (.pair a b)) :
    encodeVal target (.pair a b) p =
      cast (by simp [LegalTarget.legalTys, h]) (show Tup Val [.pair a b] from (p, ())) := by
  simp only [encodeVal, h, ↓reduceDIte]

theorem encodeVal_pair_split (target : LegalTarget) {a b : Ty}
    (h : target.keepsPacked (.pair a b) = false) (p : Val (.pair a b)) :
    encodeVal target (.pair a b) p =
      cast (by simp [LegalTarget.legalTys, h])
        (tupAppend (encodeVal target a p.1) (encodeVal target b p.2)) := by
  simp only [encodeVal, h, Bool.false_eq_true, ↓reduceDIte]

theorem valsTup_packedToTup_encode (target : LegalTarget) {a b : Ty}
    (h : target.keepsPacked (.pair a b) = true)
    {xs : Tup (Arg Val) (target.legalTys (.pair a b))} {p : Val (.pair a b)}
    (hxs : valsTup xs = encodeVal target (.pair a b) p) :
    valsTup (packedToTup h xs) = (p, ()) := by
  rw [valsTup_packedToTup h, hxs, encodeVal_pair_packed target h, cast_cast_eq]

theorem valsTup_splitToTup_encode (target : LegalTarget) {a b : Ty}
    (h : target.keepsPacked (.pair a b) = false)
    {xs : Tup (Arg Val) (target.legalTys (.pair a b))} {p : Val (.pair a b)}
    (hxs : valsTup xs = encodeVal target (.pair a b) p) :
    valsTup (splitToTup h xs) = tupAppend (encodeVal target a p.1) (encodeVal target b p.2) := by
  rw [valsTup_splitToTup h, hxs, encodeVal_pair_split target h, cast_cast_eq]

theorem valsTup_tupToPacked_encode (target : LegalTarget) {a b : Ty}
    (h : target.keepsPacked (.pair a b) = true)
    {xs : Tup (Arg Val) [.pair a b]} {p : Val (.pair a b)} (hxs : valsTup xs = (p, ())) :
    valsTup (tupToPacked h xs) = encodeVal target (.pair a b) p := by
  rw [valsTup_tupToPacked h, hxs, encodeVal_pair_packed target h]

theorem valsTup_tupToSplit_encode (target : LegalTarget) {a b : Ty}
    (h : target.keepsPacked (.pair a b) = false)
    {xs : Tup (Arg Val) (target.legalTys a ++ target.legalTys b)} {p : Val (.pair a b)}
    (hxs : valsTup xs = tupAppend (encodeVal target a p.1) (encodeVal target b p.2)) :
    valsTup (tupToSplit h xs) = encodeVal target (.pair a b) p := by
  rw [valsTup_tupToSplit h, hxs, encodeVal_pair_split target h]

theorem supportsTy_mask (target : LegalTarget) : ∀ (t : Ty), target.supportsTy t.mask = true
  | .bool | .bits _ | .float _ => rfl
  | .pair a b => by simp [LegalTarget.supportsTy, supportsTy_mask target a, supportsTy_mask target b]

theorem legalTys_eq_singleton_of_isLegalTy (target : LegalTarget) :
    ∀ {t : Ty}, target.isLegalTy t = true → target.legalTys t = [t]
  | .bool, _ => rfl
  | .bits n, ht => by
    have hmem : n ∈ target.bitWidths := by simpa [LegalTarget.isLegalTy] using ht
    simp [LegalTarget.legalTys, widenWidth_eq_self_of_mem target hmem]
  | .float _, _ => rfl
  | .pair a b, ht => by
    have hp : target.keepsPacked (.pair a b) = true := by simpa [LegalTarget.isLegalTy] using ht
    simp [LegalTarget.legalTys, hp]

theorem encodeVal_self (target : LegalTarget) :
    ∀ {t : Ty} (ht : target.isLegalTy t = true) (v : Val t),
      encodeVal target t v =
        cast (congrArg (Tup Val) (legalTys_eq_singleton_of_isLegalTy target ht).symm)
          (show Tup Val [t] from (v, ()))
  | .bool, _, _ => rfl
  | .bits n, ht, v => by
    have hmem : n ∈ target.bitWidths := by simpa [LegalTarget.isLegalTy] using ht
    have hw : target.widenWidth n = n := widenWidth_eq_self_of_mem target hmem
    dsimp only [encodeVal, LegalTarget.legalTys]
    exact setWidth_eq_cast hw.symm v
  | .float _, _, _ => rfl
  | .pair a b, ht, v => by
    have hp : target.keepsPacked (.pair a b) = true := by simpa [LegalTarget.isLegalTy] using ht
    exact encodeVal_pair_packed target hp v

theorem encodeVal_inj (target : LegalTarget) :
    ∀ {t : Ty}, target.supportsTy t = true → Function.Injective (encodeVal target t)
  | .bool, _, a, b, h => congrArg Prod.fst h
  | .bits n, ht, a, b, h => by
    have hle := le_widenWidth_of_supports ht
    have h1 : a.setWidth (target.widenWidth n) = b.setWidth (target.widenWidth n) :=
      congrArg Prod.fst h
    have h' := congrArg (BitVec.setWidth n) h1
    simpa [BitVec.setWidth_setWidth_of_le _ hle, BitVec.setWidth_eq] using h'
  | .float _, _, a, b, h => congrArg Prod.fst h
  | .pair a b, ht, p₁, p₂, h => by
    simp only [LegalTarget.supportsTy, Bool.and_eq_true] at ht
    by_cases hp : target.keepsPacked (.pair a b) = true
    · rw [encodeVal_pair_packed target hp p₁, encodeVal_pair_packed target hp p₂] at h
      exact congrArg Prod.fst (cast_inj (congrArg (Tup Val) (by simp [LegalTarget.legalTys, hp])) h)
    · have hf := Bool.eq_false_iff.mpr hp
      rw [encodeVal_pair_split target hf p₁, encodeVal_pair_split target hf p₂] at h
      have h' := cast_inj (congrArg (Tup Val) (by simp [LegalTarget.legalTys, hf])) h
      have hsp := congrArg tupSplit h'
      simp only [tupSplit_tupAppend, Prod.mk.injEq] at hsp
      exact Prod.ext (encodeVal_inj target ht.1 hsp.1) (encodeVal_inj target ht.2 hsp.2)

theorem tupAppend_inj {α : Type} {f : α → Type} :
    {as bs : List α} → {x₁ x₂ : Tup f as} → {y₁ y₂ : Tup f bs} →
    tupAppend x₁ y₁ = tupAppend x₂ y₂ → x₁ = x₂ ∧ y₁ = y₂
  | [], _, (), (), _, _, h => ⟨rfl, h⟩
  | _ :: _, _, (_, _), (_, _), _, _, h => by
    have h1 : _ = _ := congrArg Prod.fst h
    have ih := tupAppend_inj (congrArg Prod.snd h)
    exact ⟨Prod.ext h1 ih.1, ih.2⟩

theorem encodeTup_inj (target : LegalTarget) :
    ∀ {ts : List Ty}, ts.all target.supportsTy = true → Function.Injective (encodeTup target ts)
  | [], _, (), (), _ => rfl
  | _ :: _, ht, (_, _), (_, _), h => by
    simp only [List.all_cons, Bool.and_eq_true] at ht
    simp only [encodeTup] at h
    obtain ⟨h1, h2⟩ := tupAppend_inj h
    exact Prod.ext (encodeVal_inj target ht.1 h1) (encodeTup_inj target ht.2 h2)

private theorem encodeTup_one_of_eq {t : Ty} {l : List Ty} (hl : l = [t])
    (heq : l ++ [] = [t]) (v : Val t) (z : Tup Val l)
    (hz : z = cast (congrArg (Tup Val) hl.symm) (show Tup Val [t] from (v, ()))) :
    tupAppend z () = cast (congrArg (Tup Val) heq.symm) (show Tup Val [t] from (v, ())) := by
  subst hl; rw [hz]; rfl

theorem encodeTup_singleton_eq_cast (target : LegalTarget) {t : Ty} (ht : target.isLegalTy t = true)
    (heq : target.legalSig [t] = [t]) (v : Val t) :
    encodeTup target [t] (v, ()) = cast (congrArg (Tup Val) heq.symm) (show Tup Val [t] from (v, ())) :=
  encodeTup_one_of_eq (legalTys_eq_singleton_of_isLegalTy target ht) heq v (encodeVal target t v)
    (encodeVal_self target ht v)

theorem legalPost_of_isLegal (target : LegalTarget) {t : Ty} (ht : target.isLegalTy t = true)
    (Q : Post [t]) (y : Val t) (m : Mem 64)
    (heq : target.legalSig [t] = [t] := by
      simp [LegalTarget.legalSig, legalTys_eq_singleton_of_isLegalTy target ht]) :
    legalPost target Q (cast (congrArg (Tup Val) heq.symm) (show Tup Val [t] from (y, ()))) m ↔
      Q (y, ()) m := by
  have h1 := encodeTup_singleton_eq_cast target ht heq
  constructor
  · rintro ⟨⟨x, ⟨⟩⟩, hx, hq⟩
    rw [h1 x] at hx
    have hx' := cast_inj (congrArg (Tup Val) heq.symm) hx
    have hxy : x = y := congrArg Prod.fst hx'
    subst hxy; exact hq
  · intro hq
    exact ⟨(y, ()), h1 y, hq⟩

/-! ### Value and label relations for `legalExpr_wp` -/

/-- Value context invariant during `legalExpr_wp`. -/
def CGoodWp (target : LegalTarget) (G : Ctx Val (LVar target Val)) : Prop :=
  ∀ t v lv, ⟨t, v, lv⟩ ∈ G → valsTup lv = encodeVal target t v

/-- Label context invariant during `legalExpr_wp`. -/
def DGoodWp (target : LegalTarget) (D : Ctx Cont (LLab target Cont)) : Prop :=
  ∀ ts j₁ j₂, ⟨ts, j₁, j₂⟩ ∈ D → ∀ xs m, j₁ xs m → j₂ (encodeTup target ts xs) m

theorem CGoodWp.weaken {target : LegalTarget} {G G' : Ctx Val (LVar target Val)}
    (hG : ∀ p ∈ G', p ∈ G) (hc : CGoodWp target G) : CGoodWp target G' :=
  fun t v lv hm => hc t v lv (hG _ hm)

theorem valsTup_legalArg (target : LegalTarget) {G : Ctx Val (LVar target Val)} (hc : CGoodWp target G)
    {t : Ty} {a : Arg Val t} {la : Arg (LVar target Val) t} (ha : ArgRel G t a la) :
    valsTup (legalArg target la) = encodeVal target t a.val := by
  cases ha with
  | var hm => exact hc _ _ _ hm
  | imm c => simp [legalArg, Arg.val]

theorem valsTup_joinArgs (target : LegalTarget) {G : Ctx Val (LVar target Val)} (hc : CGoodWp target G) :
    {ts : List Ty} → {as : Tup (Arg Val) ts} → {las : Tup (Arg (LVar target Val)) ts} →
    TRel (ArgRel G) as las → valsTup (joinArgs target las) = encodeTup target ts (valsTup as)
  | [], (), (), .nil => rfl
  | _ :: _, (_, _), (_, _), .cons ha has => by
    dsimp only [joinArgs, encodeTup, LegalTarget.legalSig]
    rw [valsTup_tupAppend, valsTup_legalArg target hc ha, valsTup_joinArgs target hc has,
      valsTup_cons]

theorem CGoodWp.pushTRel (target : LegalTarget) {G : Ctx Val (LVar target Val)} (hc : CGoodWp target G) :
    {ts : List Ty} → {xs : Tup Val ts} → {lxs : Tup (LVar target Val) ts} →
    TRel (fun t x lv => valsTup lv = encodeVal target t x) xs lxs →
    CGoodWp target (Tup.zip xs lxs ++ G)
  | [], (), (), .nil, _, _, _, hm => hc _ _ _ hm
  | _ :: _, (_, _), (_, _), .cons hx hxs, t, v, lv, hm => by
    simp only [Tup.zip, List.cons_append] at hm
    rcases List.mem_cons.1 hm with hhead | htail
    · cases hhead; exact hx
    · exact CGoodWp.pushTRel target hc hxs t v lv htail

theorem CGoodWp.pushSplit (target : LegalTarget) {G : Ctx Val (LVar target Val)} (hc : CGoodWp target G) :
    (ts : List Ty) → (xs : Tup Val ts) →
    CGoodWp target (Tup.zip xs (splitParams target ts (encodeTup target ts xs)) ++ G)
  | [], (), _, _, _, hm => hc _ _ _ hm
  | _ :: us, (x, xs), _, _, _, hm => by
    simp only [encodeTup, splitParams, tupSplit_tupAppend, Tup.zip, List.cons_append] at hm
    rcases List.mem_cons.1 hm with hhead | htail
    · cases hhead; simp [varsTup_valsTup]
    · exact CGoodWp.pushSplit target hc us xs _ _ _ htail

/-- Lift target continuations into source continuations via `encodeTup`. -/
def unlegalTupCont (target : LegalTarget) :
    {sig : List (List Ty)} → Tup Cont (sig.map target.legalSig) → Tup Cont sig
  | [], () => ()
  | ts :: _, (j, js) => (fun xs m => j (encodeTup target ts xs) m, unlegalTupCont target js)

theorem unlegalTupCont_get (target : LegalTarget) :
    {sig : List (List Ty)} → (Js : Tup Cont (sig.map target.legalSig)) →
    {ts : List Ty} → (i : Member ts sig) → (xs : Tup Val ts) → (m : Mem 64) →
    (unlegalTupCont target Js).get i xs m = (Js.get (Member.map target.legalSig i)) (encodeTup target ts xs) m
  | _ :: _, (_, _), _, .here, _, _ => rfl
  | _ :: _, (_, Js), _, .there i, xs, m => unlegalTupCont_get target Js i xs m

theorem DGoodWp.pushUnlegal (target : LegalTarget) {D : Ctx Cont (LLab target Cont)} (hd : DGoodWp target D) :
    {sig : List (List Ty)} → (Js : Tup Cont (sig.map target.legalSig)) →
    DGoodWp target (Tup.zip (unlegalTupCont target Js) (tupLiftMap target.legalSig Cont Js) ++ D)
  | [], (), _, _, _, hm, xs, m, hj => hd _ _ _ hm xs m hj
  | _ :: _, (_, js), _, _, _, hm, xs, m, hj => by
    simp only [unlegalTupCont, tupLiftMap, Tup.zip, List.cons_append] at hm
    rcases List.mem_cons.1 hm with hhead | htail
    · cases hhead; exact hj
    · exact DGoodWp.pushUnlegal target hd js _ _ _ htail xs m hj

theorem legalBlocks_get (target : LegalTarget) {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} :
    {sig : List (List Ty)} → (bs : Blocks (LVar target V) (LLab target L) rs sig) →
    {ts : List Ty} → (i : Member ts sig) → (xs : Tup V (target.legalSig ts)) →
    (legalBlocks target bs).get (Member.map target.legalSig i) xs =
      legalExpr target (bs.get i (splitParams target ts xs))
  | _ :: _, .cons _ _, _, .here, _ => rfl
  | _ :: _, .cons _ bs, _, .there i, xs => legalBlocks_get target bs i xs

theorem toTBlocks_get (target : LegalTarget) {rs : List Ty} :
    {sig : List (List Ty)} → (bs : Blocks K KL rs sig) →
    {ts : List Ty} → (i : Member ts sig) → (nv nl : Nat) →
    (toTBlocks bs nv nl).supportsSource target = true →
    ts.all target.supportsTy = true ∧
      (toTFlat (bs.get i (Tup.levels ts nv)) (nv + ts.length) nl).supportsSource target = true
  | _ :: _, .cons _ _, _, .here, _, _, h => by
    simp only [toTBlocks, TBlocks.supportsSource, Bool.and_eq_true] at h
    exact ⟨h.1.1, h.1.2⟩
  | _ :: _, .cons _ bs, _, .there i, nv, nl, h => by
    simp only [toTBlocks, TBlocks.supportsSource, Bool.and_eq_true] at h
    exact toTBlocks_get target bs i nv nl h.2

/-! ### Bridge helper `_wp` theorems (`unpack*` / `pack*` / `splitLegalToLeaves`) -/

private theorem unpackToLeaves_wp (target : LegalTarget) {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} :
    ∀ (t : Ty), target.supportsTy t = true → (a : Arg Val t) →
      {k : Tup (Arg Val) (target.leafTys t) → Expr Val Cont rs} → {m : Mem 64} →
      (∀ fx, valsTup fx = leafVals target t a.val → wp Γ Q X (k fx) m) →
      wp Γ Q X (unpackToLeaves target t a k) m
  | .bool, _, a, k, _, hk => hk (a, ()) rfl
  | .bits n, ht, a, k, _, hk => by
    have hnw : n ≤ target.widenWidth n := le_widenWidth_of_supports ht
    dsimp only [unpackToLeaves]
    split
    · next heq =>
      refine hk _ ?_
      dsimp only [LegalTarget.leafTys]
      rw [valsTup_single, val_castArgBits, leafVals, cast_eq_setWidth heq]
    · simp only [wp, Op.wp, OpCode.wp]
      exact ⟨hnw, hk _ rfl⟩
  | .float _, _, a, k, _, hk => hk (a, ()) rfl
  | .pair a b, ht, p, k, m, hk => by
    simp only [LegalTarget.supportsTy, Bool.and_eq_true] at ht
    cases p with
    | imm c =>
      dsimp only [unpackToLeaves]
      exact hk (leafImm target (.pair a b) c) (by rw [valsTup_leafImm]; rfl)
    | var v =>
      dsimp only [unpackToLeaves, wp, Op.wp, OpCode.wp]
      exact unpackToLeaves_wp target a ht.1 (.var v.1) (fun fx1 h1 =>
        unpackToLeaves_wp target b ht.2 (.var v.2) (fun fx2 h2 =>
          hk (tupAppend fx1 fx2) (by
            dsimp only [LegalTarget.leafTys]
            rw [valsTup_tupAppend, h1, h2]
            rfl)))

private theorem unpackToLegal_wp (target : LegalTarget) {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} :
    ∀ (t : Ty), target.supportsTy t = true → (a : Arg Val t) →
      {k : Tup (Arg Val) (target.legalTys t) → Expr Val Cont rs} → {m : Mem 64} →
      (∀ fx, valsTup fx = encodeVal target t a.val → wp Γ Q X (k fx) m) →
      wp Γ Q X (unpackToLegal target t a k) m
  | .bool, _, a, k, _, hk => hk (a, ()) rfl
  | .bits n, ht, a, k, _, hk => by
    have hnw : n ≤ target.widenWidth n := le_widenWidth_of_supports ht
    dsimp only [unpackToLegal]
    split
    · next heq =>
      refine hk _ ?_
      dsimp only [LegalTarget.legalTys]
      rw [valsTup_single, val_castArgBits, encodeVal, cast_eq_setWidth heq]
    · simp only [wp, Op.wp, OpCode.wp]
      exact ⟨hnw, hk _ rfl⟩
  | .float _, _, a, k, _, hk => hk (a, ()) rfl
  | .pair a b, ht, p, k, m, hk => by
    dsimp only [unpackToLegal]
    split
    · next hp =>
      exact hk (tupToPacked hp (p, ())) (valsTup_tupToPacked_encode target hp rfl)
    · next hp =>
      have hf := Bool.eq_false_iff.mpr hp
      simp only [LegalTarget.supportsTy, Bool.and_eq_true] at ht
      cases p with
      | imm c => exact hk (encodeImm target (.pair a b) c) (by rw [valsTup_encodeImm]; rfl)
      | var v =>
        dsimp only [wp, Op.wp, OpCode.wp]
        exact unpackToLegal_wp target a ht.1 (.var v.1) (fun fx1 h1 =>
          unpackToLegal_wp target b ht.2 (.var v.2) (fun fx2 h2 =>
            hk (tupToSplit hf (tupAppend fx1 fx2))
              (valsTup_tupToSplit_encode target hf (by rw [valsTup_tupAppend, h1, h2]; rfl))))

private theorem packFromLegal_wp (target : LegalTarget) {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} :
    ∀ (t : Ty), target.supportsTy t = true → (la : Tup (Arg Val) (target.legalTys t)) →
      (x : Val t) → valsTup la = encodeVal target t x →
      {k : Arg Val t → Expr Val Cont rs} → {m : Mem 64} →
      (∀ r, r.val = x → wp Γ Q X (k r) m) →
      wp Γ Q X (packFromLegal target t la k) m
  | .bool, _, (a, ()), x, hla, k, _, hk => hk a (congrArg Prod.fst hla)
  | .bits n, ht, (a, ()), x, hla, k, _, hk => by
    have hnw : n ≤ target.widenWidth n := le_widenWidth_of_supports ht
    have ha : a.val = x.setWidth (target.widenWidth n) := congrArg Prod.fst hla
    dsimp only [packFromLegal]
    split
    · next heq =>
      refine hk _ ?_
      rw [val_castArgBits, ha, cast_eq_setWidth heq.symm, BitVec.setWidth_setWidth_of_le _ hnw, BitVec.setWidth_eq]
    · simp only [wp, Op.wp, OpCode.wp]
      refine ⟨hnw, hk _ ?_⟩
      change (a.val).setWidth n = x
      rw [ha, BitVec.setWidth_setWidth_of_le _ hnw, BitVec.setWidth_eq]
  | .float _, _, (a, ()), x, hla, k, _, hk => hk a (congrArg Prod.fst hla)
  | .pair a b, ht, xs, p, hxs, k, m, hk => by
    dsimp only [packFromLegal]
    split
    · next hp =>
      exact hk _ (congrArg Prod.fst (valsTup_packedToTup_encode target hp hxs))
    · next hp =>
      have hf := Bool.eq_false_iff.mpr hp
      simp only [LegalTarget.supportsTy, Bool.and_eq_true] at ht
      have hsp := valsTup_splitToTup_encode target hf hxs
      have h12 := congrArg tupSplit hsp
      simp only [tupSplit_valsTup, tupSplit_tupAppend] at h12
      exact packFromLegal_wp target a ht.1 (tupSplit (splitToTup hf xs)).1 p.1 (congrArg Prod.fst h12)
        (fun va hva => packFromLegal_wp target b ht.2 (tupSplit (splitToTup hf xs)).2 p.2
          (congrArg Prod.snd h12) (fun vb hvb =>
            by
              dsimp only [wp, Op.wp, OpCode.wp]
              exact hk _ (Prod.ext hva hvb)))

private theorem splitLegalToLeaves_wp (target : LegalTarget) {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} :
    ∀ (t : Ty), target.supportsTy t = true → (xs : Tup (Arg Val) (target.legalTys t)) →
      (x : Val t) → valsTup xs = encodeVal target t x →
      {k : Tup (Arg Val) (target.leafTys t) → Expr Val Cont rs} → {m : Mem 64} →
      (∀ fx, valsTup fx = leafVals target t x → wp Γ Q X (k fx) m) →
      wp Γ Q X (splitLegalToLeaves target t xs k) m
  | .bool, _, xs, _, hxs, k, _, hk => hk xs hxs
  | .bits _, _, xs, _, hxs, k, _, hk => hk xs hxs
  | .float _, _, xs, _, hxs, k, _, hk => hk xs hxs
  | .pair a b, ht, xs, p, hxs, k, m, hk => by
    simp only [LegalTarget.supportsTy, Bool.and_eq_true] at ht
    dsimp only [splitLegalToLeaves]
    split
    · next hp =>
      have h' : (packedToTup hp xs).1.val = p := congrArg Prod.fst (valsTup_packedToTup_encode target hp hxs)
      exact unpackToLeaves_wp target (.pair a b) (by simp [LegalTarget.supportsTy, ht]) _
        (fun fx hfx => hk fx (by rw [hfx, h']))
    · next hp =>
      have hf := Bool.eq_false_iff.mpr hp
      have hsp := valsTup_splitToTup_encode target hf hxs
      have h12 := congrArg tupSplit hsp
      simp only [tupSplit_valsTup, tupSplit_tupAppend] at h12
      exact splitLegalToLeaves_wp target a ht.1 _ p.1 (congrArg Prod.fst h12) (fun fa hfa =>
        splitLegalToLeaves_wp target b ht.2 _ p.2 (congrArg Prod.snd h12) (fun fb hfb =>
          hk (tupAppend fa fb) (by
            dsimp only [LegalTarget.leafTys]
            rw [valsTup_tupAppend, hfa, hfb]
            rfl)))

private theorem packLeavesToLegal_wp (target : LegalTarget) {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} :
    ∀ (t : Ty), target.supportsTy t = true → (fx : Tup (Arg Val) (target.leafTys t)) →
      (x : Val t) → valsTup fx = leafVals target t x →
      {k : Tup (Arg Val) (target.legalTys t) → Expr Val Cont rs} → {m : Mem 64} →
      (∀ res, valsTup res = encodeVal target t x → wp Γ Q X (k res) m) →
      wp Γ Q X (packLeavesToLegal target t fx k) m
  | .bool, _, fx, _, hfx, k, _, hk => hk fx hfx
  | .bits _, _, fx, _, hfx, k, _, hk => hk fx hfx
  | .float _, _, fx, _, hfx, k, _, hk => hk fx hfx
  | .pair a b, ht, fx, p, hfx, k, m, hk => by
    simp only [LegalTarget.supportsTy, Bool.and_eq_true] at ht
    dsimp only [LegalTarget.leafTys] at fx hfx
    dsimp only [packLeavesToLegal]
    have h12 := congrArg (tupSplit (as := target.leafTys a) (bs := target.leafTys b)) hfx
    rw [leafVals_pair, tupSplit_tupAppend, tupSplit_valsTup] at h12
    have h1 : valsTup (tupSplit (as := target.leafTys a) (bs := target.leafTys b) fx).1 = leafVals target a p.1 :=
      congrArg Prod.fst h12
    have h2 : valsTup (tupSplit (as := target.leafTys a) (bs := target.leafTys b) fx).2 = leafVals target b p.2 :=
      congrArg Prod.snd h12
    split
    · next hp =>
      exact packLeavesToLegal_wp target a ht.1 _ p.1 h1 (fun la hla =>
        packLeavesToLegal_wp target b ht.2 _ p.2 h2 (fun lb hlb =>
          packFromLegal_wp target a ht.1 la p.1 hla (fun va hva =>
            packFromLegal_wp target b ht.2 lb p.2 hlb (fun vb hvb =>
              by
                dsimp only [wp, Op.wp, OpCode.wp]
                exact hk _ (valsTup_tupToPacked_encode target hp
                  (by rw [valsTup_single]; exact congrArg (·, ()) (Prod.ext hva hvb)))))))
    · next hp =>
      have hf := Bool.eq_false_iff.mpr hp
      exact packLeavesToLegal_wp target a ht.1 _ p.1 h1 (fun la hla =>
        packLeavesToLegal_wp target b ht.2 _ p.2 h2 (fun lb hlb =>
          hk _ (valsTup_tupToSplit_encode target hf
            (by rw [valsTup_tupAppend, hla, hlb]))))

/-! ### Scalar BitVec widening, masking, sign-extension, ternary logic, and bool-op `_wp` helpers -/

private theorem lowMask_and {n w : Nat} (hnw : n ≤ w) (x : BitVec w) :
    x &&& lowMask n w = (x.setWidth n).setWidth w := by
  ext i hi
  simp only [← BitVec.getLsbD_eq_getElem, lowMask, BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_allOnes, BitVec.getLsbD_setWidth]
  by_cases hin : i < n
  · have hiw : w - n + i < w := by omega
    simp [hi, hin, hiw]
  · have hiw : ¬ (w - n + i < w) := by omega
    simp [hi, hin, hiw]

private theorem bitVec0_eq_zero (x : BitVec 0) : x = 0#0 := Subsingleton.elim _ _

private theorem setWidth_zero_setWidth {w : Nat} (x : BitVec w) :
    (x.setWidth 0).setWidth w = 0#w := by
  rw [bitVec0_eq_zero (x.setWidth 0)]; rfl

private theorem emitMaskToN_wp {target_Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {n w : Nat} (hnw : n ≤ w) {x : Arg Val (.bits w)} {v : BitVec w} (hx : x.val = v)
    {k : Arg Val (.bits w) → Expr Val Cont rs} {m : Mem 64}
    (hk : ∀ r, r.val = (v.setWidth n).setWidth w → wp target_Γ Q X (k r) m) :
    wp target_Γ Q X (emitMaskToN n w x k) m := by
  dsimp only [emitMaskToN]
  by_cases hn0 : n = 0
  · subst hn0
    simp only [beq_self_eq_true, ↓reduceIte]
    exact hk _ (setWidth_zero_setWidth v).symm
  · have hn0' : (n == 0) = false := beq_false_of_ne hn0
    simp only [hn0', Bool.false_eq_true, ↓reduceIte]
    by_cases hwn : w ≤ n
    · have heq : n = w := Nat.le_antisymm hnw hwn
      subst heq
      simp only [hwn, ↓reduceIte]
      exact hk x (by rw [hx, BitVec.setWidth_eq, BitVec.setWidth_eq])
    · simp only [hwn, ↓reduceIte, wp, Op.wp, OpCode.wp]
      exact hk _ (by change x.val &&& lowMask n w = _; rw [hx, lowMask_and hnw])

private theorem signExtend_eq_shl_ashr {n w : Nat} (hn0 : 0 < n) (hnw : n < w) (a : BitVec n) :
    (a.setWidth w <<< (w - n)).sshiftRight (w - n) = a.signExtend w := by
  ext i hi
  simp only [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_sshiftRight, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_signExtend, hi]
  have hmsb : ((a.setWidth w) <<< (w - n)).msb = a.msb := by
    rw [BitVec.msb_eq_getLsbD_last, BitVec.msb_eq_getLsbD_last]
    simp only [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
    have hd1 : decide (w - 1 < w) = true := decide_eq_true (by omega)
    have hd2 : decide (w - 1 < w - n) = false := decide_eq_false (by omega)
    have hd3 : decide (n - 1 < w) = true := decide_eq_true (by omega)
    have hcancel : w - 1 - (w - n) = n - 1 := by omega
    simp only [hd1, hd2, hd3, hcancel, Bool.not_false, Bool.true_and]
  by_cases hin : i < n
  · have hltw : w - n + i < w := by omega
    have hnot2 : ¬ (w ≤ i) := by omega
    have hge : ¬ (w - n + i < w - n) := by omega
    have hcancel : w - n + i - (w - n) = i := by omega
    simp [hltw, hnot2, hge, hcancel, hin, hi]
  · have hge : ¬ (w - n + i < w) := by omega
    have hnot2 : ¬ (w ≤ i) := by omega
    simp [hge, hin, hmsb, hnot2]

private theorem emitSextToW_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {n w : Nat} (hn0 : 0 < n) (hnw : n ≤ w) {x : Arg Val (.bits w)} {a : BitVec n}
    (hx : x.val = a.setWidth w) {k : Arg Val (.bits w) → Expr Val Cont rs} {m : Mem 64}
    (hk : ∀ r, r.val = a.signExtend w → wp Γ Q X (k r) m) :
    wp Γ Q X (emitSextToW n w x k) m := by
  dsimp only [emitSextToW]
  by_cases hle : w ≤ n
  · have heq : n = w := Nat.le_antisymm hnw hle
    subst heq
    have hcond : (n == 0 || decide (n ≤ n)) = true := by
      simp only [Nat.le_refl, decide_true, Bool.or_true]
    simp only [hcond]
    exact hk x (by rw [hx, BitVec.setWidth_eq, BitVec.signExtend_eq])
  · have hnwl : n < w := by omega
    have hn0f : (n == 0) = false := beq_false_of_ne (by omega)
    have hcond : (n == 0 || decide (w ≤ n)) = false := by
      simp only [hn0f, Bool.false_or, decide_eq_false hle]
    simp only [hcond, Bool.false_eq_true, ↓reduceIte]
    dsimp only [wp, Op.wp, OpCode.wp, vals, lift2, Arg.val_imm]
    have hpow : w < 2 ^ w := @Nat.lt_pow_self w 2 (by decide)
    have hsh_mod : (BitVec.ofNat w (w - n)).toNat % w = w - n := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans (by omega) hpow), Nat.mod_eq_of_lt (by omega)]
    refine hk _ ?_
    change (x.val <<< ((BitVec.ofNat w (w - n)).toNat % w)).sshiftRight
      ((BitVec.ofNat w (w - n)).toNat % w) = a.signExtend w
    rw [hx, hsh_mod]
    exact signExtend_eq_shl_ashr hn0 hnwl a

private theorem emitCountMod_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {n w : Nat} (hn0 : 0 < n) (hnw : n < w) {c : Arg Val (.bits w)} {b : BitVec n}
    (hc : c.val = b.setWidth w) {k : Arg Val (.bits w) → Expr Val Cont rs} {m : Mem 64}
    (hk : ∀ r, r.val = BitVec.ofNat w (b.toNat % n) → wp Γ Q X (k r) m) :
    wp Γ Q X (emitCountMod n w c k) m := by
  have h2nw : 2 ^ n < 2 ^ w := Nat.pow_lt_pow_right (by omega) hnw
  have hcn : c.val.toNat = b.toNat := by
    rw [hc, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans b.isLt h2nw)]
  cases c with
  | imm cb =>
    dsimp only [emitCountMod]
    exact hk _ (by dsimp only [Arg.val] at hcn ⊢; rw [hcn])
  | var _ =>
    dsimp only [emitCountMod, wp, Op.wp, OpCode.wp, vals]
    have hpow : w < 2 ^ w := @Nat.lt_pow_self w 2 (by decide)
    have hn_lt : n < 2 ^ w := Nat.lt_trans hnw hpow
    have hof_nat : (BitVec.ofNat w n).toNat = n := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn_lt]
    refine ⟨?_, hk _ ?_⟩
    · intro h0
      dsimp only [Arg.val_imm] at h0
      have h0' := congrArg BitVec.toNat h0
      rw [hof_nat] at h0'
      exact Nat.ne_of_gt hn0 h0'
    · apply BitVec.eq_of_toNat_eq
      dsimp only [Arg.val] at hcn ⊢
      rw [BitVec.toNat_umod, hcn, hof_nat, BitVec.toNat_ofNat]
      symm
      exact Nat.mod_eq_of_lt (Nat.lt_trans (Nat.lt_trans (Nat.mod_lt _ hn0) hnw) hpow)

private theorem boolCmp_spec (o : CmpOp) (a b : Bool) :
    (match o with
     | .eq => !(a ^^ b)
     | .ne => a ^^ b
     | .ult | .sgt => !a && b
     | .ule | .sge => !a || b
     | .ugt | .slt => a && !b
     | .uge | .sle => a || !b) = o.evalBool a b := by
  cases o <;> cases a <;> cases b <;> rfl

private theorem emitBoolCmp_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (o : CmpOp) (a b : Arg Val .bool) {k : Arg Val .bool → Expr Val Cont rs} {m : Mem 64}
    (hk : ∀ r, r.val = o.evalBool a.val b.val → wp Γ Q X (k r) m) :
    wp Γ Q X (emitBoolCmp o a b k) m := by
  have hsp := boolCmp_spec o a.val b.val
  cases o <;> dsimp only [emitBoolCmp, wp, Op.wp, OpCode.wp, vals, lift1, lift2] at * <;>
    exact hk _ hsp

private theorem emitBoolSelect_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (c a b : Arg Val .bool) {k : Arg Val .bool → Expr Val Cont rs} {m : Mem 64}
    (hk : ∀ r, r.val = (if c.val then a.val else b.val) → wp Γ Q X (k r) m) :
    wp Γ Q X (emitBoolSelect c a b k) m := by
  dsimp only [emitBoolSelect, wp, Op.wp, OpCode.wp, vals, lift1, lift2]
  exact hk _ (by cases c.val <;> cases a.val <;> cases b.val <;> rfl)

private theorem list_drop_range8 :
    ∀ idx < 8, (List.range 8).drop idx = idx :: (List.range 8).drop (idx + 1)
  | 0, _ => rfl | 1, _ => rfl | 2, _ => rfl | 3, _ => rfl
  | 4, _ => rfl | 5, _ => rfl | 6, _ => rfl | 7, _ => rfl

private theorem ite_arg_val {t : Ty}
    (c : Prop) [Decidable c] (a b : Arg Val t) :
    (if c then a else b).val = if c then a.val else b.val := by
  by_cases h : c
  · rw [ite_eq_left h, ite_eq_left h]
  · rw [ite_eq_right h, ite_eq_right h]

private theorem emitTernlogBits_go_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {w : Nat}
    (a b c na nb nc : Arg Val (.bits w))
    (hna : na.val = ~~~a.val) (hnb : nb.val = ~~~b.val) (hnc : nc.val = ~~~c.val)
    (imm : BitVec 8) :
    ∀ (d idx : Nat), idx + d = 8 →
      ∀ (acc : Option (Arg Val (.bits w)))
        {k : Arg Val (.bits w) → Expr Val Cont rs} {m : Mem 64},
        (∀ r, r.val =
          ((List.range 8).drop idx).foldl (fun cur i =>
            if imm.getLsbD i then
              cur ||| ((if i / 4 % 2 == 1 then a.val else na.val) &&&
                       (if i / 2 % 2 == 1 then b.val else nb.val) &&&
                       (if i % 2 == 1 then c.val else nc.val))
            else cur) (match acc with | some v => v.val | none => 0#w) →
          wp Γ Q X (k r) m) →
        wp Γ Q X (emitTernlogBits.go w imm k idx acc a b c na nb nc) m
  | 0, idx, hd, acc, k, _, hk => by
    have hge : idx ≥ 8 := by omega
    have hdrop : (List.range 8).drop idx = [] := List.drop_eq_nil_of_le (by simp; omega)
    rw [emitTernlogBits.go.eq_def, ite_eq_left hge]
    cases acc with
    | none => exact hk (.imm 0#w) (by simp [hdrop])
    | some v => exact hk v (by simp [hdrop])
  | d + 1, idx, hd, acc, k, m, hk => by
    have hlt : ¬ (idx ≥ 8) := by omega
    have hdrop := list_drop_range8 idx (by omega)
    rw [emitTernlogBits.go.eq_def, ite_eq_right hlt]
    by_cases himm : imm.getLsbD idx = true
    · rw [ite_eq_left himm]
      dsimp only [wp, Op.wp, OpCode.wp, vals, lift2]
      cases acc with
      | none =>
        refine emitTernlogBits_go_wp a b c na nb nc hna hnb hnc imm d (idx + 1) (by omega)
          (some (.var _)) fun r hr => hk r ?_
        rw [hr, hdrop]
        simp [himm, lift2, ite_arg_val]
      | some prev =>
        dsimp only [wp, Op.wp, OpCode.wp, vals, lift2]
        refine emitTernlogBits_go_wp a b c na nb nc hna hnb hnc imm d (idx + 1) (by omega)
          (some (.var _)) fun r hr => hk r ?_
        rw [hr, hdrop]
        simp [himm, lift2, ite_arg_val]
    · rw [ite_eq_right himm]
      refine emitTernlogBits_go_wp a b c na nb nc hna hnb hnc imm d (idx + 1) (by omega) acc
        fun r hr => hk r ?_
      rw [hr, hdrop]
      simp [himm]

private theorem ternaryLogic_allOnes {w : Nat} (a b c : BitVec w) :
    ternaryLogic a b c 0xff#8 = BitVec.allOnes w := by
  ext i hi
  rw [show (0xff#8 : BitVec 8) = BitVec.allOnes 8 from rfl]
  simp only [← BitVec.getLsbD_eq_getElem, ternaryLogic, BitVec.getLsbD_allOnes, hi, decide_true]
  rw [show List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] from rfl]
  simp only [List.foldl_cons, List.foldl_nil]
  cases ha : a[i] <;> cases hb : b[i] <;> cases hc : c[i] <;>
    simp [hi, ha, hb, hc]

private theorem ternaryLogic_zero {w : Nat} (a b c : BitVec w) :
    ternaryLogic a b c 0#8 = 0#w := by
  simp [ternaryLogic, List.range_succ]

private theorem emitTernlogBits_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {w : Nat}
    (a b c : Arg Val (.bits w)) (imm : BitVec 8)
    {k : Arg Val (.bits w) → Expr Val Cont rs} {m : Mem 64}
    (hk : ∀ r, r.val = ternaryLogic a.val b.val c.val imm → wp Γ Q X (k r) m) :
    wp Γ Q X (emitTernlogBits w a b c imm k) m := by
  dsimp only [emitTernlogBits]
  by_cases h0 : (imm == 0#8) = true
  · rw [ite_eq_left h0]
    have himm : imm = 0#8 := beq_iff_eq.mp h0
    subst himm
    exact hk (.imm 0#w) (ternaryLogic_zero a.val b.val c.val).symm
  · rw [ite_eq_right h0]
    by_cases hff : (imm == 0xff#8) = true
    · rw [ite_eq_left hff]
      have himm : imm = 0xff#8 := beq_iff_eq.mp hff
      subst himm
      exact hk (.imm (BitVec.allOnes w)) (ternaryLogic_allOnes a.val b.val c.val).symm
    · rw [ite_eq_right hff]
      dsimp only [wp, Op.wp, OpCode.wp, vals, lift1]
      exact emitTernlogBits_go_wp a b c (.var _) (.var _) (.var _) rfl rfl rfl imm 8 0 rfl none
        fun r hr => hk r (by simpa [ternaryLogic] using hr)

private theorem emitTernlogBool_go_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (a b c na nb nc : Arg Val .bool)
    (hna : na.val = !a.val) (hnb : nb.val = !b.val) (hnc : nc.val = !c.val)
    (imm : BitVec 8) :
    ∀ (d idx : Nat), idx + d = 8 →
      ∀ (acc : Option (Arg Val .bool))
        {k : Arg Val .bool → Expr Val Cont rs} {m : Mem 64},
        (∀ r, r.val =
          ((List.range 8).drop idx).foldl (fun cur i =>
            if imm.getLsbD i then
              cur || ((if i / 4 % 2 == 1 then a.val else na.val) &&
                      (if i / 2 % 2 == 1 then b.val else nb.val) &&
                      (if i % 2 == 1 then c.val else nc.val))
            else cur) (match acc with | some v => v.val | none => false) →
          wp Γ Q X (k r) m) →
        wp Γ Q X (emitTernlogBool.go imm k idx acc a b c na nb nc) m
  | 0, idx, hd, acc, k, _, hk => by
    have hge : idx ≥ 8 := by omega
    have hdrop : (List.range 8).drop idx = [] := List.drop_eq_nil_of_le (by simp; omega)
    rw [emitTernlogBool.go.eq_def, ite_eq_left hge]
    cases acc with
    | none => exact hk (.imm false) (by simp [hdrop])
    | some v => exact hk v (by simp [hdrop])
  | d + 1, idx, hd, acc, k, m, hk => by
    have hlt : ¬ (idx ≥ 8) := by omega
    have hdrop := list_drop_range8 idx (by omega)
    rw [emitTernlogBool.go.eq_def, ite_eq_right hlt]
    by_cases himm : imm.getLsbD idx = true
    · rw [ite_eq_left himm]
      dsimp only [wp, Op.wp, OpCode.wp, vals, lift2]
      cases acc with
      | none =>
        refine emitTernlogBool_go_wp a b c na nb nc hna hnb hnc imm d (idx + 1) (by omega)
          (some (.var _)) fun r hr => hk r ?_
        rw [hr, hdrop]
        simp [himm, lift2, ite_arg_val]
      | some prev =>
        dsimp only [wp, Op.wp, OpCode.wp, vals, lift2]
        refine emitTernlogBool_go_wp a b c na nb nc hna hnb hnc imm d (idx + 1) (by omega)
          (some (.var _)) fun r hr => hk r ?_
        rw [hr, hdrop]
        simp [himm, lift2, ite_arg_val]
    · rw [ite_eq_right himm]
      refine emitTernlogBool_go_wp a b c na nb nc hna hnb hnc imm d (idx + 1) (by omega) acc
        fun r hr => hk r ?_
      rw [hr, hdrop]
      simp [himm]

private theorem emitTernlogBool_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (a b c : Arg Val .bool) (imm : BitVec 8)
    {k : Arg Val .bool → Expr Val Cont rs} {m : Mem 64}
    (hk : ∀ r, r.val = ternaryLogicBool a.val b.val c.val imm → wp Γ Q X (k r) m) :
    wp Γ Q X (emitTernlogBool a b c imm k) m := by
  dsimp only [emitTernlogBool]
  by_cases h0 : (imm == 0#8) = true
  · rw [ite_eq_left h0]
    have himm : imm = 0#8 := beq_iff_eq.mp h0
    subst himm
    exact hk (.imm false) (by simp [ternaryLogicBool])
  · rw [ite_eq_right h0]
    by_cases hff : (imm == 0xff#8) = true
    · rw [ite_eq_left hff]
      have himm : imm = 0xff#8 := beq_iff_eq.mp hff
      subst himm
      exact hk (.imm true) (by
        have h : ∀ va vb vc : Bool, ternaryLogicBool va vb vc 0xff#8 = true := by decide
        exact (h a.val b.val c.val).symm)
    · rw [ite_eq_right hff]
      dsimp only [wp, Op.wp, OpCode.wp, vals, lift1]
      refine emitTernlogBool_go_wp a b c (.var _) (.var _) (.var _) rfl rfl rfl imm 8 0 rfl none
        fun r hr => hk r ?_
      have hfold : ∀ (va vb vc : Bool) (imm : BitVec 8),
          ([0, 1, 2, 3, 4, 5, 6, 7].foldl (fun cur i =>
            if imm.getLsbD i then
              cur || ((if i / 4 % 2 == 1 then va else !va) &&
                      (if i / 2 % 2 == 1 then vb else !vb) &&
                      (if i % 2 == 1 then vc else !vc))
            else cur) false) = ternaryLogicBool va vb vc imm := by
        intro va vb vc imm
        cases va <;> cases vb <;> cases vc <;> simp [ternaryLogicBool]
      rw [hr, show (List.range 8).drop 0 = [0, 1, 2, 3, 4, 5, 6, 7] from rfl]
      exact hfold a.val b.val c.val imm

/-! ### BitVec widening arithmetic, shift, bit-manipulation, comparison, and conversion lemmas -/

private theorem toNat_setWidth_of_le {n w : Nat} (hnw : n ≤ w) (a : BitVec n) :
    (a.setWidth w).toNat = a.toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt]
  exact Nat.lt_of_lt_of_le a.isLt (Nat.pow_le_pow_right (by decide : 0 < 2) hnw)

private theorem setWidth_inj_of_le {n w : Nat} (hnw : n ≤ w) {a b : BitVec n}
    (h : a.setWidth w = b.setWidth w) : a = b := by
  apply BitVec.eq_of_toNat_eq
  rw [← toNat_setWidth_of_le hnw a, ← toNat_setWidth_of_le hnw b, h]

private theorem setWidth_setWidth_lowMask {n w : Nat} (hnw : n ≤ w) (x : BitVec w) :
    (x.setWidth n).setWidth w = x &&& lowMask n w :=
  (lowMask_and hnw x).symm

private theorem setWidth_add_of_le {n w : Nat} (hnw : n ≤ w) (a b : BitVec n) :
    (a.setWidth w + b.setWidth w) &&& lowMask n w = (a + b).setWidth w := by
  rw [lowMask_and hnw]
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_add,
    toNat_setWidth_of_le hnw a, toNat_setWidth_of_le hnw b]
  exact Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 hnw)

private theorem setWidth_mul_of_le {n w : Nat} (hnw : n ≤ w) (a b : BitVec n) :
    (a.setWidth w * b.setWidth w) &&& lowMask n w = (a * b).setWidth w := by
  rw [lowMask_and hnw]
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_mul, BitVec.toNat_mul,
    toNat_setWidth_of_le hnw a, toNat_setWidth_of_le hnw b]
  exact Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 hnw)

private theorem setWidth_sub_of_le {n w : Nat} (hnw : n ≤ w) (a b : BitVec n) :
    (a.setWidth w - b.setWidth w) &&& lowMask n w = (a - b).setWidth w := by
  rw [lowMask_and hnw]
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_sub,
    toNat_setWidth_of_le hnw a, toNat_setWidth_of_le hnw b]
  have hdvd : 2 ^ n ∣ 2 ^ w := Nat.pow_dvd_pow 2 hnw
  rcases hdvd with ⟨k, hk⟩
  have hkpos : 0 < k := Nat.pos_of_ne_zero fun hk0 => by
    rw [hk0, Nat.mul_zero] at hk
    exact Nat.ne_of_gt (Nat.two_pow_pos w) hk
  have ha : a.toNat < 2 ^ n := a.isLt
  have hb : b.toNat < 2 ^ n := b.isLt
  have hk1 : 2 ^ n * k = 2 ^ n * (k - 1) + 2 ^ n := by
    calc 2 ^ n * k = 2 ^ n * (k - 1 + 1) := by rw [Nat.sub_add_cancel hkpos]
      _ = 2 ^ n * (k - 1) + 2 ^ n := Nat.mul_add_one _ _
  have h1 : 2 ^ w - b.toNat + a.toNat = (k - 1) * 2 ^ n + (2 ^ n - b.toNat + a.toNat) := by
    rw [hk, hk1, Nat.mul_comm (2 ^ n) (k - 1)]
    omega
  rw [Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 hnw), h1, Nat.mul_comm (k - 1), Nat.mul_add_mod]

private theorem setWidth_neg_of_le {n w : Nat} (hnw : n ≤ w) (a : BitVec n) :
    (-(a.setWidth w)) &&& lowMask n w = (-a).setWidth w := by
  have hz : (0#n).setWidth w = 0#w := BitVec.setWidth_zero w n
  have hsub := setWidth_sub_of_le hnw 0#n a
  rw [hz] at hsub
  simpa using hsub

private theorem setWidth_and_of_le {n w : Nat} (a b : BitVec n) :
    a.setWidth w &&& b.setWidth w = (a &&& b).setWidth w := by
  ext i hi
  simp only [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_and, BitVec.getLsbD_setWidth, hi,
    decide_true, Bool.true_and]

private theorem setWidth_or_of_le {n w : Nat} (a b : BitVec n) :
    a.setWidth w ||| b.setWidth w = (a ||| b).setWidth w := by
  ext i hi
  simp only [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_or, BitVec.getLsbD_setWidth, hi,
    decide_true, Bool.true_and]

private theorem setWidth_xor_of_le {n w : Nat} (a b : BitVec n) :
    a.setWidth w ^^^ b.setWidth w = (a ^^^ b).setWidth w := by
  ext i hi
  simp only [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_xor, BitVec.getLsbD_setWidth, hi,
    decide_true, Bool.true_and]

private theorem setWidth_not_of_le {n w : Nat} (hnw : n ≤ w) (a : BitVec n) :
    (~~~(a.setWidth w)) &&& lowMask n w = (~~~a).setWidth w := by
  rw [lowMask_and hnw]
  congr 1
  ext i hi
  have hiw : i < w := Nat.lt_of_lt_of_le hi hnw
  simp only [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_setWidth, BitVec.getLsbD_not, hi, hiw,
    decide_true, Bool.true_and]

private theorem setWidth_shl_of_lt {n w : Nat} (hnw : n < w) (a : BitVec n) (s : Nat) :
    ((a.setWidth w) <<< s) &&& lowMask n w = (a <<< s).setWidth w := by
  rw [lowMask_and (Nat.le_of_lt hnw)]
  congr 1
  ext i hi
  have hiw : i < w := Nat.lt_trans hi hnw
  simp only [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_setWidth, BitVec.getLsbD_shiftLeft,
    hi, hiw, decide_true, Bool.true_and]
  have hlt : decide (i - s < w) = true := decide_eq_true (by omega)
  simp only [hlt, Bool.true_and]

private theorem setWidth_lshr_of_le {n w : Nat} (hnw : n ≤ w) (a : BitVec n) (s : Nat) :
    (a.setWidth w) >>> s = (a >>> s).setWidth w := by
  ext i hi
  simp only [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_setWidth, hi]
  by_cases his : s + i < n
  · have hisw : s + i < w := Nat.lt_of_lt_of_le his hnw
    simp [his, hisw]
  · have hfalse : a.getLsbD (s + i) = false := BitVec.getLsbD_of_ge a (s + i) (by omega)
    simp [hfalse]

private theorem msb_signExtend_of_pos_le {n w : Nat} (hn0 : 0 < n) (hnw : n ≤ w) (a : BitVec n) :
    (a.signExtend w).msb = a.msb := by
  rw [BitVec.msb_eq_getLsbD_last, BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_signExtend]
  have hw0 : w - 1 < w := by omega
  have hnot : ¬ (w - 1 < n) ∨ n = w := by omega
  rcases hnot with hge | rfl
  · simp [hw0, hge, BitVec.msb_eq_getLsbD_last]
  · simp [hw0]

private theorem setWidth_ashr_signExtend_of_lt {n w : Nat} (hn0 : 0 < n) (hnw : n < w)
    (a : BitVec n) (s : Nat) :
    ((a.signExtend w).sshiftRight s) &&& lowMask n w = (a.sshiftRight s).setWidth w := by
  rw [lowMask_and (Nat.le_of_lt hnw)]
  congr 1
  ext i hi
  simp only [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_setWidth, BitVec.getLsbD_sshiftRight,
    BitVec.getLsbD_signExtend, hi, decide_true, Bool.true_and]
  rw [msb_signExtend_of_pos_le hn0 (Nat.le_of_lt hnw) a]
  have hnw1 : decide (w ≤ i) = false := decide_eq_false (by omega)
  have hnw2 : decide (n ≤ i) = false := decide_eq_false (by omega)
  by_cases hsn : s + i < n
  · have hsw : s + i < w := Nat.lt_trans hsn hnw
    simp [hnw1, hnw2, hsn, hsw]
  · by_cases hsw : s + i < w <;> simp [hnw1, hnw2, hsn, hsw]

private theorem setWidth_rotl_of_lt {n w : Nat} (hn0 : 0 < n) (hnw : n < w)
    (a b : BitVec n) :
    let s := b.toNat % n
    (((a.setWidth w) <<< s) ||| ((a.setWidth w) >>> (n - s))) &&& lowMask n w =
      (a.rotateLeft (b.toNat % n)).setWidth w := by
  intro s
  have hsn : s < n := Nat.mod_lt _ hn0
  rw [lowMask_and (Nat.le_of_lt hnw)]
  congr 1
  ext i hi
  have hiw : i < w := Nat.lt_trans hi hnw
  simp only [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_setWidth, BitVec.getLsbD_or,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_rotateLeft,
    hi, hiw, decide_true, Bool.true_and]
  by_cases his : i < s
  · have h2 : n - s + i < n := by omega
    have h3 : n - s + i < w := Nat.lt_trans h2 hnw
    dsimp only [s] at his h3 ⊢
    simp [his, h3]
  · have hisn : i - s < n := by omega
    have hisw : i - s < w := Nat.lt_trans hisn hnw
    have hge : n ≤ n - s + i := by omega
    have hfalse : a.getLsbD (n - s + i) = false := BitVec.getLsbD_of_ge a (n - s + i) hge
    dsimp only [s] at his hisw hfalse ⊢
    simp [his, hisw, hfalse]

private theorem setWidth_rotr_of_lt {n w : Nat} (hn0 : 0 < n) (hnw : n < w)
    (a b : BitVec n) :
    let s := b.toNat % n
    (((a.setWidth w) >>> s) ||| ((a.setWidth w) <<< (n - s))) &&& lowMask n w =
      (a.rotateRight (b.toNat % n)).setWidth w := by
  intro s
  have hsn : s < n := Nat.mod_lt _ hn0
  rw [lowMask_and (Nat.le_of_lt hnw)]
  congr 1
  ext i hi
  have hiw : i < w := Nat.lt_trans hi hnw
  simp only [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_setWidth, BitVec.getLsbD_or,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_rotateRight,
    hi, hiw, decide_true, Bool.true_and]
  by_cases hsi : s + i < n
  · have hlt : i < n - s := by omega
    have hsw : s + i < w := Nat.lt_trans hsi hnw
    dsimp only [s] at hlt hsw ⊢
    simp [hlt, hsw]
  · have hns : ¬ (i < n - s) := by omega
    have hge : n ≤ s + i := by omega
    have hfalse : a.getLsbD (s + i) = false := BitVec.getLsbD_of_ge a (s + i) hge
    have hsub : i - (n - s) < n := by omega
    have hsubw : i - (n - s) < w := Nat.lt_trans hsub hnw
    dsimp only [s] at hns hfalse hsubw ⊢
    simp [hns, hfalse, hsubw]

private theorem countMod_toNat_mod {n w : Nat} (hn0 : 0 < n) (hnw : n < w) (b : BitVec n) :
    (BitVec.ofNat w (b.toNat % n)).toNat % w = b.toNat % n := by
  have hpow : w < 2 ^ w := @Nat.lt_pow_self w 2 (by decide)
  have hb : b.toNat % n < n := Nat.mod_lt _ hn0
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans hb (Nat.lt_trans hnw hpow)),
    Nat.mod_eq_of_lt (Nat.lt_trans hb hnw)]

private theorem ofNat_sub_toNat_mod {n w s : Nat} (hnw : n < w) (hs : s < n) :
    (BitVec.ofNat w n - BitVec.ofNat w s).toNat % w = n - s := by
  have hpow : w < 2 ^ w := @Nat.lt_pow_self w 2 (by decide)
  have h1 : (BitVec.ofNat w n).toNat = n := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h2 : (BitVec.ofNat w s).toNat = s := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hdiff : (BitVec.ofNat w n - BitVec.ofNat w s).toNat = n - s := by
    rw [BitVec.toNat_sub, h1, h2]
    have hsplit : 2 ^ w - s + n = 2 ^ w + (n - s) := by omega
    rw [hsplit, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
  rw [hdiff, Nat.mod_eq_of_lt (by omega)]

private theorem legalBitsArith_wp (target : LegalTarget) {Γ : Env} {rs : List Ty}
    {Q : Post rs} {X : XPost} {n : Nat} (hn : target.supportsTy (.bits n) = true)
    (c : OpCode [.bits n, .bits n] [.bits n])
    (hc : match c with
      | .add _ | .sub _ | .mul _ | .and _ | .or _ | .xor _
      | .shl _ | .lshr _ | .ashr _ | .rotl _ | .rotr _ => True
      | _ => False)
    (a' b' : Arg Val (.bits (target.widenWidth n))) (a b : BitVec n)
    (ha : a'.val = a.setWidth (target.widenWidth n))
    (hb : b'.val = b.setWidth (target.widenWidth n))
    {k : Arg Val (.bits (target.widenWidth n)) → Expr Val Cont rs} {m : Mem 64}
    (hk : Op.wp ⟨c, ((Arg.imm a : Arg Val (.bits n)), Arg.imm b, ())⟩
      (fun (res, ()) => ∀ r, r.val = res.setWidth (target.widenWidth n) → wp Γ Q X (k r) m)) :
    wp Γ Q X (legalBitsArith target n c a' b' k) m := by
  have hnw : n ≤ target.widenWidth n := le_widenWidth_of_supports hn
  dsimp only [legalBitsArith]
  by_cases hn0 : n = 0
  · subst hn0
    have ha0 : a = 0#0 := bitVec0_eq_zero a
    have hb0 : b = 0#0 := bitVec0_eq_zero b
    subst ha0; subst hb0
    simp only [beq_self_eq_true, ↓reduceIte]
    have h0 : ∀ v : BitVec 0, v.setWidth (target.widenWidth 0) = 0#(target.widenWidth 0) :=
      fun v => by rw [bitVec0_eq_zero v, BitVec.setWidth_zero _ 0]
    cases c <;> try exact hc.elim
    all_goals
      dsimp only [Op.wp, OpCode.wp, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, vals, Arg.val_imm, lift2] at hk
      exact hk (.imm 0#(target.widenWidth 0)) (by simp [h0])
  · have hn0pos : 0 < n := Nat.pos_of_ne_zero hn0
    have hn0f : (n == 0) = false := beq_false_of_ne hn0
    simp only [hn0f, Bool.false_eq_true, ↓reduceIte]
    cases c with
    | add _ =>
      dsimp only [Op.wp, OpCode.wp, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, vals, Arg.val_imm, lift2] at hk
      simp only [wp, Op.wp, OpCode.wp, op2, vals, lift2]
      refine emitMaskToN_wp hnw rfl fun r hr => hk r ?_
      rw [hr, ← lowMask_and hnw]
      change (a'.val + b'.val) &&& lowMask n (target.widenWidth n) = _
      rw [ha, hb, setWidth_add_of_le hnw]
    | sub _ =>
      dsimp only [Op.wp, OpCode.wp, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, vals, Arg.val_imm, lift2] at hk
      simp only [wp, Op.wp, OpCode.wp, op2, vals, lift2]
      refine emitMaskToN_wp hnw rfl fun r hr => hk r ?_
      rw [hr, ← lowMask_and hnw]
      change (a'.val - b'.val) &&& lowMask n (target.widenWidth n) = _
      rw [ha, hb, setWidth_sub_of_le hnw]
    | mul _ =>
      dsimp only [Op.wp, OpCode.wp, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, vals, Arg.val_imm, lift2] at hk
      simp only [wp, Op.wp, OpCode.wp, op2, vals, lift2]
      refine emitMaskToN_wp hnw rfl fun r hr => hk r ?_
      rw [hr, ← lowMask_and hnw]
      change (a'.val * b'.val) &&& lowMask n (target.widenWidth n) = _
      rw [ha, hb, setWidth_mul_of_le hnw]
    | and _ =>
      dsimp only [Op.wp, OpCode.wp, vals, Arg.val_imm, lift2] at hk
      simp only [wp, Op.wp, OpCode.wp, op2, vals, lift2]
      exact hk _ (by change a'.val &&& b'.val = _; rw [ha, hb, setWidth_and_of_le])
    | or _ =>
      dsimp only [Op.wp, OpCode.wp, vals, Arg.val_imm, lift2] at hk
      simp only [wp, Op.wp, OpCode.wp, op2, vals, lift2]
      exact hk _ (by change a'.val ||| b'.val = _; rw [ha, hb, setWidth_or_of_le])
    | xor _ =>
      dsimp only [Op.wp, OpCode.wp, vals, Arg.val_imm, lift2] at hk
      simp only [wp, Op.wp, OpCode.wp, op2, vals, lift2]
      exact hk _ (by change a'.val ^^^ b'.val = _; rw [ha, hb, setWidth_xor_of_le])
    | shl _ =>
      dsimp only [Op.wp, OpCode.wp, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, vals, Arg.val_imm, lift2] at hk
      by_cases heq : n = target.widenWidth n
      · have hbeq : (n == target.widenWidth n) = true := beq_iff_eq.mpr heq
        simp only [hbeq, ↓reduceIte, wp, Op.wp, OpCode.wp, op2, vals, lift2]
        revert a' b' ha hb k hk
        rw [← heq]
        intro a' b' ha hb k hk
        rw [BitVec.setWidth_eq] at ha hb hk
        exact hk _ (by change a'.val <<< (b'.val.toNat % n) = _; rw [ha, hb])
      · have hlt : n < target.widenWidth n := Nat.lt_of_le_of_ne hnw heq
        have hf : (n == target.widenWidth n) = false := beq_false_of_ne heq
        simp only [hf, Bool.false_eq_true, ↓reduceIte]
        refine emitCountMod_wp hn0pos hlt hb fun cm hcm => ?_
        dsimp only [wp, Op.wp, OpCode.wp, vals, lift2]
        refine emitMaskToN_wp hnw rfl fun r hr => hk r ?_
        rw [hr, ← lowMask_and hnw]
        change (a'.val <<< (cm.val.toNat % target.widenWidth n)) &&&
          lowMask n (target.widenWidth n) = _
        rw [ha, hcm, countMod_toNat_mod hn0pos hlt b]
        exact setWidth_shl_of_lt hlt a (b.toNat % n)
    | lshr _ =>
      dsimp only [Op.wp, OpCode.wp, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, vals, Arg.val_imm, lift2] at hk
      by_cases heq : n = target.widenWidth n
      · have hbeq : (n == target.widenWidth n) = true := beq_iff_eq.mpr heq
        simp only [hbeq, ↓reduceIte, wp, Op.wp, OpCode.wp, op2, vals, lift2]
        revert a' b' ha hb k hk
        rw [← heq]
        intro a' b' ha hb k hk
        rw [BitVec.setWidth_eq] at ha hb hk
        exact hk _ (by change a'.val >>> (b'.val.toNat % n) = _; rw [ha, hb])
      · have hlt : n < target.widenWidth n := Nat.lt_of_le_of_ne hnw heq
        have hf : (n == target.widenWidth n) = false := beq_false_of_ne heq
        simp only [hf, Bool.false_eq_true, ↓reduceIte]
        refine emitCountMod_wp hn0pos hlt hb fun cm hcm => ?_
        dsimp only [wp, Op.wp, OpCode.wp, vals, lift2]
        exact hk _ (by
          change a'.val >>> (cm.val.toNat % target.widenWidth n) = _
          rw [ha, hcm, countMod_toNat_mod hn0pos hlt b, setWidth_lshr_of_le hnw])
    | ashr _ =>
      dsimp only [Op.wp, OpCode.wp, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, vals, Arg.val_imm, lift2] at hk
      by_cases heq : n = target.widenWidth n
      · have hbeq : (n == target.widenWidth n) = true := beq_iff_eq.mpr heq
        simp only [hbeq, ↓reduceIte, wp, Op.wp, OpCode.wp, op2, vals, lift2]
        revert a' b' ha hb k hk
        rw [← heq]
        intro a' b' ha hb k hk
        rw [BitVec.setWidth_eq] at ha hb hk
        exact hk _ (by change a'.val.sshiftRight (b'.val.toNat % n) = _; rw [ha, hb])
      · have hlt : n < target.widenWidth n := Nat.lt_of_le_of_ne hnw heq
        have hf : (n == target.widenWidth n) = false := beq_false_of_ne heq
        simp only [hf, Bool.false_eq_true, ↓reduceIte]
        refine emitCountMod_wp hn0pos hlt hb fun cm hcm =>
          emitSextToW_wp hn0pos hnw ha fun sa hsa => ?_
        dsimp only [wp, Op.wp, OpCode.wp, vals, lift2]
        refine emitMaskToN_wp hnw rfl fun r hr => hk r ?_
        rw [hr, ← lowMask_and hnw]
        change (sa.val.sshiftRight (cm.val.toNat % target.widenWidth n)) &&&
          lowMask n (target.widenWidth n) = _
        rw [hsa, hcm, countMod_toNat_mod hn0pos hlt b]
        exact setWidth_ashr_signExtend_of_lt hn0pos hlt a (b.toNat % n)
    | rotl _ =>
      dsimp only [Op.wp, OpCode.wp, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, vals, Arg.val_imm, lift2] at hk
      by_cases heq : n = target.widenWidth n
      · have hbeq : (n == target.widenWidth n) = true := beq_iff_eq.mpr heq
        simp only [hbeq, ↓reduceIte, wp, Op.wp, OpCode.wp, op2, vals, lift2]
        revert a' b' ha hb k hk
        rw [← heq]
        intro a' b' ha hb k hk
        rw [BitVec.setWidth_eq] at ha hb hk
        exact hk _ (by change a'.val.rotateLeft (b'.val.toNat % n) = _; rw [ha, hb])
      · have hlt : n < target.widenWidth n := Nat.lt_of_le_of_ne hnw heq
        have hf : (n == target.widenWidth n) = false := beq_false_of_ne heq
        simp only [hf, Bool.false_eq_true, ↓reduceIte]
        refine emitCountMod_wp hn0pos hlt hb fun cm hcm => ?_
        dsimp only [wp, Op.wp, OpCode.wp, vals, lift2, Arg.val_imm]
        refine emitMaskToN_wp hnw rfl fun r hr => hk r ?_
        rw [hr, ← lowMask_and hnw]
        change ((a'.val <<< (cm.val.toNat % target.widenWidth n)) |||
          (a'.val >>> ((BitVec.ofNat (target.widenWidth n) n - cm.val).toNat % target.widenWidth n))) &&&
          lowMask n (target.widenWidth n) = (a.rotateLeft (b.toNat % n)).setWidth (target.widenWidth n)
        rw [ha, hcm, countMod_toNat_mod hn0pos hlt b,
          ofNat_sub_toNat_mod hlt (Nat.mod_lt _ hn0pos)]
        exact setWidth_rotl_of_lt hn0pos hlt a b
    | rotr _ =>
      dsimp only [Op.wp, OpCode.wp, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, vals, Arg.val_imm, lift2] at hk
      by_cases heq : n = target.widenWidth n
      · have hbeq : (n == target.widenWidth n) = true := beq_iff_eq.mpr heq
        simp only [hbeq, ↓reduceIte, wp, Op.wp, OpCode.wp, op2, vals, lift2]
        revert a' b' ha hb k hk
        rw [← heq]
        intro a' b' ha hb k hk
        rw [BitVec.setWidth_eq] at ha hb hk
        exact hk _ (by change a'.val.rotateRight (b'.val.toNat % n) = _; rw [ha, hb])
      · have hlt : n < target.widenWidth n := Nat.lt_of_le_of_ne hnw heq
        have hf : (n == target.widenWidth n) = false := beq_false_of_ne heq
        simp only [hf, Bool.false_eq_true, ↓reduceIte]
        refine emitCountMod_wp hn0pos hlt hb fun cm hcm => ?_
        dsimp only [wp, Op.wp, OpCode.wp, vals, lift2, Arg.val_imm]
        refine emitMaskToN_wp hnw rfl fun r hr => hk r ?_
        rw [hr, ← lowMask_and hnw]
        change ((a'.val >>> (cm.val.toNat % target.widenWidth n)) |||
          (a'.val <<< ((BitVec.ofNat (target.widenWidth n) n - cm.val).toNat % target.widenWidth n))) &&&
          lowMask n (target.widenWidth n) = (a.rotateRight (b.toNat % n)).setWidth (target.widenWidth n)
        rw [ha, hcm, countMod_toNat_mod hn0pos hlt b,
          ofNat_sub_toNat_mod hlt (Nat.mod_lt _ hn0pos)]
        exact setWidth_rotr_of_lt hn0pos hlt a b
    | _ => exact hc.elim

/-! ### Signed/unsigned compare widening, byte swap, uniform vector shift/rotate, and tree `_wp` lemmas -/

private theorem signExtend_eq_setWidth_of_msb_false {n w : Nat} (_hnw : n ≤ w)
    {a : BitVec n} (hm : a.msb = false) :
    a.signExtend w = a.setWidth w := by
  ext i hi
  simp only [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_signExtend, BitVec.getLsbD_setWidth,
    hi, decide_true, Bool.true_and]
  by_cases hin : i < n
  · simp [hin]
  · have hfa : a.getLsbD i = false := BitVec.getLsbD_of_ge a i (by omega)
    simp [hin, hm, hfa]

private theorem not_signExtend_of_pos_le {n w : Nat} (_hn0 : 0 < n) (_hnw : n ≤ w)
    {a : BitVec n} (hm : a.msb = true) :
    ~~~(a.signExtend w) = (~~~a).setWidth w := by
  ext i hi
  simp only [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_not, BitVec.getLsbD_signExtend,
    BitVec.getLsbD_setWidth, hi, decide_true, Bool.true_and]
  by_cases hin : i < n
  · simp [hin]
  · simp [hin, hm]

private theorem toNat_not_add {w : Nat} (x : BitVec w) :
    x.toNat + (~~~x).toNat = 2 ^ w - 1 := by
  have h : x + ~~~x = BitVec.allOnes w := BitVec.add_not_self x
  have hn := congrArg BitVec.toNat h
  rw [BitVec.toNat_add, BitVec.toNat_allOnes] at hn
  have h1 : x.toNat < 2 ^ w := x.isLt
  have h2 : (~~~x).toNat < 2 ^ w := (~~~x).isLt
  by_cases hlt : x.toNat + (~~~x).toNat < 2 ^ w
  · rw [Nat.mod_eq_of_lt hlt] at hn
    exact hn
  · have hm : (x.toNat + (~~~x).toNat) % 2 ^ w = x.toNat + (~~~x).toNat - 2 ^ w := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [hm] at hn
    omega

private theorem two_mul_toNat_lt_iff_msb_false {n : Nat} (hn0 : 0 < n) (a : BitVec n) :
    2 * a.toNat < 2 ^ n ↔ a.msb = false := by
  have h2n : 2 ^ n = 2 * 2 ^ (n - 1) := by
    calc 2 ^ n = 2 ^ (n - 1 + 1) := by rw [Nat.sub_add_cancel hn0]
      _ = 2 ^ (n - 1) * 2 := Nat.pow_succ _ _
      _ = 2 * 2 ^ (n - 1) := Nat.mul_comm _ _
  rw [BitVec.msb_eq_decide, h2n]
  constructor
  · intro h; simp only [decide_eq_false_iff_not]; omega
  · intro h; simp only [decide_eq_false_iff_not] at h; omega

private theorem toInt_signExtend_of_pos_le {n w : Nat} (hn0 : 0 < n) (hnw : n ≤ w) (a : BitVec n) :
    (a.signExtend w).toInt = a.toInt := by
  have hw0 : 0 < w := Nat.lt_of_lt_of_le hn0 hnw
  rw [BitVec.toInt_eq_toNat_cond, BitVec.toInt_eq_toNat_cond]
  by_cases hm : a.msb = true
  · have hms : (a.signExtend w).msb = true := by rwa [msb_signExtend_of_pos_le hn0 hnw]
    have hna : ¬ (2 * a.toNat < 2 ^ n) := by
      rw [two_mul_toNat_lt_iff_msb_false hn0, hm]; decide
    have hns : ¬ (2 * (a.signExtend w).toNat < 2 ^ w) := by
      rw [two_mul_toNat_lt_iff_msb_false hw0, hms]; decide
    simp only [hna, hns, ↓reduceIte]
    have hnot := not_signExtend_of_pos_le hn0 hnw hm
    have h1 := toNat_not_add (a.signExtend w)
    have h2 := toNat_not_add a
    rw [hnot, toNat_setWidth_of_le hnw] at h1
    omega
  · have hmf : a.msb = false := Bool.eq_false_iff.mpr hm
    have hms : (a.signExtend w).msb = false := by rwa [msb_signExtend_of_pos_le hn0 hnw]
    have hna : 2 * a.toNat < 2 ^ n := (two_mul_toNat_lt_iff_msb_false hn0 a).2 hmf
    have hns : 2 * (a.signExtend w).toNat < 2 ^ w :=
      (two_mul_toNat_lt_iff_msb_false hw0 (a.signExtend w)).2 hms
    simp only [hna, hns, ↓reduceIte]
    rw [signExtend_eq_setWidth_of_msb_false hnw hmf, toNat_setWidth_of_le hnw]

private theorem evalBits_setWidth_unsigned {n w : Nat} (hnw : n ≤ w) (o : CmpOp)
    (ho : match o with | .slt | .sle | .sgt | .sge => False | _ => True)
    (a b : BitVec n) :
    o.evalBits (a.setWidth w) (b.setWidth w) = o.evalBits a b := by
  cases o with
  | eq => simp only [CmpOp.evalBits]; exact decide_eq_decide.2 ⟨setWidth_inj_of_le hnw, congrArg _⟩
  | ne => simp only [CmpOp.evalBits]; exact decide_eq_decide.2 (not_congr ⟨setWidth_inj_of_le hnw, congrArg _⟩)
  | ult | ule | ugt | uge =>
    simp only [CmpOp.evalBits, BitVec.ult, BitVec.ule, toNat_setWidth_of_le hnw]
  | _ => exact ho.elim

private theorem evalBits_signExtend_signed {n w : Nat} (hn0 : 0 < n) (hnw : n ≤ w) (o : CmpOp)
    (ho : match o with | .slt | .sle | .sgt | .sge => True | _ => False) (a b : BitVec n) :
    o.evalBits (a.signExtend w) (b.signExtend w) = o.evalBits a b := by
  cases o with
  | slt | sgt => simp only [CmpOp.evalBits, BitVec.slt, toInt_signExtend_of_pos_le hn0 hnw]
  | sle | sge => simp only [CmpOp.evalBits, BitVec.sle, toInt_signExtend_of_pos_le hn0 hnw]
  | _ => exact ho.elim

private theorem getLsbD_bswapBits_go {w : Nat} :
    ∀ (m : Nat) (x : BitVec w) {i : Nat}, i < 8 * m →
      (bswapBits.go x m).getLsbD i = x.getLsbD (8 * (m - 1 - i / 8) + i % 8)
  | 0, _, _, hi => by omega
  | m + 1, x, i, hi => by
    dsimp only [bswapBits.go]
    rw [BitVec.getLsbD_cast, BitVec.getLsbD_append]
    by_cases hi8 : i < 8
    · have hq : i / 8 = 0 := Nat.div_eq_of_lt hi8
      have hr : i % 8 = i := Nat.mod_eq_of_lt hi8
      simp only [hi8, ↓reduceIte, hq, hr, Nat.sub_zero, Nat.add_sub_cancel]
      rw [BitVec.getLsbD_extractLsb']
      simp [hi8]
    · have hi8' : ¬ (i < 8) := hi8
      have him : i - 8 < 8 * m := by omega
      have ih := getLsbD_bswapBits_go m x him
      have hq : i / 8 = (i - 8) / 8 + 1 := by omega
      have hr : i % 8 = (i - 8) % 8 := by omega
      have hsub : m + 1 - 1 - i / 8 = m - 1 - (i - 8) / 8 := by omega
      simp only [hi8', ↓reduceIte, ih, hsub, ← hr]

private theorem bswapBits_8 (x : BitVec 8) : bswapBits x = x := by
  ext i hi
  simp only [← BitVec.getLsbD_eq_getElem, bswapBits, BitVec.getLsbD_setWidth, hi, decide_true,
    Bool.true_and]
  rw [getLsbD_bswapBits_go 1 x hi]
  have hq : i / 8 = 0 := Nat.div_eq_of_lt hi
  have hr : i % 8 = i := Nat.mod_eq_of_lt hi
  simp [hq, hr]

private theorem setWidth_bswap_of_lt {n w : Nat} (_hn0 : 0 < n) (hnw : n < w)
    (hn8 : n % 8 = 0) (hw8 : w % 8 = 0) (a : BitVec n) :
    (bswapBits (a.setWidth w)) >>> (w - n) = (bswapBits a).setWidth w := by
  ext i hi
  simp only [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_setWidth,
    bswapBits, hi, decide_true, Bool.true_and]
  by_cases hin : i < n
  · have hni : w - n + i < w := by omega
    have hnw8 : w - n + i < 8 * (w / 8) := by omega
    have hin8 : i < 8 * (n / 8) := by omega
    rw [decide_eq_true hni, decide_eq_true hin, Bool.true_and, Bool.true_and,
      getLsbD_bswapBits_go (w / 8) (a.setWidth w) hnw8,
      getLsbD_bswapBits_go (n / 8) a hin8]
    have hidx_eq : 8 * (w / 8 - 1 - (w - n + i) / 8) + (w - n + i) % 8 =
        8 * (n / 8 - 1 - i / 8) + i % 8 := by omega
    have hlt_w : 8 * (n / 8 - 1 - i / 8) + i % 8 < w := by omega
    rw [hidx_eq, BitVec.getLsbD_setWidth, decide_eq_true hlt_w, Bool.true_and]
  · have hge : ¬ (w - n + i < w) := by omega
    simp [decide_eq_false hge, decide_eq_false hin]

private theorem rotateRight_sub_eq_rotateLeft {w s : Nat} (hs0 : 0 < s) (hs : s < w) (x : BitVec w) :
    x.rotateRight (w - s) = x.rotateLeft s := by
  ext i hi
  simp only [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_rotateRight, BitVec.getLsbD_rotateLeft,
    hi, decide_true, Bool.true_and]
  have h1 : s % w = s := Nat.mod_eq_of_lt hs
  have h2 : (w - s) % w = w - s := Nat.mod_eq_of_lt (by omega)
  have h3 : w - (w - s) = s := by omega
  rw [h1, h2, h3]

private theorem rotateRight_and_allOnes_shl_eq_shl {w s : Nat} (hs0 : 0 < s) (hs : s < w) (x : BitVec w) :
    x.rotateRight (w - s) &&& (BitVec.allOnes w <<< s) = x <<< s := by
  ext i hi
  simp only [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_and, BitVec.getLsbD_rotateRight,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_allOnes, hi, decide_true, Bool.true_and]
  have h2 : (w - s) % w = w - s := Nat.mod_eq_of_lt (by omega)
  have h3 : w - (w - s) = s := by omega
  rw [h2, h3]
  by_cases his : i < s
  · simp [his]
  · have hisw : i - s < w := by omega
    simp [his, hisw]

private theorem uniformShiftLeaf?_hasFloat_false :
    ∀ (t : Ty) (c : Val t) {w s : Nat}, uniformShiftLeaf? t c = some (w, s) → t.hasFloat = false
  | .bool, _, _, _, h => by simp [uniformShiftLeaf?] at h
  | .float _, _, _, _, h => by simp [uniformShiftLeaf?] at h
  | .bits _, _, _, _, _ => rfl
  | .pair a b, (x, y), w, s, h => by
    simp only [uniformShiftLeaf?] at h
    cases ha : uniformShiftLeaf? a x with
    | none => simp [ha] at h
    | some pa =>
      cases hb : uniformShiftLeaf? b y with
      | none => simp [ha, hb] at h
      | some pb =>
        have hfa := uniformShiftLeaf?_hasFloat_false a x ha
        have hfb := uniformShiftLeaf?_hasFloat_false b y hb
        simp [Ty.hasFloat, hfa, hfb]

private theorem uniformShiftLeaf?_lt :
    ∀ (t : Ty) (c : Val t) {w s : Nat}, uniformShiftLeaf? t c = some (w, s) → 0 < w ∧ s < w
  | .bool, _, _, _, h => by simp [uniformShiftLeaf?] at h
  | .float _, _, _, _, h => by simp [uniformShiftLeaf?] at h
  | .bits n, x, w, s, h => by
    simp only [uniformShiftLeaf?] at h
    by_cases hn0 : n = 0
    · simp [hn0] at h
    · have hf : (n == 0) = false := beq_false_of_ne hn0
      simp only [hf, Bool.false_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      have hpos : 0 < n := Nat.pos_of_ne_zero hn0
      exact ⟨hpos, Nat.mod_lt _ hpos⟩
  | .pair a b, (x, y), w, s, h => by
    simp only [uniformShiftLeaf?] at h
    cases ha : uniformShiftLeaf? a x with
    | none => simp [ha] at h
    | some pa =>
      cases hb : uniformShiftLeaf? b y with
      | none => simp [ha, hb] at h
      | some pb =>
        simp only [ha, hb, Bind.bind, Option.bind] at h
        by_cases hc : (pa.1 == pb.1 && pa.2 == pb.2) = true
        · simp only [hc, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          exact uniformShiftLeaf?_lt a x ha
        · simp [hc] at h

private theorem bv_rotateLeft_zero {n : Nat} (x : BitVec n) : x.rotateLeft 0 = x := by
  ext i hi
  simp [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_rotateLeft, hi]

private theorem uniformShiftLeaf?_zero_rotl :
    ∀ (t : Ty) (x c : Val t) {w : Nat}, uniformShiftLeaf? t c = some (w, 0) →
      lift2 (fun {n} x y => x.rotateLeft (y.toNat % n)) (fun x _ => x) t x c = x
  | .bool, _, _, _, h => by simp [uniformShiftLeaf?] at h
  | .float _, _, _, _, h => by simp [uniformShiftLeaf?] at h
  | .bits n, x, c, w, h => by
    simp only [uniformShiftLeaf?] at h
    by_cases hn0 : n = 0
    · simp [hn0] at h
    · have hf : (n == 0) = false := beq_false_of_ne hn0
      simp only [hf, Bool.false_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, hc0⟩
      simp [lift2, hc0, bv_rotateLeft_zero]
  | .pair a b, (x1, x2), (c1, c2), w, h => by
    simp only [uniformShiftLeaf?] at h
    cases ha : uniformShiftLeaf? a c1 with
    | none => simp [ha] at h
    | some pa =>
      cases hb : uniformShiftLeaf? b c2 with
      | none => simp [ha, hb] at h
      | some pb =>
        simp only [ha, hb, Bind.bind, Option.bind] at h
        by_cases hc : (pa.1 == pb.1 && pa.2 == pb.2) = true
        · simp only [hc, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
          simp only [Bool.and_eq_true, beq_iff_eq] at hc
          rcases hc with ⟨hweq, hseq⟩
          rcases h with ⟨rfl, h0⟩
          have ha' : uniformShiftLeaf? a c1 = some (pa.1, 0) := by
            rw [ha]; congr 1; exact Prod.ext rfl h0
          have hb' : uniformShiftLeaf? b c2 = some (pa.1, 0) := by
            rw [hb]; congr 1; exact Prod.ext hweq.symm (hseq.symm.trans h0)
          exact Prod.ext (uniformShiftLeaf?_zero_rotl a x1 c1 ha')
            (uniformShiftLeaf?_zero_rotl b x2 c2 hb')
        · simp [hc] at h

private theorem uniformShiftLeaf?_zero_shl :
    ∀ (t : Ty) (x c : Val t) {w : Nat}, uniformShiftLeaf? t c = some (w, 0) →
      lift2 (fun {n} x y => x <<< (y.toNat % n)) (fun x _ => x) t x c = x
  | .bool, _, _, _, h => by simp [uniformShiftLeaf?] at h
  | .float _, _, _, _, h => by simp [uniformShiftLeaf?] at h
  | .bits n, x, c, w, h => by
    simp only [uniformShiftLeaf?] at h
    by_cases hn0 : n = 0
    · simp [hn0] at h
    · have hf : (n == 0) = false := beq_false_of_ne hn0
      simp only [hf, Bool.false_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, hc0⟩
      simp [lift2, hc0]
  | .pair a b, (x1, x2), (c1, c2), w, h => by
    simp only [uniformShiftLeaf?] at h
    cases ha : uniformShiftLeaf? a c1 with
    | none => simp [ha] at h
    | some pa =>
      cases hb : uniformShiftLeaf? b c2 with
      | none => simp [ha, hb] at h
      | some pb =>
        simp only [ha, hb, Bind.bind, Option.bind] at h
        by_cases hc : (pa.1 == pb.1 && pa.2 == pb.2) = true
        · simp only [hc, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, h0⟩
          simp only [Bool.and_eq_true, beq_iff_eq] at hc
          rcases hc with ⟨hweq, hseq⟩
          have ha' : uniformShiftLeaf? a c1 = some (pa.1, 0) := by
            rw [ha]; congr 1; exact Prod.ext rfl h0
          have hb' : uniformShiftLeaf? b c2 = some (pa.1, 0) := by
            rw [hb]; congr 1; exact Prod.ext hweq.symm (hseq.symm.trans h0)
          exact Prod.ext (uniformShiftLeaf?_zero_shl a x1 c1 ha')
            (uniformShiftLeaf?_zero_shl b x2 c2 hb')
        · simp [hc] at h

private theorem uniformShiftLeaf?_splat_rotl :
    ∀ (t : Ty) (x c : Val t) {w s : Nat}, uniformShiftLeaf? t c = some (w, s) → 0 < s →
      lift2 (fun {n} x y => x.rotateLeft (y.toNat % n)) (fun x _ => x) t x c =
        lift2 (fun {n} x y => x.rotateRight (y.toNat % n)) (fun x _ => x) t x
          (splatBits w (BitVec.ofNat w (w - s)) t)
  | .bool, _, _, _, _, h, _ => by simp [uniformShiftLeaf?] at h
  | .float _, _, _, _, _, h, _ => by simp [uniformShiftLeaf?] at h
  | .bits n, x, c, w, s, h, hs => by
    have ⟨hwpos, hsw⟩ := uniformShiftLeaf?_lt (.bits n) c h
    simp only [uniformShiftLeaf?] at h
    by_cases hn0 : n = 0
    · simp [hn0] at h
    · have hf : (n == 0) = false := beq_false_of_ne hn0
      simp only [hf, Bool.false_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      simp only [lift2, splatBits, dite_true]
      have hpow : n < 2 ^ n := @Nat.lt_pow_self n 2 (by decide)
      have hsub_lt : n - c.toNat % n < 2 ^ n := Nat.lt_of_le_of_lt (Nat.sub_le _ _) hpow
      have hmod : (BitVec.ofNat n (n - c.toNat % n)).toNat % n = n - c.toNat % n := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsub_lt, Nat.mod_eq_of_lt (by omega)]
      rw [hmod]
      exact (rotateRight_sub_eq_rotateLeft hs hsw x).symm
  | .pair a b, (x1, x2), (c1, c2), w, s, h, hs => by
    simp only [uniformShiftLeaf?] at h
    cases ha : uniformShiftLeaf? a c1 with
    | none => simp [ha] at h
    | some pa =>
      cases hb : uniformShiftLeaf? b c2 with
      | none => simp [ha, hb] at h
      | some pb =>
        simp only [ha, hb, Bind.bind, Option.bind] at h
        by_cases hc : (pa.1 == pb.1 && pa.2 == pb.2) = true
        · simp only [hc, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          simp only [Bool.and_eq_true, beq_iff_eq] at hc
          rcases hc with ⟨hweq, hseq⟩
          have hb' : uniformShiftLeaf? b c2 = some (pa.1, pa.2) := by
            rw [hb]; congr 1; exact Prod.ext hweq.symm hseq.symm
          exact Prod.ext (uniformShiftLeaf?_splat_rotl a x1 c1 ha hs)
            (uniformShiftLeaf?_splat_rotl b x2 c2 hb' hs)
        · simp [hc] at h

private theorem uniformShiftLeaf?_splat_shl :
    ∀ (t : Ty) (x c : Val t) {w s : Nat}, uniformShiftLeaf? t c = some (w, s) → 0 < s →
      lift2 (fun {n} x y => x <<< (y.toNat % n)) (fun x _ => x) t x c =
        lift2 (· &&& ·) (· && ·) t
          (lift2 (fun {n} x y => x.rotateRight (y.toNat % n)) (fun x _ => x) t x
            (splatBits w (BitVec.ofNat w (w - s)) t))
          (splatBits w (BitVec.allOnes w <<< s) t)
  | .bool, _, _, _, _, h, _ => by simp [uniformShiftLeaf?] at h
  | .float _, _, _, _, _, h, _ => by simp [uniformShiftLeaf?] at h
  | .bits n, x, c, w, s, h, hs => by
    have ⟨hwpos, hsw⟩ := uniformShiftLeaf?_lt (.bits n) c h
    simp only [uniformShiftLeaf?] at h
    by_cases hn0 : n = 0
    · simp [hn0] at h
    · have hf : (n == 0) = false := beq_false_of_ne hn0
      simp only [hf, Bool.false_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      simp only [lift2, splatBits, dite_true]
      have hpow : n < 2 ^ n := @Nat.lt_pow_self n 2 (by decide)
      have hsub_lt : n - c.toNat % n < 2 ^ n := Nat.lt_of_le_of_lt (Nat.sub_le _ _) hpow
      have hmod : (BitVec.ofNat n (n - c.toNat % n)).toNat % n = n - c.toNat % n := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsub_lt, Nat.mod_eq_of_lt (by omega)]
      rw [hmod]
      exact (rotateRight_and_allOnes_shl_eq_shl hs hsw x).symm
  | .pair a b, (x1, x2), (c1, c2), w, s, h, hs => by
    simp only [uniformShiftLeaf?] at h
    cases ha : uniformShiftLeaf? a c1 with
    | none => simp [ha] at h
    | some pa =>
      cases hb : uniformShiftLeaf? b c2 with
      | none => simp [ha, hb] at h
      | some pb =>
        simp only [ha, hb, Bind.bind, Option.bind] at h
        by_cases hc : (pa.1 == pb.1 && pa.2 == pb.2) = true
        · simp only [hc, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          simp only [Bool.and_eq_true, beq_iff_eq] at hc
          rcases hc with ⟨hweq, hseq⟩
          have hb' : uniformShiftLeaf? b c2 = some (pa.1, pa.2) := by
            rw [hb]; congr 1; exact Prod.ext hweq.symm hseq.symm
          exact Prod.ext (uniformShiftLeaf?_splat_shl a x1 c1 ha hs)
            (uniformShiftLeaf?_splat_shl b x2 c2 hb' hs)
        · simp [hc] at h

/-! ### Relational tree weakest-precondition specs -/

private def TreeRel1 (onB : Bool → (Bool → Prop) → Prop)
    (onBits : ∀ n, BitVec n → (BitVec n → Prop) → Prop)
    (onF : ∀ (f : Fmt), BitVec f.width → (BitVec f.width → Prop) → Prop) :
    (u : Ty) → Val u → (Val u → Prop) → Prop
  | .bool, x, post => onB x post
  | .bits n, x, post => onBits n x post
  | .float f, x, post => onF f x post
  | .pair a b, p, post =>
    TreeRel1 onB onBits onF a p.1 fun r1 =>
    TreeRel1 onB onBits onF b p.2 fun r2 => post (r1, r2)

private theorem TreeRel1.mono {onB onBits onF}
    (hB : ∀ x {p q : Bool → Prop}, (∀ r, p r → q r) → onB x p → onB x q)
    (hBits : ∀ n x {p q : BitVec n → Prop}, (∀ r, p r → q r) → onBits n x p → onBits n x q)
    (hF : ∀ (f : Fmt) x {p q : BitVec f.width → Prop}, (∀ r, p r → q r) → onF f x p → onF f x q) :
    ∀ {u : Ty} {x : Val u} {p q : Val u → Prop}, (∀ r, p r → q r) →
      TreeRel1 onB onBits onF u x p → TreeRel1 onB onBits onF u x q
  | .bool, _, _, _, hpq, h => hB _ hpq h
  | .bits n, _, _, _, hpq, h => hBits n _ hpq h
  | .float f, _, _, _, hpq, h => hF f _ hpq h
  | .pair a b, (_, _), _, _, hpq, h =>
    TreeRel1.mono (u := a) hB hBits hF (fun r1 h2 =>
      TreeRel1.mono (u := b) hB hBits hF (fun r2 hr2 => hpq (r1, r2) hr2) h2) h

private def TreeRel2 (onB : Bool → Bool → (Bool → Prop) → Prop)
    (onBits : ∀ n, BitVec n → BitVec n → (BitVec n → Prop) → Prop)
    (onF : ∀ (f : Fmt), BitVec f.width → BitVec f.width → (BitVec f.width → Prop) → Prop) :
    (u : Ty) → Val u → Val u → (Val u → Prop) → Prop
  | .bool, x, y, post => onB x y post
  | .bits n, x, y, post => onBits n x y post
  | .float f, x, y, post => onF f x y post
  | .pair a b, p, q, post =>
    TreeRel2 onB onBits onF a p.1 q.1 fun r1 =>
    TreeRel2 onB onBits onF b p.2 q.2 fun r2 => post (r1, r2)

private theorem TreeRel2.mono {onB onBits onF}
    (hB : ∀ x y {p q : Bool → Prop}, (∀ r, p r → q r) → onB x y p → onB x y q)
    (hBits : ∀ n x y {p q : BitVec n → Prop}, (∀ r, p r → q r) → onBits n x y p → onBits n x y q)
    (hF : ∀ (f : Fmt) x y {p q : BitVec f.width → Prop}, (∀ r, p r → q r) → onF f x y p → onF f x y q) :
    ∀ {u : Ty} {x y : Val u} {p q : Val u → Prop}, (∀ r, p r → q r) →
      TreeRel2 onB onBits onF u x y p → TreeRel2 onB onBits onF u x y q
  | .bool, _, _, _, _, hpq, h => hB _ _ hpq h
  | .bits n, _, _, _, _, hpq, h => hBits n _ _ hpq h
  | .float f, _, _, _, _, hpq, h => hF f _ _ hpq h
  | .pair a b, (_, _), (_, _), _, _, hpq, h =>
    TreeRel2.mono (u := a) hB hBits hF (fun r1 h2 =>
      TreeRel2.mono (u := b) hB hBits hF (fun r2 hr2 => hpq (r1, r2) hr2) h2) h

private def TreeRel3 (onB : Bool → Bool → Bool → (Bool → Prop) → Prop)
    (onBits : ∀ n, BitVec n → BitVec n → BitVec n → (BitVec n → Prop) → Prop)
    (onF : ∀ (f : Fmt), BitVec f.width → BitVec f.width → BitVec f.width → (BitVec f.width → Prop) → Prop) :
    (u : Ty) → Val u → Val u → Val u → (Val u → Prop) → Prop
  | .bool, x, y, z, post => onB x y z post
  | .bits n, x, y, z, post => onBits n x y z post
  | .float f, x, y, z, post => onF f x y z post
  | .pair a b, p, q, r, post =>
    TreeRel3 onB onBits onF a p.1 q.1 r.1 fun r1 =>
    TreeRel3 onB onBits onF b p.2 q.2 r.2 fun r2 => post (r1, r2)

private theorem TreeRel3.mono {onB onBits onF}
    (hB : ∀ x y z {p q : Bool → Prop}, (∀ r, p r → q r) → onB x y z p → onB x y z q)
    (hBits : ∀ n x y z {p q : BitVec n → Prop}, (∀ r, p r → q r) → onBits n x y z p → onBits n x y z q)
    (hF : ∀ (f : Fmt) x y z {p q : BitVec f.width → Prop}, (∀ r, p r → q r) → onF f x y z p → onF f x y z q) :
    ∀ {u : Ty} {x y z : Val u} {p q : Val u → Prop}, (∀ r, p r → q r) →
      TreeRel3 onB onBits onF u x y z p → TreeRel3 onB onBits onF u x y z q
  | .bool, _, _, _, _, _, hpq, h => hB _ _ _ hpq h
  | .bits n, _, _, _, _, _, hpq, h => hBits n _ _ _ hpq h
  | .float f, _, _, _, _, _, hpq, h => hF f _ _ _ hpq h
  | .pair a b, (_, _), (_, _), (_, _), _, _, hpq, h =>
    TreeRel3.mono (u := a) hB hBits hF (fun r1 h2 =>
      TreeRel3.mono (u := b) hB hBits hF (fun r2 hr2 => hpq (r1, r2) hr2) h2) h

private theorem legalUnaryTree_goS_wp (target : LegalTarget) {Γ : Env} {rs : List Ty}
    {Q : Post rs} {X : XPost}
    (onBool : Arg Val .bool → (Arg Val .bool → Expr Val Cont rs) → Expr Val Cont rs)
    (onBits : (n : Nat) → Arg Val (.bits (target.widenWidth n)) →
      (Arg Val (.bits (target.widenWidth n)) → Expr Val Cont rs) → Expr Val Cont rs)
    (onFloat : (f : Fmt) → Arg Val (.float f) →
      (Arg Val (.float f) → Expr Val Cont rs) → Expr Val Cont rs)
    {onB : Bool → (Bool → Prop) → Prop}
    {onBi : ∀ n, BitVec n → (BitVec n → Prop) → Prop}
    {onF : ∀ (f : Fmt), BitVec f.width → (BitVec f.width → Prop) → Prop}
    (hB : ∀ x' x k m, x'.val = x →
      onB x (fun res => ∀ r, r.val = res → wp Γ Q X (k r) m) → wp Γ Q X (onBool x' k) m)
    (hBi : ∀ n, target.supportsTy (.bits n) = true → ∀ x' x k m,
      x'.val = x.setWidth (target.widenWidth n) →
      onBi n x (fun res => ∀ r, r.val = res.setWidth (target.widenWidth n) → wp Γ Q X (k r) m) →
      wp Γ Q X (onBits n x' k) m)
    (hF : ∀ (f : Fmt), target.supportsTy (.float f) = true → ∀ x' x k m, x'.val = x →
      onF f x (fun res => ∀ r, r.val = res → wp Γ Q X (k r) m) → wp Γ Q X (onFloat f x' k) m)
    (hB_m : ∀ x {p q : Bool → Prop}, (∀ r, p r → q r) → onB x p → onB x q)
    (hBi_m : ∀ n x {p q : BitVec n → Prop}, (∀ r, p r → q r) → onBi n x p → onBi n x q)
    (hF_m : ∀ (f : Fmt) x {p q : BitVec f.width → Prop}, (∀ r, p r → q r) → onF f x p → onF f x q) :
    ∀ (u : Ty), target.supportsTy u = true →
      ∀ (fx : Tup (Arg Val) (target.leafTys u)) (x : Val u), valsTup fx = leafVals target u x →
        ∀ (k : Tup (Arg Val) (target.leafTys u) → Expr Val Cont rs) (m : Mem 64),
          TreeRel1 onB onBi onF u x (fun res =>
            ∀ fres, valsTup fres = leafVals target u res → wp Γ Q X (k fres) m) →
          wp Γ Q X (legalUnaryTree.goS target onBool onBits onFloat u fx k) m
  | .bool, _, (x', ()), x, hx, k, m, hk =>
    hB x' x (fun r => k (r, ())) m (congrArg Prod.fst hx)
      (hB_m x (fun res hr r hrv => hr (r, ()) (congrArg (·, ()) hrv)) hk)
  | .bits n, ht, (x', ()), x, hx, k, m, hk =>
    hBi n ht x' x (fun r => k (r, ())) m (congrArg Prod.fst hx)
      (hBi_m n x (fun res hr r hrv => hr (r, ()) (congrArg (·, ()) hrv)) hk)
  | .float f, ht, (x', ()), x, hx, k, m, hk =>
    hF f ht x' x (fun r => k (r, ())) m (congrArg Prod.fst hx)
      (hF_m f x (fun res hr r hrv => hr (r, ()) (congrArg (·, ()) hrv)) hk)
  | .pair u1 u2, ht, fx, x, hx, k, m, hk => by
    simp only [LegalTarget.supportsTy, Bool.and_eq_true] at ht
    dsimp only [LegalTarget.leafTys] at fx hx
    dsimp only [legalUnaryTree.goS]
    have h12 := congrArg (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2)) hx
    rw [leafVals_pair, tupSplit_tupAppend, tupSplit_valsTup] at h12
    refine legalUnaryTree_goS_wp target onBool onBits onFloat hB hBi hF hB_m hBi_m hF_m u1 ht.1
      (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2) fx).1 x.1
      (congrArg Prod.fst h12) _ m ?_
    refine TreeRel1.mono hB_m hBi_m hF_m (fun r1 hr1 fres1 hres1 => ?_) hk
    refine legalUnaryTree_goS_wp target onBool onBits onFloat hB hBi hF hB_m hBi_m hF_m u2 ht.2
      (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2) fx).2 x.2
      (congrArg Prod.snd h12) _ m ?_
    refine TreeRel1.mono hB_m hBi_m hF_m (fun r2 hr2 fres2 hres2 => ?_) hr1
    exact hr2 (tupAppend fres1 fres2) (by
      dsimp only [LegalTarget.leafTys]
      rw [leafVals_pair, valsTup_tupAppend, hres1, hres2])

private theorem legalUnaryTree_wp (target : LegalTarget) {Γ : Env} {rs : List Ty}
    {Q : Post rs} {X : XPost}
    (mkCode : (u : Ty) → OpCode [u] [u])
    (vecSupported : (u : Ty) → Bool)
    (onBool : Arg Val .bool → (Arg Val .bool → Expr Val Cont rs) → Expr Val Cont rs)
    (onBits : (n : Nat) → Arg Val (.bits (target.widenWidth n)) →
      (Arg Val (.bits (target.widenWidth n)) → Expr Val Cont rs) → Expr Val Cont rs)
    (onFloat : (f : Fmt) → Arg Val (.float f) →
      (Arg Val (.float f) → Expr Val Cont rs) → Expr Val Cont rs)
    {onB : Bool → (Bool → Prop) → Prop}
    {onBi : ∀ n, BitVec n → (BitVec n → Prop) → Prop}
    {onF : ∀ (f : Fmt), BitVec f.width → (BitVec f.width → Prop) → Prop}
    (hB : ∀ x' x k m, x'.val = x →
      onB x (fun res => ∀ r, r.val = res → wp Γ Q X (k r) m) → wp Γ Q X (onBool x' k) m)
    (hBi : ∀ n, target.supportsTy (.bits n) = true → ∀ x' x k m,
      x'.val = x.setWidth (target.widenWidth n) →
      onBi n x (fun res => ∀ r, r.val = res.setWidth (target.widenWidth n) → wp Γ Q X (k r) m) →
      wp Γ Q X (onBits n x' k) m)
    (hF : ∀ (f : Fmt), target.supportsTy (.float f) = true → ∀ x' x k m, x'.val = x →
      onF f x (fun res => ∀ r, r.val = res → wp Γ Q X (k r) m) → wp Γ Q X (onFloat f x' k) m)
    (hVec : ∀ u, target.keepsPacked u = true → vecSupported u = true → target.supportsTy u = true →
      ∀ x (p : Val u → Prop), TreeRel1 onB onBi onF u x p →
        OpCode.wp (mkCode u) (x, ()) (fun (res, ()) => p res))
    (hB_m : ∀ x {p q : Bool → Prop}, (∀ r, p r → q r) → onB x p → onB x q)
    (hBi_m : ∀ n x {p q : BitVec n → Prop}, (∀ r, p r → q r) → onBi n x p → onBi n x q)
    (hF_m : ∀ (f : Fmt) x {p q : BitVec f.width → Prop}, (∀ r, p r → q r) → onF f x p → onF f x q) :
    ∀ (t : Ty), target.supportsTy t = true → (xs : Tup (Arg Val) (target.legalTys t)) →
      (x : Val t) → valsTup xs = encodeVal target t x →
      (k : Tup (Arg Val) (target.legalTys t) → Expr Val Cont rs) → (m : Mem 64) →
      TreeRel1 onB onBi onF t x (fun res =>
        ∀ fres, valsTup fres = encodeVal target t res → wp Γ Q X (k fres) m) →
      wp Γ Q X (legalUnaryTree target mkCode vecSupported onBool onBits onFloat t xs k) m
  | .bool, _, (x', ()), x, hx, k, m, hk =>
    hB x' x (fun r => k (r, ())) m (congrArg Prod.fst hx)
      (hB_m x (fun res hr r hrv => hr (r, ()) (congrArg (·, ()) hrv)) hk)
  | .bits n, ht, (x', ()), x, hx, k, m, hk =>
    hBi n ht x' x (fun r => k (r, ())) m (congrArg Prod.fst hx)
      (hBi_m n x (fun res hr r hrv => hr (r, ()) (congrArg (·, ()) hrv)) hk)
  | .float f, ht, (x', ()), x, hx, k, m, hk =>
    hF f ht x' x (fun r => k (r, ())) m (congrArg Prod.fst hx)
      (hF_m f x (fun res hr r hrv => hr (r, ()) (congrArg (·, ()) hrv)) hk)
  | .pair t1 t2, ht, xs, p, hxs, k, m, hk => by
    simp only [LegalTarget.supportsTy, Bool.and_eq_true] at ht
    dsimp only [legalUnaryTree]
    split
    · next hp =>
      have hxt := congrArg Prod.fst (valsTup_packedToTup_encode target hp hxs)
      simp only [valsTup, Tup.map] at hxt
      by_cases hvs : vecSupported (.pair t1 t2) = true
      · rw [ite_eq_left hvs]
        dsimp only [wp, Op.wp, vals, op1]
        rw [hxt]
        exact OpCode.wp_mono (mkCode (.pair t1 t2)) (p, ())
          (fun (res, ()) hres =>
            hres (tupToPacked hp (.var res, ()))
              (valsTup_tupToPacked_encode target hp (by rw [valsTup_single]; rfl)))
          (hVec (.pair t1 t2) hp hvs (by simp [LegalTarget.supportsTy, ht]) p _ hk)
      · rw [ite_eq_right hvs]
        refine splitLegalToLeaves_wp target (.pair t1 t2) (by simp [LegalTarget.supportsTy, ht]) xs p hxs fun fx hfx => ?_
        refine legalUnaryTree_goS_wp target onBool onBits onFloat hB hBi hF hB_m hBi_m hF_m (.pair t1 t2)
          (by simp [LegalTarget.supportsTy, ht]) fx p hfx _ m ?_
        refine TreeRel1.mono hB_m hBi_m hF_m (fun res hres fres hfres => ?_) hk
        exact packLeavesToLegal_wp target (.pair t1 t2) (by simp [LegalTarget.supportsTy, ht]) fres res hfres hres
    · next hp =>
      have hf := Bool.eq_false_iff.mpr hp
      have hsp := valsTup_splitToTup_encode target hf hxs
      have h12 := congrArg tupSplit hsp
      simp only [tupSplit_valsTup, tupSplit_tupAppend] at h12
      refine legalUnaryTree_wp target mkCode vecSupported onBool onBits onFloat
        hB hBi hF hVec hB_m hBi_m hF_m t1 ht.1 (tupSplit (splitToTup hf xs)).1 p.1
        (congrArg Prod.fst h12) _ m ?_
      refine TreeRel1.mono hB_m hBi_m hF_m (fun r1 hr1 res1 hres1 => ?_) hk
      refine legalUnaryTree_wp target mkCode vecSupported onBool onBits onFloat
        hB hBi hF hVec hB_m hBi_m hF_m t2 ht.2 (tupSplit (splitToTup hf xs)).2 p.2
        (congrArg Prod.snd h12) _ m ?_
      refine TreeRel1.mono hB_m hBi_m hF_m (fun r2 hr2 res2 hres2 => ?_) hr1
      exact hr2 (tupToSplit hf (tupAppend res1 res2))
        (valsTup_tupToSplit_encode target hf (by rw [valsTup_tupAppend, hres1, hres2]))

private theorem treeRel1_bswap {onB : Bool → (Bool → Prop) → Prop}
    {onBi : ∀ n, BitVec n → (BitVec n → Prop) → Prop}
    {onF : ∀ (f : Fmt), BitVec f.width → (BitVec f.width → Prop) → Prop}
    (hBi : ∀ n (a : BitVec n) (p : BitVec n → Prop), n % 8 = 0 → p (bswapBits a) → onBi n a p) :
    ∀ (u : Ty), u.bswapOk = true → ∀ (x : Val u) (p : Val u → Prop),
      p (lift1 bswapBits id u x) → TreeRel1 onB onBi onF u x p
  | .bool, hu, _, _, _ => by simp [Ty.bswapOk] at hu
  | .float _, hu, _, _, _ => by simp [Ty.bswapOk] at hu
  | .bits n, hu, x, p, hp => hBi n x p (beq_iff_eq.mp (by simpa [Ty.bswapOk] using hu)) hp
  | .pair a b, hu, (x1, x2), p, hp => by
    simp only [Ty.bswapOk, Bool.and_eq_true] at hu
    exact treeRel1_bswap hBi a hu.1 x1 _ (treeRel1_bswap hBi b hu.2 x2 _ hp)

private theorem legalBswapTree_wp (target : LegalTarget) (hv : target.valid = true)
    {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (t : Ty) (ht : target.supportsTy t = true) (hb : t.bswapOk = true)
    (xs : Tup (Arg Val) (target.legalTys t)) (x : Val t) (hxs : valsTup xs = encodeVal target t x)
    {k : Tup (Arg Val) (target.legalTys t) → Expr Val Cont rs} {m : Mem 64}
    (hk : ∀ res, valsTup res = encodeVal target t (lift1 bswapBits id t x) → wp Γ Q X (k res) m) :
    wp Γ Q X (legalBswapTree target t xs k) m := by
  dsimp only [legalBswapTree]
  simp only [show (!t.bswapOk) = false by simp [hb], Bool.false_eq_true, ↓reduceIte]
  let onB := fun (_ : Bool) (_ : Bool → Prop) => False
  let onBi := fun (n : Nat) (a : BitVec n) (post : BitVec n → Prop) =>
    n % 8 = 0 ∧ post (bswapBits a)
  let onF := fun (f : Fmt) (_ : BitVec f.width) (_ : BitVec f.width → Prop) => False
  have hB : ∀ (x' : Arg Val .bool) (x : Bool) (k : Arg Val .bool → Expr Val Cont rs) (m : Mem 64), x'.val = x →
      onB x (fun res => ∀ (r : Arg Val .bool), r.val = res → wp Γ Q X (k r) m) → wp Γ Q X (.hlt) m :=
    fun _ _ _ _ _ h => False.elim h
  have hBi : ∀ (n : Nat), target.supportsTy (.bits n) = true →
      ∀ (x' : Arg Val (.bits (target.widenWidth n))) (x : BitVec n)
        (k : Arg Val (.bits (target.widenWidth n)) → Expr Val Cont rs) (m : Mem 64),
      x'.val = x.setWidth (target.widenWidth n) →
      onBi n x (fun res => ∀ (r : Arg Val (.bits (target.widenWidth n))),
        r.val = res.setWidth (target.widenWidth n) → wp Γ Q X (k r) m) →
      wp Γ Q X (
        if n == 0 then k (.imm 0#(target.widenWidth n))
        else if n == 8 then k x'
        else if n == target.widenWidth n then
          .let_ (op1 (.bswap (.bits (target.widenWidth n))) x') fun bw => k (.var bw.1)
        else if target.widenWidth n % 8 == 0 then
          .let_ (op1 (.bswap (.bits (target.widenWidth n))) x') fun bw =>
          .let_ (op2 (.lshr (.bits (target.widenWidth n))) (.var bw.1)
            (.imm (BitVec.ofNat (target.widenWidth n) (target.widenWidth n - n)))) fun r =>
          k (.var r.1)
        else .hlt) m := by
    intro n hsn x' a k' m' hax ⟨hn8, hk'⟩
    have hnw := le_widenWidth_of_supports hsn
    have hwSpec := valid_bitWidth_spec hv (widenWidth_mem_of_supports hsn)
    by_cases hn0 : n = 0
    · subst hn0
      simp only [beq_self_eq_true, ↓reduceIte]
      have ha0 : a = 0#0 := bitVec0_eq_zero a
      subst ha0
      exact hk' _ (by rw [bitVec0_eq_zero (bswapBits 0#0), BitVec.setWidth_zero]; rfl)
    · have hn0pos : 0 < n := Nat.pos_of_ne_zero hn0
      have hn0f : (n == 0) = false := beq_false_of_ne hn0
      simp only [hn0f, Bool.false_eq_true, ↓reduceIte]
      by_cases hn8eq : n = 8
      · subst hn8eq
        simp only [beq_self_eq_true, ↓reduceIte]
        exact hk' x' (by rw [hax, bswapBits_8])
      · have hn8f : (n == 8) = false := beq_false_of_ne hn8eq
        simp only [hn8f, Bool.false_eq_true, ↓reduceIte]
        by_cases heq : n = target.widenWidth n
        · have hbeq : (n == target.widenWidth n) = true := beq_iff_eq.mpr heq
          simp only [hbeq, ↓reduceIte, wp, Op.wp, OpCode.wp, op1, vals, lift1, Ty.bswapOk]
          have hw8t : (target.widenWidth n % 8 == 0) = true := beq_iff_eq.mpr hwSpec.2.1
          simp only [hw8t, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          revert x' a k' hax hk'
          rw [← heq]
          intro x' a k' hax hk'
          rw [BitVec.setWidth_eq] at hax hk'
          exact hk' _ (by change bswapBits x'.val = _; rw [hax])
        · have hlt : n < target.widenWidth n := Nat.lt_of_le_of_ne hnw heq
          have hneqf : (n == target.widenWidth n) = false := beq_false_of_ne heq
          have hw8t : (target.widenWidth n % 8 == 0) = true := beq_iff_eq.mpr hwSpec.2.1
          simp only [hneqf, Bool.false_eq_true, ↓reduceIte, hw8t, wp, Op.wp, OpCode.wp, op1, op2,
            vals, lift1, lift2, Ty.bswapOk, Bool.not_true]
          have hpow : target.widenWidth n < 2 ^ target.widenWidth n :=
            @Nat.lt_pow_self (target.widenWidth n) 2 (by decide)
          have hsub_lt : target.widenWidth n - n < 2 ^ target.widenWidth n :=
            Nat.lt_of_le_of_lt (Nat.sub_le _ _) hpow
          have hsh : (BitVec.ofNat (target.widenWidth n) (target.widenWidth n - n)).toNat %
              target.widenWidth n = target.widenWidth n - n := by
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsub_lt, Nat.mod_eq_of_lt (by omega)]
          exact hk' _ (by
            change (bswapBits x'.val) >>> ((BitVec.ofNat (target.widenWidth n)
              (target.widenWidth n - n)).toNat % target.widenWidth n) = _
            rw [hax, hsh, setWidth_bswap_of_lt hn0pos hlt hn8 hwSpec.2.1])
  have hF : ∀ (f : Fmt), target.supportsTy (.float f) = true →
      ∀ (x' : Arg Val (.float f)) (x : BitVec f.width)
        (k : Arg Val (.float f) → Expr Val Cont rs) (m : Mem 64), x'.val = x →
      onF f x (fun res => ∀ (r : Arg Val (.float f)), r.val = res → wp Γ Q X (k r) m) → wp Γ Q X (.hlt) m :=
    fun _ _ _ _ _ _ _ h => False.elim h
  have hVec : ∀ u, target.keepsPacked u = true → false = true → target.supportsTy u = true →
      ∀ x (p : Val u → Prop), TreeRel1 onB onBi onF u x p →
        OpCode.wp (.bswap u) (x, ()) (fun (res, ()) => p res) :=
    fun _ _ hc => by cases hc
  exact legalUnaryTree_wp target .bswap (fun _ => false) (fun _ _ => .hlt)
    (fun n x cont =>
      if n == 0 then cont (.imm 0#(target.widenWidth n))
      else if n == 8 then cont x
      else if n == target.widenWidth n then
        .let_ (op1 (.bswap (.bits (target.widenWidth n))) x) fun bw => cont (.var bw.1)
      else if target.widenWidth n % 8 == 0 then
        .let_ (op1 (.bswap (.bits (target.widenWidth n))) x) fun bw =>
        .let_ (op2 (.lshr (.bits (target.widenWidth n))) (.var bw.1)
          (.imm (BitVec.ofNat (target.widenWidth n) (target.widenWidth n - n)))) fun r =>
        cont (.var r.1)
      else .hlt)
    (fun _ _ _ => .hlt)
    hB hBi hF hVec (fun _ _ _ _ h => False.elim h) (fun n _ _ _ h1 h2 => ⟨h2.1, h1 _ h2.2⟩)
    (fun _ _ _ _ _ h => False.elim h)
    t ht xs x hxs k m
    (treeRel1_bswap (fun _ _ _ hn8 hp => ⟨hn8, hp⟩) t hb x _ hk)

private theorem legalTernaryTree_goS_wp (target : LegalTarget) {Γ : Env} {rs : List Ty}
    {Q : Post rs} {X : XPost}
    (onBool : Arg Val .bool → Arg Val .bool → Arg Val .bool →
      (Arg Val .bool → Expr Val Cont rs) → Expr Val Cont rs)
    (onBits : (n : Nat) → Arg Val (.bits (target.widenWidth n)) → Arg Val (.bits (target.widenWidth n)) →
      Arg Val (.bits (target.widenWidth n)) →
      (Arg Val (.bits (target.widenWidth n)) → Expr Val Cont rs) → Expr Val Cont rs)
    (onFloat : (f : Fmt) → Arg Val (.float f) → Arg Val (.float f) → Arg Val (.float f) →
      (Arg Val (.float f) → Expr Val Cont rs) → Expr Val Cont rs)
    {onB : Bool → Bool → Bool → (Bool → Prop) → Prop}
    {onBi : ∀ n, BitVec n → BitVec n → BitVec n → (BitVec n → Prop) → Prop}
    {onF : ∀ (f : Fmt), BitVec f.width → BitVec f.width → BitVec f.width → (BitVec f.width → Prop) → Prop}
    (hB : ∀ a' b' c' a b c k m, a'.val = a → b'.val = b → c'.val = c →
      onB a b c (fun res => ∀ r, r.val = res → wp Γ Q X (k r) m) →
      wp Γ Q X (onBool a' b' c' k) m)
    (hBi : ∀ n, target.supportsTy (.bits n) = true → ∀ a' b' c' a b c k m,
      a'.val = a.setWidth (target.widenWidth n) → b'.val = b.setWidth (target.widenWidth n) →
      c'.val = c.setWidth (target.widenWidth n) →
      onBi n a b c (fun res => ∀ r, r.val = res.setWidth (target.widenWidth n) → wp Γ Q X (k r) m) →
      wp Γ Q X (onBits n a' b' c' k) m)
    (hF : ∀ (f : Fmt), target.supportsTy (.float f) = true → ∀ a' b' c' a b c k m,
      a'.val = a → b'.val = b → c'.val = c →
      onF f a b c (fun res => ∀ r, r.val = res → wp Γ Q X (k r) m) →
      wp Γ Q X (onFloat f a' b' c' k) m)
    (hB_m : ∀ x y z {p q : Bool → Prop}, (∀ r, p r → q r) → onB x y z p → onB x y z q)
    (hBi_m : ∀ n x y z {p q : BitVec n → Prop}, (∀ r, p r → q r) → onBi n x y z p → onBi n x y z q)
    (hF_m : ∀ (f : Fmt) x y z {p q : BitVec f.width → Prop}, (∀ r, p r → q r) → onF f x y z p → onF f x y z q) :
    ∀ (u : Ty), target.supportsTy u = true →
      ∀ (fx fy fz : Tup (Arg Val) (target.leafTys u)) (x y z : Val u),
        valsTup fx = leafVals target u x → valsTup fy = leafVals target u y →
        valsTup fz = leafVals target u z →
        ∀ (k : Tup (Arg Val) (target.leafTys u) → Expr Val Cont rs) (m : Mem 64),
          TreeRel3 onB onBi onF u x y z (fun res =>
            ∀ fres, valsTup fres = leafVals target u res → wp Γ Q X (k fres) m) →
          wp Γ Q X (legalTernaryTree.goS target onBool onBits onFloat u fx fy fz k) m
  | .bool, _, (a', ()), (b', ()), (c', ()), a, b, c, ha, hb, hc, k, m, hk =>
    hB a' b' c' a b c (fun r => k (r, ())) m
      (congrArg Prod.fst ha) (congrArg Prod.fst hb) (congrArg Prod.fst hc)
      (hB_m a b c (fun res hr r hrv => hr (r, ()) (congrArg (·, ()) hrv)) hk)
  | .bits n, ht, (a', ()), (b', ()), (c', ()), a, b, c, ha, hb, hc, k, m, hk =>
    hBi n ht a' b' c' a b c (fun r => k (r, ())) m
      (congrArg Prod.fst ha) (congrArg Prod.fst hb) (congrArg Prod.fst hc)
      (hBi_m n a b c (fun res hr r hrv => hr (r, ()) (congrArg (·, ()) hrv)) hk)
  | .float f, ht, (a', ()), (b', ()), (c', ()), a, b, c, ha, hb, hc, k, m, hk =>
    hF f ht a' b' c' a b c (fun r => k (r, ())) m
      (congrArg Prod.fst ha) (congrArg Prod.fst hb) (congrArg Prod.fst hc)
      (hF_m f a b c (fun res hr r hrv => hr (r, ()) (congrArg (·, ()) hrv)) hk)
  | .pair u1 u2, ht, fx, fy, fz, x, y, z, hx, hy, hz, k, m, hk => by
    simp only [LegalTarget.supportsTy, Bool.and_eq_true] at ht
    dsimp only [LegalTarget.leafTys] at fx fy fz hx hy hz
    dsimp only [legalTernaryTree.goS]
    have hx12 := congrArg (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2)) hx
    have hy12 := congrArg (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2)) hy
    have hz12 := congrArg (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2)) hz
    rw [leafVals_pair, tupSplit_tupAppend, tupSplit_valsTup] at hx12 hy12 hz12
    refine legalTernaryTree_goS_wp target onBool onBits onFloat hB hBi hF hB_m hBi_m hF_m u1 ht.1
      (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2) fx).1
      (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2) fy).1
      (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2) fz).1
      x.1 y.1 z.1 (congrArg Prod.fst hx12) (congrArg Prod.fst hy12) (congrArg Prod.fst hz12) _ m ?_
    refine TreeRel3.mono hB_m hBi_m hF_m (fun r1 hr1 fres1 hres1 => ?_) hk
    refine legalTernaryTree_goS_wp target onBool onBits onFloat hB hBi hF hB_m hBi_m hF_m u2 ht.2
      (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2) fx).2
      (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2) fy).2
      (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2) fz).2
      x.2 y.2 z.2 (congrArg Prod.snd hx12) (congrArg Prod.snd hy12) (congrArg Prod.snd hz12) _ m ?_
    refine TreeRel3.mono hB_m hBi_m hF_m (fun r2 hr2 fres2 hres2 => ?_) hr1
    exact hr2 (tupAppend fres1 fres2) (by
      dsimp only [LegalTarget.leafTys]
      rw [leafVals_pair, valsTup_tupAppend, hres1, hres2])

private theorem legalTernaryTree_wp (target : LegalTarget) {Γ : Env} {rs : List Ty}
    {Q : Post rs} {X : XPost}
    (mkCode : (u : Ty) → OpCode [u, u, u] [u])
    (vecSupported : (u : Ty) → Bool)
    (onBool : Arg Val .bool → Arg Val .bool → Arg Val .bool →
      (Arg Val .bool → Expr Val Cont rs) → Expr Val Cont rs)
    (onBits : (n : Nat) → Arg Val (.bits (target.widenWidth n)) → Arg Val (.bits (target.widenWidth n)) →
      Arg Val (.bits (target.widenWidth n)) →
      (Arg Val (.bits (target.widenWidth n)) → Expr Val Cont rs) → Expr Val Cont rs)
    (onFloat : (f : Fmt) → Arg Val (.float f) → Arg Val (.float f) → Arg Val (.float f) →
      (Arg Val (.float f) → Expr Val Cont rs) → Expr Val Cont rs)
    {onB : Bool → Bool → Bool → (Bool → Prop) → Prop}
    {onBi : ∀ n, BitVec n → BitVec n → BitVec n → (BitVec n → Prop) → Prop}
    {onF : ∀ (f : Fmt), BitVec f.width → BitVec f.width → BitVec f.width → (BitVec f.width → Prop) → Prop}
    (hB : ∀ a' b' c' a b c k m, a'.val = a → b'.val = b → c'.val = c →
      onB a b c (fun res => ∀ r, r.val = res → wp Γ Q X (k r) m) →
      wp Γ Q X (onBool a' b' c' k) m)
    (hBi : ∀ n, target.supportsTy (.bits n) = true → ∀ a' b' c' a b c k m,
      a'.val = a.setWidth (target.widenWidth n) → b'.val = b.setWidth (target.widenWidth n) →
      c'.val = c.setWidth (target.widenWidth n) →
      onBi n a b c (fun res => ∀ r, r.val = res.setWidth (target.widenWidth n) → wp Γ Q X (k r) m) →
      wp Γ Q X (onBits n a' b' c' k) m)
    (hF : ∀ (f : Fmt), target.supportsTy (.float f) = true → ∀ a' b' c' a b c k m,
      a'.val = a → b'.val = b → c'.val = c →
      onF f a b c (fun res => ∀ r, r.val = res → wp Γ Q X (k r) m) →
      wp Γ Q X (onFloat f a' b' c' k) m)
    (hVec : ∀ u, target.keepsPacked u = true → vecSupported u = true → target.supportsTy u = true →
      ∀ x y z (p : Val u → Prop), TreeRel3 onB onBi onF u x y z p →
        OpCode.wp (mkCode u) (x, y, z, ()) (fun (res, ()) => p res))
    (hB_m : ∀ x y z {p q : Bool → Prop}, (∀ r, p r → q r) → onB x y z p → onB x y z q)
    (hBi_m : ∀ n x y z {p q : BitVec n → Prop}, (∀ r, p r → q r) → onBi n x y z p → onBi n x y z q)
    (hF_m : ∀ (f : Fmt) x y z {p q : BitVec f.width → Prop}, (∀ r, p r → q r) → onF f x y z p → onF f x y z q) :
    ∀ (t : Ty), target.supportsTy t = true →
      (xs ys zs : Tup (Arg Val) (target.legalTys t)) → (x y z : Val t) →
      valsTup xs = encodeVal target t x → valsTup ys = encodeVal target t y →
      valsTup zs = encodeVal target t z →
      (k : Tup (Arg Val) (target.legalTys t) → Expr Val Cont rs) → (m : Mem 64) →
      TreeRel3 onB onBi onF t x y z (fun res =>
        ∀ fres, valsTup fres = encodeVal target t res → wp Γ Q X (k fres) m) →
      wp Γ Q X (legalTernaryTree target mkCode vecSupported onBool onBits onFloat t xs ys zs k) m
  | .bool, _, (a', ()), (b', ()), (c', ()), a, b, c, ha, hb, hc, k, m, hk =>
    hB a' b' c' a b c (fun r => k (r, ())) m
      (congrArg Prod.fst ha) (congrArg Prod.fst hb) (congrArg Prod.fst hc)
      (hB_m a b c (fun res hr r hrv => hr (r, ()) (congrArg (·, ()) hrv)) hk)
  | .bits n, ht, (a', ()), (b', ()), (c', ()), a, b, c, ha, hb, hc, k, m, hk =>
    hBi n ht a' b' c' a b c (fun r => k (r, ())) m
      (congrArg Prod.fst ha) (congrArg Prod.fst hb) (congrArg Prod.fst hc)
      (hBi_m n a b c (fun res hr r hrv => hr (r, ()) (congrArg (·, ()) hrv)) hk)
  | .float f, ht, (a', ()), (b', ()), (c', ()), a, b, c, ha, hb, hc, k, m, hk =>
    hF f ht a' b' c' a b c (fun r => k (r, ())) m
      (congrArg Prod.fst ha) (congrArg Prod.fst hb) (congrArg Prod.fst hc)
      (hF_m f a b c (fun res hr r hrv => hr (r, ()) (congrArg (·, ()) hrv)) hk)
  | .pair t1 t2, ht, xs, ys, zs, px, py, pz, hxs, hys, hzs, k, m, hk => by
    simp only [LegalTarget.supportsTy, Bool.and_eq_true] at ht
    dsimp only [legalTernaryTree]
    split
    · next hp =>
      have hxt := congrArg Prod.fst (valsTup_packedToTup_encode target hp hxs)
      have hyt := congrArg Prod.fst (valsTup_packedToTup_encode target hp hys)
      have hzt := congrArg Prod.fst (valsTup_packedToTup_encode target hp hzs)
      simp only [valsTup, Tup.map] at hxt hyt hzt
      by_cases hvs : vecSupported (.pair t1 t2) = true
      · rw [ite_eq_left hvs]
        dsimp only [wp, Op.wp, vals, op3]
        rw [hxt, hyt, hzt]
        exact OpCode.wp_mono (mkCode (.pair t1 t2)) (px, py, pz, ())
          (fun (res, ()) hres =>
            hres (tupToPacked hp (.var res, ()))
              (valsTup_tupToPacked_encode target hp (by rw [valsTup_single]; rfl)))
          (hVec (.pair t1 t2) hp hvs (by simp [LegalTarget.supportsTy, ht]) px py pz _ hk)
      · rw [ite_eq_right hvs]
        refine splitLegalToLeaves_wp target (.pair t1 t2) (by simp [LegalTarget.supportsTy, ht]) xs px hxs fun fx hfx =>
          splitLegalToLeaves_wp target (.pair t1 t2) (by simp [LegalTarget.supportsTy, ht]) ys py hys fun fy hfy =>
          splitLegalToLeaves_wp target (.pair t1 t2) (by simp [LegalTarget.supportsTy, ht]) zs pz hzs fun fz hfz => ?_
        refine legalTernaryTree_goS_wp target onBool onBits onFloat hB hBi hF hB_m hBi_m hF_m
          (.pair t1 t2) (by simp [LegalTarget.supportsTy, ht]) fx fy fz px py pz hfx hfy hfz _ m ?_
        refine TreeRel3.mono hB_m hBi_m hF_m (fun res hres fres hfres => ?_) hk
        exact packLeavesToLegal_wp target (.pair t1 t2) (by simp [LegalTarget.supportsTy, ht]) fres res hfres hres
    · next hp =>
      have hf := Bool.eq_false_iff.mpr hp
      have hx12 := congrArg tupSplit (valsTup_splitToTup_encode target hf hxs)
      have hy12 := congrArg tupSplit (valsTup_splitToTup_encode target hf hys)
      have hz12 := congrArg tupSplit (valsTup_splitToTup_encode target hf hzs)
      simp only [tupSplit_valsTup, tupSplit_tupAppend] at hx12 hy12 hz12
      refine legalTernaryTree_wp target mkCode vecSupported onBool onBits onFloat
        hB hBi hF hVec hB_m hBi_m hF_m t1 ht.1
        (tupSplit (splitToTup hf xs)).1 (tupSplit (splitToTup hf ys)).1 (tupSplit (splitToTup hf zs)).1
        px.1 py.1 pz.1 (congrArg Prod.fst hx12) (congrArg Prod.fst hy12) (congrArg Prod.fst hz12) _ m ?_
      refine TreeRel3.mono hB_m hBi_m hF_m (fun r1 hr1 res1 hres1 => ?_) hk
      refine legalTernaryTree_wp target mkCode vecSupported onBool onBits onFloat
        hB hBi hF hVec hB_m hBi_m hF_m t2 ht.2
        (tupSplit (splitToTup hf xs)).2 (tupSplit (splitToTup hf ys)).2 (tupSplit (splitToTup hf zs)).2
        px.2 py.2 pz.2 (congrArg Prod.snd hx12) (congrArg Prod.snd hy12) (congrArg Prod.snd hz12) _ m ?_
      refine TreeRel3.mono hB_m hBi_m hF_m (fun r2 hr2 res2 hres2 => ?_) hr1
      exact hr2 (tupToSplit hf (tupAppend res1 res2))
        (valsTup_tupToSplit_encode target hf (by rw [valsTup_tupAppend, hres1, hres2]))

private theorem legalBinTree_goS_wp (target : LegalTarget) {Γ : Env} {rs : List Ty}
    {Q : Post rs} {X : XPost}
    (onBool : Arg Val .bool → Arg Val .bool → (Arg Val .bool → Expr Val Cont rs) → Expr Val Cont rs)
    (onBits : (n : Nat) → Arg Val (.bits (target.widenWidth n)) → Arg Val (.bits (target.widenWidth n)) →
      (Arg Val (.bits (target.widenWidth n)) → Expr Val Cont rs) → Expr Val Cont rs)
    (onFloat : (f : Fmt) → Arg Val (.float f) → Arg Val (.float f) →
      (Arg Val (.float f) → Expr Val Cont rs) → Expr Val Cont rs)
    {onB : Bool → Bool → (Bool → Prop) → Prop}
    {onBi : ∀ n, BitVec n → BitVec n → (BitVec n → Prop) → Prop}
    {onF : ∀ (f : Fmt), BitVec f.width → BitVec f.width → (BitVec f.width → Prop) → Prop}
    (hB : ∀ a' b' a b k m, a'.val = a → b'.val = b →
      onB a b (fun res => ∀ r, r.val = res → wp Γ Q X (k r) m) → wp Γ Q X (onBool a' b' k) m)
    (hBi : ∀ n, target.supportsTy (.bits n) = true → ∀ a' b' a b k m,
      a'.val = a.setWidth (target.widenWidth n) → b'.val = b.setWidth (target.widenWidth n) →
      onBi n a b (fun res => ∀ r, r.val = res.setWidth (target.widenWidth n) → wp Γ Q X (k r) m) →
      wp Γ Q X (onBits n a' b' k) m)
    (hF : ∀ (f : Fmt), target.supportsTy (.float f) = true → ∀ a' b' a b k m, a'.val = a → b'.val = b →
      onF f a b (fun res => ∀ r, r.val = res → wp Γ Q X (k r) m) → wp Γ Q X (onFloat f a' b' k) m)
    (hB_m : ∀ x y {p q : Bool → Prop}, (∀ r, p r → q r) → onB x y p → onB x y q)
    (hBi_m : ∀ n x y {p q : BitVec n → Prop}, (∀ r, p r → q r) → onBi n x y p → onBi n x y q)
    (hF_m : ∀ (f : Fmt) x y {p q : BitVec f.width → Prop}, (∀ r, p r → q r) → onF f x y p → onF f x y q) :
    ∀ (u : Ty), target.supportsTy u = true →
      ∀ (fx fy : Tup (Arg Val) (target.leafTys u)) (x y : Val u),
        valsTup fx = leafVals target u x → valsTup fy = leafVals target u y →
        ∀ (k : Tup (Arg Val) (target.leafTys u) → Expr Val Cont rs) (m : Mem 64),
          TreeRel2 onB onBi onF u x y (fun res =>
            ∀ fres, valsTup fres = leafVals target u res → wp Γ Q X (k fres) m) →
          wp Γ Q X (legalBinTree.goS target onBool onBits onFloat u fx fy k) m
  | .bool, _, (a', ()), (b', ()), a, b, ha, hb, k, m, hk =>
    hB a' b' a b (fun r => k (r, ())) m (congrArg Prod.fst ha) (congrArg Prod.fst hb)
      (hB_m a b (fun res hr r hrv => hr (r, ()) (congrArg (·, ()) hrv)) hk)
  | .bits n, ht, (a', ()), (b', ()), a, b, ha, hb, k, m, hk =>
    hBi n ht a' b' a b (fun r => k (r, ())) m (congrArg Prod.fst ha) (congrArg Prod.fst hb)
      (hBi_m n a b (fun res hr r hrv => hr (r, ()) (congrArg (·, ()) hrv)) hk)
  | .float f, ht, (a', ()), (b', ()), a, b, ha, hb, k, m, hk =>
    hF f ht a' b' a b (fun r => k (r, ())) m (congrArg Prod.fst ha) (congrArg Prod.fst hb)
      (hF_m f a b (fun res hr r hrv => hr (r, ()) (congrArg (·, ()) hrv)) hk)
  | .pair u1 u2, ht, fx, fy, x, y, hx, hy, k, m, hk => by
    simp only [LegalTarget.supportsTy, Bool.and_eq_true] at ht
    dsimp only [LegalTarget.leafTys] at fx fy hx hy
    dsimp only [legalBinTree.goS]
    have hx12 := congrArg (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2)) hx
    have hy12 := congrArg (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2)) hy
    rw [leafVals_pair, tupSplit_tupAppend, tupSplit_valsTup] at hx12 hy12
    refine legalBinTree_goS_wp target onBool onBits onFloat hB hBi hF hB_m hBi_m hF_m u1 ht.1
      (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2) fx).1
      (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2) fy).1
      x.1 y.1 (congrArg Prod.fst hx12) (congrArg Prod.fst hy12) _ m ?_
    refine TreeRel2.mono hB_m hBi_m hF_m (fun r1 hr1 fres1 hres1 => ?_) hk
    refine legalBinTree_goS_wp target onBool onBits onFloat hB hBi hF hB_m hBi_m hF_m u2 ht.2
      (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2) fx).2
      (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2) fy).2
      x.2 y.2 (congrArg Prod.snd hx12) (congrArg Prod.snd hy12) _ m ?_
    refine TreeRel2.mono hB_m hBi_m hF_m (fun r2 hr2 fres2 hres2 => ?_) hr1
    exact hr2 (tupAppend fres1 fres2) (by
      dsimp only [LegalTarget.leafTys]
      rw [leafVals_pair, valsTup_tupAppend, hres1, hres2])

private theorem legalBinTree_wp (target : LegalTarget) {Γ : Env} {rs : List Ty}
    {Q : Post rs} {X : XPost}
    (mkCode : (u : Ty) → OpCode [u, u] [u])
    (vecSupported : (u : Ty) → Bool → Bool)
    (onBool : Arg Val .bool → Arg Val .bool → (Arg Val .bool → Expr Val Cont rs) → Expr Val Cont rs)
    (onBits : (n : Nat) → Arg Val (.bits (target.widenWidth n)) → Arg Val (.bits (target.widenWidth n)) →
      (Arg Val (.bits (target.widenWidth n)) → Expr Val Cont rs) → Expr Val Cont rs)
    (onFloat : (f : Fmt) → Arg Val (.float f) → Arg Val (.float f) →
      (Arg Val (.float f) → Expr Val Cont rs) → Expr Val Cont rs)
    (uniformImmRhs : (u : Ty) → Arg (LVar target Val) u → Bool)
    {onB : Bool → Bool → (Bool → Prop) → Prop}
    {onBi : ∀ n, BitVec n → BitVec n → (BitVec n → Prop) → Prop}
    {onF : ∀ (f : Fmt), BitVec f.width → BitVec f.width → (BitVec f.width → Prop) → Prop}
    (hB : ∀ a' b' a b k m, a'.val = a → b'.val = b →
      onB a b (fun res => ∀ r, r.val = res → wp Γ Q X (k r) m) → wp Γ Q X (onBool a' b' k) m)
    (hBi : ∀ n, target.supportsTy (.bits n) = true → ∀ a' b' a b k m,
      a'.val = a.setWidth (target.widenWidth n) → b'.val = b.setWidth (target.widenWidth n) →
      onBi n a b (fun res => ∀ r, r.val = res.setWidth (target.widenWidth n) → wp Γ Q X (k r) m) →
      wp Γ Q X (onBits n a' b' k) m)
    (hF : ∀ (f : Fmt), target.supportsTy (.float f) = true → ∀ a' b' a b k m, a'.val = a → b'.val = b →
      onF f a b (fun res => ∀ r, r.val = res → wp Γ Q X (k r) m) → wp Γ Q X (onFloat f a' b' k) m)
    (hVec : ∀ u unif, target.keepsPacked u = true → vecSupported u unif = true →
      target.supportsTy u = true → ∀ x y (p : Val u → Prop),
        TreeRel2 onB onBi onF u x y p → OpCode.wp (mkCode u) (x, y, ()) (fun (res, ()) => p res))
    (hRotl : ∀ u c w s, opShiftKind (mkCode u) = some true → uniformShiftLeaf? u c = some (w, s) →
      target.supportsTy u = true → ∀ x (p : Val u → Prop), TreeRel2 onB onBi onF u x c p →
        if s == 0 then p x
        else OpCode.wp (.rotr u) (x, splatBits w (BitVec.ofNat w (w - s)) u, ()) (fun (r, ()) => p r))
    (hShl : ∀ u c w s, opShiftKind (mkCode u) = some false → uniformShiftLeaf? u c = some (w, s) →
      target.supportsTy u = true → ∀ x (p : Val u → Prop), TreeRel2 onB onBi onF u x c p →
        if s == 0 then p x
        else OpCode.wp (.rotr u) (x, splatBits w (BitVec.ofNat w (w - s)) u, ()) (fun (rt, ()) =>
          OpCode.wp (.and u) (rt, splatBits w (BitVec.allOnes w <<< s) u, ()) (fun (r, ()) => p r)))
    (hB_m : ∀ x y {p q : Bool → Prop}, (∀ r, p r → q r) → onB x y p → onB x y q)
    (hBi_m : ∀ n x y {p q : BitVec n → Prop}, (∀ r, p r → q r) → onBi n x y p → onBi n x y q)
    (hF_m : ∀ f x y {p q : BitVec f.width → Prop}, (∀ r, p r → q r) → onF f x y p → onF f x y q) :
    ∀ (t : Ty), target.supportsTy t = true →
      (xs ys : Tup (Arg Val) (target.legalTys t)) → (rawRhs : Option (Arg (LVar target Val) t)) →
      (x y : Val t) → valsTup xs = encodeVal target t x → valsTup ys = encodeVal target t y →
      (∀ c, rawRhs = some (.imm c) → y = c) →
      (k : Tup (Arg Val) (target.legalTys t) → Expr Val Cont rs) → (m : Mem 64) →
      TreeRel2 onB onBi onF t x y (fun res =>
        ∀ fres, valsTup fres = encodeVal target t res → wp Γ Q X (k fres) m) →
      wp Γ Q X (legalBinTree target mkCode vecSupported onBool onBits onFloat uniformImmRhs t xs ys rawRhs k) m
  | .bool, _, (a', ()), (b', ()), _, a, b, ha, hb, _, k, m, hk =>
    hB a' b' a b (fun r => k (r, ())) m (congrArg Prod.fst ha) (congrArg Prod.fst hb)
      (hB_m a b (fun res hr r hrv => hr (r, ()) (congrArg (·, ()) hrv)) hk)
  | .bits n, ht, (a', ()), (b', ()), _, a, b, ha, hb, _, k, m, hk =>
    hBi n ht a' b' a b (fun r => k (r, ())) m (congrArg Prod.fst ha) (congrArg Prod.fst hb)
      (hBi_m n a b (fun res hr r hrv => hr (r, ()) (congrArg (·, ()) hrv)) hk)
  | .float f, ht, (a', ()), (b', ()), _, a, b, ha, hb, _, k, m, hk =>
    hF f ht a' b' a b (fun r => k (r, ())) m (congrArg Prod.fst ha) (congrArg Prod.fst hb)
      (hF_m f a b (fun res hr r hrv => hr (r, ()) (congrArg (·, ()) hrv)) hk)
  | .pair t1 t2, ht, xs, ys, rawRhs, px, py, hxs, hys, hraw, k, m, hk => by
    simp only [LegalTarget.supportsTy, Bool.and_eq_true] at ht
    have ht_pair : target.supportsTy (.pair t1 t2) = true := by simp [LegalTarget.supportsTy, ht]
    dsimp only [legalBinTree]
    split
    · next hp =>
      have hxt := congrArg Prod.fst (valsTup_packedToTup_encode target hp hxs)
      have hyt := congrArg Prod.fst (valsTup_packedToTup_encode target hp hys)
      simp only [valsTup, Tup.map] at hxt hyt
      have hscalar : wp Γ Q X (
          splitLegalToLeaves target (.pair t1 t2) xs fun fx =>
          splitLegalToLeaves target (.pair t1 t2) ys fun fy =>
          legalBinTree.goS target onBool onBits onFloat (.pair t1 t2) fx fy fun fres =>
            packLeavesToLegal target (.pair t1 t2) fres k) m := by
        refine splitLegalToLeaves_wp target (.pair t1 t2) ht_pair xs px hxs fun fx hfx =>
          splitLegalToLeaves_wp target (.pair t1 t2) ht_pair ys py hys fun fy hfy => ?_
        refine legalBinTree_goS_wp target onBool onBits onFloat hB hBi hF hB_m hBi_m hF_m
          (.pair t1 t2) ht_pair fx fy px py hfx hfy _ m ?_
        refine TreeRel2.mono hB_m hBi_m hF_m (fun res hres fres hfres => ?_) hk
        exact packLeavesToLegal_wp target (.pair t1 t2) ht_pair fres res hfres hres
      cases hrr : rawRhs with
      | none =>
        by_cases hvs : vecSupported (.pair t1 t2)
            (checkUniformImmShift (.pair t1 t2) (mkCode (.pair t1 t2)) (packedToTup hp ys).1) = true
        · simp only [hvs, ↓reduceIte, wp, Op.wp, vals, op2]
          rw [hxt, hyt]
          exact OpCode.wp_mono (mkCode (.pair t1 t2)) (px, py, ())
            (fun (res, ()) hres =>
              hres (tupToPacked hp (.var res, ()))
                (valsTup_tupToPacked_encode target hp (by rw [valsTup_single]; rfl)))
            (hVec (.pair t1 t2) _ hp hvs ht_pair px py _ hk)
        · have hvsf : vecSupported (.pair t1 t2)
              (checkUniformImmShift (.pair t1 t2) (mkCode (.pair t1 t2)) (packedToTup hp ys).1) = false :=
            Bool.eq_false_iff.mpr hvs
          simp only [hvsf, Bool.false_eq_true, ↓reduceIte]
          cases opShiftKind (mkCode (.pair t1 t2)) with
          | none => exact hscalar
          | some b => cases b <;> exact hscalar
      | some r =>
        by_cases hvs : vecSupported (.pair t1 t2)
            (checkUniformImmShift (.pair t1 t2) (mkCode (.pair t1 t2)) (packedToTup hp ys).1) = true
        · simp only [hvs, ↓reduceIte, wp, Op.wp, vals, op2]
          rw [hxt, hyt]
          exact OpCode.wp_mono (mkCode (.pair t1 t2)) (px, py, ())
            (fun (res, ()) hres =>
              hres (tupToPacked hp (.var res, ()))
                (valsTup_tupToPacked_encode target hp (by rw [valsTup_single]; rfl)))
            (hVec (.pair t1 t2) _ hp hvs ht_pair px py _ hk)
        · have hvsf : vecSupported (.pair t1 t2)
              (checkUniformImmShift (.pair t1 t2) (mkCode (.pair t1 t2)) (packedToTup hp ys).1) = false :=
            Bool.eq_false_iff.mpr hvs
          simp only [hvsf, Bool.false_eq_true, ↓reduceIte]
          cases hsk : opShiftKind (mkCode (.pair t1 t2)) with
          | none => exact hscalar
          | some b =>
            cases r with
            | var _ => cases b <;> exact hscalar
            | imm c =>
              have hpy : py = c := hraw c hrr
              subst hpy
              cases b with
              | true =>
                dsimp only
                cases hus : uniformShiftLeaf? (.pair t1 t2) py with
                | none => exact hscalar
                | some p =>
                  rcases p with ⟨w, s⟩
                  dsimp only
                  have hrl := hRotl (.pair t1 t2) py w s hsk hus ht_pair px _ hk
                  by_cases hs0 : (s == 0) = true
                  · rw [ite_eq_left hs0]
                    simp only [hs0, ↓reduceIte] at hrl
                    exact hrl (tupToPacked hp (packedToTup hp xs))
                      (valsTup_tupToPacked_encode target hp (valsTup_packedToTup_encode target hp hxs))
                  · rw [ite_eq_right hs0]
                    have hs0' : (s == 0) = false := Bool.eq_false_iff.mpr hs0
                    simp only [hs0', Bool.false_eq_true, ↓reduceIte] at hrl
                    by_cases hsup : target.vecIntOpSupported (.rotr (.pair t1 t2)) (.pair t1 t2) true = true
                    · rw [ite_eq_left hsup]
                      dsimp only [wp, Op.wp, vals, op2, Arg.val_imm]
                      rw [hxt]
                      exact OpCode.wp_mono (.rotr (.pair t1 t2)) _ (fun (r, ()) hr =>
                        hr (tupToPacked hp (.var r, ()))
                          (valsTup_tupToPacked_encode target hp (by rw [valsTup_single]; rfl))) hrl
                    · rw [ite_eq_right hsup]
                      exact hscalar
              | false =>
                dsimp only
                cases hus : uniformShiftLeaf? (.pair t1 t2) py with
                | none => exact hscalar
                | some p =>
                  rcases p with ⟨w, s⟩
                  dsimp only
                  have hsh := hShl (.pair t1 t2) py w s hsk hus ht_pair px _ hk
                  by_cases hs0 : (s == 0) = true
                  · rw [ite_eq_left hs0]
                    simp only [hs0, ↓reduceIte] at hsh
                    exact hsh (tupToPacked hp (packedToTup hp xs))
                      (valsTup_tupToPacked_encode target hp (valsTup_packedToTup_encode target hp hxs))
                  · rw [ite_eq_right hs0]
                    have hs0' : (s == 0) = false := Bool.eq_false_iff.mpr hs0
                    simp only [hs0', Bool.false_eq_true, ↓reduceIte] at hsh
                    by_cases hsup : (target.vecIntOpSupported (.rotr (.pair t1 t2)) (.pair t1 t2) true &&
                        target.vecIntOpSupported (.and (.pair t1 t2)) (.pair t1 t2) false) = true
                    · rw [ite_eq_left hsup]
                      dsimp only [wp, Op.wp, vals, op2, Arg.val_imm]
                      rw [hxt]
                      exact OpCode.wp_mono (.rotr (.pair t1 t2)) _ (fun (rt, ()) hrt =>
                        OpCode.wp_mono (.and (.pair t1 t2)) _ (fun (r, ()) hr =>
                          hr (tupToPacked hp (.var r, ()))
                            (valsTup_tupToPacked_encode target hp (by rw [valsTup_single]; rfl))) hrt) hsh
                    · rw [ite_eq_right hsup]
                      exact hscalar
    · next hp =>
      have hf := Bool.eq_false_iff.mpr hp
      have hx12 := congrArg tupSplit (valsTup_splitToTup_encode target hf hxs)
      have hy12 := congrArg tupSplit (valsTup_splitToTup_encode target hf hys)
      simp only [tupSplit_valsTup, tupSplit_tupAppend] at hx12 hy12
      refine legalBinTree_wp target mkCode vecSupported onBool onBits onFloat uniformImmRhs
        hB hBi hF hVec hRotl hShl hB_m hBi_m hF_m t1 ht.1
        (tupSplit (splitToTup hf xs)).1 (tupSplit (splitToTup hf ys)).1 none px.1 py.1
        (congrArg Prod.fst hx12) (congrArg Prod.fst hy12) (fun _ h => by cases h) _ m ?_
      refine TreeRel2.mono hB_m hBi_m hF_m (fun r1 hr1 res1 hres1 => ?_) hk
      refine legalBinTree_wp target mkCode vecSupported onBool onBits onFloat uniformImmRhs
        hB hBi hF hVec hRotl hShl hB_m hBi_m hF_m t2 ht.2
        (tupSplit (splitToTup hf xs)).2 (tupSplit (splitToTup hf ys)).2 none px.2 py.2
        (congrArg Prod.snd hx12) (congrArg Prod.snd hy12) (fun _ h => by cases h) _ m ?_
      refine TreeRel2.mono hB_m hBi_m hF_m (fun r2 hr2 res2 hres2 => ?_) hr1
      exact hr2 (tupToSplit hf (tupAppend res1 res2))
        (valsTup_tupToSplit_encode target hf (by rw [valsTup_tupAppend, hres1, hres2]))

private theorem legalCmpBits_wp (target : LegalTarget) {Γ : Env} {rs : List Ty}
    {Q : Post rs} {X : XPost} (o : CmpOp) {n : Nat} (hn : target.supportsTy (.bits n) = true)
    (a' b' : Arg Val (.bits (target.widenWidth n))) (a b : BitVec n)
    (ha : a'.val = a.setWidth (target.widenWidth n))
    (hb : b'.val = b.setWidth (target.widenWidth n))
    {k : Arg Val .bool → Expr Val Cont rs} {m : Mem 64}
    (hk : ∀ r, r.val = o.evalBits a b → wp Γ Q X (k r) m) :
    wp Γ Q X (
      if n == 0 then k (.imm (o.evalBits 0#0 0#0))
      else if n == target.widenWidth n then
        .let_ (op2 (.cmp o (.bits (target.widenWidth n))) a' b') fun r => k (.var r.1)
      else
        if (match o with | .slt | .sle | .sgt | .sge => true | _ => false) then
          emitSextToW n (target.widenWidth n) a' fun sa =>
            emitSextToW n (target.widenWidth n) b' fun sb =>
              .let_ (op2 (.cmp o (.bits (target.widenWidth n))) sa sb) fun r => k (.var r.1)
        else .let_ (op2 (.cmp o (.bits (target.widenWidth n))) a' b') fun r => k (.var r.1)) m := by
  have hnw := le_widenWidth_of_supports hn
  by_cases hn0 : n = 0
  · subst hn0
    simp only [beq_self_eq_true, ↓reduceIte]
    rw [bitVec0_eq_zero a, bitVec0_eq_zero b] at hk
    exact hk _ rfl
  · have hn0pos : 0 < n := Nat.pos_of_ne_zero hn0
    have hn0f : (n == 0) = false := beq_false_of_ne hn0
    simp only [hn0f, Bool.false_eq_true, ↓reduceIte]
    by_cases heq : n = target.widenWidth n
    · have hbeq : (n == target.widenWidth n) = true := beq_iff_eq.mpr heq
      simp only [hbeq, ↓reduceIte, wp, Op.wp, OpCode.wp, op2, vals, Ty.hasFloat,
        Bool.false_eq_true, liftCmp]
      revert a' b' ha hb hk
      rw [← heq]
      intro a' b' ha hb hk
      rw [BitVec.setWidth_eq] at ha hb
      exact hk _ (by change o.evalBits a'.val b'.val = _; rw [ha, hb])
    · have hneqf : (n == target.widenWidth n) = false := beq_false_of_ne heq
      simp only [hneqf, Bool.false_eq_true, ↓reduceIte]
      cases o <;> simp only [↓reduceIte, Bool.false_eq_true]
      · exact hk _ (by change CmpOp.evalBits .eq a'.val b'.val = _; rw [ha, hb]; exact evalBits_setWidth_unsigned hnw .eq trivial a b)
      · exact hk _ (by change CmpOp.evalBits .ne a'.val b'.val = _; rw [ha, hb]; exact evalBits_setWidth_unsigned hnw .ne trivial a b)
      · exact hk _ (by change CmpOp.evalBits .ult a'.val b'.val = _; rw [ha, hb]; exact evalBits_setWidth_unsigned hnw .ult trivial a b)
      · exact hk _ (by change CmpOp.evalBits .ule a'.val b'.val = _; rw [ha, hb]; exact evalBits_setWidth_unsigned hnw .ule trivial a b)
      · exact hk _ (by change CmpOp.evalBits .ugt a'.val b'.val = _; rw [ha, hb]; exact evalBits_setWidth_unsigned hnw .ugt trivial a b)
      · exact hk _ (by change CmpOp.evalBits .uge a'.val b'.val = _; rw [ha, hb]; exact evalBits_setWidth_unsigned hnw .uge trivial a b)
      · refine emitSextToW_wp hn0pos hnw ha fun sa hsa => emitSextToW_wp hn0pos hnw hb fun sb hsb => ?_
        simp only [wp, Op.wp, OpCode.wp, op2, vals, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, liftCmp]
        exact hk _ (by change CmpOp.evalBits .slt sa.val sb.val = _; rw [hsa, hsb]; exact evalBits_signExtend_signed hn0pos hnw .slt trivial a b)
      · refine emitSextToW_wp hn0pos hnw ha fun sa hsa => emitSextToW_wp hn0pos hnw hb fun sb hsb => ?_
        simp only [wp, Op.wp, OpCode.wp, op2, vals, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, liftCmp]
        exact hk _ (by change CmpOp.evalBits .sle sa.val sb.val = _; rw [hsa, hsb]; exact evalBits_signExtend_signed hn0pos hnw .sle trivial a b)
      · refine emitSextToW_wp hn0pos hnw ha fun sa hsa => emitSextToW_wp hn0pos hnw hb fun sb hsb => ?_
        simp only [wp, Op.wp, OpCode.wp, op2, vals, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, liftCmp]
        exact hk _ (by change CmpOp.evalBits .sgt sa.val sb.val = _; rw [hsa, hsb]; exact evalBits_signExtend_signed hn0pos hnw .sgt trivial a b)
      · refine emitSextToW_wp hn0pos hnw ha fun sa hsa => emitSextToW_wp hn0pos hnw hb fun sb hsb => ?_
        simp only [wp, Op.wp, OpCode.wp, op2, vals, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, liftCmp]
        exact hk _ (by change CmpOp.evalBits .sge sa.val sb.val = _; rw [hsa, hsb]; exact evalBits_signExtend_signed hn0pos hnw .sge trivial a b)

private theorem legalCmpTree_goMask_wp (target : LegalTarget) {Γ : Env} {rs : List Ty}
    {Q : Post rs} {X : XPost} (o : CmpOp) :
    ∀ (u : Ty), target.supportsTy u = true → u.hasFloat = false →
      (fx fy : Tup (Arg Val) (target.leafTys u)) → (x y : Val u) →
      valsTup fx = leafVals target u x → valsTup fy = leafVals target u y →
      (k : Tup (Arg Val) (target.leafTys u.mask) → Expr Val Cont rs) → (m : Mem 64) →
      (∀ res, valsTup res = leafVals target u.mask (liftCmp o.evalBits o.evalBool u x y) →
        wp Γ Q X (k res) m) →
      wp Γ Q X (legalCmpTree.goMask target o u fx fy k) m
  | .bool, _, _, (a', ()), (b', ()), a, b, ha, hb, k, m, hk => by
    dsimp only [LegalTarget.leafTys, Ty.mask, leafVals] at ha hb
    rw [valsTup_single] at ha hb
    replace ha := congrArg Prod.fst ha
    replace hb := congrArg Prod.fst hb
    dsimp only at ha hb
    dsimp only [legalCmpTree.goMask]
    by_cases hbc : target.boolCmp = true
    · rw [ite_eq_left hbc]
      simp only [wp, Op.wp, OpCode.wp, op2, vals, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, liftCmp]
      exact hk _ (by
        dsimp only [Ty.mask, LegalTarget.leafTys, leafVals]
        rw [valsTup_single]
        exact congrArg (·, ()) (by change o.evalBool a'.val b'.val = _; rw [ha, hb]; rfl))
    · rw [ite_eq_right hbc]
      refine emitBoolCmp_wp o a' b' fun r hr => hk (r, ()) ?_
      dsimp only [Ty.mask, LegalTarget.leafTys, leafVals]
      rw [valsTup_single, hr, ha, hb]; rfl
  | .bits n, ht, _, (a', ()), (b', ()), a, b, ha, hb, k, m, hk => by
    dsimp only [LegalTarget.leafTys, leafVals] at ha hb
    rw [valsTup_single] at ha hb
    dsimp only [Ty.mask, LegalTarget.leafTys] at k hk ⊢
    dsimp only [legalCmpTree.goMask]
    refine legalCmpBits_wp target o ht a' b' a b (congrArg Prod.fst ha) (congrArg Prod.fst hb)
      (k := fun r => k (r, ())) ?_
    intro r hr; exact hk (r, ()) (by dsimp only [leafVals]; rw [valsTup_single, hr]; rfl)
  | .float _, _, hf, _, _, _, _, _, _, _, _, _ => by simp [Ty.hasFloat] at hf
  | .pair u1 u2, ht, hf, fx, fy, px, py, hx, hy, k, m, hk => by
    simp only [LegalTarget.supportsTy, Bool.and_eq_true] at ht
    simp only [Ty.hasFloat, Bool.or_eq_false_iff] at hf
    dsimp only [LegalTarget.leafTys] at fx fy hx hy
    dsimp only [legalCmpTree.goMask]
    have hx12 := congrArg (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2)) hx
    have hy12 := congrArg (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2)) hy
    rw [leafVals_pair, tupSplit_tupAppend, tupSplit_valsTup] at hx12 hy12
    refine legalCmpTree_goMask_wp target o u1 ht.1 hf.1
      (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2) fx).1
      (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2) fy).1 px.1 py.1
      (congrArg Prod.fst hx12) (congrArg Prod.fst hy12) _ m fun m1 hm1 => ?_
    refine legalCmpTree_goMask_wp target o u2 ht.2 hf.2
      (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2) fx).2
      (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2) fy).2 px.2 py.2
      (congrArg Prod.snd hx12) (congrArg Prod.snd hy12) _ m fun m2 hm2 => ?_
    exact hk (tupAppend m1 m2) (by
      dsimp only [Ty.mask, LegalTarget.leafTys]
      rw [leafVals_pair, valsTup_tupAppend, hm1, hm2]; rfl)

private theorem legalCmpTree_wp (target : LegalTarget) {Γ : Env} {rs : List Ty}
    {Q : Post rs} {X : XPost} (o : CmpOp) :
    ∀ (t : Ty), target.supportsTy t = true → t.hasFloat = false →
      (xs ys : Tup (Arg Val) (target.legalTys t)) → (x y : Val t) →
      valsTup xs = encodeVal target t x → valsTup ys = encodeVal target t y →
      (k : Tup (Arg Val) (target.legalTys t.mask) → Expr Val Cont rs) → (m : Mem 64) →
      (∀ res, valsTup res = encodeVal target t.mask (liftCmp o.evalBits o.evalBool t x y) →
        wp Γ Q X (k res) m) →
      wp Γ Q X (legalCmpTree target o t xs ys k) m
  | .bool, _, _, (a', ()), (b', ()), a, b, ha, hb, k, m, hk => by
    dsimp only [LegalTarget.legalTys, LegalTarget.leafTys, Ty.mask, encodeVal] at ha hb
    rw [valsTup_single] at ha hb
    replace ha := congrArg Prod.fst ha
    replace hb := congrArg Prod.fst hb
    dsimp only at ha hb
    dsimp only [legalCmpTree]
    by_cases hbc : target.boolCmp = true
    · rw [ite_eq_left hbc]
      simp only [wp, Op.wp, OpCode.wp, op2, vals, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, liftCmp]
      exact hk _ (by
        dsimp only [Ty.mask, LegalTarget.legalTys, LegalTarget.leafTys, encodeVal]
        rw [valsTup_single]
        exact congrArg (·, ()) (by change o.evalBool a'.val b'.val = _; rw [ha, hb]; rfl))
    · rw [ite_eq_right hbc]
      refine emitBoolCmp_wp o a' b' fun r hr => hk (r, ()) ?_
      dsimp only [Ty.mask, LegalTarget.legalTys, LegalTarget.leafTys, encodeVal]
      rw [valsTup_single, hr, ha, hb]; rfl
  | .bits n, ht, _, (a', ()), (b', ()), a, b, ha, hb, k, m, hk => by
    dsimp only [LegalTarget.legalTys, LegalTarget.leafTys, encodeVal] at ha hb
    rw [valsTup_single] at ha hb
    dsimp only [Ty.mask, LegalTarget.legalTys, LegalTarget.leafTys] at k hk ⊢
    dsimp only [legalCmpTree]
    refine legalCmpBits_wp target o ht a' b' a b (congrArg Prod.fst ha) (congrArg Prod.fst hb)
      (k := fun r => k (r, ())) ?_
    intro r hr; exact hk (r, ()) (by dsimp only [encodeVal]; rw [valsTup_single, hr]; rfl)
  | .float _, _, hf, _, _, _, _, _, _, _, _, _ => by simp [Ty.hasFloat] at hf
  | .pair t1 t2, ht, hf, xs, ys, px, py, hxs, hys, k, m, hk => by
    have htp : target.supportsTy (.pair t1 t2) = true := ht
    dsimp only [legalCmpTree]
    refine splitLegalToLeaves_wp target (.pair t1 t2) htp xs px hxs fun fx hfx =>
      splitLegalToLeaves_wp target (.pair t1 t2) htp ys py hys fun fy hfy => ?_
    refine legalCmpTree_goMask_wp target o (.pair t1 t2) htp hf fx fy px py hfx hfy _ m fun mres hmres => ?_
    exact packLeavesToLegal_wp target (Ty.mask (.pair t1 t2)) (supportsTy_mask target (.pair t1 t2))
      mres (liftCmp o.evalBits o.evalBool (.pair t1 t2) px py) hmres hk

private theorem op3_select_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {t : Ty} (c' : Arg Val .bool) (c : Bool) (hc : c'.val = c)
    (a' b' : Arg Val t) (a b : Val t) (ha : a'.val = a) (hb : b'.val = b)
    (k : Arg Val t → Expr Val Cont rs) (m : Mem 64)
    (hk : ∀ r, r.val = (if c then a else b) → wp Γ Q X (k r) m) :
    wp Γ Q X (.let_ (op3 (.select t) c' a' b') fun r => k (.var r.1)) m := by
  cases c' <;> cases a' <;> cases b' <;>
    · dsimp only [wp, Op.wp, OpCode.wp, op3, vals, Arg.val] at hc ha hb ⊢
      cases c <;> simp_all [Arg.val]

private theorem legalSelectTree_goSel_wp (target : LegalTarget) {Γ : Env} {rs : List Ty}
    {Q : Post rs} {X : XPost} (c' : Arg Val .bool) (c : Bool) (hc : c'.val = c) :
    ∀ (u : Ty), target.supportsTy u = true →
      (fx fy : Tup (Arg Val) (target.leafTys u)) → (x y : Val u) →
      valsTup fx = leafVals target u x → valsTup fy = leafVals target u y →
      (k : Tup (Arg Val) (target.leafTys u) → Expr Val Cont rs) → (m : Mem 64) →
      (∀ res, valsTup res = leafVals target u (if c then x else y) → wp Γ Q X (k res) m) →
      wp Γ Q X (legalSelectTree.goSel target c' u fx fy k) m
  | .bool, _, (a', ()), (b', ()), a, b, ha, hb, k, m, hk => by
    dsimp only [LegalTarget.leafTys, leafVals] at ha hb k hk ⊢
    rw [valsTup_single] at ha hb
    replace ha := congrArg Prod.fst ha
    replace hb := congrArg Prod.fst hb
    dsimp only at ha hb
    dsimp only [legalSelectTree.goSel]
    by_cases hbs : target.boolSelect = true
    · rw [ite_eq_left hbs]
      exact op3_select_wp c' c hc a' b' a b ha hb (fun r => k (r, ())) m fun r hr =>
        hk (r, ()) (by rw [valsTup_single, hr])
    · rw [ite_eq_right hbs]
      refine emitBoolSelect_wp c' a' b' fun r hr => hk (r, ()) ?_
      rw [valsTup_single, hr, hc, ha, hb]
  | .bits n, _, (a', ()), (b', ()), a, b, ha, hb, k, m, hk => by
    dsimp only [LegalTarget.leafTys, leafVals] at ha hb k hk ⊢
    rw [valsTup_single] at ha hb
    replace ha := congrArg Prod.fst ha
    replace hb := congrArg Prod.fst hb
    dsimp only at ha hb
    dsimp only [legalSelectTree.goSel]
    exact op3_select_wp c' c hc a' b' (a.setWidth (target.widenWidth n)) (b.setWidth (target.widenWidth n))
      ha hb (fun r => k (r, ())) m fun r hr =>
      hk (r, ()) (by rw [valsTup_single, hr]; cases c <;> rfl)
  | .float f, _, (a', ()), (b', ()), a, b, ha, hb, k, m, hk => by
    dsimp only [LegalTarget.leafTys, leafVals] at ha hb k hk ⊢
    rw [valsTup_single] at ha hb
    replace ha := congrArg Prod.fst ha
    replace hb := congrArg Prod.fst hb
    dsimp only at ha hb
    dsimp only [legalSelectTree.goSel]
    exact op3_select_wp c' c hc a' b' a b ha hb (fun r => k (r, ())) m fun r hr =>
      hk (r, ()) (by rw [valsTup_single, hr])
  | .pair u1 u2, ht, fx, fy, px, py, hx, hy, k, m, hk => by
    simp only [LegalTarget.supportsTy, Bool.and_eq_true] at ht
    dsimp only [LegalTarget.leafTys] at fx fy hx hy
    dsimp only [legalSelectTree.goSel]
    have hx12 := congrArg (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2)) hx
    have hy12 := congrArg (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2)) hy
    rw [leafVals_pair, tupSplit_tupAppend, tupSplit_valsTup] at hx12 hy12
    refine legalSelectTree_goSel_wp target c' c hc u1 ht.1
      (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2) fx).1
      (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2) fy).1 px.1 py.1
      (congrArg Prod.fst hx12) (congrArg Prod.fst hy12) _ m fun r1 hr1 => ?_
    refine legalSelectTree_goSel_wp target c' c hc u2 ht.2
      (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2) fx).2
      (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2) fy).2 px.2 py.2
      (congrArg Prod.snd hx12) (congrArg Prod.snd hy12) _ m fun r2 hr2 => ?_
    exact hk (tupAppend r1 r2) (by
      dsimp only [LegalTarget.leafTys]
      rw [leafVals_pair, valsTup_tupAppend, hr1, hr2]
      cases c <;> rfl)

private theorem legalSelectTree_wp (target : LegalTarget) {Γ : Env} {rs : List Ty}
    {Q : Post rs} {X : XPost} (c' : Arg Val .bool) (c : Bool) (hc : c'.val = c) :
    ∀ (t : Ty), target.supportsTy t = true →
      (xs ys : Tup (Arg Val) (target.legalTys t)) → (x y : Val t) →
      valsTup xs = encodeVal target t x → valsTup ys = encodeVal target t y →
      (k : Tup (Arg Val) (target.legalTys t) → Expr Val Cont rs) → (m : Mem 64) →
      (∀ res, valsTup res = encodeVal target t (if c then x else y) → wp Γ Q X (k res) m) →
      wp Γ Q X (legalSelectTree target c' t xs ys k) m
  | .bool, _, (a', ()), (b', ()), a, b, ha, hb, k, m, hk => by
    dsimp only [LegalTarget.legalTys, LegalTarget.leafTys, encodeVal] at ha hb k hk ⊢
    rw [valsTup_single] at ha hb
    replace ha := congrArg Prod.fst ha
    replace hb := congrArg Prod.fst hb
    dsimp only at ha hb
    dsimp only [legalSelectTree]
    by_cases hbs : target.boolSelect = true
    · rw [ite_eq_left hbs]
      exact op3_select_wp c' c hc a' b' a b ha hb (fun r => k (r, ())) m fun r hr =>
        hk (r, ()) (by rw [valsTup_single, hr])
    · rw [ite_eq_right hbs]
      refine emitBoolSelect_wp c' a' b' fun r hr => hk (r, ()) ?_
      rw [valsTup_single, hr, hc, ha, hb]
  | .bits n, _, (a', ()), (b', ()), a, b, ha, hb, k, m, hk => by
    dsimp only [LegalTarget.legalTys, LegalTarget.leafTys, encodeVal] at ha hb k hk ⊢
    rw [valsTup_single] at ha hb
    replace ha := congrArg Prod.fst ha
    replace hb := congrArg Prod.fst hb
    dsimp only at ha hb
    dsimp only [legalSelectTree]
    exact op3_select_wp c' c hc a' b' (a.setWidth (target.widenWidth n)) (b.setWidth (target.widenWidth n))
      ha hb (fun r => k (r, ())) m fun r hr =>
      hk (r, ()) (by rw [valsTup_single, hr]; cases c <;> rfl)
  | .float f, _, (a', ()), (b', ()), a, b, ha, hb, k, m, hk => by
    dsimp only [LegalTarget.legalTys, LegalTarget.leafTys, encodeVal] at ha hb k hk ⊢
    rw [valsTup_single] at ha hb
    replace ha := congrArg Prod.fst ha
    replace hb := congrArg Prod.fst hb
    dsimp only at ha hb
    dsimp only [legalSelectTree]
    exact op3_select_wp c' c hc a' b' a b ha hb (fun r => k (r, ())) m fun r hr =>
      hk (r, ()) (by rw [valsTup_single, hr])
  | .pair t1 t2, ht, xs, ys, px, py, hxs, hys, k, m, hk => by
    have htp : target.supportsTy (.pair t1 t2) = true := ht
    dsimp only [legalSelectTree]
    refine splitLegalToLeaves_wp target (.pair t1 t2) htp xs px hxs fun fx hfx =>
      splitLegalToLeaves_wp target (.pair t1 t2) htp ys py hys fun fy hfy => ?_
    refine legalSelectTree_goSel_wp target c' c hc (.pair t1 t2) htp fx fy px py hfx hfy _ m fun fres hfres => ?_
    exact packLeavesToLegal_wp target (.pair t1 t2) htp fres (if c then px else py) hfres hk

private theorem legalBlendTree_goBlend_wp (target : LegalTarget) {Γ : Env} {rs : List Ty}
    {Q : Post rs} {X : XPost} :
    ∀ (u : Ty), target.supportsTy u = true →
      (fm : Tup (Arg Val) (target.leafTys u.mask)) →
      (fx fy : Tup (Arg Val) (target.leafTys u)) →
      (msk : Val u.mask) → (x y : Val u) →
      valsTup fm = leafVals target u.mask msk →
      valsTup fx = leafVals target u x → valsTup fy = leafVals target u y →
      (k : Tup (Arg Val) (target.leafTys u) → Expr Val Cont rs) → (m : Mem 64) →
      (∀ res, valsTup res = leafVals target u (blendV u msk x y) → wp Γ Q X (k res) m) →
      wp Γ Q X (legalBlendTree.goBlend target u fm fx fy k) m
  | .bool, _, (c', ()), (a', ()), (b', ()), c, a, b, hc, ha, hb, k, m, hk => by
    dsimp only [Ty.mask, LegalTarget.leafTys, leafVals] at hc ha hb k hk ⊢
    rw [valsTup_single] at hc ha hb
    replace hc := congrArg Prod.fst hc
    replace ha := congrArg Prod.fst ha
    replace hb := congrArg Prod.fst hb
    dsimp only at hc ha hb
    dsimp only [legalBlendTree.goBlend]
    by_cases hbs : target.boolSelect = true
    · rw [ite_eq_left hbs]
      exact op3_select_wp c' c hc a' b' a b ha hb (fun r => k (r, ())) m fun r hr =>
        hk (r, ()) (by rw [valsTup_single, hr]; rfl)
    · rw [ite_eq_right hbs]
      refine emitBoolSelect_wp c' a' b' fun r hr => hk (r, ()) ?_
      rw [valsTup_single, hr, hc, ha, hb]; rfl
  | .bits n, _, (c', ()), (a', ()), (b', ()), c, a, b, hc, ha, hb, k, m, hk => by
    dsimp only [Ty.mask, LegalTarget.leafTys, leafVals] at hc ha hb k hk ⊢
    rw [valsTup_single] at hc ha hb
    replace hc := congrArg Prod.fst hc
    replace ha := congrArg Prod.fst ha
    replace hb := congrArg Prod.fst hb
    dsimp only at hc ha hb
    dsimp only [legalBlendTree.goBlend]
    exact op3_select_wp c' c hc a' b' (a.setWidth (target.widenWidth n)) (b.setWidth (target.widenWidth n))
      ha hb (fun r => k (r, ())) m fun r hr =>
      hk (r, ()) (by rw [valsTup_single, hr]; cases c <;> rfl)
  | .float f, _, (c', ()), (a', ()), (b', ()), c, a, b, hc, ha, hb, k, m, hk => by
    dsimp only [Ty.mask, LegalTarget.leafTys, leafVals] at hc ha hb k hk ⊢
    rw [valsTup_single] at hc ha hb
    replace hc := congrArg Prod.fst hc
    replace ha := congrArg Prod.fst ha
    replace hb := congrArg Prod.fst hb
    dsimp only at hc ha hb
    dsimp only [legalBlendTree.goBlend]
    exact op3_select_wp c' c hc a' b' a b ha hb (fun r => k (r, ())) m fun r hr =>
      hk (r, ()) (by rw [valsTup_single, hr]; rfl)
  | .pair u1 u2, ht, fm, fx, fy, msk, px, py, hm, hx, hy, k, m, hk => by
    simp only [LegalTarget.supportsTy, Bool.and_eq_true] at ht
    dsimp only [Ty.mask, LegalTarget.leafTys] at fm fx fy hm hx hy
    dsimp only [legalBlendTree.goBlend]
    have hm12 := congrArg (tupSplit (as := target.leafTys u1.mask) (bs := target.leafTys u2.mask)) hm
    have hx12 := congrArg (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2)) hx
    have hy12 := congrArg (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2)) hy
    rw [leafVals_pair, tupSplit_tupAppend, tupSplit_valsTup] at hm12 hx12 hy12
    refine legalBlendTree_goBlend_wp target u1 ht.1
      (tupSplit (as := target.leafTys u1.mask) (bs := target.leafTys u2.mask) fm).1
      (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2) fx).1
      (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2) fy).1 msk.1 px.1 py.1
      (congrArg Prod.fst hm12) (congrArg Prod.fst hx12) (congrArg Prod.fst hy12) _ m fun r1 hr1 => ?_
    refine legalBlendTree_goBlend_wp target u2 ht.2
      (tupSplit (as := target.leafTys u1.mask) (bs := target.leafTys u2.mask) fm).2
      (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2) fx).2
      (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2) fy).2 msk.2 px.2 py.2
      (congrArg Prod.snd hm12) (congrArg Prod.snd hx12) (congrArg Prod.snd hy12) _ m fun r2 hr2 => ?_
    exact hk (tupAppend r1 r2) (by
      dsimp only [LegalTarget.leafTys]
      rw [leafVals_pair, valsTup_tupAppend, hr1, hr2]; rfl)

private theorem legalBlendTree_wp (target : LegalTarget) {Γ : Env} {rs : List Ty}
    {Q : Post rs} {X : XPost} :
    ∀ (t : Ty), target.supportsTy t = true →
      (ms : Tup (Arg Val) (target.legalTys t.mask)) →
      (xs ys : Tup (Arg Val) (target.legalTys t)) →
      (msk : Val t.mask) → (x y : Val t) →
      valsTup ms = encodeVal target t.mask msk →
      valsTup xs = encodeVal target t x → valsTup ys = encodeVal target t y →
      (k : Tup (Arg Val) (target.legalTys t) → Expr Val Cont rs) → (m : Mem 64) →
      (∀ res, valsTup res = encodeVal target t (blendV t msk x y) → wp Γ Q X (k res) m) →
      wp Γ Q X (legalBlendTree target t ms xs ys k) m
  | .bool, _, (c', ()), (a', ()), (b', ()), c, a, b, hc, ha, hb, k, m, hk => by
    dsimp only [Ty.mask, LegalTarget.legalTys, LegalTarget.leafTys, encodeVal] at hc ha hb k hk ⊢
    rw [valsTup_single] at hc ha hb
    replace hc := congrArg Prod.fst hc
    replace ha := congrArg Prod.fst ha
    replace hb := congrArg Prod.fst hb
    dsimp only at hc ha hb
    dsimp only [legalBlendTree]
    by_cases hbs : target.boolSelect = true
    · rw [ite_eq_left hbs]
      exact op3_select_wp c' c hc a' b' a b ha hb (fun r => k (r, ())) m fun r hr =>
        hk (r, ()) (by rw [valsTup_single, hr]; rfl)
    · rw [ite_eq_right hbs]
      refine emitBoolSelect_wp c' a' b' fun r hr => hk (r, ()) ?_
      rw [valsTup_single, hr, hc, ha, hb]; rfl
  | .bits n, _, (c', ()), (a', ()), (b', ()), c, a, b, hc, ha, hb, k, m, hk => by
    dsimp only [Ty.mask, LegalTarget.legalTys, LegalTarget.leafTys, encodeVal] at hc ha hb k hk ⊢
    rw [valsTup_single] at hc ha hb
    replace hc := congrArg Prod.fst hc
    replace ha := congrArg Prod.fst ha
    replace hb := congrArg Prod.fst hb
    dsimp only at hc ha hb
    dsimp only [legalBlendTree]
    exact op3_select_wp c' c hc a' b' (a.setWidth (target.widenWidth n)) (b.setWidth (target.widenWidth n))
      ha hb (fun r => k (r, ())) m fun r hr =>
      hk (r, ()) (by rw [valsTup_single, hr]; cases c <;> rfl)
  | .float f, _, (c', ()), (a', ()), (b', ()), c, a, b, hc, ha, hb, k, m, hk => by
    dsimp only [Ty.mask, LegalTarget.legalTys, LegalTarget.leafTys, encodeVal] at hc ha hb k hk ⊢
    rw [valsTup_single] at hc ha hb
    replace hc := congrArg Prod.fst hc
    replace ha := congrArg Prod.fst ha
    replace hb := congrArg Prod.fst hb
    dsimp only at hc ha hb
    dsimp only [legalBlendTree]
    exact op3_select_wp c' c hc a' b' a b ha hb (fun r => k (r, ())) m fun r hr =>
      hk (r, ()) (by rw [valsTup_single, hr]; rfl)
  | .pair t1 t2, ht, ms, xs, ys, msk, px, py, hms, hxs, hys, k, m, hk => by
    have htp : target.supportsTy (.pair t1 t2) = true := ht
    dsimp only [legalBlendTree]
    refine splitLegalToLeaves_wp target (Ty.mask (.pair t1 t2)) (supportsTy_mask target (.pair t1 t2))
        ms msk hms fun fm hfm =>
      splitLegalToLeaves_wp target (.pair t1 t2) htp xs px hxs fun fx hfx =>
      splitLegalToLeaves_wp target (.pair t1 t2) htp ys py hys fun fy hfy => ?_
    refine legalBlendTree_goBlend_wp target (.pair t1 t2) htp fm fx fy msk px py hfm hfx hfy _ m fun fres hfres => ?_
    exact packLeavesToLegal_wp target (.pair t1 t2) htp fres (blendV (.pair t1 t2) msk px py) hfres hk

private theorem legalFCmpTree_goFCmp_wp (target : LegalTarget) {Γ : Env} {rs : List Ty}
    {Q : Post rs} {X : XPost} (o : FCmpOp) :
    ∀ (u : Ty), target.supportsTy u = true → u.isFloatTree = true →
      (fx fy : Tup (Arg Val) (target.leafTys u)) → (x y : Val u) →
      valsTup fx = leafVals target u x → valsTup fy = leafVals target u y →
      (k : Tup (Arg Val) (target.leafTys u.mask) → Expr Val Cont rs) → (m : Mem 64) →
      (∀ res, valsTup res = leafVals target u.mask (liftFCmp o u x y) →
        wp Γ Q X (k res) m) →
      wp Γ Q X (legalFCmpTree.goFCmp target o u fx fy k) m
  | .bool, _, hf, _, _, _, _, _, _, _, _, _ => by simp [Ty.isFloatTree] at hf
  | .bits _, _, hf, _, _, _, _, _, _, _, _, _ => by simp [Ty.isFloatTree] at hf
  | .float f, _, _, (a', ()), (b', ()), a, b, ha, hb, k, m, hk => by
    dsimp only [LegalTarget.leafTys, leafVals] at ha hb
    rw [valsTup_single] at ha hb
    replace ha := congrArg Prod.fst ha
    replace hb := congrArg Prod.fst hb
    dsimp only at ha hb
    simp only [legalFCmpTree.goFCmp, wp, Op.wp, OpCode.wp, op2, vals, Ty.isFloatTree,
      Bool.not_true, Bool.false_eq_true, ↓reduceIte, liftFCmp]
    exact hk _ (by
      dsimp only [Ty.mask, LegalTarget.leafTys, leafVals]
      rw [valsTup_single]
      exact congrArg (·, ()) (by
        change fcmpLeaf o f a'.val b'.val = _
        rw [ha, hb]; rfl))
  | .pair u1 u2, ht, hf, fx, fy, px, py, hx, hy, k, m, hk => by
    simp only [LegalTarget.supportsTy, Bool.and_eq_true] at ht
    simp only [Ty.isFloatTree, Bool.and_eq_true] at hf
    dsimp only [LegalTarget.leafTys] at fx fy hx hy
    dsimp only [legalFCmpTree.goFCmp]
    have hx12 := congrArg (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2)) hx
    have hy12 := congrArg (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2)) hy
    rw [leafVals_pair, tupSplit_tupAppend, tupSplit_valsTup] at hx12 hy12
    refine legalFCmpTree_goFCmp_wp target o u1 ht.1 hf.1
      (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2) fx).1
      (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2) fy).1 px.1 py.1
      (congrArg Prod.fst hx12) (congrArg Prod.fst hy12) _ m fun m1 hm1 => ?_
    refine legalFCmpTree_goFCmp_wp target o u2 ht.2 hf.2
      (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2) fx).2
      (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2) fy).2 px.2 py.2
      (congrArg Prod.snd hx12) (congrArg Prod.snd hy12) _ m fun m2 hm2 => ?_
    exact hk (tupAppend m1 m2) (by
      dsimp only [Ty.mask, LegalTarget.leafTys]
      rw [leafVals_pair, valsTup_tupAppend, hm1, hm2]; rfl)

private theorem legalFCmpTree_wp (target : LegalTarget) {Γ : Env} {rs : List Ty}
    {Q : Post rs} {X : XPost} (o : FCmpOp) :
    ∀ (t : Ty), target.supportsTy t = true → t.isFloatTree = true →
      (xs ys : Tup (Arg Val) (target.legalTys t)) → (x y : Val t) →
      valsTup xs = encodeVal target t x → valsTup ys = encodeVal target t y →
      (k : Tup (Arg Val) (target.legalTys t.mask) → Expr Val Cont rs) → (m : Mem 64) →
      (∀ res, valsTup res = encodeVal target t.mask (liftFCmp o t x y) →
        wp Γ Q X (k res) m) →
      wp Γ Q X (legalFCmpTree target o t xs ys k) m
  | .bool, _, hf, _, _, _, _, _, _, _, _, _ => by simp [Ty.isFloatTree] at hf
  | .bits _, _, hf, _, _, _, _, _, _, _, _, _ => by simp [Ty.isFloatTree] at hf
  | .float f, _, _, (a', ()), (b', ()), a, b, ha, hb, k, m, hk => by
    dsimp only [LegalTarget.legalTys, LegalTarget.leafTys, encodeVal] at ha hb
    rw [valsTup_single] at ha hb
    replace ha := congrArg Prod.fst ha
    replace hb := congrArg Prod.fst hb
    dsimp only at ha hb
    simp only [legalFCmpTree, wp, Op.wp, OpCode.wp, op2, vals, Ty.isFloatTree,
      Bool.not_true, Bool.false_eq_true, ↓reduceIte, liftFCmp]
    exact hk _ (by
      dsimp only [Ty.mask, LegalTarget.legalTys, LegalTarget.leafTys, encodeVal]
      rw [valsTup_single]
      exact congrArg (·, ()) (by
        change fcmpLeaf o f a'.val b'.val = _
        rw [ha, hb]; rfl))
  | .pair t1 t2, ht, hf, xs, ys, px, py, hxs, hys, k, m, hk => by
    have htp : target.supportsTy (.pair t1 t2) = true := ht
    dsimp only [legalFCmpTree]
    refine splitLegalToLeaves_wp target (.pair t1 t2) htp xs px hxs fun fx hfx =>
      splitLegalToLeaves_wp target (.pair t1 t2) htp ys py hys fun fy hfy => ?_
    refine legalFCmpTree_goFCmp_wp target o (.pair t1 t2) htp hf fx fy px py hfx hfy _ m fun mres hmres => ?_
    exact packLeavesToLegal_wp target (Ty.mask (.pair t1 t2)) (supportsTy_mask target (.pair t1 t2))
      mres (liftFCmp o (.pair t1 t2) px py) hmres hk

private theorem op1_bitcast_wp_top {t u : Ty} (h : t.size = u.size) (a : Val t)
    (post : Tup Val [u] → Prop) :
    OpCode.wp (.bitcast t u h) (a, ()) post = post (ofBits u (BitVec.cast h (toBits t a)), ()) := rfl

private theorem legalFloatBit2_wp (target : LegalTarget) {Γ : Env} {rs : List Ty}
    {Q : Post rs} {X : XPost}
    (mkOp : (w : Nat) → OpCode [.bits w, .bits w] [.bits w])
    (mkFOp : (f : Fmt) → OpCode [.float f, .float f] [.float f])
    (f : Fmt) (g : BitVec f.width → BitVec f.width → BitVec f.width)
    (hF : ∀ (a b : BitVec f.width) post, OpCode.wp (mkFOp f) (a, b, ()) post ↔ post (g a b, ()))
    (hB : ∀ (a b : BitVec f.width) post, OpCode.wp (mkOp f.width) (a, b, ()) post ↔ post (g a b, ()))
    (x' y' : Arg Val (.float f)) (x y : BitVec f.width)
    (hx : x'.val = x) (hy : y'.val = y)
    {k : Arg Val (.float f) → Expr Val Cont rs} {m : Mem 64}
    (hk : ∀ r, r.val = g x y → wp Γ Q X (k r) m) :
    wp Γ Q X (legalFloatBit2 target mkOp mkFOp f x' y' k) m := by
  dsimp only [legalFloatBit2]
  by_cases hsb : target.scalarFloatBitwise = true
  · rw [ite_eq_left hsb]
    dsimp only [wp, Op.wp, op2, vals]
    rw [hx, hy, hF]
    exact hk _ rfl
  · rw [ite_eq_right hsb]
    dsimp only [wp, Op.wp, op1, op2, vals]
    rw [op1_bitcast_wp_top, op1_bitcast_wp_top]
    dsimp only [Arg.val_var, toBits, ofBits]
    simp only [BitVec.cast_eq]
    rw [hB x'.val y'.val]
    rw [op1_bitcast_wp_top]
    dsimp only [toBits, ofBits]
    simp only [BitVec.cast_eq]
    exact hk _ (by change g x'.val y'.val = _; rw [hx, hy])

/-! ### Word stream (`packLeavesToWords64` / `unpackWords64ToLeaves`) and 128-bit SIMD lowering -/

private def words64GetLsb (ws : List (Arg Val i64)) (i : Nat) : Bool :=
  (ws.getD (i / 64) (.imm 0#64)).val.getLsbD (i % 64)

private def Words64Stream (ws : List (Arg Val i64)) (acc : Arg Val i64)
    (accBits totalBits : Nat) (bits : Nat → Bool) : Prop :=
  accBits < 64 ∧
  totalBits = 64 * ws.length + accBits ∧
  (∀ j, accBits ≤ j → acc.val.getLsbD j = false) ∧
  (∀ i, i < 64 * ws.length → words64GetLsb ws i = bits i) ∧
  (∀ j, j < accBits → acc.val.getLsbD j = bits (64 * ws.length + j))

private theorem list_getD_append_left {α : Type} (xs ys : List α) (d : α) {i : Nat}
    (hi : i < xs.length) : (xs ++ ys).getD i d = xs.getD i d := by
  simp [List.getD, List.getElem?_append_left hi]

private theorem list_getD_append_right_eq {α : Type} (xs : List α) (x d : α) :
    (xs ++ [x]).getD xs.length d = x := by
  simp [List.getD]

private theorem words64GetLsb_append_left (ws ys : List (Arg Val i64)) {i : Nat}
    (hi : i < 64 * ws.length) :
    words64GetLsb (ws ++ ys) i = words64GetLsb ws i := by
  unfold words64GetLsb
  have hdiv : i / 64 < ws.length := Nat.div_lt_of_lt_mul (by omega)
  rw [list_getD_append_left ws ys (.imm 0#64) hdiv]

private theorem words64GetLsb_append_singleton_right (ws : List (Arg Val i64)) (x : Arg Val i64)
    {i : Nat} (hlo : 64 * ws.length ≤ i) (hhi : i < 64 * (ws.length + 1)) :
    words64GetLsb (ws ++ [x]) i = x.val.getLsbD (i - 64 * ws.length) := by
  unfold words64GetLsb
  have hdiv : i / 64 = ws.length := by
    apply Nat.le_antisymm
    · exact Nat.le_of_lt_succ (Nat.div_lt_of_lt_mul (by omega))
    · exact (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
  have hmod : i % 64 = i - 64 * ws.length := by
    have := Nat.div_add_mod i 64
    rw [hdiv] at this
    omega
  rw [hdiv, list_getD_append_right_eq, hmod]

private theorem Words64Stream.finish {ws : List (Arg Val i64)} {acc : Arg Val i64}
    {accBits totalBits : Nat} {bits : Nat → Bool}
    (hS : Words64Stream ws acc accBits totalBits bits) :
    let out := if accBits == 0 then ws else ws ++ [acc]
    (∀ i, i < totalBits → words64GetLsb out i = bits i) ∧
    out.length = (totalBits + 63) / 64 ∧
    (totalBits % 64 = 0 → out.length = totalBits / 64) := by
  rcases hS with ⟨hLt, hTot, _, hWs, hAcc⟩
  dsimp only
  by_cases h0 : accBits = 0
  · simp only [h0, beq_self_eq_true, ↓reduceIte]
    rw [h0, Nat.add_zero] at hTot
    refine ⟨fun i hi => hWs i (hTot ▸ hi), ?_, fun _ => by rw [hTot]; omega⟩
    rw [hTot]; omega
  · have hne : (accBits == 0) = false := beq_false_of_ne h0
    simp only [hne, Bool.false_eq_true, ↓reduceIte, List.length_append, List.length_singleton]
    refine ⟨?_, ?_, ?_⟩
    · intro i hi
      by_cases hlt : i < 64 * ws.length
      · rw [words64GetLsb_append_left ws [acc] hlt]
        exact hWs i hlt
      · have hge : 64 * ws.length ≤ i := Nat.le_of_not_lt hlt
        have hhi : i < 64 * (ws.length + 1) := by omega
        rw [words64GetLsb_append_singleton_right ws acc hge hhi]
        have hj : i - 64 * ws.length < accBits := by omega
        have := hAcc (i - 64 * ws.length) hj
        rwa [show 64 * ws.length + (i - 64 * ws.length) = i by omega] at this
    · rw [hTot]; omega
    · intro hmod
      exfalso
      have : accBits = 0 := by omega
      exact h0 this

private theorem words64GetLsb_ge (ws : List (Arg Val i64)) {i : Nat} (hi : 64 * ws.length ≤ i) :
    words64GetLsb ws i = false := by
  unfold words64GetLsb
  have hdiv : ws.length ≤ i / 64 := (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
  simp [List.getD, hdiv]

private theorem Words64Stream.finish_all {ws : List (Arg Val i64)} {acc : Arg Val i64}
    {accBits totalBits : Nat} {bits : Nat → Bool}
    (hS : Words64Stream ws acc accBits totalBits bits) :
    let out := if accBits == 0 then ws else ws ++ [acc]
    (∀ i, words64GetLsb out i = if i < totalBits then bits i else false) ∧
    out.length = (totalBits + 63) / 64 ∧
    (totalBits % 64 = 0 → out.length = totalBits / 64) := by
  have ⟨hBits, hLen, hDiv⟩ := Words64Stream.finish hS
  rcases hS with ⟨hLt, hTot, hAccHi, _, _⟩
  refine ⟨fun i => ?_, hLen, hDiv⟩
  by_cases hi : i < totalBits
  · simp only [hi, ↓reduceIte]
    exact hBits i hi
  · simp only [hi, ↓reduceIte]
    by_cases h0 : accBits = 0
    · simp only [h0, beq_self_eq_true, ↓reduceIte]
      exact words64GetLsb_ge ws (by omega)
    · have hne : (accBits == 0) = false := beq_false_of_ne h0
      simp only [hne, Bool.false_eq_true, ↓reduceIte]
      by_cases hhi : i < 64 * (ws.length + 1)
      · rw [words64GetLsb_append_singleton_right ws acc (by omega) hhi]
        exact hAccHi (i - 64 * ws.length) (by omega)
      · exact words64GetLsb_ge (ws ++ [acc]) (by simp; omega)

private theorem pushLeafWord64_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {w : Nat} (hw : w ≤ 64) {leaf : Arg Val i64}
    {ws : List (Arg Val i64)} {acc : Arg Val i64} {accBits totalBits : Nat}
    {bits bits' : Nat → Bool}
    (hS : Words64Stream ws acc accBits totalBits bits)
    (hLeafHi : ∀ j, w ≤ j → leaf.val.getLsbD j = false)
    (hAgree : ∀ i, i < totalBits → bits' i = bits i)
    (hLeafBits : ∀ j, j < w → leaf.val.getLsbD j = bits' (totalBits + j))
    {k : List (Arg Val i64) → Arg Val i64 → Nat → Expr Val Cont rs} {m : Mem 64}
    (hk : ∀ ws' acc' accBits',
      Words64Stream ws' acc' accBits' (totalBits + w) bits' →
      wp Γ Q X (k ws' acc' accBits') m) :
    wp Γ Q X (pushLeafWord64 w leaf ws acc accBits k) m := by
  rcases hS with ⟨hAccLt, hTot, hAccHi, hWs, hAccBits⟩
  unfold pushLeafWord64
  by_cases hw0 : w = 0
  · subst hw0
    simp only [beq_self_eq_true, ↓reduceIte]
    apply hk
    refine ⟨hAccLt, by omega, hAccHi, ?_, ?_⟩
    · intro i hi
      rw [hAgree i (by omega)]
      exact hWs i hi
    · intro j hj
      rw [hAgree (64 * ws.length + j) (by omega)]
      exact hAccBits j hj
  · have hwNe : (w == 0) = false := beq_false_of_ne hw0
    simp only [hwNe, Bool.false_eq_true, ↓reduceIte]
    by_cases ha0 : accBits = 0
    · simp only [ha0, beq_self_eq_true, ↓reduceIte]
      rw [ha0, Nat.add_zero] at hTot
      by_cases hw64 : w ≥ 64
      · have hwEq : w = 64 := by omega
        subst hwEq
        simp only [ge_iff_le, Nat.le_refl, ↓reduceIte]
        apply hk
        refine ⟨by omega, by simp only [List.length_append, List.length_singleton]; omega, fun j _ => by simp, ?_, fun j hj => by omega⟩
        intro i hi
        simp only [List.length_append, List.length_singleton] at hi
        by_cases hlt : i < 64 * ws.length
        · rw [words64GetLsb_append_left ws [leaf] hlt, hAgree i (by omega)]
          exact hWs i hlt
        · have hge : 64 * ws.length ≤ i := Nat.le_of_not_lt hlt
          rw [words64GetLsb_append_singleton_right ws leaf hge hi]
          have := hLeafBits (i - 64 * ws.length) (by omega)
          rwa [show totalBits + (i - 64 * ws.length) = i by omega] at this
      · have hwLt : w < 64 := by omega
        simp only [show ¬(w ≥ 64) by omega, ↓reduceIte]
        apply hk
        refine ⟨hwLt, by omega, hLeafHi, ?_, ?_⟩
        · intro i hi
          rw [hAgree i (by omega)]
          exact hWs i hi
        · intro j hj
          have := hLeafBits j hj
          rwa [← hTot]
    · have haNe : (accBits == 0) = false := beq_false_of_ne ha0
      simp only [haNe, Bool.false_eq_true, ↓reduceIte]
      dsimp only [wp, Op.wp, op2, vals]
      rw [OpCode.wp_shl]
      simp only [Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, lift2, Arg.val_imm]
      rw [OpCode.wp_or]
      dsimp only [lift2, Arg.val_var]
      have hModAcc : (BitVec.ofNat 64 accBits).toNat % 64 = accBits := by
        rw [BitVec.toNat_ofNat]
        simp [Nat.mod_eq_of_lt hAccLt]
      have hLoGet : ∀ j, j < 64 →
          (acc.val ||| leaf.val <<< ((BitVec.ofNat 64 accBits).toNat % 64)).getLsbD j =
            if j < accBits then bits' (64 * ws.length + j)
            else if j - accBits < w then bits' (64 * ws.length + j) else false := by
        intro j hj64
        rw [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, hModAcc]
        by_cases hjAcc : j < accBits
        · simp [hjAcc, hAgree (64 * ws.length + j) (by omega), hAccBits j hjAcc]
        · rw [hAccHi j (by omega)]
          simp [hjAcc, hj64]
          by_cases hjw : j - accBits < w
          · simp only [hjw]
            have := hLeafBits (j - accBits) hjw
            rwa [show totalBits + (j - accBits) = 64 * ws.length + j by omega] at this
          · simp only [hjw]
            exact hLeafHi (j - accBits) (by omega)
      by_cases hSumLt : accBits + w < 64
      · simp only [hSumLt, ↓reduceIte]
        apply hk
        refine ⟨hSumLt, by omega, ?_, ?_, ?_⟩
        · intro j hj
          by_cases hj64 : j < 64
          · dsimp only [Arg.val_var]
            rw [hLoGet j hj64]
            simp [show ¬(j < accBits) by omega, show ¬(j - accBits < w) by omega]
          · exact BitVec.getLsbD_of_ge _ j (by omega)
        · intro i hi
          rw [hAgree i (by omega)]
          exact hWs i hi
        · intro j hj
          dsimp only [Arg.val_var]
          rw [hLoGet j (by omega)]
          by_cases hjAcc : j < accBits <;> simp [hjAcc, show j - accBits < w by omega]
      · simp only [hSumLt, ↓reduceIte]
        by_cases hSumEq : accBits + w = 64
        · simp only [hSumEq, beq_self_eq_true, ↓reduceIte]
          apply hk
          refine ⟨by omega, by simp only [List.length_append, List.length_singleton]; omega, fun j _ => by simp, ?_, fun j hj => by omega⟩
          intro i hi
          simp only [List.length_append, List.length_singleton] at hi
          by_cases hlt : i < 64 * ws.length
          · rw [words64GetLsb_append_left ws [.var _] hlt, hAgree i (by omega)]
            exact hWs i hlt
          · have hge : 64 * ws.length ≤ i := Nat.le_of_not_lt hlt
            rw [words64GetLsb_append_singleton_right ws (.var _) hge hi]
            dsimp only [Arg.val_var]
            have hj64 : i - 64 * ws.length < 64 := by omega
            rw [hLoGet (i - 64 * ws.length) hj64]
            by_cases hjAcc : i - 64 * ws.length < accBits
            · simp [hjAcc, show 64 * ws.length + (i - 64 * ws.length) = i by omega]
            · simp [hjAcc, show i - 64 * ws.length - accBits < w by omega,
                show 64 * ws.length + (i - 64 * ws.length) = i by omega]
        · have hSumGt : 64 < accBits + w := by omega
          have hSumNe : (accBits + w == 64) = false := beq_false_of_ne hSumEq
          simp only [hSumNe, Bool.false_eq_true, ↓reduceIte]
          dsimp only [wp, Op.wp, op2, vals]
          rw [OpCode.wp_lshr]
          simp only [Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, lift2, Arg.val_imm]
          have hModSub : (BitVec.ofNat 64 (64 - accBits)).toNat % 64 = 64 - accBits := by
            rw [BitVec.toNat_ofNat]
            have haPos : 0 < accBits := Nat.pos_of_ne_zero ha0
            simp [Nat.mod_eq_of_lt (by omega : 64 - accBits < 64)]
          apply hk
          refine ⟨by omega, by simp only [List.length_append, List.length_singleton]; omega, ?_, ?_, ?_⟩
          · intro j hj
            dsimp only [Arg.val_var]
            rw [BitVec.getLsbD_ushiftRight, hModSub]
            by_cases hhi64 : 64 - accBits + j < 64
            · exact hLeafHi (64 - accBits + j) (by omega)
            · exact BitVec.getLsbD_of_ge leaf.val _ (by omega)
          · intro i hi
            simp only [List.length_append, List.length_singleton] at hi
            by_cases hlt : i < 64 * ws.length
            · rw [words64GetLsb_append_left ws [.var _] hlt, hAgree i (by omega)]
              exact hWs i hlt
            · have hge : 64 * ws.length ≤ i := Nat.le_of_not_lt hlt
              rw [words64GetLsb_append_singleton_right ws (.var _) hge hi]
              dsimp only [Arg.val_var]
              have hj64 : i - 64 * ws.length < 64 := by omega
              rw [hLoGet (i - 64 * ws.length) hj64]
              by_cases hjAcc : i - 64 * ws.length < accBits
              · simp [hjAcc, show 64 * ws.length + (i - 64 * ws.length) = i by omega]
              · simp [hjAcc, show i - 64 * ws.length - accBits < w by omega,
                  show 64 * ws.length + (i - 64 * ws.length) = i by omega]
          · intro j hj
            dsimp only [Arg.val_var]
            rw [BitVec.getLsbD_ushiftRight, hModSub]
            have h1 := hLeafBits (64 - accBits + j) (by omega)
            simp only [List.length_append, List.length_singleton]
            rwa [show totalBits + (64 - accBits + j) = 64 * (ws.length + 1) + j by omega] at h1

private theorem getLsbD_eq_rec {a b : Nat} (h : a = b) (x : BitVec a) (i : Nat) :
    (h ▸ x).getLsbD i = x.getLsbD i := by
  subst h; rfl

private theorem packLeavesToWords64_go_wp (target : LegalTarget) (hv : target.valid = true)
    {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} :
    ∀ (u : Ty), target.supportsTy u = true →
    ∀ {fx : Tup (Arg Val) (target.leafTys u)} {v : Val u}
      {ws : List (Arg Val i64)} {acc : Arg Val i64} {accBits totalBits : Nat}
      {bits bits' : Nat → Bool},
      valsTup fx = leafVals target u v →
      Words64Stream ws acc accBits totalBits bits →
      (∀ i, i < totalBits → bits' i = bits i) →
      (∀ j, j < u.size → (toBits u v).getLsbD j = bits' (totalBits + j)) →
      ∀ {k : List (Arg Val i64) → Arg Val i64 → Nat → Expr Val Cont rs} {m : Mem 64},
        (∀ ws' acc' accBits',
          Words64Stream ws' acc' accBits' (totalBits + u.size) bits' →
          wp Γ Q X (k ws' acc' accBits') m) →
        wp Γ Q X (packLeavesToWords64.go target u fx ws acc accBits k) m
  | .bool, _, fx, v, ws, acc, accBits, totalBits, bits, bits', hFx, hS, hAgree, hNew, k, m, hk => by
    dsimp only [LegalTarget.leafTys] at fx hFx
    rcases fx with ⟨b, ⟨⟩⟩
    rw [packLeavesToWords64.go.eq_1]
    dsimp only [wp, Op.wp, op1, vals]
    rw [OpCode.wp_ofBool]
    dsimp only [Arg.val_var]
    have hb : b.val = v := by
      rw [valsTup_single] at hFx
      dsimp only [leafVals] at hFx
      exact congrArg Prod.fst hFx
    apply pushLeafWord64_wp (by omega) hS
    · intro j hj
      dsimp only [Arg.val_var]
      rw [hb, BitVec.getLsbD_ofNat]
      cases v <;> simp [Bool.toNat]
      intro _
      exact Nat.testBit_lt_two_pow (Nat.one_lt_two_pow (by omega : j ≠ 0))
    · exact hAgree
    · intro j hj
      have hj0 : j = 0 := by omega
      subst hj0
      have h0 := hNew 0 (by simp [Ty.size])
      dsimp only [Arg.val_var]
      rw [Nat.add_zero] at h0 ⊢
      rw [← h0, hb]
      cases v <;> simp [toBits, Bool.toNat]
    · simpa [Ty.size] using hk
  | .bits n, hSup, fx, v, ws, acc, accBits, totalBits, bits, bits', hFx, hS, hAgree, hNew, k, m, hk => by
    dsimp only [LegalTarget.leafTys] at fx hFx
    rcases fx with ⟨x, ⟨⟩⟩
    rw [packLeavesToWords64.go.eq_2]
    have hx : x.val = BitVec.setWidth (target.widenWidth n) v := by
      rw [valsTup_single] at hFx
      dsimp only [leafVals] at hFx
      exact congrArg Prod.fst hFx
    have hn64 : n ≤ 64 := (supportsTy_bits_iff.mp hSup).2
    have hnW : n ≤ target.widenWidth n := le_widenWidth_of_supports hSup
    have hWle64 := widenWidth_le_64_of_supports hv hSup
    by_cases hn0 : n = 0
    · subst hn0
      simp only [beq_self_eq_true, ↓reduceIte]
      apply hk
      rcases hS with ⟨hLt, hTot, hAccHi, hWs, hAcc⟩
      refine ⟨hLt, hTot, hAccHi, ?_, ?_⟩
      · intro i hi; rw [hAgree i (by omega)]; exact hWs i hi
      · intro j hj; rw [hAgree (64 * ws.length + j) (by omega)]; exact hAcc j hj
    · have hnNe : (n == 0) = false := beq_false_of_ne hn0
      simp only [hnNe, Bool.false_eq_true, ↓reduceIte, Nat.min_eq_left hn64]
      by_cases hwn64 : target.widenWidth n = 64
      · simp only [hwn64, ↓reduceDIte]
        have hCast : (castArgBits hwn64 x).val = BitVec.setWidth 64 v := by
          rw [val_castArgBits, hx]
          apply BitVec.eq_of_getLsbD_eq; intro j hj64
          rw [getLsbD_eq_rec, BitVec.getLsbD_setWidth, BitVec.getLsbD_setWidth]
          by_cases hjn : j < n
          · simp [hj64, show j < target.widenWidth n by omega]
          · simp [BitVec.getLsbD_of_ge v j (by omega)]
        apply pushLeafWord64_wp hn64 hS
        · intro j hj
          rw [hCast, BitVec.getLsbD_setWidth]
          simp [BitVec.getLsbD_of_ge v j hj]
        · exact hAgree
        · intro j hj
          have h0 := hNew j (by simp [Ty.size]; exact hj)
          rw [← h0, hCast, BitVec.getLsbD_setWidth]
          simp [toBits, show j < 64 by omega]
        · simpa [Ty.size] using hk
      · have hwnLt64 : target.widenWidth n < 64 := by omega
        simp only [hwn64, hwnLt64, ↓reduceDIte, ↓reduceIte]
        dsimp only [wp, Op.wp, op1, vals]
        rw [OpCode.wp_zext]
        refine ⟨Nat.le_of_lt hwnLt64, ?_⟩
        dsimp only [Arg.val_var]
        have hZext : BitVec.setWidth 64 x.val = BitVec.setWidth 64 v := by
          apply BitVec.eq_of_getLsbD_eq
          intro j hj64
          rw [hx, BitVec.getLsbD_setWidth, BitVec.getLsbD_setWidth, BitVec.getLsbD_setWidth]
          by_cases hjn : j < n
          · simp [hj64, show j < target.widenWidth n by omega]
          · simp [BitVec.getLsbD_of_ge v j (by omega)]
        apply pushLeafWord64_wp hn64 hS
        · intro j hj
          dsimp only [Arg.val_var]
          rw [hZext, BitVec.getLsbD_setWidth]
          simp [BitVec.getLsbD_of_ge v j hj]
        · exact hAgree
        · intro j hj
          have h0 := hNew j (by simp [Ty.size]; exact hj)
          dsimp only [Arg.val_var]
          rw [← h0, hZext, BitVec.getLsbD_setWidth]
          simp [toBits, show j < 64 by omega]
        · simpa [Ty.size] using hk
  | .float f, hSup, fx, v, ws, acc, accBits, totalBits, bits, bits', hFx, hS, hAgree, hNew, k, m, hk => by
    dsimp only [LegalTarget.leafTys] at fx hFx
    rcases fx with ⟨x, ⟨⟩⟩
    rw [packLeavesToWords64.go.eq_3]
    have hx : x.val = v := by
      rw [valsTup_single] at hFx
      dsimp only [leafVals] at hFx
      exact congrArg Prod.fst hFx
    have hSupAnd : f ∈ target.floatFmts ∧ f.width ≤ 64 := by
      simpa [LegalTarget.supportsTy] using hSup
    have hFwSpec := valid_bitWidth_spec hv (valid_float_spec hv hSupAnd.1).1
    have hFwLe64 : f.width ≤ 64 := hFwSpec.2.2
    dsimp only [wp, Op.wp, op1, vals]
    rw [op1_bitcast_wp_top]
    dsimp only [toBits, ofBits, Arg.val_var]
    by_cases hfw64 : f.width = 64
    · simp only [hfw64, ↓reduceDIte]
      apply pushLeafWord64_wp (by omega) hS
      · intro j hj
        rw [val_castArgBits]
        exact BitVec.getLsbD_of_ge _ j (by omega)
      · exact hAgree
      · intro j hj
        have h0 := hNew j (by simp [Ty.size, hfw64]; exact hj)
        rw [← h0, val_castArgBits, getLsbD_eq_rec]
        dsimp only [Arg.val_var]
        rw [BitVec.getLsbD_cast]
        simp [toBits, hx]
      · simpa [hfw64] using hk
    · have hfwLt64 : f.width < 64 := by omega
      simp only [hfw64, hfwLt64, ↓reduceDIte, ↓reduceIte]
      dsimp only [wp, Op.wp, op1, vals]
      rw [OpCode.wp_zext]
      refine ⟨Nat.le_of_lt hfwLt64, ?_⟩
      dsimp only [Arg.val_var]
      apply pushLeafWord64_wp hFwLe64 hS
      · intro j hj
        dsimp only [Arg.val_var]
        rw [BitVec.getLsbD_setWidth]
        simp [BitVec.getLsbD_of_ge _ j hj]
      · exact hAgree
      · intro j hj
        have h0 := hNew j (by simp [Ty.size]; exact hj)
        dsimp only [Arg.val_var]
        rw [← h0, BitVec.getLsbD_setWidth, BitVec.getLsbD_cast]
        simp [toBits, hx, show j < 64 by omega]
      · simpa [Ty.size] using hk
  | .pair a b, hSup, fx, v, ws, acc, accBits, totalBits, bits, bits', hFx, hS, hAgree, hNew, k, m, hk => by
    rw [packLeavesToWords64.go.eq_4]
    have hSupPair : target.supportsTy a = true ∧ target.supportsTy b = true := by
      simpa [LegalTarget.supportsTy] using hSup
    dsimp only [LegalTarget.leafTys] at fx hFx
    have hSplitFx := tupSplit_valsTup (fx := fx)
    rw [hFx, leafVals_pair, tupSplit_tupAppend] at hSplitFx
    have hFst : valsTup (tupSplit fx).1 = leafVals target a v.1 :=
      (congrArg Prod.fst hSplitFx).symm
    have hSnd : valsTup (tupSplit fx).2 = leafVals target b v.2 :=
      (congrArg Prod.snd hSplitFx).symm
    apply packLeavesToWords64_go_wp target hv a hSupPair.1 hFst hS hAgree
    · intro j hj
      have h0 := hNew j (by simp [Ty.size]; omega)
      rw [← h0]
      simp [toBits, BitVec.getLsbD_cast, BitVec.getLsbD_append, hj]
    · intro ws1 acc1 bits1 hS1
      apply packLeavesToWords64_go_wp target hv b hSupPair.2 hSnd hS1 (fun _ _ => rfl)
      · intro j hj
        have h0 := hNew (a.size + j) (by simp [Ty.size]; omega)
        rw [← Nat.add_assoc] at h0
        rw [← h0]
        simp [toBits, BitVec.getLsbD_cast, BitVec.getLsbD_append, show ¬(a.size + j < a.size) by omega]
      · intro ws2 acc2 bits2 hS2
        exact hk ws2 acc2 bits2 (by simpa [Ty.size, Nat.add_assoc] using hS2)

private theorem packLeavesToWords64_wp (target : LegalTarget) (hv : target.valid = true)
    {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (t : Ty) (ht : target.supportsTy t = true)
    {fx : Tup (Arg Val) (target.leafTys t)} {x : Val t}
    (hFx : valsTup fx = leafVals target t x)
    {k : List (Arg Val i64) → Expr Val Cont rs} {m : Mem 64}
    (hk : ∀ words : List (Arg Val i64),
      (∀ i, i < t.size → words64GetLsb words i = (toBits t x).getLsbD i) →
      words.length = (t.size + 63) / 64 →
      (t.size % 64 = 0 → words.length = t.size / 64) →
      wp Γ Q X (k words) m) :
    wp Γ Q X (packLeavesToWords64 target t fx k) m := by
  unfold packLeavesToWords64
  have hS0 : Words64Stream ([] : List (Arg Val i64)) (.imm 0#64) 0 0 (fun _ => false) :=
    ⟨by omega, by simp, fun j _ => by simp, fun i hi => by simp at hi, fun j hj => by omega⟩
  apply packLeavesToWords64_go_wp target hv t ht hFx hS0
    (bits' := fun i => if i < t.size then (toBits t x).getLsbD i else false) (fun i hi => by omega)
  · intro j hj; simp [hj]
  · intro ws acc accBits hS
    have ⟨hBits, hLen, hDiv⟩ := Words64Stream.finish hS
    by_cases h0 : accBits = 0
    · simp only [h0, beq_self_eq_true, ↓reduceIte] at hBits hLen hDiv ⊢
      apply hk ws
      · intro i hi
        have := hBits i (by omega)
        simpa [hi] using this
      · simpa using hLen
      · simpa using hDiv
    · have hne : (accBits == 0) = false := beq_false_of_ne h0
      simp only [hne, Bool.false_eq_true, ↓reduceIte] at hBits hLen hDiv ⊢
      apply hk (ws ++ [acc])
      · intro i hi
        have := hBits i (by omega)
        simpa [hi] using this
      · simpa using hLen
      · simpa using hDiv

private theorem packLeavesToWords64_wp_all (target : LegalTarget) (hv : target.valid = true)
    {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (t : Ty) (ht : target.supportsTy t = true)
    {fx : Tup (Arg Val) (target.leafTys t)} {x : Val t}
    (hFx : valsTup fx = leafVals target t x)
    {k : List (Arg Val i64) → Expr Val Cont rs} {m : Mem 64}
    (hk : ∀ words : List (Arg Val i64),
      (∀ i, words64GetLsb words i = if i < t.size then (toBits t x).getLsbD i else false) →
      words.length = (t.size + 63) / 64 →
      (t.size % 64 = 0 → words.length = t.size / 64) →
      wp Γ Q X (k words) m) :
    wp Γ Q X (packLeavesToWords64 target t fx k) m := by
  unfold packLeavesToWords64
  have hS0 : Words64Stream ([] : List (Arg Val i64)) (.imm 0#64) 0 0 (fun _ => false) :=
    ⟨by omega, by simp, fun j _ => by simp, fun i hi => by simp at hi, fun j hj => by omega⟩
  apply packLeavesToWords64_go_wp target hv t ht hFx hS0
    (bits' := fun i => if i < t.size then (toBits t x).getLsbD i else false) (fun i hi => by omega)
  · intro j hj; simp [hj]
  · intro ws acc accBits hS
    have ⟨hBits, hLen, hDiv⟩ := Words64Stream.finish_all hS
    by_cases h0 : accBits = 0
    · simp only [h0, beq_self_eq_true, ↓reduceIte] at hBits hLen hDiv ⊢
      apply hk ws
      · intro i
        have := hBits i
        by_cases hi : i < t.size
        · simpa [hi] using this
        · simpa [hi] using this
      · simpa using hLen
      · simpa using hDiv
    · have hne : (accBits == 0) = false := beq_false_of_ne h0
      simp only [hne, Bool.false_eq_true, ↓reduceIte] at hBits hLen hDiv ⊢
      apply hk (ws ++ [acc])
      · intro i
        have := hBits i
        by_cases hi : i < t.size
        · simpa [hi] using this
        · simpa [hi] using this
      · simpa using hLen
      · simpa using hDiv

private theorem extractBitsFromWords64_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {words : List (Arg Val i64)} {off w : Nat} (hw : w ≤ 64)
    {bits : Nat → Bool}
    (hW : ∀ i, i < w → words64GetLsb words (off + i) = bits i)
    {k : Arg Val i64 → Expr Val Cont rs} {m : Mem 64}
    (hk : ∀ raw : Arg Val i64,
      (∀ i, raw.val.getLsbD i = (if i < w then bits i else false)) →
      wp Γ Q X (k raw) m) :
    wp Γ Q X (extractBitsFromWords64 words off w k) m := by
  unfold extractBitsFromWords64
  by_cases hw0 : w = 0
  · subst hw0
    simp only [beq_self_eq_true, ↓reduceIte]
    apply hk
    intro i; simp
  · have hwNe : (w == 0) = false := beq_false_of_ne hw0
    simp only [hwNe, Bool.false_eq_true, ↓reduceIte]
    have hBitLt : off % 64 < 64 := Nat.mod_lt off (by omega)
    have hOffEq : off = 64 * (off / 64) + off % 64 := by
      have := Nat.div_add_mod off 64
      omega
    have hLoStep :
        ∀ (cont : Arg Val i64 → Expr Val Cont rs),
        (∀ lo : Arg Val i64,
          (∀ j, j < 64 - off % 64 → lo.val.getLsbD j = words64GetLsb words (off + j)) →
          (∀ j, 64 - off % 64 ≤ j → lo.val.getLsbD j = false) →
          wp Γ Q X (cont lo) m) →
        wp Γ Q X (if (off % 64 == 0) = true then cont (words.getD (off / 64) (.imm 0#64))
          else Expr.let_ (op2 (.lshr i64) (words.getD (off / 64) (.imm 0#64)) (.imm (BitVec.ofNat 64 (off % 64))))
            fun r => cont (.var r.1)) m := by
      intro cont hcont
      by_cases hb0 : off % 64 = 0
      · simp only [hb0, beq_self_eq_true, ↓reduceIte]
        apply hcont
        · intro j hj
          have hdiv : (off + j) / 64 = off / 64 := by omega
          have hmod : (off + j) % 64 = j := by omega
          simp [words64GetLsb, hdiv, hmod]
        · intro j hj
          exact BitVec.getLsbD_of_ge _ j (by omega)
      · have hbNe : (off % 64 == 0) = false := beq_false_of_ne hb0
        simp only [hbNe, Bool.false_eq_true, ↓reduceIte, wp, Op.wp, op2, vals]
        rw [OpCode.wp_lshr]
        simp only [Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, lift2, Arg.val_imm]
        have hModBo : (BitVec.ofNat 64 (off % 64)).toNat % 64 = off % 64 := by
          rw [BitVec.toNat_ofNat]
          simp [Nat.mod_eq_of_lt hBitLt]
        apply hcont
        · intro j hj
          dsimp only [Arg.val_var]
          rw [BitVec.getLsbD_ushiftRight, hModBo]
          have hdiv : (off + j) / 64 = off / 64 := by omega
          have hmod : (off + j) % 64 = off % 64 + j := by omega
          simp [words64GetLsb, hdiv, hmod]
        · intro j hj
          dsimp only [Arg.val_var]
          rw [BitVec.getLsbD_ushiftRight, hModBo]
          exact BitVec.getLsbD_of_ge _ _ (by omega)
    apply hLoStep (fun lo =>
      if off % 64 + w ≤ 64 then emitMaskToN w 64 lo k
      else
        Expr.let_ (op2 (.shl i64) (words.getD (off / 64 + 1) (.imm 0#64)) (.imm (BitVec.ofNat 64 (64 - off % 64))))
          fun h => Expr.let_ (op2 (.or i64) lo (.var h.1)) fun lo' => emitMaskToN w 64 (.var lo'.1) k)
    intro lo hLoGood hLoHi
    by_cases hFit : off % 64 + w ≤ 64
    · simp only [hFit, ↓reduceIte]
      apply emitMaskToN_wp hw rfl
      intro r hr
      apply hk
      intro i
      rw [hr, BitVec.getLsbD_setWidth, BitVec.getLsbD_setWidth]
      by_cases hiw : i < w
      · have hi64 : i < 64 := by omega
        have hj : i < 64 - off % 64 := by omega
        rw [hLoGood i hj, hW i hiw]
        simp [hi64, hiw]
      · simp [hiw]
    · have hNotFit : ¬(off % 64 + w ≤ 64) := hFit
      have hBPos : 0 < off % 64 := by omega
      simp only [hNotFit, ↓reduceIte, wp, Op.wp, op2, vals]
      rw [OpCode.wp_shl]
      simp only [Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, lift2, Arg.val_imm]
      rw [OpCode.wp_or]
      dsimp only [lift2, Arg.val_var]
      have hModSub : (BitVec.ofNat 64 (64 - off % 64)).toNat % 64 = 64 - off % 64 := by
        rw [BitVec.toNat_ofNat]
        simp [Nat.mod_eq_of_lt (by omega : 64 - off % 64 < 64)]
      apply emitMaskToN_wp hw rfl
      intro r hr
      apply hk
      intro i
      rw [hr, BitVec.getLsbD_setWidth, BitVec.getLsbD_setWidth]
      by_cases hiw : i < w
      · have hi64 : i < 64 := by omega
        simp only [hi64, hiw, decide_true, Bool.true_and]
        dsimp only [Arg.val_var]
        rw [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, hModSub]
        by_cases hilt : i < 64 - off % 64
        · simp [hilt, hLoGood i hilt, hW i hiw]
        · have hfLo : lo.val.getLsbD i = false := hLoHi i (by omega)
          have ht1 : (decide (i < 64) && !decide (i < 64 - off % 64)) = true := by simp [hi64, hilt]
          simp only [hfLo, ht1, Bool.true_and, Bool.false_or]
          have hdiv : (off + i) / 64 = off / 64 + 1 := by omega
          have hmod : (off + i) % 64 = i - (64 - off % 64) := by omega
          have hw1 : (words.getD (off / 64 + 1) (.imm 0#64)).val.getLsbD (i - (64 - off % 64)) = bits i := by
            have := hW i hiw
            simpa [words64GetLsb, hdiv, hmod] using this
          exact hw1
      · simp [hiw]

private theorem unpackWords64ToLeaves_wp (target : LegalTarget) (hv : target.valid = true)
    {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} :
    ∀ (u : Ty), target.supportsTy u = true →
    ∀ {words : List (Arg Val i64)} {off : Nat} {v : Val u},
      (∀ i, i < u.size → words64GetLsb words (off + i) = (toBits u v).getLsbD i) →
      ∀ {k : Tup (Arg Val) (target.leafTys u) → Expr Val Cont rs} {m : Mem 64},
        (∀ fres : Tup (Arg Val) (target.leafTys u),
          valsTup fres = leafVals target u v →
          wp Γ Q X (k fres) m) →
        wp Γ Q X (unpackWords64ToLeaves target words off u k) m
  | .bool, _, words, off, v, hW, k, m, hk => by
    rw [unpackWords64ToLeaves.eq_1]
    apply extractBitsFromWords64_wp (by omega) (fun i hi => hW i (by simp [Ty.size]; omega))
    intro raw hRaw
    dsimp only [wp, Op.wp, op2, vals]
    rw [OpCode.wp_cmp]
    simp only [Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, liftCmp, CmpOp.evalBits, Arg.val_imm,
      cast_eq]
    have hEqVal : raw.val = if v then 1#64 else 0#64 := by
      apply BitVec.eq_of_getLsbD_eq
      intro i hi64
      rw [hRaw i]
      by_cases hi0 : i = 0
      · subst hi0
        cases v <;> simp [toBits]
      · have hi1 : ¬(i < 1) := by omega
        cases v <;> simp [hi1, hi0]
    apply hk (.var _, ())
    dsimp only [LegalTarget.leafTys] at *
    rw [valsTup_single]
    dsimp only [leafVals, Arg.val_var]
    rw [hEqVal]
    cases v <;> decide
  | .bits n, hSup, words, off, v, hW, k, m, hk => by
    rw [unpackWords64ToLeaves.eq_2]
    have hn64 : n ≤ 64 := (supportsTy_bits_iff.mp hSup).2
    have hnW : n ≤ target.widenWidth n := le_widenWidth_of_supports hSup
    have hWle64 := widenWidth_le_64_of_supports hv hSup
    by_cases hn0 : n = 0
    · subst hn0
      simp only [beq_self_eq_true, ↓reduceIte]
      apply hk (.imm 0#(target.widenWidth 0), ())
      have hv0 : v = 0#0 := Subsingleton.elim v 0#0
      subst hv0
      simp only [LegalTarget.leafTys, leafVals]
      apply Prod.ext _ rfl
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      simp
    · have hnNe : (n == 0) = false := beq_false_of_ne hn0
      simp only [hnNe, Bool.false_eq_true, ↓reduceIte, Nat.min_eq_left hn64]
      apply extractBitsFromWords64_wp hn64 (fun i hi => hW i (by simp [Ty.size]; exact hi))
      intro raw hRaw
      have hRawEq : raw.val = BitVec.setWidth 64 v := by
        apply BitVec.eq_of_getLsbD_eq
        intro i hi64
        rw [hRaw i, BitVec.getLsbD_setWidth]
        by_cases hin : i < n
        · simp [hin, hi64, toBits]
        · simp only [hin, ↓reduceIte, BitVec.getLsbD_of_ge v i (by omega), Bool.and_false]
      by_cases hwn64 : target.widenWidth n = 64
      · simp only [hwn64, ↓reduceDIte]
        apply hk (castArgBits hwn64.symm raw, ())
        dsimp only [LegalTarget.leafTys] at *
        rw [valsTup_single]
        dsimp only [leafVals]
        congr 1
        rw [val_castArgBits, hRawEq]
        apply BitVec.eq_of_getLsbD_eq
        intro i hiW
        rw [getLsbD_eq_rec, BitVec.getLsbD_setWidth, BitVec.getLsbD_setWidth]
        simp [hiW, show i < 64 by omega]
      · have hwnLt64 : target.widenWidth n < 64 := by omega
        simp only [hwn64, hwnLt64, ↓reduceDIte, ↓reduceIte]
        dsimp only [wp, Op.wp, op1, vals]
        rw [OpCode.wp_trunc]
        refine ⟨Nat.le_of_lt hwnLt64, ?_⟩
        apply hk (.var _, ())
        dsimp only [LegalTarget.leafTys] at *
        rw [valsTup_single]
        dsimp only [leafVals, Arg.val_var]
        rw [hRawEq]
        congr 1
        apply BitVec.eq_of_getLsbD_eq
        intro i hiW
        rw [BitVec.getLsbD_setWidth, BitVec.getLsbD_setWidth, BitVec.getLsbD_setWidth]
        simp [hiW, show i < 64 by omega]
  | .float f, hSup, words, off, v, hW, k, m, hk => by
    rw [unpackWords64ToLeaves.eq_3]
    have hSupAnd : f ∈ target.floatFmts ∧ f.width ≤ 64 := by
      simpa [LegalTarget.supportsTy] using hSup
    have hFwSpec := valid_bitWidth_spec hv (valid_float_spec hv hSupAnd.1).1
    have hFwLe64 : f.width ≤ 64 := hFwSpec.2.2
    simp only [Nat.min_eq_left hFwLe64]
    apply extractBitsFromWords64_wp hFwLe64 (fun i hi => hW i (by simp [Ty.size]; exact hi))
    intro raw hRaw
    have hRawEq : raw.val = BitVec.setWidth 64 v := by
      apply BitVec.eq_of_getLsbD_eq
      intro i hi64
      rw [hRaw i, BitVec.getLsbD_setWidth]
      by_cases hif : i < f.width
      · simp [hif, hi64, toBits]
      · simp only [hif, ↓reduceIte, BitVec.getLsbD_of_ge v i (by omega), Bool.and_false]
    by_cases hfw64 : f.width = 64
    · simp only [hfw64, ↓reduceDIte]
      dsimp only [wp, Op.wp, op1, vals]
      rw [op1_bitcast_wp_top]
      dsimp only [toBits, ofBits]
      apply hk (.var _, ())
      dsimp only [LegalTarget.leafTys] at *
      rw [valsTup_single]
      dsimp only [leafVals, Arg.val_var]
      rw [hRawEq]
      congr 1
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      have hi64 : i < 64 := by simpa [Ty.size, hfw64] using hi
      rw [BitVec.getLsbD_cast, BitVec.getLsbD_setWidth]
      simp [hi64]
    · have hfwLt64 : f.width < 64 := by omega
      simp only [hfw64, hfwLt64, ↓reduceDIte, ↓reduceIte]
      dsimp only [wp, Op.wp, op1, vals]
      rw [OpCode.wp_trunc]
      refine ⟨Nat.le_of_lt hfwLt64, ?_⟩
      rw [op1_bitcast_wp_top]
      dsimp only [toBits, ofBits, Arg.val_var]
      apply hk (.var _, ())
      dsimp only [LegalTarget.leafTys] at *
      rw [valsTup_single]
      dsimp only [leafVals, Arg.val_var]
      rw [hRawEq]
      congr 1
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      have hif : i < f.width := by simpa [Ty.size] using hi
      rw [BitVec.getLsbD_cast, BitVec.getLsbD_setWidth, BitVec.getLsbD_setWidth]
      simp [hif, show i < 64 by omega]
  | .pair a b, hSup, words, off, v, hW, k, m, hk => by
    rw [unpackWords64ToLeaves.eq_4]
    have hSupPair : target.supportsTy a = true ∧ target.supportsTy b = true := by
      simpa [LegalTarget.supportsTy] using hSup
    apply unpackWords64ToLeaves_wp target hv a hSupPair.1 (v := v.1)
    · intro i hi
      have h0 := hW i (by simp [Ty.size]; omega)
      rw [h0]
      simp [toBits, BitVec.getLsbD_cast, BitVec.getLsbD_append, hi]
    · intro fa hFa
      apply unpackWords64ToLeaves_wp target hv b hSupPair.2 (v := v.2)
      · intro i hi
        have h0 := hW (a.size + i) (by simp [Ty.size]; omega)
        rw [← Nat.add_assoc] at h0
        rw [h0]
        simp [toBits, BitVec.getLsbD_cast, BitVec.getLsbD_append, show ¬(a.size + i < a.size) by omega]
      · intro fb hFb
        apply hk (tupAppend fa fb)
        dsimp only [LegalTarget.leafTys]
        rw [valsTup_tupAppend, hFa, hFb, leafVals_pair]

private theorem foldl_bvOfLanes_getLsbD (w c : Nat) (hc : 0 < c) (f : Nat → BitVec c) :
    ∀ (n : Nat) (init : BitVec w) (k : Nat),
      k < w →
      ((List.range n).foldl (fun acc i => acc ||| BitVec.setWidth w (f i) <<< (c * i)) init).getLsbD k =
        (init.getLsbD k || (if k / c < n then (f (k / c)).getLsbD (k % c) else false))
  | 0, init, k, _ => by simp
  | n + 1, init, k, hk => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [BitVec.getLsbD_or, foldl_bvOfLanes_getLsbD w c hc f n init k hk]
    rw [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
    simp only [hk, decide_true, Bool.true_and]
    by_cases hkc : k / c < n
    · have hk_lt : k < c * n := by rw [Nat.mul_comm]; exact (Nat.div_lt_iff_lt_mul hc).mp hkc
      have hlt_dec : decide (k < c * n) = true := decide_eq_true hk_lt
      have hkc1 : k / c < n + 1 := by omega
      simp [hkc, hkc1, hlt_dec]
    · by_cases heq : k / c = n
      · have hge : c * n ≤ k := by
          have := Nat.div_add_mod k c
          rw [heq] at this; omega
        have hsub : k - c * n = k % c := by
          have := Nat.div_add_mod k c
          rw [heq] at this; omega
        have hnot : decide (k < c * n) = false := decide_eq_false (by omega)
        have hmc : decide (k % c < w) = true := decide_eq_true (Nat.lt_of_le_of_lt (Nat.mod_le _ _) hk)
        rw [hsub]
        simp [hnot, hmc, heq]
      · have hgt : n + 1 ≤ k / c := by omega
        have hnot1 : ¬(k / c < n + 1) := by omega
        have hdiff : c * (n + 1) ≤ k := by rw [Nat.mul_comm]; exact (Nat.le_div_iff_mul_le hc).mp hgt
        have hdiff' : c * n + c ≤ k := by simpa [Nat.mul_succ] using hdiff
        have hf : (f n).getLsbD (k - c * n) = false :=
          BitVec.getLsbD_of_ge (f n) (k - c * n) (by omega)
        simp [hkc, hnot1, hf]

private theorem getLsbD_bvOfLanes {w c : Nat} (hc : 0 < c) (f : Nat → BitVec c) {k : Nat}
    (hk : k < w) :
    (bvOfLanes w c f).getLsbD k =
      (if k / c < w / c then (f (k / c)).getLsbD (k % c) else false) := by
  unfold bvOfLanes
  rw [foldl_bvOfLanes_getLsbD w c hc f (w / c) (0#w) k hk]
  simp

private theorem getLsbD_bvLane {w : Nat} (c i : Nat) (v : BitVec w) (j : Nat) :
    (bvLane c i v).getLsbD j = (decide (j < c) && v.getLsbD (c * i + j)) := by
  unfold bvLane
  exact BitVec.getLsbD_extractLsb' (c * i) c v j

private theorem bvLane8_bvLane32 (v : BitVec 128) (q r : Nat) (hr : r < 4) :
    bvLane 8 r (bvLane 32 q v) = bvLane 8 (4 * q + r) v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi8
  rw [getLsbD_bvLane, getLsbD_bvLane, getLsbD_bvLane]
  have hi32 : 8 * r + i < 32 := by omega
  simp only [hi8, decide_true, Bool.true_and, hi32]
  rw [show 32 * q + (8 * r + i) = 8 * (4 * q + r) + i by omega]

private theorem words2ToDwords4_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {w0 w1 : Arg Val i64} {v : BitVec 128}
    (hw0 : w0.val = BitVec.extractLsb' 0 64 v)
    (hw1 : w1.val = BitVec.extractLsb' 64 64 v)
    {k : Arg Val i32 → Arg Val i32 → Arg Val i32 → Arg Val i32 → Expr Val Cont rs} {m : Mem 64}
    (hk : ∀ d0 d1 d2 d3 : Arg Val i32,
      d0.val = bvLane 32 0 v →
      d1.val = bvLane 32 1 v →
      d2.val = bvLane 32 2 v →
      d3.val = bvLane 32 3 v →
      wp Γ Q X (k d0 d1 d2 d3) m) :
    wp Γ Q X (words2ToDwords4 w0 w1 k) m := by
  unfold words2ToDwords4
  dsimp only [wp, Op.wp, op1, op2, vals]
  rw [OpCode.wp_trunc]; refine ⟨by omega, ?_⟩
  rw [OpCode.wp_lshr]; simp only [Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, lift2, Arg.val_imm]
  rw [OpCode.wp_trunc]; refine ⟨by omega, ?_⟩
  rw [OpCode.wp_trunc]; refine ⟨by omega, ?_⟩
  rw [OpCode.wp_lshr]; simp only [Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, lift2]
  rw [OpCode.wp_trunc]; refine ⟨by omega, ?_⟩
  apply hk
  · apply BitVec.eq_of_getLsbD_eq; intro i hi
    dsimp only [Arg.val_var]
    rw [BitVec.getLsbD_setWidth, hw0, BitVec.getLsbD_extractLsb', getLsbD_bvLane]
    simp [hi, show i < 64 by omega]
  · apply BitVec.eq_of_getLsbD_eq; intro i hi
    dsimp only [Arg.val_var]
    rw [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, hw0, BitVec.getLsbD_extractLsb', getLsbD_bvLane]
    have hmod : (32#64).toNat % 64 = 32 := by decide
    rw [hmod]
    simp [hi, show 32 + i < 64 by omega]
  · apply BitVec.eq_of_getLsbD_eq; intro i hi
    dsimp only [Arg.val_var]
    rw [BitVec.getLsbD_setWidth, hw1, BitVec.getLsbD_extractLsb', getLsbD_bvLane]
    simp [hi, show i < 64 by omega]
  · apply BitVec.eq_of_getLsbD_eq; intro i hi
    dsimp only [Arg.val_var]
    rw [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, hw1, BitVec.getLsbD_extractLsb', getLsbD_bvLane]
    have hmod : (32#64).toNat % 64 = 32 := by decide
    rw [hmod]
    simp [hi, show 32 + i < 64 by omega, show 64 + (32 + i) = 32 * 3 + i by omega]

private theorem dwords4ToWords2_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {d0 d1 d2 d3 : Arg Val i32} {v : BitVec 128}
    (hd0 : d0.val = bvLane 32 0 v)
    (hd1 : d1.val = bvLane 32 1 v)
    (hd2 : d2.val = bvLane 32 2 v)
    (hd3 : d3.val = bvLane 32 3 v)
    {k : Arg Val i64 → Arg Val i64 → Expr Val Cont rs} {m : Mem 64}
    (hk : ∀ w0 w1 : Arg Val i64,
      w0.val = BitVec.extractLsb' 0 64 v →
      w1.val = BitVec.extractLsb' 64 64 v →
      wp Γ Q X (k w0 w1) m) :
    wp Γ Q X (dwords4ToWords2 d0 d1 d2 d3 k) m := by
  unfold dwords4ToWords2
  dsimp only [wp, Op.wp, op1, op2, vals]
  rw [OpCode.wp_zext]; refine ⟨by omega, ?_⟩
  rw [OpCode.wp_zext]; refine ⟨by omega, ?_⟩
  rw [OpCode.wp_shl]; simp only [Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, lift2, Arg.val_imm, Arg.val_var]
  rw [OpCode.wp_or]; dsimp only [lift2, Arg.val_var]
  rw [OpCode.wp_zext]; refine ⟨by omega, ?_⟩
  rw [OpCode.wp_zext]; refine ⟨by omega, ?_⟩
  rw [OpCode.wp_shl]; simp only [Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, lift2]
  rw [OpCode.wp_or]; dsimp only [lift2, Arg.val_var]
  have hmod : (32#64).toNat % 64 = 32 := by decide
  apply hk
  · apply BitVec.eq_of_getLsbD_eq; intro i hi64
    dsimp only [Arg.val_var]
    rw [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, hmod, BitVec.getLsbD_setWidth,
        BitVec.getLsbD_setWidth, BitVec.getLsbD_extractLsb', hd0, hd1, getLsbD_bvLane, getLsbD_bvLane]
    by_cases hi32 : i < 32
    · simp [hi64, hi32]
    · have ht32 : i - 32 < 32 := by omega
      have ht64 : i - 32 < 64 := by omega
      simp [hi64, hi32, ht32, ht64, show 32 + (i - 32) = i by omega]
  · apply BitVec.eq_of_getLsbD_eq; intro i hi64
    dsimp only [Arg.val_var]
    rw [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, hmod, BitVec.getLsbD_setWidth,
        BitVec.getLsbD_setWidth, BitVec.getLsbD_extractLsb', hd2, hd3, getLsbD_bvLane, getLsbD_bvLane]
    by_cases hi32 : i < 32
    · simp [hi64, hi32]
    · have ht32 : i - 32 < 32 := by omega
      have ht64 : i - 32 < 64 := by omega
      simp [hi64, hi32, ht32, ht64, show 32 * 3 + (i - 32) = 64 + i by omega]

private theorem dwordToBytes4_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {d : Arg Val i32} {v : BitVec 32} (hd : d.val = v)
    {k : Arg Val i8 → Arg Val i8 → Arg Val i8 → Arg Val i8 → Expr Val Cont rs} {m : Mem 64}
    (hk : ∀ b0 b1 b2 b3 : Arg Val i8,
      b0.val = bvLane 8 0 v →
      b1.val = bvLane 8 1 v →
      b2.val = bvLane 8 2 v →
      b3.val = bvLane 8 3 v →
      wp Γ Q X (k b0 b1 b2 b3) m) :
    wp Γ Q X (dwordToBytes4 d k) m := by
  unfold dwordToBytes4
  dsimp only [wp, Op.wp, op1, op2, vals]
  rw [OpCode.wp_trunc]; refine ⟨by omega, ?_⟩
  rw [OpCode.wp_lshr]; simp only [Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, lift2, Arg.val_imm]
  rw [OpCode.wp_trunc]; refine ⟨by omega, ?_⟩
  rw [OpCode.wp_lshr]; simp only [Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, lift2]
  rw [OpCode.wp_trunc]; refine ⟨by omega, ?_⟩
  rw [OpCode.wp_lshr]; simp only [Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, lift2]
  rw [OpCode.wp_trunc]; refine ⟨by omega, ?_⟩
  have hm8 : (8#32).toNat % 32 = 8 := by decide
  have hm16 : (16#32).toNat % 32 = 16 := by decide
  have hm24 : (24#32).toNat % 32 = 24 := by decide
  apply hk
  · apply BitVec.eq_of_getLsbD_eq; intro i hi
    dsimp only [Arg.val_var]
    rw [BitVec.getLsbD_setWidth, hd, getLsbD_bvLane]; simp [hi]
  · apply BitVec.eq_of_getLsbD_eq; intro i hi
    dsimp only [Arg.val_var]
    rw [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, hm8, hd, getLsbD_bvLane]
  · apply BitVec.eq_of_getLsbD_eq; intro i hi
    dsimp only [Arg.val_var]
    rw [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, hm16, hd, getLsbD_bvLane]
  · apply BitVec.eq_of_getLsbD_eq; intro i hi
    dsimp only [Arg.val_var]
    rw [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, hm24, hd, getLsbD_bvLane]

private theorem bytes4ToDword_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {b0 b1 b2 b3 : Arg Val i8} {v : BitVec 32}
    (hb0 : b0.val = bvLane 8 0 v) (hb1 : b1.val = bvLane 8 1 v)
    (hb2 : b2.val = bvLane 8 2 v) (hb3 : b3.val = bvLane 8 3 v)
    {k : Arg Val i32 → Expr Val Cont rs} {m : Mem 64}
    (hk : ∀ r : Arg Val i32, r.val = v → wp Γ Q X (k r) m) :
    wp Γ Q X (bytes4ToDword b0 b1 b2 b3 k) m := by
  unfold bytes4ToDword
  dsimp only [wp, Op.wp, op1, op2, vals]
  rw [OpCode.wp_zext]; refine ⟨by omega, ?_⟩
  rw [OpCode.wp_zext]; refine ⟨by omega, ?_⟩
  rw [OpCode.wp_shl]; simp only [Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, lift2, Arg.val_imm, Arg.val_var]
  rw [OpCode.wp_or]; dsimp only [lift2, Arg.val_var]
  rw [OpCode.wp_zext]; refine ⟨by omega, ?_⟩
  rw [OpCode.wp_shl]; simp only [Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, lift2]
  rw [OpCode.wp_or]; dsimp only [lift2, Arg.val_var]
  rw [OpCode.wp_zext]; refine ⟨by omega, ?_⟩
  rw [OpCode.wp_shl]; simp only [Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, lift2]
  rw [OpCode.wp_or]; dsimp only [lift2, Arg.val_var]
  have hm8 : (8#32).toNat % 32 = 8 := by decide
  have hm16 : (16#32).toNat % 32 = 16 := by decide
  have hm24 : (24#32).toNat % 32 = 24 := by decide
  apply hk
  apply BitVec.eq_of_getLsbD_eq; intro i hi32
  dsimp only [Arg.val_var]
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
    hm8, hm16, hm24, hb0, hb1, hb2, hb3, getLsbD_bvLane, hi32, decide_true, Bool.true_and]
  by_cases h8 : i < 8
  · have h16 : decide (i < 16) = true := decide_eq_true (by omega)
    have h24 : decide (i < 24) = true := decide_eq_true (by omega)
    simp [h8, h16, h24]
  · by_cases h16 : i < 16
    · have ht1 : decide (i - 8 < 32) = true := decide_eq_true (by omega)
      have ht2 : decide (i - 8 < 8) = true := decide_eq_true (by omega)
      simp [h8, h16, ht1, ht2, show ¬(24 ≤ i) by omega, show 8 + (i - 8) = i by omega]
    · by_cases h24 : i < 24
      · have hf1 : decide (i - 8 < 8) = false := decide_eq_false (by omega)
        have ht1 : decide (i - 16 < 32) = true := decide_eq_true (by omega)
        have ht2 : decide (i - 16 < 8) = true := decide_eq_true (by omega)
        simp [h8, h16, h24, hf1, ht1, ht2, show 16 + (i - 16) = i by omega]
      · have hf1 : decide (i - 8 < 8) = false := decide_eq_false (by omega)
        have hf2 : decide (i - 16 < 8) = false := decide_eq_false (by omega)
        have ht1 : decide (i - 24 < 32) = true := decide_eq_true (by omega)
        have ht2 : decide (i - 24 < 8) = true := decide_eq_true (by omega)
        simp [h8, h16, h24, hf1, hf2, ht1, ht2, show 24 + (i - 24) = i by omega]

private theorem dwords4ToBytes16_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {d0 d1 d2 d3 : Arg Val i32} {v : BitVec 128}
    (hd0 : d0.val = bvLane 32 0 v) (hd1 : d1.val = bvLane 32 1 v)
    (hd2 : d2.val = bvLane 32 2 v) (hd3 : d3.val = bvLane 32 3 v)
    {k : List (Arg Val i8) → Expr Val Cont rs} {m : Mem 64}
    (hk : ∀ bs : List (Arg Val i8), bs.length = 16 →
      (∀ j, j < 16 → (bs.getD j (.imm 0#8)).val = bvLane 8 j v) →
      wp Γ Q X (k bs) m) :
    wp Γ Q X (dwords4ToBytes16 d0 d1 d2 d3 k) m := by
  unfold dwords4ToBytes16
  apply dwordToBytes4_wp hd0; intro b0 b1 b2 b3 h0 h1 h2 h3
  apply dwordToBytes4_wp hd1; intro b4 b5 b6 b7 h4 h5 h6 h7
  apply dwordToBytes4_wp hd2; intro b8 b9 b10 b11 h8 h9 h10 h11
  apply dwordToBytes4_wp hd3; intro b12 b13 b14 b15 h12 h13 h14 h15
  apply hk _ (by simp)
  intro j hj
  have := bvLane8_bvLane32 v
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨
    j = 8 ∨ j = 9 ∨ j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h0.trans (this 0 0 (by omega))
  · exact h1.trans (this 0 1 (by omega))
  · exact h2.trans (this 0 2 (by omega))
  · exact h3.trans (this 0 3 (by omega))
  · exact h4.trans (this 1 0 (by omega))
  · exact h5.trans (this 1 1 (by omega))
  · exact h6.trans (this 1 2 (by omega))
  · exact h7.trans (this 1 3 (by omega))
  · exact h8.trans (this 2 0 (by omega))
  · exact h9.trans (this 2 1 (by omega))
  · exact h10.trans (this 2 2 (by omega))
  · exact h11.trans (this 2 3 (by omega))
  · exact h12.trans (this 3 0 (by omega))
  · exact h13.trans (this 3 1 (by omega))
  · exact h14.trans (this 3 2 (by omega))
  · exact h15.trans (this 3 3 (by omega))

private theorem bytes16ToDwords4_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {bs : List (Arg Val i8)} {v : BitVec 128}
    (hbs : ∀ j, j < 16 → (bs.getD j (.imm 0#8)).val = bvLane 8 j v)
    {k : Arg Val i32 → Arg Val i32 → Arg Val i32 → Arg Val i32 → Expr Val Cont rs} {m : Mem 64}
    (hk : ∀ d0 d1 d2 d3 : Arg Val i32,
      d0.val = bvLane 32 0 v →
      d1.val = bvLane 32 1 v →
      d2.val = bvLane 32 2 v →
      d3.val = bvLane 32 3 v →
      wp Γ Q X (k d0 d1 d2 d3) m) :
    wp Γ Q X (bytes16ToDwords4 bs k) m := by
  unfold bytes16ToDwords4
  dsimp only
  have hb := fun q r (hq : q < 4) (hr : r < 4) =>
    (hbs (4 * q + r) (by omega)).trans (bvLane8_bvLane32 v q r hr).symm
  apply bytes4ToDword_wp (hb 0 0 (by omega) (by omega)) (hb 0 1 (by omega) (by omega))
    (hb 0 2 (by omega) (by omega)) (hb 0 3 (by omega) (by omega))
  intro d0 hd0
  apply bytes4ToDword_wp (hb 1 0 (by omega) (by omega)) (hb 1 1 (by omega) (by omega))
    (hb 1 2 (by omega) (by omega)) (hb 1 3 (by omega) (by omega))
  intro d1 hd1
  apply bytes4ToDword_wp (hb 2 0 (by omega) (by omega)) (hb 2 1 (by omega) (by omega))
    (hb 2 2 (by omega) (by omega)) (hb 2 3 (by omega) (by omega))
  intro d2 hd2
  apply bytes4ToDword_wp (hb 3 0 (by omega) (by omega)) (hb 3 1 (by omega) (by omega))
    (hb 3 2 (by omega) (by omega)) (hb 3 3 (by omega) (by omega))
  intro d3 hd3
  exact hk d0 d1 d2 d3 hd0 hd1 hd2 hd3

private theorem bvLane_32_shuffleDwords (v : BitVec 128) (imm : BitVec 8) (i : Nat) (hi : i < 4) :
    bvLane 32 i (shuffleDwords v imm) = bvLane 32 (imm.toNat >>> (2 * i) % 4) v := by
  unfold shuffleDwords
  apply BitVec.eq_of_getLsbD_eq
  intro j hj32
  rw [getLsbD_bvLane, getLsbD_bvOfLanes (by omega) _ (by omega)]
  have hjLt : 32 * i + j < 128 := by omega
  have hdiv : (32 * i + j) / 32 = i := by omega
  have hmod : (32 * i + j) % 32 = j := by omega
  have hi_lt : i < 128 / 32 := by omega
  have hzero : i / 4 = 0 := by omega
  simp [hj32, hdiv, hmod, hi_lt, hzero, Nat.mod_eq_of_lt hi]

private theorem scalarShufd128_eq (imm : BitVec 8) {d0 d1 d2 d3 : Arg Val i32} {v : BitVec 128}
    (h0 : d0.val = bvLane 32 0 v) (h1 : d1.val = bvLane 32 1 v)
    (h2 : d2.val = bvLane 32 2 v) (h3 : d3.val = bvLane 32 3 v) :
    let (r0, r1, r2, r3) := scalarShufd128 imm d0 d1 d2 d3
    r0.val = bvLane 32 0 (shuffleDwords v imm) ∧
    r1.val = bvLane 32 1 (shuffleDwords v imm) ∧
    r2.val = bvLane 32 2 (shuffleDwords v imm) ∧
    r3.val = bvLane 32 3 (shuffleDwords v imm) := by
  unfold scalarShufd128
  dsimp only
  have hPick : ∀ i, i < 4 →
      (match imm.toNat >>> (2 * i) % 4 with | 0 => d0 | 1 => d1 | 2 => d2 | _ => d3).val =
      bvLane 32 i (shuffleDwords v imm) := by
    intro i hi
    rw [bvLane_32_shuffleDwords v imm i hi]
    have hm : imm.toNat >>> (2 * i) % 4 < 4 := Nat.mod_lt _ (by omega)
    rcases (by omega : imm.toNat >>> (2 * i) % 4 = 0 ∨ imm.toNat >>> (2 * i) % 4 = 1 ∨
        imm.toNat >>> (2 * i) % 4 = 2 ∨ imm.toNat >>> (2 * i) % 4 = 3) with hq | hq | hq | hq <;>
      simp [hq, h0, h1, h2, h3]
  exact ⟨hPick 0 (by omega), hPick 1 (by omega), hPick 2 (by omega), hPick 3 (by omega)⟩

private theorem scalarBlendwLane_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (imm : BitVec 8) (idx : Nat) (hIdx : idx < 4)
    {ai bi : Arg Val i32} {a b : BitVec 128}
    (ha : ai.val = bvLane 32 idx a) (hb : bi.val = bvLane 32 idx b)
    {k : Arg Val i32 → Expr Val Cont rs} {m : Mem 64}
    (hk : ∀ r : Arg Val i32, r.val = bvLane 32 idx (blendWords a b imm) → wp Γ Q X (k r) m) :
    wp Γ Q X (scalarBlendwLane imm idx ai bi k) m := by
  unfold scalarBlendwLane
  dsimp only
  have hTarget : ∀ j, j < 32 →
      (bvLane 32 idx (blendWords a b imm)).getLsbD j =
        (if imm.getLsbD (2 * idx + (if j < 16 then 0 else 1)) then bi.val else ai.val).getLsbD j := by
    intro j hj32
    unfold blendWords
    rw [getLsbD_bvLane, getLsbD_bvOfLanes (by omega) _ (by omega)]
    have hi_lt : (32 * idx + j) / 16 < 128 / 16 := by omega
    simp only [hj32, decide_true, Bool.true_and, hi_lt, ↓reduceIte]
    by_cases hj16 : j < 16
    · have hd : (32 * idx + j) / 16 = 2 * idx := by omega
      have hm : (32 * idx + j) % 16 = j := by omega
      have h8 : (2 * idx) % 8 = 2 * idx := Nat.mod_eq_of_lt (by omega)
      simp only [hj16, ↓reduceIte, Nat.add_zero, hd, hm, h8]
      cases imm.getLsbD (2 * idx)
      · rw [ha]; simp [bvLane, hj32, hj16, show 16 * (2 * idx) + j = 32 * idx + j by omega]
      · rw [hb]; simp [bvLane, hj32, hj16, show 16 * (2 * idx) + j = 32 * idx + j by omega]
    · have hd : (32 * idx + j) / 16 = 2 * idx + 1 := by omega
      have hm : (32 * idx + j) % 16 = j - 16 := by omega
      have h8 : (2 * idx + 1) % 8 = 2 * idx + 1 := Nat.mod_eq_of_lt (by omega)
      simp only [hj16, ↓reduceIte, hd, hm, h8]
      cases imm.getLsbD (2 * idx + 1)
      · rw [ha]; simp [bvLane, hj32, show j - 16 < 16 by omega,
          show 16 * (2 * idx + 1) + (j - 16) = 32 * idx + j by omega]
      · rw [hb]; simp [bvLane, hj32, show j - 16 < 16 by omega,
          show 16 * (2 * idx + 1) + (j - 16) = 32 * idx + j by omega]
  cases hlo : imm.getLsbD (2 * idx) <;> cases hhi : imm.getLsbD (2 * idx + 1)
  · dsimp only
    apply hk
    apply BitVec.eq_of_getLsbD_eq; intro j hj32
    rw [hTarget j hj32]
    by_cases hj16 : j < 16 <;> simp [hj16, hlo, hhi]
  · dsimp only [wp, Op.wp, op2, vals]
    rw [OpCode.wp_and]; dsimp only [lift2, Arg.val_imm]
    rw [OpCode.wp_and]; dsimp only [lift2, Arg.val_imm]
    rw [OpCode.wp_or]; dsimp only [lift2, Arg.val_var]
    apply hk
    apply BitVec.eq_of_getLsbD_eq; intro j hj32
    dsimp only [Arg.val_var]
    rw [hTarget j hj32, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_and]
    by_cases hj16 : j < 16
    · have c1 : (65535#32).getLsbD j = true := by
        rw [BitVec.getLsbD_ofNat]; simp [hj32]
        have : (65535 : Nat) = 2 ^ 16 - 1 := by decide
        rw [this, Nat.testBit_two_pow_sub_one]; exact decide_eq_true hj16
      have c2 : (4294901760#32).getLsbD j = false := by
        rw [BitVec.getLsbD_ofNat]; simp [hj32]
        have : (4294901760 : Nat) = (2 ^ 16 - 1) <<< 16 := by decide
        rw [this, Nat.testBit_shiftLeft]; simp [show ¬(16 ≤ j) by omega]
      simp [hj16, hlo, c1, c2]
    · have c1 : (65535#32).getLsbD j = false := by
        rw [BitVec.getLsbD_ofNat]; simp [hj32]
        exact Nat.testBit_lt_two_pow
          (Nat.lt_of_lt_of_le (by decide : 65535 < 2 ^ 16) (Nat.pow_le_pow_right (by omega) (by omega)))
      have c2 : (4294901760#32).getLsbD j = true := by
        rw [BitVec.getLsbD_ofNat]; simp [hj32]
        have : (4294901760 : Nat) = (2 ^ 16 - 1) <<< 16 := by decide
        rw [this, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one]
        simp [show 16 ≤ j by omega, show j - 16 < 16 by omega]
      simp [hj16, hhi, c1, c2]
  · dsimp only [wp, Op.wp, op2, vals]
    rw [OpCode.wp_and]; dsimp only [lift2, Arg.val_imm]
    rw [OpCode.wp_and]; dsimp only [lift2, Arg.val_imm]
    rw [OpCode.wp_or]; dsimp only [lift2, Arg.val_var]
    apply hk
    apply BitVec.eq_of_getLsbD_eq; intro j hj32
    dsimp only [Arg.val_var]
    rw [hTarget j hj32, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_and]
    by_cases hj16 : j < 16
    · have c1 : (65535#32).getLsbD j = true := by
        rw [BitVec.getLsbD_ofNat]; simp [hj32]
        have : (65535 : Nat) = 2 ^ 16 - 1 := by decide
        rw [this, Nat.testBit_two_pow_sub_one]; exact decide_eq_true hj16
      have c2 : (4294901760#32).getLsbD j = false := by
        rw [BitVec.getLsbD_ofNat]; simp [hj32]
        have : (4294901760 : Nat) = (2 ^ 16 - 1) <<< 16 := by decide
        rw [this, Nat.testBit_shiftLeft]; simp [show ¬(16 ≤ j) by omega]
      simp [hj16, hlo, c1, c2]
    · have c1 : (65535#32).getLsbD j = false := by
        rw [BitVec.getLsbD_ofNat]; simp [hj32]
        exact Nat.testBit_lt_two_pow
          (Nat.lt_of_lt_of_le (by decide : 65535 < 2 ^ 16) (Nat.pow_le_pow_right (by omega) (by omega)))
      have c2 : (4294901760#32).getLsbD j = true := by
        rw [BitVec.getLsbD_ofNat]; simp [hj32]
        have : (4294901760 : Nat) = (2 ^ 16 - 1) <<< 16 := by decide
        rw [this, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one]
        simp [show 16 ≤ j by omega, show j - 16 < 16 by omega]
      simp [hj16, hhi, c1, c2]
  · dsimp only
    apply hk
    apply BitVec.eq_of_getLsbD_eq; intro j hj32
    rw [hTarget j hj32]
    by_cases hj16 : j < 16 <;> simp [hj16, hlo, hhi]

private theorem scalarBlendw128_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (imm : BitVec 8) {a0 a1 a2 a3 b0 b1 b2 b3 : Arg Val i32} {a b : BitVec 128}
    (ha0 : a0.val = bvLane 32 0 a) (ha1 : a1.val = bvLane 32 1 a)
    (ha2 : a2.val = bvLane 32 2 a) (ha3 : a3.val = bvLane 32 3 a)
    (hb0 : b0.val = bvLane 32 0 b) (hb1 : b1.val = bvLane 32 1 b)
    (hb2 : b2.val = bvLane 32 2 b) (hb3 : b3.val = bvLane 32 3 b)
    {k : Arg Val i32 → Arg Val i32 → Arg Val i32 → Arg Val i32 → Expr Val Cont rs} {m : Mem 64}
    (hk : ∀ r0 r1 r2 r3 : Arg Val i32,
      r0.val = bvLane 32 0 (blendWords a b imm) →
      r1.val = bvLane 32 1 (blendWords a b imm) →
      r2.val = bvLane 32 2 (blendWords a b imm) →
      r3.val = bvLane 32 3 (blendWords a b imm) →
      wp Γ Q X (k r0 r1 r2 r3) m) :
    wp Γ Q X (scalarBlendw128 imm a0 a1 a2 a3 b0 b1 b2 b3 k) m := by
  unfold scalarBlendw128
  apply scalarBlendwLane_wp imm 0 (by omega) ha0 hb0; intro r0 hr0
  apply scalarBlendwLane_wp imm 1 (by omega) ha1 hb1; intro r1 hr1
  apply scalarBlendwLane_wp imm 2 (by omega) ha2 hb2; intro r2 hr2
  apply scalarBlendwLane_wp imm 3 (by omega) ha3 hb3; intro r3 hr3
  exact hk r0 r1 r2 r3 hr0 hr1 hr2 hr3

private theorem scalarAlignr128_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (imm : BitVec 8) {h0 h1 h2 h3 l0 l1 l2 l3 : Arg Val i32} {hi lo : BitVec 128}
    (hh0 : h0.val = bvLane 32 0 hi) (hh1 : h1.val = bvLane 32 1 hi)
    (hh2 : h2.val = bvLane 32 2 hi) (hh3 : h3.val = bvLane 32 3 hi)
    (hl0 : l0.val = bvLane 32 0 lo) (hl1 : l1.val = bvLane 32 1 lo)
    (hl2 : l2.val = bvLane 32 2 lo) (hl3 : l3.val = bvLane 32 3 lo)
    {k : Arg Val i32 → Arg Val i32 → Arg Val i32 → Arg Val i32 → Expr Val Cont rs} {m : Mem 64}
    (hk : ∀ r0 r1 r2 r3 : Arg Val i32,
      r0.val = bvLane 32 0 (alignBytes hi lo imm) →
      r1.val = bvLane 32 1 (alignBytes hi lo imm) →
      r2.val = bvLane 32 2 (alignBytes hi lo imm) →
      r3.val = bvLane 32 3 (alignBytes hi lo imm) →
      wp Γ Q X (k r0 r1 r2 r3) m) :
    wp Γ Q X (scalarAlignr128 imm h0 h1 h2 h3 l0 l1 l2 l3 k) m := by
  unfold scalarAlignr128
  apply dwords4ToBytes16_wp hl0 hl1 hl2 hl3; intro lbs _ hLbs
  apply dwords4ToBytes16_wp hh0 hh1 hh2 hh3; intro hbs _ hHbs
  apply bytes16ToDwords4_wp (v := alignBytes hi lo imm)
  · intro i hi16
    change Arg.val ((List.map (fun i =>
      if i + imm.toNat < 16 then lbs.getD (i + imm.toNat) (.imm 0#8)
      else if i + imm.toNat < 32 then hbs.getD (i + imm.toNat - 16) (.imm 0#8) else .imm 0#8)
      (List.range 16)).getD i (.imm 0#8)) = bvLane 8 i (alignBytes hi lo imm)
    have hMap : (List.map (fun i =>
      if i + imm.toNat < 16 then lbs.getD (i + imm.toNat) (.imm 0#8)
      else if i + imm.toNat < 32 then hbs.getD (i + imm.toNat - 16) (.imm 0#8) else .imm 0#8)
      (List.range 16)).getD i (.imm 0#8) =
      (if i + imm.toNat < 16 then lbs.getD (i + imm.toNat) (.imm 0#8)
       else if i + imm.toNat < 32 then hbs.getD (i + imm.toNat - 16) (.imm 0#8) else .imm 0#8) := by
      simp [List.getD, List.getElem?_map, List.getElem?_range hi16]
    rw [hMap]
    apply BitVec.eq_of_getLsbD_eq; intro bit hbit8
    rw [getLsbD_bvLane]
    unfold alignBytes
    rw [getLsbD_bvOfLanes (by omega) _ (by omega)]
    have hdiv : (8 * i + bit) / 8 = i := by omega
    have hmod : (8 * i + bit) % 8 = bit := by omega
    have hlt16 : i < 128 / 8 := by omega
    have hzero : i / 16 = 0 := by omega
    have hmod16 : i % 16 = i := by omega
    simp only [hbit8, decide_true, Bool.true_and, hdiv, hmod, hlt16, ↓reduceIte, hzero, hmod16,
      Nat.mul_zero, Nat.zero_add]
    by_cases h16 : i + imm.toNat < 16
    · simp only [h16, ↓reduceIte]
      rw [hLbs (i + imm.toNat) h16]
    · by_cases h32 : i + imm.toNat < 32
      · simp only [h16, h32, ↓reduceIte]
        rw [hHbs (i + imm.toNat - 16) (by omega)]
      · simp [h16, h32]
  · exact hk

private theorem scalarShufb128_muxBytes_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (idx : Arg Val i8) :
    ∀ (bs : List (Arg Val i8)) (j : Nat)
      {k : Arg Val i8 → Expr Val Cont rs} {m : Mem 64},
      (∀ r : Arg Val i8,
        (bs ≠ [] → j ≤ idx.val.toNat → idx.val.toNat < j + bs.length →
          r.val = (bs.getD (idx.val.toNat - j) (.imm 0#8)).val) →
        wp Γ Q X (k r) m) →
      wp Γ Q X (scalarShufb128.muxBytes idx bs j k) m
  | [], j, k, m, hk => by
    rw [scalarShufb128.muxBytes.eq_def]
    exact hk (.imm 0#8) (fun hne _ _ => absurd rfl hne)
  | [b], j, k, m, hk => by
    rw [scalarShufb128.muxBytes.eq_def]
    apply hk b
    intro _ hle hlt
    simp only [List.length_singleton] at hlt
    have hsub : idx.val.toNat - j = 0 := by omega
    simp [hsub]
  | b :: b' :: bs, j, k, m, hk => by
    rw [scalarShufb128.muxBytes.eq_def]
    dsimp only
    apply scalarShufb128_muxBytes_wp idx (b' :: bs) (j + 1)
    intro rest hRest
    dsimp only [wp, Op.wp, op2, op3, vals]
    rw [OpCode.wp_cmp]
    dsimp only [Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, liftCmp, CmpOp.evalBits, Arg.val_imm,
      eq_mp_eq_cast, cast_eq]
    rw [OpCode.wp_select]
    dsimp only [Arg.val_var]
    apply hk (.var _)
    intro _ hle hlt
    by_cases hjEq : idx.val.toNat = j
    · have hj256 : j < 256 := by omega
      have hbEq : idx.val = BitVec.ofNat 8 j := by
        apply BitVec.eq_of_toNat_eq
        simp [hjEq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj256]
      have hsub : idx.val.toNat - j = 0 := by omega
      rw [hsub, hbEq]
      simp
    · have hgt : j + 1 ≤ idx.val.toNat := by omega
      have hne : idx.val ≠ BitVec.ofNat 8 j := by
        intro hEq
        apply hjEq
        have := congrArg BitVec.toNat hEq
        simp only [BitVec.toNat_ofNat] at this
        have hlt256 : j < 256 := by omega
        omega
      have hRestEq := hRest (List.cons_ne_nil _ _) hgt (by simp only [List.length_cons] at hlt ⊢; omega)
      have hsub : idx.val.toNat - j = (idx.val.toNat - (j + 1)) + 1 := by omega
      simp [hne, hRestEq, hsub]

private theorem scalarShufb128_doBytes_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {abs mbs : List (Arg Val i8)} {a m128 : BitVec 128}
    (hAbsLen : abs.length = 16)
    (hAbs : ∀ p, p < 16 → (abs.getD p (.imm 0#8)).val = bvLane 8 p a)
    (hMbs : ∀ p, p < 16 → (mbs.getD p (.imm 0#8)).val = bvLane 8 p m128) :
    ∀ (k : Arg Val i32 → Arg Val i32 → Arg Val i32 → Arg Val i32 → Expr Val Cont rs)
      (i : Nat) (acc : List (Arg Val i8)) (mem : Mem 64),
      acc.length = i →
      (∀ q, q < i → (acc.getD q (.imm 0#8)).val = bvLane 8 q (shuffleBytes a m128)) →
      (∀ r0 r1 r2 r3 : Arg Val i32,
        r0.val = bvLane 32 0 (shuffleBytes a m128) →
        r1.val = bvLane 32 1 (shuffleBytes a m128) →
        r2.val = bvLane 32 2 (shuffleBytes a m128) →
        r3.val = bvLane 32 3 (shuffleBytes a m128) →
        wp Γ Q X (k r0 r1 r2 r3) mem) →
      wp Γ Q X (scalarShufb128.doBytes k abs mbs i acc) mem := by
  intro k i
  suffices h : ∀ (n : Nat) (i : Nat), n = 16 - i →
      ∀ (acc : List (Arg Val i8)) (mem : Mem 64),
        acc.length = i →
        (∀ q, q < i → (acc.getD q (.imm 0#8)).val = bvLane 8 q (shuffleBytes a m128)) →
        (∀ r0 r1 r2 r3 : Arg Val i32,
          r0.val = bvLane 32 0 (shuffleBytes a m128) →
          r1.val = bvLane 32 1 (shuffleBytes a m128) →
          r2.val = bvLane 32 2 (shuffleBytes a m128) →
          r3.val = bvLane 32 3 (shuffleBytes a m128) →
          wp Γ Q X (k r0 r1 r2 r3) mem) →
        wp Γ Q X (scalarShufb128.doBytes k abs mbs i acc) mem by
    exact h (16 - i) i rfl
  intro n
  induction n with
  | zero =>
    intro i hi acc mem hLen hAcc hk
    rw [scalarShufb128.doBytes.eq_def]
    have hi16 : i ≥ 16 := by omega
    simp only [hi16, ↓reduceIte]
    apply bytes16ToDwords4_wp (fun p hp => hAcc p (by omega)) hk
  | succ n ih =>
    intro i hi acc mem hLen hAcc hk
    rw [scalarShufb128.doBytes.eq_def]
    have hiLt : i < 16 := by omega
    simp only [show ¬(i ≥ 16) by omega, ↓reduceIte]
    dsimp only [wp, Op.wp, op2, vals]
    rw [OpCode.wp_cmp]
    simp only [Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, liftCmp, CmpOp.evalBits, Arg.val_imm,
      cast_eq]
    rw [OpCode.wp_and]; dsimp only [lift2, Arg.val_imm]
    apply scalarShufb128_muxBytes_wp (.var _) abs 0
    intro sel hSel
    dsimp only [wp, Op.wp, op3, vals]
    rw [OpCode.wp_select]
    dsimp only [Arg.val_var, Arg.val_imm]
    apply ih (i + 1) (by omega) _ mem (by simp [hLen])
    · intro q hq
      have hLaneEq : bvLane 8 i (shuffleBytes a m128) =
          let index := bvLane 8 i m128
          if index.msb then 0#8 else bvLane 8 (index.toNat % 16) a := by
        unfold shuffleBytes
        apply BitVec.eq_of_getLsbD_eq; intro bit hbit8
        rw [getLsbD_bvLane, getLsbD_bvOfLanes (by omega) _ (by omega)]
        have hdiv : (8 * i + bit) / 8 = i := by omega
        have hmod : (8 * i + bit) % 8 = bit := by omega
        have hlt16 : i < 128 / 8 := by omega
        have hzero : i / 16 = 0 := by omega
        simp [hbit8, hdiv, hmod, hlt16, hzero]
      by_cases hqi : q < i
      · rw [list_getD_append_left acc [.var _] (.imm 0#8) (by omega)]
        exact hAcc q hqi
      · have hqEq : q = i := by omega
        subst hqEq
        rw [hLaneEq]
        have hGet : ∀ (v : Val i8) (d : Arg Val i8),
            ((acc ++ [Arg.var v]).getD q d).val = v := by
          intro v d
          rw [← hLen, list_getD_append_right_eq]; rfl
        rw [hGet]
        have hMb := hMbs q hiLt
        have hSlt : ((mbs.getD q (.imm 0#8)).val.slt 0#8) = (bvLane 8 q m128).msb := by
          rw [hMb]; exact BitVec.slt_zero_eq_msb
        rw [hSlt]
        by_cases hMsb : (bvLane 8 q m128).msb = true
        · simp [hMsb]
        · simp only [hMsb, Bool.false_eq_true, ↓reduceIte]
          have hIdxMod : ((mbs.getD q (.imm 0#8)).val &&& 15#8).toNat = (bvLane 8 q m128).toNat % 16 := by
            rw [hMb]
            have h1 : ((bvLane 8 q m128) &&& 15#8).toNat = (bvLane 8 q m128).toNat &&& 15 := by simp
            rw [h1, show (15 : Nat) = 2 ^ 4 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]
          have hIdxLt : ((mbs.getD q (.imm 0#8)).val &&& 15#8).toNat < 16 := by
            rw [hIdxMod]; exact Nat.mod_lt _ (by omega)
          have hAbsNe : abs ≠ [] := by intro h; simp [h] at hAbsLen
          have hSelEq := hSel hAbsNe (by omega) (by rw [hAbsLen]; exact hIdxLt)
          dsimp only [Arg.val_var] at hSelEq
          rw [Nat.sub_zero, hIdxMod] at hSelEq
          have hRes := hAbs ((bvLane 8 q m128).toNat % 16) (Nat.mod_lt _ (by omega))
          exact hSelEq.trans hRes
    · exact hk

private theorem scalarShufb128_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {a0 a1 a2 a3 m0 m1 m2 m3 : Arg Val i32} {a m128 : BitVec 128}
    (ha0 : a0.val = bvLane 32 0 a) (ha1 : a1.val = bvLane 32 1 a)
    (ha2 : a2.val = bvLane 32 2 a) (ha3 : a3.val = bvLane 32 3 a)
    (hm0 : m0.val = bvLane 32 0 m128) (hm1 : m1.val = bvLane 32 1 m128)
    (hm2 : m2.val = bvLane 32 2 m128) (hm3 : m3.val = bvLane 32 3 m128)
    {k : Arg Val i32 → Arg Val i32 → Arg Val i32 → Arg Val i32 → Expr Val Cont rs} {mem : Mem 64}
    (hk : ∀ r0 r1 r2 r3 : Arg Val i32,
      r0.val = bvLane 32 0 (shuffleBytes a m128) →
      r1.val = bvLane 32 1 (shuffleBytes a m128) →
      r2.val = bvLane 32 2 (shuffleBytes a m128) →
      r3.val = bvLane 32 3 (shuffleBytes a m128) →
      wp Γ Q X (k r0 r1 r2 r3) mem) :
    wp Γ Q X (scalarShufb128 a0 a1 a2 a3 m0 m1 m2 m3 k) mem := by
  unfold scalarShufb128
  apply dwords4ToBytes16_wp ha0 ha1 ha2 ha3; intro abs hAbsLen hAbs
  apply dwords4ToBytes16_wp hm0 hm1 hm2 hm3; intro mbs _ hMbs
  exact scalarShufb128_doBytes_wp hAbsLen hAbs hMbs k 0 [] mem rfl (fun _ h => absurd h (by omega)) hk

private theorem emitRotr32_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (x : Arg Val i32) (n : Nat) (hn : n < 32)
    {k : Arg Val i32 → Expr Val Cont rs} {m : Mem 64}
    (hk : ∀ r : Arg Val i32, r.val = x.val.rotateRight n → wp Γ Q X (k r) m) :
    wp Γ Q X (emitRotr32 x n k) m := by
  unfold emitRotr32
  dsimp only [wp, Op.wp, op2, vals]
  rw [OpCode.wp_rotr]
  dsimp only [Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, lift2, Arg.val_imm, Arg.val_var]
  have hmod : (BitVec.ofNat 32 n).toNat % 32 = n := by
    rw [BitVec.toNat_ofNat]; simp [Nat.mod_eq_of_lt hn]
  rw [hmod]
  exact hk (.var _) rfl

private theorem emitLshr32_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (x : Arg Val i32) (n : Nat) (hn : n < 32)
    {k : Arg Val i32 → Expr Val Cont rs} {m : Mem 64}
    (hk : ∀ r : Arg Val i32, r.val = x.val >>> n → wp Γ Q X (k r) m) :
    wp Γ Q X (emitLshr32 x n k) m := by
  unfold emitLshr32
  dsimp only [wp, Op.wp, op2, vals]
  rw [OpCode.wp_lshr]
  dsimp only [Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, lift2, Arg.val_imm, Arg.val_var]
  have hmod : (BitVec.ofNat 32 n).toNat % 32 = n := by
    rw [BitVec.toNat_ofNat]; simp [Nat.mod_eq_of_lt hn]
  rw [hmod]
  exact hk (.var _) rfl

private theorem emitShaSig0_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (x : Arg Val i32) {k : Arg Val i32 → Expr Val Cont rs} {m : Mem 64}
    (hk : ∀ r : Arg Val i32, r.val = Sha256.σ₀ x.val → wp Γ Q X (k r) m) :
    wp Γ Q X (emitShaSig0 x k) m := by
  unfold emitShaSig0 emitXor32
  apply emitRotr32_wp x 7 (by omega); intro r7 hr7
  apply emitRotr32_wp x 18 (by omega); intro r18 hr18
  apply emitLshr32_wp x 3 (by omega); intro s3 hs3
  dsimp only [wp, Op.wp, op2, vals]
  rw [OpCode.wp_xor]; dsimp only [lift2]
  rw [OpCode.wp_xor]; dsimp only [lift2, Arg.val_var]
  exact hk (.var _) (by simp [Sha256.σ₀, hr7, hr18, hs3])

private theorem emitShaSig1_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (x : Arg Val i32) {k : Arg Val i32 → Expr Val Cont rs} {m : Mem 64}
    (hk : ∀ r : Arg Val i32, r.val = Sha256.σ₁ x.val → wp Γ Q X (k r) m) :
    wp Γ Q X (emitShaSig1 x k) m := by
  unfold emitShaSig1 emitXor32
  apply emitRotr32_wp x 17 (by omega); intro r17 hr17
  apply emitRotr32_wp x 19 (by omega); intro r19 hr19
  apply emitLshr32_wp x 10 (by omega); intro s10 hs10
  dsimp only [wp, Op.wp, op2, vals]
  rw [OpCode.wp_xor]; dsimp only [lift2]
  rw [OpCode.wp_xor]; dsimp only [lift2, Arg.val_var]
  exact hk (.var _) (by simp [Sha256.σ₁, hr17, hr19, hs10])

private theorem emitShaRound_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (a b c d e f g h wk : Arg Val i32)
    {k : Arg Val i32 → Arg Val i32 → Arg Val i32 → Arg Val i32 →
         Arg Val i32 → Arg Val i32 → Arg Val i32 → Arg Val i32 → Expr Val Cont rs}
    {m : Mem 64}
    (hk : ∀ a' b' c' d' e' f' g' h' : Arg Val i32,
      a'.val = (Sha256.State.round { a := a.val, b := b.val, c := c.val, d := d.val,
                                     e := e.val, f := f.val, g := g.val, h := h.val } wk.val).a ∧
      b'.val = (Sha256.State.round { a := a.val, b := b.val, c := c.val, d := d.val,
                                     e := e.val, f := f.val, g := g.val, h := h.val } wk.val).b ∧
      c'.val = (Sha256.State.round { a := a.val, b := b.val, c := c.val, d := d.val,
                                     e := e.val, f := f.val, g := g.val, h := h.val } wk.val).c ∧
      d'.val = (Sha256.State.round { a := a.val, b := b.val, c := c.val, d := d.val,
                                     e := e.val, f := f.val, g := g.val, h := h.val } wk.val).d ∧
      e'.val = (Sha256.State.round { a := a.val, b := b.val, c := c.val, d := d.val,
                                     e := e.val, f := f.val, g := g.val, h := h.val } wk.val).e ∧
      f'.val = (Sha256.State.round { a := a.val, b := b.val, c := c.val, d := d.val,
                                     e := e.val, f := f.val, g := g.val, h := h.val } wk.val).f ∧
      g'.val = (Sha256.State.round { a := a.val, b := b.val, c := c.val, d := d.val,
                                     e := e.val, f := f.val, g := g.val, h := h.val } wk.val).g ∧
      h'.val = (Sha256.State.round { a := a.val, b := b.val, c := c.val, d := d.val,
                                     e := e.val, f := f.val, g := g.val, h := h.val } wk.val).h →
      wp Γ Q X (k a' b' c' d' e' f' g' h') m) :
    wp Γ Q X (emitShaRound a b c d e f g h wk k) m := by
  unfold emitShaRound emitShaCh emitShaMaj emitShaSigma0 emitShaSigma1
    emitAnd32 emitNot32 emitXor32 emitAdd32
  dsimp only [wp, Op.wp, op1, op2, vals]
  rw [OpCode.wp_and, OpCode.wp_not, OpCode.wp_and, OpCode.wp_xor]; dsimp only [lift1, lift2, Arg.val_var]
  apply emitRotr32_wp e 6 (by omega); intro r6 hr6
  apply emitRotr32_wp e 11 (by omega); intro r11 hr11
  apply emitRotr32_wp e 25 (by omega); intro r25 hr25
  dsimp only [wp, Op.wp, op2, vals]
  rw [OpCode.wp_xor, OpCode.wp_xor]; dsimp only [lift2, Arg.val_var]
  rw [OpCode.wp_add, OpCode.wp_add, OpCode.wp_add]
  simp only [Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, lift2]
  rw [OpCode.wp_and, OpCode.wp_and, OpCode.wp_and, OpCode.wp_xor, OpCode.wp_xor]
  dsimp only [lift2, Arg.val_var]
  apply emitRotr32_wp a 2 (by omega); intro r2 hr2
  apply emitRotr32_wp a 13 (by omega); intro r13 hr13
  apply emitRotr32_wp a 22 (by omega); intro r22 hr22
  dsimp only [wp, Op.wp, op2, vals]
  rw [OpCode.wp_xor, OpCode.wp_xor]; dsimp only [lift2, Arg.val_var]
  rw [OpCode.wp_add, OpCode.wp_add, OpCode.wp_add]
  simp only [Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, lift2]
  apply hk
  simp [Sha256.State.round, Sha256.ch, Sha256.maj, Sha256.«Σ₀», Sha256.«Σ₁»,
    hr6, hr11, hr25, hr2, hr13, hr22]

private theorem scalarSha256rnds2_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {cd0 cd1 cd2 cd3 ab0 ab1 ab2 ab3 wk0 wk1 wk2 wk3 : Arg Val i32}
    {cdgh abef wk : BitVec 128}
    (hcd0 : cd0.val = bvLane 32 0 cdgh) (hcd1 : cd1.val = bvLane 32 1 cdgh)
    (hcd2 : cd2.val = bvLane 32 2 cdgh) (hcd3 : cd3.val = bvLane 32 3 cdgh)
    (hab0 : ab0.val = bvLane 32 0 abef) (hab1 : ab1.val = bvLane 32 1 abef)
    (hab2 : ab2.val = bvLane 32 2 abef) (hab3 : ab3.val = bvLane 32 3 abef)
    (hwk0 : wk0.val = bvLane 32 0 wk) (hwk1 : wk1.val = bvLane 32 1 wk)
    {k : Arg Val i32 → Arg Val i32 → Arg Val i32 → Arg Val i32 → Expr Val Cont rs} {m : Mem 64}
    (hk : ∀ r0 r1 r2 r3 : Arg Val i32,
      r0.val = bvLane 32 0 (Sha256.rounds2 cdgh abef wk) →
      r1.val = bvLane 32 1 (Sha256.rounds2 cdgh abef wk) →
      r2.val = bvLane 32 2 (Sha256.rounds2 cdgh abef wk) →
      r3.val = bvLane 32 3 (Sha256.rounds2 cdgh abef wk) →
      wp Γ Q X (k r0 r1 r2 r3) m) :
    wp Γ Q X (scalarSha256rnds2 cd0 cd1 cd2 cd3 ab0 ab1 ab2 ab3 wk0 wk1 wk2 wk3 k) m := by
  unfold scalarSha256rnds2
  apply emitShaRound_wp; intro a1 b1 c1 d1 e1 f1 g1 h1 hSt1
  apply emitShaRound_wp; intro a2 b2 c2 d2 e2 f2 g2 h2 hSt2
  rcases hSt1 with ⟨ha1, hb1, hc1, hd1, he1, hf1, hg1, hh1⟩
  rcases hSt2 with ⟨ha2, _, _, _, he2, _, _, _⟩
  have hL : ∀ (idx : Nat), idx < 4 →
      bvLane 32 idx (Sha256.rounds2 cdgh abef wk) =
        let s : Sha256.State := { a := ab3.val, b := ab2.val, c := cd3.val, d := cd2.val,
                                  e := ab1.val, f := ab0.val, g := cd1.val, h := cd0.val }
        let s1 := s.round wk0.val
        let s2 := s1.round wk1.val
        if idx = 0 then s1.e else if idx = 1 then s2.e else if idx = 2 then s1.a else s2.a := by
    intro idx hIdx
    unfold Sha256.rounds2
    dsimp only
    rw [hab0, hab1, hab2, hab3, hcd0, hcd1, hcd2, hcd3, hwk0, hwk1]
    apply BitVec.eq_of_getLsbD_eq; intro bit hbit32
    rw [getLsbD_bvLane, getLsbD_bvOfLanes (by omega) _ (by omega)]
    have hdiv : (32 * idx + bit) / 32 = idx := by omega
    have hmod : (32 * idx + bit) % 32 = bit := by omega
    have hlt4 : idx < 128 / 32 := by omega
    simp only [hbit32, decide_true, Bool.true_and, hdiv, hmod, hlt4, ↓reduceIte]
    rcases idx with _ | _ | _ | _ | _ <;> first | omega | rfl
  apply hk e1 e2 a1 a2
  · rw [he1, hL 0 (by omega)]; rfl
  · rw [he2, hL 1 (by omega), ha1, hb1, hc1, hd1, he1, hf1, hg1, hh1]; rfl
  · rw [ha1, hL 2 (by omega)]; rfl
  · rw [ha2, hL 3 (by omega), ha1, hb1, hc1, hd1, he1, hf1, hg1, hh1]; rfl

private theorem scalarSha256msg1_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {a0 a1 a2 a3 b0 b1 b2 b3 : Arg Val i32} {w0123 w4 : BitVec 128}
    (ha0 : a0.val = bvLane 32 0 w0123) (ha1 : a1.val = bvLane 32 1 w0123)
    (ha2 : a2.val = bvLane 32 2 w0123) (ha3 : a3.val = bvLane 32 3 w0123)
    (hb0 : b0.val = bvLane 32 0 w4)
    {k : Arg Val i32 → Arg Val i32 → Arg Val i32 → Arg Val i32 → Expr Val Cont rs} {m : Mem 64}
    (hk : ∀ r0 r1 r2 r3 : Arg Val i32,
      r0.val = bvLane 32 0 (Sha256.msg1 w0123 w4) →
      r1.val = bvLane 32 1 (Sha256.msg1 w0123 w4) →
      r2.val = bvLane 32 2 (Sha256.msg1 w0123 w4) →
      r3.val = bvLane 32 3 (Sha256.msg1 w0123 w4) →
      wp Γ Q X (k r0 r1 r2 r3) m) :
    wp Γ Q X (scalarSha256msg1 a0 a1 a2 a3 b0 b1 b2 b3 k) m := by
  unfold scalarSha256msg1 emitAdd32
  apply emitShaSig0_wp a1; intro s0 hs0
  dsimp only [wp, Op.wp, op2, vals]; rw [OpCode.wp_add]
  simp only [Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, lift2]
  apply emitShaSig0_wp a2; intro s1 hs1
  dsimp only [wp, Op.wp, op2, vals]; rw [OpCode.wp_add]
  simp only [Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, lift2]
  apply emitShaSig0_wp a3; intro s2 hs2
  dsimp only [wp, Op.wp, op2, vals]; rw [OpCode.wp_add]
  simp only [Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, lift2]
  apply emitShaSig0_wp b0; intro s3 hs3
  dsimp only [wp, Op.wp, op2, vals]; rw [OpCode.wp_add]
  simp only [Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, lift2]
  have hL : ∀ (idx : Nat) (hIdx : idx < 4),
      bvLane 32 idx (Sha256.msg1 w0123 w4) =
        bvLane 32 idx w0123 + Sha256.σ₀ (if idx < 3 then bvLane 32 (idx + 1) w0123 else bvLane 32 0 w4) := by
    intro idx hIdx
    unfold Sha256.msg1
    apply BitVec.eq_of_getLsbD_eq; intro bit hbit32
    rw [getLsbD_bvLane, getLsbD_bvOfLanes (by omega) _ (by omega)]
    have hdiv : (32 * idx + bit) / 32 = idx := by omega
    have hmod : (32 * idx + bit) % 32 = bit := by omega
    have hlt4 : idx < 128 / 32 := by omega
    simp [hbit32, hdiv, hmod, hlt4]
  apply hk
  · dsimp only [Arg.val_var]; rw [hs0, ha0, ha1, hL 0 (by omega)]; simp
  · dsimp only [Arg.val_var]; rw [hs1, ha1, ha2, hL 1 (by omega)]; simp
  · dsimp only [Arg.val_var]; rw [hs2, ha2, ha3, hL 2 (by omega)]; simp
  · dsimp only [Arg.val_var]; rw [hs3, ha3, hb0, hL 3 (by omega)]; simp

private theorem scalarSha256msg2_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {s0 s1 s2 s3 w0 w1 w2 w3 : Arg Val i32} {sums w : BitVec 128}
    (hs0 : s0.val = bvLane 32 0 sums) (hs1 : s1.val = bvLane 32 1 sums)
    (hs2 : s2.val = bvLane 32 2 sums) (hs3 : s3.val = bvLane 32 3 sums)
    (hw2 : w2.val = bvLane 32 2 w) (hw3 : w3.val = bvLane 32 3 w)
    {k : Arg Val i32 → Arg Val i32 → Arg Val i32 → Arg Val i32 → Expr Val Cont rs} {m : Mem 64}
    (hk : ∀ r0 r1 r2 r3 : Arg Val i32,
      r0.val = bvLane 32 0 (Sha256.msg2 sums w) →
      r1.val = bvLane 32 1 (Sha256.msg2 sums w) →
      r2.val = bvLane 32 2 (Sha256.msg2 sums w) →
      r3.val = bvLane 32 3 (Sha256.msg2 sums w) →
      wp Γ Q X (k r0 r1 r2 r3) m) :
    wp Γ Q X (scalarSha256msg2 s0 s1 s2 s3 w0 w1 w2 w3 k) m := by
  unfold scalarSha256msg2 emitAdd32
  apply emitShaSig1_wp w2; intro sig2 hsig2
  dsimp only [wp, Op.wp, op2, vals]; rw [OpCode.wp_add]
  simp only [Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, lift2]
  apply emitShaSig1_wp w3; intro sig3 hsig3
  dsimp only [wp, Op.wp, op2, vals]; rw [OpCode.wp_add]
  simp only [Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, lift2]
  apply emitShaSig1_wp (.var _); intro sig16 hsig16
  dsimp only [wp, Op.wp, op2, vals]; rw [OpCode.wp_add]
  simp only [Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, lift2]
  apply emitShaSig1_wp (.var _); intro sig17 hsig17
  dsimp only [wp, Op.wp, op2, vals]; rw [OpCode.wp_add]
  simp only [Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, lift2]
  have hL : ∀ (idx : Nat), idx < 4 →
      bvLane 32 idx (Sha256.msg2 sums w) =
        let w16 := bvLane 32 0 sums + Sha256.σ₁ (bvLane 32 2 w)
        let w17 := bvLane 32 1 sums + Sha256.σ₁ (bvLane 32 3 w)
        let w18 := bvLane 32 2 sums + Sha256.σ₁ w16
        let w19 := bvLane 32 3 sums + Sha256.σ₁ w17
        if idx = 0 then w16 else if idx = 1 then w17 else if idx = 2 then w18 else w19 := by
    intro idx hIdx
    unfold Sha256.msg2
    apply BitVec.eq_of_getLsbD_eq; intro bit hbit32
    rw [getLsbD_bvLane, getLsbD_bvOfLanes (by omega) _ (by omega)]
    have hdiv : (32 * idx + bit) / 32 = idx := by omega
    have hmod : (32 * idx + bit) % 32 = bit := by omega
    have hlt4 : idx < 128 / 32 := by omega
    simp only [hbit32, decide_true, Bool.true_and, hdiv, hmod, hlt4, ↓reduceIte]
    rcases idx with _ | _ | _ | _ | _ <;> first | omega | rfl
  apply hk
  · dsimp only [Arg.val_var]; rw [hsig2, hs0, hw2, hL 0 (by omega)]; rfl
  · dsimp only [Arg.val_var]; rw [hsig3, hs1, hw3, hL 1 (by omega)]; rfl
  · dsimp only [Arg.val_var]; rw [hsig16, hsig2, hs0, hs2, hw2, hL 2 (by omega)]; rfl
  · dsimp only [Arg.val_var]; rw [hsig17, hsig3, hs1, hs3, hw3, hL 3 (by omega)]; rfl

private theorem legalSimdScalar128_goWords_wp (target : LegalTarget) (hv : target.valid = true)
    {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (on128 : Arg Val i32 → Arg Val i32 → Arg Val i32 → Arg Val i32 →
      Arg Val i32 → Arg Val i32 → Arg Val i32 → Arg Val i32 →
      (Arg Val i32 → Arg Val i32 → Arg Val i32 → Arg Val i32 → Expr Val Cont rs) → Expr Val Cont rs)
    (spec128 : BitVec 128 → BitVec 128 → BitVec 128)
    (h128 : ∀ {a0 a1 a2 a3 b0 b1 b2 b3 : Arg Val i32} {u v : BitVec 128}
      (k : Arg Val i32 → Arg Val i32 → Arg Val i32 → Arg Val i32 → Expr Val Cont rs) (m : Mem 64),
      a0.val = bvLane 32 0 u → a1.val = bvLane 32 1 u → a2.val = bvLane 32 2 u → a3.val = bvLane 32 3 u →
      b0.val = bvLane 32 0 v → b1.val = bvLane 32 1 v → b2.val = bvLane 32 2 v → b3.val = bvLane 32 3 v →
      (∀ r0 r1 r2 r3 : Arg Val i32,
        r0.val = bvLane 32 0 (spec128 u v) →
        r1.val = bvLane 32 1 (spec128 u v) →
        r2.val = bvLane 32 2 (spec128 u v) →
        r3.val = bvLane 32 3 (spec128 u v) →
        wp Γ Q X (k r0 r1 r2 r3) m) →
      wp Γ Q X (on128 a0 a1 a2 a3 b0 b1 b2 b3 k) m)
    (t : Ty) (ht : target.supportsTy t = true) (hSize : t.size ≠ 0 ∧ t.size % 128 = 0)
    (xBits yBits specFull : BitVec t.size)
    (hChunks : ∀ q, q < t.size / 128 → ∀ j, j < 128 →
      specFull.getLsbD (128 * q + j) =
        (spec128 (BitVec.extractLsb' (128 * q) 128 xBits) (BitVec.extractLsb' (128 * q) 128 yBits)).getLsbD j) :
    ∀ (rem : Nat) (q : Nat), q + rem = t.size / 128 →
      ∀ (rx ry acc : List (Arg Val i64)) (k : Tup (Arg Val) (target.legalTys t) → Expr Val Cont rs) (m : Mem 64),
        rx.length = 2 * rem → ry.length = 2 * rem → acc.length = 2 * q →
        (∀ i, i < 128 * rem → words64GetLsb rx i = xBits.getLsbD (128 * q + i)) →
        (∀ i, i < 128 * rem → words64GetLsb ry i = yBits.getLsbD (128 * q + i)) →
        (∀ i, i < 128 * q → words64GetLsb acc i = specFull.getLsbD i) →
        (∀ res : Tup (Arg Val) (target.legalTys t),
          valsTup res = encodeVal target t (ofBits t specFull) →
          wp Γ Q X (k res) m) →
        wp Γ Q X (legalSimdScalar128.goWords target on128 t k rx ry acc) m
  | 0, q, hq, rx, ry, acc, k, m, hrxLen, hryLen, haccLen, _, _, hAcc, hk => by
    rw [legalSimdScalar128.goWords.eq_def]
    have hrxNil : rx = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hryNil : ry = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hrxNil hryNil
    dsimp only
    apply unpackWords64ToLeaves_wp target hv t ht (words := acc) (off := 0) (v := ofBits t specFull)
    · intro i hi
      rw [Nat.zero_add, toBits_ofBits]
      exact hAcc i (by omega)
    · intro fres hFres
      exact packLeavesToLegal_wp target t ht fres (ofBits t specFull) hFres hk
  | rem + 1, q, hq, rx, ry, acc, k, m, hrxLen, hryLen, haccLen, hRx, hRy, hAcc, hk => by
    rw [legalSimdScalar128.goWords.eq_def]
    rcases rx with _ | ⟨x0, _ | ⟨x1, rxs⟩⟩
    · simp at hrxLen
    · simp only [List.length_cons, List.length_nil] at hrxLen; omega
    · rcases ry with _ | ⟨y0, _ | ⟨y1, rys⟩⟩
      · simp at hryLen
      · simp only [List.length_cons, List.length_nil] at hryLen; omega
      · dsimp only
        have hx0 : x0.val = BitVec.extractLsb' 0 64 (BitVec.extractLsb' (128 * q) 128 xBits) := by
          apply BitVec.eq_of_getLsbD_eq; intro j hj64
          rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_extractLsb']
          have hw := hRx j (by omega)
          have hlt128 : j < 128 := by omega
          simpa [words64GetLsb, Nat.div_eq_of_lt hj64, Nat.mod_eq_of_lt hj64, hj64, hlt128] using hw
        have hx1 : x1.val = BitVec.extractLsb' 64 64 (BitVec.extractLsb' (128 * q) 128 xBits) := by
          apply BitVec.eq_of_getLsbD_eq; intro j hj64
          rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_extractLsb']
          have hw := hRx (64 + j) (by omega)
          have hdiv : (64 + j) / 64 = 1 := by omega
          have hmod : (64 + j) % 64 = j := by omega
          have hlt128 : 64 + j < 128 := by omega
          simpa [words64GetLsb, hdiv, hmod, hj64, hlt128, Nat.add_assoc] using hw
        have hy0 : y0.val = BitVec.extractLsb' 0 64 (BitVec.extractLsb' (128 * q) 128 yBits) := by
          apply BitVec.eq_of_getLsbD_eq; intro j hj64
          rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_extractLsb']
          have hw := hRy j (by omega)
          have hlt128 : j < 128 := by omega
          simpa [words64GetLsb, Nat.div_eq_of_lt hj64, Nat.mod_eq_of_lt hj64, hj64, hlt128] using hw
        have hy1 : y1.val = BitVec.extractLsb' 64 64 (BitVec.extractLsb' (128 * q) 128 yBits) := by
          apply BitVec.eq_of_getLsbD_eq; intro j hj64
          rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_extractLsb']
          have hw := hRy (64 + j) (by omega)
          have hdiv : (64 + j) / 64 = 1 := by omega
          have hmod : (64 + j) % 64 = j := by omega
          have hlt128 : 64 + j < 128 := by omega
          simpa [words64GetLsb, hdiv, hmod, hj64, hlt128, Nat.add_assoc] using hw
        apply words2ToDwords4_wp hx0 hx1; intro a0 a1 a2 a3 ha0 ha1 ha2 ha3
        apply words2ToDwords4_wp hy0 hy1; intro b0 b1 b2 b3 hb0 hb1 hb2 hb3
        apply h128 (u := BitVec.extractLsb' (128 * q) 128 xBits)
          (v := BitVec.extractLsb' (128 * q) 128 yBits) _ m ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3
        intro r0 r1 r2 r3 hr0 hr1 hr2 hr3
        apply dwords4ToWords2_wp hr0 hr1 hr2 hr3; intro w0 w1 hw0 hw1
        apply legalSimdScalar128_goWords_wp target hv on128 spec128 h128 t ht hSize xBits yBits specFull
          hChunks rem (q + 1) (by omega) rxs rys (acc ++ [w0, w1]) k m
          (by simp only [List.length_cons] at hrxLen; omega)
          (by simp only [List.length_cons] at hryLen; omega)
          (by simp [haccLen]; omega)
        · intro i hi
          have h := hRx (128 + i) (by omega)
          have hdiv : (128 + i) / 64 = i / 64 + 2 := by omega
          have hmod : (128 + i) % 64 = i % 64 := by omega
          simp only [words64GetLsb, hdiv, hmod, List.getD, List.getElem?_cons_succ] at h
          rwa [show 128 * (q + 1) + i = 128 * q + (128 + i) by omega]
        · intro i hi
          have h := hRy (128 + i) (by omega)
          have hdiv : (128 + i) / 64 = i / 64 + 2 := by omega
          have hmod : (128 + i) % 64 = i % 64 := by omega
          simp only [words64GetLsb, hdiv, hmod, List.getD, List.getElem?_cons_succ] at h
          rwa [show 128 * (q + 1) + i = 128 * q + (128 + i) by omega]
        · intro i hi
          by_cases hltOld : i < 128 * q
          · rw [words64GetLsb_append_left acc [w0, w1] (by rw [haccLen]; omega)]
            exact hAcc i hltOld
          · have hChunkEq := hChunks q (by omega) (i - 128 * q) (by omega)
            rw [show 128 * q + (i - 128 * q) = i by omega] at hChunkEq
            rw [hChunkEq]
            by_cases hltMid : i < 128 * q + 64
            · have hdiv : i / 64 = acc.length := by rw [haccLen]; omega
              have hmod : i % 64 = i - 128 * q := by omega
              have hj64 : i - 128 * q < 64 := by omega
              simp only [words64GetLsb, hdiv, hmod, List.getD, List.getElem?_append_right (Nat.le_refl _)]
              simp [hw0, hj64]
            · have hdiv : i / 64 = acc.length + 1 := by rw [haccLen]; omega
              have hmod : i % 64 = i - (128 * q + 64) := by omega
              have hj64 : i - (128 * q + 64) < 64 := by omega
              simp only [words64GetLsb, hdiv, hmod, List.getD, List.getElem?_append_right (by omega : acc.length ≤ acc.length + 1),
                show acc.length + 1 - acc.length = 1 by omega]
              simp [hw1, hj64, show 64 + (i - (128 * q + 64)) = i - 128 * q by omega]
        · exact hk

private theorem legalSimdScalar128_wp (target : LegalTarget) (hv : target.valid = true)
    {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (on128 : Arg Val i32 → Arg Val i32 → Arg Val i32 → Arg Val i32 →
      Arg Val i32 → Arg Val i32 → Arg Val i32 → Arg Val i32 →
      (Arg Val i32 → Arg Val i32 → Arg Val i32 → Arg Val i32 → Expr Val Cont rs) → Expr Val Cont rs)
    (spec128 : BitVec 128 → BitVec 128 → BitVec 128)
    (h128 : ∀ {a0 a1 a2 a3 b0 b1 b2 b3 : Arg Val i32} {u v : BitVec 128}
      (k : Arg Val i32 → Arg Val i32 → Arg Val i32 → Arg Val i32 → Expr Val Cont rs) (m : Mem 64),
      a0.val = bvLane 32 0 u → a1.val = bvLane 32 1 u → a2.val = bvLane 32 2 u → a3.val = bvLane 32 3 u →
      b0.val = bvLane 32 0 v → b1.val = bvLane 32 1 v → b2.val = bvLane 32 2 v → b3.val = bvLane 32 3 v →
      (∀ r0 r1 r2 r3 : Arg Val i32,
        r0.val = bvLane 32 0 (spec128 u v) →
        r1.val = bvLane 32 1 (spec128 u v) →
        r2.val = bvLane 32 2 (spec128 u v) →
        r3.val = bvLane 32 3 (spec128 u v) →
        wp Γ Q X (k r0 r1 r2 r3) m) →
      wp Γ Q X (on128 a0 a1 a2 a3 b0 b1 b2 b3 k) m)
    (t : Ty) (ht : target.supportsTy t = true) (hSize : t.size ≠ 0 ∧ t.size % 128 = 0)
    (xs ys : Tup (Arg Val) (target.legalTys t)) (x y : Val t)
    (hx : valsTup xs = encodeVal target t x) (hy : valsTup ys = encodeVal target t y)
    (specFull : BitVec t.size)
    (hChunks : ∀ q, q < t.size / 128 → ∀ j, j < 128 →
      specFull.getLsbD (128 * q + j) =
        (spec128 (BitVec.extractLsb' (128 * q) 128 (toBits t x))
                 (BitVec.extractLsb' (128 * q) 128 (toBits t y))).getLsbD j)
    (k : Tup (Arg Val) (target.legalTys t) → Expr Val Cont rs) (m : Mem 64)
    (hk : ∀ res : Tup (Arg Val) (target.legalTys t),
      valsTup res = encodeVal target t (ofBits t specFull) → wp Γ Q X (k res) m) :
    wp Γ Q X (legalSimdScalar128 target on128 t xs ys k) m := by
  unfold legalSimdScalar128
  apply splitLegalToLeaves_wp target t ht xs x hx; intro fx hFx
  apply splitLegalToLeaves_wp target t ht ys y hy; intro fy hFy
  apply packLeavesToWords64_wp target hv t ht hFx; intro wx hWx _ hWxDiv
  apply packLeavesToWords64_wp target hv t ht hFy; intro wy hWy _ hWyDiv
  have hMod64 : t.size % 64 = 0 := by omega
  have hWxLen : wx.length = 2 * (t.size / 128) := by rw [hWxDiv hMod64]; omega
  have hWyLen : wy.length = 2 * (t.size / 128) := by rw [hWyDiv hMod64]; omega
  apply legalSimdScalar128_goWords_wp target hv on128 spec128 h128 t ht hSize (toBits t x) (toBits t y)
    specFull hChunks (t.size / 128) 0 (by omega) wx wy [] k m hWxLen hWyLen rfl
  · intro i hi; rw [Nat.zero_add]; exact hWx i (by omega)
  · intro i hi; rw [Nat.zero_add]; exact hWy i (by omega)
  · intro i hi; omega
  · exact hk

private theorem extractLsb_128_shuffleDwords {w : Nat} (hw : w % 128 = 0)
    (v : BitVec w) (q : Nat) (hq : q < w / 128) (imm : BitVec 8) :
    ∀ j, j < 128 →
      (shuffleDwords v imm).getLsbD (128 * q + j) =
        (shuffleDwords (BitVec.extractLsb' (128 * q) 128 v) imm).getLsbD j := by
  intro j hj
  unfold shuffleDwords
  have hLt : 128 * q + j < w := by omega
  rw [getLsbD_bvOfLanes (by omega) _ hLt, getLsbD_bvOfLanes (by omega) _ hj]
  have hW : w / 32 = 4 * (w / 128) := by omega
  have hdiv1 : (128 * q + j) / 32 = 4 * q + j / 32 := by omega
  have hmod1 : (128 * q + j) % 32 = j % 32 := by omega
  have hc1 : (128 * q + j) / 32 < w / 32 := by omega
  have hc2 : j / 32 < 128 / 32 := by omega
  have hInner : (4 * q + j / 32) / 4 = q + (j / 32) / 4 := by omega
  have hInnerZ : (j / 32) / 4 = 0 := by omega
  have hMod4 : (4 * q + j / 32) % 4 = (j / 32) % 4 := by omega
  rw [hdiv1] at hc1
  simp only [hc1, hc2, ↓reduceIte, hdiv1, hmod1, hInner, hInnerZ, hMod4, Nat.add_zero]
  rw [getLsbD_bvLane, getLsbD_bvLane, BitVec.getLsbD_extractLsb']
  have hj32 : j % 32 < 32 := Nat.mod_lt _ (by omega)
  have hm4 : imm.toNat >>> (2 * ((j / 32) % 4)) % 4 < 4 := Nat.mod_lt _ (by omega)
  have hlt128 : 32 * (0 + imm.toNat >>> (2 * ((j / 32) % 4)) % 4) + j % 32 < 128 := by omega
  simp only [hj32, decide_true, Bool.true_and, hlt128]
  congr 1
  generalize imm.toNat >>> (2 * ((j / 32) % 4)) % 4 = laneIdx at *
  omega

private theorem extractLsb_128_blendWords {w : Nat} (hw : w % 128 = 0)
    (a b : BitVec w) (q : Nat) (hq : q < w / 128) (imm : BitVec 8) :
    ∀ j, j < 128 →
      (blendWords a b imm).getLsbD (128 * q + j) =
        (blendWords (BitVec.extractLsb' (128 * q) 128 a) (BitVec.extractLsb' (128 * q) 128 b) imm).getLsbD j := by
  intro j hj
  unfold blendWords
  have hLt : 128 * q + j < w := by omega
  rw [getLsbD_bvOfLanes (by omega) _ hLt, getLsbD_bvOfLanes (by omega) _ hj]
  have hdiv1 : (128 * q + j) / 16 = 8 * q + j / 16 := by omega
  have hmod1 : (128 * q + j) % 16 = j % 16 := by omega
  have hc1 : (128 * q + j) / 16 < w / 16 := by omega
  have hc2 : j / 16 < 128 / 16 := by omega
  have hMod8 : (8 * q + j / 16) % 8 = (j / 16) % 8 := by omega
  rw [hdiv1] at hc1
  simp only [hc1, hc2, ↓reduceIte, hdiv1, hmod1, hMod8]
  have hj16 : j % 16 < 16 := Nat.mod_lt _ (by omega)
  have hlt128 : 16 * (j / 16) + j % 16 < 128 := by omega
  cases imm.getLsbD (j / 16 % 8) <;>
    simp only [Bool.false_eq_true, ↓reduceIte] <;>
    rw [getLsbD_bvLane, getLsbD_bvLane, BitVec.getLsbD_extractLsb'] <;>
    simp [hj16, hlt128, show 128 * q + (16 * (j / 16) + j % 16) = 16 * (8 * q + j / 16) + j % 16 by omega]

private theorem extractLsb_128_alignBytes {w : Nat} (hw : w % 128 = 0)
    (hi lo : BitVec w) (q : Nat) (hq : q < w / 128) (imm : BitVec 8) :
    ∀ j, j < 128 →
      (alignBytes hi lo imm).getLsbD (128 * q + j) =
        (alignBytes (BitVec.extractLsb' (128 * q) 128 hi) (BitVec.extractLsb' (128 * q) 128 lo) imm).getLsbD j := by
  intro j hj
  unfold alignBytes
  have hLt : 128 * q + j < w := by omega
  rw [getLsbD_bvOfLanes (by omega) _ hLt, getLsbD_bvOfLanes (by omega) _ hj]
  have hdiv1 : (128 * q + j) / 8 = 16 * q + j / 8 := by omega
  have hmod1 : (128 * q + j) % 8 = j % 8 := by omega
  have hc1 : (128 * q + j) / 8 < w / 8 := by omega
  have hc2 : j / 8 < 128 / 8 := by omega
  have hMod16 : (16 * q + j / 8) % 16 = (j / 8) % 16 := by omega
  have hDiv16 : (16 * q + j / 8) / 16 = q + (j / 8) / 16 := by omega
  have hDivZ : (j / 8) / 16 = 0 := by omega
  rw [hdiv1] at hc1
  simp only [hc1, hc2, ↓reduceIte, hdiv1, hmod1, hMod16, hDiv16, hDivZ, Nat.add_zero]
  by_cases h16 : j / 8 % 16 + imm.toNat < 16
  · simp only [h16, ↓reduceIte]
    rw [getLsbD_bvLane, getLsbD_bvLane, BitVec.getLsbD_extractLsb']
    have hj8 : j % 8 < 8 := Nat.mod_lt _ (by omega)
    have hlt128 : 8 * (0 + (j / 8 % 16 + imm.toNat)) + j % 8 < 128 := by omega
    simp only [Nat.zero_add] at hlt128 ⊢
    simp [hj8, hlt128, show 128 * q + (8 * (j / 8 % 16 + imm.toNat) + j % 8) =
      8 * (16 * q + (j / 8 % 16 + imm.toNat)) + j % 8 by omega]
  · by_cases h32 : j / 8 % 16 + imm.toNat < 32
    · simp only [h16, h32, ↓reduceIte]
      rw [getLsbD_bvLane, getLsbD_bvLane, BitVec.getLsbD_extractLsb']
      have hj8 : j % 8 < 8 := Nat.mod_lt _ (by omega)
      have hlt128 : 8 * (0 + (j / 8 % 16 + imm.toNat) - 16) + j % 8 < 128 := by omega
      simp only [Nat.zero_add] at hlt128 ⊢
      simp [hj8, hlt128, show 128 * q + (8 * (j / 8 % 16 + imm.toNat - 16) + j % 8) =
        8 * (16 * q + (j / 8 % 16 + imm.toNat) - 16) + j % 8 by omega]
    · simp [h16, h32]

private theorem extractLsb_128_shuffleBytes {w : Nat} (hw : w % 128 = 0)
    (a m : BitVec w) (q : Nat) (hq : q < w / 128) :
    ∀ j, j < 128 →
      (shuffleBytes a m).getLsbD (128 * q + j) =
        (shuffleBytes (BitVec.extractLsb' (128 * q) 128 a) (BitVec.extractLsb' (128 * q) 128 m)).getLsbD j := by
  intro j hj
  unfold shuffleBytes
  have hLt : 128 * q + j < w := by omega
  rw [getLsbD_bvOfLanes (by omega) _ hLt, getLsbD_bvOfLanes (by omega) _ hj]
  have hdiv1 : (128 * q + j) / 8 = 16 * q + j / 8 := by omega
  have hmod1 : (128 * q + j) % 8 = j % 8 := by omega
  have hc1 : (128 * q + j) / 8 < w / 8 := by omega
  have hc2 : j / 8 < 128 / 8 := by omega
  have hDiv16 : (16 * q + j / 8) / 16 = q := by omega
  have hDivZ : (j / 8) / 16 = 0 := by omega
  rw [hdiv1] at hc1
  simp only [hc1, hc2, ↓reduceIte, hdiv1, hmod1, hDiv16, hDivZ, Nat.mul_zero, Nat.zero_add]
  have hIdxEq : bvLane 8 (16 * q + j / 8) m = bvLane 8 (j / 8) (BitVec.extractLsb' (128 * q) 128 m) := by
    apply BitVec.eq_of_getLsbD_eq; intro bit hbit8
    rw [getLsbD_bvLane, getLsbD_bvLane, BitVec.getLsbD_extractLsb']
    have hlt128 : 8 * (j / 8) + bit < 128 := by omega
    simp [hbit8, hlt128, show 128 * q + (8 * (j / 8) + bit) = 8 * (16 * q + j / 8) + bit by omega]
  rw [hIdxEq]
  cases hmsb : (bvLane 8 (j / 8) (BitVec.extractLsb' (128 * q) 128 m)).msb
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [getLsbD_bvLane, getLsbD_bvLane, BitVec.getLsbD_extractLsb']
    have hj8 : j % 8 < 8 := Nat.mod_lt _ (by omega)
    have hm16 : (bvLane 8 (j / 8) (BitVec.extractLsb' (128 * q) 128 m)).toNat % 16 < 16 := Nat.mod_lt _ (by omega)
    have hlt128 : 8 * ((bvLane 8 (j / 8) (BitVec.extractLsb' (128 * q) 128 m)).toNat % 16) + j % 8 < 128 := by omega
    simp [hj8, hlt128, show 128 * q + (8 * ((bvLane 8 (j / 8) (BitVec.extractLsb' (128 * q) 128 m)).toNat % 16) + j % 8) =
      8 * (16 * q + (bvLane 8 (j / 8) (BitVec.extractLsb' (128 * q) 128 m)).toNat % 16) + j % 8 by omega]
  · simp

private theorem simdPair_split_shuffleDwords (a b : Ty) (ha : a.size ≠ 0 ∧ a.size % 128 = 0)
    (hb : b.size ≠ 0 ∧ b.size % 128 = 0) (x : Val (.pair a b)) (imm : BitVec 8) :
    ofBits (.pair a b) (shuffleDwords (toBits (.pair a b) x) imm) =
      (ofBits a (shuffleDwords (toBits a x.1) imm),
       ofBits b (shuffleDwords (toBits b x.2) imm)) := by
  rw [ofBits.eq_4]
  congr 1
  · congr 1
    apply BitVec.eq_of_getLsbD_eq; intro j hj
    rw [BitVec.getLsbD_extractLsb']; simp only [hj, decide_true, Bool.true_and, Nat.zero_add]
    unfold shuffleDwords
    have hLt : j < (a.pair b).size := by simp [Ty.size]; omega
    rw [getLsbD_bvOfLanes (by omega) _ hLt, getLsbD_bvOfLanes (by omega) _ hj]
    have hc1 : j / 32 < (a.pair b).size / 32 := by simp [Ty.size]; omega
    have hc2 : j / 32 < a.size / 32 := by omega
    have hSelLt : 4 * (j / 32 / 4) + imm.toNat >>> (2 * (j / 32 % 4)) % 4 < a.size / 32 := by
      have : j / 32 / 4 < a.size / 128 := by omega
      have : imm.toNat >>> (2 * (j / 32 % 4)) % 4 < 4 := Nat.mod_lt _ (by omega)
      omega
    simp only [hc1, hc2, ↓reduceIte]
    rw [getLsbD_bvLane, getLsbD_bvLane]
    have hj32 : j % 32 < 32 := Nat.mod_lt _ (by omega)
    have hBitLt : 32 * (4 * (j / 32 / 4) + imm.toNat >>> (2 * (j / 32 % 4)) % 4) + j % 32 < a.size := by omega
    simp [hj32, toBits, BitVec.getLsbD_cast, BitVec.getLsbD_append, hBitLt]
  · congr 1
    apply BitVec.eq_of_getLsbD_eq; intro j hj
    rw [BitVec.getLsbD_extractLsb']; simp only [hj, decide_true, Bool.true_and]
    unfold shuffleDwords
    have hLt : a.size + j < (a.pair b).size := by simp [Ty.size]; omega
    rw [getLsbD_bvOfLanes (by omega) _ hLt, getLsbD_bvOfLanes (by omega) _ hj]
    have hc1 : (a.size + j) / 32 < (a.pair b).size / 32 := by simp [Ty.size]; omega
    have hc2 : j / 32 < b.size / 32 := by omega
    have hdiv : (a.size + j) / 32 = a.size / 32 + j / 32 := by omega
    have hmod : (a.size + j) % 32 = j % 32 := by omega
    have hKa : (a.size / 32 + j / 32) / 4 = a.size / 128 + (j / 32) / 4 := by omega
    have hMod4 : (a.size / 32 + j / 32) % 4 = (j / 32) % 4 := by omega
    rw [hdiv] at hc1
    simp only [hc1, hc2, ↓reduceIte, hdiv, hmod, hKa, hMod4]
    rw [getLsbD_bvLane, getLsbD_bvLane]
    have hj32 : j % 32 < 32 := Nat.mod_lt _ (by omega)
    have hm4 : imm.toNat >>> (2 * (j / 32 % 4)) % 4 < 4 := Nat.mod_lt _ (by omega)
    have hNotLt : ¬(32 * (4 * (a.size / 128 + j / 32 / 4) + imm.toNat >>> (2 * (j / 32 % 4)) % 4) + j % 32 < a.size) := by omega
    simp only [hj32, decide_true, Bool.true_and, toBits, BitVec.getLsbD_cast, BitVec.getLsbD_append,
      hNotLt, ↓reduceIte]
    congr 1
    generalize imm.toNat >>> (2 * (j / 32 % 4)) % 4 = laneIdx at *
    omega

private theorem simdPair_split_blendWords (a b : Ty) (ha : a.size ≠ 0 ∧ a.size % 128 = 0)
    (hb : b.size ≠ 0 ∧ b.size % 128 = 0) (x y : Val (.pair a b)) (imm : BitVec 8) :
    ofBits (.pair a b) (blendWords (toBits (.pair a b) x) (toBits (.pair a b) y) imm) =
      (ofBits a (blendWords (toBits a x.1) (toBits a y.1) imm),
       ofBits b (blendWords (toBits b x.2) (toBits b y.2) imm)) := by
  rw [ofBits.eq_4]
  congr 1
  · congr 1
    apply BitVec.eq_of_getLsbD_eq; intro j hj
    rw [BitVec.getLsbD_extractLsb']; simp only [hj, decide_true, Bool.true_and, Nat.zero_add]
    unfold blendWords
    have hLt : j < (a.pair b).size := by simp [Ty.size]; omega
    rw [getLsbD_bvOfLanes (by omega) _ hLt, getLsbD_bvOfLanes (by omega) _ hj]
    have hc1 : j / 16 < (a.pair b).size / 16 := by simp [Ty.size]; omega
    have hc2 : j / 16 < a.size / 16 := by omega
    simp only [hc1, hc2, ↓reduceIte]
    have hj16 : j % 16 < 16 := Nat.mod_lt _ (by omega)
    have hBitLt : 16 * (j / 16) + j % 16 < a.size := by omega
    cases imm.getLsbD (j / 16 % 8) <;>
      simp only [Bool.false_eq_true, ↓reduceIte] <;>
      rw [getLsbD_bvLane, getLsbD_bvLane] <;>
      simp [hj16, toBits, BitVec.getLsbD_cast, BitVec.getLsbD_append, hBitLt]
  · congr 1
    apply BitVec.eq_of_getLsbD_eq; intro j hj
    rw [BitVec.getLsbD_extractLsb']; simp only [hj, decide_true, Bool.true_and]
    unfold blendWords
    have hLt : a.size + j < (a.pair b).size := by simp [Ty.size]; omega
    rw [getLsbD_bvOfLanes (by omega) _ hLt, getLsbD_bvOfLanes (by omega) _ hj]
    have hc1 : (a.size + j) / 16 < (a.pair b).size / 16 := by simp [Ty.size]; omega
    have hc2 : j / 16 < b.size / 16 := by omega
    have hdiv : (a.size + j) / 16 = a.size / 16 + j / 16 := by omega
    have hmod : (a.size + j) % 16 = j % 16 := by omega
    have hMod8 : (a.size / 16 + j / 16) % 8 = (j / 16) % 8 := by omega
    rw [hdiv] at hc1
    simp only [hc1, hc2, ↓reduceIte, hdiv, hmod, hMod8]
    have hj16 : j % 16 < 16 := Nat.mod_lt _ (by omega)
    have hNotLt : ¬(16 * (a.size / 16 + j / 16) + j % 16 < a.size) := by omega
    cases imm.getLsbD (j / 16 % 8) <;>
      simp only [Bool.false_eq_true, ↓reduceIte] <;>
      rw [getLsbD_bvLane, getLsbD_bvLane] <;>
      simp [hj16, toBits, BitVec.getLsbD_cast, BitVec.getLsbD_append, hNotLt,
        show 16 * (a.size / 16 + j / 16) + j % 16 - a.size = 16 * (j / 16) + j % 16 by omega]

private theorem simdPair_split_alignBytes (a b : Ty) (ha : a.size ≠ 0 ∧ a.size % 128 = 0)
    (hb : b.size ≠ 0 ∧ b.size % 128 = 0) (hi lo : Val (.pair a b)) (imm : BitVec 8) :
    ofBits (.pair a b) (alignBytes (toBits (.pair a b) hi) (toBits (.pair a b) lo) imm) =
      (ofBits a (alignBytes (toBits a hi.1) (toBits a lo.1) imm),
       ofBits b (alignBytes (toBits b hi.2) (toBits b lo.2) imm)) := by
  rw [ofBits.eq_4]
  congr 1
  · congr 1
    apply BitVec.eq_of_getLsbD_eq; intro j hj
    rw [BitVec.getLsbD_extractLsb']; simp only [hj, decide_true, Bool.true_and, Nat.zero_add]
    unfold alignBytes
    have hLt : j < (a.pair b).size := by simp [Ty.size]; omega
    rw [getLsbD_bvOfLanes (by omega) _ hLt, getLsbD_bvOfLanes (by omega) _ hj]
    have hc1 : j / 8 < (a.pair b).size / 8 := by simp [Ty.size]; omega
    have hc2 : j / 8 < a.size / 8 := by omega
    simp only [hc1, hc2, ↓reduceIte]
    have hj8 : j % 8 < 8 := Nat.mod_lt _ (by omega)
    by_cases h16 : j / 8 % 16 + imm.toNat < 16
    · simp only [h16, ↓reduceIte]
      rw [getLsbD_bvLane, getLsbD_bvLane]
      have hBitLt : 8 * (16 * (j / 8 / 16) + (j / 8 % 16 + imm.toNat)) + j % 8 < a.size := by omega
      simp [hj8, toBits, BitVec.getLsbD_cast, BitVec.getLsbD_append, hBitLt]
    · by_cases h32 : j / 8 % 16 + imm.toNat < 32
      · simp only [h16, h32, ↓reduceIte]
        rw [getLsbD_bvLane, getLsbD_bvLane]
        have hBitLt : 8 * (16 * (j / 8 / 16) + (j / 8 % 16 + imm.toNat) - 16) + j % 8 < a.size := by omega
        simp [hj8, toBits, BitVec.getLsbD_cast, BitVec.getLsbD_append, hBitLt]
      · simp [h16, h32]
  · congr 1
    apply BitVec.eq_of_getLsbD_eq; intro j hj
    rw [BitVec.getLsbD_extractLsb']; simp only [hj, decide_true, Bool.true_and]
    unfold alignBytes
    have hLt : a.size + j < (a.pair b).size := by simp [Ty.size]; omega
    rw [getLsbD_bvOfLanes (by omega) _ hLt, getLsbD_bvOfLanes (by omega) _ hj]
    have hc1 : (a.size + j) / 8 < (a.pair b).size / 8 := by simp [Ty.size]; omega
    have hc2 : j / 8 < b.size / 8 := by omega
    have hdiv : (a.size + j) / 8 = a.size / 8 + j / 8 := by omega
    have hmod : (a.size + j) % 8 = j % 8 := by omega
    have hMod16 : (a.size / 8 + j / 8) % 16 = (j / 8) % 16 := by omega
    have hDiv16 : (a.size / 8 + j / 8) / 16 = a.size / 128 + (j / 8) / 16 := by omega
    rw [hdiv] at hc1
    simp only [hc1, hc2, ↓reduceIte, hdiv, hmod, hMod16, hDiv16]
    have hj8 : j % 8 < 8 := Nat.mod_lt _ (by omega)
    by_cases h16 : j / 8 % 16 + imm.toNat < 16
    · simp only [h16, ↓reduceIte]
      rw [getLsbD_bvLane, getLsbD_bvLane]
      have hNotLt : ¬(8 * (16 * (a.size / 128 + j / 8 / 16) + (j / 8 % 16 + imm.toNat)) + j % 8 < a.size) := by omega
      simp [hj8, toBits, BitVec.getLsbD_cast, BitVec.getLsbD_append, hNotLt,
        show 8 * (16 * (a.size / 128 + j / 8 / 16) + (j / 8 % 16 + imm.toNat)) + j % 8 - a.size =
          8 * (16 * (j / 8 / 16) + (j / 8 % 16 + imm.toNat)) + j % 8 by omega]
    · by_cases h32 : j / 8 % 16 + imm.toNat < 32
      · simp only [h16, h32, ↓reduceIte]
        rw [getLsbD_bvLane, getLsbD_bvLane]
        have hNotLt : ¬(8 * (16 * (a.size / 128 + j / 8 / 16) + (j / 8 % 16 + imm.toNat) - 16) + j % 8 < a.size) := by omega
        simp [hj8, toBits, BitVec.getLsbD_cast, BitVec.getLsbD_append, hNotLt,
          show 8 * (16 * (a.size / 128 + j / 8 / 16) + (j / 8 % 16 + imm.toNat) - 16) + j % 8 - a.size =
            8 * (16 * (j / 8 / 16) + (j / 8 % 16 + imm.toNat) - 16) + j % 8 by omega]
      · simp [h16, h32]

private theorem simdPair_split_shuffleBytes (a b : Ty) (ha : a.size ≠ 0 ∧ a.size % 128 = 0)
    (hb : b.size ≠ 0 ∧ b.size % 128 = 0) (x m : Val (.pair a b)) :
    ofBits (.pair a b) (shuffleBytes (toBits (.pair a b) x) (toBits (.pair a b) m)) =
      (ofBits a (shuffleBytes (toBits a x.1) (toBits a m.1)),
       ofBits b (shuffleBytes (toBits b x.2) (toBits b m.2))) := by
  rw [ofBits.eq_4]
  congr 1
  · congr 1
    apply BitVec.eq_of_getLsbD_eq; intro j hj
    rw [BitVec.getLsbD_extractLsb']; simp only [hj, decide_true, Bool.true_and, Nat.zero_add]
    unfold shuffleBytes
    have hLt : j < (a.pair b).size := by simp [Ty.size]; omega
    rw [getLsbD_bvOfLanes (by omega) _ hLt, getLsbD_bvOfLanes (by omega) _ hj]
    have hc1 : j / 8 < (a.pair b).size / 8 := by simp [Ty.size]; omega
    have hc2 : j / 8 < a.size / 8 := by omega
    simp only [hc1, hc2, ↓reduceIte]
    have hIdxEq : bvLane 8 (j / 8) (toBits (a.pair b) m) = bvLane 8 (j / 8) (toBits a m.1) := by
      apply BitVec.eq_of_getLsbD_eq; intro bit hbit8
      rw [getLsbD_bvLane, getLsbD_bvLane]
      have hBitLt : 8 * (j / 8) + bit < a.size := by omega
      simp [hbit8, toBits, BitVec.getLsbD_cast, BitVec.getLsbD_append, hBitLt]
    rw [hIdxEq]
    cases (bvLane 8 (j / 8) (toBits a m.1)).msb
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [getLsbD_bvLane, getLsbD_bvLane]
      have hj8 : j % 8 < 8 := Nat.mod_lt _ (by omega)
      have hm16 : (bvLane 8 (j / 8) (toBits a m.1)).toNat % 16 < 16 := Nat.mod_lt _ (by omega)
      have hBitLt : 8 * (16 * (j / 8 / 16) + (bvLane 8 (j / 8) (toBits a m.1)).toNat % 16) + j % 8 < a.size := by
        have : j / 8 / 16 < a.size / 128 := by omega
        omega
      simp [hj8, toBits, BitVec.getLsbD_cast, BitVec.getLsbD_append, hBitLt]
    · simp
  · congr 1
    apply BitVec.eq_of_getLsbD_eq; intro j hj
    rw [BitVec.getLsbD_extractLsb']; simp only [hj, decide_true, Bool.true_and]
    unfold shuffleBytes
    have hLt : a.size + j < (a.pair b).size := by simp [Ty.size]; omega
    rw [getLsbD_bvOfLanes (by omega) _ hLt, getLsbD_bvOfLanes (by omega) _ hj]
    have hc1 : (a.size + j) / 8 < (a.pair b).size / 8 := by simp [Ty.size]; omega
    have hc2 : j / 8 < b.size / 8 := by omega
    have hdiv : (a.size + j) / 8 = a.size / 8 + j / 8 := by omega
    have hmod : (a.size + j) % 8 = j % 8 := by omega
    have hDiv16 : (a.size / 8 + j / 8) / 16 = a.size / 128 + (j / 8) / 16 := by omega
    rw [hdiv] at hc1
    simp only [hc1, hc2, ↓reduceIte, hdiv, hmod, hDiv16]
    have hIdxEq : bvLane 8 (a.size / 8 + j / 8) (toBits (a.pair b) m) = bvLane 8 (j / 8) (toBits b m.2) := by
      apply BitVec.eq_of_getLsbD_eq; intro bit hbit8
      rw [getLsbD_bvLane, getLsbD_bvLane]
      have hNotLt : ¬(8 * (a.size / 8 + j / 8) + bit < a.size) := by omega
      simp [hbit8, toBits, BitVec.getLsbD_cast, BitVec.getLsbD_append, hNotLt,
        show 8 * (a.size / 8 + j / 8) + bit - a.size = 8 * (j / 8) + bit by omega]
    rw [hIdxEq]
    cases (bvLane 8 (j / 8) (toBits b m.2)).msb
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [getLsbD_bvLane, getLsbD_bvLane]
      have hj8 : j % 8 < 8 := Nat.mod_lt _ (by omega)
      have hm16 : (bvLane 8 (j / 8) (toBits b m.2)).toNat % 16 < 16 := Nat.mod_lt _ (by omega)
      have hNotLt : ¬(8 * (16 * (a.size / 128 + j / 8 / 16) + (bvLane 8 (j / 8) (toBits b m.2)).toNat % 16) + j % 8 < a.size) := by omega
      simp [hj8, toBits, BitVec.getLsbD_cast, BitVec.getLsbD_append, hNotLt,
        show 8 * (16 * (a.size / 128 + j / 8 / 16) + (bvLane 8 (j / 8) (toBits b m.2)).toNat % 16) + j % 8 - a.size =
          8 * (16 * (j / 8 / 16) + (bvLane 8 (j / 8) (toBits b m.2)).toNat % 16) + j % 8 by omega]
    · simp

private theorem legalShufd_wp (target : LegalTarget) (hv : target.valid = true)
    {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} (imm : BitVec 8) :
    ∀ (t : Ty), target.supportsTy t = true → t.size ≠ 0 → t.size % 128 = 0 →
    ∀ (xs : Tup (Arg Val) (target.legalTys t)) (x : Val t),
      valsTup xs = encodeVal target t x →
      ∀ (k : Tup (Arg Val) (target.legalTys t) → Expr Val Cont rs) (m : Mem 64),
        (∀ res : Tup (Arg Val) (target.legalTys t),
          valsTup res = encodeVal target t (ofBits t (shuffleDwords (toBits t x) imm)) →
          wp Γ Q X (k res) m) →
        wp Γ Q X (legalShufd target imm t xs k) m
  | t, ht, hNe, hMod, xs, x, hx, k, m, hk => by
    rw [legalShufd.eq_def]
    have hBad : (t.size == 0 || t.size % 128 != 0) = false := by
      simp [beq_false_of_ne hNe, hMod]
    simp only [hBad, Bool.false_eq_true, ↓reduceIte]
    have hOn128 : ∀ {a0 a1 a2 a3 b0 b1 b2 b3 : Arg Val i32} {u _v : BitVec 128}
        (cont : Arg Val i32 → Arg Val i32 → Arg Val i32 → Arg Val i32 → Expr Val Cont rs) (mem : Mem 64),
        a0.val = bvLane 32 0 u → a1.val = bvLane 32 1 u → a2.val = bvLane 32 2 u → a3.val = bvLane 32 3 u →
        b0.val = bvLane 32 0 _v → b1.val = bvLane 32 1 _v → b2.val = bvLane 32 2 _v → b3.val = bvLane 32 3 _v →
        (∀ r0 r1 r2 r3 : Arg Val i32,
          r0.val = bvLane 32 0 (shuffleDwords u imm) →
          r1.val = bvLane 32 1 (shuffleDwords u imm) →
          r2.val = bvLane 32 2 (shuffleDwords u imm) →
          r3.val = bvLane 32 3 (shuffleDwords u imm) →
          wp Γ Q X (cont r0 r1 r2 r3) mem) →
        wp Γ Q X (match scalarShufd128 imm a0 a1 a2 a3 with | (r0, r1, r2, r3) => cont r0 r1 r2 r3) mem := by
      intro a0 a1 a2 a3 b0 b1 b2 b3 u _v cont mem ha0 ha1 ha2 ha3 _ _ _ _ hcont
      rcases scalarShufd128_eq imm ha0 ha1 ha2 ha3 with ⟨h0, h1, h2, h3⟩
      exact hcont _ _ _ _ h0 h1 h2 h3
    cases t with
    | bool | bits _ | float _ =>
      exact legalSimdScalar128_wp target hv _ (fun u _ => shuffleDwords u imm) hOn128
        _ ht ⟨hNe, hMod⟩ xs xs x x hx hx _
        (fun q hq j hj => extractLsb_128_shuffleDwords hMod (toBits _ x) q hq imm j hj)
        k m hk
    | pair a b =>
      dsimp only
      by_cases hPack : target.keepsPacked (.pair a b) = true
      · simp only [hPack, ↓reduceDIte]
        by_cases hVec : target.vecIntOpSupported (.shufd (.pair a b) imm) (.pair a b) false = true
        · simp only [hVec, ↓reduceIte, wp, Op.wp, op1, vals]
          rw [OpCode.wp_shufd]
          refine ⟨hNe, hMod, ?_⟩
          have hx' : (packedToTup hPack xs).fst.val = x := by
            have h1 := valsTup_packedToTup_encode target hPack hx
            rw [valsTup_single] at h1
            exact congrArg Prod.fst h1
          rw [hx']
          apply hk
          exact valsTup_tupToPacked_encode target hPack rfl
        · simp only [hVec, Bool.false_eq_true, ↓reduceIte]
          exact legalSimdScalar128_wp target hv _ (fun u _ => shuffleDwords u imm) hOn128
            (.pair a b) ht ⟨hNe, hMod⟩ xs xs x x hx hx _
            (fun q hq j hj => extractLsb_128_shuffleDwords hMod (toBits (.pair a b) x) q hq imm j hj)
            k m hk
      · have hPackF : target.keepsPacked (.pair a b) = false := Bool.eq_false_iff.mpr hPack
        simp only [hPack]
        by_cases hSplit128 : (a.size != 0 && a.size % 128 == 0 && b.size != 0 && b.size % 128 == 0) = true
        · simp only [hSplit128, ↓reduceIte]
          rcases (by simpa [Bool.and_eq_true, bne_iff_ne, beq_iff_eq] using hSplit128 :
              ((a.size ≠ 0 ∧ a.size % 128 = 0) ∧ b.size ≠ 0) ∧ b.size % 128 = 0) with
            ⟨⟨⟨haNe, haMod⟩, hbNe⟩, hbMod⟩
          have hSupPair : target.supportsTy a = true ∧ target.supportsTy b = true := by
            simpa [LegalTarget.supportsTy] using ht
          have hSplitXs := tupSplit_valsTup (fx := splitToTup hPackF xs)
          rw [valsTup_splitToTup_encode target hPackF hx] at hSplitXs
          have hxa : valsTup (tupSplit (splitToTup hPackF xs)).1 = encodeVal target a x.1 := by
            simpa [tupSplit_tupAppend] using (congrArg Prod.fst hSplitXs).symm
          have hxb : valsTup (tupSplit (splitToTup hPackF xs)).2 = encodeVal target b x.2 := by
            simpa [tupSplit_tupAppend] using (congrArg Prod.snd hSplitXs).symm
          apply legalShufd_wp target hv imm a hSupPair.1 haNe haMod _ x.1 hxa
          intro ra hRa
          apply legalShufd_wp target hv imm b hSupPair.2 hbNe hbMod _ x.2 hxb
          intro rb hRb
          apply hk
          apply valsTup_tupToSplit_encode target hPackF
          rw [simdPair_split_shuffleDwords a b ⟨haNe, haMod⟩ ⟨hbNe, hbMod⟩ x imm]
          rw [valsTup_tupAppend, hRa, hRb]
        · simp only [hSplit128, Bool.false_eq_true, ↓reduceIte]
          exact legalSimdScalar128_wp target hv _ (fun u _ => shuffleDwords u imm) hOn128
            (.pair a b) ht ⟨hNe, hMod⟩ xs xs x x hx hx _
            (fun q hq j hj => extractLsb_128_shuffleDwords hMod (toBits (.pair a b) x) q hq imm j hj)
            k m hk

private theorem legalBlendw_wp (target : LegalTarget) (hv : target.valid = true)
    {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} (imm : BitVec 8) :
    ∀ (t : Ty), target.supportsTy t = true → t.size ≠ 0 → t.size % 128 = 0 →
    ∀ (xs ys : Tup (Arg Val) (target.legalTys t)) (x y : Val t),
      valsTup xs = encodeVal target t x → valsTup ys = encodeVal target t y →
      ∀ (k : Tup (Arg Val) (target.legalTys t) → Expr Val Cont rs) (m : Mem 64),
        (∀ res : Tup (Arg Val) (target.legalTys t),
          valsTup res = encodeVal target t (ofBits t (blendWords (toBits t x) (toBits t y) imm)) →
          wp Γ Q X (k res) m) →
        wp Γ Q X (legalBlendw target imm t xs ys k) m
  | t, ht, hNe, hMod, xs, ys, x, y, hx, hy, k, m, hk => by
    rw [legalBlendw.eq_def]
    have hBad : (t.size == 0 || t.size % 128 != 0) = false := by
      simp [beq_false_of_ne hNe, hMod]
    simp only [hBad, Bool.false_eq_true, ↓reduceIte]
    have hOn128 : ∀ {a0 a1 a2 a3 b0 b1 b2 b3 : Arg Val i32} {u v : BitVec 128}
        (cont : Arg Val i32 → Arg Val i32 → Arg Val i32 → Arg Val i32 → Expr Val Cont rs) (mem : Mem 64),
        a0.val = bvLane 32 0 u → a1.val = bvLane 32 1 u → a2.val = bvLane 32 2 u → a3.val = bvLane 32 3 u →
        b0.val = bvLane 32 0 v → b1.val = bvLane 32 1 v → b2.val = bvLane 32 2 v → b3.val = bvLane 32 3 v →
        (∀ r0 r1 r2 r3 : Arg Val i32,
          r0.val = bvLane 32 0 (blendWords u v imm) →
          r1.val = bvLane 32 1 (blendWords u v imm) →
          r2.val = bvLane 32 2 (blendWords u v imm) →
          r3.val = bvLane 32 3 (blendWords u v imm) →
          wp Γ Q X (cont r0 r1 r2 r3) mem) →
        wp Γ Q X (scalarBlendw128 imm a0 a1 a2 a3 b0 b1 b2 b3 cont) mem :=
      fun cont mem ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 hcont =>
        scalarBlendw128_wp imm ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 hcont
    cases t with
    | bool | bits _ | float _ =>
      exact legalSimdScalar128_wp target hv _ (fun u v => blendWords u v imm) hOn128
        _ ht ⟨hNe, hMod⟩ xs ys x y hx hy _
        (fun q hq j hj => extractLsb_128_blendWords hMod (toBits _ x) (toBits _ y) q hq imm j hj)
        k m hk
    | pair a b =>
      dsimp only
      by_cases hPack : target.keepsPacked (.pair a b) = true
      · simp only [hPack, ↓reduceDIte]
        by_cases hVec : target.vecIntOpSupported (.blendw (.pair a b) imm) (.pair a b) false = true
        · simp only [hVec, ↓reduceIte, wp, Op.wp, op2, vals]
          rw [OpCode.wp_blendw]
          refine ⟨hNe, hMod, ?_⟩
          have hx' : (packedToTup hPack xs).fst.val = x := by
            have h1 := valsTup_packedToTup_encode target hPack hx
            rw [valsTup_single] at h1
            exact congrArg Prod.fst h1
          have hy' : (packedToTup hPack ys).fst.val = y := by
            have h1 := valsTup_packedToTup_encode target hPack hy
            rw [valsTup_single] at h1
            exact congrArg Prod.fst h1
          rw [hx', hy']
          apply hk
          exact valsTup_tupToPacked_encode target hPack rfl
        · simp only [hVec, Bool.false_eq_true, ↓reduceIte]
          exact legalSimdScalar128_wp target hv _ (fun u v => blendWords u v imm) hOn128
            (.pair a b) ht ⟨hNe, hMod⟩ xs ys x y hx hy _
            (fun q hq j hj => extractLsb_128_blendWords hMod (toBits (.pair a b) x) (toBits (.pair a b) y) q hq imm j hj)
            k m hk
      · have hPackF : target.keepsPacked (.pair a b) = false := Bool.eq_false_iff.mpr hPack
        simp only [hPack]
        by_cases hSplit128 : (a.size != 0 && a.size % 128 == 0 && b.size != 0 && b.size % 128 == 0) = true
        · simp only [hSplit128, ↓reduceIte]
          rcases (by simpa [Bool.and_eq_true, bne_iff_ne, beq_iff_eq] using hSplit128 :
              ((a.size ≠ 0 ∧ a.size % 128 = 0) ∧ b.size ≠ 0) ∧ b.size % 128 = 0) with
            ⟨⟨⟨haNe, haMod⟩, hbNe⟩, hbMod⟩
          have hSupPair : target.supportsTy a = true ∧ target.supportsTy b = true := by
            simpa [LegalTarget.supportsTy] using ht
          have hSplitXs := tupSplit_valsTup (fx := splitToTup hPackF xs)
          rw [valsTup_splitToTup_encode target hPackF hx] at hSplitXs
          have hSplitYs := tupSplit_valsTup (fx := splitToTup hPackF ys)
          rw [valsTup_splitToTup_encode target hPackF hy] at hSplitYs
          have hxa : valsTup (tupSplit (splitToTup hPackF xs)).1 = encodeVal target a x.1 := by
            simpa [tupSplit_tupAppend] using (congrArg Prod.fst hSplitXs).symm
          have hxb : valsTup (tupSplit (splitToTup hPackF xs)).2 = encodeVal target b x.2 := by
            simpa [tupSplit_tupAppend] using (congrArg Prod.snd hSplitXs).symm
          have hya : valsTup (tupSplit (splitToTup hPackF ys)).1 = encodeVal target a y.1 := by
            simpa [tupSplit_tupAppend] using (congrArg Prod.fst hSplitYs).symm
          have hyb : valsTup (tupSplit (splitToTup hPackF ys)).2 = encodeVal target b y.2 := by
            simpa [tupSplit_tupAppend] using (congrArg Prod.snd hSplitYs).symm
          apply legalBlendw_wp target hv imm a hSupPair.1 haNe haMod _ _ x.1 y.1 hxa hya
          intro ra hRa
          apply legalBlendw_wp target hv imm b hSupPair.2 hbNe hbMod _ _ x.2 y.2 hxb hyb
          intro rb hRb
          apply hk
          apply valsTup_tupToSplit_encode target hPackF
          rw [simdPair_split_blendWords a b ⟨haNe, haMod⟩ ⟨hbNe, hbMod⟩ x y imm]
          rw [valsTup_tupAppend, hRa, hRb]
        · simp only [hSplit128, Bool.false_eq_true, ↓reduceIte]
          exact legalSimdScalar128_wp target hv _ (fun u v => blendWords u v imm) hOn128
            (.pair a b) ht ⟨hNe, hMod⟩ xs ys x y hx hy _
            (fun q hq j hj => extractLsb_128_blendWords hMod (toBits (.pair a b) x) (toBits (.pair a b) y) q hq imm j hj)
            k m hk

private theorem legalAlignr_wp (target : LegalTarget) (hv : target.valid = true)
    {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} (imm : BitVec 8) :
    ∀ (t : Ty), target.supportsTy t = true → t.size ≠ 0 → t.size % 128 = 0 →
    ∀ (xs ys : Tup (Arg Val) (target.legalTys t)) (x y : Val t),
      valsTup xs = encodeVal target t x → valsTup ys = encodeVal target t y →
      ∀ (k : Tup (Arg Val) (target.legalTys t) → Expr Val Cont rs) (m : Mem 64),
        (∀ res : Tup (Arg Val) (target.legalTys t),
          valsTup res = encodeVal target t (ofBits t (alignBytes (toBits t x) (toBits t y) imm)) →
          wp Γ Q X (k res) m) →
        wp Γ Q X (legalAlignr target imm t xs ys k) m
  | t, ht, hNe, hMod, xs, ys, x, y, hx, hy, k, m, hk => by
    rw [legalAlignr.eq_def]
    have hBad : (t.size == 0 || t.size % 128 != 0) = false := by
      simp [beq_false_of_ne hNe, hMod]
    simp only [hBad, Bool.false_eq_true, ↓reduceIte]
    have hOn128 : ∀ {a0 a1 a2 a3 b0 b1 b2 b3 : Arg Val i32} {u v : BitVec 128}
        (cont : Arg Val i32 → Arg Val i32 → Arg Val i32 → Arg Val i32 → Expr Val Cont rs) (mem : Mem 64),
        a0.val = bvLane 32 0 u → a1.val = bvLane 32 1 u → a2.val = bvLane 32 2 u → a3.val = bvLane 32 3 u →
        b0.val = bvLane 32 0 v → b1.val = bvLane 32 1 v → b2.val = bvLane 32 2 v → b3.val = bvLane 32 3 v →
        (∀ r0 r1 r2 r3 : Arg Val i32,
          r0.val = bvLane 32 0 (alignBytes u v imm) →
          r1.val = bvLane 32 1 (alignBytes u v imm) →
          r2.val = bvLane 32 2 (alignBytes u v imm) →
          r3.val = bvLane 32 3 (alignBytes u v imm) →
          wp Γ Q X (cont r0 r1 r2 r3) mem) →
        wp Γ Q X (scalarAlignr128 imm a0 a1 a2 a3 b0 b1 b2 b3 cont) mem :=
      fun cont mem ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 hcont =>
        scalarAlignr128_wp imm ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 hcont
    cases t with
    | bool | bits _ | float _ =>
      exact legalSimdScalar128_wp target hv _ (fun u v => alignBytes u v imm) hOn128
        _ ht ⟨hNe, hMod⟩ xs ys x y hx hy _
        (fun q hq j hj => extractLsb_128_alignBytes hMod (toBits _ x) (toBits _ y) q hq imm j hj)
        k m hk
    | pair a b =>
      dsimp only
      by_cases hPack : target.keepsPacked (.pair a b) = true
      · simp only [hPack, ↓reduceDIte]
        by_cases hVec : target.vecIntOpSupported (.alignr (.pair a b) imm) (.pair a b) false = true
        · simp only [hVec, ↓reduceIte, wp, Op.wp, op2, vals]
          rw [OpCode.wp_alignr]
          refine ⟨hNe, hMod, ?_⟩
          have hx' : (packedToTup hPack xs).fst.val = x := by
            have h1 := valsTup_packedToTup_encode target hPack hx
            rw [valsTup_single] at h1
            exact congrArg Prod.fst h1
          have hy' : (packedToTup hPack ys).fst.val = y := by
            have h1 := valsTup_packedToTup_encode target hPack hy
            rw [valsTup_single] at h1
            exact congrArg Prod.fst h1
          rw [hx', hy']
          apply hk
          exact valsTup_tupToPacked_encode target hPack rfl
        · simp only [hVec, Bool.false_eq_true, ↓reduceIte]
          exact legalSimdScalar128_wp target hv _ (fun u v => alignBytes u v imm) hOn128
            (.pair a b) ht ⟨hNe, hMod⟩ xs ys x y hx hy _
            (fun q hq j hj => extractLsb_128_alignBytes hMod (toBits (.pair a b) x) (toBits (.pair a b) y) q hq imm j hj)
            k m hk
      · have hPackF : target.keepsPacked (.pair a b) = false := Bool.eq_false_iff.mpr hPack
        simp only [hPack]
        by_cases hSplit128 : (a.size != 0 && a.size % 128 == 0 && b.size != 0 && b.size % 128 == 0) = true
        · simp only [hSplit128, ↓reduceIte]
          rcases (by simpa [Bool.and_eq_true, bne_iff_ne, beq_iff_eq] using hSplit128 :
              ((a.size ≠ 0 ∧ a.size % 128 = 0) ∧ b.size ≠ 0) ∧ b.size % 128 = 0) with
            ⟨⟨⟨haNe, haMod⟩, hbNe⟩, hbMod⟩
          have hSupPair : target.supportsTy a = true ∧ target.supportsTy b = true := by
            simpa [LegalTarget.supportsTy] using ht
          have hSplitXs := tupSplit_valsTup (fx := splitToTup hPackF xs)
          rw [valsTup_splitToTup_encode target hPackF hx] at hSplitXs
          have hSplitYs := tupSplit_valsTup (fx := splitToTup hPackF ys)
          rw [valsTup_splitToTup_encode target hPackF hy] at hSplitYs
          have hxa : valsTup (tupSplit (splitToTup hPackF xs)).1 = encodeVal target a x.1 := by
            simpa [tupSplit_tupAppend] using (congrArg Prod.fst hSplitXs).symm
          have hxb : valsTup (tupSplit (splitToTup hPackF xs)).2 = encodeVal target b x.2 := by
            simpa [tupSplit_tupAppend] using (congrArg Prod.snd hSplitXs).symm
          have hya : valsTup (tupSplit (splitToTup hPackF ys)).1 = encodeVal target a y.1 := by
            simpa [tupSplit_tupAppend] using (congrArg Prod.fst hSplitYs).symm
          have hyb : valsTup (tupSplit (splitToTup hPackF ys)).2 = encodeVal target b y.2 := by
            simpa [tupSplit_tupAppend] using (congrArg Prod.snd hSplitYs).symm
          apply legalAlignr_wp target hv imm a hSupPair.1 haNe haMod _ _ x.1 y.1 hxa hya
          intro ra hRa
          apply legalAlignr_wp target hv imm b hSupPair.2 hbNe hbMod _ _ x.2 y.2 hxb hyb
          intro rb hRb
          apply hk
          apply valsTup_tupToSplit_encode target hPackF
          rw [simdPair_split_alignBytes a b ⟨haNe, haMod⟩ ⟨hbNe, hbMod⟩ x y imm]
          rw [valsTup_tupAppend, hRa, hRb]
        · simp only [hSplit128, Bool.false_eq_true, ↓reduceIte]
          exact legalSimdScalar128_wp target hv _ (fun u v => alignBytes u v imm) hOn128
            (.pair a b) ht ⟨hNe, hMod⟩ xs ys x y hx hy _
            (fun q hq j hj => extractLsb_128_alignBytes hMod (toBits (.pair a b) x) (toBits (.pair a b) y) q hq imm j hj)
            k m hk

private theorem legalShufb_wp (target : LegalTarget) (hv : target.valid = true)
    {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} :
    ∀ (t : Ty), target.supportsTy t = true → t.size ≠ 0 → t.size % 128 = 0 →
    ∀ (xs ys : Tup (Arg Val) (target.legalTys t)) (x y : Val t),
      valsTup xs = encodeVal target t x → valsTup ys = encodeVal target t y →
      ∀ (k : Tup (Arg Val) (target.legalTys t) → Expr Val Cont rs) (m : Mem 64),
        (∀ res : Tup (Arg Val) (target.legalTys t),
          valsTup res = encodeVal target t (ofBits t (shuffleBytes (toBits t x) (toBits t y))) →
          wp Γ Q X (k res) m) →
        wp Γ Q X (legalShufb target t xs ys k) m
  | t, ht, hNe, hMod, xs, ys, x, y, hx, hy, k, m, hk => by
    rw [legalShufb.eq_def]
    have hBad : (t.size == 0 || t.size % 128 != 0) = false := by
      simp [beq_false_of_ne hNe, hMod]
    simp only [hBad, Bool.false_eq_true, ↓reduceIte]
    have hOn128 : ∀ {a0 a1 a2 a3 b0 b1 b2 b3 : Arg Val i32} {u v : BitVec 128}
        (cont : Arg Val i32 → Arg Val i32 → Arg Val i32 → Arg Val i32 → Expr Val Cont rs) (mem : Mem 64),
        a0.val = bvLane 32 0 u → a1.val = bvLane 32 1 u → a2.val = bvLane 32 2 u → a3.val = bvLane 32 3 u →
        b0.val = bvLane 32 0 v → b1.val = bvLane 32 1 v → b2.val = bvLane 32 2 v → b3.val = bvLane 32 3 v →
        (∀ r0 r1 r2 r3 : Arg Val i32,
          r0.val = bvLane 32 0 (shuffleBytes u v) →
          r1.val = bvLane 32 1 (shuffleBytes u v) →
          r2.val = bvLane 32 2 (shuffleBytes u v) →
          r3.val = bvLane 32 3 (shuffleBytes u v) →
          wp Γ Q X (cont r0 r1 r2 r3) mem) →
        wp Γ Q X (scalarShufb128 a0 a1 a2 a3 b0 b1 b2 b3 cont) mem :=
      fun cont mem ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 hcont =>
        scalarShufb128_wp ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 hcont
    cases t with
    | bool | bits _ | float _ =>
      exact legalSimdScalar128_wp target hv _ shuffleBytes hOn128
        _ ht ⟨hNe, hMod⟩ xs ys x y hx hy _
        (fun q hq j hj => extractLsb_128_shuffleBytes hMod (toBits _ x) (toBits _ y) q hq j hj)
        k m hk
    | pair a b =>
      dsimp only
      by_cases hPack : target.keepsPacked (.pair a b) = true
      · simp only [hPack, ↓reduceDIte]
        by_cases hVec : target.vecIntOpSupported (.shufb (.pair a b)) (.pair a b) false = true
        · simp only [hVec, ↓reduceIte, wp, Op.wp, op2, vals]
          rw [OpCode.wp_shufb]
          refine ⟨hNe, hMod, ?_⟩
          have hx' : (packedToTup hPack xs).fst.val = x := by
            have h1 := valsTup_packedToTup_encode target hPack hx
            rw [valsTup_single] at h1
            exact congrArg Prod.fst h1
          have hy' : (packedToTup hPack ys).fst.val = y := by
            have h1 := valsTup_packedToTup_encode target hPack hy
            rw [valsTup_single] at h1
            exact congrArg Prod.fst h1
          rw [hx', hy']
          apply hk
          exact valsTup_tupToPacked_encode target hPack rfl
        · simp only [hVec, Bool.false_eq_true, ↓reduceIte]
          exact legalSimdScalar128_wp target hv _ shuffleBytes hOn128
            (.pair a b) ht ⟨hNe, hMod⟩ xs ys x y hx hy _
            (fun q hq j hj => extractLsb_128_shuffleBytes hMod (toBits (.pair a b) x) (toBits (.pair a b) y) q hq j hj)
            k m hk
      · have hPackF : target.keepsPacked (.pair a b) = false := Bool.eq_false_iff.mpr hPack
        simp only [hPack]
        by_cases hSplit128 : (a.size != 0 && a.size % 128 == 0 && b.size != 0 && b.size % 128 == 0) = true
        · simp only [hSplit128, ↓reduceIte]
          rcases (by simpa [Bool.and_eq_true, bne_iff_ne, beq_iff_eq] using hSplit128 :
              ((a.size ≠ 0 ∧ a.size % 128 = 0) ∧ b.size ≠ 0) ∧ b.size % 128 = 0) with
            ⟨⟨⟨haNe, haMod⟩, hbNe⟩, hbMod⟩
          have hSupPair : target.supportsTy a = true ∧ target.supportsTy b = true := by
            simpa [LegalTarget.supportsTy] using ht
          have hSplitXs := tupSplit_valsTup (fx := splitToTup hPackF xs)
          rw [valsTup_splitToTup_encode target hPackF hx] at hSplitXs
          have hSplitYs := tupSplit_valsTup (fx := splitToTup hPackF ys)
          rw [valsTup_splitToTup_encode target hPackF hy] at hSplitYs
          have hxa : valsTup (tupSplit (splitToTup hPackF xs)).1 = encodeVal target a x.1 := by
            simpa [tupSplit_tupAppend] using (congrArg Prod.fst hSplitXs).symm
          have hxb : valsTup (tupSplit (splitToTup hPackF xs)).2 = encodeVal target b x.2 := by
            simpa [tupSplit_tupAppend] using (congrArg Prod.snd hSplitXs).symm
          have hya : valsTup (tupSplit (splitToTup hPackF ys)).1 = encodeVal target a y.1 := by
            simpa [tupSplit_tupAppend] using (congrArg Prod.fst hSplitYs).symm
          have hyb : valsTup (tupSplit (splitToTup hPackF ys)).2 = encodeVal target b y.2 := by
            simpa [tupSplit_tupAppend] using (congrArg Prod.snd hSplitYs).symm
          apply legalShufb_wp target hv a hSupPair.1 haNe haMod _ _ x.1 y.1 hxa hya
          intro ra hRa
          apply legalShufb_wp target hv b hSupPair.2 hbNe hbMod _ _ x.2 y.2 hxb hyb
          intro rb hRb
          apply hk
          apply valsTup_tupToSplit_encode target hPackF
          rw [simdPair_split_shuffleBytes a b ⟨haNe, haMod⟩ ⟨hbNe, hbMod⟩ x y]
          rw [valsTup_tupAppend, hRa, hRb]
        · simp only [hSplit128, Bool.false_eq_true, ↓reduceIte]
          exact legalSimdScalar128_wp target hv _ shuffleBytes hOn128
            (.pair a b) ht ⟨hNe, hMod⟩ xs ys x y hx hy _
            (fun q hq j hj => extractLsb_128_shuffleBytes hMod (toBits (.pair a b) x) (toBits (.pair a b) y) q hq j hj)
            k m hk

/-! ### Chunk 4.3b: Scalar widening arithmetic, tree-relation bridges, and `legalOp_wp` -/

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

private theorem opWp_widen_spec {target : LegalTarget} (hv : target.valid = true) {n : Nat}
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

private theorem opWp_widen_mono {target : LegalTarget} (hv : target.valid = true) {m n : Nat}
    (hm : target.supportsTy (Ty.bits m) = true) (hn : target.supportsTy (Ty.bits n) = true)
    (hmn : m ≤ n) : target.widenWidth m ≤ target.widenWidth n := by
  have sm := opWp_widen_spec hv hm
  have sn := opWp_widen_spec hv hn
  exact sm.2.2.2.2.2.2 (target.widenWidth n) sn.1 (Nat.le_trans hmn sn.2.1)

private theorem opWp_isLegalTy_legalTys {target : LegalTarget} {t : Ty}
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

private theorem opWp_valsTup_encodeImm (target : LegalTarget) (t : Ty) (v : Val t) :
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

private theorem opWp_valsTup_tupToPacked {target : LegalTarget} {a b : Ty}
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

private theorem opWp_packedToTup_fst {target : LegalTarget} {a b : Ty}
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

private theorem opWp_valsTup_tupToSplit {target : LegalTarget} {a b : Ty}
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

private theorem opWp_valsTup_splitToTup {target : LegalTarget} {a b : Ty}
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

private theorem opWp_cast_isLegal_in {target : LegalTarget} {t : Ty} (ht : target.isLegalTy t = true)
    (hlt : target.legalTys t = [t]) (la : Tup (Arg Val) (target.legalTys t)) (x : Val t)
    (hx : valsTup la = encodeVal target t x) :
    (cast (congrArg (Tup (Arg Val)) hlt) la).fst.val = x := by
  rw [encodeVal_self target ht] at hx
  have hm : ∀ (ls : List Ty) (hl : ls = [t]) (la : Tup (Arg Val) ls)
      (hx : valsTup la = cast (congrArg (Tup Val) hl.symm) (x, ())),
      (cast (congrArg (Tup (Arg Val)) hl) la).fst.val = x := by
    intro ls hl la hx; subst hl; exact (Prod.mk.inj hx).1
  exact hm (target.legalTys t) hlt la hx

private theorem opWp_cast_isLegal_out {target : LegalTarget} {t : Ty} (ht : target.isLegalTy t = true)
    (hlt : target.legalTys t = [t]) (r : Arg Val t) :
    valsTup (cast (congrArg (Tup (Arg Val)) hlt.symm) (r, ())) = encodeVal target t r.val := by
  rw [encodeVal_self target ht]
  have hm : ∀ (ls : List Ty) (hl : ls = [t]),
      valsTup (cast (congrArg (Tup (Arg Val)) hl.symm) (r, ())) =
        cast (congrArg (Tup Val) hl.symm) (r.val, ()) := by
    intro ls hl; subst hl; rfl
  exact hm (target.legalTys t) hlt

/-! #### TreeRel1 / TreeRel2 / TreeRel3 bridges -/

private theorem opWp_floatResultWp_mono (f : Fmt) (r : Float.Model.UnpackedFloat)
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

private theorem opWp_treeRel1_lift1 (f : {n : Nat} → BitVec n → BitVec n) (g : Bool → Bool)
    (onF : (fmt : Fmt) → BitVec fmt.width → (BitVec fmt.width → Prop) → Prop)
    (honF : ∀ fmt (x : BitVec fmt.width) (p : BitVec fmt.width → Prop), p (f x) → onF fmt x p) :
    ∀ (t : Ty) (x : Val t) (p : Val t → Prop),
      p (lift1 f g t x) → TreeRel1 (fun a q => q (g a)) (fun _ a q => q (f a)) onF t x p
  | .bool, _, _, hp => hp
  | .bits _, _, _, hp => hp
  | .float fmt, x, p, hp => honF fmt x p hp
  | .pair a b, x, _p, hp =>
    opWp_treeRel1_lift1 f g onF honF a x.1 _ (opWp_treeRel1_lift1 f g onF honF b x.2 _ hp)

private theorem opWp_treeRel1_lift1_noFloat (f : {n : Nat} → BitVec n → BitVec n) (g : Bool → Bool) :
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

private theorem opWp_lift1_of_treeRel1 (f : {n : Nat} → BitVec n → BitVec n) (g : Bool → Bool)
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

private theorem opWp_treeRel3_lift3 (f : {n : Nat} → BitVec n → BitVec n → BitVec n → BitVec n)
    (g : Bool → Bool → Bool → Bool) :
    ∀ (t : Ty) (x y z : Val t) (p : Val t → Prop),
      p (lift3 f g t x y z) →
      TreeRel3 (fun a b c q => q (g a b c)) (fun _ a b c q => q (f a b c)) (fun _ a b c q => q (f a b c)) t x y z p
  | .bool, _, _, _, _, hp => hp
  | .bits _, _, _, _, _, hp => hp
  | .float _, _, _, _, _, hp => hp
  | .pair a b, x, y, z, _p, hp =>
    opWp_treeRel3_lift3 f g a x.1 y.1 z.1 _ (opWp_treeRel3_lift3 f g b x.2 y.2 z.2 _ hp)

private theorem opWp_lift3_of_treeRel3 (f : {n : Nat} → BitVec n → BitVec n → BitVec n → BitVec n)
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

private theorem opWp_liftFloatRel1_mono
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

private theorem opWp_liftFloatRel3_mono
    (op : Float.Model.Format → Float.Model.UnpackedFloat → Float.Model.UnpackedFloat → Float.Model.UnpackedFloat → Float.Model.UnpackedFloat) :
    ∀ (t : Ty) (_x _y _z : Val t) {p q : Val t → Prop}, (∀ r, p r → q r) →
      liftFloatRel3 op t _x _y _z p → liftFloatRel3 op t _x _y _z q
  | .bool, _, _, _, _, _, _, h => False.elim h
  | .bits _, _, _, _, _, _, _, h => False.elim h
  | .float fmt, _, _, _, _, _, hpq, h => opWp_floatResultWp_mono fmt _ hpq h
  | .pair a b, x, y, z, _, _, hpq, h =>
    opWp_liftFloatRel3_mono op a x.1 y.1 z.1 (fun r1 hr1 =>
      opWp_liftFloatRel3_mono op b x.2 y.2 z.2 (fun r2 => hpq (r1, r2)) hr1) h

private theorem opWp_treeRel1_float1
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

private theorem opWp_treeRel3_float3
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

private theorem opWp_treeRel1_lift1_float (f : {n : Nat} → BitVec n → BitVec n) :
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

private theorem opWp_lift1_float_of_treeRel1 (f : {n : Nat} → BitVec n → BitVec n) :
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

private theorem opWp_rotl_uniformShift :
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

private theorem opWp_shl_uniformShift :
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

private theorem opWp_setWidth_neg {n w : Nat} (hnw : n ≤ w) (a : BitVec n) :
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

private theorem opWp_not_setWidth {n w : Nat} (hnw : n ≤ w) (a : BitVec n) :
    BitVec.setWidth n (~~~(BitVec.setWidth w a)) = ~~~a := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [hi, Nat.lt_of_lt_of_le hi hnw]

private theorem opWp_ternaryLogic_setWidth {n w : Nat} (hnw : n ≤ w)
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

private theorem opWp_fshl_widened {n w : Nat} (hn : 0 < n) (hnw : n < w)
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

private theorem opWp_fshr_widened {n w : Nat} (hn : 0 < n) (hnw : n < w)
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

private theorem opWp_clz_widened {n w : Nat} (hn : 0 < n) (hnw : n < w) (a : BitVec n) :
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

private theorem opWp_cls_widened {n w : Nat} (hn : 0 < n) (hnw : n < w) (a : BitVec n) :
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

private theorem opWp_rbit_widened {n w : Nat} (_hn : 0 < n) (hnw : n < w) (a : BitVec n) :
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

private theorem opWp_ctz_widened {n w : Nat} (hn : 0 < n) (hnw : n < w) (a : BitVec n) :
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

private theorem opWp_popcnt_widened {n w : Nat} (hnw : n ≤ w) (a : BitVec n) :
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

private theorem opWp_signExtend_toInt {n w : Nat} (hnw : n ≤ w) (a : BitVec n) :
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

private theorem opWp_sdiv_widened {n w : Nat} (hnw : n ≤ w) (a b : BitVec n) :
    BitVec.setWidth n (BitVec.sdiv (BitVec.signExtend w a) (BitVec.signExtend w b)) = BitVec.sdiv a b := by
  rw [← opWp_ofInt_toInt_eq_setWidth hnw, BitVec.toInt_sdiv,
    opWp_signExtend_toInt hnw a, opWp_signExtend_toInt hnw b,
    opWp_ofInt_bmod_eq hnw, ← opWp_ofInt_bmod_eq (n := n) (w := n) (Nat.le_refl n),
    ← BitVec.toInt_sdiv, BitVec.ofInt_toInt]

private theorem opWp_srem_widened {n w : Nat} (hnw : n ≤ w) (a b : BitVec n) :
    BitVec.setWidth n (BitVec.srem (BitVec.signExtend w a) (BitVec.signExtend w b)) = BitVec.srem a b := by
  rw [← opWp_ofInt_toInt_eq_setWidth hnw, BitVec.toInt_srem,
    opWp_signExtend_toInt hnw a, opWp_signExtend_toInt hnw b,
    ← BitVec.toInt_srem, BitVec.ofInt_toInt]

private theorem opWp_sdivDefined_widened {n w : Nat} (hn : 0 < n) (hnw : n < w)
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

private theorem opWp_addc_widened {n w : Nat} (hn : 0 < n) (hnw : n < w) (a b : BitVec n) (c : Bool) :
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

private theorem opWp_subb_widened {n w : Nat} (hn : 0 < n) (hnw : n < w) (a b : BitVec n) (c : Bool) :
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

private theorem opWp_umulw_widened {n w : Nat} (_hn : 0 < n) (hnw : n < w) (a b : BitVec n) :
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

private theorem opWp_smulw_widened {n w : Nat} (hn : 0 < n) (hnw : n < w) (a b : BitVec n) :
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

private theorem opWp_fptoui_widened {n w : Nat} (_hn : 0 < n) (hnw : n ≤ w)
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

private theorem opWp_fptosi_widened {n w : Nat} (hnw : n ≤ w) (z : Int) :
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

private theorem opWp_lift1_noFloat_of_treeRel1
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

private theorem opWp_float1_isFloatTree_of_treeRel1
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

private theorem opWp_float3_isFloatTree_of_treeRel3
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

private theorem op1_wp_eq {a : Ty} {rs : List Ty} (c : OpCode [a] rs) (x : Arg Val a) (P : Tup Val rs → Prop) :
    (op1 c x).wp P = c.wp (x.val, ()) P := rfl

private theorem op2_wp_eq {a b : Ty} {rs : List Ty} (c : OpCode [a, b] rs) (x : Arg Val a) (y : Arg Val b) (P : Tup Val rs → Prop) :
    (op2 c x y).wp P = c.wp (x.val, y.val, ()) P := rfl

private theorem op3_wp_eq {a b d : Ty} {rs : List Ty} (c : OpCode [a, b, d] rs) (x : Arg Val a) (y : Arg Val b) (z : Arg Val d) (P : Tup Val rs → Prop) :
    (op3 c x y z).wp P = c.wp (x.val, y.val, z.val, ()) P := rfl

private theorem legalOp_intBin_wp (target : LegalTarget)
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

private theorem legalOp_bitwiseBin_wp (target : LegalTarget)
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

private theorem legalOp_shiftBin_wp (target : LegalTarget)
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

private theorem legalOp_floatBin_wp (target : LegalTarget)
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

private theorem op1_setWidth_self {op : {k : Nat} → BitVec k → BitVec k} {n w : Nat}
    (h : n = w) {a' : BitVec w} {a : BitVec n} (ha : a' = BitVec.setWidth w a) :
    op a' = BitVec.setWidth w (op a) := by
  subst h; rw [ha, BitVec.setWidth_eq, BitVec.setWidth_eq]

private theorem op2_setWidth_self {op : {k : Nat} → BitVec k → BitVec k → BitVec k} {n w : Nat}
    (h : n = w) {a' b' : BitVec w} {a b : BitVec n}
    (ha : a' = BitVec.setWidth w a) (hb : b' = BitVec.setWidth w b) :
    op a' b' = BitVec.setWidth w (op a b) := by
  subst h; rw [ha, hb, BitVec.setWidth_eq, BitVec.setWidth_eq, BitVec.setWidth_eq]

private theorem op3_setWidth_self {op : {k : Nat} → BitVec k → BitVec k → BitVec k → BitVec k} {n w : Nat}
    (h : n = w) {a' b' c' : BitVec w} {a b c : BitVec n}
    (ha : a' = BitVec.setWidth w a) (hb : b' = BitVec.setWidth w b) (hc : c' = BitVec.setWidth w c) :
    op a' b' c' = BitVec.setWidth w (op a b c) := by
  subst h; rw [ha, hb, hc, BitVec.setWidth_eq, BitVec.setWidth_eq, BitVec.setWidth_eq, BitVec.setWidth_eq]

private theorem op2_pred_self {P : {k : Nat} → BitVec k → BitVec k → Prop} {n w : Nat}
    (h : n = w) {a' b' : BitVec w} {a b : BitVec n}
    (ha : a' = BitVec.setWidth w a) (hb : b' = BitVec.setWidth w b) :
    P a b → P a' b' := by
  subst h; rw [ha, hb, BitVec.setWidth_eq, BitVec.setWidth_eq]; exact id

private theorem opWp_words64_two (ws : List (Arg Val i64)) (v : BitVec 128)
    (hbits : ∀ i < 128, words64GetLsb ws i = v.getLsbD i) (hlen : ws.length = 2) :
    (ws.getD 0 (Arg.imm 0#64)).val = BitVec.extractLsb' 0 64 v ∧
    (ws.getD 1 (Arg.imm 0#64)).val = BitVec.extractLsb' 64 64 v := by
  rcases ws with _ | ⟨w0, _ | ⟨w1, _ | _⟩⟩ <;> simp at hlen
  constructor <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi
  · rw [BitVec.getLsbD_extractLsb', decide_eq_true hi, Bool.true_and, Nat.zero_add, ← hbits i (by omega)]
    simp only [words64GetLsb, Nat.div_eq_of_lt hi, Nat.mod_eq_of_lt hi]
  · rw [BitVec.getLsbD_extractLsb', decide_eq_true hi, Bool.true_and, ← hbits (64 + i) (by omega)]
    simp only [words64GetLsb, show (64 + i) / 64 = 1 by omega, show (64 + i) % 64 = i by omega]

private theorem dite_true_wp {α : Sort _} {P : α → Prop} {c : Prop} [Decidable c]
    {t : c → α} {e : ¬ c → α} (hc : c) (ht : P (t hc)) : P (dite c t e) := by
  rw [dite_eq_left hc]; exact ht

private theorem dite_false_wp {α : Sort _} {P : α → Prop} {c : Prop} [Decidable c]
    {t : c → α} {e : ¬ c → α} (hc : ¬ c) (he : P (e hc)) : P (dite c t e) := by
  rw [dite_eq_right hc]; exact he

private def isNatTy (target : LegalTarget) : Ty → Bool
  | .bits n => target.isLegalTy (.bits n) && (target.widenWidth n == n)
  | t => target.isLegalTy t

private theorem legalOp_wp (target : LegalTarget) (hv : target.valid = true)
    {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {G : Ctx Val (LVar target Val)} (hG : CGoodWp target G)
    {ts : List Ty} {op₁ : Op Val ts} {op₂ : Op (LVar target Val) ts}
    (hop : OpRel G op₁ op₂) (hsupp : target.supportsOpCode op₁.code = true)
    {P : Tup Val ts → Prop}
    {k : Tup (LVar target Val) ts → Expr Val Cont rs} {m : Mem 64}
    (hw : op₁.wp P)
    (hk : ∀ (r : Tup Val ts) (lr : Tup (LVar target Val) ts),
      TRel (fun t x lv => valsTup lv = encodeVal target t x) r lr →
      P r → wp Γ Q X (k lr) m) :
    wp Γ Q X (legalOp target op₂ k) m := by
  rcases hop with ⟨code, hargs⟩
  dsimp only at hsupp hw
  cases code with
  | copy t =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩; cases hargs
    rw [legalOp.eq_1]
    exact hk _ _ (TRel.cons (valsTup_legalArg target hG ha) TRel.nil) hw
  | add t =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩; rcases hargs with _ | @⟨_, _, b₁, b₂, _, _, hb, hargs⟩; cases hargs
    rw [legalOp.eq_2]
    exact legalOp_intBin_wp target hG OpCode.add (fun {n} x1 x2 => x1 + x2) (fun x1 x2 => x1 ^^ x2)
      (fun u x y p => OpCode.wp_add u (x, y, ()) p) (fun _ => rfl)
      (fun x y cont => Expr.let_ (op2 (OpCode.xor Ty.bool) x y) fun (r, _) => cont (Arg.var r))
      (fun a' b' a b cont m' ha' hb' hpre => by
        rw [wp_let, op2_wp_eq, OpCode.wp_xor, ha', hb']; exact hpre _ rfl)
      (fun n hsn a' b' a b cont m' ha' hb' hpre =>
        legalBitsArith_wp target hsn (OpCode.add (Ty.bits n)) trivial a' b' a b ha' hb'
          (by dsimp only [Op.wp, vals]; rw [OpCode.wp_add]; simpa [lift2] using hpre))
      hsupp ha hb hw hk
  | sub t =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩; rcases hargs with _ | @⟨_, _, b₁, b₂, _, _, hb, hargs⟩; cases hargs
    rw [legalOp.eq_3]
    exact legalOp_intBin_wp target hG OpCode.sub (fun {n} x1 x2 => x1 - x2) (fun x1 x2 => x1 ^^ x2)
      (fun u x y p => OpCode.wp_sub u (x, y, ()) p) (fun _ => rfl)
      (fun x y cont => Expr.let_ (op2 (OpCode.xor Ty.bool) x y) fun (r, _) => cont (Arg.var r))
      (fun a' b' a b cont m' ha' hb' hpre => by
        rw [wp_let, op2_wp_eq, OpCode.wp_xor, ha', hb']; exact hpre _ rfl)
      (fun n hsn a' b' a b cont m' ha' hb' hpre =>
        legalBitsArith_wp target hsn (OpCode.sub (Ty.bits n)) trivial a' b' a b ha' hb'
          (by dsimp only [Op.wp, vals]; rw [OpCode.wp_sub]; simpa [lift2] using hpre))
      hsupp ha hb hw hk
  | mul t =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩; rcases hargs with _ | @⟨_, _, b₁, b₂, _, _, hb, hargs⟩; cases hargs
    rw [legalOp.eq_4]
    exact legalOp_intBin_wp target hG OpCode.mul (fun {n} x1 x2 => x1 * x2) (fun x1 x2 => x1 && x2)
      (fun u x y p => OpCode.wp_mul u (x, y, ()) p) (fun _ => rfl)
      (fun x y cont => Expr.let_ (op2 (OpCode.and Ty.bool) x y) fun (r, _) => cont (Arg.var r))
      (fun a' b' a b cont m' ha' hb' hpre => by
        rw [wp_let, op2_wp_eq, OpCode.wp_and, ha', hb']; exact hpre _ rfl)
      (fun n hsn a' b' a b cont m' ha' hb' hpre =>
        legalBitsArith_wp target hsn (OpCode.mul (Ty.bits n)) trivial a' b' a b ha' hb'
          (by dsimp only [Op.wp, vals]; rw [OpCode.wp_mul]; simpa [lift2] using hpre))
      hsupp ha hb hw hk
  | neg t =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩; cases hargs
    dsimp only [Op.wp, vals] at hw
    rw [OpCode.wp_neg] at hw
    rw [legalOp.eq_5]
    cases hf : t.hasFloat
    · simp only [hf, Bool.false_eq_true, ↓reduceIte] at hw ⊢
      refine legalUnaryTree_wp target OpCode.neg (fun u => target.vecIntOpSupported (OpCode.neg u) u false)
        (fun x cont => cont x)
        (fun n x cont => if (n == 0) = true then cont (Arg.imm 0#(target.widenWidth n)) else
          Expr.let_ (op1 (OpCode.neg (Ty.bits (target.widenWidth n))) x) fun (r, _) =>
            emitMaskToN n (target.widenWidth n) (Arg.var r) cont)
        (fun _ _ _ => Expr.hlt)
        (onB := fun a q => q a) (onBi := fun _ a q => q (-a)) (onF := fun _ _ _ => False)
        ?_ ?_ (fun _ _ _ _ _ _ _ h => False.elim h)
        ?_ (fun _ _ _ hpq h => hpq _ h) (fun _ _ _ _ hpq h => hpq _ h) (fun _ _ _ _ _ h => False.elim h)
        t hsupp (legalArg target a₂) a₁.val (valsTup_legalArg target hG ha) (fun res => k (res, ())) m
        (opWp_treeRel1_lift1_noFloat (fun {n} x => -x) id t hf _ _
          fun fres hfres => hk _ _ (TRel.cons hfres TRel.nil) hw)
      · intro x' x cont m' hx' hpre; exact hpre x' hx'
      · intro n hsn x' x cont m' hx' hpre
        have hs := opWp_widen_spec hv hsn
        dsimp only at hs ⊢
        by_cases hn0 : n = 0
        · subst hn0; simp only [beq_self_eq_true, ↓reduceIte]
          apply hpre (Arg.imm 0#(target.widenWidth 0))
          have h0 : (-x : BitVec 0) = 0#0 := Subsingleton.elim _ _
          rw [Arg.val_imm, h0]; apply BitVec.eq_of_toNat_eq; simp
        · simp only [beq_iff_eq, hn0, ↓reduceIte]
          rw [wp_let, op1_wp_eq, OpCode.wp_neg]; dsimp only
          have hbf : (Ty.bits (target.widenWidth n)).hasFloat = false := rfl
          simp only [hbf, Bool.false_eq_true, ↓reduceIte]
          refine emitMaskToN_wp hs.2.1 rfl fun r hr => ?_
          simp only [Arg.val_var, lift1] at hr
          apply hpre r
          rw [hr, hx', opWp_setWidth_neg hs.2.1 x]
      · intro u _ _ _ x p htr
        have hu := opWp_lift1_noFloat_of_treeRel1 (fun {n} x => -x) id u x p htr
        rw [OpCode.wp_neg]; simp [hu.1, hu.2]
    · simp [hf] at hw
  | and t =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩; rcases hargs with _ | @⟨_, _, b₁, b₂, _, _, hb, hargs⟩; cases hargs
    rw [legalOp.eq_6]
    exact legalOp_bitwiseBin_wp target hG OpCode.and (fun {n} x1 x2 => x1 &&& x2) (fun x1 x2 => x1 && x2)
      (fun u x y p => OpCode.wp_and u (x, y, ()) p) (fun _ => rfl) (fun _ => trivial) hsupp ha hb hw hk
  | or t =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩; rcases hargs with _ | @⟨_, _, b₁, b₂, _, _, hb, hargs⟩; cases hargs
    rw [legalOp.eq_7]
    exact legalOp_bitwiseBin_wp target hG OpCode.or (fun {n} x1 x2 => x1 ||| x2) (fun x1 x2 => x1 || x2)
      (fun u x y p => OpCode.wp_or u (x, y, ()) p) (fun _ => rfl) (fun _ => trivial) hsupp ha hb hw hk
  | xor t =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩; rcases hargs with _ | @⟨_, _, b₁, b₂, _, _, hb, hargs⟩; cases hargs
    rw [legalOp.eq_8]
    exact legalOp_bitwiseBin_wp target hG OpCode.xor (fun {n} x1 x2 => x1 ^^^ x2) (fun x1 x2 => x1 ^^ x2)
      (fun u x y p => OpCode.wp_xor u (x, y, ()) p) (fun _ => rfl) (fun _ => trivial) hsupp ha hb hw hk
  | not t =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩; cases hargs
    dsimp only [Op.wp, vals] at hw
    rw [OpCode.wp_not] at hw
    rw [legalOp.eq_9]
    refine legalUnaryTree_wp target OpCode.not (fun u => target.vecIntOpSupported (OpCode.not u) u false)
      (fun x cont => Expr.let_ (op1 (OpCode.not Ty.bool) x) fun (r, _) => cont (Arg.var r))
      (fun n x cont =>
        let w := target.widenWidth n
        if (n == 0) = true then cont (Arg.imm 0#w)
        else if (n == w) = true then Expr.let_ (op1 (OpCode.not (Ty.bits w)) x) fun (r, _) => cont (Arg.var r)
        else Expr.let_ (op1 (OpCode.not (Ty.bits w)) x) fun (r, _) => emitMaskToN n w (Arg.var r) cont)
      (fun fmt x cont =>
        if target.scalarFloatBitwise = true then Expr.let_ (op1 (OpCode.not (Ty.float fmt)) x) fun (r, _) => cont (Arg.var r)
        else
          let fw := fmt.width
          Expr.let_ (op1 (OpCode.bitcast (Ty.float fmt) (Ty.bits fw) rfl) x) fun (bx, _) =>
            Expr.let_ (op1 (OpCode.not (Ty.bits fw)) (Arg.var bx)) fun (br, _) =>
              Expr.let_ (op1 (OpCode.bitcast (Ty.bits fw) (Ty.float fmt) rfl) (Arg.var br)) fun (r, _) =>
                cont (Arg.var r))
      (onB := fun a q => q (!a)) (onBi := fun _ a q => q (~~~a)) (onF := fun _ a q => q (~~~a))
      ?_ ?_ ?_ ?_ (fun _ _ _ hpq h => hpq _ h) (fun _ _ _ _ hpq h => hpq _ h) (fun _ _ _ _ hpq h => hpq _ h)
      t hsupp (legalArg target a₂) a₁.val (valsTup_legalArg target hG ha) (fun res => k (res, ())) m
      (opWp_treeRel1_lift1 (fun {n} x => ~~~x) (fun x => !x) (fun _ a q => q (~~~a))
        (fun _ _ _ h => h) t _ _ fun fres hfres => hk _ _ (TRel.cons hfres TRel.nil) hw)
    · intro x' x cont m' hx' hpre
      rw [wp_let, op1_wp_eq, OpCode.wp_not, hx']; exact hpre _ rfl
    · intro n hsn x' x cont m' hx' hpre
      have hs := opWp_widen_spec hv hsn
      dsimp only at hs ⊢
      by_cases hn0 : n = 0
      · subst hn0; simp only [beq_self_eq_true, ↓reduceIte]
        apply hpre (Arg.imm 0#(target.widenWidth 0))
        have h0 : (~~~x : BitVec 0) = 0#0 := Subsingleton.elim _ _
        rw [Arg.val_imm, h0]; apply BitVec.eq_of_toNat_eq; simp
      · simp only [beq_iff_eq, hn0, ↓reduceIte]
        split
        · next hnw =>
          rw [wp_let, op1_wp_eq, OpCode.wp_not]; dsimp only
          simp only [lift1]
          refine hpre _ ?_
          simp only [Arg.val_var]
          exact op1_setWidth_self (op := fun {k} (x : BitVec k) => ~~~x) hnw hx'
        · next _ =>
          rw [wp_let, op1_wp_eq, OpCode.wp_not]; dsimp only
          refine emitMaskToN_wp hs.2.1 rfl fun r hr => ?_
          simp only [Arg.val_var, lift1] at hr
          apply hpre r; rw [hr, hx', opWp_not_setWidth hs.2.1 x]
    · intro fmt _ x' x cont m' hx' hpre
      dsimp only
      split
      · rw [wp_let, op1_wp_eq, OpCode.wp_not, hx']; exact hpre _ rfl
      · rw [wp_let, op1_wp_eq, OpCode.wp_bitcast, wp_let, op1_wp_eq, OpCode.wp_not,
          wp_let, op1_wp_eq, OpCode.wp_bitcast]
        apply hpre (Arg.var _)
        simp only [Arg.val_var, toBits, ofBits, lift1, BitVec.cast_eq]
        rw [hx']
    · intro u _ _ _ x p htr
      rw [OpCode.wp_not]
      exact opWp_lift1_of_treeRel1 (fun {n} x => ~~~x) (fun x => !x) (fun _ a q => q (~~~a))
        (fun _ _ _ h => h) (fun _ _ _ _ hpq h => hpq _ h) u x p htr
  | ternlog t imm =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩; rcases hargs with _ | @⟨_, _, b₁, b₂, _, _, hb, hargs⟩
    rcases hargs with _ | @⟨_, _, c₁, c₂, _, _, hc', hargs⟩; cases hargs
    dsimp only [Op.wp, vals] at hw
    rw [OpCode.wp_ternlog] at hw
    rw [legalOp.eq_10]
    refine legalTernaryTree_wp target (fun u => OpCode.ternlog u imm)
      (fun u => target.vecIntOpSupported (OpCode.ternlog u imm) u false)
      (fun x y z cont => emitTernlogBool x y z imm cont)
      (fun n x y z cont =>
        let w := target.widenWidth n
        if (n == 0) = true then cont (Arg.imm 0#w)
        else if target.scalarTernlog = true then
          Expr.let_ (op3 (OpCode.ternlog (Ty.bits w) imm) x y z) fun (r, _) => emitMaskToN n w (Arg.var r) cont
        else emitTernlogBits w x y z imm fun r => emitMaskToN n w r cont)
      (fun fmt x y z cont =>
        if (target.scalarFloatBitwise && target.scalarTernlog) = true then
          Expr.let_ (op3 (OpCode.ternlog (Ty.float fmt) imm) x y z) fun (r, _) => cont (Arg.var r)
        else
          let fw := fmt.width
          Expr.let_ (op1 (OpCode.bitcast (Ty.float fmt) (Ty.bits fw) rfl) x) fun (bx, _) =>
            Expr.let_ (op1 (OpCode.bitcast (Ty.float fmt) (Ty.bits fw) rfl) y) fun (by_, _) =>
              Expr.let_ (op1 (OpCode.bitcast (Ty.float fmt) (Ty.bits fw) rfl) z) fun (bz, _) =>
                (if target.scalarTernlog = true then fun cc =>
                  Expr.let_ (op3 (OpCode.ternlog (Ty.bits fw) imm) (Arg.var bx) (Arg.var by_) (Arg.var bz))
                    fun (br, _) => cc (Arg.var br)
                else emitTernlogBits fw (Arg.var bx) (Arg.var by_) (Arg.var bz) imm) fun br =>
                  Expr.let_ (op1 (OpCode.bitcast (Ty.bits fw) (Ty.float fmt) rfl) br) fun (r, _) =>
                    cont (Arg.var r))
      (onB := fun a b c q => q (ternaryLogicBool a b c imm))
      (onBi := fun _ a b c q => q (ternaryLogic a b c imm))
      (onF := fun _ a b c q => q (ternaryLogic a b c imm))
      ?_ ?_ ?_ ?_ (fun _ _ _ _ _ hpq h => hpq _ h) (fun _ _ _ _ _ _ hpq h => hpq _ h) (fun _ _ _ _ _ _ hpq h => hpq _ h)
      t hsupp (legalArg target a₂) (legalArg target b₂) (legalArg target c₂) a₁.val b₁.val c₁.val
      (valsTup_legalArg target hG ha) (valsTup_legalArg target hG hb) (valsTup_legalArg target hG hc')
      (fun res => k (res, ())) m
      (opWp_treeRel3_lift3 (fun {n} x y z => ternaryLogic x y z imm)
        (fun x y z => ternaryLogicBool x y z imm) t _ _ _ _
        fun fres hfres => hk _ _ (TRel.cons hfres TRel.nil) hw)
    · intro a' b' c' a b c cont m' ha' hb' hc'' hpre
      exact emitTernlogBool_wp a' b' c' imm fun r hr => hpre r (by simpa [ha', hb', hc''] using hr)
    · intro n hsn a' b' c' a b c cont m' ha' hb' hc'' hpre
      have hs := opWp_widen_spec hv hsn
      dsimp only at hs ⊢
      by_cases hn0 : n = 0
      · subst hn0; simp only [beq_self_eq_true, ↓reduceIte]
        apply hpre (Arg.imm 0#(target.widenWidth 0))
        have h0 : ternaryLogic a b c imm = 0#0 := Subsingleton.elim _ _
        rw [Arg.val_imm, h0]; apply BitVec.eq_of_toNat_eq; simp
      · simp only [beq_iff_eq, hn0, ↓reduceIte]
        split
        · rw [wp_let, op3_wp_eq, OpCode.wp_ternlog]; dsimp only
          refine emitMaskToN_wp hs.2.1 rfl fun r hr => ?_
          simp only [Arg.val_var, lift3] at hr
          apply hpre r; rw [hr, ha', hb', hc'']
          exact congrArg (BitVec.setWidth _) (opWp_ternaryLogic_setWidth hs.2.1 a b c imm)
        · refine emitTernlogBits_wp a' b' c' imm fun r1 hr1 =>
            emitMaskToN_wp hs.2.1 rfl fun r hr => ?_
          apply hpre r; rw [hr, hr1, ha', hb', hc'']
          exact congrArg (BitVec.setWidth _) (opWp_ternaryLogic_setWidth hs.2.1 a b c imm)
    · intro fmt _ a' b' c' a b c cont m' ha' hb' hc'' hpre
      dsimp only
      split
      · rw [wp_let, op3_wp_eq, OpCode.wp_ternlog, ha', hb', hc'']
        exact hpre _ rfl
      · rw [wp_let, op1_wp_eq, OpCode.wp_bitcast, wp_let, op1_wp_eq, OpCode.wp_bitcast,
          wp_let, op1_wp_eq, OpCode.wp_bitcast]
        split
        · rw [wp_let, op3_wp_eq, OpCode.wp_ternlog, wp_let, op1_wp_eq, OpCode.wp_bitcast]
          apply hpre (Arg.var _)
          simp only [Arg.val_var, toBits, ofBits, lift3, BitVec.cast_eq]
          rw [ha', hb', hc'']
        · refine emitTernlogBits_wp _ _ _ imm fun br hbr => ?_
          rw [wp_let, op1_wp_eq, OpCode.wp_bitcast]
          apply hpre (Arg.var _)
          simp only [Arg.val_var, toBits, ofBits, BitVec.cast_eq] at hbr ⊢
          rw [hbr, ha', hb', hc'']
    · intro u _ _ _ x y z p htr
      rw [OpCode.wp_ternlog]
      exact opWp_lift3_of_treeRel3 (fun {n} x y z => ternaryLogic x y z imm)
        (fun x y z => ternaryLogicBool x y z imm) u x y z p htr
  | shl t =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩; rcases hargs with _ | @⟨_, _, b₁, b₂, _, _, hb, hargs⟩; cases hargs
    rw [legalOp.eq_11]
    exact legalOp_shiftBin_wp target hG OpCode.shl (fun {n} x y => x <<< (y.toNat % n))
      (fun u x y p => OpCode.wp_shl u (x, y, ()) p)
      (fun n hsn a' b' a b cont m' ha' hb' hpre =>
        legalBitsArith_wp target hsn (OpCode.shl (Ty.bits n)) trivial a' b' a b ha' hb'
          (by dsimp only [Op.wp, vals]; rw [OpCode.wp_shl]; simpa [lift2] using hpre))
      (fun _ _ _ _ hsk => by cases hsk)
      (fun u c w s _ hunif x => opWp_shl_uniformShift u c w s hunif x)
      hsupp ha hb hw hk
  | lshr t =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩; rcases hargs with _ | @⟨_, _, b₁, b₂, _, _, hb, hargs⟩; cases hargs
    rw [legalOp.eq_12]
    exact legalOp_shiftBin_wp target hG OpCode.lshr (fun {n} x y => x >>> (y.toNat % n))
      (fun u x y p => OpCode.wp_lshr u (x, y, ()) p)
      (fun n hsn a' b' a b cont m' ha' hb' hpre =>
        legalBitsArith_wp target hsn (OpCode.lshr (Ty.bits n)) trivial a' b' a b ha' hb'
          (by dsimp only [Op.wp, vals]; rw [OpCode.wp_lshr]; simpa [lift2] using hpre))
      (fun _ _ _ _ hsk => by cases hsk) (fun _ _ _ _ hsk => by cases hsk)
      hsupp ha hb hw hk
  | ashr t =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩; rcases hargs with _ | @⟨_, _, b₁, b₂, _, _, hb, hargs⟩; cases hargs
    rw [legalOp.eq_13]
    exact legalOp_shiftBin_wp target hG OpCode.ashr (fun {n} x y => x.sshiftRight (y.toNat % n))
      (fun u x y p => OpCode.wp_ashr u (x, y, ()) p)
      (fun n hsn a' b' a b cont m' ha' hb' hpre =>
        legalBitsArith_wp target hsn (OpCode.ashr (Ty.bits n)) trivial a' b' a b ha' hb'
          (by dsimp only [Op.wp, vals]; rw [OpCode.wp_ashr]; simpa [lift2] using hpre))
      (fun _ _ _ _ hsk => by cases hsk) (fun _ _ _ _ hsk => by cases hsk)
      hsupp ha hb hw hk
  | rotl t =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩; rcases hargs with _ | @⟨_, _, b₁, b₂, _, _, hb, hargs⟩; cases hargs
    rw [legalOp.eq_14]
    exact legalOp_shiftBin_wp target hG OpCode.rotl (fun {n} x y => x.rotateLeft (y.toNat % n))
      (fun u x y p => OpCode.wp_rotl u (x, y, ()) p)
      (fun n hsn a' b' a b cont m' ha' hb' hpre =>
        legalBitsArith_wp target hsn (OpCode.rotl (Ty.bits n)) trivial a' b' a b ha' hb'
          (by dsimp only [Op.wp, vals]; rw [OpCode.wp_rotl]; simpa [lift2] using hpre))
      (fun u c w s _ hunif x => opWp_rotl_uniformShift u c w s hunif x)
      (fun _ _ _ _ hsk => by cases hsk)
      hsupp ha hb hw hk
  | rotr t =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩; rcases hargs with _ | @⟨_, _, b₁, b₂, _, _, hb, hargs⟩; cases hargs
    rw [legalOp.eq_15]
    exact legalOp_shiftBin_wp target hG OpCode.rotr (fun {n} x y => x.rotateRight (y.toNat % n))
      (fun u x y p => OpCode.wp_rotr u (x, y, ()) p)
      (fun n hsn a' b' a b cont m' ha' hb' hpre =>
        legalBitsArith_wp target hsn (OpCode.rotr (Ty.bits n)) trivial a' b' a b ha' hb'
          (by dsimp only [Op.wp, vals]; rw [OpCode.wp_rotr]; simpa [lift2] using hpre))
      (fun _ _ _ _ hsk => by cases hsk) (fun _ _ _ _ hsk => by cases hsk)
      hsupp ha hb hw hk
  | fshl n =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩
    rcases hargs with _ | @⟨_, _, b₁, b₂, _, _, hb, hargs⟩
    rcases hargs with _ | @⟨_, _, c₁, c₂, _, _, hc', hargs⟩; cases hargs
    dsimp only [Op.wp, vals] at hw
    rw [OpCode.wp_fshl] at hw
    rw [legalOp.eq_16]
    dsimp only [Tup, LVar, LegalTarget.legalTys] at k ⊢
    have ha_val := valsTup_legalArg target hG ha
    have hb_val := valsTup_legalArg target hG hb
    have hc_val := valsTup_legalArg target hG hc'
    rcases hpa : legalArg target a₂ with ⟨a', ⟨⟩⟩
    rcases hpb : legalArg target b₂ with ⟨b', ⟨⟩⟩
    rcases hpc : legalArg target c₂ with ⟨c', ⟨⟩⟩
    rw [hpa] at ha_val; rw [hpb] at hb_val; rw [hpc] at hc_val
    have haeq : a'.val = BitVec.setWidth (target.widenWidth n) a₁.val := (Prod.mk.inj ha_val).1
    have hbeq : b'.val = BitVec.setWidth (target.widenWidth n) b₁.val := (Prod.mk.inj hb_val).1
    have hceq : c'.val = BitVec.setWidth (target.widenWidth n) c₁.val := (Prod.mk.inj hc_val).1
    have hs := opWp_widen_spec hv hsupp
    dsimp only [Tup, LVar, LegalTarget.legalTys] at k hs ⊢
    by_cases hn0 : n = 0
    · subst hn0; simp only [beq_self_eq_true, ↓reduceIte]
      refine hk _ _ (TRel.cons ?_ TRel.nil) hw
      change (0#(target.widenWidth 0), ()) = (BitVec.setWidth (target.widenWidth 0) _, ())
      have h0 : BitVec.extractLsb' 0 0 ((a₁.val ++ b₁.val) <<< (c₁.val.toNat % 0)) = 0#0 := Subsingleton.elim _ _
      rw [h0]; congr 1
    · simp only [beq_iff_eq, hn0, ↓reduceIte]
      split
      · next hnw =>
        rw [wp_let, op3_wp_eq, OpCode.wp_fshl]; dsimp only
        refine hk _ _ (TRel.cons ?_ TRel.nil) hw
        change (_, ()) = (BitVec.setWidth (target.widenWidth n) _, ())
        congr 1
        exact op3_setWidth_self (op := fun {k} (x y z : BitVec k) => BitVec.extractLsb' k k ((x ++ y) <<< (z.toNat % k)))
          hnw haeq hbeq hceq
      · next hnw =>
        have hn_pos : 0 < n := Nat.pos_of_ne_zero hn0
        have hn_lt : n < target.widenWidth n := Nat.lt_of_le_of_ne hs.2.1 hnw
        refine emitCountMod_wp hn_pos hn_lt hceq fun cm hcm => ?_
        rw [wp_let, op2_wp_eq, OpCode.wp_sub, wp_let, op2_wp_eq, OpCode.wp_shl,
          wp_let, op2_wp_eq, OpCode.wp_lshr, wp_let, op2_wp_eq, OpCode.wp_or]
        simp only [Bool.false_eq_true, ↓reduceIte]
        refine emitMaskToN_wp hs.2.1 rfl fun r hr => ?_
        refine hk _ _ (TRel.cons ?_ TRel.nil) hw
        change (r.val, ()) = (BitVec.setWidth (target.widenWidth n) _, ())
        congr 1
        rw [hr]
        congr 1
        simp only [Arg.val_var, Arg.val_imm, lift2, haeq, hbeq, hcm]
        have hnw2 : target.widenWidth n < 2 ^ target.widenWidth n := Nat.lt_two_pow_self
        have hn2w : n < 2 ^ target.widenWidth n := Nat.lt_trans hn_lt hnw2
        have hcn2w : c₁.val.toNat % n < 2 ^ target.widenWidth n := Nat.lt_trans (Nat.mod_lt _ hn_pos) hn2w
        have hm1 : (BitVec.ofNat (target.widenWidth n) (c₁.val.toNat % n)).toNat % target.widenWidth n =
            c₁.val.toNat % n := by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcn2w, Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ hn_pos) hn_lt)]
        have hm2 : (BitVec.ofNat (target.widenWidth n) n -
            BitVec.ofNat (target.widenWidth n) (c₁.val.toNat % n)).toNat % target.widenWidth n =
            (BitVec.ofNat (target.widenWidth n) n -
              BitVec.ofNat (target.widenWidth n) (c₁.val.toNat % n)).toNat := by
          apply Nat.mod_eq_of_lt
          rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt hn2w, Nat.mod_eq_of_lt hcn2w]
          have : c₁.val.toNat % n < n := Nat.mod_lt _ hn_pos
          rw [← Nat.sub_add_comm (Nat.le_of_lt hcn2w), Nat.add_sub_assoc (Nat.le_of_lt this),
            Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
          omega
        change BitVec.setWidth n
          ((BitVec.setWidth (target.widenWidth n) a₁.val <<<
              ((BitVec.ofNat (target.widenWidth n) (c₁.val.toNat % n)).toNat % target.widenWidth n)) |||
           (BitVec.setWidth (target.widenWidth n) b₁.val >>>
              ((BitVec.ofNat (target.widenWidth n) n - BitVec.ofNat (target.widenWidth n) (c₁.val.toNat % n)).toNat %
                target.widenWidth n))) = _
        rw [hm1, hm2]
        have hres := opWp_fshl_widened hn_pos hn_lt a₁.val b₁.val c₁.val
        have hs_bv : (BitVec.ofNat (target.widenWidth n) (c₁.val.toNat % n)).toNat = c₁.val.toNat % n := by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcn2w]
        have hsl_eq : ∀ (x y : BitVec (target.widenWidth n)), x <<< y = x <<< y.toNat := fun _ _ => rfl
        have hsr_eq : ∀ (x y : BitVec (target.widenWidth n)), x >>> y = x >>> y.toNat := fun _ _ => rfl
        rw [hsl_eq, hsr_eq, hs_bv] at hres
        exact hres
  | fshr n =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩
    rcases hargs with _ | @⟨_, _, b₁, b₂, _, _, hb, hargs⟩
    rcases hargs with _ | @⟨_, _, c₁, c₂, _, _, hc', hargs⟩; cases hargs
    dsimp only [Op.wp, vals] at hw
    rw [OpCode.wp_fshr] at hw
    rw [legalOp.eq_17]
    dsimp only [Tup, LVar, LegalTarget.legalTys] at k ⊢
    have ha_val := valsTup_legalArg target hG ha
    have hb_val := valsTup_legalArg target hG hb
    have hc_val := valsTup_legalArg target hG hc'
    rcases hpa : legalArg target a₂ with ⟨a', ⟨⟩⟩
    rcases hpb : legalArg target b₂ with ⟨b', ⟨⟩⟩
    rcases hpc : legalArg target c₂ with ⟨c', ⟨⟩⟩
    rw [hpa] at ha_val; rw [hpb] at hb_val; rw [hpc] at hc_val
    have haeq : a'.val = BitVec.setWidth (target.widenWidth n) a₁.val := (Prod.mk.inj ha_val).1
    have hbeq : b'.val = BitVec.setWidth (target.widenWidth n) b₁.val := (Prod.mk.inj hb_val).1
    have hceq : c'.val = BitVec.setWidth (target.widenWidth n) c₁.val := (Prod.mk.inj hc_val).1
    have hs := opWp_widen_spec hv hsupp
    dsimp only [Tup, LVar, LegalTarget.legalTys] at k hs ⊢
    by_cases hn0 : n = 0
    · subst hn0; simp only [beq_self_eq_true, ↓reduceIte]
      refine hk _ _ (TRel.cons ?_ TRel.nil) hw
      change (0#(target.widenWidth 0), ()) = (BitVec.setWidth (target.widenWidth 0) _, ())
      have h0 : BitVec.extractLsb' 0 0 ((a₁.val ++ b₁.val) >>> (c₁.val.toNat % 0)) = 0#0 := Subsingleton.elim _ _
      rw [h0]; congr 1
    · simp only [beq_iff_eq, hn0, ↓reduceIte]
      split
      · next hnw =>
        rw [wp_let, op3_wp_eq, OpCode.wp_fshr]; dsimp only
        refine hk _ _ (TRel.cons ?_ TRel.nil) hw
        change (_, ()) = (BitVec.setWidth (target.widenWidth n) _, ())
        congr 1
        exact op3_setWidth_self (op := fun {k} (x y z : BitVec k) => BitVec.extractLsb' 0 k ((x ++ y) >>> (z.toNat % k)))
          hnw haeq hbeq hceq
      · next hnw =>
        have hn_pos : 0 < n := Nat.pos_of_ne_zero hn0
        have hn_lt : n < target.widenWidth n := Nat.lt_of_le_of_ne hs.2.1 hnw
        refine emitCountMod_wp hn_pos hn_lt hceq fun cm hcm => ?_
        rw [wp_let, op2_wp_eq, OpCode.wp_sub, wp_let, op2_wp_eq, OpCode.wp_lshr,
          wp_let, op2_wp_eq, OpCode.wp_shl, wp_let, op2_wp_eq, OpCode.wp_or]
        simp only [Bool.false_eq_true, ↓reduceIte]
        refine emitMaskToN_wp hs.2.1 rfl fun r hr => ?_
        refine hk _ _ (TRel.cons ?_ TRel.nil) hw
        change (r.val, ()) = (BitVec.setWidth (target.widenWidth n) _, ())
        congr 1; rw [hr]; congr 1
        simp only [Arg.val_var, Arg.val_imm, lift2, haeq, hbeq, hcm]
        have hnw2 : target.widenWidth n < 2 ^ target.widenWidth n := Nat.lt_two_pow_self
        have hn2w : n < 2 ^ target.widenWidth n := Nat.lt_trans hn_lt hnw2
        have hcn2w : c₁.val.toNat % n < 2 ^ target.widenWidth n := Nat.lt_trans (Nat.mod_lt _ hn_pos) hn2w
        have hm1 : (BitVec.ofNat (target.widenWidth n) (c₁.val.toNat % n)).toNat % target.widenWidth n =
            c₁.val.toNat % n := by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcn2w, Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ hn_pos) hn_lt)]
        have hm2 : (BitVec.ofNat (target.widenWidth n) n -
            BitVec.ofNat (target.widenWidth n) (c₁.val.toNat % n)).toNat % target.widenWidth n =
            (BitVec.ofNat (target.widenWidth n) n -
              BitVec.ofNat (target.widenWidth n) (c₁.val.toNat % n)).toNat := by
          apply Nat.mod_eq_of_lt
          rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt hn2w, Nat.mod_eq_of_lt hcn2w]
          have : c₁.val.toNat % n < n := Nat.mod_lt _ hn_pos
          rw [← Nat.sub_add_comm (Nat.le_of_lt hcn2w), Nat.add_sub_assoc (Nat.le_of_lt this),
            Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
          omega
        change BitVec.setWidth n
          ((BitVec.setWidth (target.widenWidth n) b₁.val >>>
              ((BitVec.ofNat (target.widenWidth n) (c₁.val.toNat % n)).toNat % target.widenWidth n)) |||
           (BitVec.setWidth (target.widenWidth n) a₁.val <<<
              ((BitVec.ofNat (target.widenWidth n) n - BitVec.ofNat (target.widenWidth n) (c₁.val.toNat % n)).toNat %
                target.widenWidth n))) = _
        rw [hm1, hm2]
        have hres := opWp_fshr_widened hn_pos hn_lt a₁.val b₁.val c₁.val
        have hs_bv : (BitVec.ofNat (target.widenWidth n) (c₁.val.toNat % n)).toNat = c₁.val.toNat % n := by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcn2w]
        have hsl_eq : ∀ (x y : BitVec (target.widenWidth n)), x <<< y = x <<< y.toNat := fun _ _ => rfl
        have hsr_eq : ∀ (x y : BitVec (target.widenWidth n)), x >>> y = x >>> y.toNat := fun _ _ => rfl
        rw [hsr_eq, hsl_eq, hs_bv] at hres
        exact hres
  | bswap t =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩; cases hargs
    dsimp only [Op.wp, vals] at hw
    rw [OpCode.wp_bswap] at hw
    cases hbs : t.bswapOk
    · simp [hbs] at hw
    · simp only [hbs, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hw
      rw [legalOp.eq_18]
      exact legalBswapTree_wp target hv t hsupp hbs (legalArg target a₂) a₁.val
        (valsTup_legalArg target hG ha) fun res hres => hk _ _ (TRel.cons hres TRel.nil) hw
  | clz n =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩; cases hargs
    dsimp only [Op.wp, vals] at hw
    rw [OpCode.wp_clz] at hw
    rw [legalOp.eq_19]
    dsimp only [Tup, LVar, LegalTarget.legalTys] at k ⊢
    have ha_val := valsTup_legalArg target hG ha
    rcases hpa : legalArg target a₂ with ⟨a', ⟨⟩⟩; rw [hpa] at ha_val
    have haeq : a'.val = BitVec.setWidth (target.widenWidth n) a₁.val := (Prod.mk.inj ha_val).1
    have hs := opWp_widen_spec hv hsupp
    dsimp only [Tup, LVar, LegalTarget.legalTys] at k hs ⊢
    by_cases hn0 : n = 0
    · subst hn0; simp only [beq_self_eq_true, ↓reduceIte]
      refine hk _ _ (TRel.cons ?_ TRel.nil) hw
      have h0 : a₁.val.clz = 0#0 := Subsingleton.elim _ _
      change (0#(target.widenWidth 0), ()) = (BitVec.setWidth (target.widenWidth 0) a₁.val.clz, ())
      rw [h0]; congr 1
    · simp only [beq_iff_eq, hn0, ↓reduceIte]
      split
      · next hnw =>
        rw [wp_let, op1_wp_eq, OpCode.wp_clz]; dsimp only
        refine hk _ _ (TRel.cons ?_ TRel.nil) hw
        change (a'.val.clz, ()) = (BitVec.setWidth (target.widenWidth n) a₁.val.clz, ())
        congr 1; exact op1_setWidth_self hnw haeq
      · next hnw =>
        rw [wp_let, op1_wp_eq, OpCode.wp_clz, wp_let, op2_wp_eq, OpCode.wp_sub]
        dsimp only
        refine hk _ _ (TRel.cons ?_ TRel.nil) hw
        change (_, ()) = (BitVec.setWidth (target.widenWidth n) a₁.val.clz, ())
        congr 1
        simp only [Arg.val_var, Arg.val_imm, lift2, haeq]
        exact opWp_clz_widened (Nat.pos_of_ne_zero hn0) (Nat.lt_of_le_of_ne hs.2.1 hnw) a₁.val
  | cls n =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩; cases hargs
    dsimp only [Op.wp, vals] at hw
    rw [OpCode.wp_cls] at hw
    rw [legalOp.eq_20]
    dsimp only [Tup, LVar, LegalTarget.legalTys] at k ⊢
    have ha_val := valsTup_legalArg target hG ha
    rcases hpa : legalArg target a₂ with ⟨a', ⟨⟩⟩; rw [hpa] at ha_val
    have haeq : a'.val = BitVec.setWidth (target.widenWidth n) a₁.val := (Prod.mk.inj ha_val).1
    have hs := opWp_widen_spec hv hsupp
    dsimp only [Tup, LVar, LegalTarget.legalTys] at k hs ⊢
    by_cases hn0 : n = 0
    · subst hn0; simp only [beq_self_eq_true, ↓reduceIte]
      refine hk _ _ (TRel.cons ?_ TRel.nil) hw
      have h0 : ((if a₁.val.msb = true then (~~~a₁.val).clz else a₁.val.clz) - 1#0) = 0#0 := Subsingleton.elim _ _
      change (0#(target.widenWidth 0), ()) = (BitVec.setWidth _ _, ())
      rw [h0]; congr 1
    · simp only [beq_iff_eq, hn0, ↓reduceIte]
      split
      · next hnw =>
        rw [wp_let, op1_wp_eq, OpCode.wp_cls]; dsimp only
        refine hk _ _ (TRel.cons ?_ TRel.nil) hw
        change (_, ()) = (BitVec.setWidth (target.widenWidth n) _, ())
        congr 1
        exact op1_setWidth_self (op := fun {k} (x : BitVec k) => (if x.msb = true then (~~~x).clz else x.clz) - 1#k)
          hnw haeq
      · next hnw =>
        have hn_pos : 0 < n := Nat.pos_of_ne_zero hn0
        have hn_lt : n < target.widenWidth n := Nat.lt_of_le_of_ne hs.2.1 hnw
        refine emitSextToW_wp hn_pos hs.2.1 haeq fun sa hsa => ?_
        rw [wp_let, op1_wp_eq, OpCode.wp_cls, wp_let, op2_wp_eq, OpCode.wp_sub]
        dsimp only
        refine hk _ _ (TRel.cons ?_ TRel.nil) hw
        change (_, ()) = (BitVec.setWidth (target.widenWidth n) _, ())
        congr 1
        simp only [Arg.val_var, Arg.val_imm, lift2, hsa]
        exact opWp_cls_widened hn_pos hn_lt a₁.val
  | rbit n =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩; cases hargs
    dsimp only [Op.wp, vals] at hw
    rw [OpCode.wp_rbit] at hw
    rw [legalOp.eq_21]
    dsimp only [Tup, LVar, LegalTarget.legalTys] at k ⊢
    have ha_val := valsTup_legalArg target hG ha
    rcases hpa : legalArg target a₂ with ⟨a', ⟨⟩⟩; rw [hpa] at ha_val
    have haeq : a'.val = BitVec.setWidth (target.widenWidth n) a₁.val := (Prod.mk.inj ha_val).1
    have hs := opWp_widen_spec hv hsupp
    dsimp only [Tup, LVar, LegalTarget.legalTys] at k hs ⊢
    by_cases hn0 : n = 0
    · subst hn0; simp only [beq_self_eq_true, ↓reduceIte]
      refine hk _ _ (TRel.cons ?_ TRel.nil) hw
      have h0 : a₁.val.reverse = 0#0 := Subsingleton.elim _ _
      change (0#(target.widenWidth 0), ()) = (BitVec.setWidth _ _, ())
      rw [h0]; congr 1
    · simp only [beq_iff_eq, hn0, ↓reduceIte]
      split
      · next hnw =>
        rw [wp_let, op1_wp_eq, OpCode.wp_rbit]; dsimp only
        refine hk _ _ (TRel.cons ?_ TRel.nil) hw
        change (_, ()) = (BitVec.setWidth (target.widenWidth n) _, ())
        congr 1; exact op1_setWidth_self hnw haeq
      · next hnw =>
        rw [wp_let, op1_wp_eq, OpCode.wp_rbit, wp_let, op2_wp_eq, OpCode.wp_lshr]
        dsimp only
        simp only [Bool.false_eq_true, ↓reduceIte]
        refine hk _ _ (TRel.cons ?_ TRel.nil) hw
        change (_, ()) = (BitVec.setWidth (target.widenWidth n) _, ())
        congr 1
        simp only [Arg.val_var, Arg.val_imm, lift2, haeq]
        have hnw2 : target.widenWidth n < 2 ^ target.widenWidth n := Nat.lt_two_pow_self
        have hmod : (BitVec.ofNat (target.widenWidth n) (target.widenWidth n - n)).toNat % target.widenWidth n =
            target.widenWidth n - n := by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hnw2),
            Nat.mod_eq_of_lt (by omega)]
        rw [hmod]
        exact opWp_rbit_widened (Nat.pos_of_ne_zero hn0) (Nat.lt_of_le_of_ne hs.2.1 hnw) a₁.val
  | ctz n =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩; cases hargs
    dsimp only [Op.wp, vals] at hw
    rw [OpCode.wp_ctz] at hw
    rw [legalOp.eq_22]
    dsimp only [Tup, LVar, LegalTarget.legalTys] at k ⊢
    have ha_val := valsTup_legalArg target hG ha
    rcases hpa : legalArg target a₂ with ⟨a', ⟨⟩⟩; rw [hpa] at ha_val
    have haeq : a'.val = BitVec.setWidth (target.widenWidth n) a₁.val := (Prod.mk.inj ha_val).1
    have hs := opWp_widen_spec hv hsupp
    dsimp only [Tup, LVar, LegalTarget.legalTys] at k hs ⊢
    by_cases hn0 : n = 0
    · subst hn0; simp only [beq_self_eq_true, ↓reduceIte]
      refine hk _ _ (TRel.cons ?_ TRel.nil) hw
      have h0 : a₁.val.reverse.clz = 0#0 := Subsingleton.elim _ _
      change (0#(target.widenWidth 0), ()) = (BitVec.setWidth _ _, ())
      rw [h0]; congr 1
    · simp only [beq_iff_eq, hn0, ↓reduceIte]
      split
      · next hnw =>
        rw [wp_let, op1_wp_eq, OpCode.wp_ctz]; dsimp only
        refine hk _ _ (TRel.cons ?_ TRel.nil) hw
        change (_, ()) = (BitVec.setWidth (target.widenWidth n) _, ())
        congr 1
        exact op1_setWidth_self (op := fun {k} (x : BitVec k) => x.reverse.clz) hnw haeq
      · next hnw =>
        rw [wp_let, op2_wp_eq, OpCode.wp_or, wp_let, op1_wp_eq, OpCode.wp_ctz]
        dsimp only
        refine hk _ _ (TRel.cons ?_ TRel.nil) hw
        change (_, ()) = (BitVec.setWidth (target.widenWidth n) _, ())
        congr 1
        simp only [Arg.val_var, Arg.val_imm, lift2, haeq]
        exact opWp_ctz_widened (Nat.pos_of_ne_zero hn0) (Nat.lt_of_le_of_ne hs.2.1 hnw) a₁.val
  | popcnt n =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩; cases hargs
    dsimp only [Op.wp, vals] at hw
    rw [OpCode.wp_popcnt] at hw
    rw [legalOp.eq_23]
    dsimp only [Tup, LVar, LegalTarget.legalTys] at k ⊢
    have ha_val := valsTup_legalArg target hG ha
    rcases hpa : legalArg target a₂ with ⟨a', ⟨⟩⟩; rw [hpa] at ha_val
    have haeq : a'.val = BitVec.setWidth (target.widenWidth n) a₁.val := (Prod.mk.inj ha_val).1
    have hs := opWp_widen_spec hv hsupp
    dsimp only [Tup, LVar, LegalTarget.legalTys] at k hs ⊢
    by_cases hn0 : n = 0
    · subst hn0; simp only [beq_self_eq_true, ↓reduceIte]
      refine hk _ _ (TRel.cons ?_ TRel.nil) hw
      have h0 : a₁.val.cpop = 0#0 := Subsingleton.elim _ _
      change (0#(target.widenWidth 0), ()) = (BitVec.setWidth _ _, ())
      rw [h0]; congr 1
    · simp only [beq_iff_eq, hn0, ↓reduceIte]
      rw [wp_let, op1_wp_eq, OpCode.wp_popcnt]; dsimp only
      refine hk _ _ (TRel.cons ?_ TRel.nil) hw
      change (_, ()) = (BitVec.setWidth (target.widenWidth n) a₁.val.cpop, ())
      congr 1; rw [haeq]; exact opWp_popcnt_widened hs.2.1 a₁.val
  | cmp o t m_ty hm =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩; rcases hargs with _ | @⟨_, _, b₁, b₂, _, _, hb, hargs⟩; cases hargs
    cases hm
    dsimp only [Op.wp, vals] at hw
    rw [OpCode.wp_cmp] at hw
    rw [legalOp.eq_24]
    cases hf : t.hasFloat
    · simp only [hf, Bool.false_eq_true, ↓reduceIte] at hw ⊢
      exact legalCmpTree_wp target o t hsupp hf (legalArg target a₂) (legalArg target b₂)
        a₁.val b₁.val (valsTup_legalArg target hG ha) (valsTup_legalArg target hG hb)
        (fun res => k (res, ())) m
        (fun res hres => hk (liftCmp (fun {n} => o.evalBits) o.evalBool t a₁.val b₁.val, ())
          (res, ()) (TRel.cons hres TRel.nil) hw)
    · simp [hf] at hw
  | select t =>
    rcases hargs with _ | @⟨_, _, c₁, c₂, _, _, hc', hargs⟩
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩
    rcases hargs with _ | @⟨_, _, b₁, b₂, _, _, hb, hargs⟩; cases hargs
    dsimp only [Op.wp, vals] at hw
    rw [OpCode.wp_select] at hw
    rw [legalOp.eq_25]
    have hc_val := valsTup_legalArg target hG hc'
    rcases hpc : legalArg target c₂ with ⟨c', ⟨⟩⟩; rw [hpc] at hc_val
    have hceq : c'.val = c₁.val := (Prod.mk.inj hc_val).1
    exact legalSelectTree_wp target c' c₁.val hceq t hsupp (legalArg target a₂) (legalArg target b₂)
      a₁.val b₁.val (valsTup_legalArg target hG ha) (valsTup_legalArg target hG hb)
      (fun res => k (res, ())) m
      (fun res hres => hk _ _ (TRel.cons hres TRel.nil) hw)
  | blend t m_ty hm =>
    rcases hargs with _ | @⟨_, _, c₁, c₂, _, _, hc', hargs⟩
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩
    rcases hargs with _ | @⟨_, _, b₁, b₂, _, _, hb, hargs⟩; cases hargs
    cases hm
    dsimp only [Op.wp, vals] at hw
    rw [OpCode.wp_blend] at hw
    rw [legalOp.eq_26]
    exact legalBlendTree_wp target t hsupp (legalArg target c₂) (legalArg target a₂) (legalArg target b₂)
      c₁.val a₁.val b₁.val (valsTup_legalArg target hG hc') (valsTup_legalArg target hG ha)
      (valsTup_legalArg target hG hb) (fun res => k (res, ())) m
      (fun res hres => hk _ _ (TRel.cons hres TRel.nil) hw)
  | zext m' n =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩; cases hargs
    dsimp only [Op.wp, vals] at hw
    rw [OpCode.wp_zext] at hw
    rcases hw with ⟨hmn, hwP⟩
    rw [legalOp.eq_27]
    simp only [Nat.not_lt.mpr hmn, ↓reduceIte]
    have ha_val := valsTup_legalArg target hG ha
    split
    · next a' hpa =>
      dsimp only [Tup, LVar, LegalTarget.legalTys] at k ha_val ⊢
      rw [hpa] at ha_val
      have haeq : a'.val = BitVec.setWidth (target.widenWidth m') a₁.val := (Prod.mk.inj ha_val).1
      dsimp only [LegalTarget.supportsOpCode] at hsupp
      simp only [Bool.and_eq_true] at hsupp
      have hsm := opWp_widen_spec hv hsupp.1
      have hsn := opWp_widen_spec hv hsupp.2
      have hmono := opWp_widen_mono hv hsupp.1 hsupp.2 hmn
      by_cases hm0 : m' = 0
      · subst hm0; simp only [beq_self_eq_true, ↓reduceIte]
        refine hk _ _ (TRel.cons ?_ TRel.nil) hwP
        have ha0 : a₁.val = 0#0 := Subsingleton.elim _ _
        change (0#(target.widenWidth n), ()) = (BitVec.setWidth (target.widenWidth n) (BitVec.setWidth n a₁.val), ())
        rw [ha0]; congr 1; apply BitVec.eq_of_toNat_eq; simp
      · simp only [beq_iff_eq, hm0, ↓reduceIte]
        by_cases heqw : target.widenWidth m' = target.widenWidth n
        · simp only [heqw, ↓reduceDIte]
          refine hk _ _ (TRel.cons ?_ TRel.nil) hwP
          change ((castArgBits heqw a').val, ()) = (BitVec.setWidth (target.widenWidth n) (BitVec.setWidth n a₁.val), ())
          rw [val_castArgBits]
          congr 1
          apply BitVec.eq_of_toNat_eq
          have hp1 : 2 ^ m' ≤ 2 ^ target.widenWidth m' := Nat.pow_le_pow_right (by omega) hsm.2.1
          have hp2 : 2 ^ m' ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hmn
          have hp3 : 2 ^ n ≤ 2 ^ target.widenWidth n := Nat.pow_le_pow_right (by omega) hsn.2.1
          rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth,
            Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le a₁.val.isLt hp2),
            Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le a₁.val.isLt (Nat.le_trans hp2 hp3))]
          have hcast : ∀ (k : Nat) (hk : target.widenWidth m' = k) (v : BitVec (target.widenWidth m')),
              (hk ▸ v).toNat = v.toNat := by intro k hk v; subst hk; rfl
          rw [hcast _ heqw a'.val, haeq, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le a₁.val.isLt hp1)]
        · have hltw : target.widenWidth m' < target.widenWidth n := Nat.lt_of_le_of_ne hmono heqw
          simp only [heqw, ↓reduceDIte, hltw, ↓reduceIte]
          rw [wp_let, op1_wp_eq, OpCode.wp_zext]; refine ⟨Nat.le_of_lt hltw, ?_⟩
          refine hk _ _ (TRel.cons ?_ TRel.nil) hwP
          dsimp only [Arg.val]
          change (BitVec.setWidth (target.widenWidth n) a'.val, ()) =
            (BitVec.setWidth (target.widenWidth n) (BitVec.setWidth n a₁.val), ())
          congr 1; apply BitVec.eq_of_toNat_eq
          have hp1 : 2 ^ m' ≤ 2 ^ target.widenWidth m' := Nat.pow_le_pow_right (by omega) hsm.2.1
          have hp2 : 2 ^ m' ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hmn
          have hp3 : 2 ^ n ≤ 2 ^ target.widenWidth n := Nat.pow_le_pow_right (by omega) hsn.2.1
          have hp4 : 2 ^ target.widenWidth m' ≤ 2 ^ target.widenWidth n := Nat.pow_le_pow_right (by omega) hmono
          rw [haeq, BitVec.toNat_setWidth, BitVec.toNat_setWidth, BitVec.toNat_setWidth, BitVec.toNat_setWidth,
            Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le a₁.val.isLt hp1),
            Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le a₁.val.isLt (Nat.le_trans hp1 hp4)),
            Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le a₁.val.isLt hp2),
            Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le a₁.val.isLt (Nat.le_trans hp2 hp3))]
  | sext m' n =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩; cases hargs
    dsimp only [Op.wp, vals] at hw
    rw [OpCode.wp_sext] at hw
    rcases hw with ⟨hmn, hwP⟩
    rw [legalOp.eq_28]
    simp only [Nat.not_lt.mpr hmn, ↓reduceIte]
    have ha_val := valsTup_legalArg target hG ha
    split
    · next a' hpa =>
      dsimp only [Tup, LVar, LegalTarget.legalTys] at k ha_val ⊢
      rw [hpa] at ha_val
      have haeq : a'.val = BitVec.setWidth (target.widenWidth m') a₁.val := (Prod.mk.inj ha_val).1
      dsimp only [LegalTarget.supportsOpCode] at hsupp
      simp only [Bool.and_eq_true] at hsupp
      have hsm := opWp_widen_spec hv hsupp.1
      have hsn := opWp_widen_spec hv hsupp.2
      have hmono := opWp_widen_mono hv hsupp.1 hsupp.2 hmn
      by_cases hm0 : m' = 0
      · subst hm0; simp only [beq_self_eq_true, ↓reduceIte]
        refine hk _ _ (TRel.cons ?_ TRel.nil) hwP
        have ha0 : a₁.val = 0#0 := Subsingleton.elim _ _
        change (0#(target.widenWidth n), ()) = (BitVec.setWidth (target.widenWidth n) (BitVec.signExtend n a₁.val), ())
        rw [ha0]
        congr 1; apply BitVec.eq_of_toNat_eq
        rw [BitVec.signExtend_eq_setWidth_of_msb_false (by rfl)]; simp
      · simp only [beq_iff_eq, hm0, ↓reduceIte]
        have hm_pos : 0 < m' := Nat.pos_of_ne_zero hm0
        refine emitSextToW_wp hm_pos hsm.2.1 haeq fun sx hsx => ?_
        have hstep2 : ∀ (cont : Arg Val (Ty.bits (target.widenWidth n)) → _),
            (∀ r : Arg Val (Ty.bits (target.widenWidth n)),
              r.val = BitVec.signExtend (target.widenWidth n) a₁.val → wp Γ Q X (cont r) m) →
            wp Γ Q X (if h : target.widenWidth m' = target.widenWidth n then cont (castArgBits h sx)
              else if target.widenWidth m' < target.widenWidth n then
                Expr.let_ (op1 (OpCode.sext (target.widenWidth m') (target.widenWidth n)) sx) fun (r, _) => cont (Arg.var r)
              else Expr.hlt) m := by
          intro cont hcont
          by_cases heqw : target.widenWidth m' = target.widenWidth n
          · simp only [heqw, ↓reduceDIte]
            apply hcont (castArgBits heqw sx)
            rw [val_castArgBits, hsx]
            apply BitVec.eq_of_getLsbD_eq; intro i hi
            rw [getLsbD_eq_rec heqw, BitVec.getLsbD_signExtend, BitVec.getLsbD_signExtend,
              decide_eq_true hi, decide_eq_true (by rw [heqw]; exact hi)]
          · have hltw : target.widenWidth m' < target.widenWidth n := Nat.lt_of_le_of_ne hmono heqw
            simp only [heqw, ↓reduceDIte, hltw, ↓reduceIte]
            rw [wp_let, op1_wp_eq, OpCode.wp_sext]; refine ⟨Nat.le_of_lt hltw, ?_⟩
            apply hcont (Arg.var _)
            simp only [Arg.val_var]
            rw [hsx]
            apply BitVec.eq_of_getLsbD_eq
            intro i hi
            simp only [BitVec.getLsbD_signExtend, decide_eq_true hi, Bool.true_and]
            by_cases him : i < target.widenWidth m'
            · simp [him]
            · have hlast : target.widenWidth m' - 1 < target.widenWidth m' := by omega
              have hmsb_eq : (BitVec.signExtend (target.widenWidth m') a₁.val).msb = a₁.val.msb := by
                rw [BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_signExtend, decide_eq_true hlast, Bool.true_and]
                by_cases hlastm : target.widenWidth m' - 1 < m'
                · have heqm : target.widenWidth m' - 1 = m' - 1 := by omega
                  simp only [heqm, ← BitVec.msb_eq_getLsbD_last, ite_self]
                · simp only [hlastm, ↓reduceIte]
              have him' : ¬ i < m' := by omega
              simp [him, him', hmsb_eq]
        refine hstep2 (fun r => emitMaskToN n (target.widenWidth n) r fun rm => k ((rm, ()), ())) fun r hr => ?_
        refine emitMaskToN_wp hsn.2.1 rfl fun rm hrm => ?_
        refine hk _ _ (TRel.cons ?_ TRel.nil) hwP
        change (rm.val, ()) = (BitVec.setWidth (target.widenWidth n) (BitVec.signExtend n a₁.val), ())
        congr 1; rw [hrm, hr]; congr 1
        apply BitVec.eq_of_getLsbD_eq; intro i hi
        simp only [BitVec.getLsbD_setWidth, decide_eq_true hi, Bool.true_and,
          BitVec.getLsbD_signExtend, decide_eq_true (Nat.lt_of_lt_of_le hi hsn.2.1)]
  | trunc m' n =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩; cases hargs
    dsimp only [Op.wp, vals] at hw
    rw [OpCode.wp_trunc] at hw
    rcases hw with ⟨hnm, hwP⟩
    rw [legalOp.eq_29]
    simp only [Nat.not_lt.mpr hnm, ↓reduceIte]
    have ha_val := valsTup_legalArg target hG ha
    split
    · next a' hpa =>
      dsimp only [Tup, LVar, LegalTarget.legalTys] at k ha_val ⊢
      rw [hpa] at ha_val
      have haeq : a'.val = BitVec.setWidth (target.widenWidth m') a₁.val := (Prod.mk.inj ha_val).1
      dsimp only [LegalTarget.supportsOpCode] at hsupp
      simp only [Bool.and_eq_true] at hsupp
      have hsm := opWp_widen_spec hv hsupp.1
      have hsn := opWp_widen_spec hv hsupp.2
      have hmono := opWp_widen_mono hv hsupp.2 hsupp.1 hnm
      by_cases hn0 : n = 0
      · subst hn0; simp only [beq_self_eq_true, ↓reduceIte]
        refine hk _ _ (TRel.cons ?_ TRel.nil) hwP
        have h0 : BitVec.setWidth 0 a₁.val = 0#0 := Subsingleton.elim _ _
        change (0#(target.widenWidth 0), ()) = (BitVec.setWidth _ _, ())
        rw [h0]; congr 1
      · simp only [beq_iff_eq, hn0, ↓reduceIte]
        have hstep1 : ∀ (cont : Arg Val (Ty.bits (target.widenWidth n)) → _),
            (∀ r : Arg Val (Ty.bits (target.widenWidth n)),
              BitVec.setWidth n r.val = BitVec.setWidth n a₁.val → wp Γ Q X (cont r) m) →
            wp Γ Q X (if h : target.widenWidth n = target.widenWidth m' then cont (castArgBits h.symm a')
              else if target.widenWidth n < target.widenWidth m' then
                Expr.let_ (op1 (OpCode.trunc (target.widenWidth m') (target.widenWidth n)) a')
                  fun (r, _) => cont (Arg.var r)
              else Expr.hlt) m := by
          intro cont hcont
          by_cases heqw : target.widenWidth n = target.widenWidth m'
          · simp only [heqw, ↓reduceDIte]
            apply hcont (castArgBits heqw.symm a')
            rw [val_castArgBits]
            apply BitVec.eq_of_getLsbD_eq; intro i hi
            have hcast : ∀ (k : Nat) (hk : target.widenWidth m' = k) (v : BitVec (target.widenWidth m')),
                (hk ▸ v).getLsbD i = v.getLsbD i := fun k hk v => getLsbD_eq_rec hk v i
            rw [BitVec.getLsbD_setWidth, BitVec.getLsbD_setWidth, decide_eq_true hi, Bool.true_and,
              hcast _ heqw.symm a'.val, haeq, BitVec.getLsbD_setWidth,
              decide_eq_true (Nat.lt_of_lt_of_le hi (by rw [← heqw]; exact hsn.2.1)), Bool.true_and]
          · have hltw : target.widenWidth n < target.widenWidth m' := Nat.lt_of_le_of_ne hmono heqw
            simp only [heqw, ↓reduceDIte, hltw, ↓reduceIte]
            rw [wp_let, op1_wp_eq, OpCode.wp_trunc]; refine ⟨Nat.le_of_lt hltw, ?_⟩
            apply hcont (Arg.var _)
            simp only [Arg.val_var]
            rw [haeq, BitVec.setWidth_setWidth_of_le _ hsn.2.1,
              BitVec.setWidth_setWidth_of_le _ (Nat.le_trans hnm hsm.2.1)]
        refine hstep1 (fun r => emitMaskToN n (target.widenWidth n) r fun rm => k ((rm, ()), ())) fun r hr => ?_
        refine emitMaskToN_wp hsn.2.1 rfl fun rm hrm => ?_
        refine hk _ _ (TRel.cons ?_ TRel.nil) hwP
        change (rm.val, ()) = (BitVec.setWidth (target.widenWidth n) (BitVec.setWidth n a₁.val), ())
        congr 1; rw [hrm, hr]
  | ofBool n =>
    rcases hargs with _ | @⟨_, _, c₁, c₂, _, _, hc', hargs⟩; cases hargs
    dsimp only [Op.wp, vals] at hw
    rw [OpCode.wp_ofBool] at hw
    rw [legalOp.eq_30]
    dsimp only [Tup, LVar, LegalTarget.legalTys] at k ⊢
    have hc_val := valsTup_legalArg target hG hc'
    rcases hpc : legalArg target c₂ with ⟨c', ⟨⟩⟩; rw [hpc] at hc_val
    have hceq : c'.val = c₁.val := (Prod.mk.inj hc_val).1
    have hs := opWp_widen_spec hv hsupp
    dsimp only [Tup, LVar, LegalTarget.legalTys] at k hs ⊢
    by_cases hn0 : n = 0
    · subst hn0; simp only [beq_self_eq_true, ↓reduceIte]
      refine hk _ _ (TRel.cons ?_ TRel.nil) hw
      have h0 : BitVec.ofNat 0 c₁.val.toNat = 0#0 := Subsingleton.elim _ _
      change (0#(target.widenWidth 0), ()) = (BitVec.setWidth _ _, ())
      rw [h0]; congr 1
    · simp only [beq_iff_eq, hn0, ↓reduceIte]
      rw [wp_let, op1_wp_eq, OpCode.wp_ofBool]; dsimp only
      refine hk _ _ (TRel.cons ?_ TRel.nil) hw
      change (_, ()) = (BitVec.setWidth (target.widenWidth n) _, ())
      congr 1; simp only [Arg.val_var, hceq]; apply BitVec.eq_of_toNat_eq
      have hcc : c₁.val.toNat ≤ 1 := by cases c₁.val <;> simp
      have hpn : 1 < 2 ^ n := Nat.one_lt_pow hn0 (by omega)
      have hpw : 2 ^ n ≤ 2 ^ target.widenWidth n := Nat.pow_le_pow_right (by omega) hs.2.1
      rw [BitVec.toNat_ofNat, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  | addc n =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩
    rcases hargs with _ | @⟨_, _, b₁, b₂, _, _, hb, hargs⟩
    rcases hargs with _ | @⟨_, _, c₁, c₂, _, _, hc', hargs⟩; cases hargs
    dsimp only [Op.wp, vals] at hw
    rw [OpCode.wp_addc] at hw
    rw [legalOp.eq_31]
    dsimp only [Tup, LVar, LegalTarget.legalTys] at k ⊢
    have ha_val := valsTup_legalArg target hG ha
    have hb_val := valsTup_legalArg target hG hb
    have hc_val := valsTup_legalArg target hG hc'
    rcases hpa : legalArg target a₂ with ⟨a', ⟨⟩⟩; rw [hpa] at ha_val
    rcases hpb : legalArg target b₂ with ⟨b', ⟨⟩⟩; rw [hpb] at hb_val
    rcases hpc : legalArg target c₂ with ⟨c', ⟨⟩⟩; rw [hpc] at hc_val
    have haeq : a'.val = BitVec.setWidth (target.widenWidth n) a₁.val := (Prod.mk.inj ha_val).1
    have hbeq : b'.val = BitVec.setWidth (target.widenWidth n) b₁.val := (Prod.mk.inj hb_val).1
    have hceq : c'.val = c₁.val := (Prod.mk.inj hc_val).1
    have hs := opWp_widen_spec hv hsupp
    dsimp only [Tup, LVar, LegalTarget.legalTys] at k hs ⊢
    by_cases hn0 : n = 0
    · subst hn0; simp only [beq_self_eq_true, ↓reduceIte]
      refine hk _ _ (TRel.cons ?_ (TRel.cons ?_ TRel.nil)) hw
      · change (0#(target.widenWidth 0), ()) = (BitVec.setWidth _ _, ())
        have h0 : a₁.val + b₁.val + BitVec.ofNat 0 c₁.val.toNat = 0#0 := Subsingleton.elim _ _
        rw [h0]; congr 1
      · change (c'.val, ()) = (decide (2 ^ 0 ≤ a₁.val.toNat + b₁.val.toNat + c₁.val.toNat), ())
        have ha0 : a₁.val.toNat = 0 := by have := a₁.val.isLt; omega
        have hb0 : b₁.val.toNat = 0 := by have := b₁.val.isLt; omega
        rw [hceq, ha0, hb0]; cases c₁.val <;> rfl
    · simp only [beq_iff_eq, hn0, ↓reduceIte]
      split
      · next hnw =>
        rw [wp_let, op3_wp_eq, OpCode.wp_addc]; dsimp only
        have hp : 2 ^ n = 2 ^ target.widenWidth n := by rw [← hnw]
        have ha_nat : a'.val.toNat = a₁.val.toNat := by
          rw [haeq, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by simpa [← hp] using a₁.val.isLt)]
        have hb_nat : b'.val.toNat = b₁.val.toNat := by
          rw [hbeq, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by simpa [← hp] using b₁.val.isLt)]
        refine hk _ _ (TRel.cons ?_ (TRel.cons ?_ TRel.nil)) hw
        · change (_, ()) = (BitVec.setWidth (target.widenWidth n) _, ())
          congr 1; simp only [Arg.val_var]; apply BitVec.eq_of_toNat_eq
          rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, ha_nat, hb_nat, hceq,
            BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, ← hp, Nat.mod_mod]
        · change (decide _, ()) = (decide _, ())
          congr 1; simp only [hp, ha_nat, hb_nat, hceq]
      · next hnw =>
        rw [wp_let, op1_wp_eq, OpCode.wp_ofBool, wp_let, op2_wp_eq, OpCode.wp_add, wp_let, op2_wp_eq, OpCode.wp_add]
        simp only [Bool.false_eq_true, ↓reduceIte]
        refine emitMaskToN_wp hs.2.1 rfl fun s hs_eq => ?_
        rw [wp_let, op2_wp_eq, OpCode.wp_cmp]; simp only [Bool.false_eq_true, ↓reduceIte]
        simp only [Arg.val_var, Arg.val_imm, lift2, liftCmp, CmpOp.evalBits] at hs_eq ⊢
        have hwid := opWp_addc_widened (Nat.pos_of_ne_zero hn0) (Nat.lt_of_le_of_ne hs.2.1 hnw)
          a₁.val b₁.val c₁.val
        refine hk _ _ (TRel.cons ?_ (TRel.cons ?_ TRel.nil)) hw
        · change (s.val, ()) = (BitVec.setWidth (target.widenWidth n) _, ())
          congr 1; rw [hs_eq, haeq, hbeq, hceq, hwid.1]
        · change (BitVec.ule (1#(target.widenWidth n) <<< n) _, ()) = (_, ())
          congr 1; rw [haeq, hbeq, hceq]; exact hwid.2
  | subb n =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩
    rcases hargs with _ | @⟨_, _, b₁, b₂, _, _, hb, hargs⟩
    rcases hargs with _ | @⟨_, _, c₁, c₂, _, _, hc', hargs⟩; cases hargs
    dsimp only [Op.wp, vals] at hw
    rw [OpCode.wp_subb] at hw
    rw [legalOp.eq_32]
    dsimp only [Tup, LVar, LegalTarget.legalTys] at k ⊢
    have ha_val := valsTup_legalArg target hG ha
    have hb_val := valsTup_legalArg target hG hb
    have hc_val := valsTup_legalArg target hG hc'
    rcases hpa : legalArg target a₂ with ⟨a', ⟨⟩⟩; rw [hpa] at ha_val
    rcases hpb : legalArg target b₂ with ⟨b', ⟨⟩⟩; rw [hpb] at hb_val
    rcases hpc : legalArg target c₂ with ⟨c', ⟨⟩⟩; rw [hpc] at hc_val
    have haeq : a'.val = BitVec.setWidth (target.widenWidth n) a₁.val := (Prod.mk.inj ha_val).1
    have hbeq : b'.val = BitVec.setWidth (target.widenWidth n) b₁.val := (Prod.mk.inj hb_val).1
    have hceq : c'.val = c₁.val := (Prod.mk.inj hc_val).1
    have hs := opWp_widen_spec hv hsupp
    dsimp only [Tup, LVar, LegalTarget.legalTys] at k hs ⊢
    by_cases hn0 : n = 0
    · subst hn0; simp only [beq_self_eq_true, ↓reduceIte]
      refine hk _ _ (TRel.cons ?_ (TRel.cons ?_ TRel.nil)) hw
      · change (0#(target.widenWidth 0), ()) = (BitVec.setWidth _ _, ())
        have h0 : a₁.val - b₁.val - BitVec.ofNat 0 c₁.val.toNat = 0#0 := Subsingleton.elim _ _
        rw [h0]; congr 1
      · change (c'.val, ()) = (decide (a₁.val.toNat < b₁.val.toNat + c₁.val.toNat), ())
        have ha0 : a₁.val.toNat = 0 := by have := a₁.val.isLt; omega
        have hb0 : b₁.val.toNat = 0 := by have := b₁.val.isLt; omega
        rw [hceq, ha0, hb0]; cases c₁.val <;> rfl
    · simp only [beq_iff_eq, hn0, ↓reduceIte]
      split
      · next hnw =>
        rw [wp_let, op3_wp_eq, OpCode.wp_subb]; dsimp only
        have hp : 2 ^ n = 2 ^ target.widenWidth n := by rw [← hnw]
        have ha_nat : a'.val.toNat = a₁.val.toNat := by
          rw [haeq, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by simpa [← hp] using a₁.val.isLt)]
        have hb_nat : b'.val.toNat = b₁.val.toNat := by
          rw [hbeq, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by simpa [← hp] using b₁.val.isLt)]
        refine hk _ _ (TRel.cons ?_ (TRel.cons ?_ TRel.nil)) hw
        · change (_, ()) = (BitVec.setWidth (target.widenWidth n) _, ())
          congr 1; rw [hceq]
          exact op2_setWidth_self (op := fun {k} (x y : BitVec k) => x - y - BitVec.ofNat k c₁.val.toNat)
            hnw haeq hbeq
        · change (decide _, ()) = (decide _, ())
          congr 1; simp only [ha_nat, hb_nat, hceq]
      · next hnw =>
        rw [wp_let, op3_wp_eq, OpCode.wp_subb]; dsimp only
        refine emitMaskToN_wp hs.2.1 rfl fun d hd => ?_
        simp only [Arg.val_var] at hd
        have hwid := opWp_subb_widened (Nat.pos_of_ne_zero hn0) (Nat.lt_of_le_of_ne hs.2.1 hnw)
          a₁.val b₁.val c₁.val
        refine hk _ _ (TRel.cons ?_ (TRel.cons ?_ TRel.nil)) hw
        · change (d.val, ()) = (BitVec.setWidth (target.widenWidth n) _, ())
          congr 1; rw [hd, haeq, hbeq, hceq, hwid.1]
        · change (decide (a'.val.toNat < b'.val.toNat + c'.val.toNat), ()) = (_, ())
          congr 1; rw [haeq, hbeq, hceq]; exact hwid.2
  | umulw n =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩
    rcases hargs with _ | @⟨_, _, b₁, b₂, _, _, hb, hargs⟩; cases hargs
    dsimp only [Op.wp, vals] at hw
    rw [OpCode.wp_umulw] at hw
    rw [legalOp.eq_33]
    dsimp only [Tup, LVar, LegalTarget.legalTys] at k ⊢
    have ha_val := valsTup_legalArg target hG ha
    have hb_val := valsTup_legalArg target hG hb
    rcases hpa : legalArg target a₂ with ⟨a', ⟨⟩⟩; rw [hpa] at ha_val
    rcases hpb : legalArg target b₂ with ⟨b', ⟨⟩⟩; rw [hpb] at hb_val
    have haeq : a'.val = BitVec.setWidth (target.widenWidth n) a₁.val := (Prod.mk.inj ha_val).1
    have hbeq : b'.val = BitVec.setWidth (target.widenWidth n) b₁.val := (Prod.mk.inj hb_val).1
    have hs := opWp_widen_spec hv hsupp
    dsimp only [Tup, LVar, LegalTarget.legalTys] at k hs ⊢
    by_cases hn0 : n = 0
    · subst hn0; simp only [beq_self_eq_true, ↓reduceIte]
      have hzv : ∀ v : BitVec 0, 0#(target.widenWidth 0) = BitVec.setWidth (target.widenWidth 0) v := fun v => by
        rw [Subsingleton.elim v (0#0)]; apply BitVec.eq_of_toNat_eq; simp
      refine hk _ _ (TRel.cons ?_ (TRel.cons ?_ TRel.nil)) hw <;>
        (change (0#(target.widenWidth 0), ()) = (BitVec.setWidth (target.widenWidth 0) _, ());
         congr 1; exact hzv _)
    · simp only [beq_iff_eq, hn0, ↓reduceIte]
      split
      · next hnw =>
        rw [wp_let, op2_wp_eq, OpCode.wp_umulw]; dsimp only
        refine hk _ _ (TRel.cons ?_ (TRel.cons ?_ TRel.nil)) hw
        · change (_, ()) = (BitVec.setWidth (target.widenWidth n) _, ())
          congr 1; simp only [Arg.val_var]
          exact op2_setWidth_self (op := fun {k} (x y : BitVec k) => x * y) hnw haeq hbeq
        · change (_, ()) = (BitVec.setWidth (target.widenWidth n) _, ())
          congr 1; simp only [Arg.val_var]
          exact op2_setWidth_self (op := fun {k} (x y : BitVec k) => BitVec.ofNat k (x.toNat * y.toNat / 2 ^ k))
            hnw haeq hbeq
      · next hnw =>
        have hn_pos : 0 < n := Nat.pos_of_ne_zero hn0
        have hn_lt : n < target.widenWidth n := Nat.lt_of_le_of_ne hs.2.1 hnw
        rw [wp_let, op2_wp_eq, OpCode.wp_umulw]; dsimp only
        refine emitMaskToN_wp hs.2.1 rfl fun lo hlo => ?_
        rw [wp_let, op2_wp_eq, OpCode.wp_lshr, wp_let, op2_wp_eq, OpCode.wp_shl, wp_let, op2_wp_eq, OpCode.wp_or]
        simp only [Bool.false_eq_true, ↓reduceIte]
        refine emitMaskToN_wp hs.2.1 rfl fun hi hhi => ?_
        simp only [Arg.val_var] at hlo
        simp only [Arg.val_var, Arg.val_imm, lift2] at hhi
        have hwid := opWp_umulw_widened hn_pos hn_lt a₁.val b₁.val
        have hnw2 : target.widenWidth n < 2 ^ target.widenWidth n := Nat.lt_two_pow_self
        have hn2w : n < 2 ^ target.widenWidth n := Nat.lt_trans hn_lt hnw2
        have hwsub2w : target.widenWidth n - n < 2 ^ target.widenWidth n :=
          Nat.lt_of_le_of_lt (Nat.sub_le _ _) hnw2
        have hm1 : (BitVec.ofNat (target.widenWidth n) n).toNat % target.widenWidth n = n := by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn2w, Nat.mod_eq_of_lt hn_lt]
        have hm2 : (BitVec.ofNat (target.widenWidth n) (target.widenWidth n - n)).toNat % target.widenWidth n =
            target.widenWidth n - n := by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hwsub2w, Nat.mod_eq_of_lt (by omega)]
        refine hk _ _ (TRel.cons ?_ (TRel.cons ?_ TRel.nil)) hw
        · change (lo.val, ()) = (BitVec.setWidth (target.widenWidth n) _, ())
          congr 1; rw [hlo, haeq, hbeq, hwid.1]
        · change (hi.val, ()) = (BitVec.setWidth (target.widenWidth n) _, ())
          congr 1; rw [hhi, haeq, hbeq, hm1, hm2, hwid.2]
  | smulw n =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩
    rcases hargs with _ | @⟨_, _, b₁, b₂, _, _, hb, hargs⟩; cases hargs
    dsimp only [Op.wp, vals] at hw
    rw [OpCode.wp_smulw] at hw
    rw [legalOp.eq_34]
    dsimp only [Tup, LVar, LegalTarget.legalTys] at k ⊢
    have ha_val := valsTup_legalArg target hG ha
    have hb_val := valsTup_legalArg target hG hb
    rcases hpa : legalArg target a₂ with ⟨a', ⟨⟩⟩; rw [hpa] at ha_val
    rcases hpb : legalArg target b₂ with ⟨b', ⟨⟩⟩; rw [hpb] at hb_val
    have haeq : a'.val = BitVec.setWidth (target.widenWidth n) a₁.val := (Prod.mk.inj ha_val).1
    have hbeq : b'.val = BitVec.setWidth (target.widenWidth n) b₁.val := (Prod.mk.inj hb_val).1
    have hs := opWp_widen_spec hv hsupp
    dsimp only [Tup, LVar, LegalTarget.legalTys] at k hs ⊢
    by_cases hn0 : n = 0
    · subst hn0; simp only [beq_self_eq_true, ↓reduceIte]
      have hzv : ∀ v : BitVec 0, 0#(target.widenWidth 0) = BitVec.setWidth (target.widenWidth 0) v := fun v => by
        rw [Subsingleton.elim v (0#0)]; apply BitVec.eq_of_toNat_eq; simp
      refine hk _ _ (TRel.cons ?_ (TRel.cons ?_ TRel.nil)) hw <;>
        (change (0#(target.widenWidth 0), ()) = (BitVec.setWidth (target.widenWidth 0) _, ());
         congr 1; exact hzv _)
    · simp only [beq_iff_eq, hn0, ↓reduceIte]
      split
      · next hnw =>
        rw [wp_let, op2_wp_eq, OpCode.wp_smulw]; dsimp only
        refine hk _ _ (TRel.cons ?_ (TRel.cons ?_ TRel.nil)) hw
        · change (_, ()) = (BitVec.setWidth (target.widenWidth n) _, ())
          congr 1; simp only [Arg.val_var]
          exact op2_setWidth_self (op := fun {k} (x y : BitVec k) => x * y) hnw haeq hbeq
        · change (_, ()) = (BitVec.setWidth (target.widenWidth n) _, ())
          congr 1; simp only [Arg.val_var]
          exact op2_setWidth_self (op := fun {k} (x y : BitVec k) =>
            BitVec.extractLsb' k k (BitVec.ofInt (k + k) (x.toInt * y.toInt))) hnw haeq hbeq
      · next hnw =>
        have hn_pos : 0 < n := Nat.pos_of_ne_zero hn0
        have hn_lt : n < target.widenWidth n := Nat.lt_of_le_of_ne hs.2.1 hnw
        refine emitSextToW_wp hn_pos hs.2.1 haeq fun sa hsa =>
          emitSextToW_wp hn_pos hs.2.1 hbeq fun sb hsb => ?_
        rw [wp_let, op2_wp_eq, OpCode.wp_smulw]; dsimp only
        refine emitMaskToN_wp hs.2.1 rfl fun lo hlo => ?_
        rw [wp_let, op2_wp_eq, OpCode.wp_lshr, wp_let, op2_wp_eq, OpCode.wp_shl, wp_let, op2_wp_eq, OpCode.wp_or]
        simp only [Bool.false_eq_true, ↓reduceIte]
        refine emitMaskToN_wp hs.2.1 rfl fun hi hhi => ?_
        simp only [Arg.val_var] at hlo
        simp only [Arg.val_var, Arg.val_imm, lift2] at hhi
        have hwid := opWp_smulw_widened hn_pos hn_lt a₁.val b₁.val
        have hnw2 : target.widenWidth n < 2 ^ target.widenWidth n := Nat.lt_two_pow_self
        have hn2w : n < 2 ^ target.widenWidth n := Nat.lt_trans hn_lt hnw2
        have hwsub2w : target.widenWidth n - n < 2 ^ target.widenWidth n :=
          Nat.lt_of_le_of_lt (Nat.sub_le _ _) hnw2
        have hm1 : (BitVec.ofNat (target.widenWidth n) n).toNat % target.widenWidth n = n := by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn2w, Nat.mod_eq_of_lt hn_lt]
        have hm2 : (BitVec.ofNat (target.widenWidth n) (target.widenWidth n - n)).toNat % target.widenWidth n =
            target.widenWidth n - n := by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hwsub2w, Nat.mod_eq_of_lt (by omega)]
        refine hk _ _ (TRel.cons ?_ (TRel.cons ?_ TRel.nil)) hw
        · change (lo.val, ()) = (BitVec.setWidth (target.widenWidth n) _, ())
          congr 1; rw [hlo, hsa, hsb, hwid.1]
        · change (hi.val, ()) = (BitVec.setWidth (target.widenWidth n) _, ())
          congr 1; rw [hhi, hsa, hsb, hm1, hm2, hwid.2]
  | udiv n =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩
    rcases hargs with _ | @⟨_, _, b₁, b₂, _, _, hb, hargs⟩; cases hargs
    dsimp only [Op.wp, vals] at hw
    rw [OpCode.wp_udiv] at hw
    rcases hw with ⟨hb0, hwP⟩
    have hn0 : n ≠ 0 := by intro h; subst h; exact hb0 (Subsingleton.elim _ _)
    rw [legalOp.eq_35]
    dsimp only [Tup, LVar, LegalTarget.legalTys] at k ⊢
    have ha_val := valsTup_legalArg target hG ha
    have hb_val := valsTup_legalArg target hG hb
    rcases hpa : legalArg target a₂ with ⟨a', ⟨⟩⟩; rw [hpa] at ha_val
    rcases hpb : legalArg target b₂ with ⟨b', ⟨⟩⟩; rw [hpb] at hb_val
    have haeq : a'.val = BitVec.setWidth (target.widenWidth n) a₁.val := (Prod.mk.inj ha_val).1
    have hbeq : b'.val = BitVec.setWidth (target.widenWidth n) b₁.val := (Prod.mk.inj hb_val).1
    have hs := opWp_widen_spec hv hsupp
    dsimp only [Tup, LVar, LegalTarget.legalTys] at k hs ⊢
    simp only [beq_iff_eq, hn0, ↓reduceIte]
    rw [wp_let, op2_wp_eq, OpCode.wp_udiv]
    have hp : 2 ^ n ≤ 2 ^ target.widenWidth n := Nat.pow_le_pow_right (by omega) hs.2.1
    have hbnz : b'.val ≠ 0 := by
      intro h; apply hb0; apply BitVec.eq_of_toNat_eq
      have := congrArg BitVec.toNat h
      rw [hbeq, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le b₁.val.isLt hp)] at this
      exact this
    refine ⟨hbnz, hk _ _ (TRel.cons ?_ TRel.nil) hwP⟩
    change (a'.val / b'.val, ()) = (BitVec.setWidth (target.widenWidth n) (a₁.val / b₁.val), ())
    congr 1; apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_udiv, haeq, hbeq, BitVec.toNat_setWidth, BitVec.toNat_setWidth,
      BitVec.toNat_setWidth, BitVec.toNat_udiv,
      Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le a₁.val.isLt hp),
      Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le b₁.val.isLt hp),
      Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self a₁.val.toNat b₁.val.toNat) (Nat.lt_of_lt_of_le a₁.val.isLt hp))]
  | sdiv n =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩
    rcases hargs with _ | @⟨_, _, b₁, b₂, _, _, hb, hargs⟩; cases hargs
    dsimp only [Op.wp, vals] at hw
    rw [OpCode.wp_sdiv] at hw
    rcases hw with ⟨hsdef, hwP⟩
    have hb0 : b₁.val ≠ 0 := by
      unfold sdivDefined at hsdef; simp only [Bool.and_eq_true, bne_iff_ne] at hsdef; exact hsdef.1
    have hn0 : n ≠ 0 := by intro h; subst h; exact hb0 (Subsingleton.elim _ _)
    rw [legalOp.eq_36]
    dsimp only [Tup, LVar, LegalTarget.legalTys] at k ⊢
    have ha_val := valsTup_legalArg target hG ha
    have hb_val := valsTup_legalArg target hG hb
    rcases hpa : legalArg target a₂ with ⟨a', ⟨⟩⟩; rw [hpa] at ha_val
    rcases hpb : legalArg target b₂ with ⟨b', ⟨⟩⟩; rw [hpb] at hb_val
    have haeq : a'.val = BitVec.setWidth (target.widenWidth n) a₁.val := (Prod.mk.inj ha_val).1
    have hbeq : b'.val = BitVec.setWidth (target.widenWidth n) b₁.val := (Prod.mk.inj hb_val).1
    have hs := opWp_widen_spec hv hsupp
    dsimp only [Tup, LVar, LegalTarget.legalTys] at k hs ⊢
    simp only [beq_iff_eq, hn0, ↓reduceIte]
    split
    · next hnw =>
      rw [wp_let, op2_wp_eq, OpCode.wp_sdiv]; dsimp only
      refine ⟨op2_pred_self (P := fun {k} x y => sdivDefined x y = true) hnw haeq hbeq hsdef,
        hk _ _ (TRel.cons ?_ TRel.nil) hwP⟩
      change (_, ()) = (BitVec.setWidth (target.widenWidth n) _, ())
      congr 1; simp only [Arg.val_var]; exact op2_setWidth_self hnw haeq hbeq
    · next hnw =>
      have hn_pos : 0 < n := Nat.pos_of_ne_zero hn0
      have hn_lt : n < target.widenWidth n := Nat.lt_of_le_of_ne hs.2.1 hnw
      refine emitSextToW_wp hn_pos hs.2.1 haeq fun sa hsa =>
        emitSextToW_wp hn_pos hs.2.1 hbeq fun sb hsb => ?_
      rw [wp_let, op2_wp_eq, OpCode.wp_sdiv]; dsimp only
      refine ⟨by rw [hsa, hsb]; exact opWp_sdivDefined_widened hn_pos hn_lt hb0, ?_⟩
      refine emitMaskToN_wp hs.2.1 rfl fun rm hrm => ?_
      simp only [Arg.val_var] at hrm
      refine hk _ _ (TRel.cons ?_ TRel.nil) hwP
      change (rm.val, ()) = (BitVec.setWidth (target.widenWidth n) (BitVec.sdiv a₁.val b₁.val), ())
      congr 1; rw [hrm, hsa, hsb, opWp_sdiv_widened hs.2.1 a₁.val b₁.val]
  | urem n =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩
    rcases hargs with _ | @⟨_, _, b₁, b₂, _, _, hb, hargs⟩; cases hargs
    dsimp only [Op.wp, vals] at hw
    rw [OpCode.wp_urem] at hw
    rcases hw with ⟨hb0, hwP⟩
    have hn0 : n ≠ 0 := by intro h; subst h; exact hb0 (Subsingleton.elim _ _)
    rw [legalOp.eq_37]
    dsimp only [Tup, LVar, LegalTarget.legalTys] at k ⊢
    have ha_val := valsTup_legalArg target hG ha
    have hb_val := valsTup_legalArg target hG hb
    rcases hpa : legalArg target a₂ with ⟨a', ⟨⟩⟩; rw [hpa] at ha_val
    rcases hpb : legalArg target b₂ with ⟨b', ⟨⟩⟩; rw [hpb] at hb_val
    have haeq : a'.val = BitVec.setWidth (target.widenWidth n) a₁.val := (Prod.mk.inj ha_val).1
    have hbeq : b'.val = BitVec.setWidth (target.widenWidth n) b₁.val := (Prod.mk.inj hb_val).1
    have hs := opWp_widen_spec hv hsupp
    dsimp only [Tup, LVar, LegalTarget.legalTys] at k hs ⊢
    simp only [beq_iff_eq, hn0, ↓reduceIte]
    rw [wp_let, op2_wp_eq, OpCode.wp_urem]
    have hp : 2 ^ n ≤ 2 ^ target.widenWidth n := Nat.pow_le_pow_right (by omega) hs.2.1
    have hbnz : b'.val ≠ 0 := by
      intro h; apply hb0; apply BitVec.eq_of_toNat_eq
      have := congrArg BitVec.toNat h
      rw [hbeq, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le b₁.val.isLt hp)] at this
      exact this
    refine ⟨hbnz, hk _ _ (TRel.cons ?_ TRel.nil) hwP⟩
    change (a'.val % b'.val, ()) = (BitVec.setWidth (target.widenWidth n) (a₁.val % b₁.val), ())
    congr 1; apply BitVec.eq_of_toNat_eq
    have hbpos : 0 < b₁.val.toNat := Nat.pos_of_ne_zero fun h => hb0 (BitVec.eq_of_toNat_eq h)
    rw [BitVec.toNat_umod, haeq, hbeq, BitVec.toNat_setWidth, BitVec.toNat_setWidth,
      BitVec.toNat_setWidth, BitVec.toNat_umod,
      Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le a₁.val.isLt hp),
      Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le b₁.val.isLt hp),
      Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt a₁.val.toNat hbpos) (Nat.lt_of_lt_of_le b₁.val.isLt hp))]
  | srem n =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩
    rcases hargs with _ | @⟨_, _, b₁, b₂, _, _, hb, hargs⟩; cases hargs
    dsimp only [Op.wp, vals] at hw
    rw [OpCode.wp_srem] at hw
    rcases hw with ⟨hsdef, hwP⟩
    have hb0 : b₁.val ≠ 0 := by
      unfold sdivDefined at hsdef; simp only [Bool.and_eq_true, bne_iff_ne] at hsdef; exact hsdef.1
    have hn0 : n ≠ 0 := by intro h; subst h; exact hb0 (Subsingleton.elim _ _)
    rw [legalOp.eq_38]
    dsimp only [Tup, LVar, LegalTarget.legalTys] at k ⊢
    have ha_val := valsTup_legalArg target hG ha
    have hb_val := valsTup_legalArg target hG hb
    rcases hpa : legalArg target a₂ with ⟨a', ⟨⟩⟩; rw [hpa] at ha_val
    rcases hpb : legalArg target b₂ with ⟨b', ⟨⟩⟩; rw [hpb] at hb_val
    have haeq : a'.val = BitVec.setWidth (target.widenWidth n) a₁.val := (Prod.mk.inj ha_val).1
    have hbeq : b'.val = BitVec.setWidth (target.widenWidth n) b₁.val := (Prod.mk.inj hb_val).1
    have hs := opWp_widen_spec hv hsupp
    dsimp only [Tup, LVar, LegalTarget.legalTys] at k hs ⊢
    simp only [beq_iff_eq, hn0, ↓reduceIte]
    split
    · next hnw =>
      rw [wp_let, op2_wp_eq, OpCode.wp_srem]; dsimp only
      refine ⟨op2_pred_self (P := fun {k} x y => sdivDefined x y = true) hnw haeq hbeq hsdef,
        hk _ _ (TRel.cons ?_ TRel.nil) hwP⟩
      change (_, ()) = (BitVec.setWidth (target.widenWidth n) _, ())
      congr 1; simp only [Arg.val_var]; exact op2_setWidth_self hnw haeq hbeq
    · next hnw =>
      have hn_pos : 0 < n := Nat.pos_of_ne_zero hn0
      have hn_lt : n < target.widenWidth n := Nat.lt_of_le_of_ne hs.2.1 hnw
      refine emitSextToW_wp hn_pos hs.2.1 haeq fun sa hsa =>
        emitSextToW_wp hn_pos hs.2.1 hbeq fun sb hsb => ?_
      rw [wp_let, op2_wp_eq, OpCode.wp_srem]; dsimp only
      refine ⟨by rw [hsa, hsb]; exact opWp_sdivDefined_widened hn_pos hn_lt hb0, ?_⟩
      refine emitMaskToN_wp hs.2.1 rfl fun rm hrm => ?_
      simp only [Arg.val_var] at hrm
      refine hk _ _ (TRel.cons ?_ TRel.nil) hwP
      change (rm.val, ()) = (BitVec.setWidth (target.widenWidth n) (BitVec.srem a₁.val b₁.val), ())
      congr 1; rw [hrm, hsa, hsb, opWp_srem_widened hs.2.1 a₁.val b₁.val]
  | udiv0 n =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩
    rcases hargs with _ | @⟨_, _, b₁, b₂, _, _, hb, hargs⟩; cases hargs
    dsimp only [Op.wp, vals] at hw
    rw [OpCode.wp_udiv0] at hw
    rw [legalOp.eq_39]
    dsimp only [Tup, LVar, LegalTarget.legalTys] at k ⊢
    have ha_val := valsTup_legalArg target hG ha
    have hb_val := valsTup_legalArg target hG hb
    rcases hpa : legalArg target a₂ with ⟨a', ⟨⟩⟩; rw [hpa] at ha_val
    rcases hpb : legalArg target b₂ with ⟨b', ⟨⟩⟩; rw [hpb] at hb_val
    have haeq : a'.val = BitVec.setWidth (target.widenWidth n) a₁.val := (Prod.mk.inj ha_val).1
    have hbeq : b'.val = BitVec.setWidth (target.widenWidth n) b₁.val := (Prod.mk.inj hb_val).1
    have hs := opWp_widen_spec hv hsupp
    dsimp only [Tup, LVar, LegalTarget.legalTys] at k hs ⊢
    by_cases hn0 : n = 0
    · subst hn0; simp only [beq_self_eq_true, ↓reduceIte]
      refine hk _ _ (TRel.cons ?_ TRel.nil) hw
      change (0#(target.widenWidth 0), ()) = (BitVec.setWidth _ _, ())
      have h0 : (if b₁.val = 0 then 0 else a₁.val / b₁.val) = 0#0 := Subsingleton.elim _ _
      rw [h0]; congr 1
    · simp only [beq_iff_eq, hn0, ↓reduceIte]
      rw [wp_let, op2_wp_eq, OpCode.wp_udiv0]; dsimp only
      refine hk _ _ (TRel.cons ?_ TRel.nil) hw
      change ((if b'.val = 0 then 0 else a'.val / b'.val), ()) =
        (BitVec.setWidth (target.widenWidth n) (if b₁.val = 0 then 0 else a₁.val / b₁.val), ())
      congr 1
      have hp : 2 ^ n ≤ 2 ^ target.widenWidth n := Nat.pow_le_pow_right (by omega) hs.2.1
      have hbz : (b'.val = 0) ↔ (b₁.val = 0) := by
        constructor
        · intro h; apply BitVec.eq_of_toNat_eq
          have := congrArg BitVec.toNat h
          rw [hbeq, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le b₁.val.isLt hp)] at this
          exact this
        · intro h; rw [hbeq, h]; apply BitVec.eq_of_toNat_eq; simp
      by_cases hb0 : b₁.val = 0
      · have hb0' : b'.val = 0 := hbz.mpr hb0
        simp only [hb0, hb0', ↓reduceIte]; apply BitVec.eq_of_toNat_eq; simp
      · have hb0' : b'.val ≠ 0 := fun h => hb0 (hbz.mp h)
        simp only [hb0, hb0', ↓reduceIte]; apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_udiv, haeq, hbeq, BitVec.toNat_setWidth, BitVec.toNat_setWidth,
          BitVec.toNat_setWidth, BitVec.toNat_udiv,
          Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le a₁.val.isLt hp),
          Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le b₁.val.isLt hp),
          Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self a₁.val.toNat b₁.val.toNat) (Nat.lt_of_lt_of_le a₁.val.isLt hp))]
  | sdiv0 n =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩
    rcases hargs with _ | @⟨_, _, b₁, b₂, _, _, hb, hargs⟩; cases hargs
    dsimp only [Op.wp, vals] at hw
    rw [OpCode.wp_sdiv0] at hw
    rw [legalOp.eq_40]
    dsimp only [Tup, LVar, LegalTarget.legalTys] at k ⊢
    have ha_val := valsTup_legalArg target hG ha
    have hb_val := valsTup_legalArg target hG hb
    rcases hpa : legalArg target a₂ with ⟨a', ⟨⟩⟩; rw [hpa] at ha_val
    rcases hpb : legalArg target b₂ with ⟨b', ⟨⟩⟩; rw [hpb] at hb_val
    have haeq : a'.val = BitVec.setWidth (target.widenWidth n) a₁.val := (Prod.mk.inj ha_val).1
    have hbeq : b'.val = BitVec.setWidth (target.widenWidth n) b₁.val := (Prod.mk.inj hb_val).1
    have hs := opWp_widen_spec hv hsupp
    dsimp only [Tup, LVar, LegalTarget.legalTys] at k hs ⊢
    by_cases hn0 : n = 0
    · subst hn0; simp only [beq_self_eq_true, ↓reduceIte]
      refine hk _ _ (TRel.cons ?_ TRel.nil) hw
      change (0#(target.widenWidth 0), ()) = (BitVec.setWidth _ _, ())
      have h0 : (if b₁.val = 0 then 0 else BitVec.sdiv a₁.val b₁.val) = 0#0 := Subsingleton.elim _ _
      rw [h0]; congr 1
    · simp only [beq_iff_eq, hn0, ↓reduceIte]
      split
      · next hnw =>
        rw [wp_let, op2_wp_eq, OpCode.wp_sdiv0]; dsimp only
        refine hk _ _ (TRel.cons ?_ TRel.nil) hw
        change (_, ()) = (BitVec.setWidth (target.widenWidth n) _, ())
        congr 1
        exact op2_setWidth_self (op := fun {k} (x y : BitVec k) => if y = 0 then 0 else BitVec.sdiv x y)
          hnw haeq hbeq
      · next _ =>
        have hn_pos : 0 < n := Nat.pos_of_ne_zero hn0
        refine emitSextToW_wp hn_pos hs.2.1 haeq fun sa hsa =>
          emitSextToW_wp hn_pos hs.2.1 hbeq fun sb hsb => ?_
        rw [wp_let, op2_wp_eq, OpCode.wp_sdiv0]; dsimp only
        refine emitMaskToN_wp hs.2.1 rfl fun rm hrm => ?_
        simp only [Arg.val_var] at hrm
        refine hk _ _ (TRel.cons ?_ TRel.nil) hw
        change (rm.val, ()) = (BitVec.setWidth (target.widenWidth n) _, ())
        congr 1; rw [hrm, hsa, hsb]; congr 1
        have hsbz : (BitVec.signExtend (target.widenWidth n) b₁.val = 0) ↔ (b₁.val = 0) := by
          constructor
          · intro h
            have hi := congrArg BitVec.toInt h
            rw [opWp_signExtend_toInt hs.2.1] at hi
            have := congrArg (BitVec.ofInt n) hi
            simpa [BitVec.ofInt_toInt] using this
          · intro h; rw [h]; apply BitVec.eq_of_toNat_eq
            rw [BitVec.signExtend_eq_setWidth_of_msb_false (by
              rw [BitVec.msb_eq_getLsbD_last]; simp)]; simp
        by_cases hb0 : b₁.val = 0
        · have hb0' : BitVec.signExtend (target.widenWidth n) b₁.val = 0 := hsbz.mpr hb0
          simp only [hb0', ↓reduceIte]; simp only [hb0, ↓reduceIte]; apply BitVec.eq_of_toNat_eq; simp
        · have hb0' : BitVec.signExtend (target.widenWidth n) b₁.val ≠ 0 := fun h => hb0 (hsbz.mp h)
          rw [ite_eq_right hb0', ite_eq_right hb0]
          exact opWp_sdiv_widened hs.2.1 a₁.val b₁.val
  | mkpair a b =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩
    rcases hargs with _ | @⟨_, _, b₁, b₂, _, _, hb, hargs⟩; cases hargs
    dsimp only [Op.wp, vals] at hw
    rw [OpCode.wp_mkpair] at hw
    rw [legalOp.eq_41]
    dsimp only [LegalTarget.supportsOpCode] at hsupp
    simp only [Bool.and_eq_true] at hsupp
    dsimp only
    by_cases hkp : target.keepsPacked (a.pair b) = true
    · simp only [hkp, ↓reduceDIte]
      refine packFromLegal_wp target a hsupp.1 (legalArg target a₂) a₁.val (valsTup_legalArg target hG ha)
        fun pa hpa => packFromLegal_wp target b hsupp.2 (legalArg target b₂) b₁.val
          (valsTup_legalArg target hG hb) fun pb hpb => ?_
      rw [wp_let, op2_wp_eq, OpCode.wp_mkpair]; dsimp only
      refine hk _ _ (TRel.cons ?_ TRel.nil) hw
      have hres := opWp_valsTup_tupToPacked hkp (Arg.var (V := Val) (pa.val, pb.val), ())
      simpa [hpa, hpb] using hres
    · have hkf : target.keepsPacked (a.pair b) = false := Bool.eq_false_iff.mpr hkp
      simp only [hkp]
      exact hk _ _ (TRel.cons (opWp_valsTup_tupToSplit hkf (legalArg target a₂) (legalArg target b₂)
        (valsTup_legalArg target hG ha) (valsTup_legalArg target hG hb)) TRel.nil) hw
  | unpair a b =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, hp, hargs⟩; cases hargs
    dsimp only [Op.wp, vals] at hw
    rw [OpCode.wp_unpair] at hw
    rw [legalOp.eq_42]
    dsimp only [LegalTarget.supportsOpCode] at hsupp
    simp only [Bool.and_eq_true] at hsupp
    dsimp only
    by_cases hkp : target.keepsPacked (a.pair b) = true
    · simp only [hkp, ↓reduceDIte]
      have hlp := valsTup_legalArg target hG hp
      have hfst := opWp_packedToTup_fst hkp (legalArg target a₂) a₁.val hlp
      cases hpfst : (packedToTup hkp (legalArg target a₂)).fst with
      | imm c =>
        simp only [hpfst] at hfst ⊢
        have hc_eq : c = a₁.val := hfst
        rw [hc_eq]
        exact hk _ _ (TRel.cons (opWp_valsTup_encodeImm target a a₁.val.1)
          (TRel.cons (opWp_valsTup_encodeImm target b a₁.val.2) TRel.nil)) hw
      | var v =>
        simp only [hpfst] at hfst ⊢
        have hv_eq : v = a₁.val := hfst
        rw [wp_let, op1_wp_eq, OpCode.wp_unpair]; dsimp only
        rw [hv_eq]
        exact unpackToLegal_wp target a hsupp.1 (Arg.var a₁.val.1) fun la hla =>
          unpackToLegal_wp target b hsupp.2 (Arg.var a₁.val.2) fun lb hlb =>
            hk _ _ (TRel.cons hla (TRel.cons hlb TRel.nil)) hw
    · have hkf : target.keepsPacked (a.pair b) = false := Bool.eq_false_iff.mpr hkp
      simp only [hkp]
      have hsp := opWp_valsTup_splitToTup hkf (legalArg target a₂) a₁.val (valsTup_legalArg target hG hp)
      rcases htup : tupSplit (splitToTup hkf (legalArg target a₂)) with ⟨la, lb⟩
      rw [htup] at hsp
      simp only [htup]
      exact hk _ _ (TRel.cons hsp.1 (TRel.cons hsp.2 TRel.nil)) hw
  | bitcast t u hsz =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩; cases hargs
    dsimp only [Op.wp, vals] at hw
    rw [OpCode.wp_bitcast] at hw
    rw [legalOp.eq_43]
    dsimp only [LegalTarget.supportsOpCode] at hsupp
    simp only [Bool.and_eq_true] at hsupp
    dsimp only
    by_cases heq : t = u
    · subst heq; simp only [↓reduceDIte]
      have hid : ofBits t (BitVec.cast rfl (toBits t a₁.val)) = a₁.val := ofBits_toBits t a₁.val
      rw [hid] at hw
      exact hk _ _ (TRel.cons (valsTup_legalArg target hG ha) TRel.nil) hw
    · simp only [heq, ↓reduceDIte]
      by_cases ht : isNatTy target t = true
      · refine dite_true_wp (P := fun e => wp Γ Q X e m) (by cases t <;> simpa [isNatTy] using ht) ?_
        by_cases hu : isNatTy target u = true
        · refine dite_true_wp (P := fun e => wp Γ Q X e m) (by cases u <;> simpa [isNatTy] using hu) ?_
          have hlt_leg : target.isLegalTy t = true := by
            cases t with | bits _ => exact (Bool.and_eq_true _ _ |>.mp ht).1 | _ => exact ht
          have hlu_leg : target.isLegalTy u = true := by
            cases u with | bits _ => exact (Bool.and_eq_true _ _ |>.mp hu).1 | _ => exact hu
          have hlt_tys : target.legalTys t = [t] := opWp_isLegalTy_legalTys hlt_leg
          have hlu_tys : target.legalTys u = [u] := opWp_isLegalTy_legalTys hlu_leg
          rw [wp_let, op1_wp_eq, OpCode.wp_bitcast]; dsimp only
          have hin := opWp_cast_isLegal_in hlt_leg hlt_tys (legalArg target a₂) a₁.val
            (valsTup_legalArg target hG ha)
          rw [hin]
          exact hk _ _ (TRel.cons (opWp_cast_isLegal_out hlu_leg hlu_tys (Arg.var _)) TRel.nil) hw
        · refine dite_false_wp (P := fun e => wp Γ Q X e m) (by cases u <;> simpa [isNatTy] using hu) ?_
          refine splitLegalToLeaves_wp target t hsupp.1 (legalArg target a₂) a₁.val
            (valsTup_legalArg target hG ha) fun fx hfx =>
            packLeavesToWords64_wp target hv t hsupp.1 hfx fun words hbits _ _ =>
            unpackWords64ToLeaves_wp target hv u hsupp.2
              (fun i hi => by
                rw [Nat.zero_add, hbits i (by rw [hsz]; exact hi), toBits_ofBits, BitVec.getLsbD_cast])
              fun fu hfu => packLeavesToLegal_wp target u hsupp.2 fu _ hfu fun res hres =>
                hk _ _ (TRel.cons hres TRel.nil) hw
      · refine dite_false_wp (P := fun e => wp Γ Q X e m) (by cases t <;> simpa [isNatTy] using ht) ?_
        refine splitLegalToLeaves_wp target t hsupp.1 (legalArg target a₂) a₁.val
          (valsTup_legalArg target hG ha) fun fx hfx =>
          packLeavesToWords64_wp target hv t hsupp.1 hfx fun words hbits _ _ =>
          unpackWords64ToLeaves_wp target hv u hsupp.2
            (fun i hi => by
              rw [Nat.zero_add, hbits i (by rw [hsz]; exact hi), toBits_ofBits, BitVec.getLsbD_cast])
            fun fu hfu => packLeavesToLegal_wp target u hsupp.2 fu _ hfu fun res hres =>
              hk _ _ (TRel.cons hres TRel.nil) hw
  | shufd t imm =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩; cases hargs
    have hsupp := (Bool.and_eq_true _ _ |>.mp hsupp).1
    dsimp only [Op.wp, vals] at hw
    rw [OpCode.wp_shufd] at hw
    rcases hw with ⟨hne, hmod, hwP⟩
    rw [legalOp.eq_44]
    exact legalShufd_wp target hv imm t hsupp hne hmod (legalArg target a₂) a₁.val
      (valsTup_legalArg target hG ha) (fun res => k (res, ())) m fun res hres =>
        hk _ _ (TRel.cons hres TRel.nil) hwP
  | shufb t =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩
    rcases hargs with _ | @⟨_, _, b₁, b₂, _, _, hb, hargs⟩; cases hargs
    have hsupp := (Bool.and_eq_true _ _ |>.mp hsupp).1
    dsimp only [Op.wp, vals] at hw
    rw [OpCode.wp_shufb] at hw
    rcases hw with ⟨hne, hmod, hwP⟩
    rw [legalOp.eq_45]
    exact legalShufb_wp target hv t hsupp hne hmod (legalArg target a₂) (legalArg target b₂) a₁.val b₁.val
      (valsTup_legalArg target hG ha) (valsTup_legalArg target hG hb) (fun res => k (res, ())) m
      fun res hres => hk _ _ (TRel.cons hres TRel.nil) hwP
  | alignr t imm =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩
    rcases hargs with _ | @⟨_, _, b₁, b₂, _, _, hb, hargs⟩; cases hargs
    have hsupp := (Bool.and_eq_true _ _ |>.mp hsupp).1
    dsimp only [Op.wp, vals] at hw
    rw [OpCode.wp_alignr] at hw
    rcases hw with ⟨hne, hmod, hwP⟩
    rw [legalOp.eq_46]
    exact legalAlignr_wp target hv imm t hsupp hne hmod (legalArg target a₂) (legalArg target b₂) a₁.val b₁.val
      (valsTup_legalArg target hG ha) (valsTup_legalArg target hG hb) (fun res => k (res, ())) m
      fun res hres => hk _ _ (TRel.cons hres TRel.nil) hwP
  | blendw t imm =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩
    rcases hargs with _ | @⟨_, _, b₁, b₂, _, _, hb, hargs⟩; cases hargs
    have hsupp := (Bool.and_eq_true _ _ |>.mp hsupp).1
    dsimp only [Op.wp, vals] at hw
    rw [OpCode.wp_blendw] at hw
    rcases hw with ⟨hne, hmod, hwP⟩
    rw [legalOp.eq_47]
    exact legalBlendw_wp target hv imm t hsupp hne hmod (legalArg target a₂) (legalArg target b₂) a₁.val b₁.val
      (valsTup_legalArg target hG ha) (valsTup_legalArg target hG hb) (fun res => k (res, ())) m
      fun res hres => hk _ _ (TRel.cons hres TRel.nil) hwP
  | sha256rnds2 =>
    rcases hargs with _ | @⟨_, _, c₁, c₂, _, _, hc', hargs⟩
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩
    rcases hargs with _ | @⟨_, _, w₁, w₂, _, _, hw', hargs⟩; cases hargs
    have hsupp := (Bool.and_eq_true _ _ |>.mp hsupp).1
    dsimp only [Op.wp, vals] at hw
    rw [OpCode.wp_sha256rnds2] at hw
    rw [legalOp.eq_48]
    split
    · next hkps =>
      have hl_leg : target.isLegalTy v4i32 = true := hkps
      have hl_tys : target.legalTys v4i32 = [v4i32] := opWp_isLegalTy_legalTys hkps
      have hc_val := valsTup_legalArg target hG hc'
      have ha_val := valsTup_legalArg target hG ha
      have hw_val := valsTup_legalArg target hG hw'
      split
      · rw [wp_let, op3_wp_eq, OpCode.wp_sha256rnds2]; dsimp only
        rw [opWp_cast_isLegal_in hl_leg hl_tys (legalArg target c₂) c₁.val hc_val,
          opWp_cast_isLegal_in hl_leg hl_tys (legalArg target a₂) a₁.val ha_val,
          opWp_cast_isLegal_in hl_leg hl_tys (legalArg target w₂) w₁.val hw_val]
        exact hk _ _ (TRel.cons (opWp_cast_isLegal_out hl_leg hl_tys (Arg.var _)) TRel.nil) hw
      · refine splitLegalToLeaves_wp target v4i32 hsupp (legalArg target c₂) c₁.val hc_val fun fc hfc =>
          splitLegalToLeaves_wp target v4i32 hsupp (legalArg target a₂) a₁.val ha_val fun fa hfa =>
          splitLegalToLeaves_wp target v4i32 hsupp (legalArg target w₂) w₁.val hw_val fun fw hfw =>
          packLeavesToWords64_wp target hv v4i32 hsupp hfc fun wc hwc _ hwcl =>
          packLeavesToWords64_wp target hv v4i32 hsupp hfa fun wa hwa _ hwal =>
          packLeavesToWords64_wp target hv v4i32 hsupp hfw fun ww hww _ hwwl => ?_
        have hcw := opWp_words64_two wc (toBits v4i32 c₁.val) hwc (hwcl rfl)
        have haw := opWp_words64_two wa (toBits v4i32 a₁.val) hwa (hwal rfl)
        have hww' := opWp_words64_two ww (toBits v4i32 w₁.val) hww (hwwl rfl)
        refine words2ToDwords4_wp hcw.1 hcw.2 fun cd0 cd1 cd2 cd3 hcd0 hcd1 hcd2 hcd3 =>
          words2ToDwords4_wp haw.1 haw.2 fun ab0 ab1 ab2 ab3 hab0 hab1 hab2 hab3 =>
          words2ToDwords4_wp hww'.1 hww'.2 fun wk0 wk1 wk2 wk3 hwk0 hwk1 _ _ =>
          scalarSha256rnds2_wp hcd0 hcd1 hcd2 hcd3 hab0 hab1 hab2 hab3 hwk0 hwk1 fun r0 r1 r2 r3 hr0 hr1 hr2 hr3 =>
          dwords4ToWords2_wp hr0 hr1 hr2 hr3 fun w0 w1 hw0 hw1 =>
          unpackWords64ToLeaves_wp target hv v4i32 hsupp (fun i hi => by
            have hi128 : i < 128 := hi
            rw [Nat.zero_add, toBits_ofBits]
            by_cases hi64 : i < 64
            · simp [words64GetLsb, Nat.div_eq_of_lt hi64, Nat.mod_eq_of_lt hi64, hw0, hi64]
            · have hi2 : i - 64 < 64 := by omega
              simp [words64GetLsb, show i / 64 = 1 by omega, show i % 64 = i - 64 by omega, hw1,
                hi2, show 64 + (i - 64) = i by omega])
          fun fres hfres => packLeavesToLegal_wp target v4i32 hsupp fres _ hfres fun res hres =>
            hk _ _ (TRel.cons hres TRel.nil) hw
    · have hc_val := valsTup_legalArg target hG hc'
      have ha_val := valsTup_legalArg target hG ha
      have hw_val := valsTup_legalArg target hG hw'
      refine splitLegalToLeaves_wp target v4i32 hsupp (legalArg target c₂) c₁.val hc_val fun fc hfc =>
        splitLegalToLeaves_wp target v4i32 hsupp (legalArg target a₂) a₁.val ha_val fun fa hfa =>
        splitLegalToLeaves_wp target v4i32 hsupp (legalArg target w₂) w₁.val hw_val fun fw hfw =>
        packLeavesToWords64_wp target hv v4i32 hsupp hfc fun wc hwc _ hwcl =>
        packLeavesToWords64_wp target hv v4i32 hsupp hfa fun wa hwa _ hwal =>
        packLeavesToWords64_wp target hv v4i32 hsupp hfw fun ww hww _ hwwl => ?_
      have hcw := opWp_words64_two wc (toBits v4i32 c₁.val) hwc (hwcl rfl)
      have haw := opWp_words64_two wa (toBits v4i32 a₁.val) hwa (hwal rfl)
      have hww' := opWp_words64_two ww (toBits v4i32 w₁.val) hww (hwwl rfl)
      refine words2ToDwords4_wp hcw.1 hcw.2 fun cd0 cd1 cd2 cd3 hcd0 hcd1 hcd2 hcd3 =>
        words2ToDwords4_wp haw.1 haw.2 fun ab0 ab1 ab2 ab3 hab0 hab1 hab2 hab3 =>
        words2ToDwords4_wp hww'.1 hww'.2 fun wk0 wk1 wk2 wk3 hwk0 hwk1 _ _ =>
        scalarSha256rnds2_wp hcd0 hcd1 hcd2 hcd3 hab0 hab1 hab2 hab3 hwk0 hwk1 fun r0 r1 r2 r3 hr0 hr1 hr2 hr3 =>
        dwords4ToWords2_wp hr0 hr1 hr2 hr3 fun w0 w1 hw0 hw1 =>
        unpackWords64ToLeaves_wp target hv v4i32 hsupp (fun i hi => by
          have hi128 : i < 128 := hi
          rw [Nat.zero_add, toBits_ofBits]
          by_cases hi64 : i < 64
          · simp [words64GetLsb, Nat.div_eq_of_lt hi64, Nat.mod_eq_of_lt hi64, hw0, hi64]
          · have hi2 : i - 64 < 64 := by omega
            simp [words64GetLsb, show i / 64 = 1 by omega, show i % 64 = i - 64 by omega, hw1,
              hi2, show 64 + (i - 64) = i by omega])
        fun fres hfres => packLeavesToLegal_wp target v4i32 hsupp fres _ hfres fun res hres =>
          hk _ _ (TRel.cons hres TRel.nil) hw
  | sha256msg1 =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩
    rcases hargs with _ | @⟨_, _, b₁, b₂, _, _, hb, hargs⟩; cases hargs
    have hsupp := (Bool.and_eq_true _ _ |>.mp hsupp).1
    dsimp only [Op.wp, vals] at hw
    rw [OpCode.wp_sha256msg1] at hw
    rw [legalOp.eq_49]
    have ha_val := valsTup_legalArg target hG ha
    have hb_val := valsTup_legalArg target hG hb
    split
    · next hcond =>
      have hkp : target.keepsPacked v4i32 = true := (Bool.and_eq_true _ _ |>.mp hcond).1
      have hl_leg : target.isLegalTy v4i32 = true := hkp
      have hl_tys : target.legalTys v4i32 = [v4i32] := opWp_isLegalTy_legalTys hkp
      rw [wp_let, op2_wp_eq, OpCode.wp_sha256msg1]; dsimp only
      rw [opWp_cast_isLegal_in hl_leg hl_tys (legalArg target a₂) a₁.val ha_val,
        opWp_cast_isLegal_in hl_leg hl_tys (legalArg target b₂) b₁.val hb_val]
      exact hk _ _ (TRel.cons (opWp_cast_isLegal_out hl_leg hl_tys (Arg.var _)) TRel.nil) hw
    · refine splitLegalToLeaves_wp target v4i32 hsupp (legalArg target a₂) a₁.val ha_val fun fa hfa =>
        splitLegalToLeaves_wp target v4i32 hsupp (legalArg target b₂) b₁.val hb_val fun fb hfb =>
        packLeavesToWords64_wp target hv v4i32 hsupp hfa fun wa hwa _ hwal =>
        packLeavesToWords64_wp target hv v4i32 hsupp hfb fun wb hwb _ hwbl => ?_
      have haw := opWp_words64_two wa (toBits v4i32 a₁.val) hwa (hwal rfl)
      have hbw := opWp_words64_two wb (toBits v4i32 b₁.val) hwb (hwbl rfl)
      refine words2ToDwords4_wp haw.1 haw.2 fun a0 a1 a2 a3 ha0 ha1 ha2 ha3 =>
        words2ToDwords4_wp hbw.1 hbw.2 fun b0 b1 b2 b3 hb0 _ _ _ =>
        scalarSha256msg1_wp ha0 ha1 ha2 ha3 hb0 fun r0 r1 r2 r3 hr0 hr1 hr2 hr3 =>
        dwords4ToWords2_wp hr0 hr1 hr2 hr3 fun w0 w1 hw0 hw1 =>
        unpackWords64ToLeaves_wp target hv v4i32 hsupp (fun i hi => by
          have hi128 : i < 128 := hi
          rw [Nat.zero_add, toBits_ofBits]
          by_cases hi64 : i < 64
          · simp [words64GetLsb, Nat.div_eq_of_lt hi64, Nat.mod_eq_of_lt hi64, hw0, hi64]
          · have hi2 : i - 64 < 64 := by omega
            simp [words64GetLsb, show i / 64 = 1 by omega, show i % 64 = i - 64 by omega, hw1,
              hi2, show 64 + (i - 64) = i by omega])
        fun fres hfres => packLeavesToLegal_wp target v4i32 hsupp fres _ hfres fun res hres =>
          hk _ _ (TRel.cons hres TRel.nil) hw
  | sha256msg2 =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩
    rcases hargs with _ | @⟨_, _, b₁, b₂, _, _, hb, hargs⟩; cases hargs
    have hsupp := (Bool.and_eq_true _ _ |>.mp hsupp).1
    dsimp only [Op.wp, vals] at hw
    rw [OpCode.wp_sha256msg2] at hw
    rw [legalOp.eq_50]
    have ha_val := valsTup_legalArg target hG ha
    have hb_val := valsTup_legalArg target hG hb
    split
    · next hkps =>
      have hl_leg : target.isLegalTy v4i32 = true := hkps
      have hl_tys : target.legalTys v4i32 = [v4i32] := opWp_isLegalTy_legalTys hkps
      split
      · rw [wp_let, op2_wp_eq, OpCode.wp_sha256msg2]; dsimp only
        rw [opWp_cast_isLegal_in hl_leg hl_tys (legalArg target a₂) a₁.val ha_val,
          opWp_cast_isLegal_in hl_leg hl_tys (legalArg target b₂) b₁.val hb_val]
        exact hk _ _ (TRel.cons (opWp_cast_isLegal_out hl_leg hl_tys (Arg.var _)) TRel.nil) hw
      · refine splitLegalToLeaves_wp target v4i32 hsupp (legalArg target a₂) a₁.val ha_val fun fa hfa =>
          splitLegalToLeaves_wp target v4i32 hsupp (legalArg target b₂) b₁.val hb_val fun fb hfb =>
          packLeavesToWords64_wp target hv v4i32 hsupp hfa fun wa hwa _ hwal =>
          packLeavesToWords64_wp target hv v4i32 hsupp hfb fun wb hwb _ hwbl => ?_
        have haw := opWp_words64_two wa (toBits v4i32 a₁.val) hwa (hwal rfl)
        have hbw := opWp_words64_two wb (toBits v4i32 b₁.val) hwb (hwbl rfl)
        refine words2ToDwords4_wp haw.1 haw.2 fun s0 s1 s2 s3 hs0 hs1 hs2 hs3 =>
          words2ToDwords4_wp hbw.1 hbw.2 fun w0 w1 w2 w3 _ _ hw2 hw3 =>
          scalarSha256msg2_wp hs0 hs1 hs2 hs3 hw2 hw3 fun r0 r1 r2 r3 hr0 hr1 hr2 hr3 =>
          dwords4ToWords2_wp hr0 hr1 hr2 hr3 fun wr0 wr1 hwr0 hwr1 =>
          unpackWords64ToLeaves_wp target hv v4i32 hsupp (fun i hi => by
            have hi128 : i < 128 := hi
            rw [Nat.zero_add, toBits_ofBits]
            by_cases hi64 : i < 64
            · simp [words64GetLsb, Nat.div_eq_of_lt hi64, Nat.mod_eq_of_lt hi64, hwr0, hi64]
            · have hi2 : i - 64 < 64 := by omega
              simp [words64GetLsb, show i / 64 = 1 by omega, show i % 64 = i - 64 by omega, hwr1,
                hi2, show 64 + (i - 64) = i by omega])
          fun fres hfres => packLeavesToLegal_wp target v4i32 hsupp fres _ hfres fun res hres =>
            hk _ _ (TRel.cons hres TRel.nil) hw
    · refine splitLegalToLeaves_wp target v4i32 hsupp (legalArg target a₂) a₁.val ha_val fun fa hfa =>
        splitLegalToLeaves_wp target v4i32 hsupp (legalArg target b₂) b₁.val hb_val fun fb hfb =>
        packLeavesToWords64_wp target hv v4i32 hsupp hfa fun wa hwa _ hwal =>
        packLeavesToWords64_wp target hv v4i32 hsupp hfb fun wb hwb _ hwbl => ?_
      have haw := opWp_words64_two wa (toBits v4i32 a₁.val) hwa (hwal rfl)
      have hbw := opWp_words64_two wb (toBits v4i32 b₁.val) hwb (hwbl rfl)
      refine words2ToDwords4_wp haw.1 haw.2 fun s0 s1 s2 s3 hs0 hs1 hs2 hs3 =>
        words2ToDwords4_wp hbw.1 hbw.2 fun w0 w1 w2 w3 _ _ hw2 hw3 =>
        scalarSha256msg2_wp hs0 hs1 hs2 hs3 hw2 hw3 fun r0 r1 r2 r3 hr0 hr1 hr2 hr3 =>
        dwords4ToWords2_wp hr0 hr1 hr2 hr3 fun wr0 wr1 hwr0 hwr1 =>
        unpackWords64ToLeaves_wp target hv v4i32 hsupp (fun i hi => by
          have hi128 : i < 128 := hi
          rw [Nat.zero_add, toBits_ofBits]
          by_cases hi64 : i < 64
          · simp [words64GetLsb, Nat.div_eq_of_lt hi64, Nat.mod_eq_of_lt hi64, hwr0, hi64]
          · have hi2 : i - 64 < 64 := by omega
            simp [words64GetLsb, show i / 64 = 1 by omega, show i % 64 = i - 64 by omega, hwr1,
              hi2, show 64 + (i - 64) = i by omega])
        fun fres hfres => packLeavesToLegal_wp target v4i32 hsupp fres _ hfres fun res hres =>
          hk _ _ (TRel.cons hres TRel.nil) hw
  | fadd t =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩
    rcases hargs with _ | @⟨_, _, b₁, b₂, _, _, hb, hargs⟩; cases hargs
    rw [legalOp.eq_51]
    exact legalOp_floatBin_wp target hG OpCode.fadd Float.Model.UnpackedFloat.add
      (fun u x y p => OpCode.wp_fadd u (x, y, ()) p) (fun _ => rfl) hsupp ha hb hw hk
  | fsub t =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩
    rcases hargs with _ | @⟨_, _, b₁, b₂, _, _, hb, hargs⟩; cases hargs
    rw [legalOp.eq_52]
    exact legalOp_floatBin_wp target hG OpCode.fsub Float.Model.UnpackedFloat.sub
      (fun u x y p => OpCode.wp_fsub u (x, y, ()) p) (fun _ => rfl) hsupp ha hb hw hk
  | fmul t =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩
    rcases hargs with _ | @⟨_, _, b₁, b₂, _, _, hb, hargs⟩; cases hargs
    rw [legalOp.eq_53]
    exact legalOp_floatBin_wp target hG OpCode.fmul Float.Model.UnpackedFloat.mul
      (fun u x y p => OpCode.wp_fmul u (x, y, ()) p) (fun _ => rfl) hsupp ha hb hw hk
  | fdiv t =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩
    rcases hargs with _ | @⟨_, _, b₁, b₂, _, _, hb, hargs⟩; cases hargs
    rw [legalOp.eq_54]
    exact legalOp_floatBin_wp target hG OpCode.fdiv Float.Model.UnpackedFloat.div
      (fun u x y p => OpCode.wp_fdiv u (x, y, ()) p) (fun _ => rfl) hsupp ha hb hw hk
  | ffma t =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩
    rcases hargs with _ | @⟨_, _, b₁, b₂, _, _, hb, hargs⟩
    rcases hargs with _ | @⟨_, _, c₁, c₂, _, _, hc', hargs⟩; cases hargs
    dsimp only [Op.wp, vals] at hw
    rw [OpCode.wp_ffma] at hw
    rw [legalOp.eq_55]
    cases hft : t.isFloatTree
    · simp [hft] at hw
    · simp only [hft, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hw ⊢
      refine legalTernaryTree_wp target OpCode.ffma (fun u => target.vecFloatOpSupported (OpCode.ffma u) u)
        (fun _ _ _ _ => Expr.hlt) (fun _ _ _ _ _ => Expr.hlt)
        (fun fmt x y z cont => Expr.let_ (op3 (OpCode.ffma (Ty.float fmt)) x y z) fun (r, _) => cont (Arg.var r))
        (onB := fun _ _ _ _ => False) (onBi := fun _ _ _ _ _ => False)
        (onF := fun fmt a b c q =>
          floatResultWp fmt (Float.Model.UnpackedFloat.fma fmt.format
            (unpackFloat fmt a) (unpackFloat fmt b) (unpackFloat fmt c)) q)
        (by intros; contradiction)
        (by intros; contradiction)
        ?_ ?_ (by intros; contradiction) (by intros; contradiction)
        (fun fmt _ _ _ _ _ hpq h => opWp_floatResultWp_mono fmt _ hpq h)
        t hsupp (legalArg target a₂) (legalArg target b₂) (legalArg target c₂) a₁.val b₁.val c₁.val
        (valsTup_legalArg target hG ha) (valsTup_legalArg target hG hb) (valsTup_legalArg target hG hc')
        (fun res => k (res, ())) m ?_
      · intro fmt _ a' b' c' a b c cont m' ha' hb' hc'' hpre
        rw [wp_let, op3_wp_eq, OpCode.wp_ffma]; simp only [Ty.isFloatTree, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        change floatResultWp fmt (Float.Model.UnpackedFloat.fma fmt.format
          (unpackFloat fmt a'.val) (unpackFloat fmt b'.val) (unpackFloat fmt c'.val)) _
        rw [ha', hb', hc'']
        exact opWp_floatResultWp_mono fmt _ (fun res hres => hres (Arg.var res) rfl) hpre
      · intro u _ _ _ x y z p htr
        have hu := opWp_float3_isFloatTree_of_treeRel3 Float.Model.UnpackedFloat.fma u x y z p htr
        rw [OpCode.wp_ffma]; simp [hu.1, hu.2]
      · exact opWp_treeRel3_float3 Float.Model.UnpackedFloat.fma t hft a₁.val b₁.val c₁.val _
          (opWp_liftFloatRel3_mono Float.Model.UnpackedFloat.fma t a₁.val b₁.val c₁.val
            (fun r hr => fun fres hfres => hk _ _ (TRel.cons hfres TRel.nil) hr) hw)
  | fsqrt t =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩; cases hargs
    dsimp only [Op.wp, vals] at hw
    rw [OpCode.wp_fsqrt] at hw
    rw [legalOp.eq_56]
    cases hft : t.isFloatTree
    · simp [hft] at hw
    · simp only [hft, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hw ⊢
      refine legalUnaryTree_wp target OpCode.fsqrt (fun u => target.vecFloatOpSupported (OpCode.fsqrt u) u)
        (fun _ _ => Expr.hlt) (fun _ _ _ => Expr.hlt)
        (fun fmt x cont => Expr.let_ (op1 (OpCode.fsqrt (Ty.float fmt)) x) fun (r, _) => cont (Arg.var r))
        (onB := fun _ _ => False) (onBi := fun _ _ _ => False)
        (onF := fun fmt a q =>
          floatResultWp fmt (Float.Model.UnpackedFloat.sqrt fmt.format (unpackFloat fmt a)) q)
        (by intros; contradiction)
        (by intros; contradiction)
        ?_ ?_ (by intros; contradiction) (by intros; contradiction)
        (fun fmt _ _ _ hpq h => opWp_floatResultWp_mono fmt _ hpq h)
        t hsupp (legalArg target a₂) a₁.val (valsTup_legalArg target hG ha) (fun res => k (res, ())) m ?_
      · intro fmt _ a' a cont m' ha' hpre
        rw [wp_let, op1_wp_eq, OpCode.wp_fsqrt]; simp only [Ty.isFloatTree, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        change floatResultWp fmt (Float.Model.UnpackedFloat.sqrt fmt.format (unpackFloat fmt a'.val)) _
        rw [ha']
        exact opWp_floatResultWp_mono fmt _ (fun res hres => hres (Arg.var res) rfl) hpre
      · intro u _ _ _ x p htr
        have hu := opWp_float1_isFloatTree_of_treeRel1 Float.Model.UnpackedFloat.sqrt u x p htr
        rw [OpCode.wp_fsqrt]; simp [hu.1, hu.2]
      · exact opWp_treeRel1_float1 Float.Model.UnpackedFloat.sqrt t hft a₁.val _
          (opWp_liftFloatRel1_mono Float.Model.UnpackedFloat.sqrt t a₁.val
            (fun r hr => fun fres hfres => hk _ _ (TRel.cons hfres TRel.nil) hr) hw)
  | fneg t =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩; cases hargs
    dsimp only [Op.wp, vals] at hw
    rw [OpCode.wp_fneg] at hw
    rw [legalOp.eq_57]
    cases hft : t.isFloatTree
    · simp [hft] at hw
    · simp only [hft, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hw ⊢
      refine legalUnaryTree_wp target OpCode.fneg (fun u => target.vecFloatOpSupported (OpCode.fneg u) u)
        (fun _ _ => Expr.hlt) (fun _ _ _ => Expr.hlt)
        (fun fmt x cont => Expr.let_ (op1 (OpCode.fneg (Ty.float fmt)) x) fun (r, _) => cont (Arg.var r))
        (onB := fun _ _ => False) (onBi := fun _ _ _ => False)
        (onF := fun fmt a q => q (a ^^^ 1#fmt.width <<< (fmt.width - 1)))
        (by intros; contradiction)
        (by intros; contradiction)
        (fun fmt _ x' x cont m' hx' hpre => by
          rw [wp_let, op1_wp_eq, OpCode.wp_fneg, hx']; exact hpre _ rfl)
        (fun u _ _ _ x p htr => by
          have hu := opWp_lift1_float_of_treeRel1 (fun {n} x => x ^^^ 1#n <<< (n - 1)) u x p htr
          rw [OpCode.wp_fneg]; simp [hu.1, hu.2])
        (by intros; contradiction) (by intros; contradiction)
        (fun _ _ _ _ hpq h => hpq _ h)
        t hsupp (legalArg target a₂) a₁.val (valsTup_legalArg target hG ha) (fun res => k (res, ())) m
        (opWp_treeRel1_lift1_float (fun {n} x => x ^^^ 1#n <<< (n - 1)) t hft _ _
          fun fres hfres => hk _ _ (TRel.cons hfres TRel.nil) hw)
  | fabs t =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩; cases hargs
    dsimp only [Op.wp, vals] at hw
    rw [OpCode.wp_fabs] at hw
    rw [legalOp.eq_58]
    cases hft : t.isFloatTree
    · simp [hft] at hw
    · simp only [hft, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hw ⊢
      refine legalUnaryTree_wp target OpCode.fabs (fun u => target.vecFloatOpSupported (OpCode.fabs u) u)
        (fun _ _ => Expr.hlt) (fun _ _ _ => Expr.hlt)
        (fun fmt x cont => Expr.let_ (op1 (OpCode.fabs (Ty.float fmt)) x) fun (r, _) => cont (Arg.var r))
        (onB := fun _ _ => False) (onBi := fun _ _ _ => False)
        (onF := fun fmt a q => q (a &&& ~~~(1#fmt.width <<< (fmt.width - 1))))
        (by intros; contradiction)
        (by intros; contradiction)
        (fun fmt _ x' x cont m' hx' hpre => by
          rw [wp_let, op1_wp_eq, OpCode.wp_fabs, hx']; exact hpre _ rfl)
        (fun u _ _ _ x p htr => by
          have hu := opWp_lift1_float_of_treeRel1 (fun {n} x => x &&& ~~~(1#n <<< (n - 1))) u x p htr
          rw [OpCode.wp_fabs]; simp [hu.1, hu.2])
        (by intros; contradiction) (by intros; contradiction)
        (fun _ _ _ _ hpq h => hpq _ h)
        t hsupp (legalArg target a₂) a₁.val (valsTup_legalArg target hG ha) (fun res => k (res, ())) m
        (opWp_treeRel1_lift1_float (fun {n} x => x &&& ~~~(1#n <<< (n - 1))) t hft _ _
          fun fres hfres => hk _ _ (TRel.cons hfres TRel.nil) hw)
  | fcmp o t m_ty hm =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩
    rcases hargs with _ | @⟨_, _, b₁, b₂, _, _, hb, hargs⟩; cases hargs
    cases hm
    dsimp only [Op.wp, vals] at hw
    rw [OpCode.wp_fcmp] at hw
    rw [legalOp.eq_59]
    cases hft : t.isFloatTree
    · simp [hft] at hw
    · simp only [hft, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hw ⊢
      exact legalFCmpTree_wp target o t hsupp hft (legalArg target a₂) (legalArg target b₂)
        a₁.val b₁.val (valsTup_legalArg target hG ha) (valsTup_legalArg target hG hb)
        (fun res => k (res, ())) m
        (fun res hres => hk (liftFCmp o t a₁.val b₁.val, ()) (res, ()) (TRel.cons hres TRel.nil) hw)
  | fptoui fmt n =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩; cases hargs
    dsimp only [Op.wp, vals] at hw
    rw [OpCode.wp_fptoui] at hw
    rw [legalOp.eq_60]
    have ha_val := valsTup_legalArg target hG ha
    split
    · next a' hpa =>
      dsimp only [Tup, LVar, LegalTarget.legalTys] at k ha_val ⊢
      rw [hpa] at ha_val
      have haeq : a'.val = a₁.val := (Prod.mk.inj ha_val).1
      dsimp only [LegalTarget.supportsOpCode] at hsupp
      simp only [Bool.and_eq_true] at hsupp
      have hs := opWp_widen_spec hv hsupp.2
      cases htr : truncToInt (unpackFloat fmt a₁.val) with
      | none => simp [htr] at hw
      | some z =>
        simp only [htr] at hw
        rcases hw with ⟨hz0, hzn, hwP⟩
        have hzn' : z < ((2 ^ n : Nat) : Int) := by
          push_cast; exact hzn
        have hp : 2 ^ n ≤ 2 ^ target.widenWidth n := Nat.pow_le_pow_right (by omega) hs.2.1
        have hzw : z < 2 ^ target.widenWidth n := by
          rw [show (2 ^ target.widenWidth n : Int) = ((2 ^ target.widenWidth n : Nat) : Int) from (Int.natCast_pow 2 _).symm]
          omega
        by_cases hn0 : n = 0
        · subst hn0; simp only [beq_self_eq_true, ↓reduceIte]
          rw [wp_let, op1_wp_eq, OpCode.wp_fptoui, haeq, htr]
          refine ⟨hz0, hzw, hk _ _ (TRel.cons ?_ TRel.nil) hwP⟩
          change (0#(target.widenWidth 0), ()) = (BitVec.setWidth _ _, ())
          have h0 : BitVec.ofInt 0 z = 0#0 := Subsingleton.elim _ _
          rw [h0]; congr 1
        · simp only [beq_iff_eq, hn0, ↓reduceIte]
          rw [wp_let, op1_wp_eq, OpCode.wp_fptoui, haeq, htr]
          refine ⟨hz0, hzw, hk _ _ (TRel.cons ?_ TRel.nil) hwP⟩
          change (BitVec.ofInt (target.widenWidth n) z, ()) = (BitVec.setWidth (target.widenWidth n) (BitVec.ofInt n z), ())
          congr 1; exact opWp_fptoui_widened (Nat.pos_of_ne_zero hn0) hs.2.1 hz0 hzn'
  | fptosi fmt n =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩; cases hargs
    dsimp only [Op.wp, vals] at hw
    rw [OpCode.wp_fptosi] at hw
    rcases hw with ⟨hn0, hw⟩
    rw [legalOp.eq_61]
    have ha_val := valsTup_legalArg target hG ha
    split
    · next a' hpa =>
      dsimp only [Tup, LVar, LegalTarget.legalTys] at k ha_val ⊢
      rw [hpa] at ha_val
      have haeq : a'.val = a₁.val := (Prod.mk.inj ha_val).1
      dsimp only [LegalTarget.supportsOpCode] at hsupp
      simp only [Bool.and_eq_true] at hsupp
      have hs := opWp_widen_spec hv hsupp.2
      simp only [beq_iff_eq, hn0, ↓reduceIte]
      cases htr : truncToInt (unpackFloat fmt a₁.val) with
      | none => simp [htr] at hw
      | some z =>
        simp only [htr] at hw
        rcases hw with ⟨hzlo, hzhi, hwP⟩
        have hn_pos : 0 < n := Nat.pos_of_ne_zero hn0
        have hp : 2 ^ (n - 1) ≤ 2 ^ (target.widenWidth n - 1) :=
          Nat.pow_le_pow_right (by omega) (by omega)
        have hzlo' : -(2 ^ (target.widenWidth n - 1) : Int) ≤ z := by
          rw [show (2 ^ (target.widenWidth n - 1) : Int) = ((2 ^ (target.widenWidth n - 1) : Nat) : Int) from (Int.natCast_pow 2 _).symm]
          rw [show (2 ^ (n - 1) : Int) = ((2 ^ (n - 1) : Nat) : Int) from (Int.natCast_pow 2 _).symm] at hzlo
          omega
        have hzhi' : z < 2 ^ (target.widenWidth n - 1) := by
          rw [show (2 ^ (target.widenWidth n - 1) : Int) = ((2 ^ (target.widenWidth n - 1) : Nat) : Int) from (Int.natCast_pow 2 _).symm]
          rw [show (2 ^ (n - 1) : Int) = ((2 ^ (n - 1) : Nat) : Int) from (Int.natCast_pow 2 _).symm] at hzhi
          omega
        split
        · next hnw =>
          rw [wp_let, op1_wp_eq, OpCode.wp_fptosi, haeq, htr]
          refine ⟨Nat.ne_of_gt hs.2.2.1, hzlo', hzhi', hk _ _ (TRel.cons ?_ TRel.nil) hwP⟩
          change (BitVec.ofInt (target.widenWidth n) z, ()) = (BitVec.setWidth (target.widenWidth n) (BitVec.ofInt n z), ())
          congr 1
          apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_setWidth, ← hnw]
          exact (Nat.mod_eq_of_lt (BitVec.ofInt n z).isLt).symm
        · next _ =>
          rw [wp_let, op1_wp_eq, OpCode.wp_fptosi, haeq, htr]
          refine ⟨Nat.ne_of_gt hs.2.2.1, hzlo', hzhi', ?_⟩
          refine emitMaskToN_wp hs.2.1 rfl fun rm hrm => ?_
          simp only [Arg.val_var] at hrm
          refine hk _ _ (TRel.cons ?_ TRel.nil) hwP
          change (rm.val, ()) = (BitVec.setWidth (target.widenWidth n) (BitVec.ofInt n z), ())
          congr 1; rw [hrm, opWp_fptosi_widened hs.2.1 z]
  | uitofp n fmt =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩; cases hargs
    dsimp only [Op.wp, vals] at hw
    rw [OpCode.wp_uitofp] at hw
    rw [legalOp.eq_62]
    have ha_val := valsTup_legalArg target hG ha
    split
    · next a' hpa =>
      dsimp only [Tup, LVar, LegalTarget.legalTys] at k ha_val ⊢
      rw [hpa] at ha_val
      have haeq : a'.val = BitVec.setWidth (target.widenWidth n) a₁.val := (Prod.mk.inj ha_val).1
      dsimp only [LegalTarget.supportsOpCode] at hsupp
      simp only [Bool.and_eq_true] at hsupp
      have hs := opWp_widen_spec hv hsupp.2
      by_cases hn0 : n = 0
      · subst hn0; simp only [beq_self_eq_true, ↓reduceIte]
        rw [wp_let, op1_wp_eq, OpCode.wp_uitofp]; dsimp only
        have ha0 : a₁.val = 0#0 := Subsingleton.elim _ _
        have h0 : (0#(target.widenWidth 0)).toNat = (0#0).toNat := by simp
        rw [ha0, ← h0] at hw
        exact hk _ _ (TRel.cons (by rfl) TRel.nil) hw
      · simp only [beq_iff_eq, hn0, ↓reduceIte]
        rw [wp_let, op1_wp_eq, OpCode.wp_uitofp]; dsimp only
        have hp : 2 ^ n ≤ 2 ^ target.widenWidth n := Nat.pow_le_pow_right (by omega) hs.2.1
        have htn : a'.val.toNat = a₁.val.toNat := by
          rw [haeq, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le a₁.val.isLt hp)]
        rw [htn]
        exact hk _ _ (TRel.cons (by rfl) TRel.nil) hw
  | sitofp n fmt =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩; cases hargs
    dsimp only [Op.wp, vals] at hw
    rw [OpCode.wp_sitofp] at hw
    rw [legalOp.eq_63]
    have ha_val := valsTup_legalArg target hG ha
    split
    · next a' hpa =>
      dsimp only [Tup, LVar, LegalTarget.legalTys] at k ha_val ⊢
      rw [hpa] at ha_val
      have haeq : a'.val = BitVec.setWidth (target.widenWidth n) a₁.val := (Prod.mk.inj ha_val).1
      dsimp only [LegalTarget.supportsOpCode] at hsupp
      simp only [Bool.and_eq_true] at hsupp
      have hs := opWp_widen_spec hv hsupp.2
      by_cases hn0 : n = 0
      · subst hn0; simp only [beq_self_eq_true, ↓reduceIte]
        rw [wp_let, op1_wp_eq, OpCode.wp_sitofp]; dsimp only
        have ha0 : a₁.val = 0#0 := Subsingleton.elim _ _
        have hi0 : (0#(target.widenWidth 0)).toInt = (0#0).toInt := by
          simp [BitVec.toInt_zero]
        rw [ha0, ← hi0] at hw
        exact hk _ _ (TRel.cons (by rfl) TRel.nil) hw
      · simp only [beq_iff_eq, hn0, ↓reduceIte]
        refine emitSextToW_wp (Nat.pos_of_ne_zero hn0) hs.2.1 haeq fun sa hsa => ?_
        rw [wp_let, op1_wp_eq, OpCode.wp_sitofp]; dsimp only
        rw [hsa, opWp_signExtend_toInt hs.2.1]
        exact hk _ _ (TRel.cons (by rfl) TRel.nil) hw
  | fcvt fmt g =>
    rcases hargs with _ | @⟨_, _, a₁, a₂, _, _, ha, hargs⟩; cases hargs
    dsimp only [Op.wp, vals] at hw
    rw [OpCode.wp_fcvt] at hw
    rw [legalOp.eq_64]
    have ha_val := valsTup_legalArg target hG ha
    rcases hpa : legalArg target a₂ with ⟨a', ⟨⟩⟩; rw [hpa] at ha_val
    have haeq : a'.val = a₁.val := (Prod.mk.inj ha_val).1
    rw [wp_let, op1_wp_eq, OpCode.wp_fcvt, haeq]
    have hmono : ∀ (src dst : Fmt) (b : BitVec src.width) {p q : BitVec dst.width → Prop},
        (∀ r, p r → q r) → convertFloat src dst b p → convertFloat src dst b q := by
      intro src dst b p q hpq hcf
      unfold convertFloat at hcf ⊢
      cases huf : unpackFloat src b with
      | notANumber => simp only [huf] at hcf; exact fun r hr => hpq r (hcf r hr)
      | _ => simp only [huf] at hcf; exact hpq _ hcf
    exact hmono fmt g a₁.val (fun r hr => hk _ _ (TRel.cons (by rfl) TRel.nil) hr) hw

/-! ### Chunk 4.4: Memory widening/byte-chunking (`emitLoadBits`, `emitStoreBits`, `legalLoad`, `legalStore`) and `Func.legal_wp` -/

private theorem memWp_int_toBytes_add :
    ∀ (n1 n2 : Nat) (v : Int),
      Int.toBytes (n1 + n2) v = Int.toBytes n1 v ++ Int.toBytes n2 (v / (256 : Int) ^ n1)
  | 0, n2, v => by simp [Int.toBytes]
  | n1 + 1, n2, v => by
    rw [Nat.succ_add, Int.toBytes, Int.toBytes, List.cons_append]
    congr 1
    rw [memWp_int_toBytes_add n1 n2 (v / 256)]
    congr 2
    rw [Int.pow_succ, Int.mul_comm ((256 : Int) ^ n1) 256]
    exact Int.ediv_ediv_of_nonneg (by decide)

private theorem memWp_int_toBytes_bitVec_toNat (n w : Nat) (_hn : 8 * n ≤ w) (x : BitVec w) :
    Int.toBytes n (BitVec.setWidth (8 * n) x).toInt = Int.toBytes n (x.toNat : Int) := by
  rw [← Int.toBytes_emod n (BitVec.setWidth (8 * n) x).toInt,
      ← Int.toBytes_emod n (x.toNat : Int)]
  congr 1
  dsimp only [Int.take]
  have hp : (2 : Int) ^ (8 * n) = ((2 ^ (8 * n) : Nat) : Int) := (Int.natCast_pow 2 (8 * n)).symm
  have h1 : (BitVec.setWidth (8 * n) x).toInt % (2 : Int) ^ (8 * n) =
      ((BitVec.setWidth (8 * n) x).toNat : Int) := by
    have hnn : 0 ≤ (BitVec.setWidth (8 * n) x).toInt % (2 : Int) ^ (8 * n) :=
      Int.emod_nonneg _ (Int.ne_of_gt (Int.pow_pos (by decide)))
    rw [← Int.toNat_of_nonneg hnn]
    congr 1
    have hbv : (BitVec.ofInt (8 * n) (BitVec.setWidth (8 * n) x).toInt).toNat =
        (BitVec.setWidth (8 * n) x).toNat := by rw [BitVec.ofInt_toInt]
    rw [BitVec.toNat_ofInt, ← hp] at hbv
    exact hbv
  rw [h1, BitVec.toNat_setWidth, hp, ← Int.natCast_emod]

private theorem memWp_int_toBytes_shift {c w off : Nat} (hle : 8 * (off + c) ≤ w) (x : BitVec w) :
    Int.toBytes c ((x >>> (8 * off)).setWidth (8 * c)).toInt =
      Int.toBytes c ((x.toNat : Int) / (256 : Int) ^ off) := by
  rw [memWp_int_toBytes_bitVec_toNat c w (by omega) (x >>> (8 * off))]
  congr 1
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have hp : (256 : Int) ^ off = ((2 ^ (8 * off) : Nat) : Int) := by
    rw [show (256 : Int) = ((2 ^ 8 : Nat) : Int) by decide, ← Int.natCast_pow, ← Nat.pow_mul]
  rw [hp, ← Int.natCast_ediv]

private theorem memWp_storeBytes_append (m : Mem 64) (a : BitVec 64) (bs1 bs2 : List UInt8)
    (hlen : bs1.length + bs2.length ≤ 2 ^ 64) :
    m.storeBytes a (bs1 ++ bs2) =
      (m.storeBytes a bs1).storeBytes (a + BitVec.ofNat 64 bs1.length) bs2 := by
  simp only [Mem.storeBytes, List.At_append bs1 bs2 a hlen]
  apply Std.ExtHashMap.ext_getElem?
  intro k
  simp only [Std.ExtHashMap.union_eq, Std.ExtHashMap.getElem?_union]
  cases (bs2.At (a + BitVec.ofNat 64 bs1.length))[k]? <;>
    cases (bs1.At a)[k]? <;> cases m[k]? <;> rfl

private theorem memWp_storeBytes_nil (m : Mem 64) (a : BitVec 64) : m.storeBytes a [] = m := by
  simp only [Mem.storeBytes]
  apply Std.ExtHashMap.ext_getElem?
  intro k
  have hnone : (([] : List UInt8).At a)[k]? = none := by
    rw [Std.ExtHashMap.getElem?_eq_none]
    simp [mem_At_iff]
  simp only [Std.ExtHashMap.union_eq, Std.ExtHashMap.getElem?_union, hnone]
  cases m[k]? <;> rfl

private theorem memWp_list_range_add (n1 n2 : Nat) :
    List.range (n1 + n2) = List.range n1 ++ (List.range n2).map (n1 + ·) := by
  induction n2 with
  | zero => simp
  | succ n2 ih =>
    rw [Nat.add_succ, List.range_succ, ih, List.range_succ, List.map_append, List.map_singleton,
      List.append_assoc]

private theorem memWp_list_mapM_id_append {α : Type} :
    ∀ (xs ys : List (Option α)) {zs : List α},
      (xs ++ ys).mapM id = some zs ↔
        ∃ x' y', xs.mapM id = some x' ∧ ys.mapM id = some y' ∧ zs = x' ++ y'
  | [], ys, zs => by
    simp only [List.nil_append, List.mapM_nil, Option.pure_def, Option.some.injEq]
    constructor
    · intro h; exact ⟨[], zs, rfl, h, rfl⟩
    · rintro ⟨_, y', rfl, hy, rfl⟩; exact hy
  | x :: xs, ys, zs => by
    simp only [List.cons_append, List.mapM_cons, id_eq, Option.pure_def, Option.bind_eq_bind,
      Option.bind_eq_some_iff, Option.some.injEq]
    constructor
    · rintro ⟨a, ha, rest, hrest, rfl⟩
      obtain ⟨x', y', hx, hy, rfl⟩ := (memWp_list_mapM_id_append xs ys).mp hrest
      exact ⟨a :: x', y', ⟨a, ha, x', hx, rfl⟩, hy, rfl⟩
    · rintro ⟨_, y', ⟨a, ha, x', hx, rfl⟩, hy, rfl⟩
      have hrest : (xs ++ ys).mapM id = some (x' ++ y') :=
        (memWp_list_mapM_id_append xs ys).mpr ⟨x', y', hx, hy, rfl⟩
      exact ⟨a, ha, x' ++ y', hrest, rfl⟩

private theorem memWp_loadBytes_length (m : Mem 64) (a : BitVec 64) :
    ∀ (n : Nat) {bs : List UInt8}, m.loadBytes a n = some bs → bs.length = n := by
  intro n bs h
  unfold Mem.loadBytes at h
  induction n generalizing bs with
  | zero =>
    simp only [List.range_zero, List.map_nil, List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h; rfl
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.map_singleton] at h
    obtain ⟨x', y', hx, hy, rfl⟩ := (memWp_list_mapM_id_append _ _).mp h
    simp only [List.mapM_cons, List.mapM_nil, id_eq, Option.pure_def, Option.bind_eq_bind,
      Option.bind_eq_some_iff, Option.some.injEq] at hy
    rcases hy with ⟨b, _, _, hnil, rfl⟩
    cases hnil
    simp [ih hx]

private theorem memWp_loadBytes_add (m : Mem 64) (a : BitVec 64) (n1 n2 : Nat) {bs : List UInt8} :
    m.loadBytes a (n1 + n2) = some bs ↔
      ∃ bs1 bs2, m.loadBytes a n1 = some bs1 ∧
        m.loadBytes (a + BitVec.ofNat 64 n1) n2 = some bs2 ∧ bs = bs1 ++ bs2 := by
  unfold Mem.loadBytes
  rw [memWp_list_range_add, List.map_append, List.map_map, memWp_list_mapM_id_append]
  have hmap :
      ((List.range n2).map ((fun i => m.get? (a + BitVec.ofNat 64 i)) ∘ (n1 + ·))) =
      ((List.range n2).map fun j => m.get? ((a + BitVec.ofNat 64 n1) + BitVec.ofNat 64 j)) := by
    apply List.map_congr_left
    intro j _
    simp only [Function.comp_apply, BitVec.ofNat_add, BitVec.add_assoc]
  rw [hmap]

private theorem memWp_loadBytes_one (m : Mem 64) (a : BitVec 64) {bs : List UInt8} :
    m.loadBytes a 1 = some bs ↔ ∃ b, m.get? a = some b ∧ bs = [b] := by
  unfold Mem.loadBytes
  simp only [List.range_one, List.map_cons, List.map_nil, List.mapM_cons, List.mapM_nil, id_eq,
    Option.pure_def, Option.bind_eq_bind, BitVec.add_zero, Std.ExtHashMap.get?_eq_getElem?]
  cases m[a]? <;> simp [eq_comm]

private theorem memWp_loadBytes_isSome_storeBytes {m : Mem 64} {a b : BitVec 64} {n : Nat}
    (hbs : List UInt8) (hm : ∃ ys, m.loadBytes b n = some ys) :
    ∃ ys', (m.storeBytes a hbs).loadBytes b n = some ys' := by
  rcases hm with ⟨ys, hys⟩
  induction n generalizing b ys with
  | zero => exact ⟨[], by simp [Mem.loadBytes]⟩
  | succ n ih =>
    rw [memWp_loadBytes_add] at hys
    rcases hys with ⟨ys1, ys2, h1, h2, _⟩
    obtain ⟨ys1', h1'⟩ := ih ys1 h1
    obtain ⟨y, hy, _⟩ := memWp_loadBytes_one m (b + BitVec.ofNat 64 n) |>.mp h2
    have hget : ((m.storeBytes a hbs).get? (b + BitVec.ofNat 64 n)).isSome = true := by
      simp only [Mem.storeBytes, Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.union_eq,
        Std.ExtHashMap.getElem?_union]
      rw [Std.ExtHashMap.get?_eq_getElem?] at hy
      rw [hy]
      cases (hbs.At a)[b + BitVec.ofNat 64 n]? <;> simp
    rcases Option.isSome_iff_exists.1 hget with ⟨y', hy'⟩
    have h2' : (m.storeBytes a hbs).loadBytes (b + BitVec.ofNat 64 n) 1 = some [y'] :=
      (memWp_loadBytes_one _ _).mpr ⟨y', hy', rfl⟩
    exact ⟨ys1' ++ [y'], (memWp_loadBytes_add _ _ n 1).mpr ⟨ys1', [y'], h1', h2', rfl⟩⟩

private theorem memWp_getLsbD_ofNat_pow_add (a k b i : Nat) (ha : a < 2 ^ k) :
    Nat.testBit (a + 2 ^ k * b) i =
      if i < k then a.testBit i else b.testBit (i - k) := by
  simp only [Nat.testBit, Nat.shiftRight_eq_div_pow]
  by_cases hik : i < k
  · simp only [hik, ↓reduceIte]
    have hpow : 2 ^ k = 2 ^ i * 2 ^ (k - i) := by rw [← Nat.pow_add, Nat.add_sub_cancel' (Nat.le_of_lt hik)]
    have hd : (a + 2 ^ k * b) / 2 ^ i = a / 2 ^ i + 2 ^ (k - i) * b := by
      rw [hpow, Nat.mul_assoc, Nat.add_mul_div_left _ _ (Nat.two_pow_pos i)]
    have h2 : 2 ^ (k - i) = 2 * 2 ^ (k - i - 1) := by
      conv => lhs; rw [show k - i = (k - i - 1) + 1 by omega, Nat.pow_succ, Nat.mul_comm _ 2]
    rw [hd, h2, Nat.mul_assoc, Nat.and_comm 1 _, Nat.and_one_is_mod, Nat.add_mul_mod_self_left]
    conv => rhs; rw [Nat.and_comm 1 _, Nat.and_one_is_mod]
  · simp only [hik, ↓reduceIte]
    have hge : k ≤ i := Nat.le_of_not_lt hik
    have hpow : 2 ^ i = 2 ^ k * 2 ^ (i - k) := by rw [← Nat.pow_add, Nat.add_sub_cancel' hge]
    rw [hpow, ← Nat.div_div_eq_div_mul]
    rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos k), Nat.div_eq_of_lt ha, Nat.zero_add]

private theorem memWp_getLsbD_ofInt_nonneg {w : Nat} {z : Int} (hz : 0 ≤ z) (i : Nat) :
    (BitVec.ofInt w z).getLsbD i = (decide (i < w) && z.toNat.testBit i) := by
  have hc : z = ((z.toNat : Nat) : Int) := (Int.toNat_of_nonneg hz).symm
  rw [hc, show BitVec.ofInt w (z.toNat : Int) = BitVec.ofNat w z.toNat from rfl, BitVec.getLsbD_ofNat,
    Int.toNat_natCast]

private theorem memWp_getLsbD_ofInt_ofBytes_append (n : Nat) (bs1 bs2 : List UInt8)
    (h : bs1.length + bs2.length = n) (i : Nat) :
    (BitVec.ofInt (8 * n) (Int.ofBytes (bs1 ++ bs2))).getLsbD i =
      if i < 8 * bs1.length then (BitVec.ofInt (8 * bs1.length) (Int.ofBytes bs1)).getLsbD i
      else (BitVec.ofInt (8 * bs2.length) (Int.ofBytes bs2)).getLsbD (i - 8 * bs1.length) := by
  have ha0 := Int.ofBytes_ge_zero bs1
  have hb0 := Int.ofBytes_ge_zero bs2
  have haLt : Int.ofBytes bs1 < 256 ^ bs1.length := Int.ofBytes_lt bs1
  have hc1 : ((Int.ofBytes bs1).toNat : Int) = Int.ofBytes bs1 := Int.toNat_of_nonneg ha0
  have hc2 : ((Int.ofBytes bs2).toNat : Int) = Int.ofBytes bs2 := Int.toNat_of_nonneg hb0
  have hp1 : (256 : Int) ^ bs1.length = ((2 ^ (8 * bs1.length) : Nat) : Int) := by
    rw [show (256 : Int) = ((2 ^ 8 : Nat) : Int) by decide, ← Int.natCast_pow, ← Nat.pow_mul]
  have hsum : Int.ofBytes (bs1 ++ bs2) =
      (((Int.ofBytes bs1).toNat + 2 ^ (8 * bs1.length) * (Int.ofBytes bs2).toNat : Nat) : Int) := by
    rw [Int.ofBytes_append, hp1]
    push_cast
    rw [hc1, hc2]
  have haLt' : (Int.ofBytes bs1).toNat < 2 ^ (8 * bs1.length) := by omega
  rw [memWp_getLsbD_ofInt_nonneg (Int.ofBytes_ge_zero _), memWp_getLsbD_ofInt_nonneg ha0,
    memWp_getLsbD_ofInt_nonneg hb0, hsum, Int.toNat_natCast,
    memWp_getLsbD_ofNat_pow_add _ _ _ i haLt']
  by_cases hi1 : i < 8 * bs1.length
  · have hi_n : i < 8 * n := by omega
    simp [hi1, hi_n]
  · by_cases hi_n : i < 8 * n
    · have hi2 : i - 8 * bs1.length < 8 * bs2.length := by omega
      simp [hi1, hi_n, hi2]
    · have hi2 : ¬ (i - 8 * bs1.length < 8 * bs2.length) := by omega
      simp [hi1, hi_n, hi2]

private theorem memWp_loadVal_bits_of_loadBytes {m : Mem 64} {a : BitVec 64} {n : Nat} {bs : List UInt8}
    (h : m.loadBytes a (Ty.bits n).bytes = some bs) :
    loadVal m (.bits n) a = some (BitVec.ofInt n (Int.ofBytes bs)) := by
  simp only [loadVal, Mem.loadInt, h, Option.map_some, Option.bind_some, ofBits]

private theorem memWp_storeOk_of_loadBytes {m : Mem 64} {a : BitVec 64} {t : Ty} {bs : List UInt8}
    (h : m.loadBytes a t.bytes = some bs) : storeOk m t a :=
  ⟨Int.ofBytes bs, by simp [Mem.loadInt, h]⟩

private theorem memWp_storeOk_iff_exists_loadBytes {m : Mem 64} {a : BitVec 64} {t : Ty} :
    storeOk m t a ↔ ∃ bs, m.loadBytes a t.bytes = some bs := by
  constructor
  · rintro ⟨i, hi⟩
    simp only [Mem.loadInt, Option.map_eq_some_iff] at hi
    rcases hi with ⟨bs, hbs, _⟩
    exact ⟨bs, hbs⟩
  · rintro ⟨bs, hbs⟩
    exact memWp_storeOk_of_loadBytes hbs

private theorem memWp_chunkBytes_pos_of_valid (target : LegalTarget) (hv : target.valid = true) (b : Nat) :
    (∀ c ∈ chunkBytes target.bitWidths b, 0 < c ∧ 8 * c ∈ target.bitWidths ∧ 8 * c ≤ 64) ∧
    (chunkBytes target.bitWidths b).sum = b := by
  have h8 : 8 ∈ target.bitWidths := valid_mem8 hv
  have h := chunkBytes_pos_mem_sum target.bitWidths h8 b
  refine ⟨fun c hc => ?_, h.2⟩
  obtain ⟨hp, hm⟩ := h.1 c hc
  exact ⟨hp, hm, (valid_bitWidth_spec hv hm).2.2⟩

private theorem memWp_loadBytes_split3 {m : Mem 64} {a : BitVec 64} {off c rest : Nat} {bs : List UInt8}
    (h : m.loadBytes a (off + (c + rest)) = some bs) :
    ∃ bs1 bs2 bs3,
      bs = bs1 ++ (bs2 ++ bs3) ∧ bs1.length = off ∧ bs2.length = c ∧ bs3.length = rest ∧
      m.loadBytes a off = some bs1 ∧
      m.loadBytes (a + BitVec.ofNat 64 off) c = some bs2 ∧
      m.loadBytes (a + BitVec.ofNat 64 (off + c)) rest = some bs3 := by
  rw [memWp_loadBytes_add] at h
  rcases h with ⟨bs1, bs23, h1, h23, rfl⟩
  rw [memWp_loadBytes_add] at h23
  rcases h23 with ⟨bs2, bs3, h2, h3, rfl⟩
  have hl1 := memWp_loadBytes_length _ _ _ h1
  have hl2 := memWp_loadBytes_length _ _ _ h2
  have hl3 := memWp_loadBytes_length _ _ _ h3
  have ha : (a + BitVec.ofNat 64 off) + BitVec.ofNat 64 c = a + BitVec.ofNat 64 (off + c) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  rw [ha] at h3
  exact ⟨bs1, bs2, bs3, rfl, hl1, hl2, hl3, h1, h2, h3⟩

private theorem emitLoadChunk_wp (w c byteOff : Nat) (hcw_le_w : 8 * c ≤ w)
    (hltw : 8 * byteOff < w)
    {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {ptr : Arg Val i64} {chunkVal : BitVec (8 * c)}
    (hLoadChunk : loadVal m (.bits (8 * c)) (ptr.val + BitVec.ofNat 64 byteOff) = some chunkVal)
    (cont : Arg Val (.bits w) → Expr Val Cont rs)
    (hk : ∀ sv : Arg Val (.bits w),
      sv.val = chunkVal.setWidth w <<< (8 * byteOff) → wp Γ Q X (cont sv) m) :
    wp Γ Q X
      (if byteOff == 0 then
        Expr.load (.bits (8 * c)) ptr fun raw =>
          if h : 8 * c = w then
            if byteOff == 0 then cont (castArgBits h (.var raw))
            else Expr.let_ (op2 (OpCode.shl (.bits w)) (castArgBits h (.var raw)) (.imm (BitVec.ofNat w (8 * byteOff)))) fun (s, _) =>
              cont (.var s)
          else if 8 * c < w then
            Expr.let_ (op1 (OpCode.zext (8 * c) w) (.var raw)) fun (z, _) =>
              if byteOff == 0 then cont (.var z)
              else Expr.let_ (op2 (OpCode.shl (.bits w)) (.var z) (.imm (BitVec.ofNat w (8 * byteOff)))) fun (s, _) =>
                cont (.var s)
          else
            Expr.let_ (op1 (OpCode.trunc (8 * c) w) (.var raw)) fun (z, _) =>
              if byteOff == 0 then cont (.var z)
              else Expr.let_ (op2 (OpCode.shl (.bits w)) (.var z) (.imm (BitVec.ofNat w (8 * byteOff)))) fun (s, _) =>
                cont (.var s)
      else
        Expr.let_ (op2 (OpCode.add i64) ptr (.imm (BitVec.ofNat 64 byteOff))) fun (ap, _) =>
          Expr.load (.bits (8 * c)) (.var ap) fun raw =>
            if h : 8 * c = w then
              if byteOff == 0 then cont (castArgBits h (.var raw))
              else Expr.let_ (op2 (OpCode.shl (.bits w)) (castArgBits h (.var raw)) (.imm (BitVec.ofNat w (8 * byteOff)))) fun (s, _) =>
                cont (.var s)
            else if 8 * c < w then
              Expr.let_ (op1 (OpCode.zext (8 * c) w) (.var raw)) fun (z, _) =>
                if byteOff == 0 then cont (.var z)
                else Expr.let_ (op2 (OpCode.shl (.bits w)) (.var z) (.imm (BitVec.ofNat w (8 * byteOff)))) fun (s, _) =>
                  cont (.var s)
            else
              Expr.let_ (op1 (OpCode.trunc (8 * c) w) (.var raw)) fun (z, _) =>
                if byteOff == 0 then cont (.var z)
                else Expr.let_ (op2 (OpCode.shl (.bits w)) (.var z) (.imm (BitVec.ofNat w (8 * byteOff)))) fun (s, _) =>
                  cont (.var s)) m := by
  have hShift : ∀ (vw : Arg Val (.bits w)), vw.val = chunkVal.setWidth w →
      wp Γ Q X (if byteOff == 0 then cont vw
        else Expr.let_ (op2 (OpCode.shl (.bits w)) vw (.imm (BitVec.ofNat w (8 * byteOff)))) fun (s, _) => cont (.var s)) m := by
    intro vw hvw
    by_cases hb0 : byteOff = 0
    · simp only [hb0, beq_self_eq_true, ↓reduceIte]
      subst hb0
      exact hk vw (by simp [hvw])
    · have hne : (byteOff == 0) = false := beq_false_of_ne hb0
      have hw2 : w < 2 ^ w := Nat.lt_two_pow_self
      have hmod : (BitVec.ofNat w (8 * byteOff)).toNat % w = 8 * byteOff := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans hltw hw2), Nat.mod_eq_of_lt hltw]
      simp only [hne, Bool.false_eq_true, ↓reduceIte, wp, Op.wp, op2, vals, OpCode.wp_shl,
        Ty.hasFloat, Bool.false_eq_true, lift2, Arg.val_imm]
      exact hk (.var _) (by dsimp only [Arg.val_var]; rw [hmod, hvw])
  have hLoadStep : ∀ (ap : Arg Val i64), ap.val = ptr.val + BitVec.ofNat 64 byteOff →
      wp Γ Q X (Expr.load (.bits (8 * c)) ap fun raw =>
        if h : 8 * c = w then
          if byteOff == 0 then cont (castArgBits h (.var raw))
          else Expr.let_ (op2 (OpCode.shl (.bits w)) (castArgBits h (.var raw)) (.imm (BitVec.ofNat w (8 * byteOff)))) fun (s, _) =>
            cont (.var s)
        else if 8 * c < w then
          Expr.let_ (op1 (OpCode.zext (8 * c) w) (.var raw)) fun (z, _) =>
            if byteOff == 0 then cont (.var z)
            else Expr.let_ (op2 (OpCode.shl (.bits w)) (.var z) (.imm (BitVec.ofNat w (8 * byteOff)))) fun (s, _) =>
              cont (.var s)
        else
          Expr.let_ (op1 (OpCode.trunc (8 * c) w) (.var raw)) fun (z, _) =>
            if byteOff == 0 then cont (.var z)
            else Expr.let_ (op2 (OpCode.shl (.bits w)) (.var z) (.imm (BitVec.ofNat w (8 * byteOff)))) fun (s, _) =>
              cont (.var s)) m := by
    intro ap hap
    rw [wp_load, hap]
    refine ⟨chunkVal, hLoadChunk, ?_⟩
    by_cases heq : 8 * c = w
    · simp only [heq, ↓reduceDIte]
      apply hShift (castArgBits heq (.var chunkVal))
      rw [val_castArgBits, Arg.val_var, cast_eq_setWidth heq]
    · have hlt : 8 * c < w := by omega
      simp only [heq, hlt, ↓reduceDIte, ↓reduceIte, wp, Op.wp, op1, vals, OpCode.wp_zext]
      exact ⟨Nat.le_of_lt hlt, hShift (.var _) rfl⟩
  by_cases hb0 : byteOff = 0
  · simp only [hb0, beq_self_eq_true, ↓reduceIte]
    subst hb0
    exact hLoadStep ptr (by simp)
  · have hne : (byteOff == 0) = false := beq_false_of_ne hb0
    simp only [hne, Bool.false_eq_true, ↓reduceIte] at hLoadStep
    simp only [hne, Bool.false_eq_true, ↓reduceIte, wp, Op.wp, op2, vals, OpCode.wp_add,
      Ty.hasFloat, Bool.false_eq_true, lift2, Arg.val_imm]
    exact hLoadStep (.var _) rfl

private theorem emitLoadBits_go_wp (target : LegalTarget) (_hv : target.valid = true)
    {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {n w : Nat}
    (hnw : n ≤ w) (hw64 : w ≤ 64) (hw8 : w % 8 = 0) (_hn_pos : 0 < n)
    {m : Mem 64} {ptr : Arg Val i64} {bs : List UInt8}
    (hMem : m.loadBytes ptr.val ((n + 7) / 8) = some bs) :
    ∀ (cs : List Nat) (byteOff : Nat) (acc : Option (Arg Val (.bits w))),
      (∀ c ∈ cs, 0 < c ∧ 8 * c ∈ target.bitWidths ∧ 8 * c ≤ 64) →
      byteOff + cs.sum = (n + 7) / 8 →
      (acc = none → byteOff = 0) →
      (∀ ac, acc = some ac → ∀ i, ac.val.getLsbD i =
        if i < 8 * byteOff then (BitVec.ofInt (8 * ((n + 7) / 8)) (Int.ofBytes bs)).getLsbD i
        else false) →
      ∀ {k : Arg Val (.bits w) → Expr Val Cont rs},
        (∀ r : Arg Val (.bits w),
          r.val = (BitVec.ofInt n (Int.ofBytes bs)).setWidth w → wp Γ Q X (k r) m) →
        wp Γ Q X (emitLoadBits.go n w ptr k byteOff cs acc) m
  | [], byteOff, acc, _, hsum, hnone, hacc, k, hk => by
    simp only [List.sum_nil, Nat.add_zero] at hsum
    subst hsum
    cases acc with
    | none =>
      exfalso
      have h0 := hnone rfl
      omega
    | some v =>
      dsimp only [emitLoadBits.go]
      refine emitMaskToN_wp hnw rfl fun r hr => ?_
      apply hk r
      rw [hr]
      congr 1
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      have hv' := hacc v rfl i
      rw [BitVec.getLsbD_setWidth, decide_eq_true hi, Bool.true_and, hv']
      have hlt : i < 8 * ((n + 7) / 8) := by omega
      simp only [hlt, ↓reduceIte]
      have h0 := Int.ofBytes_ge_zero bs
      rw [memWp_getLsbD_ofInt_nonneg h0, memWp_getLsbD_ofInt_nonneg h0]
      simp [hi, hlt]
  | c :: rest, byteOff, acc, hcs, hsum, _hnone, hacc, k, hk => by
    have hcmem := hcs c List.mem_cons_self
    have hc_pos : 0 < c := hcmem.1
    have hcw64 : 8 * c ≤ 64 := hcmem.2.2
    have hb_le_w : 8 * ((n + 7) / 8) ≤ w := by omega
    have hsum' : byteOff + (c + rest.sum) = (n + 7) / 8 := by simpa [List.sum_cons] using hsum
    have hcw_le_w : 8 * c ≤ w := by omega
    have hbl := memWp_loadBytes_length _ _ _ hMem
    have hMem_rw : m.loadBytes ptr.val (byteOff + (c + rest.sum)) = some bs := by rwa [hsum']
    obtain ⟨bs1, bs2, bs3, rfl, hl1, hl2, hl3, _h1, h2, _h3⟩ := memWp_loadBytes_split3 hMem_rw
    have hLoadChunk : loadVal m (.bits (8 * c)) (ptr.val + BitVec.ofNat 64 byteOff) =
        some (BitVec.ofInt (8 * c) (Int.ofBytes bs2)) := by
      apply memWp_loadVal_bits_of_loadBytes
      simpa [Ty.bytes, Ty.size, show (8 * c + 7) / 8 = c by omega] using h2
    have hSvBits : ∀ (sv : Arg Val (.bits w)),
        sv.val = (BitVec.ofInt (8 * c) (Int.ofBytes bs2)).setWidth w <<< (8 * byteOff) →
        ∀ i, sv.val.getLsbD i =
          if 8 * byteOff ≤ i ∧ i < 8 * (byteOff + c) then
            (BitVec.ofInt (8 * ((n + 7) / 8)) (Int.ofBytes (bs1 ++ (bs2 ++ bs3)))).getLsbD i
          else false := by
      intro sv hsv i
      rw [hsv, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
      by_cases hi_w : i < w
      · by_cases hi_lo : i < 8 * byteOff
        · have hnot : ¬ (8 * byteOff ≤ i ∧ i < 8 * (byteOff + c)) := by omega
          simp [hi_lo, hnot]
        · by_cases hi_hi : i < 8 * (byteOff + c)
          · have hsub : i - 8 * byteOff < 8 * c := by omega
            have hsp1 := memWp_getLsbD_ofInt_ofBytes_append (byteOff + (c + rest.sum)) bs1 (bs2 ++ bs3)
              (by simp [hl1, hl2, hl3]) i
            rw [hsum', hl1] at hsp1
            rw [hsp1, ite_eq_right hi_lo]
            have hsp2 := memWp_getLsbD_ofInt_ofBytes_append ((bs2 ++ bs3).length) bs2 bs3
              List.length_append.symm (i - 8 * byteOff)
            rw [List.length_append, hl2, hl3] at hsp2
            rw [List.length_append, hl2, hl3, hsp2, ite_eq_left hsub]
            simp [hi_w, hi_lo, hi_hi, show 8 * byteOff ≤ i by omega, show i - 8 * byteOff < w by omega]
          · have hnot : ¬ (8 * byteOff ≤ i ∧ i < 8 * (byteOff + c)) := by omega
            rw [BitVec.getLsbD_of_ge _ _ (by omega)]
            simp [hi_w, hi_lo, hnot]
      · have hnot : ¬ (8 * byteOff ≤ i ∧ i < 8 * (byteOff + c)) := by omega
        simp only [decide_eq_false hi_w, Bool.false_and, hnot, ↓reduceIte]
    dsimp only [emitLoadBits.go]
    cases acc with
    | none =>
      refine emitLoadChunk_wp w c byteOff hcw_le_w (by omega) hLoadChunk
        (fun sv => emitLoadBits.go n w ptr k (byteOff + c) rest (some sv))
        fun sv hsv => ?_
      refine emitLoadBits_go_wp target _hv hnw hw64 hw8 _hn_pos (bs := bs1 ++ (bs2 ++ bs3)) hMem
        rest (byteOff + c) (some sv)
        (fun x hx => hcs x (List.mem_cons_of_mem _ hx)) (by omega) (fun h => by cases h)
        (fun ac hac i => ?_) hk
      cases hac
      rw [hSvBits sv hsv i]
      by_cases hi_hi : i < 8 * (byteOff + c)
      · have hb0 := _hnone rfl
        simp [hb0]
      · simp [hi_hi]
    | some prev =>
      refine emitLoadChunk_wp w c byteOff hcw_le_w (by omega) hLoadChunk
        (fun sv => Expr.let_ (op2 (OpCode.or (.bits w)) prev sv) fun (u, _) =>
          emitLoadBits.go n w ptr k (byteOff + c) rest (some (.var u)))
        fun sv hsv => ?_
      dsimp only [wp, Op.wp, op2, vals, OpCode.wp_or, lift2, Ty.hasFloat, Bool.false_eq_true]
      refine emitLoadBits_go_wp target _hv hnw hw64 hw8 _hn_pos (bs := bs1 ++ (bs2 ++ bs3)) hMem
        rest (byteOff + c) (some (.var _))
        (fun x hx => hcs x (List.mem_cons_of_mem _ hx)) (by omega) (fun h => by cases h)
        (fun ac hac i => ?_) hk
      cases hac
      dsimp only [Arg.val_var]
      rw [BitVec.getLsbD_or, hacc prev rfl i, hSvBits sv hsv i]
      by_cases hi_lo : i < 8 * byteOff
      · have hi_hi : i < 8 * (byteOff + c) := by omega
        simp [hi_lo, hi_hi]
      · by_cases hi_hi : i < 8 * (byteOff + c)
        · simp [hi_lo, hi_hi, show 8 * byteOff ≤ i from by omega]
        · simp [hi_lo, hi_hi]

private theorem emitLoadBits_wp (target : LegalTarget) (hv : target.valid = true)
    {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {n : Nat}
    (hsupp : target.supportsTy (.bits n) = true) (_hnw_ne : n ≠ target.widenWidth n)
    {m : Mem 64} {ptr : Arg Val i64} {v : BitVec n}
    (hLoad : loadVal m (.bits n) ptr.val = some v)
    {k : Arg Val (.bits (target.widenWidth n)) → Expr Val Cont rs}
    (hk : ∀ r : Arg Val (.bits (target.widenWidth n)),
      r.val = v.setWidth (target.widenWidth n) → wp Γ Q X (k r) m) :
    wp Γ Q X (emitLoadBits target.bitWidths n (target.widenWidth n) ptr k) m := by
  have hnw := le_widenWidth_of_supports hsupp
  have hws := valid_bitWidth_spec hv (widenWidth_mem_of_supports hsupp)
  have hw8 := hws.2.1
  have hw64 := hws.2.2
  unfold emitLoadBits
  by_cases hn0 : n = 0
  · subst hn0
    simp only [Nat.zero_add, show (7 : Nat) / 8 = 0 by decide, beq_self_eq_true, ↓reduceIte]
    apply hk (.imm 0#(target.widenWidth 0))
    rw [Arg.val_imm, Subsingleton.elim v (0#0)]
    apply BitVec.eq_of_toNat_eq; simp
  · have hn_pos : 0 < n := Nat.pos_of_ne_zero hn0
    have hb_ne : ((n + 7) / 8 == 0) = false := beq_false_of_ne (by omega)
    simp only [hb_ne, Bool.false_eq_true, ↓reduceIte]
    simp only [loadVal, Mem.loadInt, Option.bind_eq_some_iff,
      Option.map_eq_some_iff, Option.some.injEq] at hLoad
    rcases hLoad with ⟨i, ⟨bs, hMem, rfl⟩, rfl⟩
    obtain ⟨hcs, hsum⟩ := memWp_chunkBytes_pos_of_valid target hv ((n + 7) / 8)
    exact emitLoadBits_go_wp target hv hnw hw64 hw8 hn_pos hMem
      (chunkBytes target.bitWidths ((n + 7) / 8)) 0 none hcs (by omega) (fun _ => rfl)
      (fun _ h => by cases h) hk

private theorem emitStoreBits_go_wp (target : LegalTarget) (_hv : target.valid = true)
    {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {n w : Nat}
    (hnw : n ≤ w) (hw64 : w ≤ 64) (hw8 : w % 8 = 0) (_hn_pos : 0 < n)
    (v : Arg Val (.bits w)) (ptr : Arg Val i64) (k : Expr Val Cont rs) :
    ∀ (cs : List Nat) (byteOff : Nat) (m : Mem 64),
      (∀ c ∈ cs, 0 < c ∧ 8 * c ∈ target.bitWidths ∧ 8 * c ≤ 64) →
      byteOff + cs.sum = (n + 7) / 8 →
      (∃ bs, m.loadBytes (ptr.val + BitVec.ofNat 64 byteOff) cs.sum = some bs) →
      wp Γ Q X k (m.storeBytes (ptr.val + BitVec.ofNat 64 byteOff)
        (Int.toBytes cs.sum ((v.val.toNat : Int) / (256 : Int) ^ byteOff))) →
      wp Γ Q X (emitStoreBits.go w v ptr k byteOff cs) m
  | [], byteOff, m, _, _, _, hk => by
    rw [emitStoreBits.go.eq_1]
    simpa [List.sum_nil, Int.toBytes, memWp_storeBytes_nil] using hk
  | c :: rest, byteOff, m, hcs, hsum, hOk, hk => by
    have hcmem := hcs c List.mem_cons_self
    have hc_pos : 0 < c := hcmem.1
    have hcw64 : 8 * c ≤ 64 := hcmem.2.2
    have hb_le_w : 8 * ((n + 7) / 8) ≤ w := by omega
    have hsum' : byteOff + (c + rest.sum) = (n + 7) / 8 := by simpa [List.sum_cons] using hsum
    have hcw_le_w : 8 * c ≤ w := by omega
    rcases hOk with ⟨bs, hLoad⟩
    rw [List.sum_cons, memWp_loadBytes_add] at hLoad
    rcases hLoad with ⟨bs1, bs2, hLoadC, hLoadRest, _⟩
    have hOkC : storeOk m (.bits (8 * c)) (ptr.val + BitVec.ofNat 64 byteOff) := by
      apply memWp_storeOk_of_loadBytes
      simpa [Ty.bytes, Ty.size, show (8 * c + 7) / 8 = c by omega] using hLoadC
    rw [emitStoreBits.go.eq_2]
    dsimp only
    have hShifted : ∀ (cont : Arg Val (.bits w) → Expr Val Cont rs),
        (∀ sv : Arg Val (.bits w), sv.val = v.val >>> (8 * byteOff) → wp Γ Q X (cont sv) m) →
        wp Γ Q X (if byteOff == 0 then cont v
          else Expr.let_ (op2 (OpCode.lshr (.bits w)) v (.imm (BitVec.ofNat w (8 * byteOff)))) fun (s, _) => cont (.var s)) m := by
      intro cont hcont
      by_cases hb0 : byteOff = 0
      · simp only [hb0, beq_self_eq_true, ↓reduceIte]
        subst hb0
        exact hcont v (by rw [Nat.mul_zero]; rfl)
      · have hne : (byteOff == 0) = false := beq_false_of_ne hb0
        have hw2 : w < 2 ^ w := Nat.lt_two_pow_self
        have hltw : 8 * byteOff < w := by omega
        have hmod : (BitVec.ofNat w (8 * byteOff)).toNat % w = 8 * byteOff := by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans hltw hw2), Nat.mod_eq_of_lt hltw]
        simp only [hne, Bool.false_eq_true, ↓reduceIte, wp, Op.wp, op2, vals, OpCode.wp_lshr,
          Ty.hasFloat, Bool.false_eq_true, lift2, Arg.val_imm]
        exact hcont (.var _) (by dsimp only [Arg.val_var]; rw [hmod])
    refine hShifted (fun sv =>
      (fun val =>
        (fun ap => .store (t := .bits (8 * c)) val ap (emitStoreBits.go w v ptr k (byteOff + c) rest)) |>
          fun f => if byteOff == 0 then f ptr else Expr.let_ (op2 (OpCode.add i64) ptr (.imm (BitVec.ofNat 64 byteOff))) fun (ap, _) => f (.var ap)) |>
        fun g => if h : 8 * c = w then g (castArgBits h.symm sv)
          else if 8 * c < w then Expr.let_ (op1 (OpCode.trunc w (8 * c)) sv) fun (tr, _) => g (.var tr)
          else Expr.let_ (op1 (OpCode.zext w (8 * c)) sv) fun (tr, _) => g (.var tr))
      fun sv hsv => ?_
    have hToCw : ∀ (cont : Arg Val (.bits (8 * c)) → Expr Val Cont rs),
        (∀ val : Arg Val (.bits (8 * c)),
          val.val = (v.val >>> (8 * byteOff)).setWidth (8 * c) → wp Γ Q X (cont val) m) →
        wp Γ Q X (if h : 8 * c = w then cont (castArgBits h.symm sv)
          else if 8 * c < w then Expr.let_ (op1 (OpCode.trunc w (8 * c)) sv) fun (tr, _) => cont (.var tr)
          else Expr.let_ (op1 (OpCode.zext w (8 * c)) sv) fun (tr, _) => cont (.var tr)) m := by
      intro cont hcont
      by_cases heq : 8 * c = w
      · simp only [heq, ↓reduceDIte]
        apply hcont (castArgBits heq.symm sv)
        rw [val_castArgBits, hsv, cast_eq_setWidth heq.symm]
      · have hlt : 8 * c < w := by omega
        simp only [heq, hlt, ↓reduceDIte, ↓reduceIte, wp, Op.wp, op1, vals, OpCode.wp_trunc]
        refine ⟨Nat.le_of_lt hlt, hcont (.var _) (by simp [hsv])⟩
    refine hToCw (fun val =>
      if byteOff == 0 then .store (t := .bits (8 * c)) val ptr (emitStoreBits.go w v ptr k (byteOff + c) rest)
      else Expr.let_ (op2 (OpCode.add i64) ptr (.imm (BitVec.ofNat 64 byteOff))) fun (ap, _) =>
        .store (t := .bits (8 * c)) val (.var ap) (emitStoreBits.go w v ptr k (byteOff + c) rest))
      fun val hval => ?_
    have hAddr : ∀ (cont : Arg Val i64 → Expr Val Cont rs),
        (∀ ap : Arg Val i64, ap.val = ptr.val + BitVec.ofNat 64 byteOff → wp Γ Q X (cont ap) m) →
        wp Γ Q X (if byteOff == 0 then cont ptr
          else Expr.let_ (op2 (OpCode.add i64) ptr (.imm (BitVec.ofNat 64 byteOff))) fun (ap, _) => cont (.var ap)) m := by
      intro cont hcont
      by_cases hb0 : byteOff = 0
      · simp only [hb0, beq_self_eq_true, ↓reduceIte]
        subst hb0
        exact hcont ptr (by simp)
      · have hne : (byteOff == 0) = false := beq_false_of_ne hb0
        simp only [hne, Bool.false_eq_true, ↓reduceIte, wp, Op.wp, op2, vals, OpCode.wp_add,
          Ty.hasFloat, Bool.false_eq_true, lift2, Arg.val_imm]
        exact hcont (.var _) rfl
    refine hAddr (fun ap => .store (t := .bits (8 * c)) val ap (emitStoreBits.go w v ptr k (byteOff + c) rest))
      fun ap hap => ?_
    rw [wp_store, hap]
    refine ⟨hOkC, ?_⟩
    have hbytes_eq : Int.toBytes c (((val.val : BitVec (8 * c)).setWidth (8 * (Ty.bits (8 * c)).bytes)).toInt) =
        Int.toBytes c ((v.val.toNat : Int) / (256 : Int) ^ byteOff) := by
      have hbw : (Ty.bits (8 * c)).bytes = c := by simp [Ty.bytes, Ty.size]; omega
      rw [hbw, BitVec.setWidth_eq, hval]
      exact memWp_int_toBytes_shift (by omega) v.val
    have hm' : storeMem m (.bits (8 * c)) (ptr.val + BitVec.ofNat 64 byteOff) val.val =
        m.storeBytes (ptr.val + BitVec.ofNat 64 byteOff)
          (Int.toBytes c ((v.val.toNat : Int) / (256 : Int) ^ byteOff)) := by
      simp only [storeMem, Mem.storeInt, toBits,
        show (Ty.bits (8 * c)).bytes = c by simp [Ty.bytes, Ty.size]; omega]
      exact congrArg (m.storeBytes (ptr.val + BitVec.ofNat 64 byteOff)) hbytes_eq
    rw [hm']
    have ha_rest : (ptr.val + BitVec.ofNat 64 byteOff) + BitVec.ofNat 64 c =
        ptr.val + BitVec.ofNat 64 (byteOff + c) := by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    have hOkRest : ∃ bs', (m.storeBytes (ptr.val + BitVec.ofNat 64 byteOff)
        (Int.toBytes c ((v.val.toNat : Int) / (256 : Int) ^ byteOff))).loadBytes
        (ptr.val + BitVec.ofNat 64 (byteOff + c)) rest.sum = some bs' := by
      apply memWp_loadBytes_isSome_storeBytes
      rw [← ha_rest]
      exact ⟨bs2, hLoadRest⟩
    refine emitStoreBits_go_wp target _hv hnw hw64 hw8 _hn_pos v ptr k rest (byteOff + c) _
      (fun x hx => hcs x (List.mem_cons_of_mem _ hx)) (by omega) hOkRest ?_
    have hlen_le : (Int.toBytes c ((v.val.toNat : Int) / (256 : Int) ^ byteOff)).length +
        (Int.toBytes rest.sum ((v.val.toNat : Int) / (256 : Int) ^ (byteOff + c))).length ≤ 2 ^ 64 := by
      rw [Int.toBytes_length, Int.toBytes_length]; omega
    have ha_len : (ptr.val + BitVec.ofNat 64 byteOff) +
        BitVec.ofNat 64 (Int.toBytes c ((v.val.toNat : Int) / (256 : Int) ^ byteOff)).length =
        ptr.val + BitVec.ofNat 64 (byteOff + c) := by
      rw [Int.toBytes_length, ha_rest]
    rw [← ha_len, ← memWp_storeBytes_append m (ptr.val + BitVec.ofNat 64 byteOff) _ _ hlen_le]
    have hAddBytes :
        Int.toBytes c ((v.val.toNat : Int) / (256 : Int) ^ byteOff) ++
          Int.toBytes rest.sum ((v.val.toNat : Int) / (256 : Int) ^ (byteOff + c)) =
        Int.toBytes (c + rest.sum) ((v.val.toNat : Int) / (256 : Int) ^ byteOff) := by
      rw [memWp_int_toBytes_add c rest.sum ((v.val.toNat : Int) / (256 : Int) ^ byteOff)]
      congr 2
      have hdiv : ((v.val.toNat : Int) / (256 : Int) ^ byteOff) / (256 : Int) ^ c =
          (v.val.toNat : Int) / (256 : Int) ^ (byteOff + c) := by
        rw [Int.pow_add]
        exact (Int.ediv_ediv_of_nonneg (Int.pow_nonneg (by decide)))
      exact hdiv.symm
    rw [hAddBytes]
    simpa [List.sum_cons] using hk

private theorem emitStoreBits_wp (target : LegalTarget) (hv : target.valid = true)
    {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {n : Nat}
    (hsupp : target.supportsTy (.bits n) = true) (_hnw_ne : n ≠ target.widenWidth n)
    {m : Mem 64} {v' : Arg Val (.bits (target.widenWidth n))} {v : BitVec n}
    (hv' : v'.val = v.setWidth (target.widenWidth n)) {ptr : Arg Val i64}
    {k : Expr Val Cont rs}
    (hOk : storeOk m (.bits n) ptr.val)
    (hk : wp Γ Q X k (storeMem m (.bits n) ptr.val v)) :
    wp Γ Q X (emitStoreBits target.bitWidths n (target.widenWidth n) v' ptr k) m := by
  have hnw := le_widenWidth_of_supports hsupp
  have hws := valid_bitWidth_spec hv (widenWidth_mem_of_supports hsupp)
  have hw8 := hws.2.1
  have hw64 := hws.2.2
  unfold emitStoreBits
  by_cases hn0 : n = 0
  · subst hn0
    simp only [Nat.zero_add, show (7 : Nat) / 8 = 0 by decide, beq_self_eq_true, ↓reduceIte]
    simpa [storeMem, Mem.storeInt, Ty.bytes, Ty.size, Int.toBytes, memWp_storeBytes_nil] using hk
  · have hn_pos : 0 < n := Nat.pos_of_ne_zero hn0
    have hb_ne : ((n + 7) / 8 == 0) = false := beq_false_of_ne (by omega)
    simp only [hb_ne, Bool.false_eq_true, ↓reduceIte]
    obtain ⟨bs, hLoad⟩ := memWp_storeOk_iff_exists_loadBytes.mp hOk
    obtain ⟨hcs, hsum⟩ := memWp_chunkBytes_pos_of_valid target hv ((n + 7) / 8)
    refine emitStoreBits_go_wp target hv hnw hw64 hw8 hn_pos v' ptr k
      (chunkBytes target.bitWidths ((n + 7) / 8)) 0 m hcs (by omega)
      ⟨bs, by simpa [BitVec.add_zero, hsum, Ty.bytes, Ty.size] using hLoad⟩ ?_
    simp only [BitVec.add_zero, hsum, Int.pow_zero, Int.ediv_one]
    rw [← memWp_int_toBytes_bitVec_toNat ((n + 7) / 8) (target.widenWidth n) (by omega) v'.val]
    have hsw : v'.val.setWidth (8 * ((n + 7) / 8)) = v.setWidth (8 * ((n + 7) / 8)) := by
      rw [hv', BitVec.setWidth_setWidth_of_le _ (by omega)]
    rw [hsw]
    simpa [storeMem, Mem.storeInt, Ty.bytes, Ty.size, toBits] using hk

private theorem size_eq_eight_mul_bytes_of_isByteAlignedStruct :
    ∀ (t : Ty), t.isByteAlignedStruct = true →
      0 < t.size ∧ t.size % 8 = 0 ∧ t.size = 8 * t.bytes ∧ 0 < t.bytes
  | .bool, h => by simp [Ty.isByteAlignedStruct] at h
  | .bits n, h => by
    simp only [Ty.isByteAlignedStruct, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    rcases h with ⟨hpos, hm8⟩
    simp only [Ty.size, Ty.bytes]
    refine ⟨hpos, hm8, by omega, by omega⟩
  | .float f, _ => by cases f <;> decide
  | .pair a b, h => by
    simp only [Ty.isByteAlignedStruct, Bool.and_eq_true] at h
    have ha := size_eq_eight_mul_bytes_of_isByteAlignedStruct a h.1
    have hb := size_eq_eight_mul_bytes_of_isByteAlignedStruct b h.2
    simp only [Ty.size, Ty.bytes] at ha hb ⊢
    omega

private theorem bytes_pair_of_isByteAlignedStruct {a b : Ty}
    (h : (a.pair b).isByteAlignedStruct = true) :
    a.isByteAlignedStruct = true ∧ b.isByteAlignedStruct = true ∧
      (a.pair b).bytes = a.bytes + b.bytes ∧
      a.size = 8 * a.bytes ∧ b.size = 8 * b.bytes ∧ 0 < a.bytes ∧ 0 < b.bytes := by
  simp only [Ty.isByteAlignedStruct, Bool.and_eq_true] at h
  have ha := size_eq_eight_mul_bytes_of_isByteAlignedStruct a h.1
  have hb := size_eq_eight_mul_bytes_of_isByteAlignedStruct b h.2
  refine ⟨h.1, h.2, ?_, ha.2.2.1, hb.2.2.1, ha.2.2.2, hb.2.2.2⟩
  simp only [Ty.bytes, Ty.size] at ha hb ⊢
  omega

private theorem loadVal_eq_of_loadBytes_of_isByteAlignedStruct {m : Mem 64} {p : BitVec 64}
    {t : Ty} (ht : t.isByteAlignedStruct = true) {bs : List UInt8}
    (hm : m.loadBytes p t.bytes = some bs) :
    loadVal m t p = some (ofBits t (BitVec.ofInt t.size (Int.ofBytes bs))) := by
  cases t with
  | bool => simp [Ty.isByteAlignedStruct] at ht
  | bits n => simp [loadVal, Mem.loadInt, hm]
  | float f => simp [loadVal, Mem.loadInt, hm]
  | pair a b => simp [loadVal, Mem.loadInt, hm, Ty.size]

private theorem loadVal_pair_of_isByteAlignedStruct {m : Mem 64} {ptr : BitVec 64}
    {a b : Ty} (h : (a.pair b).isByteAlignedStruct = true)
    {va : Val a} {vb : Val b}
    (hLoad : loadVal m (.pair a b) ptr = some (va, vb)) :
    loadVal m a ptr = some va ∧ loadVal m b (ptr + BitVec.ofNat 64 a.bytes) = some vb := by
  obtain ⟨ha, hb, hbytes, hsa, hsb, _, _⟩ := bytes_pair_of_isByteAlignedStruct h
  simp only [loadVal, Mem.loadInt, Option.bind_eq_some_iff, Option.map_eq_some_iff,
    Option.some.injEq] at hLoad
  rcases hLoad with ⟨i, ⟨bs, hMem, rfl⟩, hEq⟩
  rw [hbytes, memWp_loadBytes_add] at hMem
  rcases hMem with ⟨bs1, bs2, h1, h2, rfl⟩
  have hl1 := memWp_loadBytes_length _ _ _ h1
  have hl2 := memWp_loadBytes_length _ _ _ h2
  rw [loadVal_eq_of_loadBytes_of_isByteAlignedStruct ha h1,
      loadVal_eq_of_loadBytes_of_isByteAlignedStruct hb h2]
  simp only [ofBits, Prod.mk.injEq] at hEq
  rcases hEq with ⟨hva, hvb⟩
  have hext1 : BitVec.extractLsb' 0 a.size (BitVec.ofInt (a.size + b.size) (Int.ofBytes (bs1 ++ bs2))) =
      BitVec.ofInt a.size (Int.ofBytes bs1) := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    rw [BitVec.getLsbD_extractLsb', Nat.zero_add, decide_eq_true hj, Bool.true_and]
    have hsp := memWp_getLsbD_ofInt_ofBytes_append (bs1.length + bs2.length) bs1 bs2 rfl j
    rw [hl1, hl2, Nat.mul_add, ← hsa, ← hsb] at hsp
    rw [hsp, ite_eq_left (by omega)]
  have hext2 : BitVec.extractLsb' a.size b.size (BitVec.ofInt (a.size + b.size) (Int.ofBytes (bs1 ++ bs2))) =
      BitVec.ofInt b.size (Int.ofBytes bs2) := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    rw [BitVec.getLsbD_extractLsb', decide_eq_true hj, Bool.true_and]
    have hsp := memWp_getLsbD_ofInt_ofBytes_append (bs1.length + bs2.length) bs1 bs2 rfl (a.size + j)
    rw [hl1, hl2, Nat.mul_add, ← hsa, ← hsb] at hsp
    rw [hsp, ite_eq_right (by omega), Nat.add_sub_cancel_left]
  rw [hext1] at hva
  rw [hext2] at hvb
  simp [hva, hvb]

private theorem storeOk_pair_of_isByteAlignedStruct {m : Mem 64} {ptr : BitVec 64}
    {a b : Ty} (h : (a.pair b).isByteAlignedStruct = true)
    (hOk : storeOk m (.pair a b) ptr) :
    storeOk m a ptr ∧ ∀ va : Val a, storeOk (storeMem m a ptr va) b (ptr + BitVec.ofNat 64 a.bytes) := by
  obtain ⟨_ha, _hb, hbytes, _, _, _, _⟩ := bytes_pair_of_isByteAlignedStruct h
  rw [memWp_storeOk_iff_exists_loadBytes] at hOk
  rcases hOk with ⟨bs, hLoad⟩
  rw [hbytes, memWp_loadBytes_add] at hLoad
  rcases hLoad with ⟨bs1, bs2, h1, h2, _⟩
  refine ⟨memWp_storeOk_of_loadBytes h1, fun va => ?_⟩
  rw [memWp_storeOk_iff_exists_loadBytes]
  exact memWp_loadBytes_isSome_storeBytes _ ⟨bs2, h2⟩

private theorem memWp_toNat_append_bv {n m : Nat} (y : BitVec m) (x : BitVec n) :
    (y ++ x).toNat = x.toNat + 2 ^ n * y.toNat := by
  have hbveq : ∀ {k : Nat} (v : BitVec k), BitVec.ofNat k v.toNat = v := by
    intro k v; apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt v.isLt]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [memWp_getLsbD_ofNat_pow_add x.toNat n y.toNat i x.isLt]
  have hget : (y ++ x).toNat.testBit i = (y ++ x).getLsbD i := by
    conv => rhs; rw [← hbveq (y ++ x)]
    rw [BitVec.getLsbD_ofNat]
    by_cases him : i < m + n
    · simp [him]
    · have hge : (y ++ x).toNat < 2 ^ i :=
        Nat.lt_of_lt_of_le (y ++ x).isLt (Nat.pow_le_pow_right (by omega) (by omega))
      rw [Nat.testBit_lt_two_pow hge]
      simp [him]
  rw [hget, BitVec.getLsbD_append]
  by_cases hin : i < n
  · rw [ite_eq_left hin, ite_eq_left hin]
    conv => lhs; rw [← hbveq x]
    rw [BitVec.getLsbD_ofNat]
    simp [hin]
  · rw [ite_eq_right hin, ite_eq_right hin]
    conv => lhs; rw [← hbveq y]
    rw [BitVec.getLsbD_ofNat]
    by_cases him : i - n < m
    · simp [him]
    · have hge : y.toNat < 2 ^ (i - n) :=
        Nat.lt_of_lt_of_le y.isLt (Nat.pow_le_pow_right (by omega) (by omega))
      rw [Nat.testBit_lt_two_pow hge]
      simp [him]

private theorem storeMem_pair_of_isByteAlignedStruct {m : Mem 64} {ptr : BitVec 64}
    {a b : Ty} (h : (a.pair b).isByteAlignedStruct = true)
    (hle : (a.pair b).bytes ≤ 2 ^ 64) (va : Val a) (vb : Val b) :
    storeMem (storeMem m a ptr va) b (ptr + BitVec.ofNat 64 a.bytes) vb =
      storeMem m (.pair a b) ptr (va, vb) := by
  obtain ⟨_ha, _hb, hbytes, hsa, hsb, _, _⟩ := bytes_pair_of_isByteAlignedStruct h
  simp only [storeMem, Mem.storeInt]
  rw [memWp_int_toBytes_bitVec_toNat a.bytes a.size (by omega) (toBits a va),
      memWp_int_toBytes_bitVec_toNat b.bytes b.size (by omega) (toBits b vb),
      memWp_int_toBytes_bitVec_toNat (a.pair b).bytes (a.pair b).size (by
        simp only [Ty.size] at hsa hsb ⊢; rw [hbytes]; omega) (toBits (.pair a b) (va, vb))]
  have hlen : (Int.toBytes a.bytes ((toBits a va).toNat : Int)).length +
      (Int.toBytes b.bytes ((toBits b vb).toNat : Int)).length ≤ 2 ^ 64 := by
    rw [Int.toBytes_length, Int.toBytes_length, ← hbytes]; exact hle
  have ha_len : ptr + BitVec.ofNat 64 (Int.toBytes a.bytes ((toBits a va).toNat : Int)).length =
      ptr + BitVec.ofNat 64 a.bytes := by rw [Int.toBytes_length]
  rw [← ha_len, ← memWp_storeBytes_append m ptr _ _ hlen]
  congr 1
  rw [hbytes, memWp_int_toBytes_add]
  have hcat : (toBits (.pair a b) (va, vb)).toNat =
      (toBits a va).toNat + 2 ^ (8 * a.bytes) * (toBits b vb).toNat := by
    simp only [toBits, BitVec.toNat_cast, memWp_toNat_append_bv, hsa]
  rw [hcat]
  have hp : (256 : Int) ^ a.bytes = (2 : Int) ^ (8 * a.bytes) := by
    rw [show (256 : Int) = 2 ^ 8 by decide, ← Int.pow_mul]
  have ha_lt : ((toBits a va).toNat : Int) < (256 : Int) ^ a.bytes := by
    rw [hp, show ((2 : Int) ^ (8 * a.bytes)) = ((2 ^ (8 * a.bytes) : Nat) : Int) from (Int.natCast_pow 2 _).symm]
    exact Int.ofNat_lt.mpr (by rw [← hsa]; exact (toBits a va).isLt)
  have hp_pos : (0 : Int) < (256 : Int) ^ a.bytes := Int.pow_pos (by decide)
  have hmod1 : ((((toBits a va).toNat + 2 ^ (8 * a.bytes) * (toBits b vb).toNat : Nat) : Int)) %
      (2 : Int) ^ (8 * a.bytes) = ((toBits a va).toNat : Int) := by
    push_cast
    rw [← hp, Int.mul_comm ((256 : Int) ^ a.bytes), Int.add_mul_emod_self_right,
      Int.emod_eq_of_lt (Int.natCast_nonneg _) ha_lt]
  have hdiv1 : ((((toBits a va).toNat + 2 ^ (8 * a.bytes) * (toBits b vb).toNat : Nat) : Int)) /
      (256 : Int) ^ a.bytes = ((toBits b vb).toNat : Int) := by
    push_cast
    rw [← hp, Int.mul_comm ((256 : Int) ^ a.bytes), Int.add_mul_ediv_right _ _ (Int.ne_of_gt hp_pos),
      Int.ediv_eq_zero_of_lt (Int.natCast_nonneg _) ha_lt, Int.zero_add]
  have hleft : Int.toBytes a.bytes ((toBits a va).toNat : Int) =
      Int.toBytes a.bytes ((((toBits a va).toNat + 2 ^ (8 * a.bytes) * (toBits b vb).toNat : Nat) : Int)) := by
    conv => rhs; rw [← Int.toBytes_emod a.bytes]
    dsimp only [Int.take]
    rw [hmod1]
  rw [hleft, hdiv1]

private theorem emitLoadChunk64_wp (c byteOff : Nat) (hc64 : 8 * c ≤ 64)
    {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {ptr : Arg Val i64} {chunkVal : BitVec (8 * c)}
    (hLoadChunk : loadVal m (.bits (8 * c)) (ptr.val + BitVec.ofNat 64 byteOff) = some chunkVal)
    (cont : Arg Val i64 → Expr Val Cont rs)
    (hk : ∀ wd : Arg Val i64, wd.val = chunkVal.setWidth 64 → wp Γ Q X (cont wd) m) :
    wp Γ Q X
      (if byteOff == 0 then
        Expr.load (.bits (8 * c)) ptr fun raw =>
          if h : 8 * c = 64 then cont (castArgBits h (.var raw))
          else if 8 * c < 64 then Expr.let_ (op1 (OpCode.zext (8 * c) 64) (.var raw)) fun (z, _) => cont (.var z)
          else Expr.let_ (op1 (OpCode.trunc (8 * c) 64) (.var raw)) fun (z, _) => cont (.var z)
       else
        Expr.let_ (op2 (OpCode.add i64) ptr (.imm (BitVec.ofNat 64 byteOff))) fun (ap, _) =>
          Expr.load (.bits (8 * c)) (.var ap) fun raw =>
            if h : 8 * c = 64 then cont (castArgBits h (.var raw))
            else if 8 * c < 64 then Expr.let_ (op1 (OpCode.zext (8 * c) 64) (.var raw)) fun (z, _) => cont (.var z)
            else Expr.let_ (op1 (OpCode.trunc (8 * c) 64) (.var raw)) fun (z, _) => cont (.var z)) m := by
  have hStep : ∀ ap : Arg Val i64, ap.val = ptr.val + BitVec.ofNat 64 byteOff →
      wp Γ Q X (Expr.load (.bits (8 * c)) ap fun raw =>
        if h : 8 * c = 64 then cont (castArgBits h (.var raw))
        else if 8 * c < 64 then Expr.let_ (op1 (OpCode.zext (8 * c) 64) (.var raw)) fun (z, _) => cont (.var z)
        else Expr.let_ (op1 (OpCode.trunc (8 * c) 64) (.var raw)) fun (z, _) => cont (.var z)) m := by
    intro ap hap
    rw [wp_load, hap]
    refine ⟨chunkVal, hLoadChunk, ?_⟩
    by_cases heq : 8 * c = 64
    · simp only [heq, ↓reduceDIte]
      apply hk (castArgBits heq (.var chunkVal))
      rw [val_castArgBits, Arg.val_var, cast_eq_setWidth heq]
    · have hlt : 8 * c < 64 := by omega
      simp only [heq, hlt, ↓reduceDIte, ↓reduceIte, wp, Op.wp, op1, vals, OpCode.wp_zext]
      exact ⟨Nat.le_of_lt hlt, hk (.var _) rfl⟩
  by_cases hb0 : byteOff = 0
  · simp only [hb0, beq_self_eq_true, ↓reduceIte]
    subst hb0
    exact hStep ptr (by simp)
  · have hne : (byteOff == 0) = false := beq_false_of_ne hb0
    simp only [hne, Bool.false_eq_true, ↓reduceIte, wp, Op.wp, op2, vals, OpCode.wp_add,
      Ty.hasFloat, Bool.false_eq_true, lift2, Arg.val_imm]
    exact hStep (.var _) rfl

private theorem loadByteChunksToWords64_wp (target : LegalTarget) (_hv : target.valid = true)
    {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {bTotal : Nat}
    {m : Mem 64} {ptr : Arg Val i64} {bs : List UInt8}
    (hMem : m.loadBytes ptr.val bTotal = some bs) :
    ∀ (cs : List Nat) (byteOff : Nat)
      (ws : List (Arg Val i64)) (acc : Arg Val i64) (accBits : Nat),
      (∀ c ∈ cs, 0 < c ∧ 8 * c ∈ target.bitWidths ∧ 8 * c ≤ 64) →
      byteOff + cs.sum = bTotal →
      Words64Stream ws acc accBits (8 * byteOff)
        (fun i => (BitVec.ofInt (8 * bTotal) (Int.ofBytes bs)).getLsbD i) →
      ∀ {k : List (Arg Val i64) → Expr Val Cont rs},
        (∀ words : List (Arg Val i64),
          (∀ i, i < 8 * bTotal →
            words64GetLsb words i = (BitVec.ofInt (8 * bTotal) (Int.ofBytes bs)).getLsbD i) →
          wp Γ Q X (k words) m) →
        wp Γ Q X (loadByteChunksToWords64 ptr byteOff cs ws acc accBits k) m
  | [], byteOff, ws, acc, accBits, _, hsum, hS, k, hk => by
    simp only [List.sum_nil, Nat.add_zero] at hsum
    subst hsum
    rw [loadByteChunksToWords64.eq_1]
    have ⟨hBits, _, _⟩ := Words64Stream.finish hS
    by_cases h0 : accBits = 0
    · simp only [h0, beq_self_eq_true, ↓reduceIte] at hBits ⊢
      exact hk ws hBits
    · have hne : (accBits == 0) = false := beq_false_of_ne h0
      simp only [hne, Bool.false_eq_true, ↓reduceIte] at hBits ⊢
      exact hk (ws ++ [acc]) hBits
  | c :: rest, byteOff, ws, acc, accBits, hcs, hsum, hS, k, hk => by
    have hcmem := hcs c List.mem_cons_self
    have hc_pos : 0 < c := hcmem.1
    have hcw64 : 8 * c ≤ 64 := hcmem.2.2
    have hsum' : byteOff + (c + rest.sum) = bTotal := by simpa [List.sum_cons] using hsum
    have hMem_rw : m.loadBytes ptr.val (byteOff + (c + rest.sum)) = some bs := by rwa [hsum']
    obtain ⟨bs1, bs2, bs3, rfl, hl1, hl2, hl3, _h1, h2, _h3⟩ := memWp_loadBytes_split3 hMem_rw
    have hLoadChunk : loadVal m (.bits (8 * c)) (ptr.val + BitVec.ofNat 64 byteOff) =
        some (BitVec.ofInt (8 * c) (Int.ofBytes bs2)) := by
      apply memWp_loadVal_bits_of_loadBytes
      simpa [Ty.bytes, Ty.size, show (8 * c + 7) / 8 = c by omega] using h2
    rw [loadByteChunksToWords64.eq_2]
    dsimp only
    refine emitLoadChunk64_wp c byteOff hcw64 hLoadChunk
      (fun wd => pushLeafWord64 (min (8 * c) 64) wd ws acc accBits fun ws' acc' bits' =>
        loadByteChunksToWords64 ptr (byteOff + c) rest ws' acc' bits' k)
      fun wd hwd => ?_
    refine pushLeafWord64_wp (by omega) hS ?_ (fun _ _ => rfl) ?_ ?_
    · intro j hj
      rw [hwd, BitVec.getLsbD_setWidth]
      have hge : 8 * c ≤ j := by omega
      simp [BitVec.getLsbD_of_ge _ j hge]
    · intro j hj
      have hjc : j < 8 * c := by omega
      rw [hwd, BitVec.getLsbD_setWidth, decide_eq_true (by omega), Bool.true_and]
      have hsp1 := memWp_getLsbD_ofInt_ofBytes_append (byteOff + (c + rest.sum)) bs1 (bs2 ++ bs3)
        (by simp [hl1, hl2, hl3]) (8 * byteOff + j)
      rw [hsum', hl1] at hsp1
      have hnot_lo : ¬ (8 * byteOff + j < 8 * byteOff) := by omega
      rw [hsp1, ite_eq_right hnot_lo]
      have hsp2 := memWp_getLsbD_ofInt_ofBytes_append ((bs2 ++ bs3).length) bs2 bs3
        List.length_append.symm ((8 * byteOff + j) - 8 * byteOff)
      rw [List.length_append, hl2, hl3] at hsp2 ⊢
      rw [Nat.add_sub_cancel_left] at hsp2 ⊢
      rw [hsp2, ite_eq_left hjc]
    · intro ws' acc' accBits' hS'
      rw [show 8 * byteOff + min (8 * c) 64 = 8 * (byteOff + c) by omega] at hS'
      exact loadByteChunksToWords64_wp target _hv hMem rest (byteOff + c) ws' acc' accBits'
        (fun x hx => hcs x (List.mem_cons_of_mem _ hx)) (by omega) hS' hk

private theorem storeByteChunksFromWords64_wp (target : LegalTarget) (_hv : target.valid = true)
    {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {bTotal : Nat} (hb_le : bTotal ≤ 2 ^ 64)
    (words : List (Arg Val i64)) (vec : BitVec (8 * bTotal))
    (hWords : ∀ i, i < 8 * bTotal → words64GetLsb words i = vec.getLsbD i)
    (ptr : Arg Val i64) (k : Expr Val Cont rs) :
    ∀ (cs : List Nat) (byteOff : Nat) (m : Mem 64),
      (∀ c ∈ cs, 0 < c ∧ 8 * c ∈ target.bitWidths ∧ 8 * c ≤ 64) →
      byteOff + cs.sum = bTotal →
      (∃ bs, m.loadBytes (ptr.val + BitVec.ofNat 64 byteOff) cs.sum = some bs) →
      wp Γ Q X k (m.storeBytes (ptr.val + BitVec.ofNat 64 byteOff)
        (Int.toBytes cs.sum ((vec.toNat : Int) / (256 : Int) ^ byteOff))) →
      wp Γ Q X (storeByteChunksFromWords64 words ptr byteOff cs k) m
  | [], byteOff, m, _, _, _, hk => by
    rw [storeByteChunksFromWords64.eq_1]
    simpa [List.sum_nil, Int.toBytes, memWp_storeBytes_nil] using hk
  | c :: rest, byteOff, m, hcs, hsum, hOk, hk => by
    have hcmem := hcs c List.mem_cons_self
    have hc_pos : 0 < c := hcmem.1
    have hcw64 : 8 * c ≤ 64 := hcmem.2.2
    have hsum' : byteOff + (c + rest.sum) = bTotal := by simpa [List.sum_cons] using hsum
    rcases hOk with ⟨bs, hLoad⟩
    rw [List.sum_cons, memWp_loadBytes_add] at hLoad
    rcases hLoad with ⟨bs1, bs2, hLoadC, hLoadRest, _⟩
    have hOkC : storeOk m (.bits (8 * c)) (ptr.val + BitVec.ofNat 64 byteOff) := by
      apply memWp_storeOk_of_loadBytes
      simpa [Ty.bytes, Ty.size, show (8 * c + 7) / 8 = c by omega] using hLoadC
    rw [storeByteChunksFromWords64.eq_2]
    dsimp only
    refine extractBitsFromWords64_wp (by omega)
      (bits := fun j => vec.getLsbD (8 * byteOff + j))
      (fun j hj => hWords (8 * byteOff + j) (by omega))
      fun raw hRaw => ?_
    have hToCw : ∀ (cont : Arg Val (.bits (8 * c)) → Expr Val Cont rs),
        (∀ val : Arg Val (.bits (8 * c)),
          val.val = (vec >>> (8 * byteOff)).setWidth (8 * c) → wp Γ Q X (cont val) m) →
        wp Γ Q X (if h : 8 * c = 64 then cont (castArgBits h.symm raw)
          else if 8 * c < 64 then Expr.let_ (op1 (OpCode.trunc 64 (8 * c)) raw) fun (tr, _) => cont (.var tr)
          else Expr.let_ (op1 (OpCode.zext 64 (8 * c)) raw) fun (tr, _) => cont (.var tr)) m := by
      intro cont hcont
      by_cases heq : 8 * c = 64
      · simp only [heq, ↓reduceDIte]
        apply hcont (castArgBits heq.symm raw)
        rw [val_castArgBits, cast_eq_setWidth heq.symm]
        apply BitVec.eq_of_getLsbD_eq
        intro j hj
        have hmin : j < min (8 * c) 64 := by omega
        rw [BitVec.getLsbD_setWidth, decide_eq_true hj, Bool.true_and, hRaw j,
          BitVec.getLsbD_setWidth, decide_eq_true hj, Bool.true_and, BitVec.getLsbD_ushiftRight]
        simp [hmin]
      · have hlt : 8 * c < 64 := by omega
        simp only [heq, hlt, ↓reduceDIte, ↓reduceIte, wp, Op.wp, op1, vals, OpCode.wp_trunc]
        refine ⟨Nat.le_of_lt hlt, hcont (.var _) ?_⟩
        apply BitVec.eq_of_getLsbD_eq
        intro j hj
        have hmin : j < min (8 * c) 64 := by omega
        dsimp only [Arg.val_var]
        rw [BitVec.getLsbD_setWidth, decide_eq_true hj, Bool.true_and, hRaw j,
          BitVec.getLsbD_setWidth, decide_eq_true hj, Bool.true_and, BitVec.getLsbD_ushiftRight]
        simp [hmin]
    refine hToCw (fun val =>
      if byteOff == 0 then
        Expr.store (t := .bits (8 * c)) val ptr (storeByteChunksFromWords64 words ptr (byteOff + c) rest k)
      else
        Expr.let_ (op2 (OpCode.add i64) ptr (.imm (BitVec.ofNat 64 byteOff))) fun (ap, _) =>
          Expr.store (t := .bits (8 * c)) val (.var ap) (storeByteChunksFromWords64 words ptr (byteOff + c) rest k))
      fun val hval => ?_
    have hAddr : ∀ (cont : Arg Val i64 → Expr Val Cont rs),
        (∀ ap : Arg Val i64, ap.val = ptr.val + BitVec.ofNat 64 byteOff → wp Γ Q X (cont ap) m) →
        wp Γ Q X (if byteOff == 0 then cont ptr
          else Expr.let_ (op2 (OpCode.add i64) ptr (.imm (BitVec.ofNat 64 byteOff))) fun (ap, _) => cont (.var ap)) m := by
      intro cont hcont
      by_cases hb0 : byteOff = 0
      · simp only [hb0, beq_self_eq_true, ↓reduceIte]
        subst hb0
        exact hcont ptr (by simp)
      · have hne : (byteOff == 0) = false := beq_false_of_ne hb0
        simp only [hne, Bool.false_eq_true, ↓reduceIte, wp, Op.wp, op2, vals, OpCode.wp_add,
          Ty.hasFloat, Bool.false_eq_true, lift2, Arg.val_imm]
        exact hcont (.var _) rfl
    refine hAddr (fun ap => .store (t := .bits (8 * c)) val ap (storeByteChunksFromWords64 words ptr (byteOff + c) rest k))
      fun ap hap => ?_
    rw [wp_store, hap]
    refine ⟨hOkC, ?_⟩
    have hbytes_eq : Int.toBytes c (((val.val : BitVec (8 * c)).setWidth (8 * (Ty.bits (8 * c)).bytes)).toInt) =
        Int.toBytes c ((vec.toNat : Int) / (256 : Int) ^ byteOff) := by
      have hbw : (Ty.bits (8 * c)).bytes = c := by simp [Ty.bytes, Ty.size]; omega
      rw [hbw, BitVec.setWidth_eq, hval]
      exact memWp_int_toBytes_shift (by omega) vec
    have hm' : storeMem m (.bits (8 * c)) (ptr.val + BitVec.ofNat 64 byteOff) val.val =
        m.storeBytes (ptr.val + BitVec.ofNat 64 byteOff)
          (Int.toBytes c ((vec.toNat : Int) / (256 : Int) ^ byteOff)) := by
      simp only [storeMem, Mem.storeInt, toBits,
        show (Ty.bits (8 * c)).bytes = c by simp [Ty.bytes, Ty.size]; omega]
      exact congrArg (m.storeBytes (ptr.val + BitVec.ofNat 64 byteOff)) hbytes_eq
    rw [hm']
    have ha_rest : (ptr.val + BitVec.ofNat 64 byteOff) + BitVec.ofNat 64 c =
        ptr.val + BitVec.ofNat 64 (byteOff + c) := by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    have hOkRest : ∃ bs', (m.storeBytes (ptr.val + BitVec.ofNat 64 byteOff)
        (Int.toBytes c ((vec.toNat : Int) / (256 : Int) ^ byteOff))).loadBytes
        (ptr.val + BitVec.ofNat 64 (byteOff + c)) rest.sum = some bs' := by
      apply memWp_loadBytes_isSome_storeBytes
      rw [← ha_rest]
      exact ⟨bs2, hLoadRest⟩
    refine storeByteChunksFromWords64_wp target _hv hb_le words vec hWords ptr k rest (byteOff + c) _
      (fun x hx => hcs x (List.mem_cons_of_mem _ hx)) (by omega) hOkRest ?_
    have hlen_le : (Int.toBytes c ((vec.toNat : Int) / (256 : Int) ^ byteOff)).length +
        (Int.toBytes rest.sum ((vec.toNat : Int) / (256 : Int) ^ (byteOff + c))).length ≤ 2 ^ 64 := by
      rw [Int.toBytes_length, Int.toBytes_length]; omega
    have ha_len : (ptr.val + BitVec.ofNat 64 byteOff) +
        BitVec.ofNat 64 (Int.toBytes c ((vec.toNat : Int) / (256 : Int) ^ byteOff)).length =
        ptr.val + BitVec.ofNat 64 (byteOff + c) := by
      rw [Int.toBytes_length, ha_rest]
    rw [← ha_len, ← memWp_storeBytes_append m (ptr.val + BitVec.ofNat 64 byteOff) _ _ hlen_le]
    have hAddBytes :
        Int.toBytes c ((vec.toNat : Int) / (256 : Int) ^ byteOff) ++
          Int.toBytes rest.sum ((vec.toNat : Int) / (256 : Int) ^ (byteOff + c)) =
        Int.toBytes (c + rest.sum) ((vec.toNat : Int) / (256 : Int) ^ byteOff) := by
      rw [memWp_int_toBytes_add c rest.sum ((vec.toNat : Int) / (256 : Int) ^ byteOff)]
      congr 2
      have hdiv : ((vec.toNat : Int) / (256 : Int) ^ byteOff) / (256 : Int) ^ c =
          (vec.toNat : Int) / (256 : Int) ^ (byteOff + c) := by
        rw [Int.pow_add]
        exact (Int.ediv_ediv_of_nonneg (Int.pow_nonneg (by decide)))
      exact hdiv.symm
    rw [hAddBytes]
    simpa [List.sum_cons] using hk

private theorem legalLoad_wp (target : LegalTarget) (hv : target.valid = true)
    {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} :
    ∀ (t : Ty), target.supportsTy t = true → t.bytes ≤ 2 ^ 64 →
      ∀ {m : Mem 64} {ptr : Arg Val i64} {v : Val t},
        loadVal m t ptr.val = some v →
        ∀ {k : LVar target Val t → Expr Val Cont rs},
          (∀ r : LVar target Val t, valsTup r = encodeVal target t v → wp Γ Q X (k r) m) →
          wp Γ Q X (legalLoad target t ptr k) m
  | .bool, _, _, m, ptr, v, hLoad, k, hk => by
    rw [legalLoad.eq_1, wp_load]
    exact ⟨v, hLoad, hk _ (by dsimp only [LegalTarget.legalTys, encodeVal]; rw [valsTup_single]; rfl)⟩
  | .bits n, hSup, _, m, ptr, v, hLoad, k, hk => by
    rw [legalLoad.eq_2]
    dsimp only
    by_cases hnw : n = target.widenWidth n
    · have hbeq : (n == target.widenWidth n) = true := beq_iff_eq.mpr hnw
      simp only [hbeq, ↓reduceIte]
      rw [wp_load]
      have hW : ∀ (w : Nat) (h : n = w), loadVal m (.bits w) ptr.val = some (h ▸ v) :=
        fun _ h => by cases h; exact hLoad
      refine ⟨hnw ▸ v, hW (target.widenWidth n) hnw, ?_⟩
      apply hk (.var _, ())
      dsimp only [LegalTarget.legalTys, encodeVal]
      rw [valsTup_single]
      refine congrArg (·, ()) ?_
      dsimp only [Arg.val_var]
      rw [cast_eq_setWidth hnw]
    · have hne : (n == target.widenWidth n) = false := beq_false_of_ne hnw
      simp only [hne, Bool.false_eq_true, ↓reduceIte]
      refine emitLoadBits_wp target hv hSup hnw hLoad fun r hr => ?_
      apply hk (r, ())
      dsimp only [LegalTarget.legalTys, encodeVal]
      rw [valsTup_single]
      exact congrArg (·, ()) hr
  | .float f, _, _, m, ptr, v, hLoad, k, hk => by
    rw [legalLoad.eq_3, wp_load]
    exact ⟨v, hLoad, hk _ (by dsimp only [LegalTarget.legalTys, encodeVal]; rw [valsTup_single]; rfl)⟩
  | .pair a b, hSup, hble, m, ptr, v, hLoad, k, hk => by
    rw [legalLoad.eq_4]
    dsimp only
    by_cases hp : target.keepsPacked (.pair a b) = true
    · simp only [hp, ↓reduceDIte, wp_load]
      refine ⟨v, hLoad, hk _ (valsTup_tupToPacked_encode target hp (by rw [valsTup_single]; rfl))⟩
    · have hf : target.keepsPacked (.pair a b) = false := Bool.eq_false_iff.mpr hp
      rw [dite_eq_right hp]
      have hSupPair : target.supportsTy a = true ∧ target.supportsTy b = true := by
        simpa [LegalTarget.supportsTy] using hSup
      by_cases hba : (a.pair b).isByteAlignedStruct = true
      · simp only [hba, ↓reduceIte]
        obtain ⟨_ha, _hb, hbytes, _, _, hapos, _⟩ := bytes_pair_of_isByteAlignedStruct hba
        obtain ⟨hLa, hLb⟩ := loadVal_pair_of_isByteAlignedStruct hba hLoad
        refine legalLoad_wp target hv a hSupPair.1 (by omega) hLa fun la hla => ?_
        have hane : (a.bytes == 0) = false := beq_false_of_ne (by omega)
        simp only [hane, Bool.false_eq_true, ↓reduceIte, wp, Op.wp, op2, vals, OpCode.wp_add,
          Ty.hasFloat, Bool.false_eq_true, lift2, Arg.val_imm]
        refine legalLoad_wp target hv b hSupPair.2 (by omega) (ptr := .var _) hLb fun lb hlb => ?_
        exact hk _ (valsTup_tupToSplit_encode target hf (by rw [valsTup_tupAppend, hla, hlb]))
      · simp only [hba, Bool.false_eq_true, ↓reduceIte]
        by_cases hbc0 : (a.pair b).bytes = 0
        · have hbe : ((a.pair b).bytes == 0) = true := beq_iff_eq.mpr hbc0
          simp only [hbe, ↓reduceIte]
          have hsz0 : (a.pair b).size = 0 := by simp only [Ty.bytes] at hbc0; omega
          refine unpackWords64ToLeaves_wp target hv (.pair a b) hSup (words := []) (off := 0) (v := v)
            (fun i hi => by omega) fun fres hfres => ?_
          exact packLeavesToLegal_wp target (.pair a b) hSup fres v hfres hk
        · have hbe : ((a.pair b).bytes == 0) = false := beq_false_of_ne hbc0
          simp only [hbe, Bool.false_eq_true, ↓reduceIte]
          have hLoadRaw := hLoad
          simp only [loadVal, Mem.loadInt, Option.bind_eq_some_iff, Option.map_eq_some_iff,
            Option.some.injEq] at hLoadRaw
          rcases hLoadRaw with ⟨i, ⟨bs, hMem, rfl⟩, rfl⟩
          obtain ⟨hcs, hsum⟩ := memWp_chunkBytes_pos_of_valid target hv (a.pair b).bytes
          have hS0 : Words64Stream ([] : List (Arg Val i64)) (.imm 0#64) 0 (8 * 0)
              (fun i => (BitVec.ofInt (8 * (a.pair b).bytes) (Int.ofBytes bs)).getLsbD i) :=
            ⟨by omega, by simp, fun _ _ => by simp, fun i hi => by simp at hi, fun j hj => by omega⟩
          refine loadByteChunksToWords64_wp target hv hMem (chunkBytes target.bitWidths (a.pair b).bytes) 0
            [] (.imm 0#64) 0 hcs (by omega) hS0 fun words hWords => ?_
          refine unpackWords64ToLeaves_wp target hv (.pair a b) hSup (words := words) (off := 0)
            (v := ofBits (.pair a b) (BitVec.ofInt (a.size + b.size) (Int.ofBytes bs))) ?_
            fun fres hfres => ?_
          · intro j hj
            rw [Nat.zero_add, hWords j (by simp only [Ty.bytes] at *; omega)]
            rw [toBits_ofBits]
            have h0 := Int.ofBytes_ge_zero bs
            rw [memWp_getLsbD_ofInt_nonneg h0, memWp_getLsbD_ofInt_nonneg h0]
            have hj1 : j < a.size + b.size := by simpa [Ty.size] using hj
            have hj2 : j < 8 * (a.pair b).bytes := by simp only [Ty.bytes, Ty.size] at *; omega
            simp [hj1, hj2]
          · exact packLeavesToLegal_wp target (.pair a b) hSup fres _ hfres hk

private theorem legalStore_wp (target : LegalTarget) (hv : target.valid = true)
    {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} :
    ∀ (t : Ty), target.supportsTy t = true → t.bytes ≤ 2 ^ 64 →
      ∀ {m : Mem 64} {xs : LVar target Val t} {ptr : Arg Val i64} {v : Val t},
        valsTup xs = encodeVal target t v →
        storeOk m t ptr.val →
        ∀ {k : Expr Val Cont rs},
          wp Γ Q X k (storeMem m t ptr.val v) →
          wp Γ Q X (legalStore target t xs ptr k) m
  | .bool, _, _, m, (vx, ()), ptr, v, hxs, hOk, k, hk => by
    dsimp only [encodeVal, LegalTarget.legalTys] at hxs
    rw [valsTup_single] at hxs
    have hvx : vx.val = v := congrArg Prod.fst hxs
    rw [legalStore.eq_1, wp_store, hvx]
    exact ⟨hOk, hk⟩
  | .bits n, hSup, _, m, (vx, ()), ptr, v, hxs, hOk, k, hk => by
    dsimp only [encodeVal, LegalTarget.legalTys] at hxs
    rw [valsTup_single] at hxs
    have hvx : vx.val = v.setWidth (target.widenWidth n) := congrArg Prod.fst hxs
    rw [legalStore.eq_2]
    dsimp only
    by_cases hnw : n = target.widenWidth n
    · have hbeq : (n == target.widenWidth n) = true := beq_iff_eq.mpr hnw
      simp only [hbeq, ↓reduceIte]
      rw [wp_store]
      have hW : ∀ (w : Nat) (h : n = w) (vx' : Arg Val (.bits w)), vx'.val = v.setWidth w →
          storeOk m (.bits w) ptr.val ∧ wp Γ Q X k (storeMem m (.bits w) ptr.val vx'.val) := by
        intro w h vx' hvx'
        cases h
        simpa [BitVec.setWidth_eq, hvx'] using ⟨hOk, hk⟩
      exact hW (target.widenWidth n) hnw vx hvx
    · have hne : (n == target.widenWidth n) = false := beq_false_of_ne hnw
      simp only [hne, Bool.false_eq_true, ↓reduceIte]
      exact emitStoreBits_wp target hv hSup hnw hvx hOk hk
  | .float f, _, _, m, (vx, ()), ptr, v, hxs, hOk, k, hk => by
    dsimp only [encodeVal, LegalTarget.legalTys] at hxs
    rw [valsTup_single] at hxs
    have hvx : vx.val = v := congrArg Prod.fst hxs
    rw [legalStore.eq_3, wp_store, hvx]
    exact ⟨hOk, hk⟩
  | .pair a b, hSup, hble, m, xs, ptr, (va, vb), hxs, hOk, k, hk => by
    rw [legalStore.eq_4]
    dsimp only
    by_cases hp : target.keepsPacked (.pair a b) = true
    · simp only [hp, ↓reduceDIte, wp_store]
      have hpx := valsTup_packedToTup_encode target hp hxs
      dsimp only [valsTup] at hpx
      have hfst : (packedToTup hp xs).fst.val = (va, vb) := congrArg Prod.fst hpx
      rw [hfst]
      exact ⟨hOk, hk⟩
    · have hf : target.keepsPacked (.pair a b) = false := Bool.eq_false_iff.mpr hp
      rw [dite_eq_right hp]
      have hSupPair : target.supportsTy a = true ∧ target.supportsTy b = true := by
        simpa [LegalTarget.supportsTy] using hSup
      by_cases hba : (a.pair b).isByteAlignedStruct = true
      · simp only [hba, ↓reduceIte]
        obtain ⟨_ha, _hb, hbytes, _, _, hapos, _⟩ := bytes_pair_of_isByteAlignedStruct hba
        obtain ⟨hOkA, hOkB⟩ := storeOk_pair_of_isByteAlignedStruct hba hOk
        have hsp := valsTup_splitToTup_encode target hf hxs
        replace hsp := congrArg tupSplit hsp
        rw [tupSplit_valsTup] at hsp
        have hla : valsTup (tupSplit (splitToTup hf xs)).1 = encodeVal target a va := by
          have := congrArg Prod.fst hsp
          simpa [tupSplit_tupAppend] using this
        have hlb : valsTup (tupSplit (splitToTup hf xs)).2 = encodeVal target b vb := by
          have := congrArg Prod.snd hsp
          simpa [tupSplit_tupAppend] using this
        refine legalStore_wp target hv a hSupPair.1 (by omega) hla hOkA ?_
        have hane : (a.bytes == 0) = false := beq_false_of_ne (by omega)
        simp only [hane, Bool.false_eq_true, ↓reduceIte, wp, Op.wp, op2, vals, OpCode.wp_add,
          Ty.hasFloat, Bool.false_eq_true, lift2, Arg.val_imm]
        refine legalStore_wp target hv b hSupPair.2 (by omega) (ptr := .var _) hlb (hOkB va) ?_
        dsimp only [Arg.val_var]
        rwa [storeMem_pair_of_isByteAlignedStruct hba hble va vb]
      · simp only [hba, Bool.false_eq_true, ↓reduceIte]
        by_cases hbc0 : (a.pair b).bytes = 0
        · have hbe : ((a.pair b).bytes == 0) = true := beq_iff_eq.mpr hbc0
          simp only [hbe, ↓reduceIte]
          simpa [storeMem, Mem.storeInt, hbc0, Int.toBytes, memWp_storeBytes_nil] using hk
        · have hbe : ((a.pair b).bytes == 0) = false := beq_false_of_ne hbc0
          simp only [hbe, Bool.false_eq_true, ↓reduceIte]
          refine splitLegalToLeaves_wp target (.pair a b) hSup xs (va, vb) hxs fun fx hfx => ?_
          refine packLeavesToWords64_wp_all target hv (.pair a b) hSup hfx fun words hWords _ _ => ?_
          obtain ⟨bs, hLoad⟩ := memWp_storeOk_iff_exists_loadBytes.mp hOk
          obtain ⟨hcs, hsum⟩ := memWp_chunkBytes_pos_of_valid target hv (a.pair b).bytes
          let vec : BitVec (8 * (a.pair b).bytes) := (toBits (.pair a b) (va, vb)).setWidth (8 * (a.pair b).bytes)
          refine storeByteChunksFromWords64_wp target hv hble words vec ?_ ptr k
            (chunkBytes target.bitWidths (a.pair b).bytes) 0 m hcs (by omega)
            ⟨bs, by simpa [BitVec.add_zero, hsum] using hLoad⟩ ?_
          · intro j hj
            rw [hWords j]
            simp only [vec, BitVec.getLsbD_setWidth, decide_eq_true hj, Bool.true_and]
            by_cases hjs : j < (a.pair b).size
            · simp [hjs]
            · simp only [hjs, ↓reduceIte]
              exact (BitVec.getLsbD_of_ge _ _ (by omega)).symm
          · simp only [BitVec.add_zero, hsum, Int.pow_zero, Int.ediv_one]
            rw [← memWp_int_toBytes_bitVec_toNat (a.pair b).bytes (8 * (a.pair b).bytes) (by omega) vec]
            have hsw : vec.setWidth (8 * (a.pair b).bytes) = (toBits (.pair a b) (va, vb)).setWidth (8 * (a.pair b).bytes) := by
              simp only [vec, BitVec.setWidth_eq]
            rw [hsw]
            simpa [storeMem, Mem.storeInt] using hk

/-! ### Source support reification, `legalExpr_wp`, `Func.legal_wp`, `Func.legal_spec` -/

private inductive ExprSupports (target : LegalTarget) : {rs : List Ty} → Expr Val Cont rs → Prop
  | let_ {rs ts : List Ty} (op : Op Val ts) (k : Tup Val ts → Expr Val Cont rs) :
    target.supportsOpCode op.code = true →
    (∀ xs, ExprSupports target (k xs)) →
    ExprSupports target (.let_ op k)
  | load {rs : List Ty} (t : Ty) (a : Arg Val i64) (k : Val t → Expr Val Cont rs) :
    target.supportsTy t = true → t.bytes ≤ 2 ^ 64 →
    (∀ v, ExprSupports target (k v)) →
    ExprSupports target (.load t a k)
  | store {rs : List Ty} {t : Ty} (v : Arg Val t) (a : Arg Val i64) (k : Expr Val Cont rs) :
    target.supportsTy t = true → t.bytes ≤ 2 ^ 64 →
    ExprSupports target k →
    ExprSupports target (.store v a k)
  | call {rs as bs : List Ty} (f : Sym) (args : Tup (Arg Val) as) (k : Tup Val bs → Expr Val Cont rs) :
    as.all target.supportsTy = true → bs.all target.supportsTy = true →
    (∀ xs, ExprSupports target (k xs)) →
    ExprSupports target (.call f args k)
  | jnz {rs : List Ty} (c : Arg Val .bool) (t e : Expr Val Cont rs) :
    ExprSupports target t → ExprSupports target e →
    ExprSupports target (.jnz c t e)
  | jump {rs ts : List Ty} (j : Cont ts) (args : Tup (Arg Val) ts) :
    ts.all target.supportsTy = true →
    ExprSupports target (.jump j args)
  | ret {rs : List Ty} (vs : Tup (Arg Val) rs) :
    rs.all target.supportsTy = true →
    ExprSupports target (.ret vs)
  | exit {rs as : List Ty} (f : Sym) (args : Tup (Arg Val) as) :
    as.all target.supportsTy = true →
    ExprSupports target (.exit f args)
  | hlt {rs : List Ty} :
    ExprSupports target (.hlt (rs := rs))
  | group {rs : List Ty} {sig : List (List Ty)}
      (bodies : Tup Cont sig → Blocks Val Cont rs sig)
      (k : Tup Cont sig → Expr Val Cont rs) :
    (sig.all (·.all target.supportsTy)) = true →
    (∀ Js {ts} (i : Member ts sig) xs, ExprSupports target ((bodies Js).get i xs)) →
    (∀ Js, ExprSupports target (k Js)) →
    ExprSupports target (.group bodies k)

private theorem exprSupports_of_wf_toTFlat (target : LegalTarget) :
    {rs : List Ty} → {G : Ctx K Val} → {D : Ctx KL Cont} →
    {eK : Expr K KL rs} → {eV : Expr Val Cont rs} →
    Wf G D eK eV →
    ∀ nv nl, (toTFlat eK nv nl).supportsSource target = true → ExprSupports target eV := by
  intro rs G D eK eV hwf
  induction hwf using Wf.induct with
  | @let_ G D ts op₁ op₂ k₁ k₂ hop hk ih =>
    intro nv nl hs
    rw [toTFlat.eq_1] at hs
    simp only [TFlat.supportsSource, Bool.and_eq_true] at hs
    rcases hop with ⟨code, _⟩
    exact ExprSupports.let_ _ k₂ hs.1 fun xs =>
      ih (Tup.levels ts nv) xs (nv + ts.length) nl hs.2
  | @load G D t a₁ a₂ k₁ k₂ ha hk ih =>
    intro nv nl hs
    rw [toTFlat.eq_2] at hs
    simp only [TFlat.supportsSource, Bool.and_eq_true, decide_eq_true_eq] at hs
    exact ExprSupports.load t a₂ k₂ hs.1.1 hs.1.2 fun v => ih nv v (nv + 1) nl hs.2
  | @store G D t v₁ v₂ a₁ a₂ k₁ k₂ hv ha hk ih =>
    intro nv nl hs
    rw [toTFlat.eq_3] at hs
    simp only [TFlat.supportsSource, Bool.and_eq_true, decide_eq_true_eq] at hs
    exact ExprSupports.store v₂ a₂ k₂ hs.1.1 hs.1.2 (ih nv nl hs.2)
  | @call G D f as bs args₁ args₂ k₁ k₂ hargs hk ih =>
    intro nv nl hs
    rw [toTFlat.eq_4] at hs
    simp only [TFlat.supportsSource, Bool.and_eq_true] at hs
    exact ExprSupports.call f args₂ k₂ hs.1.1 hs.1.2 fun xs =>
      ih (Tup.levels bs nv) xs (nv + bs.length) nl hs.2
  | @jnz G D c₁ c₂ t₁ t₂ e₁ e₂ hc ht he iht ihe =>
    intro nv nl hs
    rw [toTFlat.eq_5] at hs
    simp only [TFlat.supportsSource, Bool.and_eq_true] at hs
    exact ExprSupports.jnz c₂ t₂ e₂ (iht nv nl hs.1) (ihe nv nl hs.2)
  | @jump G D ts j₁ j₂ args₁ args₂ hj hargs =>
    intro nv nl hs
    rw [toTFlat.eq_6] at hs
    simp only [TFlat.supportsSource] at hs
    exact ExprSupports.jump (rs := rs) j₂ args₂ hs
  | @ret G D vs₁ vs₂ hvs =>
    intro nv nl hs
    rw [toTFlat.eq_7] at hs
    simp only [TFlat.supportsSource] at hs
    exact ExprSupports.ret vs₂ hs
  | @exit G D f as args₁ args₂ hargs =>
    intro nv nl hs
    rw [toTFlat.eq_8] at hs
    simp only [TFlat.supportsSource] at hs
    exact ExprSupports.exit (rs := rs) f args₂ hs
  | @hlt G D =>
    intro _ _ _
    exact ExprSupports.hlt
  | @group G D sig b₁ b₂ k₁ k₂ hb hk ihb ihk =>
    intro nv nl hs
    rw [toTFlat.eq_10] at hs
    dsimp only at hs
    simp only [TFlat.supportsSource, Bool.and_eq_true] at hs
    refine ExprSupports.group b₂ k₂ hs.1.1 (fun Js ts i xs => ?_) (fun Js => ?_)
    · have hget := toTBlocks_get target (b₁ (Tup.levels sig nl)) i nv (nl + sig.length) hs.1.2
      exact ihb (Tup.levels sig nl) Js i (Tup.levels ts nv) xs (nv + ts.length) (nl + sig.length) hget.2
    · exact ihk (Tup.levels sig nl) Js nv (nl + sig.length) hs.2

private theorem exprSupports_of_reify (target : LegalTarget) {as rs : List Ty} (f : Func as rs)
    (hf : f.Wf) (hsupp : f.supportsSource target = true) (xs : Tup Val as) :
    ExprSupports target (f Val Cont xs) := by
  simp only [Func.supportsSource, Bool.and_eq_true] at hsupp
  exact exprSupports_of_wf_toTFlat target (hf K Val KL Cont (Tup.levels as 0) xs) as.length 0 hsupp.2

private theorem cast_legalArg_i64_val (target : LegalTarget) (_hv : target.valid = true)
    {G : Ctx Val (LVar target Val)} (hG : CGoodWp target G)
    {a₁ : Arg Val i64} {a₂ : Arg (LVar target Val) i64} (ha : ArgRel G i64 a₁ a₂)
    (h64 : target.widenWidth 64 = 64) :
    (castArgBits h64 (legalArg target a₂).fst).val = a₁.val := by
  have hval := valsTup_legalArg target hG ha
  dsimp only [encodeVal, LegalTarget.legalTys, valsTup, Tup.map] at hval
  have hfst : (legalArg target a₂).fst.val = a₁.val.setWidth (target.widenWidth 64) :=
    congrArg Prod.fst hval
  rw [val_castArgBits, cast_eq_setWidth h64, hfst, BitVec.setWidth_setWidth_of_le _ (by omega),
    BitVec.setWidth_eq]

private theorem legalExpr_wp (target : LegalTarget) (hv : target.valid = true)
    {Γsrc Γtgt : Env} (hEnv : EnvRefines target Γsrc Γtgt)
    {rs : List Ty} :
    ∀ {G : Ctx Val (LVar target Val)} {D : Ctx Cont (LLab target Cont)}
      {e₁ : Expr Val Cont rs} {e₂ : Expr (LVar target Val) (LLab target Cont) rs},
      Wf G D e₁ e₂ →
      CGoodWp target G → DGoodWp target D →
      ExprSupports target e₁ →
      ∀ {Q : Post rs} {X : XPost} {m : Mem 64},
        wp Γsrc Q X e₁ m →
        wp Γtgt (legalPost target Q) (legalXPost target X) (legalExpr target e₂) m := by
  intro G D e₁ e₂ hwf
  induction hwf using Wf.induct with
  | @let_ G D ts op₁ op₂ k₁ k₂ hop hk ih =>
    intro hG hD hSupp Q X m hwp
    rw [wp_let] at hwp
    rw [legalExpr.eq_1]
    cases hSupp with | let_ _ _ hs_op hs_k =>
    refine legalOp_wp target hv hG hop hs_op hwp fun r lr hrel hr => ?_
    exact ih r lr (CGoodWp.pushTRel target hG hrel) hD (hs_k r) hr
  | @load G D t a₁ a₂ k₁ k₂ ha hk ih =>
    intro hG hD hSupp Q X m hwp
    rw [wp_load] at hwp
    rcases hwp with ⟨v, hLoad, hwpk⟩
    cases hSupp with | load _ _ _ hst hble hs_k =>
    have h64mem : 64 ∈ target.bitWidths := by
      simp only [LegalTarget.valid, Bool.and_eq_true, decide_eq_true_eq] at hv
      exact hv.1.1.2
    have h64 : target.widenWidth 64 = 64 := widenWidth_eq_self_of_mem target h64mem
    rw [legalExpr.eq_2, dite_eq_left h64]
    have hap : (castArgBits h64 (legalArg target a₂).fst).val = a₁.val :=
      cast_legalArg_i64_val target hv hG ha h64
    refine legalLoad_wp target hv t hst hble (ptr := castArgBits h64 (legalArg target a₂).fst)
      (by rwa [hap]) fun lr hlr => ?_
    refine ih v lr ?_ hD (hs_k v) hwpk
    intro t' x' lv' hm
    rcases List.mem_cons.1 hm with hhead | htail
    · cases hhead; exact hlr
    · exact hG _ _ _ htail
  | @store G D t v₁ v₂ a₁ a₂ k₁ k₂ hv_rel ha hk ih =>
    intro hG hD hSupp Q X m hwp
    rw [wp_store] at hwp
    rcases hwp with ⟨hOk, hwpk⟩
    cases hSupp with | store _ _ _ hst hble hs_k =>
    have h64mem : 64 ∈ target.bitWidths := by
      simp only [LegalTarget.valid, Bool.and_eq_true, decide_eq_true_eq] at hv
      exact hv.1.1.2
    have h64 : target.widenWidth 64 = 64 := widenWidth_eq_self_of_mem target h64mem
    rw [legalExpr.eq_3, dite_eq_left h64]
    have hap : (castArgBits h64 (legalArg target a₂).fst).val = a₁.val :=
      cast_legalArg_i64_val target hv hG ha h64
    refine legalStore_wp target hv t hst hble (xs := legalArg target v₂)
      (ptr := castArgBits h64 (legalArg target a₂).fst) (v := v₁.val)
      (valsTup_legalArg target hG hv_rel) (by rwa [hap]) ?_
    rw [hap]
    exact ih hG hD hs_k hwpk
  | @call G D f as bs args₁ args₂ k₁ k₂ hargs hk ih =>
    intro hG hD hSupp Q X m hwp
    cases hSupp with | call _ _ _ _ _ hs_k =>
    rw [legalExpr.eq_4]
    dsimp only [wp, wp._f] at hwp ⊢
    rcases hwp with ⟨P, E, hCall, hPost, hExit⟩
    refine ⟨legalPost target P, legalXPost target E, ?_, ?_, ?_⟩
    · have hJoin := valsTup_joinArgs target hG hargs
      rw [valsTup_eq_vals] at hJoin
      rw [valsTup_eq_vals] at hJoin
      rw [hJoin]
      exact hEnv f as bs (vals args₁) m P E hCall
    · rintro ys m' ⟨xs, rfl, hP⟩
      exact ih xs (splitParams target bs (encodeTup target bs xs))
        (CGoodWp.pushSplit target hG bs xs) hD (hs_k xs) (hPost xs m' hP)
    · rintro g cs' ys m' ⟨cs, hcs, xs, rfl, hE⟩
      exact ⟨cs, hcs, xs, rfl, hExit g cs xs m' hE⟩
  | @jnz G D c₁ c₂ t₁ t₂ e₁ e₂ hc ht he iht ihe =>
    intro hG hD hSupp Q X m hwp
    cases hSupp with | jnz _ _ _ hst hse =>
    rw [wp_jnz] at hwp
    rw [legalExpr.eq_5, wp_jnz]
    have hcv := valsTup_legalArg target hG hc
    dsimp only [encodeVal, LegalTarget.legalTys, valsTup, Tup.map] at hcv
    have hceq : (legalArg target c₂).fst.val = c₁.val := congrArg Prod.fst hcv
    rw [hceq]
    exact ⟨fun h => iht hG hD hst (hwp.1 h), fun h => ihe hG hD hse (hwp.2 h)⟩
  | @jump G D ts j₁ j₂ args₁ args₂ hj hargs =>
    intro hG hD _ Q X m hwp
    rw [wp_jump] at hwp
    rw [legalExpr.eq_6, wp_jump]
    have hJoin := valsTup_joinArgs target hG hargs
    rw [valsTup_eq_vals, valsTup_eq_vals] at hJoin
    rw [hJoin]
    exact hD ts j₁ j₂ hj (vals args₁) m hwp
  | @ret G D vs₁ vs₂ hvs =>
    intro hG _ _ Q X m hwp
    rw [wp_ret] at hwp
    rw [legalExpr.eq_7, wp_ret]
    have hJoin := valsTup_joinArgs target hG hvs
    rw [valsTup_eq_vals, valsTup_eq_vals] at hJoin
    exact ⟨vals vs₁, hJoin.symm, hwp⟩
  | @exit G D f as args₁ args₂ hargs =>
    intro hG _ _ Q X m hwp
    rw [wp_exit] at hwp
    rw [legalExpr.eq_8, wp_exit]
    have hJoin := valsTup_joinArgs target hG hargs
    rw [valsTup_eq_vals, valsTup_eq_vals] at hJoin
    exact ⟨as, rfl, vals args₁, hJoin.symm, hwp⟩
  | @hlt G D =>
    intro _ _ _ _ _ _ hwp
    cases hwp
  | @group G D sig b₁ b₂ k₁ k₂ hb hk ihb ihk =>
    intro hG hD hSupp Q X m hwp
    cases hSupp with | group _ _ _ hs_b hs_k =>
    rw [legalExpr.eq_10]
    dsimp only [wp, wp._f] at hwp ⊢
    intro Js2 hClosed2
    have hD' : DGoodWp target (Tup.zip (unlegalTupCont target Js2) (tupLiftMap target.legalSig Cont Js2) ++ D) :=
      DGoodWp.pushUnlegal target hD Js2
    have hClosed1 : Closed Γsrc Q X (b₁ (unlegalTupCont target Js2)) (unlegalTupCont target Js2) := by
      rw [closed_iff]
      intro ts i xs m' hbody1
      rw [unlegalTupCont_get]
      rw [closed_iff] at hClosed2
      apply hClosed2 (Member.map target.legalSig i) (encodeTup target ts xs) m'
      rw [legalBlocks_get]
      exact ihb (unlegalTupCont target Js2) (tupLiftMap target.legalSig Cont Js2) i xs
        (splitParams target ts (encodeTup target ts xs))
        (CGoodWp.pushSplit target hG ts xs) hD' (hs_b (unlegalTupCont target Js2) i xs) hbody1
    exact ihk (unlegalTupCont target Js2) (tupLiftMap target.legalSig Cont Js2)
      hG hD' (hs_k (unlegalTupCont target Js2)) (hwp (unlegalTupCont target Js2) hClosed1)

/-- `Func.legal` semantic preservation under any target environment refining `Γsrc`. -/
theorem Func.legal_wp_of_refines (target : LegalTarget) {as rs : List Ty} (f : Func as rs)
    (hf : f.Wf) (hsupp : f.supportsSource target = true)
    {Γsrc Γtgt : Env} (hEnv : EnvRefines target Γsrc Γtgt)
    (xs : Tup Val as) (m : Mem 64) (Q : Post rs) (X : XPost) :
    Func.wp Γsrc f xs m Q X →
    Func.wp Γtgt (f.legal target) (encodeTup target as xs) m (legalPost target Q) (legalXPost target X) := by
  intro hwp
  have hv : target.valid = true := by
    simp only [Func.supportsSource, Bool.and_eq_true] at hsupp
    exact hsupp.1.1.1
  unfold Func.wp Func.legal
  exact legalExpr_wp target hv hEnv
    (hf Val (LVar target Val) Cont (LLab target Cont) xs (splitParams target as (encodeTup target as xs)))
    (by simpa using CGoodWp.pushSplit target (fun _ _ _ hm => False.elim (List.not_mem_nil hm)) as xs)
    (fun _ _ _ hm => False.elim (List.not_mem_nil hm))
    (exprSupports_of_reify target f hf hsupp xs)
    hwp

/-- Main `T5` semantic preservation theorem for `Func.legal` with canonical `legalEnv`. -/
theorem Func.legal_wp (target : LegalTarget) {as rs : List Ty} (f : Func as rs)
    (hf : f.Wf) (hsupp : f.supportsSource target = true)
    (Γ : Env) (xs : Tup Val as) (m : Mem 64) (Q : Post rs) (X : XPost) :
    Func.wp Γ f xs m Q X →
    Func.wp (legalEnv target Γ) (f.legal target) (encodeTup target as xs) m
      (legalPost target Q) (legalXPost target X) :=
  Func.legal_wp_of_refines target f hf hsupp (envRefines_legalEnv target Γ) xs m Q X

/-- Specification-style consequence of `Func.legal_wp` matching E1's `Spec` convention. -/
theorem Func.legal_spec (target : LegalTarget) {as rs : List Ty} (f : Func as rs)
    (hf : f.Wf) (hsupp : f.supportsSource target = true)
    (Γ : Env) (xs : Tup Val as) (m : Mem 64) (Q : Post rs) (X : XPost) :
    Func.spec Γ f xs m Q X →
    Func.spec (legalEnv target Γ) (f.legal target) (encodeTup target as xs) m
      (legalPost target Q) (legalXPost target X) :=
  Func.legal_wp target f hf hsupp Γ xs m Q X

/-- Specification preservation for closed `Fn` units via `Fn.legal`. -/
theorem Fn.legal_spec (target : LegalTarget) (fn : Fn)
    (hf : fn.body.Wf) (hsupp : fn.body.supportsSource target = true)
    (Γ : Env) (xs : Tup Val fn.as) (m : Mem 64) (Q : Post fn.rs) (X : XPost) :
    Func.spec Γ fn.body xs m Q X →
    Func.spec (legalEnv target Γ) (fn.legal target).body (encodeTup target fn.as xs) m
      (legalPost target Q) (legalXPost target X) :=
  Func.legal_wp target fn.body hf hsupp Γ xs m Q X

end LegalWp

end LeanQbe.T








