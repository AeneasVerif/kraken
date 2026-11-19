module

public import LeanQbe.T.LegalCheck3b

/-!
# Target legality proofs for `LeanQbe.T.Legal` (Part 3b: `Func.legal_isLegal`)
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T

section LegalIsLegal

private theorem TBlocks_isLegal_of_forall (target : LegalTarget) {rs : List Ty}
    {Γ : List (Ty × VarKind)} {Δ : List (List Ty)} :
    ∀ {sig : List (List Ty)} (bs : Blocks K KL rs sig),
      (∀ ts (i : Member ts sig),
        target.isLegalSig ts = true ∧
        (toTFlat (bs.get i (Tup.levels ts Γ.length)) (Γ.length + ts.length) Δ.length).isLegal target
          (pushNormal ts Γ) Δ = true) →
      (toTBlocks bs Γ.length Δ.length).isLegal target Γ Δ = true
  | [], .nil, _ => rfl
  | ts :: sig', .cons b bs, h => by
    rw [toTBlocks_cons, TBlocks.isLegal_cons]
    have h0 := h ts .here
    simp only [Bool.and_eq_true] at h0 ⊢
    refine ⟨⟨h0.1, h0.2⟩, TBlocks_isLegal_of_forall target bs fun ts' i => h ts' (.there i)⟩

private theorem TBlocks_supportsSource_get (target : LegalTarget) {rs : List Ty} :
    ∀ {sig : List (List Ty)} (bs : Blocks K KL rs sig) {nv nl : Nat},
      (toTBlocks bs nv nl).supportsSource target = true →
      ∀ {ts} (i : Member ts sig),
        ts.all target.supportsTy = true ∧
        (toTFlat (bs.get i (Tup.levels ts nv)) (nv + ts.length) nl).supportsSource target = true
  | _, .cons b bs, nv, nl, hs, _, .here => by
    rw [toTBlocks_cons] at hs
    simp only [TBlocks.supportsSource, Bool.and_eq_true] at hs
    exact ⟨hs.1.1, hs.1.2⟩
  | _, .cons b bs, nv, nl, hs, ts, .there i => by
    rw [toTBlocks_cons] at hs
    simp only [TBlocks.supportsSource, Bool.and_eq_true] at hs
    exact TBlocks_supportsSource_get target bs hs.2 i

private theorem member_map_inv {α β : Type} (f : α → β) :
    ∀ {xs : List α} {b : β} (i' : Member b (xs.map f)),
      ∃ a, ∃ (i : Member a xs), b = f a ∧ HEq i' (Member.map f i) := by
  intro xs b i'
  induction xs generalizing b with
  | nil => cases i'
  | cons a xs ih =>
    cases i' with
    | here => exact ⟨a, .here, rfl, HEq.rfl⟩
    | there j =>
      obtain ⟨a0, i0, rfl, hij⟩ := ih j
      exact ⟨a0, .there i0, rfl, by cases hij; exact HEq.rfl⟩

theorem legalExpr_isLegal_wf (target : LegalTarget) (hv : target.valid = true) :
    {rs : List Ty} → {G : Ctx K (LVar target K)} → {D : Ctx KL (LLab target KL)} →
    {e₁ : Expr K KL rs} → {e₂ : Expr (LVar target K) (LLab target KL) rs} →
    Wf G D e₁ e₂ →
    ∀ {Γ : List (Ty × VarKind)} {Δ : List (List Ty)} (nv₁ nl₁ : Nat),
      CLegal target Γ G → DLegal target Δ D →
      (toTFlat e₁ nv₁ nl₁).supportsSource target = true →
      rs.all target.supportsTy = true →
      (toTFlat (legalExpr target e₂) Γ.length Δ.length).isLegal target Γ Δ = true := by
  intro rs G D e₁ e₂ hwf
  induction hwf using Wf.induct with
  | @let_ G D ts op₁ op₂ k₁ k₂ hop hk ih =>
    intro Γ Δ nv₁ nl₁ hc hd hs hrs
    rw [toTFlat_let] at hs
    simp only [TFlat.supportsSource, Bool.and_eq_true] at hs
    rw [legalExpr.eq_1]
    refine legalOp_isLegal target hv hc hop hs.1 nv₁ fun Γ' res hExt hres => ?_
    exact ih (Tup.levels ts nv₁) res (nv₁ + ts.length) nl₁ (hc.mono hExt |>.pushTRel hres) hd hs.2
      hrs
  | @load G D t a₁ a₂ k₁ k₂ ha hk ih =>
    intro Γ Δ nv₁ nl₁ hc hd hs hrs
    rw [toTFlat_load] at hs
    simp only [TFlat.supportsSource, Bool.and_eq_true, decide_eq_true_eq] at hs
    have h64 := valid_mem64 hv
    have h64w : target.widenWidth 64 = 64 := widenWidth_eq_self_of_mem target h64
    rw [legalExpr.eq_2, dite_eq_left h64w]
    have hs64 : target.supportsTy i64 = true :=
      supportsTy_bits_iff.2 ⟨⟨64, h64, Nat.le_refl 64⟩, by omega⟩
    have haN : ArgNormal target Γ i64 (castArgBits h64w (legalArg target a₂).1) :=
      ArgNormal.cast h64w (legalArg_isNormal hc hs64 ha).1
    refine legalLoad_isLegal target hv t _ hs.1.1 haN fun Γ' res hExt hres => ?_
    refine ih nv₁ res (nv₁ + 1) nl₁ ?_ hd hs.2 hrs
    intro t' lv₁ lv₂ hm
    rcases List.mem_cons.1 hm with ⟨rfl, rfl, rfl⟩ | htail
    · exact hres
    · exact (hc t' lv₁ lv₂ htail).mono hExt
  | @store G D t v₁ v₂ a₁ a₂ k₁ k₂ hv_rel ha hk ih =>
    intro Γ Δ nv₁ nl₁ hc hd hs hrs
    rw [toTFlat_store] at hs
    simp only [TFlat.supportsSource, Bool.and_eq_true, decide_eq_true_eq] at hs
    have h64 := valid_mem64 hv
    have h64w : target.widenWidth 64 = 64 := widenWidth_eq_self_of_mem target h64
    rw [legalExpr.eq_3, dite_eq_left h64w]
    have hs64 : target.supportsTy i64 = true :=
      supportsTy_bits_iff.2 ⟨⟨64, h64, Nat.le_refl 64⟩, by omega⟩
    have hvN := legalArg_isNormal hc hs.1.1 hv_rel
    have haN : ArgNormal target Γ i64 (castArgBits h64w (legalArg target a₂).1) :=
      ArgNormal.cast h64w (legalArg_isNormal hc hs64 ha).1
    refine legalStore_isLegal target hv t (legalArg target v₂) _ hs.1.1 hvN haN fun Γ' hExt => ?_
    exact ih nv₁ nl₁ (hc.mono hExt) hd hs.2 hrs
  | @call G D f as bs args₁ args₂ k₁ k₂ hargs hk ih =>
    intro Γ Δ nv₁ nl₁ hc hd hs hrs
    rw [toTFlat_call] at hs
    simp only [TFlat.supportsSource, Bool.and_eq_true] at hs
    rw [legalExpr.eq_4, toTFlat_call, TFlat.isLegal_call]
    have hArgsN := joinArgs_isNormal hc hs.1.1 hargs
    have hsigA := isLegalSig_legalSig hv hs.1.1
    have hsigB := isLegalSig_legalSig hv hs.1.2
    simp only [hsigA, hsigB, hArgsN.checkLegalArgs, Bool.true_and]
    let Γ' := pushNormal (target.legalSig bs) Γ
    have hlen : Γ'.length = Γ.length + (target.legalSig bs).length := by
      simp [Γ', pushNormal_length, Nat.add_comm]
    rw [← hlen]
    exact ih (Tup.levels bs nv₁) (splitParams target bs (Tup.levels (target.legalSig bs) Γ.length))
      (nv₁ + bs.length) nl₁ (CLegal.pushSplit target hv hc bs hs.1.2 _) hd hs.2 hrs
  | @jnz G D c₁ c₂ t₁ t₂ e₁ e₂ hrel ht he iht ihe =>
    intro Γ Δ nv₁ nl₁ hc hd hs hrs
    rw [toTFlat_jnz] at hs
    simp only [TFlat.supportsSource, Bool.and_eq_true] at hs
    rcases hpc : legalArg target c₂ with ⟨c', ⟨⟩⟩
    have hcN := legalArg_isNormal hc rfl hrel
    rw [hpc] at hcN
    simp only
      [legalExpr.eq_5, toTFlat_jnz, TFlat.isLegal_jnz, hpc, hcN.1.checkLegalArg, Bool.true_and,
      Bool.and_eq_true]
    exact ⟨iht nv₁ nl₁ hc hd hs.1 hrs, ihe nv₁ nl₁ hc hd hs.2 hrs⟩
  | @jump G D ts j₁ j₂ args₁ args₂ hj hargs =>
    intro Γ Δ _ _ hc hd hs _
    rw [toTFlat_jump] at hs
    simp only [TFlat.supportsSource] at hs
    rw [legalExpr.eq_6, toTFlat_jump, TFlat.isLegal_jump]
    obtain ⟨hlt, hget, hts⟩ := hd ts j₁ j₂ hj
    have hsigT := isLegalSig_legalSig hv hts
    have hArgsN := joinArgs_isNormal hc hts hargs
    simp only [hlt, ↓reduceIte, hget, hsigT, hArgsN.checkLegalArgs, Bool.true_and, Bool.and_true]
    cases hd' : listTyDecEq (target.legalSig ts) (target.legalSig ts) with
    | isTrue _ => rfl
    | isFalse hf => exact absurd rfl hf
  | @ret G D vs₁ vs₂ hvs =>
    intro Γ Δ _ _ hc _ _ hrs
    rw [legalExpr.eq_7, toTFlat_ret, TFlat.isLegal_ret]
    have hsigR := isLegalSig_legalSig hv hrs
    have hArgsN := joinArgs_isNormal hc hrs hvs
    simp [hsigR, hArgsN.checkLegalArgs]
  | @exit G D f as args₁ args₂ hargs =>
    intro Γ Δ _ _ hc _ hs _
    rw [toTFlat_exit] at hs
    simp only [TFlat.supportsSource] at hs
    rw [legalExpr.eq_8, toTFlat_exit, TFlat.isLegal_exit]
    have hsigA := isLegalSig_legalSig hv hs
    have hArgsN := joinArgs_isNormal hc hs hargs
    simp [hsigA, hArgsN.checkLegalArgs]
  | @hlt G D =>
    intro _ _ _ _ _ _ _ _
    simp [legalExpr.eq_9]
  | @group G D sig b₁ b₂ k₁ k₂ hb hk ihb ihk =>
    intro Γ Δ nv₁ nl₁ hc hd hs hrs
    rw [toTFlat_group] at hs
    simp only [TFlat.supportsSource, Bool.and_eq_true] at hs
    rw [legalExpr.eq_10, toTFlat_group, TFlat.isLegal_group]
    have hsigAll : (sig.map target.legalSig).all target.isLegalSig = true := by
      rw [List.all_map]
      exact List.all_eq_true.mpr fun ts hts =>
        isLegalSig_legalSig hv (List.all_eq_true.mp hs.1.1 ts hts)
    let Js₁ := Tup.levels sig nl₁
    let Js₂ := tupLiftMap target.legalSig KL (Tup.levels (sig.map target.legalSig) Δ.length)
    let Δ' := pushTypes (sig.map target.legalSig) Δ
    have hD' : DLegal target Δ' (Tup.zip Js₁ Js₂ ++ D) :=
      DLegal.pushLiftMap target hd sig hs.1.1 nl₁
    have hlenΔ : Δ'.length = Δ.length + (sig.map target.legalSig).length := by
      simp [Δ', pushTypes_length, Nat.add_comm]
    rw [← hlenΔ]
    have hB : (toTBlocks (legalBlocks target (b₂ Js₂)) Γ.length Δ'.length).isLegal target Γ Δ' =
      true := by
      refine TBlocks_isLegal_of_forall target (legalBlocks target (b₂ Js₂)) fun ts' i' => ?_
      obtain ⟨ts, i, rfl, heqi⟩ := member_map_inv target.legalSig i'
      have heqi' : i' = Member.map target.legalSig i := eq_of_heq heqi
      subst heqi'
      obtain ⟨hts_supp, hget_supp⟩ := TBlocks_supportsSource_get target (b₁ Js₁) hs.1.2 i
      have hsigT := isLegalSig_legalSig hv hts_supp
      refine ⟨hsigT, ?_⟩
      rw [legalBlocks_get]
      let Γ' := pushNormal (target.legalSig ts) Γ
      have hlenΓ : Γ'.length = Γ.length + (target.legalSig ts).length := by
        simp [Γ', pushNormal_length, Nat.add_comm]
      rw [← hlenΓ]
      exact ihb Js₁ Js₂ i (Tup.levels ts nv₁)
        (splitParams target ts (Tup.levels (target.legalSig ts) Γ.length))
        (nv₁ + ts.length) (nl₁ + sig.length)
        (CLegal.pushSplit target hv hc ts hts_supp (Tup.levels ts nv₁)) hD' hget_supp hrs
    have hK : (toTFlat (legalExpr target (k₂ Js₂)) Γ.length Δ'.length).isLegal target Γ Δ' = true :=
      ihk Js₁ Js₂ nv₁ (nl₁ + sig.length) hc hD' hs.2 hrs
    simp only [hsigAll, Bool.true_and, Bool.and_eq_true]
    exact ⟨hB, hK⟩

theorem Func.legal_isLegal (target : LegalTarget) {as rs : List Ty} (f : Func as rs)
    (hf : f.Wf) (hsupp : f.supportsSource target = true) :
    (f.legal target).isLegal target = true := by
  simp only [Func.supportsSource, Bool.and_eq_true] at hsupp
  rcases hsupp with ⟨⟨⟨hv, has⟩, hrs⟩, hbody⟩
  simp only [Func.isLegal, Bool.and_eq_true]
  refine ⟨⟨isLegalSig_legalSig hv has, isLegalSig_legalSig hv hrs⟩, ?_⟩
  let Γ₀ := pushNormal (target.legalSig as) []
  have hlen₀ : Γ₀.length = (target.legalSig as).length := by simp [Γ₀, pushNormal_length]
  change (toTFlat (legalExpr target (f (LVar target K) (LLab target KL)
    (splitParams target as (Tup.levels (target.legalSig as) 0)))) (target.legalSig as).length
      0).isLegal
      target Γ₀ [] = true
  rw [← hlen₀, show (0 : Nat) = ([] : List (List Ty)).length from rfl]
  have hc₀ : CLegal target Γ₀ (Tup.zip (Tup.levels as 0)
      (splitParams target as (Tup.levels (target.legalSig as) ([] : List (Ty × VarKind)).length)) ++
        []) :=
    CLegal.pushSplit target hv (fun _ _ _ h => by cases h) as has (Tup.levels as 0)
  have hd₀ : DLegal target ([] : List (List Ty)) [] := fun _ _ _ h => by cases h
  exact legalExpr_isLegal_wf target hv
    (hf K (LVar target K) KL (LLab target KL) (Tup.levels as 0)
      (splitParams target as (Tup.levels (target.legalSig as) 0)))
    as.length 0 (by simpa using hc₀) hd₀ hbody hrs

theorem Fn.legal_isLegal (target : LegalTarget) (fn : Fn)
    (hf : fn.Wf) (hsupp : fn.body.supportsSource target = true) :
    (fn.legal target).body.isLegal target = true :=
  Func.legal_isLegal target fn.body hf hsupp


end LegalIsLegal

end LeanQbe.T
